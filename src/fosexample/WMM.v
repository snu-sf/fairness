From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Export ITreeLib WFLibLarge FairBeh NatStructs Mod pind.
From PromisingLib Require Import Loc Event.
From PromisingSEQ Require Import Time View TView Cell Memory Local.

Set Implicit Arguments.

Module WMem.
  Program Definition init_cell: Cell.t :=
    @Cell.mk (LocMap.singleton Time.bot (Time.bot, Message.concrete (Const.of_Z (BinIntDef.Z.of_nat 0)) None)) _.
  Next Obligation.
  Proof.
    econs.
    { i. eapply LocMap.singleton_find_inv in GET. des; clarify. auto. }
    { i. eapply LocMap.singleton_find_inv in GET. des; clarify. auto. }
    { i. eapply LocMap.singleton_find_inv in GET1.
      eapply LocMap.singleton_find_inv in GET2. des; clarify.
    }
  Qed.

  Definition init_mem: Memory.t := fun _ => init_cell.

  Record t :=
    mk
      {
        memory:> Memory.t;
        sc: TimeMap.t;
      }.

  Definition init: t := mk init_mem TimeMap.bot.

  Let ident := (Loc.t * Time.t)%type.

  Definition view_to_local (vw: View.t): Local.t := Local.mk (TView.mk (fun _ => vw) vw vw) Memory.bot.

  Definition missed (m: Memory.t) (loc: Loc.t) (ts: Time.t): fmap ident :=
    fun '(loc', ts') =>
      if (Loc.eq_dec loc' loc)
      then
        if (Time.le_lt_dec ts' ts)
        then Flag.emp
        else match Memory.get loc' ts' m with
             | Some (_, Message.concrete _ (Some _)) => Flag.fail
             | _ => Flag.emp
             end
      else Flag.emp.

  Definition load_fun:
    ktree (threadE ident t) (View.t * Loc.t * Ordering.t) (View.t * Const.t) :=
    fun '(vw0, loc, ord) =>
      msc <- trigger (Get id);;
      '(exist _ (lc1, val, to) _) <- trigger (Choose (sig (fun '(lc1, val, to) =>
                                                             exists released,
                                                               Local.read_step
                                                                 (view_to_local vw0)
                                                                 (msc.(memory))
                                                                 loc
                                                                 to
                                                                 val
                                                                 released
                                                                 ord
                                                                 lc1)));;
      _ <- trigger (Fair (missed msc loc to));;
      Ret (lc1.(Local.tview).(TView.cur), val)
  .

  Definition store_fun:
    ktree (threadE ident t) (View.t * Loc.t * Const.t * Ordering.t) (View.t) :=
    fun '(vw0, loc, val, ord) =>
      msc <- trigger (Get id);;
      '(exist _ (lc1, to, sc1, mem1) _) <- trigger (Choose (sig (fun '(lc1, to, sc1, mem1) =>
                                                                   exists from released kind,
                                                                     Local.write_step
                                                                       (view_to_local vw0)
                                                                       (msc.(sc))
                                                                       (msc.(memory))
                                                                       loc
                                                                       from
                                                                       to
                                                                       val
                                                                       None
                                                                       released
                                                                       ord
                                                                       lc1
                                                                       sc1
                                                                       mem1
                                                                       kind)));;
      _ <- trigger (Fair (missed msc loc to));;
      _ <- trigger (Put (mk mem1 sc1));;
      Ret (lc1.(Local.tview).(TView.cur))
  .

  Definition faa_fun:
    ktree (threadE ident t) (View.t * Loc.t * Const.t * Ordering.t * Ordering.t) (View.t * Const.t) :=
    fun '(vw0, loc, addendum, ordr, ordw) =>
      msc <- trigger (Get id);;
      '(exist _ (lc2, to, val, sc1, mem1) _) <-
        trigger (Choose (sig (fun '(lc2, to, val, sc1, mem1) =>
                                exists lc1 from releasedr releasedw kind,
                                  (Local.read_step
                                     (view_to_local vw0)
                                     (msc.(memory))
                                     loc
                                     from
                                     val
                                     releasedr
                                     ordr
                                     lc1) /\
                                    (Local.write_step
                                       lc1
                                       (msc.(sc))
                                       (msc.(memory))
                                       loc
                                       from
                                       to
                                       (Const.add val addendum)
                                       releasedr
                                       releasedw
                                       ordw
                                       lc2
                                       sc1
                                       mem1
                                       kind))));;
      _ <- trigger (Fair (missed msc loc to));;
      _ <- trigger (Put (mk mem1 sc1));;
      Ret (lc2.(Local.tview).(TView.cur), val)
  .

  Definition mod: Mod.t :=
    Mod.mk
      init
      (Mod.get_funs [("store", Mod.wrap_fun store_fun);
                     ("load", Mod.wrap_fun load_fun);
                     ("faa", Mod.wrap_fun faa_fun)
      ]).

End WMem.

From Fairness Require Import PCM IProp IPMFOS FairRA StateRA MonotonePCM.
From PromisingSEQ Require Import MemoryProps.

Section MEMRA.
  Definition wmemRA: URA.t := (Loc.t ==> (Auth.t (Excl.t Cell.t)))%ra.

  Context `{WMEMRA: @GRA.inG wmemRA Σ}.

  Definition memory_resource_black (m: WMem.t): wmemRA :=
    fun loc =>
      Auth.black (Excl.just (m.(WMem.memory) loc): Excl.t Cell.t).

  Definition points_to_white (loc: Loc.t) (c: Cell.t): wmemRA :=
    fun loc' =>
      if (Loc.eq_dec loc' loc)
      then Auth.white (Excl.just c: Excl.t Cell.t)
      else URA.unit
  .

  Definition points_to (loc: Loc.t) (c: Cell.t): iProp :=
    OwnM (points_to_white loc c).

  Definition wmemory_black (m: WMem.t): iProp :=
    OwnM (memory_resource_black m).

  (* TODO: multiple locs *)
  Definition wmem_init_res (l0 l1: Loc.t): wmemRA :=
    points_to_white l0 WMem.init_cell ⋅ points_to_white l1 WMem.init_cell ⋅ memory_resource_black WMem.init.

  Lemma wmem_init_res_wf l0 l1
        (DISJ: l0 <> l1)
    :
    URA.wf (wmem_init_res l0 l1).
  Proof.
    unfold wmem_init_res, points_to_white, points_to, Auth.white.
    Local Transparent URA.unit.
    ur. i. ur. des_ifs.
    { splits.
      { eexists (URA.unit). ur. ss. }
      { ur. ss. }
    }
    { splits.
      { eexists (URA.unit). ur. ss. }
      { ur. ss. }
    }
    { splits.
      { eexists (Excl.just (WMem.init_mem k)). ur. ss. }
      { ur. ss. }
    }
  Qed.

  Lemma wmem_init_res_prop l0 l1
    :
    (OwnM (wmem_init_res l0 l1))
      -∗
      (points_to l0 WMem.init_cell ** points_to l1 WMem.init_cell ** wmemory_black WMem.init).
  Proof.
    iIntros "[[H0 H1] H2]". iFrame.
  Qed.

  (* normal points-to *)
  Definition wpoints_to (l: Loc.t) (v: Const.t) (vw: View.t): iProp :=
    ∃ c,
      (points_to l c)
        **
        (⌜exists from released,
              (<<GET: Cell.get (Cell.max_ts c) c = Some (from, Message.concrete v released)>>) /\
                (<<DEFINED: v <> Const.undef>>) /\
                (<<VIEW: View.le (View.singleton_ur l (Cell.max_ts c)) vw >>)⌝)
  .

  Lemma init_cell_max_ts
    :
    Cell.max_ts WMem.init_cell = Time.bot.
  Proof.
    auto.
  Qed.

  Lemma init_cell_get
    :
    Cell.get (Cell.max_ts WMem.init_cell) WMem.init_cell =
      Some (Time.bot, Message.concrete (BinIntDef.Z.of_nat 0) None).
  Proof.
    ss.
  Qed.

  Lemma init_cell_get_if to from msg
        (GET: Cell.get to WMem.init_cell = Some (from, msg))
    :
    (<<TO: to = Time.bot>>) /\
      (<<FROM: from = Time.bot>>) /\
      (<<MSG: msg = Message.concrete (BinIntDef.Z.of_nat 0) None>>).
  Proof.
    hexploit Cell.max_ts_spec; eauto. i. des.
    rewrite init_cell_max_ts in *. inv MAX.
    { inv H. }
    { inv H. setoid_rewrite init_cell_get in GET. clarify. }
  Qed.

  Lemma init_points_to_wpoints_to l v
    :
    (points_to l WMem.init_cell)
      -∗
      wpoints_to l (Const.of_Z (BinIntDef.Z.of_nat 0)) v.
  Proof.
    iIntros "H". iExists _. iFrame. iPureIntro. esplits.
    { rewrite init_cell_get. eauto. }
    { ss. }
    { econs.
      { ss. eapply TimeMap.singleton_spec.
        rewrite init_cell_max_ts. eapply Time.bot_spec. }
      { ss. eapply TimeMap.singleton_spec.
        rewrite init_cell_max_ts. eapply Time.bot_spec. }
    }
  Qed.

  Lemma wpoints_to_view_mon l v vw0 vw1
        (LE: View.le vw0 vw1)
    :
    (wpoints_to l v vw0)
      ⊢
      (wpoints_to l v vw1).
  Proof.
    unfold wpoints_to.
    iIntros "[% [OWN %]]". des. iExists _. iSplit; [iFrame|].
    iPureIntro. esplits; eauto.
  Qed.

  Lemma wmemory_ra_get
        m l c
    :
    (wmemory_black m)
      -∗
      (points_to l c)
      -∗
      ⌜m.(WMem.memory) l = c⌝.
  Proof.
    iIntros "BLACK WHITE".
    unfold wmemory_black, points_to.
    iCombine "BLACK WHITE" as "OWN". iOwnWf "OWN". iPureIntro.
    ur in H. specialize (H l).
    unfold memory_resource_black, points_to_white in H. des_ifs.
    ur in H. ur in H. des_ifs. des. rr in H. des. ur in H. des_ifs.
  Qed.

  Lemma pointwise_updatabable M K (a b: URA.pointwise K M)
        (POINTWISE: forall k, URA.updatable (a k) (b k))
    :
    URA.updatable a b.
  Proof.
    ii. ur. ur in H. i. eapply POINTWISE; eauto.
  Qed.

  Lemma wmemory_ra_write
        m0 m1 l c
        from to msg
        (WRITE: Memory.add m0.(WMem.memory) l from to msg m1)
    :
    (wmemory_black m0)
      -∗
      (points_to l c)
      -∗
      (#=> (wmemory_black (WMem.mk m1 m0.(WMem.sc)) ** points_to l (m1 l))).
  Proof.
    iIntros "BLACK WHITE".
    unfold wmemory_black, points_to.
    iCombine "BLACK WHITE" as "OWN". iOwnWf "OWN".
    ur in H. specialize (H l).
    unfold memory_resource_black, points_to_white in H. des_ifs.
    ur in H. ur in H. des_ifs. des. rr in H. des. ur in H. des_ifs.
    iAssert (#=> OwnM (memory_resource_black (WMem.mk m1 m0.(WMem.sc)) ⋅ points_to_white l (m1 l))) with "[OWN]" as "> [BLACK WHITE]".
    { iApply (OwnM_Upd with "OWN").
      ur. apply pointwise_updatabable. i.
      unfold memory_resource_black, points_to_white. ss.
      inv WRITE. setoid_rewrite LocFun.add_spec. des_ifs.
      eapply Auth.auth_update. ii. des. split; ss.
      { ur. ss. }
      { ur in FRAME. ur. des_ifs. rr.
        f_equal. symmetry. apply LocFun.add_spec_eq.
      }
    }
    { iModIntro. iFrame. }
  Qed.

  Lemma memory_write_max_ts m0 loc from to msg m1
        (ADD: Memory.add m0 loc from to msg m1)
        (MAX: Time.le (Memory.max_ts loc m0) to)
    :
    Memory.max_ts loc m1 = to.
  Proof.
    apply TimeFacts.antisym.
    { hexploit Memory.max_ts_spec.
      { eapply Memory.add_get0; eauto. }
      i. des. erewrite Memory.add_o in GET; eauto. des_ifs.
      { ss. des; clarify. }
      { des; ss. eapply Memory.max_ts_spec in GET. des. etrans; eauto. }
    }
    { eapply Memory.add_get0 in ADD. des.
      eapply Memory.max_ts_spec in GET0. des. auto.
    }
  Qed.

  Lemma wmemory_ra_load
        m l v0 v1 vw0 vw1
        ord lc1 to released
        (READ: Local.read_step (WMem.view_to_local vw0) m.(WMem.memory) l to v1 released ord lc1)
        (VIEW: vw1 = lc1.(Local.tview).(TView.cur))
        (ORD: ord = Ordering.plain)
    :
    (wmemory_black m)
      -∗
      (wpoints_to l v0 vw0)
      -∗
      ((wmemory_black m) ∗ (⌜(View.le vw0 vw1) /\ (v0 = v1)⌝) ∗ #=>(wpoints_to l v0 vw1)).
  Proof.
    iIntros "BLACK [% [WHITE %]]". des. subst.
    iPoseProof (wmemory_ra_get with "BLACK WHITE") as "%". subst.
    iSplitL "BLACK"; [auto|]. inv READ. ss. iSplit.
    { iPureIntro. split.
      { etrans; [|eapply View.join_l]. eapply View.join_l. }
      { assert (to = (Cell.max_ts (WMem.memory m l))).
        { eapply TimeFacts.antisym.
          { eapply Memory.max_ts_spec in GET0. des. clarify. }
          { inv READABLE. etrans; eauto.
            inv VIEW0. ss. specialize (PLN0 l).
            unfold TimeMap.singleton in PLN0.
            setoid_rewrite LocFun.add_spec_eq in PLN0. auto.
          }
        }
        subst. setoid_rewrite GET in GET0. clarify.
        inv VAL; ss.
        destruct v1, val'; ss. apply Z.eqb_eq in H0. subst. auto.
      }
    }
    { iModIntro. iExists _. iFrame. iPureIntro. esplits; eauto.
      ss. unfold View.singleton_ur_if. des_ifs.
      etrans; eauto.
      etrans; [|eapply View.join_l]. eapply View.join_l.
    }
  Qed.

  Lemma wmemory_ra_store
        m0 l v0 vw0 m1 v1 vw1
        lc1 to sc1 mem1 ord from released kind
        (WRITE: Local.write_step (WMem.view_to_local vw0) m0.(WMem.sc) m0.(WMem.memory) l from to v1 None released ord lc1 sc1 mem1 kind)
        (VIEW: vw1 = lc1.(Local.tview).(TView.cur))
        (MEM: m1 = WMem.mk mem1 sc1)
        (ORD: ord = Ordering.plain)
        (DEFINED: v1 <> Const.undef)
    :
    (wmemory_black m0)
      -∗
      (wpoints_to l v0 vw0)
      -∗
      ((⌜View.le vw0 vw1⌝) ∗ #=>((wmemory_black m1) ∗ (wpoints_to l v1 vw1))).
  Proof.
    iIntros "BLACK [% [WHITE %]]". des. subst.
    iPoseProof (wmemory_ra_get with "BLACK WHITE") as "%". subst.
    inv WRITE. ss. hexploit memory_write_bot_add; eauto. i. subst.
    inv WRITE0. inv PROMISE. clear REMOVE PROMISES ATTACH TS.
    assert (MAX: Cell.max_ts (mem1 l) = to).
    { hexploit Memory.max_ts_spec.
      { eapply Memory.add_get1; eauto. }
      i. des. erewrite Memory.add_o in GET0; eauto. des_ifs; ss.
      { des; clarify. }
      { des; ss. eapply Memory.max_ts_spec in GET0. des.
        hexploit Memory.max_ts_spec.
        { eapply Memory.add_get0; eauto. }
        i. des. inv WRITABLE.
        exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
        { eapply TS. }
        etrans; eauto.
        etrans; eauto.
        inv VIEW0. ss. specialize (RLX l).
        unfold TimeMap.singleton in RLX. setoid_rewrite LocFun.add_spec_eq in RLX. auto.
      }
    }
    subst. iSplit.
    { iPureIntro. eapply View.join_l. }
    iPoseProof (wmemory_ra_write with "BLACK WHITE") as "> [BLACK WHITE]".
    { eauto. }
    iModIntro. iSplitL "BLACK"; [auto|].
    iExists _. iSplit; [iFrame|]. iPureIntro. esplits; eauto.
    { eapply Memory.add_get0; eauto. }
    { ss. eapply View.join_r. }
  Qed.

  (* faa points-to *)
  Definition wpoints_to_faa (l: Loc.t) (v: Const.t): iProp :=
    ∃ c,
      (points_to l c)
        **
        (⌜exists from released,
              (<<GET: Cell.get (Cell.max_ts c) c = Some (from, Message.concrete v released)>>) /\
                (<<FAA: forall to from msg (GET: Cell.get to c = Some (from, msg)),
                    ((exists to' msg',
                         (<<GET: Cell.get to' c = Some (to, msg')>>) /\ (<<TS: Time.lt to to'>>)) \/
                       (<<TS: to = Cell.max_ts c>>))>>) /\
                (<<DEFINED: v <> Const.undef>>)⌝)
  .

  Lemma init_points_to_wpoints_to_faa l
    :
    (points_to l WMem.init_cell)
      -∗
      wpoints_to_faa l (Const.of_Z (BinIntDef.Z.of_nat 0)).
  Proof.
    iIntros "H". iExists _. iFrame. iPureIntro. esplits.
    { rewrite init_cell_get. eauto. }
    { i. hexploit init_cell_get_if; eauto. i. des; clarify.
      right. rewrite init_cell_max_ts. auto.
    }
    { ss. }
  Qed.

  Lemma wmemory_ra_faa
        v msc
        vw0 loc addendum ordr ordw
        lc1 from releasedr releasedw kind
        lc2 to val sc1 mem1
        (READ: Local.read_step (WMem.view_to_local vw0) (msc.(WMem.memory)) loc from val releasedr ordr lc1)
        (WRITE: Local.write_step lc1 (msc.(WMem.sc)) (msc.(WMem.memory)) loc from to (Const.add val addendum) releasedr releasedw ordw lc2 sc1 mem1 kind)
        (ORDR: ordr = Ordering.plain)
        (ORDW: ordw = Ordering.acqrel)
        (DEFINED: addendum <> Const.undef)
    :
    (wmemory_black msc)
      -∗
      (wpoints_to_faa loc v)
      -∗
      ((⌜(View.le vw0 lc2.(Local.tview).(TView.cur)) /\ (v = val)⌝)
         ∗ #=>((wmemory_black (WMem.mk mem1 sc1)) ∗ wpoints_to_faa loc (Const.add v addendum))).
  Proof.
    iIntros "BLACK [% [WHITE %]]". des. subst.
    iPoseProof (wmemory_ra_get with "BLACK WHITE") as "%". subst.
    inv READ. inv WRITE. ss.
    inv WRITE0. ss. hexploit memory_write_bot_add; eauto. i. subst.
    inv PROMISE. clear REMOVE PROMISES ATTACH TS.
    hexploit add_succeed_wf; eauto. i. des.
    assert (MAX0: from = Cell.max_ts (WMem.memory msc loc)).
    { hexploit FAA; eauto. i. des; auto.
      hexploit DISJOINT; eauto. i. exfalso. eapply H.
      { instantiate (1:=Time.meet to to'). econs; ss.
        { unfold Time.meet. des_ifs. }
        { eapply Time.meet_l. }
      }
      { econs; ss.
        { unfold Time.meet. des_ifs. }
        { eapply Time.meet_r. }
      }
    }
    subst. setoid_rewrite GET0 in GET. inv GET.
    assert (val = v).
    { inv VAL; ss. destruct val, v; ss. apply Z.eqb_eq in H0. subst. auto. }
    subst. iSplit.
    { iPureIntro. split.
      { etrans; [|eapply View.join_l].
        etrans; [|eapply View.join_l].
        eapply View.join_l.
      }
      { auto. }
    }
    assert (MAX1: to = Cell.max_ts (mem1 loc)).
    { eapply TimeFacts.antisym.
      { hexploit Memory.max_ts_spec.
        { eapply Memory.add_get0; eauto. }
        { i. des. eauto. }
      }
      { hexploit Memory.max_ts_spec.
        { eapply Memory.add_get1; eauto. }
        i. des. erewrite Memory.add_o in GET; eauto. des_ifs.
        { ss. des; subst. reflexivity. }
        { guardH o. eapply Memory.max_ts_spec in GET. des.
          etrans ;eauto. left. auto.
        }
      }
    }
    iPoseProof (wmemory_ra_write with "BLACK WHITE") as "> [BLACK WHITE]".
    { eauto. }
    iModIntro. iSplitL "BLACK"; [auto|].
    iExists _. iSplit; [iFrame|]. iPureIntro. esplits; eauto.
    { erewrite <- MAX1. eapply Memory.add_get0; eauto. }
    { i. setoid_rewrite Memory.add_o in GET; [|eauto]. des_ifs.
      { ss. des; clarify. auto. }
      { guardH o. hexploit FAA; eauto. i. des.
        { left. esplits; eauto. eapply Memory.add_get1; eauto. }
        { subst. left. esplits; eauto.
          { eapply Memory.add_get0; eauto. }
        }
      }
    }
    { ii. destruct v, addendum; ss. }
  Qed.

  (* full points-to *)
  Definition wProp := Const.t -> View.t -> Prop.
  Definition wor (P Q: wProp): wProp := fun c vw => ((P c vw) \/ (Q c vw)).
  Definition wimpl (P Q: wProp): Prop := (∀ c vw, (P c vw) -> (Q c vw)).

  Definition lift_wProp (P: wProp) (c: Const.t) (vw: View.t): iProp :=
    ∃ vw', (⌜P c vw'⌝) ∗ (⌜View.le vw' vw⌝).

  Lemma lift_wProp_mon
        P c vw0 vw1
        (LE: View.le vw0 vw1)
    :
    (lift_wProp P c vw0) -∗ (lift_wProp P c vw1).
  Proof.
    unfold lift_wProp. iIntros "[% [A %B]]". iExists vw'. iFrame.
    iPureIntro. etrans. eapply B. auto.
  Qed.




  Variable S: Type.
  Variable p: Prism.t S WMem.ident.

  Context `{OBLGRA: @GRA.inG ObligationRA.t Σ}.
  Context `{ARROWRA: @GRA.inG (ArrowRA S) Σ}.
  Context `{IDENTTGT: @GRA.inG (identTgtRA S) Σ}.
  Context `{EDGERA: @GRA.inG EdgeRA Σ}.
  Context `{ONESHOTSRA: @GRA.inG (@FiniteMap.t (OneShot.t unit)) Σ}.

  Definition wmemory_black_strong m: iProp :=
    wmemory_black m ** (FairRA.blacks (Prism.compose inrp p) (fun id => exists loc to, id = (loc, to) /\ Memory.get loc to m.(WMem.memory) = None)).

  Lemma wmemory_ra_write_strong
        m0 m1 l c
        from to msg
        (WRITE: Memory.add m0.(WMem.memory) l from to msg m1)
    :
    (wmemory_black_strong m0)
      -∗
      (points_to l c)
      -∗
      (#=> (wmemory_black_strong (WMem.mk m1 m0.(WMem.sc)) ** points_to l (m1 l) ** FairRA.black_ex (Prism.compose inrp p) (l, to) 1%Qp)).
  Proof.
    iIntros "[BLACK BLACKS] WHITE".
    iPoseProof (wmemory_ra_write with "BLACK WHITE") as "> [BLACK WHITE]"; [eauto|..].
    iModIntro. iFrame. iApply (FairRA.blacks_unfold with "BLACKS").
    { i. ss. des; subst.
      { erewrite Memory.add_o in IN0; eauto. des_ifs. esplits; eauto. }
      { esplits; eauto. eapply Memory.add_get0. eauto. }
    }
    { ii. des. clarify. ss. eapply Memory.add_get0 in WRITE. des; clarify. }
  Qed.

  Lemma wmemory_ra_faa_strong
        v msc
        vw0 loc addendum ordr ordw
        lc1 from releasedr releasedw kind
        lc2 to val sc1 mem1
        (READ: Local.read_step (WMem.view_to_local vw0) (msc.(WMem.memory)) loc from val releasedr ordr lc1)
        (WRITE: Local.write_step lc1 (msc.(WMem.sc)) (msc.(WMem.memory)) loc from to (Const.add val addendum) releasedr releasedw ordw lc2 sc1 mem1 kind)
        (ORDR: ordr = Ordering.plain)
        (ORDW: ordw = Ordering.acqrel)
        (DEFINED: addendum <> Const.undef)
    :
    (wmemory_black_strong msc)
      -∗
      (wpoints_to_faa loc v)
      -∗
      ((⌜(View.le vw0 lc2.(Local.tview).(TView.cur)) /\ (v = val)⌝)
         ∗ #=>((wmemory_black_strong (WMem.mk mem1 sc1)) ∗ wpoints_to_faa loc (Const.add v addendum))).
  Proof.
    iIntros "[BLACK BLACKS] WHITE".
    iPoseProof (wmemory_ra_faa with "BLACK WHITE") as "[% H]"; eauto.
    iSplitR; [auto|]. iPoseProof ("H") as "> [H0 H1]".
    iModIntro. unfold wmemory_black_strong. iFrame.
    inv READ. inv WRITE. hexploit memory_write_bot_add; eauto. i. subst. ss.
    inv WRITE0. inv PROMISE. ss.
    iPoseProof (FairRA.blacks_unfold with "BLACKS") as "[H0 H1]"; [..|iApply "H0"].
    { i. ss. des; subst.
      { erewrite Memory.add_o in IN0; eauto. des_ifs. esplits; eauto. }
      { esplits; eauto. eapply Memory.add_get0. eauto. }
    }
    { ii. des. clarify. eapply Memory.add_get0 in MEM. des; clarify. }
  Qed.

  Definition wpoints_to_full (l: Loc.t) (V: View.t) (k: nat) (P Q: wProp) : iProp :=
    ∃ c,
      (points_to l c)
        **
        (∃ v released,
            (⌜Cell.max_ts c = Time.bot⌝ ∨ ObligationRA.duty (Prism.compose inrp p) (l, (Cell.max_ts c)) [(k,Ord.S Ord.O)])
              **
              (ObligationRA.pending k 1%Qp)
              **
              (⌜Q v View.bot⌝)
              **
              (⌜(<<MSGVIEW: V = View.join (View.unwrap released) (View.singleton_ur l (Cell.max_ts c))>>) /\
                 (<<DEFINED: v <> Const.undef>>) /\
                 exists from,
                   (<<GET: Cell.get (Cell.max_ts c) c = Some (from, Message.concrete v released)>>) /\
                     (<<DEFINED: v <> Const.undef>>) /\
                     (<<RELEASED: Time.lt Time.bot (Cell.max_ts c) -> released <> None>>)⌝)
              **
              (⌜forall to from' v' released' (GET: Cell.get to c = Some (from', Message.concrete v' released'))
                       (LT: Time.lt to (Cell.max_ts c)),
                    (P v' View.bot) /\ (<<DEFINED: v' <> Const.undef>>)⌝))
  .

  Lemma init_points_to_wpoints_to_full l (P Q: wProp)
        (SAT: Q (Const.of_Z (BinIntDef.Z.of_nat 0)) View.bot)
    :
    (points_to l WMem.init_cell)
      -∗
      #=>
      (∃ k, wpoints_to_full l View.bot k P Q ** ObligationRA.black k Ord.O).
  Proof.
    iIntros "H".
    iPoseProof (ObligationRA.alloc) as "> [% [[B W] PENDING]]".
    iModIntro. iExists _. iSplitR "B"; [|iApply "B"]. iExists _.
    iSplitL "H"; [iApply "H"|]. iExists _, _. iSplitL.
    { iSplitL.
      { iSplit; [|eauto]. iSplitR.
        { iLeft. iPureIntro. apply init_cell_max_ts. }
        { iApply "PENDING". }
      }
      { iPureIntro. esplits; eauto.
        { eapply View.antisym.
          { eapply View.bot_spec. }
          { ss. eapply View.join_spec.
            { reflexivity. }
            { rewrite init_cell_max_ts.
              econs; ss; eapply TimeMap.singleton_spec; eapply Time.bot_spec.
            }
          }
        }
        { i. rewrite init_cell_max_ts in H. inv H. }
      }
    }
    { iPureIntro. i. apply init_cell_get_if in GET. des. clarify.
      rewrite init_cell_max_ts in LT. inv LT.
    }
  Qed.

  Lemma wpoints_to_full_not_shot
        l V k P Q
    :
    (wpoints_to_full l V k P Q) ∗ (ObligationRA.shot k) -∗ ⌜False⌝.
  Proof.
    iIntros "[[% [? [% [% [[[[? PENDING] ?] ?] H]]]]] SHOT]".
    iApply (ObligationRA.pending_not_shot with "PENDING SHOT").
  Qed.

  Lemma wpoints_to_full_impl
        l V k P P' Q
    :
    ((⌜wimpl P P'⌝) ∗ (wpoints_to_full l V k P Q))
      -∗ (wpoints_to_full l V k P' Q).
  Proof.
    iIntros "[% [% [A [% [% [B %]]]]]]".
    iExists _. iSplitL "A"; [iFrame|]. iExists _, _. iFrame.
    iIntros (? ? ? ? ? ?). iPureIntro.
    hexploit H0; eauto. i. des. split; auto.
  Qed.

  Lemma wmemory_ra_get_strong
        m l c
    :
    (wmemory_black_strong m)
      -∗
      (points_to l c)
      -∗
      ⌜m.(WMem.memory) l = c⌝.
  Proof.
    iIntros "[BLACK _] WHITE". iApply (wmemory_ra_get with "BLACK WHITE").
  Qed.

  Lemma wmemory_ra_load_acq
        l V k (P Q: wProp)
        m val vw0 vw1
        ord lc1 to released
        (READ: Local.read_step (WMem.view_to_local vw0) m.(WMem.memory) l to val released ord lc1)
        (VIEW: vw1 = lc1.(Local.tview).(TView.cur))
        (ORD: ord = Ordering.acqrel)
    :
    (wmemory_black_strong m)
      -∗
      (wpoints_to_full l V k P Q)
      -∗
      ((⌜View.le vw0 vw1⌝)
         ∗ (wmemory_black_strong m)
         ∗ (wpoints_to_full l V k P Q)
         ∗ (((lift_wProp P val vw1)
               ∗ (∃ ts, (ObligationRA.correl (Prism.compose inrp p) (l, ts) k (Ord.S Ord.O))
                          ∗ (⌜WMem.missed m.(WMem.memory) l to (l, ts) = Flag.fail⌝)))
            ∨ ((lift_wProp Q val vw1) ∗ (⌜View.le V vw1⌝)))
      ).
  Proof.
    iIntros "BLACK [% [WHITE [% [% [[[[X Y] %] %] %]]]]]". des. subst.
    iPoseProof (wmemory_ra_get_strong with "BLACK WHITE") as "%". subst.
    inv READ. ss. iSplit.
    { iPureIntro. aggrtac. }
    iAssert (⌜Cell.max_ts (WMem.memory m l) = Time.bot⌝
             ∨ (ObligationRA.correl (Prism.compose inrp p) _ _ _))%I with "[X]" as "#CORREL".
    { iPoseProof "X" as "[X|X]"; [auto|].
      iRight. iApply (ObligationRA.duty_correl with "X"). ss. eauto.
    }
    iSplitL "BLACK"; [auto|]. iSplitL.
    { iExists _. iFrame. iExists _, _. iSplit.
      { iSplit.
        { auto. }
        { iPureIntro. esplits; eauto. }
      }
      { iPureIntro. auto. }
    }
    destruct (Time.eq_dec to (Cell.max_ts (WMem.memory m l))).
    { iRight. subst. setoid_rewrite GET0 in GET. inv GET.
      assert (val = v).
      { inv VAL; ss.
        destruct v, val; ss. apply Z.eqb_eq in H2. subst. auto.
      }
      subst. iSplit.
      { unfold lift_wProp. iExists _. iSplit.
        { iPureIntro. eauto. }
        { iPureIntro. apply View.bot_spec. }
      }
      { iPureIntro. unfold View.singleton_ur_if. des_ifs.
        eapply View.join_spec.
        { aggrtac. }
        { etrans; [|eapply View.join_l]. eapply View.join_r. }
      }
    }
    { iLeft. hexploit Memory.max_ts_spec.
      { eapply GET0. }
      i. des. dup MAX. inv MAX; ss.
      hexploit H1; eauto. i. des.
      assert (val' = val).
      { inv VAL; ss. destruct val, val'; ss. apply Z.eqb_eq in H4. subst. auto. }
      subst. iSplitR.
      { unfold lift_wProp. iExists _. iSplit.
        { iPureIntro. eapply H1; eauto. }
        { iPureIntro. apply View.bot_spec. }
      }
      iExists _. iSplitR.
      { iPoseProof "CORREL" as "[%BOT|CORR]"; [|auto].
        setoid_rewrite BOT in H0. inv H0.
      }
      iPureIntro.
      destruct (LocSet.Facts.eq_dec l l); ss.
      destruct (Time.le_lt_dec (Cell.max_ts (WMem.memory m l)) to).
      { exfalso. eapply Time.lt_strorder.
        eapply TimeFacts.lt_le_lt; [|apply l0]; eauto.
      }
      setoid_rewrite GET. hexploit RELEASED; auto.
      { eapply TimeFacts.le_lt_lt; eauto. eapply Time.bot_spec. }
      { i. des_ifs. }
    }
  Qed.

  Lemma wmemory_ra_load_rlx
        l V k (P Q: wProp)
        m val vw0 vw1
        ord lc1 to released
        (READ: Local.read_step (WMem.view_to_local vw0) m.(WMem.memory) l to val released ord lc1)
        (VIEW: vw1 = lc1.(Local.tview).(TView.cur))
        (ORD: ord = Ordering.relaxed)
    :
    (wmemory_black_strong m)
      -∗
      (wpoints_to_full l V k P Q)
      -∗
      (⌜View.le V vw0⌝)
      -∗
      ((⌜View.le vw0 vw1⌝)
         ∗ (wmemory_black_strong m)
         ∗ (wpoints_to_full l V k P Q)
         ∗ (lift_wProp Q val vw1)
      ).
  Proof.
    iIntros "BLACK [% [WHITE [% [% [[[X %] %] Z]]]]] %". des. subst.
    iPoseProof (wmemory_ra_get_strong with "BLACK WHITE") as "%". subst.
    inv READ. ss.
    assert (TO: to = Cell.max_ts (WMem.memory m l)).
    { eapply TimeFacts.antisym.
      { eapply Memory.max_ts_spec in GET0. des. clarify. }
      { inv READABLE. etrans; eauto.
        inv H1. ss. specialize (PLN0 l).
        unfold TimeMap.singleton in PLN0. etrans; [|eauto].
        unfold TimeMap.join. setoid_rewrite LocFun.add_spec_eq.
        apply Time.join_r.
      }
    }
    subst. setoid_rewrite GET0 in GET. inv GET.
    assert (val = v).
    { inv VAL; ss.
      destruct v, val; ss. apply Z.eqb_eq in H2. subst. auto.
    }
    subst. iSplit.
    { iPureIntro. aggrtac. }
    iSplitL "BLACK"; [auto|]. iSplitL.
    { iExists _. iFrame. iExists _, _. iSplit; eauto. iPureIntro. esplits; eauto. }
    { unfold lift_wProp. iExists _. iPureIntro. splits; eauto. eapply View.bot_spec. }
  Qed.

  Lemma wmemory_ra_store_rel
        l V k (P Q R: wProp)
        m0 vw0 m1 val vw1
        lc1 to sc1 mem1 ord from released kind
        (WRITE: Local.write_step (WMem.view_to_local vw0) m0.(WMem.sc) m0.(WMem.memory) l from to val None released ord lc1 sc1 mem1 kind)
        (VIEW: vw1 = lc1.(Local.tview).(TView.cur))
        (MEM: m1 = WMem.mk mem1 sc1)
        (ORD: ord = Ordering.acqrel)
        (DEFINED: val <> Const.undef)
    :
    (wmemory_black_strong m0)
      -∗
      (wpoints_to_full l V k P Q)
      -∗
      (⌜View.le V vw0⌝)
      -∗
      (⌜R val View.bot⌝)
      -∗
      ((⌜View.le vw0 vw1⌝)
         ∗ #=( ObligationRA.arrows_sat (S:=sum_tid S) )=> ((wmemory_black_strong m1))
         ∗ (∃ V' k' o,
               (⌜View.le V' vw1⌝)
                 ∗
                 (⌜View.le vw0 V'⌝)
                 ∗
                 #=>((wpoints_to_full l V' k' (wor P Q) R)
                       ∗ (ObligationRA.black k' o)
                    )
           )
      ).
  Proof.
    iIntros "BLACK [% [WHITE [% [% [[[[_ Y] %] %] %]]]]] % %". des. subst.
    iPoseProof (wmemory_ra_get_strong with "BLACK WHITE") as "%". subst.
    inv WRITE. ss. iSplit.
    { iPureIntro. aggrtac. }
    hexploit memory_write_bot_add; eauto. i. subst.
    inv WRITE0. inv PROMISE. clear REMOVE PROMISES ATTACH TS.
    iPoseProof (wmemory_ra_write_strong with "BLACK WHITE") as "> [[BLACK WHITE] FAIRBLACK]".
    { eauto. }
    assert (TS: Time.lt (Cell.max_ts (WMem.memory m0 l)) to).
    { inv WRITABLE. eapply TimeFacts.le_lt_lt; [|eauto].
      inv H2. ss. etrans; [|eapply RLX].
      unfold TimeMap.join, TimeMap.singleton. setoid_rewrite LocFun.add_spec_eq.
      eapply Time.join_r.
    }
    hexploit memory_write_max_ts.
    { eauto. }
    { left. auto. }
    i. subst.
    iPoseProof (ObligationRA.alloc) as "> [% [[B W] PENDING]]".
    iPoseProof (ObligationRA.duty_alloc with "[FAIRBLACK] W") as "> DUTY".
    { unfold ObligationRA.duty. iExists [], _.  iSplit.
      { iFrame. iApply ObligationRA.duty_list_nil. }
      { ss. }
    }
    iModIntro. iSplitL "BLACK"; [auto|].
    iExists _, _, _. iSplit; cycle 1.
    { iSplitR; cycle 1.
      { iModIntro. iSplitR "B"; [|eauto].
        iExists _. iSplitL "WHITE"; [auto|].
        iExists _, _. iSplitL.
        { iSplitL.
          { iSplitL; [|eauto]. iSplitL "DUTY". eauto. iFrame. }
          { iPureIntro. splits; eauto. esplits.
            { eapply Memory.add_get0. eauto. }
            { auto. }
            { i. ss. }
          }
        }
        { iPureIntro. i. setoid_rewrite Memory.add_o in GET0; eauto. des_ifs.
          { ss. des; clarify. exfalso. eapply Time.lt_strorder. eapply LT. }
          { des; ss. hexploit Memory.max_ts_spec; eauto. i. des. inv MAX.
            { hexploit H1; eauto. i. des; ss. splits; auto. rr. auto. }
            { inv H0. clarify. setoid_rewrite GET1 in GET. clarify.
              splits; auto. rr. auto.
            }
          }
        }
      }
      { iPureIntro. unfold TView.write_released. des_ifs. ss. des_ifs.
        setoid_rewrite LocFun.add_spec_eq. aggrtac.
      }
    }
    { iPureIntro. unfold TView.write_released. des_ifs. ss. des_ifs.
      setoid_rewrite LocFun.add_spec_eq. eapply View.join_spec.
      { eapply View.join_spec.
        { eapply View.bot_spec. }
        { reflexivity. }
      }
      { eapply View.join_r. }
    }
  Qed.

End MEMRA.

Global Opaque wmemory_black wpoints_to wpoints_to_faa wpoints_to_full.
