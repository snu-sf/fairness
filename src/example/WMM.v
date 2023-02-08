Unset Universe Checking.
From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Export ITreeLib WFLib FairBeh NatStructs Mod pind.
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
    ktree (((@eventE ident) +' cE) +' sE t) (View.t * Loc.t * Ordering.t) (View.t * Const.t) :=
    fun '(vw0, loc, ord) =>
      msc <- trigger (@Get _);;
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
    ktree (((@eventE ident) +' cE) +' sE t) (View.t * Loc.t * Const.t * Ordering.t) (View.t) :=
    fun '(vw0, loc, val, ord) =>
      msc <- trigger (@Get _);;
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
    ktree (((@eventE ident) +' cE) +' sE t) (View.t * Loc.t * Const.t * Ordering.t * Ordering.t) (View.t * Const.t) :=
    fun '(vw0, loc, addendum, ordr, ordw) =>
      msc <- trigger (@Get _);;
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

From Fairness Require Import PCM IProp IPM FairRA StateRA MonotonePCM.
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

  Lemma wmemory_ra_set
        m l c0 c1
    :
    (wmemory_black m)
      -∗
      (points_to l c0)
      -∗
      (#=> (wmemory_black (WMem.mk (LocFun.add l c1 m.(WMem.memory)) m.(WMem.sc)) ** points_to l c1)).
  Proof.
    iIntros "BLACK WHITE".
    unfold wmemory_black, points_to.
    iCombine "BLACK WHITE" as "OWN". iOwnWf "OWN".
    ur in H. specialize (H l).
    unfold memory_resource_black, points_to_white in H. des_ifs.
    ur in H. ur in H. des_ifs. des. rr in H. des. ur in H. des_ifs.
    iAssert (#=> OwnM (memory_resource_black (WMem.mk (LocFun.add l c1 m.(WMem.memory)) m.(WMem.sc)) ⋅ points_to_white l c1)) with "[OWN]" as "> [BLACK WHITE]".
    { iApply (OwnM_Upd with "OWN").
      ur. apply pointwise_updatabable. i.
      unfold memory_resource_black, points_to_white. ss.
      setoid_rewrite LocFun.add_spec. des_ifs.
      eapply Auth.auth_update. ii. des. split; ss.
      { ur. ss. }
      { ur in FRAME. ur. des_ifs. }
    }
    { iModIntro. iFrame. }
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
    iPoseProof (wmemory_ra_set with "BLACK WHITE") as "> [BLACK WHITE]".
    instantiate (1:=mem1 l). iModIntro. iSplitL "BLACK".
    { assert (EQ: mem1 = (LocFun.add l (mem1 l) (WMem.memory m0))).
      { inv MEM. extensionality l0. setoid_rewrite LocFun.add_spec. des_ifs.
        setoid_rewrite LocFun.add_spec_eq. auto.
      }
      iEval (rewrite EQ). auto.
    }
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
    iPoseProof (wmemory_ra_set with "BLACK WHITE") as "> [BLACK WHITE]".
    instantiate (1:=mem1 loc). iModIntro. iSplitL "BLACK".
    { assert (EQ: mem1 = (LocFun.add loc (mem1 loc) (WMem.memory msc))).
      { inv MEM. extensionality l0. setoid_rewrite LocFun.add_spec. des_ifs.
        setoid_rewrite LocFun.add_spec_eq. auto.
      }
      iEval (rewrite EQ). auto.
    }
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

  Context `{OBLGRA: @GRA.inG ObligationRA.t Σ}.
  Context `{ARROWRA: @GRA.inG (ArrowRA (void + WMem.ident)%type) Σ}.

  Definition wpoints_to_full (l: Loc.t) (V: View.t) (k: nat) (P Q: wProp) : iProp :=
    ∃ c,
      (points_to l c)
        **
        (∃ v released,
            (ObligationRA.correl (inr (inr (l, (Cell.max_ts c)))) k (Ord.S Ord.O))
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

  Lemma wmemory_ra_load_acq
        l V k (P Q: wProp)
        m val vw0 vw1
        ord lc1 to released
        (READ: Local.read_step (WMem.view_to_local vw0) m.(WMem.memory) l to val released ord lc1)
        (VIEW: vw1 = lc1.(Local.tview).(TView.cur))
        (ORD: ord = Ordering.acqrel)
    :
    (wmemory_black m)
      -∗
      (wpoints_to_full l V k P Q)
      -∗
      ((⌜View.le vw0 vw1⌝)
         ∗ (wmemory_black m)
         ∗ (wpoints_to_full l V k P Q)
         ∗ (((lift_wProp P val vw1)
               ∗ (∃ ts, (ObligationRA.correl (inr (inr (l, ts))) k (Ord.S Ord.O))
                          ∗ (⌜WMem.missed m.(WMem.memory) l to (l, ts) = Flag.fail⌝)))
            ∨ ((lift_wProp Q val vw1) ∗ (⌜View.le V vw1⌝)))
      ).
  Proof.
    iIntros "BLACK [% [WHITE [% [% [[[[#X Y] %] %] %]]]]]". des. subst.
    iPoseProof (wmemory_ra_get with "BLACK WHITE") as "%". subst.
    inv READ. ss. iSplit.
    { iPureIntro. aggrtac. }
    iSplitL "BLACK"; [auto|]. iSplitL.
    { iExists _. iFrame. iExists _, _. iSplit.
      { iSplit.
        { iSplit; auto. }
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
      iExists _. iSplitR; auto. iPureIntro.
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
    (wmemory_black m)
      -∗
      (wpoints_to_full l V k P Q)
      -∗
      (⌜View.le V vw0⌝)
      -∗
      ((⌜View.le vw0 vw1⌝)
         ∗ (wmemory_black m)
         ∗ (wpoints_to_full l V k P Q)
         ∗ (lift_wProp Q val vw1)
      ).
  Proof.
    iIntros "BLACK [% [WHITE [% [% [[[X %] %] Z]]]]] %". des. subst.
    iPoseProof (wmemory_ra_get with "BLACK WHITE") as "%". subst.
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
    (wmemory_black m0)
      -∗
      (wpoints_to_full l V k P Q)
      -∗
      (⌜View.le V vw0⌝)
      -∗
      (⌜R val vw0⌝)
      -∗
      ((⌜View.le vw0 vw1⌝)
         ∗ #=>((wmemory_black m1))
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
    iIntros "BLACK [% [WHITE [% [% [[[[#X Y] %] %] %]]]]] % %". des. subst.
    iPoseProof (wmemory_ra_get with "BLACK WHITE") as "%". subst.
    inv WRITE. ss. iSplit.
    { iPureIntro. aggrtac. }
    hexploit memory_write_bot_add; eauto. i. subst.
    inv WRITE0. inv PROMISE. clear REMOVE PROMISES ATTACH TS.
    iPoseProof (wmemory_ra_set with "BLACK WHITE") as "> [BLACK WHITE]".
    instantiate (1:=mem1 l). iModIntro. iSplitL "BLACK".
    { assert (EQ: mem1 = (LocFun.add l (mem1 l) (WMem.memory m0))).
      { inv MEM. extensionality l0. setoid_rewrite LocFun.add_spec. des_ifs.
        setoid_rewrite LocFun.add_spec_eq. auto.
      }
      iEval (rewrite EQ). auto.
    }


    iExists _,
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


    iSplitL "BLACK"; [auto|]. iSplitL.
    { iExists _. iFrame. iExists _, _. iSplit.
      { iSplit.
        { iSplit; auto. }
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
      iExists _. iSplitR; auto. iPureIntro.
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


  Admitted.

End MEMRA.

Global Opaque wmemory_black wpoints_to wpoints_to_faa wpoints_to_full.
