From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
Unset Universe Checking.
From Fairness Require Export
     ITreeLib WFLib FairBeh NatStructs Mod pind Axioms
     OpenMod WMM Red IRed Wrapper WeakestAdequacy.
From PromisingLib Require Import Loc Event.
From PromisingSEQ Require Import TView.
From Ordinal Require Export ClassicalHessenberg.
Require Import Coq.Numbers.BinNums.

Set Implicit Arguments.

Section INIT.

  Definition nat2c (n: nat): Const.t := Const.of_Z (BinIntDef.Z.of_nat n).

  Definition const_1: Const.t := nat2c 1.

End INIT.

Module TicketLockW.

  Definition tk := nat.

  Definition now_serving: Loc.t := Loc.of_nat 0.
  Definition next_ticket: Loc.t := Loc.of_nat 1.

  Definition lock_loop (myticket: Const.t) (tvw: TView.t):
    itree ((((@eventE void) +' cE) +' (sE unit)) +' OpenMod.callE) TView.t
    :=
    ITree.iter
      (fun (tvw: TView.t) =>
         '(tvw, now) <- (OMod.call "load" (tvw, now_serving, Ordering.acqrel));;
         b <- unwrap (Const.eqb myticket now);;
         if (b: bool) then Ret (inr tvw) else Ret (inl tvw)) tvw.

  Definition lock_fun:
    ktree ((((@eventE void) +' cE) +' (sE unit)) +' OpenMod.callE) TView.t TView.t :=
    fun tvw =>
      '(tvw, myticket) <- (OMod.call "faa" (tvw, next_ticket, const_1, Ordering.plain, Ordering.acqrel));;
      tvw <- lock_loop myticket tvw;;
      _ <- trigger Yield;;
      Ret tvw
  .

  Definition unlock_fun:
    ktree ((((@eventE void) +' cE) +' (sE unit)) +' OpenMod.callE) TView.t TView.t :=
    fun tvw =>
      '(tvw, v) <- (OMod.call "load" (tvw, now_serving, Ordering.relaxed));;
      let v := Const.add v const_1 in
      tvw <- (OMod.call "store" (tvw: TView.t, now_serving, v, Ordering.acqrel));;
      _ <- trigger Yield;;
      Ret tvw
  .

  Definition omod: OMod.t :=
    OMod.mk
      tt
      (Mod.get_funs [("lock", Mod.wrap_fun lock_fun);
                     ("unlock", Mod.wrap_fun unlock_fun)])
  .

  Definition mod: Mod.t :=
    OMod.close
      (omod)
      (WMem.mod)
  .

  Lemma lock_loop_red myticket tvw
    :
    lock_loop myticket tvw
    =
      '(tvw, now) <- (OMod.call "load" (tvw, now_serving, Ordering.acqrel));;
      b <- unwrap (Const.eqb myticket now);;
      if (b: bool)
      then Ret tvw else tau;; lock_loop myticket tvw.
  Proof.
    unfold lock_loop. etransitivity.
    { apply unfold_iter_eq. }
    grind.
  Qed.

End TicketLockW.



From Fairness Require Import IProp IPM Weakest.
From Fairness Require Import ModSim PCM MonotonePCM StateRA FairRA.
From Fairness Require Import FairLock.

Section AUX.

  Variant prod_le
          {A B: Type} {RA: A -> A -> Prop} {RB: B -> B -> Prop}
          (PRA: PartialOrder RA) (PRB: PreOrder RB) :
    (A * B) -> (A * B) -> Prop :=
    | prod_le_l
        a0 a1 b0 b1
        (ORD: RA a0 a1)
        (NEQ: a0 <> a1)
      :
      prod_le PRA PRB (a0, b0) (a1, b1)
    | prod_le_r
        a b0 b1
        (ORD: RB b0 b1)
      :
      prod_le PRA PRB (a, b0) (a, b1)
  .

  Global Program Instance prod_le_PreOrder
         {A B: Type} {RA: A -> A -> Prop} {RB: B -> B -> Prop}
         (PRA: PartialOrder RA) (PRB: PreOrder RB)
    : PreOrder (prod_le PRA PRB).
  Next Obligation.
    ii. destruct x. econs 2. inv PRB. auto.
  Qed.
  Next Obligation.
    ii. destruct x as [a0 b0], y as [a1 b1], z as [a2 b2].
    inv H.
    - inv H0.
      + econs 1; inv PRA.
        * inv partial_order_pre. eapply PreOrder_Transitive; eauto.
        * ii. clarify. apply NEQ0. apply partial_order_anti_symm; auto.
      + econs 1; auto.
    - inv H0.
      + econs 1; auto.
      + econs 2. inv PRB. eapply PreOrder_Transitive; eauto.
  Qed.

End AUX.

Module Tkst.
  Section TKST.

    Definition t X := (nat * X)%type.

    Definition le {X} (s0 s1: @t X): Prop :=
      let '(n0, x0) := s0 in
      let '(n1, x1) := s1 in
      (n0 <= n1) /\ (n0 = n1 -> x0 = x1).

    Global Program Instance le_PreOrder X: PreOrder (@le X).
    Next Obligation.
      ii. unfold le. des_ifs.
    Qed.
    Next Obligation.
      ii. unfold le in *. des_ifs. des; clarify. split; auto; try lia.
      i. clarify. assert (n0 = n1). lia. clarify. rewrite H2; auto.
    Qed.


    Definition a {X} x : t X := (1, x).
    Definition b {X} x : t X := (2, x).
    Definition c {X} x : t X := (3, x).
    Definition d {X} x : t X := (4, x).

  End TKST.
End Tkst.

Section TKQ.

  Inductive tkqueue
            (l: list thread_id) (tks: NatMap.t TicketLockW.tk) (inc exc: TicketLockW.tk)
    : Prop :=
  | tkqueue_nil
      (EMP1: l = [])
      (EMP2: tks = @NatMap.empty _)
      (EQ: inc = exc)
    :
    tkqueue l tks inc exc
  | tkqueue_cons
      hd tl
      (QUEUE: l = hd :: tl)
      (FIND: NatMap.find hd tks = Some inc)
      (TL: tkqueue tl (NatMap.remove hd tks) (S inc) exc)
    :
    tkqueue l tks inc exc
  .

  Lemma tkqueue_enqueue
        l tks inc exc
        (TQ: tkqueue l tks inc exc)
        k
        (FIND: NatMap.find k tks = None)
    :
    tkqueue (l ++ [k]) (NatMap.add k exc tks) inc (S exc).
  Proof.
    revert_until TQ. induction TQ; i; clarify; ss.
    { econs 2. ss. apply nm_find_add_eq. econs 1; auto. rewrite nm_find_none_rm_add_eq; auto. }
    assert (NEQ: hd <> k).
    { ii. clarify. }
    econs 2. instantiate (2:=hd). ss. rewrite nm_find_add_neq; auto.
    erewrite <- nm_find_none_add_rm_is_eq. eapply IHTQ.
    rewrite nm_find_rm_neq; auto. rewrite nm_find_add_neq; auto. apply nm_find_rm_eq.
    instantiate (1:=inc). rewrite nm_add_rm_comm_eq; auto.
    rewrite <- nm_find_some_rm_add_eq; auto. rewrite nm_find_add_neq; auto.
  Qed.

  Lemma tkqueue_dequeue
        l tks inc exc
        (TQ: tkqueue l tks inc exc)
        hd tl
        (HD: l = hd :: tl)
    :
    tkqueue tl (NatMap.remove hd tks) (S inc) exc.
  Proof.
    revert_until TQ. induction TQ; i; clarify; ss.
  Qed.

  Lemma tkqueue_range
        l tks inc exc
        (TQ: tkqueue l tks inc exc)
    :
    inc <= exc.
  Proof.
    induction TQ; i; clarify; ss. lia.
  Qed.

  Lemma tkqueue_val_range_l
        l tks inc exc
        (TQ: tkqueue l tks inc exc)
        t v
        (FIND: NatMap.find t tks = Some v)
    :
    inc <= v.
  Proof.
    revert_until TQ. induction TQ; i; clarify; ss.
    destruct (tid_dec t hd) eqn:DEC; clarify.
    hexploit (IHTQ t v). rewrite nm_find_rm_neq; auto. i. lia.
  Qed.

  Lemma tkqueue_val_range_r
        l tks inc exc
        (TQ: tkqueue l tks inc exc)
        t v
        (FIND: NatMap.find t tks = Some v)
    :
    v < exc.
  Proof.
    revert_until TQ. induction TQ; i; clarify; ss.
    destruct (tid_dec t hd) eqn:DEC; clarify.
    - eapply tkqueue_range in TQ. lia.
    - hexploit (IHTQ t v). rewrite nm_find_rm_neq; auto. i. lia.
  Qed.

  Lemma tkqueue_inv_unique
        l tks inc exc
        (TQ: tkqueue l tks inc exc)
        t0 t1 v
        (FIND0: NatMap.find t0 tks = Some v)
        (FIND1: NatMap.find t1 tks = Some v)
    :
    t0 = t1.
  Proof.
    revert_until TQ. induction TQ; i; clarify; ss.
    destruct (tid_dec t0 hd) eqn:DEC0; clarify; eauto.
    { destruct (tid_dec t1 hd) eqn:DEC1; clarify; eauto.
      hexploit tkqueue_val_range_l. eapply TQ. erewrite nm_find_rm_neq.
      2:{ ii. apply n. symmetry. eapply H. }
      eapply FIND1. i. lia.
    }
    { destruct (tid_dec t1 hd) eqn:DEC1; clarify; eauto.
      { hexploit tkqueue_val_range_l. eapply TQ. erewrite nm_find_rm_neq.
        2:{ ii. apply n. symmetry. eapply H. }
        eapply FIND0. i. lia.
      }
      eapply IHTQ; rewrite nm_find_rm_neq; eauto.
    }
  Qed.

  Lemma tkqueue_inv_hd
        l tks inc exc
        (TQ: tkqueue l tks inc exc)
        t
        (FIND: NatMap.find t tks = Some inc)
    :
    exists tl, l = t :: tl.
  Proof.
    revert_until TQ. induction TQ; i; clarify; ss.
    destruct (tid_dec t hd) eqn:DEC; clarify; eauto.
    hexploit tkqueue_inv_unique. 2: eapply FIND. 2: eapply FIND0.
    { instantiate (1:=exc). instantiate (1:=inc). instantiate (1:=hd :: tl).
      econs 2; eauto.
    }
    i; clarify.
  Qed.

  Lemma tkqueue_find_in
        l tks inc exc
        (TQ: tkqueue l tks inc exc)
        t v
        (FIND: NatMap.find t tks = Some v)
    :
    In t l.
  Proof.
    revert_until TQ. induction TQ; i; clarify; ss.
    destruct (tid_dec t hd) eqn:DEC; clarify; auto.
    right. hexploit (IHTQ t v). rewrite nm_find_rm_neq; auto. i. auto.
  Qed.

  Lemma tkqueue_in_find
        l tks inc exc
        (TQ: tkqueue l tks inc exc)
        t
        (IN: In t l)
    :
    exists v, NatMap.find t tks = Some v.
  Proof.
    revert_until TQ. induction TQ; i; clarify; ss. des; clarify; eauto.
    hexploit (IHTQ t IN). i. des. exists v. rewrite NatMapP.F.remove_o in H. des_ifs.
  Qed.

End TKQ.

Section AUX.

  Definition ord_ge: Ord.t -> Ord.t -> Prop := fun o1 o2 => Ord.le o2 o1.

  Global Program Instance ord_ge_PreOrder: PreOrder ord_ge.
  Next Obligation.
    ii. unfold ord_ge. reflexivity.
  Qed.
  Next Obligation.
    ii. unfold ord_ge in *. etrans; eauto.
  Qed.

End AUX.

Section SIM.

  Context `{Σ: GRA.t}.

  Context `{MONORA: @GRA.inG monoRA Σ}.
  Context `{THDRA: @GRA.inG ThreadRA Σ}.
  Context `{STATESRC: @GRA.inG (stateSrcRA (Mod.state AbsLockW.mod)) Σ}.
  Context `{STATETGT: @GRA.inG (stateTgtRA (OMod.closed_state TicketLockW.omod (WMem.mod))) Σ}.
  Context `{IDENTSRC: @GRA.inG (identSrcRA (Mod.ident AbsLockW.mod)) Σ}.
  Context `{IDENTTGT: @GRA.inG (identTgtRA (OMod.closed_ident TicketLockW.omod (WMem.mod))) Σ}.
  Context `{OBLGRA: @GRA.inG ObligationRA.t Σ}.
  Context `{ARROWRA: @GRA.inG (ArrowRA (OMod.closed_ident TicketLockW.omod (WMem.mod))) Σ}.
  Context `{EDGERA: @GRA.inG EdgeRA Σ}.
  Context `{ONESHOTSRA: @GRA.inG (@FiniteMap.t (OneShot.t unit)) Σ}.
  Context `{WMEMRA: @GRA.inG wmemRA Σ}.

  Context `{NATMAPRA: @GRA.inG (Auth.t (NatMapRA.t TicketLockW.tk)) Σ}.
  Context `{AUTHRA1: @GRA.inG (Auth.t (Excl.t nat)) Σ}.
  (* Context `{AUTHRA2: @GRA.inG (Auth.t (Excl.t (((nat * nat) * TView.t) * nat))) Σ}. *)
  Context `{AUTHRA2: @GRA.inG (Auth.t (Excl.t (((nat * nat) * TView.t)))) Σ}.
  Context `{IN2: @GRA.inG (thread_id ==> (Auth.t (Excl.t nat)))%ra Σ}.
  (* Context `{IN2: @GRA.inG (thread_id ==> (Auth.t (Excl.t (nat * Ord.t))))%ra Σ}. *)

  Let mypreord := prod_le_PreOrder nat_le_po (Tkst.le_PreOrder nat).
  Let wmpreord := prod_le_PreOrder nat_le_po (base.PreOrder_instance_0 nat).
  Let wopreord := prod_le_PreOrder nat_le_po (ord_ge_PreOrder).
  Variable monok: nat.
  Variable tk_mono: nat.
  Variable wm_mono: nat.
  Variable wo_mono: nat.

  (* Definition ticket_lock_inv_unlocking *)
  (*            (l: list thread_id) (tks: NatMap.t nat) (now next: nat) (myt: thread_id) : iProp := *)
  (*   (own_thread myt) *)
  (*     ∗ *)
  (*     (⌜tkqueue l tks (S now) next⌝) *)
  (*     ∗ *)
  (*     (natmap_prop_sum tks (fun th tk => FairRA.white th (Ord.from_nat (tk - (S now))))) *)
  (*     ∗ *)
  (*     (list_prop_sum (fun th => ((ObligationRA.duty (inl th) []) *)
  (*                               ∗ (∃ u, maps_to th (Auth.black (Excl.just u: Excl.t nat))))%I) l) *)
  (*     ∗ *)
  (*     (∃ (k: nat) (o: Ord.t), *)
  (*         (monoBlack monok mypreord (now, Tkst.d k)) *)
  (*           ∗ (ObligationRA.black k o) *)
  (*           ∗ (ObligationRA.pending k 1) *)
  (*           ∗ (ObligationRA.duty (inl myt) [(k, Ord.S Ord.O)]) *)
  (*     ) *)
  (* . *)

  Definition ticket_lock_inv_unlocking
             (l: list thread_id) (tks: NatMap.t nat) (now next: nat) (myt: thread_id) : iProp :=
    (own_thread myt)
      ∗
      (⌜tkqueue l tks (S now) next⌝)
      ∗
      (natmap_prop_sum tks (fun th tk => FairRA.white th (Ord.from_nat (tk - (S now)))))
      ∗
      (list_prop_sum (fun th => ((ObligationRA.duty (inl th) [])
                                ∗ (∃ u, maps_to th (Auth.black (Excl.just u: Excl.t nat))))%I) l)
      ∗
      (∃ (k: nat),
          (monoBlack monok mypreord (now, Tkst.c k))
      )
  .

  Definition ticket_lock_inv_unlocked0
             (l: list thread_id) (tks: NatMap.t nat) (now next: nat)
             (myt: thread_id) (V: TView.t) : iProp :=
    (OwnM (Auth.white (Excl.just (now, myt, V): Excl.t (nat * nat * TView.t)%type)))
      ∗
      (⌜(l = []) /\ (tks = @NatMap.empty _) /\ (now = next)⌝)
      ∗
      (∃ (k: nat),
          (monoBlack monok mypreord (now, Tkst.a k))
      )
  .

  Definition ticket_lock_inv_unlocked1
             (l: list thread_id) (tks: NatMap.t nat) (now next: nat)
             (myt: thread_id) (V: TView.t) (wo: Ord.t): iProp :=
    ∃ yourt waits,
      (OwnM (Auth.white (Excl.just (now, myt, V): Excl.t (nat * nat * TView.t)%type)))
        ∗
        (⌜(l = yourt :: waits)⌝)
        ∗
        (⌜tkqueue l tks now next⌝)
        ∗
        (natmap_prop_sum tks (fun th tk => FairRA.white th (Ord.from_nat (tk - (now)))))
        ∗
        (list_prop_sum (fun th => ((ObligationRA.duty (inl th) [])
                                  ∗ (∃ u, maps_to th (Auth.black (Excl.just u: Excl.t nat))))%I) waits)
        ∗
        (∃ (k: nat) (o: Ord.t) (u: nat),
            (monoBlack monok mypreord (now, Tkst.b k))
              ∗ (ObligationRA.black k o)
              ∗ (ObligationRA.pending k 1)
              ∗ (ObligationRA.duty (inl yourt) [(k, Ord.S Ord.O)])
              ∗ (ObligationRA.white k (((Ord.S Ord.O) × Ord.omega) × (Ord.from_nat u))%ord)
              ∗ (maps_to yourt (Auth.black (Excl.just u: Excl.t nat)))
              ∗ (ObligationRA.white k (((Ord.S Ord.O) × Ord.omega) × wo)%ord)
        )
  .

  Definition ticket_lock_inv_locked
             (l: list thread_id) (tks: NatMap.t nat) (now next: nat)
             (myt: thread_id) (V: TView.t) : iProp :=
    (OwnM (Auth.white (Excl.just (now, myt, V): Excl.t (nat * nat * TView.t)%type)))
      ∗
      (⌜tkqueue l tks (S now) next⌝)
      ∗
      (natmap_prop_sum tks (fun th tk => FairRA.white th (Ord.from_nat (tk - (S now)))))
      ∗
      (list_prop_sum (fun th => ((ObligationRA.duty (inl th) [])
                                ∗ (∃ u, maps_to th (Auth.black (Excl.just u: Excl.t nat))))%I) l)
      ∗
      (∃ (k: nat),
          (monoBlack monok mypreord (now, Tkst.c k))
      )
  .

  Definition ticket_lock_inv_tks
             (tks: NatMap.t nat) : iProp :=
    ((OwnM (Auth.black (Some tks: NatMapRA.t nat)))
       ∗ (FairRA.whites (fun id => (~ NatMap.In id tks)) Ord.omega)
       ∗ (natmap_prop_sum tks (fun tid tk => (own_thread tid)))
       ∗ (OwnMs (fun id => (~ NatMap.In id tks))
                ((Auth.black (Excl.just 0: Excl.t nat)) ⋅ (Auth.white (Excl.just 0: Excl.t nat))))
    )
  .

  Definition wP (n: nat): wProp := fun c _ => (⌜exists m, (c = nat2c m) /\ (m < n)⌝)%I.
  Definition wQ (n: nat) (svw: TView.t): wProp := fun c vw => (⌜(c = nat2c n) /\ (TView.le svw vw)⌝)%I.

  Definition ticket_lock_inv_mem
             (mem: WMem.t) (V: TView.t) (wk: nat) (wo: Ord.t) (svw: TView.t) (now next: nat) (myt: thread_id) : iProp :=
    ((wmemory_black mem)
       ∗ (wpoints_to_full TicketLockW.now_serving V wk (wP now) (wQ now svw))
       ∗ (wpoints_to_faa TicketLockW.next_ticket (nat2c next))
       ∗ (OwnM (Auth.black (Excl.just (now, myt, V): Excl.t (((nat * nat) * TView.t))%type)))
       ∗ (monoBlack tk_mono Nat.le_preorder now)
       ∗ (monoBlack wm_mono wmpreord (now, wk))
       ∗ (monoBlack wo_mono wopreord (now, wo))
       ∗ (ObligationRA.black wk wo)
       (* ∗ (∃ o, ObligationRA.black wk o) *)
    )
  .

  Definition ticket_lock_inv_state
             (mem: WMem.t) (own: bool) (svw: TView.t) (ing: bool) (tks: NatMap.t nat) : iProp :=
    ((St_tgt (tt, mem)) ∗ (St_src (((own, svw), ing), (key_set tks))))
  .

  Definition ticket_lock_inv : iProp :=
    ∃ (mem: WMem.t) (own ing: bool) (V svw: TView.t) (wk: nat) (wo: Ord.t)
      (l: list thread_id) (tks: NatMap.t nat) (now next: nat) (myt: thread_id),
      (ticket_lock_inv_tks tks)
        ∗
        ((ticket_lock_inv_mem mem V wk wo svw now next myt) ∗ (⌜TView.le V svw⌝))
        ∗
        ((ticket_lock_inv_state mem own svw ing tks))
        ∗
        (((⌜own = true⌝)
            ∗ (((⌜ing = false⌝) ∗ (ticket_lock_inv_locked l tks now next myt V))
               ∨
                 ((⌜ing = true⌝) ∗ (ticket_lock_inv_unlocking l tks now next myt))
              )
         )
         ∨
           ((⌜own = false⌝)
              ∗
              (⌜ing = false⌝)
              ∗ 
              ((ticket_lock_inv_unlocked0 l tks now next myt V)
               ∨
                 (ticket_lock_inv_unlocked1 l tks now next myt V wo))
        ))
  .

  Let I: list iProp := [ticket_lock_inv].

  (* Properties *)
  (* Lemma unlocking_mono *)
  (*       l tks now next myt: *)
  (*   (ticket_lock_inv_unlocking l tks now next myt) *)
  (*     -∗ *)
  (*     ((⌜tkqueue l tks (S now) next⌝) *)
  (*        ∗ *)
  (*        (∃ k o, (monoWhite monok mypreord (now, Tkst.d k)) *)
  (*                  ∗ (ObligationRA.black k o) *)
  (*     )). *)
  (* Proof. *)
  (*   iIntros "I". iDestruct "I" as "[_ [%I2 [_ [_ I]]]]". do 2 iDestruct "I" as "[% I]". *)
  (*   iDestruct "I" as "[MB [OB _]]". iPoseProof (black_white with "MB") as "#MYTURN". *)
  (*   iSplit. auto. iExists k, o. iFrame. auto. *)
  (* Qed. *)

  Lemma unlocking_contra
        tid l tks now next myt
        (FIND: NatMap.find tid tks = Some now)
    :
    (ticket_lock_inv_unlocking l tks now next myt)
      -∗ ⌜False⌝.
  Proof.
    iIntros "I". iDestruct "I" as "[_ [%I2 [_ [_ _]]]]". exfalso.
    hexploit (tkqueue_val_range_l I2 _ FIND). i. lia.
  Qed.

  Lemma unlocking_myturn
        tid l tks now next myt
        mytk o
        (FIND: NatMap.find tid tks = Some mytk)
    :
    (monoWhite monok mypreord (mytk, o))
      -∗
      (ticket_lock_inv_unlocking l tks now next myt)
      -∗ ⌜False⌝.
  Proof.
    iIntros "MYT I". iDestruct "I" as "[_ [%I2 [_ [_ I3]]]]".
    do 1 (iDestruct "I3" as "[% I3]").
    iPoseProof (black_white_compare with "MYT I3") as "%LE". exfalso.
    hexploit (tkqueue_val_range_l I2 _ FIND). i. inv LE; try lia.
  Qed.

  Lemma unlocked0_contra
        tid l tks now next myt mytk V
        (FIND: NatMap.find tid tks = Some mytk)
    :
    (ticket_lock_inv_unlocked0 l tks now next myt V)
      -∗ ⌜False⌝.
  Proof.
    iIntros "I". iDestruct "I" as "[_ [%I2 _]]". exfalso. des; clarify.
  Qed.

  Lemma unlocked1_mono
        l tks now next myt V wo:
    (ticket_lock_inv_unlocked1 l tks now next myt V wo)
      -∗
      ((⌜tkqueue l tks now next⌝)
         ∗
         (∃ k o, (monoWhite monok mypreord (now, Tkst.b k))
                   ∗ (ObligationRA.black k o)
      )).
  Proof.
    iIntros "I". do 2 iDestruct "I" as "[% I]". iDestruct "I" as "[_ [_ [%I3 [_ [_ I]]]]]".
    do 3 iDestruct "I" as "[% I]". iDestruct "I" as "[MB [OB _]]".
    iSplit. auto. iPoseProof (black_white with "MB") as "#MYTURN". iExists k, o. iFrame. auto.
  Qed.

  Lemma unlocked1_myturn
        tid l tks now next myt V wo
        mytk o
        (FIND: NatMap.find tid tks = Some mytk)
    :
    (monoWhite monok mypreord (mytk, o))
      -∗
      (ticket_lock_inv_unlocked1 l tks now next myt V wo)
      -∗ ⌜now = mytk⌝.
  Proof.
    iIntros "MYT I". do 2 iDestruct "I" as "[% I]". iDestruct "I" as "[_ [%I1 [%I2 [_ [_ I]]]]]".
    do 3 iDestruct "I" as "[% I]". iDestruct "I" as "[MB _]".
    iPoseProof (black_white_compare with "MYT MB") as "%LE".
    hexploit (tkqueue_val_range_l I2 _ FIND). i. inv LE; auto. lia.
  Qed.

  Lemma locked_contra
        tid l tks now next myt V
        (FIND: NatMap.find tid tks = Some now)
    :
    (ticket_lock_inv_locked l tks now next myt V)
      -∗ ⌜False⌝.
  Proof.
    iIntros "I". iDestruct "I" as "[_ [%I2 _]]". exfalso.
    hexploit (tkqueue_val_range_l I2 _ FIND). clear. i. lia.
  Qed.

  Lemma locked_myturn
        tid l tks now next myt V
        mytk o
        (FIND: NatMap.find tid tks = Some mytk)
    :
    (monoWhite monok mypreord (mytk, o))
      -∗
      (ticket_lock_inv_locked l tks now next myt V)
      -∗ ⌜False⌝.
  Proof.
    iIntros "MYT I". iDestruct "I" as "[_ [%I2 [_ [_ [% I3]]]]]".
    iPoseProof (black_white_compare with "MYT I3") as "%LE". exfalso.
    hexploit (tkqueue_val_range_l I2 _ FIND). i. inv LE; try lia.
  Qed.

  Lemma mytk_find_some tid mytk tks:
    (OwnM (Auth.white (NatMapRA.singleton tid mytk: NatMapRA.t nat)))
      ∗ (ticket_lock_inv_tks tks)
      -∗ ⌜NatMap.find tid tks = Some mytk⌝.
  Proof.
    iIntros "[MYTK TKS]". iDestruct "TKS" as "[TKS0 _]".
    iApply (NatMapRA_find_some with "TKS0 MYTK").
  Qed.

  Lemma ticket_lock_inv_mem_mono
        mem now next myt V wk wo svw
    :
    (ticket_lock_inv_mem mem V wk wo svw now next myt)
      -∗
      (monoWhite tk_mono Nat.le_preorder now).
  Proof.
    iIntros "MEM". iDestruct "MEM" as "[MEM0 [MEM1 [MEM2 [MEM3 [MEM4 MEM5]]]]]".
    iPoseProof (black_white with "MEM4") as "#MONOTK". auto.
  Qed.

  Lemma ticket_lock_inv_mem_mono2
        mem now next myt V wk wo svw
    :
    (ticket_lock_inv_mem mem V wk wo svw now next myt)
      -∗
      (monoWhite wm_mono wmpreord (now, wk)).
  Proof.
    iIntros "MEM". iDestruct "MEM" as "[MEM0 [MEM1 [MEM2 [MEM3 [MEM4 [MEM5 MEM6]]]]]]".
    iPoseProof (black_white with "MEM5") as "#MONOTK". auto.
  Qed.

  Lemma ticket_lock_inv_mem_mono3
        mem now next myt V wk wo svw
    :
    (ticket_lock_inv_mem mem V wk wo svw now next myt)
      -∗
      (monoWhite wo_mono wopreord (now, wo)).
  Proof.
    iIntros "MEM". iDestruct "MEM" as "[MEM0 [MEM1 [MEM2 [MEM3 [MEM4 [MEM5 [MEM6 MEM7]]]]]]]".
    iPoseProof (black_white with "MEM6") as "#MONOTK". auto.
  Qed.

  Lemma ticket_lock_inv_mem_blk
        mem now next myt V wk wo svw
    :
    (ticket_lock_inv_mem mem V wk wo svw now next myt)
      -∗
      (ObligationRA.black wk wo).
  Proof.
    iIntros "MEM". iDestruct "MEM" as "[MEM0 [MEM1 [MEM2 [MEM3 [MEM4 [MEM5 [MEM6 MEM7]]]]]]]". iFrame.
  Qed.

  Lemma ticket_lock_inv_mem_mono_fact1
        mem now0 now1 next myt V wk wo svw
    :
    (ticket_lock_inv_mem mem V wk wo svw now1 next myt)
      -∗
      (monoWhite tk_mono Nat.le_preorder now0)
     -∗ (⌜now0 <= now1⌝).
  Proof.
    iIntros "MEM WH". iDestruct "MEM" as "[MEM0 [MEM1 [MEM2 [MEM3 [MEM4 MEM5]]]]]".
    iPoseProof (black_white_compare with "WH MEM4") as "%FA". auto.
  Qed.

  Lemma ticket_lock_inv_mem_mono_fact2
        mem now next myt V wk0 wk1 wo svw
    :
    (ticket_lock_inv_mem mem V wk1 wo svw now next myt)
      -∗
      (monoWhite wm_mono wmpreord (now, wk0))
      -∗ (⌜wk0 = wk1⌝).
  Proof.
    iIntros "MEM WH". iDestruct "MEM" as "[MEM0 [MEM1 [MEM2 [MEM3 [MEM4 [MEM5 MEM6]]]]]]".
    iPoseProof (black_white_compare with "WH MEM5") as "%FA".
    inv FA. exfalso. lia. auto.
  Qed.

  Lemma ticket_lock_inv_mem_mono_fact3
        mem now next myt V wk wo0 wo1 svw
    :
    (ticket_lock_inv_mem mem V wk wo1 svw now next myt)
      -∗
      (monoWhite wo_mono wopreord (now, wo0))
      -∗ (⌜Ord.le wo1 wo0⌝).
  Proof.
    iIntros "MEM WH". iDestruct "MEM" as "[MEM0 [MEM1 [MEM2 [MEM3 [MEM4 [MEM5 [MEM6 MEM7]]]]]]]".
    iPoseProof (black_white_compare with "WH MEM6") as "%FA".
    inv FA. exfalso. lia. iPureIntro. unfold ord_ge in ORD. auto.
  Qed.

  (* Simulations *)
  Lemma lock_enqueue tid tvw:
    ((own_thread tid)
       ∗ (ObligationRA.duty (inl tid) [])
    )
      ∗
      (∀ mytk tview,
          (
            (OwnM (Auth.white (NatMapRA.singleton tid mytk: NatMapRA.t TicketLockW.tk)))
              ∗ (maps_to tid (Auth.white (Excl.just 1: Excl.t nat)))
              ∗ (⌜TView.le tvw tview⌝)
          )
            -∗
  (stsim I tid (topset I) ibot7 ibot7
         (λ r_src r_tgt : TView.t, (own_thread tid ** ObligationRA.duty (inl tid) []) ** ⌜r_src = r_tgt⌝)
         false false
    (ITree.iter
       (λ _ : (),
          trigger Yield;;;
          ` x_ : bool * TView.t * bool * NatMap.t () <- trigger (Get (bool * TView.t * bool * NatMap.t ()));;
          (let (y, _) := x_ in let (y1, _) := y in let (own, _) := y1 in if own then Ret (inl ()) else Ret (inr ()))) ();;;
     ` x_ : bool * TView.t * bool * NatMap.t () <- trigger (Get (bool * TView.t * bool * NatMap.t ()));;
     (let (y, ts) := x_ in
      let (y0, ing) := y in
      let (_, tvw_lock) := y0 in
      if ing
      then ` x : _ <- trigger (Choose void);; Empty_set_rect (λ _ : void, itree ((eventE +' cE) +' sE AbsLockW.st) TView.t) x
      else
       ` x_0 : {tvw' : TView.t | TView.le (TView.join tvw tvw_lock) tvw'} <-
       trigger (Choose {tvw' : TView.t | TView.le (TView.join tvw tvw_lock) tvw'});;
       (let (tvw', _) := x_0 in
        trigger (Put (true, tvw_lock, false, NatMap.remove (elt:=()) tid ts));;;
        trigger
          (Fair
             (λ i : nat,
                if tid_dec i tid
                then Flag.success
                else if NatMapP.F.In_dec (NatMap.remove (elt:=()) tid ts) i then Flag.fail else Flag.emp));;;
        trigger Yield;;; Ret tvw')))
    (` a : TView.t <- OMod.close_itree TicketLockW.omod WMem.mod (TicketLockW.lock_loop (nat2c mytk) tview);;
     OMod.close_itree TicketLockW.omod WMem.mod (trigger Yield;;; Ret a))
  )
      )
      ⊢
      (stsim I tid (topset I) ibot7 ibot7
             (fun r_src r_tgt => own_thread tid ** ObligationRA.duty (inl tid) [] ** ⌜r_src = r_tgt⌝)
             false false
             (AbsLockW.lock_fun tvw)
             (OMod.close_itree TicketLockW.omod (WMem.mod)
                               (TicketLockW.lock_fun tvw))).
  Proof.
    iIntros "[[MYTH DUTY] SIM]".
    unfold AbsLockW.lock_fun, TicketLockW.lock_fun. rred.
    rewrite close_itree_call. rred.
    iApply (stsim_sync with "[DUTY]"). msubtac. iFrame. iIntros "DUTY _".
    unfold Mod.wrap_fun, WMem.faa_fun. rred.
    iApply stsim_tidL. lred.

    iopen 0 "I" "K". do 12 iDestruct "I" as "[% I]". iDestruct "I" as "[TKS [MEM [ST CASES]]]".
    iDestruct "ST" as "[ST0 ST1]".
    iApply stsim_getL. iSplit. auto. iApply (stsim_putL with "ST1"). iIntros "ST1".

    iApply stsim_getR. iSplit. auto. rred. iApply stsim_tauR. rred.
    iDestruct "MEM" as "[MEM %VWLE]". iDestruct "MEM" as "[MEM0 [MEM1 [MEM2 MEM3]]]".
    iApply stsim_chooseR. iIntros "%".
    destruct x. destruct x as [[[[lc2 to] val] sc1] mem1]. des. rename y into READ, y0 into WRITE. rred.

    iPoseProof (wmemory_ra_faa with "MEM0 MEM2") as "[%FAA >[MEM0 MEM2]]".
    eapply READ. eapply WRITE. auto. auto.
    iApply stsim_tauR. rred.
    iApply stsim_fairR.
    { i. instantiate (1:= []). ss. clear - IN. unfold sum_fmap_r, sum_fmap_l, WMem.missed in IN. des_ifs. }
    { i. instantiate (1:=[]) in IN. inv IN. }
    { econs. }
    { auto. }
    iIntros "_ _". rred.
    iApply stsim_tauR. rred.
    iApply stsim_getR. iSplit. auto. rred.
    iApply (stsim_putR with "ST0"). iIntros "ST0". rred.
    iApply stsim_tauR. rred. iApply stsim_tauR. rred.

    iAssert (⌜NatMap.find tid tks = None⌝)%I as "%FINDNONE".
    { destruct (NatMap.find tid tks) eqn:FIND; auto.
      iDestruct "TKS" as "[_ [_ [YTH _]]]". iPoseProof (natmap_prop_sum_in with "YTH") as "FALSE".
      eauto. iPoseProof (own_thread_unique with "MYTH FALSE") as "%FALSE". auto.
    }

    iDestruct "TKS" as "[TKS0 [TKS1 [TKS2 TKS3]]]".
    set (tks' := NatMap.add tid next tks).
    iPoseProof (NatMapRA_add with "TKS0") as ">[TKS0 MYTK]". eauto. instantiate (1:=next).
    iAssert (St_src (own, svw, ing, (key_set tks')))%I with "[ST1]" as "ST1".
    { subst tks'. rewrite key_set_pull_add_eq. iFrame. }
    iPoseProof ((FairRA.whites_unfold (fun id => ~ NatMap.In id tks') _ (i:=tid)) with "TKS1") as "[TKS1 MYTRI]".
    { subst tks'. i. ss. des; clarify.
      - ii. apply IN. destruct (tid_dec j tid); clarify.
        apply NatMapP.F.not_find_in_iff in H; clarify. apply NatMapP.F.add_in_iff; auto.
      - apply NatMapP.F.not_find_in_iff; auto.
    }
    { subst tks'. ii. apply H. apply NatMapP.F.add_in_iff. auto. }

    iPoseProof ((OwnMs_unfold (fun id => ~ NatMap.In id tks') _ (i:=tid)) with "TKS3") as "[TKS3 MYNUM]".
    { subst tks'. i. ss. des; clarify.
      - ii. apply IN. destruct (tid_dec j tid); clarify.
        apply NatMapP.F.not_find_in_iff in H; clarify. apply NatMapP.F.add_in_iff; auto.
      - apply NatMapP.F.not_find_in_iff; auto.
    }
    { subst tks'. ii. apply H. apply NatMapP.F.add_in_iff. auto. }
    iPoseProof (OwnM_Upd with "MYNUM") as "> MYNUM".
    { eapply maps_to_updatable. apply Auth.auth_update.
      instantiate (1:=Excl.just 1). instantiate (1:=Excl.just 1).
      ii. des. ur in FRAME. des_ifs. split.
      { ur. ss. }
      { ur. ss. }
    }
    rewrite <- maps_to_res_add. iDestruct "MYNUM" as "[MYNB MYNW]".

    iAssert (natmap_prop_sum tks' (λ tid0 _ : nat, own_thread tid0))%I with "[MYTH TKS2]" as "TKS2".
    { subst tks'. iApply (natmap_prop_sum_add with "TKS2"). iFrame. }

    iDestruct "CASES" as "[[%TRUE [[%IF INV] | [%IT INV]]] | [%FALSE [%IF [INV | INV]]]]"; subst.
    { iPoseProof (FairRA.white_mon with "MYTRI") as ">MYTRI".
      { instantiate (1:=Ord.from_nat (next - (S now))). ss. apply Ord.lt_le. apply Ord.omega_upperbound. }
      iMod ("K" with "[DUTY TKS0 TKS1 TKS2 TKS3 MEM0 MEM1 MEM2 MEM3 INV ST0 ST1 MYTRI MYNB]") as "_".
      { subst tks'. unfold ticket_lock_inv.
        iExists _, true, false, V, svw, wk, wo. iExists (l ++ [tid]), (NatMap.add tid next tks), now, (S next), myt.
        iFrame.
        iSplitL "MEM2".
        { iSplit. 2: auto. replace (nat2c (S next)) with (Const.add (nat2c next) const_1). iFrame.
          unfold nat2c. ss. clear. unfold BinIntDef.Z.of_nat. des_ifs. ss. rewrite Z.add_comm. rewrite Pos2Z.add_pos_pos.
          rewrite Pplus_one_succ_l. econs.
        }
        iLeft. iSplit. auto. iLeft. iSplit. auto. unfold ticket_lock_inv_locked.
        iDestruct "INV" as "[INV0 [INV1 [INV2 [INV3 INV4]]]]". iFrame.
        iSplit.
        { iPure "INV1" as ?. iPureIntro. apply tkqueue_enqueue; auto. }
        iPoseProof (natmap_prop_sum_add with "INV2 MYTRI") as "INV2". iFrame.
        iApply list_prop_sum_add. iFrame. iExists 1. iFrame.
      }
      iApply stsim_reset. destruct lc2. ss. des. subst val. iApply "SIM". iFrame. auto.
    }

    { iPoseProof (FairRA.white_mon with "MYTRI") as ">MYTRI".
      { instantiate (1:=Ord.from_nat (next - (S now))). ss. apply Ord.lt_le. apply Ord.omega_upperbound. }
      iMod ("K" with "[DUTY TKS0 TKS1 TKS2 TKS3 MEM0 MEM1 MEM2 MEM3 INV ST0 ST1 MYTRI MYNB]") as "_".
      { subst tks'. unfold ticket_lock_inv.
        iExists _, true, true, V, svw, wk, wo. iExists (l ++ [tid]), (NatMap.add tid next tks), now, (S next), myt.
        remember (
    (⌜true = true⌝ **
     (⌜true = false⌝ ** ticket_lock_inv_locked (l ++ [tid]) (NatMap.add tid next tks) now (S next) myt V)
     ∨ (⌜true = true⌝ ** ticket_lock_inv_unlocking (l ++ [tid]) (NatMap.add tid next tks) now (S next) myt))
    ∨ (⌜true = false⌝ **
       (⌜true = false⌝ **
        ticket_lock_inv_unlocked0 (l ++ [tid]) (NatMap.add tid next tks) now (S next) myt V
        ∨ ticket_lock_inv_unlocked1 (l ++ [tid]) (NatMap.add tid next tks) now (S next) myt V wo))
          )%I as temp.
        iFrame. subst temp.
        iSplitL "MEM2".
        { iSplit. 2: auto. replace (nat2c (S next)) with (Const.add (nat2c next) const_1). iFrame.
          unfold nat2c. ss. clear. unfold BinIntDef.Z.of_nat. des_ifs. ss. rewrite Z.add_comm. rewrite Pos2Z.add_pos_pos.
          rewrite Pplus_one_succ_l. econs.
        }
        iLeft. iSplit. auto. iRight. iSplit. auto. unfold ticket_lock_inv_unlocking.
        iDestruct "INV" as "[INV0 [INV1 [INV2 [INV3 INV4]]]]". iFrame.
        iSplit.
        { iPure "INV1" as ?. iPureIntro. apply tkqueue_enqueue; auto. }
        iPoseProof (natmap_prop_sum_add with "INV2 MYTRI") as "INV2". iFrame.
        iApply list_prop_sum_add. iFrame. iExists 1. iFrame.
      }
      iApply stsim_reset. destruct lc2. ss. des. subst val. iApply "SIM". iFrame. auto.
    }

    { iPoseProof (FairRA.white_mon with "MYTRI") as ">MYTRI".
      { instantiate (1:=Ord.from_nat (next - (now))). ss. apply Ord.lt_le. apply Ord.omega_upperbound. }
      iPoseProof (ObligationRA.alloc
                    ((((Ord.S Ord.O) × Ord.omega) × (Ord.from_nat 2))
                       ⊕ (((Ord.S Ord.O) × Ord.omega) × wo))%ord) as "> [% [[OBLK OWHI] OPEND]]".
      iPoseProof (ObligationRA.white_split_eq with "OWHI") as "[OWHI WW]".
      iPoseProof (ObligationRA.white_eq with "OWHI") as "OWHI".
      { rewrite Ord.from_nat_S. rewrite Jacobsthal.mult_S. reflexivity. }
      iPoseProof (ObligationRA.white_split_eq with "OWHI") as "[OWHI TAX]".
      iPoseProof (ObligationRA.duty_alloc with "DUTY OWHI") as "> DUTY".
      unfold ticket_lock_inv_unlocked0. iDestruct "INV" as "[INV0 [% [% INV2]]]".
      iPoseProof ((black_updatable _ _ _ (now, Tkst.b k)) with "INV2") as ">INV2".
      { econs 2. ss. split; auto. i; ss. }

      iMod ("K" with "[DUTY TKS0 TKS1 TKS2 TKS3 MEM0 MEM1 MEM2 MEM3 INV0 INV2 ST0 ST1 MYTRI MYNB OBLK OPEND TAX WW]") as "_".
      { subst tks'. unfold ticket_lock_inv.
        iExists _, false, false, V, svw, wk, wo. iExists (l ++ [tid]), (NatMap.add tid next tks), now, (S next), myt.
        remember (
    (⌜true = true⌝ **
     (⌜true = false⌝ ** ticket_lock_inv_locked (l ++ [tid]) (NatMap.add tid next tks) now (S next) myt V)
     ∨ (⌜true = true⌝ ** ticket_lock_inv_unlocking (l ++ [tid]) (NatMap.add tid next tks) now (S next) myt))
    ∨ (⌜true = false⌝ **
       (⌜true = false⌝ **
        ticket_lock_inv_unlocked0 (l ++ [tid]) (NatMap.add tid next tks) now (S next) myt V
        ∨ ticket_lock_inv_unlocked1 (l ++ [tid]) (NatMap.add tid next tks) now (S next) myt V wo))
          )%I as temp.
        iFrame. subst temp.
        iSplitL "MEM2".
        { iSplit. 2: auto. replace (nat2c (S next)) with (Const.add (nat2c next) const_1). iFrame.
          unfold nat2c. ss. clear. unfold BinIntDef.Z.of_nat. des_ifs. ss. rewrite Z.add_comm. rewrite Pos2Z.add_pos_pos.
          rewrite Pplus_one_succ_l. econs.
        }
        iRight. iSplit. auto. iSplit. auto. iRight. unfold ticket_lock_inv_unlocked1.
        des; clarify. ss. iExists tid, []. ss. iFrame.
        iSplit; auto.
        iSplit.
        { iPureIntro. econs 2; eauto. apply NatMapP.F.add_eq_o; auto. econs 1; auto.
          apply nm_find_none_rm_add_eq. apply NatMapP.F.empty_o.
        }
        iSplitR. auto. iExists k, _, 1. iFrame.
      }
      iApply stsim_reset. destruct lc2. ss. des. subst val. iApply "SIM". iFrame. auto.
    }

    { iPoseProof (FairRA.white_mon with "MYTRI") as ">MYTRI".
      { instantiate (1:=Ord.from_nat (next - (now))). ss. apply Ord.lt_le. apply Ord.omega_upperbound. }
      iMod ("K" with "[DUTY TKS0 TKS1 TKS2 TKS3 MEM0 MEM1 MEM2 MEM3 INV ST0 ST1 MYTRI MYNB]") as "_".
      { subst tks'. unfold ticket_lock_inv.
        iExists _, false, false, V, svw, wk, wo. iExists (l ++ [tid]), (NatMap.add tid next tks), now, (S next), myt.
        remember (
    (⌜true = true⌝ **
     (⌜true = false⌝ ** ticket_lock_inv_locked (l ++ [tid]) (NatMap.add tid next tks) now (S next) myt V)
     ∨ (⌜true = true⌝ ** ticket_lock_inv_unlocking (l ++ [tid]) (NatMap.add tid next tks) now (S next) myt))
    ∨ (⌜true = false⌝ **
       (⌜true = false⌝ **
        ticket_lock_inv_unlocked0 (l ++ [tid]) (NatMap.add tid next tks) now (S next) myt V
        ∨ ticket_lock_inv_unlocked1 (l ++ [tid]) (NatMap.add tid next tks) now (S next) myt V wo))
          )%I as temp.
        iFrame. subst temp.
        iSplitL "MEM2".
        { iSplit. 2: auto. replace (nat2c (S next)) with (Const.add (nat2c next) const_1). iFrame.
          unfold nat2c. ss. clear. unfold BinIntDef.Z.of_nat. des_ifs. ss. rewrite Z.add_comm. rewrite Pos2Z.add_pos_pos.
          rewrite Pplus_one_succ_l. econs.
        }
        iRight. iSplit; auto. iSplit. auto. iRight. unfold ticket_lock_inv_unlocked1.
        do 2 iDestruct "INV" as "[% INV]".
        iDestruct "INV" as "[INV0 [% [INV2 [INV3 [INV4 INV5]]]]]". subst.
        iExists yourt, (waits ++ [tid]). ss. iFrame.
        iSplit. auto.
        iSplit.
        { iPure "INV2" as ?. iPureIntro. rewrite app_comm_cons. apply tkqueue_enqueue; auto. }
        iPoseProof (natmap_prop_sum_add with "INV3 MYTRI") as "INV3". iFrame.
        iApply list_prop_sum_add. iFrame. iExists 1. iFrame.
      }
      iApply stsim_reset. destruct lc2. ss. des. subst val. iApply "SIM". iFrame. auto.
    }
  Qed.

  Lemma lock_myturn_yieldR
        (g0 g1 : ∀ R_src R_tgt : Type,
            (R_src → R_tgt → iProp)
            → bool
            → bool
            → itree ((eventE +' cE) +' sE (Mod.state AbsLockW.mod)) R_src
            → itree
                ((eventE +' cE) +'
                                   sE (OMod.closed_state TicketLockW.omod (WMem.mod))) R_tgt
            → iProp)
        (ps pt: bool)
        (src: itree ((eventE +' cE) +' sE (Mod.state AbsLockW.mod)) TView.t)
        (tgt: itree ((eventE +' cE) +' sE (OMod.closed_state TicketLockW.omod (WMem.mod))) TView.t)
        (tid mytk u: nat)
        x
    :
    (
      (OwnM (Auth.white ((NatMapRA.singleton tid mytk: NatMapRA.t TicketLockW.tk))))
        ∗ (maps_to tid (Auth.white (Excl.just (S u): Excl.t nat)))
        ∗ (monoWhite monok mypreord (mytk, x))
    )
      ∗
      (
      ((OwnM (Auth.white ((NatMapRA.singleton tid mytk: NatMapRA.t TicketLockW.tk))))
        ∗ (maps_to tid (Auth.white (Excl.just u: Excl.t nat)))
        ∗ (monoWhite monok mypreord (mytk, x)))
        -∗
  (stsim I tid (topset I) g0 g1
    (λ r_src r_tgt : TView.t, (own_thread tid ** ObligationRA.duty (inl tid) []) ** ⌜r_src = r_tgt⌝)
    ps true
    (trigger Yield;;; src)
    (tgt))
      )
      ⊢
  (stsim I tid (topset I) g0 g1
    (λ r_src r_tgt : TView.t, (own_thread tid ** ObligationRA.duty (inl tid) []) ** ⌜r_src = r_tgt⌝)
    ps pt
    (trigger Yield;;; src)
    (trigger Yield;;; tgt)).
  Proof.
    iIntros "[[MYTK [MYNW MYTURN]] SIM]".
    iopen 0 "I" "K". do 12 iDestruct "I" as "[% I]". iDestruct "I" as "[TKS [MEM [ST CASES]]]".
    iPoseProof (mytk_find_some with "[MYTK TKS]") as "%FIND". iFrame.
    iDestruct "CASES" as "[[%CT [[% I] | [% I]]] | [%CF [%CF2 [I | I]]]]".
    { iPoseProof (locked_myturn with "MYTURN I") as "%FF". eauto. inv FF. }
    { iPoseProof (unlocking_myturn with "MYTURN I") as "%FF". eauto. inv FF. }
    { iPoseProof (unlocked0_contra with "I") as "%FF". eauto. inv FF. }
    iPoseProof (unlocked1_myturn with "MYTURN I") as "%EQ". eauto. subst mytk.
    do 2 iDestruct "I" as "[% I]". iDestruct "I" as "[I0 [% [%I2 [I3 [I4 I5]]]]]".
    do 3 iDestruct "I5" as "[% I5]". iDestruct "I5" as "[I5 I6]".
    iDestruct "I6" as "[I6 [I7 [I8 [I9 [I10 I11]]]]]".
    hexploit (tkqueue_inv_hd I2 _ FIND). i. des.
    inv H. symmetry in H1. inv H1.

    iCombine "I10 MYNW" as "MYNUM".
    iPoseProof (OwnM_valid with "MYNUM") as "%EQ".
    assert (u0 = S u).
    { clear -EQ. ur in EQ. specialize (EQ tid). unfold maps_to_res in EQ.
      des_ifs. ur in EQ. des. rr in EQ. des. ur in EQ. des_ifs.
    }
    subst u0. clear EQ.
    iPoseProof (OwnM_Upd with "MYNUM") as "> MYNUM".
    { rewrite maps_to_res_add. eapply maps_to_updatable. eapply Auth.auth_update.
      instantiate (1:=Excl.just u). instantiate (1:=Excl.just u).
      ii. des. ur in FRAME. des_ifs. split; ur; ss.
    }
    rewrite <- maps_to_res_add. iDestruct "MYNUM" as "[I10 MYNW]".

    iPoseProof (ObligationRA.white_eq with "I9") as "I9".
    { rewrite Ord.from_nat_S. rewrite Jacobsthal.mult_S. reflexivity. }
    iPoseProof (ObligationRA.white_split_eq with "I9") as "[TAX I9]".
    iApply (stsim_yieldR_strong with "[I8 TAX]").
    { iFrame. iApply ObligationRA.tax_cons_fold. iFrame. }
    iIntros "I8 _".
    iMod ("K" with "[TKS MEM ST I0 I3 I4 I5 I6 I7 I8 I9 I10 I11]") as "_".
    { unfold ticket_lock_inv. iExists mem, false, false, V, svw, wk, wo. iExists (tid :: tl), tks, now, next, myt.
      remember (
    (⌜false = true⌝ **
     (⌜false = false⌝ ** ticket_lock_inv_locked (tid :: tl) tks now next myt V)
     ∨ (⌜false = true⌝ ** ticket_lock_inv_unlocking (tid :: tl) tks now next myt))
    ∨ (⌜false = false⌝ **
       (⌜false = false⌝ **
        ticket_lock_inv_unlocked0 (tid :: tl) tks now next myt V ∨ ticket_lock_inv_unlocked1 (tid :: tl) tks now next myt V wo))
        )%I as temp.
      iFrame. subst temp.
      iRight. iSplit. auto. iSplit. auto. iRight.
      iExists tid, tl. iFrame. iSplit. auto. iSplit. auto.
      iExists k, o, u. iFrame.
    }
    iModIntro. iApply "SIM". iFrame.
  Qed.

  Lemma lock_yourturn_yieldR
        (g0 g1 : ∀ R_src R_tgt : Type,
            (R_src → R_tgt → iProp)
            → bool
            → bool
            → itree ((eventE +' cE) +' sE (Mod.state AbsLockW.mod)) R_src
            → itree
                ((eventE +' cE) +'
                                   sE (OMod.closed_state TicketLockW.omod (WMem.mod))) R_tgt
            → iProp)
        (ps pt: bool)
        (src: itree ((eventE +' cE) +' sE (Mod.state AbsLockW.mod)) TView.t)
        (tgt: itree ((eventE +' cE) +' sE (OMod.closed_state TicketLockW.omod (WMem.mod))) TView.t)
        (tid mytk now: nat)
        tks mem next l myt own V wk svw ing
        (VW: TView.le V svw)
        (NEQ: mytk <> now)
        wo
    :
  (OwnM (Auth.white (NatMapRA.singleton tid mytk: NatMapRA.t nat)) **
    (ticket_lock_inv_tks tks **
     (ticket_lock_inv_mem mem V wk wo svw now next myt **
      (ticket_lock_inv_state mem own svw ing tks **
       ((⌜own = true⌝ **
           (⌜ing = false⌝ ** ticket_lock_inv_locked l tks now next myt V)
           ∨ (⌜ing = true⌝ ** ticket_lock_inv_unlocking l tks now next myt))
          ∨ (⌜own = false⌝ **
             (⌜ing = false⌝ ** ticket_lock_inv_unlocked0 l tks now next myt V ∨ ticket_lock_inv_unlocked1 l tks now next myt V wo)) **
        (ticket_lock_inv -*
         MUpd (nth_default True%I I)
           (fairI (ident_tgt:=OMod.closed_ident TicketLockW.omod (WMem.mod))) []
           [0] True))))))
      ∗
      (((OwnM (Auth.white ((NatMapRA.singleton tid mytk: NatMapRA.t nat))))
          ∗ (FairRA.white_thread (_Id:=_)))
        -∗
  (stsim I tid (topset I) g0 g1
    (λ r_src r_tgt : TView.t, (own_thread tid ** ObligationRA.duty (inl tid) []) ** ⌜r_src = r_tgt⌝)
    ps true
    (trigger Yield;;; src)
    (tgt))
      )
      ⊢
  (stsim I tid [] g0 g1
    (λ r_src r_tgt : TView.t, (own_thread tid ** ObligationRA.duty (inl tid) []) ** ⌜r_src = r_tgt⌝)
    ps pt
    (trigger Yield;;; src)
    (trigger Yield;;; tgt)).
  Proof.
    iIntros "[[MYTH [TKS [MEM [ST [CASES K]]]]] SIM]".
    iPoseProof (mytk_find_some with "[MYTH TKS]") as "%FIND". iFrame.
    iDestruct "CASES" as "[[CT [[IF INV] | [IT INV]]]|[CF [IF [INV | INV]]]]".
    { unfold ticket_lock_inv_locked. iDestruct "INV" as "[INV0 [%INV1 [INV2 [INV3 INV4]]]]".
      hexploit (tkqueue_find_in INV1 _ FIND). i.
      iPoseProof (list_prop_sum_in_split with "INV3") as "[[DUTY MAPS] INV3]". eapply H.
      iApply (stsim_yieldR_strong with "[DUTY]"). iFrame. iIntros "DUTY RIGHT".
      iMod ("K" with "[TKS MEM ST CT IF INV0 INV2 INV4 MAPS INV3 DUTY]") as "_".
      { unfold ticket_lock_inv. iExists mem, own, ing, V, svw, wk, wo. iExists l, tks, now, next, myt.
        remember (
    (⌜own = true⌝ **
     (⌜ing = false⌝ ** ticket_lock_inv_locked l tks now next myt V) ∨ (⌜ing = true⌝ ** ticket_lock_inv_unlocking l tks now next myt))
    ∨ (⌜own = false⌝ **
          (⌜ing = false⌝ ** ticket_lock_inv_unlocked0 l tks now next myt V ∨ ticket_lock_inv_unlocked1 l tks now next myt V wo))
          )%I as temp.
        iFrame. iSplit. auto. subst temp.
        iLeft. iSplit. auto. iFrame. iLeft. iSplit. auto. iFrame. iSplit. auto. iApply "INV3". iFrame.
      }
      iModIntro. iApply "SIM". iFrame.
    }
    { iDestruct "INV" as "[INV0 [%INV1 [INV2 [INV3 INV4]]]]".
      hexploit (tkqueue_find_in INV1 _ FIND). i.
      iPoseProof (list_prop_sum_in_split with "INV3") as "[[DUTY MAPS] INV3]". eapply H.
      iApply (stsim_yieldR_strong with "[DUTY]"). iFrame. iIntros "DUTY RIGHT".
      iMod ("K" with "[TKS MEM ST CT IT INV0 INV2 INV4 MAPS INV3 DUTY]") as "_".
      { iExists mem, own, ing, V, svw, wk, wo. iExists l, tks, now, next, myt.
        remember (
    (⌜own = true⌝ **
     (⌜ing = false⌝ ** ticket_lock_inv_locked l tks now next myt V) ∨ (⌜ing = true⌝ ** ticket_lock_inv_unlocking l tks now next myt))
    ∨ (⌜own = false⌝ **
            (⌜ing = false⌝ ** ticket_lock_inv_unlocked0 l tks now next myt V ∨ ticket_lock_inv_unlocked1 l tks now next myt V wo))
          )%I as temp.
        iFrame. iSplit. auto. subst temp.
        iLeft. iSplit. auto. iFrame. iRight. iSplit. auto. iFrame. iSplit. auto. iApply "INV3". iFrame.
      }
      iModIntro. iApply "SIM". iFrame.
    }
    { iDestruct "INV" as "[INV0 [%INV1 INV2]]". exfalso. des; clarify. }
    { do 2 iDestruct "INV" as "[% INV]".
      iDestruct "INV" as "[INV0 [%INV1 [%INV2 [INV3 [INV4 INV5]]]]]".
      hexploit (tkqueue_dequeue INV2). eapply INV1. i.
      assert (NOTMT: tid <> yourt).
      { ii. clarify. inv INV2; ss. clarify. setoid_rewrite FIND in FIND0. inv FIND0. ss. }
      hexploit (tkqueue_find_in H).
      { instantiate (1:=mytk). instantiate (1:=tid). rewrite nm_find_rm_neq; auto. }
      intro IN.
      iPoseProof (list_prop_sum_in_split with "INV4") as "[[DUTY MAPS] INV4]". eapply IN.
      iApply (stsim_yieldR_strong with "[DUTY]"). iFrame. iIntros "DUTY RIGHT".
      iMod ("K" with "[TKS MEM ST CF IF INV0 INV3 INV5 MAPS INV4 DUTY]") as "_".
      { iExists mem, own, ing, V, svw, wk, wo. iExists l, tks, now, next, myt.
        remember (
    (⌜own = true⌝ **
     (⌜ing = false⌝ ** ticket_lock_inv_locked l tks now next myt V) ∨ (⌜ing = true⌝ ** ticket_lock_inv_unlocking l tks now next myt))
    ∨ (⌜own = false⌝ **
           (⌜ing = false⌝ ** ticket_lock_inv_unlocked0 l tks now next myt V ∨ ticket_lock_inv_unlocked1 l tks now next myt V wo))
          )%I as temp.
        iFrame. iSplit. auto. subst temp.
        iRight. iSplit. auto. iSplit. auto. iRight. iFrame. iExists yourt, waits.
        iSplit. auto. iSplit. auto. iFrame. iApply "INV4". iFrame.
      }
      iModIntro. iApply "SIM". iFrame.
    }
  Qed.

  Lemma lock_myturn0
        (g0 g1 : ∀ R_src R_tgt : Type,
            (R_src → R_tgt → iProp)
            → bool
            → bool
            → itree ((eventE +' cE) +' sE (Mod.state AbsLockW.mod)) R_src
            → itree ((eventE +' cE) +' sE (OMod.closed_state TicketLockW.omod (WMem.mod))) R_tgt → iProp)
        (ps pt: bool)
        (tid: nat)
        (now: TicketLockW.tk)
        x
        (* tx *)
        (* (TX: 1 <= tx) *)
        (tvw tview : TView.t)
        (TVLE : TView.le tvw tview)
        ph
    :
    ((monoWhite monok mypreord (now, x))
       ∗ (OwnM (Auth.white (NatMapRA.singleton tid now: NatMapRA.t nat)))
       ∗ (maps_to tid (Auth.white (Excl.just ph: Excl.t nat))))
       (* ∗ (maps_to tid (Auth.white (Excl.just tx: Excl.t nat)))) *)
  ⊢ stsim I tid (topset I) g0 g1
      (λ r_src r_tgt : TView.t, (own_thread tid ** ObligationRA.duty (inl tid) []) ** ⌜r_src = r_tgt⌝)
      ps pt
      (trigger Yield;;;
       ` x : () + () <-
       (` x_ : bool * TView.t * bool * NatMap.t () <- trigger (Get (bool * TView.t * bool * NatMap.t ()));;
        (let (y, _) := x_ in let (y1, _) := y in let (own0, _) := y1 in if own0 then Ret (inl ()) else Ret (inr ())));;
       match x with
       | inl l0 =>
           tau;; ITree.iter
                   (λ _ : (),
                      trigger Yield;;;
                      ` x_ : bool * TView.t * bool * NatMap.t () <- trigger (Get (bool * TView.t * bool * NatMap.t ()));;
                      (let (y, _) := x_ in let (y1, _) := y in let (own0, _) := y1 in if own0 then Ret (inl ()) else Ret (inr ())))
                   l0
       | inr r0 => Ret r0
       end;;;
       ` x_ : bool * TView.t * bool * NatMap.t () <- trigger (Get (bool * TView.t * bool * NatMap.t ()));;
       (let (y, ts) := x_ in
        let (y0, ing0) := y in
        let (_, tvw_lock) := y0 in
        if ing0
        then ` x1 : void <- trigger (Choose void);; Empty_set_rect (λ _ : void, itree ((eventE +' cE) +' sE AbsLockW.st) TView.t) x1
        else
         ` x_0 : {tvw' : TView.t | TView.le (TView.join tvw tvw_lock) tvw'} <-
         trigger (Choose {tvw' : TView.t | TView.le (TView.join tvw tvw_lock) tvw'});;
         (let (tvw', _) := x_0 in
          trigger (Put (true, tvw_lock, false, NatMap.remove (elt:=()) tid ts));;;
          trigger
            (Fair
               (λ i : nat,
                  if tid_dec i tid
                  then Flag.success
                  else if NatMapP.F.In_dec (NatMap.remove (elt:=()) tid ts) i then Flag.fail else Flag.emp));;;
          trigger Yield;;; Ret tvw')))
      (` r : Any.t <-
       OMod.embed_itree TicketLockW.omod WMem.mod
         (Mod.wrap_fun WMem.load_fun (Any.upcast (tview, TicketLockW.now_serving, Ordering.acqrel)));;
       ` x : TView.t * Const.t <- (tau;; unwrap (Any.downcast r));;
       ` x0 : TView.t <-
       OMod.close_itree TicketLockW.omod WMem.mod
         (let (tvw0, now0) := x in
          ` b : bool <- unwrap match now0 with
                               | Const.num b => Some (BinIntDef.Z.of_nat now =? b)%Z
                               | Const.undef => None
                               end;; (if b then Ret tvw0 else tau;; TicketLockW.lock_loop (nat2c now) tvw0));;
       OMod.close_itree TicketLockW.omod WMem.mod (trigger Yield;;; Ret x0)).
  Proof.
    iIntros "[#MYTN [MYTK MYNU]]".
    iopen 0 "I" "K". do 12 iDestruct "I" as "[% I]". iDestruct "I" as "[TKS [MEM [ST CASES]]]".
    iPoseProof (mytk_find_some with "[MYTK TKS]") as "%FIND". iFrame.
    iDestruct "CASES" as "[[%CT [[% I] | [% I]]] | [%CF [% [I | I]]]]".
    { iPoseProof (locked_myturn with "MYTN I") as "%FF". eauto. inv FF. }
    { iPoseProof (unlocking_myturn with "MYTN I") as "%FF". eauto. inv FF. }
    { iPoseProof (unlocked0_contra with "I") as "%FF". eauto. inv FF. }
    iPoseProof (unlocked1_myturn with "MYTN I") as "%EQ". eauto. subst now0.

    iDestruct "MEM" as "[MEM SVLE]".
    iPoseProof (ticket_lock_inv_mem_blk with "MEM") as "#INDB".
    iPoseProof (ticket_lock_inv_mem_mono2 with "MEM") as "#INDK".
    iPoseProof (ticket_lock_inv_mem_mono3 with "MEM") as "#INDO".
    iMod ("K" with "[TKS MEM SVLE ST I]") as "_".
    { unfold ticket_lock_inv. iExists mem, own, ing, V, svw, wk, wo. iExists l, tks, now, next, myt.
      iSplitL "TKS". iFrame. iSplitL "MEM SVLE". iFrame. iSplitL "ST". iFrame. iRight. iSplit; auto.
    }

    revert TVLE. clear_upto I. i. move tid before g1. move now before tid. move wk before now. move wo before wk.
    iStopProof. revert_until wo. pattern wo. revert wo.
    apply (well_founded_induction Ord.lt_well_founded).
    intros wo IHo. intros.
    iIntros "[#[MYTN [INDB [INDK INDO]]] [MYTK MYNU]]".

    iopen 0 "I" "K". do 12 iDestruct "I" as "[% I]". iDestruct "I" as "[TKS [MEM [ST CASES]]]".
    iPoseProof (mytk_find_some with "[MYTK TKS]") as "%FIND". iFrame.
    iDestruct "CASES" as "[[%CT [[% I] | [% I]]] | [%CF [% [I | I]]]]".
    { iPoseProof (locked_myturn with "MYTN I") as "%FF". eauto. inv FF. }
    { iPoseProof (unlocking_myturn with "MYTN I") as "%FF". eauto. inv FF. }
    { iPoseProof (unlocked0_contra with "I") as "%FF". eauto. inv FF. }
    iPoseProof (unlocked1_myturn with "MYTN I") as "%EQ". eauto. subst now0. subst.

    iDestruct "MEM" as "[MEM %SVLE]".
    iPoseProof (ticket_lock_inv_mem_mono_fact2 with "MEM INDK") as "%EQ". subst wk0.
    iPoseProof (ticket_lock_inv_mem_mono_fact3 with "MEM INDO") as "%WOLE".
    iClear "INDB". iPoseProof (ticket_lock_inv_mem_blk with "MEM") as "#INDB".
    iClear "INDO".

    unfold Mod.wrap_fun, WMem.load_fun. rred.
    iDestruct "MEM" as "[MEM0 [MEM1 [MEM2 MEM3]]]". iDestruct "ST" as "[ST0 ST1]".
    iApply stsim_getR. iSplit. eauto. rred.
    iApply stsim_tauR. rred.
    iApply stsim_chooseR. iIntros. destruct x0. destruct x0 as [[lc1 val] to]. des. rred. rename y into READ.
    iApply stsim_tauR. rred.
    iPoseProof (wmemory_ra_load_acq with "MEM0 MEM1") as "[%RVLE [MEM0 [MEM1 WCASES]]]".
    eapply READ. eauto. auto.
    iDestruct "WCASES" as "[[%WP [% [#WCOR %MISSED]]] | [%WQ %VVLE]]".

    { iApply stsim_fairR.
      { i. instantiate (1:=[]). exfalso. clear - IN. unfold sum_fmap_r, WMem.missed in IN. des_ifs. }
      { i. instantiate (1:=[inr (TicketLockW.now_serving, ts)]) in IN. inv IN. ss. inv H. }
      { econs. ii. inv H. econs. }
      { ss. }
      iIntros "_ RIGHT". iDestruct "RIGHT" as "[RIGHT _]". clear MISSED.
      rred. iApply stsim_tauR. rred. iApply stsim_tauR. rred.
      des. subst val. rred.
      destruct (BinIntDef.Z.of_nat now =? BinIntDef.Z.of_nat m)%Z eqn:IF.
      { exfalso. clear - IF WP1. apply Z.eqb_eq in IF. apply Nat2Z.inj_iff in IF. lia. }
      rred. iApply stsim_tauR. rred.

      rewrite TicketLockW.lock_loop_red. rred. rewrite close_itree_call. rred.
      iPoseProof (ObligationRA.correl_correlate with "WCOR RIGHT") as ">[DROP | CONTRA]".
      2:{ iPoseProof (wpoints_to_full_not_shot with "[MEM1 CONTRA]") as "%FF". iFrame. inv FF. }
      iPoseProof (ObligationRA.black_white_decr_one with "INDB DROP") as ">[% [#INDB2 %LT]]".

      do 2 iDestruct "I" as "[% I]". iDestruct "I" as "[I0 [%I1 [%I2 [I3 [I4 I5]]]]]".
      do 3 iDestruct "I5" as "[% I5]". iDestruct "I5" as "[I5 [I6 [I7 [I8 [I9 [I10 I11]]]]]]".
      assert (SUBST: Ord.le ((Ord.S Ord.O) ⊕ o0)%ord wo0).
      { clear - LT. apply Ord.S_supremum in LT. rewrite Hessenberg.add_S_l. rewrite Hessenberg.add_O_l. auto. }
      iPoseProof (ObligationRA.white_mon with "I11") as ">I11".
      { instantiate (1:= ((Ord.S Ord.O × Ord.omega) ⊕ ((Ord.S Ord.O × Ord.omega) × o0))%ord).
        etrans.
        2:{ instantiate (1:= (((Ord.S Ord.O × Ord.omega) × (Ord.S Ord.O)) ⊕ ((Ord.S Ord.O × Ord.omega) × o0))%ord).
            etrans.
            2:{ instantiate (1:= ((Ord.S Ord.O × Ord.omega) × (Ord.S Ord.O ⊕ o0))%ord). apply Jacobsthal.le_mult_r. auto. }
            remember (Ord.S Ord.O) as one. remember (one × Ord.omega)%ord as omg. rewrite ClassicJacobsthal.mult_dist.
            reflexivity.
        }
        apply Hessenberg.le_add_l. rewrite Jacobsthal.mult_1_r. reflexivity.
      }
      iPoseProof (ObligationRA.white_split_eq with "I11") as "[TAX I11]".
      clear SUBST.

      hexploit (tkqueue_inv_hd I2 _ FIND). i. des. inv H. inv H0.
      iClear "INDB".
      iDestruct "MEM3" as "[MEM3 [MEM4 [MEM5 [MEM6 MEM7]]]]".
      iPoseProof (black_updatable with "MEM6") as ">MEM6".
      { instantiate (1:= (now, o0)). econs 2. clear - LT. unfold ord_ge. apply Ord.lt_le. auto. }
      iAssert (ticket_lock_inv_mem mem V wk o0 svw now next myt)%I with "[MEM0 MEM1 MEM2 MEM3 MEM4 MEM5 MEM6 MEM7]" as "MEM".
      { iFrame. iApply "INDB2". }
      iPoseProof (ticket_lock_inv_mem_mono3 with "MEM") as "#INDO".

      iApply (stsim_yieldR_strong with "[I8 TAX]").
      { iFrame. iApply ObligationRA.tax_cons_fold. iFrame. }
      iIntros "I8 _".
      iMod ("K" with "[TKS MEM ST0 ST1 I0 I3 I4 I5 I6 I7 I8 I9 I10 I11]") as "_".
      { unfold ticket_lock_inv. iExists mem, false, false, V, svw, wk, o0. iExists (tid :: tl), tks, now, next, myt.
        remember (
            (⌜false = true⌝ **
                          (⌜false = false⌝ ** ticket_lock_inv_locked (tid :: tl) tks now next myt V)
             ∨ (⌜false = true⌝ ** ticket_lock_inv_unlocking (tid :: tl) tks now next myt))
            ∨ (⌜false = false⌝ **
                             (⌜false = false⌝ **
                                            ticket_lock_inv_unlocked0 (tid :: tl) tks now next myt V ∨ ticket_lock_inv_unlocked1 (tid :: tl) tks now next myt V o0))
          )%I as temp.
        iFrame. iSplit. auto. subst temp. iRight. iSplit. auto. iSplit. auto. iRight.
        iExists tid, tl. iFrame. iSplit. auto. iSplit. auto.
        iExists k, o, u. iFrame.
      }
      iModIntro. specialize (IHo o0). rred. iApply IHo.
      { clear - WOLE LT. eapply Ord.lt_le_lt; eauto. }
      { etrans. eapply TVLE. auto. }
      { iFrame. iModIntro. auto. }
    }

    iApply stsim_fairR.
    { i. instantiate (1:=[]). exfalso. clear - IN. unfold sum_fmap_r, WMem.missed in IN. des_ifs. }
    { i. instantiate (1:=[]) in IN. inv IN. }
    { econs. }
    { ss. }
    iIntros "_ _".
    rred. iApply stsim_tauR. rred. iApply stsim_tauR. rred.
    des. subst val. rred.
    destruct (BinIntDef.Z.of_nat now =? BinIntDef.Z.of_nat now)%Z eqn:IF.
    2:{ exfalso. clear - IF. apply Z.eqb_neq in IF. apply IF. auto. }
    rred.

    iApply stsim_yieldL. lred.
    iApply stsim_getL. iSplit. auto. lred.
    iApply stsim_getL. iSplit. auto. destruct lc1. ss.
    iApply stsim_chooseL.
    assert (SIG: TView.le (TView.join tvw svw) tview0).
    { apply TView.join_spec. etrans. eapply TVLE. auto. etrans. eapply WQ1. auto. }
    iExists (@exist TView.t _ tview0 SIG). lred.
    iApply (stsim_putL with "ST1"). iIntros "ST1".

    remember (NatMap.remove tid tks) as tks'.
    rewrite <- key_set_pull_rm_eq. rewrite <- Heqtks'.
    iAssert (ticket_lock_inv_state mem true svw false tks')%I with "[ST0 ST1]" as "ST". iFrame.
    iAssert (ticket_lock_inv_mem mem V wk wo0 svw now next myt)%I with "[MEM0 MEM1 MEM2 MEM3]" as "MEM". iFrame.
    iDestruct "TKS" as "[TKS0 [TKS1 [TKS2 TKS3]]]".
    do 2 iDestruct "I" as "[% I]". iDestruct "I" as "[I0 [% [%I2 [I3 [I4 I5]]]]]".
    do 3 iDestruct "I5" as "[% I5]". iDestruct "I5" as "[I5 [I6 [I7 [I8 [I9 [I10 I11]]]]]]".
    hexploit (tkqueue_inv_hd I2 _ FIND). i. des.
    subst l. inversion H0; clear H0. subst yourt waits.

    iPoseProof (NatMapRA_remove with "TKS0 MYTK") as ">TKS0". rewrite <- Heqtks'.
    iPoseProof (natmap_prop_remove_find with "TKS2") as "[MYTH TKS2]". eauto. rewrite <- Heqtks'.
    iCombine "I10 MYNU" as "MYNUM". rewrite maps_to_res_add.
    iPoseProof (OwnM_Upd with "MYNUM") as "> MYNUM".
    { eapply maps_to_updatable. apply Auth.auth_update.
      instantiate (1:=Excl.just 0). instantiate (1:=Excl.just 0).
      ii. des. ur in FRAME. des_ifs. split; ur; ss.
    }
    iPoseProof (OwnMs_fold with "[TKS3 MYNUM]") as "TKS3".
    2:{ iSplitL "TKS3". iFrame. iFrame. }
    { instantiate (1:= fun id => ~ NatMap.In id tks'). i. ss. subst tks'.
      destruct (tid_dec j tid); auto. left. ii. apply IN.
      rewrite NatMapP.F.remove_neq_in_iff; auto.
    }

    iClear "I6 I9". iPoseProof (ObligationRA.pending_shot with "I7") as ">I7".
    iPoseProof (ObligationRA.duty_done with "I8 I7") as ">DUTY".
    iPoseProof (black_updatable with "I5") as ">I5".
    { instantiate (1:=(now, Tkst.c k)). econs 2. ss. split; ss. lia. }
    hexploit (tkqueue_dequeue I2).
    { reflexivity. }
    i. rename I2 into I2Old, H into I2. unfold TicketLockW.tk in I2. rewrite <- Heqtks' in I2.
    iPoseProof (natmap_prop_remove with "I3") as "I3". rewrite <- Heqtks'.

    iPoseProof (natmap_prop_sum_impl with "I3") as "I3".
    { instantiate (1:= fun th tk =>
                         ((FairRA.white th (Ord.from_nat (tk - (S now))))
                            ∗ (FairRA.white th Ord.one))%I).
      i. ss. iIntros "WHI". erewrite FairRA.white_eq.
      2:{ instantiate (1:= (OrderedCM.add (Ord.from_nat (a - (S now))) (Ord.one))).
          rewrite <- Ord.from_nat_1. ss. rewrite <- Hessenberg.add_from_nat. rr. ss.
          hexploit (tkqueue_val_range_l I2 _ IN). i. split.
          { apply OrdArith.le_from_nat. lia. }
          { apply OrdArith.le_from_nat. lia. }
      }
      iPoseProof (FairRA.white_split with "WHI") as "[WHI1 WHI2]". iFrame.
    }
    iPoseProof (natmap_prop_sepconj_sum with "I3") as "[I3 TAX]".

    iApply (stsim_fairL with "[TAX]").
    { i. ss. instantiate (1:= (NatSet.elements (key_set tks'))). des_ifs.
      eapply NatSetIn_In. auto.
    }
    { instantiate (1:=[tid]). i; ss. des; clarify. des_ifs. }
    { unfold natmap_prop_sum. unfold NatSet.elements. unfold nm_proj1.
      unfold key_set. rewrite <- list_map_elements_nm_map. unfold unit1. rewrite List.map_map.
      iPoseProof (list_prop_sum_map with "TAX") as "TAX".
      2: iFrame.
      ss. i. destruct a; ss.
    }
    instantiate (1:= Ord.omega). iIntros "[MYW _]".
    iPoseProof (FairRA.whites_fold with "[TKS1 MYW]") as "TKS1".
    2:{ iSplitL "TKS1". iFrame. iFrame. }
    { instantiate (1:= fun id => ~ NatMap.In id tks'). ss. i. destruct (tid_dec j tid); auto.
      left. ii. apply IN. subst tks'. rewrite NatMapP.F.remove_neq_in_iff; auto.
    }

    iMod ("K" with "[I0 I4 ST MEM TKS0 TKS2 TKS3 I5 I3 TKS1]") as "_".
    { unfold ticket_lock_inv. iExists mem, true, false, V, svw, wk, wo0. iExists tl, tks', now, next, myt.
      remember (
    (⌜true = true⌝ **
     (⌜false = false⌝ ** ticket_lock_inv_locked tl tks' now next myt V)
     ∨ (⌜false = true⌝ ** ticket_lock_inv_unlocking tl tks' now next myt))
    ∨ (⌜true = false⌝ **
       (⌜false = false⌝ ** ticket_lock_inv_unlocked0 tl tks' now next myt V ∨ ticket_lock_inv_unlocked1 tl tks' now next myt V wo0))
        )%I as temp.
      iFrame. iSplit. auto. subst temp. iLeft. iSplit. auto.
      iLeft. iSplit. auto. iFrame. iSplit. auto. iExists k. iFrame.
    }
    iApply (stsim_sync with "[DUTY]"). msubtac. iFrame.
    iIntros "DUTY _". rred.
    iApply stsim_tauR. rred. iApply stsim_ret. iModIntro. iFrame. auto.

  Qed.

  Lemma lock_myturn1
        (g0 g1 : ∀ R_src R_tgt : Type,
            (R_src → R_tgt → iProp)
            → bool
            → bool
            → itree ((eventE +' cE) +' sE (Mod.state AbsLockW.mod)) R_src
            → itree ((eventE +' cE) +' sE (OMod.closed_state TicketLockW.omod (WMem.mod))) R_tgt → iProp)
        (ps pt: bool)
        (tid : nat)
        (tvw: TView.t)
        (now : TicketLockW.tk)
        (mem : WMem.t)
        (own ing : bool)
        (l : list nat)
        (tks : NatMap.t nat)
        (next myt : nat)
        (tview : TView.t)
        (TVLE : TView.le tvw tview)
        (V svw : TView.t)
        (wk : nat)
        wo
    :
  (OwnM (Auth.white (NatMapRA.singleton tid now: NatMapRA.t nat)) **
   (maps_to tid (Auth.white (Excl.just 1: Excl.t nat)) **
    (ticket_lock_inv_tks tks **
     ((ticket_lock_inv_mem mem V wk wo svw now next myt ** ⌜TView.le V svw⌝) **
      (ticket_lock_inv_state mem own svw ing tks **
       ((⌜own = true⌝ **
         (⌜ing = false⌝ ** ticket_lock_inv_locked l tks now next myt V)
         ∨ (⌜ing = true⌝ ** ticket_lock_inv_unlocking l tks now next myt))
        ∨ (⌜own = false⌝ **
           (⌜ing = false⌝ ** ticket_lock_inv_unlocked0 l tks now next myt V ∨ ticket_lock_inv_unlocked1 l tks now next myt V wo)) **
        (ticket_lock_inv -* MUpd (nth_default True%I I) (fairI (ident_tgt:=OMod.closed_ident TicketLockW.omod WMem.mod)) [] [0] True)))))))
  ⊢ (stsim I tid [] g0 g1
      (λ r_src r_tgt : TView.t, (own_thread tid ** ObligationRA.duty (inl tid) []) ** ⌜r_src = r_tgt⌝)
      ps pt
      (trigger Yield;;;
       ` x : () + () <-
       (` x_ : bool * TView.t * bool * NatMap.t () <- trigger (Get (bool * TView.t * bool * NatMap.t ()));;
        (let (y, _) := x_ in let (y1, _) := y in let (own0, _) := y1 in if own0 then Ret (inl ()) else Ret (inr ())));;
       match x with
       | inl l0 =>
           tau;; ITree.iter
                   (λ _ : (),
                      trigger Yield;;;
                      ` x_ : bool * TView.t * bool * NatMap.t () <- trigger (Get (bool * TView.t * bool * NatMap.t ()));;
                      (let (y, _) := x_ in let (y1, _) := y in let (own0, _) := y1 in if own0 then Ret (inl ()) else Ret (inr ())))
                   l0
       | inr r0 => Ret r0
       end;;;
       ` x_ : bool * TView.t * bool * NatMap.t () <- trigger (Get (bool * TView.t * bool * NatMap.t ()));;
       (let (y, ts) := x_ in
        let (y0, ing0) := y in
        let (_, tvw_lock) := y0 in
        if ing0
        then ` x1 : void <- trigger (Choose void);; Empty_set_rect (λ _ : void, itree ((eventE +' cE) +' sE AbsLockW.st) TView.t) x1
        else
         ` x_0 : {tvw' : TView.t | TView.le (TView.join tvw tvw_lock) tvw'} <-
         trigger (Choose {tvw' : TView.t | TView.le (TView.join tvw tvw_lock) tvw'});;
         (let (tvw', _) := x_0 in
          trigger (Put (true, tvw_lock, false, NatMap.remove (elt:=()) tid ts));;;
          trigger
            (Fair
               (λ i : nat,
                  if tid_dec i tid
                  then Flag.success
                  else if NatMapP.F.In_dec (NatMap.remove (elt:=()) tid ts) i then Flag.fail else Flag.emp));;;
          trigger Yield;;; Ret tvw')))
      (trigger Yield;;;
       ` x : TView.t * Const.t <-
       (` rv : Any.t <-
        OMod.embed_itree TicketLockW.omod WMem.mod
          (Mod.wrap_fun WMem.load_fun (Any.upcast (tview, TicketLockW.now_serving, Ordering.acqrel)));;
        (tau;; unwrap (Any.downcast rv)));;
       ` x0 : TView.t <-
       OMod.close_itree TicketLockW.omod WMem.mod
         (let (tvw0, now0) := x in
          ` b : bool <- unwrap match now0 with
                               | Const.num b => Some (BinIntDef.Z.of_nat now =? b)%Z
                               | Const.undef => None
                               end;; (if b then Ret tvw0 else tau;; TicketLockW.lock_loop (nat2c now) tvw0));;
       OMod.close_itree TicketLockW.omod WMem.mod (trigger Yield;;; Ret x0))).
  Proof.
    iIntros "[MYTK [MYN [TKS [MEM [ST [CASES K]]]]]]".
    iAssert (⌜NatMap.find tid tks = Some now⌝)%I as "%FIND".
    { iDestruct "TKS" as "[TKS0 _]". iApply (NatMapRA_find_some with "TKS0 MYTK"). }
    iDestruct "CASES" as "[[%CT [[% I] | [% I]]] | [%CF [% [I | I]]]]".
    { iPoseProof (locked_contra with "I") as "%F". eauto. inv F. }
    { iPoseProof (unlocking_contra with "I") as "%F". eauto. inv F. }
    { iPoseProof (unlocked0_contra with "I") as "%F". eauto. inv F. }
    iPoseProof (unlocked1_mono with "I") as "[%TKQ #MYMW]".
    iDestruct "MYMW" as "[% [% [MYMW _]]]".
    iMod ("K" with "[TKS MEM ST I]") as "_".
    { unfold ticket_lock_inv. iExists mem, own, ing, V, svw, wk, wo. iExists l, tks, now, next, myt. iFrame. iRight. iSplit; auto. }
    iApply lock_myturn_yieldR. iSplitL. iFrame. auto.
    iIntros "[MYTK [MYN _]]". rred.
    iApply lock_myturn0. auto. iFrame. auto.
  Qed.

  (* Lemma lock_myturn2 *)
  (*       (g0 g1 : ∀ R_src R_tgt : Type, *)
  (*           (R_src → R_tgt → iProp) *)
  (*           → bool *)
  (*           → bool *)
  (*           → itree ((eventE +' cE) +' sE (Mod.state AbsLockW.mod)) R_src *)
  (*           → itree ((eventE +' cE) +' sE (OMod.closed_state TicketLock.omod (WMem.mod TicketLock.gvs))) R_tgt → iProp) *)
  (*       (ps pt: bool) *)
  (*       (tid : nat) *)
  (*       (mytk : TicketLockW.tk) *)
  (*       (mem : WMem.t) *)
  (*       (own : bool) *)
  (*       (l : list nat) *)
  (*       (tks : NatMap.t nat) *)
  (*       (next myt : nat) *)
  (*       now_old *)
  (*       (NEQ: mytk <> now_old) *)
  (*   : *)
  (* (OwnM (Auth.white (NatMapRA.singleton tid mytk: NatMapRA.t nat)) ** *)
  (*  (maps_to tid (Auth.white (Excl.just 2: Excl.t nat)) ** *)
  (*   (ticket_lock_inv_tks tks ** *)
  (*    (ticket_lock_inv_mem mem mytk next myt ** *)
  (*     (ticket_lock_inv_state mem own tks ** *)
  (*      ((⌜own = true⌝ ** ticket_lock_inv_locked l tks mytk next myt) *)
  (*       ∨ (⌜own = false⌝ ** *)
  (*          ticket_lock_inv_unlocking l tks mytk next myt *)
  (*          ∨ ticket_lock_inv_unlocked0 l tks mytk next myt *)
  (*            ∨ ticket_lock_inv_unlocked1 l tks mytk next myt) ** *)
  (*       (ticket_lock_inv -* *)
  (*        MUpd (nth_default True%I I) *)
  (*          (fairI (ident_tgt:=OMod.closed_ident TicketLock.omod (WMem.mod TicketLock.gvs))) [] *)
  (*          [0] True))))))) *)
  (* ⊢ (stsim I tid [] g0 g1 *)
  (*   (λ r_src r_tgt : (), (own_thread tid ** ObligationRA.duty (inl tid) []) ** ⌜r_src = r_tgt⌝) *)
  (*   ps pt *)
  (*   (trigger Yield;;; *)
  (*    ` x : () + () <- *)
  (*    (` x_0 : bool * NatMap.t () <- trigger (Get (bool * NatMap.t ()));; *)
  (*     (let (own0, _) := x_0 in if Bool.eqb own0 true then Ret (inl ()) else Ret (inr ())));; *)
  (*    match x with *)
  (*    | inl l0 => *)
  (*        tau;; ITree.iter *)
  (*                (λ _ : (), *)
  (*                   trigger Yield;;; *)
  (*                   ` x_0 : bool * NatMap.t () <- trigger (Get (bool * NatMap.t ()));; *)
  (*                   (let (own0, _) := x_0 in *)
  (*                    if Bool.eqb own0 true then Ret (inl ()) else Ret (inr ()))) l0 *)
  (*    | inr r0 => Ret r0 *)
  (*    end;;; *)
  (*    ` x_0 : bool * NatMap.t () <- trigger (Get (bool * NatMap.t ()));; *)
  (*    (let (_, ts0) := x_0 in *)
  (*     trigger (Put (true, NatMap.remove (elt:=()) tid ts0));;; *)
  (*     trigger *)
  (*       (Fair *)
  (*          (λ i : nat, *)
  (*             if tid_dec i tid *)
  (*             then Flag.success *)
  (*             else *)
  (*              if NatMapP.F.In_dec (NatMap.remove (elt:=()) tid ts0) i *)
  (*              then Flag.fail *)
  (*              else Flag.emp));;; trigger Yield;;; Ret ())) *)
  (*   (` r : Any.t <- *)
  (*    OMod.embed_itree TicketLock.omod (WMem.mod TicketLock.gvs) *)
  (*      (Mod.wrap_fun WMem.compare_fun (Any.upcast (WMem.val_nat now_old, WMem.val_nat mytk)));; *)
  (*    ` x : bool <- (tau;; unwrap (Any.downcast r));; *)
  (*    OMod.close_itree TicketLock.omod (WMem.mod TicketLock.gvs) *)
  (*      (if x then Ret () else tau;; TicketLock.lock_loop (WMem.val_nat mytk));;; *)
  (*      OMod.close_itree TicketLock.omod (WMem.mod TicketLock.gvs) (trigger Yield))). *)
  (* Proof. *)
  (*   iIntros "[MYTK [MYN [TKS [MEM [ST [CASES K]]]]]]". *)
  (*   unfold Mod.wrap_fun, WMem.compare_fun. rred. *)
  (*   iDestruct "MEM" as "[MEM0 [MEM1 [MEM2 MEM3]]]". iDestruct "ST" as "[ST0 ST1]". *)
  (*   iApply stsim_getR. iSplit. eauto. rred. *)
  (*   iApply stsim_tauR. rred. iApply stsim_tauR. rred. *)
  (*   destruct (Nat.eq_dec now_old mytk). *)
  (*   { exfalso. clarify. } *)
  (*   rred. iApply stsim_tauR. *)
  (*   rewrite TicketLock.lock_loop_red. rred. rewrite close_itree_call. rred. *)
  (*   iApply lock_myturn1. *)
  (*   iSplitL "MYTK". iFrame. iSplitL "MYN". iFrame. iSplitL "TKS". iFrame. *)
  (*   iSplitL "MEM0 MEM1 MEM2 MEM3". iFrame. iSplitL "ST0 ST1". iFrame. iSplitL "CASES". iFrame. *)
  (*   iFrame. *)
  (* Qed. *)

  (* Let src_code_coind tid: itree ((eventE +' cE) +' sE (Mod.state AbsLockW.mod)) () := *)
  (*         ((` lr : () + () <- *)
  (*           (trigger Yield;;; *)
  (*            ` x_0 : bool * NatMap.t () <- trigger (Get (bool * NatMap.t ()));; *)
  (*            (let (own0, _) := x_0 in if Bool.eqb own0 true then Ret (inl ()) else Ret (inr ())));; *)
  (*           match lr with *)
  (*           | inl l0 => *)
  (*               tau;; ITree.iter *)
  (*                       (λ _ : (), *)
  (*                          trigger Yield;;; *)
  (*                          ` x_0 : bool * NatMap.t () <- trigger (Get (bool * NatMap.t ()));; *)
  (*                          (let (own0, _) := x_0 in *)
  (*                           if Bool.eqb own0 true then Ret (inl ()) else Ret (inr ()))) l0 *)
  (*           | inr r0 => Ret r0 *)
  (*           end);;; *)
  (*          ` x_0 : bool * NatMap.t () <- trigger (Get (bool * NatMap.t ()));; *)
  (*          (let (_, ts0) := x_0 in *)
  (*           trigger (Put (true, NatMap.remove (elt:=()) tid ts0));;; *)
  (*           trigger *)
  (*             (Fair *)
  (*                (λ i : nat, *)
  (*                   if tid_dec i tid *)
  (*                   then Flag.success *)
  (*                   else *)
  (*                    if NatMapP.F.In_dec (NatMap.remove (elt:=()) tid ts0) i *)
  (*                    then Flag.fail *)
  (*                    else Flag.emp));;; trigger Yield;;; Ret ())). *)

  (* Let tgt_code_coind a := *)
  (*         (trigger Yield;;; *)
  (*          ` x : WMem.val <- *)
  (*          (` rv : Any.t <- *)
  (*           OMod.embed_itree TicketLock.omod (WMem.mod TicketLock.gvs) *)
  (*             (` arg : WMem.val <- unwrap (Any.downcast (Any.upcast TicketLock.now_serving));; *)
  (*              ` ret : WMem.val <- *)
  (*              (` m : WMem.t <- trigger (Get WMem.t);; *)
  (*               ` v : WMem.val <- unwrap (WMem.load m arg);; Ret v);;  *)
  (*              Ret (Any.upcast ret));; (tau;; unwrap (Any.downcast rv)));; *)
  (*          OMod.close_itree TicketLock.omod (WMem.mod TicketLock.gvs) *)
  (*            (` b : bool <- OMod.call "compare" (x, WMem.val_nat a);; *)
  (*             (if b then Ret () else tau;; TicketLock.lock_loop (WMem.val_nat a)));;; *)
  (*          OMod.close_itree TicketLock.omod (WMem.mod TicketLock.gvs) (trigger Yield)). *)

  (* Lemma lock_yourturn_coind *)
  (*       (g0 g1 : ∀ R_src R_tgt : Type, *)
  (*           (R_src → R_tgt → iProp) *)
  (*           → bool *)
  (*           → bool *)
  (*           → itree ((eventE +' cE) +' sE (Mod.state AbsLockW.mod)) R_src *)
  (*           → itree ((eventE +' cE) +' sE (OMod.closed_state TicketLock.omod (WMem.mod TicketLock.gvs))) R_tgt → iProp) *)
  (*       (ps pt: bool) *)
  (*       (tid : nat) *)
  (*       (mytk : TicketLockW.tk) *)
  (*       (mem : WMem.t) *)
  (*       (l : list nat) *)
  (*       (tks : NatMap.t nat) *)
  (*       (now next myt : nat) *)
  (*       now_old *)
  (*       (NEQ: mytk <> now_old) *)
  (*   : *)
  (* (□ (∀ a : TicketLockW.tk, *)
  (*       (OwnM (Auth.white (NatMapRA.singleton tid a: NatMapRA.t nat)) ** maps_to tid (Auth.white (Excl.just 2: Excl.t nat))) -* *)
  (*       g1 ()%type ()%type *)
  (*         (λ r_src r_tgt : (), *)
  (*             (own_thread tid ** ObligationRA.duty (inl tid) []) ** ⌜r_src = r_tgt⌝) false false *)
  (*         (src_code_coind tid) *)
  (*         (tgt_code_coind a) *)
  (*    ) ** *)
  (*  (maps_to tid (Auth.white (Excl.just 2: Excl.t nat)) ** *)
  (*   (OwnM (Auth.white (NatMapRA.singleton tid mytk: NatMapRA.t nat)) ** *)
  (*    (ticket_lock_inv_tks tks ** *)
  (*     (ticket_lock_inv_mem mem now next myt ** *)
  (*      (ticket_lock_inv_state mem true tks ** *)
  (*       (ticket_lock_inv_locked l tks now next myt ** *)
  (*        (ticket_lock_inv -* *)
  (*         MUpd (nth_default True%I I) *)
  (*           (fairI (ident_tgt:=OMod.closed_ident TicketLock.omod (WMem.mod TicketLock.gvs))) [] *)
  (*           [0] True))))))) *)
  (* ) *)
  (* ⊢ (stsim I tid [] g0 g1 *)
  (*     (λ r_src r_tgt : (), (own_thread tid ** ObligationRA.duty (inl tid) []) ** ⌜r_src = r_tgt⌝) *)
  (*     ps pt *)
  (*     (trigger Yield;;; *)
  (*      ` x : () + () <- *)
  (*      (` x_0 : bool * NatMap.t () <- trigger (Get (bool * NatMap.t ()));; *)
  (*       (let (own0, _) := x_0 in if Bool.eqb own0 true then Ret (inl ()) else Ret (inr ())));; *)
  (*      match x with *)
  (*      | inl l0 => *)
  (*          tau;; ITree.iter *)
  (*                  (λ _ : (), *)
  (*                     trigger Yield;;; *)
  (*                     ` x_0 : bool * NatMap.t () <- trigger (Get (bool * NatMap.t ()));; *)
  (*                     (let (own0, _) := x_0 in *)
  (*                      if Bool.eqb own0 true then Ret (inl ()) else Ret (inr ()))) l0 *)
  (*      | inr r0 => Ret r0 *)
  (*      end;;; *)
  (*      ` x_0 : bool * NatMap.t () <- trigger (Get (bool * NatMap.t ()));; *)
  (*      (let (_, ts0) := x_0 in *)
  (*       trigger (Put (true, NatMap.remove (elt:=()) tid ts0));;; *)
  (*       trigger *)
  (*         (Fair *)
  (*            (λ i : nat, *)
  (*               if tid_dec i tid *)
  (*               then Flag.success *)
  (*               else *)
  (*                if NatMapP.F.In_dec (NatMap.remove (elt:=()) tid ts0) i *)
  (*                then Flag.fail *)
  (*                else Flag.emp));;; trigger Yield;;; Ret ())) *)
  (*     (` r : Any.t <- *)
  (*      OMod.embed_itree TicketLock.omod (WMem.mod TicketLock.gvs) *)
  (*        (Mod.wrap_fun WMem.compare_fun (Any.upcast (WMem.val_nat now_old, WMem.val_nat mytk)));; *)
  (*      ` x : bool <- (tau;; unwrap (Any.downcast r));; *)
  (*      OMod.close_itree TicketLock.omod (WMem.mod TicketLock.gvs) *)
  (*        (if x then Ret () else tau;; TicketLock.lock_loop (WMem.val_nat mytk));;; *)
  (*      OMod.close_itree TicketLock.omod (WMem.mod TicketLock.gvs) (trigger Yield))). *)
  (* Proof. *)
  (*   iIntros "[#CIH [MYTK [MYN [TKS [MEM [ST [I K]]]]]]]". *)
  (*   unfold Mod.wrap_fun, WMem.compare_fun. rred. *)
  (*   iDestruct "MEM" as "[MEM0 [MEM1 [MEM2 MEM3]]]". iDestruct "ST" as "[ST0 ST1]". *)
  (*   iApply stsim_getR. iSplit. eauto. rred. *)
  (*   iApply stsim_tauR. rred. iApply stsim_tauR. rred. *)
  (*   destruct (Nat.eq_dec now_old mytk). *)
  (*   { exfalso. clarify. } *)
  (*   rred. iApply stsim_tauR. *)
  (*   rewrite TicketLock.lock_loop_red. rred. rewrite close_itree_call. rred. *)

  (*   iApply stsim_yieldL. lred. *)
  (*   iApply stsim_getL. iSplit. auto. lred. *)
  (*   iApply stsim_tauL. *)
  (*   iMod ("K" with "[TKS MEM0 MEM1 MEM2 MEM3 ST0 ST1 I]") as "_". *)
  (*   { do 7 iExists _. *)
  (*     iSplitL "TKS". iFrame. iSplitL "MEM0 MEM1 MEM2 MEM3". iFrame. *)
  (*     iSplitL "ST0 ST1". iFrame. *)
  (*     iLeft. iSplit. auto. iFrame. *)
  (*   } *)
  (*   iApply stsim_progress. iApply stsim_base. msubtac. *)
  (*   rewrite unfold_iter_eq. iApply "CIH". iFrame. *)
  (* Qed. *)

  Lemma yourturn_range
        tid tks mytk now next own ing l myt V wo
        (FIND : NatMap.find tid tks = Some mytk)
        (NEQ : mytk ≠ now)
    :
    ((⌜own = true⌝ ∗
     ((⌜ing = false⌝ ∗ ticket_lock_inv_locked l tks now next myt V) ∨ (⌜ing = true⌝ ∗ ticket_lock_inv_unlocking l tks now next myt)))
    ∨ (⌜own = false⌝ ∗
                   (⌜ing = false⌝ ∗
                                (ticket_lock_inv_unlocked0 l tks now next myt V ∨ ticket_lock_inv_unlocked1 l tks now next myt V wo))))
        ⊢
      (⌜now < mytk⌝).
  Proof.
    iIntros "[[%CT [[%IF I] | [%IT I]]] | [%CF [%IF [I | I]]]]".
    { iDestruct "I" as "[_ [%I1 _]]".
      hexploit (tkqueue_val_range_l I1 _ FIND). i. iPureIntro. lia. }
    { iDestruct "I" as "[_ [%I1 _]]".
      hexploit (tkqueue_val_range_l I1 _ FIND). i. iPureIntro. lia. }
    { iPoseProof (unlocked0_contra with "I") as "%FF". eauto. inv FF. }
    { iPoseProof (unlocked1_mono with "I") as "[%I1 _]".
      hexploit (tkqueue_val_range_l I1 _ FIND). i. iPureIntro. lia. }
  Qed.

  (* Let src_code_ind tid: itree ((eventE +' cE) +' sE (Mod.state AbsLockW.mod)) () := *)
  (*                        (trigger Yield;;; *)
  (*                         ` x : () + () <- *)
  (*                         (` x_0 : bool * NatMap.t () <- trigger (Get (bool * NatMap.t ()));; *)
  (*                          (let (own0, _) := x_0 in *)
  (*                           if Bool.eqb own0 true then Ret (inl ()) else Ret (inr ())));; *)
  (*                         match x with *)
  (*                         | inl l0 => *)
  (*                             tau;; ITree.iter *)
  (*                                     (λ _ : (), *)
  (*                                        trigger Yield;;; *)
  (*                                        ` x_0 : bool * NatMap.t () <- *)
  (*                                        trigger (Get (bool * NatMap.t ()));; *)
  (*                                        (let (own0, _) := x_0 in *)
  (*                                         if Bool.eqb own0 true *)
  (*                                         then Ret (inl ()) *)
  (*                                         else Ret (inr ()))) l0 *)
  (*                         | inr r0 => Ret r0 *)
  (*                         end;;; *)
  (*                         ` x_0 : bool * NatMap.t () <- trigger (Get (bool * NatMap.t ()));; *)
  (*                         (let (_, ts0) := x_0 in *)
  (*                          trigger (Put (true, NatMap.remove (elt:=()) tid ts0));;; *)
  (*                          trigger *)
  (*                            (Fair *)
  (*                               (λ i : nat, *)
  (*                                  if tid_dec i tid *)
  (*                                  then Flag.success *)
  (*                                  else *)
  (*                                   if NatMapP.F.In_dec (NatMap.remove (elt:=()) tid ts0) i *)
  (*                                   then Flag.fail *)
  (*                                   else Flag.emp));;; trigger Yield;;; Ret ())). *)

  (* Let tgt_code_ind mytk now_old := *)
  (*                        (` r : Any.t <- *)
  (*                         OMod.embed_itree TicketLock.omod (WMem.mod TicketLock.gvs) *)
  (*                           (Mod.wrap_fun WMem.compare_fun *)
  (*                              (Any.upcast (WMem.val_nat now_old, WMem.val_nat mytk)));; *)
  (*                         ` x : bool <- (tau;; unwrap (Any.downcast r));; *)
  (*                         OMod.close_itree TicketLock.omod (WMem.mod TicketLock.gvs) *)
  (*                           (if x *)
  (*                            then Ret () *)
  (*                            else tau;; TicketLock.lock_loop (WMem.val_nat mytk));;; *)
  (*                         OMod.close_itree TicketLock.omod (WMem.mod TicketLock.gvs) *)
  (*                           (trigger Yield)). *)

  (* Lemma lock_yourturn_ind0 *)
  (*       (g0 g1 : ∀ R_src R_tgt : Type, *)
  (*           (R_src → R_tgt → iProp) *)
  (*           → bool *)
  (*           → bool *)
  (*           → itree ((eventE +' cE) +' sE (Mod.state AbsLockW.mod)) R_src *)
  (*           → itree ((eventE +' cE) +' sE (OMod.closed_state TicketLock.omod (WMem.mod TicketLock.gvs))) R_tgt → iProp) *)
  (*       (tid : nat) *)
  (*       (mytk : TicketLockW.tk) *)
  (* (now : nat) *)
  (* (LT : now < mytk) *)
  (* (IH : ∀ y : nat, *)
  (*        y < mytk - now *)
  (*        → ∀ now_old : nat, *)
  (*            mytk ≠ now_old *)
  (*            → ∀ (mem : WMem.t) (own : bool) (l : list nat) (tks : NatMap.t nat) *)
  (*                (now next myt : nat), *)
  (*                now < mytk *)
  (*                → y = mytk - now *)
  (*                  → (□ ((∀ a : TicketLockW.tk, *)
  (*                           (OwnM (Auth.white (NatMapRA.singleton tid a: NatMapRA.t nat)) ** *)
  (*                            maps_to tid (Auth.white (Excl.just 2: Excl.t nat))) -* *)
  (*                           g1 ()%type ()%type *)
  (*                             (λ r_src r_tgt : (), *)
  (*                                (own_thread tid ** ObligationRA.duty (inl tid) []) ** *)
  (*                                ⌜r_src = r_tgt⌝) false false *)
  (*                             (src_code_coind tid) *)
  (*                             (tgt_code_coind a) *)
  (*                        ) ∧ monoWhite tk_mono Nat.le_preorder now) ** *)
  (*                     (maps_to tid (Auth.white (Excl.just 2: Excl.t nat)) ** *)
  (*                      (OwnM (Auth.white (NatMapRA.singleton tid mytk: NatMapRA.t nat)) ** *)
  (*                       (ticket_lock_inv_tks tks ** *)
  (*                        (ticket_lock_inv_state mem own tks ** *)
  (*                         ((⌜own = true⌝ ** ticket_lock_inv_locked l tks now next myt) *)
  (*                          ∨ (⌜own = false⌝ ** *)
  (*                             ticket_lock_inv_unlocking l tks now next myt *)
  (*                             ∨ ticket_lock_inv_unlocked0 l tks now next myt *)
  (*                               ∨ ticket_lock_inv_unlocked1 l tks now next myt) ** *)
  (*                          ((ticket_lock_inv -* *)
  (*                            MUpd (nth_default True%I I) *)
  (*                              (fairI *)
  (*                                 (ident_tgt:=OMod.closed_ident TicketLock.omod *)
  (*                                               (WMem.mod TicketLock.gvs))) [] [0] True) ** *)
  (*                           ticket_lock_inv_mem mem now next myt))))))) *)
  (*                    ⊢ stsim I tid [] g0 g1 *)
  (*                        (λ r_src r_tgt : (), *)
  (*                           (own_thread tid ** ObligationRA.duty (inl tid) []) ** ⌜r_src = r_tgt⌝) *)
  (*                        false true *)
  (*                        (src_code_ind tid) *)
  (*                        (tgt_code_ind mytk now_old) *)
  (* ) *)
  (* (now_old : nat) *)
  (* (NEQ : mytk ≠ now_old) *)
  (* (mem : WMem.t) *)
  (* (l : list nat) *)
  (* (tks : NatMap.t nat) *)
  (* (next myt : nat) *)
  (*   : *)
  (* (□ ((∀ a : TicketLockW.tk, *)
  (*       (OwnM (Auth.white (NatMapRA.singleton tid a: NatMapRA.t nat)) ** maps_to tid (Auth.white (Excl.just 2: Excl.t nat))) -* *)
  (*       g1 ()%type ()%type *)
  (*         (λ r_src r_tgt : (), *)
  (*            (own_thread tid ** ObligationRA.duty (inl tid) []) ** ⌜r_src = r_tgt⌝) false false *)
  (*         (src_code_coind tid) *)
  (*         (tgt_code_coind a)) *)
  (*         ∧ *)
  (* (monoWhite tk_mono Nat.le_preorder now) *)
  (*    ) ** *)
  (*  (maps_to tid (Auth.white (Excl.just 2: Excl.t nat)) ** *)
  (*   (OwnM (Auth.white (NatMapRA.singleton tid mytk: NatMapRA.t nat)) ** *)
  (*    (ticket_lock_inv_tks tks ** *)
  (*     (ticket_lock_inv_mem mem now next myt ** *)
  (*      (ticket_lock_inv_state mem false tks ** *)
  (*       (ticket_lock_inv_unlocking l tks now next myt ** *)
  (*        (ticket_lock_inv -* *)
  (*         MUpd (nth_default True%I I) *)
  (*           (fairI (ident_tgt:=OMod.closed_ident TicketLock.omod (WMem.mod TicketLock.gvs))) [] *)
  (*           [0] True))))))) *)
  (* ) *)
  (* ⊢ (stsim I tid [] g0 g1 *)
  (*     (λ r_src r_tgt : (), (own_thread tid ** ObligationRA.duty (inl tid) []) ** ⌜r_src = r_tgt⌝) *)
  (*     false true *)
  (*     (trigger Yield;;; *)
  (*      ` x : () + () <- *)
  (*      (` x_0 : bool * NatMap.t () <- trigger (Get (bool * NatMap.t ()));; *)
  (*       (let (own0, _) := x_0 in if Bool.eqb own0 true then Ret (inl ()) else Ret (inr ())));; *)
  (*      match x with *)
  (*      | inl l0 => *)
  (*          tau;; ITree.iter *)
  (*                  (λ _ : (), *)
  (*                     trigger Yield;;; *)
  (*                     ` x_0 : bool * NatMap.t () <- trigger (Get (bool * NatMap.t ()));; *)
  (*                     (let (own0, _) := x_0 in *)
  (*                      if Bool.eqb own0 true then Ret (inl ()) else Ret (inr ()))) l0 *)
  (*      | inr r0 => Ret r0 *)
  (*      end;;; *)
  (*      ` x_0 : bool * NatMap.t () <- trigger (Get (bool * NatMap.t ()));; *)
  (*      (let (_, ts0) := x_0 in *)
  (*       trigger (Put (true, NatMap.remove (elt:=()) tid ts0));;; *)
  (*       trigger *)
  (*         (Fair *)
  (*            (λ i : nat, *)
  (*               if tid_dec i tid *)
  (*               then Flag.success *)
  (*               else *)
  (*                if NatMapP.F.In_dec (NatMap.remove (elt:=()) tid ts0) i *)
  (*                then Flag.fail *)
  (*                else Flag.emp));;; trigger Yield;;; Ret ())) *)
  (*     (` r : Any.t <- *)
  (*      OMod.embed_itree TicketLock.omod (WMem.mod TicketLock.gvs) *)
  (*        (Mod.wrap_fun WMem.compare_fun (Any.upcast (WMem.val_nat now_old, WMem.val_nat mytk)));; *)
  (*      ` x : bool <- (tau;; unwrap (Any.downcast r));; *)
  (*      OMod.close_itree TicketLock.omod (WMem.mod TicketLock.gvs) *)
  (*        (if x then Ret () else tau;; TicketLock.lock_loop (WMem.val_nat mytk));;; *)
  (*      OMod.close_itree TicketLock.omod (WMem.mod TicketLock.gvs) (trigger Yield))). *)
  (* Proof. *)
  (*   iIntros "[#[CIH MONOTK] [MYN [MYTK [TKS [MEM [ST [I K]]]]]]]". *)
  (*   iPoseProof (mytk_find_some with "[MYTK TKS]") as "%FIND". iFrame. *)
  (*   iPoseProof (unlocking_mono with "I") as "[%TKQ #[% [% [MONOW OBLB]]]]". *)
  (*   clear FIND TKQ. *)
  (*   iStopProof. move o before IH. revert_until o. pattern o. revert o. *)
  (*   apply (well_founded_induction Ord.lt_well_founded). *)
  (*   intros o IHo. intros. *)
  (*   iIntros "[#[CIH [MONOTK [MONOW BLK]]] [MYN [MYTK [TKS [MEM [ST [I K]]]]]]]". *)

  (*   unfold Mod.wrap_fun, WMem.compare_fun. rred. *)
  (*   iDestruct "MEM" as "[MEM0 [MEM1 [MEM2 MEM3]]]". iDestruct "ST" as "[ST0 ST1]". *)
  (*   iApply stsim_getR. iSplit. eauto. rred. *)
  (*   iApply stsim_tauR. rred. iApply stsim_tauR. rred. *)
  (*   destruct (Nat.eq_dec now_old mytk). *)
  (*   { exfalso. clarify. } *)
  (*   rred. iApply stsim_tauR. *)
  (*   rewrite TicketLock.lock_loop_red. rred. rewrite close_itree_call. rred. *)
  (*   iAssert (ticket_lock_inv_mem mem now next myt)%I with "[MEM0 MEM1 MEM2 MEM3]" as "MEM". iFrame. *)
  (*   iAssert (ticket_lock_inv_state mem false tks)%I with "[ST0 ST1]" as "ST". iFrame. *)
  (*   iMod ("K" with "[TKS MEM ST I]") as "_". *)
  (*   { do 7 iExists _. iSplitL "TKS". iFrame. iSplitL "MEM". iFrame. iSplitL "ST". iFrame. *)
  (*     iRight. iSplit. auto. iLeft. iFrame. *)
  (*   } *)
  (*   clear mem l tks next myt now_old NEQ n. *)
  (*   rename now into now_past, LT into LTPAST, k into k_past, o into o_past. *)

  (*   iopen 0 "I" "K". do 7 iDestruct "I" as "[% I]". iDestruct "I" as "[TKS [MEM [ST CASES]]]". *)
  (*   destruct (Nat.eq_dec mytk now); subst. *)
  (*   { iClear "CIH". *)
  (*     iApply lock_myturn1. *)
  (*     iSplitL "MYTK". iFrame. iSplitL "MYN". iFrame. iSplitL "TKS". iFrame. *)
  (*     iSplitL "MEM". iFrame. iSplitL "ST". iFrame. iSplitL "CASES". iFrame. *)
  (*     iFrame. *)
  (*   } *)

  (*   rename n into NEQ. *)
  (*   iApply lock_yourturn_yieldR. eapply NEQ. *)
  (*   iSplitL "MYTK TKS MEM ST CASES K". *)
  (*   iSplitL "MYTK". iFrame. iSplitL "TKS". iFrame. iSplitL "MEM". iFrame. *)
  (*   iSplitL "ST". iFrame. iSplitL "CASES". iFrame. iFrame. *)
  (*   iIntros "[MYTK _]". rred. *)
  (*   clear mem own l tks now next myt NEQ. *)
  (*   iopen 0 "I" "K". do 7 iDestruct "I" as "[% I]". iDestruct "I" as "[TKS [MEM [ST CASES]]]". *)
  (*   destruct (Nat.eq_dec mytk now); subst. *)
  (*   { iClear "CIH". *)
  (*     iPoseProof (mytk_find_some with "[MYTK TKS]") as "%FIND". iFrame. *)
  (*     iDestruct "CASES" as "[[%CT I] | [%CF [I | [I | I]]]]". *)
  (*     { iPoseProof (locked_contra with "I") as "%F". eauto. inv F. } *)
  (*     { iPoseProof (unlocking_contra with "I") as "%F". eauto. inv F. } *)
  (*     { iPoseProof (unlocked0_contra with "I") as "%F". eauto. inv F. } *)
  (*     iPoseProof (unlocked1_mono with "I") as "[%TKQ #[% [% [MYTN _]]]]". *)
  (*     iMod ("K" with "[TKS MEM ST I]") as "_". *)
  (*     { do 7 iExists _. iSplitL "TKS". iFrame. iSplitL "MEM". iFrame. iSplitL "ST". iFrame. *)
  (*       iRight. iSplit. auto. iFrame. *)
  (*     } *)
  (*     iApply lock_myturn0. 2: iFrame; auto. lia. *)
  (*   } *)

  (*   rename n into NEQ. unfold Mod.wrap_fun, WMem.load_fun. rred. *)
  (*   iDestruct "MEM" as "[MEM0 [MEM1 [MEM2 MEM3]]]". iDestruct "ST" as "[ST0 ST1]". *)
  (*   iApply stsim_getR. iSplit. eauto. rred. *)
  (*   iApply stsim_tauR. rred. *)
  (*   iPoseProof (memory_ra_load with "MEM0 MEM1") as "%LOAD". des. rewrite LOAD. rred. *)
  (*   iApply stsim_tauR. rred. *)
  (*   rewrite close_itree_call. rred. *)
  (*   iApply lock_yourturn_yieldR. eapply NEQ. *)
  (*   iSplitL "MYTK TKS MEM0 MEM1 MEM2 MEM3 ST0 ST1 CASES K". *)
  (*   iSplitL "MYTK". iFrame. iSplitL "TKS". iFrame. iSplitL "MEM0 MEM1 MEM2 MEM3". iFrame. *)
  (*   iSplitL "ST0 ST1". iFrame. iSplitL "CASES". iFrame. iFrame. *)
  (*   iIntros "[MYTK RIGHT]". rred. *)
  (*   rename now into now_old. clear mem own l tks next myt LOAD LOAD0. *)

  (*   iopen 0 "I" "K". do 7 iDestruct "I" as "[% I]". iDestruct "I" as "[TKS [MEM [ST CASES]]]". *)
  (*   destruct (Nat.eq_dec mytk now); subst. *)
  (*   { iClear "CIH". iApply lock_myturn2. auto. *)
  (*     iSplitL "MYTK". iFrame. iSplitL "MYN". iFrame. iSplitL "TKS". iFrame. *)
  (*     iSplitL "MEM". iFrame. iSplitL "ST". iFrame. iSplitL "CASES". iFrame. *)
  (*     iFrame. *)
  (*   } *)

  (*   iPoseProof (mytk_find_some with "[MYTK TKS]") as "%FIND". iFrame. *)
  (*   rename n into NEQ2. iPoseProof (yourturn_range with "CASES") as "%LT". eapply FIND. auto. *)
  (*   clear NEQ2. iDestruct "CASES" as "[[%CT I] | [%CF [I | [I | I]]]]". *)
  (*   { subst own. iApply lock_yourturn_coind. auto. iSplit. iApply "CIH". *)
  (*     iSplitL "MYN". iFrame. iSplitL "MYTK". iFrame. iSplitL "TKS". iFrame. *)
  (*     iSplitL "MEM". iFrame. iSplitL "ST". iFrame. iSplitL "I". iFrame. iFrame. *)
  (*   } *)

  (*   { iPoseProof (ticket_lock_inv_mem_mono with "MEM") as "#MONOTK2". *)
  (*     iDestruct "I" as "[I0 [%I1 [I2 [I3 I4]]]]". *)
  (*     do 2 iDestruct "I4" as "[% I4]". iDestruct "I4" as "[I4 [I5 [I6 I7]]]". *)
  (*     iPoseProof (black_white_compare with "MONOW I4") as "%LE". *)
  (*     inv LE. *)
  (*     { remember (mytk - now) as ind. specialize (IH ind). *)
  (*       iApply IH. *)
  (*       { subst ind. lia. } *)
  (*       { auto. } *)
  (*       { eapply LT. } *)
  (*       { eapply Heqind. } *)
  (*       iSplit. *)
  (*       { iClear "MYN MYTK RIGHT TKS MEM ST I0 I2 I3 I4 I5 I6 I7 K". *)
  (*         iModIntro. iSplit. iApply "CIH". auto. *)
  (*       } *)
  (*       iSplitL "MYN". iFrame. iSplitL "MYTK". iFrame. iSplitL "TKS". iFrame. *)
  (*       iSplitL "ST". iFrame. iSplitR "K MEM". 2: iFrame. *)
  (*       iRight. iSplit. auto. iLeft. iFrame. iSplit. auto. iExists _, _. iFrame. *)
  (*     } *)
  (*     { inv ORD. hexploit H0. lia. i. clear H H0. subst k. *)
  (*       iClear "MONOTK2". *)
  (*       iPoseProof (ObligationRA.duty_correl_thread with "I7") as "#COR". *)
  (*       { ss. left; eauto. } *)
  (*       iPoseProof (ObligationRA.correl_thread_correlate with "COR RIGHT") as ">[DROP | FF]". *)
  (*       2:{ iPoseProof (ObligationRA.pending_not_shot with "I6 FF") as "%FF". inv FF. } *)
  (*       iPoseProof (ObligationRA.black_white_decr with "BLK DROP") as ">[%o_now [#OBLK2 %DROP]]". *)
  (*       iClear "BLK". *)
  (*       specialize (IHo o_now). *)
  (*       iApply IHo. *)
  (*       { rewrite Hessenberg.add_S_r in DROP. rewrite Hessenberg.add_O_r in DROP. *)
  (*         eapply Ord.lt_le_lt. 2: eapply DROP. apply Ord.S_lt. *)
  (*       } *)
  (*       { auto. } *)
  (*       iSplit. *)
  (*       { iClear "MYN MYTK TKS MEM ST I0 I2 I3 I4 I5 I6 I7 K". *)
  (*         iModIntro. iSplit. iApply "CIH". iSplit; auto. *)
  (*       } *)
  (*       iSplitL "MYN". iFrame. iSplitL "MYTK". iFrame. iSplitL "TKS". iFrame. *)
  (*       iSplitL "MEM". iFrame. iSplitL "ST". iFrame. iSplitR "K". 2: iFrame. *)
  (*       iFrame. iSplit. auto. iExists _, _. iFrame. *)
  (*     } *)
  (*   } *)
  (*   { iPoseProof (unlocked0_contra with "I") as "%FF". eauto. inv FF. } *)

  (*   { iPoseProof (ticket_lock_inv_mem_mono with "MEM") as "#MONOTK2". *)
  (*     do 2 iDestruct "I" as "[% I]". iDestruct "I" as "[I0 [I1 [%I2 [I3 [I4 I5]]]]]". *)
  (*     do 3 iDestruct "I5" as "[% I5]". iDestruct "I5" as "[I5 [I6 [I7 [I8 [I9 I10]]]]]". *)
  (*     iPoseProof (black_white_compare with "MONOW I5") as "%LE". *)
  (*     inv LE. *)
  (*     { remember (mytk - now) as ind. specialize (IH ind). *)
  (*       iApply IH. *)
  (*       { subst ind. lia. } *)
  (*       { auto. } *)
  (*       { eapply LT. } *)
  (*       { eapply Heqind. } *)
  (*       iSplit. *)
  (*       { iClear "MYN MYTK RIGHT TKS MEM ST I0 I1 I3 I4 I5 I6 I7 I8 I9 I10 K". *)
  (*         iModIntro. iSplit. iApply "CIH". auto. *)
  (*       } *)
  (*       iSplitL "MYN". iFrame. iSplitL "MYTK". iFrame. iSplitL "TKS". iFrame. *)
  (*       iSplitL "ST". iFrame. iSplitR "K MEM". 2: iFrame. *)
  (*       iRight. iSplit. auto. iRight. iRight. iFrame. *)
  (*       iExists yourt, waits. iSplit. auto. iSplit. auto. iFrame. *)
  (*       iExists k, o, u. iFrame. *)
  (*     } *)
  (*     { exfalso. inv ORD. lia. } *)
  (*   } *)
  (* Qed. *)

  (* Lemma lock_yourturn_ind1 *)
  (*       (g0 g1 : ∀ R_src R_tgt : Type, *)
  (*           (R_src → R_tgt → iProp) *)
  (*           → bool *)
  (*           → bool *)
  (*           → itree ((eventE +' cE) +' sE (Mod.state AbsLockW.mod)) R_src *)
  (*           → itree ((eventE +' cE) +' sE (OMod.closed_state TicketLock.omod (WMem.mod TicketLock.gvs))) R_tgt → iProp) *)
  (*       (tid : nat) *)
  (*       (mytk : TicketLockW.tk) *)
  (* (now : nat) *)
  (* (LT : now < mytk) *)
  (* (IH : ∀ y : nat, *)
  (*        y < mytk - now *)
  (*        → ∀ now_old : nat, *)
  (*            mytk ≠ now_old *)
  (*            → ∀ (mem : WMem.t) (own : bool) (l : list nat) (tks : NatMap.t nat) *)
  (*                (now next myt : nat), *)
  (*                now < mytk *)
  (*                → y = mytk - now *)
  (*                  → (□ ((∀ a : TicketLockW.tk, *)
  (*                           (OwnM (Auth.white (NatMapRA.singleton tid a: NatMapRA.t nat)) ** *)
  (*                            maps_to tid (Auth.white (Excl.just 2: Excl.t nat))) -* *)
  (*                           g1 ()%type ()%type *)
  (*                             (λ r_src r_tgt : (), *)
  (*                                (own_thread tid ** ObligationRA.duty (inl tid) []) ** *)
  (*                                ⌜r_src = r_tgt⌝) false false *)
  (*                             (src_code_coind tid) *)
  (*                             (tgt_code_coind a) *)
  (*                        ) ∧ monoWhite tk_mono Nat.le_preorder now) ** *)
  (*                     (maps_to tid (Auth.white (Excl.just 2: Excl.t nat)) ** *)
  (*                      (OwnM (Auth.white (NatMapRA.singleton tid mytk: NatMapRA.t nat)) ** *)
  (*                       (ticket_lock_inv_tks tks ** *)
  (*                        (ticket_lock_inv_state mem own tks ** *)
  (*                         ((⌜own = true⌝ ** ticket_lock_inv_locked l tks now next myt) *)
  (*                          ∨ (⌜own = false⌝ ** *)
  (*                             ticket_lock_inv_unlocking l tks now next myt *)
  (*                             ∨ ticket_lock_inv_unlocked0 l tks now next myt *)
  (*                               ∨ ticket_lock_inv_unlocked1 l tks now next myt) ** *)
  (*                          ((ticket_lock_inv -* *)
  (*                            MUpd (nth_default True%I I) *)
  (*                              (fairI *)
  (*                                 (ident_tgt:=OMod.closed_ident TicketLock.omod *)
  (*                                               (WMem.mod TicketLock.gvs))) [] [0] True) ** *)
  (*                           ticket_lock_inv_mem mem now next myt))))))) *)
  (*                    ⊢ stsim I tid [] g0 g1 *)
  (*                        (λ r_src r_tgt : (), *)
  (*                           (own_thread tid ** ObligationRA.duty (inl tid) []) ** ⌜r_src = r_tgt⌝) *)
  (*                        false true *)
  (*                        (src_code_ind tid) *)
  (*                        (tgt_code_ind mytk now_old) *)
  (* ) *)
  (* (now_old : nat) *)
  (* (NEQ : mytk ≠ now_old) *)
  (* (mem : WMem.t) *)
  (* (l : list nat) *)
  (* (tks : NatMap.t nat) *)
  (* (next myt : nat) *)
  (*   : *)
  (* (□ ((∀ a : TicketLockW.tk, *)
  (*       (OwnM (Auth.white (NatMapRA.singleton tid a: NatMapRA.t nat)) ** maps_to tid (Auth.white (Excl.just 2: Excl.t nat))) -* *)
  (*       g1 ()%type ()%type *)
  (*         (λ r_src r_tgt : (), *)
  (*            (own_thread tid ** ObligationRA.duty (inl tid) []) ** ⌜r_src = r_tgt⌝) false false *)
  (*         (src_code_coind tid) *)
  (*         (tgt_code_coind a)) *)
  (*         ∧ *)
  (* (monoWhite tk_mono Nat.le_preorder now) *)
  (*    ) ** *)
  (*  (maps_to tid (Auth.white (Excl.just 2: Excl.t nat)) ** *)
  (*   (OwnM (Auth.white (NatMapRA.singleton tid mytk: NatMapRA.t nat)) ** *)
  (*    (ticket_lock_inv_tks tks ** *)
  (*     (ticket_lock_inv_mem mem now next myt ** *)
  (*      (ticket_lock_inv_state mem false tks ** *)
  (*       (ticket_lock_inv_unlocked1 l tks now next myt ** *)
  (*        (ticket_lock_inv -* *)
  (*         MUpd (nth_default True%I I) *)
  (*           (fairI (ident_tgt:=OMod.closed_ident TicketLock.omod (WMem.mod TicketLock.gvs))) [] *)
  (*           [0] True))))))) *)
  (* ) *)
  (* ⊢ (stsim I tid [] g0 g1 *)
  (*     (λ r_src r_tgt : (), (own_thread tid ** ObligationRA.duty (inl tid) []) ** ⌜r_src = r_tgt⌝) *)
  (*     false true *)
  (*     (trigger Yield;;; *)
  (*      ` x : () + () <- *)
  (*      (` x_0 : bool * NatMap.t () <- trigger (Get (bool * NatMap.t ()));; *)
  (*       (let (own0, _) := x_0 in if Bool.eqb own0 true then Ret (inl ()) else Ret (inr ())));; *)
  (*      match x with *)
  (*      | inl l0 => *)
  (*          tau;; ITree.iter *)
  (*                  (λ _ : (), *)
  (*                     trigger Yield;;; *)
  (*                     ` x_0 : bool * NatMap.t () <- trigger (Get (bool * NatMap.t ()));; *)
  (*                     (let (own0, _) := x_0 in *)
  (*                      if Bool.eqb own0 true then Ret (inl ()) else Ret (inr ()))) l0 *)
  (*      | inr r0 => Ret r0 *)
  (*      end;;; *)
  (*      ` x_0 : bool * NatMap.t () <- trigger (Get (bool * NatMap.t ()));; *)
  (*      (let (_, ts0) := x_0 in *)
  (*       trigger (Put (true, NatMap.remove (elt:=()) tid ts0));;; *)
  (*       trigger *)
  (*         (Fair *)
  (*            (λ i : nat, *)
  (*               if tid_dec i tid *)
  (*               then Flag.success *)
  (*               else *)
  (*                if NatMapP.F.In_dec (NatMap.remove (elt:=()) tid ts0) i *)
  (*                then Flag.fail *)
  (*                else Flag.emp));;; trigger Yield;;; Ret ())) *)
  (*     (` r : Any.t <- *)
  (*      OMod.embed_itree TicketLock.omod (WMem.mod TicketLock.gvs) *)
  (*        (Mod.wrap_fun WMem.compare_fun (Any.upcast (WMem.val_nat now_old, WMem.val_nat mytk)));; *)
  (*      ` x : bool <- (tau;; unwrap (Any.downcast r));; *)
  (*      OMod.close_itree TicketLock.omod (WMem.mod TicketLock.gvs) *)
  (*        (if x then Ret () else tau;; TicketLock.lock_loop (WMem.val_nat mytk));;; *)
  (*      OMod.close_itree TicketLock.omod (WMem.mod TicketLock.gvs) (trigger Yield))). *)
  (* Proof. *)
  (*   iIntros "[#[CIH MONOTK] [MYN [MYTK [TKS [MEM [ST [I K]]]]]]]". *)
  (*   iPoseProof (mytk_find_some with "[MYTK TKS]") as "%FIND". iFrame. *)
  (*   iPoseProof (unlocked1_mono with "I") as "[%TKQ #[% [% [MONOW OBLB]]]]". *)
  (*   clear FIND TKQ. *)
  (*   iStopProof. move o before IH. revert_until o. pattern o. revert o. *)
  (*   apply (well_founded_induction Ord.lt_well_founded). *)
  (*   intros o IHo. intros. *)
  (*   iIntros "[#[CIH [MONOTK [MONOW BLK]]] [MYN [MYTK [TKS [MEM [ST [I K]]]]]]]". *)

  (*   unfold Mod.wrap_fun, WMem.compare_fun. rred. *)
  (*   iDestruct "MEM" as "[MEM0 [MEM1 [MEM2 MEM3]]]". iDestruct "ST" as "[ST0 ST1]". *)
  (*   iApply stsim_getR. iSplit. eauto. rred. *)
  (*   iApply stsim_tauR. rred. iApply stsim_tauR. rred. *)
  (*   destruct (Nat.eq_dec now_old mytk). *)
  (*   { exfalso. clarify. } *)
  (*   rred. iApply stsim_tauR. *)
  (*   rewrite TicketLock.lock_loop_red. rred. rewrite close_itree_call. rred. *)
  (*   iAssert (ticket_lock_inv_mem mem now next myt)%I with "[MEM0 MEM1 MEM2 MEM3]" as "MEM". iFrame. *)
  (*   iAssert (ticket_lock_inv_state mem false tks)%I with "[ST0 ST1]" as "ST". iFrame. *)
  (*   iMod ("K" with "[TKS MEM ST I]") as "_". *)
  (*   { do 7 iExists _. iSplitL "TKS". iFrame. iSplitL "MEM". iFrame. iSplitL "ST". iFrame. *)
  (*     iRight. iSplit. auto. iRight. iRight. iFrame. *)
  (*   } *)
  (*   clear mem l tks next myt now_old NEQ n. *)
  (*   rename now into now_past, LT into LTPAST, k into k_past, o into o_past. *)

  (*   iopen 0 "I" "K". do 7 iDestruct "I" as "[% I]". iDestruct "I" as "[TKS [MEM [ST CASES]]]". *)
  (*   destruct (Nat.eq_dec mytk now); subst. *)
  (*   { iClear "CIH". *)
  (*     iApply lock_myturn1. *)
  (*     iSplitL "MYTK". iFrame. iSplitL "MYN". iFrame. iSplitL "TKS". iFrame. *)
  (*     iSplitL "MEM". iFrame. iSplitL "ST". iFrame. iSplitL "CASES". iFrame. *)
  (*     iFrame. *)
  (*   } *)

  (*   rename n into NEQ. *)
  (*   iApply lock_yourturn_yieldR. eapply NEQ. *)
  (*   iSplitL "MYTK TKS MEM ST CASES K". *)
  (*   iSplitL "MYTK". iFrame. iSplitL "TKS". iFrame. iSplitL "MEM". iFrame. *)
  (*   iSplitL "ST". iFrame. iSplitL "CASES". iFrame. iFrame. *)
  (*   iIntros "[MYTK _]". rred. *)
  (*   clear mem own l tks now next myt NEQ. *)
  (*   iopen 0 "I" "K". do 7 iDestruct "I" as "[% I]". iDestruct "I" as "[TKS [MEM [ST CASES]]]". *)
  (*   destruct (Nat.eq_dec mytk now); subst. *)
  (*   { iClear "CIH". *)
  (*     iPoseProof (mytk_find_some with "[MYTK TKS]") as "%FIND". iFrame. *)
  (*     iDestruct "CASES" as "[[%CT I] | [%CF [I | [I | I]]]]". *)
  (*     { iPoseProof (locked_contra with "I") as "%F". eauto. inv F. } *)
  (*     { iPoseProof (unlocking_contra with "I") as "%F". eauto. inv F. } *)
  (*     { iPoseProof (unlocked0_contra with "I") as "%F". eauto. inv F. } *)
  (*     iPoseProof (unlocked1_mono with "I") as "[%TKQ #[% [% [MYTN _]]]]". *)
  (*     iMod ("K" with "[TKS MEM ST I]") as "_". *)
  (*     { do 7 iExists _. iSplitL "TKS". iFrame. iSplitL "MEM". iFrame. iSplitL "ST". iFrame. *)
  (*       iRight. iSplit. auto. iFrame. *)
  (*     } *)
  (*     iApply lock_myturn0. 2: iFrame; auto. lia. *)
  (*   } *)

  (*   rename n into NEQ. unfold Mod.wrap_fun, WMem.load_fun. rred. *)
  (*   iDestruct "MEM" as "[MEM0 [MEM1 [MEM2 MEM3]]]". iDestruct "ST" as "[ST0 ST1]". *)
  (*   iApply stsim_getR. iSplit. eauto. rred. *)
  (*   iApply stsim_tauR. rred. *)
  (*   iPoseProof (memory_ra_load with "MEM0 MEM1") as "%LOAD". des. rewrite LOAD. rred. *)
  (*   iApply stsim_tauR. rred. *)
  (*   rewrite close_itree_call. rred. *)
  (*   iApply lock_yourturn_yieldR. eapply NEQ. *)
  (*   iSplitL "MYTK TKS MEM0 MEM1 MEM2 MEM3 ST0 ST1 CASES K". *)
  (*   iSplitL "MYTK". iFrame. iSplitL "TKS". iFrame. iSplitL "MEM0 MEM1 MEM2 MEM3". iFrame. *)
  (*   iSplitL "ST0 ST1". iFrame. iSplitL "CASES". iFrame. iFrame. *)
  (*   iIntros "[MYTK RIGHT]". rred. *)
  (*   rename now into now_old. clear mem own l tks next myt LOAD LOAD0. *)

  (*   iopen 0 "I" "K". do 7 iDestruct "I" as "[% I]". iDestruct "I" as "[TKS [MEM [ST CASES]]]". *)
  (*   destruct (Nat.eq_dec mytk now); subst. *)
  (*   { iClear "CIH". iApply lock_myturn2. auto. *)
  (*     iSplitL "MYTK". iFrame. iSplitL "MYN". iFrame. iSplitL "TKS". iFrame. *)
  (*     iSplitL "MEM". iFrame. iSplitL "ST". iFrame. iSplitL "CASES". iFrame. *)
  (*     iFrame. *)
  (*   } *)

  (*   iPoseProof (mytk_find_some with "[MYTK TKS]") as "%FIND". iFrame. *)
  (*   rename n into NEQ2. iPoseProof (yourturn_range with "CASES") as "%LT". eapply FIND. auto. *)
  (*   clear NEQ2. iDestruct "CASES" as "[[%CT I] | [%CF [I | [I | I]]]]". *)
  (*   { subst own. iApply lock_yourturn_coind. auto. iSplit. iApply "CIH". *)
  (*     iSplitL "MYN". iFrame. iSplitL "MYTK". iFrame. iSplitL "TKS". iFrame. *)
  (*     iSplitL "MEM". iFrame. iSplitL "ST". iFrame. iSplitL "I". iFrame. iFrame. *)
  (*   } *)

  (*   { iPoseProof (ticket_lock_inv_mem_mono with "MEM") as "#MONOTK2". *)
  (*     iAssert (⌜now_past <= now⌝)%I with "[MEM]" as "%PROG". *)
  (*     { iDestruct "MEM" as "[MEM0 [MEM1 [MEM2 [MEM3 MEM4]]]]". *)
  (*       iPoseProof (black_white_compare with "MONOTK MEM4") as "%". auto. *)
  (*     } *)
  (*     iApply lock_yourturn_ind0. apply LT. *)
  (*     { clear IHo. move LT before IH. move PROG before LT. clear_upto PROG. *)
  (*       intros y H. eapply IH. lia. *)
  (*     } *)
  (*     auto. *)
  (*     iSplit. *)
  (*     { iClear "MYN MYTK RIGHT TKS MEM ST I K". iModIntro. iSplit. iApply "CIH". auto. } *)
  (*     iSplitL "MYN". iFrame. iSplitL "MYTK". iFrame. iSplitL "TKS". iFrame. iSplitL "MEM". iFrame. *)
  (*     iSplitL "ST". subst. iFrame. iSplitR "K". 2: iFrame. *)
  (*     iFrame. *)
  (*   } *)

  (*   { iPoseProof (unlocked0_contra with "I") as "%FF". eauto. inv FF. } *)

  (*   { iPoseProof (ticket_lock_inv_mem_mono with "MEM") as "#MONOTK2". *)
  (*     do 2 iDestruct "I" as "[% I]". iDestruct "I" as "[I0 [%I1 [%I2 [I3 [I4 I5]]]]]". *)
  (*     do 3 iDestruct "I5" as "[% I5]". iDestruct "I5" as "[I5 [I6 [I7 [I8 [I9 I10]]]]]". *)
  (*     iPoseProof (black_white_compare with "MONOW I5") as "%LE". *)
  (*     inv LE. *)
  (*     { remember (mytk - now) as ind. specialize (IH ind). *)
  (*       iApply IH. *)
  (*       { subst ind. lia. } *)
  (*       { auto. } *)
  (*       { eapply LT. } *)
  (*       { eapply Heqind. } *)
  (*       iSplit. *)
  (*       { iClear "MYN MYTK RIGHT TKS MEM ST I0 I3 I4 I5 I6 I7 I8 I9 I10 K". *)
  (*         iModIntro. iSplit. iApply "CIH". auto. *)
  (*       } *)
  (*       iSplitL "MYN". iFrame. iSplitL "MYTK". iFrame. iSplitL "TKS". iFrame. *)
  (*       iSplitL "ST". iFrame. iSplitR "K MEM". 2: iFrame. *)
  (*       iRight. iSplit. auto. iRight. iRight. iFrame. iExists yourt, waits. *)
  (*       iSplit. auto. iSplit. auto. iFrame. iExists k, o, u. iFrame. *)
  (*     } *)
  (*     { inv ORD. hexploit H0. lia. i. clear H H0. subst k. *)
  (*       iClear "MONOTK2". *)
  (*       iPoseProof (ObligationRA.duty_correl_thread with "I8") as "#COR". *)
  (*       { ss. left; eauto. } *)
  (*       iPoseProof (ObligationRA.correl_thread_correlate with "COR RIGHT") as ">[DROP | FF]". *)
  (*       2:{ iPoseProof (ObligationRA.pending_not_shot with "I7 FF") as "%FF". inv FF. } *)
  (*       iPoseProof (ObligationRA.black_white_decr with "BLK DROP") as ">[%o_now [#OBLK2 %DROP]]". *)
  (*       iClear "BLK". *)
  (*       specialize (IHo o_now). iApply IHo. *)
  (*       { rewrite Hessenberg.add_S_r in DROP. rewrite Hessenberg.add_O_r in DROP. *)
  (*         eapply Ord.lt_le_lt. 2: eapply DROP. apply Ord.S_lt. *)
  (*       } *)
  (*       { auto. } *)
  (*       iSplit. *)
  (*       { iClear "MYN MYTK TKS MEM ST I0 I3 I4 I5 I6 I7 I8 I9 I10 K". *)
  (*         iModIntro. iSplit. iApply "CIH". auto. *)
  (*       } *)
  (*       iSplitL "MYN". iFrame. iSplitL "MYTK". iFrame. iSplitL "TKS". iFrame. *)
  (*       iSplitL "MEM". iFrame. iSplitL "ST". iFrame. iSplitR "K". 2: iFrame. *)
  (*       iFrame. iExists yourt, waits. *)
  (*       iSplit. auto. iSplit. auto. iFrame. iExists _, _, u. iFrame. *)
  (*     } *)
  (*   } *)
  (* Qed. *)

  Lemma correct_lock tid tvw:
    ((own_thread tid)
       ∗ (ObligationRA.duty (inl tid) [])
    )
      ⊢
      (stsim I tid (topset I) ibot7 ibot7
             (fun r_src r_tgt => own_thread tid ** ObligationRA.duty (inl tid) [] ** ⌜r_src = r_tgt⌝)
             false false
             (AbsLockW.lock_fun tvw)
             (OMod.close_itree TicketLockW.omod (WMem.mod)
                               (TicketLockW.lock_fun tvw))).
  Proof.
    iIntros "[MYTH DUTY]".
    iApply lock_enqueue. iSplitL. iFrame.
    iIntros "% % [MYTK [MYN TVLE]]".
    rewrite TicketLockW.lock_loop_red. rred. rewrite close_itree_call. rred.
    iStopProof. revert tview. eapply stsim_coind. msubtac.
    iIntros "% %tview". iIntros "#[_ CIH] [MYTK [MYN %TVLE]]".

    iopen 0 "I" "K". do 12 iDestruct "I" as "[% I]". iDestruct "I" as "[TKS [MEM [ST CASES]]]".
    destruct (Nat.eq_dec mytk now); subst.
    { iClear "CIH".
      rewrite unfold_iter_eq. lred.
      iApply lock_myturn1. auto.
      iSplitL "MYTK". iFrame. iSplitL "MYN". iFrame. iSplitL "TKS". iFrame.
      iSplitL "MEM". iFrame. iSplitL "ST". iFrame. iSplitL "CASES". iFrame.
      iFrame.
    }

    rename n into NEQ. rewrite unfold_iter_eq. lred.
    iDestruct "MEM" as "[MEM %SVLE]".
    iApply lock_yourturn_yieldR. eapply SVLE. eapply NEQ.
    iSplitL "MYTK TKS MEM ST CASES K".
    iSplitL "MYTK". iFrame. iSplitL "TKS". iFrame. iSplitL "MEM". iFrame.
    iSplitL "ST". iFrame. iSplitL "CASES". iFrame. iFrame.
    iIntros "[MYTK _]". rred.
    clear_upto TVLE.
    (* clear mem own ing  l tks now next myt NEQ. *)
    iopen 0 "I" "K". do 12 iDestruct "I" as "[% I]". iDestruct "I" as "[TKS [MEM [ST CASES]]]".
    destruct (Nat.eq_dec mytk now); subst.
    { iClear "CIH".
      iPoseProof (mytk_find_some with "[MYTK TKS]") as "%FIND". iFrame.
      iDestruct "CASES" as "[[%CT [[% I] | [% I]]] | [%CF [%CF2 [I | I]]]]".
      { iPoseProof (locked_contra with "I") as "%F". eauto. inv F. }
      { iPoseProof (unlocking_contra with "I") as "%F". eauto. inv F. }
      { iPoseProof (unlocked0_contra with "I") as "%F". eauto. inv F. }
      iPoseProof (unlocked1_mono with "I") as "[%TKQ #[% [% [MYTN _]]]]".
      iMod ("K" with "[TKS MEM ST I]") as "_".
      { do 12 iExists _. iSplitL "TKS". iFrame. iSplitL "MEM". iFrame. iSplitL "ST". iFrame.
        iRight. iSplit. auto. iSplit. auto. iFrame.
      }
      iApply lock_myturn0. auto. iFrame; auto.
    }

    rename n into NEQ.
    iPoseProof (mytk_find_some with "[MYTK TKS]") as "%FIND". iFrame.
    iPoseProof (yourturn_range with "CASES") as "%LT". eapply FIND. auto.
    clear NEQ FIND.
    (* TODO *)



    
    unfold Mod.wrap_fun, WMem.load_fun. rred.
    iDestruct "MEM" as "[MEM0 [MEM1 [MEM2 MEM3]]]". iDestruct "ST" as "[ST0 ST1]".
    iApply stsim_getR. iSplit. eauto. rred.
    iApply stsim_tauR. rred.
    iPoseProof (memory_ra_load with "MEM0 MEM1") as "%LOAD". des. rewrite LOAD. rred.
    iApply stsim_tauR. rred.
    rewrite close_itree_call. rred.
    iApply lock_yourturn_yieldR. eapply NEQ.
    iSplitL "MYTK TKS MEM0 MEM1 MEM2 MEM3 ST0 ST1 CASES K".
    iSplitL "MYTK". iFrame. iSplitL "TKS". iFrame. iSplitL "MEM0 MEM1 MEM2 MEM3". iFrame.
    iSplitL "ST0 ST1". iFrame. iSplitL "CASES". iFrame. iFrame.
    iIntros "[MYTK _]". rred.
    rename now into now_old. clear mem own l tks next myt LOAD LOAD0.

    iopen 0 "I" "K". do 7 iDestruct "I" as "[% I]". iDestruct "I" as "[TKS [MEM [ST CASES]]]".
    destruct (Nat.eq_dec mytk now); subst.
    { iClear "CIH". iApply lock_myturn2. auto.
      iSplitL "MYTK". iFrame. iSplitL "MYN". iFrame. iSplitL "TKS". iFrame.
      iSplitL "MEM". iFrame. iSplitL "ST". iFrame. iSplitL "CASES". iFrame.
      iFrame.
    }

    rename n into NEQ2.
    iPoseProof (mytk_find_some with "[MYTK TKS]") as "%FIND". iFrame.
    iDestruct "MEM" as "[MEM0 [MEM1 [MEM2 [MEM3 MEM4]]]]".
    iPoseProof (black_white with "MEM4") as "#MONOTK".
    iAssert (ticket_lock_inv_mem mem now next myt)%I with "[MEM0 MEM1 MEM2 MEM3 MEM4]" as "MEM".
    iFrame.
    iPoseProof (yourturn_range with "CASES") as "%LT". eapply FIND. auto.
    clear FIND NEQ2.
    remember (mytk - now) as ind.
    iStopProof. move ind before mytk. revert_until ind. pattern ind. revert ind.
    apply (well_founded_induction Nat.lt_wf_0).
    intros ind IH. intros.
    iIntros "[#[CIH MONOTK] [MYN [MYTK [TKS [ST [CASES [K MEM]]]]]]]".

    iDestruct "CASES" as "[[%CT I] | [%CF [I | [I | I]]]]".
    { subst own. iApply lock_yourturn_coind. auto. iSplit. iApply "CIH".
      iSplitL "MYN". iFrame. iSplitL "MYTK". iFrame. iSplitL "TKS". iFrame.
      iSplitL "MEM". iFrame. iSplitL "ST". iFrame. iSplitL "I". iFrame. iFrame.
    }
    { subst. iApply lock_yourturn_ind0. apply LT. apply IH. auto.
      iSplit.
      { iClear "MYN MYTK TKS MEM ST I K".
        iModIntro. iSplit. iApply "CIH". auto.
      }
      iSplitL "MYN". iFrame. iSplitL "MYTK". iFrame. iSplitL "TKS". iFrame.
      iSplitL "MEM". iFrame. iSplitL "ST". iFrame. iSplitR "K". 2: iFrame.
      iFrame.
    }
    { iPoseProof (mytk_find_some with "[MYTK TKS]") as "%FIND". iFrame.
      iPoseProof (unlocked0_contra with "I") as "%FF". eauto. inv FF.
    }
    { subst. iApply lock_yourturn_ind1. apply LT. apply IH. auto.
      iSplit.
      { iClear "MYN MYTK TKS MEM ST I K". iModIntro. iSplit. iApply "CIH". auto. }
      iSplitL "MYN". iFrame. iSplitL "MYTK". iFrame. iSplitL "TKS". iFrame.
      iSplitL "MEM". iFrame. iSplitL "ST". iFrame. iSplitR "K". 2: iFrame.
      iFrame.
    }

  Qed.

  Lemma correct_unlock tid:
    ((own_thread tid)
       ∗ (ObligationRA.duty (inl tid) [])
    )
      ⊢
      (stsim I tid (topset I) ibot7 ibot7
             (fun r_src r_tgt => own_thread tid ** ObligationRA.duty (inl tid) [] ** ⌜r_src = r_tgt⌝)
             false false
             (AbsLock.unlock_fun tt)
             (OMod.close_itree TicketLock.omod (WMem.mod TicketLock.gvs)
                               (TicketLock.unlock_fun tt))).
  Proof.
    iIntros "[MYTH DUTY]".
    unfold AbsLock.unlock_fun, TicketLock.unlock_fun. rred.
    rewrite close_itree_call. rred.
    iApply (stsim_sync with "[DUTY]"). msubtac. iFrame. iIntros "DUTY _".
    iopen 0 "I" "K". do 7 iDestruct "I" as "[% I]". iDestruct "I" as "[TKS [MEM [ST CASES]]]".
    iDestruct "CASES" as "[[%CT I] | [%CF [I | [I | I]]]]"; cycle 1.
    { subst own. iDestruct "ST" as "[ST0 ST1]".
      iApply stsim_getL. iSplit. auto. rred.
      destruct (Bool.eqb false true) eqn:BEQ. exfalso. inv BEQ.
      iApply stsim_UB.
    }
    { subst own. iDestruct "ST" as "[ST0 ST1]".
      iApply stsim_getL. iSplit. auto. rred.
      destruct (Bool.eqb false true) eqn:BEQ. exfalso. inv BEQ.
      iApply stsim_UB.
    }
    { subst own. iDestruct "ST" as "[ST0 ST1]".
      iApply stsim_getL. iSplit. auto. rred.
      destruct (Bool.eqb false true) eqn:BEQ. exfalso. inv BEQ.
      iApply stsim_UB.
    }

    subst own. iDestruct "ST" as "[ST0 ST1]".
    iApply stsim_getL. iSplit. auto. rred.
    destruct (Bool.eqb true true) eqn:BEQ. 2: exfalso; inv BEQ.
    clear BEQ.
    iApply (stsim_putL with "ST1"). iIntros "ST1".

    unfold Mod.wrap_fun, WMem.load_fun. rred.
    iDestruct "MEM" as "[MEM0 [MEM1 [MEM2 [MEM3 MEM4]]]]".
    iApply stsim_getR. iSplit. eauto. rred.
    iApply stsim_tauR. rred.
    iPoseProof (memory_ra_load with "MEM0 MEM1") as "%LOAD". des. rewrite LOAD. rred.
    iApply stsim_tauR. rred.
    rewrite close_itree_call. rred.

    iPoseProof (ObligationRA.alloc (((Ord.S Ord.O) × Ord.omega) × (Ord.from_nat 2))%ord) as "> [% [[OBLK OWHI] OPEND]]".
    iPoseProof (ObligationRA.white_eq with "OWHI") as "OWHI".
    { rewrite Ord.from_nat_S. rewrite Jacobsthal.mult_S. reflexivity. }
    iPoseProof (ObligationRA.white_split_eq with "OWHI") as "[OWHI TAX]".
    iPoseProof (ObligationRA.duty_alloc with "DUTY OWHI") as "> DUTY".

    iDestruct "I" as "[I0 [I1 [I2 [I3 [% I5]]]]]".
    iPoseProof (black_updatable with "I5") as ">I5".
    { instantiate (1:=(now, Tkst.d k)). econs 2. ss. split; try lia. }
    iPoseProof (black_white_update with "MEM3 I0") as ">[MEM3 HOLD]". instantiate (1:=(now, tid)).

    iApply (stsim_yieldR_strong with "[DUTY TAX]").
    { iSplitL "DUTY". iFrame. iApply ObligationRA.tax_cons_fold. iSplit. 2: auto.
      iApply ObligationRA.white_eq. 2: iFrame.
      rewrite Ord.from_nat_1. rewrite Jacobsthal.mult_1_r. reflexivity.
    }
    iIntros "DUTY _".
    iMod ("K" with "[MYTH TKS MEM0 MEM1 MEM2 MEM3 MEM4 ST0 ST1 I1 I2 I3 I5 OBLK OPEND DUTY]") as "_".
    { iExists mem, false, l, tks, now, next, tid.
      remember (
    (⌜false = true⌝ ** ticket_lock_inv_locked l tks now next tid)
    ∨ (⌜false = false⌝ **
       ticket_lock_inv_unlocking l tks now next tid
       ∨ ticket_lock_inv_unlocked0 l tks now next tid
       ∨ ticket_lock_inv_unlocked1 l tks now next tid))%I as temp.
      iFrame. subst temp.
      iRight. iSplit. auto. iLeft. iFrame.
      iExists _, _. iFrame.
    }
    iModIntro. clear_upto tid.

    iopen 0 "I" "K". do 7 iDestruct "I" as "[% I]". iDestruct "I" as "[TKS [MEM [ST CASES]]]".
    iDestruct "CASES" as "[[%CT I] | [%CF [I | [I | I]]]]"; cycle 2.
    { iDestruct "I" as "[I _]". iPoseProof (white_white_excl with "HOLD I") as "%FF". inv FF. }
    { do 2 iDestruct "I" as "[% I]". iDestruct "I" as "[I _]".
      iPoseProof (white_white_excl with "HOLD I") as "%FF". inv FF. }
    { iDestruct "I" as "[I _]". iPoseProof (white_white_excl with "HOLD I") as "%FF". inv FF. }

    unfold Mod.wrap_fun, WMem.store_fun. rred.
    iDestruct "ST" as "[ST0 ST1]". iDestruct "MEM" as "[MEM0 [MEM1 [MEM2 [MEM3 MEM4]]]]".
    iApply stsim_getR. iSplit. auto. rred.
    iApply stsim_tauR. rred.
    iPoseProof (memory_ra_store with "MEM0 MEM1") as "[% [%STORE >[MEM0 MEM1]]]".
    rewrite STORE. rred.
    iApply stsim_getR. iSplit. auto. rred.
    iApply (stsim_putR with "ST0"). iIntros "ST0". rred.
    iApply stsim_tauR. rred. iApply stsim_tauR. rred.

    iPoseProof (black_white_equal with "MEM3 HOLD") as "%EQ". inv EQ.
    remember (S now) as now'.
    replace (now + 1) with now'. 2: lia.
    iPoseProof (black_white_update with "MEM3 HOLD") as ">[MEM3 HOLD]". instantiate (1:=(now', tid)).
    iPoseProof (black_updatable with "MEM4") as ">MEM4".
    { instantiate (1:=now'). lia. }
    iDestruct "I" as "[I1 [%I2 [I3 [I4 I5]]]]".
    do 2 iDestruct "I5" as "[% I5]". iDestruct "I5" as "[I5 [_ [OPEND DUTY]]]".
    iPoseProof (ObligationRA.pending_shot with "OPEND") as ">OSHOT".
    iPoseProof (ObligationRA.duty_done with "DUTY OSHOT") as ">DUTY".

    destruct l as [ | yourt waits].
    { iPoseProof (black_updatable with "I5") as ">I5".
      { instantiate (1:=(now', Tkst.a k)). econs 1; try lia. }
      iAssert (ticket_lock_inv_mem m1 now' next tid)%I with "[MEM0 MEM1 MEM2 MEM3 MEM4]" as "MEM".
      iFrame.
      iAssert (ticket_lock_inv_state m1 false tks)%I with "[ST0 ST1]" as "ST". iFrame.
      iMod ("K" with "[TKS MEM ST I3 I4 I5 HOLD]") as "_".
      { do 7 iExists _. iSplitL "TKS". iFrame. iSplitL "MEM". iFrame. iSplitL "ST". iFrame.
        iRight. iSplit. auto. iRight. iLeft. iFrame. iSplit.
        iPureIntro. split; eauto. inv I2; ss.
        iExists _. iFrame.
      }
      iApply (stsim_sync with "[DUTY]"). msubtac. iFrame. iIntros "DUTY _".
      iApply stsim_tauR.
      iApply stsim_ret. iModIntro. iFrame. auto.
    }

    iPoseProof (list_prop_sum_cons_unfold with "I4") as "[[YDUTY [% YMAPS]] I4]".
    iPoseProof (ObligationRA.alloc (((Ord.S Ord.O) × Ord.omega) × (Ord.S (Ord.from_nat u)))%ord) as "> [% [[OBLK OWHI] OPEND]]".
    iPoseProof (ObligationRA.white_eq with "OWHI") as "OWHI".
    { rewrite Jacobsthal.mult_S. reflexivity. }
    iPoseProof (ObligationRA.white_split_eq with "OWHI") as "[OWHI YTAX]".
    iPoseProof (ObligationRA.duty_alloc with "YDUTY OWHI") as "> YDUTY".

    iPoseProof (black_updatable with "I5") as ">I5".
    { instantiate (1:=(now', Tkst.b k0)). econs 1; try lia. }
    iAssert (ticket_lock_inv_mem m1 now' next tid)%I with "[MEM0 MEM1 MEM2 MEM3 MEM4]" as "MEM".
    iFrame.
    iAssert (ticket_lock_inv_state m1 false tks)%I with "[ST0 ST1]" as "ST". iFrame.
    iMod ("K" with "[TKS MEM ST I3 HOLD YMAPS I4 OBLK OPEND YTAX YDUTY I5]") as "_".
    { subst now'. do 7 iExists _. iSplitL "TKS". iFrame. iSplitL "MEM". iFrame.
      iSplitL "ST". iFrame. iRight. iSplit. auto. iRight. iRight. iExists yourt, waits.
      iFrame. iSplit. auto. iSplit. auto.
      iExists k0, _, u. iFrame.
    }
    iApply (stsim_sync with "[DUTY]"). msubtac. iFrame. iIntros "DUTY _".
    iApply stsim_tauR.
    iApply stsim_ret. iModIntro. iFrame. auto.

  Qed.







  (* Lemma ticketlock_fair: *)
  (*   ModSim.mod_sim FairLockW.mod TicketLockW.mod. *)
  (* Admitted. *)
  Lemma ticketlock_fair:
    ModSim.mod_sim AbsLockW.mod TicketLockW.mod.
  Admitted.
End SIM.
