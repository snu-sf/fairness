From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
Unset Universe Checking.
From Fairness Require Export ITreeLib WFLib FairBeh NatStructs Mod pind Axioms OpenMod SCM Red IRed Wrapper WeakestAdequacy.
From Ordinal Require Export ClassicalHessenberg.

Set Implicit Arguments.

Module TicketLock.
  Definition gvs : list nat := [2].
  Definition now_serving: SCMem.val := SCMem.val_ptr (0, 0).
  Definition next_ticket: SCMem.val := SCMem.val_ptr (0, 1).

  Definition tk := nat.

  Definition lock_loop (myticket: SCMem.val):
    itree ((((@eventE void) +' cE) +' (sE unit)) +' OpenMod.callE) unit
    :=
    ITree.iter
      (fun (_: unit) =>
         now <- (OMod.call "load" (now_serving));;
         b <- (OMod.call "compare" (now: SCMem.val, myticket: SCMem.val));;
         if (b: bool) then Ret (inr tt) else Ret (inl tt)) tt.

  Lemma lock_loop_red myticket
    :
    lock_loop myticket
    =
      now <- (OMod.call "load" (now_serving));;
      b <- (OMod.call "compare" (now: SCMem.val, myticket: SCMem.val));;
      if (b: bool)
      then Ret tt else tau;; lock_loop myticket.
  Proof.
    unfold lock_loop. etransitivity.
    { apply unfold_iter_eq. }
    grind.
  Qed.

  Definition lock_fun:
    ktree ((((@eventE void) +' cE) +' (sE unit)) +' OpenMod.callE) unit unit :=
    fun _ =>
      myticket <- (OMod.call "faa" (next_ticket, 1));;
      _ <- lock_loop myticket;;
      trigger Yield
  .

  Definition unlock_fun:
    ktree ((((@eventE void) +' cE) +' (sE unit)) +' OpenMod.callE) unit unit :=
    fun _ =>
      upd <- (OMod.call "load" now_serving);;
      let upd := SCMem.val_add upd 1 in
      `_: unit <- (OMod.call "store" (now_serving, upd));;
      trigger Yield
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
      (SCMem.mod gvs)
  .

End TicketLock.



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
            (l: list thread_id) (tks: NatMap.t TicketLock.tk) (inc exc: TicketLock.tk)
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


Section SIM.

  Context `{Σ: GRA.t}.

  Context `{MONORA: @GRA.inG monoRA Σ}.
  Context `{THDRA: @GRA.inG ThreadRA Σ}.
  Context `{STATESRC: @GRA.inG (stateSrcRA (Mod.state AbsLock.mod)) Σ}.
  Context `{STATETGT: @GRA.inG (stateTgtRA (OMod.closed_state TicketLock.omod (SCMem.mod TicketLock.gvs))) Σ}.
  Context `{IDENTSRC: @GRA.inG (identSrcRA (Mod.ident AbsLock.mod)) Σ}.
  Context `{IDENTTGT: @GRA.inG (identTgtRA (OMod.closed_ident TicketLock.omod (SCMem.mod TicketLock.gvs))) Σ}.
  (* Context `{IDENTTGT: @GRA.inG (identTgtRA (void + SCMem.val)%type) Σ}. *)
  Context `{OBLGRA: @GRA.inG ObligationRA.t Σ}.
  Context `{ARROWRA: @GRA.inG (ArrowRA (OMod.closed_ident TicketLock.omod (SCMem.mod TicketLock.gvs))) Σ}.
  Context `{EDGERA: @GRA.inG EdgeRA Σ}.
  Context `{ONESHOTSRA: @GRA.inG (@FiniteMap.t (OneShot.t unit)) Σ}.
  Context `{MEMRA: @GRA.inG memRA Σ}.

  Context `{NATMAPRA: @GRA.inG (Auth.t (NatMapRA.t TicketLock.tk)) Σ}.
  Context `{AUTHRA1: @GRA.inG (Auth.t (Excl.t nat)) Σ}.
  Context `{AUTHRA2: @GRA.inG (Auth.t (Excl.t (nat * nat))) Σ}.
  Context `{IN2: @GRA.inG (thread_id ==> (Auth.t (Excl.t nat)))%ra Σ}.
  (* Context `{REGIONRA: @GRA.inG (Region.t (thread_id * nat)) Σ}. *)
  (* Context `{CONSENTRA: @GRA.inG (@FiniteMap.t (Consent.t nat)) Σ}. *)

  Let mypreord := prod_le_PreOrder nat_le_po (Tkst.le_PreOrder nat).
  Variable monok: nat.

  (* Program Instance Persistent_white_my: Persistent (∃ o, monoWhite monok mypreord o). *)
  (* Next Obligation. apply bi.exist_persistent. i. apply Persistent_white. Qed. *)

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
      (∃ (k: nat) (o: Ord.t),
          (monoBlack monok mypreord (now, Tkst.d k))
            ∗ (ObligationRA.black k o)
            ∗ (ObligationRA.pending k 1)
            ∗ (ObligationRA.duty (inl myt) [(k, Ord.S Ord.O)])
      )
  .

  Definition ticket_lock_inv_unlocked0
             (l: list thread_id) (tks: NatMap.t nat) (now next: nat) (myt: thread_id) : iProp :=
    (OwnM (Auth.white (Excl.just (now, myt): Excl.t (nat * nat)%type)))
      ∗
      (⌜(l = []) /\ (tks = @NatMap.empty _) /\ (now = next)⌝)
      ∗
      (∃ (k: nat),
          (monoBlack monok mypreord (now, Tkst.a k))
      )
  .

  Definition ticket_lock_inv_unlocked1
             (l: list thread_id) (tks: NatMap.t nat) (now next: nat) (myt: thread_id) : iProp :=
    ∃ yourt waits,
      (OwnM (Auth.white (Excl.just (now, myt): Excl.t (nat * nat)%type)))
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
        )
  .

  Definition ticket_lock_inv_locked
             (l: list thread_id) (tks: NatMap.t nat) (now next: nat) (myt: thread_id) : iProp :=
    (OwnM (Auth.white (Excl.just (now, myt): Excl.t (nat * nat)%type)))
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

  Definition ticket_lock_inv_mem
             (mem: SCMem.t) (now next: nat) (myt: thread_id) : iProp :=
    ((memory_black mem)
       ∗ (points_to TicketLock.now_serving (SCMem.val_nat now))
       ∗ (points_to TicketLock.next_ticket (SCMem.val_nat next))
       ∗ (OwnM (Auth.black (Excl.just (now, myt): Excl.t (nat * nat)%type)))
    )
  .

  Definition ticket_lock_inv_state
             (mem: SCMem.t) (own: bool) (tks: NatMap.t nat) : iProp :=
    ((St_tgt (tt, mem)) ∗ (St_src (own, (key_set tks))))
  .

  Definition ticket_lock_inv : iProp :=
    ∃ (mem: SCMem.t) (own: bool)
      (l: list thread_id) (tks: NatMap.t nat) (now next: nat) (myt: thread_id),
      (ticket_lock_inv_tks tks)
        ∗
        (ticket_lock_inv_mem mem now next myt)
        ∗
        (ticket_lock_inv_state mem own tks)
        ∗
        (((⌜own = true⌝)
            ∗ (ticket_lock_inv_locked l tks now next myt)
         )
         ∨
           ((⌜own = false⌝)
              ∗ ((ticket_lock_inv_unlocking l tks now next myt)
                 ∨
                   ((ticket_lock_inv_unlocked0 l tks now next myt)
                    ∨
                      (ticket_lock_inv_unlocked1 l tks now next myt))
                )
        ))
  .

  Let I: list iProp := [ticket_lock_inv].

  (* Properties *)
  Lemma unlocking_mono
        l tks now next myt:
    (ticket_lock_inv_unlocking l tks now next myt)
      -∗ (∃ k o, (monoWhite monok mypreord (now, Tkst.d k))
                   ∗ (ObligationRA.black k o)
         ).
  Proof.
    iIntros "I". iDestruct "I" as "[_ [_ [_ [_ I]]]]". do 2 iDestruct "I" as "[% I]".
    iDestruct "I" as "[MB [OB _]]". iPoseProof (black_white with "MB") as "#MYTURN".
    iExists k, o. iFrame. auto.
  Qed.

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
    do 2 (iDestruct "I3" as "[% I3]"). iDestruct "I3" as "[I3 _]".
    iPoseProof (black_white_compare with "MYT I3") as "%LE". exfalso.
    hexploit (tkqueue_val_range_l I2 _ FIND). i. inv LE; try lia.
  Qed.

  Lemma unlocked0_contra
        tid l tks now next myt mytk
        (FIND: NatMap.find tid tks = Some mytk)
    :
    (ticket_lock_inv_unlocked0 l tks now next myt)
      -∗ ⌜False⌝.
  Proof.
    iIntros "I". iDestruct "I" as "[_ [%I2 _]]". exfalso. des; clarify.
  Qed.

  Lemma unlocked1_mono
        l tks now next myt:
    (ticket_lock_inv_unlocked1 l tks now next myt)
      -∗ (∃ k o, (monoWhite monok mypreord (now, Tkst.b k))
                   ∗ (ObligationRA.black k o)
         ).
  Proof.
    iIntros "I". do 2 iDestruct "I" as "[% I]". iDestruct "I" as "[_ [_ [_ [_ [_ I]]]]]".
    do 3 iDestruct "I" as "[% I]". iDestruct "I" as "[MB [OB _]]".
    iPoseProof (black_white with "MB") as "#MYTURN". iExists k, o. iFrame. auto.
  Qed.

  Lemma unlocked1_myturn
        tid l tks now next myt
        mytk o
        (FIND: NatMap.find tid tks = Some mytk)
    :
    (monoWhite monok mypreord (mytk, o))
      -∗
      (ticket_lock_inv_unlocked1 l tks now next myt)
      -∗ ⌜now = mytk⌝.
  Proof.
    iIntros "MYT I". do 2 iDestruct "I" as "[% I]". iDestruct "I" as "[_ [%I1 [%I2 [_ [_ I]]]]]".
    do 3 iDestruct "I" as "[% I]". iDestruct "I" as "[MB _]".
    iPoseProof (black_white_compare with "MYT MB") as "%LE".
    hexploit (tkqueue_val_range_l I2 _ FIND). i. inv LE; auto. lia.
  Qed.

  Lemma locked_contra
        tid l tks now next myt
        (FIND: NatMap.find tid tks = Some now)
    :
    (ticket_lock_inv_locked l tks now next myt)
      -∗ ⌜False⌝.
  Proof.
    iIntros "I". iDestruct "I" as "[_ [%I2 _]]". exfalso.
    hexploit (tkqueue_val_range_l I2 _ FIND). clear. i. lia.
  Qed.

  Lemma locked_myturn
        tid l tks now next myt
        mytk o
        (FIND: NatMap.find tid tks = Some mytk)
    :
    (monoWhite monok mypreord (mytk, o))
      -∗
      (ticket_lock_inv_locked l tks now next myt)
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


  (* Simulations *)
  Lemma lock_enqueue tid:
    ((own_thread tid)
       ∗ (ObligationRA.duty (inl tid) [])
    )
      ∗
      (∀ mytk,
          (
            (OwnM (Auth.white (NatMapRA.singleton tid mytk: NatMapRA.t TicketLock.tk)))
              ∗ (maps_to tid (Auth.white (Excl.just 2: Excl.t nat)))
          )
          -∗
  (stsim I tid (topset I) ibot7 ibot7
         (λ r_src r_tgt : (), (own_thread tid ** ObligationRA.duty (inl tid) []) ** ⌜r_src = r_tgt⌝)
         false false
    (ITree.iter
        (λ _ : (),
           trigger Yield;;;
           ` x_0 : bool * NatMap.t () <- trigger (Get (bool * NatMap.t ()));;
           (let (own0, _) := x_0 in if Bool.eqb own0 true then Ret (inl ()) else Ret (inr ())))
        ();;;
      ` x_0 : bool * NatMap.t () <- trigger (Get (bool * NatMap.t ()));;
      (let (_, ts0) := x_0 in
       trigger (Put (true, NatMap.remove (elt:=()) tid ts0));;;
       trigger
         (Fair
            (λ i : nat,
               if tid_dec i tid
               then Flag.success
               else
                if NatMapP.F.In_dec (NatMap.remove (elt:=()) tid ts0) i
                then Flag.fail
                else Flag.emp));;; trigger Yield;;; Ret ()))
    (OMod.close_itree TicketLock.omod (SCMem.mod TicketLock.gvs)
       (TicketLock.lock_loop (SCMem.val_nat mytk));;;
     OMod.close_itree TicketLock.omod (SCMem.mod TicketLock.gvs) (trigger Yield))
  )
      )
      ⊢
      (stsim I tid (topset I) ibot7 ibot7
             (fun r_src r_tgt => own_thread tid ** ObligationRA.duty (inl tid) [] ** ⌜r_src = r_tgt⌝)
             false false
             (AbsLock.lock_fun tt)
             (OMod.close_itree TicketLock.omod (SCMem.mod TicketLock.gvs)
                               (TicketLock.lock_fun tt))).
  Proof.
    iIntros "[[MYTH DUTY] SIM]".
    unfold AbsLock.lock_fun, TicketLock.lock_fun. rred.
    rewrite close_itree_call. rred.
    iApply (stsim_sync with "[DUTY]"). msubtac. iFrame. iIntros "DUTY _".
    unfold Mod.wrap_fun, SCMem.faa_fun. rred.
    iApply stsim_tidL. lred.

    iopen 0 "I" "K". do 7 iDestruct "I" as "[% I]". iDestruct "I" as "[TKS [MEM [ST CASES]]]".
    iDestruct "ST" as "[ST0 ST1]".
    iApply stsim_getL. iSplit. auto. iApply (stsim_putL with "ST1"). iIntros "ST1".

    iApply stsim_getR. iSplit. auto. rred. iApply stsim_tauR. rred.
    iDestruct "MEM" as "[MEM0 [MEM1 [MEM2 MEM3]]]".
    iPoseProof (memory_ra_faa with "MEM0 MEM2") as "[% [%FAA >[MEM0 MEM2]]]".
    erewrite FAA. rred.
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
    iAssert (St_src (own, (key_set tks')))%I with "[ST1]" as "ST1".
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
      instantiate (1:=Excl.just 2). instantiate (1:=Excl.just 2).
      ii. des. ur in FRAME. des_ifs. split.
      { ur. ss. }
      { ur. ss. }
    }
    rewrite <- maps_to_res_add. iDestruct "MYNUM" as "[MYNB MYNW]".

    iAssert (natmap_prop_sum tks' (λ tid0 _ : nat, own_thread tid0))%I with "[MYTH TKS2]" as "TKS2".
    { subst tks'. iApply (natmap_prop_sum_add with "TKS2"). iFrame. }

    iDestruct "CASES" as "[[%TRUE INV] | [%FALSE INV]]"; subst.
    { iPoseProof (FairRA.white_mon with "MYTRI") as ">MYTRI".
      { instantiate (1:=Ord.from_nat (next - (S now))). ss.
        apply Ord.lt_le. apply Ord.omega_upperbound.
      }
      iMod ("K" with "[DUTY TKS0 TKS1 TKS2 TKS3 MEM0 MEM1 MEM2 MEM3 INV ST0 ST1 MYTRI MYNB]") as "_".
      { subst tks'. unfold ticket_lock_inv.
        iExists m1, true, (l ++ [tid]), (NatMap.add tid next tks), now, (S next), myt.
        iFrame.
        iSplitL "MEM2".
        { ss. replace (S next) with (next + 1). iFrame. lia. }
        iLeft. iSplit; auto. unfold ticket_lock_inv_locked.
        iDestruct "INV" as "[INV0 [INV1 [INV2 [INV3 INV4]]]]". iFrame.
        iSplit.
        { iPure "INV1" as ?. iPureIntro. apply tkqueue_enqueue; auto. }
        iPoseProof (natmap_prop_sum_add with "INV2 MYTRI") as "INV2". iFrame.
        iApply list_prop_sum_add. iFrame. iExists 2. iFrame.
      }
      iApply stsim_reset. iApply "SIM". iFrame.
    }

    iDestruct "INV" as "[INV | INV]".
    { iPoseProof (FairRA.white_mon with "MYTRI") as ">MYTRI".
      { instantiate (1:=Ord.from_nat (next - (S now))). ss.
        apply Ord.lt_le. apply Ord.omega_upperbound.
      }
      iMod ("K" with "[DUTY TKS0 TKS1 TKS2 TKS3 MEM0 MEM1 MEM2 MEM3 INV ST0 ST1 MYTRI MYNB]") as "_".
      { subst tks'. unfold ticket_lock_inv.
        iExists m1, false, (l ++ [tid]), (NatMap.add tid next tks), now, (S next), myt.
    remember ((⌜false = true⌝ **
     ticket_lock_inv_locked (l ++ [tid]) (NatMap.add tid next tks) now (S next) myt)
    ∨ (⌜false = false⌝ **
       ticket_lock_inv_unlocking (l ++ [tid]) (NatMap.add tid next tks) now (S next) myt
       ∨ ticket_lock_inv_unlocked0 (l ++ [tid]) (NatMap.add tid next tks) now (S next) myt
         ∨ ticket_lock_inv_unlocked1 (l ++ [tid]) (NatMap.add tid next tks) now (S next) myt))%I as temp.
        iFrame. subst temp.
        iSplitL "MEM2".
        { ss. replace (S next) with (next + 1). iFrame. lia. }
        iRight. iSplit; auto. iLeft. unfold ticket_lock_inv_unlocking.
        iDestruct "INV" as "[INV0 [INV1 [INV2 [INV3 INV4]]]]". iFrame.
        iSplit.
        { iPure "INV1" as ?. iPureIntro. apply tkqueue_enqueue; auto. }
        iPoseProof (natmap_prop_sum_add with "INV2 MYTRI") as "INV2". iFrame.
        iApply list_prop_sum_add. iFrame. iExists 2. iFrame.
      }
      iApply stsim_reset. iApply "SIM". iFrame.
    }

    iDestruct "INV" as "[INV | INV]".
    { iPoseProof (FairRA.white_mon with "MYTRI") as ">MYTRI".
      { instantiate (1:=Ord.from_nat (next - (now))). ss.
        apply Ord.lt_le. apply Ord.omega_upperbound.
      }
      iPoseProof (ObligationRA.alloc (((Ord.S Ord.O) × Ord.omega) × (Ord.from_nat 3))%ord) as "> [% [[OBLK OWHI] OPEND]]".
      iPoseProof (ObligationRA.white_eq with "OWHI") as "OWHI".
      { rewrite Ord.from_nat_S. rewrite Jacobsthal.mult_S. reflexivity. }
      iPoseProof (ObligationRA.white_split_eq with "OWHI") as "[OWHI TAX]".
      iPoseProof (ObligationRA.duty_alloc with "DUTY OWHI") as "> DUTY".
      unfold ticket_lock_inv_unlocked0. iDestruct "INV" as "[INV0 [% [% INV2]]]".
      iPoseProof ((black_updatable _ _ _ (now, Tkst.b k)) with "INV2") as ">INV2".
      { econs 2. ss. split; auto. i; ss. }

      iMod ("K" with "[DUTY TKS0 TKS1 TKS2 TKS3 MEM0 MEM1 MEM2 MEM3 INV0 INV2 ST0 ST1 MYTRI MYNB OBLK OPEND TAX]") as "_".
      { subst tks'. unfold ticket_lock_inv.
        iExists m1, false, (l ++ [tid]), (NatMap.add tid next tks), now, (S next), myt.
    remember ((⌜false = true⌝ **
     ticket_lock_inv_locked (l ++ [tid]) (NatMap.add tid next tks) now (S next) myt)
    ∨ (⌜false = false⌝ **
       ticket_lock_inv_unlocking (l ++ [tid]) (NatMap.add tid next tks) now (S next) myt
       ∨ ticket_lock_inv_unlocked0 (l ++ [tid]) (NatMap.add tid next tks) now (S next) myt
         ∨ ticket_lock_inv_unlocked1 (l ++ [tid]) (NatMap.add tid next tks) now (S next) myt))%I as temp.
        iFrame. subst temp.
        iSplitL "MEM2".
        { ss. replace (S next) with (next + 1). iFrame. lia. }
        iRight. iSplit; auto. iRight. iRight.
        unfold ticket_lock_inv_unlocked1.
        des; clarify. ss. iExists tid, []. ss. iFrame.
        iSplit; auto.
        iSplit.
        { iPureIntro. econs 2; eauto. apply NatMapP.F.add_eq_o; auto. econs 1; auto.
          apply nm_find_none_rm_add_eq. apply NatMapP.F.empty_o.
        }
        iSplitR. auto. iExists k, _, 2. iFrame.
      }
      iApply stsim_reset. iApply "SIM". iFrame.
    }

    { iPoseProof (FairRA.white_mon with "MYTRI") as ">MYTRI".
      { instantiate (1:=Ord.from_nat (next - (now))). ss.
        apply Ord.lt_le. apply Ord.omega_upperbound.
      }
      iMod ("K" with "[DUTY TKS0 TKS1 TKS2 TKS3 MEM0 MEM1 MEM2 MEM3 INV ST0 ST1 MYTRI MYNB]") as "_".
      { subst tks'. unfold ticket_lock_inv.
        iExists m1, false, (l ++ [tid]), (NatMap.add tid next tks), now, (S next), myt.
    remember ((⌜false = true⌝ **
     ticket_lock_inv_locked (l ++ [tid]) (NatMap.add tid next tks) now (S next) myt)
    ∨ (⌜false = false⌝ **
       ticket_lock_inv_unlocking (l ++ [tid]) (NatMap.add tid next tks) now (S next) myt
       ∨ ticket_lock_inv_unlocked0 (l ++ [tid]) (NatMap.add tid next tks) now (S next) myt
         ∨ ticket_lock_inv_unlocked1 (l ++ [tid]) (NatMap.add tid next tks) now (S next) myt))%I as temp.
        iFrame. subst temp.
        iSplitL "MEM2".
        { ss. replace (S next) with (next + 1). iFrame. lia. }
        iRight. iSplit; auto. iRight. iRight. unfold ticket_lock_inv_unlocked1.
        do 2 iDestruct "INV" as "[% INV]".
        iDestruct "INV" as "[INV0 [% [INV2 [INV3 [INV4 INV5]]]]]". subst.
        iExists yourt, (waits ++ [tid]). ss. iFrame.
        iSplit. auto.
        iSplit.
        { iPure "INV2" as ?. iPureIntro. rewrite app_comm_cons. apply tkqueue_enqueue; auto. }
        iPoseProof (natmap_prop_sum_add with "INV3 MYTRI") as "INV3". iFrame.
        iApply list_prop_sum_add. iFrame. iExists 2. iFrame.
      }
      iApply stsim_reset. iApply "SIM". iFrame.
    }
  Qed.

  Lemma lock_myturn_yieldR
        (g0 g1 : ∀ R_src R_tgt : Type,
            (R_src → R_tgt → iProp)
            → bool
            → bool
            → itree ((eventE +' cE) +' sE (Mod.state AbsLock.mod)) R_src
            → itree
                ((eventE +' cE) +'
                                   sE (OMod.closed_state TicketLock.omod (SCMem.mod TicketLock.gvs))) R_tgt
            → iProp)
        (ps pt: bool)
        (src: itree ((eventE +' cE) +' sE (Mod.state AbsLock.mod)) unit)
        (tgt: itree ((eventE +' cE) +' sE (OMod.closed_state TicketLock.omod (SCMem.mod TicketLock.gvs))) unit)
        (tid mytk u: nat)
        x
    :
    (
      (OwnM (Auth.white ((NatMapRA.singleton tid mytk: NatMapRA.t TicketLock.tk))))
        ∗ (maps_to tid (Auth.white (Excl.just (S u): Excl.t nat)))
        ∗ (monoWhite monok mypreord (mytk, x))
    )
      ∗
      (
      ((OwnM (Auth.white ((NatMapRA.singleton tid mytk: NatMapRA.t TicketLock.tk))))
        ∗ (maps_to tid (Auth.white (Excl.just u: Excl.t nat)))
        ∗ (monoWhite monok mypreord (mytk, x)))
        -∗
  (stsim I tid (topset I) g0 g1
    (λ r_src r_tgt : (), (own_thread tid ** ObligationRA.duty (inl tid) []) ** ⌜r_src = r_tgt⌝)
    ps true
    (trigger Yield;;; src)
    (tgt))
      )
      ⊢
  (stsim I tid (topset I) g0 g1
    (λ r_src r_tgt : (), (own_thread tid ** ObligationRA.duty (inl tid) []) ** ⌜r_src = r_tgt⌝)
    ps pt
    (trigger Yield;;; src)
    (trigger Yield;;; tgt)).
  Proof.
    iIntros "[[MYTK [MYNW MYTURN]] SIM]".
    iopen 0 "I" "K". do 7 iDestruct "I" as "[% I]". iDestruct "I" as "[TKS [MEM [ST CASES]]]".
    iPoseProof (mytk_find_some with "[MYTK TKS]") as "%FIND". iFrame.
    iDestruct "CASES" as "[[%CT I] | [%CF [I | [I | I]]]]".
    { iPoseProof (locked_myturn with "MYTURN I") as "%FF". eauto. inv FF. }
    { iPoseProof (unlocking_myturn with "MYTURN I") as "%FF". eauto. inv FF. }
    { iPoseProof (unlocked0_contra with "I") as "%FF". eauto. inv FF. }
    iPoseProof (unlocked1_myturn with "MYTURN I") as "%EQ". eauto. subst mytk.
    do 2 iDestruct "I" as "[% I]". iDestruct "I" as "[I0 [% [%I2 [I3 [I4 I5]]]]]".
    do 3 iDestruct "I5" as "[% I5]". iDestruct "I5" as "[I5 I6]".
    iDestruct "I6" as "[I6 [I7 [I8 [I9 I10]]]]".
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
    iMod ("K" with "[TKS MEM ST I0 I3 I4 I5 I6 I7 I8 I9 I10]") as "_".
    { iExists mem, false, (tid :: tl), tks, now, next, myt.
      remember (
          (⌜false = true⌝ ** ticket_lock_inv_locked (tid :: tl) tks now next myt)
          ∨ (⌜false = false⌝ **
                           ticket_lock_inv_unlocking (tid :: tl) tks now next myt
             ∨ ticket_lock_inv_unlocked0 (tid :: tl) tks now next myt
             ∨ ticket_lock_inv_unlocked1 (tid :: tl) tks now next myt))%I as temp.
      iFrame. subst temp.
      iRight. iSplit. auto. iRight. iRight.
      iExists tid, tl. iFrame. iSplit. auto. iSplit. auto.
      iExists k, o, u. iFrame.
    }
    iModIntro. iApply "SIM". iFrame.
  Qed.

  Lemma lock_myturn0
        (g0 g1 : ∀ R_src R_tgt : Type,
            (R_src → R_tgt → iProp)
            → bool
            → bool
            → itree ((eventE +' cE) +' sE (Mod.state AbsLock.mod)) R_src
            → itree ((eventE +' cE) +' sE (OMod.closed_state TicketLock.omod (SCMem.mod TicketLock.gvs))) R_tgt → iProp)
        (ps pt: bool)
        (tid : nat)
        (mytk : TicketLock.tk)
        x
    :
    ((monoWhite monok mypreord (mytk, x))
       ∗ (OwnM (Auth.white (NatMapRA.singleton tid mytk: NatMapRA.t nat)))
       ∗ (maps_to tid (Auth.white (Excl.just 1: Excl.t nat))))
  ⊢ stsim I tid (topset I) g0 g1
      (λ r_src r_tgt : (), (own_thread tid ** ObligationRA.duty (inl tid) []) ** ⌜r_src = r_tgt⌝)
      ps pt
      (trigger Yield;;;
       ` x : () + () <-
       (` x_0 : bool * NatMap.t () <- trigger (Get (bool * NatMap.t ()));;
        (let (own0, _) := x_0 in if Bool.eqb own0 true then Ret (inl ()) else Ret (inr ())));;
       match x with
       | inl l0 =>
           tau;; ITree.iter
                   (λ _ : (),
                      trigger Yield;;;
                      ` x_0 : bool * NatMap.t () <- trigger (Get (bool * NatMap.t ()));;
                      (let (own0, _) := x_0 in
                       if Bool.eqb own0 true then Ret (inl ()) else Ret (inr ()))) l0
       | inr r0 => Ret r0
       end;;;
       ` x_0 : bool * NatMap.t () <- trigger (Get (bool * NatMap.t ()));;
       (let (_, ts0) := x_0 in
        trigger (Put (true, NatMap.remove (elt:=()) tid ts0));;;
        trigger
          (Fair
             (λ i : nat,
                if tid_dec i tid
                then Flag.success
                else
                 if NatMapP.F.In_dec (NatMap.remove (elt:=()) tid ts0) i
                 then Flag.fail
                 else Flag.emp));;; trigger Yield;;; Ret ()))
      (` r : Any.t <-
       OMod.embed_itree TicketLock.omod (SCMem.mod TicketLock.gvs)
         (Mod.wrap_fun SCMem.load_fun (Any.upcast TicketLock.now_serving));;
       ` x : SCMem.val <- (tau;; unwrap (Any.downcast r));;
       OMod.close_itree TicketLock.omod (SCMem.mod TicketLock.gvs)
         (` b : bool <- OMod.call "compare" (x, SCMem.val_nat mytk);;
          (if b then Ret () else tau;; TicketLock.lock_loop (SCMem.val_nat mytk)));;;
         OMod.close_itree TicketLock.omod (SCMem.mod TicketLock.gvs) (trigger Yield)).
  Proof.
    iIntros "[#MYTN [MYTK MYNU]]". 
    iopen 0 "I" "K". do 7 iDestruct "I" as "[% I]". iDestruct "I" as "[TKS [MEM [ST CASES]]]".
    iPoseProof (mytk_find_some with "[MYTK TKS]") as "%FIND". iFrame.
    iDestruct "CASES" as "[[%CT I] | [%CF [I | [I | I]]]]".
    { iPoseProof (locked_myturn with "MYTN I") as "%FF". eauto. inv FF. }
    { iPoseProof (unlocking_myturn with "MYTN I") as "%FF". eauto. inv FF. }
    { iPoseProof (unlocked0_contra with "I") as "%FF". eauto. inv FF. }
    iPoseProof (unlocked1_myturn with "MYTN I") as "%EQ". eauto. subst now.

    unfold Mod.wrap_fun, SCMem.load_fun. rred.
    iDestruct "MEM" as "[MEM0 [MEM1 [MEM2 MEM3]]]". iDestruct "ST" as "[ST0 ST1]".
    iApply stsim_getR. iSplit. eauto. rred.
    iApply stsim_tauR. rred.
    iPoseProof (memory_ra_load with "MEM0 MEM1") as "%LOAD". des. rewrite LOAD. rred.
    iApply stsim_tauR. rred.
    rewrite close_itree_call. rred.

    iMod ("K" with "[TKS MEM0 MEM1 MEM2 MEM3 ST0 ST1 I]") as "_".
    { iExists mem, own, l, tks, mytk, next, myt. iFrame. iRight. iSplit; auto. }
    clear pt mem own l tks next myt FIND CF LOAD LOAD0.
    iApply lock_myturn_yieldR. iSplitL. iFrame. auto.
    iIntros "[MYTK [MYNUM _]]". rred.

    iopen 0 "I" "K". do 7 iDestruct "I" as "[% I]". iDestruct "I" as "[TKS [MEM [ST CASES]]]".
    iPoseProof (mytk_find_some with "[MYTK TKS]") as "%FIND". iFrame.
    iDestruct "CASES" as "[[%CT I] | [%CF [I | [I | I]]]]".
    { iPoseProof (locked_myturn with "MYTN I") as "%FF". eauto. inv FF. }
    { iPoseProof (unlocking_myturn with "MYTN I") as "%FF". eauto. inv FF. }
    { iPoseProof (unlocked0_contra with "I") as "%FF". eauto. inv FF. }
    iPoseProof (unlocked1_myturn with "MYTN I") as "%EQ". eauto. subst now.

    unfold Mod.wrap_fun, SCMem.compare_fun. rred.
    iDestruct "MEM" as "[MEM0 [MEM1 [MEM2 MEM3]]]". iDestruct "ST" as "[ST0 ST1]".
    iApply stsim_getR. iSplit. eauto. rred.
    iApply stsim_tauR. rred. iApply stsim_tauR. rred.
    destruct (Nat.eq_dec mytk mytk).
    2:{ exfalso. auto. }
    clear e. subst. rred.

    iApply stsim_yieldL. lred.
    iApply stsim_getL. iSplit. auto. lred.
    iApply stsim_getL. iSplit. auto.
    iApply (stsim_putL with "ST1"). iIntros "ST1".

    remember (NatMap.remove tid tks) as tks'.
    rewrite <- key_set_pull_rm_eq. rewrite <- Heqtks'.
    iAssert (ticket_lock_inv_state mem true tks')%I with "[ST0 ST1]" as "ST". iFrame.
    iAssert (ticket_lock_inv_mem mem mytk next myt)%I with "[MEM0 MEM1 MEM2 MEM3]" as "MEM". iFrame.
    iDestruct "TKS" as "[TKS0 [TKS1 [TKS2 TKS3]]]".
    do 2 iDestruct "I" as "[% I]". iDestruct "I" as "[I0 [% [%I2 [I3 [I4 I5]]]]]".
    do 3 iDestruct "I5" as "[% I5]". iDestruct "I5" as "[I5 [I6 [I7 [I8 [I9 I10]]]]]".
    hexploit (tkqueue_inv_hd I2 _ FIND). i. des.
    subst l. inversion H0; clear H0. subst yourt waits.

    iPoseProof (NatMapRA_remove with "TKS0 MYTK") as ">TKS0". rewrite <- Heqtks'.
    iPoseProof (natmap_prop_remove_find with "TKS2") as "[MYTH TKS2]". eauto. rewrite <- Heqtks'.
    iCombine "I10 MYNUM" as "MYNUM". rewrite maps_to_res_add.
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
    

    

  Lemma lock_myturn1
        (g0 g1 : ∀ R_src R_tgt : Type,
            (R_src → R_tgt → iProp)
            → bool
            → bool
            → itree ((eventE +' cE) +' sE (Mod.state AbsLock.mod)) R_src
            → itree ((eventE +' cE) +' sE (OMod.closed_state TicketLock.omod (SCMem.mod TicketLock.gvs))) R_tgt → iProp)
        (ps pt: bool)
        (tid : nat)
        (mytk : TicketLock.tk)
        (mem : SCMem.t)
        (own : bool)
        (l : list nat)
        (tks : NatMap.t nat)
        (next myt : nat)
    :
  (OwnM (Auth.white (NatMapRA.singleton tid mytk: NatMapRA.t nat)) **
   (maps_to tid (Auth.white (Excl.just 2: Excl.t nat)) **
    (ticket_lock_inv_tks tks **
     (ticket_lock_inv_mem mem mytk next myt **
      (ticket_lock_inv_state mem own tks **
       ((⌜own = true⌝ ** ticket_lock_inv_locked l tks mytk next myt)
        ∨ (⌜own = false⌝ **
           ticket_lock_inv_unlocking l tks mytk next myt
           ∨ ticket_lock_inv_unlocked0 l tks mytk next myt
             ∨ ticket_lock_inv_unlocked1 l tks mytk next myt) **
        (ticket_lock_inv -*
         MUpd (nth_default True%I I)
           (fairI (ident_tgt:=OMod.closed_ident TicketLock.omod (SCMem.mod TicketLock.gvs))) []
           [0] True)))))))
  ⊢ (stsim I tid [] g0 g1
      (λ r_src r_tgt : (), (own_thread tid ** ObligationRA.duty (inl tid) []) ** ⌜r_src = r_tgt⌝)
      ps pt
      (ITree.iter
         (λ _ : (),
            trigger Yield;;;
            ` x_0 : bool * NatMap.t () <- trigger (Get (bool * NatMap.t ()));;
            (let (own0, _) := x_0 in if Bool.eqb own0 true then Ret (inl ()) else Ret (inr ())))
         ();;;
       ` x_0 : bool * NatMap.t () <- trigger (Get (bool * NatMap.t ()));;
       (let (_, ts0) := x_0 in
        trigger (Put (true, NatMap.remove (elt:=()) tid ts0));;;
        trigger
          (Fair
             (λ i : nat,
                if tid_dec i tid
                then Flag.success
                else
                 if NatMapP.F.In_dec (NatMap.remove (elt:=()) tid ts0) i
                 then Flag.fail
                 else Flag.emp));;; trigger Yield;;; Ret ()))
      (trigger Yield;;;
       ` x : SCMem.val <-
       (` rv : Any.t <-
        OMod.embed_itree TicketLock.omod (SCMem.mod TicketLock.gvs)
          (Mod.wrap_fun SCMem.load_fun (Any.upcast TicketLock.now_serving));;
        (tau;; unwrap (Any.downcast rv)));;
       OMod.close_itree TicketLock.omod (SCMem.mod TicketLock.gvs)
         (` b : bool <- OMod.call "compare" (x, SCMem.val_nat mytk);;
          (if b then Ret () else tau;; TicketLock.lock_loop (SCMem.val_nat mytk)));;;
         OMod.close_itree TicketLock.omod (SCMem.mod TicketLock.gvs) (trigger Yield))).
  Proof.
    iIntros "[MYTK [MYN [TKS [MEM [ST [CASES K]]]]]]".
    rewrite unfold_iter_eq. lred.
    iAssert (⌜NatMap.find tid tks = Some mytk⌝)%I as "%FIND".
    { iDestruct "TKS" as "[TKS0 _]". iApply (NatMapRA_find_some with "TKS0 MYTK"). }
    iDestruct "CASES" as "[[%CT I] | [%CF [I | [I | I]]]]".
    { iPoseProof (locked_contra with "I") as "%F". eauto. inv F. }
    { iPoseProof (unlocking_contra with "I") as "%F". eauto. inv F. }
    { iPoseProof (unlocked0_contra with "I") as "%F". eauto. inv F. }
    iPoseProof (unlocked1_mono with "I") as "#MYMW". iDestruct "MYMW" as "[% [% [MYMW _]]]".
    iMod ("K" with "[TKS MEM ST I]") as "_".
    { iExists mem, own, l, tks, mytk, next, myt. iFrame. iRight. iSplit; auto. }
    iApply lock_myturn_yield. iSplitL. iFrame. auto.
    iIntros "[MYTK [MYN _]]". rred.

    (* TODO *)
    iStopProof.



  (* Lemma get_duty tid mytk *)
  (*   : *)
  (*   ⊢ *)
  (*     ((OwnM (Auth.white (NatMapRA.singleton tid mytk: NatMapRA.t nat))) *)
  (*        -∗ *)
  (*        (MUpd (nth_default True%I I) (fairI (ident_tgt:= OMod.closed_ident TicketLock.omod (SCMem.mod TicketLock.gvs))) [0] [] *)
  (*              (((ObligationRA.duty (inl tid) []) ∗ (OwnM (Auth.white (NatMapRA.singleton tid mytk: NatMapRA.t nat)))) *)
  (*                 ∗ ((ObligationRA.duty (inl tid) []) *)
  (*                      -∗ (MUpd (nth_default True%I I) (fairI (ident_tgt:= OMod.closed_ident TicketLock.omod (SCMem.mod TicketLock.gvs))) [] [0] True%I) *)
  (*     ))))%I. *)
  (* Proof. *)
  (*   iIntros "MYTH". *)
  (*   (iPoseProof (MUpd_open (nth_default True%I I) _ 0) as "> _H"; *)
  (*    [ let x := eval cbn in ((nth_default True%I I) 0) in *)
  (*        change ((nth_default True%I I) 0) with x; msimpl; iDestruct "_H" as "[I K]" ]). *)
  (*   iModIntro. *)
  (*   do 7 iDestruct "I" as "[% I]". iDestruct "I" as "[TKS [MEM [ST CASES]]]". *)
  (*   iDestruct "TKS" as "[TKS0 TKS1]". *)
  (*   iPoseProof (NatMapRA_find_some with "TKS0 MYTH") as "%FIND". *)
  (*   iDestruct "CASES" as "[[CT INV]|[CF INV]]". *)
  (*   { unfold ticket_lock_inv_locked. iDestruct "INV" as "[INV0 [%INV1 [INV2 [INV3 INV4]]]]". *)
  (*     hexploit (tkqueue_find_in INV1 _ FIND). i. *)
  (*     iPoseProof (list_prop_sum_in_split with "INV3") as "[DUTY INV3]". eapply H. *)
  (*     iSplitL "DUTY MYTH". iFrame. *)
  (*     iIntros "DUTY". iApply "K". *)
  (*     unfold ticket_lock_inv. iExists mem, own, l, tks, now, next, myt. *)
  (*     iSplitL "TKS0 TKS1". iFrame. iSplitL "MEM". iFrame. iSplitL "ST". iFrame. *)
  (*     iLeft. iFrame. iSplit. auto. iApply "INV3". iFrame. *)
  (*   } *)
  (*   iDestruct "INV" as "[INV | [INV | INV]]". *)
  (*   { unfold ticket_lock_inv_unlocking. iDestruct "INV" as "[INV0 [%INV1 [INV2 [INV3 INV4]]]]". *)
  (*     hexploit (tkqueue_find_in INV1 _ FIND). i. *)
  (*     iPoseProof (list_prop_sum_in_split with "INV3") as "[DUTY INV3]". eapply H. *)
  (*     iSplitL "DUTY MYTH". iFrame. *)
  (*     iIntros "DUTY". iApply "K". *)
  (*     unfold ticket_lock_inv. iExists mem, own, l, tks, now, next, myt. *)
  (*     iSplitL "TKS0 TKS1". iFrame. iSplitL "MEM". iFrame. iSplitL "ST". iFrame. *)
  (*     iRight. iSplit. iFrame. iLeft. iFrame. iSplit; auto. iApply "INV3". iFrame. *)
  (*   } *)
  (*   { unfold ticket_lock_inv_unlocked0. iDestruct "INV" as "[INV0 [%INV1 INV2]]". *)
  (*     des; subst. rewrite NatMapP.F.empty_o in FIND. ss. *)
  (*   } *)
  (*   { unfold ticket_lock_inv_unlocked1. *)
  (*     do 2 iDestruct "INV" as "[% INV]". *)
  (*     iDestruct "INV" as "[INV0 [%INV1 [%INV2 [INV3 [INV4 INV5]]]]]". *)
  (*     (* TODO *) *)
  (* Abort. *)

  (* tid : nat *)
  (* g1 : ∀ R_src R_tgt : Type, *)
  (*        (R_src → R_tgt → iProp) *)
  (*        → bool *)
  (*          → bool *)
  (*            → itree ((eventE +' cE) +' sE (Mod.state AbsLock.mod)) R_src *)
  (*              → itree *)
  (*                  ((eventE +' cE) +' *)
  (*                   sE (OMod.closed_state TicketLock.omod (SCMem.mod TicketLock.gvs))) R_tgt *)
  (*                → iProp *)
  (* mytk : TicketLock.tk *)
  (* mem : SCMem.t *)
  (* own : bool *)
  (* l : list nat *)
  (* tks : NatMap.t nat *)
  (* next, myt : nat *)
  (* ============================ *)
  (* (□ (∀ a : TicketLock.tk, *)
  (*       (OwnM (Auth.white (NatMapRA.singleton tid a)) ** maps_to tid (Auth.white (Excl.just 2))) -* *)
  (*       g1 ()%type ()%type *)
  (*         (λ r_src r_tgt : (), *)
  (*            (own_thread tid ** ObligationRA.duty (inl tid) []) ** ⌜r_src = r_tgt⌝) false false *)
  (*         (ITree.iter *)
  (*            (λ _ : (), *)
  (*               trigger Yield;;; *)
  (*               ` x_0 : bool * NatMap.t () <- trigger (Get (bool * NatMap.t ()));; *)
  (*               (let (own0, _) := x_0 in *)
  (*                if Bool.eqb own0 true then Ret (inl ()) else Ret (inr ()))) ();;; *)
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
  (*                    else Flag.emp));;; trigger Yield;;; Ret ())) *)
  (*         (trigger Yield;;; *)
  (*          ` x : SCMem.val <- *)
  (*          (` rv : Any.t <- *)
  (*           OMod.embed_itree TicketLock.omod (SCMem.mod TicketLock.gvs) *)
  (*             (Mod.wrap_fun SCMem.load_fun (Any.upcast TicketLock.now_serving));; *)
  (*           (tau;; unwrap (Any.downcast rv)));; *)
  (*          OMod.close_itree TicketLock.omod (SCMem.mod TicketLock.gvs) *)
  (*            (` b : bool <- OMod.call "compare" (x, SCMem.val_nat a);; *)
  (*             (if b then Ret () else tau;; TicketLock.lock_loop (SCMem.val_nat a)));;; *)
  (*          OMod.close_itree TicketLock.omod (SCMem.mod TicketLock.gvs) (trigger Yield))) ** *)
  (*  (OwnM (Auth.white (NatMapRA.singleton tid mytk)) ** *)
  (*   (maps_to tid (Auth.white (Excl.just 2)) ** *)
  (*    (ticket_lock_inv_tks tks ** *)
  (*     (ticket_lock_inv_mem mem mytk next myt ** *)
  (*      (ticket_lock_inv_state mem own tks ** *)
  (*       ((⌜own = true⌝ ** ticket_lock_inv_locked l tks mytk next myt) *)
  (*        ∨ (⌜own = false⌝ ** *)
  (*           ticket_lock_inv_unlocking l tks mytk next myt *)
  (*           ∨ ticket_lock_inv_unlocked0 l tks mytk next myt *)
  (*             ∨ ticket_lock_inv_unlocked1 l tks mytk next myt) ** *)
  (*        (ticket_lock_inv -* *)
  (*         MUpd (nth_default True%I I) *)
  (*           (fairI (ident_tgt:=OMod.closed_ident TicketLock.omod (SCMem.mod TicketLock.gvs))) [] *)
  (*           [0] True)))))))) *)
  (* ⊢ stsim I tid [] ibot7 g1 *)
  (*     (λ r_src r_tgt : (), (own_thread tid ** ObligationRA.duty (inl tid) []) ** ⌜r_src = r_tgt⌝) *)
  (*     false false *)
  (*     (ITree.iter *)
  (*        (λ _ : (), *)
  (*           trigger Yield;;; *)
  (*           ` x_0 : bool * NatMap.t () <- trigger (Get (bool * NatMap.t ()));; *)
  (*           (let (own0, _) := x_0 in if Bool.eqb own0 true then Ret (inl ()) else Ret (inr ()))) *)
  (*        ();;; *)
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
  (*     (trigger Yield;;; *)
  (*      ` x : SCMem.val <- *)
  (*      (` rv : Any.t <- *)
  (*       OMod.embed_itree TicketLock.omod (SCMem.mod TicketLock.gvs) *)
  (*         (Mod.wrap_fun SCMem.load_fun (Any.upcast TicketLock.now_serving));; *)
  (*       (tau;; unwrap (Any.downcast rv)));; *)
  (*      OMod.close_itree TicketLock.omod (SCMem.mod TicketLock.gvs) *)
  (*        (` b : bool <- OMod.call "compare" (x, SCMem.val_nat mytk);; *)
  (*         (if b then Ret () else tau;; TicketLock.lock_loop (SCMem.val_nat mytk)));;; *)
  (*      OMod.close_itree TicketLock.omod (SCMem.mod TicketLock.gvs) (trigger Yield)) *)

  Lemma correct_lock tid:
    ((own_thread tid)
       ∗ (ObligationRA.duty (inl tid) [])
    )
      ⊢
      (stsim I tid (topset I) ibot7 ibot7
             (fun r_src r_tgt => own_thread tid ** ObligationRA.duty (inl tid) [] ** ⌜r_src = r_tgt⌝)
             false false
             (AbsLock.lock_fun tt)
             (OMod.close_itree TicketLock.omod (SCMem.mod TicketLock.gvs)
                               (TicketLock.lock_fun tt))).
  Proof.
    iIntros "[MYTH DUTY]".
    iApply correct_lock_enqueue. iSplitL. iFrame.
    iIntros "% [MYTK MYN]".
    rewrite TicketLock.lock_loop_red. rred. rewrite close_itree_call. rred.
    iStopProof. revert mytk. eapply stsim_coind. msubtac.
    iIntros "% %mytk". iIntros "#[_ CIH] [MYTK MYN]".
    (* rewrite unfold_iter_eq. lred. *)

    iopen 0 "I" "K". do 7 iDestruct "I" as "[% I]". iDestruct "I" as "[TKS [MEM [ST CASES]]]".
    destruct (Nat.eq_dec now mytk); subst.
    {

      iAssert (⌜NatMap.find tid tks = Some mytk⌝)%I as "%FIND".
      { iDestruct "TKS" as "[TKS0 _]". iApply (NatMapRA_find_some with "TKS0 MYTK"). }
      iDestruct "CASES" as "[[%CT I] | [%CF [I | [I | I]]]]".
      { iPoseProof (locked_contra with "I") as "%F". eauto. inv F. }
      { iPoseProof (unlocking_contra with "I") as "%F". eauto. inv F. }
      { iPoseProof (unlocked0_contra with "I") as "%F". eauto. inv F. }
      

        iDestruct "I" as "[_ [%I2 _]]". exfalso. hexploit (tkqueue_val_range_l I2 _ FIND).
        clear. i. red in H. lia.
      - iDestruct "I" as "[_ [%I2 _]]". exfalso. hexploit (tkqueue_val_range_l I2 _ FIND).
        clear. i. red in H. lia.
      - iDestruct "I" as "[_ [%I2 _]]". exfalso. des;  clarify.
      - do 2 iDestruct "I" as "[% I]". iDestruct "I" as "[I0 [% [I2 [I3 [I4 I5]]]]]".
        do 3 iDestruct "I5" as "[% I5]". iDestruct "I5" as "[I5a I5b]".
        iPoseProof (black_white with "I5a") as "#MYTURN".
        iMod ("K" with "[TKS MEM ST I0 I2 I3 I4 I5a I5b]") as "_".
        { iExists mem, own, l, tks, mytk, next, myt.
          remember 
    (⌜own = false⌝ **
       ticket_lock_inv_unlocking l tks mytk next myt
       ∨ ticket_lock_inv_unlocked0 l tks mytk next myt
     ∨ ticket_lock_inv_unlocked1 l tks mytk next myt) as temp.
          iFrame. subst temp. iRight. iSplit. auto.
          iRight. iRight. iExists yourt, waits. iFrame. iSplit. auto.
          iExists k, o, u. iFrame.
        }
        (* TODO *)

        hexploit (tkqueue_val_range_l I2 _ FIND).
        clear. i. red in H. lia.
      - 


      iStopProof.

    iAssert ((OwnM (Auth.white (NatMapRA.singleton tid mytk: NatMapRA.t nat)))
               -∗
         (MUpd (nth_default True%I I) (fairI (ident_tgt:= OMod.closed_ident TicketLock.omod (SCMem.mod TicketLock.gvs))) [0] []
               (((ObligationRA.duty (inl tid) []) ∗ (OwnM (Auth.white (NatMapRA.singleton tid mytk: NatMapRA.t nat))))
                  ∗ ((ObligationRA.duty (inl tid) [])
                       -∗ (MUpd (nth_default True%I I) (fairI (ident_tgt:= OMod.closed_ident TicketLock.omod (SCMem.mod TicketLock.gvs))) [] [0] True%I)
            ))))%I as "TEMP".
    { admit. }

    iMod ("TEMP" with "MYTK") as "[[DUTY MYTK] CLOSE]".
    iApply (stsim_yieldR_strong with "[DUTY]"). iFrame.
    iIntros "DUTY _". iPoseProof ("CLOSE" with "DUTY") as "CLOSE".
    iMod ("CLOSE") as "_". iModIntro.

    iApply MUpd_intro.

    iFrame.
    
    iMod 
    
    iApply (stsim_yieldR with ""
    
    (* TODO *)
    
    

    


  Abort.

  Lemma correct_unlock tid:
    ((own_thread tid)
       ∗ (ObligationRA.duty (inl tid) [])
    )
      ⊢
      (stsim I tid (topset I) ibot7 ibot7
             (fun r_src r_tgt => own_thread tid ** ObligationRA.duty (inl tid) [] ** ⌜r_src = r_tgt⌝)
             false false
             (AbsLock.unlock_fun tt)
             (OMod.close_itree TicketLock.omod (SCMem.mod TicketLock.gvs)
                               (TicketLock.unlock_fun tt))).
  Proof.
  Abort.







  (* Definition wait_set_wf (W: NatMap.t unit) (n: nat): iProp := *)
  (*   ((natmap_prop_sum W (fun tid _ => own_thread tid)) *)
  (*      ** *)
  (*      (OwnM (Auth.black (Some W: NatMapRA.t unit))) *)
  (*      ** *)
  (*      (⌜NatMap.cardinal W = n⌝)) *)
  (* . *)

  (* Lemma wait_set_wf_empty *)
  (*   : *)
  (*   (OwnM (Auth.black (Some (NatMap.empty unit): NatMapRA.t unit))) ⊢ wait_set_wf (NatMap.empty unit) 0. *)
  (* Proof. *)
  (*   iIntros "OWN". unfold wait_set_wf. iFrame. auto. *)
  (* Qed. *)

  (* Lemma wait_set_wf_add W tid n *)
  (*   : *)
  (*   (wait_set_wf W n) *)
  (*     -∗ *)
  (*     (own_thread tid) *)
  (*     -∗ *)
  (*     #=> (wait_set_wf (NatMap.add tid tt W) (S n) ** (OwnM (Auth.white (NatMapRA.singleton tid tt: NatMapRA.t unit)))). *)
  (* Proof. *)
  (*   iIntros "[[SUM BLACK] %] TH". *)
  (*   iAssert (⌜NatMap.find tid W = None⌝)%I as "%". *)
  (*   { destruct (NatMap.find tid W) eqn:EQ; auto. *)
  (*     iExFalso. iPoseProof (natmap_prop_sum_in with "SUM") as "H". *)
  (*     { eauto. } *)
  (*     iPoseProof (own_thread_unique with "TH H") as "%". ss. *)
  (*   } *)
  (*   iPoseProof (OwnM_Upd with "BLACK") as "> [BLACK WHTIE]". *)
  (*   { apply Auth.auth_alloc. eapply (@NatMapRA.add_local_update unit W tid tt). auto. } *)
  (*   iModIntro. iFrame. iSplit; auto. *)
  (*   { iApply (natmap_prop_sum_add with "SUM"). auto. } *)
  (*   iPureIntro. subst. *)
  (*   eapply NatMapP.cardinal_2; eauto. *)
  (*   { apply NatMapP.F.not_find_in_iff; eauto. } *)
  (*   { ss. } *)
  (* Qed. *)

  (* Lemma wait_set_wf_sub W tid n *)
  (*   : *)
  (*   (wait_set_wf W n) *)
  (*     -∗ *)
  (*     (OwnM (Auth.white (NatMapRA.singleton tid tt: NatMapRA.t unit))) *)
  (*     -∗ *)
  (*     (∃ n', *)
  (*         (⌜n = S n'⌝) *)
  (*           ** *)
  (*           #=> (wait_set_wf (NatMap.remove tid W) n' ** own_thread tid)). *)
  (* Proof. *)
  (*   iIntros "[[SUM BLACK] %] TH". *)
  (*   iCombine "BLACK TH" as "OWN". iOwnWf "OWN". *)
  (*   iAssert (⌜NatMap.find tid W = Some tt⌝)%I as "%". *)
  (*   { iOwnWf "OWN". *)
  (*     ur in H0. rewrite URA.unit_idl in H0. des. *)
  (*     apply NatMapRA.extends_singleton_iff in H0. auto. *)
  (*   } *)
  (*   hexploit cardinal_remove. *)
  (*   { apply NatMapP.F.in_find_iff. rewrite H1. ss. } *)
  (*   i. subst. iExists _. iSplit; auto. *)
  (*   iPoseProof (OwnM_Upd with "OWN") as "> BLACK". *)
  (*   { eapply Auth.auth_dealloc. apply NatMapRA.remove_local_update. } *)
  (*   iModIntro. iPoseProof (natmap_prop_remove_find with "SUM") as "[HD TL]"; [eauto|]. *)
  (*   iFrame. auto. *)
  (* Qed. *)

  (* Definition regionl (n: nat): iProp := *)
  (*   (∃ l, (Region.black l) ** (⌜List.length l = n⌝)). *)

  (* Lemma regionl_alloc n a tid *)
  (*   : *)
  (*   (regionl n) *)
  (*     -∗ *)
  (*     (#=> (regionl (S n) ** Region.white n (tid, a))). *)
  (* Proof. *)
  (*   iIntros "[% [BLACK %]]". subst. *)
  (*   iPoseProof (Region.black_alloc with "BLACK") as "> [BLACK WHITE]". *)
  (*   iModIntro. iFrame. iExists _. iSplit; auto. *)
  (*   iPureIntro. ss. apply last_length. *)
  (* Qed. *)

  (* Definition waiters (start n: nat): iProp := *)
  (*   (list_prop_sum *)
  (*      (fun a => (∃ k j tid, *)
  (*                    (Region.white (start + a) (tid, k)) *)
  (*                      ** *)
  (*                      (OwnM (FiniteMap.singleton k (Consent.vote j (/2)%Qp))) *)
  (*                      ** *)
  (*                      (ObligationRA.correl_thread j 1%ord) *)
  (*                      ** *)
  (*                      (ObligationRA.pending j (/2)%Qp) *)
  (*                      ** *)
  (*                      (∃ o, ObligationRA.black j o) *)
  (*                      ** *)
  (*                      (FairRA.white (inl tid) (a × Ord.one)%ord) *)
  (*                      ** *)
  (*                      (OwnM (Auth.white (NatMapRA.singleton tid tt: NatMapRA.t unit))) *)
  (*      )) *)
  (*      (seq 0 n))%I. *)

  (* Lemma waiters_nil start *)
  (*   : *)
  (*   ⊢ waiters start 0. *)
  (* Proof. *)
  (*   unfold waiters. ss. auto. *)
  (* Qed. *)

  (* Lemma waiters_push start n *)
  (*   : *)
  (*   (waiters start n) *)
  (*     -∗ *)
  (*     (∃ k j tid, *)
  (*         (Region.white (start + n) (tid, k)) *)
  (*           ** *)
  (*           (OwnM (FiniteMap.singleton k (Consent.vote j (/2)%Qp))) *)
  (*           ** *)
  (*           (ObligationRA.correl_thread j 1%ord) *)
  (*           ** *)
  (*           (ObligationRA.pending j (/2)%Qp) *)
  (*           ** *)
  (*           (∃ o, ObligationRA.black j o) *)
  (*           ** *)
  (*           (FairRA.white (inl tid) (n × Ord.one)%ord) *)
  (*           ** *)
  (*           (OwnM (Auth.white (NatMapRA.singleton tid tt: NatMapRA.t unit)))) *)
  (*     -∗ *)
  (*     (waiters start (S n)). *)
  (* Proof. *)
  (*   unfold waiters. rewrite list_numbers.seq_S. *)
  (*   iIntros "WAIT H". iApply list_prop_sum_combine. iSplitR "H". *)
  (*   { auto. } *)
  (*   { ss. iFrame. } *)
  (* Qed. *)

  (* Lemma waiters_rollback start n tid k a *)
  (*       (IN: start <= a < start + n) *)
  (*   : *)
  (*     (Region.white a (tid, k)) *)
  (*     -∗ *)
  (*     (waiters start n) *)
  (*     -∗ *)
  (*     ((∃ j, (OwnM (FiniteMap.singleton k (Consent.vote j (/2)%Qp))) *)
  (*              ** *)
  (*              (ObligationRA.pending j (/2)%Qp)) *)
  (*        ** *)
  (*        (∀ j, *)
  (*            (OwnM (FiniteMap.singleton k (Consent.vote j (/2)%Qp))) *)
  (*              -* *)
  (*              (ObligationRA.correl_thread j 1%ord) *)
  (*              -* *)
  (*              (ObligationRA.pending j (/2)%Qp) *)
  (*              -* *)
  (*              (∃ o, ObligationRA.black j o) *)
  (*              -* *)
  (*              (waiters start n))). *)
  (* Proof. *)
  (*   assert (RANGE: (0 <= a - start < 0 + n)%nat). *)
  (*   { lia. } *)
  (*   iIntros "WHITE WAIT". *)
  (*   apply in_seq in RANGE. apply in_split in RANGE. des. *)
  (*   unfold waiters. rewrite RANGE. *)
  (*   iPoseProof (list_prop_sum_split with "WAIT") as "[WAIT0 WAIT1]". *)
  (*   iPoseProof (list_prop_sum_cons_unfold with "WAIT1") as "[[% [% [% [[[[[[H0 H1] H2] H3] H4] H5] H6]]]] WAIT2]". *)
  (*   replace (start + (a - start)) with a by lia. *)
  (*   iPoseProof (Region.white_agree with "WHITE H0") as "%". *)
  (*   clarify. *)
  (*   iSplitL "H1 H3". *)
  (*   { iExists _. iFrame. } *)
  (*   iIntros (?) "VOTE CORR PEND BLACK". *)
  (*   iApply list_prop_sum_combine. iSplitL "WAIT0". *)
  (*   { auto. } *)
  (*   iApply list_prop_sum_cons_fold. iSplitR "WAIT2". *)
  (*   2:{ auto. } *)
  (*   iExists _, j0, _. iFrame. *)
  (*   replace (start + (a - start)) with a by lia. iFrame. *)
  (* Qed. *)

  (* Definition waiters_tax start n: iProp := *)
  (*   (list_prop_sum *)
  (*      (fun a => (∃ k tid, *)
  (*                    (Region.white (start + a) (tid, k)) *)
  (*                      ** *)
  (*                      (FairRA.white (inl tid) Ord.one))) *)
  (*      (seq 0 n))%I. *)

  (* Lemma waiters_pop start n *)
  (*   : *)
  (*   (waiters start (S n)) *)
  (*     -∗ *)
  (*     (∃ k j, *)
  (*         (waiters (S start) n) *)
  (*           ** *)
  (*           ((ConsentP.voted_singleton k j) *)
  (*              ** *)
  (*              (ObligationRA.correl_thread j 1%ord) *)
  (*              ** *)
  (*              (ObligationRA.pending j (/2)%Qp) *)
  (*              ** *)
  (*              (∃ o, ObligationRA.black j o)) *)
  (*           ** *)
  (*           (waiters_tax (S start) n)). *)
  (* Proof. *)
  (*   iIntros "WAIT". *)
  (* Admitted. *)

  (* Definition ticketlock_inv *)
  (*            (L: bool) (W: NatMap.t unit) *)
  (*            (reserved: bool) *)
  (*            (now_serving: nat) (n: nat): iProp := *)
  (*   (wait_set_wf W n) *)
  (*     ** *)
  (*     (regionl ((Nat.b2n reserved) + now_serving + n)) *)
  (*     ** *)
  (*     ((⌜n = 0 /\ L = false /\ reserved = false⌝ ** OwnM (Excl.just tt: Excl.t unit)) *)
  (*      ∨ *)
  (*        ((waiters (S ((Nat.b2n reserved) + now_serving)) n) *)
  (*           ** *)
  (*           (∃ k j, *)
  (*               (ConsentP.voted_singleton k j) *)
  (*                 ** *)
  (*                 (ObligationRA.correl_thread j 1%ord) *)
  (*                 ** *)
  (*                 (∃ o, ObligationRA.black j o) *)
  (*                 ** *)
  (*                 (((⌜L = false /\ reserved = true⌝) *)
  (*                     ** *)
  (*                     (OwnM (Excl.just tt: Excl.t unit)) *)
  (*                     ** *)
  (*                     (waiters_tax (S ((Nat.b2n reserved) + now_serving)) n) *)
  (*                     ** *)
  (*                     (ObligationRA.pending j (/2)%Qp)) *)
  (*                  ∨ *)
  (*                    ((⌜L = true /\ reserved = false⌝) *)
  (*                       ** *)
  (*                       (ObligationRA.shot j)))))). *)

End SIM.
