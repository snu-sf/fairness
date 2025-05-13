From sflib Require Import sflib.
From Paco Require Import paco.
From stdpp Require namespaces.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Export ITreeLib WFLibLarge FairBeh pind Axioms
     Mod Linking SCM Red IRed WeakestAdequacy.
From Ordinal Require Export ClassicalHessenberg.
From Fairness Require Import NatStructs NatMapRAFOS.

Set Implicit Arguments.

Module TicketLock.
  Definition gvs : list nat := [2].
  Definition now_serving: SCMem.val := SCMem.val_ptr (0, 0).
  Definition next_ticket: SCMem.val := SCMem.val_ptr (0, 1).

  Notation tk := nat.

  Definition lock_loop (myticket: SCMem.val):
    itree (threadE void unit) unit
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
    ktree (threadE void unit) unit unit :=
    fun _ =>
      myticket <- (OMod.call "faa" (next_ticket, 1));;
      _ <- lock_loop myticket;;
      trigger Yield
  .

  Definition unlock_fun:
    ktree (threadE void unit) unit unit :=
    fun _ =>
      upd <- (OMod.call "load" now_serving);;
      let upd := SCMem.val_add upd 1 in
      `_: unit <- (OMod.call "store" (now_serving, upd));;
      trigger Yield
  .

  Definition omod: Mod.t :=
    Mod.mk
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



From Fairness Require Import  IPMFOS Weakest.
From Fairness Require Import ModSim PCMFOS MonotonePCM StateRA FairRA.
From Fairness Require Import FairLock.
From Fairness Require Import NatStructs NatMapRAFOS.

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

Section INVARIANT.

  Context `{Σ: GRA.t}.

  Context `{MONORA: @GRA.inG monoRA Σ}.
  Context `{THDRA: @GRA.inG ThreadRA Σ}.
  Context `{STATESRC: @GRA.inG (stateSrcRA (Mod.state AbsLock.mod)) Σ}.
  Context `{STATETGT: @GRA.inG (stateTgtRA (OMod.closed_state TicketLock.omod (SCMem.mod TicketLock.gvs))) Σ}.
  Context `{IDENTSRC: @GRA.inG (identSrcRA (Mod.ident AbsLock.mod)) Σ}.
  Context `{IDENTTGT: @GRA.inG (identTgtRA (OMod.closed_ident TicketLock.omod (SCMem.mod TicketLock.gvs))) Σ}.
  Context `{OBLGRA: @GRA.inG ObligationRA.t Σ}.
  Context `{ARROWRA: @GRA.inG (ArrowRA (OMod.closed_ident TicketLock.omod (SCMem.mod TicketLock.gvs))) Σ}.
  Context `{EDGERA: @GRA.inG EdgeRA Σ}.
  Context `{ONESHOTSRA: @GRA.inG (@FiniteMap.t (OneShot.t unit)) Σ}.
  Context `{MEMRA: @GRA.inG memRA Σ}.

  Context `{NATMAPRA: @GRA.inG (Auth.t (NatMapRAFOS.t TicketLock.tk)) Σ}.
  Context `{AUTHRA1: @GRA.inG (Auth.t (Excl.t nat)) Σ}.
  Context `{AUTHRA2: @GRA.inG (Auth.t (Excl.t (nat * nat))) Σ}.
  Context `{IN2: @GRA.inG (thread_id ==> (Auth.t (Excl.t nat)))%ra Σ}.

  Variable monok: nat.
  Variable tk_mono: nat.

  Definition mypreord := prod_le_PreOrder Nat.le_po (Tkst.le_PreOrder nat).

  Definition ticket_lock_inv_unlocking
             (l: list thread_id) (tks: NatMap.t nat) (now next: nat) (myt: thread_id) : iProp :=
    (own_thread myt)
      ∗
      (⌜tkqueue l tks (S now) next⌝)
      ∗
      (natmap_prop_sum tks (fun th tk => FairRA.white Prism.id th (Ord.from_nat (tk - (S now)))))
      ∗
      (list_prop_sum (fun th => ((ObligationRA.duty inlp th [])
                                ∗ (∃ u, maps_to th (Auth.black (Excl.just u: Excl.t nat))))%I) l)
      ∗
      (∃ (k: nat) (o: Ord.t),
          (monoBlack monok mypreord (now, Tkst.d k))
            ∗ (ObligationRA.black k o)
            ∗ (ObligationRA.pending k 1)
            ∗ (ObligationRA.duty inlp myt [(k, Ord.S Ord.O)])
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
        (natmap_prop_sum tks (fun th tk => FairRA.white Prism.id th (Ord.from_nat (tk - (now)))))
        ∗
        (list_prop_sum (fun th => ((ObligationRA.duty inlp th [])
                                  ∗ (∃ u, maps_to th (Auth.black (Excl.just u: Excl.t nat))))%I) waits)
        ∗
        (∃ (k: nat) (o: Ord.t) (u: nat),
            (monoBlack monok mypreord (now, Tkst.b k))
              ∗ (ObligationRA.black k o)
              ∗ (ObligationRA.pending k 1)
              ∗ (ObligationRA.duty inlp yourt [(k, Ord.S Ord.O)])
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
      (natmap_prop_sum tks (fun th tk => FairRA.white Prism.id th (Ord.from_nat (tk - (S now)))))
      ∗
      (list_prop_sum (fun th => ((ObligationRA.duty inlp th [])
                                ∗ (∃ u, maps_to th (Auth.black (Excl.just u: Excl.t nat))))%I) l)
      ∗
      (∃ (k: nat),
          (monoBlack monok mypreord (now, Tkst.c k))
      )
  .

  Definition ticket_lock_inv_tks
             (tks: NatMap.t nat) : iProp :=
    ((OwnM (Auth.black (Some tks: NatMapRAFOS.t nat)))
       ∗ (FairRA.whites Prism.id (fun id => (~ NatMap.In id tks)) Ord.omega)
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
       ∗ (monoBlack tk_mono Nat.le_preorder now)
    )
  .

  Definition ticket_lock_inv_state
             (mem: SCMem.t) (own: bool) (tks: NatMap.t nat) : iProp :=
    ((St_tgt (tt, mem)) ∗ (St_src (own, key_set tks)))
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

  (* Properties *)
  Lemma unlocking_mono
        l tks now next myt:
    (ticket_lock_inv_unlocking l tks now next myt)
      -∗
      ((⌜tkqueue l tks (S now) next⌝)
         ∗
         (∃ k o, (monoWhite monok mypreord (now, Tkst.d k))
                   ∗ (ObligationRA.black k o)
      )).
  Proof.
    iIntros "I". iDestruct "I" as "[_ [%I2 [_ [_ I]]]]". do 2 iDestruct "I" as "[% I]".
    iDestruct "I" as "[MB [OB _]]". iPoseProof (black_white with "MB") as "#MYTURN".
    iSplit. auto. iExists k, o. iFrame. auto.
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
    (OwnM (Auth.white (NatMapRAFOS.singleton tid mytk: NatMapRAFOS.t nat)))
      ∗ (ticket_lock_inv_tks tks)
      -∗ ⌜NatMap.find tid tks = Some mytk⌝.
  Proof.
    iIntros "[MYTK TKS]". iDestruct "TKS" as "[TKS0 _]".
    iApply (NatMapRA_find_some with "TKS0 MYTK").
  Qed.

  Lemma ticket_lock_inv_mem_mono
        mem now next myt
    :
    (ticket_lock_inv_mem mem now next myt)
      -∗
      (monoWhite tk_mono Nat.le_preorder now).
  Proof.
    iIntros "MEM". iDestruct "MEM" as "[MEM0 [MEM1 [MEM2 [MEM3 MEM4]]]]".
    iPoseProof (black_white with "MEM4") as "#MONOTK".
    auto.
  Qed.

End INVARIANT.

Section SIM.

  Context `{Σ: GRA.t}.

  Variable Invs : @InvSet Σ.

  Context `{MONORA: @GRA.inG monoRA Σ}.
  Context `{THDRA: @GRA.inG ThreadRA Σ}.
  Context `{STATESRC: @GRA.inG (stateSrcRA (Mod.state AbsLock.mod)) Σ}.
  Context `{STATETGT: @GRA.inG (stateTgtRA (OMod.closed_state TicketLock.omod (SCMem.mod TicketLock.gvs))) Σ}.
  Context `{IDENTSRC: @GRA.inG (identSrcRA (Mod.ident AbsLock.mod)) Σ}.
  Context `{IDENTTGT: @GRA.inG (identTgtRA (OMod.closed_ident TicketLock.omod (SCMem.mod TicketLock.gvs))) Σ}.
  Context `{OBLGRA: @GRA.inG ObligationRA.t Σ}.
  Context `{ARROWRA: @GRA.inG (ArrowRA (OMod.closed_ident TicketLock.omod (SCMem.mod TicketLock.gvs))) Σ}.
  Context `{EDGERA: @GRA.inG EdgeRA Σ}.
  Context `{ONESHOTSRA: @GRA.inG (@FiniteMap.t (OneShot.t unit)) Σ}.
  Context `{COPSETRA : @GRA.inG CoPset.t Σ}.
  Context `{GSETRA : @GRA.inG Gset.t Σ}.
  Context `{INVSETRA : @GRA.inG (InvSetRA Var) Σ}.
  Context `{MEMRA: @GRA.inG memRA Σ}.

  Context `{NATMAPRA: @GRA.inG (Auth.t (NatMapRAFOS.t TicketLock.tk)) Σ}.
  Context `{AUTHRA1: @GRA.inG (Auth.t (Excl.t nat)) Σ}.
  Context `{AUTHRA2: @GRA.inG (Auth.t (Excl.t (nat * nat))) Σ}.
  Context `{IN2: @GRA.inG (thread_id ==> (Auth.t (Excl.t nat)))%ra Σ}.

  Variable monok: nat.
  Variable tk_mono: nat.
  Variable N : stdpp.namespaces.namespace.

  (* Simulations *)
  Lemma lock_enqueue tid :
    (inv N (ticket_lock_inv monok tk_mono)) ∗
    ((own_thread tid)
       ∗ (ObligationRA.duty inlp tid [])
    )
      ∗
      (∀ mytk,
          (
            (OwnM (Auth.white (NatMapRAFOS.singleton tid mytk: NatMapRAFOS.t TicketLock.tk)))
              ∗ (maps_to tid (Auth.white (Excl.just 2: Excl.t nat)))
          )
          -∗
  (stsim tid ⊤ ibot7 ibot7
         (λ r_src r_tgt : (), (own_thread tid ** ObligationRA.duty inlp tid []) ** ⌜r_src = r_tgt⌝)
         false false
    (ITree.iter
        (λ _ : (),
           trigger Yield;;;
           ` x_0 : bool * NatMap.t () <- trigger (Get id);;
           (let (own0, _) := x_0 in if Bool.eqb own0 true then Ret (inl ()) else Ret (inr ())))
        ();;;
      ` x_0 : bool * NatMap.t () <- trigger (Get id);;
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
      (stsim tid ⊤ ibot7 ibot7
             (fun r_src r_tgt => own_thread tid ** ObligationRA.duty inlp tid [] ** ⌜r_src = r_tgt⌝)
             false false
             (AbsLock.lock_fun tt)
             (OMod.close_itree TicketLock.omod (SCMem.mod TicketLock.gvs)
                               (TicketLock.lock_fun tt))).
  Proof.
    iIntros "(#LOCK_INV & [MYTH DUTY] & SIM)".
    unfold AbsLock.lock_fun, TicketLock.lock_fun. rred.
    rewrite close_itree_call. rred.
    iApply (stsim_sync with "[DUTY]"). msubtac. iFrame. iIntros "DUTY _".
    unfold Mod.wrap_fun, SCMem.faa_fun. rred.
    iApply stsim_tidL. lred.

    iInv "LOCK_INV" as "I" "K". do 7 iDestruct "I" as "[% I]". iDestruct "I" as "[TKS [MEM [ST CASES]]]".
    iDestruct "ST" as "[ST0 ST1]".
    iApply stsim_getL. iSplit. auto. iApply (stsim_modifyL with "ST1"). iIntros "ST1".

    iApply stsim_getR. iSplit. auto. rred.
    iDestruct "MEM" as "[MEM0 [MEM1 [MEM2 MEM3]]]".
    iPoseProof (memory_ra_faa with "MEM0 MEM2") as "[% [%FAA >[MEM0 MEM2]]]".
    erewrite FAA. rred. unfold OMod.emb_callee.
    iApply (stsim_modifyR with "ST0"). iIntros "ST0". rred.
    iApply stsim_tauR. rred.

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
    iPoseProof ((FairRA.whites_unfold Prism.id (fun id => ~ NatMap.In id tks') _ (i:=tid)) with "TKS1") as "[TKS1 MYTRI]".
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
     ticket_lock_inv_locked monok (l ++ [tid]) (NatMap.add tid next tks) now (S next) myt)
    ∨ (⌜false = false⌝ **
       ticket_lock_inv_unlocking monok (l ++ [tid]) (NatMap.add tid next tks) now (S next) myt
       ∨ ticket_lock_inv_unlocked0 monok (l ++ [tid]) (NatMap.add tid next tks) now (S next) myt
         ∨ ticket_lock_inv_unlocked1 monok (l ++ [tid]) (NatMap.add tid next tks) now (S next) myt))%I as temp.
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
     ticket_lock_inv_locked monok (l ++ [tid]) (NatMap.add tid next tks) now (S next) myt)
    ∨ (⌜false = false⌝ **
       ticket_lock_inv_unlocking monok (l ++ [tid]) (NatMap.add tid next tks) now (S next) myt
       ∨ ticket_lock_inv_unlocked0 monok (l ++ [tid]) (NatMap.add tid next tks) now (S next) myt
         ∨ ticket_lock_inv_unlocked1 monok (l ++ [tid]) (NatMap.add tid next tks) now (S next) myt))%I as temp.
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
     ticket_lock_inv_locked monok (l ++ [tid]) (NatMap.add tid next tks) now (S next) myt)
    ∨ (⌜false = false⌝ **
       ticket_lock_inv_unlocking monok (l ++ [tid]) (NatMap.add tid next tks) now (S next) myt
       ∨ ticket_lock_inv_unlocked0 monok (l ++ [tid]) (NatMap.add tid next tks) now (S next) myt
         ∨ ticket_lock_inv_unlocked1 monok (l ++ [tid]) (NatMap.add tid next tks) now (S next) myt))%I as temp.
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
            → itree (threadE _ (Mod.state AbsLock.mod)) R_src
            → itree
                (threadE _ (OMod.closed_state TicketLock.omod (SCMem.mod TicketLock.gvs))) R_tgt
            → iProp)
        (ps pt: bool)
        (src: itree (threadE _ (Mod.state AbsLock.mod)) unit)
        (tgt: itree (threadE _ (OMod.closed_state TicketLock.omod (SCMem.mod TicketLock.gvs))) unit)
        (tid mytk u: nat)
        x
    :
    (inv N (ticket_lock_inv monok tk_mono))
      ∗
    (
      (OwnM (Auth.white ((NatMapRAFOS.singleton tid mytk: NatMapRAFOS.t TicketLock.tk))))
        ∗ (maps_to tid (Auth.white (Excl.just (S u): Excl.t nat)))
        ∗ (monoWhite monok mypreord (mytk, x))
    )
      ∗
      (
      ((OwnM (Auth.white ((NatMapRAFOS.singleton tid mytk: NatMapRAFOS.t TicketLock.tk))))
        ∗ (maps_to tid (Auth.white (Excl.just u: Excl.t nat)))
        ∗ (monoWhite monok mypreord (mytk, x)))
        -∗
  (stsim tid ⊤ g0 g1
    (λ r_src r_tgt : (), (own_thread tid ** ObligationRA.duty inlp tid []) ** ⌜r_src = r_tgt⌝)
    ps true
    (trigger Yield;;; src)
    (tgt))
      )
      ⊢
  (stsim tid ⊤ g0 g1
    (λ r_src r_tgt : (), (own_thread tid ** ObligationRA.duty inlp tid []) ** ⌜r_src = r_tgt⌝)
    ps pt
    (trigger Yield;;; src)
    (trigger Yield;;; tgt)).
  Proof.
    iIntros "(LOCK_INV & [MYTK [MYNW MYTURN]] & SIM)".
    iInv "LOCK_INV" as "I" "K". do 7 iDestruct "I" as "[% I]". iDestruct "I" as "[TKS [MEM [ST CASES]]]".
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
          (⌜false = true⌝ ** ticket_lock_inv_locked monok (tid :: tl) tks now next myt)
          ∨ (⌜false = false⌝ **
                           ticket_lock_inv_unlocking monok (tid :: tl) tks now next myt
             ∨ ticket_lock_inv_unlocked0 monok (tid :: tl) tks now next myt
             ∨ ticket_lock_inv_unlocked1 monok (tid :: tl) tks now next myt))%I as temp.
      iFrame. subst temp.
      iRight. iSplit. auto. iRight. iRight.
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
            → itree (threadE _ (Mod.state AbsLock.mod)) R_src
            → itree
                (threadE _ (OMod.closed_state TicketLock.omod (SCMem.mod TicketLock.gvs))) R_tgt
            → iProp)
        (ps pt: bool)
        (src: itree (threadE _ (Mod.state AbsLock.mod)) unit)
        (tgt: itree (threadE _ (OMod.closed_state TicketLock.omod (SCMem.mod TicketLock.gvs))) unit)
        (tid mytk now: nat)
        tks mem next l myt own
        (NEQ: mytk <> now)
    :
  (OwnM (Auth.white (NatMapRAFOS.singleton tid mytk: NatMapRAFOS.t nat)) **
    (ticket_lock_inv_tks tks **
     (ticket_lock_inv_mem tk_mono mem now next myt **
      (ticket_lock_inv_state mem own tks **
       ((⌜own = true⌝ ** ticket_lock_inv_locked monok l tks now next myt)
        ∨ (⌜own = false⌝ **
           ticket_lock_inv_unlocking monok l tks now next myt
           ∨ ticket_lock_inv_unlocked0 monok l tks now next myt
             ∨ ticket_lock_inv_unlocked1 monok l tks now next myt) **
        (ticket_lock_inv monok tk_mono -*
         FUpd (fairI (ident_tgt:=OMod.closed_ident TicketLock.omod (SCMem.mod TicketLock.gvs)))
           (⊤∖↑N) ⊤ emp))))))
      ∗
      (((OwnM (Auth.white ((NatMapRAFOS.singleton tid mytk: NatMapRAFOS.t nat))))
          ∗ (FairRA.white_thread (S:=_)))
        -∗
  (stsim tid ⊤ g0 g1
    (λ r_src r_tgt : (), (own_thread tid ** ObligationRA.duty inlp tid []) ** ⌜r_src = r_tgt⌝)
    ps true
    (trigger Yield;;; src)
    (tgt))
      )
      ⊢
  (stsim tid (⊤ ∖ ↑N) g0 g1
    (λ r_src r_tgt : (), (own_thread tid ** ObligationRA.duty inlp tid []) ** ⌜r_src = r_tgt⌝)
    ps pt
    (trigger Yield;;; src)
    (trigger Yield;;; tgt)).
  Proof.
    iIntros "[[MYTH [TKS [MEM [ST [CASES K]]]]] SIM]".
    iPoseProof (mytk_find_some with "[MYTH TKS]") as "%FIND". iFrame.
    iDestruct "CASES" as "[[CT INV]|[CF INV]]".
    { unfold ticket_lock_inv_locked. iDestruct "INV" as "[INV0 [%INV1 [INV2 [INV3 INV4]]]]".
      hexploit (tkqueue_find_in INV1 _ FIND). i.
      iPoseProof (list_prop_sum_in_split with "INV3") as "[[DUTY MAPS] INV3]". eapply H.
      iApply (stsim_yieldR_strong with "[DUTY]"). iFrame. iIntros "DUTY RIGHT".
      iMod ("K" with "[TKS MEM ST CT INV0 INV2 INV4 MAPS INV3 DUTY]") as "_".
      { iExists mem, own, l, tks, now, next, myt.
        remember
    ((⌜own = true⌝ ** ticket_lock_inv_locked monok l tks now next myt)
    ∨ (⌜own = false⌝ **
       ticket_lock_inv_unlocking monok l tks now next myt
       ∨ ticket_lock_inv_unlocked0 monok l tks now next myt
       ∨ ticket_lock_inv_unlocked1 monok l tks now next myt))%I as temp. iFrame. subst temp.
        iLeft. iSplit. auto. iFrame. iSplit. auto. iApply "INV3". iFrame.
      }
      iModIntro. iApply "SIM". iFrame.
    }
    iDestruct "INV" as "[INV | [INV | INV]]".
    { iDestruct "INV" as "[INV0 [%INV1 [INV2 [INV3 INV4]]]]".
      hexploit (tkqueue_find_in INV1 _ FIND). i.
      iPoseProof (list_prop_sum_in_split with "INV3") as "[[DUTY MAPS] INV3]". eapply H.
      iApply (stsim_yieldR_strong with "[DUTY]"). iFrame. iIntros "DUTY RIGHT".
      iMod ("K" with "[TKS MEM ST CF INV0 INV2 INV4 MAPS INV3 DUTY]") as "_".
      { iExists mem, own, l, tks, now, next, myt.
        remember
    ((⌜own = true⌝ ** ticket_lock_inv_locked monok l tks now next myt)
    ∨ (⌜own = false⌝ **
       ticket_lock_inv_unlocking monok l tks now next myt
       ∨ ticket_lock_inv_unlocked0 monok l tks now next myt
       ∨ ticket_lock_inv_unlocked1 monok l tks now next myt))%I as temp. iFrame. subst temp.
        iRight. iSplit. auto. iLeft. iFrame. iSplit. auto. iApply "INV3". iFrame.
      }
      iModIntro. iApply "SIM". iFrame.
    }
    { iDestruct "INV" as "[INV0 [%INV1 INV2]]". exfalso. des; clarify. }
    { do 2 iDestruct "INV" as "[% INV]".
      iDestruct "INV" as "[INV0 [%INV1 [%INV2 [INV3 [INV4 INV5]]]]]".
      hexploit (tkqueue_dequeue INV2). eapply INV1. i.
      assert (NOTMT: tid <> yourt).
      { ii. clarify. inv INV2; ss. clarify. } (* setoid_rewrite FIND in FIND0. inv FIND0. ss. } *)
      hexploit (tkqueue_find_in H).
      { instantiate (1:=mytk). instantiate (1:=tid). rewrite nm_find_rm_neq; auto. }
      intro IN.
      iPoseProof (list_prop_sum_in_split with "INV4") as "[[DUTY MAPS] INV4]". eapply IN.
      iApply (stsim_yieldR_strong with "[DUTY]"). iFrame. iIntros "DUTY RIGHT".
      iMod ("K" with "[TKS MEM ST CF INV0 INV3 INV5 MAPS INV4 DUTY]") as "_".
      { iExists mem, own, l, tks, now, next, myt.
        remember
    ((⌜own = true⌝ ** ticket_lock_inv_locked monok l tks now next myt)
    ∨ (⌜own = false⌝ **
       ticket_lock_inv_unlocking monok l tks now next myt
       ∨ ticket_lock_inv_unlocked0 monok l tks now next myt
       ∨ ticket_lock_inv_unlocked1 monok l tks now next myt))%I as temp. iFrame. subst temp.
        iRight. iSplit. auto. iRight. iRight. iFrame. iExists yourt, waits.
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
            → itree (threadE _ (Mod.state AbsLock.mod)) R_src
            → itree (threadE _ (OMod.closed_state TicketLock.omod (SCMem.mod TicketLock.gvs))) R_tgt → iProp)
        (ps pt: bool)
        (tid : nat)
        (mytk : TicketLock.tk)
        x tx
        (TX: 1 <= tx)
    :
    (inv N (ticket_lock_inv monok tk_mono)) ∗
    ((monoWhite monok mypreord (mytk, x))
       ∗ (OwnM (Auth.white (NatMapRAFOS.singleton tid mytk: NatMapRAFOS.t nat)))
       ∗ (maps_to tid (Auth.white (Excl.just tx: Excl.t nat))))
  ⊢ stsim tid ⊤ g0 g1
      (λ r_src r_tgt : (), (own_thread tid ** ObligationRA.duty inlp tid []) ** ⌜r_src = r_tgt⌝)
      ps pt
      (trigger Yield;;;
       ` x : () + () <-
       (` x_0 : bool * NatMap.t () <- trigger (Get id);;
        (let (own0, _) := x_0 in if Bool.eqb own0 true then Ret (inl ()) else Ret (inr ())));;
       match x with
       | inl l0 =>
           tau;; ITree.iter
                   (λ _ : (),
                      trigger Yield;;;
                      ` x_0 : bool * NatMap.t () <- trigger (Get id);;
                      (let (own0, _) := x_0 in
                       if Bool.eqb own0 true then Ret (inl ()) else Ret (inr ()))) l0
       | inr r0 => Ret r0
       end;;;
       ` x_0 : bool * NatMap.t () <- trigger (Get id);;
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
       map_event (OMod.emb_callee TicketLock.omod (SCMem.mod TicketLock.gvs))
         (Mod.wrap_fun SCMem.load_fun (Any.upcast TicketLock.now_serving));;
       ` x : SCMem.val <- (tau;; unwrap (Any.downcast r));;
       OMod.close_itree TicketLock.omod (SCMem.mod TicketLock.gvs)
         (` b : bool <- OMod.call "compare" (x, SCMem.val_nat mytk);;
          (if b then Ret () else tau;; TicketLock.lock_loop (SCMem.val_nat mytk)));;;
         OMod.close_itree TicketLock.omod (SCMem.mod TicketLock.gvs) (trigger Yield)).
  Proof.
    iIntros "[#LOCK_INV [#MYTN [MYTK MYNU]]]".
    iInv "LOCK_INV" as "I" "K".
    do 7 iDestruct "I" as "[% I]". iDestruct "I" as "[TKS [MEM [ST CASES]]]".
    iPoseProof (mytk_find_some with "[MYTK TKS]") as "%FIND". iFrame.
    iDestruct "CASES" as "[[%CT I] | [%CF [I | [I | I]]]]".
    { iPoseProof (locked_myturn with "MYTN I") as "%FF". eauto. inv FF. }
    { iPoseProof (unlocking_myturn with "MYTN I") as "%FF". eauto. inv FF. }
    { iPoseProof (unlocked0_contra with "I") as "%FF". eauto. inv FF. }
    iPoseProof (unlocked1_myturn with "MYTN I") as "%EQ". eauto. subst now.

    unfold Mod.wrap_fun, SCMem.load_fun. rred.
    iDestruct "MEM" as "[MEM0 [MEM1 [MEM2 MEM3]]]". iDestruct "ST" as "[ST0 ST1]".
    iApply stsim_getR. iSplit. eauto. rred.
    iPoseProof (memory_ra_load with "MEM0 MEM1") as "%LOAD". des. rewrite LOAD. rred.
    iApply stsim_tauR. rred.
    rewrite close_itree_call. rred.

    iMod ("K" with "[TKS MEM0 MEM1 MEM2 MEM3 ST0 ST1 I]") as "_".
    { iExists mem, own, l, tks, mytk, next, myt. iFrame. iRight. iSplit; auto. }
    clear pt mem own l tks next myt FIND CF LOAD LOAD0.
    assert (exists tx0, tx = S tx0).
    { inv TX; eauto. }
    des. subst tx.
    iApply lock_myturn_yieldR. iSplitR. iApply "LOCK_INV". iSplitL. iFrame. auto.
    iIntros "[MYTK [MYNUM _]]". rred.

    iInv "LOCK_INV" as "I" "K".
    do 7 iDestruct "I" as "[% I]". iDestruct "I" as "[TKS [MEM [ST CASES]]]".
    iPoseProof (mytk_find_some with "[MYTK TKS]") as "%FIND". iFrame.
    iDestruct "CASES" as "[[%CT I] | [%CF [I | [I | I]]]]".
    { iPoseProof (locked_myturn with "MYTN I") as "%FF". eauto. inv FF. }
    { iPoseProof (unlocking_myturn with "MYTN I") as "%FF". eauto. inv FF. }
    { iPoseProof (unlocked0_contra with "I") as "%FF". eauto. inv FF. }
    iPoseProof (unlocked1_myturn with "MYTN I") as "%EQ". eauto. subst now.

    unfold Mod.wrap_fun, SCMem.compare_fun. rred.
    iDestruct "MEM" as "[MEM0 [MEM1 [MEM2 MEM3]]]". iDestruct "ST" as "[ST0 ST1]".
    iApply stsim_getR. iSplit. eauto. rred.
    iApply stsim_tauR. rred.
    destruct (Nat.eq_dec mytk mytk).
    2:{ exfalso. auto. }
    clear e. subst. rred.

    iApply stsim_yieldL. lred.
    iApply stsim_getL. iSplit. auto. lred.
    iApply stsim_getL. iSplit. auto.
    iApply (stsim_modifyL with "ST1"). iIntros "ST1".

    remember (NatMap.remove tid tks) as tks'.
    rewrite <- key_set_pull_rm_eq. rewrite <- Heqtks'.
    iAssert (ticket_lock_inv_state mem true tks')%I with "[ST0 ST1]" as "ST". iFrame.
    iAssert (ticket_lock_inv_mem tk_mono mem mytk next myt)%I with "[MEM0 MEM1 MEM2 MEM3]" as "MEM". iFrame.
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

    iClear "I6 I9". iPoseProof (ObligationRA.pending_shot with "I7") as ">I7".
    iPoseProof (ObligationRA.duty_done with "I8 I7") as ">DUTY".
    iPoseProof (black_updatable with "I5") as ">I5".
    { instantiate (1:=(mytk, Tkst.c k)). econs 2. ss. split; ss. lia. }
    hexploit (tkqueue_dequeue I2).
    { reflexivity. }
    i. rename I2 into I2Old, H into I2. (* unfold TicketLock.tk in I2. *) rewrite <- Heqtks' in I2.
    iPoseProof (natmap_prop_remove with "I3") as "I3". rewrite <- Heqtks'.

    iPoseProof (natmap_prop_sum_impl with "I3") as "I3".
    { instantiate (1:= fun th tk =>
                         ((FairRA.white Prism.id th (Ord.from_nat (tk - (S mytk))))
                            ∗ (FairRA.white Prism.id th Ord.one))%I).
      i. ss. iIntros "WHI". erewrite FairRA.white_eq.
      2:{ instantiate (1:= (OrderedCM.add (Ord.from_nat (a - (S mytk))) (Ord.one))).
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
    { iExists mem, true, tl, tks', mytk, next, myt.
      remember
    ((⌜true = true⌝ ** ticket_lock_inv_locked monok tl tks' mytk next myt)
    ∨ (⌜true = false⌝ **
       ticket_lock_inv_unlocking monok tl tks' mytk next myt
       ∨ ticket_lock_inv_unlocked0 monok tl tks' mytk next myt
       ∨ ticket_lock_inv_unlocked1 monok tl tks' mytk next myt))%I as temp.
      iFrame. subst temp. iLeft. iSplit. auto.
      iFrame. iSplit. auto. iExists k. iFrame.
    }
    iApply (stsim_sync with "[DUTY]"). msubtac. iFrame.
    iIntros "DUTY _". rred.
    iApply stsim_tauR. iApply stsim_ret. iModIntro. iFrame. auto.

  Qed.

  Lemma lock_myturn1
        (g0 g1 : ∀ R_src R_tgt : Type,
            (R_src → R_tgt → iProp)
            → bool
            → bool
            → itree (threadE _ (Mod.state AbsLock.mod)) R_src
            → itree (threadE _ (OMod.closed_state TicketLock.omod (SCMem.mod TicketLock.gvs))) R_tgt → iProp)
        (ps pt: bool)
        (tid : nat)
        (mytk : TicketLock.tk)
        (mem : SCMem.t)
        (own : bool)
        (l : list nat)
        (tks : NatMap.t nat)
        (next myt : nat)
    :
    (inv N (ticket_lock_inv monok tk_mono)) ∗
  (OwnM (Auth.white (NatMapRAFOS.singleton tid mytk: NatMapRAFOS.t nat)) **
   (maps_to tid (Auth.white (Excl.just 2: Excl.t nat)) **
    (ticket_lock_inv_tks tks **
     (ticket_lock_inv_mem tk_mono mem mytk next myt **
      (ticket_lock_inv_state mem own tks **
       ((⌜own = true⌝ ** ticket_lock_inv_locked monok l tks mytk next myt)
        ∨ (⌜own = false⌝ **
           ticket_lock_inv_unlocking monok l tks mytk next myt
           ∨ ticket_lock_inv_unlocked0 monok l tks mytk next myt
             ∨ ticket_lock_inv_unlocked1 monok l tks mytk next myt) **
        (ticket_lock_inv monok tk_mono -*
           FUpd (fairI (ident_tgt:=OMod.closed_ident TicketLock.omod (SCMem.mod TicketLock.gvs)))
           (⊤∖↑N) ⊤ emp)))))))
  ⊢ (stsim tid (⊤∖↑N) g0 g1
      (λ r_src r_tgt : (), (own_thread tid ** ObligationRA.duty inlp tid []) ** ⌜r_src = r_tgt⌝)
      ps pt
      (trigger Yield;;;
       ` x : () + () <-
       (` x_0 : bool * NatMap.t () <- trigger (Get id);;
        (let (own0, _) := x_0 in if Bool.eqb own0 true then Ret (inl ()) else Ret (inr ())));;
       match x with
       | inl l0 =>
           tau;; ITree.iter
                   (λ _ : (),
                      trigger Yield;;;
                      ` x_0 : bool * NatMap.t () <- trigger (Get id);;
                      (let (own0, _) := x_0 in
                       if Bool.eqb own0 true then Ret (inl ()) else Ret (inr ()))) l0
       | inr r0 => Ret r0
       end;;;
       ` x_0 : bool * NatMap.t () <- trigger (Get id);;
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
        map_event (OMod.emb_callee TicketLock.omod (SCMem.mod TicketLock.gvs))
          (Mod.wrap_fun SCMem.load_fun (Any.upcast TicketLock.now_serving));;
        (tau;; unwrap (Any.downcast rv)));;
       OMod.close_itree TicketLock.omod (SCMem.mod TicketLock.gvs)
         (` b : bool <- OMod.call "compare" (x, SCMem.val_nat mytk);;
          (if b then Ret () else tau;; TicketLock.lock_loop (SCMem.val_nat mytk)));;;
         OMod.close_itree TicketLock.omod (SCMem.mod TicketLock.gvs) (trigger Yield))).
  Proof.
    iIntros "[#LOCK_INV [MYTK [MYN [TKS [MEM [ST [CASES K]]]]]]]".
    iAssert (⌜NatMap.find tid tks = Some mytk⌝)%I as "%FIND".
    { iDestruct "TKS" as "[TKS0 _]". iApply (NatMapRA_find_some with "TKS0 MYTK"). }
    iDestruct "CASES" as "[[%CT I] | [%CF [I | [I | I]]]]".
    { iPoseProof (locked_contra with "I") as "%F". eauto. inv F. }
    { iPoseProof (unlocking_contra with "I") as "%F". eauto. inv F. }
    { iPoseProof (unlocked0_contra with "I") as "%F". eauto. inv F. }
    iPoseProof (unlocked1_mono with "I") as "[%TKQ #MYMW]".
    iDestruct "MYMW" as "[% [% [MYMW _]]]".
    iMod ("K" with "[TKS MEM ST I]") as "_".
    { iExists mem, own, l, tks, mytk, next, myt. iFrame. iRight. iSplit; auto. }
    iApply stsim_FUpd. instantiate (1 := ⊤). iModIntro.
    iApply lock_myturn_yieldR. iSplitR. iApply "LOCK_INV". iSplitL. iFrame. auto.
    iIntros "[MYTK [MYN _]]". rred.
    iApply lock_myturn0. 2: iFrame; auto. lia.
  Qed.

  Lemma lock_myturn2
        (g0 g1 : ∀ R_src R_tgt : Type,
            (R_src → R_tgt → iProp)
            → bool
            → bool
            → itree (threadE _(Mod.state AbsLock.mod)) R_src
            → itree (threadE _ (OMod.closed_state TicketLock.omod (SCMem.mod TicketLock.gvs))) R_tgt → iProp)
        (ps pt: bool)
        (tid : nat)
        (mytk : TicketLock.tk)
        (mem : SCMem.t)
        (own : bool)
        (l : list nat)
        (tks : NatMap.t nat)
        (next myt : nat)
        now_old
        (NEQ: mytk <> now_old)
    :
    (inv N (ticket_lock_inv monok tk_mono)) ∗
  (OwnM (Auth.white (NatMapRAFOS.singleton tid mytk: NatMapRAFOS.t nat)) **
   (maps_to tid (Auth.white (Excl.just 2: Excl.t nat)) **
    (ticket_lock_inv_tks tks **
     (ticket_lock_inv_mem tk_mono mem mytk next myt **
      (ticket_lock_inv_state mem own tks **
       ((⌜own = true⌝ ** ticket_lock_inv_locked monok l tks mytk next myt)
        ∨ (⌜own = false⌝ **
           ticket_lock_inv_unlocking monok l tks mytk next myt
           ∨ ticket_lock_inv_unlocked0 monok l tks mytk next myt
             ∨ ticket_lock_inv_unlocked1 monok l tks mytk next myt) **
        (ticket_lock_inv monok tk_mono -*
           FUpd (fairI (ident_tgt:=OMod.closed_ident TicketLock.omod (SCMem.mod TicketLock.gvs)))
           (⊤∖↑N) ⊤ emp)))))))
  ⊢ (stsim tid (⊤∖↑N) g0 g1
    (λ r_src r_tgt : (), (own_thread tid ** ObligationRA.duty inlp tid []) ** ⌜r_src = r_tgt⌝)
    ps pt
    (trigger Yield;;;
     ` x : () + () <-
     (` x_0 : bool * NatMap.t () <- trigger (Get id);;
      (let (own0, _) := x_0 in if Bool.eqb own0 true then Ret (inl ()) else Ret (inr ())));;
     match x with
     | inl l0 =>
         tau;; ITree.iter
                 (λ _ : (),
                    trigger Yield;;;
                    ` x_0 : bool * NatMap.t () <- trigger (Get id);;
                    (let (own0, _) := x_0 in
                     if Bool.eqb own0 true then Ret (inl ()) else Ret (inr ()))) l0
     | inr r0 => Ret r0
     end;;;
     ` x_0 : bool * NatMap.t () <- trigger (Get id);;
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
     map_event (OMod.emb_callee TicketLock.omod (SCMem.mod TicketLock.gvs))
       (Mod.wrap_fun SCMem.compare_fun (Any.upcast (SCMem.val_nat now_old, SCMem.val_nat mytk)));;
     ` x : bool <- (tau;; unwrap (Any.downcast r));;
     OMod.close_itree TicketLock.omod (SCMem.mod TicketLock.gvs)
       (if x then Ret () else tau;; TicketLock.lock_loop (SCMem.val_nat mytk));;;
       OMod.close_itree TicketLock.omod (SCMem.mod TicketLock.gvs) (trigger Yield))).
  Proof.
    iIntros "[#LOCK_INV [MYTK [MYN [TKS [MEM [ST [CASES K]]]]]]]".
    unfold Mod.wrap_fun, SCMem.compare_fun. rred.
    iDestruct "MEM" as "[MEM0 [MEM1 [MEM2 MEM3]]]". iDestruct "ST" as "[ST0 ST1]".
    iApply stsim_getR. iSplit. eauto. rred.
    iApply stsim_tauR. rred.
    destruct (Nat.eq_dec now_old mytk).
    { exfalso. clarify. }
    rred. iApply stsim_tauR.
    rewrite TicketLock.lock_loop_red. rred. rewrite close_itree_call. rred.
    iApply lock_myturn1.
    iSplitR. iApply "LOCK_INV". iSplitL "MYTK". iFrame. iSplitL "MYN". iFrame. iSplitL "TKS". iFrame.
    iSplitL "MEM0 MEM1 MEM2 MEM3". iFrame. iSplitL "ST0 ST1". iFrame. iSplitL "CASES". iFrame.
    iFrame.
  Qed.

  Let src_code_coind tid: itree (threadE _ (Mod.state AbsLock.mod)) () :=
          ((` lr : () + () <-
            (trigger Yield;;;
             ` x_0 : bool * NatMap.t () <- trigger (Get id);;
             (let (own0, _) := x_0 in if Bool.eqb own0 true then Ret (inl ()) else Ret (inr ())));;
            match lr with
            | inl l0 =>
                tau;; ITree.iter
                        (λ _ : (),
                           trigger Yield;;;
                           ` x_0 : bool * NatMap.t () <- trigger (Get id);;
                           (let (own0, _) := x_0 in
                            if Bool.eqb own0 true then Ret (inl ()) else Ret (inr ()))) l0
            | inr r0 => Ret r0
            end);;;
           ` x_0 : bool * NatMap.t () <- trigger (Get id);;
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
                     else Flag.emp));;; trigger Yield;;; Ret ())).

  Let tgt_code_coind a :=
          (trigger Yield;;;
           ` x : SCMem.val <-
           (` rv : Any.t <-
            map_event (OMod.emb_callee TicketLock.omod (SCMem.mod TicketLock.gvs))
              (` arg : SCMem.val <- unwrap (Any.downcast (Any.upcast TicketLock.now_serving));;
               ` ret : SCMem.val <-
               (` m : SCMem.t <- trigger (Get id);;
                ` v : SCMem.val <- unwrap (SCMem.load m arg);; Ret v);;
               Ret (Any.upcast ret));; (tau;; unwrap (Any.downcast rv)));;
           OMod.close_itree TicketLock.omod (SCMem.mod TicketLock.gvs)
             (` b : bool <- OMod.call "compare" (x, SCMem.val_nat a);;
              (if b then Ret () else tau;; TicketLock.lock_loop (SCMem.val_nat a)));;;
           OMod.close_itree TicketLock.omod (SCMem.mod TicketLock.gvs) (trigger Yield)).

  Lemma lock_yourturn_coind
        (g0 g1 : ∀ R_src R_tgt : Type,
            (R_src → R_tgt → iProp)
            → bool
            → bool
            → itree (threadE _ (Mod.state AbsLock.mod)) R_src
            → itree (threadE _ (OMod.closed_state TicketLock.omod (SCMem.mod TicketLock.gvs))) R_tgt → iProp)
        (ps pt: bool)
        (tid : nat)
        (mytk : TicketLock.tk)
        (mem : SCMem.t)
        (l : list nat)
        (tks : NatMap.t nat)
        (now next myt : nat)
        now_old
        (NEQ: mytk <> now_old)
    :
  (□ (∀ a : TicketLock.tk,
        (OwnM (Auth.white (NatMapRAFOS.singleton tid a: NatMapRAFOS.t nat)) ** maps_to tid (Auth.white (Excl.just 2: Excl.t nat))) -*
        g1 ()%type ()%type
          (λ r_src r_tgt : (),
              (own_thread tid ** ObligationRA.duty inlp tid []) ** ⌜r_src = r_tgt⌝) false false
          (src_code_coind tid)
          (tgt_code_coind a)
     ) **
   (maps_to tid (Auth.white (Excl.just 2: Excl.t nat)) **
    (OwnM (Auth.white (NatMapRAFOS.singleton tid mytk: NatMapRAFOS.t nat)) **
     (ticket_lock_inv_tks tks **
      (ticket_lock_inv_mem tk_mono mem now next myt **
       (ticket_lock_inv_state mem true tks **
        (ticket_lock_inv_locked monok l tks now next myt **
         (ticket_lock_inv monok tk_mono -*
            FUpd (fairI (ident_tgt:=OMod.closed_ident TicketLock.omod (SCMem.mod TicketLock.gvs)))
            (⊤∖↑N) ⊤ emp)))))))
  )
  ⊢ (stsim tid (⊤∖↑N) g0 g1
      (λ r_src r_tgt : (), (own_thread tid ** ObligationRA.duty inlp tid []) ** ⌜r_src = r_tgt⌝)
      ps pt
      (trigger Yield;;;
       ` x : () + () <-
       (` x_0 : bool * NatMap.t () <- trigger (Get id);;
        (let (own0, _) := x_0 in if Bool.eqb own0 true then Ret (inl ()) else Ret (inr ())));;
       match x with
       | inl l0 =>
           tau;; ITree.iter
                   (λ _ : (),
                      trigger Yield;;;
                      ` x_0 : bool * NatMap.t () <- trigger (Get id);;
                      (let (own0, _) := x_0 in
                       if Bool.eqb own0 true then Ret (inl ()) else Ret (inr ()))) l0
       | inr r0 => Ret r0
       end;;;
       ` x_0 : bool * NatMap.t () <- trigger (Get id);;
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
       map_event (OMod.emb_callee TicketLock.omod (SCMem.mod TicketLock.gvs))
         (Mod.wrap_fun SCMem.compare_fun (Any.upcast (SCMem.val_nat now_old, SCMem.val_nat mytk)));;
       ` x : bool <- (tau;; unwrap (Any.downcast r));;
       OMod.close_itree TicketLock.omod (SCMem.mod TicketLock.gvs)
         (if x then Ret () else tau;; TicketLock.lock_loop (SCMem.val_nat mytk));;;
       OMod.close_itree TicketLock.omod (SCMem.mod TicketLock.gvs) (trigger Yield))).
  Proof.
    iIntros "[#CIH [MYTK [MYN [TKS [MEM [ST [I K]]]]]]]".
    unfold Mod.wrap_fun, SCMem.compare_fun. rred.
    iDestruct "MEM" as "[MEM0 [MEM1 [MEM2 MEM3]]]". iDestruct "ST" as "[ST0 ST1]".
    iApply stsim_getR. iSplit. eauto. rred.
    iApply stsim_tauR. rred.
    destruct (Nat.eq_dec now_old mytk).
    { exfalso. clarify. }
    rred. iApply stsim_tauR.
    rewrite TicketLock.lock_loop_red. rred. rewrite close_itree_call. rred.

    iApply stsim_yieldL. lred.
    iApply stsim_getL. iSplit. auto. lred.
    iApply stsim_tauL.
    iMod ("K" with "[TKS MEM0 MEM1 MEM2 MEM3 ST0 ST1 I]") as "_".
    { do 7 iExists _.
      iSplitL "TKS". iFrame. iSplitL "MEM0 MEM1 MEM2 MEM3". iFrame.
      iSplitL "ST0 ST1". iFrame.
      iLeft. iSplit. auto. iFrame.
    }
    iApply stsim_progress. iApply stsim_base. ss.
    rewrite unfold_iter_eq. iApply "CIH". iFrame.
  Qed.

  Lemma yourturn_range
        tid tks mytk now next own l myt
        (FIND : NatMap.find tid tks = Some mytk)
        (NEQ : mytk ≠ now)
    :
    ((⌜own = true⌝ ∗ ticket_lock_inv_locked monok l tks now next myt)
     ∨ (⌜own = false⌝ ∗
                    (ticket_lock_inv_unlocking monok l tks now next myt
                     ∨ ticket_lock_inv_unlocked0 monok l tks now next myt
                     ∨ ticket_lock_inv_unlocked1 monok l tks now next myt)))
      ⊢
      (⌜now < mytk⌝).
  Proof.
    iIntros "[[%CT I] | [%CF [I | [I | I]]]]".
    { iDestruct "I" as "[_ [%I1 _]]".
      hexploit (tkqueue_val_range_l I1 _ FIND). i. iPureIntro. lia. }
    { iDestruct "I" as "[_ [%I1 _]]".
      hexploit (tkqueue_val_range_l I1 _ FIND). i. iPureIntro. lia. }
    { iPoseProof (unlocked0_contra with "I") as "%FF". eauto. inv FF. }
    { iPoseProof (unlocked1_mono with "I") as "[%I1 _]".
      hexploit (tkqueue_val_range_l I1 _ FIND). i. iPureIntro. lia. }
  Qed.

  Let src_code_ind tid: itree (threadE _ (Mod.state AbsLock.mod)) () :=
                         (trigger Yield;;;
                          ` x : () + () <-
                          (` x_0 : bool * NatMap.t () <- trigger (Get id);;
                           (let (own0, _) := x_0 in
                            if Bool.eqb own0 true then Ret (inl ()) else Ret (inr ())));;
                          match x with
                          | inl l0 =>
                              tau;; ITree.iter
                                      (λ _ : (),
                                         trigger Yield;;;
                                         ` x_0 : bool * NatMap.t () <-
                                         trigger (Get id);;
                                         (let (own0, _) := x_0 in
                                          if Bool.eqb own0 true
                                          then Ret (inl ())
                                          else Ret (inr ()))) l0
                          | inr r0 => Ret r0
                          end;;;
                          ` x_0 : bool * NatMap.t () <- trigger (Get id);;
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
                                    else Flag.emp));;; trigger Yield;;; Ret ())).

  Let tgt_code_ind mytk now_old :=
                         (` r : Any.t <-
                          map_event (OMod.emb_callee TicketLock.omod (SCMem.mod TicketLock.gvs))
                            (Mod.wrap_fun SCMem.compare_fun
                               (Any.upcast (SCMem.val_nat now_old, SCMem.val_nat mytk)));;
                          ` x : bool <- (tau;; unwrap (Any.downcast r));;
                          OMod.close_itree TicketLock.omod (SCMem.mod TicketLock.gvs)
                            (if x
                             then Ret ()
                             else tau;; TicketLock.lock_loop (SCMem.val_nat mytk));;;
                          OMod.close_itree TicketLock.omod (SCMem.mod TicketLock.gvs)
                            (trigger Yield)).

  Lemma lock_yourturn_ind0
        (g0 g1 : ∀ R_src R_tgt : Type,
            (R_src → R_tgt → iProp)
            → bool
            → bool
            → itree (threadE _ (Mod.state AbsLock.mod)) R_src
            → itree (threadE _ (OMod.closed_state TicketLock.omod (SCMem.mod TicketLock.gvs))) R_tgt → iProp)
        (tid : nat)
        (mytk : TicketLock.tk)
  (now : nat)
  (LT : now < mytk)
  (IH : ∀ y : nat,
         y < mytk - now
         → ∀ now_old : nat,
             mytk ≠ now_old
             → ∀ (mem : SCMem.t) (own : bool) (l : list nat) (tks : NatMap.t nat)
                 (now next myt : nat),
                 now < mytk
                 → y = mytk - now
                   → (□ ((∀ a : TicketLock.tk,
                             (□ inv N (ticket_lock_inv monok tk_mono)) ∗
                            (OwnM (Auth.white (NatMapRAFOS.singleton tid a: NatMapRAFOS.t nat)) **
                             maps_to tid (Auth.white (Excl.just 2: Excl.t nat))) -*
                            g1 ()%type ()%type
                              (λ r_src r_tgt : (),
                                 (own_thread tid ** ObligationRA.duty inlp tid []) **
                                 ⌜r_src = r_tgt⌝) false false
                              (src_code_coind tid)
                              (tgt_code_coind a)
                         )
                         ∧ (inv N (ticket_lock_inv monok tk_mono))
                         ∧ monoWhite tk_mono Nat.le_preorder now
                        ) **
                      (maps_to tid (Auth.white (Excl.just 2: Excl.t nat)) **
                       (OwnM (Auth.white (NatMapRAFOS.singleton tid mytk: NatMapRAFOS.t nat)) **
                        (ticket_lock_inv_tks tks **
                         (ticket_lock_inv_state mem own tks **
                          ((⌜own = true⌝ ** ticket_lock_inv_locked monok l tks now next myt)
                           ∨ (⌜own = false⌝ **
                              ticket_lock_inv_unlocking monok l tks now next myt
                              ∨ ticket_lock_inv_unlocked0 monok l tks now next myt
                                ∨ ticket_lock_inv_unlocked1 monok l tks now next myt) **
                           ((ticket_lock_inv monok tk_mono -*
                               FUpd
                               (fairI
                                  (ident_tgt:=OMod.closed_ident TicketLock.omod
                                                (SCMem.mod TicketLock.gvs)))
                               (⊤∖↑N) ⊤ emp) **
                            ticket_lock_inv_mem tk_mono mem now next myt)))))))
                     ⊢ stsim tid (⊤∖↑N) g0 g1
                         (λ r_src r_tgt : (),
                            (own_thread tid ** ObligationRA.duty inlp tid []) ** ⌜r_src = r_tgt⌝)
                         false true
                         (src_code_ind tid)
                         (tgt_code_ind mytk now_old)
  )
  (now_old : nat)
  (NEQ : mytk ≠ now_old)
  (mem : SCMem.t)
  (l : list nat)
  (tks : NatMap.t nat)
  (next myt : nat)
    :
    (inv N (ticket_lock_inv monok tk_mono)) ∗
  (□ ((∀ a : TicketLock.tk,
    (□ inv N (ticket_lock_inv monok tk_mono)) ∗
        (OwnM (Auth.white (NatMapRAFOS.singleton tid a: NatMapRAFOS.t nat)) ** maps_to tid (Auth.white (Excl.just 2: Excl.t nat))) -*
        g1 ()%type ()%type
          (λ r_src r_tgt : (),
             (own_thread tid ** ObligationRA.duty inlp tid []) ** ⌜r_src = r_tgt⌝) false false
          (src_code_coind tid)
          (tgt_code_coind a))
          ∧
  (monoWhite tk_mono Nat.le_preorder now)
     ) **
   (maps_to tid (Auth.white (Excl.just 2: Excl.t nat)) **
    (OwnM (Auth.white (NatMapRAFOS.singleton tid mytk: NatMapRAFOS.t nat)) **
     (ticket_lock_inv_tks tks **
      (ticket_lock_inv_mem tk_mono mem now next myt **
       (ticket_lock_inv_state mem false tks **
        (ticket_lock_inv_unlocking monok l tks now next myt **
         (ticket_lock_inv monok tk_mono -*
            FUpd
            (fairI (ident_tgt:=OMod.closed_ident TicketLock.omod (SCMem.mod TicketLock.gvs)))
            (⊤∖↑N) ⊤ emp)))))))
  )
  ⊢ (stsim tid (⊤∖↑N) g0 g1
      (λ r_src r_tgt : (), (own_thread tid ** ObligationRA.duty inlp tid []) ** ⌜r_src = r_tgt⌝)
      false true
      (trigger Yield;;;
       ` x : () + () <-
       (` x_0 : bool * NatMap.t () <- trigger (Get id);;
        (let (own0, _) := x_0 in if Bool.eqb own0 true then Ret (inl ()) else Ret (inr ())));;
       match x with
       | inl l0 =>
           tau;; ITree.iter
                   (λ _ : (),
                      trigger Yield;;;
                      ` x_0 : bool * NatMap.t () <- trigger (Get id);;
                      (let (own0, _) := x_0 in
                       if Bool.eqb own0 true then Ret (inl ()) else Ret (inr ()))) l0
       | inr r0 => Ret r0
       end;;;
       ` x_0 : bool * NatMap.t () <- trigger (Get id);;
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
       map_event (OMod.emb_callee TicketLock.omod (SCMem.mod TicketLock.gvs))
         (Mod.wrap_fun SCMem.compare_fun (Any.upcast (SCMem.val_nat now_old, SCMem.val_nat mytk)));;
       ` x : bool <- (tau;; unwrap (Any.downcast r));;
       OMod.close_itree TicketLock.omod (SCMem.mod TicketLock.gvs)
         (if x then Ret () else tau;; TicketLock.lock_loop (SCMem.val_nat mytk));;;
       OMod.close_itree TicketLock.omod (SCMem.mod TicketLock.gvs) (trigger Yield))).
  Proof.
    iIntros "[#LOCK_INV [#[CIH MONOTK] [MYN [MYTK [TKS [MEM [ST [I K]]]]]]]]".
    iPoseProof (mytk_find_some with "[MYTK TKS]") as "%FIND". iFrame.
    iPoseProof (unlocking_mono with "I") as "[%TKQ #[% [% [MONOW OBLB]]]]".
    clear FIND TKQ.
    iStopProof. move o before IH. revert_until o. pattern o. revert o.
    apply (well_founded_induction Ord.lt_well_founded).
    intros o IHo. intros.
    iIntros "[#[LOCK_INV [CIH [MONOTK [MONOW BLK]]]] [MYN [MYTK [TKS [MEM [ST [I K]]]]]]]".

    unfold Mod.wrap_fun, SCMem.compare_fun. rred.
    iDestruct "MEM" as "[MEM0 [MEM1 [MEM2 MEM3]]]". iDestruct "ST" as "[ST0 ST1]".
    iApply stsim_getR. iSplit. eauto. rred.
    iApply stsim_tauR. rred.
    destruct (Nat.eq_dec now_old mytk).
    { exfalso. clarify. }
    rred. iApply stsim_tauR.
    rewrite TicketLock.lock_loop_red. rred. rewrite close_itree_call. rred.
    iAssert (ticket_lock_inv_mem tk_mono mem now next myt)%I with "[MEM0 MEM1 MEM2 MEM3]" as "MEM". iFrame.
    iAssert (ticket_lock_inv_state mem false tks)%I with "[ST0 ST1]" as "ST". iFrame.
    iMod ("K" with "[TKS MEM ST I]") as "_".
    { do 7 iExists _. iSplitL "TKS". iFrame. iSplitL "MEM". iFrame. iSplitL "ST". iFrame.
      iRight. iSplit. auto. iLeft. iFrame.
    }
    clear mem l tks next myt now_old NEQ n.
    rename now into now_past, LT into LTPAST, k into k_past, o into o_past.

    iApply stsim_FUpd. instantiate (1 := ⊤). iModIntro.
    iInv "LOCK_INV" as "I" "K".
    do 7 iDestruct "I" as "[% I]". iDestruct "I" as "[TKS [MEM [ST CASES]]]".
    destruct (Nat.eq_dec mytk now); subst.
    { iClear "CIH".
      iApply lock_myturn1.
      iSplitR. ss. iSplitL "MYTK". iFrame. iSplitL "MYN". iFrame. iSplitL "TKS". iFrame.
      iSplitL "MEM". iFrame. iSplitL "ST". iFrame. iSplitL "CASES". iFrame. iFrame.
    }

    rename n into NEQ.
    iApply lock_yourturn_yieldR. eapply NEQ.
    iSplitL "MYTK TKS MEM ST CASES K".
    iSplitL "MYTK". iFrame. iSplitL "TKS". iFrame. iSplitL "MEM". iFrame.
    iSplitL "ST". iFrame. iSplitL "CASES". iFrame. iFrame.
    iIntros "[MYTK _]". rred.
    clear mem own l tks now next myt NEQ.
    iInv "LOCK_INV" as "I" "K".
    do 7 iDestruct "I" as "[% I]". iDestruct "I" as "[TKS [MEM [ST CASES]]]".
    destruct (Nat.eq_dec mytk now); subst.
    { iClear "CIH".
      iPoseProof (mytk_find_some with "[MYTK TKS]") as "%FIND". iFrame.
      iDestruct "CASES" as "[[%CT I] | [%CF [I | [I | I]]]]".
      { iPoseProof (locked_contra with "I") as "%F". eauto. inv F. }
      { iPoseProof (unlocking_contra with "I") as "%F". eauto. inv F. }
      { iPoseProof (unlocked0_contra with "I") as "%F". eauto. inv F. }
      iPoseProof (unlocked1_mono with "I") as "[%TKQ #[% [% [MYTN _]]]]".
      iMod ("K" with "[TKS MEM ST I]") as "_".
      { do 7 iExists _. iSplitL "TKS". iFrame. iSplitL "MEM". iFrame. iSplitL "ST". iFrame.
        iRight. iSplit. auto. iFrame.
      }
      iApply lock_myturn0. 2: iFrame; auto. lia.
    }

    rename n into NEQ. unfold Mod.wrap_fun, SCMem.load_fun. rred.
    iDestruct "MEM" as "[MEM0 [MEM1 [MEM2 MEM3]]]". iDestruct "ST" as "[ST0 ST1]".
    iApply stsim_getR. iSplit. eauto. rred.
    iPoseProof (memory_ra_load with "MEM0 MEM1") as "%LOAD". des. rewrite LOAD. rred.
    iApply stsim_tauR. rred.
    rewrite close_itree_call. rred.
    iApply lock_yourturn_yieldR. eapply NEQ.
    iSplitL "MYTK TKS MEM0 MEM1 MEM2 MEM3 ST0 ST1 CASES K".
    iSplitL "MYTK". iFrame. iSplitL "TKS". iFrame. iSplitL "MEM0 MEM1 MEM2 MEM3". iFrame.
    iSplitL "ST0 ST1". iFrame. iSplitL "CASES". iFrame. iFrame.
    iIntros "[MYTK RIGHT]". rred.
    rename now into now_old. clear mem own l tks next myt LOAD LOAD0.

    iInv "LOCK_INV" as "I" "K".
    do 7 iDestruct "I" as "[% I]". iDestruct "I" as "[TKS [MEM [ST CASES]]]".
    destruct (Nat.eq_dec mytk now); subst.
    { iClear "CIH". iApply lock_myturn2. auto.
      iSplitR. ss. iSplitL "MYTK". iFrame. iSplitL "MYN". iFrame. iSplitL "TKS". iFrame.
      iSplitL "MEM". iFrame. iSplitL "ST". iFrame. iSplitL "CASES". iFrame. iFrame.
    }

    iPoseProof (mytk_find_some with "[MYTK TKS]") as "%FIND". iFrame.
    rename n into NEQ2. iPoseProof (yourturn_range with "CASES") as "%LT". eapply FIND. auto.
    clear NEQ2. iDestruct "CASES" as "[[%CT I] | [%CF [I | [I | I]]]]".
    { subst own. iApply lock_yourturn_coind. auto. iSplit.
      { iModIntro. iIntros (a) "[H1 H2]". iApply "CIH". iFrame. iApply "LOCK_INV". }
      iSplitL "MYN". iFrame. iSplitL "MYTK". iFrame. iSplitL "TKS". iFrame.
      iSplitL "MEM". iFrame. iSplitL "ST". iFrame. iSplitL "I". iFrame. iFrame.
    }

    { iPoseProof (ticket_lock_inv_mem_mono with "MEM") as "#MONOTK2".
      iDestruct "I" as "[I0 [%I1 [I2 [I3 I4]]]]".
      do 2 iDestruct "I4" as "[% I4]". iDestruct "I4" as "[I4 [I5 [I6 I7]]]".
      iPoseProof (black_white_compare with "MONOW I4") as "%LE".
      inv LE.
      { remember (mytk - now) as ind. specialize (IH ind).
        iApply IH.
        { subst ind. lia. }
        { auto. }
        { eapply LT. }
        { eapply Heqind. }
        iSplit.
        { iClear "MYN MYTK RIGHT TKS MEM ST I0 I2 I3 I4 I5 I6 I7 K".
          iModIntro. iSplit. iApply "CIH". auto.
        }
        iSplitL "MYN". iFrame. iSplitL "MYTK". iFrame. iSplitL "TKS". iFrame.
        iSplitL "ST". iFrame. iSplitR "K MEM". 2: iFrame.
        iRight. iSplit. auto. iLeft. iFrame. iSplit. auto. iExists _, _. iFrame.
      }
      { inv ORD. hexploit H0. lia. i. clear H H0. subst k.
        iClear "MONOTK2".
        iPoseProof (ObligationRA.duty_correl_thread with "I7") as "#COR".
        { ss. left; eauto. }
        iPoseProof (ObligationRA.correl_thread_correlate with "COR RIGHT") as ">[DROP | FF]".
        2:{ iPoseProof (ObligationRA.pending_not_shot with "I6 FF") as "%FF". inv FF. }
        iPoseProof (ObligationRA.black_white_decr with "BLK DROP") as ">[%o_now [#OBLK2 %DROP]]".
        iClear "BLK".
        specialize (IHo o_now).
        iApply IHo.
        { rewrite Hessenberg.add_S_r in DROP. rewrite Hessenberg.add_O_r in DROP.
          eapply Ord.lt_le_lt. 2: eapply DROP. apply Ord.S_lt.
        }
        { auto. }
        iSplit.
        { iClear "MYN MYTK TKS MEM ST I0 I2 I3 I4 I5 I6 I7 K".
          iModIntro. iSplit. ss. iSplit. iApply "CIH". iSplit; auto.
        }
        iSplitL "MYN". iFrame. iSplitL "MYTK". iFrame. iSplitL "TKS". iFrame.
        iSplitL "MEM". iFrame. iSplitL "ST". iFrame. iSplitR "K". 2: iFrame.
        iFrame. iSplit. auto. iExists _, _. iFrame.
      }
    }
    { iPoseProof (unlocked0_contra with "I") as "%FF". eauto. inv FF. }

    { iPoseProof (ticket_lock_inv_mem_mono with "MEM") as "#MONOTK2".
      do 2 iDestruct "I" as "[% I]". iDestruct "I" as "[I0 [I1 [%I2 [I3 [I4 I5]]]]]".
      do 3 iDestruct "I5" as "[% I5]". iDestruct "I5" as "[I5 [I6 [I7 [I8 [I9 I10]]]]]".
      iPoseProof (black_white_compare with "MONOW I5") as "%LE".
      inv LE.
      { remember (mytk - now) as ind. specialize (IH ind).
        iApply IH.
        { subst ind. lia. }
        { auto. }
        { eapply LT. }
        { eapply Heqind. }
        iSplit.
        { iClear "MYN MYTK RIGHT TKS MEM ST I0 I1 I3 I4 I5 I6 I7 I8 I9 I10 K".
          iModIntro. iSplit. iApply "CIH". auto.
        }
        iSplitL "MYN". iFrame. iSplitL "MYTK". iFrame. iSplitL "TKS". iFrame.
        iSplitL "ST". iFrame. iSplitR "K MEM". 2: iFrame.
        iRight. iSplit. auto. iRight. iRight. iFrame.
        iExists yourt, waits. iSplit. auto. iSplit. auto. iFrame.
        iExists k, o, u. iFrame.
      }
      { exfalso. inv ORD. lia. }
    }
  Qed.

  Lemma lock_yourturn_ind1
        (g0 g1 : ∀ R_src R_tgt : Type,
            (R_src → R_tgt → iProp)
            → bool
            → bool
            → itree (threadE _ (Mod.state AbsLock.mod)) R_src
            → itree (threadE _ (OMod.closed_state TicketLock.omod (SCMem.mod TicketLock.gvs))) R_tgt → iProp)
        (tid : nat)
        (mytk : TicketLock.tk)
  (now : nat)
  (LT : now < mytk)
  (IH : ∀ y : nat,
         y < mytk - now
         → ∀ now_old : nat,
             mytk ≠ now_old
             → ∀ (mem : SCMem.t) (own : bool) (l : list nat) (tks : NatMap.t nat)
                 (now next myt : nat),
                 now < mytk
                 → y = mytk - now
                   → (□ ((∀ a : TicketLock.tk,
                             (□ inv N (ticket_lock_inv monok tk_mono)) ∗
                            (OwnM (Auth.white (NatMapRAFOS.singleton tid a: NatMapRAFOS.t nat)) **
                             maps_to tid (Auth.white (Excl.just 2: Excl.t nat))) -*
                            g1 ()%type ()%type
                              (λ r_src r_tgt : (),
                                 (own_thread tid ** ObligationRA.duty inlp tid []) **
                                 ⌜r_src = r_tgt⌝) false false
                              (src_code_coind tid)
                              (tgt_code_coind a)
                         )
                         ∧ (inv N (ticket_lock_inv monok tk_mono))
                         ∧ monoWhite tk_mono Nat.le_preorder now) **
                      (maps_to tid (Auth.white (Excl.just 2: Excl.t nat)) **
                       (OwnM (Auth.white (NatMapRAFOS.singleton tid mytk: NatMapRAFOS.t nat)) **
                        (ticket_lock_inv_tks tks **
                         (ticket_lock_inv_state mem own tks **
                          ((⌜own = true⌝ ** ticket_lock_inv_locked monok l tks now next myt)
                           ∨ (⌜own = false⌝ **
                              ticket_lock_inv_unlocking monok l tks now next myt
                              ∨ ticket_lock_inv_unlocked0 monok l tks now next myt
                                ∨ ticket_lock_inv_unlocked1 monok l tks now next myt) **
                           ((ticket_lock_inv monok tk_mono -*
                               FUpd
                               (fairI
                                  (ident_tgt:=OMod.closed_ident TicketLock.omod
                                                (SCMem.mod TicketLock.gvs)))
                               (⊤∖↑N) ⊤ emp) **
                            ticket_lock_inv_mem tk_mono mem now next myt)))))))
                     ⊢ stsim tid (⊤∖↑N) g0 g1
                         (λ r_src r_tgt : (),
                            (own_thread tid ** ObligationRA.duty inlp tid []) ** ⌜r_src = r_tgt⌝)
                         false true
                         (src_code_ind tid)
                         (tgt_code_ind mytk now_old)
  )
  (now_old : nat)
  (NEQ : mytk ≠ now_old)
  (mem : SCMem.t)
  (l : list nat)
  (tks : NatMap.t nat)
  (next myt : nat)
    :
    (inv N (ticket_lock_inv monok tk_mono)) ∗
  (□ ((∀ a : TicketLock.tk,
          (□ inv N (ticket_lock_inv monok tk_mono)) ∗
        (OwnM (Auth.white (NatMapRAFOS.singleton tid a: NatMapRAFOS.t nat)) ** maps_to tid (Auth.white (Excl.just 2: Excl.t nat))) -*
        g1 ()%type ()%type
          (λ r_src r_tgt : (),
             (own_thread tid ** ObligationRA.duty inlp tid []) ** ⌜r_src = r_tgt⌝) false false
          (src_code_coind tid)
          (tgt_code_coind a))
          ∧
  (monoWhite tk_mono Nat.le_preorder now)
     ) **
   (maps_to tid (Auth.white (Excl.just 2: Excl.t nat)) **
    (OwnM (Auth.white (NatMapRAFOS.singleton tid mytk: NatMapRAFOS.t nat)) **
     (ticket_lock_inv_tks tks **
      (ticket_lock_inv_mem tk_mono mem now next myt **
       (ticket_lock_inv_state mem false tks **
        (ticket_lock_inv_unlocked1 monok l tks now next myt **
         (ticket_lock_inv monok tk_mono -*
            FUpd
            (fairI (ident_tgt:=OMod.closed_ident TicketLock.omod (SCMem.mod TicketLock.gvs)))
            (⊤∖↑N) ⊤ emp)))))))
  )
  ⊢ (stsim tid (⊤∖↑N) g0 g1
      (λ r_src r_tgt : (), (own_thread tid ** ObligationRA.duty inlp tid []) ** ⌜r_src = r_tgt⌝)
      false true
      (trigger Yield;;;
       ` x : () + () <-
       (` x_0 : bool * NatMap.t () <- trigger (Get id);;
        (let (own0, _) := x_0 in if Bool.eqb own0 true then Ret (inl ()) else Ret (inr ())));;
       match x with
       | inl l0 =>
           tau;; ITree.iter
                   (λ _ : (),
                      trigger Yield;;;
                      ` x_0 : bool * NatMap.t () <- trigger (Get id);;
                      (let (own0, _) := x_0 in
                       if Bool.eqb own0 true then Ret (inl ()) else Ret (inr ()))) l0
       | inr r0 => Ret r0
       end;;;
       ` x_0 : bool * NatMap.t () <- trigger (Get id);;
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
       map_event (OMod.emb_callee TicketLock.omod (SCMem.mod TicketLock.gvs))
         (Mod.wrap_fun SCMem.compare_fun (Any.upcast (SCMem.val_nat now_old, SCMem.val_nat mytk)));;
       ` x : bool <- (tau;; unwrap (Any.downcast r));;
       OMod.close_itree TicketLock.omod (SCMem.mod TicketLock.gvs)
         (if x then Ret () else tau;; TicketLock.lock_loop (SCMem.val_nat mytk));;;
       OMod.close_itree TicketLock.omod (SCMem.mod TicketLock.gvs) (trigger Yield))).
  Proof.
    iIntros "[#LOCK_INV [#[CIH MONOTK] [MYN [MYTK [TKS [MEM [ST [I K]]]]]]]]".
    iPoseProof (mytk_find_some with "[MYTK TKS]") as "%FIND". iFrame.
    iPoseProof (unlocked1_mono with "I") as "[%TKQ #[% [% [MONOW OBLB]]]]".
    clear FIND TKQ.
    iStopProof. move o before IH. revert_until o. pattern o. revert o.
    apply (well_founded_induction Ord.lt_well_founded).
    intros o IHo. intros.
    iIntros "[#[LOCK_INV [CIH [MONOTK [MONOW BLK]]]] [MYN [MYTK [TKS [MEM [ST [I K]]]]]]]".

    unfold Mod.wrap_fun, SCMem.compare_fun. rred.
    iDestruct "MEM" as "[MEM0 [MEM1 [MEM2 MEM3]]]". iDestruct "ST" as "[ST0 ST1]".
    iApply stsim_getR. iSplit. eauto. rred.
    iApply stsim_tauR. rred.
    destruct (Nat.eq_dec now_old mytk).
    { exfalso. clarify. }
    rred. iApply stsim_tauR.
    rewrite TicketLock.lock_loop_red. rred. rewrite close_itree_call. rred.
    iAssert (ticket_lock_inv_mem tk_mono mem now next myt)%I with "[MEM0 MEM1 MEM2 MEM3]" as "MEM". iFrame.
    iAssert (ticket_lock_inv_state mem false tks)%I with "[ST0 ST1]" as "ST". iFrame.
    iMod ("K" with "[TKS MEM ST I]") as "_".
    { do 7 iExists _. iSplitL "TKS". iFrame. iSplitL "MEM". iFrame. iSplitL "ST". iFrame.
      iRight. iSplit. auto. iRight. iRight. iFrame.
    }
    clear mem l tks next myt now_old NEQ n.
    rename now into now_past, LT into LTPAST, k into k_past, o into o_past.

    iInv "LOCK_INV" as "I" "K".
    do 7 iDestruct "I" as "[% I]". iDestruct "I" as "[TKS [MEM [ST CASES]]]".
    destruct (Nat.eq_dec mytk now); subst.
    { iClear "CIH".
      iApply lock_myturn1.
      iSplitR. ss. iSplitL "MYTK". iFrame. iSplitL "MYN". iFrame. iSplitL "TKS". iFrame.
      iSplitL "MEM". iFrame. iSplitL "ST". iFrame. iSplitL "CASES". iFrame. iFrame.
    }

    rename n into NEQ.
    iApply lock_yourturn_yieldR. eapply NEQ.
    iSplitL "MYTK TKS MEM ST CASES K".
    iSplitL "MYTK". iFrame. iSplitL "TKS". iFrame. iSplitL "MEM". iFrame.
    iSplitL "ST". iFrame. iSplitL "CASES". iFrame. iFrame.
    iIntros "[MYTK _]". rred.
    clear mem own l tks now next myt NEQ.
    iInv "LOCK_INV" as "I" "K".
    do 7 iDestruct "I" as "[% I]". iDestruct "I" as "[TKS [MEM [ST CASES]]]".
    destruct (Nat.eq_dec mytk now); subst.
    { iClear "CIH".
      iPoseProof (mytk_find_some with "[MYTK TKS]") as "%FIND". iFrame.
      iDestruct "CASES" as "[[%CT I] | [%CF [I | [I | I]]]]".
      { iPoseProof (locked_contra with "I") as "%F". eauto. inv F. }
      { iPoseProof (unlocking_contra with "I") as "%F". eauto. inv F. }
      { iPoseProof (unlocked0_contra with "I") as "%F". eauto. inv F. }
      iPoseProof (unlocked1_mono with "I") as "[%TKQ #[% [% [MYTN _]]]]".
      iMod ("K" with "[TKS MEM ST I]") as "_".
      { do 7 iExists _. iSplitL "TKS". iFrame. iSplitL "MEM". iFrame. iSplitL "ST". iFrame.
        iRight. iSplit. auto. iFrame.
      }
      iApply lock_myturn0. 2: iFrame; auto. lia.
    }

    rename n into NEQ. unfold Mod.wrap_fun, SCMem.load_fun. rred.
    iDestruct "MEM" as "[MEM0 [MEM1 [MEM2 MEM3]]]". iDestruct "ST" as "[ST0 ST1]".
    iApply stsim_getR. iSplit. eauto. rred.
    iPoseProof (memory_ra_load with "MEM0 MEM1") as "%LOAD". des. rewrite LOAD. rred.
    iApply stsim_tauR. rred.
    rewrite close_itree_call. rred.
    iApply lock_yourturn_yieldR. eapply NEQ.
    iSplitL "MYTK TKS MEM0 MEM1 MEM2 MEM3 ST0 ST1 CASES K".
    iSplitL "MYTK". iFrame. iSplitL "TKS". iFrame. iSplitL "MEM0 MEM1 MEM2 MEM3". iFrame.
    iSplitL "ST0 ST1". iFrame. iSplitL "CASES". iFrame. iFrame.
    iIntros "[MYTK RIGHT]". rred.
    rename now into now_old. clear mem own l tks next myt LOAD LOAD0.

    iInv "LOCK_INV" as "I" "K".
    do 7 iDestruct "I" as "[% I]". iDestruct "I" as "[TKS [MEM [ST CASES]]]".
    destruct (Nat.eq_dec mytk now); subst.
    { iClear "CIH". iApply lock_myturn2. auto.
      iSplitR. ss. iSplitL "MYTK". iFrame. iSplitL "MYN". iFrame. iSplitL "TKS". iFrame.
      iSplitL "MEM". iFrame. iSplitL "ST". iFrame. iSplitL "CASES". iFrame.
      iFrame.
    }

    iPoseProof (mytk_find_some with "[MYTK TKS]") as "%FIND". iFrame.
    rename n into NEQ2. iPoseProof (yourturn_range with "CASES") as "%LT". eapply FIND. auto.
    clear NEQ2. iDestruct "CASES" as "[[%CT I] | [%CF [I | [I | I]]]]".
    { subst own. iApply lock_yourturn_coind. auto. iSplit.
      { iModIntro. iIntros (a) "[H1 H2]". iApply "CIH". iFrame. iApply "LOCK_INV". }
      iSplitL "MYN". iFrame. iSplitL "MYTK". iFrame. iSplitL "TKS". iFrame.
      iSplitL "MEM". iFrame. iSplitL "ST". iFrame. iSplitL "I". iFrame. iFrame.
    }

    { iPoseProof (ticket_lock_inv_mem_mono with "MEM") as "#MONOTK2".
      iAssert (⌜now_past <= now⌝)%I with "[MEM]" as "%PROG".
      { iDestruct "MEM" as "[MEM0 [MEM1 [MEM2 [MEM3 MEM4]]]]".
        iPoseProof (black_white_compare with "MONOTK MEM4") as "%". auto.
      }
      iApply lock_yourturn_ind0. apply LT.
      { clear IHo. move LT before IH. move PROG before LT. clear_upto PROG.
        intros y H. eapply IH. lia.
      }
      auto.
      iSplit. ss.
      iSplit.
      { iClear "MYN MYTK RIGHT TKS MEM ST I K". iModIntro. iSplit. iApply "CIH". auto. }
      iSplitL "MYN". iFrame. iSplitL "MYTK". iFrame. iSplitL "TKS". iFrame. iSplitL "MEM". iFrame.
      iSplitL "ST". subst. iFrame. iSplitR "K". 2: iFrame.
      iFrame.
    }

    { iPoseProof (unlocked0_contra with "I") as "%FF". eauto. inv FF. }

    { iPoseProof (ticket_lock_inv_mem_mono with "MEM") as "#MONOTK2".
      do 2 iDestruct "I" as "[% I]". iDestruct "I" as "[I0 [%I1 [%I2 [I3 [I4 I5]]]]]".
      do 3 iDestruct "I5" as "[% I5]". iDestruct "I5" as "[I5 [I6 [I7 [I8 [I9 I10]]]]]".
      iPoseProof (black_white_compare with "MONOW I5") as "%LE".
      inv LE.
      { remember (mytk - now) as ind. specialize (IH ind).
        iApply IH.
        { subst ind. lia. }
        { auto. }
        { eapply LT. }
        { eapply Heqind. }
        iSplit.
        { iClear "MYN MYTK RIGHT TKS MEM ST I0 I3 I4 I5 I6 I7 I8 I9 I10 K".
          iModIntro. iSplit. iApply "CIH". auto.
        }
        iSplitL "MYN". iFrame. iSplitL "MYTK". iFrame. iSplitL "TKS". iFrame.
        iSplitL "ST". iFrame. iSplitR "K MEM". 2: iFrame.
        iRight. iSplit. auto. iRight. iRight. iFrame. iExists yourt, waits.
        iSplit. auto. iSplit. auto. iFrame. iExists k, o, u. iFrame.
      }
      { inv ORD. hexploit H0. lia. i. clear H H0. subst k.
        iClear "MONOTK2".
        iPoseProof (ObligationRA.duty_correl_thread with "I8") as "#COR".
        { ss. left; eauto. }
        iPoseProof (ObligationRA.correl_thread_correlate with "COR RIGHT") as ">[DROP | FF]".
        2:{ iPoseProof (ObligationRA.pending_not_shot with "I7 FF") as "%FF". inv FF. }
        iPoseProof (ObligationRA.black_white_decr with "BLK DROP") as ">[%o_now [#OBLK2 %DROP]]".
        iClear "BLK".
        specialize (IHo o_now). iApply IHo.
        { rewrite Hessenberg.add_S_r in DROP. rewrite Hessenberg.add_O_r in DROP.
          eapply Ord.lt_le_lt. 2: eapply DROP. apply Ord.S_lt.
        }
        { auto. }
        iSplit.
        { iClear "MYN MYTK TKS MEM ST I0 I3 I4 I5 I6 I7 I8 I9 I10 K".
          iModIntro. iSplitR. ss. iSplit. iApply "CIH". auto.
        }
        iSplitL "MYN". iFrame. iSplitL "MYTK". iFrame. iSplitL "TKS". iFrame.
        iSplitL "MEM". iFrame. iSplitL "ST". iFrame. iSplitR "K". 2: iFrame.
        iFrame. iExists yourt, waits.
        iSplit. auto. iSplit. auto. iFrame. iExists _, _, u. iFrame.
      }
    }
  Qed.

  Lemma correct_lock tid:
    inv N (ticket_lock_inv monok tk_mono) ∗
    ((own_thread tid)
       ∗ (ObligationRA.duty inlp tid [])
    )
      ⊢
      (stsim tid ⊤ ibot7 ibot7
             (fun r_src r_tgt => own_thread tid ** ObligationRA.duty inlp tid [] ** ⌜r_src = r_tgt⌝)
             false false
             (AbsLock.lock_fun tt)
             (OMod.close_itree TicketLock.omod (SCMem.mod TicketLock.gvs)
                               (TicketLock.lock_fun tt))).
  Proof.
    iIntros "[#LOCK_INV [MYTH DUTY]]".
    iApply lock_enqueue. iSplitR. ss. iSplitL. iFrame.
    iIntros "% [MYTK MYN]".
    rewrite TicketLock.lock_loop_red. rred. rewrite close_itree_call. rred.
    iStopProof. revert mytk. eapply stsim_coind. ss. msubtac.
    iIntros "% %mytk". iIntros "#[_ CIH] [#LOCK_INV [MYTK MYN]]".

    iInv "LOCK_INV" as "I" "K".
    do 7 iDestruct "I" as "[% I]". iDestruct "I" as "[TKS [MEM [ST CASES]]]".
    destruct (Nat.eq_dec mytk now); subst.
    { iClear "CIH".
      rewrite unfold_iter_eq. lred. iApply lock_myturn1.
      iSplitR. ss. iSplitL "MYTK". iFrame. iSplitL "MYN". iFrame. iSplitL "TKS". iFrame.
      iSplitL "MEM". iFrame. iSplitL "ST". iFrame. iSplitL "CASES". iFrame. iFrame.
    }

    rename n into NEQ. rewrite unfold_iter_eq. lred.
    iApply lock_yourturn_yieldR. eapply NEQ.
    iSplitL "MYTK TKS MEM ST CASES K".
    iSplitL "MYTK". iFrame. iSplitL "TKS". iFrame. iSplitL "MEM". iFrame.
    iSplitL "ST". iFrame. iSplitL "CASES". iFrame. iFrame.
    iIntros "[MYTK _]". rred.
    clear mem own l tks now next myt NEQ.
    iInv "LOCK_INV" as "I" "K".
    do 7 iDestruct "I" as "[% I]". iDestruct "I" as "[TKS [MEM [ST CASES]]]".
    destruct (Nat.eq_dec mytk now); subst.
    { iClear "CIH".
      iPoseProof (mytk_find_some with "[MYTK TKS]") as "%FIND". iFrame.
      iDestruct "CASES" as "[[%CT I] | [%CF [I | [I | I]]]]".
      { iPoseProof (locked_contra with "I") as "%F". eauto. inv F. }
      { iPoseProof (unlocking_contra with "I") as "%F". eauto. inv F. }
      { iPoseProof (unlocked0_contra with "I") as "%F". eauto. inv F. }
      iPoseProof (unlocked1_mono with "I") as "[%TKQ #[% [% [MYTN _]]]]".
      iMod ("K" with "[TKS MEM ST I]") as "_".
      { do 7 iExists _. iSplitL "TKS". iFrame. iSplitL "MEM". iFrame. iSplitL "ST". iFrame.
        iRight. iSplit. auto. iFrame.
      }
      iApply lock_myturn0. 2: iFrame; auto. lia.
    }

    rename n into NEQ.
    unfold Mod.wrap_fun, SCMem.load_fun. rred.
    iDestruct "MEM" as "[MEM0 [MEM1 [MEM2 MEM3]]]". iDestruct "ST" as "[ST0 ST1]".
    iApply stsim_getR. iSplit. eauto. rred.
    iPoseProof (memory_ra_load with "MEM0 MEM1") as "%LOAD". des. rewrite LOAD. rred.
    iApply stsim_tauR. rred.
    rewrite close_itree_call. rred.
    iApply lock_yourturn_yieldR. eapply NEQ.
    iSplitL "MYTK TKS MEM0 MEM1 MEM2 MEM3 ST0 ST1 CASES K".
    iSplitL "MYTK". iFrame. iSplitL "TKS". iFrame. iSplitL "MEM0 MEM1 MEM2 MEM3". iFrame.
    iSplitL "ST0 ST1". iFrame. iSplitL "CASES". iFrame. iFrame.
    iIntros "[MYTK _]". rred.
    rename now into now_old. clear mem own l tks next myt LOAD LOAD0.

    iInv "LOCK_INV" as "I" "K".
    do 7 iDestruct "I" as "[% I]". iDestruct "I" as "[TKS [MEM [ST CASES]]]".
    destruct (Nat.eq_dec mytk now); subst.
    { iClear "CIH". iApply lock_myturn2. auto.
      iSplitR. ss. iSplitL "MYTK". iFrame. iSplitL "MYN". iFrame. iSplitL "TKS". iFrame.
      iSplitL "MEM". iFrame. iSplitL "ST". iFrame. iSplitL "CASES". iFrame. iFrame.
    }

    rename n into NEQ2.
    iPoseProof (mytk_find_some with "[MYTK TKS]") as "%FIND". iFrame.
    iDestruct "MEM" as "[MEM0 [MEM1 [MEM2 [MEM3 MEM4]]]]".
    iPoseProof (black_white with "MEM4") as "#MONOTK".
    iAssert (ticket_lock_inv_mem tk_mono mem now next myt)%I with "[MEM0 MEM1 MEM2 MEM3 MEM4]" as "MEM".
    iFrame.
    iPoseProof (yourturn_range with "CASES") as "%LT". eapply FIND. auto.
    clear FIND NEQ2.
    remember (mytk - now) as ind.
    iStopProof. move ind before mytk. revert_until ind. pattern ind. revert ind.
    apply (well_founded_induction Nat.lt_wf_0).
    intros ind IH. intros.
    iIntros "[#[CIH [LOCK_INV MONOTK]] [MYN [MYTK [TKS [ST [CASES [K MEM]]]]]]]".

    iDestruct "CASES" as "[[%CT I] | [%CF [I | [I | I]]]]".
    { subst own. iApply lock_yourturn_coind. auto. iSplit.
      - iModIntro. iIntros (a). iSpecialize ("CIH" $! a). iIntros. iApply "CIH". iFrame. ss.
      - iSplitL "MYN". iFrame. iSplitL "MYTK". iFrame. iSplitL "TKS". iFrame.
        iSplitL "MEM". iFrame. iSplitL "ST". iFrame. iSplitL "I". iFrame. iFrame.
    }
    { subst. iApply lock_yourturn_ind0. apply LT. apply IH. auto.
      iSplit. iApply "LOCK_INV".
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
      iSplit. iApply "LOCK_INV".
      iSplit.
      { iClear "MYN MYTK TKS MEM ST I K". iModIntro. iSplit. iApply "CIH". auto. }
      iSplitL "MYN". iFrame. iSplitL "MYTK". iFrame. iSplitL "TKS". iFrame.
      iSplitL "MEM". iFrame. iSplitL "ST". iFrame. iSplitR "K". 2: iFrame.
      iFrame.
    }

  Qed.

  Lemma correct_unlock tid:
    inv N (ticket_lock_inv monok tk_mono) ∗
    ((own_thread tid)
       ∗ (ObligationRA.duty inlp tid [])
    )
      ⊢
      (stsim tid ⊤ ibot7 ibot7
             (fun r_src r_tgt => own_thread tid ** ObligationRA.duty inlp tid [] ** ⌜r_src = r_tgt⌝)
             false false
             (AbsLock.unlock_fun tt)
             (OMod.close_itree TicketLock.omod (SCMem.mod TicketLock.gvs)
                               (TicketLock.unlock_fun tt))).
  Proof.
    iIntros "[#LOCK_INV [MYTH DUTY]]".
    unfold AbsLock.unlock_fun, TicketLock.unlock_fun. rred.
    rewrite close_itree_call. rred.
    iApply (stsim_sync with "[DUTY]"). msubtac. iFrame. iIntros "DUTY _".

    iInv "LOCK_INV" as "I" "K".
    do 7 iDestruct "I" as "[% I]". iDestruct "I" as "[TKS [MEM [ST CASES]]]".
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
    iApply (stsim_modifyL with "ST1"). iIntros "ST1".

    unfold Mod.wrap_fun, SCMem.load_fun. rred.
    iDestruct "MEM" as "[MEM0 [MEM1 [MEM2 [MEM3 MEM4]]]]".
    iApply stsim_getR. iSplit. eauto. rred.
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
    (⌜false = true⌝ ** ticket_lock_inv_locked monok l tks now next tid)
    ∨ (⌜false = false⌝ **
       ticket_lock_inv_unlocking monok l tks now next tid
       ∨ ticket_lock_inv_unlocked0 monok l tks now next tid
       ∨ ticket_lock_inv_unlocked1 monok l tks now next tid))%I as temp.
      iFrame. subst temp.
      iRight. iSplit. auto. iLeft. iFrame.
      iExists _, _. iFrame.
    }
    iModIntro. clear_upto tid.

    iInv "LOCK_INV" as "I" "K".
    do 7 iDestruct "I" as "[% I]". iDestruct "I" as "[TKS [MEM [ST CASES]]]".
    iDestruct "CASES" as "[[%CT I] | [%CF [I | [I | I]]]]"; cycle 2.
    { iDestruct "I" as "[I _]". iPoseProof (white_white_excl with "HOLD I") as "%FF". inv FF. }
    { do 2 iDestruct "I" as "[% I]". iDestruct "I" as "[I _]".
      iPoseProof (white_white_excl with "HOLD I") as "%FF". inv FF. }
    { iDestruct "I" as "[I _]". iPoseProof (white_white_excl with "HOLD I") as "%FF". inv FF. }

    unfold Mod.wrap_fun, SCMem.store_fun. rred.
    iDestruct "ST" as "[ST0 ST1]". iDestruct "MEM" as "[MEM0 [MEM1 [MEM2 [MEM3 MEM4]]]]".
    iApply stsim_getR. iSplit. auto. rred.
    iPoseProof (memory_ra_store with "MEM0 MEM1") as "[% [%STORE >[MEM0 MEM1]]]".
    rewrite STORE. rred.
    iApply (stsim_modifyR with "ST0"). iIntros "ST0". rred.
    iApply stsim_tauR. rred.

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
      iAssert (ticket_lock_inv_mem tk_mono m1 now' next tid)%I with "[MEM0 MEM1 MEM2 MEM3 MEM4]" as "MEM".
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
    iAssert (ticket_lock_inv_mem tk_mono m1 now' next tid)%I with "[MEM0 MEM1 MEM2 MEM3 MEM4]" as "MEM".
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

End SIM.
