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

End Tkst.

Section TKQ.

  Inductive tkqueue
            (l: list thread_id) (tks: NatMap.t TicketLock.tk) (inc exc: TicketLock.tk)
    : Prop :=
  | tkqueue_empty
      (EMP1: l = [])
      (EMP2: tks = @NatMap.empty _)
      (EQ: inc = exc)
    :
    tkqueue l tks inc exc
  | tkqueue_hd
      hd tl
      (QUEUE: l = hd :: tl)
      (FIND: NatMap.find hd tks = Some inc)
      (TL: tkqueue tl (NatMap.remove hd tks) (S inc) exc)
    :
    tkqueue l tks inc exc
  .

End TKQ.

Section SIM.

  Let mypreord := prod_le_PreOrder nat_le_po (Tkst.le_PreOrder nat).

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
  Context `{AUTHRA2: @GRA.inG (Auth.t (Excl.t (nat * unit))) Σ}.
  (* Context `{REGIONRA: @GRA.inG (Region.t (thread_id * nat)) Σ}. *)
  (* Context `{CONSENTRA: @GRA.inG (@FiniteMap.t (Consent.t nat)) Σ}. *)

  Variable monok: nat.

  Definition ticket_lock_inv_unlocking
             (l: list thread_id) (tks: NatMap.t nat) (now next: nat) : iProp :=
    ∃ (myt: thread_id),
      (OwnM (Auth.black (Excl.just (myt, tt): Excl.t (thread_id * unit)%type)))
        ∗
        (⌜tkqueue l tks (S now) next⌝)
        (* (⌜list_map_natmap l tks = Some (list_nats (S now) next)⌝) *)
        ∗
        (natmap_prop_sum tks (fun th tk => FairRA.white th (Ord.from_nat (tk - (S now)))))
        ∗
        (list_prop_sum (fun th => ObligationRA.duty (inl th) []) l)
        ∗
        (∃ (k: nat) (o: Ord.t),
            (monoBlack monok mypreord (now, Tkst.d k))
              ∗ (ObligationRA.black k o)
              ∗ (ObligationRA.pending k 1)
              ∗ (ObligationRA.duty (inl myt) [(k, Ord.S Ord.O)])
        )
  .

  Definition ticket_lock_inv_unlocked
             (l: list thread_id) (tks: NatMap.t nat) (now next: nat) : iProp :=
    (OwnM (Auth.white (Excl.just now: Excl.t nat)))
      ∗
      (∃ myt,
          (OwnM (Auth.black (Excl.just (myt, tt): Excl.t (thread_id * unit)%type)))
            ∗
            (OwnM (Auth.white (Excl.just (myt, tt): Excl.t (thread_id * unit)%type)))
      )
      ∗
      (match l with
       | [] =>
           (⌜(tks = @NatMap.empty _) /\ (now = next)⌝)
             ∗
             (∃ (k: nat),
                 (monoBlack monok mypreord (now, Tkst.a k))
             )
       | yourt :: waits =>
           (⌜tkqueue l tks now next⌝)
           (* (⌜list_map_natmap l tks = Some (list_nats now next)⌝) *)
             ∗
             (natmap_prop_sum tks (fun th tk => FairRA.white th (Ord.from_nat (tk - (now)))))
             ∗
             (list_prop_sum (fun th => ObligationRA.duty (inl th) []) waits)
             ∗
             (∃ (k: nat) (o: Ord.t),
                 (monoBlack monok mypreord (now, Tkst.b k))
                   ∗ (ObligationRA.black k o)
                   ∗ (ObligationRA.pending k 1)
                   ∗ (ObligationRA.duty (inl yourt) [(k, Ord.S Ord.O)])
             )
       end)
  .

  Definition ticket_lock_inv_locked
             (l: list thread_id) (tks: NatMap.t nat) (now next: nat) : iProp :=
    (OwnM (Auth.white (Excl.just now: Excl.t nat)))
      ∗
      (∃ myt,
          (OwnM (Auth.black (Excl.just (myt, tt): Excl.t (thread_id * unit)%type)))
            ∗
            (OwnM (Auth.white (Excl.just (myt, tt): Excl.t (thread_id * unit)%type)))
      )
      ∗
      (⌜tkqueue l tks (S now) next⌝)
      (* (⌜list_map_natmap l tks = Some (list_nats (S now) next)⌝) *)
      ∗
      (natmap_prop_sum tks (fun th tk => FairRA.white th (Ord.from_nat (tk - (S now)))))
      ∗
      (list_prop_sum (fun th => ObligationRA.duty (inl th) []) l)
      ∗
      (∃ (k: nat),
          (monoBlack monok mypreord (now, Tkst.c k))
      )
  .

  Definition ticket_lock_inv : iProp :=
    ∃ (mem: SCMem.t) (own: bool) (l: list thread_id) (tks: NatMap.t nat) (now next: nat),
      ((OwnM (Auth.black (Some tks: NatMapRA.t nat)))
         ∗ (FairRA.whites (fun id => (~ NatMap.In id tks)) Ord.omega)
         ∗ (natmap_prop_sum tks (fun tid tk => (own_thread tid)))
      )
        ∗
        ((memory_black mem)
           ∗ (points_to TicketLock.now_serving (SCMem.val_nat now))
           ∗ (points_to TicketLock.next_ticket (SCMem.val_nat next))
           ∗ (OwnM (Auth.black (Excl.just now: Excl.t nat)))
        )
        ∗
        ((St_tgt (tt, mem)) ∗ (St_src (own, (key_set tks))))
        ∗
        (((⌜own = true⌝)
            ∗ (ticket_lock_inv_locked l tks now next)
         )
         ∨
           ((⌜own = false⌝)
              ∗ ((ticket_lock_inv_unlocking l tks now next)
                 ∨
                   (ticket_lock_inv_unlocked l tks now next))
        ))
  .

  Let I: list iProp := [ticket_lock_inv].








  Definition wait_set_wf (W: NatMap.t unit) (n: nat): iProp :=
    ((natmap_prop_sum W (fun tid _ => own_thread tid))
       **
       (OwnM (Auth.black (Some W: NatMapRA.t unit)))
       **
       (⌜NatMap.cardinal W = n⌝))
  .

  Lemma wait_set_wf_empty
    :
    (OwnM (Auth.black (Some (NatMap.empty unit): NatMapRA.t unit))) ⊢ wait_set_wf (NatMap.empty unit) 0.
  Proof.
    iIntros "OWN". unfold wait_set_wf. iFrame. auto.
  Qed.

  Lemma wait_set_wf_add W tid n
    :
    (wait_set_wf W n)
      -∗
      (own_thread tid)
      -∗
      #=> (wait_set_wf (NatMap.add tid tt W) (S n) ** (OwnM (Auth.white (NatMapRA.singleton tid tt: NatMapRA.t unit)))).
  Proof.
    iIntros "[[SUM BLACK] %] TH".
    iAssert (⌜NatMap.find tid W = None⌝)%I as "%".
    { destruct (NatMap.find tid W) eqn:EQ; auto.
      iExFalso. iPoseProof (natmap_prop_sum_in with "SUM") as "H".
      { eauto. }
      iPoseProof (own_thread_unique with "TH H") as "%". ss.
    }
    iPoseProof (OwnM_Upd with "BLACK") as "> [BLACK WHTIE]".
    { apply Auth.auth_alloc. eapply (@NatMapRA.add_local_update unit W tid tt). auto. }
    iModIntro. iFrame. iSplit; auto.
    { iApply (natmap_prop_sum_add with "SUM"). auto. }
    iPureIntro. subst.
    eapply NatMapP.cardinal_2; eauto.
    { apply NatMapP.F.not_find_in_iff; eauto. }
    { ss. }
  Qed.

  Lemma wait_set_wf_sub W tid n
    :
    (wait_set_wf W n)
      -∗
      (OwnM (Auth.white (NatMapRA.singleton tid tt: NatMapRA.t unit)))
      -∗
      (∃ n',
          (⌜n = S n'⌝)
            **
            #=> (wait_set_wf (NatMap.remove tid W) n' ** own_thread tid)).
  Proof.
    iIntros "[[SUM BLACK] %] TH".
    iCombine "BLACK TH" as "OWN". iOwnWf "OWN".
    iAssert (⌜NatMap.find tid W = Some tt⌝)%I as "%".
    { iOwnWf "OWN".
      ur in H0. rewrite URA.unit_idl in H0. des.
      apply NatMapRA.extends_singleton_iff in H0. auto.
    }
    hexploit cardinal_remove.
    { apply NatMapP.F.in_find_iff. rewrite H1. ss. }
    i. subst. iExists _. iSplit; auto.
    iPoseProof (OwnM_Upd with "OWN") as "> BLACK".
    { eapply Auth.auth_dealloc. apply NatMapRA.remove_local_update. }
    iModIntro. iPoseProof (natmap_prop_remove_find with "SUM") as "[HD TL]"; [eauto|].
    iFrame. auto.
  Qed.

  Definition regionl (n: nat): iProp :=
    (∃ l, (Region.black l) ** (⌜List.length l = n⌝)).

  Lemma regionl_alloc n a tid
    :
    (regionl n)
      -∗
      (#=> (regionl (S n) ** Region.white n (tid, a))).
  Proof.
    iIntros "[% [BLACK %]]". subst.
    iPoseProof (Region.black_alloc with "BLACK") as "> [BLACK WHITE]".
    iModIntro. iFrame. iExists _. iSplit; auto.
    iPureIntro. ss. apply last_length.
  Qed.

  Definition waiters (start n: nat): iProp :=
    (list_prop_sum
       (fun a => (∃ k j tid,
                     (Region.white (start + a) (tid, k))
                       **
                       (OwnM (FiniteMap.singleton k (Consent.vote j (/2)%Qp)))
                       **
                       (ObligationRA.correl_thread j 1%ord)
                       **
                       (ObligationRA.pending j (/2)%Qp)
                       **
                       (∃ o, ObligationRA.black j o)
                       **
                       (FairRA.white (inl tid) (a × Ord.one)%ord)
                       **
                       (OwnM (Auth.white (NatMapRA.singleton tid tt: NatMapRA.t unit)))
       ))
       (seq 0 n))%I.

  Lemma waiters_nil start
    :
    ⊢ waiters start 0.
  Proof.
    unfold waiters. ss. auto.
  Qed.

  Lemma waiters_push start n
    :
    (waiters start n)
      -∗
      (∃ k j tid,
          (Region.white (start + n) (tid, k))
            **
            (OwnM (FiniteMap.singleton k (Consent.vote j (/2)%Qp)))
            **
            (ObligationRA.correl_thread j 1%ord)
            **
            (ObligationRA.pending j (/2)%Qp)
            **
            (∃ o, ObligationRA.black j o)
            **
            (FairRA.white (inl tid) (n × Ord.one)%ord)
            **
            (OwnM (Auth.white (NatMapRA.singleton tid tt: NatMapRA.t unit))))
      -∗
      (waiters start (S n)).
  Proof.
    unfold waiters. rewrite list_numbers.seq_S.
    iIntros "WAIT H". iApply list_prop_sum_combine. iSplitR "H".
    { auto. }
    { ss. iFrame. }
  Qed.

  Lemma waiters_rollback start n tid k a
        (IN: start <= a < start + n)
    :
      (Region.white a (tid, k))
      -∗
      (waiters start n)
      -∗
      ((∃ j, (OwnM (FiniteMap.singleton k (Consent.vote j (/2)%Qp)))
               **
               (ObligationRA.pending j (/2)%Qp))
         **
         (∀ j,
             (OwnM (FiniteMap.singleton k (Consent.vote j (/2)%Qp)))
               -*
               (ObligationRA.correl_thread j 1%ord)
               -*
               (ObligationRA.pending j (/2)%Qp)
               -*
               (∃ o, ObligationRA.black j o)
               -*
               (waiters start n))).
  Proof.
    assert (RANGE: (0 <= a - start < 0 + n)%nat).
    { lia. }
    iIntros "WHITE WAIT".
    apply in_seq in RANGE. apply in_split in RANGE. des.
    unfold waiters. rewrite RANGE.
    iPoseProof (list_prop_sum_split with "WAIT") as "[WAIT0 WAIT1]".
    iPoseProof (list_prop_sum_cons_unfold with "WAIT1") as "[[% [% [% [[[[[[H0 H1] H2] H3] H4] H5] H6]]]] WAIT2]".
    replace (start + (a - start)) with a by lia.
    iPoseProof (Region.white_agree with "WHITE H0") as "%".
    clarify.
    iSplitL "H1 H3".
    { iExists _. iFrame. }
    iIntros (?) "VOTE CORR PEND BLACK".
    iApply list_prop_sum_combine. iSplitL "WAIT0".
    { auto. }
    iApply list_prop_sum_cons_fold. iSplitR "WAIT2".
    2:{ auto. }
    iExists _, j0, _. iFrame.
    replace (start + (a - start)) with a by lia. iFrame.
  Qed.

  Definition waiters_tax start n: iProp :=
    (list_prop_sum
       (fun a => (∃ k tid,
                     (Region.white (start + a) (tid, k))
                       **
                       (FairRA.white (inl tid) Ord.one)))
       (seq 0 n))%I.

  Lemma waiters_pop start n
    :
    (waiters start (S n))
      -∗
      (∃ k j,
          (waiters (S start) n)
            **
            ((ConsentP.voted_singleton k j)
               **
               (ObligationRA.correl_thread j 1%ord)
               **
               (ObligationRA.pending j (/2)%Qp)
               **
               (∃ o, ObligationRA.black j o))
            **
            (waiters_tax (S start) n)).
  Proof.
    iIntros "WAIT".
  Admitted.

  Definition ticketlock_inv
             (L: bool) (W: NatMap.t unit)
             (reserved: bool)
             (now_serving: nat) (n: nat): iProp :=
    (wait_set_wf W n)
      **
      (regionl ((Nat.b2n reserved) + now_serving + n))
      **
      ((⌜n = 0 /\ L = false /\ reserved = false⌝ ** OwnM (Excl.just tt: Excl.t unit))
       ∨
         ((waiters (S ((Nat.b2n reserved) + now_serving)) n)
            **
            (∃ k j,
                (ConsentP.voted_singleton k j)
                  **
                  (ObligationRA.correl_thread j 1%ord)
                  **
                  (∃ o, ObligationRA.black j o)
                  **
                  (((⌜L = false /\ reserved = true⌝)
                      **
                      (OwnM (Excl.just tt: Excl.t unit))
                      **
                      (waiters_tax (S ((Nat.b2n reserved) + now_serving)) n)
                      **
                      (ObligationRA.pending j (/2)%Qp))
                   ∨
                     ((⌜L = true /\ reserved = false⌝)
                        **
                        (ObligationRA.shot j)))))).
End SIM.
