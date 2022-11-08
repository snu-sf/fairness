From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
Unset Universe Checking.
From Fairness Require Export ITreeLib WFLib FairBeh NatStructs Mod pind Axioms OpenMod SCM Red IRed Wrapper.
From Ordinal Require Export ClassicalHessenberg.


Set Implicit Arguments.


Module FairLock.
  Definition lock_fun: WMod.function bool unit void :=
    WMod.mk_fun
      tt
      (fun (_: unit) st next =>
         match st with
         | true => next = WMod.disabled
         | false => next = WMod.normal true tt (sum_fmap_l (fun _ => Flag.fail))
         end).

  Definition unlock_fun: WMod.function bool unit void :=
    WMod.mk_fun
      tt
      (fun (_: unit) st next =>
         match st with
         | false => next = WMod.stuck
         | true => next = WMod.normal false tt (sum_fmap_l (fun _ => Flag.emp))
         end).

  Definition wmod: WMod.t :=
    WMod.mk
      false
      [("lock", lock_fun);
       ("unlock", unlock_fun)
      ].

  Definition mod: Mod.t :=
    WMod.interp_mod wmod.
End FairLock.

Module TicketLock.
  Definition now_serving: SCMem.val := SCMem.val_ptr (0, 0).
  Definition next_ticket: SCMem.val := SCMem.val_ptr (0, 1).

  Definition lock_loop (myticket: SCMem.val):
    itree ((((@eventE void) +' cE) +' (sE unit)) +' OpenMod.callE) unit
    :=
    ITree.iter
      (fun (_: unit) =>
         next <- (OMod.call "load" (now_serving));;
         b <- (OMod.call "compare" (next: SCMem.val, myticket: SCMem.val));;
         if (b: bool) then Ret (inr tt) else Ret (inl tt)) tt.

  Lemma lock_loop_red myticket
    :
    lock_loop myticket
    =
      next <- (OMod.call "load" (now_serving));;
      b <- (OMod.call "compare" (next: SCMem.val, myticket: SCMem.val));;
      if (b: bool)
      then Ret tt else tau;; lock_loop myticket.
  Proof.
    unfold lock_loop. etransitivity.
    { apply unfold_iter. }
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
      _ <- trigger Yield;;
      v <- (OMod.call "load" now_serving);;
      let v := SCMem.val_add v 1 in
      `_: unit <- (OMod.call "store" (now_serving, v));;
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
      (SCMem.mod [1; 1])
  .
End TicketLock.

From Fairness Require Import IProp IPM Weakest.
From Fairness Require Import ModSim PCM MonotonePCM StateRA FairRA.

Section SIM.
  Context `{Σ: GRA.t}.

  Context `{MONORA: @GRA.inG monoRA Σ}.
  Context `{THDRA: @GRA.inG ThreadRA Σ}.
  Context `{STATESRC: @GRA.inG (stateSrcRA (bool * NatMap.t unit)) Σ}.
  Context `{STATETGT: @GRA.inG (stateTgtRA (unit * SCMem.t)) Σ}.
  Context `{IDENTSRC: @GRA.inG (identSrcRA (id_sum thread_id void)) Σ}.
  Context `{IDENTTGT: @GRA.inG (identTgtRA (void + SCMem.val)%type) Σ}.
  Context `{OBLGRA: @GRA.inG ObligationRA.t Σ}.
  Context `{ARROWRA: @GRA.inG (ArrowRA (void + SCMem.val)%type) Σ}.
  Context `{EDGERA: @GRA.inG EdgeRA Σ}.
  Context `{ONESHOTSRA: @GRA.inG (@FiniteMap.t (OneShot.t unit)) Σ}.

  Context `{MEMRA: @GRA.inG memRA Σ}.
  Context `{EXCL: @GRA.inG (Excl.t unit) Σ}.
  Context `{ONESHOTRA: @GRA.inG (OneShot.t thread_id) Σ}.
  Context `{NATMAPRA: @GRA.inG (Auth.t (NatMapRA.t unit)) Σ}.
  Context `{REGIONRA: @GRA.inG (Region.t (thread_id * nat)) Σ}.
  Context `{CONSENTRA: @GRA.inG (@FiniteMap.t (Consent.t nat)) Σ}.
  Context `{AUTHRA: @GRA.inG (Auth.t (NatMapRA.t (nat * nat))) Σ}.

  Lemma natmap_prop_sum_in A P k a (m: NatMap.t A)
        (FIND: NatMap.find k m = Some a)
    :
    (natmap_prop_sum m P)
      -∗
      (P k a).
  Proof.
    iIntros "MAP". iPoseProof (natmap_prop_remove_find with "MAP") as "[H0 H1]".
    { eauto. }
    eauto.
  Qed.

  Lemma natmap_prop_sum_impl A P0 P1 (m: NatMap.t A)
        (IMPL: forall k a (IN: NatMap.find k m = Some a), P0 k a ⊢ P1 k a)
    :
    (natmap_prop_sum m P0)
      -∗
      (natmap_prop_sum m P1).
  Proof.
    revert IMPL. pattern m. eapply nm_ind.
    { iIntros. iApply natmap_prop_sum_empty. }
    i. iIntros "MAP".
    iPoseProof (natmap_prop_remove_find with "MAP") as "[H0 H1]".
    { eapply nm_find_add_eq. }
    iPoseProof (IMPL with "H0") as "H0".
    { rewrite nm_find_add_eq. auto. }
    iApply (natmap_prop_sum_add with "[H1] H0").
    iApply IH.
    { i. eapply IMPL. rewrite NatMapP.F.add_o; eauto. des_ifs. }
    { rewrite nm_find_none_rm_add_eq; auto. }
  Qed.

  Lemma natmap_prop_sum_wand (A: Type) P0 P1 (m: NatMap.t A)
    :
    (natmap_prop_sum m P0)
      -∗
      (natmap_prop_sum m (fun k v => P0 k v -* P1 k v))
      -∗
      (natmap_prop_sum m P1).
  Proof.
    pattern m. eapply nm_ind.
    { iIntros. iApply natmap_prop_sum_empty. }
    i. iIntros "MAP IMPL".
    iPoseProof (natmap_prop_remove_find with "MAP") as "[H0 H1]".
    { eapply nm_find_add_eq. }
    iPoseProof (natmap_prop_remove_find with "IMPL") as "[G0 G1]".
    { eapply nm_find_add_eq. }
    iApply (natmap_prop_sum_add with "[H1 G1] [H0 G0]").
    { rewrite nm_find_none_rm_add_eq; auto. iApply (IH with "H1 G1"). }
    { iApply ("G0" with "H0"). }
  Qed.

  Lemma natmap_prop_sum_impl_strong (A: Type) P0 P1 Q (m: NatMap.t A)
        (IMPL: forall k v, P0 k v ** Q ⊢ P1 k v ** Q)
    :
    (natmap_prop_sum m P0 ** Q)
      -∗
      (natmap_prop_sum m P1 ** Q).
  Proof.
    pattern m. eapply nm_ind.
    { iIntros "[SUM H]". iFrame. }
    i. iIntros "[MAP H]".
    iPoseProof (natmap_prop_remove_find with "MAP") as "[H0 H1]".
    { eapply nm_find_add_eq. }
    rewrite nm_find_none_rm_add_eq; [|auto].
    iPoseProof (IH with "[H1 H]") as "[H1 H]".
    { iFrame. }
    iPoseProof (IMPL with "[H0 H]") as "[H0 H]".
    { iFrame. }
    iFrame. iApply (natmap_prop_sum_add with "H1 H0").
  Qed.

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
      ((∃ k j tid,
           (waiters (S start) n)
             **
             ((Region.white start (tid, k))
                **
                (ConsentP.voted_singleton k j)
                **
                (ObligationRA.correl_thread j 1%ord)
                **
                (ObligationRA.pending j (/2)%Qp)
                **
                (∃ o, ObligationRA.black j o)
                **
                (OwnM (Auth.white (NatMapRA.singleton tid tt: NatMapRA.t unit)))
             )
             **
             (waiters_tax (S start) n))).
  Proof.
    iIntros "WAIT".
  Admitted.

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



  Definition waiters_tax start n: iProp :=
    (list_prop_sum
       (fun a => (∃ k tid,
                     (Region.white (start + a) (tid, k))
                       **
                       (FairRA.white (inl tid) Ord.one)))
       (seq 0 n))%I.

  Definition waiters_set_tax (W: NatMap.t unit): iProp :=
    (∃ lf,
        (⌜forall i (IN: @WMod.interp_fmap FairLock.wmod (fun _ => Flag.fail) W i = Flag.fail), List.In i lf⌝)
          **
          (list_prop_sum (fun i => FairRA.white i Ord.one) lf)).

  Lemma waiters_tax_push start n
    :
    (waiters_tax start n)
      -∗
      (∃ k tid,
          (Region.white (start + n) (tid, k))
            **
            (FairRA.white (inl tid) Ord.one))
      -∗
      (waiters_tax start (S n)).
  Proof.
    unfold waiters_tax. rewrite list_numbers.seq_S.
    iIntros "WAIT H". iApply list_prop_sum_combine. iSplitR "H".
    { auto. }
    { ss. iFrame. }
  Qed.

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

  Definition ticketlock_locked_inv
             (L: bool) (W: NatMap.t unit)
             (now_serving: nat) (n: nat): iProp :=
    (wait_set_wf W (n + (if L then 0 else 1)))
      **
      (∀


.


  * i in (0, n], exists j tid, (now + i) ~ (j, tid) * white(tid, i)
  |W| = n + (1 - L)
  forall tid in W, exists i in [L, n], exists j tid, (now + i) ~ (j, tid)
  exists j,
    now ~ (j, _)
    L = 0 * excl * white(W) ~j~> L = 1 * auth_white{now}


    if llocked then


  Definition ticketlock_inv
             (L: bool) (W: NatMap.t unit)
             (llocked: bool)
             (now_serving: nat) (n: nat): iProp :=
    if llocked then


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
                      (ObligationRA.pending k (/2)%Qp))
                   ∨
                     ((⌜L = true /\ reserved = false⌝)
                        **
                        (ObligationRA.shot k)))))).

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
                      (ObligationRA.pending k (/2)%Qp))
                   ∨
                     ((⌜L = true /\ reserved = false⌝)
                        **
                        (ObligationRA.shot k)))))).

  Definition ticket (n: nat) (tid: thread_id) (k: nat) (j: nat): iProp. Admitted.
  Definition own_lock (n: nat): iProp. Admitted.

  Lemma ticket_check t tid k j
        L W reserved now_serving n
    :
    (ticket t tid k j)
      -∗
      (ticketlock_inv L W reserved now_serving n)
      -∗
      (⌜(now_serving = t /\ reserved = true /\ L = false) \/
         (now_serving < t <= now_serving + n)⌝)%I.
  Admitted.

  Lemma own_check t
        L W reserved now_serving n
    :
    (ticketlock_inv L W reserved now_serving n)
      -∗
      (own_lock t)
      -∗
      (⌜L = true /\ reserved = false /\ now_serving = t⌝)%I.
  Admitted.

  Lemma ticketlock_inv_init
    :
    (Region.black [] ** OwnM (Auth.black (Some (NatMap.empty unit): NatMapRA.t unit)) ** (OwnM (Excl.just tt: Excl.t unit)))
      -∗
      ticketlock_inv false (NatMap.empty unit) false 0 0.
  Proof.
    iIntros "[[BLACK EMPTY] EXCL]". iSplitR "EXCL".
    { ss. iSplitL "EMPTY".
      { unfold wait_set_wf. iFrame. iPureIntro. apply NatMapP.cardinal_1. apply NatMap.empty_1.
      }
      { iExists _. iFrame. auto. }
    }
    iLeft. iSplit; auto.
  Qed.

  Lemma ticketlock_inv_register L W reserved now_serving n tid
    :
    (ticketlock_inv L W reserved now_serving n)
      -∗
      (own_thread tid)
      -∗
      (FairRA.white (inl tid) (Ord.one × (S n))%ord)
      -∗
      (ticketlock_inv L (NatMap.add tid tt W) reserved now_serving (S n)).
  Admitted.

  Lemma ticketlock_inv_pass W now_serving n
    :
    (ticketlock_inv true W false now_serving (S n))
      -∗
      (own_lock now_serving)
      -∗
      (ticketlock_inv false W true (S now_serving) n).
  Admitted.

  Lemma ticketlock_inv_release W now_serving
    :
    (ticketlock_inv true W false now_serving 0)
      -∗
      (own_lock now_serving)
      -∗
      (ticketlock_inv false W false now_serving 0).
  Admitted.

  Lemma ticketlock_inv_lock W now_serving n tid k j
    :
    (ticketlock_inv false W true now_serving n)
      -∗
      (ticket now_serving tid k j)
      -∗
      ((ObligationRA.pending k (/2)%Qp)
         **
         (waiters_set_tax W)
         **
         ((ObligationRA.shot k)
            -*
            (ticketlock_inv true W false now_serving n))).
  Admitted.

  Lemma ticketlock_inv_rollback L W reserved now_serving n t tid k j
        (RANGE: t <= now_serving + n)
    :
    (ticketlock_inv L W reserved now_serving n)
      -∗
      (ticket t tid k j)
      -∗
      ((OwnM (FiniteMap.singleton k (Consent.vote j (/2)%Qp)))
         **
         (ObligationRA.pending j (/2)%Qp)
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
               (ticket t tid k j ** ticketlock_inv L W reserved now_serving n))).
  Admitted.

  Let I: list iProp := [
      (∃ m,
          (memory_black m)
            **
            (St_tgt (tt, m)));
      (∃ L W reserved now_serving n,
          (St_src (L, W))
            **
            (ticketlock_inv L W reserved now_serving n)
            **
            (points_to TicketLock.next_ticket (SCMem.val_nat ((Nat.b2n reserved) + now_serving + n)))
            **
            (points_to TicketLock.next_ticket (SCMem.val_nat ((Nat.b2n reserved) + now_serving + n))))]%I.

  Lemma sim: ModSim.mod_sim TicketLock.mod FairLock.mod.
  Proof.
    refine (@ModSim.mk _ _ nat_wf nat_wf _ _ Σ _ _ _).
    { econs. exact 0. }
    { i. exists (S o0). ss. }
    { admit. }
    { i. ss. unfold OMod.closed_funs. ss. des_ifs.
      { cut (forall tid,
                (own_thread tid ** ObligationRA.duty (inl tid) []) ⊢ stsim I tid [0; 1] ibot5 ibot5 (fun r_src r_tgt => own_thread tid ** ObligationRA.duty (inl tid) [] ** ⌜r_src = r_tgt⌝) (Mod.wrap_fun (WMod.interp_fun FairLock.wmod FairLock.lock_fun) args) (OMod.close_itree TicketLock.omod (SCMem.mod [1; 1]) (Mod.wrap_fun TicketLock.lock_fun args))).
        { admit. }
        i. iIntros "[TH DUTY]".
        unfold Mod.wrap_fun, TicketLock.lock_fun. lred. rred.
        destruct (Any.downcast args) eqn:EQ.
        2:{ ss. unfold UB. lred. iApply stsim_UB. }
        clear EQ. ss. lred. rred.
        rewrite WMod.interp_fun_unfold. unfold WMod.interp_fun_register. lred.
        rewrite close_itree_call. ss. rred.
        iApply (stsim_sync with "[DUTY]"); [msubtac|iFrame|]. iIntros "DUTY _".
        rred. unfold SCMem.faa_fun, Mod.wrap_fun. rred.
        iopen 0 "[% [MEM ST]]" "K0".
        iApply stsim_getR. iSplit.
        { iFrame. }
        rred. iApply stsim_tauR. rred.
        iopen 1 "[% [% [% [% [% [[[SRC INV] NOW] NEXT]]]]]]" "K1".
        iPoseProof (memory_ra_faa with "MEM NOW") as "[% [% > [MEM NOW]]]".
        des. rewrite H.
        rred. iApply stsim_getR. iSplit.
        { iFrame. }
        rred. iApply (stsim_putR with "ST"). iIntros "ST".
        rred. iApply stsim_tauR.
        rred. iApply stsim_tauR.
        rred. lred. iApply stsim_tidL. lred.
        iApply stsim_getL. iSplit.
        { iFrame. }
        lred. iApply (stsim_putL with "SRC"). iIntros "SRC".
        lred. iApply stsim_fairL.
        { instantiate (1:=[]). unfold sum_fmap_l. i. des_ifs. }
        { instantiate (1:=[inl tid]). unfold sum_fmap_l. i. ss. des; clarify. des_ifs. }
        { ss. }
        instantiate (1:=Hessenberg.add Ord.one (Ord.one × (S n))%ord).
        iIntros "[WHITES _]".
        lred. rewrite WMod.interp_loop_unfold.
        lred. iApply stsim_chooseL. iExists true.
        iPoseProof (FairRA.white_split with "WHITES") as "[WHITE WHITES]".
        lred. iApply (stsim_fairL with "[WHITE]").
        { instantiate (1:=[inl tid]). unfold sum_fmap_l. i. ss. des_ifs. auto. }
        { instantiate (1:=[]). unfold sum_fmap_l. i. ss. }
        { ss. iFrame. }
        iIntros "_".
        lred.






des_ifs. }

        { ss. }


ss.


Hessenberg.add
        iIntros "[
FairRA.cut_white
        { instantiate (1:=[]). i

ss.

iIntros "ST".





        iPoseProof (@ObligationRA.alloc _ _ ((1 × Ord.omega) × 10)%ord) as "> [% [[# BLACK WHITES] OBL]]".
        iPoseProof (ObligationRA.cut_white with "WHITES") as "[WHITES WHITE]".
        iPoseProof (ObligationRA.duty_alloc with "DUTY WHITE") as "> DUTY".
        iPoseProof (ObligationRA.duty_correl_thread with "DUTY") as "# CORR"; [ss; eauto|].
        iPoseProof (OwnM_Upd with "PEND") as "> SHOT".
        { eapply (OneShot.pending_shot k). }
        iPoseProof (own_persistent with "SHOT") as "# SHOTP". iClear "SHOT". ss.
        iMod ("K0" with "[MEM ST]") as "_".
        { iExists _. iFrame. }
        iPoseProof (ObligationRA.pending_split with "[OBL]") as "[OBL0 OBL1]".
        { rewrite Qp_inv_half_half. iFrame. }
        iMod ("K1" with "[POINTF POINTL OBL1]") as "_".
        { iRight. iExists _. iFrame. iSplitR.
          { iSplit; [iSplit; [iApply "SHOTP"|iApply "CORR"]|eauto]. }
          { iLeft. iFrame. }
        }
        { msubtac. }
        iPoseProof (ObligationRA.cut_white with "WHITES") as "[WHITES WHITE]".
        msimpl. iApply (stsim_yieldR with "[DUTY WHITE]").
        { msubtac. }
        { iFrame. iSplit; auto. }
        iIntros "DUTY _".
        rred. iApply stsim_tauR.
        iPoseProof (ObligationRA.cut_white with "WHITES") as "[WHITES WHITE]".
        rred. iApply (stsim_yieldR with "[DUTY WHITE]").
        { msubtac. }
        { iFrame. iSplit; auto. }
        iIntros "DUTY _".
        rred. iApply stsim_tauR.
        rred. rewrite close_itree_call. ss.
        iPoseProof (ObligationRA.cut_white with "WHITES") as "[WHITES WHITE]".
        rred. iApply (stsim_yieldR with "[DUTY WHITE]").
        { msubtac. }
        { iFrame. iSplit; auto. }
        iIntros "DUTY _".
        unfold SCMem.store_fun, Mod.wrap_fun. rred.
        iopen 0 "[% [MEM ST]]" "K0".
        iApply stsim_getR. iSplit.
        { iFrame. }
        rred. iApply stsim_tauR. rred.
        iopen 1 "[[[POINTL POINTF] PEND]|[% [H H1]]]" "K1".
        { iExFalso. iApply OneShotP.pending_not_shot. iSplit; iFrame. auto. }
        { iPoseProof (OneShotP.shot_agree with "[H]") as "%".
          { iSplit.
            { iApply "SHOTP". }
            { iDestruct "H" as "[[[H _] _] _]". iApply "H". }
          }
          subst.
          iDestruct "H1" as "[[POINTF PEND]|[POINTF OBL1]]".
          { iPoseProof (memory_ra_store with "MEM POINTF") as "[% [% > [MEM POINTF]]]".
            rewrite H2. ss.
            rred. iApply stsim_getR. iSplit.
            { iFrame. }
            rred. iApply (stsim_putR with "ST"). iIntros "ST".
            rred. iApply stsim_tauR.
            rred. iApply stsim_tauR. rred.
            iMod ("K0" with "[MEM ST]") as "_".
            { iExists _. iFrame. }
            iPoseProof (ObligationRA.pending_shot with "[OBL0 PEND]") as "> # OSHOT".
            { rewrite <- Qp_inv_half_half. iApply (ObligationRA.pending_sum with "OBL0 PEND"). }
            iMod ("K1" with "[POINTF H OSHOT]") as "_".
            { iRight. iExists _. iFrame. iRight. iFrame. auto. }
            { msubtac. }
            iPoseProof (ObligationRA.duty_done with "DUTY OSHOT") as "> DUTY".
            iApply (stsim_sync with "[DUTY]").
            { msubtac. }
            { iFrame. }
            iIntros "DUTY _".
            iApply stsim_tauR.
            iApply stsim_ret. iModIntro. iFrame. auto.
          }
          { iExFalso. iApply (ObligationRA.pending_not_shot with "OBL0 OBL1"). }
        }
      }
      { iDestruct "H" as "[[[[# SHOTK # CORR] [% # BLACK]] POINTL] F]".
        iPoseProof (memory_ra_load with "MEM POINTL") as "%". des; clarify.
        rewrite H. ss.
        rred. iApply stsim_tauR.
        iMod ("K0" with "[MEM ST]") as "_".
        { iExists _. iFrame. }
        iMod ("K1" with "[POINTL F]") as "_".
        { iRight. iExists _. iFrame. auto. }
        { msubtac. }
        rred. iStopProof. pattern n. revert n.
        apply (well_founded_induction Ord.lt_well_founded). intros o IH.
        iIntros "[# [SHOTK [CORR BLACK]] [TH DUTY]]".
        rewrite OpenMod.unfold_iter. rred.
        iApply (stsim_yieldR with "[DUTY]").
        { msubtac. }
        { iFrame. }
        iIntros "DUTY WHITE".
        rred. iApply stsim_tauR. rred.
        rewrite close_itree_call. ss.
        unfold SCMem.load_fun, Mod.wrap_fun.
        rred. iApply (stsim_yieldR with "[DUTY]").
        { msubtac. }
        { iFrame. }
        iIntros "DUTY _".
        iopen 0 "[% [MEM ST]]" "K0".
        rred. iApply stsim_getR. iSplit.
        { iFrame. }
        rred. iApply stsim_tauR. rred.
        iopen 1 "[FALSE|[% H]]" "K1".
        { iExFalso. iApply OneShotP.pending_not_shot. iSplit; [|iApply "SHOTK"].
          iDestruct "FALSE" as "[[? ?] ?]". iFrame.
        }
        iDestruct "H" as "[X [Y|Y]]".
        { iPoseProof (OneShotP.shot_agree with "[X]") as "%".
          { iSplit.
            { iApply "SHOTK". }
            { iDestruct "X" as "[[[H ?] ?] ?]". iApply "H". }
          }
          subst.
          iPoseProof (ObligationRA.correl_thread_correlate with "CORR WHITE") as "> [WHITE|WHITE]"; cycle 1.
          { iExFalso. iApply (ObligationRA.pending_not_shot with "[Y] WHITE").
            iDestruct "Y" as "[_ ?]". eauto.
          }
          iPoseProof (memory_ra_load with "MEM [Y]") as "%".
          { iDestruct "Y" as "[? _]". iFrame. }
          des. rewrite H1.
          rred. iApply stsim_tauR.
          iMod ("K0" with "[MEM ST]") as "_".
          { iExists _. iFrame. }
          iMod ("K1" with "[X Y]") as "_".
          { iRight. iExists _. iFrame. }
          { msubtac. }
          rred. iApply (stsim_yieldR with "[DUTY]").
          { msubtac. }
          { iFrame. }
          iIntros "DUTY _".
          rred. iApply stsim_tauR.
          rred. rewrite close_itree_call. ss.
          unfold SCMem.compare_fun, Mod.wrap_fun.
          rred. iApply (stsim_yieldR with "[DUTY]").
          { msubtac. }
          { iFrame. }
          iIntros "DUTY _".
          iopen 0 "[% [MEM ST]]" "K0".
          rred. iApply stsim_getR. iSplit.
          { iFrame. }
          iMod ("K0" with "[MEM ST]") as "_".
          { iExists _. iFrame. }
          { msubtac. }
          rred. iApply stsim_tauR.
          rred. iApply stsim_tauR.
          rred. iApply (stsim_yieldR with "[DUTY]").
          { msubtac. }
          { iFrame. }
          iIntros "DUTY _".
          rred. iApply stsim_tauR.
          rred. iApply stsim_tauR.
          iPoseProof (ObligationRA.black_white_decr_one with "BLACK WHITE") as "> [% [# BLACK1 %]]".
          iApply IH; eauto. iFrame. iModIntro. iSplit; auto.
        }
        { iPoseProof (memory_ra_load with "MEM [Y]") as "%".
          { iDestruct "Y" as "[? _]". iFrame. }
          des. rewrite H1.
          rred. iApply stsim_tauR.
          iMod ("K0" with "[MEM ST]") as "_".
          { iExists _. iFrame. }
          iMod ("K1" with "[X Y]") as "_".
          { iRight. iExists _. iFrame. }
          { msubtac. }
          rred. iApply (stsim_yieldR with "[DUTY]").
          { msubtac. }
          { iFrame. }
          iIntros "DUTY _".
          rred. iApply stsim_tauR.
          rred. rewrite close_itree_call. ss.
          unfold SCMem.compare_fun, Mod.wrap_fun.
          rred. iApply (stsim_yieldR with "[DUTY]").
          { msubtac. }
          { iFrame. }
          iIntros "DUTY _".
          iopen 0 "[% [MEM ST]]" "K0".
          rred. iApply stsim_getR. iSplit.
          { iFrame. }
          iMod ("K0" with "[MEM ST]") as "_".
          { iExists _. iFrame. }
          { msubtac. }
          rred. iApply stsim_tauR.
          rred. iApply stsim_tauR.
          rred. iApply (stsim_sync with "[DUTY]").
          { msubtac. }
          { iFrame. }
          iIntros "DUTY _".
          rred. iApply stsim_tauR.
          rred. iApply stsim_ret.
          iModIntro. iFrame. auto.
        }
      }

instantiate (1:=None). ss. iFrame. iIntros "INV _".
        rred. lred. iApply fsim_tidL. lred.
        iDestruct "INV" as "[[[%m [MEM TGT]] IM] [% [% [[[[NEXT NOW] MONO] MAP] WAIT]]]]".
        unfold Mod.wrap_fun, SCMem.faa_fun.
        rred. iApply fsim_getR. iSplit.
        { iFrame. }
        rred. iApply fsim_tauR.
        iPoseProof (memory_ra_faa with "MEM NEXT") as "[% [% > [MEM NEXT]]]".
        rred. rewrite H.
        rred. iApply fsim_getR. iSplit.
        { iFrame. }
        rred. iApply (fsim_putR with "TGT"). iIntros "TGT".
        rred. iApply fsim_tauR.
        rred. iApply fsim_tauR.
        iPoseProof "IM" as "[% [% [BLACK IM]]]".
        rred. iDestruct "WAIT" as "[[% SRC]|H]".
        { subst. iApply fsim_getL. iSplit.
          { iFrame. }
          lred. iApply (fsim_putL with "SRC"). iIntros "SRC".
          iPoseProof ((@blacks_success_single tid (Ord.S (Ord.S Ord.O))) with "BLACK") as "> [% [[BLACK FUEL] %]]".
          lred. iApply (fsim_fairL with "IM"). iExists _. iSplit.
          { iPureIntro. eapply imap_sum_update_l; eauto. }
          iIntros "IM".
          iPoseProof (fair_white_one with "FUEL") as "[FUEL ONE]".
          iApply fsim_alloc_obligation.
          { instantiate (1:=Ord.S (Ord.S (Ord.O))).
            iIntros "% PENDING NEG # POS".
            iPoseProof "MAP" as "[% [MAP %]]".
            iPoseProof (black_updatable with "MAP") as "> MAP".
            { instantiate (1:=(fun m => if (Nat.eq_dec m (now_serving + 1)) then Some k else f m)).
              ii. des_ifs. exfalso. rewrite H1 in SOME; ss. lia.
            }


tid_dec

            iAssert (#=> (I ** monoBlack 1 (partial_map_PreOrder nat nat) (partial_map_singleton (now_serving + 1))) with "[NOW MONO MAP MEM NEXT TGT SRC BLACK IM FUEL ONE]" as "INV".
            { unfold I. iSplitL "MEM TGT BLACK IM".
              { iModIntro. iSplitL "MEM TGT".
                { iExists _. iFrame. }
                { iExists _, _. iFrame. }
              }
              iExists now_serving, 1. iFrame. iSplitL "NEXT MAP".
              { monoBlack 1 (partial_map_PreOrder nat nat) (partial_map_singleton (now_serving + 1) )

ss.

, _. iFrame.


 red.

          rewrite unfold_iter_eq. lred. iApply fsim_chooseL. iExists true.
          lred.

(inl ).

          rewrite ITree.iter

          iPoseProof ((@blacks_success_single tid (Ord.S (Ord.S Ord.O))) with "IMBLACK") as "> [% [[IMBLACK FUEL] %]]".
          lred. iApply (fsim_fairL with "IM"). iExists _. iSplit.
          { iPureIntro. eapply imap_sum_update_l; eauto. }
          iIntros "IM".



blacks_fail_single
          lred.

          {


          ss.
          { ss. unfold OMod.closed_ident. ss. eapply IDENTTGT.
unfold

s

          iPoseProof (memory_ra_faa with "MEM NEXT") as "[% [% > [MEM NEXT]]]".




iApply fsim_tauR.

iApply (fsim_putR with "ST"). iIntros "ST".

iSplit.
        { iFrame. }


ss. des; clarify.


        rred. iApply fsim_getR. iSplit.
        { iFrame. }
        rred. iApply fsim_tauR.
        iPoseProof (memory_ra_load with "MEM NEXT") as "%". ss. des; clarify.
        rred. ss. rewrite H.

                iPoseProof (memory_ra_load
        rred.

[% [% [% [% H]]]]]".

        iDestruct "INV" as "[[[%m [MEM ST]] IM] [% [% [% [% H]]]]]".


  Let I: iProp :=
        (∃ m,
            (memory_black m)
              **
              (St_tgt (tt, m)))
          **
          (∃ im0 im1,
              (OwnM (Auth.white (Excl.just (imap_sum_id (im0, im1)): @Excl.t _): identSrcRA (id_sum thread_id void) (mk_wf Ord.lt_well_founded)))
                **
                True
          )
          **
          (∃ now_serving n f i,
              (points_to TicketLock.next_ticket (SCMem.val_nat (now_serving + n)))
                **
                (monoBlack 0 ge_PreOrder now_serving)
                **
                (monoBlack 1 (@partial_map_PreOrder nat nat) f)
                **
                (⌜forall m (LT: now_serving + n < m), f m = None⌝)
                **
                (monoWhite 1 (@partial_map_PreOrder nat nat) (partial_map_singleton now_serving i))
                **
                (Eventually i (points_to TicketLock.now_serving (SCMem.val_nat now_serving)))
                **
                (waiters now_serving n))
  .

        iApply fsim_getR. iSplit.
        { iFrame. }
        rred. iApply fsim_tauR. rred.

        unfold SCMem.cas.
        destruct w; ss.
        { iDestruct "H" as "[[POINTL POINTF] EXCL]".
          iPoseProof (memory_ra_load with "MEM POINTL") as "%". ss. des; clarify.
          rewrite H. ss.
          iPoseProof (memory_ra_store with "MEM POINTL") as "[% [% > [MEM POINTL]]]".
          rewrite H1. ss.
          rred. iApply fsim_getR. iSplit.
          { iFrame. }
          rred. iApply (fsim_putR with "ST"). iIntros "ST".
          rred. iApply fsim_tauR.
          rred. iApply fsim_tauR.

          iApply (@fsim_alloc_obligation _ _ _ _ _ _ _ (Ord.large × 10)%ord). iIntros "% ONG NEG # POS".
          iDestruct (monoBlack_alloc le_PreOrder 0) as "-# > [% ORD]".
          iPoseProof (black_updatable with "MONO") as "> MONO".
          { instantiate (1:=W_own k k0). econs. }
          iPoseProof (black_persistent_white with "MONO") as "# MWHITE".
          iPoseProof (Neg_split with "NEG") as "> [FUEL NEG]". { eapply ord_mult_split. }
          rred. iApply (@fsim_yieldR _ _ _ _ _ _ _ None). iSplitR "EXCL NEG".
          { ss. iFrame. iSplit; auto. iSplitL "MEM ST".
            { iExists _. iFrame. }
            iExists _. iFrame. iSplit.
            { iExists _. iFrame. auto. }
            { iClear "POINTF ORD". iModIntro. iExists _. eauto. }
          }
          iIntros "INV _".
          iPoseProof (Neg_split with "NEG") as "> [FUEL NEG]". { eapply ord_mult_split. }
          rred. iApply fsim_tauR.
          rred. iApply (@fsim_yieldR _ _ _ _ _ _ _ None). ss. iFrame.
          iIntros "INV _".
          iPoseProof (Neg_split with "NEG") as "> [FUEL NEG]". { eapply ord_mult_split. }

        rred. iApply fsim_tauR.
        rred. rewrite close_itree_call. ss.
        rred. iApply (@fsim_yieldR _ _ _ _ _ _ _ None). ss. iFrame.
        iIntros "INV _".
        iPoseProof (Neg_split with "NEG") as "> [FUEL NEG]". { eapply ord_mult_split. }

        unfold SCMem.store_fun, Mod.wrap_fun.
        iDestruct "INV" as "[[% [MEM ST]] [% [MONO H]]]".
        rred. iApply fsim_getR. iSplit.
        { iFrame. }
        rred. iApply fsim_tauR. rred.

        iPoseProof (black_white_compare with "MWHITE MONO") as "%". inv H2.
        ss. iDestruct "H" as "[[POINTL [% [[POINTF ORD] %]]] EVT]".

        iPoseProof (memory_ra_store with "MEM POINTF") as "[% [% > [MEM POINTF]]]".
        rewrite H3. ss.
        rred. iApply fsim_getR. iSplit.
        { iFrame. }
        rred. iApply (fsim_putR with "ST"). iIntros "ST".
        rred. iApply fsim_tauR.
        rred. iApply fsim_tauR.
        iPoseProof (eventually_finish with "EVT") as "[# DONE | [ONG EVT]]".
        { iApply (fsim_obligation_not_done with "DONE"). ss. auto. }
        iPoseProof (black_updatable with "ORD") as "> ORD".
        { instantiate (1:=1). lia. }
        iPoseProof (black_persistent_white with "ORD") as "#WHITE".
        iApply (fsim_dealloc_obligation with "ONG").
        { ss. }
        iIntros "# DONE". iPoseProof ("EVT" with "DONE WHITE") as "EVT".

        rred. iApply (@fsim_sync _ _ _ _ _ _ _ None). iSplitR "".
        { ss. unfold I. iSplit; auto. iSplit; auto. iSplitL "MEM ST".
          { iExists _. iFrame. }
          iExists _. iFrame. ss. iFrame.
          iExists _. iFrame. auto.
        }
        iIntros "INV _". iApply fsim_tauR. iApply fsim_ret. auto.
      }

      { iDestruct "H" as "[[POINTL POINTF] EXCL]".
        iPoseProof (memory_ra_load with "MEM POINTL") as "%". des; clarify.
        iPoseProof (eventually_obligation with "EXCL") as "# [% OBL]".
        rewrite H. ss.
        rred. iApply fsim_tauR.
        rred.
        iPoseProof (black_persistent_white with "MONO") as "# WHITE".
        iAssert I with "[MEM ST MONO POINTL POINTF EXCL]" as "INV".
        { unfold I. iSplitL "MEM ST".
          { iExists _. iFrame. }
          iExists (W_own _ _). ss. iFrame.
        }
        iStopProof.
        pattern n. revert n. eapply (well_founded_induction Ord.lt_well_founded). intros o IH.
        iIntros "[# [OBL WHITE] INV]".
        rewrite unfold_iter_eq. rred.
        iApply (@fsim_yieldR _ _ _ _ _ _ _ (Some k)).
        ss. iFrame. iSplitL.
        { iExists _. eauto. }
        iIntros "INV FUEL".
        rred. iApply fsim_tauR.
        rred. rewrite close_itree_call. ss.
        unfold SCMem.load_fun, Mod.wrap_fun. ss.
        rred. iApply (@fsim_yieldR _ _ _ _ _ _ _ None). ss. iFrame. iIntros "INV _".
        iDestruct "INV" as "[[% [MEM ST]] [% [MONO H]]]".
        rred. iApply fsim_getR. iSplit. { iFrame. }
        rred. iApply fsim_tauR. rred.
        iPoseProof (black_white_compare with "WHITE MONO") as "%". inv H1.
        ss. iDestruct "H" as "[[POINTL [% [[POINTF PWHITE] %]]] EVT]".
        iPoseProof (memory_ra_load with "MEM POINTF") as "%".
        destruct H2 as [LOAD _]. rewrite LOAD.
        rred. iApply fsim_tauR.
        rred. des; subst; cycle 1.
        { iApply (@fsim_yieldR _ _ _ _ _ _ _ None). ss. iSplitL.
          { iSplit; auto. iSplit; auto. unfold I. iSplitL "MEM ST".
            { iExists _. iFrame. }
            iExists (W_own _ _). ss. iFrame. iExists _. iFrame. auto.
          }
          iIntros "INV _".
          rred. iApply fsim_tauR.
          rred. rewrite close_itree_call. ss.
          unfold SCMem.compare_fun, Mod.wrap_fun.
          rred. iApply (@fsim_yieldR _ _ _ _ _ _ _ None). ss. iFrame. iIntros "INV _".
          iDestruct "INV" as "[[% [MEM ST]] [% [MONO H]]]".
          rred. iApply fsim_getR. iSplit; [eauto|].
          rred. iApply fsim_tauR.
          rred. iApply fsim_tauR.
          rred. iApply (@fsim_sync _ _ _ _ _ _ _ None). ss. iSplitL.
          { iSplit; auto. iSplit; auto. unfold I. iSplitL "MEM ST".
            { iExists _. iFrame. }
            { iExists _. iFrame. }
          }
          iIntros "INV _". rred. iApply fsim_tauR.
          rred. iApply fsim_ret. auto.
        }
        { iDestruct "FUEL" as "[FUEL|#DONE]"; cycle 1.
          { iDestruct (eventually_done with "DONE EVT") as "[H EVT]".
            iPoseProof (black_white_compare with "H PWHITE") as "%". exfalso. lia.
          }
          rred. iApply (@fsim_yieldR _ _ _ _ _ _ _ None). ss. iSplitR "FUEL".
          { iSplit; auto. iSplit; auto. unfold I. iSplitL "MEM ST".
            { iExists _. iFrame. }
            { iExists _. iFrame. unfold I_aux. iFrame. iExists _. iFrame. auto. }
          }
          iIntros "INV _".
          rred. iApply fsim_tauR.
          rred. rewrite close_itree_call. ss.
          unfold SCMem.compare_fun, Mod.wrap_fun. ss.
          rred. iApply (@fsim_yieldR _ _ _ _ _ _ _ None). ss. iFrame. iIntros "INV _".
          rred. iDestruct "INV" as "[[% [MEM ST]] [% [MONO H]]]".
          iApply fsim_getR. iSplit. { iFrame. }
          rred. iApply fsim_tauR.
          rred. iApply fsim_tauR.
          rred. iApply (@fsim_yieldR _ _ _ _ _ _ _ None). ss. iSplitR "FUEL".
          { iSplit; auto. iSplit; auto. unfold I. iSplitL "MEM ST".
            { iExists _. iFrame. }
            { iExists _. iFrame. }
          }
          iIntros "INV _".
          rred. iApply fsim_tauR.
          rred. iApply fsim_tauR.
          iPoseProof (Pos_Neg_annihilate with "OBL FUEL") as "> [% [H %]]".
          iClear "OBL". iPoseProof (Pos_persistent with "H") as "# OBL".
          iApply IH; eauto. iSplit; auto. iClear "INV H". auto.
        }
      }
    }
  Admitted.
End SIM.
