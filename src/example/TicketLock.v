From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
Unset Universe Checking.
From Fairness Require Export ITreeLib WFLib FairBeh NatStructs Mod pind Axioms OpenMod SCM Red IRed Wrapper WeakestAdequacy.
From Ordinal Require Export ClassicalHessenberg.


Set Implicit Arguments.


Module TicketLock.
  Definition now_serving: SCMem.val := SCMem.val_ptr (0, 0).
  Definition next_ticket: SCMem.val := SCMem.val_ptr (0, 1).

  Definition lock_loop (myticket: SCMem.val):
    itree (programE void unit) unit
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
    { apply unfold_iter_eq. }
    grind.
  Qed.

  Definition lock_fun:
    ktree (programE void unit) unit unit :=
    fun _ =>
      myticket <- (OMod.call "faa" (next_ticket, 1));;
      _ <- lock_loop myticket;;
      trigger Yield
  .

  Definition unlock_fun:
    ktree (programE void unit) unit unit :=
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
End SIM.
