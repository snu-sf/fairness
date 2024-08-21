From sflib Require Import sflib.

From iris.algebra Require Import lib.dfrac_agree.

Module Consent.
  Section CONSENT.
    Variable A: Type.

    Definition t : ucmra := optionUR (dfrac_agreeR (leibnizO A)).

    Definition vote (a: A) (q: Qp): t := Some (to_frac_agree q (a : leibnizO A)).

    Lemma vote_one_wf a: ✓ (vote a 1%Qp).
    Proof. done. Qed.

    Lemma vote_agree a0 q0 a1 q1
          (WF: ✓ (vote a0 q0 ⋅ vote a1 q1))
      :
      a0 = a1 /\ (q0 + q1 ≤ 1)%Qp.
    Proof.
      rewrite /vote -Some_op Some_valid frac_agree_op_valid_L in WF.
      des. done.
    Qed.

    Lemma vote_wf a q
          (WF: ✓ (vote a q))
      :
      (q ≤ 1)%Qp.
    Proof. rewrite /vote Some_valid pair_valid in WF. des. done. Qed.

    Lemma vote_sum a q0 q1
      :
      vote a (q0 + q1)%Qp ≡ vote a q0 ⋅ vote a q1.
    Proof. rewrite /vote -Some_op frac_agree_op //. Qed.

    Lemma vote_revolution a0 a1
      :
      (vote a0 1%Qp) ~~> (vote a1 1%Qp).
    Proof.
      rewrite /vote cmra_discrete_total_update. intros mz WF.
      apply exclusive_Some_l in WF; [|apply _].
      subst. done.
    Qed.
  End CONSENT.
  Global Opaque vote.
End Consent.
Global Arguments Consent.vote {_} _ _.

From Fairness Require Import PCM IPM FiniteMapRA.

Module ConsentP.
  Lemma vote_agree (A: Type)
        `{@GRA.inG (Consent.t A) Σ}
        (a0 a1: A) q0 q1
    :
    (OwnM (Consent.vote a0 q0) ∗ (OwnM (Consent.vote a1 q1)))
      -∗
      (⌜a0 = a1⌝).
  Proof.
    iIntros "[H0 H1]".
    iCombine "H0 H1" as "H". iOwnWf "H". apply Consent.vote_agree in H0. des. auto.
  Qed.

  Definition voted
             `{@GRA.inG (Consent.t A) Σ}
             (a: A): iProp Σ :=
    ∃ q, OwnM (Consent.vote a q).

  Lemma voted_agree (A: Type)
        `{@GRA.inG (Consent.t A) Σ}
        (a0 a1: A)
    :
    (voted a0 ∗ voted a1)
      -∗
      (⌜a0 = a1⌝).
  Proof.
    iIntros "[[% H0] [% H1]]". iApply vote_agree. iFrame "H0 H1".
  Qed.

  Lemma voted_duplicable (A: Type)
        `{@GRA.inG (Consent.t A) Σ}
        (a: A)
    :
    (voted a)
      -∗
      (voted a ∗ voted a).
  Proof.
    iIntros "[% H]". erewrite <- (Qp.div_2 q).
    rewrite Consent.vote_sum.
    iDestruct "H" as "[H0 H1]". iSplitL "H0".
    { iExists _. iFrame. }
    { iExists _. iFrame. }
  Qed.

  Definition voted_singleton
             `{@GRA.inG (@FiniteMap.t (Consent.t A)) Σ}
             k (a: A): iProp Σ :=
    ∃ q, OwnM (FiniteMap.singleton k (Consent.vote a q)).

  Lemma voted_agree_singleton (A: Type)
        `{@GRA.inG (@FiniteMap.t (Consent.t A)) Σ}
        k (a0 a1: A)
    :
    (voted_singleton k a0 ∗ voted_singleton k a1)
      -∗
      (⌜a0 = a1⌝).
  Proof.
    iIntros "[[% H0] [% H1]]".
    iCombine "H0 H1" as "H". iOwnWf "H".
    apply FiniteMap.singleton_wf in H0.
    apply Consent.vote_agree in H0. des. auto.
  Qed.

  Lemma voted_duplicable_singleton (A: Type)
        `{@GRA.inG (@FiniteMap.t (Consent.t A)) Σ}
        k (a: A)
    :
    (voted_singleton k a)
      -∗
      (voted_singleton k a ∗ voted_singleton k a).
  Proof.
    iIntros "[% H]". erewrite <- (Qp.div_2 q).
    rewrite Consent.vote_sum.
    rewrite <- FiniteMap.singleton_add.
    iDestruct "H" as "[H0 H1]". iSplitL "H0".
    { iExists _. iFrame. }
    { iExists _. iFrame. }
  Qed.
  Global Opaque voted voted_singleton.
End ConsentP.
