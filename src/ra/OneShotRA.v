From sflib Require Import sflib.
From iris.algebra Require Import frac agree csum updates.

Set Implicit Arguments.

(* Lemma Qp_add_lt_one : forall (q : Qp), (1 + q ≤ 1)%Qp -> False.
Proof. intros. eapply Qp.not_add_le_l. eauto. Qed. *)

Module OneShot.
  Section ONESHOT.
    Variable A: Type.

    Definition t : ucmra := optionUR (csumR fracR (agreeR (leibnizO A))).

    Definition to_pending (q : Qp) : t := Some (Cinl q).
    Definition pending (q : Qp) : t := to_pending q.
    Definition to_shot (a : A) : t := Some (Cinr (to_agree (a : leibnizO A))).
    Definition shot (a : A) : t := to_shot a.

    Global Instance shot_core_id a: CoreId (shot a).
    Proof. apply _. Qed.

    Lemma pending_one_wf: ✓ (pending 1).
    Proof. done. Qed.

    Lemma shot_wf a: ✓ (shot a).
    Proof. done. Qed.

    Lemma shot_agree a0 a1
          (WF: ✓ (shot a0 ⋅ shot a1))
      :
      a0 = a1.
    Proof. by apply to_agree_op_inv_L in WF. Qed.

    Lemma pending_not_shot a q
          (WF: ✓ (pending q ⋅ shot a))
      :
      False.
    Proof. done. Qed.

    Lemma pending_wf q
          (WF: ✓ (pending q))
      :
      (q ≤ 1)%Qp.
    Proof. done. Qed.

    Lemma pending_sum q0 q1
      :
      pending (q0 + q1)%Qp = pending q0 ⋅ pending q1.
    Proof. done. Qed.

    Lemma pending_shot a
      :
      (pending 1) ~~> (shot a).
    Proof.
      rewrite /pending /shot /t.
      rewrite cmra_discrete_total_update. intros mz WF.
      apply exclusive_Some_l in WF; [|apply _].
      subst. done.
    Qed.

    Lemma shot_dup a
      :
      (shot a) ≡ (shot a) ⋅ (shot a).
    Proof.
      rewrite /shot -Some_op -Cinr_op.
      rewrite <- core_id_dup; [done|apply _].
    Qed.

  End ONESHOT.
  Global Opaque to_shot shot to_pending pending.
End OneShot.
Global Arguments OneShot.shot {_} _.

From Fairness Require Import PCM IPM FiniteMapRA.

Module OneShotP.

  Definition pending A `{GRA.inG (OneShot.t A) Σ} (q : Qp) : iProp Σ :=
    OwnM (OneShot.pending A q).

  Definition shot `{@GRA.inG (OneShot.t A) Σ} a : iProp Σ := OwnM (OneShot.shot a).

  Global Program Instance shot_persistent (A: Type)
         `{@GRA.inG (OneShot.t A) Σ}
         (a: A)
    :
    Persistent (shot a).
  Next Obligation.
    i. iIntros "H". iPoseProof (OwnM_persistently with "H") as "# G". ss.
  Qed.

  Lemma shot_agree (A: Type)
        `{@GRA.inG (OneShot.t A) Σ}
        (a0 a1: A)
    :
    (shot a0 ∧ (shot a1))
      -∗
      (⌜a0 = a1⌝).
  Proof.
    iIntros "[# H0 # H1]".
    iCombine "H0 H1" as "H". iOwnWf "H". apply OneShot.shot_agree in H0. auto.
  Qed.

  Lemma pending_not_shot (A: Type)
        `{@GRA.inG (OneShot.t A) Σ}
        (a: A) q
    :
    (pending q ∧ (shot a))
      -∗
      False.
  Proof.
    iIntros "[H0 # H1]".
    iCombine "H0 H1" as "H". iOwnWf "H". apply OneShot.pending_not_shot in H0. auto.
  Qed.

  Global Program Instance shot_persistent_singleton (A: Type)
         `{@GRA.inG (@FiniteMap.t (OneShot.t A)) Σ}
         k (a: A)
    :
    Persistent (OwnM (FiniteMap.singleton k (OneShot.shot a))).
  Next Obligation.
    i. iIntros "H". iPoseProof (OwnM_persistently with "H") as "# G".
    rewrite FiniteMap.singleton_core_total. ss.
  Qed.

  Lemma shot_agree_singleton (A: Type)
        `{@GRA.inG (@FiniteMap.t (OneShot.t A)) Σ}
        k (a0 a1: A)
    :
    (OwnM (FiniteMap.singleton k (OneShot.shot a0)) ∧ (OwnM (FiniteMap.singleton k (OneShot.shot a1))))
      -∗
      (⌜a0 = a1⌝).
  Proof.
    iIntros "[# H0 # H1]".
    iCombine "H0 H1" as "H". iOwnWf "H".
    apply FiniteMap.singleton_wf in H0.
    apply OneShot.shot_agree in H0. auto.
  Qed.

  Lemma pending_not_shot_singleton (A: Type)
        `{@GRA.inG (@FiniteMap.t (OneShot.t A)) Σ}
        k (a: A) q
    :
    (OwnM (FiniteMap.singleton k (OneShot.pending A q)) ∧ (OwnM (FiniteMap.singleton k (OneShot.shot a))))
      -∗
      False.
  Proof.
    iIntros "[H0 # H1]".
    iCombine "H0 H1" as "H". iOwnWf "H".
    apply FiniteMap.singleton_wf in H0.
    apply OneShot.pending_not_shot in H0. auto.
  Qed.

Global Opaque shot pending.
End OneShotP.
