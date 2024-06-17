From sflib Require Import sflib.
From Fairness Require Import Any PCM IProp IPM IPropAux.
From Fairness Require Import MonotoneRA.
From Fairness Require Import TemporalLogic.

Module OneShots.

  Definition t (A : Type) : URA.t := @FiniteMap.t (OneShot.t A).

  Section RA.

    Context `{Σ : GRA.t}.
    Context `{@GRA.inG (t A) Σ}.

    Definition pending (k: nat) (q: Qp): iProp :=
      OwnM (FiniteMap.singleton k (OneShot.pending _ q)).

    Definition shot (k: nat) (a : A) : iProp :=
      OwnM (FiniteMap.singleton k (OneShot.shot a)).

    Lemma shot_persistent k a
      :
      shot k a -∗ □ shot k a.
    Proof.
      iIntros "H". iPoseProof (own_persistent with "H") as "H".
      rewrite FiniteMap.singleton_core. auto.
    Qed.

    Global Program Instance Persistent_shot k a : Persistent (shot k a).
    Next Obligation.
    Proof.
      i. iIntros "POS". iPoseProof (shot_persistent with "POS") as "POS". auto.
    Qed.

    Lemma pending_shot k a
      :
      (pending k 1)
        -∗
        #=> (shot k a).
    Proof.
      iApply OwnM_Upd. eapply FiniteMap.singleton_updatable.
      { apply OneShot.pending_shot. }
    Qed.

    Lemma pending_not_shot k q a
      :
      (pending k q)
        -∗
        (shot k a)
        -∗
        False.
    Proof.
      iIntros "H0 H1". iCombine "H0 H1" as "H".
      iOwnWf "H". rewrite FiniteMap.singleton_add in H0.
      rewrite FiniteMap.singleton_wf in H0. ur in H0. exfalso. auto.
    Qed.

    Lemma pending_wf k q
      :
      (pending k q)
        -∗
        (⌜(q ≤ 1)%Qp⌝).
    Proof.
      iIntros "H". iOwnWf "H".
      rewrite FiniteMap.singleton_wf in H0. ur in H0. auto.
    Qed.

    Lemma pending_merge k q0 q1
      :
      (pending k q0)
        -∗
        (pending k q1)
        -∗
        (pending k (q0 + q1)%Qp).
    Proof.
      iIntros "H0 H1". iCombine "H0 H1" as "H".
      rewrite FiniteMap.singleton_add. ur. ss.
    Qed.

    Lemma pending_split k q0 q1
      :
      (pending k (q0 + q1)%Qp)
        -∗
        (pending k q0 ∗ pending k q1).
    Proof.
      iIntros "H".
      iPoseProof (OwnM_extends with "H") as "[H0 H1]"; [|iSplitL "H0"; [iApply "H0"|iApply "H1"]].
      { rewrite FiniteMap.singleton_add. rewrite OneShot.pending_sum. ur. reflexivity. }
    Qed.

    Lemma alloc
      :
      ⊢ #=> (∃ k, pending k 1).
    Proof.
      iPoseProof (@OwnM_unit _ _ H) as "H".
      iPoseProof (OwnM_Upd_set with "H") as "> H0".
      { eapply FiniteMap.singleton_alloc. instantiate (1:=(OneShot.pending A 1)).
        apply OneShot.pending_one_wf.
      }
      iDestruct "H0" as "[% [% H0]]".
      des. subst. iModIntro. iExists _. iFrame.
    Qed.

  End RA.

End OneShots.

Section SPROP.

  Context {STT : StateTypes}.
  Context `{sub : @SRA.subG Γ Σ}.
  Context {TLRASs : TLRAs_small STT Γ}.
  Context {TLRAS : TLRAs STT Γ Σ}.

  Context `{HasOneShots : @GRA.inG (OneShots.t A) Γ}.

  Definition s_oneshots_pending {n} (k: nat) (q: Qp) : sProp n :=
    (➢(FiniteMap.singleton k (OneShot.pending _ q)))%S.

  Lemma red_s_oneshots_pending n k q :
    ⟦s_oneshots_pending k q, n⟧ = OneShots.pending k q.
  Proof.
    unfold s_oneshots_pending. red_tl. ss.
  Qed.

  Definition s_oneshots_shot {n} (k: nat) a : sProp n :=
    (➢(FiniteMap.singleton k (OneShot.shot a)))%S.

  Lemma red_s_oneshots_shot n k a :
    ⟦s_oneshots_shot k a, n⟧ = OneShots.shot k a.
  Proof.
    unfold s_oneshots_shot. red_tl. ss.
  Qed.

End SPROP.

Ltac red_tl_oneshots := (try rewrite ! red_s_oneshots_pending;
                         try rewrite ! red_s_oneshots_shot
                        ).

Notation "'△' γ q" := (OneShots.pending γ q) (at level 90, γ, q at level 1) : bi_scope.
Notation "'△' γ q" := (s_oneshots_pending γ q) (at level 90, γ, q at level 1) : sProp_scope.
Notation "'▿' γ a" := (OneShots.shot γ a) (at level 90, γ, a at level 1) : bi_scope.
Notation "'▿' γ a" := (s_oneshots_shot γ a) (at level 90, γ, a at level 1) : sProp_scope.
