From iris.algebra Require Import cmra updates.
From sflib Require Import sflib.
From Fairness Require Import Any PCM IPM IPropAux.
From Fairness Require Import MonotoneRA.
From Fairness Require Import TemporalLogic OwnGhost.

From iris.prelude Require Import options.

Module OneShots.

  Definition t (A : Type) : ucmra := OwnG.t (OneShot.t A).

  Section RA.

    Context `{Σ : GRA.t}.
    Context `{@GRA.inG (t A) Σ}.
    Notation iProp := (iProp Σ).

    Definition pending (k: nat) (q: Qp): iProp :=
      OwnG.to_t k (OneShot.pending _ q).

    Definition shot (k: nat) (a : A) : iProp :=
      OwnG.to_t k (OneShot.shot a).

    Lemma shot_persistent k a
      :
      shot k a -∗ □ shot k a.
    Proof. iIntros "#H !>". done. Qed.

    Global Instance Persistent_shot k a : Persistent (shot k a).
    Proof. apply _. Qed.

    Lemma pending_shot k a
      :
      (pending k 1)
        -∗
        #=> (shot k a).
    Proof. iApply own_update. apply OneShot.pending_shot. Qed.

    Lemma pending_not_shot k q a
      :
      (pending k q)
        -∗
        (shot k a)
        -∗
        False.
    Proof.
      iIntros "H0 H1". iCombine "H0 H1" as "H".
      iDestruct (own_valid with "H") as %[].
    Qed.

    Lemma pending_wf k q
      :
      (pending k q)
        -∗
        (⌜(q ≤ 1)%Qp⌝).
    Proof.
      iIntros "H".
      iDestruct (own_valid with "H") as %WF.
      auto.
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
      by rewrite -OneShot.pending_sum.
    Qed.

    Lemma pending_split k q0 q1
      :
      (pending k (q0 + q1)%Qp)
        -∗
        (pending k q0 ∗ pending k q1).
    Proof.
      iIntros "H". by rewrite -own_op -OneShot.pending_sum.
    Qed.

    Lemma shot_agree k a b
      :
      (shot k a)
        -∗
        (shot k b)
        -∗
        (⌜a = b⌝).
    Proof.
      iIntros "A B". iCombine "A B" as "AB".
      iDestruct (own_valid with "AB") as %EQ.
      apply OneShot.shot_agree in EQ. auto.
    Qed.

    Lemma alloc
      :
      ⊢ #=> (∃ k, pending k 1).
    Proof. iApply own_alloc. apply OneShot.pending_one_wf. Qed.
  End RA.

End OneShots.

Section SPROP.

  Context {STT : StateTypes}.
  Context `{sub : @SRA.subG Γ Σ}.
  Context {TLRASs : TLRAs_small STT Γ}.
  Context {TLRAS : TLRAs STT Γ Σ}.

  Context `{HasOneShots : @GRA.inG (OneShots.t A) Γ}.

  Definition s_oneshots_pending {n} (k: nat) (q: Qp) : sProp n :=
    (➢(OwnG.ra k (OneShot.pending _ q)))%S.

  Lemma red_s_oneshots_pending n k q :
    ⟦s_oneshots_pending k q, n⟧ = OneShots.pending k q.
  Proof.
    unfold s_oneshots_pending. red_tl. rewrite -own_to_t_eq. ss.
  Qed.

  Definition s_oneshots_shot {n} (k: nat) a : sProp n :=
    (➢(OwnG.ra k (OneShot.shot a)))%S.

  Lemma red_s_oneshots_shot n k a :
    ⟦s_oneshots_shot k a, n⟧ = OneShots.shot k a.
  Proof.
    unfold s_oneshots_shot. red_tl. rewrite -own_to_t_eq. ss.
  Qed.

End SPROP.

Ltac red_tl_oneshots := (try rewrite ! red_s_oneshots_pending;
                         try rewrite ! red_s_oneshots_shot
                        ).

Notation "'△' γ q" := (OneShots.pending γ q) (at level 90, γ, q at level 1) : bi_scope.
Notation "'△' γ q" := (s_oneshots_pending γ q) (at level 90, γ, q at level 1) : sProp_scope.
Notation "'▿' γ a" := (OneShots.shot γ a) (at level 90, γ, a at level 1) : bi_scope.
Notation "'▿' γ a" := (s_oneshots_shot γ a) (at level 90, γ, a at level 1) : sProp_scope.
