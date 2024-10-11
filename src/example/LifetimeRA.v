From iris.algebra Require Import cmra agree updates.
From sflib Require Import sflib.
From Fairness Require Import Any PCM IPM IPropAux.
From Fairness Require Import TemporalLogic OwnGhost.

From iris.prelude Require Import options.

Module Lifetime.

  Definition t : ucmra := ownRA (prodR (agreeR (leibnizO Any.t)) (OneShot.t unit)).

  Section RA.

    Context `{Σ : GRA.t}.
    Context `{@GRA.inG t Σ}.
    Notation iProp := (iProp Σ).

    Definition pending (k: nat) {T : Type} (t : T) (q: Qp): iProp :=
      own k (to_agree (t↑ : leibnizO Any.t), OneShot.pending _ q).

    Definition shot (k: nat) {T : Type} (t : T) : iProp :=
      own k (to_agree (t↑ : leibnizO Any.t), OneShot.shot tt).

    Lemma shot_persistent k {T} (t : T)
      :
      shot k t -∗ □ shot k t.
    Proof. iIntros "#H !>". done. Qed.

    Global Instance Persistent_shot k {T} (t: T) : Persistent (shot k t).
    Proof. apply _. Qed.

    Lemma pending_shot k {T} (t : T)
      :
      (pending k t 1)
        -∗
        #=> (shot k t).
    Proof.
      iApply own_update.
      apply prod_update; simpl in *; try reflexivity.
      apply OneShot.pending_shot.
    Qed.

    Lemma pending_not_shot k q {T1 T2} (t1 : T1) (t2 : T2)
      :
      (pending k t1 q)
        -∗
        (shot k t2)
        -∗
        False.
    Proof.
      iIntros "H0 H1". iCombine "H0 H1" gives %[]. auto.
    Qed.

    Lemma pending_wf k q {T} (t : T)
      :
      (pending k t q)
        -∗
        (⌜(q ≤ 1)%Qp⌝).
    Proof.
      iIntros "H". iDestruct (own_valid with "H") as %[].
      auto.
    Qed.

    Lemma pending_merge k q0 q1 {T} (t : T)
      :
      (pending k t q0)
        -∗
        (pending k t q1)
        -∗
        (pending k t (q0 + q1)%Qp).
    Proof.
      iIntros "H0 H1". iCombine "H0 H1" as "H".
      rewrite -OneShot.pending_sum. done.
    Qed.

    Lemma pending_split k q0 q1 {T} (t : T)
      :
      (pending k t (q0 + q1)%Qp)
        -∗
        (pending k t q0 ∗ pending k t q1).
    Proof.
      iIntros "H". rewrite -own_op -pair_op -OneShot.pending_sum.
      rewrite <-core_id_dup; [done|apply _].
    Qed.

    Lemma alloc {T} (t : T)
      :
      ⊢ #=> (∃ k, pending k t 1).
    Proof.
      iApply own_alloc. apply pair_valid; split.
      - done.
      - apply OneShot.pending_one_wf.
    Qed.

  End RA.

End Lifetime.

Section SPROP.

  Context {STT : StateTypes}.
  Context `{sub : @SRA.subG Γ Σ}.
  Context {TLRASs : TLRAs_small STT Γ}.
  Context {TLRAS : TLRAs STT Γ Σ}.

  Context {HasLifetime : @GRA.inG Lifetime.t Γ}.

  Definition s_lft_pending {n} (k: nat) {T : Type} (t : T) (q: Qp) : sProp n :=
    (➢(to_own k (to_agree (t↑ : leibnizO _), OneShot.pending _ q)))%S.

  Lemma red_s_lft_pending n k T (t : T) q :
    ⟦s_lft_pending k t q, n⟧ = Lifetime.pending k t q.
  Proof.
    unfold s_lft_pending. red_tl. rewrite -own_to_own_eq. ss.
  Qed.

  Definition s_lft_shot {n} (k: nat) {T : Type} (t : T) : sProp n :=
    (➢(to_own k (to_agree (t↑ : leibnizO _), OneShot.shot tt)))%S.

  Lemma red_s_lft_shot n k T (t : T) :
    ⟦s_lft_shot k t, n⟧ = Lifetime.shot k t.
  Proof.
    unfold s_lft_shot. red_tl. rewrite -own_to_own_eq. ss.
  Qed.

End SPROP.

Ltac red_tl_lifetime := (try rewrite ! red_s_lft_pending;
                         try rewrite ! red_s_lft_shot
                        ).
Ltac red_tl_lifetime_s := (try setoid_rewrite red_s_lft_pending;
                           try setoid_rewrite red_s_lft_shot
                          ).

Notation "'live' γ t q" := (Lifetime.pending γ t q) (at level 90, γ, t, q at level 1) : bi_scope.
Notation "'live' γ t q" := (s_lft_pending γ t q) (at level 90, γ, t, q at level 1) : sProp_scope.
Notation "'dead' γ t" := (Lifetime.shot γ t) (at level 90, γ, t at level 1) : bi_scope.
Notation "'dead' γ t" := (s_lft_shot γ t) (at level 90, γ, t at level 1) : sProp_scope.
