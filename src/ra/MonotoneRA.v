From sflib Require Import sflib.
From iris.algebra Require Import cmra updates auth mra.
From Fairness Require Import PCM IPM IPropAux OwnGhost.

From Fairness Require Import Axioms.

Require Import Program.

Set Implicit Arguments.

Variant gmon: Type :=
  | mk_gmon
      (A: Type)
      (le: A -> A -> Prop)
      (ORDER: PreOrder le)
      (a: A)
.

Variant gmon_le: gmon -> gmon -> Prop :=
  | mk_gmon_intro
      A (le: A -> A -> Prop) ORDER a0 a1 (LE: le a0 a1)
    :
    gmon_le (@mk_gmon A le ORDER a0) (@mk_gmon A le ORDER a1)
.

Program Instance gmon_le_PreOrder: PreOrder gmon_le.
Next Obligation.
  ii. destruct x. econs. reflexivity.
Qed.
Next Obligation.
  ii. dependent destruction H. dependent destruction H0.
  replace ORDER0 with ORDER.
  { econs; eauto. etrans; eauto. }
  eapply proof_irrelevance.
Qed.



Section Monotone.
  Definition monoRA: ucmra := ownRA (authUR $ mraUR gmon_le).
  Context `{GRA.inG monoRA Σ}.
  Notation iProp := (iProp Σ).

  Section LE.
    Variable k: nat.

    Variable W: Type.
    Variable le: W -> W -> Prop.
    Hypothesis le_PreOrder: PreOrder le.

    Let leR (w: W) : mra gmon_le := to_mra (mk_gmon le_PreOrder w).

    Definition monoBlack (w: W): iProp :=
      own k (● (leR w) ⋅ ◯ (leR w)).

    Definition monoWhiteExact (w: W): iProp :=
      own k (◯ (leR w)).

    Definition monoWhite (w0: W): iProp :=
      ∃ w1, monoWhiteExact w1 ∧ ⌜le w0 w1⌝.

    Lemma white_idempotent w0 w1
          (LE: le w0 w1)
      :
      ◯ (leR w0) ⋅ ◯ (leR w1) ≡ ◯ (leR w1).
    Proof. rewrite -auth_frag_op to_mra_R_op //. Qed.

    Lemma white_exact_persistent w
      :
      (monoWhiteExact w) -∗ (□ monoWhiteExact w).
    Proof.
      unfold monoBlack, monoWhiteExact.
      iIntros "H". iDestruct (persistent with "H") as "#$".
    Qed.

    Global Instance Persistent_white_exact w: Persistent (monoWhiteExact w).
    Proof. apply _. Qed.

    Lemma white_persistent w
      :
      (monoWhite w) -∗ (□ monoWhite w).
    Proof.
      iIntros "H". by iDestruct "H" as (w1) "[#$ %]".
    Qed.

    Global Instance Persistent_white w: Persistent (monoWhite w).
    Proof. apply _. Qed.

    Lemma black_persistent_white_exact w
      :
      (monoBlack w) -∗ (monoWhiteExact w).
    Proof.
      unfold monoBlack, monoWhiteExact.
      iIntros "[_ H]". auto.
    Qed.

    Lemma black_white w
      :
      (monoBlack w) -∗ (monoWhite w).
    Proof.
      unfold monoWhite. iIntros "H".
      iPoseProof (black_persistent_white_exact with "H") as "H".
      iExists _. iSplit; eauto.
    Qed.

    Lemma white_mon w0 w1
          (LE: le w0 w1)
      :
      (monoWhite w1) -∗ (monoWhite w0).
    Proof.
      unfold monoWhite. iIntros "H".
      iDestruct "H" as (w) "[$ %]".
      iPureIntro. etrans; eauto.
    Qed.

    Lemma black_updatable w0 w1
          (LE: le w0 w1)
      :
      (monoBlack w0) -∗ (#=> monoBlack w1).
    Proof.
      iIntros "H". iApply (own_update with "H").
      by apply auth_update,mra_local_update_grow.
    Qed.

    Lemma black_white_exact_compare w0 w1
      :
      (monoWhiteExact w0) -∗ (monoBlack w1) -∗ ⌜le w0 w1⌝.
    Proof.
      unfold monoWhiteExact, monoBlack.
      iIntros "H0 [H1 H2]".
      iCombine "H1 H0" gives %[WF _]%auth_both_valid_discrete.
      rewrite to_mra_included in WF.
      dependent destruction WF. auto.
    Qed.

    Lemma black_white_compare w0 w1
      :
      (monoWhite w0) -∗ (monoBlack w1) -∗ ⌜le w0 w1⌝.
    Proof.
      unfold monoWhite.
      iIntros "H0 H1". iDestruct "H0" as (w) "[H0 %]".
      iPoseProof (black_white_exact_compare with "H0 H1") as "%".
      iPureIntro. etrans; eauto.
    Qed.
  End LE.

  Lemma monoBlack_alloc
        (W: Type)
        (le: W -> W -> Prop)
        (le_PreOrder: PreOrder le)
        (w: W)
    :
    ⊢ #=> (∃ k, monoBlack k le_PreOrder w).
  Proof.
    iMod own_alloc as (k) "H".
    { eapply auth_both_valid_discrete. split; [|done].
      reflexivity.
    }
    iModIntro. iExists k. auto.
  Qed.
End Monotone.

From Fairness Require Import TemporalLogic.

Section MONOTONE_SPROP.

  Context {STT : StateTypes}.
  Context `{sub : @SRA.subG Γ Σ}.
  Context {TLRASs : TLRAs_small STT Γ}.
  Context {TLRAS : TLRAs STT Γ Σ}.

  Context `{HasMono : @GRA.inG monoRA Γ}.

  Variable k: nat.

  Variable W: Type.
  Variable le: W -> W -> Prop.
  Hypothesis le_PreOrder: PreOrder le.

  Let leR (w: W) : mra gmon_le := to_mra (mk_gmon le_PreOrder w).


  Definition s_monoBlack {n} (w : W) : sProp n :=
    (➢(to_own k (● (leR w) ⋅ ◯ (leR w))))%S.

  Lemma red_s_monoBlack n (w : W) :
    ⟦s_monoBlack w, n⟧ = monoBlack k _ w.
  Proof.
    unfold s_monoBlack. red_tl. rewrite -own_to_own_eq. ss.
  Qed.

  Definition s_monoWhite {n} (w1 : W) : sProp n :=
    (∃ w2 : τ{W, n},
      ➢(to_own k (◯ (leR w2)))
      ∧ ⌜le w1 w2⌝)%S.

  Lemma red_s_monoWhite n (w : W) :
    ⟦s_monoWhite w, n⟧ = monoWhite k _ w.
  Proof.
    unfold s_monoWhite, monoWhite. red_tl. ss. f_equal. extensionalities.
    red_tl. rewrite -own_to_own_eq. unfold monoWhiteExact. ss.
  Qed.

End MONOTONE_SPROP.

Ltac red_tl_monoRA :=
  (try rewrite ! red_s_monoBlack;
  try rewrite ! red_s_monoWhite).

Section MAP.
  Definition partial_map_le {A B} (f0 f1: A -> option B): Prop :=
    forall a b (SOME: f0 a = Some b), f1 a = Some b.

  Global Program Instance partial_map_PreOrder A B: PreOrder (@partial_map_le A B).
  Next Obligation.
  Proof.
    ii. auto.
  Qed.
  Next Obligation.
  Proof.
    ii. eapply H0. eapply H. auto.
  Qed.

  Definition partial_map_empty {A B} : A -> option B :=
    fun _ => None.

  Definition partial_map_update {A B} (a: A) (b: B) (f: A -> option B):
    A -> option B :=
    fun a' => if (excluded_middle_informative (a' = a)) then Some b else (f a').

  Definition partial_map_singleton {A B} (a: A) (b: B): A -> option B :=
    partial_map_update a b (@partial_map_empty A B).

  Definition partial_map_update_le {A B} (a: A) (b: B) (f: A -> option B)
             (NONE: f a = None)
    :
    partial_map_le f (partial_map_update a b f).
  Proof.
    ii. unfold partial_map_update. des_ifs.
  Qed.

  Definition partial_map_update_le_singleton A B (a: A) (b: B) (f: A -> option B)
             (NONE: f a = None)
    :
    partial_map_le (partial_map_singleton a b) (partial_map_update a b f).
  Proof.
    ii. unfold partial_map_singleton, partial_map_update in *. des_ifs.
  Qed.

  Lemma partial_map_singleton_le_iff A B (a: A) (b: B) f
    :
    partial_map_le (partial_map_singleton a b) f <-> (f a = Some b).
  Proof.
    split.
    { i. eapply H. unfold partial_map_singleton, partial_map_update. des_ifs. }
    { ii. unfold partial_map_singleton, partial_map_update in *. des_ifs. }
  Qed.
End MAP.
