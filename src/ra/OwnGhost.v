From sflib Require Import sflib.
From iris.algebra Require Import gmap proofmode_classes updates gmap.
From iris.proofmode Require Import proofmode.
From Fairness Require Import IPM PCM IProp IPropAux.
From Fairness Require Import TemporalLogic.
From iris Require Import cmra.
(* Re-implemntation of [own] of Iris *)
From iris.prelude Require Import prelude options.

Module OwnG.
Section definitions.
(* FIXME: ideally, this definition should be opqaue, but thats very hard to do *)
Definition t (A : cmra) : ucmra := FiniteMap.t A.

Definition ra `{Σ : GRA.t} `{!GRA.inG (t A) Σ} (γ : nat) (a : A) : t A :=
  FiniteMap.singleton γ a.
(* Local Definition own_ra_aux : seal (@own_ra_def). Proof. by eexists. Qed.
Local Definition ra := own_ra_aux.(unseal).
Global Arguments ra {Σ A _} γ a.
Local Definition own_ra_eq : @ra = @own_ra_def := own_ra_aux.(seal_eq).
Local Instance: Params (@ra) 4 := {}. *)

Local Definition to_t_def `{Σ : GRA.t} `{!GRA.inG (t A) Σ} (γ : nat) (a : A) : iProp Σ := OwnM (ra γ a).
Local Definition to_t_aux : seal (@to_t_def). Proof. by eexists. Qed.
Definition to_t := to_t_aux.(unseal).
Global Arguments to_t {Σ A _} γ a.
Local Definition to_t_eq : @to_t = @to_t_def := to_t_aux.(seal_eq).
Local Instance: Params (@to_t) 4 := {}.
End definitions.
End OwnG.

Section lemmas.
Context `{Σ : GRA.t}.
Context `{GRA.inG (OwnG.t A) Σ}.
Implicit Types a : A.


Global Instance own_proper γ :
  Proper ((≡) ==> (⊣⊢)) (@OwnG.to_t Σ A _ γ).
Proof. rewrite OwnG.to_t_eq. solve_proper. Qed.

Lemma own_to_t_eq γ a :
  OwnG.to_t γ a = OwnM (OwnG.ra γ a).
Proof. by rewrite OwnG.to_t_eq. Qed.

Lemma own_op γ a1 a2 : OwnG.to_t γ (a1 ⋅ a2) ⊣⊢ OwnG.to_t γ a1 ∗ OwnG.to_t γ a2.
Proof. by rewrite !OwnG.to_t_eq /OwnG.to_t_def -OwnM_op /OwnG.ra FiniteMap.singleton_add. Qed.
Lemma own_mono γ a1 a2 : a2 ≼ a1 → OwnG.to_t γ a1 ⊢ OwnG.to_t γ a2.
Proof. move=> [c ->]. rewrite own_op. iIntros "[$ _]". Qed.

Global Instance own_mono' γ : Proper (flip (≼) ==> (⊢)) (@OwnG.to_t Σ A _ γ).
Proof. intros a1 a2. apply own_mono. Qed.

Lemma own_valid γ a : OwnG.to_t γ a ⊢ ⌜✓ a⌝.
Proof.
  rewrite !OwnG.to_t_eq /OwnG.to_t_def /OwnG.ra.
  iIntros "H". iOwnWf "H" as WF. iPureIntro.
  by apply FiniteMap.singleton_wf in WF.
Qed.
Lemma own_valid_2 γ a1 a2 : OwnG.to_t γ a1 -∗ OwnG.to_t γ a2 -∗ ⌜✓ (a1 ⋅ a2)⌝.
Proof.
  rewrite !OwnG.to_t_eq /OwnG.to_t_def /OwnG.ra.
  iIntros "H1 H2". iCombine "H1 H2" as "H".
  iOwnWf "H" as WF. iPureIntro.
  by apply FiniteMap.singleton_wf in WF.
Qed.
Lemma own_valid_3 γ a1 a2 a3 : OwnG.to_t γ a1 -∗ OwnG.to_t γ a2 -∗ OwnG.to_t γ a3 -∗ ⌜✓ (a1 ⋅ a2 ⋅ a3)⌝.
Proof.
  rewrite !OwnG.to_t_eq /OwnG.to_t_def /OwnG.ra.
  iIntros "H1 H2 H3". iCombine "H1 H2" as "H".
  iCombine "H H3" as "H".
  iOwnWf "H" as WF. iPureIntro.
  by apply FiniteMap.singleton_wf in WF.
Qed.
Lemma own_valid_r γ a : OwnG.to_t γ a ⊢ OwnG.to_t γ a ∗ ⌜✓ a⌝.
Proof. apply: bi.persistent_entails_r. apply own_valid. Qed.
Lemma own_valid_l γ a : OwnG.to_t γ a ⊢ ⌜✓ a⌝ ∗ OwnG.to_t γ a.
Proof. by rewrite comm -own_valid_r. Qed.

Global Instance own_core_persistent γ a : CoreId a → Persistent (OwnG.to_t γ a).
Proof.
  rewrite !OwnG.to_t_eq /OwnG.to_t_def /Persistent.
  iIntros (ID) "H".
  iDestruct (own_persistent with "H") as "#HP".
  rewrite core_id_core. iModIntro. done.
Qed.

(** ** Allocation *)
Lemma own_alloc_strong_dep (f : nat → A) (P : nat → Prop) :
  pred_infinite P →
  (∀ γ, P γ → ✓ (f γ)) →
  ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ OwnG.to_t γ (f γ).
Proof.
  intros HPinf Hf.
  rewrite <- (bupd_mono (∃ m, ⌜∃ γ, P γ ∧ m = FiniteMap.singleton γ (f γ)⌝ ∧ OwnM m)%I).
  - iIntros. iDestruct OwnM_unit as "U".
    iMod (OwnM_Upd_set (B:=λ m, ∃ γ : nat, P γ ∧ m = FiniteMap.singleton γ (f γ)) with "U") as "H".
    { eapply alloc_updateP_strong_dep.
      - exact HPinf.
      - intros ??. apply Hf.
      - ii. exists i. split; done.
    }
    iDestruct "H" as (m) "[%Hm H]".
    iModIntro. iExists _. iFrame. iPureIntro. done.
  - iIntros "[%m [%Hm H]]". des. subst.
    rewrite OwnG.to_t_eq /OwnG.to_t_def. iExists γ. iFrame.
    iPureIntro. done.
Qed.
Lemma own_alloc_cofinite_dep (f : nat → A) (G : gset nat) :
  (∀ γ, γ ∉ G → ✓ (f γ)) → ⊢ |==> ∃ γ, ⌜γ ∉ G⌝ ∗ OwnG.to_t γ (f γ).
Proof.
  intros Ha.
  apply (own_alloc_strong_dep f (λ γ, γ ∉ G)); [|done].
  apply (pred_infinite_set (C:=gset nat)).
  intros E. set (γ := fresh (G ∪ E)).
  exists γ. apply not_elem_of_union, is_fresh.
Qed.
Lemma own_alloc_dep (f : nat → A) :
  (∀ γ, ✓ (f γ)) → ⊢ |==> ∃ γ, OwnG.to_t γ (f γ).
Proof.
  iIntros (Ha).
  iMod (own_alloc_cofinite_dep f ∅) as (?) "[_ H]"; [done|].
  iModIntro. iExists _. done.
Qed.

Lemma own_alloc_strong a (P : nat → Prop) :
  pred_infinite P →
  ✓ a → ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ OwnG.to_t γ a.
Proof. intros HP Ha. eapply (own_alloc_strong_dep (λ _, a)); eauto. Qed.
Lemma own_alloc_cofinite a (G : gset nat) :
  ✓ a → ⊢ |==> ∃ γ, ⌜γ ∉ G⌝ ∗ OwnG.to_t γ a.
Proof. intros Ha. eapply (own_alloc_cofinite_dep (λ _, a)); eauto. Qed.
Lemma own_alloc a : ✓ a → ⊢ |==> ∃ γ, OwnG.to_t γ a.
Proof. intros Ha. eapply (own_alloc_dep (λ _, a)); eauto. Qed.

(** ** Frame preserving updates *)
Lemma own_updateP P γ a : a ~~>: P → OwnG.to_t γ a ⊢ |==> ∃ a', ⌜P a'⌝ ∗ OwnG.to_t γ a'.
Proof.
  intros Hupd. rewrite !OwnG.to_t_eq /OwnG.to_t_def /OwnG.ra.
  rewrite <- (bupd_mono (∃ m,
    ⌜ ∃ a', m = FiniteMap.singleton γ a' ∧ P a' ⌝ ∧ OwnM m)%I).
  - iIntros "H".
    iMod (OwnM_Upd_set with "H") as "H"; last first.
    + iDestruct "H" as (m) "[%Hm H]".
      iIntros "!>". iExists (m). iFrame.
      iPureIntro. exact Hm.
    + by apply singleton_updateP'.
  - iIntros "[%m [%Hm H]]".
    destruct Hm as [a' [-> HP]]. iExists a'. iFrame "∗%".
Qed.

Lemma own_update γ a a' : a ~~> a' → OwnG.to_t γ a ⊢ |==> OwnG.to_t γ a'.
Proof.
  intros. iIntros "?".
  iMod (own_updateP (a' =.) with "[$]") as (a'') "[-> $]".
  { by apply cmra_update_updateP. }
  done.
Qed.
Lemma own_update_2 γ a1 a2 a' :
  a1 ⋅ a2 ~~> a' → OwnG.to_t γ a1 -∗ OwnG.to_t γ a2 ==∗ OwnG.to_t γ a'.
Proof.
  iIntros (UPD) "H1 H2". iCombine "H1 H2" as "H".
  rewrite -own_op. by iApply own_update.
Qed.
Lemma own_update_3 γ a1 a2 a3 a' :
  a1 ⋅ a2 ⋅ a3 ~~> a' → OwnG.to_t γ a1 -∗ OwnG.to_t γ a2 -∗ OwnG.to_t γ a3 ==∗ OwnG.to_t γ a'.
Proof.
  iIntros (UPD) "H1 H2 H3".
  iCombine "H1 H2" as "H".
  iCombine "H H3" as "H".
  rewrite -!own_op. by iApply own_update.
Qed.
End lemmas.

Global Arguments own_valid {_ _} [_] _ _.
Global Arguments own_valid_2 {_ _} [_] _ _ _.
Global Arguments own_valid_3 {_ _} [_] _ _ _ _.
Global Arguments own_valid_l {_ _} [_] _ _.
Global Arguments own_valid_r {_ _} [_] _ _.
Global Arguments own_updateP {_ _} [_] _ _ _ _.
Global Arguments own_update {_ _} [_] _ _ _ _.
Global Arguments own_update_2 {_ _} [_] _ _ _ _ _.
Global Arguments own_update_3 {_ _} [_] _ _ _ _ _ _.

Lemma own_unit A `{i : !GRA.inG (OwnG.t (A:ucmra)) Σ} γ : ⊢ |==> OwnG.to_t γ (ε:A).
Proof.
  rewrite !OwnG.to_t_eq /OwnG.to_t_def.
  iDestruct OwnM_unit as "U".
  iMod (OwnM_Upd_set (B:=λ b, b = OwnG.ra γ ε) with "U") as "[% [%EQ H]]".
  { eapply alloc_unit_singleton_updateP.
    - apply ucmra_unit_valid.
    - apply _.
    - apply cmra_update_updateP. reflexivity.
    - intros y <-. done.
  }
  rewrite EQ. done.
Qed.

(* Section big_op_instances.
  Context `{!GRA.inG (ownRA (A:ucmra)) Σ}.

  Global Instance own_cmra_sep_homomorphism γ :
    WeakMonoidHomomorphism op Sepconj (≡) (OwnG.to_t γ).
  Proof. split; try apply _. apply own_op. Qed.

  Lemma big_opL_own {B} γ (f : nat → B → A) (l : list B) :
    l ≠ [] →
    OwnG.to_t γ ([^op list] k↦x ∈ l, f k x) ⊣⊢ [∗ list] k↦x ∈ l, OwnG.to_t γ (f k x).
  Proof. apply (big_opL_commute1 _). Qed.
  Lemma big_opM_own `{Countable K} {B} γ (g : K → B → A) (m : gmap K B) :
    m ≠ ∅ →
    OwnG.to_t γ ([^op map] k↦x ∈ m, g k x) ⊣⊢ [∗ map] k↦x ∈ m, OwnG.to_t γ (g k x).
  Proof. apply (big_opM_commute1 _). Qed.
  Lemma big_opS_own `{Countable B} γ (g : B → A) (X : gset B) :
    X ≠ ∅ →
    OwnG.to_t γ ([^op set] x ∈ X, g x) ⊣⊢ [∗ set] x ∈ X, OwnG.to_t γ (g x).
  Proof. apply (big_opS_commute1 _). Qed.
  Lemma big_opMS_own `{Countable B} γ (g : B → A) (X : gmultiset B) :
    X ≠ ∅ →
    OwnG.to_t γ ([^op mset] x ∈ X, g x) ⊣⊢ [∗ mset] x ∈ X, OwnG.to_t γ (g x).
  Proof. apply (big_opMS_commute1 _). Qed.

  Global Instance own_cmra_sep_entails_homomorphism γ :
    MonoidHomomorphism op uPred_sep (⊢) (OwnG.to_t γ).
  Proof.
    split; [split|]; try apply _.
    - intros. by rewrite own_op.
    - apply (affine _).
  Qed.

  Lemma big_opL_own_1 {B} γ (f : nat → B → A) (l : list B) :
    OwnG.to_t γ ([^op list] k↦x ∈ l, f k x) ⊢ [∗ list] k↦x ∈ l, OwnG.to_t γ (f k x).
  Proof. apply (big_opL_commute _). Qed.
  Lemma big_opM_own_1 `{Countable K} {B} γ (g : K → B → A) (m : gmap K B) :
    OwnG.to_t γ ([^op map] k↦x ∈ m, g k x) ⊢ [∗ map] k↦x ∈ m, OwnG.to_t γ (g k x).
  Proof. apply (big_opM_commute _). Qed.
  Lemma big_opS_own_1 `{Countable B} γ (g : B → A) (X : gset B) :
    OwnG.to_t γ ([^op set] x ∈ X, g x) ⊢ [∗ set] x ∈ X, OwnG.to_t γ (g x).
  Proof. apply (big_opS_commute _). Qed.
  Lemma big_opMS_own_1 `{Countable B} γ (g : B → A) (X : gmultiset B) :
    OwnG.to_t γ ([^op mset] x ∈ X, g x) ⊢ [∗ mset] x ∈ X, OwnG.to_t γ (g x).
  Proof. apply (big_opMS_commute _). Qed.
End big_op_instances. *)

(** Proofmode class instances *)
Section proofmode_instances.
  Context `{!GRA.inG (OwnG.t A) Σ}.
  Implicit Types a b : A.

  Global Instance into_sep_own γ a b1 b2 :
    IsOp a b1 b2 → IntoSep (OwnG.to_t γ a) (OwnG.to_t γ b1) (OwnG.to_t γ b2).
  Proof. intros. by rewrite /IntoSep (is_op a) own_op. Qed.
  Global Instance into_and_own p γ a b1 b2 :
    IsOp a b1 b2 → IntoAnd p (OwnG.to_t γ a) (OwnG.to_t γ b1) (OwnG.to_t γ b2).
  Proof.
    intros. rewrite /IntoAnd (is_op a) own_op. destruct p; simpl in *.
    1: iIntros "#[H1 H2] !>". 2: iIntros "[H1 H2]".
    all: iSplit; iFrame "∗#".
  Qed.

  Global Instance from_sep_own γ a b1 b2 :
    IsOp a b1 b2 → FromSep (OwnG.to_t γ a) (OwnG.to_t γ b1) (OwnG.to_t γ b2).
  Proof. intros. by rewrite /FromSep -own_op -is_op. Qed.
  (* TODO: Improve this instance with generic OwnG.to_t simplification machinery
  once https://gitlab.mpi-sws.org/iris/iris/-/issues/460 is fixed *)
  (* Cost > 50 to give priority to [combine_sep_as_fractional]. *)
  (* Global Instance combine_sep_as_own γ a b1 b2 :
    IsOp a b1 b2 → CombineSepAs (OwnG.to_t γ b1) (OwnG.to_t γ b2) (OwnG.to_t γ a) | 60.
  Proof. intros. by rewrite /CombineSepAs -own_op -is_op. Qed. *)
  (* TODO: Improve this instance with generic OwnG.to_t validity simplification
  machinery once https://gitlab.mpi-sws.org/iris/iris/-/issues/460 is fixed *)
  (* Global Instance combine_sep_gives_own γ b1 b2 :
    CombineSepGives (OwnG.to_t γ b1) (OwnG.to_t γ b2) (✓ (b1 ⋅ b2)).
  Proof.
    intros. rewrite /CombineSepGives -own_op own_valid.
    by apply: bi.persistently_intro.
  Qed. *)
  (* TODO: come back to this after sealing iProp, stdpp style. *)
  (* Global Instance from_and_own_persistent γ a b1 b2 :
    IsOp a b1 b2 → TCOr (CoreId b1) (CoreId b2) →
    FromAnd (OwnG.to_t γ a) (OwnG.to_t γ b1) (OwnG.to_t γ b2).
  Proof.
    intros ? Hb. rewrite /FromAnd (is_op a) own_op.
    destruct Hb; by rewrite persistent_and_sep.
  Qed. *)
End proofmode_instances.
