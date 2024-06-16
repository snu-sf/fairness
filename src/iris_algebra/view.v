From Fairness Require Import updates local_updates frac dfrac agree cmra.
From Fairness Require Import proofmode_classes big_op.
From iris.prelude Require Import prelude options.

Local Open Scope iris_algebra_scope.

(** The view camera with fractional authoritative elements *)
(** The view camera, which is reminiscent of the views framework, is used to
  provide a logical/"small-footprint" "view" of some "large-footprint" piece of
  data, which can be shared in the separation logic sense, i.e., different parts
  of the data can be separately owned by different functions or threads. This is
  achieved using the two elements of the view camera:

- The authoritative element [●V a], which describes the data under consideration.
- The fragment [◯V b], which provides a logical view of the data [a].

To enable sharing of the fragments, the type of fragments is equipped with a
camera structure so ownership of fragments can be split. Concretely, fragments
enjoy the rule [◯V (b1 ⋅ b2) = ◯V b1 ⋅ ◯V b2].

To enable sharing of the authoritative element [●V{dq} a], it is equipped with a
discardable fraction [dq]. Updates are only possible with the full authoritative
element [●V a] (syntax for [●V{#1} a]]), while fractional authoritative elements
have agreement, i.e., [✓ (●V{dq1} a1 ⋅ ●V{dq2} a2) → a1 = a2]. *)

(** * The view relation *)
(** To relate the authoritative element [a] to its possible fragments [b], the
view camera is parametrized by a (step-indexed) relation [view_rel a b]. This
relation should be a.) closed under smaller step-indexes [n], b.) non-expansive
w.r.t. the argument [a], c.) closed under smaller [b] (which implies
non-expansiveness w.r.t. [b]), and d.) ensure validity of the argument [b].

Note 1: Instead of requiring both a step-indexed and a non-step-indexed version
of the relation (like cameras do for validity), we use [∀, view_rel n] as the
non-step-indexed version. This is anyway necessary when using [≼] as the
relation (like the authoritative camera does) as its non-step-indexed version
is not equivalent to [∀, x ≼ y].

Note 2: The view relation is defined as a canonical structure so that given a
relation [nat → A → B → Prop], the instance with the laws can be inferred. We do
not use type classes for this purpose because cameras themselves are represented
using canonical structures. It has proven fragile for a canonical structure
instance to take a type class as a parameter (in this case, [viewR] would need
to take a class with the view relation laws). *)
Structure view_rel (A : Type) (B : ucmra) := ViewRel {
  view_rel_holds :> A → B → Prop;
  view_rel_mono a1 a2 b1 b2 :
    view_rel_holds a1 b1 →
    a1 = a2 →
    b2 ≼ b1 →
    view_rel_holds a2 b2;
  view_rel_valid a b :
    view_rel_holds a b → ✓ b;
  view_rel_unit :
    ∃ a, view_rel_holds a ε
}.
Global Arguments ViewRel {_ _} _ _.
Global Arguments view_rel_holds {_ _} _ _ _.
Global Instance: Params (@view_rel_holds) 4 := {}.

Global Instance view_rel_proper {A B} (rel : view_rel A B) :
  Proper ((=) ==> (=) ==> iff) rel.
Proof. intros a1 a2 -> b1 b2 ->. done. Qed.

(** * Definition of the view camera *)
(** To make use of the lemmas provided in this file, elements of [view] should
always be constructed using [●V] and [◯V], and never using the constructor
[View]. *)
Record view {A B} (rel : A → B → Prop) :=
  View { view_auth_proj : option (dfrac * agree A) ; view_frag_proj : B }.
Add Printing Constructor view.
Global Arguments View {_ _ _} _ _.
Global Arguments view_auth_proj {_ _ _} _.
Global Arguments view_frag_proj {_ _ _} _.
Global Instance: Params (@View) 3 := {}.
Global Instance: Params (@view_auth_proj) 3 := {}.
Global Instance: Params (@view_frag_proj) 3 := {}.

Definition view_auth {A B} {rel : view_rel A B} (dq : dfrac) (a : A) : view rel :=
  View (Some (dq, to_agree a)) ε.
Definition view_frag {A B} {rel : view_rel A B} (b : B) : view rel := View None b.
Global Typeclasses Opaque view_auth view_frag.

Global Instance: Params (@view_auth) 3 := {}.
Global Instance: Params (@view_frag) 3 := {}.

Notation "●V{ dq } a" := (view_auth dq a) (at level 20, format "●V{ dq }  a") : iris_algebra_scope.
Notation "●V{# q } a" := (view_auth (DfracOwn q) a) (at level 20, format "●V{# q }  a") : iris_algebra_scope.
Notation "●V□ a" := (view_auth DfracDiscarded a) (at level 20, format "●V□  a") : iris_algebra_scope.
Notation "●V a" := (view_auth (DfracOwn 1) a) (at level 20) : iris_algebra_scope.
Notation "◯V a" := (view_frag a) (at level 20) : iris_algebra_scope.

(** * The OFE structure *)
(** We omit the usual [equivI] lemma because it is hard to state a suitably
general version in terms of [●V] and [◯V], and because such a lemma has never
been needed in practice. *)


(** * The camera structure *)
Section cmra.
  Context {A B} (rel : view_rel A B).
  Implicit Types a : A.
  Implicit Types ag : option (dfrac * agree A).
  Implicit Types b : B.
  Implicit Types x y : view rel.
  Implicit Types q : frac.
  Implicit Types dq : dfrac.

  Global Instance view_auth_proper dq : Proper ((=) ==> (=)) (@view_auth A B rel dq).
  Proof. solve_proper. Qed.
  Global Instance view_frag_proper : Proper ((=) ==> (=)) (@view_frag A B rel).
  Proof. intros ??->. done. Qed.


  Global Instance view_auth_inj : Inj2 (=) (=) (=) (@view_auth A B rel).
  Proof.
    intros dq1 a1 dq2 a2 Hag; inversion Hag as [].
    done.
  Qed.
  Global Instance view_frag_inj : Inj (=) (=) (@view_frag A B rel).
  Proof. intros ?? EQ. by inversion EQ. Qed.

  Local Instance view_valid_instance : Valid (view rel) := λ x,
    match view_auth_proj x with
    | Some (dq, ag) =>
       ✓ dq ∧ (∃ a, ag = to_agree a ∧ rel a (view_frag_proj x))
    | None => ∃ a, rel a (view_frag_proj x)
    end.
  Local Instance view_pcore_instance : PCore (view rel) := λ x,
    Some (View (core (view_auth_proj x)) (core (view_frag_proj x))).
  Local Instance view_op_instance : Op (view rel) := λ x y,
    View (view_auth_proj x ⋅ view_auth_proj y) (view_frag_proj x ⋅ view_frag_proj y).

  Local Definition view_valid_eq :
    valid = λ x,
      match view_auth_proj x with
      | Some (dq, ag) =>
         ✓ dq ∧ (∃ a, ag = to_agree a ∧ rel a (view_frag_proj x))
      | None => ∃ a, rel a (view_frag_proj x)
      end := eq_refl _.
  Local Definition view_pcore_eq :
      pcore = λ x, Some (View (core (view_auth_proj x)) (core (view_frag_proj x))) :=
    eq_refl _.
  Local Definition view_core_eq :
      core = λ x, View (core (view_auth_proj x)) (core (view_frag_proj x)) :=
    eq_refl _.
  Local Definition view_op_eq :
      op = λ x y, View (view_auth_proj x ⋅ view_auth_proj y)
                       (view_frag_proj x ⋅ view_frag_proj y) :=
    eq_refl _.

  Lemma view_cmra_mixin : CmraMixin (view rel).
  Proof.
    apply (iso_cmra_mixin_restrict_validity
      (λ x : option (dfrac * agree A) * B, View x.1 x.2)
      (λ x, (view_auth_proj x, view_frag_proj x))); try done.
    - intros [y1 y1b] [x1 x1b]. simpl. naive_solver.
    - intros [x b]. simpl. done.
    - intros [x b]. by rewrite /= pair_pcore !cmra_pcore_core.
    - intros [[[dq ag]|] b]; rewrite /= view_valid_eq /=.
      + intros (?&a&->&?). repeat split; simpl; [done|by apply to_agree_valid|]. by eapply view_rel_valid.
      + intros [a ?]. repeat split; simpl. by eapply view_rel_valid.
    - rewrite view_valid_eq. intros [[[q1 ag1]|] b1] [[[q2 ag2]|] b2]; simpl.
      + intros [?%cmra_valid_op_l (a & Haga & ?)]. split; [done|].
        assert (ag1 = ag2) as Ha12.
        { apply agree_op_inv. rewrite Haga. apply to_agree_valid. }
        exists a. split; [by rewrite -Haga -Ha12 agree_idemp|].
        apply view_rel_mono with a (b1 ⋅ b2); eauto using cmra_included_l.
      + intros [? (a & Haga & ?)]. split; [done|]. exists a; split; [done|].
        apply view_rel_mono with a (b1 ⋅ b2); eauto using cmra_included_l.
      + intros [? (a & Haga & ?)]. exists a.
        apply view_rel_mono with a (b1 ⋅ b2); eauto using cmra_included_l.
      + intros [a ?]. exists a.
        apply view_rel_mono with a (b1 ⋅ b2); eauto using cmra_included_l.
  Qed.
  Canonical Structure viewR := Cmra (view rel) view_cmra_mixin.

  (* Global Instance view_auth_discrete dq a :
    Discrete a → Discrete (ε : B) → Discrete (●V{dq} a : view rel).
  Proof. intros. apply View_discrete; apply _. Qed.
  Global Instance view_frag_discrete b :
    Discrete b → Discrete (◯V b : view rel).
  Proof. intros. apply View_discrete; apply _. Qed.
  Global Instance view_cmra_discrete :
    OfeDiscrete A → CmraDiscrete B → ViewRelDiscrete rel →
    CmraDiscrete viewR.
  Proof.
    split; [apply _|]=> -[[[dq ag]|] b]; rewrite view_valid_eq view_valid_eq /=.
    - rewrite -cmra_discrete_valid_iff.
      setoid_rewrite <-(discrete_iff _ ag). naive_solver.
    - naive_solver.
  Qed. *)

  Local Instance view_empty_instance : Unit (view rel) := View ε ε.
  Lemma view_ucmra_mixin : UcmraMixin (view rel).
  Proof.
    split; simpl.
    - rewrite view_valid_eq /=. apply view_rel_unit.
    - intros [x b]. rewrite view_op_eq. f_equal.
      all: by rewrite /= left_id.
    - rewrite view_pcore_eq. f_equal. rewrite !core_id_core. done.
  Qed.
  Canonical Structure viewUR := Ucmra (view rel) view_ucmra_mixin.

  (** Operation *)
  Lemma view_auth_dfrac_op dq1 dq2 a : ●V{dq1 ⋅ dq2} a = ●V{dq1} a ⋅ ●V{dq2} a.
  Proof.
    unfold op, view_op_instance, view_auth. simpl.
    f_equal; last by rewrite left_id.
    by rewrite -Some_op -pair_op agree_idemp.
  Qed.
  Global Instance view_auth_dfrac_is_op dq dq1 dq2 a :
    IsOp dq dq1 dq2 → IsOp' (●V{dq} a) (●V{dq1} a) (●V{dq2} a).
  Proof. rewrite /IsOp' /IsOp => ->. by rewrite -view_auth_dfrac_op. Qed.

  Lemma view_frag_op b1 b2 : ◯V (b1 ⋅ b2) = ◯V b1 ⋅ ◯V b2.
  Proof. done. Qed.
  Lemma view_frag_mono b1 b2 : b1 ≼ b2 → ◯V b1 ≼ ◯V b2.
  Proof. intros [c ->]. by rewrite view_frag_op. Qed.
  Lemma view_frag_core b : core (◯V b) = ◯V (core b).
  Proof. done. Qed.
  Lemma view_both_core_discarded a b :
    core (●V□ a ⋅ ◯V b) = ●V□ a ⋅ ◯V (core b).
  Proof. rewrite view_core_eq view_op_eq /= !left_id //. Qed.
  Lemma view_both_core_frac q a b :
    core (●V{#q} a ⋅ ◯V b) = ◯V (core b).
  Proof. rewrite view_core_eq view_op_eq /= !left_id //. Qed.

  Global Instance view_auth_core_id a : CoreId (●V□ a).
  Proof. unfold view_auth,CoreId. rewrite view_pcore_eq. do 2 f_equal; simpl; auto. apply: core_id_core. Qed.
  Global Instance view_frag_core_id b : CoreId b → CoreId (◯V b).
  Proof. intro Hb. unfold view_frag,CoreId. rewrite view_pcore_eq. do 2 f_equal; simpl; auto. apply: core_id_core. Qed.
  Global Instance view_both_core_id a b : CoreId b → CoreId (●V□ a ⋅ ◯V b).
  Proof. intro Hb. unfold view_auth,view_frag,CoreId. rewrite view_pcore_eq view_op_eq. do 2 f_equal; simpl; auto. rewrite left_id. apply: core_id_core. Qed.
  Global Instance view_frag_is_op b b1 b2 :
    IsOp b b1 b2 → IsOp' (◯V b) (◯V b1) (◯V b2).
  Proof. intros IsOp. unfold IsOp',proofmode_classes.IsOp. unfold view_frag. rewrite view_op_eq. f_equal.
  simpl. done. Qed.
  Global Instance view_frag_sep_homomorphism :
    MonoidHomomorphism op op (=) (@view_frag A B rel).
  Proof. by split; [split; try apply _|]. Qed.

  Lemma big_opL_view_frag {C} (g : nat → C → B) (l : list C) :
    (◯V [^op list] k↦x ∈ l, g k x) = [^op list] k↦x ∈ l, ◯V (g k x).
  Proof. apply (big_opL_commute _). Qed.
  Lemma big_opM_view_frag `{Countable K} {C} (g : K → C → B) (m : gmap K C) :
    (◯V [^op map] k↦x ∈ m, g k x) = [^op map] k↦x ∈ m, ◯V (g k x).
  Proof. apply (big_opM_commute _). Qed.
  Lemma big_opS_view_frag `{Countable C} (g : C → B) (X : gset C) :
    (◯V [^op set] x ∈ X, g x) = [^op set] x ∈ X, ◯V (g x).
  Proof. apply (big_opS_commute _). Qed.
  Lemma big_opMS_view_frag `{Countable C} (g : C → B) (X : gmultiset C) :
    (◯V [^op mset] x ∈ X, g x) = [^op mset] x ∈ X, ◯V (g x).
  Proof. apply (big_opMS_commute _). Qed.

  (** Validity *)
  Lemma view_auth_dfrac_op_inv dq1 a1 dq2 a2 :
    ✓ (●V{dq1} a1 ⋅ ●V{dq2} a2) → a1 = a2.
  Proof.
    rewrite /op /view_op_instance /= left_id -Some_op -pair_op view_valid_eq /=.
    intros (?&?& Eq &?). apply (inj to_agree), agree_op_inv. rewrite Eq.
    apply to_agree_valid.
  Qed.
  Lemma view_auth_dfrac_op_inv_L dq1 a1 dq2 a2 :
    ✓ (●V{dq1} a1 ⋅ ●V{dq2} a2) → a1 = a2.
  Proof. by intros ?%view_auth_dfrac_op_inv. Qed.

  Lemma view_auth_dfrac_valid dq a : ✓ (●V{dq} a) ↔ ✓dq ∧ rel a ε.
  Proof.
    rewrite view_valid_eq /=. apply and_iff_compat_l. split; [|by eauto].
    by intros [? [->%(inj to_agree) ?]].
  Qed.
  Lemma view_auth_valid a : ✓ (●V a) ↔ rel a ε.
  Proof. rewrite view_auth_dfrac_valid. split; [naive_solver|done]. Qed.

  Lemma view_auth_dfrac_op_valid dq1 dq2 a1 a2 :
    ✓ (●V{dq1} a1 ⋅ ●V{dq2} a2) ↔ ✓(dq1 ⋅ dq2) ∧ a1 = a2 ∧ rel a1 ε.
  Proof.
    split.
    - intros Hval. assert (a1 = a2) as Ha by eauto using view_auth_dfrac_op_inv.
      revert Hval. rewrite Ha -view_auth_dfrac_op view_auth_dfrac_valid. naive_solver.
    - intros (?&->&?). by rewrite -view_auth_dfrac_op view_auth_dfrac_valid.
  Qed.

  Lemma view_frag_valid b : ✓ (◯V b) ↔ ∃ a, rel a b.
  Proof. done. Qed.

  Lemma view_both_dfrac_valid dq a b :
    ✓ (●V{dq} a ⋅ ◯V b) ↔ ✓dq ∧ rel a b.
  Proof.
    rewrite view_valid_eq /=. apply and_iff_compat_l.
    setoid_rewrite (left_id _ _ b). split; [|by eauto].
    by intros [?[->%(inj to_agree)]].
  Qed.
  Lemma view_both_valid a b : ✓ (●V a ⋅ ◯V b) ↔ rel a b.
  Proof. rewrite view_both_dfrac_valid. split; [naive_solver|done]. Qed.

  Lemma view_auth_op_valid a1 a2 : ✓ (●V a1 ⋅ ●V a2) ↔ False.
  Proof. rewrite view_auth_dfrac_op_valid. naive_solver. Qed.

  (** Inclusion *)
  Lemma view_auth_dfrac_included dq1 dq2 a1 a2 b :
    ●V{dq1} a1 ≼ ●V{dq2} a2 ⋅ ◯V b ↔ (dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 = a2.
  Proof.
    split.
    - intros [[[[dqf agf]|] bf] ?]; simplify_eq/=.
      + split; [eauto|]. apply to_agree_included. by exists agf.
      + split; [right; done|]. by apply (inj to_agree).
    - intros [[[? ->]| ->] ->].
      + rewrite view_auth_dfrac_op -assoc. apply cmra_included_l.
      + apply cmra_included_l.
  Qed.
  Lemma view_auth_included a1 a2 b :
    ●V a1 ≼ ●V a2 ⋅ ◯V b ↔ a1 = a2.
  Proof. rewrite view_auth_dfrac_included. naive_solver. Qed.

  Lemma view_frag_included p a b1 b2 :
    ◯V b1 ≼ ●V{p} a ⋅ ◯V b2 ↔ b1 ≼ b2.
  Proof.
    split.
    - intros [xf Hb]; simpl in *.
      revert Hb. rewrite view_op_eq /=. rewrite left_id. injection 1. intros. by exists (view_frag_proj xf).
    - intros [bf ->]. rewrite comm view_frag_op -assoc. apply cmra_included_l.
  Qed.

  (** The weaker [view_both_included] lemmas below are a consequence of the
  [view_auth_included] and [view_frag_included] lemmas above. *)
  Lemma view_both_dfrac_included dq1 dq2 a1 a2 b1 b2 :
    ●V{dq1} a1 ⋅ ◯V b1 ≼ ●V{dq2} a2 ⋅ ◯V b2 ↔
      (dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 = a2 ∧ b1 ≼ b2.
  Proof.
    split.
    - intros. rewrite assoc. split.
      + rewrite -view_auth_dfrac_included. by etrans; [apply cmra_included_l|].
      + rewrite -view_frag_included. by etrans; [apply cmra_included_r|].
    - intros (?&->&?bf&->). rewrite (comm _ b1) view_frag_op assoc.
      by apply cmra_mono_r, view_auth_dfrac_included.
  Qed.
  Lemma view_both_included a1 a2 b1 b2 :
    ●V a1 ⋅ ◯V b1 ≼ ●V a2 ⋅ ◯V b2 ↔ a1 = a2 ∧ b1 ≼ b2.
  Proof. rewrite view_both_dfrac_included. naive_solver. Qed.

  (** Updates *)

  (** Note that we quantify over a frame [bf], and since conceptually [rel a b]
      means "[b] is a Valid fragment to be part of [a]", there is another implicit
      frame quantification inside [rel] (usually because [rel] is defined via [≼]
      which contains an existential quantifier). The difference between the two
      frames is that the frame quantified inside [rel] may change but [bf] has
      to be preserved. It is not clear if it is possible to avoid this. *)
  Lemma view_updateP a b Pab :
    (∀ bf, rel a (b ⋅ bf) → ∃ a' b', Pab a' b' ∧ rel a' (b' ⋅ bf)) →
    ●V a ⋅ ◯V b ~~>: λ k, ∃ a' b', k = ●V a' ⋅ ◯V b' ∧ Pab a' b'.
  Proof.
    intros Hup; apply cmra_total_updateP. intros [[[dq ag]|] bf] V; simpl in V.
    all: rewrite view_op_eq /= view_valid_eq /= in V.
    all: destruct V as [V AG].
    { apply exclusive_l in V; last by apply dfrac_full_exclusive. done. }
    revert AG.
    intros (a0 & <-%(inj to_agree) & Hrel).
    rewrite !left_id in Hrel. apply Hup in Hrel as (a' & b' & Hab' & Hrel).
    eexists; split.
    - naive_solver.
    - split; simpl; [done|].
      exists a'; split; [done|]. by rewrite left_id.
  Qed.

  Lemma view_update a b a' b' :
    (∀ bf, rel a (b ⋅ bf) → rel a' (b' ⋅ bf)) →
    ●V a ⋅ ◯V b ~~> ●V a' ⋅ ◯V b'.
  Proof.
    intros Hup.
    eapply cmra_update_updateP, cmra_updateP_weaken.
    { eapply view_updateP with (Pab := λ a b, a = a' ∧ b = b').
      naive_solver. }
    { naive_solver. }
  Qed.

  Lemma view_update_alloc a a' b' :
    (∀ bf, rel a bf → rel a' (b' ⋅ bf)) →
    ●V a ~~> ●V a' ⋅ ◯V b'.
  Proof.
    intros Hup. rewrite -(right_id _ _ (●V a)).
    apply view_update=> bf. rewrite left_id. apply Hup.
  Qed.
  Lemma view_update_dealloc a b a' :
    (∀ bf, rel a (b ⋅ bf) → rel a' bf) →
    ●V a ⋅ ◯V b ~~> ●V a'.
  Proof.
    intros Hup. rewrite -(right_id _ _ (●V a')).
    apply view_update=> bf. rewrite left_id. apply Hup.
  Qed.

  Lemma view_update_auth a a' b' :
    (∀ bf, rel a bf → rel a' bf) →
    ●V a ~~> ●V a'.
  Proof.
    intros Hup. rewrite -(right_id _ _ (●V a)) -(right_id _ _ (●V a')).
    apply view_update=> bf. rewrite !left_id. apply Hup.
  Qed.

  Local Lemma view_updateP_auth_dfrac dq P a :
    dq ~~>: P →
    ●V{dq} a ~~>: λ k, ∃ dq', k = ●V{dq'} a ∧ P dq'.
  Proof.
    intros Hupd. apply cmra_total_updateP.
    move=> [[[dq' ag]|] bf] [Hv ?].
    - destruct (Hupd (Some dq') Hv) as (dr&Hdr&Heq).
      eexists. split; first by eexists. done.
    - destruct (Hupd None Hv) as (dr&Hdr&Heq).
      eexists. split; first by eexists. done.
  Qed.

  Lemma view_update_auth_persist dq a : ●V{dq} a ~~> ●V□ a.
  Proof.
    eapply (cmra_update_lift_updateP (λ dq, view_auth dq a)).
    { intros; by apply view_updateP_auth_dfrac. }
    { apply dfrac_discard_update. }
  Qed.
  Lemma view_updateP_auth_unpersist a : ●V□ a ~~>: λ k, ∃ q, k = ●V{#q} a.
  Proof.
    eapply cmra_updateP_weaken.
    { eapply view_updateP_auth_dfrac, dfrac_undiscard_update. }
    naive_solver.
  Qed.

  Lemma view_updateP_both_unpersist a b : ●V□ a ⋅ ◯V b ~~>: λ k, ∃ q, k = ●V{#q} a ⋅ ◯V b.
  Proof.
    eapply cmra_updateP_weaken.
    { eapply cmra_updateP_op'.
      { eapply view_updateP_auth_unpersist. }
      by eapply cmra_update_updateP. }
    naive_solver.
  Qed.

  Lemma view_updateP_frag b P :
    (∀ a bf, rel a (b ⋅ bf) → ∃ b', P b' ∧ rel a (b' ⋅ bf)) →
    ◯V b ~~>: λ k, ∃ b', k = ◯V b' ∧ P b'.
  Proof.
    rewrite !cmra_total_updateP view_valid_eq=> ? [[[dq ag]|] bf]; naive_solver.
  Qed.

  Lemma view_update_frag b b' :
    (∀ a bf, rel a (b ⋅ bf) → rel a (b' ⋅ bf)) →
    ◯V b ~~> ◯V b'.
  Proof.
    rewrite !cmra_total_update view_valid_eq=> ? [[[dq ag]|] bf]; naive_solver.
  Qed.

  Lemma view_update_dfrac_alloc dq a b :
    (∀ bf, rel a bf → rel a (b ⋅ bf)) →
    ●V{dq} a ~~> ●V{dq} a ⋅ ◯V b.
  Proof.
    intros Hup. apply cmra_total_update. intros [[[p ag]|] bf] V.
    all: rewrite view_op_eq /= view_valid_eq /= in V.
    all: destruct V as [V1 V2]; revert V1 V2.
    - intros ? (a0 & Hag & Hrel). split; simpl; [done|].
      exists a0; split; [done|]. revert Hrel.
      assert (to_agree a ≼ to_agree a0) as <-%to_agree_included.
      { by exists ag. }
      rewrite !left_id. apply Hup.
    - intros ? (a0 & <-%(inj to_agree) & Hrel). split; simpl; [done|].
      exists a; split; [done|]. revert Hrel. rewrite !left_id. apply Hup.
  Qed.

  Lemma view_local_update a b0 b1 a' b0' b1' :
    (b0, b1) ~l~> (b0', b1') →
    (view_rel_holds rel a b0 → view_rel_holds rel a' b0') →
    (●V a ⋅ ◯V b0, ●V a ⋅ ◯V b1) ~l~> (●V a' ⋅ ◯V b0', ●V a' ⋅ ◯V b1').
  Proof.
    rewrite !local_update_unital.
    move=> Hup Hrel [[[qd ag]|] bf] /view_both_valid Hrel' [/=].
    - intros H1q.
      by destruct (id_free_r (DfracOwn 1) qd).
    - rewrite !left_id=> Hb0.
      destruct (Hup bf) as [? Hb0']; [by eauto using view_rel_valid..|].
      split; [apply view_both_valid; by auto|]. by rewrite -assoc Hb0'.
  Qed.

End cmra.

(** * Utilities to construct functors *)
(** Due to the dependent type [rel] in [view] we cannot actually define
instances of the functor structures [rFunctor] and [urFunctor]. Functors can
only be defined for instances of [view], like [auth]. To make it more convenient
to define functors for instances of [view], we define the map operation
[view_map] and a bunch of lemmas about it. *)
Definition view_map {A A' B B'}
    {rel : A → B → Prop} {rel' : A' → B' → Prop}
    (f : A → A') (g : B → B') (x : view rel) : view rel' :=
  View (prod_map id (agree_map f) <$> view_auth_proj x) (g (view_frag_proj x)).
Lemma view_map_id {A B} {rel : A → B → Prop} (x : view rel) :
  view_map id id x = x.
Proof. destruct x as [[[]|] ]; by rewrite // /view_map /= agree_map_id. Qed.
Lemma view_map_compose {A A' A'' B B' B''}
    {rel : A → B → Prop} {rel' : A' → B' → Prop}
    {rel'' : A'' → B'' → Prop}
    (f1 : A → A') (f2 : A' → A'') (g1 : B → B') (g2 : B' → B'') (x : view rel) :
  view_map (f2 ∘ f1) (g2 ∘ g1) x
  =@{view rel''} view_map f2 g2 (view_map (rel':=rel') f1 g1 x).
Proof. destruct x as [[[]|] ];  by rewrite // /view_map /= agree_map_compose. Qed.
Lemma view_map_ext  {A A' B B' : Type}
    {rel : A → B → Prop} {rel' : A' → B' → Prop}
    (f1 f2 : A → A') (g1 g2 : B → B')
    (x : view rel) :
  (∀ a, f1 a = f2 a) → (∀ b, g1 b = g2 b) →
  view_map f1 g1 x =@{view rel'} view_map f2 g2 x.
Proof.
  intros. unfold view_map. f_equal; [|done].
  apply option_fmap_ext => a; rewrite /prod_map /=. f_equal. rewrite (agree_map_ext f1 f2); done.
Qed.
(* Global Instance view_map_ne {A A' B B' : Type}
    {rel : A → B → Prop} {rel' : A' → B' → Prop}
    (f : A → A') (g : B → B') `{Hf : !NonExpansive f, Hg : !NonExpansive g} :
  NonExpansive (view_map (rel':=rel') (rel:=rel) f g).
Proof.
  intros [o1 bf1] [o2 bf2] [??]; split; simpl in *; [|by apply Hg].
  apply option_fmap_ne; [|done]=> pag1 pag2 ?.
  apply prod_map_ne; [done| |done]. by apply agree_map_ne.
Qed. *)

(* Definition viewO_map {A A' B B' : Type}
    {rel : A → B → Prop} {rel' : A' → B' → Prop}
    (f : A -n> A') (g : B -n> B') : viewO rel -n> viewO rel' :=
  OfeMor (view_map f g). *)
(* Lemma viewO_map_ne {A A' B B' : Type}
    {rel : A → B → Prop} {rel' : A' → B' → Prop} :
  NonExpansive2 (viewO_map (rel:=rel) (rel':=rel')).
Proof.
  intros f f' Hf g g' Hg [[[p ag]|] bf]; split=> //=.
  do 2 f_equiv. by apply agreeO_map_ne.
Qed. *)

(* Lemma view_map_cmra_morphism {A A' B B'}
    {rel : view_rel A B} {rel' : view_rel A' B'}
    (f : A → A') (g : B → B') `{!CmraMorphism g} :
  (∀ a b, rel a b → rel' (f a) (g b)) →
  CmraMorphism (view_map (rel:=rel) (rel':=rel') f g).
Proof.
  intros Hrel. split.
  - rewrite !view_valid_eq /=. intros [[[p ag]|] bf];
      [|naive_solver eauto using cmra_morphism_valid].
    intros [? [a' [Hag ?]]]. split; [done|]. exists (f a'). split; [|by auto].
    by rewrite -agree_map_to_agree -Hag.
  - intros [o bf]. rewrite /view_map /= view_pcore_eq.
    (repeat f_equal); simpl; by rewrite cmra_morphism_core.
  - intros [[[dq1 ag1]|] bf1] [[[dq2 ag2]|] bf2];
      try apply View_proper=> //=; try by rewrite cmra_morphism_op.
Qed. *)
