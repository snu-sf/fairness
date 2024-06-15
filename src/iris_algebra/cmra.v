From stdpp Require Import finite.
From iris.prelude Require Import prelude options.
Local Set Primitive Projections.

Class PCore (A : Type) := pcore : A → option A.
Global Hint Mode PCore ! : typeclass_instances.
Global Instance: Params (@pcore) 2 := {}.

Class Op (A : Type) := op : A → A → A.
Global Hint Mode Op ! : typeclass_instances.
Global Instance: Params (@op) 2 := {}.

(* A local scope for working on [iris_algebra]. This exists so that notation used in cmra (notably, ⋅), does not conflict with the same notation in other developments. *)
Declare Scope iris_algebra_scope.
Delimit Scope iris_algebra_scope with ia.
Local Open Scope iris_algebra_scope.

Infix "⋅" := op (at level 50, left associativity) : iris_algebra_scope.
Notation "(⋅)" := op (only parsing) : iris_algebra_scope.

(* The inclusion quantifies over [A], not [option A].  This means we do not get
   reflexivity.  However, if we used [option A], the following would no longer
   hold:
     x ≼ y ↔ x.1 ≼ y.1 ∧ x.2 ≼ y.2
   If you need the reflexive closure of the inclusion relation, you can use
   [Some a ≼ Some b]. There are various [Some_included] lemmas that help
   deal with propositions of this shape.
*)
Definition included {A} `{!Op A} (x y : A) := ∃ z, y = x ⋅ z.
Infix "≼" := included (at level 70) : iris_algebra_scope.
Notation "(≼)" := included (only parsing) : iris_algebra_scope.
Global Hint Extern 0 (_ ≼ _) => reflexivity : core.
Global Instance: Params (@included) 3 := {}.

(** [opM] is used in some lemma statements where [A] has not yet been shown to
be a CMRA, so we define it directly in terms of [Op]. *)
Definition opM `{!Op A} (x : A) (my : option A) :=
  match my with Some y => x ⋅ y | None => x end.
Infix "⋅?" := opM (at level 50, left associativity) : iris_algebra_scope.

Class Valid (A : Type) := valid : A → Prop.
Global Hint Mode Valid ! : typeclass_instances.
Global Instance: Params (@valid) 2 := {}.
Notation "✓ x" := (valid x) (at level 20) : iris_algebra_scope.

Section mixin.
  Record CmraMixin A `{!PCore A, !Op A, !Valid A} := {
    (* setoids *)
    mixin_cmra_pcore_ne (x y : A) cx :
      x = y → pcore x = Some cx → ∃ cy, pcore y = Some cy ∧ cx = cy;
    (* monoid *)
    mixin_cmra_assoc : Assoc (=@{A}) (⋅);
    mixin_cmra_comm : Comm (=@{A}) (⋅);
    mixin_cmra_pcore_l (x : A) cx : pcore x = Some cx → cx ⋅ x = x;
    mixin_cmra_pcore_idemp (x : A) cx : pcore x = Some cx → pcore cx = Some cx;
    mixin_cmra_pcore_mono (x y : A) cx :
      x ≼ y → pcore x = Some cx → ∃ cy, pcore y = Some cy ∧ cx ≼ cy;
    mixin_cmra_valid_op_l (x y : A) : ✓ (x ⋅ y) → ✓ x;
    mixin_cmra_extend (x y1 y2 : A) :
      ✓ x → x = y1 ⋅ y2 →
      { z1 : A & { z2 | x = z1 ⋅ z2 ∧ z1 = y1 ∧ z2 = y2 } }
  }.
End mixin.

(** Bundled version *)
#[projections(primitive=no)] (* FIXME: making this primitive leads to strange
TC resolution failures in view.v *)
Structure cmra := Cmra {
  cmra_car :> Type;
  cmra_pcore : PCore cmra_car;
  cmra_op : Op cmra_car;
  cmra_valid : Valid cmra_car;
  cmra_mixin : CmraMixin cmra_car;
}.
Global Arguments Cmra _ {_ _ _} _.

Global Arguments cmra_car : simpl never.
Global Arguments cmra_pcore : simpl never.
Global Arguments cmra_op : simpl never.
Global Arguments cmra_valid : simpl never.
Global Arguments cmra_mixin : simpl never.
Add Printing Constructor cmra.
(* FIXME(Coq #6294) : we need the new unification algorithm here. *)
Global Hint Extern 0 (PCore _) => refine (cmra_pcore _); shelve : typeclass_instances.
Global Hint Extern 0 (Op _) => refine (cmra_op _); shelve : typeclass_instances.
Global Hint Extern 0 (Valid _) => refine (cmra_valid _); shelve : typeclass_instances.

(** As explained more thoroughly in iris#539, Coq can run into trouble when
  [cmra] combinators (such as [optionUR]) are stacked and combined with
  coercions like [cmra_ofeO]. To partially address this, we give Coq's
  type-checker some directions for unfolding, with the Strategy command.

  For these structures, we instruct Coq to eagerly _expand_ all projections,
  except for the coercion to type (in this case, [cmra_car]), since that causes
  problem with canonical structure inference. Additionally, we make Coq
  eagerly expand the coercions that go from one structure to another, like
  [cmra_ofeO] in this case. *)
Global Strategy expand [cmra_pcore cmra_op cmra_valid cmra_mixin].

Definition cmra_mixin_of' A {Ac : cmra} (f : Ac → A) : CmraMixin Ac := cmra_mixin Ac.
Notation cmra_mixin_of A :=
  ltac:(let H := eval hnf in (cmra_mixin_of' A id) in exact H) (only parsing).

(** Lifting properties from the mixin *)
Section cmra_mixin.
  Context {A : cmra}.
  Implicit Types x y : A.
  Lemma cmra_pcore_ne x y cx :
    x = y → pcore x = Some cx → ∃ cy, pcore y = Some cy ∧ cx = cy.
  Proof. apply (mixin_cmra_pcore_ne _ (cmra_mixin A)). Qed.
  Global Instance cmra_assoc : Assoc (=) (@op A _).
  Proof. apply (mixin_cmra_assoc _ (cmra_mixin A)). Qed.
  Global Instance cmra_comm : Comm (=) (@op A _).
  Proof. apply (mixin_cmra_comm _ (cmra_mixin A)). Qed.
  Lemma cmra_pcore_l x cx : pcore x = Some cx → cx ⋅ x = x.
  Proof. apply (mixin_cmra_pcore_l _ (cmra_mixin A)). Qed.
  Lemma cmra_pcore_idemp x cx : pcore x = Some cx → pcore cx = Some cx.
  Proof. apply (mixin_cmra_pcore_idemp _ (cmra_mixin A)). Qed.
  Lemma cmra_pcore_mono x y cx :
    x ≼ y → pcore x = Some cx → ∃ cy, pcore y = Some cy ∧ cx ≼ cy.
  Proof. apply (mixin_cmra_pcore_mono _ (cmra_mixin A)). Qed.
  Lemma cmra_valid_op_l x y : ✓ (x ⋅ y) → ✓ x.
  Proof. apply (mixin_cmra_valid_op_l _ (cmra_mixin A)). Qed.
  Lemma cmra_extend x y1 y2 :
    ✓ x → x = y1 ⋅ y2 →
    { z1 : A & { z2 | x = z1 ⋅ z2 ∧ z1 = y1 ∧ z2 = y2 } }.
  Proof. apply (mixin_cmra_extend _ (cmra_mixin A)). Qed.
End cmra_mixin.

(** * CoreId elements *)
Class CoreId {A : cmra} (x : A) := core_id : pcore x = Some x.
Global Arguments core_id {_} _ {_}.
Global Hint Mode CoreId + ! : typeclass_instances.
Global Instance: Params (@CoreId) 1 := {}.

(** * Exclusive elements (i.e., elements that cannot have a frame). *)
Class Exclusive {A : cmra} (x : A) := exclusive_l y : ✓ (x ⋅ y) → False.
Global Arguments exclusive_l {_} _ {_} _ _.
Global Hint Mode Exclusive + ! : typeclass_instances.
Global Instance: Params (@Exclusive) 1 := {}.

(** * Cancelable elements. *)
Class Cancelable {A : cmra} (x : A) :=
  cancelable y z : ✓(x ⋅ y) → x ⋅ y = x ⋅ z → y = z.
Global Arguments cancelable {_} _ _ _ _ _.
Global Hint Mode Cancelable + ! : typeclass_instances.
Global Instance: Params (@Cancelable) 1 := {}.

(** * Identity-free elements. *)
Class IdFree {A : cmra} (x : A) :=
  id_free0_r y : ✓x → x ⋅ y = x → False.
Global Arguments id_free0_r {_} _ {_} _ _.
Global Hint Mode IdFree + ! : typeclass_instances.
Global Instance: Params (@IdFree) 1 := {}.

(** * CMRAs whose core is total *)
Class CmraTotal (A : cmra) := cmra_total (x : A) : is_Some (pcore x).
Global Hint Mode CmraTotal ! : typeclass_instances.

(** The function [core] returns a dummy when used on CMRAs without total
core. We only ever use this for [CmraTotal] CMRAs, but it is more convenient
to not require that proof to be able to call this function. *)
Definition core {A} `{!PCore A} (x : A) : A := default x (pcore x).
Global Instance: Params (@core) 2 := {}.

(** * CMRAs with a unit element *)
Class Unit (A : Type) := ε : A.
Global Hint Mode Unit ! : typeclass_instances.
Global Arguments ε {_ _}.

Record UcmraMixin A `{!PCore A, !Op A, !Valid A, !Unit A} := {
  mixin_ucmra_unit_valid : ✓ (ε : A);
  mixin_ucmra_unit_left_id : LeftId (=@{A}) ε (⋅);
  mixin_ucmra_pcore_unit : pcore ε =@{option A} Some ε
}.

#[projections(primitive=no)] (* FIXME: making this primitive leads to strange
TC resolution failures in view.v *)
Structure ucmra := Ucmra' {
  ucmra_car :> Type;
  ucmra_pcore : PCore ucmra_car;
  ucmra_op : Op ucmra_car;
  ucmra_valid : Valid ucmra_car;
  ucmra_unit : Unit ucmra_car;
  ucmra_cmra_mixin : CmraMixin ucmra_car;
  ucmra_mixin : UcmraMixin ucmra_car;
}.
Global Arguments Ucmra' _ {_ _ _ _} _ _.
Notation Ucmra A m :=
  (Ucmra' A (cmra_mixin_of A%type) m) (only parsing).
Global Arguments ucmra_car : simpl never.
Global Arguments ucmra_pcore : simpl never.
Global Arguments ucmra_op : simpl never.
Global Arguments ucmra_valid : simpl never.
Global Arguments ucmra_cmra_mixin : simpl never.
Global Arguments ucmra_mixin : simpl never.
Add Printing Constructor ucmra.
(* FIXME(Coq #6294) : we need the new unification algorithm here. *)
Global Hint Extern 0 (Unit _) => refine (ucmra_unit _); shelve : typeclass_instances.
Coercion ucmra_cmraR (A : ucmra) : cmra :=
  Cmra A (ucmra_cmra_mixin A).
Canonical Structure ucmra_cmraR.

(** As for CMRAs above, we instruct Coq to eagerly _expand_ all projections,
  except for the coercion to type (in this case, [ucmra_car]), since that causes
  problem with canonical structure inference.  Additionally, we make Coq
  eagerly expand the coercions that go from one structure to another, like
  [ucmra_cmraR] and [ucmra_ofeO] in this case. *)
Global Strategy expand [ucmra_cmraR ucmra_pcore
                        ucmra_op ucmra_valid ucmra_unit
                        ucmra_cmra_mixin].

(** Lifting properties from the mixin *)
Section ucmra_mixin.
  Context {A : ucmra}.
  Implicit Types x y : A.
  Lemma ucmra_unit_valid : ✓ (ε : A).
  Proof. apply (mixin_ucmra_unit_valid _ (ucmra_mixin A)). Qed.
  Global Instance ucmra_unit_left_id : LeftId (=) ε (@op A _).
  Proof. apply (mixin_ucmra_unit_left_id _ (ucmra_mixin A)). Qed.
  Lemma ucmra_pcore_unit : pcore (ε:A) = Some ε.
  Proof. apply (mixin_ucmra_pcore_unit _ (ucmra_mixin A)). Qed.
End ucmra_mixin.

(** * Morphisms *)
Class CmraMorphism {A B : cmra} (f : A → B) := {
  cmra_morphism_valid x : ✓ x → ✓ f x;
  cmra_morphism_pcore x : f <$> pcore x = pcore (f x);
  cmra_morphism_op x y : f (x ⋅ y) = f x ⋅ f y
}.
Global Hint Mode CmraMorphism - - ! : typeclass_instances.
(* TOOD: check if the args are correct *)
Global Arguments cmra_morphism_valid {_ _} _ {_} _ _.
Global Arguments cmra_morphism_pcore {_ _} _ {_} _.
Global Arguments cmra_morphism_op {_ _} _ {_} _ _.

(** * Properties **)
Section cmra.
Context {A : cmra}.
Implicit Types x y z : A.
Implicit Types xs ys zs : list A.

(** ** Setoids *)
Lemma cmra_pcore_proper x y cx :
  x = y → pcore x = Some cx → ∃ cy, pcore y = Some cy ∧ cx = cy.
Proof.
  intros. destruct (cmra_pcore_ne x y cx) as (cy&?&?); auto.
  exists cy; done.
Qed.
Global Instance cmra_pcore_proper' : Proper ((=) ==> (=)) (@pcore A _).
Proof. intros x y Hxy. rewrite Hxy. done. Qed.
Global Instance cmra_op_proper' : Proper ((=) ==> (=) ==> (=)) (@op A _).
Proof. intros x y Hxy. rewrite Hxy. done. Qed.

Global Instance cmra_valid_proper : Proper ((=) ==> iff) (@valid A _).
Proof. intros x y Hxy. rewrite Hxy. done. Qed.

Global Instance cmra_included_proper :
  Proper ((=) ==> (=) ==> iff) (@included A _) | 1.
Proof.
  intros x x' Hx y y' Hy.
  by split; intros [z ?]; exists z; [rewrite -Hx -Hy|rewrite Hx Hy].
Qed.
Global Instance cmra_opM_proper : Proper ((=) ==> (=) ==> (=)) (@opM A _).
Proof. destruct 2; by setoid_subst. Qed.

Global Instance CoreId_proper : Proper ((=) ==> iff) (@CoreId A).
Proof. solve_proper. Qed.
Global Instance Exclusive_proper : Proper ((=) ==> iff) (@Exclusive A).
Proof. intros x y Hxy. rewrite /Exclusive. by setoid_rewrite Hxy. Qed.
Global Instance Cancelable_proper : Proper ((=) ==> iff) (@Cancelable A).
Proof. intros x y Hxy. rewrite /Cancelable. by setoid_rewrite Hxy. Qed.
Global Instance IdFree_proper : Proper ((=) ==> iff) (@IdFree A).
Proof. intros x y Hxy. rewrite /IdFree. by setoid_rewrite Hxy. Qed.

(** ** Op *)
Lemma cmra_op_opM_assoc x y mz : (x ⋅ y) ⋅? mz = x ⋅ (y ⋅? mz).
Proof. destruct mz; by rewrite /= -?assoc. Qed.

(** ** Validity *)
Lemma cmra_valid_op_r x y : ✓ (x ⋅ y) → ✓ y.
Proof. rewrite (comm _ x); apply cmra_valid_op_l. Qed.

(** ** Core *)
Lemma cmra_pcore_l' x cx : pcore x = Some cx → cx ⋅ x = x.
Proof. by apply cmra_pcore_l. Qed.
Lemma cmra_pcore_r x cx : pcore x = Some cx → x ⋅ cx = x.
Proof. intros. rewrite (comm _ x). by apply cmra_pcore_l. Qed.
Lemma cmra_pcore_r' x cx : pcore x = Some cx → x ⋅ cx = x.
Proof. by apply cmra_pcore_r. Qed.
Lemma cmra_pcore_idemp' x cx : pcore x = Some cx → pcore cx = Some cx.
Proof. eauto using cmra_pcore_idemp. Qed.
Lemma cmra_pcore_dup x cx : pcore x = Some cx → cx = cx ⋅ cx.
Proof. intros; symmetry; eauto using cmra_pcore_r', cmra_pcore_idemp. Qed.
Lemma cmra_pcore_dup' x cx : pcore x = Some cx → cx = cx ⋅ cx.
Proof. intros; symmetry; eauto using cmra_pcore_r', cmra_pcore_idemp'. Qed.
Lemma cmra_pcore_valid x cx : ✓ x → pcore x = Some cx → ✓ cx.
Proof.
  intros Hv Hx%cmra_pcore_l. move: Hv; rewrite -Hx. apply cmra_valid_op_l.
Qed.

(** ** Exclusive elements *)
Lemma exclusive_r x `{!Exclusive x} y : ✓ (y ⋅ x) → False.
Proof. rewrite comm. by apply exclusive_l. Qed.

Lemma exclusive_opM x `{!Exclusive x} my : ✓ (x ⋅? my) → my = None.
Proof. destruct my as [y|]; last done. move=> /(exclusive_l x) []. Qed.
Lemma exclusive_included x `{!Exclusive x} y : x ≼ y → ✓ y → False.
Proof. intros [? ->]. by apply exclusive_l. Qed.

(** ** Order *)
Global Instance cmra_included_trans: Transitive (@included A _).
Proof.
  intros x y z [z1 Hy] [z2 Hz]; exists (z1 ⋅ z2). by rewrite assoc -Hy -Hz.
Qed.
Lemma cmra_valid_included x y : ✓ y → x ≼ y → ✓ x.
Proof. intros Hyv [z ?]; setoid_subst; eauto using cmra_valid_op_l. Qed.

Lemma cmra_included_l x y : x ≼ x ⋅ y.
Proof. by exists y. Qed.
Lemma cmra_included_r x y : y ≼ x ⋅ y.
Proof. rewrite (comm op); apply cmra_included_l. Qed.

Lemma cmra_pcore_mono' x y cx :
  x ≼ y → pcore x = Some cx → ∃ cy, pcore y = Some cy ∧ cx ≼ cy.
Proof. apply cmra_pcore_mono. Qed.
Lemma cmra_included_pcore x cx : pcore x = Some cx → cx ≼ x.
Proof. exists x. by rewrite cmra_pcore_l. Qed.

Lemma cmra_mono_l x y z : x ≼ y → z ⋅ x ≼ z ⋅ y.
Proof. by intros [z1 Hz1]; exists z1; rewrite Hz1 (assoc op). Qed.
Lemma cmra_mono_r x y z : x ≼ y → x ⋅ z ≼ y ⋅ z.
Proof. by intros; rewrite -!(comm _ z); apply cmra_mono_l. Qed.
Lemma cmra_mono x1 x2 y1 y2 : x1 ≼ y1 → x2 ≼ y2 → x1 ⋅ x2 ≼ y1 ⋅ y2.
Proof. intros; etrans; eauto using cmra_mono_l, cmra_mono_r. Qed.

Global Instance cmra_mono' :
  Proper (included ==> included ==> included) (@op A _).
Proof. intros x1 x2 Hx y1 y2 Hy. by apply cmra_mono. Qed.

(** ** CoreId elements *)
Lemma core_id_dup x `{!CoreId x} : x = x ⋅ x.
Proof. by apply cmra_pcore_dup' with x. Qed.

Lemma core_id_extract x y `{!CoreId x} :
  x ≼ y → y = y ⋅ x.
Proof.
  intros ?.
  destruct (cmra_pcore_mono' x y x) as (cy & Hcy & [x' Hx']); [done|exact: core_id|].
  rewrite -(cmra_pcore_r y cy) //. rewrite Hx' -!assoc. f_equiv.
  rewrite [x' ⋅ x]comm assoc -core_id_dup. done.
Qed.

(** ** Total core *)
Section total_core.
  Local Set Default Proof Using "Type*".
  Context `{!CmraTotal A}.

  Lemma cmra_pcore_core x : pcore x = Some (core x).
  Proof.
    rewrite /core. destruct (cmra_total x) as [cx ->]. done.
  Qed.
  Lemma cmra_core_l x : core x ⋅ x = x.
  Proof.
    destruct (cmra_total x) as [cx Hcx]. by rewrite /core /= Hcx cmra_pcore_l.
  Qed.
  Lemma cmra_core_idemp x : core (core x) = core x.
  Proof.
    destruct (cmra_total x) as [cx Hcx]. by rewrite /core /= Hcx (cmra_pcore_idemp x).
  Qed.
  Lemma cmra_core_mono x y : x ≼ y → core x ≼ core y.
  Proof.
    intros; destruct (cmra_total x) as [cx Hcx].
    destruct (cmra_pcore_mono x y cx) as (cy&Hcy&?); auto.
    by rewrite /core /= Hcx Hcy.
  Qed.

  Global Instance cmra_core_proper : Proper ((=) ==> (=)) (@core A _).
  Proof. intros x y Hxy. rewrite Hxy. done. Qed.

  Lemma cmra_core_r x : x ⋅ core x = x.
  Proof. by rewrite (comm _ x) cmra_core_l. Qed.
  Lemma cmra_core_dup x : core x = core x ⋅ core x.
  Proof. by rewrite -{3}(cmra_core_idemp x) cmra_core_r. Qed.
  Lemma cmra_core_valid x : ✓ x → ✓ core x.
  Proof. rewrite -{1}(cmra_core_l x); apply cmra_valid_op_l. Qed.

  Lemma core_id_total x : CoreId x ↔ core x = x.
  Proof.
    split; [intros; by rewrite /core /= (core_id x)|].
    rewrite /CoreId /core /=.
    destruct (cmra_total x) as [? ->]. simpl. intros ->. done.
  Qed.
  Lemma core_id_core x `{!CoreId x} : core x = x.
  Proof. by apply core_id_total. Qed.

  (** Not an instance since TC search cannot solve the premise. *)
  Lemma cmra_pcore_core_id x y : pcore x = Some y → CoreId y.
  Proof. rewrite /CoreId. eauto using cmra_pcore_idemp. Qed.

  Global Instance cmra_core_core_id x : CoreId (core x).
  Proof. eapply cmra_pcore_core_id. rewrite cmra_pcore_core. done. Qed.

  Lemma cmra_included_core x : core x ≼ x.
  Proof. by exists x; rewrite cmra_core_l. Qed.
  Global Instance cmra_included_preorder : PreOrder (@included A _).
  Proof.
    split; [|apply _]. by intros x; exists (core x); rewrite cmra_core_r.
  Qed.
End total_core.


(** Cancelable elements  *)
Global Instance cancelable_proper : Proper ((=) ==> iff) (@Cancelable A).
Proof. unfold Cancelable. intros x x' EQ. by setoid_rewrite EQ. Qed.
Global Instance cancelable_op x y :
  Cancelable x → Cancelable y → Cancelable (x ⋅ y).
Proof.
  intros ?? z z' ??. apply (cancelable y), (cancelable x); try done.
  - eapply cmra_valid_op_r. by rewrite assoc.
  - by rewrite assoc.
  - by rewrite !assoc.
Qed.
Global Instance exclusive_cancelable (x : A) : Exclusive x → Cancelable x.
Proof. intros ? z z' []%(exclusive_l x). Qed.

(** Id-free elements  *)
Global Instance id_free_proper : Proper ((=) ==> iff) (@IdFree A).
Proof. intros x y ->. done. Qed.
Lemma id_free_r x `{!IdFree x} y : ✓x → x ⋅ y = x → False.
Proof. move=> ?. eauto. Qed.
Lemma id_free_l x `{!IdFree x} y : ✓x → y ⋅ x = x → False.
Proof. rewrite (comm _ y). eauto using id_free_r. Qed.
Global Instance id_free_op_r x y : IdFree y → Cancelable x → IdFree (x ⋅ y).
Proof.
  intros ?? z ? Hid%symmetry. revert Hid. rewrite -assoc=>/(cancelable x) ?.
  eapply (id_free0_r y); [by eapply cmra_valid_op_r |symmetry; eauto].
Qed.
Global Instance id_free_op_l x y : IdFree x → Cancelable y → IdFree (x ⋅ y).
Proof. intros. rewrite comm. apply _. Qed.
Global Instance exclusive_id_free x : Exclusive x → IdFree x.
Proof. intros ? z ? Hid. apply (exclusive_l x z). by rewrite Hid. Qed.
End cmra.

(* We use a [Hint Extern] with [apply:], instead of [Hint Immediate], to invoke
  the new unification algorithm. The old unification algorithm sometimes gets
  confused by going from [ucmra]'s to [cmra]'s and back. *)
Global Hint Extern 0 (?a ≼ ?a ⋅ _) => apply: cmra_included_l : core.
Global Hint Extern 0 (?a ≼ _ ⋅ ?a) => apply: cmra_included_r : core.

(** * Properties about CMRAs with a unit element **)
Section ucmra.
  Context {A : ucmra}.
  Implicit Types x y z : A.

  Lemma ucmra_unit_least x : ε ≼ x.
  Proof. by exists x; rewrite left_id. Qed.
  Global Instance ucmra_unit_right_id : RightId (=) ε (@op A _).
  Proof. by intros x; rewrite (comm op) left_id. Qed.
  Global Instance ucmra_unit_core_id : CoreId (ε:A).
  Proof. apply ucmra_pcore_unit. Qed.

  Global Instance cmra_unit_cmra_total : CmraTotal A.
  Proof.
    intros x. destruct (cmra_pcore_mono' ε x ε) as (cx&->&?); [..|by eauto].
    - apply ucmra_unit_least.
    - apply (core_id _).
  Qed.
  Global Instance empty_cancelable : Cancelable (ε:A).
  Proof. intros ???. by rewrite !left_id. Qed.

  (* For big ops *)
  (* Global Instance cmra_monoid : Monoid (@op A _) := {| monoid_unit := ε |}. *)
End ucmra.

Global Hint Immediate cmra_unit_cmra_total : core.
Global Hint Extern 0 (ε ≼ _) => apply: ucmra_unit_least : core.

(** * Constructing a CMRA with total core *)
Section cmra_total.
  Context A `{!PCore A, !Op A, !Valid A}.
  Context (total : ∀ x : A, is_Some (pcore x)).
  Context (op_assoc : Assoc (=) (@op A _)).
  Context (op_comm : Comm (=) (@op A _)).
  Context (core_l : ∀ x : A, core x ⋅ x = x).
  Context (core_idemp : ∀ x : A, core (core x) = core x).
  Context (core_mono : ∀ x y : A, x ≼ y → core x ≼ core y).
  Context (valid_op_l : ∀(x y : A), ✓ (x ⋅ y) → ✓ x).
  Context (extend : ∀(x y1 y2 : A),
    ✓ x → x = y1 ⋅ y2 →
    { z1 : A & { z2 | x = z1 ⋅ z2 ∧ z1 = y1 ∧ z2 = y2 } }).
  Lemma cmra_total_mixin : CmraMixin A.
  Proof using Type*.
    split; auto.
    - intros x y ? Hcx%(f_equal core) Hx; move: Hcx. rewrite /core /= Hx /=.
      case (total y)=> [cy ->]; eauto.
    - intros x cx Hcx. move: (core_l x). by rewrite /core /= Hcx.
    - intros x cx Hcx. move: (core_idemp x). rewrite /core /= Hcx /=.
      case (total cx)=>[ccx ->]. simpl. naive_solver.
    - intros x y cx Hxy%core_mono Hx. move: Hxy.
      rewrite /core /= Hx /=. case (total y)=> [cy ->]; eauto.
  Qed.
End cmra_total.

(** * Properties about morphisms *)
Global Instance cmra_morphism_id {A : cmra} : CmraMorphism (@id A).
Proof.
  split => /=.
  - done.
  - intros. by rewrite option_fmap_id.
  - done.
Qed.
Global Instance cmra_morphism_proper {A B : cmra} (f : A → B) `{!CmraMorphism f} :
  Proper ((=) ==> (=)) f.
Proof. by intros x y ->. Qed.
Global Instance cmra_morphism_compose {A B C : cmra} (f : A → B) (g : B → C) :
  CmraMorphism f → CmraMorphism g → CmraMorphism (g ∘ f).
Proof.
  split.
  - move=> x Hx /=. by apply cmra_morphism_valid, cmra_morphism_valid.
  - move=> x /=. by rewrite option_fmap_compose !cmra_morphism_pcore.
  - move=> x y /=. by rewrite !cmra_morphism_op.
Qed.

Section cmra_morphism.
  Local Set Default Proof Using "Type*".
  Context {A B : cmra} (f : A → B) `{!CmraMorphism f}.
  Lemma cmra_morphism_core x : f (core x) = core (f x).
  Proof. unfold core. rewrite -cmra_morphism_pcore. by destruct (pcore x). Qed.
  Lemma cmra_morphism_monotone x y : x ≼ y → f x ≼ f y.
  Proof. intros [z ->]. exists (f z). by rewrite cmra_morphism_op. Qed.
End cmra_morphism.

(** * Transporting a CMRA equality *)
Definition cmra_transport {A B : cmra} (H : A = B) (x : A) : B :=
  eq_rect A id x _ H.

Lemma cmra_transport_trans {A B C : cmra} (H1 : A = B) (H2 : B = C) x :
  cmra_transport H2 (cmra_transport H1 x) = cmra_transport (eq_trans H1 H2) x.
Proof. by destruct H2. Qed.

Section cmra_transport.
  Context {A B : cmra} (H : A = B).
  Notation T := (cmra_transport H).
  Global Instance cmra_transport_proper : Proper ((=) ==> (=)) T.
  Proof. by intros ???; destruct H. Qed.
  Lemma cmra_transport_op x y : T (x ⋅ y) = T x ⋅ T y.
  Proof. by destruct H. Qed.
  Lemma cmra_transport_core x : T (core x) = core (T x).
  Proof. by destruct H. Qed.
  Lemma cmra_transport_valid x : ✓ T x ↔ ✓ x.
  Proof. by destruct H. Qed.
  Global Instance cmra_transport_core_id x : CoreId x → CoreId (T x).
  Proof. by destruct H. Qed.
End cmra_transport.

(** * Instances *)
(** ** Discrete CMRA *)
Record RAMixin A `{PCore A, Op A, Valid A} := {
  (* setoids *)
  ra_op_proper (x : A) : Proper ((=) ==> (=)) (op x);
  ra_core_proper (x y : A) cx :
    x = y → pcore x = Some cx → ∃ cy, pcore y = Some cy ∧ cx = cy;
  ra_valid_proper : Proper ((=@{A}) ==> impl) valid;
  (* monoid *)
  ra_assoc : Assoc (=@{A}) (⋅);
  ra_comm : Comm (=@{A}) (⋅);
  ra_pcore_l (x : A) cx : pcore x = Some cx → cx ⋅ x = x;
  ra_pcore_idemp (x : A) cx : pcore x = Some cx → pcore cx = Some cx;
  ra_pcore_mono (x y : A) cx :
    x ≼ y → pcore x = Some cx → ∃ cy, pcore y = Some cy ∧ cx ≼ cy;
  ra_valid_op_l (x y : A) : ✓ (x ⋅ y) → ✓ x
}.

Section discrete.
  Local Set Default Proof Using "Type*".
  Context `{!PCore A, !Op A, !Valid A}.
  Context (ra_mix : RAMixin A).

  Definition discrete_cmra_mixin : CmraMixin A.
  Proof.
    destruct ra_mix; split; try done.
    intros x y1 y2 ??; by exists y1, y2.
  Qed.
End discrete.

Notation discreteR A ra_mix :=
  (Cmra A (discrete_cmra_mixin ra_mix))
  (only parsing).

Section ra_total.
  Local Set Default Proof Using "Type*".
  Context A `{Equiv A, PCore A, Op A, Valid A}.
  Context (total : ∀ x : A, is_Some (pcore x)).
  Context (op_proper : ∀ x : A, Proper ((=) ==> (=)) (op x)).
  Context (core_proper: Proper ((=) ==> (=)) (@core A _)).
  Context (valid_proper : Proper ((=) ==> impl) (@valid A _)).
  Context (op_assoc : Assoc (=) (@op A _)).
  Context (op_comm : Comm (=) (@op A _)).
  Context (core_l : ∀ x : A, core x ⋅ x = x).
  Context (core_idemp : ∀ x : A, core (core x) = core x).
  Context (core_mono : ∀ x y : A, x ≼ y → core x ≼ core y).
  Context (valid_op_l : ∀ x y : A, ✓ (x ⋅ y) → ✓ x).
  Lemma ra_total_mixin : RAMixin A.
  Proof.
    split; auto.
    - intros x y ? Hcx%core_proper Hx; move: Hcx. rewrite /core /= Hx /=.
      case (total y)=> [cy ->]; eauto.
    - intros x cx Hcx. move: (core_l x). by rewrite /core /= Hcx.
    - intros x cx Hcx. move: (core_idemp x). rewrite /core /= Hcx /=.
      case (total cx)=>[ccx ->]. simpl. by intros ->.
    - intros x y cx Hxy%core_mono Hx. move: Hxy.
      rewrite /core /= Hx /=. case (total y)=> [cy ->]; eauto.
  Qed.
End ra_total.

(** ** CMRA for the unit type *)
Section unit.
  Local Instance unit_valid_instance : Valid () := λ x, True.
  Local Instance unit_pcore_instance : PCore () := λ x, Some x.
  Local Instance unit_op_instance : Op () := λ x y, ().
  Lemma unit_cmra_mixin : CmraMixin ().
  Proof.
    apply discrete_cmra_mixin, ra_total_mixin; eauto.
    all: try apply _.
    intros []. done.
  Qed.
  Canonical Structure unitR : cmra := Cmra unit unit_cmra_mixin.

  Local Instance unit_unit_instance : Unit () := ().
  Lemma unit_ucmra_mixin : UcmraMixin ().
  Proof.
    split; auto.
    - done.
    - intros []. done.
  Qed.
  Canonical Structure unitUR : ucmra := Ucmra unit unit_ucmra_mixin.

  Global Instance unit_core_id (x : ()) : CoreId x.
  Proof. by constructor. Qed.
  Global Instance unit_cancelable (x : ()) : Cancelable x.
  Proof. destruct x. intros () (). constructor. Qed.
End unit.

(** ** CMRA for the empty type *)
Section empty.
  Local Instance Empty_set_valid_instance : Valid Empty_set := λ x, False.
  Local Instance Empty_set_pcore_instance : PCore Empty_set := λ x, Some x.
  Local Instance Empty_set_op_instance : Op Empty_set := λ x y, x.
  Lemma Empty_set_cmra_mixin : CmraMixin Empty_set.
  Proof.
    apply discrete_cmra_mixin, ra_total_mixin; eauto.
    all: try apply _.
    intros [].
  Qed.
  Canonical Structure Empty_setR : cmra := Cmra Empty_set Empty_set_cmra_mixin.

  Global Instance Empty_set_core_id (x : Empty_set) : CoreId x.
  Proof. by constructor. Qed.
  Global Instance Empty_set_cancelable (x : Empty_set) : Cancelable x.
  Proof. destruct x. Qed.
End empty.

(** ** Product *)
Section prod.
  Context {A B : cmra}.
  Local Arguments pcore _ _ !_ /.
  Local Arguments cmra_pcore _ !_/.

  Local Instance prod_op_instance : Op (A * B) := λ x y, (x.1 ⋅ y.1, x.2 ⋅ y.2).
  Local Instance prod_pcore_instance : PCore (A * B) := λ x,
    c1 ← pcore (x.1); c2 ← pcore (x.2); Some (c1, c2).
  Local Arguments prod_pcore_instance !_ /.
  Local Instance prod_valid_instance : Valid (A * B) := λ x, ✓ x.1 ∧ ✓ x.2.

  Lemma prod_pcore_Some (x cx : A * B) :
    pcore x = Some cx ↔ pcore (x.1) = Some (cx.1) ∧ pcore (x.2) = Some (cx.2).
  Proof. destruct x, cx; by intuition simplify_option_eq. Qed.

  Lemma prod_included (x y : A * B) : x ≼ y ↔ x.1 ≼ y.1 ∧ x.2 ≼ y.2.
  Proof.
    split.
    - intros [z Hz]. destruct x,y,z.
      unfold op,prod_op_instance in Hz.
      injection Hz. naive_solver.
    - intros [[z1 Hz1] [z2 Hz2]]; exists (z1,z2).
      unfold op,prod_op_instance.
      destruct x,y. simpl in *.
      by rewrite Hz1 Hz2.
  Qed.

  Definition prod_cmra_mixin : CmraMixin (A * B).
  Proof.
    split; try apply _.
    (* - by intros x y1 y2 [Hy1 Hy2]; split; rewrite /= ?Hy1 ?Hy2. *)
    - intros [x1 x2] [y1 y2] [cx1 cx2] Hxy [Hx Hy]%prod_pcore_Some.
      injection Hxy. intros.
      unfold pcore,prod_pcore_instance. simpl.
      destruct (cmra_pcore_ne(x1) (y1) (cx1)) as (z1&->&->); auto.
      destruct (cmra_pcore_ne(x2) (y2) (cx2)) as (z2&->&->); auto.
      exists (z1,z2); repeat constructor; auto.
    - intros [] [] []. unfold op, prod_op_instance. simpl. f_equal; by rewrite (assoc op).
    - intros [] []. unfold op, prod_op_instance. simpl. f_equal; by rewrite (comm op).
    - intros [x1 x2] [cx1 cx2]; rewrite prod_pcore_Some /op /prod_op_instance /=.
      intros [Hx1 Hx2]. f_equal; by apply cmra_pcore_l.
    - intros [x1 x2] [cx1 cx2]; rewrite prod_pcore_Some /op /prod_op_instance /=.
      by intros [->%cmra_pcore_idemp ->%cmra_pcore_idemp].
    - intros x y cx; rewrite prod_included prod_pcore_Some=> -[??] [??].
      destruct (cmra_pcore_mono (x.1) (y.1) (cx.1)) as (z1&?&?); auto.
      destruct (cmra_pcore_mono (x.2) (y.2) (cx.2)) as (z2&?&?); auto.
      exists (z1,z2). by rewrite prod_included prod_pcore_Some.
    - intros x y [??]; split; simpl in *; eauto using cmra_valid_op_l.
    - intros [x1 x2] [y11 y12] [y21 y22] [??] Hxy; simpl in *.
      rewrite /op /prod_op_instance /= in Hxy. injection Hxy. intros.
      destruct (cmra_extend(x1) (y11) (y21)) as (z11&z12&?&?&?); auto.
      destruct (cmra_extend(x2) (y12) (y22)) as (z21&z22&?&?&?); auto.
      exists (z11,z21), (z12,z22).
      rewrite /op /prod_op_instance /=.
      subst. done.
  Qed.
  Canonical Structure prodR := Cmra (prod A B) prod_cmra_mixin.

  Lemma pair_op (a a' : A) (b b' : B) : (a ⋅ a', b ⋅ b') = (a, b) ⋅ (a', b').
  Proof. done. Qed.
  Lemma pair_valid (a : A) (b : B) : ✓ (a, b) ↔ ✓ a ∧ ✓ b.
  Proof. done. Qed.
  Lemma pair_included (a a' : A) (b b' : B) :
    (a, b) ≼ (a', b') ↔ a ≼ a' ∧ b ≼ b'.
  Proof. apply prod_included. Qed.
  Lemma pair_pcore (a : A) (b : B) :
    pcore (a, b) = c1 ← pcore a; c2 ← pcore b; Some (c1, c2).
  Proof. done. Qed.
  Lemma pair_core `{!CmraTotal A, !CmraTotal B} (a : A) (b : B) :
    core (a, b) = (core a, core b).
  Proof.
    rewrite /core {1}/pcore /=.
    rewrite (cmra_pcore_core a) /= (cmra_pcore_core b). done.
  Qed.

  Global Instance prod_cmra_total : CmraTotal A → CmraTotal B → CmraTotal prodR.
  Proof.
    intros H1 H2 [a b]. destruct (H1 a) as [ca ?], (H2 b) as [cb ?].
    exists (ca,cb); by simplify_option_eq.
  Qed.

  (* FIXME(Coq #6294): This is not an instance because we need it to use the new
  unification. *)
  Lemma pair_core_id x y :
    CoreId x → CoreId y → CoreId (x,y).
  Proof. by rewrite /CoreId prod_pcore_Some. Qed.

  Global Instance pair_exclusive_l x y : Exclusive x → Exclusive (x,y).
  Proof. by intros ?[][?%exclusive_l]. Qed.
  Global Instance pair_exclusive_r x y : Exclusive y → Exclusive (x,y).
  Proof. by intros ?[][??%exclusive_l]. Qed.

  Global Instance pair_cancelable x y :
    Cancelable x → Cancelable y → Cancelable (x,y).
  Proof.
    intros ??[][] V EQ. unfold op,prod_op_instance in *. destruct V as [Vx Vy]. simpl in *. injection EQ.
    intros. f_equal.
    - by eapply cancelable.
    - by eapply cancelable.
  Qed.

  Global Instance pair_id_free_l x y : IdFree x → IdFree (x,y).
  Proof. move=> Hx [a b] [? _] [/=? _]. apply (Hx a); eauto. Qed.
  Global Instance pair_id_free_r x y : IdFree y → IdFree (x,y).
  Proof. move=> Hy [a b] [_ ?] [_ /=?]. apply (Hy b); eauto. Qed.
End prod.

(* Registering as [Hint Extern] with new unification. *)
Global Hint Extern 4 (CoreId _) =>
  notypeclasses refine (pair_core_id _ _ _ _) : typeclass_instances.

Global Arguments prodR : clear implicits.

Section prod_unit.
  Context {A B : ucmra}.

  Local Instance prod_unit_instance `{Unit A, Unit B} : Unit (A * B) := (ε, ε).
  Lemma prod_ucmra_mixin : UcmraMixin (A * B).
  Proof.
    split.
    - split; apply ucmra_unit_valid.
    - intros []. rewrite /ε /prod_unit_instance /ε /op /cmra_op /= /prod_op_instance.
      rewrite !left_id. done.
    - rewrite prod_pcore_Some; split; apply (core_id _).
  Qed.
  Canonical Structure prodUR := Ucmra (prod A B) prod_ucmra_mixin.

  Lemma pair_split (a : A) (b : B) : (a, b) = (a, ε) ⋅ (ε, b).
  Proof. by rewrite -pair_op left_id right_id. Qed.

  Lemma pair_op_1 (a a': A) : (a ⋅ a', ε) =@{A*B} (a, ε) ⋅ (a', ε).
  Proof. by rewrite -pair_op ucmra_unit_left_id. Qed.

  Lemma pair_op_2 (b b': B) : (ε, b ⋅ b') =@{A*B} (ε, b) ⋅ (ε, b').
  Proof. by rewrite -pair_op ucmra_unit_left_id. Qed.
End prod_unit.

Global Arguments prodUR : clear implicits.

Global Instance prod_map_cmra_morphism {A A' B B' : cmra} (f : A → A') (g : B → B') :
  CmraMorphism f → CmraMorphism g → CmraMorphism (prod_map f g).
Proof.
  split.
  - by intros x [??]; split; simpl; apply cmra_morphism_valid.
  - intros x. etrans; last apply (reflexivity (mbind _ _)).
    etrans; first apply (reflexivity (_ <$> mbind _ _)). simpl.
    assert (Hf := cmra_morphism_pcore f (x.1)).
    destruct (pcore (f (x.1))), (pcore (x.1)); inversion_clear Hf=>//=.
    assert (Hg := cmra_morphism_pcore g (x.2)).
    destruct (pcore (g (x.2))), (pcore (x.2)); inversion_clear Hg=>//=.
  - intros. by rewrite /prod_map /= !cmra_morphism_op.
Qed.

(** ** CMRA for the option type *)
Section option.
  Context {A : cmra}.
  Implicit Types a b : A.
  Implicit Types ma mb : option A.
  Local Arguments core _ _ !_ /.
  Local Arguments pcore _ _ !_ /.

  Local Instance option_valid_instance : Valid (option A) := λ ma,
    match ma with Some a => ✓ a | None => True end.
  Local Instance option_pcore_instance : PCore (option A) := λ ma,
    Some (ma ≫= pcore).
  Local Arguments option_pcore_instance !_ /.
  Local Instance option_op_instance : Op (option A) :=
    union_with (λ a b, Some (a ⋅ b)).

  Definition Some_valid a : ✓ Some a ↔ ✓ a := reflexivity _.
  Definition Some_op a b : Some (a ⋅ b) = Some a ⋅ Some b := eq_refl.
  Lemma Some_core `{!CmraTotal A} a : Some (core a) = core (Some a).
  Proof. rewrite /core /=. by destruct (cmra_total a) as [? ->]. Qed.
  Lemma pcore_Some a : pcore (Some a) = Some (pcore a).
  Proof. done. Qed.
  Lemma Some_op_opM a ma : Some a ⋅ ma = Some (a ⋅? ma).
  Proof. by destruct ma. Qed.

  Lemma option_included ma mb :
    ma ≼ mb ↔ ma = None ∨ ∃ a b, ma = Some a ∧ mb = Some b ∧ (a = b ∨ a ≼ b).
  Proof.
    split.
    - intros [mc Hmc].
      destruct ma as [a|]; [right|by left].
      destruct mb as [b|]; [exists a, b|destruct mc; inversion_clear Hmc].
      destruct mc as [c|]; inversion_clear Hmc; split_and?; auto;
        setoid_subst; eauto.
    - intros [->|(a&b&->&->&[Hc|[c Hc]])].
      + exists mb. by destruct mb.
      + exists None. unfold op,option_op_instance. simpl. f_equal. done.
      + exists (Some c). unfold op,option_op_instance. simpl. f_equal. done.
  Qed.
  Lemma option_included_total `{!CmraTotal A} ma mb :
    ma ≼ mb ↔ ma = None ∨ ∃ a b, ma = Some a ∧ mb = Some b ∧ a ≼ b.
  Proof.
    rewrite option_included. split; last naive_solver.
    intros [->|(a&b&->&->&[Hab|?])]; [by eauto| |by eauto 10].
    right. exists a, b. by rewrite {3}Hab.
  Qed.

  (* See below for more [included] lemmas. *)

  Lemma option_cmra_mixin : CmraMixin (option A).
  Proof.
    apply cmra_total_mixin.
    - eauto.
    - intros [a|] [b|] [c|]; rewrite /op /option_op_instance /=; rewrite ?assoc; auto.
    - intros [a|] [b|]; rewrite /op /option_op_instance /=; rewrite 1?(comm op); auto.
    - intros [a|]; simpl; auto.
      destruct (pcore a) as [ca|] eqn:?; rewrite /op /option_op_instance /=; eauto using cmra_pcore_l.
      f_equal. by apply cmra_pcore_l.
    - intros [a|]; simpl; auto.
      destruct (pcore a) as [ca|] eqn:?; simpl; eauto using cmra_pcore_idemp.
    - intros ma mb; setoid_rewrite option_included.
      intros [->|(a&b&->&->&[?|?])]; simpl; eauto.
      + destruct (pcore a) as [ca|] eqn:?; eauto.
        destruct (cmra_pcore_proper a b ca) as (?&?&?); eauto 10.
      + destruct (pcore a) as [ca|] eqn:?; eauto.
        destruct (cmra_pcore_mono a b ca) as (?&?&?); eauto 10.
    - intros[a|] [b|]; rewrite /valid /option_valid_instance /=;
        eauto using cmra_valid_op_l.
    - intros ma mb1 mb2.
      destruct ma as [a|], mb1 as [b1|], mb2 as [b2|]; intros Hx Hx';
        (try by exfalso; inversion Hx'); (try (apply (inj Some) in Hx')).
      + destruct (cmra_extend a b1 b2) as (c1&c2&?&?&?); auto.
        exists (Some c1), (Some c2); repeat rewrite /op /option_op_instance /=.
        split_and!; f_equal; auto.
      + exists (Some a), None; repeat rewrite /op /option_op_instance /=.
        split_and!; f_equal; auto.
      + exists None, (Some a); repeat rewrite /op /option_op_instance /=.
        split_and!; f_equal; auto.
      + by exists None, None; repeat rewrite /op /option_op_instance /=.
  Qed.
  Canonical Structure optionR := Cmra (option A) option_cmra_mixin.

  Local Instance option_unit_instance : Unit (option A) := None.
  Lemma option_ucmra_mixin : UcmraMixin optionR.
  Proof. split; [done|  |done]. by intros []. Qed.
  Canonical Structure optionUR := Ucmra (option A) option_ucmra_mixin.

  (** Misc *)
  Lemma op_None ma mb : ma ⋅ mb = None ↔ ma = None ∧ mb = None.
  Proof. destruct ma, mb; naive_solver. Qed.
  Lemma op_is_Some ma mb : is_Some (ma ⋅ mb) ↔ is_Some ma ∨ is_Some mb.
  Proof. rewrite -!not_eq_None_Some op_None. destruct ma, mb; naive_solver. Qed.
  (* When the goal is already of the form [None ⋅ x], the [LeftId] instance for
     [ε] does not fire. *)
  Global Instance op_None_left_id : LeftId (=) None (@op (option A) _).
  Proof. intros [a|]; done. Qed.
  Global Instance op_None_right_id : RightId (=) None (@op (option A) _).
  Proof. intros [a|]; done. Qed.

  Lemma cmra_opM_opM_assoc a mb mc : a ⋅? mb ⋅? mc = a ⋅? (mb ⋅ mc).
  Proof. destruct mb, mc; by rewrite /= -?assoc. Qed.
  Lemma cmra_opM_opM_swap a mb mc : a ⋅? mb ⋅? mc = a ⋅? mc ⋅? mb.
  Proof. by rewrite !cmra_opM_opM_assoc (comm _ mb). Qed.
  Lemma cmra_opM_fmap_Some ma1 ma2 : ma1 ⋅? (Some <$> ma2) = ma1 ⋅ ma2.
  Proof. by destruct ma1, ma2. Qed.

  Global Instance Some_core_id a : CoreId a → CoreId (Some a).
  Proof. intros H. unfold CoreId,pcore,option_pcore_instance,cmra_pcore. simpl. f_equal. done. Qed.
  Global Instance option_core_id ma : (∀ x : A, CoreId x) → CoreId ma.
  Proof. intros. destruct ma; apply _. Qed.

  Lemma exclusive_Some_l a `{!Exclusive a} mb :
    ✓ (Some a ⋅ mb) → mb = None.
  Proof. destruct mb; last done. move=> /(exclusive_l a) []. Qed.
  Lemma exclusive_Some_ra `{!Exclusive a} mb :
    ✓ (mb ⋅ Some a) → mb = None.
  Proof. rewrite comm. by apply exclusive_Some_l. Qed.

  Lemma exclusive_Some_r a `{!Exclusive a} mb : ✓ (mb ⋅ Some a) → mb = None.
  Proof. rewrite comm. by apply exclusive_Some_l. Qed.

  Lemma Some_included a b : Some a ≼ Some b ↔ a = b ∨ a ≼ b.
  Proof. rewrite option_included; naive_solver. Qed.
  Lemma Some_included_1 a b : Some a ≼ Some b → a = b ∨ a ≼ b.
  Proof. rewrite Some_included. auto. Qed.
  Lemma Some_included_2 a b : a = b ∨ a ≼ b → Some a ≼ Some b.
  Proof. rewrite Some_included. auto. Qed.
  Lemma Some_included_mono a b : a ≼ b → Some a ≼ Some b.
  Proof. rewrite Some_included. auto. Qed.
  Lemma Some_included_refl a b : a = b → Some a ≼ Some b.
  Proof. rewrite Some_included. auto. Qed.
  Lemma Some_included_is_Some x mb : Some x ≼ mb → is_Some mb.
  Proof. rewrite option_included. naive_solver. Qed.

  Lemma Some_included_opM a b : Some a ≼ Some b ↔ ∃ mc, b = a ⋅? mc.
  Proof.
    rewrite /included. f_equiv=> mc. by rewrite -(inj_iff Some b) Some_op_opM.
  Qed.

  Lemma cmra_valid_Some_included a b : ✓ a → Some b ≼ Some a → ✓ b.
  Proof. apply: (cmra_valid_included (Some _) (Some _)). Qed.

  Lemma Some_included_total `{!CmraTotal A} a b : Some a ≼ Some b ↔ a ≼ b.
  Proof. rewrite Some_included. split; [|by eauto]. by intros [->|?]. Qed.

  Lemma Some_included_exclusive a `{!Exclusive a} b :
    Some a ≼ Some b → ✓ b → a = b.
  Proof. move=> /Some_included [//|/exclusive_included]; tauto. Qed.

  Lemma is_Some_included ma mb : ma ≼ mb → is_Some ma → is_Some mb.
  Proof. rewrite -!not_eq_None_Some option_included. naive_solver. Qed.

  Global Instance cancelable_Some a :
    IdFree a → Cancelable a → Cancelable (Some a).
  Proof.
    intros Hirr ?[b|] [c|] V EQ;
    rewrite /op /option_op_instance /cmra_op /= in EQ;
    inversion EQ.
    - f_equal. by apply (cancelable a).
    - destruct (Hirr b); [|done].
      by eapply (cmra_valid_op_l a b).
    - destruct (Hirr c); [|done].
      rewrite /op /option_op_instance /cmra_op /= in V.
      done.
    - done.
  Qed.

  Global Instance option_cancelable (ma : option A) :
    (∀ a : A, IdFree a) → (∀ a : A, Cancelable a) → Cancelable ma.
  Proof. destruct ma; apply _. Qed.
End option.

Global Arguments optionR : clear implicits.
Global Arguments optionUR : clear implicits.

Section option_prod.
  Context {A B : cmra}.
  Implicit Types a : A.
  Implicit Types b : B.

  Lemma Some_pair_included a1 a2 b1 b2 :
    Some (a1,b1) ≼ Some (a2,b2) → Some a1 ≼ Some a2 ∧ Some b1 ≼ Some b2.
  Proof. rewrite !Some_included. intros [EQ|[??]%prod_included]; eauto. injection EQ. naive_solver. Qed.
  Lemma Some_pair_included_l a1 a2 b1 b2 :
    Some (a1,b1) ≼ Some (a2,b2) → Some a1 ≼ Some a2.
  Proof. intros. eapply Some_pair_included. done. Qed.
  Lemma Some_pair_included_r a1 a2 b1 b2 :
    Some (a1,b1) ≼ Some (a2,b2) → Some b1 ≼ Some b2.
  Proof. intros. eapply Some_pair_included. done. Qed.
  Lemma Some_pair_included_total_1 `{CmraTotal A} a1 a2 b1 b2 :
    Some (a1,b1) ≼ Some (a2,b2) → a1 ≼ a2 ∧ Some b1 ≼ Some b2.
  Proof. intros ?%Some_pair_included. by rewrite -(Some_included_total a1). Qed.
  Lemma Some_pair_included_total_2 `{CmraTotal B} a1 a2 b1 b2 :
    Some (a1,b1) ≼ Some (a2,b2) → Some a1 ≼ Some a2 ∧ b1 ≼ b2.
  Proof. intros ?%Some_pair_included. by rewrite -(Some_included_total b1). Qed.
End option_prod.

Lemma option_fmap_mono {A B : cmra} (f : A → B) (ma mb : option A) :
  Proper ((=) ==> (=)) f →
  (∀ a b, a ≼ b → f a ≼ f b) →
  ma ≼ mb → f <$> ma ≼ f <$> mb.
Proof.
  intros ??. rewrite !option_included; intros [->|(a&b&->&->&?)]; naive_solver.
Qed.

Global Instance option_fmap_cmra_morphism {A B : cmra} (f: A → B) `{!CmraMorphism f} :
  CmraMorphism (fmap f : option A → option B).
Proof.
  split.
  - intros[a|] ?; rewrite /cmra_valid //=. by apply (cmra_morphism_valid f).
  - move=> [a|] //. simpl.
    rewrite /pcore /option_pcore_instance /cmra_pcore /=.
    rewrite /option_pcore_instance /=. f_equal. by apply cmra_morphism_pcore.
  - move=> [a|] [b|] //=. by rewrite (cmra_morphism_op f).
Qed.
