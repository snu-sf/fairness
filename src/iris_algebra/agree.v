From sflib Require Import sflib.
From Fairness Require Import cmra Axioms.
From iris.prelude Require Import prelude options.

Local Open Scope iris_algebra_scope.

Local Arguments valid _ _  !_ /.
Local Arguments op _ _ _ !_ /.
Local Arguments pcore _ _ !_ /.

(** Define an agreement construction such that Agree A is discrete when A is discrete.
    Notice that this construction is NOT complete.  The following is due to Aleš:

Proposition: Ag(T) is not necessarily complete.
Proof.
  Let T be the set of binary streams (infinite sequences) with the usual
  ultrametric, measuring how far they agree.

  Let Aₙ be the set of all binary strings of length n. Thus for Aₙ to be a
  subset of T we have them continue as a stream of zeroes.

  Now Aₙ is a finite non-empty subset of T. Moreover {Aₙ} is a Cauchy sequence
  in the defined (Hausdorff) metric.

  However the limit (if it were to exist as an element of Ag(T)) would have to
  be the set of all binary streams, which is not exactly finite.

  Thus Ag(T) is not necessarily complete.
*)

(** Note that the projection [agree_car] is not non-expansive, so it cannot be
used in the logic. If you need to get a witness out, you should use the
lemma [to_agree_uninjN] instead. In general, [agree_car] should ONLY be used
internally in this file.  *)
Record agree (A : Type) : Type := {
  agree_car : option A;
  (* agree_not_None : bool_decide (agree_car = None) = false *)
}.
Global Arguments agree_car {_} _.
(* Global Arguments agree_not_None {_} _. *)
Local Coercion agree_car : agree >-> option.

Definition to_agree {A} (a : A) : agree A :=
  {|
    agree_car := Some a;
    (* agree_not_None := eq_refl  *)
  |}.

(* Lemma elem_of_agree {A} (x : agree A) : ∃ a, a ∈ agree_car x.
Proof. destruct x as [[|a ?] ?]; set_solver+. Qed. *)
Lemma agree_eq {A} (x y : agree A) : agree_car x = agree_car y → x = y.
Proof.
  destruct x as [[a|]], y as [[b|]]; try done.
  intros EQ. injection EQ as ->. done.
Qed.

Section agree.
Context {A : Type}.
Implicit Types a b : A.
Implicit Types x y : agree A.

(* CMRA *)

Local Instance agree_valid_instance : Valid (agree A) := λ x,
  is_Some (agree_car x).

Local Program Instance agree_op_instance : Op (agree A) := λ x y,
  if excluded_middle_informative (x = y) then x else {| agree_car := None |}.
Local Instance agree_pcore_instance : PCore (agree A) := Some.

Lemma agree_valid_def x :
  ✓ x ↔ is_Some (agree_car x).
Proof.
  by rewrite /valid /agree_valid_instance.
Qed.
Lemma to_agree_valid a :
  ✓ to_agree a.
Proof. by apply agree_valid_def. Qed.

Local Instance agree_comm : Comm (=) (@op (agree A) _).
Proof. ii. unfold op,agree_op_instance. des_ifs. Qed.
Local Instance agree_assoc : Assoc (=) (@op (agree A) _).
Proof. ii. unfold op,agree_op_instance. des_ifs. Qed.

Lemma agree_idemp x : x ⋅ x = x.
Proof. unfold op,agree_op_instance. des_ifs. Qed.

(* Local Instance agree_valid_proper : Proper (equiv ==> iff) (@Valid (agree A) _ n).
Proof. move=> x y /equiv_dist H. by split; rewrite (H n). Qed. *)

Local Instance agree_op_proper : Proper ((=) ==> (=) ==> (=)) (op (A := agree A)).
Proof. intros x1 x2 -> y1 y2 ->. done. Qed.

Lemma agree_included x y : x ≼ y ↔ y = x ⋅ y.
Proof.
  split; [|by intros ?; exists y].
  by intros [z Hz]; rewrite Hz assoc agree_idemp.
Qed.

Lemma agree_op_inv x1 x2 : ✓ (x1 ⋅ x2) → x1 = x2.
Proof.
  rewrite agree_valid_def /=.
  unfold op,agree_op_instance. des_ifs.
  intros []%is_Some_None.
Qed.

Definition agree_cmra_mixin : CmraMixin (agree A).
Proof.
  apply cmra_total_mixin; try apply _ || by eauto.
  - intros [[|]]; simpl in *.
    all: unfold agree_op_instance,core,agree_pcore_instance.
    all: des_ifs.
  - intros x y. rewrite !agree_valid_def /=.
    unfold op,agree_op_instance,core,agree_pcore_instance.
    des_ifs. intros []%is_Some_None.
Qed.
Canonical Structure agreeR : cmra := Cmra (agree A) agree_cmra_mixin.

Global Instance agree_cmra_total : CmraTotal agreeR.
Proof. rewrite /CmraTotal; eauto. Qed.
Global Instance agree_core_id x : CoreId x.
Proof. by constructor. Qed.

(* Global Instance agree_cmra_discrete : TypeDiscrete A → CmraDiscrete agreeR.
Proof.
  intros HD. split.
  - intros x y [H H'] n; split=> a; setoid_rewrite <-(discrete_iff_0 _ _); auto.
  - intros x; rewrite agree_valid_def=> Hv n. apply agree_valid_def=> a b ??.
    apply discrete_iff_0; auto.
Qed. *)

Global Instance to_agree_proper : Proper ((=@{A}) ==> (=)) to_agree.
Proof. by intros a1 a2 ->. Qed.

(* Global Instance to_agree_discrete a : Discrete a → Discrete (to_agree a).
Proof.
  intros ? y [H H'] n; split.
  - intros a' ->%elem_of_list_singleton. destruct (H a) as [b ?]; first by left.
    exists b. by rewrite -discrete_iff_0.
  - intros b Hb. destruct (H' b) as (b'&->%elem_of_list_singleton&?); auto.
    exists a. by rewrite elem_of_list_singleton -discrete_iff_0.
Qed. *)

(* Lemma agree_op_inv x y : ✓ (x ⋅ y) → x = y.
Proof.
  intros ?. apply equiv_dist=> n. by apply agree_op_invN, cmra_valid_valid.
Qed. *)

(* Global Instance to_agree_injN n : Inj (dist n) (dist n) (to_agree).
Proof.
  move=> a b [_] /=. setoid_rewrite elem_of_list_singleton. naive_solver.
Qed. *)
Global Instance to_agree_inj : Inj (=@{A}) (=) (to_agree).
Proof. intros a b EQ. unfold to_agree in *. injection EQ. done. Qed.

Lemma to_agree_uninj x : ✓ x → ∃ a, to_agree a = x.
Proof.
  rewrite agree_valid_def=> Hv.
  destruct Hv as [a Hv].
  exists a. unfold to_agree. destruct x as [[x|]]; last done.
  simpl in *. by injection Hv as ->.
Qed.

Lemma agree_valid_included x y : ✓ y → x ≼ y → x = y.
Proof.
  move=> Hval [z Hy]; move: Hval; rewrite Hy.
  by move=> /agree_op_inv->; rewrite agree_idemp.
Qed.

Lemma to_agree_included a b : to_agree a ≼ to_agree b ↔ a = b.
Proof.
  split; last by intros ->.
  intros. apply (inj to_agree), agree_valid_included; [|done].
  apply to_agree_valid.
Qed.

Global Instance agree_cancelable x : Cancelable x.
Proof.
  intros y z Hv Heq.
  destruct (to_agree_uninj x) as [x' EQx]; first by eapply cmra_valid_op_l.
  destruct (to_agree_uninj y) as [y' EQy]; first by eapply cmra_valid_op_r.
  destruct (to_agree_uninj z) as [z' EQz].
  { eapply (cmra_valid_op_r x z). by rewrite -Heq. }
  assert (Hx'y' : x' = y').
  { apply (inj to_agree), agree_op_inv. by rewrite EQx EQy. }
  assert (Hx'z' : x' = z').
  { apply (inj to_agree), agree_op_inv. by rewrite EQx EQz -Heq. }
  by rewrite -EQy -EQz -Hx'y' -Hx'z'.
Qed.

Lemma to_agree_op_inv a b : ✓ (to_agree a ⋅ to_agree b) → a = b.
Proof. by intros ?%agree_op_inv%(inj to_agree). Qed.

Lemma to_agree_op_valid a b : ✓ (to_agree a ⋅ to_agree b) ↔ a = b.
Proof.
  split; first by apply to_agree_op_inv.
  intros ->. rewrite agree_idemp //.
  apply to_agree_valid.
Qed.

End agree.

Global Instance: Params (@to_agree) 1 := {}.
Global Arguments agreeR : clear implicits.

Program Definition agree_map {A B} (f : A → B) (x : agree A) : agree B :=
  {| agree_car := f <$> agree_car x |}.
Lemma agree_map_id {A} (x : agree A) : agree_map id x = x.
Proof. apply agree_eq. by rewrite /= option_fmap_id. Qed.
Lemma agree_map_compose {A B C} (f : A → B) (g : B → C) (x : agree A) :
  agree_map (g ∘ f) x = agree_map g (agree_map f x).
Proof. apply agree_eq. by rewrite /= option_fmap_compose. Qed.
Lemma agree_map_to_agree {A B} (f : A → B) (x : A) :
  agree_map f (to_agree x) = to_agree (f x).
Proof. by apply agree_eq. Qed.

Section agree_map.
  Context {A B : Type} (f : A → B).

  Local Instance agree_map_proper : Proper ((=) ==> (=)) (agree_map f).
  Proof. by intros ?? ->. Qed.

  Lemma agree_map_ext (g : A → B) x :
    (∀ a, f a = g a) → agree_map f x = agree_map g x.
  Proof.
    intros Hfg. apply agree_eq.
    unfold agree_map. do 2 f_equal.
    apply option_fmap_ext. done.
  Qed.

  (* TODO: This requires agree to have a addition that does not check for invalid elements, this is why Iris uses a list? *)
  (* TODO: this is needed fore `view.v` *)
  (* Global Instance agree_map_morphism : CmraMorphism (agree_map f).
  Proof.
    split.
    - intros x. rewrite !agree_valid_def=> Hv.
      destruct Hv as [a Hv]. exists (f a).
      unfold agree_map. destruct x as [[x|]]; [|done].
      simpl in *. injection Hv as ->. done.
    - done.
    - intros [[x|]] [[y|]]; simpl in *.
      all: unfold agree_map,op,cmra_op.
      all: simpl in *.
      all: unfold agree_op_instance.
      all: des_ifs.
      simpl.
      unfold Proper in *.
  Qed. *)
End agree_map.
