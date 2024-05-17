Require ClassicalFacts.
Require FunctionalExtensionality.
(* Require ChoiceFacts. *)
Require Coq.Logic.Epsilon.
(* Require Classical_Prop. *)
Require Logic.Classical_Pred_Type.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.ClassicalEpsilon.
Require Import Coq.Logic.IndefiniteDescription.
Require Import Coq.Logic.PropExtensionality.


Set Implicit Arguments.

Lemma func_ext_dep {A} {B: A -> Type} (f g: forall x, B x): (forall x, f x = g x) -> f = g.
Proof.
  apply @FunctionalExtensionality.functional_extensionality_dep.
Qed.

Lemma func_ext {A B} (f g: A -> B): (forall x, f x = g x) -> f = g.
Proof.
  apply func_ext_dep.
Qed.

Definition classic := Classical_Prop.classic.
Definition inj_pair2 := Classical_Prop.EqdepTheory.inj_pair2.

Definition epsilon_on := ChoiceFacts.EpsilonStatement_on.
Definition epsilon := Epsilon.epsilon.
Lemma epsilon_spec: forall (A : Type) (i : inhabited A) (P : A -> Prop), (exists x : A, P x) -> P (epsilon i P).
Proof.
  apply Epsilon.epsilon_spec.
Qed.

Lemma not_ex_all_not_help
      A (P: A -> Prop)
      (NOT: ~ (exists a: A, P a))
  :
  forall a, ~ P a.
Proof.
  intros. eapply Classical_Pred_Type.not_ex_all_not in NOT. eauto.
Qed.

Ltac nean H := eapply not_ex_all_not_help in H; red in H.

Definition proof_irrelevance := proof_irrelevance.
Definition excluded_middle_informative := excluded_middle_informative.
Definition choice := choice.

Lemma dependent_functional_choice (A : Type) (B : A -> Type) :
  forall R : forall x : A, B x -> Prop,
    (forall x : A, exists y : B x, R x y) ->
    (exists f : (forall x : A, B x), forall x : A, R x (f x)).
Proof.
  eapply ChoiceFacts.non_dep_dep_functional_choice.
  clear. exact functional_choice.
Qed.

Definition propositional_extensionality := propositional_extensionality.
