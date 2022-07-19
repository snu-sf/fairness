Require ClassicalFacts.
Require FunctionalExtensionality.
(* Require ChoiceFacts. *)
Require Coq.Logic.Epsilon.
(* Require Classical_Prop. *)
Require Logic.Classical_Pred_Type.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.ClassicalEpsilon.

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
Lemma epsilon_spec: forall (A : Type) (i : inhabited A) (P : A -> Prop), (exists x : A, P x) -> P (epsilon _ i P).
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
