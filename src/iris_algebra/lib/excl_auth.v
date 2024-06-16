From Fairness Require Import auth excl updates.
From Fairness Require Import local_updates cmra.
From iris.prelude Require Import prelude options.

Local Open Scope iris_algebra_scope.

(** Authoritative CMRA where the fragment is exclusively owned.
This is effectively a single "ghost variable" with two views, the frament [◯E a]
and the authority [●E a]. *)

Definition excl_authR (A : Type) : cmra :=
  authR (optionUR (exclR A)).
Definition excl_authUR (A : Type) : ucmra :=
  authUR (optionUR (exclR A)).

Definition excl_auth_auth {A : Type} (a : A) : excl_authR A :=
  ● (Some (Excl a)).
Definition excl_auth_frag {A : Type} (a : A) : excl_authR A :=
  ◯ (Some (Excl a)).

Global Typeclasses Opaque excl_auth_auth excl_auth_frag.

Global Instance: Params (@excl_auth_auth) 1 := {}.
Global Instance: Params (@excl_auth_frag) 2 := {}.

Notation "●E a" := (excl_auth_auth a) (at level 10).
Notation "◯E a" := (excl_auth_frag a) (at level 10).

Section excl_auth.
  Context {A : Type}.
  Implicit Types a b : A.

  (* Global Instance excl_auth_auth_ne : NonExpansive (@excl_auth_auth A).
  Proof. solve_proper. Qed. *)
  Global Instance excl_auth_auth_proper : Proper ((=) ==> (=)) (@excl_auth_auth A).
  Proof. solve_proper. Qed.
  (* Global Instance excl_auth_frag_ne : NonExpansive (@excl_auth_frag A).
  Proof. solve_proper. Qed. *)
  Global Instance excl_auth_frag_proper : Proper ((=) ==> (=)) (@excl_auth_frag A).
  Proof. solve_proper. Qed.

  (* Global Instance excl_auth_auth_discrete a : Discrete a → Discrete (●E a).
  Proof. intros; apply auth_auth_discrete; [apply Some_discrete|]; apply _. Qed.
  Global Instance excl_auth_frag_discrete a : Discrete a → Discrete (◯E a).
  Proof. intros; apply auth_frag_discrete, Some_discrete; apply _. Qed. *)

  Lemma excl_auth_valid a : ✓ (●E a ⋅ ◯E a).
  Proof. by rewrite auth_both_valid. Qed.

  Lemma excl_auth_agree a b : ✓ (●E a ⋅ ◯E b) → a = b.
  Proof.
    rewrite auth_both_valid /= => -[Hincl Hvalid].
    move: Hincl=> /Some_included_exclusive /(_ I) ?. by apply (inj Excl).
  Qed.
  Lemma excl_auth_agree_L a b : ✓ (●E a ⋅ ◯E b) → a = b.
  Proof. intros. by apply excl_auth_agree. Qed.

  Lemma excl_auth_auth_op_valid a b : ✓ (●E a ⋅ ●E b) ↔ False.
  Proof. apply auth_auth_op_valid. Qed.

  Lemma excl_auth_frag_op_valid a b : ✓ (◯E a ⋅ ◯E b) ↔ False.
  Proof. by rewrite -auth_frag_op auth_frag_valid. Qed.

  Lemma excl_auth_update a b a' : ●E a ⋅ ◯E b ~~> ●E a' ⋅ ◯E a'.
  Proof.
    intros. by apply auth_update, option_local_update, exclusive_local_update.
  Qed.
End excl_auth.

(* Definition excl_authURF (F : oFunctor) : urFunctor :=
  authURF (optionURF (exclRF F)).

Global Instance excl_authURF_contractive F :
  oFunctorContractive F → urFunctorContractive (excl_authURF F).
Proof. apply _. Qed.

Definition excl_authRF (F : oFunctor) : rFunctor :=
  authRF (optionURF (exclRF F)).

Global Instance excl_authRF_contractive F :
  oFunctorContractive F → rFunctorContractive (excl_authRF F).
Proof. apply _. Qed. *)
