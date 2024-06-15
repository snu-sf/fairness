From Fairness Require Import cmra.
From iris.prelude Require Import prelude options.

Local Open Scope iris_algebra_scope.
Local Arguments valid _ _  !_ /.

Inductive excl (A : Type) :=
  | Excl : A → excl A
  | ExclBot : excl A.
Global Arguments Excl {_} _.
Global Arguments ExclBot {_}.

Global Instance: Params (@Excl) 1 := {}.
Global Instance: Params (@ExclBot) 1 := {}.

Notation excl' A := (option (excl A)).
Notation Excl' x := (Some (Excl x)).
Notation ExclBot' := (Some ExclBot).

Global Instance maybe_Excl {A} : Maybe (@Excl A) := λ x,
  match x with Excl a => Some a | _ => None end.

Section excl.
Context {A : Type}.
Implicit Types a b : A.
Implicit Types x y : excl A.


Global Instance Excl_proper : Proper ((=) ==> (=)) (@Excl A).
Proof. intros ??->. done. Qed.
Global Instance Excl_inj : Inj (=) (=) (@Excl A).
Proof. by inversion_clear 1. Qed.

(* CMRA *)
Local Instance excl_valid_instance : Valid (excl A) := λ x,
  match x with Excl _ => True | ExclBot => False end.
Local Instance excl_pcore_instance : PCore (excl A) := λ _, None.
Local Instance excl_op_instance : Op (excl A) := λ x y, ExclBot.

Lemma excl_cmra_mixin : CmraMixin (excl A).
Proof.
  split; try discriminate.
  - by intros [?|] [?|] [?|]; constructor.
  - by intros [?|] [?|]; constructor.
  - by intros [?|] [?|].
  - intros x [?|] [?|] ? Hx; eexists _, _; inversion_clear Hx; eauto.
Qed.
Canonical Structure exclR := Cmra (excl A) excl_cmra_mixin.

(** Exclusive *)
Global Instance excl_exclusive x : Exclusive x.
Proof. by destruct x; intros []. Qed.

(** Option excl *)
Lemma excl_valid_inv_l mx a : ✓ (Excl' a ⋅ mx) → mx = None.
Proof. by destruct mx. Qed.
Lemma excl_valid_inv_r mx a : ✓ (mx ⋅ Excl' a) → mx = None.
Proof. by destruct mx. Qed.

Lemma Excl_included a b : Excl' a ≼ Excl' b ↔ a = b.
Proof.
  split; [|by intros ->]. by intros [[c|] Hb%(inj Some)]; inversion_clear Hb.
Qed.
Lemma ExclBot_included ea : ea ≼ ExclBot.
Proof. by exists ExclBot. Qed.
End excl.

(* We use a [Hint Extern] with [apply:], instead of [Hint Immediate], to invoke
  the new unification algorithm. The old unification algorithm sometimes gets
  confused by going from [ucmra]'s to [cmra]'s and back. *)
Global Hint Extern 0 (_ ≼ ExclBot) => apply: ExclBot_included : core.

Global Arguments exclR : clear implicits.

(* Functor *)
Definition excl_map {A B} (f : A → B) (x : excl A) : excl B :=
  match x with Excl a => Excl (f a) | ExclBot => ExclBot end.
Lemma excl_map_id {A} (x : excl A) : excl_map id x = x.
Proof. by destruct x. Qed.
Lemma excl_map_compose {A B C} (f : A → B) (g : B → C) (x : excl A) :
  excl_map (g ∘ f) x = excl_map g (excl_map f x).
Proof. by destruct x. Qed.
Lemma excl_map_ext {A B : Type} (f g : A → B) x :
  (∀ x, f x = g x) → excl_map f x = excl_map g x.
Proof. destruct x; try constructor. simpl. intros. f_equal. done. Qed.
Global Instance excl_map_cmra_morphism {A B} (f : A → B) :
  CmraMorphism (excl_map f).
Proof. split; try done; try apply _. by intros [a|]. Qed.
