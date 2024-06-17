From stdpp Require Export list.

From Fairness Require Import big_op cmra.
From iris.prelude Require Import prelude options.

Local Open Scope iris_algebra_scope.


Lemma big_opL_ne_2 {M : Type} {o : M → M → M} `{!Monoid o} {A : Type} (f g : nat → A → M) l1 l2 :
  l1 = l2 →
  (∀ k y1 y2,
    l1 !! k = Some y1 → l2 !! k = Some y2 → y1 = y2 → f k y1 = g k y2) →
  ([^o list] k ↦ y ∈ l1, f k y) = ([^o list] k ↦ y ∈ l2, g k y).
Proof.
  intros Hl Hf. apply big_opL_gen_proper_2; try (apply _ || done).
  intros k. assert (l1 !! k = l2 !! k) as Hlk by (by f_equiv).
  destruct (l1 !! k) eqn:?, (l2 !! k) eqn:?; inversion Hlk; naive_solver.
Qed.

(** Functor *)
Lemma list_fmap_ext_ne {A} {B : Type} (f g : A → B) (l : list A) :
  (∀ x, f x = g x) → f <$> l = g <$> l.
Proof. intros Hf. by apply Forall_fmap_ext_1, Forall_true. Qed.
