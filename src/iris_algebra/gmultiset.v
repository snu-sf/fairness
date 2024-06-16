From stdpp Require Export sets gmultiset countable.
From Fairness Require Import cmra.
From Fairness Require Import updates local_updates big_op.
From iris.prelude Require Import prelude options.

Local Open Scope iris_algebra_scope.

(* The multiset union CMRA *)
Section gmultiset.
  Context `{Countable K}.
  Implicit Types X Y : gmultiset K.

  Local Instance gmultiset_valid_instance : Valid (gmultiset K) := λ _, True.
  Local Instance gmultiset_unit_instance : Unit (gmultiset K) := (∅ : gmultiset K).
  Local Instance gmultiset_op_instance : Op (gmultiset K) := disj_union.
  Local Instance gmultiset_pcore_instance : PCore (gmultiset K) := λ X, Some ∅.

  Lemma gmultiset_op X Y : X ⋅ Y = X ⊎ Y.
  Proof. done. Qed.
  Lemma gmultiset_core X : core X = ∅.
  Proof. done. Qed.
  Lemma gmultiset_included X Y : X ≼ Y ↔ X ⊆ Y.
  Proof.
    split.
    - intros [Z ->].
      rewrite gmultiset_op. apply gmultiset_disj_union_subseteq_l.
    - intros ->%gmultiset_disj_union_difference. by exists (Y ∖ X).
  Qed.

  Lemma gmultiset_ra_mixin : RAMixin (gmultiset K).
  Proof.
    apply ra_total_mixin; eauto.
    - by intros X Y Z ->.
    - by intros X Y ->.
    - solve_proper.
    - intros X1 X2 X3. by rewrite !gmultiset_op assoc_L.
    - intros X1 X2. by rewrite !gmultiset_op comm_L.
    - intros X. by rewrite gmultiset_core left_id.
    - intros X1 X2 HX. rewrite !gmultiset_core. exists ∅.
      by rewrite left_id.
  Qed.

  Canonical Structure gmultisetR := discreteR (gmultiset K) gmultiset_ra_mixin.

  (* Global Instance gmultiset_cmra_discrete : CmraDiscrete gmultisetR.
  Proof. apply discrete_cmra_discrete. Qed. *)

  Lemma gmultiset_ucmra_mixin : UcmraMixin (gmultiset K).
  Proof.
    split; [done | | done]. intros X.
    by rewrite gmultiset_op left_id_L.
  Qed.
  Canonical Structure gmultisetUR := Ucmra (gmultiset K) gmultiset_ucmra_mixin.

  Global Instance gmultiset_cancelable X : Cancelable X.
  Proof.
    intros Y Z _ ?. by apply (inj (X ⊎.)).
  Qed.

  Lemma gmultiset_opM X mY : X ⋅? mY = X ⊎ default ∅ mY.
  Proof. destruct mY; by rewrite /= ?right_id_L. Qed.

  Lemma gmultiset_update X Y : X ~~> Y.
  Proof. done. Qed.

  Lemma gmultiset_local_update X Y X' Y' : X ⊎ Y' = X' ⊎ Y → (X,Y) ~l~> (X', Y').
  Proof.
    intros HXY. rewrite local_update_unital_discrete=> Z' _. intros ->.
    split; first done. apply (inj (.⊎ Y)).
    rewrite -HXY !gmultiset_op.
    by rewrite -(comm_L _ Y) (comm_L _ Y') assoc_L.
  Qed.

  Lemma gmultiset_local_update_alloc X Y X' : (X,Y) ~l~> (X ⊎ X', Y ⊎ X').
  Proof. apply gmultiset_local_update. by rewrite (comm_L _ Y) assoc_L. Qed.

  Lemma gmultiset_local_update_dealloc X Y X' :
    X' ⊆ Y → (X,Y) ~l~> (X ∖ X', Y ∖ X').
  Proof.
    intros ->%gmultiset_disj_union_difference. apply local_update_total_valid.
    intros _ _ ->%gmultiset_included%gmultiset_disj_union_difference.
    apply gmultiset_local_update. apply gmultiset_eq=> x.
    repeat (rewrite multiplicity_difference || rewrite multiplicity_disj_union).
    lia.
  Qed.

  (* Lemma big_opMS_singletons X :
    ([^op mset] x ∈ X, {[+ x +]}) = X.
  Proof.
    induction X as [|x X IH] using gmultiset_ind.
    - rewrite big_opMS_empty. done.
    - unfold_leibniz. rewrite big_opMS_disj_union // big_opMS_singleton IH //.
  Qed. *)

End gmultiset.

Global Arguments gmultisetR _ {_ _}.
Global Arguments gmultisetUR _ {_ _}.
