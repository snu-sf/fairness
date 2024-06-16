From Fairness Require Import gmap coPset local_updates cmra.
From Fairness Require Import updates proofmode_classes.
From iris.prelude Require Import prelude options.

Local Open Scope iris_algebra_scope.

(** The camera [reservation_map A] over a camera [A] extends [gmap positive A]
with a notion of "reservation tokens" for a (potentially infinite) set
[E : coPset] which represent the right to allocate a map entry at any position
[k ∈ E].  The key connectives are [reservation_map_data k a] (the "points-to"
assertion of this map), which associates data [a : A] with a key [k : positive],
and [reservation_map_token E] (the reservation token), which says
that no data has been associated with the indices in the mask [E]. The important
properties of this camera are:

- The lemma [reservation_map_token_union] enables one to split [reservation_map_token]
  w.r.t. disjoint union. That is, if we have [E1 ## E2], then we get
  [reservation_map_token (E1 ∪ E2) = reservation_map_token E1 ⋅ reservation_map_token E2].
- The lemma [reservation_map_alloc] provides a frame preserving update to
  associate data to a key: [reservation_map_token E ~~> reservation_map_data k a]
  provided [k ∈ E] and [✓ a].

In the future, it could be interesting to generalize this map to arbitrary key
types instead of hard-coding [positive]. *)

Record reservation_map (A : Type) := ReservationMap {
  reservation_map_data_proj : gmap positive A;
  reservation_map_token_proj : coPset_disj
}.
Add Printing Constructor reservation_map.
Global Arguments ReservationMap {_} _ _.
Global Arguments reservation_map_data_proj {_} _.
Global Arguments reservation_map_token_proj {_} _.
Global Instance: Params (@ReservationMap) 1 := {}.
Global Instance: Params (@reservation_map_data_proj) 1 := {}.
Global Instance: Params (@reservation_map_token_proj) 1 := {}.

Definition reservation_map_data {A : cmra} (k : positive) (a : A) : reservation_map A :=
  ReservationMap {[ k := a ]} ε.
Definition reservation_map_token {A : cmra} (E : coPset) : reservation_map A :=
  ReservationMap ∅ (CoPset E).
Global Instance: Params (@reservation_map_data) 2 := {}.

(* Ofe *)


(* Global Arguments reservation_mapO : clear implicits. *)

(* Camera *)
Section cmra.
  Context {A : cmra}.
  Implicit Types a b : A.
  Implicit Types x y : reservation_map A.
  Implicit Types k : positive.

  (* Global Instance reservation_map_data_ne i : NonExpansive (@reservation_map_data A i).
  Proof. solve_proper. Qed. *)
  Global Instance reservation_map_data_proper k :
    Proper ((=) ==> (=)) (@reservation_map_data A k).
  Proof. solve_proper. Qed.
  (* Global Instance reservation_map_data_discrete k a :
    Discrete a → Discrete (reservation_map_data k a).
  Proof. intros. apply ReservationMap_discrete; apply _. Qed. *)
  (* Global Instance reservation_map_token_discrete E : Discrete (@reservation_map_token A E).
  Proof. intros. apply ReservationMap_discrete; apply _. Qed. *)

  Local Instance reservation_map_valid_instance : Valid (reservation_map A) := λ x,
    match reservation_map_token_proj x with
    | CoPset E =>
      ✓ (reservation_map_data_proj x) ∧
      (* dom (reservation_map_data_proj x) ⊥ E *)
      ∀ i, reservation_map_data_proj x !! i = None ∨ i ∉ E
    | CoPsetBot => False
    end.
  Global Arguments reservation_map_valid_instance !_ /.
  Global Arguments reservation_map_valid_instance !_ /.
  Local Instance reservation_map_pcore_instance : PCore (reservation_map A) := λ x,
    Some (ReservationMap (core (reservation_map_data_proj x)) ε).
  Local Instance reservation_map_op_instance : Op (reservation_map A) := λ x y,
    ReservationMap (reservation_map_data_proj x ⋅ reservation_map_data_proj y)
                   (reservation_map_token_proj x ⋅ reservation_map_token_proj y).

  Definition reservation_map_valid_eq :
    valid = λ x, match reservation_map_token_proj x with
                 | CoPset E =>
                   ✓ (reservation_map_data_proj x) ∧
                   (* dom (reservation_map_data_proj x) ⊥ E *)
                   ∀ i, reservation_map_data_proj x !! i = None ∨ i ∉ E
                 | CoPsetBot => False
                 end := eq_refl _.

  Lemma reservation_map_included x y :
    x ≼ y ↔
      reservation_map_data_proj x ≼ reservation_map_data_proj y ∧
      reservation_map_token_proj x ≼ reservation_map_token_proj y.
  Proof.
    split.
    - intros [[z1 z2] Hz]. split; [exists z1|exists z2].
      + unfold op,reservation_map_op_instance in Hz. simpl in *.
        apply (f_equal reservation_map_data_proj) in Hz. simpl in *. done.
      + unfold op,reservation_map_op_instance in Hz. simpl in *.
      apply (f_equal reservation_map_token_proj) in Hz. simpl in *. done.
    - intros [[z1 Hz1] [z2 Hz2]]; exists (ReservationMap z1 z2).
      unfold op,reservation_map_op_instance. simpl. destruct x,y. simpl in *. f_equal; auto.
  Qed.

  Lemma reservation_map_data_proj_valid x : ✓ x → ✓ reservation_map_data_proj x.
  Proof. by destruct x as [? [?|]]=> // -[??]. Qed.
  Lemma reservation_map_token_proj_valid x : ✓ x → ✓ reservation_map_token_proj x.
  Proof. by destruct x as [? [?|]]=> // -[??]. Qed.


  Lemma reservation_map_cmra_mixin : CmraMixin (reservation_map A).
  Proof.
    apply cmra_total_mixin.
    - eauto.
    - intros [][][]. unfold op,reservation_map_op_instance. simpl. f_equal; simpl in *.
      all: by rewrite (assoc op).
    - intros [][]. unfold op,reservation_map_op_instance. simpl. f_equal; simpl in *.
      all: by rewrite (comm op).
    - intros []. unfold op,reservation_map_op_instance. simpl. f_equal; simpl in *;
      simpl; [by rewrite cmra_core_l|by rewrite left_id_L].
    - intros []. unfold op,reservation_map_op_instance. unfold core. simpl. f_equal;
      simpl; by rewrite cmra_core_idemp.
    - intros ??; rewrite! reservation_map_included; intros [??].
      by split; simpl; apply: cmra_core_mono. (* FIXME: FIXME(Coq #6294): needs new unification *)
    - intros [m1 [E1|]] [m2 [E2|]]=> //=; rewrite reservation_map_valid_eq /=.
      rewrite {1}/op /cmra_op /=. case_decide; last done.
      intros [Hm Hdisj]; split; first by eauto using cmra_valid_op_l.
      intros i. move: (Hdisj i). rewrite lookup_op.
      case: (m1 !! i); case: (m2 !! i); set_solver.
    - intros x y1 y2 ? ?; simpl in *.
      destruct (cmra_extend (reservation_map_data_proj x)
          (reservation_map_data_proj y1) (reservation_map_data_proj y2))
        as (m1&m2&?&?&?); auto using reservation_map_data_proj_valid.
      { apply (f_equal reservation_map_data_proj) in H0. rewrite H0. done. }
      destruct (cmra_extend (reservation_map_token_proj x)
          (reservation_map_token_proj y1) (reservation_map_token_proj y2))
        as (E1&E2&?&?&?); auto using reservation_map_token_proj_valid.
      { apply (f_equal reservation_map_token_proj) in H0. rewrite H0. done. }
      exists (ReservationMap m1 E1), (ReservationMap m2 E2). subst.
      split_and!.
      + unfold op,reservation_map_op_instance. simpl. done.
      + destruct y1; done.
      + destruct y2; done.
  Qed.
  Canonical Structure reservation_mapR :=
    Cmra (reservation_map A) reservation_map_cmra_mixin.

  (* Global Instance reservation_map_cmra_discrete :
    CmraDiscrete A → CmraDiscrete reservation_mapR.
  Proof.
    split; first apply _.
    intros [m [E|]]; rewrite reservation_map_valid_eq reservation_map_valid_eq //=.
      by intros [?%cmra_discrete_valid ?].
  Qed. *)

  Local Instance reservation_map_empty_instance : Unit (reservation_map A) := ReservationMap ε ε.
  Lemma reservation_map_ucmra_mixin : UcmraMixin (reservation_map A).
  Proof.
    split; simpl.
    - rewrite reservation_map_valid_eq /=. split; [apply ucmra_unit_valid|]. set_solver.
    - intros []. unfold ε,reservation_map_empty_instance,op,reservation_map_op_instance. simpl.
      f_equal; by rewrite left_id.
    - unfold ε,reservation_map_empty_instance,pcore,reservation_map_pcore_instance. do 2 f_equal.
      simpl. unfold core. rewrite ucmra_pcore_unit. done.
  Qed.
  Canonical Structure reservation_mapUR :=
    Ucmra (reservation_map A) reservation_map_ucmra_mixin.

  Global Instance reservation_map_data_core_id k a :
    CoreId a → CoreId (reservation_map_data k a).
  Proof.
    intros C. unfold CoreId. unfold pcore,cmra_pcore. simpl.
    unfold reservation_map_pcore_instance,reservation_map_data. simpl. do 2 f_equal.
    apply core_id_core, _.
  Qed.

  Lemma reservation_map_data_valid k a : ✓ (reservation_map_data k a) ↔ ✓ a.
  Proof. rewrite reservation_map_valid_eq /= singleton_valid. set_solver. Qed.
  Lemma reservation_map_token_valid E : ✓ (reservation_map_token E).
  Proof. rewrite reservation_map_valid_eq /=. split; first done. by left. Qed.
  Lemma reservation_map_data_op k a b :
    reservation_map_data k (a ⋅ b) = reservation_map_data k a ⋅ reservation_map_data k b.
  Proof.
      by rewrite {2}/op /reservation_map_op_instance /reservation_map_data /= singleton_op left_id_L.
  Qed.
  Lemma reservation_map_data_mono k a b :
    a ≼ b → reservation_map_data k a ≼ reservation_map_data k b.
  Proof. intros [c ->]. by rewrite reservation_map_data_op. Qed.
  Global Instance reservation_map_data_is_op k a b1 b2 :
    IsOp a b1 b2 →
    IsOp' (reservation_map_data k a) (reservation_map_data k b1) (reservation_map_data k b2).
  Proof. rewrite /IsOp' /IsOp=> ->. by rewrite reservation_map_data_op. Qed.

  Lemma reservation_map_token_union E1 E2 :
    E1 ## E2 →
    reservation_map_token (E1 ∪ E2) = reservation_map_token E1 ⋅ reservation_map_token E2.
  Proof.
    intros. by rewrite /op /reservation_map_op_instance
      /reservation_map_token /= coPset_disj_union // left_id_L.
  Qed.
  Lemma reservation_map_token_difference E1 E2 :
    E1 ⊆ E2 →
    reservation_map_token E2 = reservation_map_token E1 ⋅ reservation_map_token (E2 ∖ E1).
  Proof.
    intros. rewrite -reservation_map_token_union; last set_solver.
      by rewrite -union_difference_L.
  Qed.
  Lemma reservation_map_token_valid_op E1 E2 :
    ✓ (reservation_map_token E1 ⋅ reservation_map_token E2) ↔ E1 ## E2.
  Proof.
    rewrite reservation_map_valid_eq /= {1}/op /cmra_op /=. case_decide; last done.
    split; [done|]; intros _. split.
    - by rewrite left_id.
    - intros i. rewrite lookup_op lookup_empty. auto.
  Qed.

  Lemma reservation_map_alloc E k a :
    k ∈ E → ✓ a → reservation_map_token E ~~> reservation_map_data k a.
  Proof.
    intros ??. apply cmra_total_update. intros [mf [Ef|]]; last first.
    { unfold reservation_map_data,op,reservation_map_op_instance,cmra_op. simpl.
      unfold reservation_map_op_instance. simpl.
      unfold valid,cmra_valid. simpl. done.
    }
    rewrite reservation_map_valid_eq /= {1}/op {1}/cmra_op /=.
    case_decide; last done.
    rewrite !left_id_L. intros [Hmf Hdisj]; split.
    - destruct (Hdisj k) as [Hmfi|]; last set_solver.
      intros j. rewrite lookup_op.
      destruct (decide (k = j)) as [<-|].
      + rewrite Hmfi lookup_singleton right_id_L. done.
      + by rewrite lookup_singleton_ne // left_id_L.
    - intros j. destruct (decide (k = j)); first set_solver.
      rewrite lookup_op lookup_singleton_ne //.
      destruct (Hdisj j) as [Hmfi|?]; last set_solver. rewrite Hmfi; auto.
  Qed.
  Lemma reservation_map_updateP P (Q : reservation_map A → Prop) k a :
    a ~~>: P →
    (∀ a', P a' → Q (reservation_map_data k a')) →
    reservation_map_data k a ~~>: Q.
  Proof.
    intros Hup HP. apply cmra_total_updateP. intros [mf [Ef|]]; last first.
    { unfold reservation_map_data,op,reservation_map_op_instance,cmra_op. simpl.
      unfold reservation_map_op_instance. simpl.
      unfold valid,cmra_valid. simpl. done.
    }
    rewrite reservation_map_valid_eq /= left_id_L. intros [Hmf Hdisj].
    destruct (Hup (mf !! k)) as (a'&?&?).
    { move: (Hmf (k)).
      by rewrite lookup_op lookup_singleton Some_op_opM. }
    exists (reservation_map_data k a'); split; first by eauto.
    rewrite /= left_id_L. split.
    - intros j. destruct (decide (k = j)) as [<-|].
      + by rewrite lookup_op lookup_singleton Some_op_opM.
      + rewrite lookup_op lookup_singleton_ne // left_id_L.
        move: (Hmf j). rewrite lookup_op. eauto using cmra_valid_op_r.
    - intros j. move: (Hdisj j).
      rewrite !lookup_op !op_None !lookup_singleton_None. naive_solver.
  Qed.
  Lemma reservation_map_update k a b :
    a ~~> b →
    reservation_map_data k a ~~> reservation_map_data k b.
  Proof.
    rewrite !cmra_update_updateP. eauto using reservation_map_updateP with subst.
  Qed.
End cmra.

Global Arguments reservation_mapR : clear implicits.
Global Arguments reservation_mapUR : clear implicits.
