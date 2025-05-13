From sflib Require Import sflib.
Require Import Program.
From Fairness Require Import Axioms.

Set Implicit Arguments.


Module Type ANY.

  Parameter t: Type.
  Parameter upcast: forall {T: Type}, T -> t.
  Parameter downcast: forall {T: Type}, t -> option T.

  Parameter upcast_downcast: forall T (v: T), downcast (upcast v) = Some v.
  Parameter downcast_upcast: forall T (v: T) (a: t), downcast a = Some v -> <<CAST: upcast v = a>>.
  Parameter upcast_inj: forall A B (a: A) (b: B) (EQ: upcast a = upcast b),
      <<EQ: A = B>> /\ <<EQ: JMeq a b>>.

  Parameter pair: t -> t -> t.
  Parameter split: t -> option (t * t).
  Parameter pair_split: forall (a0 a1: t), split (pair a0 a1) = Some (a0, a1).
  Parameter split_pair: forall (a a0 a1: t), split a = Some (a0, a1) -> <<PAIR: a = pair a0 a1>>.

  Parameter upcast_split: forall T (v: T), split (upcast v) = None.
  Parameter pair_downcast: forall a0 a1 T, @downcast T (pair a0 a1) = None.

End ANY.


Module _Any: ANY.

  Record box := box_intro { ty: Type; val: ty }.

  Inductive _t: Type :=
  | _upcast (b: box)
  | _pair (a0 a1: _t)
  .

  Definition t := _t.

  Definition upcast {ty} val := _upcast (@box_intro ty val).

  Definition pair := @_pair.

  Definition _downcast {T: Type} (b: box): option T :=
    match (excluded_middle_informative (b.(ty) = T)) with
    | left e =>
      Some (match e in (_ = y0) return ((fun X => X) y0) with
            | eq_refl => b.(val)
            end)
    | right _ => None
    end.

  Definition downcast {T: Type} (a: t): option T :=
    match a with
    | _upcast b => _downcast b
    | _pair _ _ => None
    end.

  Definition split (a: t): option (t * t) :=
    match a with
    | _upcast _ => None
    | _pair a0 a1 => Some (a0, a1)
    end.

  Lemma upcast_downcast
        T (a: T)
    :
      downcast (upcast a) = Some a
  .
  Proof.
    ss. unfold _downcast. ss.
    replace (excluded_middle_informative (T = T))
      with (@left _ (T <> T) (@eq_refl _ T)); ss.
    destruct (excluded_middle_informative (T = T)); ss.
    f_equal. eapply proof_irrelevance.
  Qed.

  Lemma downcast_upcast: forall T (v: T) (a: t), downcast a = Some v -> <<CAST: upcast v = a>>.
  Proof.
    i. unfold upcast, downcast, _downcast in *. des_ifs. destruct b. ss.
  Qed.

  Lemma upcast_inj
        A B (a: A) (b: B)
        (EQ: upcast a = upcast b)
    :
      <<EQ: A = B>> /\ <<EQ: JMeq a b>>
  .
  Proof. unfold upcast in *. simpl_depind. ss. Qed.

  Lemma pair_split (a0 a1: t)
    :
      split (pair a0 a1) = Some (a0, a1).
  Proof. ss. Qed.

  Lemma split_pair (a a0 a1: t) (SPLIT: split a = Some (a0, a1))
    :
      <<PAIR: a = pair a0 a1>>.
  Proof. unfold split in *. des_ifs. Qed.

  Lemma upcast_split T (v: T)
    :
      split (upcast v) = None.
  Proof. ss. Qed.

  Lemma pair_downcast a0 a1 T
    :
      @downcast T (pair a0 a1) = None.
  Proof. ss. Qed.

End _Any.


Module Any.
  Include _Any.
  Lemma pair_inj: forall a b c d, Any.pair a b = Any.pair c d -> <<EQ: a = c /\ b = d>>.
  Proof.
    i. destruct (split (pair a b)) eqn:T.
    - dup T. rewrite H in T0. rewrite <- T0 in T. rewrite ! pair_split in *. clarify.
    - dup T. rewrite H in T0. rewrite <- T0 in T. rewrite ! pair_split in *. clarify.
  Qed.
End Any.

(* Notation "↑ a" := (Any.upcast a) (at level 60, only parsing). *)
(* Notation "↓ a" := (Any.downcast a) (at level 60, only parsing). *)
(* Goal (↓↑ tt) = Some tt. rewrite Any.upcast_downcast. ss. Qed. *)
(* Check (Any.pair ↑tt ↑tt). *)
Notation "a ↑" := (Any.upcast a) (at level 9, only parsing).
Notation "a ↓" := (Any.downcast a) (at level 9, only parsing).
Notation "(↑)" := (Any.upcast) (only parsing).
Notation "(↓)" := (Any.downcast) (only parsing).
Goal (tt↑↓) = Some tt. rewrite Any.upcast_downcast. ss. Qed.
Check (Any.pair tt↑ tt↑).
