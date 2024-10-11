From sflib Require Import sflib.
Require Import Coq.Classes.RelationClasses.

From Fairness Require Import Axioms.

Require Import Program.

Set Implicit Arguments.

Module OrderedCM.
  Class t (car: Type) :=
    mk { le: car -> car -> Prop;
         unit: car;
         add: car -> car -> car;

         #[global] le_PreOrder:: PreOrder le;
         le_total: forall a0 a1, le a0 a1 \/ le a1 a0;
         add_assoc_le: forall a0 a1 a2, le (add a0 (add a1 a2)) (add (add a0 a1) a2);
         add_comm_le: forall a0 a1, le (add a0 a1) (add a1 a0);
         add_unit_le_l: forall a, le (add a unit) a;
         add_base_l: forall a0 a1, le a0 (add a0 a1);
         le_add_l: forall a0 a1 a2 (LE: le a1 a2), le (add a0 a1) (add a0 a2);
      }.

  Section MONOID.
    Variable car: Type.
    Context `{t car}.

    Definition eq (a0 a1: car): Prop := le a0 a1 /\ le a1 a0.

    Global Program Instance eq_Equivalence: Equivalence eq.
    Next Obligation.
    Proof.
      unfold eq. ii. split.
      { reflexivity. }
      { reflexivity. }
    Qed.
    Next Obligation.
    Proof.
      unfold eq. ii. des. split; auto.
    Qed.
    Next Obligation.
    Proof.
      unfold eq. ii. des. split.
      { etransitivity; eauto. }
      { etransitivity; eauto. }
    Qed.

    Lemma add_assoc_eq a0 a1 a2
      :
      eq (add a0 (add a1 a2)) (add (add a0 a1) a2).
    Proof.
      split.
      { eapply add_assoc_le. }
      { etransitivity.
        { eapply add_comm_le. }
        etransitivity.
        { eapply add_assoc_le. }
        etransitivity.
        { eapply add_comm_le. }
        etransitivity.
        { eapply add_assoc_le. }
        { eapply add_comm_le. }
      }
    Qed.

    Lemma add_comm_eq a0 a1
      :
      eq (add a0 a1) (add a1 a0).
    Proof.
      split.
      { eapply add_comm_le. }
      { eapply add_comm_le. }
    Qed.

    Lemma add_unit_le_r a
      :
      le (add unit a) a.
    Proof.
      etransitivity.
      { eapply add_comm_le. }
      { eapply add_unit_le_l. }
    Qed.

    Lemma add_unit_eq_l a
      :
      eq (add a unit) a.
    Proof.
      split.
      { apply add_unit_le_l. }
      { apply add_base_l. }
    Qed.

    Lemma add_unit_eq_r a
      :
      eq (add unit a) a.
    Proof.
      etransitivity.
      { eapply add_comm_eq. }
      { eapply add_unit_eq_l. }
    Qed.

    Lemma add_base_r a0 a1
      :
      le a1 (add a0 a1).
    Proof.
      etransitivity.
      { eapply add_base_l. }
      { eapply add_comm_le. }
    Qed.

    Lemma le_add_r a0 a1 a2
          (LE: le a0 a1)
      :
      le (add a0 a2) (add a1 a2).
    Proof.
      i. etransitivity.
      { eapply add_comm_le. }
      etransitivity.
      { eapply le_add_l; eauto. }
      { eapply add_comm_le. }
    Qed.

    Lemma le_unit a
      :
      le unit a.
    Proof.
      etransitivity.
      { eapply add_base_r. }
      { eapply add_unit_le_l. }
    Qed.

    Lemma eq_add_l a0 a1 a2
          (EQ: eq a1 a2)
      :
      eq (add a0 a1) (add a0 a2).
    Proof.
      unfold eq in *. des. split.
      { eapply le_add_l; eauto. }
      { eapply le_add_l; eauto. }
    Qed.

    Lemma eq_add_r a0 a1 a2
          (EQ: eq a0 a1)
      :
      eq (add a0 a2) (add a1 a2).
    Proof.
      unfold eq in *. des. split.
      { eapply le_add_r; eauto. }
      { eapply le_add_r; eauto. }
    Qed.

    Definition join (a0 a1: car): car :=
      if (excluded_middle_informative (le a0 a1)) then a1 else a0.

    Lemma join_l a0 a1
      :
      le a0 (join a0 a1).
    Proof.
      unfold join. des_ifs. reflexivity.
    Qed.

    Lemma join_r a0 a1
      :
      le a1 (join a0 a1).
    Proof.
      unfold join. des_ifs.
      { reflexivity. }
      { destruct (le_total a0 a1); ss. }
    Qed.

    Lemma join_supremum a0 a1 a
          (LE0: le a0 a)
          (LE1: le a1 a)
      :
      le (join a0 a1) a.
    Proof.
      unfold join. des_ifs.
    Qed.

    Lemma join_assoc_le a0 a1 a2
      :
      le (join a0 (join a1 a2)) (join (join a0 a1) a2).
    Proof.
      eapply join_supremum.
      { etransitivity.
        { eapply join_l. }
        { eapply join_l. }
      }
      { eapply join_supremum.
        { etransitivity.
          { eapply join_r. }
          { eapply join_l. }
        }
        { eapply join_r. }
      }
    Qed.

    Lemma join_comm_le a0 a1
      :
      le (join a0 a1) (join a1 a0).
    Proof.
      eapply join_supremum.
      { eapply join_r. }
      { eapply join_l. }
    Qed.

    Lemma join_unit_le_l a
      :
      le (join a unit) a.
    Proof.
      eapply join_supremum.
      { reflexivity. }
      { eapply le_unit. }
    Qed.

    Lemma le_join_l a0 a1 a2
          (LE: le a1 a2)
      :
      le (join a0 a1) (join a0 a2).
    Proof.
      eapply join_supremum.
      { eapply join_l. }
      { etransitivity; eauto. eapply join_r. }
    Qed.

    Lemma join_assoc_eq a0 a1 a2
      :
      eq (join a0 (join a1 a2)) (join (join a0 a1) a2).
    Proof.
      split.
      { eapply join_assoc_le. }
      { etransitivity.
        { eapply join_comm_le. }
        etransitivity.
        { eapply join_assoc_le. }
        etransitivity.
        { eapply join_comm_le. }
        etransitivity.
        { eapply join_assoc_le. }
        { eapply join_comm_le. }
      }
    Qed.

    Lemma join_comm_eq a0 a1
      :
      eq (join a0 a1) (join a1 a0).
    Proof.
      split.
      { eapply join_comm_le. }
      { eapply join_comm_le. }
    Qed.

    Lemma join_unit_le_r a
      :
      le (join unit a) a.
    Proof.
      etransitivity.
      { eapply join_comm_le. }
      { eapply join_unit_le_l. }
    Qed.

    Lemma join_unit_eq_l a
      :
      eq (join a unit) a.
    Proof.
      split.
      { apply join_unit_le_l. }
      { apply join_l. }
    Qed.

    Lemma join_unit_eq_r a
      :
      eq (join unit a) a.
    Proof.
      etransitivity.
      { eapply join_comm_eq. }
      { eapply join_unit_eq_l. }
    Qed.

    Lemma join_base_r a0 a1
      :
      le a1 (join a0 a1).
    Proof.
      etransitivity.
      { eapply join_l. }
      { eapply join_comm_le. }
    Qed.

    Lemma le_join_r a0 a1 a2
          (LE: le a0 a1)
      :
      le (join a0 a2) (join a1 a2).
    Proof.
      i. etransitivity.
      { eapply join_comm_le. }
      etransitivity.
      { eapply le_join_l; eauto. }
      { eapply join_comm_le. }
    Qed.

    Lemma eq_join_l a0 a1 a2
          (EQ: eq a1 a2)
      :
      eq (join a0 a1) (join a0 a2).
    Proof.
      unfold eq in *. des. split.
      { eapply le_join_l; eauto. }
      { eapply le_join_l; eauto. }
    Qed.

    Lemma eq_join_r a0 a1 a2
          (EQ: eq a0 a1)
      :
      eq (join a0 a2) (join a1 a2).
    Proof.
      unfold eq in *. des. split.
      { eapply le_join_r; eauto. }
      { eapply le_join_r; eauto. }
    Qed.

    Definition meet (a0 a1: car): car :=
      if (excluded_middle_informative (le a0 a1)) then a0 else a1.

    Lemma meet_l a0 a1
      :
      le (meet a0 a1) a0.
    Proof.
      unfold meet. des_ifs.
      { reflexivity. }
      { destruct (le_total a0 a1); ss. }
    Qed.

    Lemma meet_r a0 a1
      :
      le (meet a0 a1) a1.
    Proof.
      unfold meet. des_ifs. reflexivity.
    Qed.

    Lemma meet_infimum a0 a1 a
          (LE0: le a a0)
          (LE1: le a a1)
      :
      le a (meet a0 a1).
    Proof.
      unfold meet. des_ifs.
    Qed.

    Lemma meet_assoc_le a0 a1 a2
      :
      le (meet a0 (meet a1 a2)) (meet (meet a0 a1) a2).
    Proof.
      eapply meet_infimum.
      { eapply meet_infimum.
        { eapply meet_l. }
        { etransitivity.
          { eapply meet_r. }
          { eapply meet_l. }
        }
      }
      { etransitivity.
        { eapply meet_r. }
        { eapply meet_r. }
      }
    Qed.

    Lemma meet_comm_le a0 a1
      :
      le (meet a0 a1) (meet a1 a0).
    Proof.
      eapply meet_infimum.
      { eapply meet_r. }
      { eapply meet_l. }
    Qed.

    Lemma le_meet_l a0 a1 a2
          (LE: le a1 a2)
      :
      le (meet a0 a1) (meet a0 a2).
    Proof.
      eapply meet_infimum.
      { eapply meet_l. }
      { etransitivity; eauto. eapply meet_r. }
    Qed.

    Lemma meet_assoc_eq a0 a1 a2
      :
      eq (meet a0 (meet a1 a2)) (meet (meet a0 a1) a2).
    Proof.
      split.
      { eapply meet_assoc_le. }
      { etransitivity.
        { eapply meet_comm_le. }
        etransitivity.
        { eapply meet_assoc_le. }
        etransitivity.
        { eapply meet_comm_le. }
        etransitivity.
        { eapply meet_assoc_le. }
        { eapply meet_comm_le. }
      }
    Qed.

    Lemma meet_comm_eq a0 a1
      :
      eq (meet a0 a1) (meet a1 a0).
    Proof.
      split.
      { eapply meet_comm_le. }
      { eapply meet_comm_le. }
    Qed.

    Lemma meet_unit_eq_l a
      :
      eq (meet a unit) unit.
    Proof.
      split.
      { apply meet_r. }
      { apply le_unit. }
    Qed.

    Lemma meet_unit_eq_r a
      :
      eq (meet unit a) unit.
    Proof.
      split.
      { apply meet_l. }
      { apply le_unit. }
    Qed.

    Lemma le_meet_r a0 a1 a2
          (LE: le a0 a1)
      :
      le (meet a0 a2) (meet a1 a2).
    Proof.
      i. etransitivity.
      { eapply meet_comm_le. }
      etransitivity.
      { eapply le_meet_l; eauto. }
      { eapply meet_comm_le. }
    Qed.

    Lemma eq_meet_l a0 a1 a2
          (EQ: eq a1 a2)
      :
      eq (meet a0 a1) (meet a0 a2).
    Proof.
      unfold eq in *. des. split.
      { eapply le_meet_l; eauto. }
      { eapply le_meet_l; eauto. }
    Qed.

    Lemma eq_meet_r a0 a1 a2
          (EQ: eq a0 a1)
      :
      eq (meet a0 a2) (meet a1 a2).
    Proof.
      unfold eq in *. des. split.
      { eapply le_meet_r; eauto. }
      { eapply le_meet_r; eauto. }
    Qed.
  End MONOID.
End OrderedCM.

Require Import PeanoNat Lia.

Global Program Instance nat_OrderedCM: OrderedCM.t nat :=
  @OrderedCM.mk _ Nat.le 0 Nat.add _ _ _ _ _ _ _ .
Next Obligation. Proof. lia. Qed.
Next Obligation. Proof. lia. Qed.
Next Obligation. Proof. lia. Qed.
Next Obligation. Proof. lia. Qed.
Next Obligation. Proof. lia. Qed.
Next Obligation. Proof. lia. Qed.

From Fairness Require Import WFLibLarge.
From Ordinal Require Export Ordinal Hessenberg ClassicalOrdinal.

Definition owf: WF := mk_wf Ord.lt_well_founded.

Global Program Instance ord_OrderedCM: OrderedCM.t Ord.t :=
  @OrderedCM.mk _ Ord.le Ord.O Hessenberg.add _ _ _ _ _ _ _ .
Next Obligation.
Proof.
  eapply ClassicOrd.total_le.
Qed.
Next Obligation.
Proof.
  eapply Hessenberg.add_assoc.
Qed.
Next Obligation.
Proof.
  eapply Hessenberg.add_comm.
Qed.
Next Obligation.
Proof.
  eapply Hessenberg.add_O_r.
Qed.
Next Obligation.
Proof.
  eapply Hessenberg.add_base_l.
Qed.
Next Obligation.
Proof.
  eapply Hessenberg.le_add_r; eauto.
Qed.

Lemma ord_OrderedCM_eq (a0 a1: Ord.t):
  OrderedCM.eq a0 a1 <-> Ord.eq a0 a1.
Proof.
  auto.
Qed.

Lemma nat_OrderedCM_eq (a0 a1: nat):
  OrderedCM.eq a0 a1 <-> a0 = a1.
Proof.
  split.
  { i. red in H. des. ss. lia. }
  { i. subst. reflexivity. }
Qed.

Module SOrderedCM.
  Class t (car: Type) `{OrderedCM.t car} :=
    mk { lt: car -> car -> Prop;
         one: car;
         lt_iff: forall a0 a1,
           lt a0 a1 <-> OrderedCM.le (OrderedCM.add a0 one) a1;
      }.
End SOrderedCM.

Global Program Instance ord_SOrderedCM: @SOrderedCM.t Ord.t _ :=
  @SOrderedCM.mk _ _ Ord.lt (Ord.S Ord.O) _.
Next Obligation.
Proof.
  rewrite Hessenberg.add_S_r. rewrite Hessenberg.add_O_r.
  split; i.
  { eapply Ord.S_supremum; auto. }
  { eapply Ord.lt_le_lt; eauto. eapply Ord.S_lt. }
Qed.

Global Program Instance nat_SOrderedCM: @SOrderedCM.t nat _ :=
  @SOrderedCM.mk _ _ Nat.lt 1 _.
Next Obligation.
Proof.
  lia.
Qed.

Global Program Instance bool_OrderedCM
  : OrderedCM.t bool :=
  @OrderedCM.mk
    _ implb
    false
    orb
    _ _ _ _ _ _ _.
Next Obligation.
Proof.
  econs.
  { ii. destruct x; auto. }
  { ii. destruct x, y; ss. }
Qed.
Next Obligation.
Proof.
  destruct a0, a1; ss; auto.
Qed.
Next Obligation.
Proof.
  destruct a0, a1, a2; ss.
Qed.
Next Obligation.
Proof.
  destruct a0, a1; ss.
Qed.
Next Obligation.
Proof.
  destruct a; ss.
Qed.
Next Obligation.
Proof.
  destruct a0, a1; ss.
Qed.
Next Obligation.
Proof.
  destruct a0, a1, a2; ss.
Qed.
