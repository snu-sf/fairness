From sflib Require Import sflib.
From Fairness Require Import PCM IProp IPM MonotonePCM WFLib Mod.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.PropExtensionality.
From Fairness Require Import Axioms.
Require Import Program.

Set Implicit Arguments.

Module OrderedCM.
  Class t (car: Type) :=
    mk { le: car -> car -> Prop;
         unit: car;
         add: car -> car -> car;

         le_PreOrder:> PreOrder le;
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
      { etrans; eauto. }
      { etrans; eauto. }
    Qed.

    Lemma add_assoc_eq a0 a1 a2
      :
      eq (add a0 (add a1 a2)) (add (add a0 a1) a2).
    Proof.
      split.
      { eapply add_assoc_le. }
      { etrans.
        { eapply add_comm_le. }
        etrans.
        { eapply add_assoc_le. }
        etrans.
        { eapply add_comm_le. }
        etrans.
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
      etrans.
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
      etrans.
      { eapply add_comm_eq. }
      { eapply add_unit_eq_l. }
    Qed.

    Lemma add_base_r a0 a1
      :
      le a1 (add a0 a1).
    Proof.
      etrans.
      { eapply add_base_l. }
      { eapply add_comm_le. }
    Qed.

    Lemma le_add_r a0 a1 a2
          (LE: le a0 a1)
      :
      le (add a0 a2) (add a1 a2).
    Proof.
      i. etrans.
      { eapply add_comm_le. }
      etrans.
      { eapply le_add_l; eauto. }
      { eapply add_comm_le. }
    Qed.

    Lemma le_unit a
      :
      le unit a.
    Proof.
      etrans.
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
      { etrans.
        { eapply join_l. }
        { eapply join_l. }
      }
      { eapply join_supremum.
        { etrans.
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
      { etrans; eauto. eapply join_r. }
    Qed.

    Lemma join_assoc_eq a0 a1 a2
      :
      eq (join a0 (join a1 a2)) (join (join a0 a1) a2).
    Proof.
      split.
      { eapply join_assoc_le. }
      { etrans.
        { eapply join_comm_le. }
        etrans.
        { eapply join_assoc_le. }
        etrans.
        { eapply join_comm_le. }
        etrans.
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
      etrans.
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
      etrans.
      { eapply join_comm_eq. }
      { eapply join_unit_eq_l. }
    Qed.

    Lemma join_base_r a0 a1
      :
      le a1 (join a0 a1).
    Proof.
      etrans.
      { eapply join_l. }
      { eapply join_comm_le. }
    Qed.

    Lemma le_join_r a0 a1 a2
          (LE: le a0 a1)
      :
      le (join a0 a2) (join a1 a2).
    Proof.
      i. etrans.
      { eapply join_comm_le. }
      etrans.
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
        { etrans.
          { eapply meet_r. }
          { eapply meet_l. }
        }
      }
      { etrans.
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
      { etrans; eauto. eapply meet_r. }
    Qed.

    Lemma meet_assoc_eq a0 a1 a2
      :
      eq (meet a0 (meet a1 a2)) (meet (meet a0 a1) a2).
    Proof.
      split.
      { eapply meet_assoc_le. }
      { etrans.
        { eapply meet_comm_le. }
        etrans.
        { eapply meet_assoc_le. }
        etrans.
        { eapply meet_comm_le. }
        etrans.
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
      i. etrans.
      { eapply meet_comm_le. }
      etrans.
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


Global Program Instance nat_OrderedCM: OrderedCM.t nat :=
  @OrderedCM.mk _ Nat.le 0 Nat.add _ _ _ _ _ _ _ .
Next Obligation. Proof. lia. Qed.
Next Obligation. Proof. lia. Qed.
Next Obligation. Proof. lia. Qed.
Next Obligation. Proof. lia. Qed.
Next Obligation. Proof. lia. Qed.
Next Obligation. Proof. lia. Qed.

From Ordinal Require Import Ordinal Hessenberg ClassicalOrdinal.
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

Module Fuel.
  Section MONOID.
    Variable (A: Type).

    Record quotient `{OrderedCM.t A} :=
      mk {
          collection:> A -> Prop;
          generated: exists a0, forall a1,
            collection a1 <-> OrderedCM.le a0 a1;
        }.

    Global Program Definition from_monoid `{OrderedCM.t A} (a: A): quotient :=
      mk _ (OrderedCM.le a) _.
    Next Obligation.
    Proof.
      exists a. i. auto.
    Qed.

    Definition le `{OrderedCM.t A} (s0 s1: quotient): Prop :=
      forall a, s1 a -> s0 a.

    Global Program Instance le_PreOrder `{OrderedCM.t A}: PreOrder le.
    Next Obligation.
    Proof.
      ii. auto.
    Qed.
    Next Obligation.
    Proof.
      ii. eauto.
    Qed.

    Lemma le_anstisymmetric`{OrderedCM.t A} s0 s1
          (LE0: le s0 s1)
          (LE1: le s1 s0)
      :
      s0 = s1.
    Proof.
      destruct s0, s1.
      assert (collection0 = collection1).
      { extensionality a. eapply propositional_extensionality.
        red in LE0. red in LE1. ss. split; auto.
      }
      subst. f_equal. eapply proof_irrelevance.
    Qed.

    Lemma ext `{OrderedCM.t A} (s0 s1: quotient)
          (EXT: forall a, s0 a <-> s1 a)
      :
      s0 = s1.
    Proof.
      eapply le_anstisymmetric.
      { ii. eapply EXT; auto. }
      { ii. eapply EXT; auto. }
    Qed.

    Lemma from_monoid_exist `{OrderedCM.t A} (s: quotient)
      :
      exists a, s = from_monoid a.
    Proof.
      hexploit generated. i. des. exists a0.
      eapply ext. i. rewrite H0. ss.
    Qed.

    Lemma from_monoid_le `{OrderedCM.t A} a0 a1
      :
      from_monoid a0 a1 <-> OrderedCM.le a0 a1.
    Proof.
      ss.
    Qed.

    Lemma le_iff `{OrderedCM.t A} a0 a1
      :
      le (from_monoid a0) (from_monoid a1) <-> OrderedCM.le a0 a1.
    Proof.
      split.
      { i. exploit H0.
        { s. reflexivity. }
        i. rewrite <- from_monoid_le. ss.
      }
      { ii. ss. etrans; eauto. }
    Qed.

    Lemma from_monoid_eq `{OrderedCM.t A} a0 a1
      :
      from_monoid a0 = from_monoid a1 <-> OrderedCM.eq a0 a1.
    Proof.
      split.
      { i. split.
        { rewrite <- from_monoid_le. rewrite H0. ss. reflexivity. }
        { rewrite <- from_monoid_le. rewrite <- H0. ss. reflexivity. }
      }
      { i. red in H0. des. eapply ext. i. etrans.
        { eapply from_monoid_le. }
        etrans.
        2:{ symmetry. eapply from_monoid_le. }
        split. i.
        { etransitivity; eauto. }
        { etransitivity; eauto. }
      }
    Qed.

    Global Program Definition quotient_add `{OrderedCM.t A}
           (s0 s1: quotient): quotient :=
      mk _ (fun a => exists a0 a1 (IN0: s0 a0) (IN1: s1 a1),
                OrderedCM.le (OrderedCM.add a0 a1) a) _.
    Next Obligation.
      hexploit (from_monoid_exist s0).
      hexploit (from_monoid_exist s1). i. des. subst.
      exists (OrderedCM.add a a0). i. split.
      { i. des. etrans.
        { eapply OrderedCM.le_add_r. erewrite <- from_monoid_le. eauto. }
        etrans.
        { eapply OrderedCM.le_add_l. erewrite <- from_monoid_le. eauto. }
        { eauto. }
      }
      i. esplits.
      { erewrite from_monoid_le. reflexivity. }
      { erewrite from_monoid_le. reflexivity. }
      { eauto. }
    Qed.

    Global Program Definition quotient_join `{OrderedCM.t A}
           (s0 s1: quotient): quotient :=
      mk _ (fun a => s0 a /\ s1 a) _.
    Next Obligation.
      hexploit (from_monoid_exist s0).
      hexploit (from_monoid_exist s1). i. des. subst.
      destruct (OrderedCM.le_total a0 a).
      { exists a. i. split.
        { i. des. erewrite <- from_monoid_le. eauto. }
        { i. split; auto. erewrite from_monoid_le. etrans; eauto. }
      }
      { exists a0. i. split.
        { i. des. erewrite <- from_monoid_le. eauto. }
        { i. split; auto. erewrite from_monoid_le. etrans; eauto. }
      }
    Qed.

    Global Program Definition quotient_meet `{OrderedCM.t A}
           (s0 s1: quotient): quotient :=
      mk _ (fun a => s0 a \/ s1 a) _.
    Next Obligation.
      hexploit (from_monoid_exist s0).
      hexploit (from_monoid_exist s1). i. des. subst.
      destruct (OrderedCM.le_total a0 a).
      { exists a0. i. split.
        { i. erewrite ! from_monoid_le in H1. des; auto. etrans; eauto. }
        { i. right. erewrite from_monoid_le. auto. }
      }
      { exists a. i. split.
        { i. erewrite ! from_monoid_le in H1. des; auto. etrans; eauto. }
        { i. left. erewrite from_monoid_le. auto. }
      }
    Qed.

    Lemma from_monoid_add `{OrderedCM.t A} a0 a1
      :
      quotient_add (from_monoid a0) (from_monoid a1)
      =
        from_monoid (OrderedCM.add a0 a1).
    Proof.
      eapply ext. i. split.
      { i. ss. des. etrans.
        { eapply OrderedCM.le_add_r. eauto. }
        etrans.
        { eapply OrderedCM.le_add_l. eauto. }
        { eauto. }
      }
      { i. ss. esplits.
        { reflexivity. }
        { reflexivity. }
        { eauto. }
      }
    Qed.

    Lemma from_monoid_join_r `{OrderedCM.t A} a0 a1
          (LE: OrderedCM.le a0 a1)
      :
      quotient_join (from_monoid a0) (from_monoid a1)
      =
        from_monoid a1.
    Proof.
      eapply ext. i. split.
      { i. ss. des. auto. }
      { i. ss. esplits.
        { etrans; eauto. }
        { auto. }
      }
    Qed.

    Lemma from_monoid_join_l `{OrderedCM.t A} a0 a1
          (LE: OrderedCM.le a1 a0)
      :
      quotient_join (from_monoid a0) (from_monoid a1)
      =
        from_monoid a0.
    Proof.
      eapply ext. i. split.
      { i. ss. des. auto. }
      { i. ss. esplits.
        { auto. }
        { etrans; eauto. }
      }
    Qed.

    Lemma from_monoid_meet_l `{OrderedCM.t A} a0 a1
          (LE: OrderedCM.le a0 a1)
      :
      quotient_meet (from_monoid a0) (from_monoid a1)
      =
        from_monoid a0.
    Proof.
      eapply ext. i. split.
      { i. ss. des; auto. etrans; eauto. }
      { i. ss. left. auto. }
    Qed.

    Lemma from_monoid_meet_r `{OrderedCM.t A} a0 a1
          (LE: OrderedCM.le a1 a0)
      :
      quotient_meet (from_monoid a0) (from_monoid a1)
      =
        from_monoid a1.
    Proof.
      eapply ext. i. split.
      { i. ss. des; auto. etrans; eauto. }
      { i. ss. right. auto. }
    Qed.

    Lemma from_monoid_join `{OrderedCM.t A} a0 a1
      :
      quotient_join (from_monoid a0) (from_monoid a1)
      =
        from_monoid (OrderedCM.join a0 a1).
    Proof.
      destruct (OrderedCM.le_total a0 a1).
      { rewrite from_monoid_join_r; eauto.
        apply from_monoid_eq.
        { split.
          { eapply OrderedCM.join_r. }
          { eapply OrderedCM.join_supremum; auto. reflexivity. }
        }
      }
      { rewrite from_monoid_join_l; eauto.
        apply from_monoid_eq.
        { split.
          { eapply OrderedCM.join_l. }
          { eapply OrderedCM.join_supremum; auto. reflexivity. }
        }
      }
    Qed.

    Lemma from_monoid_meet `{OrderedCM.t A} a0 a1
      :
      quotient_meet (from_monoid a0) (from_monoid a1)
      =
        from_monoid (OrderedCM.meet a0 a1).
    Proof.
      destruct (OrderedCM.le_total a0 a1).
      { rewrite from_monoid_meet_l; eauto.
        apply from_monoid_eq.
        { split.
          { eapply OrderedCM.meet_infimum; auto. reflexivity. }
          { eapply OrderedCM.meet_l. }
        }
      }
      { rewrite from_monoid_meet_r; eauto.
        apply from_monoid_eq.
        { split.
          { eapply OrderedCM.meet_infimum; auto. reflexivity. }
          { eapply OrderedCM.meet_r. }
        }
      }
    Qed.

    Lemma quotient_add_comm `{OrderedCM.t A} s0 s1
      :
      quotient_add s0 s1
      =
        quotient_add s1 s0.
    Proof.
      hexploit (from_monoid_exist s0).
      hexploit (from_monoid_exist s1). i. des. subst.
      rewrite ! from_monoid_add.
      eapply from_monoid_eq. eapply OrderedCM.add_comm_eq.
    Qed.

    Lemma quotient_join_comm `{OrderedCM.t A} s0 s1
      :
      quotient_join s0 s1
      =
        quotient_join s1 s0.
    Proof.
      hexploit (from_monoid_exist s0).
      hexploit (from_monoid_exist s1). i. des. subst.
      rewrite ! from_monoid_join.
      eapply from_monoid_eq. eapply OrderedCM.join_comm_eq.
    Qed.

    Lemma quotient_meet_comm `{OrderedCM.t A} s0 s1
      :
      quotient_meet s0 s1
      =
        quotient_meet s1 s0.
    Proof.
      hexploit (from_monoid_exist s0).
      hexploit (from_monoid_exist s1). i. des. subst.
      rewrite ! from_monoid_meet.
      eapply from_monoid_eq. eapply OrderedCM.meet_comm_eq.
    Qed.

    Lemma quotient_add_assoc `{OrderedCM.t A} s0 s1 s2
      :
      quotient_add s0 (quotient_add s1 s2)
      =
        quotient_add (quotient_add s0 s1) s2.
    Proof.
      hexploit (from_monoid_exist s0).
      hexploit (from_monoid_exist s1).
      hexploit (from_monoid_exist s2). i. des. subst.
      rewrite ! from_monoid_add.
      eapply from_monoid_eq. eapply OrderedCM.add_assoc_eq.
    Qed.

    Lemma quotient_join_assoc `{OrderedCM.t A} s0 s1 s2
      :
      quotient_join s0 (quotient_join s1 s2)
      =
        quotient_join (quotient_join s0 s1) s2.
    Proof.
      hexploit (from_monoid_exist s0).
      hexploit (from_monoid_exist s1).
      hexploit (from_monoid_exist s2). i. des. subst.
      rewrite ! from_monoid_join.
      eapply from_monoid_eq. eapply OrderedCM.join_assoc_eq.
    Qed.

    Lemma quotient_meet_assoc `{OrderedCM.t A} s0 s1 s2
      :
      quotient_meet s0 (quotient_meet s1 s2)
      =
        quotient_meet (quotient_meet s0 s1) s2.
    Proof.
      hexploit (from_monoid_exist s0).
      hexploit (from_monoid_exist s1).
      hexploit (from_monoid_exist s2). i. des. subst.
      rewrite ! from_monoid_meet.
      eapply from_monoid_eq. eapply OrderedCM.meet_assoc_eq.
    Qed.

    Variant car `{OrderedCM.t A}: Type :=
      | frag (s: quotient)
      | excl (e: quotient) (s: quotient) (q: Qp)
      | boom
    .

    Definition black `{OrderedCM.t A} (a: A) (q: Qp): car :=
      excl (from_monoid a) (from_monoid (@OrderedCM.unit _ _)) q.

    Definition white `{OrderedCM.t A} (a: A): car :=
      frag (from_monoid a).

    Definition unit `{OrderedCM.t A}: car :=
      white (@OrderedCM.unit _ _).

    Let add `{OrderedCM.t A} :=
          fun (a0 a1: car) =>
            match a0, a1 with
            | frag f0, frag f1 => frag (quotient_add f0 f1)
            | frag f0, excl e1 f1 q1 => excl e1 (quotient_add f0 f1) q1
            | excl e0 f0 q0, frag f1 => excl e0 (quotient_add f0 f1) q0
            | excl e0 f0 q0, excl e1 f1 q1 => excl (quotient_meet e0 e1) (quotient_add f0 f1) (q0 + q1)%Qp
            | _, _ => boom
            end.

    Let wf `{OrderedCM.t A} :=
          fun (a: car) =>
            match a with
            | frag f => True
            | excl e f q => le f e /\ (Qp_le q 1)%Qp
            | boom => False
            end.

    Let core `{OrderedCM.t A} :=
          fun (a: car) => unit.

    Global Program Instance t `{OrderedCM.t A}: URA.t := {
        car := car;
        unit := unit;
        _add := add;
        _wf := wf;
        core := core;
      }
    .
    Next Obligation.
      destruct a, b; ss.
      { f_equal. eapply quotient_add_comm. }
      { f_equal. eapply quotient_add_comm. }
      { f_equal. eapply quotient_add_comm. }
      { f_equal.
        { eapply quotient_meet_comm. }
        { eapply quotient_add_comm. }
        { rewrite Qp_add_comm. auto. }
      }
    Qed.
    Next Obligation.
      destruct a, b, c; ss.
      { f_equal. eapply quotient_add_assoc. }
      { f_equal. eapply quotient_add_assoc. }
      { f_equal. eapply quotient_add_assoc. }
      { f_equal. eapply quotient_add_assoc. }
      { f_equal. eapply quotient_add_assoc. }
      { f_equal. eapply quotient_add_assoc. }
      { f_equal. eapply quotient_add_assoc. }
      { f_equal.
        { eapply quotient_meet_assoc. }
        { eapply quotient_add_assoc. }
        { rewrite Qp_add_assoc. auto. }
      }
    Qed.
    Next Obligation.
      unseal "ra". destruct a; ss.
      { f_equal.
        hexploit (from_monoid_exist s). i. des. subst.
        rewrite from_monoid_add.
        eapply from_monoid_eq. eapply OrderedCM.add_unit_eq_l.
      }
      { f_equal.
        hexploit (from_monoid_exist s). i. des. subst.
        rewrite from_monoid_add.
        eapply from_monoid_eq. eapply OrderedCM.add_unit_eq_l.
      }
    Qed.
    Next Obligation.
      unseal "ra". ss.
    Qed.
    Next Obligation.
      unseal "ra". destruct a, b; ss.
      { hexploit (from_monoid_exist s).
        hexploit (from_monoid_exist s0).
        hexploit (from_monoid_exist e). i. des. subst.
        rewrite from_monoid_add in H0.
        rewrite le_iff in H0. rewrite le_iff. split; auto.
        etrans; eauto. eapply OrderedCM.add_base_l.
      }
      { hexploit (from_monoid_exist s).
        hexploit (from_monoid_exist s0).
        hexploit (from_monoid_exist e).
        hexploit (from_monoid_exist e0). i. des. subst.
        rewrite ! from_monoid_add in H0.
        rewrite ! from_monoid_meet in H0.
        rewrite le_iff in H0. split.
        { apply le_iff. transitivity (OrderedCM.add a a0).
          { eapply OrderedCM.add_base_l. }
          etrans; eauto. eapply OrderedCM.meet_l.
        }
        { etrans; [|eauto]. eapply Qp_le_add_l. }
      }
    Qed.
    Next Obligation.
      unseal "ra". destruct a; ss.
      { f_equal.
        hexploit (from_monoid_exist s). i. des. subst.
        rewrite from_monoid_add.
        eapply from_monoid_eq.
        eapply OrderedCM.add_unit_eq_r.
      }
      { f_equal.
        hexploit (from_monoid_exist s). i. des. subst.
        rewrite from_monoid_add.
        eapply from_monoid_eq.
        eapply OrderedCM.add_unit_eq_r.
      }
    Qed.
    Next Obligation.
      unseal "ra". exists unit. unfold core, unit, white. ss.
      f_equal.
      rewrite from_monoid_add.
      eapply from_monoid_eq. symmetry.
      eapply OrderedCM.add_unit_eq_r.
    Qed.

    Lemma white_sum `{OrderedCM.t A} (a0 a1: A)
      :
      white a0 ⋅ white a1
      =
        white (OrderedCM.add a0 a1).
    Proof.
      ur. unfold white. f_equal.
      rewrite from_monoid_add. auto.
    Qed.

    Lemma black_sum `{OrderedCM.t A} (a0 a1: A) (q0 q1: Qp)
      :
      black a0 q0 ⋅ black a1 q1
      =
        black (OrderedCM.meet a0 a1) (q0 + q1).
    Proof.
      ur. unfold black. f_equal.
      { rewrite from_monoid_meet. auto. }
      { rewrite from_monoid_add.
        apply from_monoid_eq. apply OrderedCM.add_unit_eq_l.
      }
    Qed.

    Lemma white_eq `{OrderedCM.t A} (a0 a1: A)
          (EQ: OrderedCM.eq a0 a1)
      :
      white a0 = white a1.
    Proof.
      unfold white. f_equal.
      eapply from_monoid_eq; eauto.
    Qed.

    Lemma black_eq `{OrderedCM.t A} (a0 a1: A) (q: Qp)
          (EQ: OrderedCM.eq a0 a1)
      :
      black a0 q = black a1 q.
    Proof.
      unfold black. f_equal.
      eapply from_monoid_eq; eauto.
    Qed.

    Lemma white_mon `{OrderedCM.t A} (a0 a1: A)
          (LE: OrderedCM.le a0 a1)
      :
      URA.updatable (white a1) (white a0).
    Proof.
      ii. ur in H0. ur. unfold wf in *. des_ifs. des. split; auto.
      etrans; eauto.
      hexploit (from_monoid_exist s0). i. des. subst.
      rewrite ! from_monoid_add. eapply le_iff.
      eapply OrderedCM.le_add_r. auto.
    Qed.

    Lemma black_mon `{OrderedCM.t A} (a0 a1: A) (q: Qp)
          (LE: OrderedCM.le a0 a1)
      :
      URA.updatable (black a0 q) (black a1 q).
    Proof.
      ii. ur in H0. ur. unfold wf in *. des_ifs.
      { hexploit (from_monoid_exist s0). i. des. subst.
        rewrite from_monoid_add in *. split; auto. etrans; eauto.
        eapply le_iff. auto.
      }
      { hexploit (from_monoid_exist s0).
        hexploit (from_monoid_exist e0). i. des. subst.
        rewrite from_monoid_add in *. rewrite from_monoid_meet in *.
        split; auto. etrans; eauto.
        eapply le_iff. apply OrderedCM.le_meet_r. auto.
      }
    Qed.

    Lemma success_update `{OrderedCM.t A} a0 a1
      :
      URA.updatable
        (black a0 1)
        (black (OrderedCM.add a0 a1) 1 ⋅ white a1).
    Proof.
      ii. ur in H0. ur. unfold wf in *. des_ifs.
      { hexploit (from_monoid_exist s0). i. des. subst. split; auto.
        rewrite ! from_monoid_add in H0.
        rewrite ! from_monoid_add.
        erewrite le_iff in H0. erewrite le_iff.
        etrans.
        { eapply OrderedCM.le_add_l. etrans.
          { eapply OrderedCM.add_base_r. }
          { eapply H0. }
        }
        etrans.
        { eapply OrderedCM.add_comm_le. }
        { eapply OrderedCM.le_add_l.
          eapply OrderedCM.add_unit_le_r.
        }
      }
      { des. exfalso. eapply Qp_not_add_le_l. eauto. }
    Qed.

    Lemma decr_update `{OrderedCM.t A} a0 a1 q
      :
      URA.updatable_set
        (black a0 q ⋅ white a1)
        (fun r => exists a2, r = black a2 q /\ OrderedCM.le (OrderedCM.add a1 a2) a0).
    Proof.
      ii. ur in WF. unfold wf in WF. des_ifs.
      { hexploit (from_monoid_exist s0). i. des. subst.
        rewrite ! from_monoid_add in WF. rewrite le_iff in WF.
        eexists. esplits.
        { reflexivity. }
        { instantiate (1:=a). etrans; eauto.
          eapply OrderedCM.le_add_r. eapply OrderedCM.add_base_r.
        }
        ur. split; auto. rewrite ! from_monoid_add. rewrite le_iff.
        eapply OrderedCM.add_unit_le_r.
      }
      { hexploit (from_monoid_exist s0).
        hexploit (from_monoid_exist e0). i. des. subst.
        rewrite ! from_monoid_add in WF. rewrite ! from_monoid_meet in WF.
        rewrite le_iff in WF.
        eexists. esplits.
        { reflexivity. }
        { instantiate (1:=a).
          transitivity (OrderedCM.add (OrderedCM.add OrderedCM.unit a1) a).
          { eapply OrderedCM.le_add_r. apply OrderedCM.add_base_r. }
          etrans; eauto. eapply OrderedCM.meet_l.
        }
        ur. split; auto. rewrite ! from_monoid_add. rewrite ! from_monoid_meet.
        rewrite le_iff. etrans.
        { eapply OrderedCM.add_unit_le_r. }
        eapply OrderedCM.meet_infimum.
        { reflexivity. }
        { transitivity (OrderedCM.add (OrderedCM.add OrderedCM.unit a1) a).
          { eapply OrderedCM.add_base_r. }
          etrans; eauto. eapply OrderedCM.meet_r.
        }
      }
    Qed.
  End MONOID.
End Fuel.


From Paco Require Import paco.

Section INFSUM.
  Variable M: URA.t.

  Variant _infsum (infsum: forall (X: Type) (P: X -> M -> Prop) (r: M), Prop)
          (X: Type) (P: X -> M -> Prop) (r: M): Prop :=
    | infsum_intro
        (INF: forall Y (Q: Y -> M -> Prop) x
                     (f: Y -> X)
                     (PRED: forall y r, P (f y) r -> Q y r)
                     (INJ: forall y0 y1, f y0 = f y1 -> y0 = y1)
                     (MINUS: forall y, f y <> x),
          exists r0 r1,
            r = r0 ⋅ r1 /\ P x r0 /\ infsum Y Q r1)
  .

  Lemma infsum_monotone: monotone3 _infsum.
  Proof.
    ii. inv IN. econs; eauto.
    i. hexploit INF; eauto. i. des. esplits; eauto.
  Qed.
  Hint Resolve infsum_monotone: paco.
  Hint Resolve cpn3_wcompat: paco.

  Definition infsum := paco3 _infsum bot3.

  Lemma infsum_void
        (X: Type) (EMPTY: forall (x: X), False)
        (P: X -> M -> Prop)
        (r: M)
    :
    infsum P r.
  Proof.
    pfold. econs. i. exfalso. eapply EMPTY; eauto.
  Qed.

  Lemma singleton_to_infsum (r: M) (P: M -> Prop)
        (SAT: P r)
    :
    infsum (fun _: unit => P) r.
  Proof.
    pfold. econs. i.
    exists r, URA.unit. rewrite URA.unit_id. splits; auto.
    left. eapply infsum_void; eauto.
    i. eapply (MINUS x0). destruct (f x0), x; ss.
  Qed.

  Variant infsum_extendC (R: forall (X: Type) (P: X -> M -> Prop) (r: M), Prop)
          X (P: X -> M -> Prop) (r: M): Prop :=
    | infsum_extendC_intro
        r0 r1
        (SAT: R X P r0)
        (EQ: r = r0 ⋅ r1)
  .

  Lemma infsum_extendC_spec
    :
    infsum_extendC <4= gupaco3 _infsum (cpn3 _infsum).
  Proof.
    eapply wrespect3_uclo; eauto with paco. econs.
    { ii. inv IN. econs; eauto. }
    i. inv PR. eapply GF in SAT. inv SAT.
    econs. i. hexploit INF; eauto. i. des. subst.
    exists r2, (r3 ⋅ r1). splits; auto.
    { r_solve. }
    eapply rclo3_clo_base. econs; eauto.
  Qed.

  Variant infsum_monoC (R: forall (X: Type) (P: X -> M -> Prop) (r: M), Prop)
          Y (Q: Y -> M -> Prop) (r: M): Prop :=
    | infsum_monoC_intro
        X (f: Y -> X) (P: X -> M -> Prop)
        (PRED: forall y r, P (f y) r -> Q y r)
        (INJ: forall y0 y1, f y0 = f y1 -> y0 = y1)
        (SAT: R X P r)
  .

  Lemma infsum_monoC_spec
    :
    infsum_monoC <4= gupaco3 _infsum (cpn3 _infsum).
  Proof.
    eapply wrespect3_uclo; eauto with paco. econs.
    { ii. inv IN. econs; eauto. }
    i. inv PR. eapply GF in SAT. inv SAT.
    econs. i.
    hexploit (INF Y Q (f x) (fun x => f (f0 x))); auto.
    { ii. eapply INJ in H. eapply MINUS; eauto. }
    i. des. exists r0, r1. splits; auto.
    eapply rclo3_base. auto.
  Qed.

  Lemma infsum_unfold
        X Y (Q: Y -> M -> Prop) (f: Y -> X)
        (P: X -> M -> Prop) (r: M)
        (INF: infsum P r)
        (PRED: forall y r, P (f y) r -> Q y r)
        (INJ: forall y0 y1, f y0 = f y1 -> y0 = y1)
        x
        (MINUS: forall y, f y <> x)
    :
    exists r0 r1,
      r = r0 ⋅ r1 /\ P x r0 /\ infsum Q r1.
  Proof.
    punfold INF. inv INF. hexploit INF0; eauto.
    i. des. subst. pclearbot. esplits; eauto.
  Qed.

  Let partial_fun_to_total X Y (f: X -> option Y)
      (TOTAL: forall x, f x <> None)
    :
    X -> Y.
  Proof.
    intros x. destruct (f x) eqn:EQ.
    { exact y. }
    { destruct (TOTAL _ EQ). }
  Defined.

  Lemma partial_fun_to_total_eq
        X Y (f: X -> option Y)
        (TOTAL: forall x, f x <> None)
        x y
        (EQ: f x = Some y)
    :
    partial_fun_to_total f TOTAL x = y.
  Proof.
    compute.
    replace (fun (EQ0 : f x = None) => match TOTAL x EQ0 return Y with
                                       end) with
      (fun (EQ0 : f x = None) => y).
    2:{ extensionality a. clarify. }
    rewrite EQ. auto.
  Qed.

  Lemma infsum_fold_aux
    :
    forall
      (X: Type) (P0: X -> M -> Prop) (r0: M)
      (INF: infsum P0 r0)
      (P1: M -> Prop) (r1: M)
      (SAT: P1 r1),
      infsum (option_rect _ P0 P1) (r0 ⋅ r1).
  Proof.
    ginit. gcofix CIH. i. gstep. econs. i.
    destruct x.
    { assert (exists (f': sig (fun y => f y <> None) -> X),
               forall y, f (proj1_sig y) = Some (f' y)).
      { eapply (choice (fun (y: sig (fun y => f y <> None)) x => f (proj1_sig y) = Some x)).
        i. destruct x0. ss. destruct (f x0); ss. eauto.
      }
      des. hexploit (@infsum_unfold X _ (fun y => Q (proj1_sig y)) f').
      { eauto. }
      { i. eapply PRED. rewrite H. ss. }
      { i. assert (proj1_sig y0 = proj1_sig y1).
        { eapply INJ. rewrite ! H. f_equal. auto. }
        { destruct y0, y1. ss. subst. f_equal. apply proof_irrelevance. }
      }
      { instantiate (1:=x). ii. eapply MINUS. rewrite H. rewrite H0. auto. }
      i. des. subst. exists r2, (r3 ⋅ r1). splits.
      { r_solve. }
      { ss. }
      assert (exists (wrap: Y -> option (sig (fun y => f y <> None))),
               forall y,
                 match (wrap y) with
                 | None => f y = None
                 | Some (exist _ y' _) => y = y' /\ exists x, f y = Some x
                 end).
      { eapply (choice (fun y (y': option (sig (fun y => f y <> None))) =>
                          match y' with
                          | Some (exist _ y' _) => y = y' /\ exists x, f y = Some x
                          | None => f y = None
                          end)).
        i. destruct (f x0) eqn:EQ.
        { refine (ex_intro _ (Some (exist _ x0 _)) _).
          { ii. clarify. }
          { splits; eauto. }
        }
        { exists None. auto. }
      }
      des. guclo infsum_monoC_spec. econs.
      3:{ gbase. eapply CIH; eauto. }
      { instantiate (1:=wrap). i. specialize (H0 y). des_ifs; ss.
        { des. subst. auto. }
        { eapply PRED. rewrite H0. ss. }
      }
      { i. eapply INJ. pose proof (H0 y0). pose proof (H0 y1). des_ifs.
        { des. subst. auto. }
        { rewrite H4. rewrite H5. auto. }
      }
    }
    { exists r1, r0. splits.
      { eapply URA.add_comm. }
      { ss. }
      { guclo infsum_monoC_spec.
        econs.
        3:{ gfinal. right. eapply paco3_mon; eauto. ss. }
        { instantiate (1:=partial_fun_to_total f MINUS).
          intros y. destruct (f y) eqn:EQ.
          2:{ destruct (MINUS _ EQ). }
          i. hexploit partial_fun_to_total_eq; eauto. i.
          erewrite H0 in H. eapply PRED. rewrite EQ. ss.
        }
        { i. destruct (f y0) eqn:EQ0.
          2:{ destruct (MINUS _ EQ0). }
          destruct (f y1) eqn:EQ1.
          2:{ destruct (MINUS _ EQ1). }
          eapply INJ; eauto.
          erewrite partial_fun_to_total_eq in H; eauto.
          erewrite partial_fun_to_total_eq in H; eauto.
          rewrite EQ0. rewrite EQ1. subst. auto.
        }
      }
    }
  Qed.

  Lemma infsum_fold
        (X: Type) (P0: X -> M -> Prop) (r0: M)
        (INF: infsum P0 r0)
        (P1: M -> Prop) (r1: M)
        (SAT: P1 r1)
        Y (Q: Y -> M -> Prop)
        (f: Y -> option X)
        (PRED0: forall y x r (EQ: f y = Some x), P0 x r -> Q y r)
        (PRED1: forall y r (EQ: f y = None), P1 r -> Q y r)
        (INJ: forall y0 y1, f y0 = f y1 -> y0 = y1)
    :
    infsum Q (r0 ⋅ r1).
  Proof.
    ginit. guclo infsum_monoC_spec. econs.
    3:{ gfinal. right. eapply infsum_fold_aux; eauto. }
    { instantiate (1:=f). i. destruct (f y) eqn:EQ; ss; eauto. }
    { auto. }
  Qed.

  Lemma infsum_to_singleton
        (X: Type) (P: X -> M -> Prop)
        (r: M)
        (INF: infsum P r)
        x
    :
    exists r0 r1, r = r0 ⋅ r1 /\ P x r0.
  Proof.
    punfold INF. inv INF.
    hexploit (INF0 (sig (fun y => y <> x)) (fun y => P (proj1_sig y)) x proj1_sig).
    { i. auto. }
    { i. destruct y0, y1. ss. subst. f_equal. eapply proof_irrelevance. }
    { i. eapply (proj2_sig y). }
    i. des. esplits; eauto.
  Qed.
End INFSUM.
#[export] Hint Resolve infsum_monotone: paco.
#[export] Hint Resolve cpn3_wcompat: paco.

Program Definition Infsum {Σ: GRA.t} (X: Type) (P: X -> iProp): iProp :=
  iProp_intro (infsum Σ P) _.
Next Obligation.
Proof.
  rr in LE. des. subst.
  ginit. guclo infsum_extendC_spec. econs; eauto. gfinal. right. auto.
Qed.

Lemma pointwise_own_infsum A (M: URA.t)
      {Σ: GRA.t} `{ING: @GRA.inG (A ==> M)%ra Σ}
      (f: (A ==> M)%ra)
  :
  (OwnM f)
    -∗
    Infsum (fun a => OwnM (maps_to_res a (f a))).
Proof.
  uipropall. i. rr in H. uipropall. rr in H. des. subst.
  ginit. guclo infsum_extendC_spec. econs; eauto.
  clear WF ctx. revert f. gcofix CIH. i. gstep. econs. i.
  exists (GRA.embed (maps_to_res x (f x))), (GRA.embed (map_update f x URA.unit: (A ==> M)%ra)).
  splits.
  { rewrite GRA.embed_add. f_equal.
    extensionality a. ur.
    unfold maps_to_res, map_update. des_ifs.
    { r_solve. }
    { r_solve. }
  }
  { rr. uipropall. reflexivity. }
  guclo infsum_monoC_spec. econs.
  3:{ gbase. eapply CIH. }
  { instantiate (1:=f0). i. ss.
    unfold map_update in H. des_ifs.
    { exfalso. eapply MINUS; eauto. }
    { eapply PRED; eauto. }
  }
  { auto. }
Qed.

Arguments Fuel.t A {_}.
From Fairness Require Import FairBeh.

Module FairRA.
  Section FAIR.
    Variable (Id: Type).
    Variable (A: Type).
    Context `{L: OrderedCM.t A}.

    Definition t: URA.t :=
      (Id ==> @Fuel.t A _)%ra.

    Context `{ING: @GRA.inG t Σ}.

    Definition black (i: Id) (a: A) (q: Qp): iProp :=
      maps_to i (Fuel.black a q: Fuel.t A).

    Definition black_ex (i: Id) (q: Qp): iProp :=
      ∃ a, black i a q.

    Definition white (i: Id) (a: A): iProp :=
      maps_to i (Fuel.white a: Fuel.t A).

    Lemma white_sum i a0 a1
      :
      (white i a0)
        -∗
        (white i a1)
        -∗
        (white i (OrderedCM.add a0 a1)).
    Proof.
      unfold white, maps_to. iIntros "H0 H1".
      iCombine "H0 H1" as "H".
      rewrite maps_to_res_add. rewrite (@Fuel.white_sum A L). auto.
    Qed.

    Lemma white_split i a0 a1
      :
      (white i (OrderedCM.add a0 a1))
        -∗
        (white i a0 ** white i a1).
    Proof.
      unfold white, maps_to. iIntros "H".
      rewrite <- (@Fuel.white_sum A L).
      rewrite <- maps_to_res_add.
      iDestruct "H" as "[H0 H1]". iFrame.
    Qed.

    Lemma white_eq a1 i a0
          (EQ: OrderedCM.eq a0 a1)
      :
      white i a0 = white i a1.
    Proof.
      unfold white. erewrite Fuel.white_eq; eauto.
    Qed.

    Lemma black_eq a1 i a0 q
          (EQ: OrderedCM.eq a0 a1)
      :
      black i a0 q = black i a1 q.
    Proof.
      unfold black. erewrite Fuel.black_eq; eauto.
    Qed.

    Lemma white_mon a0 i a1
          (LE: OrderedCM.le a0 a1)
      :
      (white i a1)
        -∗
        (#=> white i a0).
    Proof.
      eapply OwnM_Upd. eapply maps_to_updatable.
      eapply Fuel.white_mon. auto.
    Qed.

    Lemma black_mon a1 i a0 q
          (LE: OrderedCM.le a0 a1)
      :
      (black i a0 q)
        -∗
        (#=> black i a1 q).
    Proof.
      eapply OwnM_Upd. eapply maps_to_updatable.
      eapply Fuel.black_mon. auto.
    Qed.

    Lemma success_update a1 i a0
      :
      (black i a0 1%Qp)
        -∗
        (#=> ((∃ a, black i a 1%Qp) ** (white i a1))).
    Proof.
      iIntros "H".
      iPoseProof (OwnM_Upd with "H") as "> H".
      { eapply maps_to_updatable.
        eapply Fuel.success_update. }
      rewrite <- maps_to_res_add. iDestruct "H" as "[H0 H1]".
      iModIntro. iFrame. iExists _. iFrame.
    Qed.

    Lemma success_ex_update a1 i
      :
      (black_ex i 1%Qp)
        -∗
        (#=> (black_ex i 1%Qp ** (white i a1))).
    Proof.
      iIntros "[% H]". iPoseProof (success_update with "H") as "> [[% H0] H1]".
      iModIntro. iFrame. iExists _. iFrame.
    Qed.

    Lemma decr_update i a0 a1 q
      :
      (black i a0 q)
        -∗
        (white i a1)
        -∗
        (#=> (∃ a2, black i a2 q ** ⌜OrderedCM.le (OrderedCM.add a1 a2) a0⌝)).
    Proof.
      iIntros "H0 H1". iCombine "H0 H1" as "H".
      rewrite maps_to_res_add.
      iPoseProof (OwnM_Upd_set with "H") as "> H".
      { eapply maps_to_updatable_set. eapply Fuel.decr_update. }
      iModIntro. ss. iDestruct "H" as "[% [% H]]".
      des. subst. iExists _. iFrame. auto.
    Qed.

    Lemma black_ex_sum i q0 q1
      :
      (black_ex i q0)
        -∗
        (black_ex i q1)
        -∗
        (black_ex i (q0 + q1)%Qp).
    Proof.
      unfold white, maps_to. iIntros "[% H0] [% H1]".
      iCombine "H0 H1" as "H".
      rewrite maps_to_res_add. rewrite (@Fuel.black_sum A L).
      iExists _. eauto.
    Qed.

    Lemma black_split i a q0 q1
      :
      (black i a (q0 + q1)%Qp)
        -∗
        (black i a q0 ** black i a q1).
    Proof.
      unfold black, maps_to. iIntros "H".
      erewrite Fuel.black_eq.
      { instantiate (1:=OrderedCM.meet a a).
        rewrite <- (@Fuel.black_sum A L).
        rewrite <- maps_to_res_add.
        iDestruct "H" as "[H0 H1]". iFrame.
      }
      { split.
        { apply OrderedCM.meet_infimum; reflexivity. }
        { apply OrderedCM.meet_l. }
      }
    Qed.

    Lemma black_ex_split i q0 q1
      :
      (black_ex i (q0 + q1)%Qp)
        -∗
        (black_ex i q0 ** black_ex i q1).
    Proof.
      iIntros "[% H]". iPoseProof (black_split with "H") as "[H0 H1]".
      iSplitL "H0".
      { iExists _. iFrame. }
      { iExists _. iFrame. }
    Qed.

    Definition blacks (s: Id -> Prop): iProp :=
      ∃ (f: Id -> option A),
        (⌜forall i, is_Some (f i) <-> s i⌝)
          **
          (OwnM ((fun i =>
                    match (f i) with
                    | Some a => Fuel.black a 1
                    | None => ε
                    end): (Id ==> Fuel.t A)%ra)).

    Definition whites (s: Id -> Prop) (u: A): iProp :=
      (OwnM ((fun i =>
                if (excluded_middle_informative (s i))
                then Fuel.white u
                else ε): (Id ==> Fuel.t A)%ra)).

    Lemma whites_white (s: Id -> Prop) u i
          (IN: s i)
      :
      (whites s u)
        -∗
        (white i u).
    Proof.
      iIntros "H". iApply (OwnM_extends with "H").
      unfold maps_to_res. eapply pointwise_extends.
      i. des_ifs; ss.
      { reflexivity. }
      { exists (Fuel.white u). rewrite URA.unit_idl. auto. }
      { reflexivity. }
    Qed.

    (* Target *)
    Definition whites_all (f: Id -> A): iProp :=
      OwnM ((fun i => Fuel.white (f i)): (Id ==> Fuel.t A)%ra).

    (* Source *)
    Definition blacks_all (f: Id -> A): iProp :=
      OwnM ((fun i => Fuel.black (f i) 1%Qp): (Id ==> Fuel.t A)%ra).

    Definition whites_update
               (f0 f1: Id -> A)
               (u: A)
               (fm: fmap Id)
               (UPDATE: forall i,
                   match fm i with
                   | Flag.emp => f1 i = f0 i
                   | Flag.fail => OrderedCM.le (OrderedCM.add u (f1 i)) (f0 i)
                   | Flag.success => True
                   end)
      :
      (whites_all f0)
        -∗
        (blacks (fun i => fm i = Flag.success))
        -∗
        (#=>
           ((whites_all f1)
              **
              (blacks (fun i => fm i = Flag.success))
              **
              (whites (fun i => fm i = Flag.fail) u)
              **
              (whites (fun i => fm i = Flag.success) u))).
    Proof.
      iIntros "WHITE [% [% BLACK]]".
      iCombine "WHITE BLACK" as "OWN".
      iPoseProof (OwnM_Upd_set with "OWN") as "> [% [% OWN]]".
      { eapply updatable_set_impl; cycle 1.
        { eapply pointwise_updatable_set. i.
          instantiate (1:=fun (i: Id) (a: Fuel.t A) =>
                            match (fm i) with
                            | Flag.emp => a = Fuel.white (f1 i)
                            | Flag.success =>
                                exists o, a = ((Fuel.white (f1 i): Fuel.t A) ⋅ (Fuel.black o 1: Fuel.t A) ⋅ (Fuel.white u: Fuel.t A))
                            | Flag.fail =>
                                a = ((Fuel.white (f1 i): Fuel.t A) ⋅ (Fuel.white u: Fuel.t A))
                            end).
          ss.
          match goal with
          | |- URA.updatable_set ?y _ => replace y with
              (match (f a) with
               | Some a0 => (Fuel.black a0 1: Fuel.t A) ⋅ (Fuel.white (f0 a): Fuel.t A)
               | None => Fuel.white (f0 a)
               end)
          end; cycle 1.
          { ur. des_ifs.
            { rewrite URA.add_comm. ur. auto. }
            { rewrite URA.unit_id. auto. }
          }
          specialize (UPDATE a). des_ifs; cycle 5.
          { specialize (H a). rewrite Heq0 in H. rewrite Heq in H. inv H. hexploit H1; ss. i. inv H. ss. }
          { exfalso. specialize (H a). rewrite Heq0 in H. rewrite Heq in H.
            inv H. hexploit H0; ss.
          }
          { exfalso. specialize (H a). rewrite Heq0 in H. rewrite Heq in H.
            inv H. hexploit H0; ss.
          }
          { ii. rewrite <- URA.add_assoc in WF.
            exploit Fuel.success_update; eauto. i. esplits; eauto.
            eapply URA.wf_mon. instantiate (1:=Fuel.white (f0 a)).
            r_wf x0. instantiate (1:=OrderedCM.add (f1 a) u). instantiate (1:=(OrderedCM.add a0 (OrderedCM.add (f1 a) u))).
            rewrite <- (Fuel.white_sum (f1 a) u).
            rewrite ! URA.add_assoc.
            erewrite <- (URA.add_assoc _ ctx (Fuel.white (f0 a))).
            erewrite <- (URA.add_assoc _ (Fuel.white (f0 a): @URA.car (Fuel.t A)) ctx).
            f_equal.
            2:{ r_solve. }
            f_equal. rewrite URA.add_comm. auto.
          }
          { ii. exploit Fuel.white_mon; eauto. i. esplits; eauto.
            r_wf x0.
            rewrite <- (Fuel.white_sum u (f1 a)).
            rewrite ! URA.add_assoc. f_equal. rewrite URA.add_comm. auto.
          }
          { ii. rewrite UPDATE. esplits; eauto. }
        }
        { instantiate (1:=fun r =>
                            exists (f: Id -> option A),
                              (forall i,
                                  (fun i fi =>
                                     (is_Some fi <-> fm i = Flag.success) /\
                                       (r i =
                                          (Fuel.white (f1 i): Fuel.t A)
                                            ⋅
                                            (match fi with
                                             | Some a => Fuel.black a 1
                                             | None => ε
                                             end)
                                            ⋅
                                            (if (excluded_middle_informative (fm i = Flag.fail))
                                             then Fuel.white u
                                             else ε)
                                            ⋅
                                            (if (excluded_middle_informative (fm i = Flag.success))
                                             then Fuel.white u
                                             else ε))) i (f i))).
          intros fn WF SAT. eapply choice. i. ss.
          specialize (SAT x). destruct (fm x) eqn:FM.
          { exists None. splits.
            { split; ss. i. inv H0. ss. }
            rewrite SAT. des_ifs.
            repeat rewrite URA.unit_id. ur. auto.
          }
          { exists None. splits.
            { split; ss. i. inv H0. ss. }
            rewrite SAT. des_ifs.
            repeat rewrite URA.unit_id. auto.
          }
          { des. exists (Some o). splits.
            { split; ss. }
            rewrite SAT. des_ifs.
            repeat rewrite URA.unit_id. auto.
          }
        }
      }
      ss. des.
      assert (b =
                (((fun i => Fuel.white (f1 i)): (Id ==> Fuel.t A)%ra)
                   ⋅
                   ((fun i =>
                       match f2 i with
                       | Some a => Fuel.black a 1
                       | None => ε
                       end): (Id ==> Fuel.t A)%ra)
                   ⋅
                   ((fun i =>
                       if (excluded_middle_informative (fm i = Flag.fail))
                       then Fuel.white u
                       else ε): (Id ==> Fuel.t A)%ra)
                   ⋅
                   ((fun i =>
                       if (excluded_middle_informative (fm i = Flag.success))
                       then Fuel.white u
                       else ε): (Id ==> Fuel.t A)%ra))).
      { extensionality i. specialize (H0 i). des.
        rewrite H1. erewrite ! (@unfold_pointwise_add Id (Fuel.t A)). auto.
      }
      subst. iPoseProof "OWN" as "[[[OWN0 OWN1] OWN2] OWN3]".
      iModIntro. iFrame. iExists _. iSplit.
      2:{ iFrame. }
      iPureIntro. i. specialize (H0 i). des. auto.
    Qed.

    Definition blacks_update
               (f0: Id -> A)
               (u n: A)
               (fm: fmap Id)
      :
      (blacks_all f0)
        -∗
        (whites (fun i => fm i = Flag.fail) u)
        -∗
        (#=>
           (∃ f1,
               (⌜forall i,
                     match fm i with
                     | Flag.emp => f1 i = f0 i
                     | Flag.fail => OrderedCM.le (OrderedCM.add u (f1 i)) (f0 i)
                     | Flag.success => True
                     end⌝)
                 **
                 (blacks_all f1)
                 **
                 (whites (fun i => fm i = Flag.success) n))).
    Proof.
      iIntros "BLACK WHITE".
      iCombine "BLACK WHITE" as "OWN".
      iPoseProof (OwnM_Upd_set with "OWN") as "> [% [% OWN]]".
      { eapply updatable_set_impl; cycle 1.
        { eapply pointwise_updatable_set. i.
          instantiate (1:=fun (i: Id) (a: Fuel.t A) =>
                            exists o,
                              (a = (Fuel.black o 1: Fuel.t A) ⋅ (if (excluded_middle_informative (fm i = Flag.success))
                                                                 then Fuel.white n
                                                                 else ε)) /\
                                (match fm i with
                                 | Flag.emp => o = f0 i
                                 | Flag.fail => OrderedCM.le (OrderedCM.add u o) (f0 i)
                                 | Flag.success => True
                                 end)).
          erewrite ! (@unfold_pointwise_add Id (Fuel.t A)).
          destruct (fm a) eqn:FM.
          { des_ifs. ii.
            exploit Fuel.decr_update; eauto. i. des. subst.
            esplits; eauto. rewrite URA.unit_id. auto.
          }
          { des_ifs. ii. esplits; eauto. }
          { des_ifs. rewrite URA.unit_id. ii.
            exploit Fuel.success_update; eauto. i. esplits; eauto. }
        }
        { instantiate (1 := fun r =>
                              exists (f1: Id -> A),
                                (forall i,
                                    (fun i fi =>
                                       ((match fm i with
                                         | Flag.emp => fi = f0 i
                                         | Flag.fail => OrderedCM.le (OrderedCM.add u fi) (f0 i)
                                         | Flag.success => True
                                         end) /\
                                          (r i =
                                             (Fuel.black fi 1: Fuel.t A)
                                               ⋅
                                               (if (excluded_middle_informative (fm i = Flag.success))
                                                then Fuel.white n
                                                else ε)))) i (f1 i))).
          intros fn WF SAT. eapply choice. i. ss.
          specialize (SAT x). des. rewrite SAT. destruct (fm x) eqn:FM.
          { esplits; eauto. }
          { esplits; eauto. }
          { esplits; eauto. }
        }
      }
      ss. des.
      assert (b =
                (((fun i => Fuel.black (f1 i) 1): (Id ==> Fuel.t A)%ra)
                   ⋅
                   (fun i =>
                      if (excluded_middle_informative (fm i = Flag.success))
                      then Fuel.white n
                      else ε))).
      { extensionality i. specialize (H i). des.
        rewrite H0. erewrite ! (@unfold_pointwise_add Id (Fuel.t A)). auto.
      }
      subst. iPoseProof "OWN" as "[OWN0 OWN1]".
      iModIntro. iFrame. iExists _. iSplit.
      2:{ iFrame. }
      iPureIntro. i. specialize (H i). des.
      erewrite ! (@unfold_pointwise_add Id (Fuel.t A)) in H0. des_ifs.
    Qed.

    Definition blacks_of (l: list Id): iProp :=
      fold_right (fun i P => black_ex i 1 ** P) True%I l.

    Definition whites_of (l: list Id) (u: A): iProp :=
      fold_right (fun i P => white i u ** P) True%I l.
  End FAIR.

  Section SOURCE.
    Variable (Id: Type).
    Definition srct: URA.t := @t Id Ord.t _.
    Context `{ING: @GRA.inG srct Σ}.

    Definition sat_source (f: imap Id owf) :=
      blacks_all f.

    Definition source_update
               (o: Ord.t)
               (ls lf: list Id)
               (f0: imap Id owf)
               (fm: fmap Id)
               (FAIL: forall i (IN: fm i = Flag.fail), List.In i lf)
               (SUCCESS: forall i (IN: List.In i ls), fm i = Flag.success)
      :
      (sat_source f0)
        -∗
        (whites_of lf Ord.one)
        -∗
        (#=>
           (∃ f1,
               (⌜fair_update f0 f1 fm⌝)
                 **
                 (sat_source f1)
                 **
                 (whites_of ls o))).
    Proof.
      iIntros "SAT WHITE".
      iPoseProof (blacks_update with "SAT [> WHITE]") as "> [% [[% BLACK] WHITE]]".
      { instantiate (1:=Ord.one). instantiate (1:=fm).
        iStopProof. cut (forall l (P: Id -> Prop) (COMPLETE: forall i (IN: P i), List.In i l), whites_of l Ord.one ⊢ #=> whites P Ord.one).
        { i. eapply H. auto. }
          induction l; ss; i.
          { iIntros "H". iApply (OwnM_Upd with "[]").
            { instantiate (1:=URA.unit). apply pointwise_updatable.
              i. des_ifs. exfalso. eauto.
            }
            { iApply (@OwnM_unit _ _ ING). }
          }
          iIntros "[WHITE WHITES]".
          iPoseProof ((@IHl (fun i => P i /\ a <> i)) with "WHITES") as "> WHITES".
          { i. des. hexploit COMPLETE; eauto. i. des; ss. }
          iCombine "WHITE WHITES" as "WHITES". iApply (OwnM_Upd with "WHITES").
          erewrite ! (@unfold_pointwise_add Id (Fuel.t Ord.t)).
          apply pointwise_updatable. i. unfold maps_to_res.
          des_ifs; des; ss; repeat rewrite URA.unit_id; repeat rewrite URA.unit_idl; ss.
          { ii. eapply URA.wf_mon. instantiate (1:=Fuel.white Ord.one). r_wf H. }
          { exfalso. eapply n0; ss. auto. }
      }
      { iExists f1. iFrame. iSplitR.
        { iPureIntro. ii. specialize (H i). des_ifs.
          ss. eapply Ord.lt_le_lt; [|eauto].
          unfold Ord.one. rewrite Hessenberg.add_S_l.
          rewrite Hessenberg.add_O_l. eapply Ord.S_lt.
        }
        { instantiate (1:=Jacobsthal.mult o (Ord.from_nat (List.length ls))).
          iStopProof. cut (forall l (P: Id -> Prop) (SOUND: forall i (IN: List.In i l), P i), whites P (o × List.length l)%ord ⊢ #=> whites_of l o).
          { i. eapply H0. auto. }
          induction l; ss; i.
          { iIntros "H". auto. }
          iIntros "H".
          iPoseProof (OwnM_Upd with "H") as "> H".
          { instantiate (1:=(maps_to_res a (Fuel.white o: Fuel.t Ord.t): (Id ==> Fuel.t Ord.t)%ra)
                              ⋅
                              (fun i =>
                                 if (excluded_middle_informative (P i))
                                 then (Fuel.white (o × List.length l)%ord: Fuel.t Ord.t)
                                 else ε): (Id ==> Fuel.t Ord.t)%ra).
            erewrite ! (@unfold_pointwise_add Id (Fuel.t Ord.t)).
            apply pointwise_updatable. i. unfold maps_to_res. des_ifs.
            { rewrite (@Fuel.white_sum Ord.t _ o (o × (Ord.from_nat (List.length l)))%ord).
              apply Fuel.white_mon. ss.
              rewrite Ord.from_nat_S. rewrite Jacobsthal.mult_S. reflexivity.
            }
            { rewrite URA.unit_idl.
              apply Fuel.white_mon. ss.
              apply Jacobsthal.le_mult_r. apply Ord.S_le.
            }
            { exfalso. eapply n. eapply SOUND. eauto. }
            { rewrite URA.unit_id. reflexivity. }
          }
          iPoseProof "H" as "[H0 H1]". iFrame. iApply IHl; [|eauto]. auto.
        }
      }
    Qed.
  End SOURCE.


  Section TARGET.
    Variable (_Id: Type).
    Let Id := id_sum thread_id _Id.
    Definition tgtt: URA.t := @t Id nat _.
    Context `{ING: @GRA.inG tgtt Σ}.

    Definition sat_target (f: imap Id nat_wf) (ths: TIdSet.t): iProp :=
      ∃ (f': imap Id nat_wf),
        (⌜(forall i, f (inr i) = f' (inr i)) /\
           (forall i (IN: TIdSet.In i ths), f (inl i) = f' (inl i))⌝)
          **
          (whites_all f')
          **
          (blacks (fun i => exists j, (<<NIN: ~ TIdSet.In j ths>>) /\ (<<EQ: i = inl j>>)))
    .

    Definition target_remove_thread
               tid ths
               (f: imap Id nat_wf)
      :
      (sat_target f ths)
        -∗
        (black_ex (inl tid) 1)
        -∗
        (#=>
           (sat_target f (NatMap.remove tid ths))).
    Proof.
      iIntros "[% [[% WHITES] [% [% BLACKS]]]] [% BLACK]". des.
      iExists f'. iFrame. iSplitR.
      { iPureIntro. split; auto. i. eapply H1.
        apply NatMapP.F.remove_in_iff in IN. des. auto.
      }
      iCombine "BLACKS BLACK" as "BLACK".
      iExists (fun i =>
                 match i with
                 | inl tid' => if (tid_dec tid' tid) then Some a else f0 i
                 | _ => f0 i
                 end).
      iSplitR.
      { iModIntro. iPureIntro. i. des_ifs.
        { split; i; ss. esplits; eauto.
          ii. apply NatMapP.F.remove_in_iff in H3. des; ss.
        }
        { rewrite H0. split; i.
          { des. esplits; eauto. ii.
            apply NatMapP.F.remove_in_iff in H2. des; ss.
          }
          { des. esplits; eauto. ii. clarify. eapply NIN.
            apply NatMapP.F.remove_in_iff. split; auto.
          }
        }
        { rewrite H0. split; i.
          { des; ss. }
          { des; ss. }
        }
      }
      iApply (OwnM_Upd with "BLACK").
      apply pointwise_updatable. i.
      erewrite ! (@unfold_pointwise_add Id (Fuel.t nat)).
      unfold maps_to_res. des_ifs; repeat rewrite URA.unit_id; repeat rewrite URA.unit_idl; ss.
      apply URA.extends_updatable. exists (Fuel.black n 1). apply URA.add_comm.
    Qed.

    Definition target_add_thread
               tid ths0 ths1
               (THS: TIdSet.add_new tid ths0 ths1)
               (f0 f1: imap Id nat_wf)
               (UPD: fair_update f0 f1 (sum_fmap_l (fun i => if tid_dec i tid then Flag.success else Flag.emp)))
      :
      (sat_target f0 ths0)
        -∗
        (#=>
           ((sat_target f1 ths1)
              **
              (black_ex (inl tid) 1))).
    Proof.
      iIntros "[% [[% WHITES] [% [% BLACKS]]]]". des.
      set (f2 :=
             (fun i =>
                match i with
                | inl tid' => if tid_dec tid' tid then None else f i
                | _ => f i
                end): Id -> option nat).
      iAssert (OwnM ((fun i =>
                        match (f i) with
                        | Some a => Fuel.black a 1
                        | None => ε
                        end) ⋅ (maps_to (inl tid) )

black

maps_to


      iExists f'. iFrame. iSplitR.
      { iPureIntro. split; auto. i. eapply H1.
        apply NatMapP.F.remove_in_iff in IN. des. auto.
      }
      iCombine "BLACKS BLACK" as "BLACK".
      iExists (fun i =>
                 match i with
                 | inl tid' => if (tid_dec tid' tid) then Some a else f0 i
                 | _ => f0 i
                 end).
      iSplitR.
      { iModIntro. iPureIntro. i. des_ifs.
        { split; i; ss. esplits; eauto.
          ii. apply NatMapP.F.remove_in_iff in H3. des; ss.
        }
        { rewrite H0. split; i.
          { des. esplits; eauto. ii.
            apply NatMapP.F.remove_in_iff in H2. des; ss.
          }
          { des. esplits; eauto. ii. clarify. eapply NIN.
            apply NatMapP.F.remove_in_iff. split; auto.
          }
        }
        { rewrite H0. split; i.
          { des; ss. }
          { des; ss. }
        }
      }
      iApply (OwnM_Upd with "BLACK").
      apply pointwise_updatable. i.
      erewrite ! (@unfold_pointwise_add Id (Fuel.t nat)).
      unfold maps_to_res. des_ifs; repeat rewrite URA.unit_id; repeat rewrite URA.unit_idl; ss.
      apply URA.extends_updatable. exists (Fuel.black n 1). apply URA.add_comm.
    Qed.


    Admitted.


r_solve.



      specialize (H0 (inl tid)). rewrite Heq in H0. inv H0.
      hexploit H2; eauto. i. des. clarify.

      hexploit H0; eauto.


      { admit. }
      { admit. }
      { admit. }
      { admit. }
      { admit. }
      { admit. }
      { admit. }

 des_ifs; try reflexivity.


auto.
      }

ii.

      {

ss.

in H2. des; ss.

          }
 eapply NIN.

split; i; ss. esplits; eauto.
          ii. apply NatMapP.F.remove_in_iff in H3. des; ss.
        }



des. auto.
      }
 ii.




match f0 i with
                        | Some a => Some a
                        |

      iApply (OwnM_Upd with "BLACK").

      iExists f'.
      assert (

NatMapP.F.in_find_iff
NatMap.In

odes.


    Admitted.

    Definition target_update_thread
               tid ths0 ths1
               (THS: TIdSet.add_new tid ths0 ths1)
               (f: imap Id nat_wf)
      :
      (sat_target f ths0)
        -∗
        (black_ex (inl tid) 1)
        -∗
        (#=>
           (∃ ths1,
               (⌜NatMap.remove tid ths0 = ths1⌝)
                 **
                 (sat_target f ths1))).
    Proof.
    Admitted.



               (FAIL: forall i (IN: fm i = Flag.fail), List.In i lf)
               (SUCCESS: forall i (IN: List.In i ls), fm i = Flag.success)
      :
      (sat_target f ths)
        -∗
        (sat_target f ths)
        -∗


        (whites_of lf Ord.one)
        -∗
        (#=>
           (∃ f1,
               (⌜fair_update f0 f1 fm⌝)
                 **
                 (sat_target f1 ths)
                 **
                 (whites_of ls o))).


    Proof.
      iIntros "SAT WHITE".
      iPoseProof (blacks_update with "SAT [> WHITE]") as "> [% [[% BLACK] WHITE]]".
      { instantiate (1:=Ord.one). instantiate (1:=fm).
        iStopProof. cut (forall l (P: Id -> Prop) (COMPLETE: forall i (IN: P i), List.In i l), whites_of l Ord.one ⊢ #=> whites P Ord.one).
        { i. eapply H. auto. }
          induction l; ss; i.
          { iIntros "H". iApply (OwnM_Upd with "[]").
            { instantiate (1:=URA.unit). apply pointwise_updatable.
              i. des_ifs. exfalso. eauto.
            }
            { iApply (@OwnM_unit _ _ ING). }
          }
          iIntros "[WHITE WHITES]".
          iPoseProof ((@IHl (fun i => P i /\ a <> i)) with "WHITES") as "> WHITES".
          { i. des. hexploit COMPLETE; eauto. i. des; ss. }
          iCombine "WHITE WHITES" as "WHITES". iApply (OwnM_Upd with "WHITES").
          erewrite ! (@unfold_pointwise_add Id (Fuel.t Ord.t)).
          apply pointwise_updatable. i. unfold maps_to_res.
          des_ifs; des; ss; repeat rewrite URA.unit_id; repeat rewrite URA.unit_idl; ss.
          { ii. eapply URA.wf_mon. instantiate (1:=Fuel.white Ord.one). r_wf H. }
          { exfalso. eapply n0; ss. auto. }
      }
      { iExists f1. iFrame. iSplitR.
        { iPureIntro. ii. specialize (H i). des_ifs.
          ss. eapply Ord.lt_le_lt; [|eauto].
          unfold Ord.one. rewrite Hessenberg.add_S_l.
          rewrite Hessenberg.add_O_l. eapply Ord.S_lt.
        }
        { instantiate (1:=Jacobsthal.mult o (Ord.from_nat (List.length ls))).
          iStopProof. cut (forall l (P: Id -> Prop) (SOUND: forall i (IN: List.In i l), P i), whites P (o × List.length l)%ord ⊢ #=> whites_of l o).
          { i. eapply H0. auto. }
          induction l; ss; i.
          { iIntros "H". auto. }
          iIntros "H".
          iPoseProof (OwnM_Upd with "H") as "> H".
          { instantiate (1:=(maps_to_res a (Fuel.white o: Fuel.t Ord.t): (Id ==> Fuel.t Ord.t)%ra)
                              ⋅
                              (fun i =>
                                 if (excluded_middle_informative (P i))
                                 then (Fuel.white (o × List.length l)%ord: Fuel.t Ord.t)
                                 else ε): (Id ==> Fuel.t Ord.t)%ra).
            erewrite ! (@unfold_pointwise_add Id (Fuel.t Ord.t)).
            apply pointwise_updatable. i. unfold maps_to_res. des_ifs.
            { rewrite (@Fuel.white_sum Ord.t _ o (o × (Ord.from_nat (List.length l)))%ord).
              apply Fuel.white_mon. ss.
              rewrite Ord.from_nat_S. rewrite Jacobsthal.mult_S. reflexivity.
            }
            { rewrite URA.unit_idl.
              apply Fuel.white_mon. ss.
              apply Jacobsthal.le_mult_r. apply Ord.S_le.
            }
            { exfalso. eapply n. eapply SOUND. eauto. }
            { rewrite URA.unit_id. reflexivity. }
          }
          iPoseProof "H" as "[H0 H1]". iFrame. iApply IHl; [|eauto]. auto.
        }
      }
    Qed.


    Definition target_update
               (o: Ord.t)
               (ls lf: list Id)
               (f0: imap Id owf)
               (fm: fmap Id)

               (FAIL: forall i (IN: fm i = Flag.fail), List.In i lf)
               (SUCCESS: forall i (IN: List.In i ls), fm i = Flag.success)
      :
      (sat_target f0 ths)
        -∗
        (whites_of lf Ord.one)
        -∗
        (#=>
           (∃ f1,
               (⌜fair_update f0 f1 fm⌝)
                 **
                 (sat_target f1 ths)
                 **
                 (whites_of ls o))).


    Proof.
      iIntros "SAT WHITE".
      iPoseProof (blacks_update with "SAT [> WHITE]") as "> [% [[% BLACK] WHITE]]".
      { instantiate (1:=Ord.one). instantiate (1:=fm).
        iStopProof. cut (forall l (P: Id -> Prop) (COMPLETE: forall i (IN: P i), List.In i l), whites_of l Ord.one ⊢ #=> whites P Ord.one).
        { i. eapply H. auto. }
          induction l; ss; i.
          { iIntros "H". iApply (OwnM_Upd with "[]").
            { instantiate (1:=URA.unit). apply pointwise_updatable.
              i. des_ifs. exfalso. eauto.
            }
            { iApply (@OwnM_unit _ _ ING). }
          }
          iIntros "[WHITE WHITES]".
          iPoseProof ((@IHl (fun i => P i /\ a <> i)) with "WHITES") as "> WHITES".
          { i. des. hexploit COMPLETE; eauto. i. des; ss. }
          iCombine "WHITE WHITES" as "WHITES". iApply (OwnM_Upd with "WHITES").
          erewrite ! (@unfold_pointwise_add Id (Fuel.t Ord.t)).
          apply pointwise_updatable. i. unfold maps_to_res.
          des_ifs; des; ss; repeat rewrite URA.unit_id; repeat rewrite URA.unit_idl; ss.
          { ii. eapply URA.wf_mon. instantiate (1:=Fuel.white Ord.one). r_wf H. }
          { exfalso. eapply n0; ss. auto. }
      }
      { iExists f1. iFrame. iSplitR.
        { iPureIntro. ii. specialize (H i). des_ifs.
          ss. eapply Ord.lt_le_lt; [|eauto].
          unfold Ord.one. rewrite Hessenberg.add_S_l.
          rewrite Hessenberg.add_O_l. eapply Ord.S_lt.
        }
        { instantiate (1:=Jacobsthal.mult o (Ord.from_nat (List.length ls))).
          iStopProof. cut (forall l (P: Id -> Prop) (SOUND: forall i (IN: List.In i l), P i), whites P (o × List.length l)%ord ⊢ #=> whites_of l o).
          { i. eapply H0. auto. }
          induction l; ss; i.
          { iIntros "H". auto. }
          iIntros "H".
          iPoseProof (OwnM_Upd with "H") as "> H".
          { instantiate (1:=(maps_to_res a (Fuel.white o: Fuel.t Ord.t): (Id ==> Fuel.t Ord.t)%ra)
                              ⋅
                              (fun i =>
                                 if (excluded_middle_informative (P i))
                                 then (Fuel.white (o × List.length l)%ord: Fuel.t Ord.t)
                                 else ε): (Id ==> Fuel.t Ord.t)%ra).
            erewrite ! (@unfold_pointwise_add Id (Fuel.t Ord.t)).
            apply pointwise_updatable. i. unfold maps_to_res. des_ifs.
            { rewrite (@Fuel.white_sum Ord.t _ o (o × (Ord.from_nat (List.length l)))%ord).
              apply Fuel.white_mon. ss.
              rewrite Ord.from_nat_S. rewrite Jacobsthal.mult_S. reflexivity.
            }
            { rewrite URA.unit_idl.
              apply Fuel.white_mon. ss.
              apply Jacobsthal.le_mult_r. apply Ord.S_le.
            }
            { exfalso. eapply n. eapply SOUND. eauto. }
            { rewrite URA.unit_id. reflexivity. }
          }
          iPoseProof "H" as "[H0 H1]". iFrame. iApply IHl; [|eauto]. auto.
        }
      }
    Qed.


  End SOURCE.


  Section FAIR.
    Variable (Id: Type).
    Variable (A: Type).
    Context `{L: OrderedCM.t A}.


End FairRA.

Global Opaque Fuel.from_monoid Fuel.quotient_add.

Module CounterRA.
  Section MONOID.
    Variable (A: Type).
    Context `{OrderedCM.t A}.

    Record partition :=
      mk {
          collection:> A -> Prop;
          closed: forall a0 a1 (LE: OrderedCM.le a0 a1),
            collection a1 -> collection a0;
        }.

    Lemma partition_ext (p0 p1: partition)
          (EXT: forall a, p0 a <-> p1 a)
      :
      p0 = p1.
    Proof.
      destruct p0, p1. assert (collection0 = collection1).
      { extensionality a. eapply propositional_extensionality. ss. }
      { subst. f_equal. apply proof_irrelevance. }
    Qed.

    Program Definition partition_join (p0 p1: partition): partition :=
      mk (fun a => p0 a /\ p1 a) _.
    Next Obligation.
      split.
      { eapply closed; eauto. }
      { eapply closed; eauto. }
    Qed.

    Program Definition partition_top: partition :=
      mk (fun _ => True) _.

    Program Definition partition_from_monoid (a: A): partition :=
      mk (fun a' => OrderedCM.le a' a) _.
    Next Obligation.
      etrans; eauto.
    Qed.

    Definition car: Type :=
      partition * (@Fuel.quotient A _).

    Definition add: car -> car -> car :=
      fun '(s0, q0) '(s1, q1) =>
        (partition_join s0 s1, Fuel.quotient_add q0 q1).

    Definition wf: car -> Prop :=
      fun '(s, q) =>
        exists a, Fuel.collection q a /\ s a.

    Definition core: car -> car :=
      fun '(s, q) => (s, Fuel.from_monoid OrderedCM.unit).

    Definition unit: car :=
      (partition_top, Fuel.from_monoid OrderedCM.unit).

    Global Program Instance t: URA.t := {
        car := car;
        unit := unit;
        _add := add;
        _wf := wf;
        core := core;
      }
    .
    Next Obligation.
    Proof.
      unfold add. des_ifs. f_equal.
      { apply partition_ext. i. ss. split; i; des; auto. }
      { apply Fuel.quotient_add_comm. }
    Qed.
    Next Obligation.
    Proof.
      unfold add. des_ifs. f_equal.
      { apply partition_ext. i. ss. split; i; des; auto. }
      { apply Fuel.quotient_add_assoc. }
    Qed.
    Next Obligation.
    Proof.
      unseal "ra". unfold add, unit. des_ifs. f_equal.
      { apply partition_ext. i. ss. split; i; des; auto. }
      { hexploit (Fuel.from_monoid_exist q). i. des. subst.
        rewrite Fuel.from_monoid_add.
        apply Fuel.from_monoid_eq. eapply OrderedCM.add_unit_eq_l.
      }
    Qed.
    Next Obligation.
    Proof.
      unseal "ra". ss. splits; auto. exists OrderedCM.unit.
      rewrite Fuel.from_monoid_le. splits; auto. reflexivity.
    Qed.
    Next Obligation.
    Proof.
      unseal "ra". unfold add, wf in *. des_ifs. des.
      hexploit (Fuel.from_monoid_exist q). i. des. subst.
      hexploit (Fuel.from_monoid_exist q1). i. des. subst.
      rewrite Fuel.from_monoid_add in H0.
      rewrite Fuel.from_monoid_le in H0. esplits; eauto.
      { rewrite Fuel.from_monoid_le. etrans; eauto.
        apply OrderedCM.add_base_l.
      }
      { ss. des. auto. }
    Qed.
    Next Obligation.
    Proof.
      unseal "ra". unfold add. des_ifs. ss. clarify. f_equal.
      { apply partition_ext. i. ss. split; i; des; auto. }
      { hexploit (Fuel.from_monoid_exist q0). i. des. subst.
        rewrite Fuel.from_monoid_add.
        apply Fuel.from_monoid_eq. apply OrderedCM.add_unit_eq_r.
      }
    Qed.
    Next Obligation.
    Proof.
      unfold core. des_ifs.
    Qed.
    Next Obligation.
    Proof.
      unseal "ra". unfold add. des_ifs. ss. clarify.
      eexists (_, _). f_equal.
      rewrite Fuel.from_monoid_add.
      apply Fuel.from_monoid_eq. symmetry. apply OrderedCM.add_unit_eq_r.
    Qed.

    Definition black (a: A): car :=
      (partition_from_monoid a, Fuel.from_monoid OrderedCM.unit).

    Definition white (a: A): car :=
      (partition_top, Fuel.from_monoid a).

    Lemma black_persistent a
      :
      URA.core (black a) = black a.
    Proof.
      ss.
    Qed.

    Lemma black_mon a0 a1
          (LE: OrderedCM.le a0 a1)
      :
      URA.extends (black a1) (black a0).
    Proof.
      exists (black a0).
      ur. unfold black. f_equal.
      { apply partition_ext. i. ss. split; i; des; auto.
        split; auto. etrans; eauto.
      }
      { rewrite Fuel.from_monoid_add.
        apply Fuel.from_monoid_eq. apply OrderedCM.add_unit_eq_r.
      }
    Qed.

    Lemma white_mon a0 a1
          (LE: OrderedCM.le a0 a1)
      :
      URA.updatable (white a1) (white a0).
    Proof.
      ii. ur in H0. ur. des_ifs.
      hexploit (Fuel.from_monoid_exist q). i. des. subst.
      rewrite Fuel.from_monoid_add in *. ss. des.
      esplits; eauto.
      rewrite Fuel.from_monoid_le in H0.
      rewrite Fuel.from_monoid_le. etrans; eauto.
      apply OrderedCM.le_add_r; auto.
    Qed.

    Lemma white_eq a0 a1
          (LE: OrderedCM.eq a0 a1)
      :
      white a0 = white a1.
    Proof.
      unfold white. f_equal. apply Fuel.from_monoid_eq; auto.
    Qed.

    Lemma white_split a0 a1
      :
      white (OrderedCM.add a0 a1) = white a0 ⋅ white a1.
    Proof.
      ur. unfold white. f_equal.
      { apply partition_ext. i. ss. }
      { rewrite Fuel.from_monoid_add. auto. }
    Qed.

    Lemma black_white_wf a
      :
      URA.wf (black a ⋅ white a).
    Proof.
      ur. exists a. rewrite Fuel.from_monoid_add. splits; auto.
      { rewrite Fuel.from_monoid_le. apply OrderedCM.add_unit_le_r. }
      { reflexivity. }
    Qed.

    Lemma black_white_decr a0 a1
      :
      URA.updatable_set (black a0 ⋅ white a1) (fun r => exists a2, r = black a2 /\ OrderedCM.le (OrderedCM.add a2 a1) a0).
    Proof.
      ii. ur in WF. ss. des_ifs.
      hexploit (Fuel.from_monoid_exist q). i. des. subst. ss. des.
      rewrite ! Fuel.from_monoid_add in *.
      rewrite Fuel.from_monoid_le in WF.
      eexists (_, _). esplits.
      { reflexivity. }
      { instantiate (1:=a). etrans; eauto.
        etrans; eauto. etrans.
        { eapply OrderedCM.add_comm_le. }
        { apply OrderedCM.le_add_r. apply OrderedCM.add_base_r. }
      }
      { ur. esplits.
        { rewrite Fuel.from_monoid_add. rewrite Fuel.from_monoid_le.
          eapply OrderedCM.add_unit_le_r.
        }
        { reflexivity. }
        { eapply closed; eauto. etrans; eauto.
          eapply OrderedCM.add_base_r.
        }
      }
    Qed.

    Lemma black_white_compare a0 a1
          (WF: URA.wf (black a0 ⋅ white a1))
      :
      OrderedCM.le a1 a0.
    Proof.
      exploit black_white_decr.
      { rewrite URA.unit_id. eauto. }
      i. des. etrans; eauto. apply OrderedCM.add_base_r.
    Qed.
  End MONOID.
End CounterRA.


From Ordinal Require Export Ordinal Arithmetic Hessenberg ClassicalHessenberg.

Lemma ord_mult_split (n: nat)
  :
  ((Ord.omega ⊕ Ord.large × n) <= (Ord.large × (S n)))%ord.
Proof.
  rewrite Ord.from_nat_S.
  rewrite Jacobsthal.mult_S.
  apply Hessenberg.le_add_l.
  apply Ord.lt_le.
  rewrite Ord.omega_from_peano_lt_set.
  apply Ord.large_lt_from_wf_set.
Qed.

Module ObligationRA.
  Definition t: URA.t := @FiniteMap.t (URA.prod (@CounterRA.t Ord.t _) (OneShot.t unit)).
  Section RA.
    Context `{@GRA.inG t Σ}.

    Definition black (k: nat) (o: Ord.t): iProp :=
      OwnM (FiniteMap.singleton k ((CounterRA.black o: @CounterRA.t Ord.t _, ε: OneShot.t unit): URA.prod (@CounterRA.t Ord.t _) (OneShot.t unit))).

    Definition white (k: nat) (o: Ord.t): iProp :=
      OwnM (FiniteMap.singleton k ((CounterRA.white o: @CounterRA.t Ord.t _, ε: OneShot.t unit): URA.prod (@CounterRA.t Ord.t _) (OneShot.t unit))).

    Definition pending (k: nat): iProp :=
      OwnM (FiniteMap.singleton k ((ε: @CounterRA.t Ord.t _, OneShot.pending unit: OneShot.t unit): URA.prod (@CounterRA.t Ord.t _) (OneShot.t unit))).

    Definition shot (k: nat): iProp :=
      OwnM (FiniteMap.singleton k ((ε: @CounterRA.t Ord.t _, OneShot.shot tt: OneShot.t unit): URA.prod (@CounterRA.t Ord.t _) (OneShot.t unit))).

    Definition white_one k: iProp :=
      white k (Ord.S Ord.O).

    Lemma black_persistent k o
      :
      black k o -∗ □ black k o.
    Proof.
      iIntros "H".
      unfold black.
      iPoseProof (own_persistent with "H") as "H".
      rewrite FiniteMap.singleton_core. auto.
    Qed.

    Global Program Instance Persistent_black k o: Persistent (black k o).
    Next Obligation.
    Proof.
      i. iIntros "POS". iPoseProof (black_persistent with "POS") as "POS". auto.
    Qed.

    Lemma shot_persistent k
      :
      shot k -∗ □ shot k.
    Proof.
      iIntros "H".
      unfold black.
      iPoseProof (own_persistent with "H") as "H".
      rewrite FiniteMap.singleton_core. auto.
    Qed.

    Global Program Instance Persistent_shot k: Persistent (shot k).
    Next Obligation.
    Proof.
      i. iIntros "POS". ss. iPoseProof (shot_persistent with "POS") as "POS". auto.
    Qed.

    Lemma pending_unique k
      :
      (pending k)
        -∗
        (pending k)
        -∗
        False.
    Proof.
      iIntros "H0 H1". iCombine "H0 H1" as "H".
      iOwnWf "H". rewrite FiniteMap.singleton_add in H0.
      rewrite FiniteMap.singleton_wf in H0.
      ur in H0. des. exfalso. eapply OneShot.pending_unique; eauto.
    Qed.

    Lemma pending_not_shot k
      :
      (pending k)
        -∗
        (shot k)
        -∗
        False.
    Proof.
      iIntros "H0 H1". iCombine "H0 H1" as "H".
      iOwnWf "H". rewrite FiniteMap.singleton_add in H0.
      rewrite FiniteMap.singleton_wf in H0.
      ur in H0. des. exfalso. eapply OneShot.pending_not_shot; eauto.
    Qed.

    Lemma pending_shot k
      :
      (pending k)
        -∗
        #=> (shot k).
    Proof.
      iApply OwnM_Upd. eapply FiniteMap.singleton_updatable.
      apply URA.prod_updatable.
      { reflexivity. }
      { apply OneShot.pending_shot. }
    Qed.

    Lemma alloc o
      :
      ⊢ #=> (∃ k, black k o ** white k o ** pending k).
    Proof.
      iPoseProof (@OwnM_unit _ _ H) as "H".
      iPoseProof (OwnM_Upd_set with "H") as "> H0".
      { eapply FiniteMap.singleton_alloc.
        instantiate (1:=((CounterRA.black o, ε): URA.prod (@CounterRA.t Ord.t _) (OneShot.t unit)) ⋅ ((CounterRA.white o, ε): URA.prod (@CounterRA.t Ord.t _) (OneShot.t unit)) ⋅ (ε, OneShot.pending unit)).
        repeat rewrite unfold_prod_add. repeat rewrite URA.unit_idl. repeat rewrite URA.unit_id.
        rewrite unfold_prod_wf. ss. split.
        { eapply CounterRA.black_white_wf. }
        { apply OneShot.pending_wf. }
      }
      iDestruct "H0" as "[% [% H0]]".
      des. subst. erewrite <- FiniteMap.singleton_add. erewrite <- FiniteMap.singleton_add.
      iDestruct "H0" as "[[H0 H1] H2]".
      iModIntro. iExists _. iFrame.
    Qed.

    Lemma black_mon o1 k o0
          (LE: Ord.le o0 o1)
      :
      black k o0 -∗ black k o1.
    Proof.
      iApply OwnM_extends. apply FiniteMap.singleton_extends.
      apply URA.prod_extends. split; [|reflexivity].
      apply CounterRA.black_mon. auto.
    Qed.

    Lemma white_mon o1 k o0
          (LE: Ord.le o0 o1)
      :
      white k o1 -∗ #=> white k o0.
    Proof.
      iApply OwnM_Upd. apply FiniteMap.singleton_updatable.
      apply URA.prod_updatable; [|reflexivity].
      apply CounterRA.white_mon. auto.
    Qed.

    Lemma white_eq o1 k o0
          (LE: Ord.eq o0 o1)
      :
      white k o0 -∗ white k o1.
    Proof.
      unfold white. erewrite CounterRA.white_eq; auto.
    Qed.

    Lemma white_merge k o0 o1
      :
      (white k o0)
        -∗
        (white k o1)
        -∗
        (white k (Hessenberg.add o0 o1)).
    Proof.
      iIntros "H0 H1". unfold white.
      replace (CounterRA.white (Hessenberg.add o0 o1): @CounterRA.t Ord.t ord_OrderedCM) with
        ((CounterRA.white o0: @CounterRA.t Ord.t _) ⋅ (CounterRA.white o1: @CounterRA.t Ord.t _)).
      { iCombine "H0 H1" as "H". rewrite FiniteMap.singleton_add.
        rewrite unfold_prod_add. rewrite URA.unit_id. auto.
      }
      { symmetry. eapply (@CounterRA.white_split Ord.t ord_OrderedCM o0 o1). }
    Qed.

    Lemma white_split_eq k o0 o1
      :
      (white k (Hessenberg.add o0 o1))
        -∗
        (white k o0 ** white k o1).
    Proof.
      iIntros "H". unfold white.
      replace (CounterRA.white (Hessenberg.add o0 o1): @CounterRA.t Ord.t ord_OrderedCM, ε: @OneShot.t unit) with
        (((CounterRA.white o0, ε): URA.prod (@CounterRA.t Ord.t _) (OneShot.t unit)) ⋅ ((CounterRA.white o1, ε): URA.prod (@CounterRA.t Ord.t _) (OneShot.t unit))).
      { rewrite <- FiniteMap.singleton_add. iDestruct "H" as "[H0 H1]". iFrame. }
      { rewrite unfold_prod_add. rewrite URA.unit_id. f_equal.
        symmetry. eapply (@CounterRA.white_split Ord.t ord_OrderedCM o0 o1).
      }
    Qed.

    Lemma white_split o0 o1 k o
          (LE: Ord.le (Hessenberg.add o0 o1) o)
      :
      (white k o)
        -∗
        (#=> (white k o0 ** white k o1)).
    Proof.
      iIntros "H". iPoseProof (white_mon with "H") as "> H"; eauto.
      iModIntro. iApply white_split_eq; auto.
    Qed.

    Lemma white_split_one o0 k o1
          (LT: Ord.lt o0 o1)
      :
      (white k o1)
        -∗
        (#=> (white k o0 ** white_one k)).
    Proof.
      iIntros "H". iApply white_split; eauto.
      rewrite Hessenberg.add_S_r. rewrite Hessenberg.add_O_r.
      apply Ord.S_supremum; auto.
    Qed.

    Lemma black_white_compare k o0 o1
      :
      (black k o0)
        -∗
        (white k o1)
        -∗
        ⌜Ord.le o1 o0⌝.
    Proof.
      iIntros "H0 H1".
      iCombine "H0 H1" as "H". rewrite FiniteMap.singleton_add.
      iOwnWf "H". iPureIntro.
      apply FiniteMap.singleton_wf in H0.
      rewrite ! unfold_prod_add in H0.
      rewrite unfold_prod_wf in H0. des. ss.
      apply CounterRA.black_white_compare in H0. auto.
    Qed.

    Lemma black_white_decr k o0 o1
      :
      (black k o0)
        -∗
        (white k o1)
        -∗
        (#=> ∃ o2, black k o2 ** ⌜Ord.le (Hessenberg.add o2 o1) o0⌝).
    Proof.
      iIntros "H0 H1".
      iCombine "H0 H1" as "H". rewrite FiniteMap.singleton_add.
      iPoseProof (OwnM_Upd_set with "H") as "> [% [% H]]".
      { eapply FiniteMap.singleton_updatable_set.
        rewrite unfold_prod_add. eapply URA.prod_updatable_set.
        { eapply CounterRA.black_white_decr. }
        { instantiate (1:=eq (ε ⋅ ε: OneShot.t unit)). ii. esplits; eauto. }
      }
      { ss. des. destruct m1. des; subst.
        rewrite URA.unit_id. iModIntro. iExists _. iFrame. eauto. }
    Qed.

    Lemma black_white_decr_one k o1
      :
      (black k o1)
        -∗
        (white_one k)
        -∗
        (#=> ∃ o0, black k o0 ** ⌜Ord.lt o0 o1⌝).
    Proof.
      iIntros "H0 H1".
      iPoseProof (black_white_decr with "H0 H1") as "> [% [H %]]".
      iModIntro. iExists _. iFrame. iPureIntro.
      eapply Ord.lt_le_lt; eauto.
      rewrite Hessenberg.add_S_r. rewrite Hessenberg.add_O_r.
      apply Ord.S_lt; auto.
    Qed.

    Lemma black_white_annihilate o_w0 k o_b1 o_w1
          (LT: Ord.lt o_w0 o_w1)
      :
      (black k o_b1)
        -∗
        (white k o_w1)
        -∗
        (#=> ∃ o_b0, black k o_b0 ** white k o_w0 ** ⌜Ord.lt o_b0 o_b1⌝).
    Proof.
      iIntros "H0 H1".
      iPoseProof (white_split_one with "H1") as "> [H1 H2]"; [eauto|].
      iPoseProof (black_white_decr_one with "H0 H2") as "> [% [H0 %]]".
      iModIntro. iExists _. iFrame. auto.
    Qed.
  End RA.

  Section EDGE.
    Context `{Σ: GRA.t}.
    Context `{@GRA.inG t Σ}.
    Context `{@GRA.inG (Region.t (nat * nat * Ord.t)) Σ}.

    Definition edge: (nat * nat * Ord.t) -> iProp :=
      fun '(k0, k1, c) => (∃ o, black k0 o ** white k1 (Jacobsthal.mult c o))%I.

    Definition edges_sat: iProp := Region.sat edge.

    Definition amplifier (k0 k1: nat) (c: Ord.t): iProp :=
      □ (∀ o, white k0 o -* #=(edges_sat)=> white k1 (Jacobsthal.mult c o)).

    Lemma amplifier_persistent k0 k1 c
      :
      amplifier k0 k1 c ⊢ □ amplifier k0 k1 c.
    Proof.
      iIntros "# H". auto.
    Qed.

    Global Program Instance Persistent_amplifier k0 k1 c: Persistent (amplifier k0 k1 c).

    Local Opaque IUpd.
    Lemma amplifier_mon k0 k1 c0 c1
          (LE: Ord.le c0 c1)
      :
      amplifier k0 k1 c1 ⊢ amplifier k0 k1 c0.
    Proof.
      iIntros "# H". iModIntro. iIntros "% WHITE".
      iPoseProof ("H" with "WHITE") as "> WHITE".
      iPoseProof (white_mon with "WHITE") as "> WHITE".
      {  eapply Jacobsthal.le_mult_l. eauto. }
      iModIntro. auto.
    Qed.

    Lemma amplifier_trans k0 k1 k2 c0 c1
      :
      (amplifier k0 k1 c0)
        -∗
        (amplifier k1 k2 c1)
        -∗
        (amplifier k0 k2 (Jacobsthal.mult c1 c0)).
    Proof.
      iIntros "# H0 # H1". iModIntro. iIntros "% WHITE".
      iPoseProof ("H0" with "WHITE") as "> WHITE".
      iPoseProof ("H1" with "WHITE") as "> WHITE".
      iPoseProof (white_mon with "WHITE") as "> WHITE".
      { rewrite <- ClassicJacobsthal.mult_assoc. reflexivity. }
      iModIntro. auto.
    Qed.

    Lemma amplifier_amplify k0 k1 c o
      :
      (amplifier k0 k1 c)
        -∗
        (white k0 o)
        -∗
        (#=(edges_sat)=> white k1 (Jacobsthal.mult c o)).
    Proof.
      iIntros "H0 H1".
      iPoseProof ("H0" with "H1") as "> H". iModIntro. auto.
    Qed.

    Local Transparent IUpd.
    Lemma amplifier_intro k0 k1 c o
      :
      (black k0 o)
        -∗
        (white k1 (Jacobsthal.mult c o))
        -∗
        (#=(edges_sat)=> amplifier k0 k1 c).
    Proof.
      iIntros "BLACK WHITE".
      iPoseProof (Region.alloc with "[BLACK WHITE]") as "H".
      { instantiate (1:=(k0, k1, c)). instantiate (1:=edge).
        ss. iExists _. iFrame.
      }
      iMod "H" as "[% # H]". iModIntro.
      unfold amplifier. iModIntro. iIntros "% WHITE".
      iApply (Region.update with "H [WHITE]").
      iIntros "[% [H0 H1]]".
      iPoseProof (black_white_decr with "H0 WHITE") as "> [% [H0 %]]".
      iPoseProof (white_mon with "H1") as "> H1".
      { rewrite <- Jacobsthal.le_mult_r; [|eauto].
        rewrite ClassicJacobsthal.mult_dist. reflexivity.
      }
      iPoseProof (white_split_eq with "H1") as "[H1 H2]".
      iFrame. iModIntro. iExists _. iFrame.
    Qed.
  End EDGE.


  Section ARROW.
    Variable (Id: Type).
    Context `{Σ: GRA.t}.
    Context `{@GRA.inG t Σ}.
    Context `{@GRA.inG (@FairRA.t Id nat _) Σ}.
    Context `{@GRA.inG (@FiniteMap.t (OneShot.t unit)) Σ}.
    Context `{@GRA.inG (Region.t (Id * nat * Ord.t * Qp * nat)) Σ}.

    Definition arrow: (Id * nat * Ord.t * Qp * nat) -> iProp :=
      fun '(i, k, c, q, x) =>
        ((OwnM (FiniteMap.singleton x (OneShot.shot tt)) ** shot k)
         ∨
           (∃ n, (FairRA.black i n q) ** white k (Jacobsthal.mult c (Ord.from_nat n))))%I.

    Definition arrows_sat: iProp := Region.sat arrow.

    Definition correl (i: Id) (k: nat) (c: Ord.t): iProp :=
      ∃ r q x, Region.white r (i, k, c, q, x).

    Lemma correl_persistent i k c
      :
      correl i k c ⊢ □ correl i k c.
    Proof.
      iIntros "# H". auto.
    Qed.

    Global Program Instance Persistent_correl i k c: Persistent (correl i k c).

    Local Transparent IUpd.
    Lemma correl_correlate i k c n
      :
      (correl i k c)
        -∗
        (FairRA.white i n)
        -∗
        (#=(arrows_sat)=> white k (Jacobsthal.mult c (Ord.from_nat n)) ∨ shot k).
    Proof.
      iIntros "[% [% [% WHITE]]] H".
      iApply (Region.update with "WHITE [H]").
      iIntros "[[OWN # SHOT]|[% [BLACK WHITE]]]".
      { iModIntro. iSplitL.
        { iLeft. iFrame. iApply "SHOT". }
        { iRight. auto. }
      }
      { iPoseProof (FairRA.decr_update with "BLACK H") as "> [% [H %]]".
        iPoseProof (white_split with "WHITE") as "> [WHITE0 WHITE1]".
        { ss. apply OrdArith.le_from_nat in H3.
          rewrite Hessenberg.add_from_nat in H3. rewrite <- H3.
          rewrite ClassicJacobsthal.mult_dist. reflexivity.
        }
        iModIntro. iSplitR "WHITE0".
        { iRight. iExists _. iFrame. }
        { iLeft. auto. }
      }
    Qed.

    Definition duty_list (i: Id) (rs: list (nat * (nat * Ord.t * Qp * nat))) (q: Qp): iProp :=
      (fold_right (fun '(r, (k, c, q, x)) P =>
                     (Region.white r (i, k, c, q, x))
                       **
                       (OwnM ((FiniteMap.singleton x (OneShot.pending unit))))
                       ** P) True%I rs)
        **
        (⌜(fold_right (fun '(r, (k, c, q0, x)) q1 => (q0 + q1)%Qp) q rs = 1%Qp)⌝)
    .

    Lemma duty_list_nil i
      :
      ⊢ duty_list i [] 1%Qp.
    Proof.
      unfold duty_list. iSplit; ss.
    Qed.

    Lemma duty_list_fold i tl (q0: Qp) r k c (q1: Qp) x
      :
      (duty_list i tl (q0 + q1)%Qp)
        -∗
        (Region.white r (i, k, c, q1, x))
        -∗
        (OwnM ((FiniteMap.singleton x (OneShot.pending unit))))
        -∗
        (duty_list i ((r, (k, c, q1, x))::tl) q0).
    Proof.
      iIntros "[DUTY %] WHITE OWN". des. iSplit.
      { ss. iFrame. }
      iPureIntro. ss. rewrite <- H3.
      clear H3. revert q0 q1. induction tl.
      { i. ss. rewrite Qp_add_comm. auto. }
      { i. ss. destruct a as [? [[[? ?] ?] ?]]. rewrite <- IHtl.
        rewrite Qp_add_assoc. rewrite Qp_add_assoc. f_equal.
        apply Qp_add_comm.
      }
    Qed.

    Lemma duty_list_unfold i tl (q0: Qp) r k c (q1: Qp) x
      :
      (duty_list i ((r, (k, c, q1, x))::tl) q0)
        -∗
        (Region.white r (i, k, c, q1, x) ** OwnM ((FiniteMap.singleton x (OneShot.pending unit))) ** duty_list i tl (q0 + q1)%Qp).
    Proof.
      iIntros "[DUTY %]". ss.
      iPoseProof "DUTY" as "[[WHITE OWN] DUTY]". iFrame.
      iPureIntro. rewrite <- H3.
      clear H3. revert q0 q1. induction tl.
      { i. ss. apply Qp_add_comm. }
      { i. ss. destruct a as [? [[[? ?] ?] ?]]. rewrite IHtl.
        rewrite Qp_add_assoc. rewrite Qp_add_assoc. f_equal.
        apply Qp_add_comm.
      }
    Qed.

    Lemma duty_list_permutation i rs0 rs1 q
          (PERM: Permutation rs0 rs1)
      :
      (duty_list i rs0 q)
        -∗
        (duty_list i rs1 q).
    Proof.
      revert q. rr in PERM.
      pattern rs0, rs1. revert rs0 rs1 PERM. eapply Permutation_ind_bis.
      { iIntros. ss. }
      { i. iIntros "DUTY". destruct x as [? [[[? ?] ?] ?]].
        iPoseProof (duty_list_unfold with "DUTY") as "[[WHITE OWN] DUTY]".
        iPoseProof (H4 with "DUTY") as "DUTY".
        iApply (duty_list_fold with "DUTY WHITE OWN").
      }
      { i. iIntros "DUTY".
        destruct x as [? [[[? ?] ?] ?]]. destruct y as [? [[[? ?] ?] ?]].
        iPoseProof (duty_list_unfold with "DUTY") as "[[WHITE0 OWN0] DUTY]".
        iPoseProof (duty_list_unfold with "DUTY") as "[[WHITE1 OWN1] DUTY]".
        iPoseProof (H4 with "DUTY") as "DUTY".
        iApply (duty_list_fold with "[DUTY WHITE0 OWN0] WHITE1 OWN1").
        replace (q + q1 + q0)%Qp with ((q + q0) + q1)%Qp.
        2:{ rewrite <- Qp_add_assoc. rewrite <- Qp_add_assoc. f_equal. apply Qp_add_comm. }
        iApply (duty_list_fold with "DUTY WHITE0 OWN0").
      }
      { i. iIntros "DUTY". iApply H6. iApply H4. auto. }
    Qed.

    Definition duty (i: Id) (l: list (nat * Ord.t)): iProp :=
      ∃ (rs: list (nat * (nat * Ord.t * Qp * nat))) (q: Qp),
        (FairRA.black_ex i q)
          **
          (duty_list i rs q)
          **
          (⌜List.map (fun '(r, (k, c, q, x)) => (k, c)) rs = l⌝)
    .

    Lemma duty_permutation i l0 l1
          (PERM: Permutation l0 l1)
      :
      (duty i l0)
        -∗
        (duty i l1).
    Proof.
      iIntros "[% [% [[BLACK DUTY] %]]]".
      assert (exists rs1, List.map (fun '(r, (k, c, q, x)) => (k, c)) rs1 = l1 /\ Permutation rs rs1).
      { revert rs H3. pattern l0, l1. revert l0 l1 PERM.
        eapply Permutation_ind_bis; i; ss.
        { destruct rs; ss. exists []. ss. }
        { destruct rs; ss. des_ifs. hexploit H4; eauto. i. des.
          rewrite <- H5. eexists ((_, (_, _, _, _))::_). ss. esplits; eauto.
        }
        { destruct rs; ss. destruct rs; ss. des_ifs. hexploit H4; eauto. i. des.
          rewrite <- H5. eexists ((_, (_, _, _, _))::(_, (_, _, _, _))::_).
          ss. esplits; eauto. rewrite H6. eapply perm_swap.
        }
        { hexploit H4; eauto. i. des.
          hexploit H6; eauto. i. des. esplits; eauto. etrans; eauto.
        }
      }
      des. subst.
      iPoseProof (duty_list_permutation with "DUTY") as "DUTY"; [eauto|].
      iExists _, _. iFrame. eauto.
    Qed.

    Lemma duty_list_white_list i rs q
      :
      (duty_list i rs q)
        -∗
        □ (fold_right (fun '(r, (k, c, q, x)) P =>
                         (Region.white r (i, k, c, q, x)) ** P) True%I rs).
    Proof.
      revert q. induction rs.
      { i. iIntros. iModIntro. ss. }
      i. iIntros "DUTY". destruct a as [? [[[? ?] ?] ?]].
      iPoseProof (duty_list_unfold with "DUTY") as "[[# WHITE OWN] DUTY]".
      iPoseProof (IHrs with "DUTY") as "# WHITES". iClear "OWN DUTY".
      iModIntro. ss. iFrame. iSplit; auto.
    Qed.

    Lemma duty_list_whites i rs q
      :
      (duty_list i rs q)
        -∗
        □ (∀ r k c q x (IN: List.In (r, (k, c, q, x)) rs),
              Region.white r (i, k, c, q, x)).
    Proof.
      iIntros "H".
      iPoseProof (duty_list_white_list with "H") as "# WHITES".
      iClear "H". iModIntro. iStopProof. induction rs.
      { iIntros "# WHITES" (? ? ? ? ? ?). ss. }
      iIntros "# WHITES" (? ? ? ? ? ?). ss.
      destruct a as [? [[[? ?] ?] ?]]. iPoseProof "WHITES" as "[WHITE WHITES0]".
      des; clarify. iApply IHrs; auto.
    Qed.

    Lemma duty_correl i l k c
          (IN: List.In (k, c) l)
      :
      (duty i l)
        -∗
        (correl i k c).
    Proof.
      iIntros "[% [% [[BLACK DUTY] %]]]".
      subst. eapply in_map_iff in IN. des. des_ifs.
      iPoseProof (duty_list_whites with "DUTY") as "# WHITES".
      iExists _, _, _. iApply "WHITES". iPureIntro. eauto.
    Qed.

    Lemma duty_done i l k c
      :
      (duty i ((k, c)::l))
        -∗
        (shot k)
        -∗
        #=(arrows_sat)=> (duty i l).
    Proof.
      iIntros "[% [% [[BLACK DUTY] %]]] SHOT".
      destruct rs; ss. des_ifs.
      iPoseProof (duty_list_unfold with "DUTY") as "[[WHITE OWN] DUTY]".
      iPoseProof (Region.update with "WHITE [SHOT OWN]") as "> BLACKF".
      { iIntros "[[DONE _]|[% [BLACK WHITE]]]".
        { iCombine "OWN DONE" as "FALSE".
          rewrite FiniteMap.singleton_add. iOwnWf "FALSE".
          rewrite FiniteMap.singleton_wf in H3.
          apply OneShot.pending_not_shot in H3. ss.
        }
        iPoseProof (OwnM_Upd with "OWN") as "> OWN".
        { apply FiniteMap.singleton_updatable. apply OneShot.pending_shot. }
        iModIntro. iSplitR "BLACK".
        { iLeft. iFrame. }
        { instantiate (1:=FairRA.black_ex i q0).
          iExists _. iApply "BLACK".
        }
      }
      iModIntro. iExists _, _. iSplit; [|auto].
      iSplitR "DUTY"; [|eauto]. iApply (FairRA.black_ex_sum with "BLACK BLACKF").
    Qed.

    Lemma duty_alloc k c i l
      :
      (duty i l)
        -∗
        (white k (Jacobsthal.mult c Ord.omega))
        -∗
        #=(arrows_sat)=> (duty i ((k, c)::l)).
    Proof.
      iIntros "[% [% [[BLACK DUTY] %]]] SHOT".
      iPoseProof (FairRA.black_ex_split with "[BLACK]") as "[BLACK0 [% BLACK1]]".
      { rewrite Qp_div_2. iFrame. }
      iPoseProof (@OwnM_unit (@FiniteMap.t (OneShot.t unit))) as "H".
      iPoseProof (OwnM_Upd_set with "H") as "> [% [% OWN]]".
      { eapply FiniteMap.singleton_alloc. eapply OneShot.pending_wf. }
      ss. des. subst.
      iPoseProof (white_mon with "SHOT") as "> SHOT".
      { eapply Jacobsthal.le_mult_r.
        eapply Ord.lt_le. apply Ord.omega_upperbound.
      }
      iPoseProof (Region.alloc with "[SHOT BLACK1]") as "> [% WHITE]".
      { instantiate (1:=(i, k, c, (q / 2)%Qp, k0)). iRight.
        iExists _. iFrame.
      }
      { iModIntro. iExists _, _. iSplit.
        { iSplitL "BLACK0"; [eauto|].
          iApply (duty_list_fold with "[DUTY] WHITE OWN").
          rewrite Qp_div_2. eauto.
        }
        iPureIntro. ss.
      }
    Qed.

    Definition tax (l: list (nat * Ord.t)): iProp :=
      fold_right (fun '(k, c) P => white k (Jacobsthal.mult c Ord.omega) ** P) True%I l.

    Lemma duty_list_nodup i rs q
      :
      (duty_list i rs q)
        -∗
        #=(arrows_sat)=> ((duty_list i rs q) ** ⌜List.NoDup (map fst rs)⌝).
    Proof.
      revert q. induction rs.
      { i. iIntros "H". iModIntro. iSplit; ss. iPureIntro. econs; ss. }
      i. destruct a as [? [[[? ?] ?] ?]].
      ss. iIntros "DUTY".
      iPoseProof (duty_list_unfold with "DUTY") as "[[# WHITE OWN] DUTY]".
      iPoseProof (IHrs with "DUTY") as "> [DUTY %]".
      iPoseProof (duty_list_whites with "DUTY") as "# WHITES".
      iIntros "H".
      iAssert (⌜forall r k c q x (IN: List.In (r, (k, c, q, x)) rs), n <> r⌝)%I as "%".
      { iIntros (? ? ? ? ? IN ?). subst.
        iPoseProof "H" as "[% [H _]]".
        iPoseProof (Region.white_agree with "H WHITE []") as "%".
        { iApply "WHITES". iPureIntro. eauto. }
        clarify. iPoseProof ("WHITES" $! _ _ _ _ _ IN) as "# WHITE1".
        iAssert (OwnM (FiniteMap.singleton a3 (OneShot.pending unit))) with "[DUTY]" as "OWN1".
        { apply in_split in IN. des. subst.
          iClear "WHITE WHITES WHITE1". clear IHrs H3.
          iStopProof. generalize (q + a2)%Qp. induction l1; ss.
          { i. iIntros "H". iPoseProof (duty_list_unfold with "H") as "[[_ OWN] _]". auto.
          }
          { i. iIntros "H". destruct a4 as [? [[[? ?] ?] ?]].
            iPoseProof (duty_list_unfold with "H") as "[_ H]". iApply (IHl1 with "H").
          }
        }
        iCombine "OWN OWN1" as "OWN". iOwnWf "OWN".
        rewrite FiniteMap.singleton_add in H4.
        rewrite FiniteMap.singleton_wf in H4.
        apply OneShot.pending_unique in H4. ss.
      }
      iSplitL "H".
      { eauto. }
      iModIntro. iSplit.
      { iApply (duty_list_fold with "DUTY"); auto. }
      iPureIntro. econs; ss. ii. eapply in_map_iff in H5.
      des. destruct x as [? [[[? ?] ?] ?]]. ss. subst. eapply H4; eauto.
    Qed.

    Lemma duty_update n i l
      :
      (duty i l)
        -∗
        (tax l)
        -∗
        #=(arrows_sat)=> (duty i l ** FairRA.white i n).
    Proof.
      iIntros "[% [% [[BLACK DUTY] %]]] TAX". subst.
      iPoseProof (duty_list_nodup with "DUTY") as "> [DUTY %]".
      iPoseProof (duty_list_whites with "DUTY") as "# WHITES".
      iApply (Region.updates with "[]").
      { instantiate (1:=List.map (fun '(r, (k, c, q, x)) => (r, (i, k, c, q, x))) rs).
        rewrite map_map. erewrite map_ext; [eauto|]. i. des_ifs.
      }
      { iIntros. apply in_map_iff in IN. des. des_ifs.
        iApply "WHITES". auto.
      }
      iIntros "SAT".
      iAssert (duty_list i rs q ** FairRA.black_ex i 1%Qp) with "[DUTY BLACK SAT]" as "[DUTY BLACK]".
      { iClear "WHITES". iStopProof. clear H3. revert q. induction rs.
        { ss. i. iIntros "[[DUTY %] [BLACK _]]". ss. subst. iFrame. auto. }
        i. destruct a as [? [[[? ?] ?] ?]].
        iIntros "[DUTY [BLACK SAT]]". ss.
        iPoseProof (duty_list_unfold with "DUTY") as "[[WHITE OWN] DUTY]".
        iDestruct "SAT" as "[[[SHOT _]|[% [BLACK1 SAT]]] SATS]".
        { iExFalso. iCombine "OWN SHOT" as "OWN". iOwnWf "OWN".
          rewrite FiniteMap.singleton_add in H3.
          rewrite FiniteMap.singleton_wf in H3.
          apply OneShot.pending_not_shot in H3. ss.
        }
        iPoseProof (IHrs with "[DUTY BLACK BLACK1 SATS]") as "[DUTY BLACK]".
        { iSplitL "DUTY"; [eauto|]. iSplitL "BLACK BLACK1"; [|auto].
          iApply (FairRA.black_ex_sum with "BLACK"). iExists _. iFrame.
        }
        iSplitR "BLACK"; [|auto]. iApply (duty_list_fold with "DUTY WHITE OWN").
      }
      iPoseProof (FairRA.success_ex_update with "BLACK") as "> [[% BLACK] WHITE]".
      iFrame.
      iAssert (⌜(fold_right (fun '(r, (k, c, q0, x)) q1 => (q0 + q1)%Qp) q rs = 1%Qp)⌝)%I as "%".
      { iPoseProof "DUTY" as "[DUTY %]". auto. }
      iAssert (#=> (Region.sat_list
                      arrow
                      (map snd (map (fun '(r, (k, c, q0, x)) => (r, (i, k, c, q0, x))) rs)) ** FairRA.black i a q)) with "[TAX BLACK]" as "> [REGION BLACK]".
      2:{ iModIntro. iFrame. iExists _, _. iFrame. iSplit; eauto. iExists _. iFrame. }
      rewrite <- H4. iStopProof. clear H3 H4. revert q. induction rs.
      { i. iIntros "[# WHITES [TAX BLACK]]". iModIntro. ss. iFrame. }
      { i. iIntros "[# WHITES [TAX BLACK]]". ss.
        destruct a0 as [? [[[? ?] ?] ?]]. ss.
        iPoseProof "TAX" as "[WHITE TAX]".
        replace (q0 + foldr (fun '(_, (_, _, q1, _)) q2 => (q1 + q2)%Qp) q rs)%Qp with (q + foldr (fun '(_, (_, _, q1, _)) q2 => (q1 + q2)%Qp) q0 rs)%Qp; cycle 1.
        { clear IHrs. revert q q0. induction rs; ss; i.
          { apply Qp_add_comm. }
          { destruct a0 as [? [[[? ?] ?] ?]].
            rewrite (IHrs q1 q0). rewrite (IHrs q1 q).
            rewrite Qp_add_assoc. rewrite Qp_add_assoc.
            f_equal. apply Qp_add_comm.
          }
        }
        iPoseProof (FairRA.black_split with "BLACK") as "[BLACK0 BLACK1]".
        iPoseProof (IHrs with "[TAX BLACK1]") as "> [REGION BLACK1]".
        { iSplit.
          { iClear "TAX BLACK1". iModIntro. iIntros.
            iApply "WHITES". eauto.
          }
          iFrame.
        }
        iFrame. iRight. iExists _. iFrame. iApply (white_mon with "WHITE").
        apply Jacobsthal.le_mult_r. eapply Ord.lt_le. eapply Ord.omega_upperbound.
      }
    Qed.
  End ARROW.
End ObligationRA.