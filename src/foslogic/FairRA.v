From sflib Require Import sflib.
From Fairness Require Import PCM IPropFOS IPMFOS MonotonePCM WFLibLarge Mod Optics.
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
            | excl e f q => le f e /\ (Qp.le q 1)%Qp
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
        { rewrite Qp.add_comm. auto. }
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
        { rewrite Qp.add_assoc. auto. }
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
        { etrans; [|eauto]. eapply Qp.le_add_l. }
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
      ((white a0: @URA.car t) ⋅ white a1)
      =
        white (OrderedCM.add a0 a1).
    Proof.
      ur. unfold white. f_equal.
      rewrite from_monoid_add. auto.
    Qed.

    Lemma black_sum `{OrderedCM.t A} (a0 a1: A) (q0 q1: Qp)
      :
      (black a0 q0: @URA.car t) ⋅ black a1 q1
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
      URA.updatable (white a1: @URA.car t) (white a0).
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
      URA.updatable (black a0 q: @URA.car t) (black a1 q).
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
        (black a0 1: @URA.car t)
        ((black (OrderedCM.add a0 a1) 1: @URA.car t) ⋅ white a1).
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
      { des. exfalso. eapply Qp.not_add_le_l. eauto. }
    Qed.

    Lemma decr_update `{OrderedCM.t A} a0 a1 q
      :
      URA.updatable_set
        ((black a0 q: @URA.car t) ⋅ white a1)
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


(* From Paco Require Import paco. *)

(* Section INFSUM. *)
(*   Variable M: URA.t. *)

(*   Variant _infsum (infsum: forall (X: Type) (P: X -> M -> Prop) (r: M), Prop) *)
(*           (X: Type) (P: X -> M -> Prop) (r: M): Prop := *)
(*     | infsum_intro *)
(*         (INF: forall Y (Q: Y -> M -> Prop) x *)
(*                      (f: Y -> X) *)
(*                      (PRED: forall y r, P (f y) r -> Q y r) *)
(*                      (INJ: forall y0 y1, f y0 = f y1 -> y0 = y1) *)
(*                      (MINUS: forall y, f y <> x), *)
(*           exists r0 r1, *)
(*             r = r0 ⋅ r1 /\ P x r0 /\ infsum Y Q r1) *)
(*   . *)

(*   Lemma infsum_monotone: monotone3 _infsum. *)
(*   Proof. *)
(*     ii. inv IN. econs; eauto. *)
(*     i. hexploit INF; eauto. i. des. esplits; eauto. *)
(*   Qed. *)
(*   Hint Resolve infsum_monotone: paco. *)
(*   Hint Resolve cpn3_wcompat: paco. *)

(*   Definition infsum := paco3 _infsum bot3. *)

(*   Lemma infsum_void *)
(*         (X: Type) (EMPTY: forall (x: X), False) *)
(*         (P: X -> M -> Prop) *)
(*         (r: M) *)
(*     : *)
(*     infsum P r. *)
(*   Proof. *)
(*     pfold. econs. i. exfalso. eapply EMPTY; eauto. *)
(*   Qed. *)

(*   Lemma singleton_to_infsum (r: M) (P: M -> Prop) *)
(*         (SAT: P r) *)
(*     : *)
(*     infsum (fun _: unit => P) r. *)
(*   Proof. *)
(*     pfold. econs. i. *)
(*     exists r, URA.unit. rewrite URA.unit_id. splits; auto. *)
(*     left. eapply infsum_void; eauto. *)
(*     i. eapply (MINUS x0). destruct (f x0), x; ss. *)
(*   Qed. *)

(*   Variant infsum_extendC (R: forall (X: Type) (P: X -> M -> Prop) (r: M), Prop) *)
(*           X (P: X -> M -> Prop) (r: M): Prop := *)
(*     | infsum_extendC_intro *)
(*         r0 r1 *)
(*         (SAT: R X P r0) *)
(*         (EQ: r = r0 ⋅ r1) *)
(*   . *)

(*   Lemma infsum_extendC_spec *)
(*     : *)
(*     infsum_extendC <4= gupaco3 _infsum (cpn3 _infsum). *)
(*   Proof. *)
(*     eapply wrespect3_uclo; eauto with paco. econs. *)
(*     { ii. inv IN. econs; eauto. } *)
(*     i. inv PR. eapply GF in SAT. inv SAT. *)
(*     econs. i. hexploit INF; eauto. i. des. subst. *)
(*     exists r2, (r3 ⋅ r1). splits; auto. *)
(*     { r_solve. } *)
(*     eapply rclo3_clo_base. econs; eauto. *)
(*   Qed. *)

(*   Variant infsum_monoC (R: forall (X: Type) (P: X -> M -> Prop) (r: M), Prop) *)
(*           Y (Q: Y -> M -> Prop) (r: M): Prop := *)
(*     | infsum_monoC_intro *)
(*         X (f: Y -> X) (P: X -> M -> Prop) *)
(*         (PRED: forall y r, P (f y) r -> Q y r) *)
(*         (INJ: forall y0 y1, f y0 = f y1 -> y0 = y1) *)
(*         (SAT: R X P r) *)
(*   . *)

(*   Lemma infsum_monoC_spec *)
(*     : *)
(*     infsum_monoC <4= gupaco3 _infsum (cpn3 _infsum). *)
(*   Proof. *)
(*     eapply wrespect3_uclo; eauto with paco. econs. *)
(*     { ii. inv IN. econs; eauto. } *)
(*     i. inv PR. eapply GF in SAT. inv SAT. *)
(*     econs. i. *)
(*     hexploit (INF Y Q (f x) (fun x => f (f0 x))); auto. *)
(*     { ii. eapply INJ in H. eapply MINUS; eauto. } *)
(*     i. des. exists r0, r1. splits; auto. *)
(*     eapply rclo3_base. auto. *)
(*   Qed. *)

(*   Lemma infsum_unfold *)
(*         X Y (Q: Y -> M -> Prop) (f: Y -> X) *)
(*         (P: X -> M -> Prop) (r: M) *)
(*         (INF: infsum P r) *)
(*         (PRED: forall y r, P (f y) r -> Q y r) *)
(*         (INJ: forall y0 y1, f y0 = f y1 -> y0 = y1) *)
(*         x *)
(*         (MINUS: forall y, f y <> x) *)
(*     : *)
(*     exists r0 r1, *)
(*       r = r0 ⋅ r1 /\ P x r0 /\ infsum Q r1. *)
(*   Proof. *)
(*     punfold INF. inv INF. hexploit INF0; eauto. *)
(*     i. des. subst. pclearbot. esplits; eauto. *)
(*   Qed. *)

(*   Let partial_fun_to_total X Y (f: X -> option Y) *)
(*       (TOTAL: forall x, f x <> None) *)
(*     : *)
(*     X -> Y. *)
(*   Proof. *)
(*     intros x. destruct (f x) eqn:EQ. *)
(*     { exact y. } *)
(*     { destruct (TOTAL _ EQ). } *)
(*   Defined. *)

(*   Lemma partial_fun_to_total_eq *)
(*         X Y (f: X -> option Y) *)
(*         (TOTAL: forall x, f x <> None) *)
(*         x y *)
(*         (EQ: f x = Some y) *)
(*     : *)
(*     partial_fun_to_total f TOTAL x = y. *)
(*   Proof. *)
(*     compute. *)
(*     replace (fun (EQ0 : f x = None) => match TOTAL x EQ0 return Y with *)
(*                                        end) with *)
(*       (fun (EQ0 : f x = None) => y). *)
(*     2:{ extensionality a. clarify. } *)
(*     rewrite EQ. auto. *)
(*   Qed. *)

(*   Lemma infsum_fold_aux *)
(*     : *)
(*     forall *)
(*       (X: Type) (P0: X -> M -> Prop) (r0: M) *)
(*       (INF: infsum P0 r0) *)
(*       (P1: M -> Prop) (r1: M) *)
(*       (SAT: P1 r1), *)
(*       infsum (option_rect _ P0 P1) (r0 ⋅ r1). *)
(*   Proof. *)
(*     ginit. gcofix CIH. i. gstep. econs. i. *)
(*     destruct x. *)
(*     { assert (exists (f': sig (fun y => f y <> None) -> X), *)
(*                forall y, f (proj1_sig y) = Some (f' y)). *)
(*       { eapply (choice (fun (y: sig (fun y => f y <> None)) x => f (proj1_sig y) = Some x)). *)
(*         i. destruct x0. ss. destruct (f x0); ss. eauto. *)
(*       } *)
(*       des. hexploit (@infsum_unfold X _ (fun y => Q (proj1_sig y)) f'). *)
(*       { eauto. } *)
(*       { i. eapply PRED. rewrite H. ss. } *)
(*       { i. assert (proj1_sig y0 = proj1_sig y1). *)
(*         { eapply INJ. rewrite ! H. f_equal. auto. } *)
(*         { destruct y0, y1. ss. subst. f_equal. apply proof_irrelevance. } *)
(*       } *)
(*       { instantiate (1:=x). ii. eapply MINUS. rewrite H. rewrite H0. auto. } *)
(*       i. des. subst. exists r2, (r3 ⋅ r1). splits. *)
(*       { r_solve. } *)
(*       { ss. } *)
(*       assert (exists (wrap: Y -> option (sig (fun y => f y <> None))), *)
(*                forall y, *)
(*                  match (wrap y) with *)
(*                  | None => f y = None *)
(*                  | Some (exist _ y' _) => y = y' /\ exists x, f y = Some x *)
(*                  end). *)
(*       { eapply (choice (fun y (y': option (sig (fun y => f y <> None))) => *)
(*                           match y' with *)
(*                           | Some (exist _ y' _) => y = y' /\ exists x, f y = Some x *)
(*                           | None => f y = None *)
(*                           end)). *)
(*         i. destruct (f x0) eqn:EQ. *)
(*         { refine (ex_intro _ (Some (exist _ x0 _)) _). *)
(*           { ii. clarify. } *)
(*           { splits; eauto. } *)
(*         } *)
(*         { exists None. auto. } *)
(*       } *)
(*       des. guclo infsum_monoC_spec. econs. *)
(*       3:{ gbase. eapply CIH; eauto. } *)
(*       { instantiate (1:=wrap). i. specialize (H0 y). des_ifs; ss. *)
(*         { des. subst. auto. } *)
(*         { eapply PRED. rewrite H0. ss. } *)
(*       } *)
(*       { i. eapply INJ. pose proof (H0 y0). pose proof (H0 y1). des_ifs. *)
(*         { des. subst. auto. } *)
(*         { rewrite H4. rewrite H5. auto. } *)
(*       } *)
(*     } *)
(*     { exists r1, r0. splits. *)
(*       { eapply URA.add_comm. } *)
(*       { ss. } *)
(*       { guclo infsum_monoC_spec. *)
(*         econs. *)
(*         3:{ gfinal. right. eapply paco3_mon; eauto. ss. } *)
(*         { instantiate (1:=partial_fun_to_total f MINUS). *)
(*           intros y. destruct (f y) eqn:EQ. *)
(*           2:{ destruct (MINUS _ EQ). } *)
(*           i. hexploit partial_fun_to_total_eq; eauto. i. *)
(*           erewrite H0 in H. eapply PRED. rewrite EQ. ss. *)
(*         } *)
(*         { i. destruct (f y0) eqn:EQ0. *)
(*           2:{ destruct (MINUS _ EQ0). } *)
(*           destruct (f y1) eqn:EQ1. *)
(*           2:{ destruct (MINUS _ EQ1). } *)
(*           eapply INJ; eauto. *)
(*           erewrite partial_fun_to_total_eq in H; eauto. *)
(*           erewrite partial_fun_to_total_eq in H; eauto. *)
(*           rewrite EQ0. rewrite EQ1. subst. auto. *)
(*         } *)
(*       } *)
(*     } *)
(*   Qed. *)

(*   Lemma infsum_fold *)
(*         (X: Type) (P0: X -> M -> Prop) (r0: M) *)
(*         (INF: infsum P0 r0) *)
(*         (P1: M -> Prop) (r1: M) *)
(*         (SAT: P1 r1) *)
(*         Y (Q: Y -> M -> Prop) *)
(*         (f: Y -> option X) *)
(*         (PRED0: forall y x r (EQ: f y = Some x), P0 x r -> Q y r) *)
(*         (PRED1: forall y r (EQ: f y = None), P1 r -> Q y r) *)
(*         (INJ: forall y0 y1, f y0 = f y1 -> y0 = y1) *)
(*     : *)
(*     infsum Q (r0 ⋅ r1). *)
(*   Proof. *)
(*     ginit. guclo infsum_monoC_spec. econs. *)
(*     3:{ gfinal. right. eapply infsum_fold_aux; eauto. } *)
(*     { instantiate (1:=f). i. destruct (f y) eqn:EQ; ss; eauto. } *)
(*     { auto. } *)
(*   Qed. *)

(*   Lemma infsum_to_singleton *)
(*         (X: Type) (P: X -> M -> Prop) *)
(*         (r: M) *)
(*         (INF: infsum P r) *)
(*         x *)
(*     : *)
(*     exists r0 r1, r = r0 ⋅ r1 /\ P x r0. *)
(*   Proof. *)
(*     punfold INF. inv INF. *)
(*     hexploit (INF0 (sig (fun y => y <> x)) (fun y => P (proj1_sig y)) x proj1_sig). *)
(*     { i. auto. } *)
(*     { i. destruct y0, y1. ss. subst. f_equal. eapply proof_irrelevance. } *)
(*     { i. eapply (proj2_sig y). } *)
(*     i. des. esplits; eauto. *)
(*   Qed. *)
(* End INFSUM. *)
(* #[export] Hint Resolve infsum_monotone: paco. *)
(* #[export] Hint Resolve cpn3_wcompat: paco. *)

(* Program Definition Infsum {Σ: GRA.t} (X: Type) (P: X -> iProp): iProp := *)
(*   iProp_intro (infsum Σ P) _. *)
(* Next Obligation. *)
(* Proof. *)
(*   rr in LE. des. subst. *)
(*   ginit. guclo infsum_extendC_spec. econs; eauto. gfinal. right. auto. *)
(* Qed. *)

(* Lemma pointwise_own_infsum A (M: URA.t) *)
(*       {Σ: GRA.t} `{ING: @GRA.inG (A ==> M)%ra Σ} *)
(*       (f: (A ==> M)%ra) *)
(*   : *)
(*   (OwnM f) *)
(*     -∗ *)
(*     Infsum (fun a => OwnM (maps_to_res a (f a))). *)
(* Proof. *)
(*   uipropall. i. rr in H. uipropall. rr in H. des. subst. *)
(*   ginit. guclo infsum_extendC_spec. econs; eauto. *)
(*   clear WF ctx. revert f. gcofix CIH. i. gstep. econs. i. *)
(*   exists (GRA.embed (maps_to_res x (f x))), (GRA.embed (map_update f x URA.unit: (A ==> M)%ra)). *)
(*   splits. *)
(*   { rewrite GRA.embed_add. f_equal. *)
(*     extensionality a. ur. *)
(*     unfold maps_to_res, map_update. des_ifs. *)
(*     { r_solve. } *)
(*     { r_solve. } *)
(*   } *)
(*   { rr. uipropall. reflexivity. } *)
(*   guclo infsum_monoC_spec. econs. *)
(*   3:{ gbase. eapply CIH. } *)
(*   { instantiate (1:=f0). i. ss. *)
(*     unfold map_update in H. des_ifs. *)
(*     { exfalso. eapply MINUS; eauto. } *)
(*     { eapply PRED; eauto. } *)
(*   } *)
(*   { auto. } *)
(* Qed. *)

Arguments Fuel.t A {_}.
From Fairness Require Import FairBeh.

Module FairRA.
  Section FAIR.
    Variable (S: Type).
    Variable (A: Type).
    Context `{L: OrderedCM.t A}.

    Definition t: URA.t :=
      (S ==> @Fuel.t A _)%ra.

    Context `{ING: @GRA.inG t Σ}.

    Section PRISM.
    Variable (Id: Type).
    Variable (p: Prism.t S Id).

    Definition black (i: Id) (a: A) (q: Qp): iProp :=
      maps_to (Prism.review p i) (Fuel.black a q: Fuel.t A).

    Definition black_ex (i: Id) (q: Qp): iProp :=
      ∃ a, black i a q.

    Definition white (i: Id) (a: A): iProp :=
      maps_to (Prism.review p i) (Fuel.white a: Fuel.t A).

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

    Lemma success_update_strong a1 i a0
      :
      (black i a0 1%Qp)
        -∗
        (#=> ((black i (OrderedCM.add a0 a1) 1%Qp) ** (white i a1))).
    Proof.
      iIntros "H".
      iPoseProof (OwnM_Upd with "H") as "> H".
      { eapply maps_to_updatable.
        eapply Fuel.success_update. }
      rewrite <- maps_to_res_add. iDestruct "H" as "[H0 H1]".
      iModIntro. iFrame.
    Qed.

    Lemma success_update a1 i a0
      :
      (black i a0 1%Qp)
        -∗
        (#=> ((∃ a, black i a 1%Qp) ** (white i a1))).
    Proof.
      iIntros "H". iPoseProof (success_update_strong with "H") as "> [H1 H2]".
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
                    match @Prism.preview _ _ p i with
                    | Some i =>
                        match (f i) with
                        | Some a => Fuel.black a 1
                        | None => ε
                        end
                    | None => ε
                    end): (S ==> Fuel.t A)%ra)).

    Lemma blacks_impl (s0 s1: Id -> Prop)
               (IMPL: forall i (IN: s0 i), s1 i)
      :
      (blacks s1)
        -∗
        (blacks s0).
    Proof.
      iIntros "[% [% BLACKS]]".
      iExists (fun i => if (excluded_middle_informative (s0 i)) then f i else None).
      iSplit.
      { iPureIntro. i. des_ifs.
        { split; auto. i. apply H. auto. }
        { split; i; ss. inv H0. ss. }
      }
      iApply (OwnM_extends with "BLACKS"). apply pointwise_extends.
      i. des_ifs; try by reflexivity. eexists _. rewrite URA.unit_idl. ss.
    Qed.

    Lemma blacks_empty s
               (EMPTY: forall i, ~ s i)
      :
      ⊢ blacks s.
    Proof.
      iIntros. iExists (fun _ => None). iSplit; ss.
      { iPureIntro. i. split; i; ss.
        { inv H. ss. }
        { exfalso. eapply EMPTY; eauto. }
      }
      iApply (OwnM_extends with "[]").
      2:{ iApply (@OwnM_unit (S ==> Fuel.t A)%ra). }
      apply pointwise_extends.
      i. eexists. des_ifs.
      { rewrite URA.unit_idl. eauto. }
      { rewrite URA.unit_idl. eauto. }
    Qed.

    Lemma blacks_fold (s0 s1: Id -> Prop) i
               (IMPL: forall j (IN: s0 j), s1 j \/ j = i)
      :
      (blacks s1 ** black_ex i 1)
        -∗
        (blacks s0).
    Proof.
      iIntros "[[% [% BLACKS]] [% BLACK]]".
      iCombine "BLACKS BLACK" as "BLACKS".
      iOwnWf "BLACKS".
      iExists (fun j => if (excluded_middle_informative (s0 j))
                        then if (excluded_middle_informative (j = i)) then Some a else f j
                        else None).
      iSplit.
      { iPureIntro. i. des_ifs.
        { split; auto. i. hexploit IMPL; eauto. i. des; clarify. rewrite H. ss. }
        { split; i; ss. inv H1. ss. }
      }
      iApply (OwnM_extends with "BLACKS"). apply pointwise_extends.
      i. erewrite ! (@unfold_pointwise_add S (Fuel.t A)). unfold maps_to_res.
      des_ifs; ss; repeat rewrite URA.unit_id; repeat rewrite URA.unit_idl; ss; try by reflexivity.
      { eexists. apply URA.add_comm. }
      { rewrite Prism.preview_review in *. clarify. }
      { eapply Prism.review_preview in Heq. clarify. }
      { eapply Prism.review_preview in Heq. clarify. }
      { rewrite Prism.preview_review in *. clarify.
        eexists. rewrite URA.unit_idl. ss. }
      { eapply Prism.review_preview in Heq. clarify.
        eexists. rewrite URA.unit_idl. ss. }
      { eexists. rewrite URA.unit_idl. ss. }
      { eexists. rewrite URA.unit_idl. ss. }
      { eexists. rewrite URA.unit_idl. ss. }
    Qed.

    Lemma blacks_unfold (s0 s1: Id -> Prop) i
          (IMPL: forall j (IN: s0 j \/ j = i), s1 j)
          (NIN: ~ s0 i)
      :
      (blacks s1)
        -∗
        (blacks s0 ** black_ex i 1).
    Proof.
      iIntros "[% [% BLACKS]]".
      hexploit (proj2 (H i)).
      { apply IMPL. auto. }
      i. inv H0.
      set (f1 :=fun i => if (excluded_middle_informative (s0 i)) then f i else None).
      iPoseProof (OwnM_extends with "BLACKS") as "[BLACKS0 BLACKS1]".
      { instantiate (1:=maps_to_res (Prism.review p i) (Fuel.black x 1: Fuel.t A): (S ==> Fuel.t A)%ra).
        instantiate (1:=(fun i =>
                           match Prism.preview p i with
                           | Some i =>
                               match (f1 i) with
                               | Some a => Fuel.black a 1
                               | None => ε
                               end
                           | None => ε
                           end)).
        erewrite ! (@unfold_pointwise_add S (Fuel.t A)). unfold maps_to_res, f1.
        apply pointwise_extends. i.
        des_ifs; ss; repeat rewrite URA.unit_id; repeat rewrite URA.unit_idl; ss; try by reflexivity.
        { rewrite Prism.preview_review in *. clarify. }
        { rewrite Prism.preview_review in *. clarify. reflexivity. }
        { rewrite Prism.preview_review in *. clarify. }
        { rewrite Prism.preview_review in *. clarify. }
        { eexists. rewrite URA.unit_idl. ss. }
        { rewrite Prism.preview_review in *. clarify. }
      }
      iSplitL "BLACKS0".
      { iExists f1. iSplit; auto. iPureIntro. i.
        unfold f1. des_ifs.
        { rewrite H. split; i; auto. }
        { split; ss. i. inv H0. ss. }
      }
      { iExists _. eauto. }
    Qed.

    Definition blacks_combine (s0 s1: Id -> Prop)
      :
      (blacks s0 ** blacks s1)
        -∗
        (blacks (fun i => s0 i \/ s1 i)).
    Proof.
      iIntros "[[% [% BLACKS0]] [% [% BLACKS1]]]".
      iCombine "BLACKS0 BLACKS1" as "BLACKS".
      iExists (fun i => match f i with
                        | Some a => Some a
                        | _ => f0 i
                        end).
      iSplit.
      { iPureIntro. i. rewrite <- H. rewrite <- H0. des_ifs.
        { split; auto. }
        { split; auto. i. des; ss. inv H1. ss. }
      }
      iApply (OwnM_extends with "BLACKS"). apply pointwise_extends.
      i. erewrite ! (@unfold_pointwise_add S (Fuel.t A)).
      des_ifs; ss; repeat rewrite URA.unit_id; repeat rewrite URA.unit_idl; ss; try by reflexivity.
      { eexists. eauto. }
    Qed.

    Definition blacks_split (s0 s1: Id -> Prop)
               (DISJOINT: forall i (IN0: s0 i) (IN1: s1 i), False)
      :
      (blacks (fun i => s0 i \/ s1 i))
        -∗
        (blacks s0 ** blacks s1).
    Proof.
      iIntros "[% [% BLACKS]]".
      iPoseProof (OwnM_extends with "BLACKS") as "[BLACKS0 BLACKS1]"; cycle 1.
      { iSplitL "BLACKS0".
        { iExists (fun i => if (excluded_middle_informative (s0 i)) then f i else None).
          iSplit; [|iExact "BLACKS0"].
          iPureIntro. i. des_ifs.
          { rewrite H. split; auto. }
          { split; ss. i. inv H0. ss. }
        }
        { iExists (fun i => if (excluded_middle_informative (s1 i)) then f i else None).
          iSplit; [|iExact "BLACKS1"].
          iPureIntro. i. des_ifs.
          { rewrite H. split; auto. }
          { split; ss. i. inv H0. ss. }
        }
      }
      { apply pointwise_extends.
        i. erewrite ! (@unfold_pointwise_add S (Fuel.t A)).
        des_ifs; ss; repeat rewrite URA.unit_id; repeat rewrite URA.unit_idl; ss; try by reflexivity.
        { exfalso. eapply DISJOINT; eauto. }
        { eexists. rewrite URA.unit_idl. eauto. }
      }
    Qed.

    Definition whites (s: Id -> Prop) (u: A): iProp :=
      (OwnM ((fun i =>
                match @Prism.preview _ _ p i with
                | Some i =>
                    if (excluded_middle_informative (s i))
                    then Fuel.white u
                    else ε
                | None => ε
                end): (S ==> Fuel.t A)%ra)).

    Lemma whites_impl (s0 s1: Id -> Prop) u
               (IMPL: forall i (IN: s0 i), s1 i)
      :
      (whites s1 u)
        -∗
        (whites s0 u).
    Proof.
      iIntros "WHITES".
      iApply (OwnM_extends with "WHITES"). apply pointwise_extends.
      i. des_ifs; try by reflexivity.
      { exfalso. eauto. }
      { eexists _. rewrite URA.unit_idl. ss. }
    Qed.

    Lemma whites_empty s u
               (EMPTY: forall i, ~ s i)
      :
      ⊢ whites s u.
    Proof.
      iIntros. iApply (OwnM_extends with "[]").
      2:{ iApply (@OwnM_unit (S ==> Fuel.t A)%ra). }
      apply pointwise_extends. i. des_ifs.
      { exfalso. eapply EMPTY; eauto. }
      { eexists _. rewrite URA.unit_idl. eauto. }
      { eexists _. rewrite URA.unit_idl. eauto. }
    Qed.

    Lemma whites_fold (s0 s1: Id -> Prop) i u
               (IMPL: forall j (IN: s0 j), s1 j \/ j = i)
      :
      (whites s1 u ** white i u)
        -∗
        (whites s0 u).
    Proof.
      iIntros "[WHITES WHITE]".
      iCombine "WHITES WHITE" as "WHITES".
      iApply (OwnM_extends with "WHITES"). apply pointwise_extends.
      i. erewrite ! (@unfold_pointwise_add S (Fuel.t A)). unfold maps_to_res.
      des_ifs; ss; repeat rewrite URA.unit_id; repeat rewrite URA.unit_idl; ss; try by reflexivity.
      { eexists. apply URA.add_comm. }
      { eapply Prism.review_preview in Heq.
        hexploit IMPL; eauto. i. des; clarify. }
      { eexists. rewrite URA.unit_idl. ss. }
      { eexists. rewrite URA.unit_idl. ss. }
      { eexists. rewrite URA.unit_idl. ss. }
      { eexists. rewrite URA.unit_idl. ss. }
    Qed.

    Definition whites_unfold (s0 s1: Id -> Prop) i u
               (IMPL: forall j (IN: s0 j \/ j = i), s1 j)
               (NIN: ~ s0 i)
      :
      (whites s1 u)
        -∗
        (whites s0 u ** white i u).
    Proof.
      iIntros "WHITES".
      iPoseProof (OwnM_extends with "WHITES") as "[WHITES0 WHITES1]".
      { instantiate (1:=maps_to_res (Prism.review p i) (Fuel.white u: Fuel.t A): (S ==> Fuel.t A)%ra).
        instantiate (1:=(fun i =>
                           match Prism.preview p i with
                           | Some i =>
                               if (excluded_middle_informative (s0 i))
                               then Fuel.white u
                               else ε
                           | None => ε
                           end)).
        erewrite ! (@unfold_pointwise_add S (Fuel.t A)). unfold maps_to_res.
        apply pointwise_extends. i.
        des_ifs; ss; repeat rewrite URA.unit_id; repeat rewrite URA.unit_idl; ss; try by reflexivity.
        { rewrite Prism.preview_review in *. clarify. }
        { rewrite Prism.preview_review in *. clarify. }
        { eapply Prism.review_preview in Heq.
          exfalso. eapply n0. auto. }
        { rewrite Prism.preview_review in *. clarify.
          exfalso. eapply n0. auto. }
        { eexists. rewrite URA.unit_idl. ss. }
        { rewrite Prism.preview_review in *. clarify. }
      }
      iFrame.
    Qed.

    Definition whites_combine (s0 s1: Id -> Prop) u
      :
      (whites s0 u ** whites s1 u)
        -∗
        (whites (fun i => s0 i \/ s1 i) u).
    Proof.
      iIntros "[WHITES0 WHITES1]".
      iCombine "WHITES0 WHITES1" as "WHITES".
      iApply (OwnM_extends with "WHITES"). apply pointwise_extends.
      i. erewrite ! (@unfold_pointwise_add S (Fuel.t A)).
      des_ifs; ss; repeat rewrite URA.unit_id; repeat rewrite URA.unit_idl; ss; try by reflexivity.
      { eexists. eauto. }
      { des; ss. }
      { eexists. rewrite URA.unit_idl. ss. }
      { eexists. rewrite URA.unit_idl. ss. }
      { eexists. rewrite URA.unit_idl. ss. }
    Qed.

    Definition whites_split (s0 s1: Id -> Prop) u
               (DISJOINT: forall i (IN0: s0 i) (IN1: s1 i), False)
      :
      (whites (fun i => s0 i \/ s1 i) u)
        -∗
        (whites s0 u ** whites s1 u).
    Proof.
      iIntros "WHITES".
      iPoseProof (OwnM_extends with "WHITES") as "[WHITES0 WHITES1]".
      2:{ iSplitL "WHITES0"; [iExact "WHITES0"|iExact "WHITES1"]. }
      { apply pointwise_extends.
        i. erewrite ! (@unfold_pointwise_add S (Fuel.t A)).
        des_ifs; ss; repeat rewrite URA.unit_id; repeat rewrite URA.unit_idl; ss; try by reflexivity.
        { exfalso. eapply DISJOINT; eauto. }
        { exfalso. eapply n; eauto. }
        { exfalso. eapply n0; eauto. }
        { exfalso. eapply n0; eauto. }
        { des; ss. }
      }
    Qed.

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
      { rewrite Prism.preview_review in Heq. clarify. }
      { rewrite Prism.preview_review in Heq. clarify. }
      { eexists. rewrite URA.unit_idl. auto. }
      { eexists. rewrite URA.unit_idl. auto. }
      { eexists. rewrite URA.unit_idl. auto. }
    Qed.

    Lemma blacks_black (s: Id -> Prop) i
          (IN: s i)
      :
      (blacks s)
        -∗
        (black_ex i 1).
    Proof.
      iIntros "[% [% H]]".
      hexploit (proj2 (H i)); auto. i. destruct (f i) eqn:EQ.
      2:{ inv H0. ss. }
      iExists a. iApply (OwnM_extends with "H").
      unfold maps_to_res. eapply pointwise_extends.
      i. des_ifs; ss.
      { rewrite Prism.preview_review in Heq. clarify. reflexivity. }
      { rewrite Prism.preview_review in Heq. clarify. }
      { rewrite Prism.preview_review in Heq. clarify. }
      { eexists. rewrite URA.unit_idl. auto. }
      { eexists. rewrite URA.unit_idl. auto. }
      { eexists. rewrite URA.unit_idl. auto. }
    Qed.

    Lemma black_ex_list_blacks (l: list Id) (P: Id -> Prop)
          (ALL: forall i (IN: P i), List.In i l)
      :
      (list_prop_sum (fun i => black_ex i 1) l)
        -∗
        ((blacks P) ** ((blacks P) -* (list_prop_sum (fun i => black_ex i 1) l))).
    Proof.
      revert P ALL. induction l.
      { i. ss. iIntros. iSplitL.
        { iApply blacks_empty; eauto. }
        { iIntros. auto. }
      }
      i. ss. iIntros "[HD TL]".
      destruct (classic (P a)).
      { iPoseProof ((@IHl (fun i => a <> i /\ P i)) with "TL") as "[BLACKS K]".
        { i. des. hexploit ALL; eauto. i. des; ss. }
        iSplitL "HD BLACKS".
        { iApply blacks_fold.
          2:{ iFrame. }
          i. ss. destruct (classic (a = j)); auto.
        }
        iIntros "BLACKS".
        iPoseProof (blacks_unfold with "BLACKS") as "[BLACKS BLACK]"; cycle 2.
        { iFrame. iApply ("K" with "BLACKS"). }
        { i. ss. des; clarify. }
        { ii. des; ss. }
      }
      { iPoseProof ((@IHl P) with "TL") as "[BLACKS K]".
        { i. hexploit ALL; eauto. i. des; clarify. }
        iFrame. auto.
      }
    Qed.

    Lemma whites_white_list (l: list Id) (P: Id -> Prop) u
          (ALL: forall i (IN: List.In i l), P i)
          (NODUP: List.NoDup l)
      :
      (whites P u)
        -∗
        (list_prop_sum (fun i => white i u) l).
    Proof.
      revert P ALL NODUP. induction l.
      { i. ss. auto. }
      i. inv NODUP. iIntros "WHITES".
      iPoseProof (whites_unfold with "WHITES") as "[WHITES WHITE]"; cycle 2.
      { ss. iFrame. iApply (IHl with "WHITES"); auto.
        instantiate (1:= fun i => P i /\ i <> a).
        i. ss. split; auto. ii. clarify.
      }
      { i. ss. des; ss. clarify. eapply ALL; eauto. }
      { ii. des; ss. }
    Qed.

    Definition blacks_of (l: list Id): iProp :=
      list_prop_sum (fun i => black_ex i 1) l.

    Definition whites_of (l: list Id) (u: A): iProp :=
      list_prop_sum (fun i => white i u) l.

    End PRISM.

    Section PRISM.
    Variable (Id: Type).
    Variable (p: Prism.t S Id).

    Lemma whites_prism_id P o
      :
      (whites p P o)
        -∗
        (whites Prism.id (fun s => exists i, Prism.review p i = s /\ P i) o).
    Proof.
      iIntros "WHITES".
      iApply (OwnM_extends with "WHITES"). apply pointwise_extends.
      i. ss. des_ifs; try by reflexivity.
      { des; clarify. rewrite Prism.preview_review in *. clarify. }
      { des; clarify. rewrite Prism.preview_review in *. clarify. }
      { eexists _. rewrite URA.unit_idl. ss. }
    Qed.

    Lemma whites_prism_id_rev P o
      :
      (whites Prism.id (fun s => exists i, Prism.review p i = s /\ P i) o)
        -∗
      (whites p P o).
    Proof.
      iIntros "WHITES".
      iApply (OwnM_extends with "WHITES"). apply pointwise_extends.
      i. ss. des_ifs; try by reflexivity.
      { des; clarify. eapply Prism.review_preview in Heq. clarify.
        exfalso. eauto.
      }
      { eexists _. rewrite URA.unit_idl. ss. }
      { eexists _. rewrite URA.unit_idl. ss. }
    Qed.

    Lemma blacks_prism_id P
      :
      (blacks p P)
        -∗
        (blacks Prism.id (fun s => exists i, Prism.review p i = s /\ P i)).
    Proof.
      iIntros "[% [% BLACKS]]".
      unfold blacks.
      iExists (fun s => match Prism.preview p s with
                        | Some i => f i
                        | None => None
                        end). iSplit.
      { iPureIntro. i. ss. split.
        { i. des_ifs; ss.
          { eapply Prism.review_preview in Heq. esplits; eauto. eapply H; auto. }
          { rr in H0. des. ss. }
        }
        { i. des. des_ifs.
          { rewrite Prism.preview_review in Heq. clarify. eapply H; eauto. }
          { rewrite Prism.preview_review in Heq. clarify. }
        }
      }
      iApply (OwnM_extends with "BLACKS"). apply pointwise_extends.
      i. ss. des_ifs; try by reflexivity.
    Qed.

    Lemma blacks_prism_id_rev P
      :
      (blacks Prism.id (fun s => exists i, Prism.review p i = s /\ P i))
        -∗
        (blacks p P).
    Proof.
      iIntros "[% [% BLACKS]]".
      unfold blacks.
      iExists (fun i => f (Prism.review p i)). iSplit.
      { iPureIntro. i. split.
        { i. dup H0. eapply H in H0. des; eauto.
          eapply f_equal with (f:=Prism.preview p) in H0.
          rewrite ! Prism.preview_review in H0. clarify.
        }
        { i. eapply H. esplits; eauto. }
      }
      iApply (OwnM_extends with "BLACKS"). apply pointwise_extends.
      i. ss. des_ifs; try by reflexivity.
      { eapply Prism.review_preview in Heq. clarify. reflexivity. }
      { eapply Prism.review_preview in Heq. clarify. }
      { eexists _. rewrite URA.unit_idl. ss. }
      { eexists _. rewrite URA.unit_idl. ss. }
    Qed.

    Lemma white_prism_id i o
      :
      (white p i o)
        -∗
        (white Prism.id (Prism.review p i) o).
    Proof. auto. Qed.

    Lemma white_prism_id_rev i o
      :
      (white Prism.id (Prism.review p i) o)
        -∗
        (white p i o).
    Proof. auto. Qed.

    Lemma black_prism_id i o q
      :
      (black p i o q)
        -∗
        (black Prism.id (Prism.review p i) o q).
    Proof. auto. Qed.

    Lemma black_prism_id_rev i o q
      :
      (black Prism.id (Prism.review p i) o q)
        -∗
        (black p i o q).
    Proof. auto. Qed.

    Lemma black_ex_prism_id i q
      :
      (black_ex p i q)
        -∗
        (black_ex Prism.id (Prism.review p i) q).
    Proof.
      iIntros "[% BLACK]". iExists _. auto.
    Qed.

    Lemma black_ex_prism_id_rev i q
      :
      (black_ex Prism.id (Prism.review p i) q)
        -∗
        (black_ex p i q).
    Proof.
      iIntros "[% BLACK]". iExists _. auto.
    Qed.

    Lemma whites_of_prism_id l o
      :
      (whites_of p l o)
        -∗
        (whites_of Prism.id (List.map (Prism.review p) l) o).
    Proof.
      eapply list_prop_sum_map. i. eapply white_prism_id.
    Qed.

    Lemma whites_of_prism_id_rev l o
      :
      (whites_of Prism.id (List.map (Prism.review p) l) o)
        -∗
        (whites_of p l o).
    Proof.
      eapply list_prop_sum_map_inv. i. eapply white_prism_id_rev.
    Qed.

    Lemma blacks_of_prism_id l
      :
      (blacks_of p l)
        -∗
        (blacks_of Prism.id (List.map (Prism.review p) l)).
    Proof.
      eapply list_prop_sum_map. i. eapply black_ex_prism_id.
    Qed.

    Lemma blacks_of_prism_id_rev l
      :
      (blacks_of Prism.id (List.map (Prism.review p) l))
        -∗
        (blacks_of p l).
    Proof.
      eapply list_prop_sum_map_inv. i. eapply black_ex_prism_id_rev.
    Qed.
    End PRISM.


    (* Target *)
    Definition whites_all (f: S -> A): iProp :=
      OwnM ((fun i => Fuel.white (f i)): (S ==> Fuel.t A)%ra).

    (* Source *)
    Definition blacks_all (f: S -> A): iProp :=
      OwnM ((fun i => Fuel.black (f i) 1%Qp): (S ==> Fuel.t A)%ra).

    Definition whites_update
               (f0 f1: S -> A)
               (u: A)
               (fm: fmap S)
               (UPDATE: forall i,
                   match fm i with
                   | Flag.emp => f1 i = f0 i
                   | Flag.fail => OrderedCM.le (OrderedCM.add u (f1 i)) (f0 i)
                   | Flag.success => True
                   end)
      :
      (whites_all f0)
        -∗
        (blacks Prism.id (fun i => fm i = Flag.success))
        -∗
        (#=>
           ((whites_all f1)
              **
              (blacks Prism.id (fun i => fm i = Flag.success))
              **
              (whites Prism.id (fun i => fm i = Flag.fail) u)
              **
              (whites Prism.id (fun i => fm i = Flag.success) u))).
    Proof.
      iIntros "WHITE [% [% BLACK]]".
      iCombine "WHITE BLACK" as "OWN".
      iPoseProof (OwnM_Upd_set with "OWN") as "> [% [% OWN]]".
      { eapply updatable_set_impl; cycle 1.
        { eapply pointwise_updatable_set. i.
          instantiate (1:=fun (i: S) (a: Fuel.t A) =>
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
                            exists (f: S -> option A),
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
                (((fun i => Fuel.white (f1 i)): (S ==> Fuel.t A)%ra)
                   ⋅
                   ((fun i =>
                       match f2 i with
                       | Some a => Fuel.black a 1
                       | None => ε
                       end): (S ==> Fuel.t A)%ra)
                   ⋅
                   ((fun i =>
                       if (excluded_middle_informative (fm i = Flag.fail))
                       then Fuel.white u
                       else ε): (S ==> Fuel.t A)%ra)
                   ⋅
                   ((fun i =>
                       if (excluded_middle_informative (fm i = Flag.success))
                       then Fuel.white u
                       else ε): (S ==> Fuel.t A)%ra))).
      { extensionality i. specialize (H0 i). des.
        rewrite H1. erewrite ! (@unfold_pointwise_add S (Fuel.t A)). auto.
      }
      subst. iPoseProof "OWN" as "[[[OWN0 OWN1] OWN2] OWN3]".
      iModIntro. iFrame. iExists _. iSplit.
      2:{ iFrame. }
      iPureIntro. i. specialize (H0 i). des. auto.
    Qed.

    Definition blacks_update
               (f0: S -> A)
               (u n: A)
               (fm: fmap S)
      :
      (blacks_all f0)
        -∗
        (whites Prism.id (fun i => fm i = Flag.fail) u)
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
                 (whites Prism.id (fun i => fm i = Flag.success) n))).
    Proof.
      iIntros "BLACK WHITE".
      iCombine "BLACK WHITE" as "OWN".
      iPoseProof (OwnM_Upd_set with "OWN") as "> [% [% OWN]]".
      { eapply updatable_set_impl; cycle 1.
        { eapply pointwise_updatable_set. i.
          instantiate (1:=fun (i: S) (a: Fuel.t A) =>
                            exists o,
                              (a = (Fuel.black o 1: Fuel.t A) ⋅ (if (excluded_middle_informative (fm i = Flag.success))
                                                                 then Fuel.white n
                                                                 else ε)) /\
                                (match fm i with
                                 | Flag.emp => o = f0 i
                                 | Flag.fail => OrderedCM.le (OrderedCM.add u o) (f0 i)
                                 | Flag.success => True
                                 end)).
          erewrite ! (@unfold_pointwise_add S (Fuel.t A)).
          destruct (fm a) eqn:FM.
          { des_ifs; ss.
            { ii. exploit Fuel.decr_update; eauto. i. des. subst.
              esplits; eauto. rewrite URA.unit_id. auto.
            }
            { compute in Heq. clarify. }
          }
          { des_ifs.
            { compute in Heq. clarify. rewrite FM in *. ss. }
            { ii. esplits; eauto. }
          }
          { des_ifs.
            { compute in Heq. clarify. rewrite FM in *. ss. }
            rewrite URA.unit_id. ii.
            exploit Fuel.success_update; eauto. i. esplits; eauto. }
        }
        { instantiate (1 := fun r =>
                              exists (f1: S -> A),
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
                (((fun i => Fuel.black (f1 i) 1): (S ==> Fuel.t A)%ra)
                   ⋅
                   (fun i =>
                      if (excluded_middle_informative (fm i = Flag.success))
                      then Fuel.white n
                      else ε))).
      { extensionality i. specialize (H i). des.
        rewrite H0. erewrite ! (@unfold_pointwise_add S (Fuel.t A)). auto.
      }
      subst. iPoseProof "OWN" as "[OWN0 OWN1]".
      iModIntro. iFrame. iExists _. iSplit.
      2:{ iFrame. }
      iPureIntro. i. specialize (H i). des.
      erewrite ! (@unfold_pointwise_add S (Fuel.t A)) in H0. des_ifs.
    Qed.
  End FAIR.

  Section SOURCE.
    Variable (S: Type).
    Definition srct: URA.t := @t S Ord.t _.
    Context `{ING: @GRA.inG srct Σ}.

    Definition sat_source (f: imap S owf) :=
      blacks_all f.

    Definition source_update
               (o: Ord.t)
               (ls lf: list S)
               (f0: imap S owf)
               (fm: fmap S)
               (FAIL: forall i (IN: fm i = Flag.fail), List.In i lf)
               (SUCCESS: forall i (IN: List.In i ls), fm i = Flag.success)
      :
      (sat_source f0)
        -∗
        (whites_of Prism.id lf Ord.one)
        -∗
        (#=>
           (∃ f1,
               (⌜fair_update f0 f1 (prism_fmap Prism.id fm)⌝)
                 **
                 (sat_source f1)
                 **
                 (whites_of Prism.id ls o))).
    Proof.
      iIntros "SAT WHITE".
      iPoseProof (blacks_update with "SAT [> WHITE]") as "> [% [[% BLACK] WHITE]]".
      { instantiate (1:=Ord.one). instantiate (1:=fm).
        iStopProof. cut (forall l (P: S -> Prop) (COMPLETE: forall i (IN: P i), List.In i l), whites_of Prism.id l Ord.one ⊢ #=> whites Prism.id P Ord.one).
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
        erewrite ! (@unfold_pointwise_add S (Fuel.t Ord.t)).
        apply pointwise_updatable. i. unfold maps_to_res. ss.
        des_ifs; des; ss; repeat rewrite URA.unit_id; repeat rewrite URA.unit_idl; ss.
        { ii. eapply URA.wf_mon. instantiate (1:=Fuel.white Ord.one). r_wf H. }
        { exfalso. eapply n0; ss. auto. }
      }
      { iExists f1. iFrame. iSplitR.
        { iPureIntro. ii. specialize (H i). unfold prism_fmap. ss. des_ifs.
          ss. eapply Ord.lt_le_lt; [|eauto].
          unfold Ord.one. rewrite Hessenberg.add_S_l.
          rewrite Hessenberg.add_O_l. eapply Ord.S_lt.
        }
        { instantiate (1:=Jacobsthal.mult o (Ord.from_nat (List.length ls))).
          iStopProof. cut (forall l (P: S -> Prop) (SOUND: forall i (IN: List.In i l), P i), whites Prism.id P (o × List.length l)%ord ⊢ #=> whites_of Prism.id l o).
          { i. eapply H0. auto. }
          induction l; ss; i.
          { iIntros "H". auto. }
          iIntros "H".
          iPoseProof (OwnM_Upd with "H") as "> H".
          { instantiate (1:=(maps_to_res a (Fuel.white o: Fuel.t Ord.t): (S ==> Fuel.t Ord.t)%ra)
                              ⋅
                              (fun i =>
                                 if (excluded_middle_informative (P i))
                                 then (Fuel.white (o × List.length l)%ord: Fuel.t Ord.t)
                                 else ε): (S ==> Fuel.t Ord.t)%ra).
            erewrite ! (@unfold_pointwise_add S (Fuel.t Ord.t)).
            apply pointwise_updatable. i. unfold maps_to_res. ss. des_ifs.
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

    Definition source_init_resource: srct := fun i => Fuel.black Ord.O 1.

    Lemma source_init_resource_wf:
      URA.wf source_init_resource.
    Proof.
      ur. i. ur. split; auto. reflexivity.
    Qed.

    Lemma source_init
          o
      :
      (OwnM source_init_resource)
        -∗
        (#=>
           (∃ f,
               (sat_source f)
                 **
                 (whites Prism.id (fun _ => True: Prop) o))).
    Proof.
      transitivity (blacks_all (fun (_: S) => Ord.O)); [auto|].
      iIntros "BLACKS".
      iPoseProof (blacks_update with "BLACKS []") as "> [% [[% BLACKS] WHITES]]".
      { iApply (OwnM_extends with "[]").
        { instantiate (1:=URA.unit).
          instantiate (1:=Ord.O).
          instantiate (1:=fun _ => Flag.success).
          eapply pointwise_extends. i. des_ifs.
          eexists. rewrite URA.unit_idl. eauto.
        }
        { iApply (@OwnM_unit (S ==> Fuel.t Ord.t)%ra). }
      }
      iModIntro. iExists _. iFrame.
      iApply (OwnM_extends with "WHITES").
      { eapply pointwise_extends. i. des_ifs. reflexivity. }
    Qed.
  End SOURCE.


  Section TARGET.
    Variable (S: Type).
    Let Id := id_sum thread_id S.
    Definition tgtt: URA.t := @t Id nat _.
    Context `{ING: @GRA.inG tgtt Σ}.

    Definition sat_target (f: imap Id nat_wf) (ths: TIdSet.t): iProp :=
      ((whites_all f)
         **
         (blacks Prism.id (fun i => exists j, (<<NIN: ~ TIdSet.In j ths>>) /\ (<<EQ: i = inl j>>))))
    .

    Definition target_init_resource (f: imap Id nat_wf): tgtt :=
      ((fun i => Fuel.white (f i)): (Id ==> Fuel.t nat)%ra)
        ⋅
        ((fun i => Fuel.black (f i) 1): (Id ==> Fuel.t nat)%ra).

    Lemma target_init_resource_wf f:
      URA.wf (target_init_resource f).
    Proof.
      ur. i. ur. unfold target_init_resource.
      erewrite ! (@unfold_pointwise_add Id (Fuel.t nat)).
      ur. split; auto. rewrite Fuel.from_monoid_add.
      apply Fuel.le_iff. ss. lia.
    Qed.

    Lemma target_init f ths
      :
      (OwnM (target_init_resource f))
        -∗
        ((sat_target f ths)
           **
           (natmap_prop_sum ths (fun tid _ => black_ex inlp tid 1))
           **
           (blacks inrp (fun i => True: Prop))).
    Proof.
      iIntros "[WHITES BLACKS]". unfold sat_target. iFrame.
      set (f0 :=
             (fun i =>
                match i with
                | inr _ => None
                | inl tid => if NatMap.find tid ths then None else Some (f (inl tid))
                end): Id -> option nat).
      set (f1 :=
             (fun i =>
                match i with
                | inr _ => None
                | inl tid => if NatMap.find tid ths then Some (f (inl tid)) else None
                end): Id -> option nat).
      set (f2 :=
             (fun i =>
                match i with
                | inr _ => Some (f i)
                | inl _ => None
                end): Id -> option nat).
      iPoseProof (OwnM_extends with "BLACKS") as "[BLACKS0 [BLACKS1 BLACKS2]]".
      { instantiate (1:=((fun i =>
                            match (f0 i) with
                            | Some a => Fuel.black a 1
                            | None => ε
                            end): (Id ==> Fuel.t nat)%ra)).
        instantiate (1:=((fun i =>
                            match (f1 i) with
                            | Some a => Fuel.black a 1
                            | None => ε
                            end): (Id ==> Fuel.t nat)%ra)).
        instantiate (1:=((fun i =>
                            match (f2 i) with
                            | Some a => Fuel.black a 1
                            | None => ε
                            end): (Id ==> Fuel.t nat)%ra)).
        ss. apply pointwise_extends. i. unfold f0, f1, f2.
        ur. des_ifs; repeat rewrite URA.unit_id; repeat rewrite URA.unit_idl; try reflexivity.
      }
      iSplitR "BLACKS0"; [iSplitR "BLACKS1"|].
      { iExists _. iSplit; [|iApply "BLACKS2"].
        iPureIntro.
        { unfold f0. i. des_ifs.
          { split; i; ss.
            { des. inv H. ss. }
            { des. clarify. exfalso. eapply NIN.
              eapply NatMapP.F.in_find_iff. ii. clarify.
            }
          }
          { split; i; ss. esplits; eauto.
            ii. eapply NatMapP.F.in_find_iff in H0. ss.
          }
          { split; i; ss.
            { des. inv H. ss. }
            { des. clarify. }
          }
        }
      }
      { unfold f1. clear f0 f1 f2. iStopProof.
        pattern ths. eapply nm_ind.
        { iIntros "H". iApply natmap_prop_sum_empty. }
        i. clear STRONG.
        iIntros "BLACKS".
        iPoseProof (OwnM_extends with "BLACKS") as "[BLACKS0 BLACKS1]"; cycle 1.
        { iApply (natmap_prop_sum_add with "[BLACKS0] [BLACKS1]").
          { iApply IH. iApply "BLACKS0". }
          ss. iExists (f (inl k)). iApply "BLACKS1".
        }
        apply pointwise_extends. i. unfold maps_to_res. ss.
        unfold tgtt, t.
        erewrite (@unfold_pointwise_add Id (Fuel.t nat)).
        unfold Prism.review in *. ss.
        des_ifs; repeat rewrite URA.unit_id; repeat rewrite URA.unit_idl; try by reflexivity.
        { rewrite NatMapP.F.add_o in Heq1. des_ifs. }
        { rewrite NatMapP.F.add_o in Heq1. des_ifs. }
        { rewrite NatMapP.F.add_o in Heq1. des_ifs. }
      }
      { iApply blacks_prism_id_rev.
        iExists _. iSplit; [|iApply "BLACKS0"].
        iPureIntro.
        { unfold f2. ss. i. split; i.
          { des_ifs.
            { inv H. ss. }
            rr in H. eauto.
          }
          { des. compute in H. subst. ss. }
        }
      }
    Qed.

    Definition target_remove_thread
               tid ths
               (f: imap Id nat_wf)
      :
      (sat_target f ths)
        -∗
        (black_ex inlp tid 1)
        -∗
        (#=>
           (sat_target f (NatMap.remove tid ths))).
    Proof.
      iIntros "[WHITES [% [% BLACKS]]] [% BLACK]". des.
      iFrame. iCombine "BLACKS BLACK" as "BLACK".
      iExists (fun i =>
                 match i with
                 | inl tid' => if (tid_dec tid' tid) then Some a else f0 i
                 | _ => f0 i
                 end).
      iSplitR.
      { iModIntro. iPureIntro. i. des_ifs.
        { split; i; ss. esplits; eauto.
          ii. apply NatMapP.F.remove_in_iff in H1. des; ss.
        }
        { rewrite H. split; i.
          { des. esplits; eauto. ii.
            apply NatMapP.F.remove_in_iff in H0. des; ss.
          }
          { des. esplits; eauto. ii. clarify. eapply NIN.
            apply NatMapP.F.remove_in_iff. split; auto.
          }
        }
        { rewrite H. split; i.
          { des; ss. }
          { des; ss. }
        }
      }
      iApply (OwnM_Upd with "BLACK").
      apply pointwise_updatable. i.
      erewrite ! (@unfold_pointwise_add Id (Fuel.t nat)).
      unfold maps_to_res. ss.
      des_ifs; repeat rewrite URA.unit_id; repeat rewrite URA.unit_idl; ss.
      { apply URA.extends_updatable. exists (Fuel.black n 1). apply URA.add_comm. }
      { compute in Heq1. clarify. }
      { compute in Heq1. clarify. }
    Qed.

    Definition target_add_thread
               tid ths0 ths1
               (THS: TIdSet.add_new tid ths0 ths1)
               (f0 f1: imap Id nat_wf)
               (UPD: fair_update f0 f1 (prism_fmap inlp (fun i => if tid_dec i tid then Flag.success else Flag.emp)))
      :
      (sat_target f0 ths0)
        -∗
        (#=>
           ((sat_target f1 ths1)
              **
              (black_ex inlp tid 1))).
    Proof.
      iIntros "[WHITES [% [% BLACKS]]]".
      hexploit (proj2 (H (inl tid))).
      { apply inv_add_new in THS. des. esplits; eauto. }
      i. destruct (f (inl tid)) eqn:TID.
      2:{ inv H0. ss. } clear H0.
      set (f2 :=
             (fun i =>
                match i with
                | inl tid' => if tid_dec tid' tid then None else f i
                | _ => f i
                end): Id -> option nat).
      iAssert (OwnM (((fun i =>
                         match (f2 i) with
                         | Some a => Fuel.black a 1: Fuel.t nat
                         | None => ε: Fuel.t nat
                         end): (Id ==> Fuel.t nat)%ra) ⋅ (maps_to_res (inl tid) (Fuel.black n 1: Fuel.t nat)))) with "[BLACKS]" as "[BLACKS BLACK]".
      { iApply (OwnM_extends with "BLACKS").
        erewrite ! (@unfold_pointwise_add Id (Fuel.t nat)).
        eapply pointwise_extends. i. unfold f2, maps_to_res. ss.
        des_ifs; repeat rewrite URA.unit_id; repeat rewrite URA.unit_idl; ss; reflexivity.
      }
      iPoseProof (whites_update with "WHITES [BLACK]") as "> [[[WHITES BLACK] FAIL] SUCCESS]".
      { instantiate (1:=f1). instantiate (1:=1).
        instantiate (1:=prism_fmap inlp (fun i: thread_id => if tid_dec i tid then Flag.success else Flag.emp)).
        i. specialize (UPD i). revert UPD. unfold prism_fmap; ss.
      }
      { iExists (fun i =>
                   match i with
                   | inl tid' => if tid_dec tid' tid then Some n else None
                   | _ => None
                   end). iSplit.
        { iPureIntro. i. unfold prism_fmap. destruct i; ss; des_ifs.
          - split; i; ss. inv H0. inv H1.
          - split; i; ss. inv H0. inv H1.
        }
        { iApply (OwnM_extends with "BLACK").
          eapply pointwise_extends. i. unfold maps_to_res. ss.
          des_ifs; repeat rewrite URA.unit_id; repeat rewrite URA.unit_idl; ss; reflexivity.
        }
      }
      iModIntro. iSplitR "BLACK".
      2:{ iApply (blacks_black with "BLACK"). unfold prism_fmap; ss. des_ifs. }
      unfold sat_target. iFrame.
      iExists f2. iSplit; auto.
      iPureIntro. i. unfold f2. hexploit (H i). i.
      inv THS. des_ifs.
      { split; i.
        { inv H1. ss. }
        { des. clarify. exfalso. eapply NIN.
          apply NatMapP.F.in_find_iff. rewrite nm_find_add_eq. ss.
        }
      }
      { rewrite H0. split; i; des.
        { esplits; eauto. ii. clarify.
          eapply NIN. eapply NatMapP.F.in_find_iff.
          apply NatMapP.F.in_find_iff in H2.
          rewrite nm_find_add_neq in H2; auto.
        }
        { clarify. esplits; eauto. ii.
          eapply NIN. eapply NatMapP.F.in_find_iff.
          apply NatMapP.F.in_find_iff in H2.
          rewrite nm_find_add_neq; auto.
        }
      }
      { rewrite H0. split; i; des; ss. }
    Qed.

    Definition white_thread: iProp := ∀ i, white inlp i 1.

    Definition target_update_thread
               tid ths
               (f0 f1: imap Id nat_wf)
               (UPD: fair_update f0 f1 (prism_fmap inlp (tids_fmap tid ths)))
      :
      (sat_target f0 ths)
        -∗
        (black_ex inlp tid 1)
        -∗
        (#=>
           ((sat_target f1 ths)
              **
              (black_ex inlp tid 1)
              **
              white_thread)).
    Proof.
      iIntros "[WHITES [% [% BLACKS]]] [% BLACK]".
      iCombine "BLACKS BLACK" as "BLACKS". iOwnWf "BLACKS".
      iPoseProof "BLACKS" as "[BLACKS BLACK]".
      assert (TIN: TIdSet.In tid ths).
      { ur in H0. specialize (H0 (inl tid)). ur in H0.
        unfold maps_to_res in H0. specialize (H (inl tid)). des_ifs.
        { destruct (classic (TIdSet.In tid ths)); ss.
          hexploit (proj2 H).
          { esplits; eauto. }
          { i. inv H2. ss. }
        }
        { inv Heq0. inv Heq1. des. ss. }
      }
      clear H0.
      set (f2 :=
             (fun i =>
                match i with
                | inl tid' => if tid_dec tid' tid then Some a else f i
                | _ => f i
                end): Id -> option nat).
      iPoseProof (whites_update with "WHITES [BLACKS BLACK]") as "> [[[WHITES [% [% BLACK]]] FAIL] SUCCESS]".
      { instantiate (1:=f1). instantiate (1:=1).
        instantiate (1:=prism_fmap inlp
                          (fun i: thread_id =>
                             if tid_dec i tid then Flag.success
                             else
                               if NatMap.find i ths
                               then Flag.fail
                               else Flag.success)).
        i. specialize (UPD i). revert UPD. unfold f2, prism_fmap, tids_fmap; ss. des_ifs.
        i. exfalso. eapply n2. eapply NatMapP.F.in_find_iff. ii. clarify.
      }
      { iExists f2. iCombine "BLACKS BLACK" as "BLACKS". iSplit.
        { iPureIntro. i. unfold f2, prism_fmap. specialize (H i).
          destruct i; ss; des_ifs; rewrite H; split; ss; i.
          - des. clarify. exfalso. eapply NIN. eapply NatMapP.F.in_find_iff. ii. clarify.
          - esplits; ss. ii. eapply NatMapP.F.in_find_iff in H1. ss.
          - des. clarify.
        }
        iApply (OwnM_extends with "BLACKS").
        erewrite ! (@unfold_pointwise_add Id (Fuel.t nat)).
        eapply pointwise_extends. i. unfold f2, maps_to_res. ss.
        des_ifs; repeat rewrite URA.unit_id; repeat rewrite URA.unit_idl; ss; try reflexivity.
        { eexists _. rewrite URA.add_comm. auto. }
        { eexists _. eauto. }
        { eexists. rewrite URA.unit_idl. ss. }
      }
      iSplitR "FAIL SUCCESS".
      { hexploit (proj2 (H0 (inl tid))).
        { unfold prism_fmap; ss. des_ifs. }
        i. inv H1.
        set (f4 := (fun i =>
                      match i with
                      | inl tid' => if tid_dec tid' tid then None else f3 i
                      | _ => f3 i
                      end): Id -> option nat).
        iPoseProof (OwnM_extends with "BLACK") as "[BLACKS BLACK]".
        { instantiate (1:=(maps_to_res (inl tid) (Fuel.black x 1: Fuel.t nat))).
          instantiate (1:=(fun i =>
                             match f4 i with
                             | Some a => Fuel.black a 1
                             | None => ε
                             end)).
          erewrite ! (@unfold_pointwise_add Id (Fuel.t nat)).
          eapply pointwise_extends. i. unfold f4, maps_to_res. ss.
          des_ifs; repeat rewrite URA.unit_id; repeat rewrite URA.unit_idl; ss; try reflexivity.
        }
        iModIntro. iSplitR "BLACK".
        { iSplitL "WHITES"; auto. iExists _.
          iSplit; [|iApply "BLACKS"]. iPureIntro. i.
          unfold f4. specialize (H0 i). unfold prism_fmap in H0. destruct i; ss; des_ifs.
          { split; i; ss.
            { inv H1. ss. }
            { des. clarify. }
          }
          { rewrite H0. split; i; ss. des. clarify.
            exfalso. eapply NIN. eapply NatMapP.F.in_find_iff. ii. clarify.
          }
          { rewrite H0. split; i; ss. esplits; eauto.
            ii. eapply NatMapP.F.in_find_iff in H3. ss.
          }
          { rewrite H0. split; i; ss. des. clarify. }
        }
        { iExists _. iFrame. }
      }
      { iModIntro. iIntros (tid'). destruct (tid_dec tid' tid).
        { subst. iApply (whites_white with "SUCCESS"). unfold prism_fmap in *; ss. des_ifs. }
        destruct (NatMap.find tid' ths) eqn:EQ.
        { iApply (whites_white with "FAIL"). unfold prism_fmap in *; ss. des_ifs. }
        { iApply (whites_white with "SUCCESS"). unfold prism_fmap in *; ss. des_ifs. }
      }
    Qed.

    Definition target_update_aux
               ths
               (f0 f1: imap Id nat_wf)
               (fm: fmap S)
               (UPD: fair_update f0 f1 (prism_fmap inrp fm))
      :
      (sat_target f0 ths)
        -∗
        (blacks Prism.id (fun i => (prism_fmap inrp fm) i = Flag.success))
        -∗
        (#=>
           ((sat_target f1 ths)
              **
              (blacks Prism.id (fun i => (prism_fmap inrp fm) i = Flag.success))
              **
              (whites Prism.id (fun i => (prism_fmap inrp fm) i = Flag.fail) 1))).
    Proof.
      iIntros "[WHITES [% [% BLACKS]]] BLACK".
      iPoseProof (whites_update with "WHITES BLACK") as "> [[[WHITES BLACK] FAIL] _]".
      { instantiate (1:=f1). i. specialize (UPD i). des_ifs.
        ss. instantiate (1:=1). lia.
      }
      { iModIntro. iSplitR "FAIL"; [|auto].
        iSplitR "BLACK"; [|auto].
        iSplitL "WHITES"; [auto|]. iExists _. iSplitR; [|auto]. auto.
      }
    Qed.

    Definition target_update
               (ls lf: list S)
               ths
               (f0 f1: imap Id nat_wf)
               (fm: fmap S)
               (UPD: fair_update f0 f1 (prism_fmap inrp fm))
               (SUCCESS: forall i (IN: fm i = Flag.success), List.In i ls)
               (FAIL: forall i (IN: List.In i lf), fm i = Flag.fail)
               (NODUP: List.NoDup lf)
      :
      (sat_target f0 ths)
        -∗
        (list_prop_sum (fun i => black_ex Prism.id (inr i) 1) ls)
        -∗
        (#=>
           ((sat_target f1 ths)
              **
              (list_prop_sum (fun i => black_ex Prism.id (inr i) 1) ls)
              **
              (list_prop_sum (fun i => white Prism.id (inr i) 1) lf))).
    Proof.
      iIntros "SAT BLACK".
      iPoseProof (black_ex_list_blacks with "[BLACK]") as "[BLACKS K]"; cycle 2.
      { iPoseProof (target_update_aux with "SAT BLACKS") as "> [[SAT BLACKS] WHITES]".
        { eauto. }
        iPoseProof ("K" with "BLACKS") as "BLACKS".
        iModIntro. iFrame. iSplitL "BLACKS".
        { iApply (list_prop_sum_forall2 with "BLACKS").
          { apply Forall2_flip. apply list_map_forall2. }
          { i. ss. subst. reflexivity. }
        }
        { iApply (list_prop_sum_forall2 with "[WHITES]").
          { apply Forall2_flip. apply list_map_forall2. }
          2:{ iApply (whites_white_list with "WHITES"). instantiate (1:=inr).
              { i. s. apply in_map_iff in IN. des. clarify. unfold prism_fmap; ss. auto. }
              { apply injective_map_NoDup_strong; auto. i. clarify. }
          }
          { i. apply in_map_iff in INA. des. ss. clarify. }
        }
      }
      { i. ss. unfold prism_fmap in IN. destruct i; ss. apply in_map_iff. eauto. }
      { iApply (list_prop_sum_forall2 with "BLACK").
        { apply list_map_forall2. }
        { i. ss. subst. reflexivity. }
      }
    Qed.

    Definition target_update_prism {_Id}
               (ls lf: list _Id)
               (p: Prism.t S _Id)
               ths
               (f0 f1: imap Id nat_wf)
               (fm: fmap _Id)
               (UPD: fair_update f0 f1 (prism_fmap (Prism.compose inrp p) fm))
               (SUCCESS: forall i (IN: fm i = Flag.success), List.In i ls)
               (FAIL: forall i (IN: List.In i lf), fm i = Flag.fail)
               (NODUP: List.NoDup lf)
      :
      (sat_target f0 ths)
        -∗
        (list_prop_sum (fun i => black_ex (Prism.compose inrp p) i 1) ls)
        -∗
        (#=>
           ((sat_target f1 ths)
              **
              (list_prop_sum (fun i => black_ex (Prism.compose inrp p) i 1) ls)
              **
              (list_prop_sum (fun i => white (Prism.compose inrp p) i 1) lf))).
    Proof.
      iIntros "SAT BLACKS".
      iPoseProof (target_update with "SAT [BLACKS]") as "> [[SAT BLACKS] WHITES]".
      { rewrite prism_fmap_compose in UPD. eauto. }
      { instantiate (1:=List.map (Prism.review p) ls).
        i. unfold prism_fmap in IN. des_ifs.
        eapply Prism.review_preview in Heq. subst.
        eapply in_map. eauto.
      }
      { instantiate (1:=List.map (Prism.review p) lf).
        i. eapply in_map_iff in IN. des. subst.
        unfold prism_fmap. rewrite Prism.preview_review. eauto.
      }
      { eapply FinFun.Injective_map_NoDup; eauto.
        ii. eapply f_equal with (f:=Prism.preview p) in H.
        rewrite ! Prism.preview_review in H. clarify.
      }
      { iApply (list_prop_sum_map with "BLACKS").
        i. iIntros "BLACK". iApply (black_ex_prism_id with "BLACK").
      }
      iModIntro. iFrame. iSplitL "BLACKS".
      { iApply (list_prop_sum_map_inv with "BLACKS").
        i. iIntros "BLACK". iApply (black_ex_prism_id_rev with "BLACK").
      }
      { iApply (list_prop_sum_map_inv with "WHITES").
        i. iIntros "WHITE". iApply (white_prism_id_rev with "WHITE").
      }
    Qed.

  End TARGET.
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

    Definition pending (k: nat) (q: Qp): iProp :=
      OwnM (FiniteMap.singleton k ((ε: @CounterRA.t Ord.t _, OneShot.pending unit q: OneShot.t unit): URA.prod (@CounterRA.t Ord.t _) (OneShot.t unit))).

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
      rewrite FiniteMap.singleton_core_total. auto.
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
      rewrite FiniteMap.singleton_core_total. auto.
    Qed.

    Global Program Instance Persistent_shot k: Persistent (shot k).
    Next Obligation.
    Proof.
      i. iIntros "POS". ss. iPoseProof (shot_persistent with "POS") as "POS". auto.
    Qed.

    Lemma pending_shot k
      :
      (pending k 1)
        -∗
        #=> (shot k).
    Proof.
      iApply OwnM_Upd. eapply FiniteMap.singleton_updatable.
      apply URA.prod_updatable.
      { reflexivity. }
      { apply OneShot.pending_shot. }
    Qed.

    Lemma pending_not_shot k q
      :
      (pending k q)
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

    Lemma pending_sum k q0 q1
      :
      (pending k q0)
        -∗
        (pending k q1)
        -∗
        (pending k (q0 + q1)%Qp).
    Proof.
      iIntros "H0 H1". iCombine "H0 H1" as "H".
      rewrite FiniteMap.singleton_add.
      ur. rewrite URA.unit_id. ur. auto.
    Qed.

    Lemma pending_wf k q
      :
      (pending k q)
        -∗
        (⌜(q ≤ 1)%Qp⌝).
    Proof.
      iIntros "H". iOwnWf "H".
      rewrite FiniteMap.singleton_wf in H0. ur in H0. des.
      apply OneShot.pending_wf in H1. auto.
    Qed.

    Lemma pending_split k q0 q1
      :
      (pending k (q0 + q1)%Qp)
        -∗
        (pending k q0 ** pending k q1).
    Proof.
      iIntros "H".
      iPoseProof (OwnM_extends with "H") as "[H0 H1]"; [|iSplitL "H0"; [iApply "H0"|iApply "H1"]].
      { rewrite FiniteMap.singleton_add.
        rewrite OneShot.pending_sum. ur.
        rewrite URA.unit_id. ur. reflexivity.
      }
    Qed.

    Lemma alloc o
      :
      ⊢ #=> (∃ k, black k o ** white k o ** pending k 1).
    Proof.
      iPoseProof (@OwnM_unit _ _ H) as "H".
      iPoseProof (OwnM_Upd_set with "H") as "> H0".
      { eapply FiniteMap.singleton_alloc.
        instantiate (1:=((CounterRA.black o, ε): URA.prod (@CounterRA.t Ord.t _) (OneShot.t unit)) ⋅ ((CounterRA.white o, ε): URA.prod (@CounterRA.t Ord.t _) (OneShot.t unit)) ⋅ (ε, OneShot.pending unit 1)).
        repeat rewrite unfold_prod_add. repeat rewrite URA.unit_idl. repeat rewrite URA.unit_id.
        rewrite unfold_prod_wf. ss. split.
        { eapply CounterRA.black_white_wf. }
        { apply OneShot.pending_one_wf. }
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

    Lemma cut_white k n o
      :
      (white k (o × (S n))%ord)
        -∗
        (white k (o × n)%ord ** white k o).
    Proof.
      iIntros "WHITE".
      iApply (white_split_eq with "[WHITE]").
      iApply (white_eq with "WHITE").
      rewrite Ord.from_nat_S. rewrite Jacobsthal.mult_S.
      rewrite Hessenberg.add_comm. reflexivity.
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
    Variable (S: Type).
    Context `{@GRA.inG t Σ}.
    Context `{@GRA.inG (@FairRA.t S nat _) Σ}.
    Context `{@GRA.inG (@FiniteMap.t (OneShot.t unit)) Σ}.
    Context `{@GRA.inG (Region.t (S * nat * Ord.t * Qp * nat)) Σ}.

    Section PRISM.
    Variable (Id: Type).
    Variable (p: Prism.t S Id).

    Definition arrow: (S * nat * Ord.t * Qp * nat) -> iProp :=
      fun '(i, k, c, q, x) =>
        ((OwnM (FiniteMap.singleton x (OneShot.shot tt)) ** shot k)
         ∨
           (∃ n, (FairRA.black Prism.id i n q) ** white k (Jacobsthal.mult c (Ord.from_nat n))))%I.

    Definition arrows_sat: iProp := Region.sat arrow.

    Definition correl (i: Id) (k: nat) (c: Ord.t): iProp :=
      ∃ r q x, Region.white r (Prism.review p i, k, c, q, x).

    Lemma correl_persistent i k c
      :
      correl i k c ⊢ □ correl i k c.
    Proof.
      iIntros "# H". auto.
    Qed.

    Global Program Instance Persistent_correl i k c: Persistent (correl i k c).

    Local Transparent IUpd.
    Lemma correl_correlate_gen i k c n
      :
      (correl i k c)
        -∗
        (FairRA.white p i n)
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

    Lemma correl_correlate i k c
      :
      (correl i k c)
        -∗
        (FairRA.white p i 1)
        -∗
        (#=(arrows_sat)=> white k c ∨ shot k).
    Proof.
      iIntros "CORR WHITE".
      iPoseProof (correl_correlate_gen with "CORR WHITE") as "> [H|H]"; auto.
      iModIntro. iLeft. iApply white_eq; eauto.
      apply Jacobsthal.mult_1_r.
    Qed.

    Definition duty_list (i: Id) (rs: list (nat * (nat * Ord.t * Qp * nat))) (q: Qp): iProp :=
      (list_prop_sum (fun '(r, (k, c, q, x)) =>
                        (Region.white r (Prism.review p i, k, c, q, x))
                          **
                          (OwnM ((FiniteMap.singleton x (OneShot.pending unit 1))))) rs)
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
        (Region.white r (Prism.review p i, k, c, q1, x))
        -∗
        (OwnM ((FiniteMap.singleton x (OneShot.pending unit 1))))
        -∗
        (duty_list i ((r, (k, c, q1, x))::tl) q0).
    Proof.
      iIntros "[DUTY %] WHITE OWN". des. iSplit.
      { ss. iFrame. }
      iPureIntro. ss. rewrite <- H3.
      clear H3. revert q0 q1. induction tl.
      { i. ss. rewrite Qp.add_comm. auto. }
      { i. ss. destruct a as [? [[[? ?] ?] ?]]. rewrite <- IHtl.
        rewrite Qp.add_assoc. rewrite Qp.add_assoc. f_equal.
        apply Qp.add_comm.
      }
    Qed.

    Lemma duty_list_unfold i tl (q0: Qp) r k c (q1: Qp) x
      :
      (duty_list i ((r, (k, c, q1, x))::tl) q0)
        -∗
        (Region.white r (Prism.review p i, k, c, q1, x) ** OwnM ((FiniteMap.singleton x (OneShot.pending unit 1))) ** duty_list i tl (q0 + q1)%Qp).
    Proof.
      iIntros "[DUTY %]". ss.
      iPoseProof "DUTY" as "[[WHITE OWN] DUTY]". iFrame.
      iPureIntro. rewrite <- H3.
      clear H3. revert q0 q1. induction tl.
      { i. ss. apply Qp.add_comm. }
      { i. ss. destruct a as [? [[[? ?] ?] ?]]. rewrite IHtl.
        rewrite Qp.add_assoc. rewrite Qp.add_assoc. f_equal.
        apply Qp.add_comm.
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
        2:{ rewrite <- Qp.add_assoc. rewrite <- Qp.add_assoc. f_equal. apply Qp.add_comm. }
        iApply (duty_list_fold with "DUTY WHITE0 OWN0").
      }
      { i. iIntros "DUTY". iApply H6. iApply H4. auto. }
    Qed.

    Definition duty (i: Id) (l: list (nat * Ord.t)): iProp :=
      ∃ (rs: list (nat * (nat * Ord.t * Qp * nat))) (q: Qp),
        (FairRA.black_ex p i q)
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
        □ (list_prop_sum (fun '(r, (k, c, q, x)) =>
                            (Region.white r (Prism.review p i, k, c, q, x))) rs).
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
              Region.white r (Prism.review p i, k, c, q, x)).
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
        { instantiate (1:=FairRA.black_ex p i q0).
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
      { rewrite Qp.div_2. iFrame. }
      iPoseProof (@OwnM_unit (@FiniteMap.t (OneShot.t unit))) as "H".
      iPoseProof (OwnM_Upd_set with "H") as "> [% [% OWN]]".
      { eapply FiniteMap.singleton_alloc. eapply OneShot.pending_one_wf. }
      ss. des. subst.
      iPoseProof (white_mon with "SHOT") as "> SHOT".
      { eapply Jacobsthal.le_mult_r.
        eapply Ord.lt_le. apply Ord.omega_upperbound.
      }
      iPoseProof (Region.alloc with "[SHOT BLACK1]") as "> [% WHITE]".
      { instantiate (1:=(Prism.review p i, k, c, (q / 2)%Qp, k0)). iRight.
        iExists _. iFrame.
      }
      { iModIntro. iExists _, _. iSplit.
        { iSplitL "BLACK0"; [eauto|].
          iApply (duty_list_fold with "[DUTY] WHITE OWN").
          rewrite Qp.div_2. eauto.
        }
        iPureIntro. ss.
      }
    Qed.

    Lemma duty_to_black i
      :
      (duty i [])
        -∗
        FairRA.black_ex p i 1%Qp.
    Proof.
      iIntros "[% [% [[H0 [H1 %]] %]]]". destruct rs; ss. subst. auto.
    Qed.

    Lemma black_to_duty i
      :
      (FairRA.black_ex p i 1%Qp)
        -∗
        (duty i []).
    Proof.
      iIntros "H". iExists _, _. iFrame. iSplit.
      { iSplit.
        { iApply list_prop_sum_nil. }
        { auto. }
      }
      { auto. }
    Qed.

    Definition tax (l: list (nat * Ord.t)): iProp :=
      list_prop_sum (fun '(k, c) => white k (Jacobsthal.mult c Ord.omega)) l.

    Definition taxes (l: list (nat * Ord.t)) (o: Ord.t): iProp :=
      list_prop_sum (fun '(k, c) => white k ((Jacobsthal.mult c Ord.omega) × o)%ord) l.

    Lemma tax_perm l0 l1
          (PERM: Permutation l0 l1)
      :
      tax l0 ⊢ tax l1.
    Proof.
      apply list_prop_sum_perm; auto.
    Qed.

    Lemma tax_nil
      :
      ⊢ tax [].
    Proof.
      apply list_prop_sum_nil.
    Qed.

    Lemma tax_cons_fold k c tl
      :
      (white k (Jacobsthal.mult c Ord.omega) ** tax tl)
        -∗
        (tax ((k, c)::tl)).
    Proof.
      ss.
    Qed.

    Lemma tax_cons_unfold k c tl
      :
      (tax ((k, c)::tl))
        -∗
        (white k (Jacobsthal.mult c Ord.omega) ** tax tl).
    Proof.
      ss.
    Qed.

    Lemma tax_split l0 l1
      :
      (tax (l0 ++ l1))
        -∗
        (tax l0 ** tax l1).
    Proof.
      apply list_prop_sum_split.
    Qed.

    Lemma tax_combine l0 l1
      :
      (tax l0 ** tax l1)
        -∗
        (tax (l0 ++ l1)).
    Proof.
      apply list_prop_sum_combine.
    Qed.

    Lemma taxes_perm l0 l1 o
          (PERM: Permutation l0 l1)
      :
      taxes l0 o ⊢ taxes l1 o.
    Proof.
      apply list_prop_sum_perm; auto.
    Qed.

    Lemma taxes_nil o
      :
      ⊢ taxes [] o.
    Proof.
      apply list_prop_sum_nil.
    Qed.

    Lemma taxes_cons_fold k c tl o
      :
      (white k ((c × Ord.omega) × o)%ord ** (taxes tl o))
        -∗
        (taxes ((k, c)::tl) o).
    Proof.
      ss.
    Qed.

    Lemma taxes_cons_unfold k c tl o
      :
      (taxes ((k, c)::tl) o)
        -∗
        (white k ((c × Ord.omega) × o)%ord ** taxes tl o).
    Proof.
      ss.
    Qed.

    Lemma taxes_split l0 l1 o
      :
      (taxes (l0 ++ l1) o)
        -∗
        (taxes l0 o ** taxes l1 o).
    Proof.
      apply list_prop_sum_split.
    Qed.

    Lemma taxes_combine l0 l1 o
      :
      (taxes l0 o ** taxes l1 o)
        -∗
        (taxes (l0 ++ l1) o).
    Proof.
      apply list_prop_sum_combine.
    Qed.

    Lemma taxes_ord_mon l o0 o1
          (LE: Ord.le o0 o1)
      :
      taxes l o1 ⊢ #=> taxes l o0.
    Proof.
      revert_until l. induction l; i.
      { iIntros "H". iModIntro. iApply taxes_nil. }
      iIntros "H". destruct a as [k o].
      iPoseProof (taxes_cons_unfold with "H") as "[W TX]".
      iPoseProof (IHl with "TX") as "IH".
      { eauto. }
      iPoseProof (white_mon with "W") as "W".
      { instantiate (1:=((o × Ord.omega) × o0)%ord).
        apply Jacobsthal.le_mult_r. auto.
      }
      iMod "W". iMod "IH".
      iPoseProof (taxes_cons_fold with "[W IH]") as "A".
      { iFrame. }
      iModIntro. iFrame.
    Qed.

    Lemma taxes_ord_split_eq l o0 o1
      :
      taxes l (o0 ⊕ o1)%ord ⊢ taxes l o0 ∗ taxes l o1.
    Proof.
      revert_until l. induction l; i.
      { iIntros "H". iPoseProof taxes_nil as "TN". iFrame. }
      iIntros "H". destruct a as [k o].
      iPoseProof (taxes_cons_unfold with "H") as "[W TX]".
      iPoseProof (IHl with "TX") as "[IH1 IH2]".
      iPoseProof (white_eq with "W") as "W".
      { rewrite ClassicJacobsthal.mult_dist. reflexivity. }
      iPoseProof (white_split_eq with "W") as "[W1 W2]".
      iSplitL "IH1 W1".
      { iApply taxes_cons_fold. iFrame. }
      { iApply taxes_cons_fold. iFrame. }
      Unshelve. exact o0.
    Qed.

    Lemma taxes_ord_split l o o0 o1
          (LE: ((o0 ⊕ o1) <= o)%ord)
      :
      taxes l o ⊢ #=> (taxes l o0 ∗ taxes l o1).
    Proof.
      iIntros "T". iPoseProof (taxes_ord_mon with "T") as "T". eauto.
      iMod "T". iModIntro. iApply taxes_ord_split_eq. auto.
    Qed.

    Lemma tax_is_single_taxes l
      :
      tax l ⊢ taxes l (Ord.S Ord.O).
    Proof.
      induction l.
      { iIntros. iApply taxes_nil. }
      iIntros "T". destruct a as [k o].
      iPoseProof (tax_cons_unfold with "T") as "[W T]".
      iApply taxes_cons_fold.
      iPoseProof (white_eq with "W") as "W".
      { rewrite <- Jacobsthal.mult_1_r. reflexivity. }
      iFrame. iApply IHl. auto.
    Qed.

    Lemma taxes_single_is_tax l
      :
      taxes l (Ord.S Ord.O) ⊢ tax l.
    Proof.
      induction l.
      { iIntros. iApply tax_nil. }
      iIntros "T". destruct a as [k o].
      iPoseProof (taxes_cons_unfold with "T") as "[W T]".
      iApply tax_cons_fold.
      iPoseProof (white_eq with "W") as "W".
      { rewrite Jacobsthal.mult_1_r. reflexivity. }
      iFrame. iApply IHl. auto.
    Qed.

    Lemma taxes_ord_split_one l o0 o1
          (LT: (o0 < o1)%ord)
      :
      taxes l o1 ⊢ #=> (taxes l o0 ∗ tax l).
    Proof.
      iIntros "T". iPoseProof (taxes_ord_split with "T") as "T".
      { dup LT. eapply Ord.S_supremum in LT0.
        assert (REP: (o0 == (Ord.O ⊕ o0))%ord).
        { symmetry. apply Hessenberg.add_O_l. }
        etrans. 2: eapply LT0. rewrite REP.
        rewrite <- Hessenberg.add_S_l. reflexivity.
      }
      iMod "T". iDestruct "T" as "[T1 T2]".
      iModIntro. iFrame. iApply taxes_single_is_tax. auto.
    Qed.

    Lemma taxes_ord_merge l o0 o1
      :
      taxes l o0 ∗ taxes l o1 ⊢ taxes l (o0 ⊕ o1)%ord.
    Proof.
      revert_until l. induction l; i.
      { iIntros "H". iPoseProof taxes_nil as "TN". eauto. }
      iIntros "[H1 H2]". destruct a as [k o].
      iPoseProof (taxes_cons_unfold with "H1") as "[W1 TX1]".
      iPoseProof (taxes_cons_unfold with "H2") as "[W2 TX2]".
      iApply taxes_cons_fold. iSplitR "TX1 TX2"; cycle 1.
      { iApply IHl. iFrame. }
      iApply white_eq.
      { rewrite ClassicJacobsthal.mult_dist. reflexivity. }
      iApply (white_merge with "W1 W2").
    Qed.



    Lemma duty_list_pending P i rs q
          (IMPL: P ⊢ duty_list i rs q)
      :
      (P)
        -∗
        (P ∧ (∀ r k c q x (IN: List.In (r, (k, c, q, x)) rs), OwnM ((FiniteMap.singleton x (OneShot.pending unit 1))))).
    Proof.
      revert P q IMPL. induction rs.
      { i. iIntros "H". iSplit; ss. iIntros. ss. }
      i. destruct a as [? [[[? ?] ?] ?]].
      ss. iIntros "DUTY".
      iPoseProof (IHrs with "DUTY") as "DUTY".
      { etrans; eauto. iIntros "DUTY".
        iPoseProof (duty_list_unfold with "DUTY") as "[[# WHITE OWN] DUTY]". eauto.
      }
      iSplit.
      { iDestruct "DUTY" as "[DUTY _]". auto. }
      iIntros. des; clarify.
      { iDestruct "DUTY" as "[DUTY _]". iPoseProof (IMPL with "DUTY") as "DUTY".
        iPoseProof (duty_list_unfold with "DUTY") as "[[# WHITE OWN] DUTY]". eauto.
      }
      { iDestruct "DUTY" as "[_ DUTY]". iApply "DUTY". eauto. }
    Qed.

    Lemma duty_list_disjoint P i0 rs0 q0 i1 rs1 q1
          (IMPL: P ⊢ (duty_list i0 rs0 q0 ** duty_list i1 rs1 q1))
      :
      (P)
        -∗
        #=(arrows_sat)=> (P ** ⌜forall r (IN0: List.In r (List.map fst rs0)) (IN1: List.In r (List.map fst rs1)), False⌝).
    Proof.
      iIntros "DUTY".
      iPoseProof (duty_list_whites with "[DUTY]") as "# WHITES0".
      { iPoseProof (IMPL with "DUTY") as "[DUTY0 DUTY1]". iApply "DUTY0". }
      iPoseProof (duty_list_whites with "[DUTY]") as "# WHITES1".
      { iPoseProof (IMPL with "DUTY") as "[DUTY0 DUTY1]". iApply "DUTY1". }
      iIntros "H".
      iAssert (⌜forall r v0 v1 (IN0: In (r, v0) rs0) (IN1: In (r, v1) rs1), v0 = v1⌝)%I as "%".
      { iIntros (? ? ? ? ?).
        destruct a0 as [[[? ?] ?] ?]. destruct a1 as [[[? ?] ?] ?].
        iDestruct "H" as "[% [H SAT]]".
        iPoseProof (Region.white_agree with "[] []") as "%".
        { iApply "WHITES0". eauto. }
        { iApply "WHITES1". eauto. }
        clarify.
      }
      iAssert (P ∧ ((∀ r k c q x (IN0: List.In (r, (k, c, q, x)) rs0), OwnM ((FiniteMap.singleton x (OneShot.pending unit 1)))) ** (∀ r k c q x (IN: List.In (r, (k, c, q, x)) rs1), OwnM ((FiniteMap.singleton x (OneShot.pending unit 1))))))%I with "[DUTY]" as "DUTY".
      { iSplit; [auto|]. iPoseProof (IMPL with "DUTY") as "[DUTY0 DUTY1]".
        iSplitL "DUTY0".
        { iPoseProof (duty_list_pending with "DUTY0") as "[_ DUTY0]"; eauto. }
        { iPoseProof (duty_list_pending with "DUTY1") as "[_ DUTY1]"; eauto. }
      }
      iModIntro. iFrame. iSplit.
      { iPoseProof "DUTY" as "[DUTY _]"; auto. }
      { iPoseProof "DUTY" as "[_ [OWN0 OWN1]]".
        iIntros (? ? ?).
        apply in_map_iff in a0. des. destruct x as [? [[[? ?] ?] ?]].
        apply in_map_iff in a1. des. destruct x as [? [[[? ?] ?] ?]].
        ss. subst.
        hexploit H3; eauto. i. clarify.
        iPoseProof ("OWN0" $! _ _ _ _ _ a2) as "OWN0".
        iPoseProof ("OWN1" $! _ _ _ _ _ a3) as "OWN1".
        iCombine "OWN0 OWN1" as "OWN". iOwnWf "OWN".
        rewrite FiniteMap.singleton_add in H4.
        apply FiniteMap.singleton_wf in H4.
        rewrite <- OneShot.pending_sum in H4.
        apply OneShot.pending_wf in H4. apply Qp.not_add_le_r in H4. ss.
      }
    Qed.

    Lemma duty_list_nodup P i rs q
          (IMPL: P ⊢ (duty_list i rs q))
      :
      (P)
        -∗
        #=(arrows_sat)=> ((P) ** ⌜List.NoDup (List.map fst rs)⌝).
    Proof.
      revert q P IMPL. induction rs.
      { i. iIntros "H". iModIntro. iSplit; ss. iPureIntro. econs; ss. }
      i. destruct a as [? [[[? ?] ?] ?]].
      ss. iIntros "DUTY".
      iPoseProof (IHrs with "DUTY") as "> [DUTY %]".
      { etrans; eauto. iIntros "DUTY".
        iPoseProof (duty_list_unfold with "DUTY") as "[[# WHITE OWN] DUTY]". eauto.
      }
      iPoseProof (duty_list_whites with "[DUTY]") as "# WHITES".
      { iApply IMPL. auto. }
      iIntros "H".
      iAssert (⌜forall r k c q x (IN: List.In (r, (k, c, q, x)) rs), n <> r⌝)%I as "%".
      { iIntros (? ? ? ? ? IN ?). subst.
        iPoseProof (IMPL with "DUTY") as "DUTY".
        iPoseProof (duty_list_unfold with "DUTY") as "[[WHITE PENDING] DUTY]". eauto.
        iPoseProof "H" as "[% [H _]]".
        iPoseProof (Region.white_agree with "[] WHITE") as "%".
        { iApply "WHITES". iPureIntro. ss. eauto. }
        clarify. iPoseProof ("WHITES" $! _ _ _ _ _ (or_intror IN)) as "# WHITE1".
        iAssert (OwnM (FiniteMap.singleton n1 (OneShot.pending unit 1))) with "[DUTY]" as "OWN1".
        { iClear "WHITE1 WHITES". clear IHrs H3 IMPL.
          iStopProof. generalize (q + q0)%Qp. revert IN. induction rs; ss.
          { i. destruct a0 as [? [[[? ?] ?] ?]].
            iIntros "H". iPoseProof (duty_list_unfold with "H") as "[[_ OWN] DUTY]".
            des; clarify. iApply IHrs; eauto.
          }
        }
        iCombine "PENDING OWN1" as "OWN". iOwnWf "OWN".
        rewrite FiniteMap.singleton_add in H4.
        rewrite FiniteMap.singleton_wf in H4.
        rewrite <- OneShot.pending_sum in H4.
        apply OneShot.pending_wf in H4. apply Qp.not_add_le_r in H4. ss.
      }
      iSplitL "H".
      { eauto. }
      iModIntro. iSplit; auto.
      iPureIntro. econs; ss. ii. eapply in_map_iff in H5.
      des. destruct x as [? [[[? ?] ?] ?]]. ss. subst. eapply H4; eauto.
    Qed.

    Lemma duty_update n i l
      :
      (duty i l)
        -∗
        (tax l)
        -∗
        #=(arrows_sat)=> (duty i l ** FairRA.white p i n).
    Proof.
      iIntros "[% [% [[BLACK DUTY] %]]] TAX". subst.
      iPoseProof (duty_list_nodup with "DUTY") as "> [DUTY %]".
      { reflexivity. }
      iPoseProof (duty_list_whites with "DUTY") as "# WHITES".
      iApply (Region.updates with "[]").
      { instantiate (1:=List.map (fun '(r, (k, c, q, x)) => (r, (Prism.review p i, k, c, q, x))) rs).
        rewrite List.map_map. erewrite List.map_ext; [eauto|]. i. des_ifs.
      }
      { iIntros. apply in_map_iff in IN. des. des_ifs.
        iApply "WHITES". auto.
      }
      iIntros "SAT".
      iAssert (duty_list i rs q ** FairRA.black_ex p i 1%Qp) with "[DUTY BLACK SAT]" as "[DUTY BLACK]".
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
                      (List.map snd (List.map (fun '(r, (k, c, q0, x)) => (r, (Prism.review p i, k, c, q0, x))) rs)) ** FairRA.black p i a q)) with "[TAX BLACK]" as "> [REGION BLACK]".
      2:{ iModIntro. iFrame. iExists _, _. iFrame. iSplit; eauto. iExists _. iFrame. }
      rewrite <- H4. iStopProof. clear H3 H4. revert q. induction rs.
      { i. iIntros "[# WHITES [TAX BLACK]]". iModIntro. ss. iFrame. }
      { i. iIntros "[# WHITES [TAX BLACK]]". ss.
        destruct a0 as [? [[[? ?] ?] ?]]. ss.
        iPoseProof "TAX" as "[WHITE TAX]".
        replace (q0 + foldr (fun '(_, (_, _, q1, _)) q2 => (q1 + q2)%Qp) q rs)%Qp with (q + foldr (fun '(_, (_, _, q1, _)) q2 => (q1 + q2)%Qp) q0 rs)%Qp; cycle 1.
        { clear IHrs. revert q q0. induction rs; ss; i.
          { apply Qp.add_comm. }
          { destruct a0 as [? [[[? ?] ?] ?]].
            rewrite (IHrs q1 q0). rewrite (IHrs q1 q).
            rewrite Qp.add_assoc. rewrite Qp.add_assoc.
            f_equal. apply Qp.add_comm.
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

    Lemma duty_list_updating i rs q
      :
      (duty_list i rs q)
        -∗
        (FairRA.black_ex p i q)
        -∗
        (list_prop_sum (fun '(r, (k, c, q, x)) => white k (c × Ord.omega)%ord) rs)
        -∗
        #=(arrows_sat)=>
            (updating
               (Region.sat_list arrow (List.map snd (List.map (fun '(r, (k, c, q, x)) => (r, (Prism.review p i, k, c, q, x))) rs)))
               (FairRA.black_ex p i 1)
               (FairRA.black_ex p i 1)
               (duty_list i rs q ** FairRA.black_ex p i q)).
    Proof.
      iIntros "DUTY BLACK TAX".
      iPoseProof (duty_list_nodup with "DUTY") as "> [DUTY %]".
      { reflexivity. }
      iPoseProof (duty_list_whites with "DUTY") as "# WHITES".
      iIntros "SAT". iModIntro.
      iSplitL "SAT"; [auto|]. iIntros "SAT".
      iAssert (duty_list i rs q ** FairRA.black_ex p i 1%Qp) with "[DUTY BLACK SAT]" as "[DUTY BLACK]".
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
      iModIntro. iSplitL "BLACK"; [auto|].
      iAssert (⌜(fold_right (fun '(r, (k, c, q0, x)) q1 => (q0 + q1)%Qp) q rs = 1%Qp)⌝)%I as "%".
      { iPoseProof "DUTY" as "[DUTY %]". auto. }
      iIntros "[% BLACK]".
      iAssert (#=> (Region.sat_list
                      arrow
                      (List.map snd (List.map (fun '(r, (k, c, q0, x)) => (r, (Prism.review p i, k, c, q0, x))) rs)) ** FairRA.black p i a q)) with "[TAX BLACK]" as "> [REGION BLACK]".
      2:{ iModIntro. iFrame. iExists _. eauto. }
      rewrite <- H4. iStopProof. clear H3 H4. revert q. induction rs.
      { i. iIntros "[# WHITES [TAX BLACK]]". iModIntro. ss. iFrame. }
      { i. iIntros "[# WHITES [TAX BLACK]]". ss.
        destruct a0 as [? [[[? ?] ?] ?]]. ss.
        iPoseProof "TAX" as "[WHITE TAX]".
        replace (q0 + foldr (fun '(_, (_, _, q1, _)) q2 => (q1 + q2)%Qp) q rs)%Qp with (q + foldr (fun '(_, (_, _, q1, _)) q2 => (q1 + q2)%Qp) q0 rs)%Qp; cycle 1.
        { clear IHrs. revert q q0. induction rs; ss; i.
          { apply Qp.add_comm. }
          { destruct a0 as [? [[[? ?] ?] ?]].
            rewrite (IHrs q1 q0). rewrite (IHrs q1 q).
            rewrite Qp.add_assoc. rewrite Qp.add_assoc.
            f_equal. apply Qp.add_comm.
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

    Lemma list_app_disjoint_nodup A (l0 l1: list A)
          (NODUP0: List.NoDup l0)
          (NODUP1: List.NoDup l1)
          (DISJOINT: forall a (IN0: List.In a l0) (IN1: List.In a l1), False)
      :
      List.NoDup (l0 ++ l1).
    Proof.
      revert NODUP0 DISJOINT. induction l0; ss; i. inv NODUP0. econs; eauto.
      ii. apply in_app_iff in H3. des; ss. eapply DISJOINT; eauto.
    Qed.

    Lemma duties_updating os
      :
      (list_prop_sum (fun '(i, l) => duty i l ** tax l) os)
        -∗
        #=(arrows_sat)=>
            (updating
               arrows_sat
               (FairRA.blacks_of p (List.map fst os))
               (FairRA.blacks_of p (List.map fst os))
               (list_prop_sum (fun '(i, l) => duty i l) os)).
    Proof.
      iIntros "DUTY".
      iAssert (∃ (xs: list (Id * list (nat * (nat * Ord.t * Qp * nat)) * Qp)),
                  (⌜os = List.map (fun '(i, rs, q) => (i, List.map (fun '(r, (k, c, q, x)) => (k, c)) rs)) xs⌝)
                    **
                    (list_prop_sum (fun '(i, rs, q) =>
                                      (duty_list i rs q)
                                        **
                                        (list_prop_sum (fun '(r, (k, c, q, x)) => white k (c × Ord.omega)%ord) rs)
                                        **
                                        (FairRA.black_ex p i q)) xs))%I with "[DUTY]" as "[% [% ALL]]".
      { iStopProof. induction os; ss; i.
        { iIntros. iExists []. ss. }
        { destruct a as [i l].
          iIntros "[[[% [% [[BLACK DUTY] %]]] TAX] OS]".
          iPoseProof (IHos with "OS") as "[% [% OS]]". subst.
          iExists ((_, _, _)::_). ss. iSplit.
          { iPureIntro. eauto. }
          iFrame. clear IHos. iStopProof. induction rs; ss.
          destruct a as [? [[[? ?] ?] ?]].
          iIntros "TAX". iPoseProof (tax_cons_unfold with "TAX") as "[HD TL]".
          iPoseProof (IHrs with "TL") as "TL". iFrame.
        }
      }
      subst.
      set (l := List.concat (List.map (fun '(i, rs, q) => List.map (fun '(r, (k, c, q, x)) => (r, (Prism.review p i, k, c, q, x))) rs) xs)).

      iAssert (#=(arrows_sat)=>
                 ((list_prop_sum (fun '(i, rs, q) =>
                                    (duty_list i rs q)
                                      **
                                      (list_prop_sum (fun '(r, (k, c, q, x)) => white k (c × Ord.omega)%ord) rs)
                                      **
                                      (FairRA.black_ex p i q)) xs)
                    **
                    (⌜List.NoDup (List.map fst l)⌝))) with "[ALL]" as "> [ALL %]".
      { subst l. iStopProof. induction xs; ss.
        { iIntros. iModIntro. iSplit; ss. iPureIntro. econs; ss. }
        destruct a as [[i rs] q]. iIntros "[[[DUTY HD] BLACK] TL]".
        iPoseProof (IHxs with "TL") as "> [TL %]".
        iPoseProof (duty_list_nodup with "DUTY") as "> [DUTY %]".
        { reflexivity. }
        iAssert (#=(arrows_sat)=>
                   (((duty_list i rs q)
                       **
                       (list_prop_sum (fun '(i, rs, q) =>
                                         (duty_list i rs q)
                                           **
                                           (list_prop_sum (fun '(r, (k, c, q, x)) => white k (c × Ord.omega)%ord) rs)
                                           **
                                           (FairRA.black_ex p i q)) xs))
                      **
                      (⌜forall i0 rs0 q0 (IN: List.In (i0, rs0, q0) xs),
                            (forall r (IN0: List.In r (List.map fst rs)) (IN1: List.In r (List.map fst rs0)), False)⌝)))%I with "[DUTY TL]" as "> [[DUTY TL] %]".
        { clear IHxs H3 H4. iStopProof. induction xs; ss.
          { iIntros "[DUTY TL]". iModIntro. iSplit; auto. }
          destruct a as [[i0 rs0] q0].
          iIntros "[DUTY [HD TL]]".
          iPoseProof (IHxs with "[DUTY TL]") as "> [[DUTY TL] %]".
          { iFrame. }
          iCombine "HD DUTY" as "H".
          iPoseProof (duty_list_disjoint with "H") as "> [[HD DUTY] %]".
          { iIntros "[[[H0 _] _] H1]". iFrame. }
          iModIntro. iFrame. iPureIntro. i. des; clarify; eauto.
        }
        { iModIntro. iFrame. iPureIntro.
          rewrite List.map_app. apply list_app_disjoint_nodup; auto.
          { rewrite List.map_map. erewrite List.map_ext; eauto. i. des_ifs. }
          { i. rewrite List.concat_map in IN1.
            apply in_concat in IN1. des.
            rewrite List.map_map in IN1. rewrite List.in_map_iff in IN1. des. subst.
            rewrite List.in_map_iff in IN2. des. subst.
            destruct x0 as [[? ?] ?].
            rewrite List.in_map_iff in IN1. des. subst.
            destruct x0 as [? [[[? ?] ?] ?]]. ss.
            rewrite List.map_map in IN0.
            rewrite List.in_map_iff in IN0. des. subst.
            destruct x as [? [[[? ?] ?] ?]]. ss.
            eapply H5.
            { eauto. }
            { eapply in_map_iff. esplits; eauto. }
            { ss. eapply in_map_iff. esplits; eauto. ss. }
          }
        }
      }
      iAssert (#=(arrows_sat)=>
                 (((list_prop_sum (fun '(i, rs, q) =>
                                     (updating
                                        (Region.sat_list arrow (List.map snd (List.map (fun '(r, (k, c, q, x)) => (r, (Prism.review p i, k, c, q, x))) rs)))
                                        (FairRA.black_ex p i 1)
                                        (FairRA.black_ex p i 1)
                                        (duty_list i rs q ** FairRA.black_ex p i q)))) xs)
                    ** (∀ i rs q0 r k c q1 x
                          (IN0: List.In (i, rs, q0) xs)
                          (IN1: List.In (r, (k, c, q1, x)) rs),
                           Region.white r (Prism.review p i, k, c, q1, x)))) with "[ALL]" as "> [ALL WHITES]".
      { subst l. iStopProof. clear H3. induction xs.
        { iIntros. iModIntro. ss. iSplit; auto. iIntros. ss. }
        destruct a as [[i rs] q]. iIntros "[[[DUTY TAX] BLACK] DUTIES]".
        iPoseProof (IHxs with "DUTIES") as "> [DUTIES WHITES]".
        iPoseProof (duty_list_whites with "DUTY") as "# WHITE".
        iPoseProof (duty_list_updating with "DUTY BLACK TAX") as "> UPD".
        iModIntro. iSplitL "DUTIES UPD".
        { ss. iFrame. }
        { iIntros. ss. des; clarify.
          { iApply "WHITE"; auto. }
          { iApply "WHITES"; auto. }
        }
      }
      iModIntro.
      iApply (Region.sat_updating with "[WHITES] [ALL]").
      { instantiate (1:=l). subst l. auto. }
      { iIntros. subst l. apply List.in_concat in IN. des.
        apply in_map_iff in IN. des. destruct x0 as [[i rs] q]. subst.
        apply in_map_iff in IN0. des.
        destruct x as [? [[[? ?] ?] ?]]. clarify.
        iApply "WHITES"; eauto.
      }
      subst l. clear H3. iStopProof. induction xs.
      { ss. iIntros "_ SAT". iModIntro. ss. }
      destruct a as [[i rs] q]. ss.
      iIntros "[UPD UPDS]".
      iPoseProof (IHxs with "UPDS") as "UPDS".
      iIntros "SAT". repeat rewrite List.map_app.
      iPoseProof (Region.sat_list_split with "SAT") as "[SAT SATS]".
      iPoseProof ("UPD" with "SAT") as "> [BLACK K]".
      iPoseProof ("UPDS" with "SATS") as "> [BLACKS KS]".
      iModIntro. iSplitL "BLACK BLACKS".
      { iApply list_prop_sum_cons_fold. iFrame. }
      iIntros "BLACKS".
      iPoseProof (list_prop_sum_cons_unfold with "BLACKS") as "[BLACK BLACKS]".
      iPoseProof ("K" with "BLACK") as "> [SAT [BLACK DUTY]]".
      iPoseProof ("KS" with "BLACKS") as "> [SATS DUTIES]".
      iModIntro. iSplitL "SAT SATS".
      { iApply Region.sat_list_combine. iFrame. }
      { iFrame. iExists _, _. iFrame. eauto. }
    Qed.

    End PRISM.

    Lemma duty_prism_id Id (p: Prism.t S Id) i l
      :
      (duty p i l)
        -∗
        (duty Prism.id (Prism.review p i) l).
    Proof. auto. Qed.

    Lemma duty_prism_id_rev Id (p: Prism.t S Id) i l
      :
      (duty Prism.id (Prism.review p i) l)
        -∗
        (duty p i l).
    Proof. auto. Qed.
  End ARROW.

  Section ARROWTHREAD.
    Variable (S: Type).
    Context `{@GRA.inG t Σ}.
    Context `{@GRA.inG (FairRA.tgtt S) Σ}.
    Context `{@GRA.inG (@FiniteMap.t (OneShot.t unit)) Σ}.
    Context `{@GRA.inG (Region.t ((sum_tid S) * nat * Ord.t * Qp * nat)) Σ}.

    Definition correl_thread (k: nat) (c: Ord.t): iProp :=
      ∃ i, correl inlp i k c.

    Lemma correl_thread_persistent k c
      :
      correl_thread k c ⊢ □ correl_thread k c.
    Proof.
      iIntros "# H". auto.
    Qed.

    Global Program Instance Persistent_correl_thread k c: Persistent (correl_thread k c).

    Lemma correl_thread_correlate k c
      :
      (correl_thread k c)
        -∗
        (FairRA.white_thread (S := S))
        -∗
        (#=(arrows_sat (S := sum_tid S))=> (white k c ∨ shot k)).
    Proof.
      iIntros "[% CORR] WHITE".
      iApply (correl_correlate with "CORR WHITE").
    Qed.

    Lemma duty_correl_thread i l k c
          (IN: List.In (k, c) l)
      :
      (duty inlp i l)
        -∗
        (correl_thread k c).
    Proof.
      iIntros "DUTY".
      iPoseProof (duty_correl with "DUTY") as "# CORR"; [eauto|].
      iExists _. eauto.
    Qed.
  End ARROWTHREAD.


  Section TARGET.
    Variable (S: Type).
    Let Id := id_sum thread_id S.
    Context `{Σ: GRA.t}.
    Context `{@GRA.inG t Σ}.
    Context `{@GRA.inG (@FiniteMap.t (OneShot.t unit)) Σ}.
    Context `{@GRA.inG (Region.t (Id * nat * Ord.t * Qp * nat)) Σ}.
    Context `{@GRA.inG (@FairRA.tgtt S) Σ}.

    Lemma IUpd_open I P
      :
      (#=(I)=> P)
        -∗
        I
        -∗
        (#=> (I ** P)).
    Proof.
      iIntros "H0 H1". iPoseProof ("H0" with "H1") as "H". auto.
    Qed.

    Lemma target_update_thread
          (tid: thread_id) l
          ths
          (f0 f1: imap Id nat_wf)
          (UPD: fair_update f0 f1 (prism_fmap inlp (tids_fmap tid ths)))
      :
      (FairRA.sat_target f0 ths)
        -∗
        (duty inlp tid l ** tax l)
        -∗
        (#=(arrows_sat (S := Id))=>
           ((FairRA.sat_target f1 ths)
              **
              (duty inlp tid l)
              **
              FairRA.white_thread (S := S))).
    Proof.
      iIntros "SAT DUTY ARROWS".
      iPoseProof (duties_updating with "[DUTY]") as "UPD".
      { instantiate (1:=[(tid, l)]). ss. iFrame. }
      iPoseProof (IUpd_open with "UPD ARROWS") as "> [ARROWS UPD]".
      iPoseProof ("UPD" with "ARROWS") as "> [[BLACK _] K]".
      iPoseProof (FairRA.target_update_thread with "SAT BLACK") as "> [[SAT BLACK] WHITE]".
      { eauto. }
      iPoseProof ("K" with "[BLACK]") as "> [ARROWS [DUTY _]]".
      { iFrame. }
      iModIntro. iFrame.
    Qed.

    Lemma target_update A
          lf ls ths
          (p: Prism.t S A)
          (f0 f1: imap Id nat_wf)
          (fm: fmap A)
          (UPD: fair_update f0 f1 (prism_fmap (Prism.compose inrp p) fm))
          (SUCCESS: forall i (IN: fm i = Flag.success), List.In i (List.map fst ls))
          (FAIL: forall i (IN: List.In i lf), fm i = Flag.fail)
          (NODUP: List.NoDup lf)
      :
      (FairRA.sat_target f0 ths)
        -∗
        (list_prop_sum (fun '(i, l) => duty (Prism.compose inrp p) i l ** tax l) ls)
        -∗
        (#=(arrows_sat (S := Id))=>
           ((FairRA.sat_target f1 ths)
              **
              (list_prop_sum (fun '(i, l) => duty (Prism.compose inrp p) i l) ls)
              **
              (list_prop_sum (fun i => FairRA.white (Prism.compose inrp p) i 1) lf))).
    Proof.
      iIntros "SAT DUTY ARROWS".
      iPoseProof (duties_updating with "[DUTY]") as "UPD".
      { instantiate (1:=ls).
        clear SUCCESS. iStopProof.
        induction ls; ss.
      }
      iPoseProof (IUpd_open with "UPD ARROWS") as "> [ARROWS K]".
      iPoseProof ("K" with "ARROWS") as "> [BLACKS K]".
      iPoseProof (FairRA.target_update with "SAT [BLACKS]") as "> [[SAT BLACKS] WHITES]".
      { rewrite prism_fmap_compose in UPD. eauto. }
      { instantiate (1:=List.map (Prism.review p) (List.map fst ls)).
        i. unfold prism_fmap in IN. des_ifs.
        hexploit SUCCESS; eauto. i.
        eapply Prism.review_preview in Heq. subst.
        eapply in_map in H3. eauto.
      }
      { instantiate (1:=List.map (Prism.review p) lf).
        i. eapply in_map_iff in IN. des. subst.
        unfold prism_fmap. rewrite Prism.preview_review. eauto.
      }
      { eapply FinFun.Injective_map_NoDup; eauto.
        ii. eapply f_equal with (f:=Prism.preview p) in H3.
        rewrite ! Prism.preview_review in H3. clarify.
      }
      { clear SUCCESS. iStopProof.
        induction ls; ss. destruct a. ss. unfold FairRA.blacks_of. ss.
        iIntros "[HD TL]". iFrame. iApply IHls. auto.
      }
      iPoseProof ("K" with "[BLACKS]") as "> [ARROWS DUTY]".
      { clear SUCCESS. iStopProof.
        induction ls; ss. destruct a. iIntros "[HD TL]".
        iFrame. iApply IHls. auto.
      }
      iModIntro. iFrame.
      iApply (list_prop_sum_map_inv with "WHITES").
      i. iIntros "WHITE". iApply FairRA.white_prism_id_rev. auto.
    Qed.
  End TARGET.
End ObligationRA.
