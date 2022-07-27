From sflib Require Import sflib.
From Coq Require Export
  Relations.Relation_Operators.
From Coq Require Import
  RelationClasses
  Relations.Operators_Properties.
Set Implicit Arguments.

(* TODO: definitions copied from Ordinal library *)

Variant succ_rel (n : nat) : nat -> Prop := succ_rel_intro : succ_rel n (S n).

Lemma succ_rel_well_founded : well_founded succ_rel.
Proof. ii. induction a; econs; i; inversion H. ss. Qed.

Lemma succ_clos_trans : forall m n, clos_trans_n1 nat succ_rel m n <-> m < n.
Proof.
  split.
  - revert m. induction n.
    + i. exfalso. inversion H; inversion H0.
    + i. inversion H.
      * inversion H0. ss.
      * inversion H0. subst. econs. eapply IHn, H1.
  - revert m. induction n.
    + i. inversion H.
    + i. inversion H.
      * econs 1. econs.
      * econs 2. econs. eapply IHn. ss.
Qed.

Variant double_rel A B (RA: A -> A -> Prop) (RB: B -> B -> Prop)
  : A * B -> A * B -> Prop :=
| double_rel_left a0 a1 b (LT: RA a0 a1): double_rel RA RB (a0, b) (a1, b)
| double_rel_right a b0 b1 (LT: RB b0 b1): double_rel RA RB (a, b0) (a, b1)
.

Lemma double_rel_well_founded A B (RA: A -> A -> Prop) (RB: B -> B -> Prop)
      (WFA: well_founded RA) (WFB: well_founded RB)
  :
  well_founded (double_rel RA RB).
Proof.
  cut (forall a b, Acc (double_rel RA RB) (a, b)).
  { ii. destruct a as [a b]. eapply H. }
  intros a0. pattern a0. revert a0.
  eapply (well_founded_induction WFA).
  intros a0 IHL. intros b0. pattern b0. revert b0.
  eapply (well_founded_induction WFB).
  intros b0 IHR. econs. intros [a1 b1]. i. inv H.
  { eapply IHL; eauto. }
  { eapply IHR; eauto. }
Qed.

Lemma double_well_founded_induction A B (RA: A -> A -> Prop) (RB: B -> B -> Prop)
      (WFA: well_founded RA) (WFB: well_founded RB)
      (P: A -> B -> Prop)
      (IND: forall a1 b1
                   (IHL: forall a0 (LT: RA a0 a1), P a0 b1)
                   (IHR: forall b0 (LT: RB b0 b1), P a1 b0),
          P a1 b1)
  :
  forall a b, P a b.
Proof.
  cut (forall ab, P (fst ab) (snd ab)).
  { i. apply (H (a, b)). }
  intros ab. pattern ab. revert ab.
  eapply (well_founded_induction (double_rel_well_founded WFA WFB)).
  intros [a b] ?. ss. eapply IND.
  { i. eapply (H (a0, b)). econstructor 1. auto. }
  { i. eapply (H (a, b0)). econstructor 2. auto. }
Qed.

Lemma clos_trans_well_founded
      A (R: A -> A -> Prop) (WF: well_founded R)
  :
    well_founded (clos_trans_n1 _ R).
Proof.
  ii. hexploit (well_founded_induction WF (fun a1 => forall a0 (LT: clos_trans_n1 A R a0 a1 \/ a0 = a1), Acc (clos_trans_n1 A R) a0)).
  { clear a. intros a1 IH. i. econs. i. des.
    - inv LT.
      + eapply IH; eauto.
      + eapply IH; eauto. left.
        eapply Operators_Properties.clos_trans_tn1. econs 2.
        * eapply Operators_Properties.clos_tn1_trans; eauto.
        * eapply Operators_Properties.clos_tn1_trans; eauto.
    - subst. inv H; eauto.
  }
  { right. reflexivity. }
  { eauto. }
Qed.

Lemma clos_trans_step A (R : A -> A -> Prop) x y : clos_trans_n1 _ R x y -> exists z, R z y /\ (x = z \/ clos_trans_n1 _ R x z).
Proof. i. destruct H; eauto. Qed.

Lemma clos_trans_n1_trans A (R : A -> A -> Prop) : Transitive (clos_trans_n1 _ R).
Proof.
  unfold Transitive. i.
  eapply clos_trans_tn1_iff.
  econs 2; eapply clos_trans_tn1_iff; eauto.
Qed.
