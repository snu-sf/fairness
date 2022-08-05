From sflib Require Import sflib.
From Paco Require Import paco.
From Coq Require Export
  Relations.Relation_Operators.
From Coq Require Import
  RelationClasses
  Relations.Operators_Properties.
Set Implicit Arguments.

(* TODO: definitions copied from Ordinal library *)

Lemma well_founded_irrefl A (R : A -> A -> Prop) (WF : well_founded R) : forall x, ~ R x x.
Proof. ii. specialize (WF x). induction WF; eauto. Qed.

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

Variant option_lt A (R: A -> A -> Prop): option A -> option A -> Prop :=
  | optoin_lt_top
      a
    :
    option_lt R (Some a) None
  | optoin_lt_normal
      a0 a1
      (LT: R a0 a1)
    :
    option_lt R (Some a0) (Some a1)
.

Lemma option_lt_well_founded A (R: A -> A -> Prop)
      (WF: well_founded R)
  :
  well_founded (option_lt R).
Proof.
  cut (forall a, Acc (option_lt R) (Some a)).
  { ii. destruct a; ss. econs. i. inv H0; ss. }
  i. induction (WF a). econs.
  i. inv H1. eauto.
Qed.

Variant sum_lt
        A B (RA: A -> A -> Prop) (RB: B -> B -> Prop):
  A + B -> A + B -> Prop :=
  | sum_lt_left
      a0 a1
      (LT: RA a0 a1)
    :
    sum_lt RA RB (inl a0) (inl a1)
  | sum_lt_right
      b0 b1
      (LT: RB b0 b1)
    :
    sum_lt RA RB (inr b0) (inr b1)
  | sum_lt_cross
      a b
    :
    sum_lt RA RB (inl a) (inr b)
.

Lemma sum_lt_well_founded
      A B (RA: A -> A -> Prop) (RB: B -> B -> Prop)
      (WFA: well_founded RA)
      (WFB: well_founded RB)
  :
  well_founded (sum_lt RA RB).
Proof.
  assert (ACCA: forall a, Acc (sum_lt RA RB) (inl a)).
  { i. induction (WFA a). econs.
    i. inv H1. eauto.
  }
  ii. destruct a as [a|b]; eauto.
  induction (WFB b). econs.
  i. inv H1; eauto.
Qed.

Variant prod_lt
        A B (RA: A -> A -> Prop) (RB: B -> B -> Prop):
  A * B -> A * B -> Prop :=
  | prod_lt_left
      a0 a1 b0 b1
      (ALT: RA a0 a1)
    :
    prod_lt RA RB (a0, b0) (a1, b1)
  | prod_lt_right
      a0 a1 b0 b1
      (ALE: a0 = a1 \/ RA a0 a1)
      (BLT: RB b0 b1)
    :
    prod_lt RA RB (a0, b0) (a1, b1)
.

Lemma prod_lt_well_founded
      A B (RA: A -> A -> Prop) (RB: B -> B -> Prop)
      (WFA: well_founded RA)
      (WFB: well_founded RB)
  :
  well_founded (prod_lt RA RB).
Proof.
  ii. destruct a as [a b]. revert b.
  induction (WFA a). rename x into a. clear H. rename H0 into IHA.
  intros b. induction (WFB b). rename x into b. clear H. rename H0 into IHB.
  econs. i. inv H; eauto. des; subst; eauto.
Qed.

Inductive ord_tree (A: Type): Type :=
| ord_tree_base
| ord_tree_cons (childs: A -> ord_tree A)
.

Variant ord_tree_lt A: ord_tree A -> ord_tree A -> Prop :=
  | ord_tree_lt_intro
      childs a
    :
    ord_tree_lt (childs a) (ord_tree_cons childs)
.

Lemma ord_tree_lt_well_founded A
  :
  well_founded (@ord_tree_lt A).
Proof.
  ii. induction a.
  { econs; i. inv H. }
  { econs; i. inv H0. eauto. }
Qed.

From Fairness Require Import Axioms.

Lemma ord_tree_join A (P: A -> Prop) (R: A -> ord_tree A -> Prop)
      (ORD: forall a (SAT: P a), exists o, R a o)
  :
  exists o1, forall (a: A) (SAT: P a),
  exists o0, R a o0 /\ ord_tree_lt o0 o1.
Proof.
  hexploit (choice (fun a o => P a -> R a o)).
  { i. destruct (classic (P x)).
    { hexploit ORD; eauto. i. des. eauto. }
    { eexists (ord_tree_base _). ss. }
  }
  i. des. exists (ord_tree_cons f). i.
  exists (f a). splits; eauto. econs; eauto.
Qed.


Section WFTYPE.
  Record WF: Type :=
    mk_wf {
        T: Type;
        lt: (T -> T -> Prop);
        wf: well_founded lt;
        le: (T -> T -> Prop) := eq \2/ lt;
      }.

  Global Program Instance le_Reflexive {wf: WF}: Reflexive wf.(le).
  Next Obligation.
    unfold le. auto.
  Qed.

  Lemma WF_le_Trans
        wf
        (WFTR: Transitive wf.(lt))
    :
    Transitive wf.(le).
  Proof.
    unfold le. ii. destruct wf; ss. des; clarify; eauto.
  Qed.

End WFTYPE.

Definition ord_tree_WF {A}: WF := mk_wf (@ord_tree_lt_well_founded A).

Definition sum_WF (A B: WF): WF := mk_wf (sum_lt_well_founded A.(wf) B.(wf)).
Definition prod_WF (A B: WF): WF := mk_wf (prod_lt_well_founded A.(wf) B.(wf)).
