From sflib Require Import sflib.
From Fairness Require Import WFLibLarge Mod Optics.
From Fairness Require Import PCM IProp IPM IPropAux.
From Fairness Require Import NatMapRALarge MonotoneRA RegionRA.
Require Import Coq.Classes.RelationClasses.
From Fairness Require Import Axioms.
Require Import Program.
From Fairness Require Import FairnessRA IndexedInvariants.
From Fairness Require Export ObligationRA.
(* From Ordinal Require Export Ordinal Arithmetic Hessenberg ClassicalHessenberg. *)

Notation "'ω'" := Ord.omega.
(* Notation "'ω'" := Ord.omega : ord_scope. *)

Section LAYER.

  Import Jacobsthal Hessenberg.

  Fixpoint _olayer (l : nat) : Ord.t :=
    match l with
    | O => Ord.one
    | S m => (_olayer m × ω)%ord
    end.

  Lemma _olayer_S_eq l :
    _olayer (S l) = (_olayer l × ω)%ord.
  Proof. ss. Qed.

  Lemma _olayer_zero :
    _olayer O = 1%ord.
  Proof. ss. Qed.

  Lemma zero_lt_omega : (Ord.O < ω)%ord.
  Proof.
    eapply Ord.le_lt_lt; [| eapply Ord.omega_upperbound].
    eapply Ord.O_bot.
    Unshelve. exact 0.
  Qed.

  Lemma _olayer_lowerbound l :
    (0 < _olayer l)%ord.
  Proof.
    induction l. ss. apply Ord.S_pos.
    ss. eapply Ord.le_lt_lt.
    2:{ eapply Jacobsthal.lt_mult_r. apply zero_lt_omega. auto. }
    { rewrite Jacobsthal.mult_O_r. reflexivity. }
  Qed.

  Lemma _olayer_S_lt l :
    (_olayer l < _olayer (S l))%ord.
  Proof.
    ss. remember (_olayer l × ω)%ord as a. rewrite <- mult_1_r. subst.
    apply lt_mult_r. setoid_rewrite <- Ord.from_nat_1. apply Ord.omega_upperbound.
    apply _olayer_lowerbound.
  Qed.

  Lemma _olayer_lt l1 l2 :
    l1 < l2 -> (_olayer l1 < _olayer l2)%ord.
  Proof.
    intro LT. induction LT.
    { apply _olayer_S_lt. }
    etransitivity. eauto. apply _olayer_S_lt.
  Qed.

  Lemma _olayer_le l1 l2 :
    l1 <= l2 -> (_olayer l1 <= _olayer l2)%ord.
  Proof.
    intro LE. inv LE. reflexivity.
    apply Ord.lt_le. apply _olayer_lt. lia.
  Qed.

  Lemma _olayer_S_decr l :
    forall (a : nat), ((_olayer l × a) < _olayer (S l))%ord.
  Proof.
    i. ss. apply lt_mult_r. apply Ord.omega_upperbound. apply _olayer_lowerbound.
  Qed.

  Lemma _olayer_decr :
    forall l m (a : nat), (l < m) -> ((_olayer l × a) < _olayer m)%ord.
  Proof.
    i. induction H.
    { apply _olayer_S_decr. }
    etransitivity. eauto. apply _olayer_S_lt.
  Qed.


  Definition olayer (l a : nat) : Ord.t := (_olayer l × a)%ord.

  Lemma olayer_zero1 a :
    (olayer 0 a == a)%ord.
  Proof.
    unfold olayer. ss. rewrite mult_1_l. reflexivity.
  Qed.

  Lemma olayer_zero2 l :
    (olayer l 0 == 0)%ord.
  Proof.
    unfold olayer. rewrite mult_O_r. reflexivity.
  Qed.

  Lemma olayer_S_decr_one l :
    forall a, (olayer l a < olayer (S l) 1)%ord.
  Proof.
    i. unfold olayer. eapply Ord.lt_le_lt. apply _olayer_S_decr.
    rewrite mult_1_r. reflexivity.
  Qed.

  Lemma olayer_S_decr l :
    forall a b, (0 < b) -> (olayer l a < olayer (S l) b)%ord.
  Proof.
    i. unfold olayer. eapply Ord.lt_le_lt. apply _olayer_S_decr.
    etransitivity. rewrite <- mult_1_r. reflexivity.
    apply le_mult_r. setoid_rewrite <- Ord.from_nat_1. apply OrdArith.le_from_nat. auto.
  Qed.

  Lemma olayer_decr :
    forall l m (LT : l < m) a b, (0 < b) -> (olayer l a < olayer m b)%ord.
  Proof.
    intros l m LT. induction LT; i.
    { apply olayer_S_decr. auto. }
    etransitivity. eapply IHLT; eauto.
    apply olayer_S_decr. auto.
  Qed.

  Lemma olayer_split l :
    forall a b, (olayer l (a + b) == (olayer l a ⊕ olayer l b))%ord.
  Proof.
    i. unfold olayer. rewrite <- ClassicJacobsthal.mult_dist.
    apply eq_mult_r. rewrite <- add_from_nat. reflexivity.
  Qed.

  Lemma olayer_split_le l :
    forall a b c, (a + b <= c) -> ((olayer l a ⊕ olayer l b) <= olayer l c)%ord.
  Proof.
    i. unfold olayer. rewrite <- ClassicJacobsthal.mult_dist.
    apply le_mult_r. rewrite <- add_from_nat. apply OrdArith.le_from_nat. auto.
  Qed.

End LAYER.
Global Opaque _olayer.
Global Opaque olayer.


