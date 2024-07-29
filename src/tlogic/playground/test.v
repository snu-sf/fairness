From sflib Require Import sflib.
(* From Fairness Require Import PCM IPM MonotonePCM WFLibLarge Mod Optics. *)
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.PropExtensionality.
From Fairness Require Import Axioms.
Require Import Program List.

Set Implicit Arguments.
(* Set Universe Polymorphism. *)

From Fairness Require Import WFLib.
From Ordinal Require Import Ordinal Hessenberg ClassicalOrdinal.

Section TEST.

  Definition level (n : nat) : Ord.t :=
    fold_left Jacobsthal.mult (repeat Ord.large n) Ord.one.
    (* fold_right Jacobsthal.mult Ord.one (repeat Ord.large n). *)

  Lemma large_lt_zero : (Ord.O < Ord.large)%ord.
  Proof.
    eapply Ord.le_lt_lt; [| eapply Ord.large_lt_from_wf].
    rewrite <- (Ord.from_nat_from_peano_lt O). eapply Ord.O_bot.
  Qed.

  Lemma large_dec_omega : (Ord.omega < Ord.large)%ord.
  Proof.
    rewrite Ord.omega_from_peano_lt_set. eapply Ord.large_lt_from_wf_set.
  Qed.

  Lemma large_dec_nat : forall (n : nat), (n < Ord.large)%ord.
  Proof.
    etransitivity. 2: apply large_dec_omega. apply Ord.omega_upperbound.
  Qed.

  Lemma level_red_zero : level 0 = Ord.one.
  Proof.
    ss.
  Qed.

  Lemma level_red_succ : forall n, level (S n) = ((level n) × Ord.large)%ord.
  Proof.
    unfold level. i. generalize Ord.one.
    induction n; auto. i. simpl in *. apply IHn.
  Qed.

  Lemma level_lt_zero : forall n, (Ord.O < level n)%ord.
  Proof.
    induction n.
    { rewrite level_red_zero. apply Ord.S_pos. }
    { rewrite level_red_succ. eapply Ord.le_lt_lt.
      2:{ eapply Jacobsthal.lt_mult_r. apply large_lt_zero. auto. }
      { rewrite Jacobsthal.mult_O_r. reflexivity. }
    }
  Qed.

  Lemma level_dec_wf_set :
    forall {A} {R : A -> A -> Prop} (WF : well_founded R) n, (((level n) × (Ord.from_wf_set WF)) < level (S n))%ord.
  Proof.
    i. rewrite level_red_succ. apply Jacobsthal.lt_mult_r; [|apply level_lt_zero].
    apply Ord.large_lt_from_wf_set.
  Qed.

  Lemma level_dec_wf :
    forall {A} {R : A -> A -> Prop} (WF : well_founded R) (a : A) n, (((level n) × (Ord.from_wf WF a)) < level (S n))%ord.
  Proof.
    i. etransitivity. 2: eapply level_dec_wf_set.
    eapply Jacobsthal.lt_mult_r. apply Ord.from_wf_set_upperbound. apply level_lt_zero.
  Qed.

  Lemma level_dec_omega : forall n, (((level n) × Ord.omega) < level (S n))%ord.
  Proof.
    i. rewrite Ord.omega_from_peano_lt_set. apply level_dec_wf_set.
  Qed.

  Lemma level_dec_nat : forall (a n : nat), (((level n) × a) < level (S n))%ord.
  Proof.
    i. rewrite (Ord.from_nat_from_peano_lt a). apply level_dec_wf.
  Qed.

  Lemma level_lt_succ : forall n, (level n < level (S n))%ord.
  Proof.
    induction n; i.
    - rewrite level_red_succ. rewrite level_red_zero. rewrite Jacobsthal.mult_1_l.
      eapply Ord.le_lt_lt. 2: apply (large_dec_nat 1). reflexivity.
    - rewrite (level_red_succ (S n)). rewrite <- Jacobsthal.mult_1_r at 1.
      apply Jacobsthal.lt_mult_r. 2: apply level_lt_zero.
      apply (large_dec_nat 1).
  Qed.

  Lemma level_le: forall n m, (n <= m) -> (level n <= level m)%ord.
  Proof.
    i. revert n H. induction m; i.
    - apply Le.le_n_0_eq in H. subst. reflexivity.
    - inv H. reflexivity.
      etransitivity.
      2:{ eapply Ord.lt_le. apply level_lt_succ. }
      auto.
  Qed.

  Lemma level_lt: forall n m, (n < m) -> (level n < level m)%ord.
  Proof.
    i. revert n H. induction m; i.
    - apply PeanoNat.Nat.nle_succ_0 in H. inversion H.
    - apply (PeanoNat.Nat.lt_succ_r n m) in H. eapply Ord.le_lt_lt.
      2: apply level_lt_succ.
      apply level_le; auto.
  Qed.



  Let mytype := (nat * nat)%type.
  Let mywf := prod_lt_well_founded PeanoNat.Nat.lt_wf_0 (@ord_tree_lt_well_founded mytype).

  Goal (((level 3) × (Ord.from_wf_set mywf)) < level 4)%ord.
  Proof.
    apply level_dec_wf_set.
  Qed.

Jacobsthal.lt_mult_r:
  forall [o0 o1 o2 : Ord.t], (o1 < o2)%ord -> (Ord.O < o0)%ord -> ((o0 × o1) < (o0 × o2))%ord

Hessenberg.add
prod_WF: WF -> WF -> WF

Ord.large_lt_from_wf_set:
  forall [A : Type] [R : A -> A -> Prop] (WF : well_founded R),
  (Ord.from_wf_set WF < Ord.large)%ord
Ord.large_lt_from_wf:
  forall [A : Type] [R : A -> A -> Prop] (WF : well_founded R) (a : A),
  (Ord.from_wf WF a < Ord.large)%ord
Ord.from_wf_set_upperbound:
  forall [A : Type] [R : A -> A -> Prop] (WF : well_founded R) (a : A), (Ord.from_wf WF a < Ord.from_wf_set WF)%ord


  (* Polymorphic Definition emb {A} {R: A -> A -> Prop} (wfa: well_founded R) (a: A): Ord.t := Ord.from_wf wfa a. *)
  (* Let ord_emb (o: Ord.t): Ord.t := emb Ord.lt_well_founded o. *)

  (* Definition ord_ord (o: Ord.t): Ord.t := Ord.from_wf Ord.lt_well_founded o. *)

  (* Definition leaf := Ord.t. *)
  (* Definition chain {A} := (A * leaf)%type. *)
  (* Definition embed {A} {R : A -> A -> Prop} {wfa : well_founded R} : (@chain A) -> leaf := *)
  (*   fun p => Ord.from_wf (prod_lt_well_founded wfa Ord.lt_well_founded) p. *)

End TEST.
