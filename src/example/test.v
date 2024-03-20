From sflib Require Import sflib.
(* From Fairness Require Import PCM IProp IPM MonotonePCM WFLibLarge Mod Optics. *)
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.PropExtensionality.
From Fairness Require Import Axioms.
Require Import Program List.

Set Implicit Arguments.
(* Set Universe Polymorphism. *)

From Fairness Require Import WFLib.
From Ordinal Require Import Ordinal Hessenberg ClassicalOrdinal.

Section TEST.

  Definition level (n: nat): Ord.t :=
    fold_left Jacobsthal.mult (repeat Ord.large n) Ord.one.
    (* fold_right Jacobsthal.mult Ord.one (repeat Ord.large n). *)

  Lemma level_red: forall n, level (S n) = ((level n) × Ord.large)%ord.
  Proof.
    unfold level. i. generalize Ord.one.
    induction n; ss.
  Qed.

Jacobsthal.lt_mult_r:
  forall [o0 o1 o2 : Ord.t], (o1 < o2)%ord -> (Ord.O < o0)%ord -> ((o0 × o1) < (o0 × o2))%ord

  (* Polymorphic Definition emb {A} {R: A -> A -> Prop} (wfa: well_founded R) (a: A): Ord.t := Ord.from_wf wfa a. *)
  (* Let ord_emb (o: Ord.t): Ord.t := emb Ord.lt_well_founded o. *)

  (* Definition ord_ord (o: Ord.t): Ord.t := Ord.from_wf Ord.lt_well_founded o. *)

  (* Definition leaf := Ord.t. *)
  (* Definition chain {A} := (A * leaf)%type. *)
  (* Definition embed {A} {R : A -> A -> Prop} {wfa : well_founded R} : (@chain A) -> leaf := *)
  (*   fun p => Ord.from_wf (prod_lt_well_founded wfa Ord.lt_well_founded) p. *)

prod_WF: WF -> WF -> WF

Ord.large_lt_from_wf_set:
  forall [A : Type] [R : A -> A -> Prop] (WF : well_founded R),
  (Ord.from_wf_set WF < Ord.large)%ord
Ord.large_lt_from_wf:
  forall [A : Type] [R : A -> A -> Prop] (WF : well_founded R) (a : A),
  (Ord.from_wf WF a < Ord.large)%ord

End TEST.
