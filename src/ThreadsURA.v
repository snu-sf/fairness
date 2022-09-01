From sflib Require Import sflib.
Require Import Coq.Classes.RelationClasses.
From Fairness Require Import Axioms NatStructs.
From Fairness Require Import PCM.
From Fairness Require Import Mod.

Set Implicit Arguments.

(* Definition _thsRA {A: Type}: URA.t := Auth.t (Excl.t A). *)
Global Instance thsRA {A: Type}: URA.t := (thread_id ==> Auth.t (Excl.t A))%ra.
(* Compute (URA.car (t:=_thsRA)). *)
(* Global Instance thsRA {A: Type}: URA.t := Auth.t (@_thsRA A). *)

Section THHAS.

  Definition ae_white {A} (a: A) := @Auth.white (Excl.t A) (Some a).
  Definition ae_black {A} (a: A) := @Auth.black (Excl.t A) (Some a).

  Definition th_has {A: Type} (tid: thread_id) (a: A): (@thsRA A) :=
    fun _tid => if (tid_dec _tid tid) then ae_white a else ε.

  Lemma unfold_th_has {A} tid (a: A):
    th_has tid a = fun _tid => if (tid_dec _tid tid) then ae_white a else ε.
  Proof. reflexivity. Qed.

  (* Definition th_has {A: Type} (tid: thread_id) (a: A): @thsRA A := Auth.black (_th_has tid a). *)

  (* properties *)
  Lemma th_has_hit {A: Type}: forall tid (a: A), (th_has tid a) tid = ae_white a.
  Proof. i. rewrite unfold_th_has. des_ifs. Qed.

  Lemma th_has_miss {A: Type}: forall tid tid' (MISS: tid <> tid') (a: A), (th_has tid a tid') = ε.
  Proof. i. rewrite unfold_th_has. des_ifs. Qed.

  Lemma th_has_disj {A: Type}: forall tid0 tid1 (a0 a1: A),
      URA.wf (th_has tid0 a0 ⋅ th_has tid1 a1) -> tid0 <> tid1.
  Proof. ii. do 2 ur in H. clarify. specialize (H tid1). rewrite !th_has_hit in H. ss. ur in H. ss. Qed.

End THHAS.
Notation "tid |-> a" := (th_has tid a) (at level 20).
Global Opaque th_has.

(* black + delta --> new_black *)
Definition add_delta_to_black `{M: URA.t} (b: Auth.t M) (w: Auth.t _): Auth.t _ :=
  match b, w with
  | Auth.excl e _, Auth.frag f1 => Auth.black (e ⋅ f1)
  | _, _ => Auth.boom
  end
.
