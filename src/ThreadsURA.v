From sflib Require Import sflib.
Require Import Coq.Classes.RelationClasses.
From Fairness Require Import Axioms NatStructs.
From Fairness Require Import PCM.
From Fairness Require Import Mod.

Set Implicit Arguments.

Definition _thsRA {A: Type}: URA.t := (thread_id ==> (Excl.t A))%ra.
Compute (URA.car (t:=_thsRA)).
Global Instance thsRA {A: Type}: URA.t := Auth.t (@_thsRA A).
Compute (URA.car).

Section THHAS.

  Definition _th_has {A: Type} (tid: thread_id) (a: A): (@_thsRA A) :=
    fun _tid => if (tid_dec _tid tid) then (Some a) else ε.

  Lemma unfold_th_has {A} tid (a: A):
    _th_has tid a = fun _tid => if (tid_dec _tid tid) then (Some a) else ε.
  Proof. reflexivity. Qed.

  Definition th_has {A: Type} (tid: thread_id) (a: A): @thsRA A := Auth.white (_th_has tid a).

  (* properties *)
  Lemma _th_has_hit {A: Type}: forall tid (a: A), (_th_has tid a) tid = Some a.
  Proof. i. rewrite unfold_th_has. unfold _th_has. des_ifs. Qed.

  Lemma _th_has_miss {A: Type}: forall tid tid' (MISS: tid <> tid') (a: A), (_th_has tid a tid') = ε.
  Proof. i. rewrite unfold_th_has. des_ifs. Qed.

  Lemma _th_has_disj {A: Type}: forall tid0 tid1 (a0 a1: A),
      URA.wf (_th_has tid0 a0 ⋅ _th_has tid1 a1) -> tid0 <> tid1.
  Proof. ii. do 2 ur in H. clarify. specialize (H tid1). rewrite !_th_has_hit in H. ss. Qed.

End THHAS.
Notation "tid |-> a" := (th_has tid a) (at level 20).
Global Opaque _th_has.

(* black + delta --> new_black *)
Definition add_delta_to_black `{M: URA.t} (b: Auth.t M) (w: Auth.t _): Auth.t _ :=
  match b, w with
  | Auth.excl e _, Auth.frag f1 => Auth.black (e ⋅ f1)
  | _, _ => Auth.boom
  end
.
