From sflib Require Import sflib.
Require Import Coq.Classes.RelationClasses.
From iris.algebra Require Import cmra updates functions lib.excl_auth.

From Fairness Require Import Axioms NatStructsLarge.
From Fairness Require Import PCM.
From Fairness Require Import Mod.

Set Implicit Arguments.

(* Definition _thsRA {A: Type}: ucmra := Auth.t (Excl.t A). *)
Definition thsRA {A: Type}: ucmra := (thread_id ==> (excl_authUR $ leibnizO A))%ra.
(* Compute (URA.car (t:=_thsRA)). *)
(* Global Instance thsRA {A: Type}: ucmra := Auth.t (@_thsRA A). *)

Section THHAS.

  Definition ae_white {A} (a: A) := ◯E (a : leibnizO A).
  Definition ae_black {A} (a: A) := ●E (a : leibnizO A).

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
      ✓ (th_has tid0 a0 ⋅ th_has tid1 a1) -> tid0 <> tid1.
  Proof. ii. clarify. specialize (H tid1). rewrite discrete_fun_lookup_op !th_has_hit in H. ss. eapply excl_auth_frag_op_valid,H. Qed.

End THHAS.
Notation "tid |-> a" := (th_has tid a) (at level 20).
Global Opaque th_has.
