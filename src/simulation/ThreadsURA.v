From sflib Require Import sflib.
From iris.algebra Require Import cmra updates functions lib.excl_auth.

From Fairness Require Import Mod.

Set Implicit Arguments.

Definition excl_authUR A : ucmra := (excl_authUR $ leibnizO A).

Definition thsRA {A: Type}: ucmra := thread_id -d> (excl_authUR A).

Definition excl_auth_auth {A : Type} (a : A) : excl_authUR A :=
  (●E (a : leibnizO A)).
Definition excl_auth_frag {A : Type} (a : A) : excl_authUR A :=
  (◯E (a : leibnizO A)).

Global Typeclasses Opaque excl_auth_auth excl_auth_frag.

Global Instance: Params (@excl_auth_auth) 1 := {}.
Global Instance: Params (@excl_auth_frag) 2 := {}.

Local Notation "●E a" := (excl_auth_auth a) (at level 10).
Local Notation "◯E a" := (excl_auth_frag a) (at level 10).

Section THHAS.

  Definition ae_white {A} (a: A) : excl_authUR A := ◯E a.
  Definition ae_black {A} (a: A) : excl_authUR A := ●E a.

  Lemma ae_white_black_agree {A} (a b : A) :
    ✓ (ae_black a ⋅ ae_white b) → a = b.
  Proof. by intros ->%excl_auth_agree. Qed.

  Lemma ae_white_op_valid {A} (a a' : A) :
    ✓ (ae_white a ⋅ ae_white a') → False.
  Proof. apply excl_auth_frag_op_valid. Qed.

  Lemma ae_black_white_valid {A} (a : A) :
    ✓ (ae_black a ⋅ ae_white a).
  Proof. apply excl_auth_valid. Qed.

  Lemma ae_black_white_extend {A} (a a' : A) (b : excl_authUR A) :
    ✓ (ae_black a ⋅ ae_white a ⋅ b) →
    ✓ (ae_black a' ⋅ ae_white a' ⋅ b).
  Proof. apply cmra_discrete_total_update,excl_auth_update. Qed.

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
  Proof. ii. clarify. specialize (H tid1). rewrite discrete_fun_lookup_op !th_has_hit in H. by eapply ae_white_op_valid. Qed.

End THHAS.
Notation "tid |-> a" := (th_has tid a) (at level 20).
Global Opaque th_has ae_black ae_white.
