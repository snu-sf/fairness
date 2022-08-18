From sflib Require Import sflib.
Require Import Coq.Classes.RelationClasses.
From Fairness Require Import Axioms NatStructs.
From Fairness Require Import PCM.
From Fairness Require Import Mod.
Require Import String Lia.

Set Implicit Arguments.

Let _thsRA {A: Type}: URA.t := (thread_id ==> (Excl.t A))%ra.
Compute (URA.car (t:=_thsRA)).
Instance thsRA {A: Type}: URA.t := Auth.t (@_thsRA A).
Compute (URA.car).

Section THHAS.

  Definition _th_has {A: Type} (tid: thread_id) (a: A): (@_thsRA A) :=
    fun _tid => if (tid_dec _tid tid) then (Some a) else ε.

  Lemma unfold_th_has A tid (a: A):
    _th_has tid a = fun _tid => if (tid_dec _tid tid) then (Some a) else ε.
  Proof. reflexivity. Qed.

  Definition th_has {A: Type} (tid: thread_id) (a: A): thsRA := Auth.white (_th_has tid a).

  (* properties *)
  Lemma _th_has_hit (A: Type): forall tid (a: A), (_th_has tid a) tid = Some a.
  Proof. i. unfold _th_has. des_ifs. Qed.

  Lemma _th_has_miss (A: Type): forall tid tid' (MISS: tid <> tid') (a: A), (_th_has tid a tid') = ε.
  Proof. i. unfold _th_has. des_ifs. Qed.

  Lemma _th_has_disj (A: Type): forall tid0 tid1 (a0 a1: A),
      URA.wf (_th_has tid0 a0 ⋅ _th_has tid1 a1) -> tid0 <> tid1.
  Proof.
    ii. do 2 ur in H. specialize (H tid0). rewrite _th_has_hit in H.
    rewrite unfold_th_has in H. ss. ur in H. des_ifs_safe. des_ifs; bsimpl; des; des_sumbool; subst; Ztac; try lia.
    assert(ofs0 = ofs1) by lia. subst. rewrite Z.sub_diag in *. ss.
  Qed.

End THHAS.
Notation "tid |-> a" := (th_has tid a) (at level 20).
Global Opaque _th_has.

Local Open Scope nat_scope.


(* black + delta --> new_black *)
Definition add_delta_to_black `{M: URA.t} (b: Auth.t M) (w: Auth.t _): Auth.t _ :=
  match b, w with
  | Auth.excl e _, Auth.frag f1 => Auth.excl (e ⋅ f1) URA.unit
  | _, _ => Auth.boom
  end
.


(* (*** TODO: move to Coqlib ***) *)
(* Lemma repeat_nth_some *)
(*       X (x: X) sz ofs *)
(*       (IN: ofs < sz) *)
(*   : *)
(*     nth_error (repeat x sz) ofs = Some x *)
(* . *)
(* Proof. *)
(*   ginduction sz; ii; ss. *)
(*   - lia. *)
(*   - destruct ofs; ss. exploit IHsz; et. lia. *)
(* Qed. *)

(* Lemma repeat_nth_none *)
(*       X (x: X) sz ofs *)
(*       (IN: ~(ofs < sz)) *)
(*   : *)
(*     nth_error (repeat x sz) ofs = None *)
(* . *)
(* Proof. *)
(*   generalize dependent ofs. induction sz; ii; ss. *)
(*   - destruct ofs; ss. *)
(*   - destruct ofs; ss. { lia. } hexploit (IHsz ofs); et. lia. *)
(* Qed. *)

(* Lemma repeat_nth *)
(*       X (x: X) sz ofs *)
(*   : *)
(*     nth_error (repeat x sz) ofs = if (ofs <? sz) then Some x else None *)
(* . *)
(* Proof. *)
(*   des_ifs. *)
(*   - eapply repeat_nth_some; et. apply_all_once Nat.ltb_lt. ss. *)
(*   - eapply repeat_nth_none; et. apply_all_once Nat.ltb_ge. lia. *)
(* Qed. *)



Ltac Ztac := all_once_fast ltac:(fun H => first[apply Z.leb_le in H|apply Z.ltb_lt in H|apply Z.leb_gt in H|apply Z.ltb_ge in H|idtac]).


