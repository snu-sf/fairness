From sflib Require Import sflib.
From ITree Require Export ITree.
From Paco Require Import paco.

Export ITreeNotations.

Require Import Coq.Classes.RelationClasses.

Set Implicit Arguments.

Module Flag.

  Variant t: Type :=
  | fail
  | emp
  | success
  .

  Definition le: t -> t -> Prop :=
    fun f0 f1 =>
      match f0, f1 with
      | fail, _ => True
      | _, fail => False
      | emp, _ => True
      | _, emp => False
      | success, _ => True
      end.

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
    ii. destruct x; ss.
  Qed.
  Next Obligation.
    ii. destruct x, y, z; ss.
  Qed.

End Flag.

Class ID : Type := mk { id: Type }.

Section EVENT.

  Context {Ident: ID}.

  Variant eventE: Type -> Type :=
    | Choose (X: Type): eventE X
    | Fair (m: Ident.(id) -> Flag.t): eventE unit
  .

End EVENT.



Module Tr.
  CoInductive t: Type :=
  | done
  | spin
  .
End Tr.

Section BEHAVES.

  (* Variable Ident: Type. *)
  Context {Ident: ID}.

  Inductive terminate
            (R: Type)
    :
    forall (itr: itree eventE R), Prop :=
  | terminate_ret
      r
    :
    terminate (Ret r)
  | terminate_tau
      itr
      (DIV: terminate itr)
    :
    terminate (Tau itr)
  | terminate_choose
      X ktr x
      (DIV: terminate (ktr x))
    :
    terminate (Vis (Choose X) ktr)
  | terminate_fair
      m ktr
      (DIV: terminate (ktr tt))
    :
    terminate (Vis (Fair m) ktr)
  .

  Variant _diverge_index
          (diverge_index: forall (R: Type) (idx: Ident.(id) -> nat) (itr: itree eventE R), Prop)
          (R: Type)
    :
    forall (idx: Ident.(id) -> nat) (itr: itree eventE R), Prop :=
  | diverge_index_tau
      itr idx0 idx1
      (DIV: diverge_index _ idx1 itr)
      (IDX: forall i, idx1 i <= idx0 i)
    :
    _diverge_index diverge_index idx0 (Tau itr)
  | diverge_index_choose
      X ktr x idx0 idx1
      (DIV: diverge_index _ idx1 (ktr x))
      (IDX: forall i, idx1 i <= idx0 i)
    :
    _diverge_index diverge_index idx0 (Vis (Choose X) ktr)
  | diverge_index_fair
      m ktr idx0 idx1
      (DIV: diverge_index _ idx1 (ktr tt))
      (EMP: forall j (IDX: (m j) = Flag.emp), idx1 j <= idx0 j)
      (FAIL: forall j (IDX: (m j) = Flag.fail), idx1 j < idx0 j)
    :
    _diverge_index diverge_index idx0 (Vis (Fair m) ktr)
  .

  Lemma diverge_index_mon: monotone3 _diverge_index.
  Proof.
    ii. inv IN.
    - econs 1; eauto.
    - econs 2; eauto.
    - econs 3; eauto.
  Qed.

  Definition diverge_index: forall (R: Type) (idx: Ident.(id) -> nat) (itr: itree eventE R), Prop := paco3 _diverge_index bot3.

  Definition diverge (R: Type) (itr: itree eventE R): Prop :=
    exists idx, diverge_index idx itr.

End BEHAVES.
