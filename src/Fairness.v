From sflib Require Import sflib.
From ITree Require Export ITree.
From Paco Require Import paco.

Export ITreeNotations.

Require Import Coq.Classes.RelationClasses.

Set Implicit Arguments.

Variable Ident: Type.

Variant eventE: Type -> Type :=
| Choose (X: Type): eventE X
| Success (i: Ident): eventE unit
| Fail (i: Ident): eventE unit
.

Module Tr.
  CoInductive t: Type :=
  | done
  | spin
  .
End Tr.

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

Section BEHAVES.
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
  | terminate_success
      i ktr
      (DIV: terminate (ktr tt))
    :
    terminate (Vis (Success i) ktr)
  | terminate_fail
      i ktr
      (DIV: terminate (ktr tt))
    :
    terminate (Vis (Fail i) ktr)
  .

  Variant _diverge_index
          (diverge_index: forall (R: Type) (idx: Ident -> nat) (itr: itree eventE R), Prop)
          (R: Type)
    :
    forall (idx: Ident -> nat) (itr: itree eventE R), Prop :=
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
  | diverge_index_success
      i ktr idx0 idx1
      (DIV: diverge_index _ idx1 (ktr tt))
      (IDX: forall j (NEQ: j <> i), idx1 j <= idx0 j)
    :
    _diverge_index diverge_index idx0 (Vis (Success i) ktr)
  | diverge_index_fail
      i ktr idx0 idx1
      (DIV: diverge_index _ idx1 (ktr tt))
      (IDX: forall j (NEQ: j <> i), idx1 j <= idx0 j)
      (DECR: idx1 i < idx0 i)
    :
    _diverge_index diverge_index idx0 (Vis (Fail i) ktr)
  .

  Lemma diverge_index_mon: monotone3 _diverge_index.
  Proof.
    ii. inv IN.
    - econs 1; eauto.
    - econs 2; eauto.
    - econs 3; eauto.
    - econs 4; eauto.
  Qed.

  Definition diverge_index: forall (R: Type) (idx: Ident -> nat) (itr: itree eventE R), Prop := paco3 _diverge_index bot3.

  Definition diverge (R: Type) (itr: itree eventE R): Prop :=
    exists idx, diverge_index idx itr.

  Inductive _diverge_flag
            (diverge_flag: forall (R: Type) (b: bool) (f: Ident -> Flag.t) (itr: itree eventE R), Prop)
            (R: Type)
    :
    forall (b: bool) (f: Ident -> Flag.t) (itr: itree eventE R), Prop :=
  | diverge_flag_tau
      itr b f0 f1
      (DIV: _diverge_flag _ true f1 itr)
      (FLAG: forall i, Flag.le (f1 i) (f0 i))
    :
    _diverge_flag diverge_flag b f0 (Tau itr)
  | diverge_flag_choose
      X ktr x b f0 f1
      (DIV: _diverge_flag _ true f1 (ktr x))
      (FLAG: forall i, Flag.le (f1 i) (f0 i))
    :
    _diverge_flag diverge_flag b f0 (Vis (Choose X) ktr)
  | diverge_flag_success
      i ktr b f0 f1
      (DIV: _diverge_flag _ true f1 (ktr tt))
      (FLAG: forall j (NEQ: j <> i), Flag.le (f1 j) (f0 j))
    :
    _diverge_flag diverge_flag b f0 (Vis (Success i) ktr)
  | diverge_flag_fail
      i ktr b f0 f1
      (DIV: _diverge_flag _ true f1 (ktr tt))
      (FLAG: forall j (NEQ: j <> i), Flag.le (f1 j) (f0 j))
      (FAIL: Flag.le (f0 i) Flag.emp -> Flag.le (f1 i) Flag.emp)
    :
    _diverge_flag diverge_flag b f0 (Vis (Fail i) ktr)

  | diverge_flag_progress
      itr b f
      (DIV: diverge_flag _ true (fun _ => Flag.emp) itr)
      (FLAG: forall i, Flag.le Flag.emp (f i))
    :
    _diverge_flag diverge_flag b f itr
  .

  Lemma diverge_flag_mon: monotone4 _diverge_flag.
  Proof.
    ii. induction IN.
    - econs 1; eauto.
    - econs 2; eauto.
    - econs 3; eauto.
    - econs 4; eauto.
    - econs 5; eauto.
  Qed.

  Definition diverge_flag: forall (R: Type) (b: bool) (f: Ident -> Flag.t) (itr: itree eventE R), Prop := paco4 _diverge_flag bot4.

  Definition diverge2 (R: Type) (itr: itree eventE R): Prop :=
    exists b f, diverge_flag b f itr.

  Lemma diverge_diverge2 R (itr: itree eventE R) (DIV: diverge itr)
    :
    diverge2 itr.
  Proof.
  Admitted.

  Lemma diverge2_diverge R (itr: itree eventE R) (DIV: diverge2 itr)
    :
    diverge itr.
  Proof.
  Admitted.
End BEHAVES.



Section SIM.

  Inductive _sim
            (sim: forall R0 R1 (RR: R0 -> R1 -> Prop), (bool * (option Ident))  -> (bool * (option Ident)) -> (itree eventE R0) -> (itree eventE R1) -> Prop)
            {R0 R1} (RR: R0 -> R1 -> Prop) (fi_src fi_tgt: (bool * (option Ident))) : (itree eventE R0) -> (itree eventE R1) -> Prop :=
  | sim_ret
      r_src r_tgt
      (SIM: RR r_src r_tgt)
    :
    _sim sim RR fi_src fi_tgt (Ret r_src) (Ret r_tgt)
  | sim_tauL
      itr_src0 itr_tgt0
      (SIM: @_sim sim _ _ RR (true, snd fi_src) fi_tgt itr_src0 itr_tgt0)
    :
    _sim sim RR fi_src fi_tgt (Tau itr_src0) itr_tgt0
  | sim_tauR
      itr_src0 itr_tgt0
      (SIM: @_sim sim _ _ RR fi_src (true, snd fi_tgt) itr_src0 itr_tgt0)
    :
    _sim sim RR fi_src fi_tgt (Tau itr_src0) itr_tgt0
  | sim_chooseL
      X ktr_src0 itr_tgt0
      (SIM: exists x, _sim sim RR (true, snd fi_src) fi_tgt (ktr_src0 x) itr_tgt0)
    :
    _sim sim RR fi_src fi_tgt (trigger (Choose X) >>= ktr_src0) itr_tgt0
  | sim_chooseR
      X itr_src0 ktr_tgt0
      (SIM: forall x, _sim sim RR fi_src (true, snd fi_tgt) itr_src0 (ktr_tgt0 x))
    :
    _sim sim RR fi_src fi_tgt itr_src0 (trigger (Choose X) >>= ktr_tgt0)
  | sim_successL_stop
      id ktr_src0 itr_tgt0
      (STOP: <<SOME: snd fi_src = Some id>> \/ <<NONE: snd fi_src = None>>)
      (SIM: _sim sim RR (true, None) fi_tgt (ktr_src0 tt) itr_tgt0)
    :
    _sim sim RR fi_src fi_tgt (trigger (Success id) >>= ktr_src0) itr_tgt0
  | sim_successL_pass
      id id_src ktr_src0 itr_tgt0
      (PASS: <<SOME: snd fi_src = Some id_src>> /\ <<PASS: id_src <> id>>)
      (SIM: _sim sim RR (true, snd fi_src) fi_tgt (ktr_src0 tt) itr_tgt0)
    :
    _sim sim RR fi_src fi_tgt (trigger (Success id) >>= ktr_src0) itr_tgt0
  | sim_successR_stop
      id itr_src0 ktr_tgt0
      (STOP: <<SOME: snd fi_tgt = Some id>> \/ <<NONE: snd fi_tgt = None>>)
      (SIM: _sim sim RR fi_src (true, None) itr_src0 (ktr_tgt0 tt))
    :
    _sim sim RR fi_src fi_tgt itr_src0 (trigger (Success id) >>= ktr_tgt0)
  | sim_successR_pass
      id id_tgt itr_src0 ktr_tgt0
      (PASS: <<SOME: snd fi_tgt = Some id_tgt>> /\ <<PASS: id_tgt <> id>>)
      (SIM: _sim sim RR fi_src (true, snd fi_tgt) itr_src0 (ktr_tgt0 tt))
    :
    _sim sim RR fi_src fi_tgt itr_src0 (trigger (Success id) >>= ktr_tgt0)
  | sim_failL_start
      id ktr_src0 itr_tgt0
      (START: 
      (SIM: _sim sim RR (true, snd fi_src) fi_tgt (ktr_src0 tt) itr_tgt0)
    :
    _sim sim RR fi_src fi_tgt (trigger (Fail id) >>= ktr_src0) itr_tgt0
  .



End SIM.
