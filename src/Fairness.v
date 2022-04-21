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

  Definition fmap := Ident -> Flag.t.
  Definition fmap_emp : fmap := fun _ => Flag.emp.

  Inductive _sim
            (sim: forall R0 R1 (RR: R0 -> R1 -> Prop), bool -> fmap  -> bool -> fmap -> Ident -> (itree eventE R0) -> (itree eventE R1) -> Prop)
            {R0 R1} (RR: R0 -> R1 -> Prop) (p_src: bool) (m_src: fmap) (p_tgt: bool) (m_tgt: fmap) (idx: Ident) : (itree eventE R0) -> (itree eventE R1) -> Prop :=
  | sim_ret
      r_src r_tgt
      (SIM: RR r_src r_tgt)
      (FMAP: forall j, Flag.le (m_tgt j) (m_src j))
    :
    _sim sim RR p_src m_src p_tgt m_tgt idx (Ret r_src) (Ret r_tgt)
  | sim_tauL
      itr_src0 itr_tgt0
      (SIM: @_sim sim _ _ RR true m_src p_tgt m_tgt idx itr_src0 itr_tgt0)
    :
    _sim sim RR p_src m_src p_tgt m_tgt idx (Tau itr_src0) itr_tgt0
  | sim_tauR
      itr_src0 itr_tgt0
      (SIM: @_sim sim _ _ RR p_src m_src true m_tgt idx itr_src0 itr_tgt0)
    :
    _sim sim RR p_src m_src p_tgt m_tgt idx itr_src0 (Tau itr_tgt0)
  | sim_chooseL
      X ktr_src0 itr_tgt0
      (SIM: exists x, _sim sim RR true m_src p_tgt m_tgt idx (ktr_src0 x) itr_tgt0)
    :
    _sim sim RR p_src m_src p_tgt m_tgt idx (trigger (Choose X) >>= ktr_src0) itr_tgt0
  | sim_chooseR
      X itr_src0 ktr_tgt0
      (SIM: forall x, _sim sim RR p_src m_src true m_tgt idx itr_src0 (ktr_tgt0 x))
    :
    _sim sim RR p_src m_src p_tgt m_tgt idx itr_src0 (trigger (Choose X) >>= ktr_tgt0)

  | sim_failL
      id m_src0 ktr_src0 itr_tgt0
      (SRC: forall j, Flag.le (m_src0 j) (m_src j))
      (FAIL: (Flag.le (m_src id) Flag.emp) -> (Flag.le (m_src0 id) Flag.fail))
      (SIM: _sim sim RR true m_src0 p_tgt m_tgt idx (ktr_src0 tt) itr_tgt0)
    :
    _sim sim RR p_src m_src p_tgt m_tgt idx (trigger (Fail id) >>= ktr_src0) itr_tgt0
  | sim_failR
      id m_tgt0 itr_src0 ktr_tgt0
      (TGT: forall j, Flag.le (m_tgt0 j) (m_tgt j))
      (FAIL: (Flag.le (m_tgt id) Flag.emp) -> (Flag.le (m_tgt0 id) Flag.fail))
      (SIM: _sim sim RR p_src m_src true m_tgt0 idx itr_src0 (ktr_tgt0 tt))
    :
    _sim sim RR p_src m_src p_tgt m_tgt idx itr_src0 (trigger (Fail id) >>= ktr_tgt0)

  | sim_successL
      id m_src0 ktr_src0 itr_tgt0
      (SRC: forall j (NEQ: id <> j), Flag.le (m_src0 j) (m_src j))
      (SUCCESS: Flag.le Flag.success (m_src0 id))
      (SIM: _sim sim RR true m_src0 p_tgt m_tgt idx (ktr_src0 tt) itr_tgt0)
    :
    _sim sim RR p_src m_src p_tgt m_tgt idx (trigger (Success id) >>= ktr_src0) itr_tgt0
  | sim_successR
      id m_tgt0 itr_src0 ktr_tgt0
      (TGT: forall j (NEQ: id <> j), Flag.le (m_tgt0 j) (m_tgt j))
      (SUCCESS: Flag.le Flag.success (m_tgt0 id))
      (SIM: _sim sim RR p_src m_src true m_tgt0 idx itr_src0 (ktr_tgt0 tt))
    :
    _sim sim RR p_src m_src p_tgt m_tgt idx itr_src0 (trigger (Success id) >>= ktr_tgt0)

  | sim_progress_strong
      itr_src0 itr_tgt0 idx0
      (PSRC: p_src = true)
      (PTGT: p_tgt = true)
      (FMAP: forall j, Flag.le (m_tgt j) (m_src j))
      (SIM: sim _ _ RR false fmap_emp false fmap_emp idx0 itr_src0 itr_tgt0)
    :
    _sim sim RR p_src m_src p_tgt m_tgt idx itr_src0 itr_tgt0

  | sim_progress_weak
      m_tgt0 itr_src0 itr_tgt0
      (PTGT: p_tgt = true)
      (FLAG: forall j (NEQ: idx <> j), Flag.le (m_tgt0 j) (m_tgt j))
      (FMAP: m_tgt idx = Flag.fail)
      (FMAP0: m_tgt0 idx = Flag.emp)
      (SIM: sim _ _ RR p_src m_src false m_tgt0 idx itr_src0 itr_tgt0)
    :
    _sim sim RR p_src m_src p_tgt m_tgt idx itr_src0 itr_tgt0
  .

  Lemma _sim_ind2 (r: forall R0 R1 (RR: R0 -> R1 -> Prop), bool -> fmap  -> bool -> fmap -> Ident -> (itree eventE R0) -> (itree eventE R1) -> Prop)
        R0 R1 (RR: R0 -> R1 -> Prop)
        (P: bool -> fmap  -> bool -> fmap -> Ident -> (itree eventE R0) -> (itree eventE R1) -> Prop)
        (RET: forall
            p_src m_src p_tgt m_tgt idx
            r_src r_tgt
            (SIM: RR r_src r_tgt)
            (FMAP: forall j, Flag.le (m_tgt j) (m_src j)),
            P p_src m_src p_tgt m_tgt idx (Ret r_src) (Ret r_tgt))
        (TAUL: forall 
            p_src m_src p_tgt m_tgt idx itr_src0 itr_tgt0
            (SIM: _sim r RR true m_src p_tgt m_tgt idx itr_src0 itr_tgt0)
            (IH: P true m_src p_tgt m_tgt idx itr_src0 itr_tgt0),
            P p_src m_src p_tgt m_tgt idx (Tau itr_src0) itr_tgt0)
        (TAUR: forall 
            p_src m_src p_tgt m_tgt idx itr_src0 itr_tgt0
            (SIM: _sim r RR p_src m_src true m_tgt idx itr_src0 itr_tgt0)
            (IH: P p_src m_src true m_tgt idx itr_src0 itr_tgt0),
            P p_src m_src p_tgt m_tgt idx itr_src0 (Tau itr_tgt0))
        (CHOOSEL: forall
            p_src m_src p_tgt m_tgt idx X ktr_src0 itr_tgt0
            (SIM: exists x, <<SIM: _sim r RR true m_src p_tgt m_tgt idx (ktr_src0 x) itr_tgt0>> /\
                                <<IH: P true m_src p_tgt m_tgt idx (ktr_src0 x) itr_tgt0>>),
            P p_src m_src p_tgt m_tgt idx (ITree.bind (trigger (Choose X)) ktr_src0) itr_tgt0)
        (CHOOSER: forall
            p_src m_src p_tgt m_tgt idx X itr_src0 ktr_tgt0
            (SIM: forall x, <<SIM: _sim r RR p_src m_src true m_tgt idx itr_src0 (ktr_tgt0 x)>> /\
                                <<IH: P p_src m_src true m_tgt idx itr_src0 (ktr_tgt0 x)>>),
            P p_src m_src p_tgt m_tgt idx itr_src0 (ITree.bind (trigger (Choose X)) ktr_tgt0))
        (FAILL: forall
            p_src m_src p_tgt m_tgt idx ktr_src0 itr_tgt0
            id m_src0
            (SRC: forall j, Flag.le (m_src0 j) (m_src j))
            (FAIL: (Flag.le (m_src id) Flag.emp) -> (Flag.le (m_src0 id) Flag.fail))
            (SIM: _sim r RR true m_src0 p_tgt m_tgt idx (ktr_src0 tt) itr_tgt0)
            (IH: P true m_src0 p_tgt m_tgt idx (ktr_src0 tt) itr_tgt0),
            P p_src m_src p_tgt m_tgt idx (ITree.bind (trigger (Fail id)) ktr_src0) itr_tgt0)
        (FAILR: forall
            p_src m_src p_tgt m_tgt idx itr_src0 ktr_tgt0
            id m_tgt0
            (TGT: forall j, Flag.le (m_tgt0 j) (m_tgt j))
            (FAIL: (Flag.le (m_tgt id) Flag.emp) -> (Flag.le (m_tgt0 id) Flag.fail))
            (SIM: _sim r RR p_src m_src true m_tgt0 idx itr_src0 (ktr_tgt0 tt))
            (IH: P p_src m_src true m_tgt0 idx itr_src0 (ktr_tgt0 tt)),
            P p_src m_src p_tgt m_tgt idx itr_src0 (ITree.bind (trigger (Fail id)) ktr_tgt0))
        (SUCCESSL: forall
            p_src m_src p_tgt m_tgt idx ktr_src0 itr_tgt0
            id m_src0
            (SRC: forall j (NEQ: id <> j), Flag.le (m_src0 j) (m_src j))
            (SUCCESS: Flag.le Flag.success (m_src0 id))
            (SIM: _sim r RR true m_src0 p_tgt m_tgt idx (ktr_src0 tt) itr_tgt0)
            (IH: P true m_src0 p_tgt m_tgt idx (ktr_src0 tt) itr_tgt0),
            P p_src m_src p_tgt m_tgt idx (ITree.bind (trigger (Success id)) ktr_src0) itr_tgt0)
        (SUCCESSR: forall
            p_src m_src p_tgt m_tgt idx itr_src0 ktr_tgt0
            id m_tgt0
            (TGT: forall j (NEQ: id <> j), Flag.le (m_tgt0 j) (m_tgt j))
            (SUCCESS: Flag.le Flag.success (m_tgt0 id))
            (SIM: _sim r RR p_src m_src true m_tgt0 idx itr_src0 (ktr_tgt0 tt))
            (IH: P p_src m_src true m_tgt0 idx itr_src0 (ktr_tgt0 tt)),
            P p_src m_src p_tgt m_tgt idx itr_src0 (ITree.bind (trigger (Success id)) ktr_tgt0))
        (PROGRESSS: forall
            p_src m_src p_tgt m_tgt idx itr_src0 itr_tgt0
            idx0
            (PSRC: p_src = true)
            (PTGT: p_tgt = true)
            (FMAP: forall j, Flag.le (m_tgt j) (m_src j))
            (SIM: r _ _ RR false fmap_emp false fmap_emp idx0 itr_src0 itr_tgt0),
            P p_src m_src p_tgt m_tgt idx itr_src0 itr_tgt0)
        (PROGRESSW: forall
            p_src m_src p_tgt m_tgt idx itr_src0 itr_tgt0
            m_tgt0
            (PTGT: p_tgt = true)
            (FLAG: forall j (NEQ: idx <> j), Flag.le (m_tgt0 j) (m_tgt j))
            (FMAP: m_tgt idx = Flag.fail)
            (FMAP0: m_tgt0 idx = Flag.emp)
            (SIM: r _ _ RR p_src m_src false m_tgt0 idx itr_src0 itr_tgt0),
            P p_src m_src p_tgt m_tgt idx itr_src0 itr_tgt0)
    :
    forall p_src m_src p_tgt m_tgt idx itr_src itr_tgt
      (SIM: _sim r RR p_src m_src p_tgt m_tgt idx itr_src itr_tgt),
      P p_src m_src p_tgt m_tgt idx itr_src itr_tgt.
  Proof.
    fix IH 8. i. inv SIM.
    { eapply RET; eauto. }
    { eapply TAUL; eauto. }
    { eapply TAUR; eauto. }
    { eapply CHOOSEL; eauto. des. esplits; eauto. }
    { eapply CHOOSER; eauto. }
    { eapply FAILL; eauto. }
    { eapply FAILR; eauto. }
    { eapply SUCCESSL; eauto. }
    { eapply SUCCESSR; eauto. }
    { eapply PROGRESSS; eauto. }
    { eapply PROGRESSW; eauto. }
  Qed.

  Definition sim: forall R0 R1 (RR: R0 -> R1 -> Prop), bool -> fmap  -> bool -> fmap -> Ident -> (itree eventE R0) -> (itree eventE R1) -> Prop := paco10 _sim bot10.

  Lemma sim_mon: monotone10 _sim.
  Proof.
    ii. induction IN using _sim_ind2.
    { econs 1; eauto. }
    { econs 2; eauto. }
    { econs 3; eauto. }
    { econs 4; eauto. des. esplits; eauto. }
    { econs 5; eauto. i. hexploit SIM. i; des. eauto. }
    { econs 6; eauto. }
    { econs 7; eauto. }
    { econs 8; eauto. }
    { econs 9; eauto. }
    { econs 10; eauto. }
    { econs 11; eauto. }
  Qed.

  Hint Resolve sim_mon: paco.
  Hint Resolve cpn10_wcompat: paco.



  Definition imap := Ident -> nat.

  Inductive _isim
            (isim: forall R0 R1 (RR: R0 -> R1 -> Prop), bool -> imap  -> bool -> imap -> (itree eventE R0) -> (itree eventE R1) -> Prop)
            {R0 R1} (RR: R0 -> R1 -> Prop) (p_src: bool) (m_src: imap) (p_tgt: bool) (m_tgt: imap): (itree eventE R0) -> (itree eventE R1) -> Prop :=
  | isim_ret
      r_src r_tgt
      (SIM: RR r_src r_tgt)
    :
    _isim isim RR p_src m_src p_tgt m_tgt (Ret r_src) (Ret r_tgt)
  | isim_tauL
      itr_src0 itr_tgt0
      (SIM: @_isim isim _ _ RR true m_src p_tgt m_tgt itr_src0 itr_tgt0)
    :
    _isim isim RR p_src m_src p_tgt m_tgt (Tau itr_src0) itr_tgt0
  | isim_tauR
      itr_src0 itr_tgt0
      (SIM: @_isim isim _ _ RR p_src m_src true m_tgt itr_src0 itr_tgt0)
    :
    _isim isim RR p_src m_src p_tgt m_tgt itr_src0 (Tau itr_tgt0)
  | isim_chooseL
      X ktr_src0 itr_tgt0
      (SIM: exists x, _isim isim RR true m_src p_tgt m_tgt (ktr_src0 x) itr_tgt0)
    :
    _isim isim RR p_src m_src p_tgt m_tgt (trigger (Choose X) >>= ktr_src0) itr_tgt0
  | isim_chooseR
      X itr_src0 ktr_tgt0
      (SIM: forall x, _isim isim RR p_src m_src true m_tgt itr_src0 (ktr_tgt0 x))
    :
    _isim isim RR p_src m_src p_tgt m_tgt itr_src0 (trigger (Choose X) >>= ktr_tgt0)

  | isim_failL
      id m_src0 ktr_src0 itr_tgt0
      (SRC: forall j, le (m_src0 j) (m_src j))
      (FAIL: lt (m_src0 id) (m_src id))
      (SIM: _isim isim RR true m_src0 p_tgt m_tgt (ktr_src0 tt) itr_tgt0)
    :
    _isim isim RR p_src m_src p_tgt m_tgt (trigger (Fail id) >>= ktr_src0) itr_tgt0
  | isim_failR
      id itr_src0 ktr_tgt0
      (SIM: forall m_tgt0 (TGT: forall j, le (m_tgt0 j) (m_tgt j)) (FAIL: lt (m_tgt0 id) (m_tgt id)),
          _isim isim RR p_src m_src true m_tgt0 itr_src0 (ktr_tgt0 tt))
    :
    _isim isim RR p_src m_src p_tgt m_tgt itr_src0 (trigger (Fail id) >>= ktr_tgt0)

  | isim_successL
      id m_src0 ktr_src0 itr_tgt0
      (SRC: forall j (NEQ: id <> j), le (m_src0 j) (m_src j))
      (SIM: _isim isim RR true m_src0 p_tgt m_tgt (ktr_src0 tt) itr_tgt0)
    :
    _isim isim RR p_src m_src p_tgt m_tgt (trigger (Success id) >>= ktr_src0) itr_tgt0
  | isim_successR
      id itr_src0 ktr_tgt0
      (SIM: forall m_tgt0 (TGT: forall j (NEQ: id <> j), le (m_tgt0 j) (m_tgt j)),
          _isim isim RR p_src m_src true m_tgt0 itr_src0 (ktr_tgt0 tt))
    :
    _isim isim RR p_src m_src p_tgt m_tgt itr_src0 (trigger (Success id) >>= ktr_tgt0)

  | isim_progress_strong
      itr_src0 itr_tgt0
      (PSRC: p_src = true)
      (PTGT: p_tgt = true)
      (IMAP: forall j, (<<SRC: forall n, le (m_src j) n>>) -> (<<TGT: forall n, le (m_tgt j) n>>))
      (SIM: exists m_src0 m_tgt0, isim _ _ RR false m_src0 false m_tgt0 itr_src0 itr_tgt0)
    :
    _isim isim RR p_src m_src p_tgt m_tgt itr_src0 itr_tgt0
  .

  Lemma _isim_ind2 (r: forall R0 R1 (RR: R0 -> R1 -> Prop), bool -> imap  -> bool -> imap -> (itree eventE R0) -> (itree eventE R1) -> Prop)
        R0 R1 (RR: R0 -> R1 -> Prop)
        (P: bool -> imap  -> bool -> imap -> (itree eventE R0) -> (itree eventE R1) -> Prop)
        (RET: forall
            p_src m_src p_tgt m_tgt
            r_src r_tgt
            (SIM: RR r_src r_tgt),
            P p_src m_src p_tgt m_tgt (Ret r_src) (Ret r_tgt))
        (TAUL: forall 
            p_src m_src p_tgt m_tgt itr_src0 itr_tgt0
            (SIM: _isim r RR true m_src p_tgt m_tgt itr_src0 itr_tgt0)
            (IH: P true m_src p_tgt m_tgt itr_src0 itr_tgt0),
            P p_src m_src p_tgt m_tgt (Tau itr_src0) itr_tgt0)
        (TAUR: forall 
            p_src m_src p_tgt m_tgt itr_src0 itr_tgt0
            (SIM: _isim r RR p_src m_src true m_tgt itr_src0 itr_tgt0)
            (IH: P p_src m_src true m_tgt itr_src0 itr_tgt0),
            P p_src m_src p_tgt m_tgt itr_src0 (Tau itr_tgt0))
        (CHOOSEL: forall
            p_src m_src p_tgt m_tgt X ktr_src0 itr_tgt0
            (SIM: exists x, <<SIM: _isim r RR true m_src p_tgt m_tgt (ktr_src0 x) itr_tgt0>> /\
                                <<IH: P true m_src p_tgt m_tgt (ktr_src0 x) itr_tgt0>>),
            P p_src m_src p_tgt m_tgt (ITree.bind (trigger (Choose X)) ktr_src0) itr_tgt0)
        (CHOOSER: forall
            p_src m_src p_tgt m_tgt X itr_src0 ktr_tgt0
            (SIM: forall x, <<SIM: _isim r RR p_src m_src true m_tgt itr_src0 (ktr_tgt0 x)>> /\
                                <<IH: P p_src m_src true m_tgt itr_src0 (ktr_tgt0 x)>>),
            P p_src m_src p_tgt m_tgt itr_src0 (ITree.bind (trigger (Choose X)) ktr_tgt0))
        (FAILL: forall
            p_src m_src p_tgt m_tgt ktr_src0 itr_tgt0
            id m_src0
            (SRC: forall j, le (m_src0 j) (m_src j))
            (FAIL: lt (m_src0 id) (m_src id))
            (SIM: _isim r RR true m_src0 p_tgt m_tgt (ktr_src0 tt) itr_tgt0)
            (IH: P true m_src0 p_tgt m_tgt (ktr_src0 tt) itr_tgt0),
            P p_src m_src p_tgt m_tgt (ITree.bind (trigger (Fail id)) ktr_src0) itr_tgt0)
        (FAILR: forall
            p_src m_src p_tgt m_tgt itr_src0 ktr_tgt0
            id
            (SIM: forall m_tgt0 (TGT: forall j, le (m_tgt0 j) (m_tgt j)) (FAIL: lt (m_tgt0 id) (m_tgt id)),
                (<<SIM: _isim r RR p_src m_src true m_tgt0 itr_src0 (ktr_tgt0 tt)>> /\
                          (<<IH: P p_src m_src true m_tgt0 itr_src0 (ktr_tgt0 tt)>>))),
            P p_src m_src p_tgt m_tgt itr_src0 (ITree.bind (trigger (Fail id)) ktr_tgt0))

        (SUCCESSL: forall
            p_src m_src p_tgt m_tgt ktr_src0 itr_tgt0
            id m_src0
            (SRC: forall j (NEQ: id <> j), le (m_src0 j) (m_src j))
            (SIM: _isim r RR true m_src0 p_tgt m_tgt (ktr_src0 tt) itr_tgt0)
            (IH: P true m_src0 p_tgt m_tgt (ktr_src0 tt) itr_tgt0),
            P p_src m_src p_tgt m_tgt (ITree.bind (trigger (Success id)) ktr_src0) itr_tgt0)
        (SUCCESSR: forall
            p_src m_src p_tgt m_tgt itr_src0 ktr_tgt0
            id
            (SIM: forall m_tgt0 (TGT: forall j (NEQ: id <> j), le (m_tgt0 j) (m_tgt j)),
                (<<SIM: _isim r RR p_src m_src true m_tgt0 itr_src0 (ktr_tgt0 tt)>>) /\
                  (<<IH: P p_src m_src true m_tgt0 itr_src0 (ktr_tgt0 tt)>>)),
            P p_src m_src p_tgt m_tgt itr_src0 (ITree.bind (trigger (Success id)) ktr_tgt0))
        (PROGRESSS: forall
            p_src m_src p_tgt m_tgt itr_src0 itr_tgt0
            (PSRC: p_src = true)
            (PTGT: p_tgt = true)
            (IMAP: forall j, (<<SRC: forall n, le (m_src j) n>>) -> (<<TGT: forall n, le (m_tgt j) n>>))
            (SIM: exists m_src0 m_tgt0, r _ _ RR false m_src0 false m_tgt0 itr_src0 itr_tgt0),
            P p_src m_src p_tgt m_tgt itr_src0 itr_tgt0)
    :
    forall p_src m_src p_tgt m_tgt itr_src itr_tgt
      (SIM: _isim r RR p_src m_src p_tgt m_tgt itr_src itr_tgt),
      P p_src m_src p_tgt m_tgt itr_src itr_tgt.
  Proof.
    fix IH 7. i. inv SIM.
    { eapply RET; eauto. }
    { eapply TAUL; eauto. }
    { eapply TAUR; eauto. }
    { eapply CHOOSEL; eauto. des. esplits; eauto. }
    { eapply CHOOSER; eauto. }
    { eapply FAILL; eauto. }
    { eapply FAILR; eauto. i. splits; eauto. }
    { eapply SUCCESSL; eauto. }
    { eapply SUCCESSR; eauto. i. split; eauto. }
    { eapply PROGRESSS; eauto. }
  Qed.

  Definition isim: forall R0 R1 (RR: R0 -> R1 -> Prop), bool -> imap  -> bool -> imap -> (itree eventE R0) -> (itree eventE R1) -> Prop := paco9 _isim bot9.

  Lemma isim_mon: monotone9 _isim.
  Proof.
    ii. induction IN using _isim_ind2.
    { econs 1; eauto. }
    { econs 2; eauto. }
    { econs 3; eauto. }
    { econs 4; eauto. des. esplits; eauto. }
    { econs 5; eauto. i. hexploit SIM. i; des. eauto. }
    { econs 6; eauto. }
    { econs 7; eauto. i. hexploit SIM; eauto. i; des; eauto. }
    { econs 8; eauto. }
    { econs 9; eauto. i. hexploit SIM; eauto. i; des; eauto. }
    { econs 10; eauto. des. esplits; eauto. }
  Qed.

  Hint Resolve isim_mon: paco.
  Hint Resolve cpn9_wcompat: paco.

End SIM.
