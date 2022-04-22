From sflib Require Import sflib.
From ITree Require Export ITree.
From Paco Require Import paco.

Export ITreeNotations.

Require Import Coq.Classes.RelationClasses.
Require Import Program.

From Fairness Require Import ITreeLib.
From Fairness Require Import FairBeh.

Set Implicit Arguments.

Section SIM.

  Variable Ident: Type.

  Definition fmap := Ident -> Flag.t.
  Definition fmap_emp : fmap := fun _ => Flag.emp.

  Inductive _sim
            (sim: forall R0 R1 (RR: R0 -> R1 -> Prop),
                bool -> fmap  -> bool -> fmap -> Ident -> (itree (eventE Ident) R0) -> (itree (eventE Ident) R1) -> Prop)
            {R0 R1} (RR: R0 -> R1 -> Prop) (p_src: bool) (m_src: fmap) (p_tgt: bool) (m_tgt: fmap) (idx: Ident) :
    (itree (eventE _) R0) -> (itree (eventE _) R1) -> Prop :=
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
    _sim sim RR p_src m_src p_tgt m_tgt idx (trigger (Choose _ X) >>= ktr_src0) itr_tgt0
  | sim_chooseR
      X itr_src0 ktr_tgt0
      (SIM: forall x, _sim sim RR p_src m_src true m_tgt idx itr_src0 (ktr_tgt0 x))
    :
    _sim sim RR p_src m_src p_tgt m_tgt idx itr_src0 (trigger (Choose _ X) >>= ktr_tgt0)

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

  Lemma _sim_ind2 (r: forall R0 R1 (RR: R0 -> R1 -> Prop), bool -> fmap  -> bool -> fmap -> Ident -> (itree (eventE Ident) R0) -> (itree (eventE Ident) R1) -> Prop)
        R0 R1 (RR: R0 -> R1 -> Prop)
        (P: bool -> fmap  -> bool -> fmap -> Ident -> (itree (eventE Ident) R0) -> (itree (eventE Ident) R1) -> Prop)
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
            P p_src m_src p_tgt m_tgt idx (ITree.bind (trigger (Choose _ X)) ktr_src0) itr_tgt0)
        (CHOOSER: forall
            p_src m_src p_tgt m_tgt idx X itr_src0 ktr_tgt0
            (SIM: forall x, <<SIM: _sim r RR p_src m_src true m_tgt idx itr_src0 (ktr_tgt0 x)>> /\
                                <<IH: P p_src m_src true m_tgt idx itr_src0 (ktr_tgt0 x)>>),
            P p_src m_src p_tgt m_tgt idx itr_src0 (ITree.bind (trigger (Choose _ X)) ktr_tgt0))
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

  Definition sim: forall R0 R1 (RR: R0 -> R1 -> Prop), bool -> fmap  -> bool -> fmap -> Ident -> (itree (eventE _) R0) -> (itree (eventE _) R1) -> Prop := paco10 _sim bot10.

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
            (isim: forall R0 R1 (RR: R0 -> R1 -> Prop),
                bool -> imap  -> bool -> imap -> (itree (eventE Ident) R0) -> (itree (eventE Ident) R1) -> Prop)
            {R0 R1} (RR: R0 -> R1 -> Prop) (p_src: bool) (m_src: imap) (p_tgt: bool) (m_tgt: imap):
    (itree (eventE Ident) R0) -> (itree (eventE Ident) R1) -> Prop :=
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
    _isim isim RR p_src m_src p_tgt m_tgt (trigger (Choose _ X) >>= ktr_src0) itr_tgt0
  | isim_chooseR
      X itr_src0 ktr_tgt0
      (SIM: forall x, _isim isim RR p_src m_src true m_tgt itr_src0 (ktr_tgt0 x))
    :
    _isim isim RR p_src m_src p_tgt m_tgt itr_src0 (trigger (Choose _ X) >>= ktr_tgt0)

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

  Lemma _isim_ind2 (r: forall R0 R1 (RR: R0 -> R1 -> Prop), bool -> imap  -> bool -> imap -> (itree (eventE Ident) R0) -> (itree (eventE Ident) R1) -> Prop)
        R0 R1 (RR: R0 -> R1 -> Prop)
        (P: bool -> imap  -> bool -> imap -> (itree (eventE Ident) R0) -> (itree (eventE Ident) R1) -> Prop)
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
            P p_src m_src p_tgt m_tgt (ITree.bind (trigger (Choose _ X)) ktr_src0) itr_tgt0)
        (CHOOSER: forall
            p_src m_src p_tgt m_tgt X itr_src0 ktr_tgt0
            (SIM: forall x, <<SIM: _isim r RR p_src m_src true m_tgt itr_src0 (ktr_tgt0 x)>> /\
                                <<IH: P p_src m_src true m_tgt itr_src0 (ktr_tgt0 x)>>),
            P p_src m_src p_tgt m_tgt itr_src0 (ITree.bind (trigger (Choose _ X)) ktr_tgt0))
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

  Definition isim: forall R0 R1 (RR: R0 -> R1 -> Prop), bool -> imap  -> bool -> imap -> (itree (eventE _) R0) -> (itree (eventE _) R1) -> Prop := paco9 _isim bot9.

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



Section EX.

  Definition Ident := nat.

  (* Definition uunit := prod unit unit. *)

  Definition while_itree (step: unit -> itree (eventE Ident) (unit + unit)) : itree (eventE Ident) unit :=
    ITree.iter step tt.

  Lemma unfold_iter_eq A E B
     : forall (f : A -> itree E (A + B)) (x : A),
       ITree.iter f x = lr <- f x;; match lr with
                                    | inl l => Tau (ITree.iter f l)
                                    | inr r0 => Ret r0
                                   end.
  Proof.
    i. eapply bisim_is_eq. eapply unfold_iter.
  Qed.

  Lemma unfold_while_itree
        itr
    :
    while_itree (fun u => ITree.bind itr (fun r => Ret (inl r))) =
      (* r <- itr;; *)
      (* x <- Ret (inl r);; *)
      (* match x with *)
      (* | inl l => *)
      (*     Tau *)
      (*       (ITree.iter (fun _ : unit => r0 <- itr;; Ret (inl r0)) *)
      (*                   l) *)
      (* | inr r0 => Ret r0 *)
      (* end. *)
      itr;; tau;; (while_itree (fun u => ITree.bind itr (fun r => Ret (inl r)))).
  Proof.
    unfold while_itree. rewrite unfold_iter_eq at 1. ired.
    f_equal. extensionality u. destruct u. ired. auto.
  Qed.
    (* unfold while_itree. eapply bisim_is_eq. revert1. ginit. gcofix CIH. i. *)
    (* rewrite unfold_iter_eq. ired. guclo eqit_clo_bind. econs. reflexivity. *)
    (* i; subst. ired. gstep. econs. gfinal. left. *)
    (* specialize (CIH itr). destruct u2. *)
    (* match goal with *)
    (* | _: r _ ?x |- r _ ?y => replace y with x *)
    (* end; eauto. *)
    (* rewrite unfold_iter_eq. ired. *)
    (* f_equal. extensionality a. destruct a. ired. f_equal. f_equal. *)
    (* rewrite unfold_iter_eq. ired. auto. *)

  Definition RR := @eq nat.

  Definition src1 : itree (eventE Ident) nat := Ret 0.
  Definition tgt1 : itree (eventE Ident) nat :=
    while_itree (fun u => ITree.bind (trigger (Fail 0)) (fun r => Ret (inl r)));; Ret 0.

  Goal sim RR false (@fmap_emp _) false (@fmap_emp _) 0 src1 tgt1.
  Proof.
    unfold src1, tgt1.
    pcofix CIH. pfold. rewrite unfold_while_itree. ired.
    econs 7.
    { i. instantiate (1:= fun n => if PeanoNat.Nat.eq_dec 0 n then Flag.fail else Flag.emp).
      ss. des_ifs.
    }
    { i. ss. }
    econs. econs 11; auto.
    3:{ right. eauto. }
    { i. des_ifs. }
    ss.
  Qed.

End EX.
