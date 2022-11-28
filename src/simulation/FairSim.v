From sflib Require Import sflib.
From Paco Require Import paco.

Require Import Coq.Classes.RelationClasses.
Require Import Program.
Require Import Lia.

From Fairness Require Import Axioms ITreeLib WFLib FairBeh.

Set Implicit Arguments.

Section SIM.

  Variable ids: ID.
  Variable idt: ID.
  Variable wfs: WF.
  Variable wft: WF.

  Inductive _sim
            (sim: forall R0 R1 (RR: R0 -> R1 -> Prop), bool -> (@imap ids wfs) -> bool  -> (@imap idt wft) -> (@state ids R0) -> (@state idt R1) -> Prop)
            {R0 R1} (RR: R0 -> R1 -> Prop) (p_src: bool) (m_src: @imap ids wfs) (p_tgt: bool) (m_tgt: @imap idt wft) :
    (@state ids R0) -> (@state idt R1) -> Prop :=
  | sim_ret
      r_src r_tgt
      (SIM: RR r_src r_tgt)
    :
    _sim sim RR p_src m_src p_tgt m_tgt (Ret r_src) (Ret r_tgt)
  | sim_obs
      ktr_src0 ktr_tgt0 fn args
      (SIM: forall r_src r_tgt (EQ: r_src = r_tgt),
          sim _ _ RR true m_src true m_tgt (ktr_src0 r_src) (ktr_tgt0 r_tgt))
    :
    _sim sim RR p_src m_src p_tgt m_tgt (Vis (Observe fn args) ktr_src0) (Vis (Observe fn args) ktr_tgt0)

  | sim_tauL
      itr_src0 itr_tgt0
      (SIM: @_sim sim _ _ RR true m_src p_tgt m_tgt itr_src0 itr_tgt0)
    :
    _sim sim RR p_src m_src p_tgt m_tgt (Tau itr_src0) itr_tgt0
  | sim_tauR
      itr_src0 itr_tgt0
      (SIM: @_sim sim _ _ RR p_src m_src true m_tgt itr_src0 itr_tgt0)
    :
    _sim sim RR p_src m_src p_tgt m_tgt itr_src0 (Tau itr_tgt0)
  | sim_chooseL
      X ktr_src0 itr_tgt0
      (SIM: exists x, _sim sim RR true m_src p_tgt m_tgt (ktr_src0 x) itr_tgt0)
    :
    _sim sim RR p_src m_src p_tgt m_tgt (trigger (Choose X) >>= ktr_src0) itr_tgt0
  | sim_chooseR
      X itr_src0 ktr_tgt0
      (SIM: forall x, _sim sim RR p_src m_src true m_tgt itr_src0 (ktr_tgt0 x))
    :
    _sim sim RR p_src m_src p_tgt m_tgt itr_src0 (trigger (Choose X) >>= ktr_tgt0)

  | sim_fairL
      f_src ktr_src0 itr_tgt0
      (SIM: exists m_src0, (<<FAIR: fair_update m_src m_src0 f_src>>) /\
                        (<<SIM: _sim sim RR true m_src0 p_tgt m_tgt (ktr_src0 tt) itr_tgt0>>))
    :
    _sim sim RR p_src m_src p_tgt m_tgt (trigger (Fair f_src) >>= ktr_src0) itr_tgt0
  | sim_fairR
      f_tgt itr_src0 ktr_tgt0
      (SIM: forall m_tgt0 (FAIR: fair_update m_tgt m_tgt0 f_tgt),
          _sim sim RR p_src m_src true m_tgt0 itr_src0 (ktr_tgt0 tt))
    :
    _sim sim RR p_src m_src p_tgt m_tgt itr_src0 (trigger (Fair f_tgt) >>= ktr_tgt0)

  | sim_progress
      itr_src0 itr_tgt0
      (SIM: sim _ _ RR false m_src false m_tgt itr_src0 itr_tgt0)
      (PSRC: p_src = true)
      (PTGT: p_tgt = true)
    :
    _sim sim RR p_src m_src p_tgt m_tgt itr_src0 itr_tgt0

  | sim_ub
      ktr_src0 itr_tgt0
    :
    _sim sim RR p_src m_src p_tgt m_tgt (trigger Undefined >>= ktr_src0) itr_tgt0
  .

  Lemma sim_ind (r: forall R0 R1 (RR: R0 -> R1 -> Prop), bool -> (@imap ids wfs)  -> bool -> (@imap idt wft) -> (@state ids R0) -> (@state idt R1) -> Prop)
        R0 R1 (RR: R0 -> R1 -> Prop)
        (P: bool -> (@imap ids wfs)  -> bool -> (@imap idt wft) -> (@state ids R0) -> (@state idt R1) -> Prop)
        (RET: forall
            p_src m_src p_tgt m_tgt
            r_src r_tgt
            (SIM: RR r_src r_tgt),
            P p_src m_src p_tgt m_tgt (Ret r_src) (Ret r_tgt))
        (OBS: forall
            p_src m_src p_tgt m_tgt ktr_src0 ktr_tgt0
            fn args
            (SIM: forall r_src r_tgt (EQ: r_src = r_tgt), r _ _ RR true m_src true m_tgt (ktr_src0 r_src) (ktr_tgt0 r_tgt)),
            P p_src m_src p_tgt m_tgt (Vis (Observe fn args) ktr_src0) (Vis (Observe fn args) ktr_tgt0))
        (TAUL: forall
            p_src m_src p_tgt m_tgt itr_src0 itr_tgt0
            (SIM: _sim r RR true m_src p_tgt m_tgt itr_src0 itr_tgt0)
            (IH: P true m_src p_tgt m_tgt itr_src0 itr_tgt0),
            P p_src m_src p_tgt m_tgt (Tau itr_src0) itr_tgt0)
        (TAUR: forall
            p_src m_src p_tgt m_tgt itr_src0 itr_tgt0
            (SIM: _sim r RR p_src m_src true m_tgt itr_src0 itr_tgt0)
            (IH: P p_src m_src true m_tgt itr_src0 itr_tgt0),
            P p_src m_src p_tgt m_tgt itr_src0 (Tau itr_tgt0))
        (CHOOSEL: forall
            p_src m_src p_tgt m_tgt X ktr_src0 itr_tgt0
            (SIM: exists x,
                (<<SIM: _sim r RR true m_src p_tgt m_tgt (ktr_src0 x) itr_tgt0>>) /\
                  (<<IH: P true m_src p_tgt m_tgt (ktr_src0 x) itr_tgt0>>)),
            P p_src m_src p_tgt m_tgt (ITree.bind (trigger (Choose X)) ktr_src0) itr_tgt0)
        (CHOOSER: forall
            p_src m_src p_tgt m_tgt X itr_src0 ktr_tgt0
            (SIM: forall x,
                (<<SIM: _sim r RR p_src m_src true m_tgt itr_src0 (ktr_tgt0 x)>>) /\
                  (<<IH: P p_src m_src true m_tgt itr_src0 (ktr_tgt0 x)>>)),
            P p_src m_src p_tgt m_tgt itr_src0 (ITree.bind (trigger (Choose X)) ktr_tgt0))
        (FAIRL: forall
            p_src m_src p_tgt m_tgt f_src ktr_src0 itr_tgt0
            (SIM: exists m_src0,
                (<<FAIR: fair_update m_src m_src0 f_src>>) /\
                  (<<SIM: _sim r RR true m_src0 p_tgt m_tgt (ktr_src0 tt) itr_tgt0>>) /\
                  (<<IH: P true m_src0 p_tgt m_tgt (ktr_src0 tt) itr_tgt0>>)),
            P p_src m_src p_tgt m_tgt (ITree.bind (trigger (Fair f_src)) ktr_src0) itr_tgt0)
        (FAIRR: forall
            p_src m_src p_tgt m_tgt f_tgt itr_src0 ktr_tgt0
            (SIM: forall m_tgt0 (FAIR: fair_update m_tgt m_tgt0 f_tgt),
                (<<SIM: _sim r RR p_src m_src true m_tgt0 itr_src0 (ktr_tgt0 tt)>>) /\
                  (<<IH: P p_src m_src true m_tgt0 itr_src0 (ktr_tgt0 tt)>>)),
            P p_src m_src p_tgt m_tgt itr_src0 (ITree.bind (trigger (Fair f_tgt)) ktr_tgt0))
        (PROGRESS: forall
            p_src m_src p_tgt m_tgt itr_src0 itr_tgt0
            (SIM: r _ _ RR false m_src false m_tgt itr_src0 itr_tgt0)
            (PSRC: p_src = true)
            (PTGT: p_tgt = true),
            P p_src m_src p_tgt m_tgt itr_src0 itr_tgt0)
        (UB: forall
            p_src m_src p_tgt m_tgt ktr_src0 itr_tgt0,
            P p_src m_src p_tgt m_tgt (ITree.bind (trigger Undefined) ktr_src0) itr_tgt0)
    :
    forall p_src m_src p_tgt m_tgt itr_src itr_tgt
      (SIM: _sim r RR p_src m_src p_tgt m_tgt itr_src itr_tgt),
      P p_src m_src p_tgt m_tgt itr_src itr_tgt.
  Proof.
    fix IH 7. i. inv SIM.
    { eapply RET; eauto. }
    { eapply OBS; eauto. }
    { eapply TAUL; eauto. }
    { eapply TAUR; eauto. }
    { eapply CHOOSEL; eauto. des. esplits; eauto. }
    { eapply CHOOSER; eauto. }
    { eapply FAIRL; eauto. des. esplits; eauto. }
    { eapply FAIRR; eauto. i. esplits; eauto. }
    { eapply PROGRESS; eauto. }
    { eapply UB; eauto. }
  Qed.

  Definition sim: forall R0 R1 (RR: R0 -> R1 -> Prop), bool -> (@imap ids wfs)  -> bool -> (@imap idt wft) -> (@state ids R0) -> (@state idt R1) -> Prop := paco9 _sim bot9.

  Lemma sim_mon: monotone9 _sim.
  Proof.
    ii. induction IN using sim_ind.
    { econs 1; eauto. }
    { econs 2; eauto. }
    { econs 3; eauto. }
    { econs 4; eauto. }
    { econs 5; eauto. des. esplits; eauto. }
    { econs 6; eauto. i. hexploit SIM. i; des. eauto. }
    { econs 7; eauto. des. esplits; eauto. }
    { econs 8; eauto. i. hexploit SIM. eauto. i; des. eauto. }
    { econs 9; eauto. }
    { econs 10; eauto. }
  Qed.

  Hint Constructors _sim: core.
  Hint Unfold sim: core.
  Hint Resolve sim_mon: paco.
  Hint Resolve cpn9_wcompat: paco.

  Lemma sim_ind2 R0 R1 (RR: R0 -> R1 -> Prop)
        (P: bool -> (@imap ids wfs)  -> bool -> (@imap idt wft) -> (@state ids R0) -> (@state idt R1) -> Prop)
        (RET: forall
            p_src m_src p_tgt m_tgt
            r_src r_tgt
            (SIM: RR r_src r_tgt),
            P p_src m_src p_tgt m_tgt (Ret r_src) (Ret r_tgt))
        (OBS: forall
            p_src m_src p_tgt m_tgt ktr_src0 ktr_tgt0
            fn args
            (SIM: forall r_src r_tgt (EQ: r_src = r_tgt), sim RR true m_src true m_tgt (ktr_src0 r_src) (ktr_tgt0 r_tgt)),
            P p_src m_src p_tgt m_tgt (Vis (Observe fn args) ktr_src0) (Vis (Observe fn args) ktr_tgt0))
        (TAUL: forall
            p_src m_src p_tgt m_tgt itr_src0 itr_tgt0
            (SIM: sim RR true m_src p_tgt m_tgt itr_src0 itr_tgt0)
            (IH: P true m_src p_tgt m_tgt itr_src0 itr_tgt0),
            P p_src m_src p_tgt m_tgt (Tau itr_src0) itr_tgt0)
        (TAUR: forall
            p_src m_src p_tgt m_tgt itr_src0 itr_tgt0
            (SIM: sim RR p_src m_src true m_tgt itr_src0 itr_tgt0)
            (IH: P p_src m_src true m_tgt itr_src0 itr_tgt0),
            P p_src m_src p_tgt m_tgt itr_src0 (Tau itr_tgt0))
        (CHOOSEL: forall
            p_src m_src p_tgt m_tgt X ktr_src0 itr_tgt0
            (SIM: exists x,
                (<<SIM: sim RR true m_src p_tgt m_tgt (ktr_src0 x) itr_tgt0>>) /\
                  (<<IH: P true m_src p_tgt m_tgt (ktr_src0 x) itr_tgt0>>)),
            P p_src m_src p_tgt m_tgt (ITree.bind (trigger (Choose X)) ktr_src0) itr_tgt0)
        (CHOOSER: forall
            p_src m_src p_tgt m_tgt X itr_src0 ktr_tgt0
            (SIM: forall x,
                (<<SIM: sim RR p_src m_src true m_tgt itr_src0 (ktr_tgt0 x)>>) /\
                  (<<IH: P p_src m_src true m_tgt itr_src0 (ktr_tgt0 x)>>)),
            P p_src m_src p_tgt m_tgt itr_src0 (ITree.bind (trigger (Choose X)) ktr_tgt0))
        (FAIRL: forall
            p_src m_src p_tgt m_tgt f_src ktr_src0 itr_tgt0
            (SIM: exists m_src0,
                (<<FAIR: fair_update m_src m_src0 f_src>>) /\
                  (<<SIM: sim RR true m_src0 p_tgt m_tgt (ktr_src0 tt) itr_tgt0>>) /\
                  (<<IH: P true m_src0 p_tgt m_tgt (ktr_src0 tt) itr_tgt0>>)),
            P p_src m_src p_tgt m_tgt (ITree.bind (trigger (Fair f_src)) ktr_src0) itr_tgt0)
        (FAIRR: forall
            p_src m_src p_tgt m_tgt f_tgt itr_src0 ktr_tgt0
            (SIM: forall m_tgt0 (FAIR: fair_update m_tgt m_tgt0 f_tgt),
                (<<SIM: sim RR p_src m_src true m_tgt0 itr_src0 (ktr_tgt0 tt)>>) /\
                  (<<IH: P p_src m_src true m_tgt0 itr_src0 (ktr_tgt0 tt)>>)),
            P p_src m_src p_tgt m_tgt itr_src0 (ITree.bind (trigger (Fair f_tgt)) ktr_tgt0))
        (PROGRESS: forall
            p_src m_src p_tgt m_tgt itr_src0 itr_tgt0
            (SIM: sim RR false m_src false m_tgt itr_src0 itr_tgt0)
            (PSRC: p_src = true)
            (PTGT: p_tgt = true),
            P p_src m_src p_tgt m_tgt itr_src0 itr_tgt0)
        (UB: forall
            p_src m_src p_tgt m_tgt ktr_src0 itr_tgt0,
            P p_src m_src p_tgt m_tgt (ITree.bind (trigger Undefined) ktr_src0) itr_tgt0)
    :
    forall p_src m_src p_tgt m_tgt itr_src itr_tgt
      (SIM: sim RR p_src m_src p_tgt m_tgt itr_src itr_tgt),
      P p_src m_src p_tgt m_tgt itr_src itr_tgt.
  Proof.
    i. eapply sim_ind; i; eauto.
    { eapply TAUL; eauto. pfold. eapply sim_mon; eauto. }
    { eapply TAUR; eauto. pfold. eapply sim_mon; eauto. }
    { eapply CHOOSEL; eauto. des. esplits; eauto. pfold. eapply sim_mon; eauto. }
    { eapply CHOOSER; eauto. i. specialize (SIM0 x). des. esplits; eauto. pfold. eapply sim_mon; eauto. }
    { eapply FAIRL; eauto. des. esplits; eauto. pfold. eapply sim_mon; eauto. }
    { eapply FAIRR; eauto. i. eapply SIM0 in FAIR. des. esplits; eauto. pfold. eapply sim_mon; eauto. }
    { clear - SIM. punfold SIM. eapply sim_mon; eauto. i. pclearbot. eauto. }
  Qed.

  Definition gsim: forall R0 R1 (RR: R0 -> R1 -> Prop), (@state ids R0) -> (@state idt R1) -> Prop :=
    fun R0 R1 RR src tgt => forall (mt: imap idt wft), (exists (ms: imap ids wfs) ps pt, sim RR ps ms pt mt src tgt).

  (****************************************************)
  (*********************** upto ***********************)
  (****************************************************)

  Variant sim_imap_ctxL
          (sim: forall R0 R1: Type, (R0 -> R1 -> Prop) -> bool -> (@imap ids wfs) -> bool -> (@imap idt wft) -> (@state ids R0) -> (@state idt R1) -> Prop)
          R0 R1 (RR: R0 -> R1 -> Prop)
    :
    bool -> (@imap ids wfs) -> bool -> (@imap idt wft) -> (@state ids R0) -> (@state idt R1) -> Prop :=
    | sim_imap_ctxL_intro
        msrc0 msrc1 mtgt psrc ptgt st_src st_tgt
        (SIM: @sim _ _ RR psrc msrc1 ptgt mtgt st_src st_tgt)
        (IMAP: soft_update msrc0 msrc1)
      :
      sim_imap_ctxL sim RR psrc msrc0 ptgt mtgt st_src st_tgt.

  Lemma sim_imap_ctxL_mon: monotone9 sim_imap_ctxL.
  Proof. ii. inv IN. econs; eauto. Qed.

  Hint Resolve sim_imap_ctxL_mon: paco.

  Lemma sim_imap_ctxL_wrepectful: wrespectful9 _sim sim_imap_ctxL.
  Proof.
    econs; eauto with paco.
    i. inv PR. apply GF in SIM. depgen x4. induction SIM using sim_ind; i; eauto.
    { econs. i. subst. eapply rclo9_clo_base. econs; eauto. }
    { des. econs. eexists. eapply IH. eauto. }
    { econs. i. specialize (SIM x). des. eapply IH. eauto. }
    { econs. des. rename x4 into M_SRC, m_src0 into m_src'.
      pose (M_SRC' := fun i => match f_src i with
                            | Flag.fail => match excluded_middle_informative (M_SRC i = m_src i) with
                                          | left _ => m_src' i
                                          | right _ => m_src i
                                          end
                            | Flag.emp => M_SRC i
                            | Flag.success => m_src' i
                            end).
      exists M_SRC'. splits.
      - subst M_SRC'. ii. specialize (FAIR i). specialize (IMAP i). des_ifs.
        + rewrite e. eauto.
        + destruct IMAP; ss. exfalso. eauto.
      - eapply IH. subst M_SRC'. ii. specialize (FAIR i). specialize (IMAP i).
        des_ifs; try reflexivity. destruct IMAP.
        + exfalso. eauto.
        + right. eauto.
        + rewrite FAIR. auto.
    }
    { econs. i. specialize (SIM m_tgt0). eapply SIM in FAIR. des. eauto. }
    { clarify. econs; eauto. eapply rclo9_clo_base. econs; eauto. }
  Qed.

  Lemma sim_imap_ctxL_spec: sim_imap_ctxL <10= gupaco9 _sim (cpn9 _sim).
  Proof. i. eapply wrespect9_uclo; eauto with paco. eapply sim_imap_ctxL_wrepectful. Qed.



  Variant sim_imap_ctxR
          (sim: forall R0 R1: Type, (R0 -> R1 -> Prop) -> bool -> (@imap ids wfs) -> bool -> (@imap idt wft) -> (@state ids R0) -> (@state idt R1) -> Prop)
          R0 R1 (RR: R0 -> R1 -> Prop)
    :
    bool -> (@imap ids wfs) -> bool -> (@imap idt wft) -> (@state ids R0) -> (@state idt R1) -> Prop :=
    | sim_imap_ctxR_intro
        msrc mtgt0 mtgt1 psrc ptgt st_src st_tgt
        (SIM: @sim _ _ RR psrc msrc ptgt mtgt1 st_src st_tgt)
        (IMAP: soft_update mtgt1 mtgt0)
      :
      sim_imap_ctxR sim RR psrc msrc ptgt mtgt0 st_src st_tgt.

  Lemma sim_imap_ctxR_mon: monotone9 sim_imap_ctxR.
  Proof. ii. inv IN. econs; eauto. Qed.

  Hint Resolve sim_imap_ctxR_mon: paco.

  Lemma sim_imap_ctxR_wrepectful: wrespectful9 _sim sim_imap_ctxR.
  Proof.
    econs; eauto with paco.
    i. inv PR. apply GF in SIM. depgen x6. induction SIM using sim_ind; i; eauto.
    { econs. i. subst. eapply rclo9_clo_base. econs; eauto. }
    { des. econs. eexists. eauto. }
    { econs. i. specialize (SIM x). des. eauto. }
    { econs. des. esplits; eauto. }
    { econs. i. rename m_tgt into M_TGT, x6 into m_tgt, m_tgt0 into m_tgt'.
      pose (M_TGT' := fun i => match f_tgt i with
                            | Flag.fail => match excluded_middle_informative (M_TGT i = m_tgt i) with
                                          | left _ => m_tgt' i
                                          | right _ => m_tgt i
                                          end
                            | Flag.emp => M_TGT i
                            | Flag.success => m_tgt' i
                            end).
      hexploit SIM. instantiate (1 := M_TGT').
      - subst M_TGT'. ii. specialize (IMAP i). specialize (FAIR i). des_ifs.
        + rewrite e. ss.
        + destruct IMAP; eauto. exfalso. eauto.
      - i; des. eapply IH. subst M_TGT'. ii. specialize (IMAP i). specialize (FAIR i).
        des_ifs; try reflexivity. destruct IMAP.
        + exfalso. eauto.
        + right. eauto.
        + rewrite FAIR; auto.
    }
    { clarify. econs; eauto. eapply rclo9_clo_base. econs; eauto. }
  Qed.

  Lemma sim_imap_ctxR_spec: sim_imap_ctxR <10= gupaco9 _sim (cpn9 _sim).
  Proof. i. eapply wrespect9_uclo; eauto with paco. eapply sim_imap_ctxR_wrepectful. Qed.



  Variant sim_indC
          (sim: forall R0 R1: Type, (R0 -> R1 -> Prop) -> bool -> (@imap ids wfs) -> bool -> (@imap idt wft) -> (@state ids R0) -> (@state idt R1) -> Prop)
          R0 R1 (RR: R0 -> R1 -> Prop) (p_src: bool) (m_src: @imap ids wfs) (p_tgt: bool) (m_tgt: @imap idt wft)
    :
    (@state ids R0) -> (@state idt R1) -> Prop :=
    | sim_indC_ret
        r_src r_tgt
        (SIM: RR r_src r_tgt)
      :
      sim_indC sim RR p_src m_src p_tgt m_tgt (Ret r_src) (Ret r_tgt)
    | sim_indC_obs
        ktr_src0 ktr_tgt0 fn args
        (SIM: forall r_src r_tgt (EQ: r_src = r_tgt),
            sim _ _ RR true m_src true m_tgt (ktr_src0 r_src) (ktr_tgt0 r_tgt))
      :
      sim_indC sim RR p_src m_src p_tgt m_tgt (trigger (Observe fn args) >>= ktr_src0) (trigger (Observe fn args) >>= ktr_tgt0)

    | sim_indC_tauL
        itr_src0 itr_tgt0
        (SIM: sim _ _ RR true m_src p_tgt m_tgt itr_src0 itr_tgt0)
      :
      sim_indC sim RR p_src m_src p_tgt m_tgt (Tau itr_src0) itr_tgt0
    | sim_indC_tauR
        itr_src0 itr_tgt0
        (SIM: sim _ _ RR p_src m_src true m_tgt itr_src0 itr_tgt0)
      :
      sim_indC sim RR p_src m_src p_tgt m_tgt itr_src0 (Tau itr_tgt0)
    | sim_indC_chooseL
        X ktr_src0 itr_tgt0
        (SIM: exists x, sim _ _ RR true m_src p_tgt m_tgt (ktr_src0 x) itr_tgt0)
      :
      sim_indC sim RR p_src m_src p_tgt m_tgt (trigger (Choose X) >>= ktr_src0) itr_tgt0
    | sim_indC_chooseR
        X itr_src0 ktr_tgt0
        (SIM: forall x, sim _ _ RR p_src m_src true m_tgt itr_src0 (ktr_tgt0 x))
      :
      sim_indC sim RR p_src m_src p_tgt m_tgt itr_src0 (trigger (Choose X) >>= ktr_tgt0)

    | sim_indC_fairL
        f_src ktr_src0 itr_tgt0
        (SIM: exists m_src0, (<<FAIR: fair_update m_src m_src0 f_src>>) /\
                          (<<SIM: sim _ _ RR true m_src0 p_tgt m_tgt (ktr_src0 tt) itr_tgt0>>))
      :
      sim_indC sim RR p_src m_src p_tgt m_tgt (trigger (Fair f_src) >>= ktr_src0) itr_tgt0
    | sim_indC_fairR
        f_tgt itr_src0 ktr_tgt0
        (SIM: forall m_tgt0 (FAIR: fair_update m_tgt m_tgt0 f_tgt),
            sim _ _ RR p_src m_src true m_tgt0 itr_src0 (ktr_tgt0 tt))
      :
      sim_indC sim RR p_src m_src p_tgt m_tgt itr_src0 (trigger (Fair f_tgt) >>= ktr_tgt0)

    | sim_indC_progress
        itr_src0 itr_tgt0
        (SIM: sim _ _ RR false m_src false m_tgt itr_src0 itr_tgt0)
        (PSRC: p_src = true)
        (PTGT: p_tgt = true)
      :
      sim_indC sim RR p_src m_src p_tgt m_tgt itr_src0 itr_tgt0

    | sim_indC_ub
        ktr_src0 itr_tgt0
      :
      sim_indC sim RR p_src m_src p_tgt m_tgt (trigger Undefined >>= ktr_src0) itr_tgt0
  .

  Lemma sim_indC_mon: monotone9 sim_indC.
  Proof.
    ii. inv IN.
    1,2,3,4,5,6,7,8,9: econs; eauto.
    { des; eauto. }
    { des; esplits; eauto. }
    { econs 10. }
  Qed.

  Hint Resolve sim_indC_mon: paco.

  Lemma sim_indC_wrepectful: wrespectful9 _sim sim_indC.
  Proof.
    econs; eauto with paco.
    i. inv PR; eauto.
    { rewrite ! bind_trigger. econs; eauto. i. eapply rclo9_base. eauto. }
    { econs; eauto. eapply sim_mon; eauto. i. eapply rclo9_base. auto. }
    { econs; eauto. eapply sim_mon; eauto. i. eapply rclo9_base. auto. }
    { econs; eauto. des. eexists. eapply sim_mon; eauto. i. eapply rclo9_base. auto. }
    { econs; eauto. i. eapply sim_mon; eauto. i. eapply rclo9_base. auto. }
    { econs; eauto. des. esplits; eauto. eapply sim_mon; eauto. i. eapply rclo9_base. auto. }
    { econs; eauto. i. eapply sim_mon; eauto. i. eapply rclo9_base. auto. }
    { eapply sim_mon. econs 9; eauto. i. eapply rclo9_base. auto. }
  Qed.

  Lemma sim_indC_spec: sim_indC <10= gupaco9 _sim (cpn9 _sim).
  Proof. i. eapply wrespect9_uclo; eauto with paco. eapply sim_indC_wrepectful. Qed.



  Variant sim_progress_ctx
          (sim: forall R0 R1: Type, (R0 -> R1 -> Prop) -> bool -> (@imap ids wfs) -> bool -> (@imap idt wft) -> (@state ids R0) -> (@state idt R1) -> Prop)
          R0 R1 (RR: R0 -> R1 -> Prop)
    :
    bool -> (@imap ids wfs) -> bool -> (@imap idt wft) -> (@state ids R0) -> (@state idt R1) -> Prop :=
    | sim_progress_intro
        msrc mtgt psrc0 psrc1 ptgt0 ptgt1 st_src st_tgt
        (SIM: @sim _ _ RR psrc1 msrc ptgt1 mtgt st_src st_tgt)
        (SRC: psrc1 = true -> psrc0 = true)
        (TGT: ptgt1 = true -> ptgt0 = true)
      :
      sim_progress_ctx sim RR psrc0 msrc ptgt0 mtgt st_src st_tgt.

  Lemma sim_progress_ctx_mon: monotone9 sim_progress_ctx.
  Proof. ii. inv IN. econs; eauto. Qed.

  Hint Resolve sim_progress_ctx_mon: paco.

  Lemma sim_progress_ctx_wrepectful: wrespectful9 _sim sim_progress_ctx.
  Proof.
    econs; eauto with paco.
    i. inv PR. apply GF in SIM. depgen x3. depgen x5. induction SIM using sim_ind; i; eauto.
    { econs. i. subst. eapply rclo9_clo_base. econs; eauto. }
    { des. econs. eexists. eapply IH; eauto. }
    { econs. i. specialize (SIM x). des. eapply IH; eauto. }
    { econs. des. esplits.
      2:{ eapply IH; eauto. }
      eauto.
    }
    { econs. i. specialize (SIM m_tgt0). eapply SIM in FAIR. des. eauto. }
    { clarify. hexploit TGT; clear TGT; auto; i; clarify. hexploit SRC; clear SRC; auto; i; clarify.
      eapply sim_mon; eauto. i. eapply rclo9_base. auto. }
  Qed.

  Lemma sim_progress_ctx_spec: sim_progress_ctx <10= gupaco9 _sim (cpn9 _sim).
  Proof. i. eapply wrespect9_uclo; eauto with paco. eapply sim_progress_ctx_wrepectful. Qed.

End SIM.
#[export] Hint Constructors _sim: core.
#[export] Hint Unfold sim: core.
#[export] Hint Resolve sim_mon: paco.
#[export] Hint Resolve cpn9_wcompat: paco.


Section EMBEDSIM.
  Lemma sim_embedded_src_ord (ids idt: ID)
        (wfs wft: WF)
        (wfs_lift: WF)
        (wfs_embed: wfs.(T) -> wfs_lift.(T))
        (wfs_embed_lt: forall o0 o1 (LT: wfs.(lt) o0 o1), wfs_lift.(lt) (wfs_embed o0) (wfs_embed o1))
    :
    forall
      (R0 R1: Type) (RR: R0 -> R1 -> Prop)
      (ps pt: bool) (src: @state ids R0) (tgt: @state idt R1)
      (mt: @imap idt wft) (ms: @imap ids wfs)
      (SIM: sim RR ps ms pt mt src tgt),
      sim RR ps (fun id => wfs_embed (ms id)) pt mt src tgt.
  Proof.
    ginit. gcofix CIH. i. punfold SIM. revert ps ms pt mt src tgt SIM. eapply sim_ind; i.
    { guclo sim_indC_spec. econs 1. eauto. }
    { gstep. econs 2; eauto. i. hexploit SIM; eauto. i. pclearbot. gbase. auto. }
    { guclo sim_indC_spec. econs 3. eauto. }
    { guclo sim_indC_spec. econs 4. eauto. }
    { des. guclo sim_indC_spec. econs 5. eexists x. eauto. }
    { guclo sim_indC_spec. econs 6. i. specialize (SIM x). des. eauto. }
    { des. guclo sim_indC_spec. econs 7. eexists (fun id => wfs_embed (m_src0 id)).
      splits; eauto. ii. specialize (FAIR i). des_ifs; ss; eauto.
      inv FAIR; eauto.
    }
    { guclo sim_indC_spec. econs 8. i. specialize (SIM m_tgt0 FAIR). des. eauto. }
    { gstep. econs 9; eauto. pclearbot. gbase. eauto. }
    { gstep. econs 10; eauto. }
  Qed.

  Lemma gsim_embedded_src_ord (ids idt: ID)
        (wfs wft: WF)
        (wfs_lift: WF)
        (wfs_embed: wfs.(T) -> wfs_lift.(T))
        (wfs_embed_lt: forall o0 o1 (LT: wfs.(lt) o0 o1), wfs_lift.(lt) (wfs_embed o0) (wfs_embed o1))
    :
    forall
      (R0 R1: Type) (RR: R0 -> R1 -> Prop)
      (src: @state ids R0) (tgt: @state idt R1)
      (SIM: gsim wfs wft RR src tgt),
      gsim wfs_lift wft RR src tgt.
  Proof.
    unfold gsim. i. specialize (SIM mt). des.
    esplits. eapply sim_embedded_src_ord; eauto.
  Qed.
End EMBEDSIM.


Section EX.

  Let Ident : ID := nat.
  Program Definition nat_wf: WF := @mk_wf nat Peano.lt _.
  Program Instance nat_wf_Trans: Transitive nat_wf.(lt).
  Next Obligation.
    eapply PeanoNat.Nat.lt_strorder; eauto.
  Qed.

  Definition while_itree (step: unit -> itree (@eventE Ident) (unit + unit)) : itree (@eventE Ident) unit :=
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
      itr;;; tau;; (while_itree (fun u => ITree.bind itr (fun r => Ret (inl r)))).
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
  Definition ndec := PeanoNat.Nat.eq_dec.

  Definition src1: @state Ident nat := Ret 0.
  Definition tgt1: @state _ nat :=
    while_itree (fun u => (trigger (Fair (fun id => (if ndec 0 id then Flag.fail else Flag.emp)))) >>= (fun r => Ret (inl r)));;; Ret 0.

  Definition imsrc1: imap Ident nat_wf := fun id => (if ndec 0 id then 100 else 0).
  (* Definition imtgt1: imap nat_wf := fun id => (if ndec 0 id then 100 else 0). *)

  Goal gsim nat_wf nat_wf RR src1 tgt1.
  Proof.
    ii. exists imsrc1, false, false.
    unfold src1, tgt1.
    remember (mt 0) as t_fuel. depgen mt.
    (* unfold imtgt1. remember 100 as t_fuel. clear Heqt_fuel. *)
    induction t_fuel; i.
    { ginit. rewrite unfold_while_itree. ired. guclo sim_indC_spec. econs. i. exfalso.
      unfold fair_update in FAIR. specialize (FAIR 0). rewrite <- Heqt_fuel in FAIR.
      ss. inv FAIR.
    }
    ginit. rewrite unfold_while_itree. guclo sim_indC_spec. ired. econs 8. i.
    dup FAIR. specialize (FAIR0 0). rewrite <- Heqt_fuel in FAIR0. ss.
    guclo sim_indC_spec. econs.
    guclo sim_imap_ctxR_spec. econs.
    2:{ instantiate (1:= fun id => (if ndec 0 id then t_fuel else (m_tgt0 id))). ii.
        des_ifs.
        - inv FAIR0. left; auto. right. ss.
        - left. auto.
    }
    guclo sim_progress_ctx_spec. econs.
    { gfinal. right. eapply IHt_fuel. ss. }
    { i; clarify. }
    { i; clarify. }
  Qed.


  (** counterexample for progress resetting fair index **)

  (* Definition src2: @state _ nat := *)
  (*   while_itree (fun u => r <- trigger (Fair (fun id => (if ndec 0 id then Flag.fail else Flag.emp)));; Ret (inl r));; Ret 0. *)
  (* Definition tgt2: @state _ nat := *)
  (*   while_itree (fun u => r <- trigger (Fair (fun id => (if ndec 0 id then Flag.success else Flag.emp)));; Ret (inl r));; Ret 0. *)

  (* Definition imsrc2: imap := fun id => (if ndec 0 id then 100 else 0). *)
  (* Definition imtgt2: imap := fun id => (if ndec 0 id then 100 else 0). *)

  (* Ltac rewrite2 H := *)
  (*   match goal with *)
  (*   | |- gpaco9 _ _ _ _ _ _ _ _ _ _ _ ?a _ => set (temp:=a); rewrite H; subst temp *)
  (*   end. *)

  (* Goal sim RR false imsrc2 false imtgt2 src2 tgt2. *)
  (* Proof. *)
  (*   unfold src2, tgt2. unfold imsrc2, imtgt2. *)
  (*   ginit. gcofix CIH. *)
  (*   rewrite unfold_while_itree. rewrite2 unfold_while_itree. *)
  (*   rewrite bind_bind. rewrite2 bind_bind. *)
  (*   guclo sim_indC_spec. econs 7. esplits. *)
  (*   2:{ guclo sim_indC_spec. econs 8. i. rewrite bind_tau. rewrite2 bind_tau. *)
  (*       guclo sim_indC_spec. econs 3. guclo sim_indC_spec. econs 4. *)
  (*       gstep. econs 9; eauto. gfinal. left. eauto. *)
  (*   } *)
  (*   instantiate (1:= fun id => if ndec 0 id then 0 else 0). clear. *)
  (*   ii. des_ifs. lia. *)
  (* Qed. *)

End EX.
