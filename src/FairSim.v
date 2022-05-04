From sflib Require Import sflib.
From ITree Require Export ITree.
From Paco Require Import paco.

Export ITreeNotations.

Require Import Coq.Classes.RelationClasses.
Require Import Program.
Require Import Lia.

From Fairness Require Import ITreeLib.
From Fairness Require Import FairBeh.

Set Implicit Arguments.

Section SIM.

  Context {Ident: ID}.

  (* Definition stuck_idx (m: imap) (j: id) := le (m j) 0. *)

  Inductive _sim
            (sim: forall R0 R1 (RR: R0 -> R1 -> Prop), bool -> imap -> bool  -> imap -> (@state _ R0) -> (@state _ R1) -> Prop)
            {R0 R1} (RR: R0 -> R1 -> Prop) (p_src: bool) (m_src: imap) (p_tgt: bool) (m_tgt: imap) :
    (@state _ R0) -> (@state _ R1) -> Prop :=
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
      itr_src0 itr_tgt0 m_src0 m_tgt0
      (SIM: sim _ _ RR false m_src0 false m_tgt0 itr_src0 itr_tgt0)
      (PSRC: p_src = true)
      (PTGT: p_tgt = true)
    :
    _sim sim RR p_src m_src p_tgt m_tgt itr_src0 itr_tgt0

  | sim_ub
      ktr_src0 itr_tgt0
    :
    _sim sim RR p_src m_src p_tgt m_tgt (trigger Undefined >>= ktr_src0) itr_tgt0
  .

  Lemma sim_ind (r: forall R0 R1 (RR: R0 -> R1 -> Prop), bool -> imap  -> bool -> imap -> (@state _ R0) -> (@state _ R1) -> Prop)
        R0 R1 (RR: R0 -> R1 -> Prop)
        (P: bool -> imap  -> bool -> imap -> (@state _ R0) -> (@state _ R1) -> Prop)
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
            p_src m_src p_tgt m_tgt m_src0 m_tgt0 itr_src0 itr_tgt0
            (SIM: r _ _ RR false m_src0 false m_tgt0 itr_src0 itr_tgt0)
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

  Definition sim: forall R0 R1 (RR: R0 -> R1 -> Prop), bool -> imap  -> bool -> imap -> (@state _ R0) -> (@state _ R1) -> Prop := paco9 _sim bot9.

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

  Hint Constructors _sim.
  Hint Unfold sim.
  Hint Resolve sim_mon: paco.
  Hint Resolve cpn9_wcompat: paco.

  Lemma sim_ind2 R0 R1 (RR: R0 -> R1 -> Prop)
        (P: bool -> imap  -> bool -> imap -> (@state _ R0) -> (@state _ R1) -> Prop)
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
            p_src m_src p_tgt m_tgt m_src0 m_tgt0 itr_src0 itr_tgt0
            (SIM: sim RR false m_src0 false m_tgt0 itr_src0 itr_tgt0)
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

  (****************************************************)
  (*********************** upto ***********************)
  (****************************************************)

  Variant sim_imap_ctxL
          (sim: forall R0 R1: Type, (R0 -> R1 -> Prop) -> bool -> imap -> bool -> imap -> state -> state -> Prop)
          R0 R1 (RR: R0 -> R1 -> Prop)
    :
    bool -> imap -> bool -> imap -> (@state _ R0) -> (@state _ R1) -> Prop :=
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
    { econs. des. esplits.
      2:{ eapply IH. reflexivity. }
      clear - FAIR IMAP. unfold fair_update, soft_update in *. i. specialize (FAIR i). specialize (IMAP i). des_ifs; lia.
    }
    { econs. i. specialize (SIM m_tgt0). eapply SIM in FAIR. des. eauto. }
    { clarify. eapply sim_mon; eauto. i. eapply rclo9_base. auto. }
  Qed.

  Lemma sim_imap_ctxL_spec: sim_imap_ctxL <10= gupaco9 _sim (cpn9 _sim).
  Proof. i. eapply wrespect9_uclo; eauto with paco. eapply sim_imap_ctxL_wrepectful. Qed.



  Variant sim_imap_ctxR
          (sim: forall R0 R1: Type, (R0 -> R1 -> Prop) -> bool -> imap -> bool -> imap -> state -> state -> Prop)
          R0 R1 (RR: R0 -> R1 -> Prop)
    :
    bool -> imap -> bool -> imap -> (@state _ R0) -> (@state _ R1) -> Prop :=
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
    { econs. i. hexploit SIM.
      2:{ i; des. eapply IH. reflexivity. }
      clear - IMAP FAIR. unfold fair_update, soft_update in *. i. specialize (IMAP i). specialize (FAIR i). des_ifs; lia.
    }
    { clarify. eapply sim_mon; eauto. i. eapply rclo9_base. auto. }
  Qed.

  Lemma sim_imap_ctxR_spec: sim_imap_ctxR <10= gupaco9 _sim (cpn9 _sim).
  Proof. i. eapply wrespect9_uclo; eauto with paco. eapply sim_imap_ctxR_wrepectful. Qed.



  Variant sim_indC
          (sim: forall R0 R1: Type, (R0 -> R1 -> Prop) -> bool -> imap -> bool -> imap -> (@state _ R0) -> (@state _ R1) -> Prop)
          R0 R1 (RR: R0 -> R1 -> Prop) (p_src: bool) (m_src: imap) (p_tgt: bool) (m_tgt: imap)
    :
    (@state _ R0) -> (@state _ R1) -> Prop :=
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
      sim_indC sim RR p_src m_src p_tgt m_tgt (Vis (Observe fn args) ktr_src0) (Vis (Observe fn args) ktr_tgt0)

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
        itr_src0 itr_tgt0 m_src0 m_tgt0
        (SIM: sim _ _ RR false m_src0 false m_tgt0 itr_src0 itr_tgt0)
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
    { econs; eauto. i. eapply rclo9_base. eauto. }
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

End SIM.
#[export] Hint Constructors _sim.
#[export] Hint Unfold sim.
#[export] Hint Resolve sim_mon: paco.
#[export] Hint Resolve cpn9_wcompat: paco.



Section EX.

  Instance Ident : ID := mk nat.

  (* Definition uunit := prod unit unit. *)

  Definition while_itree (step: unit -> itree eventE (unit + unit)) : itree eventE unit :=
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
  Definition ndec := PeanoNat.Nat.eq_dec.

  Definition src1: @state _ nat := Ret 0.
  Definition tgt1: @state _ nat :=
    while_itree (fun u => (trigger (Fair (fun id => (if ndec 0 id then Flag.fail else Flag.emp)))) >>= (fun r => Ret (inl r)));; Ret 0.

  Definition imsrc1: imap := fun id => (if ndec 0 id then 100 else 0).
  Definition imtgt1: imap := fun id => (if ndec 0 id then 100 else 0).

  Goal sim RR false imsrc1 false imtgt1 src1 tgt1.
  Proof.
    unfold src1, tgt1.
    ginit. gcofix CIH. rewrite unfold_while_itree. ired.
    guclo sim_indC_spec. econs 8. i.
    guclo sim_indC_spec. econs.
    guclo sim_imap_ctxR_spec. econs.
    { rewrite unfold_while_itree. ired. guclo sim_indC_spec. econs. i.
      instantiate (1:=fun id => 0) in FAIR0.
      exfalso. unfold fair_update in FAIR0. specialize FAIR0 with 0. ss. lia.
    }
    
    


      inv FAIR0.
      exfalso. unfold update_

    
    guclo sim_indC_spec. econs 8. i.
    guclo sim_imap_ctxR_spec. econs.
    { guclo sim_indC_spec. econs. 

      instantiate (1:= fun id => 0).

    gstep. rewrite unfold_while_itree. ired.
    econs 8. i. guclo sim_imap_ctxR.

    econs.
    


    
    pcofix CIH. pfold. rewrite unfold_while_itree. ired.
    econs 8. i.
    econs.
    { rewrite unfold_while_itree. ired. econs 8. i.
      instantiate (1:= fun id => 0) in FAIR0.
      exfalso. unfold fair_update in FAIR0. specialize FAIR0 with 0. ss. inv FAIR0.
    }
    ii. apply PeanoNat.Nat.le_0_l.
  Qed.

End EX.
