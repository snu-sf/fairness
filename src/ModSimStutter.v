From sflib Require Import sflib.
From Paco Require Import paco.
Require Export Coq.Strings.String.

From Fairness Require Export ITreeLib FairBeh Mod.
From Fairness Require Import pind8.

Set Implicit Arguments.



Section PRIMIVIESIM.
  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable _ident_src: ID.
  Definition ident_src := sum_tid _ident_src.
  Variable _ident_tgt: ID.
  Definition ident_tgt := sum_tid _ident_tgt.

  Variable wf_src: WF.
  Variable wf_tgt: WF.

  Let srcE := ((@eventE _ident_src +' cE) +' sE state_src).
  Let tgtE := ((@eventE _ident_tgt +' cE) +' sE state_tgt).

  Variable world: Type.
  Variable world_le: world -> world -> Prop.

  Definition shared :=
    (TIdSet.t *
       (@imap ident_src wf_src) *
       (@imap ident_tgt wf_tgt) *
       state_src *
       state_tgt *
       world)%type.

  Let shared_rel: Type := shared -> Prop.

  Definition shared_rel_wf (r: shared_rel): Prop :=
    forall ths im_src0 im_tgt0 st_src st_tgt w0
           (INV: r (ths, im_src0, im_tgt0, st_src, st_tgt, w0))
           im_tgt1 (TGT: fair_update im_tgt0 im_tgt1 (sum_fmap_l (tids_fmap_all ths))),
    exists im_src1 w1,
      (<<SRC: fair_update im_src0 im_src1 (sum_fmap_l (tids_fmap_all ths))>>) /\
        (<<INV: r (ths, im_src1, im_tgt1, st_src, st_tgt, w1)>>) /\
        (<<WORLD: world_le w0 w1>>).

  Variable I: shared_rel.

  Variant __lsim
          (tid: thread_id.(id))
          (lsim: forall R_src R_tgt (RR: R_src -> R_tgt -> shared_rel), bool -> bool -> (wf_src.(T) * itree srcE R_src) -> itree tgtE R_tgt -> shared_rel)
          (_lsim: forall R_src R_tgt (RR: R_src -> R_tgt -> shared_rel),bool -> bool -> (wf_src.(T) * itree srcE R_src) -> itree tgtE R_tgt -> shared_rel)
          R_src R_tgt (RR: R_src -> R_tgt -> shared_rel)
    :
    bool -> bool -> (wf_src.(T) * itree srcE R_src) -> itree tgtE R_tgt -> shared_rel :=
  | lsim_ret
      f_src f_tgt o
      ths im_src im_tgt st_src st_tgt w
      r_src r_tgt
      (LSIM: RR r_src r_tgt (ths, im_src, im_tgt, st_src, st_tgt, w))
    :
    __lsim tid lsim _lsim RR f_src f_tgt (o, Ret r_src) (Ret r_tgt) (ths, im_src, im_tgt, st_src, st_tgt, w)

  | lsim_tauL
      f_src f_tgt o
      ths im_src im_tgt st_src st_tgt w
      itr_src itr_tgt
      (LSIM: _lsim _ _ RR true f_tgt (o, itr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, w))
    :
    __lsim tid lsim _lsim RR f_src f_tgt (o, Tau itr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, w)
  | lsim_chooseL
      f_src f_tgt o
      ths im_src im_tgt st_src st_tgt w
      X ktr_src itr_tgt
      (LSIM: exists x, _lsim _ _ RR true f_tgt (o, ktr_src x) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, w))
    :
    __lsim tid lsim _lsim RR f_src f_tgt (o, trigger (Choose X) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, w)
  | lsim_putL
      f_src f_tgt o
      ths im_src im_tgt st_src st_tgt w
      st ktr_src itr_tgt
      (LSIM: _lsim _ _ RR true f_tgt (o, ktr_src tt) itr_tgt (ths, im_src, im_tgt, st, st_tgt, w))
    :
    __lsim tid lsim _lsim RR f_src f_tgt (o, trigger (Put st) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, w)
  | lsim_getL
      f_src f_tgt o
      ths im_src im_tgt st_src st_tgt w
      ktr_src itr_tgt
      (LSIM: _lsim _ _ RR true f_tgt (o, ktr_src st_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, w))
    :
    __lsim tid lsim _lsim RR f_src f_tgt (o, trigger (@Get _) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, w)
  | lsim_tidL
      f_src f_tgt o
      ths im_src im_tgt st_src st_tgt w
      ktr_src itr_tgt
      (LSIM: _lsim _ _ RR true f_tgt (o, ktr_src tid) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, w))
    :
    __lsim tid lsim _lsim RR f_src f_tgt (o, trigger (GetTid) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, w)
  | lsim_UB
      f_src f_tgt o
      ths im_src im_tgt st_src st_tgt w
      ktr_src itr_tgt
    :
    __lsim tid lsim _lsim RR f_src f_tgt (o, trigger (Undefined) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, w)
  | lsim_fairL
      f_src f_tgt o
      ths im_src0 im_tgt st_src st_tgt w
      f ktr_src itr_tgt
      (LSIM: exists im_src1,
          (<<FAIR: fair_update im_src0 im_src1 (sum_fmap_r f)>>) /\
            (<<LSIM: _lsim _ _ RR true f_tgt (o, ktr_src tt) itr_tgt (ths, im_src1, im_tgt, st_src, st_tgt, w)>>))
    :
    __lsim tid lsim _lsim RR f_src f_tgt (o, trigger (Fair f) >>= ktr_src) itr_tgt (ths, im_src0, im_tgt, st_src, st_tgt, w)

  | lsim_tauR
      f_src f_tgt
      ths im_src im_tgt st_src st_tgt w
      itr_src itr_tgt
      (LSIM: _lsim _ _ RR f_src true itr_src itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, w))
    :
    __lsim tid lsim _lsim RR f_src f_tgt itr_src (Tau itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, w)
  | lsim_chooseR
      f_src f_tgt
      ths im_src im_tgt st_src st_tgt w
      X itr_src ktr_tgt
      (LSIM: forall x, _lsim _ _ RR f_src true itr_src (ktr_tgt x) (ths, im_src, im_tgt, st_src, st_tgt, w))
    :
    __lsim tid lsim _lsim RR f_src f_tgt itr_src (trigger (Choose X) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, w)
  | lsim_putR
      f_src f_tgt
      ths im_src im_tgt st_src st_tgt w
      st itr_src ktr_tgt
      (LSIM: _lsim _ _ RR f_src true itr_src (ktr_tgt tt) (ths, im_src, im_tgt, st_src, st, w))
    :
    __lsim tid lsim _lsim RR f_src f_tgt itr_src (trigger (Put st) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, w)
  | lsim_getR
      f_src f_tgt
      ths im_src im_tgt st_src st_tgt w
      itr_src ktr_tgt
      (LSIM: _lsim _ _ RR f_src true itr_src (ktr_tgt st_tgt) (ths, im_src, im_tgt, st_src, st_tgt, w))
    :
    __lsim tid lsim _lsim RR f_src f_tgt itr_src (trigger (@Get _) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, w)
  | lsim_tidR
      f_src f_tgt
      ths im_src im_tgt st_src st_tgt w
      itr_src ktr_tgt
      (LSIM: _lsim _ _ RR f_src true itr_src (ktr_tgt tid) (ths, im_src, im_tgt, st_src, st_tgt, w))
    :
    __lsim tid lsim _lsim RR f_src f_tgt itr_src (trigger (GetTid) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, w)
  | lsim_fairR
      f_src f_tgt
      ths im_src im_tgt0 st_src st_tgt w
      f itr_src ktr_tgt
      (LSIM: forall im_tgt1
                   (FAIR: fair_update im_tgt0 im_tgt1 (sum_fmap_r f)),
          (<<LSIM: _lsim _ _ RR f_src true itr_src (ktr_tgt tt) (ths, im_src, im_tgt1, st_src, st_tgt, w)>>))
    :
    __lsim tid lsim _lsim RR f_src f_tgt itr_src (trigger (Fair f) >>= ktr_tgt) (ths, im_src, im_tgt0, st_src, st_tgt, w)

  | lsim_observe
      f_src f_tgt o
      ths im_src im_tgt st_src st_tgt w
      fn args ktr_src ktr_tgt
      (LSIM: forall ret,
          lsim _ _ RR true true (o, ktr_src ret) (ktr_tgt ret) (ths, im_src, im_tgt, st_src, st_tgt, w))
    :
    __lsim tid lsim _lsim RR f_src f_tgt (o, trigger (Observe fn args) >>= ktr_src) (trigger (Observe fn args) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, w)

  | lsim_sync
      f_src f_tgt o o0
      ths0 im_src0 im_tgt0 st_src0 st_tgt0 w
      w0 ktr_src ktr_tgt
      (INV: I (ths0, im_src0, im_tgt0, st_src0, st_tgt0, w0))
      (WORLD: world_le w w0)
      (STUTTER: wf_src.(lt) o0 o)
      (LSIM: forall ths1 im_src1 im_tgt1 st_src1 st_tgt1 w1
                   (INV: I (ths1, im_src1, im_tgt1, st_src1, st_tgt1, w1))
                   (WORLD: world_le w0 w1)
                   im_tgt2
                   (TGT: fair_update im_tgt1 im_tgt2 (sum_fmap_l (tids_fmap tid ths1))),
          _lsim _ _ RR f_src true (o0, trigger (Yield) >>= ktr_src) (ktr_tgt tt) (ths1, im_src1, im_tgt2, st_src1, st_tgt1, w1))
    :
    __lsim tid lsim _lsim RR f_src f_tgt (o, trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt) (ths0, im_src0, im_tgt0, st_src0, st_tgt0, w)
  | lsim_yieldL
      f_src f_tgt o
      ths im_src0 im_tgt st_src st_tgt w
      ktr_src itr_tgt
      (LSIM: exists im_src1 o1,
          (<<FAIR: fair_update im_src0 im_src1 (sum_fmap_l (tids_fmap tid ths))>>) /\
            (<<LSIM: _lsim _ _ RR true f_tgt (o1, ktr_src tt) itr_tgt (ths, im_src1, im_tgt, st_src, st_tgt, w)>>))
    :
    __lsim tid lsim _lsim RR f_src f_tgt (o, trigger (Yield) >>= ktr_src) itr_tgt (ths, im_src0, im_tgt, st_src, st_tgt, w)

  | lsim_progress
      o
      ths im_src im_tgt st_src st_tgt w
      itr_src itr_tgt
      (LSIM: lsim _ _ RR false false (o, itr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, w))
    :
    __lsim tid lsim _lsim RR true true (o, itr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, w)
  .

  Definition lsim (tid: thread_id.(id))
             R_src R_tgt (RR: R_src -> R_tgt -> shared_rel):
    bool -> bool -> (wf_src.(T) * itree srcE R_src) -> itree tgtE R_tgt -> shared_rel :=
    paco8 (fun r => pind8 (__lsim tid r) top8) bot8 R_src R_tgt RR.

  Lemma __lsim_mon tid:
    forall r r' (LE: r <8= r'), (__lsim tid r) <9= (__lsim tid r').
  Proof.
    ii. inv PR; econs; eauto.
  Qed.

  Lemma _lsim_mon tid: forall r, monotone8 (__lsim tid r).
  Proof.
    ii. inv IN; econs; eauto.
    { des. eauto. }
    { des. eauto. }
    { i. eapply LE. eapply LSIM. eauto. }
    { des. esplits; eauto. }
  Qed.

  Lemma lsim_mon tid: forall q, monotone8 (fun r => pind8 (__lsim tid r) q).
  Proof.
    ii. eapply pind8_mon_gen; eauto.
    ii. eapply __lsim_mon; eauto.
  Qed.

  Variant lsim_resetC
          (r: forall R_src R_tgt (RR: R_src -> R_tgt -> shared_rel), bool -> bool -> (wf_src.(T) * itree srcE R_src) -> itree tgtE R_tgt -> shared_rel)
          R_src R_tgt (RR: R_src -> R_tgt -> shared_rel)
    :
    bool -> bool -> (wf_src.(T) * itree srcE R_src) -> itree tgtE R_tgt -> shared_rel :=
    | lsim_resetC_intro
        src tgt shr
        ps0 pt0 ps1 pt1
        (REL: r _ _ RR ps1 pt1 src tgt shr)
        (SRC: ps1 = true -> ps0 = true)
        (TGT: pt1 = true -> pt0 = true)
      :
      lsim_resetC r RR ps0 pt0 src tgt shr
  .

  Lemma lsim_resetC_spec tid
    :
    lsim_resetC <9= gupaco8 (fun r => pind8 (__lsim tid r) top8) (cpn8 (fun r => pind8 (__lsim tid r) top8)).
  Proof.
    eapply wrespect8_uclo; eauto with paco.
    { eapply lsim_mon. }
    econs.
    { ii. inv IN. econs; eauto. }
    i. inv PR. eapply GF in REL.
    eapply pind8_acc in REL.
    instantiate (1:= (fun R0 R1 (RR: R0 -> R1 -> shared_rel) ps1 pt1 src tgt shr =>
                        forall ps0 pt0,
                          (ps1 = true -> ps0 = true) ->
                          (pt1 = true -> pt0 = true) ->
                          pind8 (__lsim tid (rclo8 lsim_resetC r)) top8 R0 R1 RR ps0 pt0 src tgt shr)) in REL; eauto.
    ss. i. eapply pind8_unfold in PR.
    2:{ eapply _lsim_mon. }
    rename PR into LSIM. inv LSIM.

    { eapply pind8_fold. econs; eauto. }

    { destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      eapply pind8_fold. eapply lsim_tauL. split; ss.
      hexploit IH; eauto.
    }

    { des. eapply pind8_fold. eapply lsim_chooseL. esplits; eauto. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { eapply pind8_fold. eapply lsim_putL. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { eapply pind8_fold. eapply lsim_getL. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { eapply pind8_fold. eapply lsim_tidL. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { eapply pind8_fold. eapply lsim_UB. }

    { des. eapply pind8_fold. eapply lsim_fairL. esplits; eauto. split; ss.
      destruct LSIM as [LSIM IND]. hexploit IH; eauto.
    }

    { destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      eapply pind8_fold. eapply lsim_tauR. split; ss.
      hexploit IH. eauto. all: eauto.
    }

    { eapply pind8_fold. eapply lsim_chooseR. i. split; ss. specialize (LSIM0 x).
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { eapply pind8_fold. eapply lsim_putR. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { eapply pind8_fold. eapply lsim_getR. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { eapply pind8_fold. eapply lsim_tidR. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { eapply pind8_fold. eapply lsim_fairR. i. split; ss. specialize (LSIM0 _ FAIR).
      des. destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { eapply pind8_fold. eapply lsim_observe. i. eapply rclo8_base. auto. }

    { eapply pind8_fold. eapply lsim_sync; eauto. i.
      hexploit LSIM0; eauto. clear LSIM0. intros LSIM0.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. split; ss.
    }

    { des. eapply pind8_fold. eapply lsim_yieldL. esplits; eauto. split; ss.
      destruct LSIM as [LSIM IND]. hexploit IH; eauto.
    }

    { pclearbot. hexploit H; ss; i. hexploit H0; ss; i. clarify.
      eapply pind8_fold. eapply lsim_progress. eapply rclo8_base. auto. }
  Qed.

  Lemma lsim_reset_prog
        tid
        R0 R1 (RR: R0 -> R1 -> shared_rel)
        src tgt shr
        ps0 pt0 ps1 pt1
        (LSIM: lsim tid RR ps1 pt1 src tgt shr)
        (SRC: ps1 = true -> ps0 = true)
        (TGT: pt1 = true -> pt0 = true)
    :
    lsim tid RR ps0 pt0 src tgt shr.
  Proof.
    ginit.
    { eapply lsim_mon. }
    { eapply cpn8_wcompat. eapply lsim_mon. }
    guclo lsim_resetC_spec.
    { eapply lsim_mon. }
    econs; eauto. gfinal.
    { eapply lsim_mon. }
    right. auto.
  Qed.

  Lemma lsim_set_prog
        tid
        R0 R1 (RR: R0 -> R1 -> shared_rel)
        src tgt shr
        (LSIM: lsim tid RR true true src tgt shr)
    :
    forall ps pt, lsim tid RR ps pt src tgt shr.
  Proof.
    i. revert_until tid. pcofix CIH. i.
    remember true as ps0 in LSIM at 1. remember true as pt0 in LSIM at 1.
    move LSIM before CIH. revert_until LSIM. punfold LSIM.
    2:{ eapply lsim_mon. }
    eapply pind8_acc in LSIM.

    { instantiate (1:= (fun R0 R1 (RR: R0 -> R1 -> shared_rel) ps0 pt0 src tgt shr =>
                          ps0 = true ->
                          pt0 = true ->
                          forall ps pt,
                            paco8
                              (fun r0 =>
                                 pind8 (__lsim tid r0) top8) r R0 R1 RR ps pt src tgt shr)) in LSIM; auto. }

    ss. clear ps0 pt0 src tgt shr LSIM.
    intros rr DEC IH R0' R1' RR' gps gpt src tgt shr LSIM. clear DEC.
    intros Egps Egpt ps pt.
    eapply pind8_unfold in LSIM.
    2:{ eapply _lsim_mon. }
    inv LSIM.

    { pfold. eapply pind8_fold. econs; eauto. }

    { destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      pfold. eapply pind8_fold. eapply lsim_tauL. split; ss.
      hexploit IH. eauto. all: eauto. i. punfold H. eapply lsim_mon.
    }

    { des. pfold. eapply pind8_fold. eapply lsim_chooseL. esplits; eauto. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind8_fold. eapply lsim_putL. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind8_fold. eapply lsim_getL. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind8_fold. eapply lsim_tidL. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind8_fold. eapply lsim_UB. }

    { des. pfold. eapply pind8_fold. eapply lsim_fairL. esplits; eauto. split; ss.
      destruct LSIM as [LSIM IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      pfold. eapply pind8_fold. eapply lsim_tauR. split; ss.
      hexploit IH. eauto. all: eauto. i. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind8_fold. eapply lsim_chooseR. i. split; ss. specialize (LSIM0 x).
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind8_fold. eapply lsim_putR. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind8_fold. eapply lsim_getR. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind8_fold. eapply lsim_tidR. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind8_fold. eapply lsim_fairR. i. split; ss. specialize (LSIM0 _ FAIR).
      des. destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind8_fold. eapply lsim_observe. i. eapply upaco8_mon_bot; eauto. }

    { pfold. eapply pind8_fold. eapply lsim_sync; eauto. i.
      hexploit LSIM0; eauto. clear LSIM0. intros LSIM0.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. split; ss. punfold H. eapply lsim_mon.
    }

    { des. pfold. eapply pind8_fold. eapply lsim_yieldL. esplits; eauto. split; ss.
      destruct LSIM as [LSIM IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pclearbot. eapply paco8_mon_bot. eapply lsim_reset_prog. eauto. all: ss. }

  Qed.

  Definition local_RR {R0 R1} (RR: R0 -> R1 -> Prop) tid :=
    fun (r_src: R0) (r_tgt: R1) '(ths2, im_src1, im_tgt1, st_src1, st_tgt1, w1) =>
      (exists ths3 w2,
          (<<THS: NatMap.remove tid ths2 = ths3>>) /\
            (<<WORLD: world_le w1 w2>>) /\
            (<<INV: I (ths3, im_src1, im_tgt1, st_src1, st_tgt1, w2)>>) /\
            (<<RET: RR r_src r_tgt>>)).

  Definition local_sim {R0 R1} (RR: R0 -> R1 -> Prop) src tgt :=
    forall ths0 im_src0 im_tgt0 st_src0 st_tgt0 w0
      (* (INV: I (ths0, tht0, im_src0, im_tgt0, st_src0, st_tgt0, o0, w0)) *)
      (* tid ths1 tht1 *)
      (* (THS: TIdSet.t_add ths0 tid ths1) *)
      (* (THT: TIdSet.t_add tht0 tid tht1) *)
      tid
      (THS: NatMap.In tid ths0)
      (INV: I (ths0, im_src0, im_tgt0, st_src0, st_tgt0, w0))
      fs ft,
    exists o,
      lsim
        tid
        (@local_RR R0 R1 RR tid)
        fs ft
        (o, src) tgt
        (ths0, im_src0, im_tgt0, st_src0, st_tgt0, w0).

  Definition local_sim_pick {R0 R1} (RR: R0 -> R1 -> Prop) src tgt tid :=
    forall ths0 im_src0 im_tgt0 st_src0 st_tgt0 w0
      (THS: NatMap.In tid ths0)
      (INV: I (ths0, im_src0, im_tgt0, st_src0, st_tgt0, w0))
      fs ft,
    forall im_tgt1 (FAIR: fair_update im_tgt0 im_tgt1 (sum_fmap_l (tids_fmap tid ths0))),
    exists im_src1, (fair_update im_src0 im_src1 (sum_fmap_l (tids_fmap tid ths0))) /\
                 (lsim
                    tid
                    (@local_RR R0 R1 RR tid)
                    fs ft
                    src tgt
                    (ths0, im_src1, im_tgt1, st_src0, st_tgt0, w0)).

End PRIMIVIESIM.
#[export] Hint Constructors __lsim: core.
#[export] Hint Unfold lsim: core.
#[export] Hint Resolve __lsim_mon: paco.
#[export] Hint Resolve _lsim_mon: paco.
#[export] Hint Resolve lsim_mon: paco.



Module ModSim.
  Section MODSIM.

    Variable md_src: Mod.t.
    Variable md_tgt: Mod.t.

    Record mod_sim: Prop :=
      mk {
          wf: WF;
          world: Type;
          world_le: world -> world -> Prop;
          I: (@shared md_src.(Mod.state) md_tgt.(Mod.state) md_src.(Mod.ident) md_tgt.(Mod.ident) wf nat_wf world) -> Prop;

          init_thread_id: TIdSet.t;
          (* INV should hold for all current existing thread_id *)
          init: forall im_tgt, exists im_src w,
            I (init_thread_id, im_src, im_tgt, md_src.(Mod.st_init), md_tgt.(Mod.st_init), w);

          (* init_thread_id: TIdSet.t; *)
          (* init: forall im_tgt, exists im_src w, *)
          (*   I (init_thread_id, init_thread_id, im_src, im_tgt, md_src.(Mod.st_init), md_tgt.(Mod.st_init), w); *)

          funs: forall fn args, local_sim world_le I (@eq Val) (md_src.(Mod.funs) fn args) (md_tgt.(Mod.funs) fn args);
        }.

    (* Record local_sim: Prop := *)
    (*   mk { *)
    (*       wf: WF; *)
    (*       world: Type; *)
    (*       world_le: world -> world -> Prop; *)
    (*       I: (@shared md_src.(Mod.state) md_tgt.(Mod.state) md_src.(Mod.ident) md_tgt.(Mod.ident) wf nat_wf world) -> Prop; *)

    (*       init: forall im_tgt th_tgt, *)
    (*       exists im_src th_src w, *)
    (*         I ([], im_src, im_tgt, th_src, th_tgt, md_src.(Mod.st_init), md_tgt.(Mod.st_init), w); *)

    (*       funs: forall ths0 im_src0 im_tgt0 th_src0 th_tgt0 o0 st_src0 st_tgt0 w0 *)
    (*               (INV: I (ths0, im_src0, im_tgt0, th_src0, th_tgt0, o0, st_src0, st_tgt0, w0)) *)
    (*               fn args tid ths1 *)
    (*               (THS: TIdSet.t_add ths0 tid ths1), *)
    (*         lsim *)
    (*           world_le *)
    (*           I *)
    (*           tid *)
    (*           (fun r_src r_tgt '(ths2, im_src1, im_tgt1, th_src1, th_tgt1, o1, st_src1, st_tgt1, w1) => *)
    (*              exists ths3 w2, *)
    (*                (<<THS: TIdSet.t_remove ths2 tid ths3>>) /\ *)
    (*                  (<<WORLD: world_le w1 w2>>) /\ *)
    (*                  (<<INV: I (ths3, im_src1, im_tgt1, th_src1, th_tgt1, o1, st_src1, st_tgt1, w2)>>) /\ *)
    (*                  (<<RET: r_src = r_tgt>>)) *)
    (*           false false *)
    (*           (md_src.(Mod.funs) fn args) (md_tgt.(Mod.funs) fn args) *)
    (*           (ths1, im_src0, im_tgt0, th_src0, th_tgt0, o0, st_src0, st_tgt0, w0); *)
    (*     }. *)

  End MODSIM.
End ModSim.
