From sflib Require Import sflib.
From Paco Require Import paco.
Require Export Coq.Strings.String.
Require Import Coq.Classes.RelationClasses.

From Fairness Require Export ITreeLib FairBeh Mod.
From Fairness Require Import pind.
From Fairness Require Import PCM.

Set Implicit Arguments.



Section PRIMIVIESIM.
  Context `{M: URA.t}.

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

  Definition shared :=
    (TIdSet.t *
       (@imap ident_src wf_src) *
       (@imap ident_tgt wf_tgt) *
       state_src *
       state_tgt *
       URA.car)%type.

  Let shared_rel: Type := shared -> Prop.

  Variable I: shared_rel.

  Variant __lsim
          (tid: thread_id)
          (lsim: forall R_src R_tgt (RR: R_src -> R_tgt -> URA.car -> URA.car -> shared_rel), bool -> bool -> URA.car -> URA.car -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel)
          (_lsim: forall R_src R_tgt (RR: R_src -> R_tgt -> URA.car -> URA.car -> shared_rel),bool -> bool -> URA.car -> URA.car -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel)
          R_src R_tgt (RR: R_src -> R_tgt -> URA.car -> URA.car -> shared_rel)
    :
    bool -> bool -> URA.car -> URA.car -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel :=
  | lsim_ret
      f_src f_tgt r_own r_ctx
      ths im_src im_tgt st_src st_tgt r_shared
      r_src r_tgt
      (LSIM: RR r_src r_tgt r_own r_ctx (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_own r_ctx (Ret r_src) (Ret r_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)

  | lsim_tauL
      f_src f_tgt r_own r_ctx
      ths im_src im_tgt st_src st_tgt r_shared
      itr_src itr_tgt
      (LSIM: _lsim _ _ RR true f_tgt r_own r_ctx itr_src itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_own r_ctx (Tau itr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | lsim_chooseL
      f_src f_tgt r_own r_ctx
      ths im_src im_tgt st_src st_tgt r_shared
      X ktr_src itr_tgt
      (LSIM: exists x, _lsim _ _ RR true f_tgt r_own r_ctx (ktr_src x) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_own r_ctx (trigger (Choose X) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | lsim_putL
      f_src f_tgt r_own r_ctx
      ths im_src im_tgt st_src st_tgt r_shared
      st ktr_src itr_tgt
      (LSIM: _lsim _ _ RR true f_tgt r_own r_ctx (ktr_src tt) itr_tgt (ths, im_src, im_tgt, st, st_tgt, r_shared))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_own r_ctx (trigger (Put st) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | lsim_getL
      f_src f_tgt r_own r_ctx
      ths im_src im_tgt st_src st_tgt r_shared
      ktr_src itr_tgt
      (LSIM: _lsim _ _ RR true f_tgt r_own r_ctx (ktr_src st_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_own r_ctx (trigger (@Get _) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | lsim_tidL
      f_src f_tgt r_own r_ctx
      ths im_src im_tgt st_src st_tgt r_shared
      ktr_src itr_tgt
      (LSIM: _lsim _ _ RR true f_tgt r_own r_ctx (ktr_src tid) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_own r_ctx (trigger (GetTid) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | lsim_UB
      f_src f_tgt r_own r_ctx
      ths im_src im_tgt st_src st_tgt r_shared
      ktr_src itr_tgt
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_own r_ctx (trigger (Undefined) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | lsim_fairL
      f_src f_tgt r_own r_ctx
      ths im_src0 im_tgt st_src st_tgt r_shared
      f ktr_src itr_tgt
      (LSIM: exists im_src1,
          (<<FAIR: fair_update im_src0 im_src1 (sum_fmap_r f)>>) /\
            (<<LSIM: _lsim _ _ RR true f_tgt r_own r_ctx (ktr_src tt) itr_tgt (ths, im_src1, im_tgt, st_src, st_tgt, r_shared)>>))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_own r_ctx (trigger (Fair f) >>= ktr_src) itr_tgt (ths, im_src0, im_tgt, st_src, st_tgt, r_shared)

  | lsim_tauR
      f_src f_tgt r_own r_ctx
      ths im_src im_tgt st_src st_tgt r_shared
      itr_src itr_tgt
      (LSIM: _lsim _ _ RR f_src true r_own r_ctx itr_src itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_own r_ctx itr_src (Tau itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | lsim_chooseR
      f_src f_tgt r_own r_ctx
      ths im_src im_tgt st_src st_tgt r_shared
      X itr_src ktr_tgt
      (LSIM: forall x, _lsim _ _ RR f_src true r_own r_ctx itr_src (ktr_tgt x) (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_own r_ctx itr_src (trigger (Choose X) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | lsim_putR
      f_src f_tgt r_own r_ctx
      ths im_src im_tgt st_src st_tgt r_shared
      st itr_src ktr_tgt
      (LSIM: _lsim _ _ RR f_src true r_own r_ctx itr_src (ktr_tgt tt) (ths, im_src, im_tgt, st_src, st, r_shared))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_own r_ctx itr_src (trigger (Put st) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | lsim_getR
      f_src f_tgt r_own r_ctx
      ths im_src im_tgt st_src st_tgt r_shared
      itr_src ktr_tgt
      (LSIM: _lsim _ _ RR f_src true r_own r_ctx itr_src (ktr_tgt st_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_own r_ctx itr_src (trigger (@Get _) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | lsim_tidR
      f_src f_tgt r_own r_ctx
      ths im_src im_tgt st_src st_tgt r_shared
      itr_src ktr_tgt
      (LSIM: _lsim _ _ RR f_src true r_own r_ctx itr_src (ktr_tgt tid) (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_own r_ctx itr_src (trigger (GetTid) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | lsim_fairR
      f_src f_tgt r_own r_ctx
      ths im_src im_tgt0 st_src st_tgt r_shared
      f itr_src ktr_tgt
      (LSIM: forall im_tgt1
                   (FAIR: fair_update im_tgt0 im_tgt1 (sum_fmap_r f)),
          (<<LSIM: _lsim _ _ RR f_src true r_own r_ctx itr_src (ktr_tgt tt) (ths, im_src, im_tgt1, st_src, st_tgt, r_shared)>>))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_own r_ctx itr_src (trigger (Fair f) >>= ktr_tgt) (ths, im_src, im_tgt0, st_src, st_tgt, r_shared)

  | lsim_observe
      f_src f_tgt r_own r_ctx
      ths im_src im_tgt st_src st_tgt r_shared
      fn args ktr_src ktr_tgt
      (LSIM: forall ret,
          lsim _ _ RR true true r_own r_ctx (ktr_src ret) (ktr_tgt ret) (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_own r_ctx (trigger (Observe fn args) >>= ktr_src) (trigger (Observe fn args) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)

  | lsim_sync
      f_src f_tgt r_own0 r_ctx0
      ths0 im_src0 im_tgt0 st_src0 st_tgt0 r_shared0
      r_own1 ktr_src ktr_tgt
      (INV: I (ths0, im_src0, im_tgt0, st_src0, st_tgt0, r_shared0))
      (VALID: URA.wf (r_shared0 ⋅ r_own0 ⋅ r_ctx0))
      (LSIM: forall ths1 im_src1 im_tgt1 st_src1 st_tgt1 r_shared1 r_ctx1
                    (INV: I (ths1, im_src1, im_tgt1, st_src1, st_tgt1, r_shared1))
                    (VALID: URA.wf (r_shared1 ⋅ r_own0 ⋅ r_ctx1))
                    im_tgt2
                    (TGT: fair_update im_tgt1 im_tgt2 (sum_fmap_l (tids_fmap tid ths1))),
          _lsim _ _ RR f_src true r_own1 r_ctx1 (trigger (Yield) >>= ktr_src) (ktr_tgt tt) (ths1, im_src1, im_tgt2, st_src1, st_tgt1, r_shared1))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_own0 r_ctx0 (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt) (ths0, im_src0, im_tgt0, st_src0, st_tgt0, r_shared0)
  | lsim_yieldL
      f_src f_tgt r_own r_ctx
      ths im_src0 im_tgt st_src st_tgt r_shared
      ktr_src itr_tgt
      (LSIM: exists im_src1,
          (<<FAIR: fair_update im_src0 im_src1 (sum_fmap_l (tids_fmap tid ths))>>) /\
            (<<LSIM: _lsim _ _ RR true f_tgt r_own r_ctx (ktr_src tt) itr_tgt (ths, im_src1, im_tgt, st_src, st_tgt, r_shared)>>))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_own r_ctx (trigger (Yield) >>= ktr_src) itr_tgt (ths, im_src0, im_tgt, st_src, st_tgt, r_shared)

  | lsim_progress
      r_own r_ctx
      ths im_src im_tgt st_src st_tgt r_shared
      itr_src itr_tgt
      (LSIM: lsim _ _ RR false false r_own r_ctx itr_src itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    __lsim tid lsim _lsim RR true true r_own r_ctx itr_src itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  .

  Definition lsim (tid: thread_id)
             R_src R_tgt (RR: R_src -> R_tgt -> URA.car -> URA.car -> shared_rel):
    bool -> bool -> URA.car -> URA.car -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel :=
    paco10 (fun r => pind10 (__lsim tid r) top10) bot10 R_src R_tgt RR.

  Lemma __lsim_mon tid:
    forall r r' (LE: r <10= r'), (__lsim tid r) <11= (__lsim tid r').
  Proof.
    ii. inv PR; econs; eauto.
  Qed.

  Lemma _lsim_mon tid: forall r, monotone10 (__lsim tid r).
  Proof.
    ii. inv IN; econs; eauto.
    { des. eauto. }
    { des. eauto. }
    { i. eapply LE. eapply LSIM. eauto. }
    { des. esplits; eauto. }
  Qed.

  Lemma lsim_mon tid: forall q, monotone10 (fun r => pind10 (__lsim tid r) q).
  Proof.
    ii. eapply pind10_mon_gen; eauto.
    ii. eapply __lsim_mon; eauto.
  Qed.

  Variant lsim_resetC
          (r: forall R_src R_tgt (RR: R_src -> R_tgt -> URA.car -> URA.car -> shared_rel), bool -> bool -> URA.car -> URA.car -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel)
          R_src R_tgt (RR: R_src -> R_tgt -> URA.car -> URA.car -> shared_rel)
    :
    bool -> bool -> URA.car -> URA.car -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel :=
    | lsim_resetC_intro
        src tgt shr r_own r_ctx
        ps0 pt0 ps1 pt1
        (REL: r _ _ RR ps1 pt1 r_own r_ctx src tgt shr)
        (SRC: ps1 = true -> ps0 = true)
        (TGT: pt1 = true -> pt0 = true)
      :
      lsim_resetC r RR ps0 pt0 r_own r_ctx src tgt shr
  .

  Lemma lsim_resetC_spec tid
    :
    lsim_resetC <11= gupaco10 (fun r => pind10 (__lsim tid r) top10) (cpn10 (fun r => pind10 (__lsim tid r) top10)).
  Proof.
    eapply wrespect10_uclo; eauto with paco.
    { eapply lsim_mon. }
    econs.
    { ii. inv IN. econs; eauto. }
    i. inv PR. eapply GF in REL.
    eapply pind10_acc in REL.
    instantiate (1:= (fun R0 R1 (RR: R0 -> R1 -> URA.car -> URA.car -> shared_rel) ps1 pt1 r_own r_ctx src tgt shr =>
                        forall ps0 pt0,
                          (ps1 = true -> ps0 = true) ->
                          (pt1 = true -> pt0 = true) ->
                          pind10 (__lsim tid (rclo10 lsim_resetC r)) top10 R0 R1 RR ps0 pt0 r_own r_ctx src tgt shr)) in REL; eauto.
    ss. i. eapply pind10_unfold in PR.
    2:{ eapply _lsim_mon. }
    rename PR into LSIM. inv LSIM.

    { eapply pind10_fold. econs; eauto. }

    { destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      eapply pind10_fold. eapply lsim_tauL. split; ss.
      hexploit IH; eauto.
    }

    { des. eapply pind10_fold. eapply lsim_chooseL. esplits; eauto. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { eapply pind10_fold. eapply lsim_putL. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { eapply pind10_fold. eapply lsim_getL. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { eapply pind10_fold. eapply lsim_tidL. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { eapply pind10_fold. eapply lsim_UB. }

    { des. eapply pind10_fold. eapply lsim_fairL. esplits; eauto. split; ss.
      destruct LSIM as [LSIM IND]. hexploit IH; eauto.
    }

    { destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      eapply pind10_fold. eapply lsim_tauR. split; ss.
      hexploit IH. eauto. all: eauto.
    }

    { eapply pind10_fold. eapply lsim_chooseR. i. split; ss. specialize (LSIM0 x).
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { eapply pind10_fold. eapply lsim_putR. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { eapply pind10_fold. eapply lsim_getR. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { eapply pind10_fold. eapply lsim_tidR. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { eapply pind10_fold. eapply lsim_fairR. i. split; ss. specialize (LSIM0 _ FAIR).
      des. destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { eapply pind10_fold. eapply lsim_observe. i. eapply rclo10_base. auto. }

    { eapply pind10_fold. eapply lsim_sync; eauto. i.
      hexploit LSIM0; eauto. clear LSIM0. intros LSIM0.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. split; ss; eauto.
    }

    { des. eapply pind10_fold. eapply lsim_yieldL. esplits; eauto. split; ss.
      destruct LSIM as [LSIM IND]. hexploit IH; eauto.
    }

    { pclearbot. hexploit H; ss; i. hexploit H0; ss; i. clarify.
      eapply pind10_fold. eapply lsim_progress. eapply rclo10_base. auto. }
  Qed.

  Lemma lsim_reset_prog
        tid
        R0 R1 (RR: R0 -> R1 -> URA.car -> URA.car -> shared_rel)
        src tgt shr
        ps0 pt0 ps1 pt1 r_own r_ctx
        (LSIM: lsim tid RR ps1 pt1 r_own r_ctx src tgt shr)
        (SRC: ps1 = true -> ps0 = true)
        (TGT: pt1 = true -> pt0 = true)
    :
    lsim tid RR ps0 pt0 r_own r_ctx src tgt shr.
  Proof.
    ginit.
    { eapply lsim_mon. }
    { eapply cpn10_wcompat. eapply lsim_mon. }
    guclo lsim_resetC_spec.
    { eapply lsim_mon. }
    econs; eauto. gfinal.
    { eapply lsim_mon. }
    right. auto.
  Qed.

  Lemma lsim_set_prog
        tid
        R0 R1 (RR: R0 -> R1 -> URA.car -> URA.car -> shared_rel)
        r_own r_ctx src tgt shr
        (LSIM: lsim tid RR true true r_own r_ctx src tgt shr)
    :
    forall ps pt, lsim tid RR ps pt r_own r_ctx src tgt shr.
  Proof.
    i. revert_until tid. pcofix CIH. i.
    remember true as ps0 in LSIM at 1. remember true as pt0 in LSIM at 1.
    move LSIM before CIH. revert_until LSIM. punfold LSIM.
    2:{ eapply lsim_mon. }
    eapply pind10_acc in LSIM.

    { instantiate (1:= (fun R0 R1 (RR: R0 -> R1 -> URA.car -> URA.car -> shared_rel) ps0 pt0 r_own r_ctx src tgt shr =>
                          ps0 = true ->
                          pt0 = true ->
                          forall ps pt,
                            paco10
                              (fun r0 =>
                                 pind10 (__lsim tid r0) top10) r R0 R1 RR ps pt r_own r_ctx src tgt shr)) in LSIM; auto. }

    ss. clear ps0 pt0 r_own r_ctx src tgt shr LSIM.
    intros rr DEC IH R0' R1' RR' gps gpt r_own r_ctx src tgt shr LSIM. clear DEC.
    intros Egps Egpt ps pt.
    eapply pind10_unfold in LSIM.
    2:{ eapply _lsim_mon. }
    inv LSIM.

    { pfold. eapply pind10_fold. econs; eauto. }

    { destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      pfold. eapply pind10_fold. eapply lsim_tauL. split; ss.
      hexploit IH. eauto. all: eauto. i. punfold H. eapply lsim_mon.
    }

    { des. pfold. eapply pind10_fold. eapply lsim_chooseL. esplits; eauto. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind10_fold. eapply lsim_putL. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind10_fold. eapply lsim_getL. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind10_fold. eapply lsim_tidL. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind10_fold. eapply lsim_UB. }

    { des. pfold. eapply pind10_fold. eapply lsim_fairL. esplits; eauto. split; ss.
      destruct LSIM as [LSIM IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      pfold. eapply pind10_fold. eapply lsim_tauR. split; ss.
      hexploit IH. eauto. all: eauto. i. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind10_fold. eapply lsim_chooseR. i. split; ss. specialize (LSIM0 x).
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind10_fold. eapply lsim_putR. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind10_fold. eapply lsim_getR. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind10_fold. eapply lsim_tidR. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind10_fold. eapply lsim_fairR. i. split; ss. specialize (LSIM0 _ FAIR).
      des. destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind10_fold. eapply lsim_observe. i. eapply upaco10_mon_bot; eauto. }

    { pfold. eapply pind10_fold. eapply lsim_sync; eauto. i.
      hexploit LSIM0; eauto. clear LSIM0. intros LSIM0.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. split; ss. punfold H. eapply lsim_mon.
    }

    { des. pfold. eapply pind10_fold. eapply lsim_yieldL. esplits; eauto. split; ss.
      destruct LSIM as [LSIM IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pclearbot. eapply paco10_mon_bot. eapply lsim_reset_prog. eauto. all: ss. }

  Qed.

  Definition local_RR {R0 R1} (RR: R0 -> R1 -> Prop) tid:
    R0 -> R1 -> URA.car -> URA.car -> shared_rel :=
    fun (r_src: R0) (r_tgt: R1) (r_own1: URA.car) (r_ctx: URA.car) '(ths2, im_src1, im_tgt1, st_src1, st_tgt1, r_shared1) =>
      (exists ths3 r_own2 r_shared2,
          (<<THS: NatMap.remove tid ths2 = ths3>>) /\
            (<<VALID: URA.wf (r_shared2 ⋅ r_own2 ⋅ r_ctx)>>) /\
            (<<INV: I (ths3, im_src1, im_tgt1, st_src1, st_tgt1, r_shared2)>>) /\
            (<<RET: RR r_src r_tgt>>)).

  Definition local_sim {R0 R1} (RR: R0 -> R1 -> Prop) src tgt :=
    forall ths0 im_src0 im_tgt0 st_src0 st_tgt0 r_shared0 r_ctx0
           (INV: I (ths0, im_src0, im_tgt0, st_src0, st_tgt0, r_shared0))
           tid ths1
           (THS: TIdSet.add_new tid ths0 ths1)
           (VALID: URA.wf (r_shared0 ⋅ r_ctx0)),
    exists r_shared1 r_own1,
      (<<INV: I (ths1, im_src0, im_tgt0, st_src0, st_tgt0, r_shared1)>>) /\
        (<<VALID: URA.wf (r_shared1 ⋅ r_own1 ⋅ r_ctx0)>>) /\
        (forall ths im_src1 im_tgt1 st_src st_tgt r_shared2 r_ctx2
                (INV: I (ths, im_src1, im_tgt1, st_src, st_tgt, r_shared2))
                (VALID: URA.wf (r_shared2 ⋅ r_own1 ⋅ r_ctx2)),
          forall im_tgt2 (TGT: fair_update im_tgt1 im_tgt2 (sum_fmap_l (tids_fmap tid ths))),
          exists im_src2,
            (<<SRC: fair_update im_src1 im_src2 (sum_fmap_l (tids_fmap tid ths))>>) /\
              (<<LSIM: forall fs ft,
                  lsim
                    tid
                    (@local_RR R0 R1 RR tid)
                    fs ft
                    r_own1 r_ctx2
                    src tgt
                    (ths, im_src2, im_tgt2, st_src, st_tgt, r_shared2)
                    >>)).

  Definition shared_rel_wf: Prop :=
    forall ths im_src0 im_tgt0 st_src st_tgt r_shared0 r_ctx
           (INV: I (ths, im_src0, im_tgt0, st_src, st_tgt, r_shared0))
           (VALID: URA.wf (r_shared0 ⋅ r_ctx)),
    forall im_tgt1
           (TGT: fair_update im_tgt0 im_tgt1 (sum_fmap_l (tids_fmap_all ths))),
    exists im_src1 r_shared1,
      (<<SRC: fair_update im_src0 im_src1 (sum_fmap_l (tids_fmap_all ths))>>) /\
        (<<INV: I (ths, im_src1, im_tgt1, st_src, st_tgt, r_shared1)>>) /\
        (<<VALID: URA.wf (r_shared1 ⋅ r_ctx)>>).

  Definition shared_rel_wf_kernel: Prop :=
    forall ths im_src0 im_tgt0 st_src st_tgt r_shared0 r_ctx
           (INV: I (ths, im_src0, im_tgt0, st_src, st_tgt, r_shared0))
           (VALID: URA.wf (r_shared0 ⋅ r_ctx)),
    forall im_tgt1
           (TGT: fair_update im_tgt0 im_tgt1 (sum_fmap_l (kernel_success_fmap))),
    exists im_src1 r_shared1,
      (<<SRC: fair_update im_src0 im_src1 (sum_fmap_l (kernel_success_fmap))>>) /\
        (<<INV: I (ths, im_src1, im_tgt1, st_src, st_tgt, r_shared1)>>) /\
        (<<VALID: URA.wf (r_shared1 ⋅ r_ctx)>>).

  Definition shared_rel_wf_kernel_list: Prop :=
    forall ths im_src0 im_tgt0 st_src st_tgt r_shared0 r_ctx
           (INV: I (ths, im_src0, im_tgt0, st_src, st_tgt, r_shared0))
           (VALID: URA.wf (r_shared0 ⋅ r_ctx)),
    forall im_tgt1
           (TGT: fair_update im_tgt0 im_tgt1 (sum_fmap_l (kernel_success_fmap))),
    exists im_src1 r_shared1,
      (<<SRC: fair_update im_src0 im_src1 (sum_fmap_l (kernel_success_fmap))>>) /\
        (<<INV: I (ths, im_src1, im_tgt1, st_src, st_tgt, r_shared1)>>) /\
        (<<VALID: URA.wf (r_shared1 ⋅ r_ctx)>>).

  (* TODO: kernel list wf *)

End PRIMIVIESIM.
#[export] Hint Constructors __lsim: core.
#[export] Hint Unfold lsim: core.
#[export] Hint Resolve __lsim_mon: paco.
#[export] Hint Resolve _lsim_mon: paco.
#[export] Hint Resolve lsim_mon: paco.
#[export] Hint Resolve cpn10_wcompat: paco.


From Coq Require Import Relations.Relation_Operators.
From Coq Require Import Relations.Operators_Properties.
From Fairness Require Import WFLib Axioms.

Section TRANS_CLOS.

  Context `{M: URA.t}.

  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable _ident_src: ID.
  Variable _ident_tgt: ID.

  Variable wf_src: WF.
  Variable wf_tgt: WF.

  Hypothesis (inh : inhabited wf_tgt.(T)).

  Let wf_tgt' := {| wf := clos_trans_well_founded wf_tgt.(wf) |}.

  Let shared_rel: Type := shared state_src state_tgt _ident_src _ident_tgt wf_src wf_tgt -> Prop.
  Let shared_rel': Type := shared state_src state_tgt _ident_src _ident_tgt wf_src wf_tgt' -> Prop.
  Variable I: shared_rel.
  Let I' : shared_rel' :=
        fun '(ths, im_src, im_tgt, st_src, st_tgt, w) =>
          exists im_tgt'0, << INV_LE : (forall i, le wf_tgt' (im_tgt i) (im_tgt'0 i)) >>
                    /\ << INV : I (ths, im_src, im_tgt'0, st_src, st_tgt, w) >>.

  Lemma fair_break Id m_tgt m_tgt'' fm
    (FAIR : @fair_update Id wf_tgt' m_tgt m_tgt'' fm)
    : exists im_tgt'0, << FAIR : @fair_update Id wf_tgt m_tgt im_tgt'0 fm >> /\ << LE : forall i, le wf_tgt' (m_tgt'' i) (im_tgt'0 i) >>.
  Proof.
    exists (fun i => match fm i with
             | Flag.fail    => epsilon _ inh (fun z => lt wf_tgt z (m_tgt i)
                                                   /\ (m_tgt'' i = z \/ clos_trans_n1 _ (lt wf_tgt) (m_tgt'' i) z))
             | Flag.emp     => m_tgt i
             | Flag.success => m_tgt'' i
             end).
    split.
    - ii. specialize (FAIR i). des_ifs.
      + eapply clos_trans_step in FAIR.
        eapply epsilon_spec in FAIR.
        destruct FAIR. eapply H.
      + reflexivity.
    - ii. specialize (FAIR i). des_ifs.
      + eapply clos_trans_step in FAIR.
        eapply epsilon_spec in FAIR.
        destruct FAIR. eapply H0.
      + reflexivity.
  Qed.

  Lemma fair_trans_l {Id im_tgt im_tgt' im_tgt'' fm}
    (LE : (forall i, le wf_tgt' (im_tgt' i) (im_tgt i)))
    (FAIR : @fair_update Id wf_tgt' im_tgt' im_tgt'' fm)
    : @fair_update Id wf_tgt' im_tgt  im_tgt'' fm.
  Proof.
    ii. specialize (LE i). specialize (FAIR i). des_ifs.
    - destruct LE.
      + rewrite <- H. ss.
      + ss. eapply clos_trans_n1_trans; eauto.
    - destruct LE.
      + rewrite <- H. ss.
      + destruct FAIR.
        * rewrite H0. right. ss.
        * right. eapply clos_trans_n1_trans; eauto.
  Qed.

  Variable R0 R1 : Type.
  Variable RR : R0 -> R1 -> Prop.

  Lemma local_sim_clos_trans src tgt (SIM : local_sim I RR src tgt)
    : local_sim I' RR src tgt.
  Proof.
    ii. ss. des. move SIM at bottom.
    specialize (SIM ths0 im_src0 im_tgt'0 st_src0 st_tgt0 r_shared0 r_ctx0 INV0 tid ths1 THS VALID).
    des. exists r_shared1, r_own1. splits; ss. { exists im_tgt'0. ss. }
    i. des. pose proof (fair_break (fair_trans_l INV1 TGT)). des. move SIM1 at bottom.
    specialize (SIM1 ths im_src1 im_tgt'1 st_src st_tgt r_shared2 r_ctx2 INV2 VALID1 im_tgt'2 FAIR).
    des. exists im_src2. split; ss. i. specialize (LSIM fs ft).
    clear - inh LSIM LE. revert_until I'. ginit. gcofix CIH. i. gstep.
    remember (local_RR I RR tid) as RR'.
    remember (ths, im_src2, im_tgt'2, st_src, st_tgt, r_shared2) as sha.
    revert ths im_src2 im_tgt2 im_tgt'2 st_src st_tgt r_shared2 LE Heqsha RR HeqRR'.
    unfold lsim in LSIM. punfold LSIM.
    pattern R0, R1, RR', fs, ft, r_own1, r_ctx2, src, tgt, sha.
    revert R0 R1 RR' fs ft r_own1 r_ctx2 src tgt sha LSIM.
    eapply pind10_acc. intros rr DEC IH R0 R1 RR' fs ft r_own r_ctx src tgt sha. i. clear DEC. subst.
    eapply pind10_unfold in PR; eauto with paco. eapply pind10_fold. inv PR.
    - econs. ss. des. exists ths3, r_own2, r_shared0. splits; ss. exists im_tgt'2. split; ss.
    - econs. split; ss. eapply IH; ss. destruct LSIM. ss.
    - econs. des. exists x. split; ss. eapply IH; ss. destruct LSIM. ss.
    - econs. split; ss. eapply IH; ss. destruct LSIM. ss.
    - econs. split; ss. eapply IH; ss. destruct LSIM. ss.
    - econs. split; ss. eapply IH; ss. destruct LSIM. ss.
    - econs.
    - econs. des. exists im_src1. splits; ss. split; ss. eapply IH; ss. destruct LSIM0. ss.
    - econs. split; ss. eapply IH; ss. destruct LSIM. ss.
    - econs. i. specialize (LSIM x). split; ss. eapply IH; ss. destruct LSIM. ss.
    - econs. split; ss. eapply IH; ss. destruct LSIM. ss.
    - econs. split; ss. eapply IH; ss. destruct LSIM. ss.
    - econs. split; ss. eapply IH; ss. destruct LSIM. ss.
    - econs. i. pose proof (fair_break (fair_trans_l LE FAIR)). des.
      specialize (LSIM im_tgt'0 FAIR0). split; ss. eapply IH; ss. destruct LSIM. ss.
    - econs. i. specialize (LSIM ret). gfinal. left. eapply CIH; ss. pclearbot. eapply LSIM.
    - econs; ss. { exists im_tgt'2. split; ss. } i. des.
      pose proof (fair_break (fair_trans_l INV_LE TGT)). des. move LSIM at bottom.
      specialize (LSIM ths1 im_src1 im_tgt'0 st_src1 st_tgt1 r_shared1 r_ctx1 INV1 VALID0 im_tgt'1 FAIR).
      split; ss. eapply IH; ss. destruct LSIM. eapply H0.
    - econs. des. exists im_src1. split; ss. split; ss. eapply IH; ss. destruct LSIM0. ss.
    - econs. gfinal. left. pclearbot. eapply CIH; ss.
  Qed.

End TRANS_CLOS.


Module ModSim.
  Section MODSIM.

    Variable md_src: Mod.t.
    Variable md_tgt: Mod.t.

    Record mod_sim: Prop :=
      mk {
          wf_src : WF;
          wf_tgt : WF;
          wf_tgt_inhabited: inhabited wf_tgt.(T);
          wf_tgt_open: forall (o0: wf_tgt.(T)), exists o1, wf_tgt.(lt) o0 o1;

          world: URA.t;

          I: (@shared world md_src.(Mod.state) md_tgt.(Mod.state) md_src.(Mod.ident) md_tgt.(Mod.ident) wf_src wf_tgt) -> Prop;
          init: forall im_tgt, exists im_src r_shared,
            I (initial_threads, im_src, im_tgt, md_src.(Mod.st_init), md_tgt.(Mod.st_init), r_shared);

          funs: forall fn args, match md_src.(Mod.funs) fn, md_tgt.(Mod.funs) fn with
                                | None, _ => True
                                | _, None => False
                                | Some ktr_src, Some ktr_tgt => local_sim I (@eq Val) (ktr_src args) (ktr_tgt args)
                                end;
        }.
  End MODSIM.
End ModSim.


Module ModSimN.
  Section MODSIMNAT.

    Variable md_src: Mod.t.
    Variable md_tgt: Mod.t.

    Record mod_sim: Prop :=
      mk {
          wf_src : WF;

          world: URA.t;

          I: (@shared world md_src.(Mod.state) md_tgt.(Mod.state) md_src.(Mod.ident) md_tgt.(Mod.ident) wf_src nat_wf) -> Prop;
          init: forall im_tgt, exists im_src r_shared,
            I (initial_threads, im_src, im_tgt, md_src.(Mod.st_init), md_tgt.(Mod.st_init), r_shared);

          funs: forall fn args, match md_src.(Mod.funs) fn, md_tgt.(Mod.funs) fn with
                                | None, _ => True
                                | _, None => False
                                | Some ktr_src, Some ktr_tgt => local_sim I (@eq Val) (ktr_src args) (ktr_tgt args)
                                end;
        }.
  End MODSIMNAT.
End ModSimN.



From Fairness Require Import Axioms.
Section NAT.
  Variable wf_tgt : WF.
  Variable wf_tgt_inhabited: inhabited wf_tgt.(T).
  Variable wf_tgt_open: forall (o0: wf_tgt.(T)), exists o1, wf_tgt.(lt) o0 o1.

  Definition wf_tgt_0: wf_tgt.(T) := epsilon _ wf_tgt_inhabited (fun _ => True).
  Definition wf_tgt_S: wf_tgt.(T) -> wf_tgt.(T) :=
    fun o0 => epsilon _ wf_tgt_inhabited (fun o1 => wf_tgt.(lt) o0 o1).

  Let wf_tgt_S_lt o: wf_tgt.(lt) o (wf_tgt_S o).
  Proof. unfold wf_tgt_S. eapply epsilon_spec; ss. Qed.

  Fixpoint nat_to_wf_tgt (n: nat): wf_tgt.(T) :=
    match n with
    | 0 => wf_tgt_0
    | S n => wf_tgt_S (nat_to_wf_tgt n)
    end.

  (*
  Lemma nat_to_wf_tgt_mono : forall m n, m < n -> lt wf_tgt (nat_to_wf_tgt m) (nat_to_wf_tgt n).
  Proof.
    i. revert H. induction n; try lia. i.
    assert (m = n \/ m < n) by lia.
    destruct H0.
    - subst. ss.
    - specialize (IHn H0). admit.
  Admitted.
   *)

  Context `{M: URA.t}.

  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable _ident_src: ID.
  Variable _ident_tgt: ID.

  Variable wf_src: WF.

  Let srcE := ((@eventE _ident_src +' cE) +' sE state_src).
  Let tgtE := ((@eventE _ident_tgt +' cE) +' sE state_tgt).

  Let shared_rel: Type := @shared M state_src state_tgt _ident_src _ident_tgt wf_src wf_tgt  -> Prop.

  Variable I: shared_rel.

  Let shared_rel_nat: Type := @shared M state_src state_tgt _ident_src _ident_tgt wf_src nat_wf  -> Prop.

  Definition to_shared_rel_nat : shared_rel_nat := 
    fun '(ths, m_src, m_tgt, st_src, st_tgt, w) =>
      exists m_tgt',
        (forall i, m_tgt i <= m_tgt' i)
        /\ I (ths, m_src, nat_to_wf_tgt ∘ m_tgt', st_src, st_tgt, w).

End NAT.

Section MODSIMNAT.
  Import Mod.

  Variable M_src M_tgt: Mod.t.

  Lemma modsim_nat_modsim_exist
    (SIM: ModSim.mod_sim M_src M_tgt)
    : ModSimN.mod_sim M_src M_tgt.
  Proof.
    (*
    destruct SIM.
    pose (nat_to_wf_tgt wf_tgt wf_tgt_inhabited) as wf_emb.
    pose (to_shared_rel_nat wf_tgt_inhabited I) as I'.
    constructor 1 with wf_src world I'.
    { i. specialize (init (wf_emb ∘ im_tgt)). des. exists im_src, r_shared. ss. exists im_tgt. ss. }
    i. specialize (funs0 fn args). des_ifs. rename funs0 into SIM.
    ii. ss. des.
    specialize (SIM ths0 im_src0 (wf_emb ∘ m_tgt') st_src0 st_tgt0 r_shared0 r_ctx0 INV0 tid ths1 THS VALID). des.
    exists r_shared1, r_own1. splits; ss. { exists m_tgt'. splits; ss. }
    i. specialize (SIM1 ths im_src1 (wf_emb ∘ m_tgt') st_src st_tgt r_shared2 r_ctx2 INV1 VALID1 (wf_emb ∘ im_tgt2)).
    hexploit SIM1; clear SIM1.
    { ii. specialize (TGT i). des_ifs.
      - ss.
      admit. }
    intro SIM. des.
    *)
  Admitted.
End MODSIMNAT.
