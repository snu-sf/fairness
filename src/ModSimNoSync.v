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
          (lsim: forall R_src R_tgt (RR: R_src -> R_tgt -> URA.car -> shared_rel), bool -> bool -> URA.car -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel)
          (_lsim: forall R_src R_tgt (RR: R_src -> R_tgt -> URA.car -> shared_rel),bool -> bool -> URA.car -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel)
          R_src R_tgt (RR: R_src -> R_tgt -> URA.car -> shared_rel)
    :
    bool -> bool -> URA.car -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel :=
  | lsim_ret
      f_src f_tgt r_ctx
      ths im_src im_tgt st_src st_tgt r_shared
      r_src r_tgt
      (LSIM: RR r_src r_tgt r_ctx (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx (Ret r_src) (Ret r_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)

  | lsim_tauL
      f_src f_tgt r_ctx
      ths im_src im_tgt st_src st_tgt r_shared
      itr_src itr_tgt
      (LSIM: _lsim _ _ RR true f_tgt r_ctx itr_src itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx (Tau itr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | lsim_chooseL
      f_src f_tgt r_ctx
      ths im_src im_tgt st_src st_tgt r_shared
      X ktr_src itr_tgt
      (LSIM: exists x, _lsim _ _ RR true f_tgt r_ctx (ktr_src x) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx (trigger (Choose X) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | lsim_putL
      f_src f_tgt r_ctx
      ths im_src im_tgt st_src st_tgt r_shared
      st ktr_src itr_tgt
      (LSIM: _lsim _ _ RR true f_tgt r_ctx (ktr_src tt) itr_tgt (ths, im_src, im_tgt, st, st_tgt, r_shared))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx (trigger (Put st) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | lsim_getL
      f_src f_tgt r_ctx
      ths im_src im_tgt st_src st_tgt r_shared
      ktr_src itr_tgt
      (LSIM: _lsim _ _ RR true f_tgt r_ctx (ktr_src st_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx (trigger (@Get _) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | lsim_tidL
      f_src f_tgt r_ctx
      ths im_src im_tgt st_src st_tgt r_shared
      ktr_src itr_tgt
      (LSIM: _lsim _ _ RR true f_tgt r_ctx (ktr_src tid) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx (trigger (GetTid) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | lsim_UB
      f_src f_tgt r_ctx
      ths im_src im_tgt st_src st_tgt r_shared
      ktr_src itr_tgt
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx (trigger (Undefined) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | lsim_fairL
      f_src f_tgt r_ctx
      ths im_src0 im_tgt st_src st_tgt r_shared
      f ktr_src itr_tgt
      (LSIM: exists im_src1,
          (<<FAIR: fair_update im_src0 im_src1 (sum_fmap_r f)>>) /\
            (<<LSIM: _lsim _ _ RR true f_tgt r_ctx (ktr_src tt) itr_tgt (ths, im_src1, im_tgt, st_src, st_tgt, r_shared)>>))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx (trigger (Fair f) >>= ktr_src) itr_tgt (ths, im_src0, im_tgt, st_src, st_tgt, r_shared)

  | lsim_tauR
      f_src f_tgt r_ctx
      ths im_src im_tgt st_src st_tgt r_shared
      itr_src itr_tgt
      (LSIM: _lsim _ _ RR f_src true r_ctx itr_src itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx itr_src (Tau itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | lsim_chooseR
      f_src f_tgt r_ctx
      ths im_src im_tgt st_src st_tgt r_shared
      X itr_src ktr_tgt
      (LSIM: forall x, _lsim _ _ RR f_src true r_ctx itr_src (ktr_tgt x) (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx itr_src (trigger (Choose X) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | lsim_putR
      f_src f_tgt r_ctx
      ths im_src im_tgt st_src st_tgt r_shared
      st itr_src ktr_tgt
      (LSIM: _lsim _ _ RR f_src true r_ctx itr_src (ktr_tgt tt) (ths, im_src, im_tgt, st_src, st, r_shared))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx itr_src (trigger (Put st) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | lsim_getR
      f_src f_tgt r_ctx
      ths im_src im_tgt st_src st_tgt r_shared
      itr_src ktr_tgt
      (LSIM: _lsim _ _ RR f_src true r_ctx itr_src (ktr_tgt st_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx itr_src (trigger (@Get _) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | lsim_tidR
      f_src f_tgt r_ctx
      ths im_src im_tgt st_src st_tgt r_shared
      itr_src ktr_tgt
      (LSIM: _lsim _ _ RR f_src true r_ctx itr_src (ktr_tgt tid) (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx itr_src (trigger (GetTid) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | lsim_fairR
      f_src f_tgt r_ctx
      ths im_src im_tgt0 st_src st_tgt r_shared
      f itr_src ktr_tgt
      (LSIM: forall im_tgt1
                   (FAIR: fair_update im_tgt0 im_tgt1 (sum_fmap_r f)),
          (<<LSIM: _lsim _ _ RR f_src true r_ctx itr_src (ktr_tgt tt) (ths, im_src, im_tgt1, st_src, st_tgt, r_shared)>>))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx itr_src (trigger (Fair f) >>= ktr_tgt) (ths, im_src, im_tgt0, st_src, st_tgt, r_shared)

  | lsim_observe
      f_src f_tgt r_ctx
      ths im_src im_tgt st_src st_tgt r_shared
      fn args ktr_src ktr_tgt
      (LSIM: forall ret,
          _lsim _ _ RR true true r_ctx (ktr_src ret) (ktr_tgt ret) (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx (trigger (Observe fn args) >>= ktr_src) (trigger (Observe fn args) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)

  | lsim_yieldR
      f_src f_tgt r_ctx0
      ths0 im_src0 im_tgt0 st_src0 st_tgt0 r_shared0
      r_own r_shared
      ktr_src ktr_tgt
      (INV: I (ths0, im_src0, im_tgt0, st_src0, st_tgt0, r_shared))
      (VALID: URA.wf (r_shared ⋅ r_own ⋅ r_ctx0))
      (LSIM: forall ths1 im_src1 im_tgt1 st_src1 st_tgt1 r_shared1 r_ctx1
                    (INV: I (ths1, im_src1, im_tgt1, st_src1, st_tgt1, r_shared1))
                    (VALID: URA.wf (r_shared1 ⋅ r_own ⋅ r_ctx1))
                    im_tgt2
                    (TGT: fair_update im_tgt1 im_tgt2 (sum_fmap_l (tids_fmap tid ths1))),
          _lsim _ _ RR f_src true r_ctx1 (trigger (Yield) >>= ktr_src) (ktr_tgt tt) (ths1, im_src1, im_tgt2, st_src1, st_tgt1, r_shared1))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx0 (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt) (ths0, im_src0, im_tgt0, st_src0, st_tgt0, r_shared0)
  | lsim_yieldL
      f_src f_tgt r_ctx
      ths im_src0 im_tgt st_src st_tgt r_shared
      ktr_src itr_tgt
      (LSIM: exists im_src1,
          (<<FAIR: fair_update im_src0 im_src1 (sum_fmap_l (tids_fmap tid ths))>>) /\
            (<<LSIM: _lsim _ _ RR true f_tgt r_ctx (ktr_src tt) itr_tgt (ths, im_src1, im_tgt, st_src, st_tgt, r_shared)>>))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx (trigger (Yield) >>= ktr_src) itr_tgt (ths, im_src0, im_tgt, st_src, st_tgt, r_shared)

  | lsim_progress
      r_ctx
      ths im_src im_tgt st_src st_tgt r_shared
      itr_src itr_tgt
      (LSIM: lsim _ _ RR false false r_ctx itr_src itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    __lsim tid lsim _lsim RR true true r_ctx itr_src itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  .

  Definition lsim (tid: thread_id)
             R_src R_tgt (RR: R_src -> R_tgt -> URA.car -> shared_rel):
    bool -> bool -> URA.car -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel :=
    paco9 (fun r => pind9 (__lsim tid r) top9) bot9 R_src R_tgt RR.

  Lemma __lsim_mon tid:
    forall r r' (LE: r <9= r'), (__lsim tid r) <10= (__lsim tid r').
  Proof.
    ii. inv PR; try (econs; eauto; fail).
  Qed.

  Lemma _lsim_mon tid: forall r, monotone9 (__lsim tid r).
  Proof.
    ii. inv IN; try (econs; eauto; fail).
    { des. econs; eauto. }
    { des. econs; eauto. }
    { econs. i. eapply LE. eapply LSIM. eauto. }
    { des. econs; esplits; eauto. }
  Qed.

  Lemma lsim_mon tid: forall q, monotone9 (fun r => pind9 (__lsim tid r) q).
  Proof.
    ii. eapply pind9_mon_gen; eauto.
    ii. eapply __lsim_mon; eauto.
  Qed.

  Variant lsim_resetC
          (r: forall R_src R_tgt (RR: R_src -> R_tgt -> URA.car -> shared_rel), bool -> bool -> URA.car -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel)
          R_src R_tgt (RR: R_src -> R_tgt -> URA.car -> shared_rel)
    :
    bool -> bool -> URA.car -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel :=
    | lsim_resetC_intro
        src tgt shr r_ctx
        ps0 pt0 ps1 pt1
        (REL: r _ _ RR ps1 pt1 r_ctx src tgt shr)
        (SRC: ps1 = true -> ps0 = true)
        (TGT: pt1 = true -> pt0 = true)
      :
      lsim_resetC r RR ps0 pt0 r_ctx src tgt shr
  .

  Lemma lsim_resetC_spec tid
    :
    lsim_resetC <10= gupaco9 (fun r => pind9 (__lsim tid r) top9) (cpn9 (fun r => pind9 (__lsim tid r) top9)).
  Proof.
    eapply wrespect9_uclo; eauto with paco.
    { eapply lsim_mon. }
    econs.
    { ii. inv IN. econs; eauto. }
    i. inv PR. eapply GF in REL.
    eapply pind9_acc in REL.
    instantiate (1:= (fun R0 R1 (RR: R0 -> R1 -> URA.car -> shared_rel) ps1 pt1 r_ctx src tgt shr =>
                        forall ps0 pt0,
                          (ps1 = true -> ps0 = true) ->
                          (pt1 = true -> pt0 = true) ->
                          pind9 (__lsim tid (rclo9 lsim_resetC r)) top9 R0 R1 RR ps0 pt0 r_ctx src tgt shr)) in REL; eauto.
    ss. i. eapply pind9_unfold in PR.
    2:{ eapply _lsim_mon. }
    rename PR into LSIM. inv LSIM.

    { eapply pind9_fold. econs; eauto. }

    { destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      eapply pind9_fold. eapply lsim_tauL. split; ss.
      hexploit IH; eauto.
    }

    { des. eapply pind9_fold. eapply lsim_chooseL. esplits; eauto. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { eapply pind9_fold. eapply lsim_putL. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { eapply pind9_fold. eapply lsim_getL. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { eapply pind9_fold. eapply lsim_tidL. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { eapply pind9_fold. eapply lsim_UB. }

    { des. eapply pind9_fold. eapply lsim_fairL. esplits; eauto. split; ss.
      destruct LSIM as [LSIM IND]. hexploit IH; eauto.
    }

    { destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      eapply pind9_fold. eapply lsim_tauR. split; ss.
      hexploit IH. eauto. all: eauto.
    }

    { eapply pind9_fold. eapply lsim_chooseR. i. split; ss. specialize (LSIM0 x).
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { eapply pind9_fold. eapply lsim_putR. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { eapply pind9_fold. eapply lsim_getR. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { eapply pind9_fold. eapply lsim_tidR. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { eapply pind9_fold. eapply lsim_fairR. i. split; ss. specialize (LSIM0 _ FAIR).
      des. destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { eapply pind9_fold. eapply lsim_observe. i. split; ss. specialize (LSIM0 ret).
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { eapply pind9_fold. eapply lsim_yieldR; eauto. i.
      hexploit LSIM0; eauto. clear LSIM0. intros LSIM0.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. split; ss; eauto.
    }

    { des. eapply pind9_fold. eapply lsim_yieldL. esplits; eauto. split; ss.
      destruct LSIM as [LSIM IND]. hexploit IH; eauto.
    }

    { pclearbot. hexploit H; ss; i. hexploit H0; ss; i. clarify.
      eapply pind9_fold. eapply lsim_progress. eapply rclo9_base. auto. }
  Qed.

  Lemma lsim_reset_prog
        tid
        R0 R1 (RR: R0 -> R1 -> URA.car -> shared_rel)
        src tgt shr
        ps0 pt0 ps1 pt1 r_ctx
        (LSIM: lsim tid RR ps1 pt1 r_ctx src tgt shr)
        (SRC: ps1 = true -> ps0 = true)
        (TGT: pt1 = true -> pt0 = true)
    :
    lsim tid RR ps0 pt0 r_ctx src tgt shr.
  Proof.
    ginit.
    { eapply lsim_mon. }
    { eapply cpn9_wcompat. eapply lsim_mon. }
    guclo lsim_resetC_spec.
    { eapply lsim_mon. }
    econs; eauto. gfinal.
    { eapply lsim_mon. }
    right. auto.
  Qed.

  Lemma lsim_set_prog
        tid
        R0 R1 (RR: R0 -> R1 -> URA.car -> shared_rel)
        r_ctx src tgt shr
        (LSIM: lsim tid RR true true r_ctx src tgt shr)
    :
    forall ps pt, lsim tid RR ps pt r_ctx src tgt shr.
  Proof.
    i. revert_until tid. pcofix CIH. i.
    remember true as ps0 in LSIM at 1. remember true as pt0 in LSIM at 1.
    move LSIM before CIH. revert_until LSIM. punfold LSIM.
    2:{ eapply lsim_mon. }
    eapply pind9_acc in LSIM.

    { instantiate (1:= (fun R0 R1 (RR: R0 -> R1 -> URA.car -> shared_rel) ps0 pt0 r_ctx src tgt shr =>
                          ps0 = true ->
                          pt0 = true ->
                          forall ps pt,
                            paco9
                              (fun r0 =>
                                 pind9 (__lsim tid r0) top9) r R0 R1 RR ps pt r_ctx src tgt shr)) in LSIM; auto. }

    ss. clear ps0 pt0 r_ctx src tgt shr LSIM.
    intros rr DEC IH R0' R1' RR' gps gpt r_ctx src tgt shr LSIM. clear DEC.
    intros Egps Egpt ps pt.
    eapply pind9_unfold in LSIM.
    2:{ eapply _lsim_mon. }
    inv LSIM.

    { pfold. eapply pind9_fold. econs; eauto. }

    { destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      pfold. eapply pind9_fold. eapply lsim_tauL. split; ss.
      hexploit IH. eauto. all: eauto. i. punfold H. eapply lsim_mon.
    }

    { des. pfold. eapply pind9_fold. eapply lsim_chooseL. esplits; eauto. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind9_fold. eapply lsim_putL. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind9_fold. eapply lsim_getL. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind9_fold. eapply lsim_tidL. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind9_fold. eapply lsim_UB. }

    { des. pfold. eapply pind9_fold. eapply lsim_fairL. esplits; eauto. split; ss.
      destruct LSIM as [LSIM IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      pfold. eapply pind9_fold. eapply lsim_tauR. split; ss.
      hexploit IH. eauto. all: eauto. i. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind9_fold. eapply lsim_chooseR. i. split; ss. specialize (LSIM0 x).
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind9_fold. eapply lsim_putR. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind9_fold. eapply lsim_getR. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind9_fold. eapply lsim_tidR. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind9_fold. eapply lsim_fairR. i. split; ss. specialize (LSIM0 _ FAIR).
      des. destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind9_fold. eapply lsim_observe. i. split; ss. specialize (LSIM0 ret).
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind9_fold. eapply lsim_yieldR; eauto. i.
      hexploit LSIM0; eauto. clear LSIM0. intros LSIM0.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. split; ss. punfold H. eapply lsim_mon.
    }

    { des. pfold. eapply pind9_fold. eapply lsim_yieldL. esplits; eauto. split; ss.
      destruct LSIM as [LSIM IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pclearbot. eapply paco9_mon_bot. eapply lsim_reset_prog. eauto. all: ss. }

  Qed.

  Local Hint Resolve __lsim_mon: paco.
  Local Hint Resolve _lsim_mon: paco.
  Local Hint Resolve lsim_mon: paco.

  (* Lemma lsim_ind *)
  (*       tid *)
  (*       (P: forall R0 R1 (RR: R0 -> R1 -> URA.car -> shared_rel), bool -> bool -> URA.car -> (itree srcE R0) -> (itree tgtE R1) -> shared_rel) *)
  (* (RET: forall R0 R1 (RR: R0 -> R1 -> URA.car -> shared_rel) *)
  (*     f_src f_tgt r_ctx *)
  (*     ths im_src im_tgt st_src st_tgt r_shared *)
  (*     r_src r_tgt *)
  (*     (LSIM: RR r_src r_tgt r_ctx (ths, im_src, im_tgt, st_src, st_tgt, r_shared)), *)
  (*   P R0 R1 RR f_src f_tgt r_ctx (Ret r_src) (Ret r_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)) *)
  (* (TAUL: forall R0 R1 (RR: R0 -> R1 -> URA.car -> shared_rel) *)
  (*     f_src f_tgt r_ctx *)
  (*     ths im_src im_tgt st_src st_tgt r_shared *)
  (*     itr_src itr_tgt *)
  (*     (LSIM: lsim tid RR true f_tgt r_ctx itr_src itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)) *)
  (*     (IH: P R0 R1 RR true f_tgt r_ctx itr_src itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)), *)
  (*   P R0 R1 RR f_src f_tgt r_ctx (Tau itr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)) *)
  (* (CHOOSEL: forall R0 R1 (RR: R0 -> R1 -> URA.car -> shared_rel) *)
  (*     f_src f_tgt r_ctx *)
  (*     ths im_src im_tgt st_src st_tgt r_shared *)
  (*     X ktr_src itr_tgt *)
  (*     (LSIM: exists x, (<<LSIM: lsim tid RR true f_tgt r_ctx (ktr_src x) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)>>) /\ *)
  (*     (<<IH: P R0 R1 RR true f_tgt r_ctx (ktr_src x) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)>>)), *)
  (*   P R0 R1 RR f_src f_tgt r_ctx (trigger (Choose X) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)) *)
  (* (PUTL: forall R0 R1 (RR: R0 -> R1 -> URA.car -> shared_rel) *)
  (*     f_src f_tgt r_ctx *)
  (*     ths im_src im_tgt st_src st_tgt r_shared *)
  (*     st ktr_src itr_tgt *)
  (*     (LSIM: lsim tid RR true f_tgt r_ctx (ktr_src tt) itr_tgt (ths, im_src, im_tgt, st, st_tgt, r_shared)) *)
  (*     (IH: P R0 R1 RR true f_tgt r_ctx (ktr_src tt) itr_tgt (ths, im_src, im_tgt, st, st_tgt, r_shared)), *)
  (*   P R0 R1 RR f_src f_tgt r_ctx (trigger (Put st) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)) *)
  (* (GETL: forall R0 R1 (RR: R0 -> R1 -> URA.car -> shared_rel) *)
  (*     f_src f_tgt r_ctx *)
  (*     ths im_src im_tgt st_src st_tgt r_shared *)
  (*     ktr_src itr_tgt *)
  (*     (LSIM: lsim tid RR true f_tgt r_ctx (ktr_src st_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)) *)
  (*     (IH: P R0 R1 RR true f_tgt r_ctx (ktr_src st_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)), *)
  (*   P R0 R1 RR f_src f_tgt r_ctx (trigger (@Get _) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)) *)
  (* (TIDL: forall R0 R1 (RR: R0 -> R1 -> URA.car -> shared_rel) *)
  (*     f_src f_tgt r_ctx *)
  (*     ths im_src im_tgt st_src st_tgt r_shared *)
  (*     ktr_src itr_tgt *)
  (*     (LSIM: lsim tid RR true f_tgt r_ctx (ktr_src tid) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)) *)
  (*     (IH: P R0 R1 RR true f_tgt r_ctx (ktr_src tid) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)), *)
  (*   P R0 R1 RR f_src f_tgt r_ctx (trigger (GetTid) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)) *)
  (* (UB: forall R0 R1 (RR: R0 -> R1 -> URA.car -> shared_rel) *)
  (*     f_src f_tgt r_ctx *)
  (*     ths im_src im_tgt st_src st_tgt r_shared *)
  (*     ktr_src itr_tgt, *)
  (*   P R0 R1 RR f_src f_tgt r_ctx (trigger (Undefined) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)) *)
  (* (FAIRL: forall R0 R1 (RR: R0 -> R1 -> URA.car -> shared_rel) *)
  (*     f_src f_tgt r_ctx *)
  (*     ths im_src0 im_tgt st_src st_tgt r_shared *)
  (*     f ktr_src itr_tgt *)
  (*     (LSIM: exists im_src1, *)
  (*         (<<FAIR: fair_update im_src0 im_src1 (sum_fmap_r f)>>) /\ *)
  (*           (<<LSIM: lsim tid RR true f_tgt r_ctx (ktr_src tt) itr_tgt (ths, im_src1, im_tgt, st_src, st_tgt, r_shared)>>) /\ *)
  (*           (<<IH: P R0 R1 RR true f_tgt r_ctx (ktr_src tt) itr_tgt (ths, im_src1, im_tgt, st_src, st_tgt, r_shared)>>)), *)
  (*   P R0 R1 RR f_src f_tgt r_ctx (trigger (Fair f) >>= ktr_src) itr_tgt (ths, im_src0, im_tgt, st_src, st_tgt, r_shared)) *)

  (* (TAUR: forall R0 R1 (RR: R0 -> R1 -> URA.car -> shared_rel) *)
  (*     f_src f_tgt r_ctx *)
  (*     ths im_src im_tgt st_src st_tgt r_shared *)
  (*     itr_src itr_tgt *)
  (*     (LSIM: lsim tid RR f_src true r_ctx itr_src itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)) *)
  (*     (IH: P R0 R1 RR f_src true r_ctx itr_src itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)), *)
  (*   P R0 R1 RR f_src f_tgt r_ctx itr_src (Tau itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)) *)
  (* (CHOOSER: forall R0 R1 (RR: R0 -> R1 -> URA.car -> shared_rel) *)
  (*     f_src f_tgt r_ctx *)
  (*     ths im_src im_tgt st_src st_tgt r_shared *)
  (*     X itr_src ktr_tgt *)
  (*     (LSIM: forall x, *)
  (*         (<<LSIM: lsim tid RR f_src true r_ctx itr_src (ktr_tgt x) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)>>) /\ *)
  (*         (<<IH: P R0 R1 RR f_src true r_ctx itr_src (ktr_tgt x) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)>>)), *)
  (*   P R0 R1 RR f_src f_tgt r_ctx itr_src (trigger (Choose X) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)) *)
  (* (PUTR: forall R0 R1 (RR: R0 -> R1 -> URA.car -> shared_rel) *)
  (*     f_src f_tgt r_ctx *)
  (*     ths im_src im_tgt st_src st_tgt r_shared *)
  (*     st itr_src ktr_tgt *)
  (*     (LSIM: lsim tid RR f_src true r_ctx itr_src (ktr_tgt tt) (ths, im_src, im_tgt, st_src, st, r_shared)) *)
  (*     (IH: P R0 R1 RR f_src true r_ctx itr_src (ktr_tgt tt) (ths, im_src, im_tgt, st_src, st, r_shared)), *)
  (*   P R0 R1 RR f_src f_tgt r_ctx itr_src (trigger (Put st) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)) *)
  (* (GETR: forall R0 R1 (RR: R0 -> R1 -> URA.car -> shared_rel) *)
  (*     f_src f_tgt r_ctx *)
  (*     ths im_src im_tgt st_src st_tgt r_shared *)
  (*     itr_src ktr_tgt *)
  (*     (LSIM: lsim tid RR f_src true r_ctx itr_src (ktr_tgt st_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)), *)
  (*   P R0 R1 RR f_src f_tgt r_ctx itr_src (trigger (@Get _) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)) *)
  (* (TIDR: forall R0 R1 (RR: R0 -> R1 -> URA.car -> shared_rel) *)
  (*     f_src f_tgt r_ctx *)
  (*     ths im_src im_tgt st_src st_tgt r_shared *)
  (*     itr_src ktr_tgt *)
  (*     (LSIM: lsim tid RR f_src true r_ctx itr_src (ktr_tgt tid) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)), *)
  (*   P R0 R1 RR f_src f_tgt r_ctx itr_src (trigger (GetTid) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)) *)
  (* (FAIRR: forall R0 R1 (RR: R0 -> R1 -> URA.car -> shared_rel) *)
  (*     f_src f_tgt r_ctx *)
  (*     ths im_src im_tgt0 st_src st_tgt r_shared *)
  (*     f itr_src ktr_tgt *)
  (*     (LSIM: forall im_tgt1 *)
  (*                  (FAIR: fair_update im_tgt0 im_tgt1 (sum_fmap_r f)), *)
  (*         (<<LSIM: lsim tid RR f_src true r_ctx itr_src (ktr_tgt tt) (ths, im_src, im_tgt1, st_src, st_tgt, r_shared)>>) /\ *)
  (*         (<<IH: P R0 R1 RR f_src true r_ctx itr_src (ktr_tgt tt) (ths, im_src, im_tgt1, st_src, st_tgt, r_shared)>>)), *)
  (*   P R0 R1 RR f_src f_tgt r_ctx itr_src (trigger (Fair f) >>= ktr_tgt) (ths, im_src, im_tgt0, st_src, st_tgt, r_shared)) *)

  (* (OBSERVE: forall R0 R1 (RR: R0 -> R1 -> URA.car -> shared_rel) *)
  (*     f_src f_tgt r_ctx *)
  (*     ths im_src im_tgt st_src st_tgt r_shared *)
  (*     fn args ktr_src ktr_tgt *)
  (*     (LSIM: forall ret, *)
  (*         (<<LSIM: lsim tid RR true true r_ctx (ktr_src ret) (ktr_tgt ret) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)>>) /\ *)
  (*         (<<IH: P R0 R1 RR true true r_ctx (ktr_src ret) (ktr_tgt ret) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)>>)), *)
  (*   P R0 R1 RR f_src f_tgt r_ctx (trigger (Observe fn args) >>= ktr_src) (trigger (Observe fn args) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)) *)

  (* (YIELDR: forall R0 R1 (RR: R0 -> R1 -> URA.car -> shared_rel) *)
  (*     f_src f_tgt r_ctx0 *)
  (*     ths0 im_src0 im_tgt0 st_src0 st_tgt0 r_shared0 *)
  (*     r_own r_shared *)
  (*     ktr_src ktr_tgt *)
  (*     (INV: I (ths0, im_src0, im_tgt0, st_src0, st_tgt0, r_shared)) *)
  (*     (VALID: URA.wf (r_shared ⋅ r_own ⋅ r_ctx0)) *)
  (*     (LSIM: forall ths1 im_src1 im_tgt1 st_src1 st_tgt1 r_shared1 r_ctx1 *)
  (*                   (INV: I (ths1, im_src1, im_tgt1, st_src1, st_tgt1, r_shared1)) *)
  (*                   (VALID: URA.wf (r_shared1 ⋅ r_own ⋅ r_ctx1)) *)
  (*                   im_tgt2 *)
  (*                   (TGT: fair_update im_tgt1 im_tgt2 (sum_fmap_l (tids_fmap tid ths1))), *)
  (*         (<<LSIM: lsim tid RR f_src true r_ctx1 (trigger (Yield) >>= ktr_src) (ktr_tgt tt) (ths1, im_src1, im_tgt2, st_src1, st_tgt1, r_shared1)>>) /\ *)
  (*           (<<IH: P R0 R1 RR f_src true r_ctx1 (trigger (Yield) >>= ktr_src) (ktr_tgt tt) (ths1, im_src1, im_tgt2, st_src1, st_tgt1, r_shared1)>>)), *)
  (*   P R0 R1 RR f_src f_tgt r_ctx0 (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt) (ths0, im_src0, im_tgt0, st_src0, st_tgt0, r_shared0)) *)
  (* (YIELDL: forall R0 R1 (RR: R0 -> R1 -> URA.car -> shared_rel) *)
  (*     f_src f_tgt r_ctx *)
  (*     ths im_src0 im_tgt st_src st_tgt r_shared *)
  (*     ktr_src itr_tgt *)
  (*     (LSIM: exists im_src1, *)
  (*         (<<FAIR: fair_update im_src0 im_src1 (sum_fmap_l (tids_fmap tid ths))>>) /\ *)
  (*           (<<LSIM: lsim tid RR true f_tgt r_ctx (ktr_src tt) itr_tgt (ths, im_src1, im_tgt, st_src, st_tgt, r_shared)>>) /\ *)
  (*           (<<IH: P R0 R1 RR true f_tgt r_ctx (ktr_src tt) itr_tgt (ths, im_src1, im_tgt, st_src, st_tgt, r_shared)>>)), *)
  (*   P R0 R1 RR f_src f_tgt r_ctx (trigger (Yield) >>= ktr_src) itr_tgt (ths, im_src0, im_tgt, st_src, st_tgt, r_shared)) *)

  (* (PROG: forall R0 R1 (RR: R0 -> R1 -> URA.car -> shared_rel) *)
  (*     r_ctx *)
  (*     ths im_src im_tgt st_src st_tgt r_shared *)
  (*     itr_src itr_tgt *)
  (*     (LSIM: lsim tid RR false false r_ctx itr_src itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)), *)
  (*     P R0 R1 RR true true r_ctx itr_src itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)) *)
  (*   : *)
  (*   forall R0 R1 (RR: R0 -> R1 -> URA.car -> shared_rel) f_src f_tgt r_ctx ths im_src im_tgt st_src st_tgt r_shared itr_src itr_tgt *)
  (*     (LSIM: lsim tid RR f_src f_tgt r_ctx itr_src itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)), *)
  (*     P R0 R1 RR f_src f_tgt r_ctx itr_src itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared). *)
  (* Proof. *)
  (*   i. match goal with | LSIM: lsim tid RR _ _ _ _ _ ?_shr |- _ => remember _shr as shr end. *)
  (*   move LSIM before PROG. revert_until LSIM. *)
  (*   punfold LSIM. *)
  (*   pattern R0, R1, RR, f_src, f_tgt, r_ctx, itr_src, itr_tgt, shr. *)
  (*   revert R0 R1 RR f_src f_tgt r_ctx itr_src itr_tgt shr LSIM. apply pind9_acc. *)
  (*   intros rr DEC IH. clear DEC. intros R0 R1 RR f_src f_tgt r_ctx itr_src itr_tgt shr LSIM. *)
  (*   i. clarify. *)
  (*   eapply pind9_unfold in LSIM. *)
  (*   2:{ eapply _lsim_mon. } *)
  (*   inv LSIM. *)

  (*   { eapply RET; eauto. } *)

  (*   { destruct LSIM0 as [LSIM IND]. eapply TAUL; eauto. *)
  (*     pfold. eapply pind9_mon_top; eauto. *)
  (*   } *)

  (*   { des. eapply CHOOSEL; eauto. exists x. *)
  (*     destruct LSIM0 as [LSIM IND]. splits; eauto. pfold. eapply pind9_mon_top; eauto. *)
  (*   } *)

  (*   { destruct LSIM0 as [LSIM IND]. eapply PUTL; eauto. *)
  (*     pfold. eapply pind9_mon_top; eauto. *)
  (*   } *)

  (*   { destruct LSIM0 as [LSIM IND]. eapply GETL; eauto. *)
  (*     pfold. eapply pind9_mon_top; eauto. *)
  (*   } *)

  (*   { destruct LSIM0 as [LSIM IND]. eapply TIDL; eauto. *)
  (*     pfold. eapply pind9_mon_top; eauto. *)
  (*   } *)

  (*   { eapply UB; eauto. } *)

  (*   { des. destruct LSIM as [LSIM IND]. *)
  (*     eapply FAIRL. esplits; eauto. pfold. eapply pind9_mon_top; eauto. *)
  (*   } *)

  (*   { destruct LSIM0 as [LSIM IND]. eapply TAUR; eauto. *)
  (*     pfold. eapply pind9_mon_top; eauto. *)
  (*   } *)

  (*   { eapply CHOOSER; eauto. i. specialize (LSIM0 x). destruct LSIM0 as [LSIM IND]. splits; eauto. *)
  (*     pfold. eapply pind9_mon_top; eauto. *)
  (*   } *)

  (*   { destruct LSIM0 as [LSIM IND]. eapply PUTR; eauto. *)
  (*     pfold. eapply pind9_mon_top; eauto. *)
  (*   } *)

  (*   { destruct LSIM0 as [LSIM IND]. eapply GETR; eauto. *)
  (*     pfold. eapply pind9_mon_top; eauto. *)
  (*   } *)

  (*   { destruct LSIM0 as [LSIM IND]. eapply TIDR; eauto. *)
  (*     pfold. eapply pind9_mon_top; eauto. *)
  (*   } *)

  (*   { eapply FAIRR; eauto. i. specialize (LSIM0 _ FAIR). destruct LSIM0 as [LSIM IND]. splits; eauto. *)
  (*     pfold. eapply pind9_mon_top; eauto. *)
  (*   } *)

  (*   { eapply OBSERVE. i. specialize (LSIM0 ret). destruct LSIM0 as [LSIM IND]. splits; eauto. *)
  (*     pfold. eapply pind9_mon_top; eauto. *)
  (*   } *)

  (*   { eapply YIELDR; eauto. i. hexploit LSIM0; clear LSIM0. eapply INV0. eapply VALID0. all: eauto. *)
  (*     intros [LSIM IND]. splits; eauto. pfold. eapply pind9_mon_top; eauto. *)
  (*   } *)

  (*   { des. destruct LSIM as [LSIM IND]. eapply YIELDL; eauto. esplits; eauto. *)
  (*     pfold. eapply pind9_mon_top; eauto. *)
  (*   } *)

  (*   { pclearbot. eapply PROG; eauto. } *)

  (* Qed. *)

  Definition local_RR {R0 R1} (RR: R0 -> R1 -> Prop) tid:
    R0 -> R1 -> URA.car -> shared_rel :=
    fun (r_src: R0) (r_tgt: R1) (r_ctx: URA.car) '(ths2, im_src1, im_tgt1, st_src1, st_tgt1, r_shared1) =>
      (exists ths3 r_own r_shared2,
          (<<THS: NatMap.remove tid ths2 = ths3>>) /\
            (<<VALID: URA.wf (r_shared2 ⋅ r_own ⋅ r_ctx)>>) /\
            (<<INV: I (ths3, im_src1, im_tgt1, st_src1, st_tgt1, r_shared2)>>) /\
            (<<RET: RR r_src r_tgt>>)).

  Definition local_sim {R0 R1} (RR: R0 -> R1 -> Prop) src tgt :=
    forall ths0 im_src0 im_tgt0 st_src0 st_tgt0 r_shared0 r_ctx0
           (INV: I (ths0, im_src0, im_tgt0, st_src0, st_tgt0, r_shared0))
           tid ths1
           (THS: TIdSet.add_new tid ths0 ths1)
           (VALID: URA.wf (r_shared0 ⋅ r_ctx0)),
    exists r_shared1 r_own,
      (<<INV: I (ths1, im_src0, im_tgt0, st_src0, st_tgt0, r_shared1)>>) /\
        (<<VALID: URA.wf (r_shared1 ⋅ r_own ⋅ r_ctx0)>>) /\
        (forall ths im_src1 im_tgt1 st_src st_tgt r_shared2 r_ctx2
                (INV: I (ths, im_src1, im_tgt1, st_src, st_tgt, r_shared2))
                (VALID: URA.wf (r_shared2 ⋅ r_own ⋅ r_ctx2)),
          forall im_tgt2 (TGT: fair_update im_tgt1 im_tgt2 (sum_fmap_l (tids_fmap tid ths))),
          exists im_src2,
            (<<SRC: fair_update im_src1 im_src2 (sum_fmap_l (tids_fmap tid ths))>>) /\
              (<<LSIM: forall fs ft,
                  lsim
                    tid
                    (@local_RR R0 R1 RR tid)
                    fs ft
                    r_ctx2
                    src tgt
                    (ths, im_src2, im_tgt2, st_src, st_tgt, r_shared2)
                    >>)).

  (* Definition shared_rel_wf: Prop := *)
  (*   forall ths im_src0 im_tgt0 st_src st_tgt r_shared0 r_ctx *)
  (*          (INV: I (ths, im_src0, im_tgt0, st_src, st_tgt, r_shared0)) *)
  (*          (VALID: URA.wf (r_shared0 ⋅ r_ctx)), *)
  (*   forall im_tgt1 *)
  (*          (TGT: fair_update im_tgt0 im_tgt1 (sum_fmap_l (tids_fmap_all ths))), *)
  (*   exists im_src1 r_shared1, *)
  (*     (<<SRC: fair_update im_src0 im_src1 (sum_fmap_l (tids_fmap_all ths))>>) /\ *)
  (*       (<<INV: I (ths, im_src1, im_tgt1, st_src, st_tgt, r_shared1)>>) /\ *)
  (*       (<<VALID: URA.wf (r_shared1 ⋅ r_ctx)>>). *)

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
          wf_src : WF;
          wf_tgt : WF;
          wf_tgt_inhabited: inhabited wf_tgt.(T);
          wf_tgt_open: forall (o0: wf_tgt.(T)), exists o1, wf_tgt.(lt) o0 o1;

          world: URA.t;

          I: (@shared world md_src.(Mod.state) md_tgt.(Mod.state) md_src.(Mod.ident) md_tgt.(Mod.ident) wf_src wf_tgt) -> Prop;
          init: forall im_tgt, exists im_src r_shared,
            (I (NatSet.empty, im_src, im_tgt, md_src.(Mod.st_init), md_tgt.(Mod.st_init), r_shared)) /\
              (URA.wf r_shared);

          funs: forall fn args, match md_src.(Mod.funs) fn, md_tgt.(Mod.funs) fn with
                           | None, _ => True
                           | _, None => False
                           | Some ktr_src, Some ktr_tgt => local_sim I (@eq Val) (ktr_src args) (ktr_tgt args)
                           end;
        }.
  End MODSIM.
End ModSim.
