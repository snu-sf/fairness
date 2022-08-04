From sflib Require Import sflib.
From ITree Require Export ITree.
From Paco Require Import paco.

Require Import Coq.Classes.RelationClasses.
Require Import Program.
Require Import Permutation.

Export ITreeNotations.

From Fairness Require Import Axioms.
From Fairness Require Export ITreeLib FairBeh FairSim NatStructs.
From Fairness Require Import pind PCM World WFLib.
From Fairness Require Export Mod ModSimNoSync ModSimStutter.

Set Implicit Arguments.

Section GENORDER.
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

  Variable wf_stt: WF.

  Let shared :=
    (TIdSet.t *
       (@imap ident_src wf_src) *
       (@imap ident_tgt wf_tgt) *
       state_src *
       state_tgt *
       URA.car)%type.

  Let shared_rel: Type := shared -> Prop.

  Variable I: shared_rel.

  Variant __geno
          (tid: thread_id)
          (* (geno: forall R_src R_tgt (RR: R_src -> R_tgt -> URA.car -> shared_rel), bool -> bool -> URA.car -> (wf_stt.(T) * itree srcE R_src) -> itree tgtE R_tgt -> shared_rel) *)
          (_geno: forall R_src R_tgt (RR: R_src -> R_tgt -> URA.car -> shared_rel),bool -> bool -> URA.car -> (wf_stt.(T) * itree srcE R_src) -> itree tgtE R_tgt -> shared_rel)
          R_src R_tgt (RR: R_src -> R_tgt -> URA.car -> shared_rel)
    :
    bool -> bool -> URA.car -> (wf_stt.(T) * itree srcE R_src) -> itree tgtE R_tgt -> shared_rel :=
  | geno_ret
      f_src f_tgt r_ctx o o0
      ths im_src im_tgt st_src st_tgt r_shared
      r_src r_tgt
      (LT: wf_stt.(lt) o0 o)
      (GENO: RR r_src r_tgt r_ctx (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    __geno tid geno _geno RR f_src f_tgt r_ctx (o, Ret r_src) (Ret r_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)

  | geno_tauL
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt r_shared
      itr_src itr_tgt
      (GENO: _geno _ _ RR true f_tgt r_ctx (o, itr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    __geno tid geno _geno RR f_src f_tgt r_ctx (o, Tau itr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | geno_chooseL
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt r_shared
      X ktr_src itr_tgt
      (GENO: exists x, _geno _ _ RR true f_tgt r_ctx (o, ktr_src x) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    __geno tid geno _geno RR f_src f_tgt r_ctx (o, trigger (Choose X) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | geno_putL
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt r_shared
      st ktr_src itr_tgt
      (GENO: _geno _ _ RR true f_tgt r_ctx (o, ktr_src tt) itr_tgt (ths, im_src, im_tgt, st, st_tgt, r_shared))
    :
    __geno tid geno _geno RR f_src f_tgt r_ctx (o, trigger (Put st) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | geno_getL
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt r_shared
      ktr_src itr_tgt
      (GENO: _geno _ _ RR true f_tgt r_ctx (o, ktr_src st_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    __geno tid geno _geno RR f_src f_tgt r_ctx (o, trigger (@Get _) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | geno_tidL
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt r_shared
      ktr_src itr_tgt
      (GENO: _geno _ _ RR true f_tgt r_ctx (o, ktr_src tid) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    __geno tid geno _geno RR f_src f_tgt r_ctx (o, trigger (GetTid) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | geno_UB
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt r_shared
      ktr_src itr_tgt
    :
    __geno tid geno _geno RR f_src f_tgt r_ctx (o, trigger (Undefined) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | geno_fairL
      f_src f_tgt r_ctx o
      ths im_src0 im_tgt st_src st_tgt r_shared
      f ktr_src itr_tgt
      (GENO: exists im_src1,
          (<<FAIR: fair_update im_src0 im_src1 (sum_fmap_r f)>>) /\
            (<<GENO: _geno _ _ RR true f_tgt r_ctx (o, ktr_src tt) itr_tgt (ths, im_src1, im_tgt, st_src, st_tgt, r_shared)>>))
    :
    __geno tid geno _geno RR f_src f_tgt r_ctx (o, trigger (Fair f) >>= ktr_src) itr_tgt (ths, im_src0, im_tgt, st_src, st_tgt, r_shared)

  | geno_tauR
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt r_shared
      itr_src itr_tgt
      (GENO: _geno _ _ RR f_src true r_ctx (o, itr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    __geno tid geno _geno RR f_src f_tgt r_ctx (o, itr_src) (Tau itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | geno_chooseR
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt r_shared
      X itr_src ktr_tgt
      (GENO: forall x, _geno _ _ RR f_src true r_ctx (o, itr_src) (ktr_tgt x) (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    __geno tid geno _geno RR f_src f_tgt r_ctx (o, itr_src) (trigger (Choose X) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | geno_putR
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt r_shared
      st itr_src ktr_tgt
      (GENO: _geno _ _ RR f_src true r_ctx (o, itr_src) (ktr_tgt tt) (ths, im_src, im_tgt, st_src, st, r_shared))
    :
    __geno tid geno _geno RR f_src f_tgt r_ctx (o, itr_src) (trigger (Put st) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | geno_getR
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt r_shared
      itr_src ktr_tgt
      (GENO: _geno _ _ RR f_src true r_ctx (o, itr_src) (ktr_tgt st_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    __geno tid geno _geno RR f_src f_tgt r_ctx (o, itr_src) (trigger (@Get _) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | geno_tidR
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt r_shared
      itr_src ktr_tgt
      (GENO: _geno _ _ RR f_src true r_ctx (o, itr_src) (ktr_tgt tid) (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    __geno tid geno _geno RR f_src f_tgt r_ctx (o, itr_src) (trigger (GetTid) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | geno_fairR
      f_src f_tgt r_ctx o
      ths im_src im_tgt0 st_src st_tgt r_shared
      f itr_src ktr_tgt
      (GENO: forall im_tgt1
                   (FAIR: fair_update im_tgt0 im_tgt1 (sum_fmap_r f)),
          (<<GENO: _geno _ _ RR f_src true r_ctx (o, itr_src) (ktr_tgt tt) (ths, im_src, im_tgt1, st_src, st_tgt, r_shared)>>))
    :
    __geno tid geno _geno RR f_src f_tgt r_ctx (o, itr_src) (trigger (Fair f) >>= ktr_tgt) (ths, im_src, im_tgt0, st_src, st_tgt, r_shared)

  | geno_observe
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt r_shared
      fn args ktr_src ktr_tgt
      (GENO: forall ret,
          _geno _ _ RR true true r_ctx (o, ktr_src ret) (ktr_tgt ret) (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    __geno tid geno _geno RR f_src f_tgt r_ctx (o, trigger (Observe fn args) >>= ktr_src) (trigger (Observe fn args) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)

  | geno_yieldR
      f_src f_tgt r_ctx0 o0
      ths0 im_src0 im_tgt0 st_src0 st_tgt0 r_shared0
      r_own r_shared
      ktr_src ktr_tgt
      (INV: I (ths0, im_src0, im_tgt0, st_src0, st_tgt0, r_shared))
      (VALID: URA.wf (r_shared ⋅ r_own ⋅ r_ctx0))
      (GENO: forall ths1 im_src1 im_tgt1 st_src1 st_tgt1 r_shared1 r_ctx1
               (INV: I (ths1, im_src1, im_tgt1, st_src1, st_tgt1, r_shared1))
               (VALID: URA.wf (r_shared1 ⋅ r_own ⋅ r_ctx1))
               im_tgt2
               (TGT: fair_update im_tgt1 im_tgt2 (sum_fmap_l (tids_fmap tid ths1))),
        exists o1,
            (<<GENO: _geno _ _ RR f_src true r_ctx1 (o1, trigger (Yield) >>= ktr_src) (ktr_tgt tt) (ths1, im_src1, im_tgt2, st_src1, st_tgt1, r_shared1)>>) /\
              (<<STUTTER: wf_stt.(lt) o1 o0>>))
    :
    __geno tid geno _geno RR f_src f_tgt r_ctx0 (o0, trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt) (ths0, im_src0, im_tgt0, st_src0, st_tgt0, r_shared0)
  | geno_yieldL
      f_src f_tgt r_ctx o0
      ths im_src0 im_tgt st_src st_tgt r_shared
      ktr_src itr_tgt
      (GENO: exists im_src1 o1,
          (<<FAIR: fair_update im_src0 im_src1 (sum_fmap_l (tids_fmap tid ths))>>) /\
            (<<GENO: _geno _ _ RR true f_tgt r_ctx (o1, ktr_src tt) itr_tgt (ths, im_src1, im_tgt, st_src, st_tgt, r_shared)>>))
    :
    __geno tid geno _geno RR f_src f_tgt r_ctx (o0, trigger (Yield) >>= ktr_src) itr_tgt (ths, im_src0, im_tgt, st_src, st_tgt, r_shared)

  | geno_progress
      r_ctx o
      ths im_src im_tgt st_src st_tgt r_shared
      itr_src itr_tgt
      (GENO: ModSimNoSync.lsim I tid RR false false r_ctx itr_src itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    __geno tid geno _geno RR true true r_ctx (o, itr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  .

  Definition lsim (tid: thread_id)
             R_src R_tgt (RR: R_src -> R_tgt -> URA.car -> shared_rel):
    bool -> bool -> URA.car -> (wf_stt.(T) * itree srcE R_src) -> itree tgtE R_tgt -> shared_rel :=
    paco9 (fun r => pind9 (__lsim tid r) top9) bot9 R_src R_tgt RR.

  Lemma __lsim_mon tid:
    forall r r' (LE: r <9= r'), (__lsim tid r) <10= (__lsim tid r').
  Proof.
    ii. inv PR; try (econs; eauto; fail).
    eapply lsim_yieldR; eauto. i. hexploit LSIM; eauto. i. des. esplits; eauto.
  Qed.

  Lemma _lsim_mon tid: forall r, monotone9 (__lsim tid r).
  Proof.
    ii. inv IN; try (econs; eauto; fail).
    { des. econs; eauto. }
    { des. econs; eauto. }
    { econs. i. eapply LE. eapply LSIM. eauto. }
    (* { econs; eauto. i. specialize (LSIM _ _ _ _ _ _ _ INV0 VALID0 _ TGT). des. esplits; eauto. } *)
    { des. econs; esplits; eauto. }
  Qed.

  Lemma lsim_mon tid: forall q, monotone9 (fun r => pind9 (__lsim tid r) q).
  Proof.
    ii. eapply pind9_mon_gen; eauto.
    ii. eapply __lsim_mon; eauto.
  Qed.

  Variant lsim_resetC
          (r: forall R_src R_tgt (RR: R_src -> R_tgt -> URA.car -> shared_rel), bool -> bool -> URA.car -> (wf_stt.(T) * itree srcE R_src) -> itree tgtE R_tgt -> shared_rel)
          R_src R_tgt (RR: R_src -> R_tgt -> URA.car -> shared_rel)
    :
    bool -> bool -> URA.car -> (wf_stt.(T) * itree srcE R_src) -> itree tgtE R_tgt -> shared_rel :=
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

    { eapply pind9_fold. eapply lsim_observe. i. eapply rclo9_base. auto. }

    { eapply pind9_fold. eapply lsim_yieldR; eauto. i.
      hexploit LSIM0; eauto. clear LSIM0. intros LSIM0. des. esplits; eauto.
      eapply rclo9_base. auto.
    }

    { des. eapply pind9_fold. eapply lsim_yieldL. esplits; eauto. split; ss.
      destruct LSIM as [LSIM IND]. hexploit IH; eauto.
    }

    { hexploit H; ss; i. hexploit H0; ss; i. clarify.
      eapply pind9_fold. eapply lsim_progress. eapply rclo9_base; auto. }
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

    { pfold. eapply pind9_fold. eapply lsim_observe. i. eapply upaco9_mon_bot; eauto. }

    { pfold. eapply pind9_fold. eapply lsim_yieldR; eauto. i.
      hexploit LSIM0; eauto. clear LSIM0. intros LSIM0. des. esplits; eauto.
      eapply upaco9_mon_bot; eauto.
    }

    { des. pfold. eapply pind9_fold. eapply lsim_yieldL. esplits; eauto. split; ss.
      destruct LSIM as [LSIM IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pclearbot. eapply paco9_mon_bot. eapply lsim_reset_prog. eauto. all: ss. }

  Qed.

  Definition local_RR {R0 R1} (RR: R0 -> R1 -> Prop) tid:
    R0 -> R1 -> URA.car -> shared_rel :=
    fun (r_src: R0) (r_tgt: R1) (r_ctx: URA.car) '(ths2, im_src1, im_tgt1, st_src1, st_tgt1, r_shared1) =>
      (exists ths3 r_own r_shared2,
          (<<THS: NatMap.remove tid ths2 = ths3>>) /\
            (<<VALID: URA.wf (r_shared2 ⋅ r_own ⋅ r_ctx)>>) /\
            (<<INV: I (ths3, im_src1, im_tgt1, st_src1, st_tgt1, r_shared2)>>) /\
            (<<RET: RR r_src r_tgt>>)).

  (* Definition local_RR {R0 R1} (RR: R0 -> R1 -> Prop) tid: *)
  (*   R0 -> R1 -> URA.car -> wf_stt.(T) -> shared_rel := *)
  (*   fun (r_src: R0) (r_tgt: R1) (r_ctx: URA.car) (o: wf_stt.(T)) '(ths2, im_src1, im_tgt1, st_src1, st_tgt1, r_shared1) => *)
  (*     (exists ths3 r_own o0 r_shared2, *)
  (*         (<<THS: NatMap.remove tid ths2 = ths3>>) /\ *)
  (*           (<<VALID: URA.wf (r_shared2 ⋅ r_own ⋅ r_ctx)>>) /\ *)
  (*           (<<INV: I (ths3, im_src1, im_tgt1, st_src1, st_tgt1, r_shared2)>>) /\ *)
  (*           (<<STT: wf_stt.(lt) o0 o>>) /\ *)
  (*           (<<RET: RR r_src r_tgt>>)). *)

  (* Definition embed_lrr {R0 R1} (LRR: R0 -> R1 -> URA.car -> shared_rel): *)
  (*   R0 -> R1 -> URA.car -> wf_stt.(T) -> shared_rel := *)
  (*   fun (r_src: R0) (r_tgt: R1) (r_ctx: URA.car) (o: wf_stt.(T)) shr => *)
  (*     (<<LSIM: LRR r_src r_tgt r_ctx shr>>) /\ (<<STT: exists o0, wf_stt.(lt) o0 o>>). *)

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
           (VALID: URA.wf (r_shared2 ⋅ r_own ⋅ r_ctx2))
           im_tgt2
           (TGT: fair_update im_tgt1 im_tgt2 (sum_fmap_l (tids_fmap tid ths))),
          exists o,
          exists im_src2, (<<SRC: fair_update im_src1 im_src2 (sum_fmap_l (tids_fmap tid ths))>>) /\
                       (<<LSIM: forall fs ft,
                           lsim
                             tid
                             (@local_RR R0 R1 RR tid)
                             fs ft
                             r_ctx2
                             (o, src) tgt
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

Section PROOF.

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

  Let shared :=
    (TIdSet.t *
       (@imap ident_src wf_src) *
       (@imap ident_tgt wf_tgt) *
       state_src *
       state_tgt *
       URA.car)%type.

  Let shared_rel: Type := shared -> Prop.

  Variable I: shared_rel.

  Lemma stutter_ord_weak
          wf_stt tid
          R0 R1 (LRR: R0 -> R1 -> URA.car -> shared_rel)
          ps pt r_ctx src tgt (shr: shared) o0 o1
          (LT: wf_stt.(lt) o0 o1)
          (LSIM: ModSimStutter.lsim wf_stt I tid LRR ps pt r_ctx (o0, src) tgt shr)
    :
    ModSimStutter.lsim wf_stt I tid LRR ps pt r_ctx (o1, src) tgt shr.
  Proof.
    revert_until tid. pcofix CIH; i.
    remember (o0, src) as osrc.
    move LSIM before CIH. revert_until LSIM.
    punfold LSIM.
    pattern R0, R1, LRR, ps, pt, r_ctx, osrc, tgt, shr.
    revert R0 R1 LRR ps pt r_ctx osrc tgt shr LSIM. apply pind9_acc.
    intros rr DEC IH. clear DEC. intros R0 R1 LRR ps pt r_ctx osrc tgt shr LSIM.
    i; clarify.
    eapply pind9_unfold in LSIM.
    2:{ eapply ModSimStutter._lsim_mon. }
    inv LSIM.

    { pfold. eapply pind9_fold. econs 1; eauto. }
    { pfold. eapply pind9_fold. econs 2; eauto.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND; eauto. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 3; eauto.
      des. exists x.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND; eauto. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 4; eauto.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND; eauto. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 5; eauto.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND; eauto. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 6; eauto.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND; eauto. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 7; eauto. }
    { pfold. eapply pind9_fold. econs 8; eauto.
      des. esplits; eauto.
      split; ss. destruct LSIM as [LSIM IND]. eapply IH in IND; eauto. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 9; eauto.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND; eauto. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 10; eauto.
      i. specialize (LSIM0 x).
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND; eauto. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 11; eauto.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND; eauto. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 12; eauto.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND; eauto. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 13; eauto.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND; eauto. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 14; eauto.
      i. specialize (LSIM0 _ FAIR).
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND; eauto. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 15; eauto.
      i. specialize (LSIM0 ret). pclearbot.
      right. eapply CIH; eauto.
    }

    { pfold. eapply pind9_fold. eapply ModSimStutter.lsim_yieldR; eauto.
      i. hexploit LSIM0; clear LSIM0; eauto; intro LSIM. des. esplits; eauto.
      pclearbot. right. eapply CIH; eauto.
    }

    { pfold. eapply pind9_fold. eapply ModSimStutter.lsim_yieldL; eauto.
      des. esplits; eauto. destruct LSIM as [LSIM IND].
      split; ss. eapply pind9_mon_gen. eapply LSIM.
      - i. eapply __lsim_mon. 2: eapply PR. i. eapply upaco9_mon_bot; eauto.
      - ss.
    }

    { pfold. eapply pind9_fold. eapply ModSimStutter.lsim_progress.
      pclearbot. right. eapply CIH; eauto.
    }

  Qed.


  Let A R0 R1 := (bool * bool * URA.car * (itree srcE R0) * (itree tgtE R1) * shared)%type.
  Let wf_stt {R0 R1} := (@ord_tree_WF (A R0 R1)).

  Lemma nosync_implies_stutter
        tid
        R0 R1 (LRR: R0 -> R1 -> URA.car -> shared_rel)
        ps pt r_ctx src tgt
        (shr: shared)
        (LSIM: ModSimNoSync.lsim I tid LRR ps pt r_ctx src tgt shr)
    :
    exists (o: (@wf_stt R0 R1).(T)),
      ModSimStutter.lsim wf_stt I tid LRR ps pt r_ctx (o, src) tgt shr.
  Proof.
    punfold LSIM.
    pattern R0, R1, LRR, ps, pt, r_ctx, src, tgt, shr.
    revert R0 R1 LRR ps pt r_ctx src tgt shr LSIM. apply pind9_acc.
    intros rr DEC IH. clear DEC. intros R0 R1 LRR ps pt r_ctx src tgt shr LSIM.
    eapply pind9_unfold in LSIM.
    2:{ eapply ModSimNoSync._lsim_mon. }
    inv LSIM.

    { remember (fun _: (A R0 R1) => @ord_tree_base (A R0 R1)) as ao. exists (ord_tree_cons ao).
      pfold. eapply pind9_fold. econs 1; eauto.
      instantiate (1:=ao (ps, pt, r_ctx, Ret r_src, Ret r_tgt, (ths, im_src, im_tgt, st_src, st_tgt, r_shared))).
      eapply ord_tree_lt_intro.
    }

    { destruct LSIM0 as [LSIM IND]. eapply IH in IND. des. exists o.
      pfold. eapply pind9_fold. econs 2; eauto.
      split; ss. punfold IND.
    }
    { des. destruct LSIM0 as [LSIM IND]. eapply IH in IND. des. exists o.
      pfold. eapply pind9_fold. econs 3; eauto. exists x.
      split; ss. punfold IND.
    }
    { destruct LSIM0 as [LSIM IND]. eapply IH in IND. des. exists o.
      pfold. eapply pind9_fold. econs 4; eauto.
      split; ss. punfold IND.
    }
    { destruct LSIM0 as [LSIM IND]. eapply IH in IND. des. exists o.
      pfold. eapply pind9_fold. econs 5; eauto.
      split; ss. punfold IND.
    }
    { destruct LSIM0 as [LSIM IND]. eapply IH in IND. des. exists o.
      pfold. eapply pind9_fold. econs 6; eauto.
      split; ss. punfold IND.
    }
    { exists (@ord_tree_base (A R0 R1)).
      pfold. eapply pind9_fold. econs 7; eauto.
    }
    { des. destruct LSIM as [LSIM IND]. eapply IH in IND. des. exists o.
      pfold. eapply pind9_fold. econs 8; eauto. esplits; eauto.
      split; ss. punfold IND.
    }

    { destruct LSIM0 as [LSIM IND]. eapply IH in IND. des. exists o.
      pfold. eapply pind9_fold. econs 9; eauto.
      split; ss. punfold IND.
    }

    { hexploit ord_tree_join.
      { instantiate (2:=A R0 R1).
        instantiate (2:= fun '(ps, pt, rs, src, tgt, shr) => @rr R0 R1 LRR ps pt rs src tgt shr).
        i. ss. des_ifs. eapply IH in SAT.
        instantiate (1:= fun '(ps, pt, rs, src, tgt, shr) o => lsim wf_stt I tid LRR ps pt rs (o, src) tgt shr).
        eauto.
      }
      intro JOIN. des. exists o1. pfold. eapply pind9_fold. econs 10. i. specialize (LSIM0 x).
      destruct LSIM0 as [LSIM IND].
      specialize (JOIN (ps, true, r_ctx, src, (ktr_tgt x), (ths, im_src, im_tgt, st_src, st_tgt, r_shared))). des_ifs.
      eapply JOIN in IND; clear JOIN. des.
      split; ss.
      eapply stutter_ord_weak in IND. punfold IND. auto.
    }

    { destruct LSIM0 as [LSIM IND]. eapply IH in IND. des. exists o.
      pfold. eapply pind9_fold. econs 11; eauto.
      split; ss. punfold IND.
    }
    { destruct LSIM0 as [LSIM IND]. eapply IH in IND. des. exists o.
      pfold. eapply pind9_fold. econs 12; eauto.
      split; ss. punfold IND.
    }
    { destruct LSIM0 as [LSIM IND]. eapply IH in IND. des. exists o.
      pfold. eapply pind9_fold. econs 13; eauto.
      split; ss. punfold IND.
    }

    { hexploit ord_tree_join.
      { instantiate (2:=A R0 R1).
        instantiate (2:= fun '(ps, pt, rs, src, tgt, shr) => @rr R0 R1 LRR ps pt rs src tgt shr).
        i. ss. des_ifs. eapply IH in SAT.
        instantiate (1:= fun '(ps, pt, rs, src, tgt, shr) o => lsim wf_stt I tid LRR ps pt rs (o, src) tgt shr).
        eauto.
      }
      intro JOIN. des. exists o1. pfold. eapply pind9_fold. econs 14. i. specialize (LSIM0 _ FAIR).
      destruct LSIM0 as [LSIM IND].
      specialize (JOIN (ps, true, r_ctx, src, (ktr_tgt ()), (ths, im_src, im_tgt1, st_src, st_tgt, r_shared))). des_ifs.
      eapply JOIN in IND; clear JOIN. des.
      split; ss.
      eapply stutter_ord_weak in IND. punfold IND. auto.
    }

    { hexploit ord_tree_join.
      { instantiate (2:=A R0 R1).
        instantiate (2:= fun '(ps, pt, rs, src, tgt, shr) => @rr R0 R1 LRR ps pt rs src tgt shr).
        i. ss. des_ifs. eapply IH in SAT.
        instantiate (1:= fun '(ps, pt, rs, src, tgt, shr) o => lsim wf_stt I tid LRR ps pt rs (o, src) tgt shr).
        eauto.
      }
      intro JOIN. des. exists o1. pfold. eapply pind9_fold. econs 15. i. specialize (LSIM0 ret).
      destruct LSIM0 as [LSIM IND].
      specialize (JOIN (true, true, r_ctx, ktr_src ret, ktr_tgt ret, (ths, im_src, im_tgt, st_src, st_tgt, r_shared))). des_ifs.
      eapply JOIN in IND; clear JOIN. des.
      eapply stutter_ord_weak in IND. punfold IND. auto.
    }

    { hexploit ord_tree_join.
      { instantiate (2:=A R0 R1).
        instantiate (2:= fun '(ps, pt, rs, src, tgt, shr) => @rr R0 R1 LRR ps pt rs src tgt shr).
        i. ss. des_ifs. eapply IH in SAT.
        instantiate (1:= fun '(ps, pt, rs, src, tgt, shr) o => lsim wf_stt I tid LRR ps pt rs (o, src) tgt shr).
        eauto.
      }
      intro JOIN. des. exists o1. pfold. eapply pind9_fold. econs 16; eauto. i.
      specialize (LSIM0 _ _ _ _ _ _ _ INV0 VALID0 _ TGT).
      destruct LSIM0 as [LSIM IND].
      specialize (JOIN (ps, true, r_ctx1, (x <- trigger Yield;; ktr_src x), ktr_tgt (), (ths1, im_src1, im_tgt2, st_src1, st_tgt1, r_shared1))). des_ifs.
      eapply JOIN in IND; clear JOIN. des. esplits; eauto.
      split; ss. punfold IND.
    }

    { des. destruct LSIM as [LSIM IND]. eapply IH in IND. des. exists o.
      pfold. eapply pind9_fold. econs 17; eauto. esplits; eauto.
      split; ss. punfold IND.
    }

    { exists (@ord_tree_base _). pfold. eapply pind9_fold. econs 18. pclearbot. auto. }

  Qed.

End PROOF.

