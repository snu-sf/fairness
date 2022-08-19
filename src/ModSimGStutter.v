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

  Variable wf_stt: WF.

  Definition shared :=
    (TIdSet.t *
       TIdSet.t *
       (@imap ident_src wf_src) *
       (@imap ident_tgt wf_tgt) *
       state_src *
       state_tgt *
       wf_stt.(T) *
       URA.car)%type.

  Let shared_rel: Type := shared -> Prop.

  Variable I: shared_rel.

  Variant __lsim R_src R_tgt (RR: R_src -> R_tgt -> URA.car -> shared_rel) (tid: thread_id)
            (lsim: bool -> bool -> URA.car -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel)
            (_lsim: bool -> bool -> URA.car -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel)
    :
    bool -> bool -> URA.car -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel :=
  | lsim_ret
      f_src f_tgt r_ctx
      ths tht im_src im_tgt st_src st_tgt o r_shared
      r_src r_tgt
      (LSIM: RR r_src r_tgt r_ctx (ths, tht, im_src, im_tgt, st_src, st_tgt, o, r_shared))
    :
    __lsim RR tid lsim _lsim f_src f_tgt r_ctx (Ret r_src) (Ret r_tgt) (ths, tht, im_src, im_tgt, st_src, st_tgt, o, r_shared)

  | lsim_tauL
      f_src f_tgt r_ctx
      ths tht im_src im_tgt st_src st_tgt o r_shared
      itr_src itr_tgt
      (LSIM: _lsim true f_tgt r_ctx itr_src itr_tgt (ths, tht, im_src, im_tgt, st_src, st_tgt, o, r_shared))
    :
    __lsim RR tid lsim _lsim f_src f_tgt r_ctx (Tau itr_src) itr_tgt (ths, tht, im_src, im_tgt, st_src, st_tgt, o, r_shared)
  | lsim_chooseL
      f_src f_tgt r_ctx
      ths tht im_src im_tgt st_src st_tgt o r_shared
      X ktr_src itr_tgt
      (LSIM: exists x, _lsim true f_tgt r_ctx (ktr_src x) itr_tgt (ths, tht, im_src, im_tgt, st_src, st_tgt, o, r_shared))
    :
    __lsim RR tid lsim _lsim f_src f_tgt r_ctx (trigger (Choose X) >>= ktr_src) itr_tgt (ths, tht, im_src, im_tgt, st_src, st_tgt, o, r_shared)
  | lsim_putL
      f_src f_tgt r_ctx
      ths tht im_src im_tgt st_src st_tgt o r_shared
      st ktr_src itr_tgt
      (LSIM: _lsim true f_tgt r_ctx (ktr_src tt) itr_tgt (ths, tht, im_src, im_tgt, st, st_tgt, o, r_shared))
    :
    __lsim RR tid lsim _lsim f_src f_tgt r_ctx (trigger (Put st) >>= ktr_src) itr_tgt (ths, tht, im_src, im_tgt, st_src, st_tgt, o, r_shared)
  | lsim_getL
      f_src f_tgt r_ctx
      ths tht im_src im_tgt st_src st_tgt o r_shared
      ktr_src itr_tgt
      (LSIM: _lsim true f_tgt r_ctx (ktr_src st_src) itr_tgt (ths, tht, im_src, im_tgt, st_src, st_tgt, o, r_shared))
    :
    __lsim RR tid lsim _lsim f_src f_tgt r_ctx (trigger (@Get _) >>= ktr_src) itr_tgt (ths, tht, im_src, im_tgt, st_src, st_tgt, o, r_shared)
  | lsim_tidL
      f_src f_tgt r_ctx
      ths tht im_src im_tgt st_src st_tgt o r_shared
      ktr_src itr_tgt
      (LSIM: _lsim true f_tgt r_ctx (ktr_src tid) itr_tgt (ths, tht, im_src, im_tgt, st_src, st_tgt, o, r_shared))
    :
    __lsim RR tid lsim _lsim f_src f_tgt r_ctx (trigger (GetTid) >>= ktr_src) itr_tgt (ths, tht, im_src, im_tgt, st_src, st_tgt, o, r_shared)
  | lsim_UB
      f_src f_tgt r_ctx
      ths tht im_src im_tgt st_src st_tgt o r_shared
      ktr_src itr_tgt
    :
    __lsim RR tid lsim _lsim f_src f_tgt r_ctx (trigger (Undefined) >>= ktr_src) itr_tgt (ths, tht, im_src, im_tgt, st_src, st_tgt, o, r_shared)
  | lsim_fairL
      f_src f_tgt r_ctx
      ths tht im_src0 im_tgt st_src st_tgt o r_shared
      f ktr_src itr_tgt
      (LSIM: exists im_src1,
          (<<FAIR: fair_update im_src0 im_src1 (sum_fmap_r f)>>) /\
            (<<LSIM: _lsim true f_tgt r_ctx (ktr_src tt) itr_tgt (ths, tht, im_src1, im_tgt, st_src, st_tgt, o, r_shared)>>))
    :
    __lsim RR tid lsim _lsim f_src f_tgt r_ctx (trigger (Fair f) >>= ktr_src) itr_tgt (ths, tht, im_src0, im_tgt, st_src, st_tgt, o, r_shared)

  | lsim_tauR
      f_src f_tgt r_ctx
      ths tht im_src im_tgt st_src st_tgt o r_shared
      itr_src itr_tgt
      (LSIM: _lsim f_src true r_ctx itr_src itr_tgt (ths, tht, im_src, im_tgt, st_src, st_tgt, o, r_shared))
    :
    __lsim RR tid lsim _lsim f_src f_tgt r_ctx itr_src (Tau itr_tgt) (ths, tht, im_src, im_tgt, st_src, st_tgt, o, r_shared)
  | lsim_chooseR
      f_src f_tgt r_ctx
      ths tht im_src im_tgt st_src st_tgt o r_shared
      X itr_src ktr_tgt
      (LSIM: forall x, _lsim f_src true r_ctx itr_src (ktr_tgt x) (ths, tht, im_src, im_tgt, st_src, st_tgt, o, r_shared))
    :
    __lsim RR tid lsim _lsim f_src f_tgt r_ctx itr_src (trigger (Choose X) >>= ktr_tgt) (ths, tht, im_src, im_tgt, st_src, st_tgt, o, r_shared)
  | lsim_putR
      f_src f_tgt r_ctx
      ths tht im_src im_tgt st_src st_tgt o r_shared
      st itr_src ktr_tgt
      (LSIM: _lsim f_src true r_ctx itr_src (ktr_tgt tt) (ths, tht, im_src, im_tgt, st_src, st, o, r_shared))
    :
    __lsim RR tid lsim _lsim f_src f_tgt r_ctx itr_src (trigger (Put st) >>= ktr_tgt) (ths, tht, im_src, im_tgt, st_src, st_tgt, o, r_shared)
  | lsim_getR
      f_src f_tgt r_ctx
      ths tht im_src im_tgt st_src st_tgt o r_shared
      itr_src ktr_tgt
      (LSIM: _lsim f_src true r_ctx itr_src (ktr_tgt st_tgt) (ths, tht, im_src, im_tgt, st_src, st_tgt, o, r_shared))
    :
    __lsim RR tid lsim _lsim f_src f_tgt r_ctx itr_src (trigger (@Get _) >>= ktr_tgt) (ths, tht, im_src, im_tgt, st_src, st_tgt, o, r_shared)
  | lsim_tidR
      f_src f_tgt r_ctx
      ths tht im_src im_tgt st_src st_tgt o r_shared
      itr_src ktr_tgt
      (LSIM: _lsim f_src true r_ctx itr_src (ktr_tgt tid) (ths, tht, im_src, im_tgt, st_src, st_tgt, o, r_shared))
    :
    __lsim RR tid lsim _lsim f_src f_tgt r_ctx itr_src (trigger (GetTid) >>= ktr_tgt) (ths, tht, im_src, im_tgt, st_src, st_tgt, o, r_shared)
  | lsim_fairR
      f_src f_tgt r_ctx
      ths tht im_src im_tgt0 st_src st_tgt o r_shared
      f itr_src ktr_tgt
      (LSIM: forall im_tgt1
                   (FAIR: fair_update im_tgt0 im_tgt1 (sum_fmap_r f)),
          (<<LSIM: _lsim f_src true r_ctx itr_src (ktr_tgt tt) (ths, tht, im_src, im_tgt1, st_src, st_tgt, o, r_shared)>>))
    :
    __lsim RR tid lsim _lsim f_src f_tgt r_ctx itr_src (trigger (Fair f) >>= ktr_tgt) (ths, tht, im_src, im_tgt0, st_src, st_tgt, o, r_shared)

  | lsim_observe
      f_src f_tgt r_ctx
      ths tht im_src im_tgt st_src st_tgt o r_shared
      fn args ktr_src ktr_tgt
      (LSIM: forall ret,
          lsim true true r_ctx (ktr_src ret) (ktr_tgt ret) (ths, tht, im_src, im_tgt, st_src, st_tgt, o, r_shared))
    :
    __lsim RR tid lsim _lsim f_src f_tgt r_ctx (trigger (Observe fn args) >>= ktr_src) (trigger (Observe fn args) >>= ktr_tgt) (ths, tht, im_src, im_tgt, st_src, st_tgt, o, r_shared)

  | lsim_sync
      f_src f_tgt r_ctx0
      ths0 tht0 im_src0 im_tgt0 st_src0 st_tgt0 o r_shared0
      r_own r_shared
      o0 ktr_src ktr_tgt
      (INV: I (ths0, tht0, im_src0, im_tgt0, st_src0, st_tgt0, o0, r_shared))
      (VALID: URA.wf (r_shared ⋅ r_own ⋅ r_ctx0))
      (STUTTER: wf_stt.(lt) o0 o)
      (LSIM: forall ths1 tht1 im_src1 im_tgt1 st_src1 st_tgt1 o1 r_shared1 r_ctx1
                    (INV: I (ths1, tht1, im_src1, im_tgt1, st_src1, st_tgt1, o1, r_shared1))
                    (VALID: URA.wf (r_shared1 ⋅ r_own ⋅ r_ctx1))
                    im_tgt2
                    (TGT: fair_update im_tgt1 im_tgt2 (sum_fmap_l (tids_fmap tid tht1))),
          lsim true true r_ctx1 (trigger (Yield) >>= ktr_src) (ktr_tgt tt) (ths1, tht1, im_src1, im_tgt2, st_src1, st_tgt1, o1, r_shared1))
    :
    __lsim RR tid lsim _lsim f_src f_tgt r_ctx0 (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt) (ths0, tht0, im_src0, im_tgt0, st_src0, st_tgt0, o, r_shared0)
  | lsim_yieldL
      f_src f_tgt r_ctx
      ths tht im_src0 im_tgt st_src st_tgt o0 r_shared
      ktr_src itr_tgt
      (LSIM: exists im_src1 o1,
          (<<FAIR: fair_update im_src0 im_src1 (sum_fmap_l (tids_fmap tid ths))>>) /\
            (<<LSIM: _lsim true f_tgt r_ctx (ktr_src tt) itr_tgt (ths, tht, im_src1, im_tgt, st_src, st_tgt, o1, r_shared)>>))
    :
    __lsim RR tid lsim _lsim f_src f_tgt r_ctx (trigger (Yield) >>= ktr_src) itr_tgt (ths, tht, im_src0, im_tgt, st_src, st_tgt, o0, r_shared)

  | lsim_progress
      r_ctx
      ths tht im_src im_tgt st_src st_tgt o r_shared
      itr_src itr_tgt
      (LSIM: lsim false false r_ctx itr_src itr_tgt (ths, tht, im_src, im_tgt, st_src, st_tgt, o, r_shared))
    :
    __lsim RR tid lsim _lsim true true r_ctx itr_src itr_tgt (ths, tht, im_src, im_tgt, st_src, st_tgt, o, r_shared)
  .

  Definition lsim R_src R_tgt (RR: R_src -> R_tgt -> URA.car -> shared_rel) (tid: thread_id):
    bool -> bool -> URA.car -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel :=
    paco6 (fun r => pind6 (__lsim RR tid r) top6) bot6.

  Lemma __lsim_mon R0 R1 (RR: R0 -> R1 -> URA.car -> shared_rel) tid:
    forall r r' (LE: r <6= r'), (__lsim RR tid r) <7= (__lsim RR tid r').
  Proof.
    ii. inv PR; econs; eauto.
  Qed.

  Lemma _lsim_mon R0 R1 (RR: R0 -> R1 -> URA.car -> shared_rel) tid: forall r, monotone6 (__lsim RR tid r).
  Proof.
    ii. inv IN; econs; eauto.
    { des. eauto. }
    { des. eauto. }
    { i. eapply LE. eapply LSIM. eauto. }
    { des. esplits; eauto. }
  Qed.

  Lemma lsim_mon R0 R1 (RR: R0 -> R1 -> URA.car -> shared_rel) tid: forall q, monotone6 (fun r => pind6 (__lsim RR tid r) q).
  Proof.
    ii. eapply pind6_mon_gen; eauto.
    ii. eapply __lsim_mon; eauto.
  Qed.


  Lemma lsim_reset_prog
        R0 R1 (RR: R0 -> R1 -> URA.car -> shared_rel) tid
        src tgt shr
        ps0 pt0 ps1 pt1
        r_ctx
        (LSIM: lsim RR tid ps1 pt1 r_ctx src tgt shr)
        (SRC: ps1 = true -> ps0 = true)
        (TGT: pt1 = true -> pt0 = true)
    :
    lsim RR tid ps0 pt0 r_ctx src tgt shr.
  Proof.
    revert_until tid. pcofix CIH. i.
    move LSIM before CIH. revert_until LSIM. punfold LSIM.
    2:{ eapply lsim_mon. }
    eapply pind6_acc in LSIM.

    { instantiate (1:= (fun ps1 pt1 r_ctx src tgt shr =>
                          forall ps0 pt0 : bool,
                            (ps1 = true -> ps0 = true) ->
                            (pt1 = true -> pt0 = true) ->
                            paco6
                              (fun
                                  r0 =>
                                  pind6 (__lsim RR tid r0) top6) r ps0 pt0 r_ctx src tgt shr)) in LSIM; auto. }

    ss. clear ps1 pt1 r_ctx src tgt shr LSIM.
    intros rr DEC IH ps1 pt1 r_ctx src tgt shr LSIM. clear DEC.
    intros ps0 pt0 SRC TGT.
    eapply pind6_unfold in LSIM.
    2:{ eapply _lsim_mon. }
    inv LSIM.

    { pfold. eapply pind6_fold. econs; eauto. }

    { destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      pfold. eapply pind6_fold. eapply lsim_tauL. split; ss.
      hexploit IH. eauto. all: eauto. i. punfold H. eapply lsim_mon.
    }

    { des. pfold. eapply pind6_fold. eapply lsim_chooseL. esplits; eauto. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind6_fold. eapply lsim_putL. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind6_fold. eapply lsim_getL. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind6_fold. eapply lsim_tidL. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind6_fold. eapply lsim_UB. }

    { des. pfold. eapply pind6_fold. eapply lsim_fairL. esplits; eauto. split; ss.
      destruct LSIM as [LSIM IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      pfold. eapply pind6_fold. eapply lsim_tauR. split; ss.
      hexploit IH. eauto. all: eauto. i. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind6_fold. eapply lsim_chooseR. i. split; ss. specialize (LSIM0 x).
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind6_fold. eapply lsim_putR. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind6_fold. eapply lsim_getR. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind6_fold. eapply lsim_tidR. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind6_fold. eapply lsim_fairR. i. split; ss. specialize (LSIM0 _ FAIR).
      des. destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind6_fold. eapply lsim_observe. i. eapply upaco6_mon_bot; eauto. }

    { pfold. eapply pind6_fold. eapply lsim_sync; eauto. i. eapply upaco6_mon_bot; eauto. }

    { des. pfold. eapply pind6_fold. eapply lsim_yieldL. esplits; eauto. split; ss.
      destruct LSIM as [LSIM IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pclearbot. hexploit SRC; ss; i. hexploit TGT; ss; i. clarify.
      pfold. eapply pind6_fold. eapply lsim_progress. right. eapply CIH. eauto. all: ss. }

  Qed.

  Lemma lsim_set_prog
        R0 R1 (RR: R0 -> R1 -> URA.car -> shared_rel) tid
        src tgt shr
        r_ctx
        (LSIM: lsim RR tid true true r_ctx src tgt shr)
    :
    forall ps pt, lsim RR tid ps pt r_ctx src tgt shr.
  Proof.
    i. revert_until tid. pcofix CIH. i.
    remember true as ps0 in LSIM at 1. remember true as pt0 in LSIM at 1.
    move LSIM before CIH. revert_until LSIM. punfold LSIM.
    2:{ eapply lsim_mon. }
    eapply pind6_acc in LSIM.

    { instantiate (1:= (fun ps0 pt0 r_ctx src tgt shr =>
                          ps0 = true ->
                          pt0 = true ->
                          forall ps pt : bool,
                            paco6
                              (fun
                                  r0 =>
                                  pind6 (__lsim RR tid r0) top6) r ps pt r_ctx src tgt shr)) in LSIM; auto. }

    ss. clear ps0 pt0 r_ctx src tgt shr LSIM.
    intros rr DEC IH gps gpt r_ctx src tgt shr LSIM. clear DEC.
    intros Egps Egpt ps pt.
    eapply pind6_unfold in LSIM.
    2:{ eapply _lsim_mon. }
    inv LSIM.

    { pfold. eapply pind6_fold. econs; eauto. }

    { destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      pfold. eapply pind6_fold. eapply lsim_tauL. split; ss.
      hexploit IH. eauto. all: eauto. i. punfold H. eapply lsim_mon.
    }

    { des. pfold. eapply pind6_fold. eapply lsim_chooseL. esplits; eauto. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind6_fold. eapply lsim_putL. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind6_fold. eapply lsim_getL. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind6_fold. eapply lsim_tidL. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind6_fold. eapply lsim_UB. }

    { des. pfold. eapply pind6_fold. eapply lsim_fairL. esplits; eauto. split; ss.
      destruct LSIM as [LSIM IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      pfold. eapply pind6_fold. eapply lsim_tauR. split; ss.
      hexploit IH. eauto. all: eauto. i. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind6_fold. eapply lsim_chooseR. i. split; ss. specialize (LSIM0 x).
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind6_fold. eapply lsim_putR. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind6_fold. eapply lsim_getR. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind6_fold. eapply lsim_tidR. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind6_fold. eapply lsim_fairR. i. split; ss. specialize (LSIM0 _ FAIR).
      des. destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind6_fold. eapply lsim_observe. i. eapply upaco6_mon_bot; eauto. }

    { pfold. eapply pind6_fold. eapply lsim_sync; eauto. i. eapply upaco6_mon_bot; eauto. }

    { des. pfold. eapply pind6_fold. eapply lsim_yieldL. esplits; eauto. split; ss.
      destruct LSIM as [LSIM IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pclearbot. eapply paco6_mon_bot. eapply lsim_reset_prog. eauto. all: ss. }

  Qed.

  Definition local_RR {R0 R1} (RR: R0 -> R1 -> Prop) tid:
    R0 -> R1 -> URA.car -> shared_rel :=
    fun (r_src: R0) (r_tgt: R1) (r_ctx: URA.car) '(ths2, tht2, im_src1, im_tgt1, st_src1, st_tgt1, o1, r_shared1) =>
      (exists ths3 tht3 o2 r_own r_shared2,
          (<<THSR: NatMap.remove tid ths2 = ths3>>) /\
            (<<THTR: NatMap.remove tid tht2 = tht3>>) /\
            (<<VALID: URA.wf (r_shared2 ⋅ r_own ⋅ r_ctx)>>) /\
            (<<STUTTER: wf_stt.(lt) o2 o1>>) /\
            (<<INV: I (ths3, tht3, im_src1, im_tgt1, st_src1, st_tgt1, o2, r_shared2)>>) /\
            (<<RET: RR r_src r_tgt>>)).

  Definition local_sim {R0 R1} (RR: R0 -> R1 -> Prop) src tgt :=
    forall ths0 tht0 im_src0 im_tgt0 st_src0 st_tgt0 o0 r_shared0 r_ctx0
      (INV: I (ths0, tht0, im_src0, im_tgt0, st_src0, st_tgt0, o0, r_shared0))
      tid ths1 tht1
      (THS: TIdSet.add_new tid ths0 ths1)
      (THT: TIdSet.add_new tid tht0 tht1)
      (VALID: URA.wf (r_shared0 ⋅ r_ctx0)),
    exists r_shared1 r_own o1, (<<INV: I (ths1, tht1, im_src0, im_tgt0, st_src0, st_tgt0, o1, r_shared1)>>) /\
               (<<VALID: URA.wf (r_shared1 ⋅ r_own ⋅ r_ctx0)>>) /\
               (forall ths tht im_src1 im_tgt1 st_src st_tgt o r_shared2 r_ctx2
                  (INV: I (ths, tht, im_src1, im_tgt1, st_src, st_tgt, o, r_shared2))
                  (VALID: URA.wf (r_shared2 ⋅ r_own ⋅ r_ctx2)),
                 forall im_tgt2 (TGT: fair_update im_tgt1 im_tgt2 (sum_fmap_l (tids_fmap tid tht))),
                 exists im_src2,
                   (<<SRC: fair_update im_src1 im_src2 (sum_fmap_l (tids_fmap tid ths))>>) /\
                     (<<LSIM: forall fs ft,
                         lsim
                           (@local_RR R0 R1 RR tid)
                           tid
                           fs ft
                           r_ctx2
                           src tgt
                           (ths, tht, im_src2, im_tgt2, st_src, st_tgt, o, r_shared2)
                           >>)).

  Definition shared_rel_wf (r: shared_rel): Prop :=
    forall ths tht im_src0 im_tgt0 st_src st_tgt o r_shared0 r_ctx
           (INV: r (ths, tht, im_src0, im_tgt0, st_src, st_tgt, o, r_shared0))
           (VALID: URA.wf (r_shared0 ⋅ r_ctx)),
    forall im_tgt1
           (TGT: fair_update im_tgt0 im_tgt1 (sum_fmap_l (tids_fmap_all ths))),
    exists im_src1 r_shared1,
      (<<SRC: fair_update im_src0 im_src1 (sum_fmap_l (tids_fmap_all tht))>>) /\
        (<<INV: r (ths, tht, im_src1, im_tgt1, st_src, st_tgt, o, r_shared1)>>) /\
        (<<VALID: URA.wf (r_shared1 ⋅ r_ctx)>>).

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
          wf_stt : WF;

          world: URA.t;

          I: (@shared world md_src.(Mod.state) md_tgt.(Mod.state) md_src.(Mod.ident) md_tgt.(Mod.ident) wf_src wf_tgt wf_stt) -> Prop;
          init: forall im_tgt, exists im_src o r_shared,
            (I (NatSet.empty, NatSet.empty, im_src, im_tgt, md_src.(Mod.st_init), md_tgt.(Mod.st_init), o, r_shared)) /\
              (URA.wf r_shared);

          funs: forall fn args, match md_src.(Mod.funs) fn, md_tgt.(Mod.funs) fn with
                           | None, _ => True
                           | _, None => False
                           | Some ktr_src, Some ktr_tgt => local_sim I (@eq Val) (ktr_src args) (ktr_tgt args)
                           end;
        }.

  End MODSIM.
End ModSim.