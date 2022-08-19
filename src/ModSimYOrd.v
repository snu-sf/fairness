From sflib Require Import sflib.
From Paco Require Import paco.
Require Export Coq.Strings.String.
Require Import Coq.Classes.RelationClasses.

From Fairness Require Export ITreeLib FairBeh Mod.
From Fairness Require Import pind PCM.

Set Implicit Arguments.



Section PRIMIVIESIM.
  Context `{M: URA.t}.

  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable ident_src: ID.
  Variable _ident_tgt: ID.
  Definition ident_tgt := sum_tid _ident_tgt.

  Variable wf_src: WF.
  Variable wf_tgt: WF.

  Let srcE := ((@eventE ident_src +' cE) +' sE state_src).
  Let tgtE := ((@eventE _ident_tgt +' cE) +' sE state_tgt).

  Definition shared :=
    (TIdSet.t *
       (@imap ident_src wf_src) *
       (@imap ident_tgt wf_tgt) *
       state_src *
       state_tgt)%type.

  Let shared_rel: Type := shared -> Prop.

  Variable I: shared -> URA.car -> Prop.

  Variable wf_stt: Type -> Type -> WF.

  Variant __lsim
          (tid: thread_id)
          (lsim: forall R0 R1 (RR: R0 -> R1 -> URA.car -> shared_rel), bool -> bool -> URA.car -> ((wf_stt R0 R1).(T) * itree srcE R0) -> ((wf_stt R0 R1).(T) * itree tgtE R1) -> shared_rel)
          (_lsim: forall R0 R1 (RR: R0 -> R1 -> URA.car -> shared_rel),bool -> bool -> URA.car -> ((wf_stt R0 R1).(T) * itree srcE R0) -> ((wf_stt R0 R1).(T) * itree tgtE R1) -> shared_rel)
          R0 R1 (RR: R0 -> R1 -> URA.car -> shared_rel)
    :
    bool -> bool -> URA.car -> ((wf_stt R0 R1).(T) * itree srcE R0) -> ((wf_stt R0 R1).(T) * itree tgtE R1) -> shared_rel :=
  | lsim_ret
      f_src f_tgt r_ctx os ot
      ths im_src im_tgt st_src st_tgt
      r_src r_tgt
      (LSIM: RR r_src r_tgt r_ctx (ths, im_src, im_tgt, st_src, st_tgt))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx (os, Ret r_src) (ot, Ret r_tgt) (ths, im_src, im_tgt, st_src, st_tgt)

  | lsim_tauL
      f_src f_tgt r_ctx os ot
      ths im_src im_tgt st_src st_tgt
      itr_src itr_tgt
      (LSIM: _lsim _ _ RR true f_tgt r_ctx (os, itr_src) (ot, itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx (os, Tau itr_src) (ot, itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)
  | lsim_chooseL
      f_src f_tgt r_ctx os ot
      ths im_src im_tgt st_src st_tgt
      X ktr_src itr_tgt
      (LSIM: exists x, _lsim _ _ RR true f_tgt r_ctx (os, ktr_src x) (ot, itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx (os, trigger (Choose X) >>= ktr_src) (ot, itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)
  | lsim_putL
      f_src f_tgt r_ctx os ot
      ths im_src im_tgt st_src st_tgt
      st ktr_src itr_tgt
      (LSIM: _lsim _ _ RR true f_tgt r_ctx (os, ktr_src tt) (ot, itr_tgt) (ths, im_src, im_tgt, st, st_tgt))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx (os, trigger (Put st) >>= ktr_src) (ot, itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)
  | lsim_getL
      f_src f_tgt r_ctx os ot
      ths im_src im_tgt st_src st_tgt
      ktr_src itr_tgt
      (LSIM: _lsim _ _ RR true f_tgt r_ctx (os, ktr_src st_src) (ot, itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx (os, trigger (@Get _) >>= ktr_src) (ot, itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)
  | lsim_tidL
      f_src f_tgt r_ctx os ot
      ths im_src im_tgt st_src st_tgt
      ktr_src itr_tgt
      (LSIM: _lsim _ _ RR true f_tgt r_ctx (os, ktr_src tid) (ot, itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx (os, trigger (GetTid) >>= ktr_src) (ot, itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)
  | lsim_UB
      f_src f_tgt r_ctx os ot
      ths im_src im_tgt st_src st_tgt
      ktr_src itr_tgt
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx (os, trigger (Undefined) >>= ktr_src) (ot, itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)
  | lsim_fairL
      f_src f_tgt r_ctx os ot
      ths im_src0 im_tgt st_src st_tgt
      f ktr_src itr_tgt
      (LSIM: exists im_src1,
          (<<FAIR: fair_update im_src0 im_src1 f>>) /\
            (<<LSIM: _lsim _ _ RR true f_tgt r_ctx (os, ktr_src tt) (ot, itr_tgt) (ths, im_src1, im_tgt, st_src, st_tgt)>>))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx (os, trigger (Fair f) >>= ktr_src) (ot, itr_tgt) (ths, im_src0, im_tgt, st_src, st_tgt)

  | lsim_tauR
      f_src f_tgt r_ctx os ot
      ths im_src im_tgt st_src st_tgt
      itr_src itr_tgt
      (LSIM: _lsim _ _ RR f_src true r_ctx (os, itr_src) (ot, itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx (os, itr_src) (ot, Tau itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)
  | lsim_chooseR
      f_src f_tgt r_ctx os ot
      ths im_src im_tgt st_src st_tgt
      X itr_src ktr_tgt
      (LSIM: forall x, _lsim _ _ RR f_src true r_ctx (os, itr_src) (ot, ktr_tgt x) (ths, im_src, im_tgt, st_src, st_tgt))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx (os, itr_src) (ot, trigger (Choose X) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)
  | lsim_putR
      f_src f_tgt r_ctx os ot
      ths im_src im_tgt st_src st_tgt
      st itr_src ktr_tgt
      (LSIM: _lsim _ _ RR f_src true r_ctx (os, itr_src) (ot, ktr_tgt tt) (ths, im_src, im_tgt, st_src, st))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx (os, itr_src) (ot, trigger (Put st) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)
  | lsim_getR
      f_src f_tgt r_ctx os ot
      ths im_src im_tgt st_src st_tgt
      itr_src ktr_tgt
      (LSIM: _lsim _ _ RR f_src true r_ctx (os, itr_src) (ot, ktr_tgt st_tgt) (ths, im_src, im_tgt, st_src, st_tgt))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx (os, itr_src) (ot, trigger (@Get _) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)
  | lsim_tidR
      f_src f_tgt r_ctx os ot
      ths im_src im_tgt st_src st_tgt
      itr_src ktr_tgt
      (LSIM: _lsim _ _ RR f_src true r_ctx (os, itr_src) (ot, ktr_tgt tid) (ths, im_src, im_tgt, st_src, st_tgt))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx (os, itr_src) (ot, trigger (GetTid) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)
  | lsim_fairR
      f_src f_tgt r_ctx os ot
      ths im_src im_tgt0 st_src st_tgt
      f itr_src ktr_tgt
      (LSIM: forall im_tgt1 (FAIR: fair_update im_tgt0 im_tgt1 (sum_fmap_r f)),
          (<<LSIM: _lsim _ _ RR f_src true r_ctx (os, itr_src) (ot, ktr_tgt tt) (ths, im_src, im_tgt1, st_src, st_tgt)>>))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx (os, itr_src) (ot, trigger (Fair f) >>= ktr_tgt) (ths, im_src, im_tgt0, st_src, st_tgt)

  | lsim_observe
      f_src f_tgt r_ctx os ot
      ths im_src im_tgt st_src st_tgt
      fn args ktr_src ktr_tgt
      (LSIM: forall ret,
          lsim _ _ RR true true r_ctx (os, ktr_src ret) (ot, ktr_tgt ret) (ths, im_src, im_tgt, st_src, st_tgt))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx (os, trigger (Observe fn args) >>= ktr_src) (ot, trigger (Observe fn args) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)

  | lsim_yieldL
      f_src f_tgt r_ctx os ot
      ths im_src im_tgt st_src st_tgt
      ktr_src itr_tgt
      (LSIM: exists os1 ot1,
          (<<LSIM: _lsim _ _ RR true f_tgt r_ctx (os1, ktr_src tt) (ot1, trigger (Yield) >>= itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)>>) /\
            (<<LT: (wf_stt R0 R1).(lt) os1 os>>))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx (os, trigger (Yield) >>= ktr_src) (ot, trigger (Yield) >>= itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)
  | lsim_yieldR
      f_src f_tgt r_ctx0 os ot
      ths0 im_src0 im_tgt0 st_src0 st_tgt0
      r_own r_shared
      ktr_src ktr_tgt
      (INV: I (ths0, im_src0, im_tgt0, st_src0, st_tgt0) r_shared)
      (VALID: URA.wf (r_shared ⋅ r_own ⋅ r_ctx0))
      (LSIM: forall ths1 im_src1 im_tgt1 st_src1 st_tgt1 r_shared1 r_ctx1
               (INV: I (ths1, im_src1, im_tgt1, st_src1, st_tgt1) r_shared1)
               (VALID: URA.wf (r_shared1 ⋅ r_own ⋅ r_ctx1))
               im_tgt2
               (TGT: fair_update im_tgt1 im_tgt2 (sum_fmap_l (tids_fmap tid ths1))),
        exists os1 ot1,
          (<<LSIM: _lsim _ _ RR f_src true r_ctx1 (os1, trigger (Yield) >>= ktr_src) (ot1, ktr_tgt tt) (ths1, im_src1, im_tgt2, st_src1, st_tgt1)>>) /\
            (<<LT: (wf_stt R0 R1).(lt) ot1 ot>>))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx0 (os, trigger (Yield) >>= ktr_src) (ot, trigger (Yield) >>= ktr_tgt) (ths0, im_src0, im_tgt0, st_src0, st_tgt0)
  | lsim_sync
      f_src f_tgt r_ctx0 os ot
      ths0 im_src0 im_tgt0 st_src0 st_tgt0
      r_own r_shared
      ktr_src ktr_tgt
      (INV: I (ths0, im_src0, im_tgt0, st_src0, st_tgt0) r_shared)
      (VALID: URA.wf (r_shared ⋅ r_own ⋅ r_ctx0))
      (LSIM: forall ths1 im_src1 im_tgt1 st_src1 st_tgt1 r_shared1 r_ctx1
               (INV: I (ths1, im_src1, im_tgt1, st_src1, st_tgt1) r_shared1)
               (VALID: URA.wf (r_shared1 ⋅ r_own ⋅ r_ctx1))
               im_tgt2
               (TGT: fair_update im_tgt1 im_tgt2 (sum_fmap_l (tids_fmap tid ths1))),
        exists os1 ot1,
          (<<LSIM: lsim _ _ RR true true r_ctx1 (os1, ktr_src tt) (ot1, ktr_tgt tt) (ths1, im_src1, im_tgt2, st_src1, st_tgt1)>>))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx0 (os, trigger (Yield) >>= ktr_src) (ot, trigger (Yield) >>= ktr_tgt) (ths0, im_src0, im_tgt0, st_src0, st_tgt0)

  | lsim_progress
      r_ctx os ot
      ths im_src im_tgt st_src st_tgt
      itr_src itr_tgt
      (LSIM: lsim _ _ RR false false r_ctx (os, itr_src) (ot, itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt))
    :
    __lsim tid lsim _lsim RR true true r_ctx (os, itr_src) (ot, itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)
  .

  Definition lsim (tid: thread_id)
             R0 R1 (RR: R0 -> R1 -> URA.car -> shared_rel):
    bool -> bool -> URA.car -> ((wf_stt R0 R1).(T) * itree srcE R0) -> ((wf_stt R0 R1).(T) * itree tgtE R1) -> shared_rel :=
    paco9 (fun r => pind9 (__lsim tid r) top9) bot9 R0 R1 RR.

  Lemma __lsim_mon tid:
    forall r r' (LE: r <9= r'), (__lsim tid r) <10= (__lsim tid r').
  Proof.
    ii. inv PR; try (econs; eauto; fail).
    eapply lsim_sync; eauto. i. hexploit LSIM. eapply INV0. eapply VALID0. all: eauto.
    i. des. esplits; eauto.
  Qed.

  Lemma _lsim_mon tid: forall r, monotone9 (__lsim tid r).
  Proof.
    ii. inv IN; try (econs; eauto; fail).
    { des. econs; eauto. }
    { des. econs; eauto. }
    { econs. i. eapply LE. eapply LSIM. eauto. }
    { des. econs; eauto. esplits; eauto. }
    { eapply lsim_yieldR; eauto. i. hexploit LSIM; eauto. i. des. esplits; eauto. }
  Qed.

  Lemma lsim_mon tid: forall q, monotone9 (fun r => pind9 (__lsim tid r) q).
  Proof.
    ii. eapply pind9_mon_gen; eauto.
    ii. eapply __lsim_mon; eauto.
  Qed.


  Variant lsim_indC tid
          (r: forall R0 R1 (RR: R0 -> R1 -> URA.car -> shared_rel), bool -> bool -> URA.car -> ((wf_stt R0 R1).(T) * itree srcE R0) -> ((wf_stt R0 R1).(T) * itree tgtE R1) -> shared_rel)
          R0 R1 (RR: R0 -> R1 -> URA.car -> shared_rel)
    :
    bool -> bool -> URA.car -> ((wf_stt R0 R1).(T) * itree srcE R0) -> ((wf_stt R0 R1).(T) * itree tgtE R1) -> shared_rel :=
    | lsim_indC_ret
        f_src f_tgt r_ctx os ot
        ths im_src im_tgt st_src st_tgt
        r_src r_tgt
        (LSIM: RR r_src r_tgt r_ctx (ths, im_src, im_tgt, st_src, st_tgt))
      :
      lsim_indC tid r RR f_src f_tgt r_ctx (os, Ret r_src) (ot, Ret r_tgt) (ths, im_src, im_tgt, st_src, st_tgt)

    | lsim_indC_tauL
        f_src f_tgt r_ctx os ot
        ths im_src im_tgt st_src st_tgt
        itr_src itr_tgt
        (LSIM: r _ _ RR true f_tgt r_ctx (os, itr_src) (ot, itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt))
      :
      lsim_indC tid r RR f_src f_tgt r_ctx (os, Tau itr_src) (ot, itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)
    | lsim_indC_chooseL
        f_src f_tgt r_ctx os ot
        ths im_src im_tgt st_src st_tgt
        X ktr_src itr_tgt
        (LSIM: exists x, r _ _ RR true f_tgt r_ctx (os, ktr_src x) (ot, itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt))
      :
      lsim_indC tid r RR f_src f_tgt r_ctx (os, trigger (Choose X) >>= ktr_src) (ot, itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)
    | lsim_indC_putL
        f_src f_tgt r_ctx os ot
        ths im_src im_tgt st_src st_tgt
        st ktr_src itr_tgt
        (LSIM: r _ _ RR true f_tgt r_ctx (os, ktr_src tt) (ot, itr_tgt) (ths, im_src, im_tgt, st, st_tgt))
      :
      lsim_indC tid r RR f_src f_tgt r_ctx (os, trigger (Put st) >>= ktr_src) (ot, itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)
    | lsim_indC_getL
        f_src f_tgt r_ctx os ot
        ths im_src im_tgt st_src st_tgt
        ktr_src itr_tgt
        (LSIM: r _ _ RR true f_tgt r_ctx (os, ktr_src st_src) (ot, itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt))
      :
      lsim_indC tid r RR f_src f_tgt r_ctx (os, trigger (@Get _) >>= ktr_src) (ot, itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)
    | lsim_indC_tidL
        f_src f_tgt r_ctx os ot
        ths im_src im_tgt st_src st_tgt
        ktr_src itr_tgt
        (LSIM: r _ _ RR true f_tgt r_ctx (os, ktr_src tid) (ot, itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt))
      :
      lsim_indC tid r RR f_src f_tgt r_ctx (os, trigger (GetTid) >>= ktr_src) (ot, itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)
    | lsim_indC_UB
        f_src f_tgt r_ctx os ot
        ths im_src im_tgt st_src st_tgt
        ktr_src itr_tgt
      :
      lsim_indC tid r RR f_src f_tgt r_ctx (os, trigger (Undefined) >>= ktr_src) (ot, itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)
    | lsim_indC_fairL
        f_src f_tgt r_ctx os ot
        ths im_src0 im_tgt st_src st_tgt
        f ktr_src itr_tgt
        (LSIM: exists im_src1,
            (<<FAIR: fair_update im_src0 im_src1 f>>) /\
              (<<LSIM: r _ _ RR true f_tgt r_ctx (os, ktr_src tt) (ot, itr_tgt) (ths, im_src1, im_tgt, st_src, st_tgt)>>))
      :
      lsim_indC tid r RR f_src f_tgt r_ctx (os, trigger (Fair f) >>= ktr_src) (ot, itr_tgt) (ths, im_src0, im_tgt, st_src, st_tgt)

    | lsim_indC_tauR
        f_src f_tgt r_ctx os ot
        ths im_src im_tgt st_src st_tgt
        itr_src itr_tgt
        (LSIM: r _ _ RR f_src true r_ctx (os, itr_src) (ot, itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt))
      :
      lsim_indC tid r RR f_src f_tgt r_ctx (os, itr_src) (ot, Tau itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)
    | lsim_indC_chooseR
        f_src f_tgt r_ctx os ot
        ths im_src im_tgt st_src st_tgt
        X itr_src ktr_tgt
        (LSIM: forall x, r _ _ RR f_src true r_ctx (os, itr_src) (ot, ktr_tgt x) (ths, im_src, im_tgt, st_src, st_tgt))
      :
      lsim_indC tid r RR f_src f_tgt r_ctx (os, itr_src) (ot, trigger (Choose X) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)
    | lsim_indC_putR
        f_src f_tgt r_ctx os ot
        ths im_src im_tgt st_src st_tgt
        st itr_src ktr_tgt
        (LSIM: r _ _ RR f_src true r_ctx (os, itr_src) (ot, ktr_tgt tt) (ths, im_src, im_tgt, st_src, st))
      :
      lsim_indC tid r RR f_src f_tgt r_ctx (os, itr_src) (ot, trigger (Put st) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)
    | lsim_indC_getR
        f_src f_tgt r_ctx os ot
        ths im_src im_tgt st_src st_tgt
        itr_src ktr_tgt
        (LSIM: r _ _ RR f_src true r_ctx (os, itr_src) (ot, ktr_tgt st_tgt) (ths, im_src, im_tgt, st_src, st_tgt))
      :
      lsim_indC tid r RR f_src f_tgt r_ctx (os, itr_src) (ot, trigger (@Get _) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)
    | lsim_indC_tidR
        f_src f_tgt r_ctx os ot
        ths im_src im_tgt st_src st_tgt
        itr_src ktr_tgt
        (LSIM: r _ _ RR f_src true r_ctx (os, itr_src) (ot, ktr_tgt tid) (ths, im_src, im_tgt, st_src, st_tgt))
      :
      lsim_indC tid r RR f_src f_tgt r_ctx (os, itr_src) (ot, trigger (GetTid) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)
    | lsim_indC_fairR
        f_src f_tgt r_ctx os ot
        ths im_src im_tgt0 st_src st_tgt
        f itr_src ktr_tgt
        (LSIM: forall im_tgt1 (FAIR: fair_update im_tgt0 im_tgt1 (sum_fmap_r f)),
            (<<LSIM: r _ _ RR f_src true r_ctx (os, itr_src) (ot, ktr_tgt tt) (ths, im_src, im_tgt1, st_src, st_tgt)>>))
      :
      lsim_indC tid r RR f_src f_tgt r_ctx (os, itr_src) (ot, trigger (Fair f) >>= ktr_tgt) (ths, im_src, im_tgt0, st_src, st_tgt)

    | lsim_indC_observe
        f_src f_tgt r_ctx os ot
        ths im_src im_tgt st_src st_tgt
        fn args ktr_src ktr_tgt
        (LSIM: forall ret,
            r _ _ RR true true r_ctx (os, ktr_src ret) (ot, ktr_tgt ret) (ths, im_src, im_tgt, st_src, st_tgt))
      :
      lsim_indC tid r RR f_src f_tgt r_ctx (os, trigger (Observe fn args) >>= ktr_src) (ot, trigger (Observe fn args) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)

   | lsim_indC_yieldL
      f_src f_tgt r_ctx os ot
      ths im_src im_tgt st_src st_tgt
      ktr_src itr_tgt
      (LSIM: exists os1 ot1,
          (<<LSIM: r _ _ RR true f_tgt r_ctx (os1, ktr_src tt) (ot1, trigger (Yield) >>= itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)>>) /\
            (<<LT: (wf_stt R0 R1).(lt) os1 os>>))
    :
    lsim_indC tid r RR f_src f_tgt r_ctx (os, trigger (Yield) >>= ktr_src) (ot, trigger (Yield) >>= itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)
  | lsim_indC_yieldR
      f_src f_tgt r_ctx0 os ot
      ths0 im_src0 im_tgt0 st_src0 st_tgt0
      r_own r_shared
      ktr_src ktr_tgt
      (INV: I (ths0, im_src0, im_tgt0, st_src0, st_tgt0) r_shared)
      (VALID: URA.wf (r_shared ⋅ r_own ⋅ r_ctx0))
      (LSIM: forall ths1 im_src1 im_tgt1 st_src1 st_tgt1 r_shared1 r_ctx1
               (INV: I (ths1, im_src1, im_tgt1, st_src1, st_tgt1) r_shared1)
               (VALID: URA.wf (r_shared1 ⋅ r_own ⋅ r_ctx1))
               im_tgt2
               (TGT: fair_update im_tgt1 im_tgt2 (sum_fmap_l (tids_fmap tid ths1))),
        exists os1 ot1,
          (<<LSIM: r _ _ RR f_src true r_ctx1 (os1, trigger (Yield) >>= ktr_src) (ot1, ktr_tgt tt) (ths1, im_src1, im_tgt2, st_src1, st_tgt1)>>) /\
            (<<LT: (wf_stt R0 R1).(lt) ot1 ot>>))
    :
    lsim_indC tid r RR f_src f_tgt r_ctx0 (os, trigger (Yield) >>= ktr_src) (ot, trigger (Yield) >>= ktr_tgt) (ths0, im_src0, im_tgt0, st_src0, st_tgt0)
  | lsim_indC_sync
      f_src f_tgt r_ctx0 os ot
      ths0 im_src0 im_tgt0 st_src0 st_tgt0
      r_own r_shared
      ktr_src ktr_tgt
      (INV: I (ths0, im_src0, im_tgt0, st_src0, st_tgt0) r_shared)
      (VALID: URA.wf (r_shared ⋅ r_own ⋅ r_ctx0))
      (LSIM: forall ths1 im_src1 im_tgt1 st_src1 st_tgt1 r_shared1 r_ctx1
               (INV: I (ths1, im_src1, im_tgt1, st_src1, st_tgt1) r_shared1)
               (VALID: URA.wf (r_shared1 ⋅ r_own ⋅ r_ctx1))
               im_tgt2
               (TGT: fair_update im_tgt1 im_tgt2 (sum_fmap_l (tids_fmap tid ths1))),
        exists os1 ot1,
          (<<LSIM: r _ _ RR true true r_ctx1 (os1, ktr_src tt) (ot1, ktr_tgt tt) (ths1, im_src1, im_tgt2, st_src1, st_tgt1)>>))
    :
    lsim_indC tid r RR f_src f_tgt r_ctx0 (os, trigger (Yield) >>= ktr_src) (ot, trigger (Yield) >>= ktr_tgt) (ths0, im_src0, im_tgt0, st_src0, st_tgt0)

    | lsim_indC_progress
        r_ctx os ot
        ths im_src im_tgt st_src st_tgt
        itr_src itr_tgt
        (LSIM: r _ _ RR false false r_ctx (os, itr_src) (ot, itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt))
      :
      lsim_indC tid r RR true true r_ctx (os, itr_src) (ot, itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)
  .

  Lemma lsim_indC_mon tid: monotone9 (lsim_indC tid).
  Proof.
    ii. inv IN; try (econs; eauto; fail).
    { des; econs; eauto. }
    { des; econs; eauto. }
    { econs. i. specialize (LSIM _ FAIR). eauto. }
    { des; econs; eauto. esplits; eauto. }
    { eapply lsim_indC_yieldR; eauto. i. hexploit LSIM; eauto. i; des. esplits; eauto. }
    { eapply lsim_indC_sync; eauto. i. hexploit LSIM; eauto. i; des. esplits; eauto. }
  Qed.

  Hint Resolve lsim_indC_mon: paco.

  Lemma lsim_indC_wrepectful tid: wrespectful9 (fun r => pind9 (__lsim tid r) top9) (lsim_indC tid).
  Proof.
    econs; eauto with paco.
    i. eapply pind9_fold. inv PR.
    { econs 1; eauto. }
    { econs 2; eauto. split; ss.
      eapply GF in LSIM. eapply pind9_mon_gen; ss. eauto.
      i. eapply __lsim_mon. 2: eauto. i. eapply rclo9_base; auto.
    }
    { des. econs 3; eauto. esplits; eauto. split; ss.
      eapply GF in LSIM. eapply pind9_mon_gen; ss. eauto.
      i. eapply __lsim_mon. 2: eauto. i. eapply rclo9_base; auto.
    }
    { econs 4; eauto. split; ss.
      eapply GF in LSIM. eapply pind9_mon_gen; ss. eauto.
      i. eapply __lsim_mon. 2: eauto. i. eapply rclo9_base; auto.
    }
    { econs 5; eauto. split; ss.
      eapply GF in LSIM. eapply pind9_mon_gen; ss. eauto.
      i. eapply __lsim_mon. 2: eauto. i. eapply rclo9_base; auto.
    }
    { econs 6; eauto. split; ss.
      eapply GF in LSIM. eapply pind9_mon_gen; ss. eauto.
      i. eapply __lsim_mon. 2: eauto. i. eapply rclo9_base; auto.
    }
    { econs 7; eauto. }
    { des. econs 8; eauto. esplits; eauto. split; ss.
      eapply GF in LSIM0. eapply pind9_mon_gen; ss. eauto.
      i. eapply __lsim_mon. 2: eauto. i. eapply rclo9_base; auto.
    }
    { econs 9; eauto. split; ss.
      eapply GF in LSIM. eapply pind9_mon_gen; ss. eauto.
      i. eapply __lsim_mon. 2: eauto. i. eapply rclo9_base; auto.
    }
    { econs 10; eauto. i. specialize (LSIM x). split; ss.
      eapply GF in LSIM. eapply pind9_mon_gen; ss. eauto.
      i. eapply __lsim_mon. 2: eauto. i. eapply rclo9_base; auto.
    }
    { econs 11; eauto. split; ss.
      eapply GF in LSIM. eapply pind9_mon_gen; ss. eauto.
      i. eapply __lsim_mon. 2: eauto. i. eapply rclo9_base; auto.
    }
    { econs 12; eauto. split; ss.
      eapply GF in LSIM. eapply pind9_mon_gen; ss. eauto.
      i. eapply __lsim_mon. 2: eauto. i. eapply rclo9_base; auto.
    }
    { econs 13; eauto. split; ss.
      eapply GF in LSIM. eapply pind9_mon_gen; ss. eauto.
      i. eapply __lsim_mon. 2: eauto. i. eapply rclo9_base; auto.
    }
    { econs 14; eauto. i. specialize (LSIM _ FAIR). split; ss.
      eapply GF in LSIM. eapply pind9_mon_gen; ss. eauto.
      i. eapply __lsim_mon. 2: eauto. i. eapply rclo9_base; auto.
    }
    { econs 15; eauto. i. specialize (LSIM ret).
      eapply rclo9_base; auto.
    }
    { econs 16; eauto. des. esplits; eauto. split; ss.
      eapply GF in LSIM0. eapply pind9_mon_gen; ss. eauto.
      i. eapply __lsim_mon. 2: eauto. i. eapply rclo9_base; auto.
    }
    { econs 17; eauto. i. specialize (LSIM _ _ _ _ _ _ _ INV0 VALID0 _ TGT).
      des. esplits; eauto. split; ss.
      eapply GF in LSIM0. eapply pind9_mon_gen; ss. eauto.
      i. eapply __lsim_mon. 2: eauto. i. eapply rclo9_base; auto.
    }
    { econs 18; eauto. i. specialize (LSIM _ _ _ _ _ _ _ INV0 VALID0 _ TGT).
      des. esplits; eauto.
      eapply rclo9_base; eauto.
    }
    { econs 19; eauto. eapply rclo9_base; auto. }
  Qed.

  Lemma lsim_indC_spec tid:
    (lsim_indC tid) <10= gupaco9 (fun r => pind9 (__lsim tid r) top9) (cpn9 (fun r => pind9 (__lsim tid r) top9)).
  Proof.
    i. eapply wrespect9_uclo; eauto with paco.
    { eapply lsim_mon. }
    eapply lsim_indC_wrepectful.
  Qed.

  Variant lsim_resetC
          (r: forall R0 R1 (RR: R0 -> R1 -> URA.car -> shared_rel), bool -> bool -> URA.car -> ((wf_stt R0 R1).(T) * itree srcE R0) -> ((wf_stt R0 R1).(T) * itree tgtE R1) -> shared_rel)
          R0 R1 (RR: R0 -> R1 -> URA.car -> shared_rel)
    :
    bool -> bool -> URA.car -> ((wf_stt R0 R1).(T) * itree srcE R0) -> ((wf_stt R0 R1).(T) * itree tgtE R1) -> shared_rel :=
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

    { des. eapply pind9_fold. eapply lsim_yieldL. esplits; eauto.
      split; ss. destruct LSIM as [LSIM IND]. hexploit IH; eauto.
    }

    { eapply pind9_fold. eapply lsim_yieldR; eauto. i.
      hexploit LSIM0; eauto. clear LSIM0. intros LSIM0.
      des. esplits; eauto. destruct LSIM as [LSIM IND].
      hexploit IH; eauto. i. split; ss; eauto.
    }

    { eapply pind9_fold. eapply lsim_sync; eauto. i.
      hexploit LSIM0. eapply INV0. eapply VALID0. all: eauto.
      i; des. esplits; eauto. eapply rclo9_base. eauto.
    }

    { hexploit H; ss; i. hexploit H0; ss; i. clarify.
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

    { pfold. eapply pind9_fold. eapply lsim_observe. i. eapply upaco9_mon_bot; eauto. }

    { des. pfold. eapply pind9_fold. eapply lsim_yieldL. esplits; eauto. split; ss.
      destruct LSIM as [LSIM IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind9_fold. eapply lsim_yieldR; eauto. i.
      hexploit LSIM0; eauto. clear LSIM0. intros LSIM0.
      des. esplits; eauto.
      destruct LSIM as [LSIM IND]. hexploit IH; eauto. i. split; ss. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind9_fold. eapply lsim_sync; eauto. i.
      hexploit LSIM0. eapply INV0. eapply VALID0. all: eauto. i; des. esplits; eauto.
      eapply upaco9_mon_bot; eauto.
    }

    { pclearbot. eapply paco9_mon_bot. eapply lsim_reset_prog. eauto. all: ss. }

  Qed.


  Variant lsim_ord_weakLC
          (r: forall R_src R_tgt (RR: R_src -> R_tgt -> URA.car -> shared_rel), bool -> bool -> URA.car -> ((wf_stt R_src R_tgt).(T) * itree srcE R_src) -> ((wf_stt R_src R_tgt).(T) * itree tgtE R_tgt) -> shared_rel)
          R_src R_tgt (RR: R_src -> R_tgt -> URA.car -> shared_rel)
    :
    bool -> bool -> URA.car -> ((wf_stt R_src R_tgt).(T) * itree srcE R_src) -> ((wf_stt R_src R_tgt).(T) * itree tgtE R_tgt) -> shared_rel :=
    | lsim_ord_weakLC_intro
        src tgt shr r_ctx ps pt o0 o1
        (REL: r _ _ RR ps pt r_ctx (o0, src) tgt shr)
        (LE: (wf_stt R_src R_tgt).(le) o0 o1)
      :
      lsim_ord_weakLC r RR ps pt r_ctx (o1, src) tgt shr
  .

  Lemma lsim_ord_weakLC_spec tid
    :
    lsim_ord_weakLC <10= gupaco9 (fun r => pind9 (__lsim tid r) top9) (cpn9 (fun r => pind9 (__lsim tid r) top9)).
  Proof.
    eapply wrespect9_uclo; eauto with paco.
    { eapply lsim_mon. }
    econs.
    { ii. inv IN. econs; eauto. }
    i. inv PR. destruct LE0 as [EQ | LT].
    { clarify. eapply pind9_mon_gen. eapply GF; eauto. 2: ss.
      i. eapply __lsim_mon. 2: eauto. i. eapply rclo9_base. auto.
    }
    eapply GF in REL.
    remember (o0, src) as osrc. rename REL into LSIM.
    move LSIM before GF. revert_until LSIM.
    pattern x0, x1, x2, x3, x4, x5, osrc, x7, x8.
    revert x0 x1 x2 x3 x4 x5 osrc x7 x8 LSIM. apply pind9_acc.
    intros rr DEC IH. clear DEC. intros R0 R1 LRR ps pt r_ctx osrc tgt shr LSIM.
    i; clarify.
    eapply pind9_unfold in LSIM.
    2:{ eapply _lsim_mon. }
    inv LSIM.

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

    { eapply pind9_fold. eapply lsim_observe. i.
      eapply rclo9_clo. econs. eapply rclo9_base; eauto.
      ss. right. auto.
    }

    { des. eapply pind9_fold. eapply lsim_yieldL. esplits; eauto.
      split; ss. destruct LSIM as [LSIM IND]. hexploit IH; eauto.
    }

    { eapply pind9_fold. eapply lsim_yieldR; eauto. i.
      hexploit LSIM0; eauto. clear LSIM0. intros LSIM0.
      des. esplits; eauto. eapply upind9_mon_gen. eauto. 2: ss.
      i. eapply __lsim_mon. 2: eauto. i. eapply rclo9_base. auto.
    }

    { eapply pind9_fold. eapply lsim_sync; eauto. i.
      hexploit LSIM0. eapply INV0. eapply VALID0. all: eauto.
      i; des. esplits; eauto. eapply rclo9_base. eauto.
    }

    { eapply pind9_fold. eapply lsim_progress. eapply rclo9_clo_base. econs; eauto. right; auto. }
  Qed.

  Variant lsim_ord_weakRC
          (r: forall R_src R_tgt (RR: R_src -> R_tgt -> URA.car -> shared_rel), bool -> bool -> URA.car -> ((wf_stt R_src R_tgt).(T) * itree srcE R_src) -> ((wf_stt R_src R_tgt).(T) * itree tgtE R_tgt) -> shared_rel)
          R_src R_tgt (RR: R_src -> R_tgt -> URA.car -> shared_rel)
    :
    bool -> bool -> URA.car -> ((wf_stt R_src R_tgt).(T) * itree srcE R_src) -> ((wf_stt R_src R_tgt).(T) * itree tgtE R_tgt) -> shared_rel :=
    | lsim_ord_weakRC_intro
        src tgt shr r_ctx ps pt o0 o1
        (REL: r _ _ RR ps pt r_ctx src (o0, tgt) shr)
        (LE: (wf_stt R_src R_tgt).(le) o0 o1)
      :
      lsim_ord_weakRC r RR ps pt r_ctx src (o1, tgt) shr
  .

  Lemma lsim_ord_weakRC_spec tid
    :
    lsim_ord_weakRC <10= gupaco9 (fun r => pind9 (__lsim tid r) top9) (cpn9 (fun r => pind9 (__lsim tid r) top9)).
  Proof.
    eapply wrespect9_uclo; eauto with paco.
    { eapply lsim_mon. }
    econs.
    { ii. inv IN. econs; eauto. }
    i. inv PR. destruct LE0 as [EQ | LT].
    { clarify. eapply pind9_mon_gen. eapply GF; eauto. 2: ss.
      i. eapply __lsim_mon. 2: eauto. i. eapply rclo9_base. auto.
    }
    eapply GF in REL.
    remember (o0, tgt) as otgt. rename REL into LSIM.
    move LSIM before GF. revert_until LSIM.
    pattern x0, x1, x2, x3, x4, x5, x6, otgt, x8.
    revert x0 x1 x2 x3 x4 x5 x6 otgt x8 LSIM. apply pind9_acc.
    intros rr DEC IH. clear DEC. intros R0 R1 LRR ps pt r_ctx src otgt shr LSIM.
    i; clarify.
    eapply pind9_unfold in LSIM.
    2:{ eapply _lsim_mon. }
    inv LSIM.

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

    { eapply pind9_fold. eapply lsim_observe. i.
      eapply rclo9_clo. econs. eapply rclo9_base; eauto.
      ss. right. auto.
    }

    { des. eapply pind9_fold. eapply lsim_yieldL. esplits; eauto.
      eapply upind9_mon_gen. eauto. 2: ss.
      i. eapply __lsim_mon. 2: eauto. i. eapply rclo9_base. auto.
    }

    { eapply pind9_fold. eapply lsim_yieldR; eauto. i.
      hexploit LSIM0; eauto. clear LSIM0. intros LSIM0.
      des. destruct LSIM as [LSIM IND]. hexploit IH; eauto.
      i. esplits. split. eapply H. ss. auto.
    }

    { eapply pind9_fold. eapply lsim_sync; eauto. i.
      hexploit LSIM0. eapply INV0. eapply VALID0. all: eauto.
      i; des. esplits; eauto. eapply rclo9_base. eauto.
    }

    { eapply pind9_fold. eapply lsim_progress. eapply rclo9_clo_base. econs; eauto. right; auto. }
  Qed.

  Definition local_RR {R0 R1} (RR: R0 -> R1 -> Prop) tid:
    R0 -> R1 -> URA.car -> shared_rel :=
    fun (r_src: R0) (r_tgt: R1) (r_ctx: URA.car) '(ths2, im_src1, im_tgt1, st_src1, st_tgt1) =>
      (exists ths3 r_own r_shared,
          (<<THS: NatMap.remove tid ths2 = ths3>>) /\
            (<<VALID: URA.wf (r_shared ⋅ r_own ⋅ r_ctx)>>) /\
            (<<INV: I (ths3, im_src1, im_tgt1, st_src1, st_tgt1) r_shared>>) /\
            (<<RET: RR r_src r_tgt>>)).

  Definition local_sim {R0 R1} (RR: R0 -> R1 -> Prop) src tgt :=
    forall ths0 im_src0 im_tgt0 st_src0 st_tgt0 r_shared0 r_ctx0
      (INV: I (ths0, im_src0, im_tgt0, st_src0, st_tgt0) r_shared0)
      tid ths1
      (THS: TIdSet.add_new tid ths0 ths1)
      (VALID: URA.wf (r_shared0 ⋅ r_ctx0)),
    forall im_tgt0'
      (UPD: fair_update im_tgt0 im_tgt0' (sum_fmap_l (fun t => if (tid_dec t tid) then Flag.success else Flag.emp))),
    exists r_shared1 r_own os ot,
      (<<INV: I (ths1, im_src0, im_tgt0', st_src0, st_tgt0) r_shared1>>) /\
        (<<VALID: URA.wf (r_shared1 ⋅ r_own ⋅ r_ctx0)>>) /\
        (forall ths im_src1 im_tgt1 st_src st_tgt r_shared2 r_ctx2
           (INV: I (ths, im_src1, im_tgt1, st_src, st_tgt) r_shared2)
           (VALID: URA.wf (r_shared2 ⋅ r_own ⋅ r_ctx2)),
          forall im_tgt2 (TGT: fair_update im_tgt1 im_tgt2 (sum_fmap_l (tids_fmap tid ths))),
            (<<LSIM: forall fs ft,
                lsim
                  tid
                  (@local_RR R0 R1 RR tid)
                  fs ft
                  r_ctx2
                  (os, src)
                  (ot, tgt)
                  (ths, im_src1, im_tgt2, st_src, st_tgt)
                  >>)).

End PRIMIVIESIM.
#[export] Hint Constructors __lsim: core.
#[export] Hint Unfold lsim: core.
#[export] Hint Resolve __lsim_mon: paco.
#[export] Hint Resolve _lsim_mon: paco.
#[export] Hint Resolve lsim_mon: paco.
#[export] Hint Resolve cpn9_wcompat: paco.


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

          I: (@shared md_src.(Mod.state) md_tgt.(Mod.state) md_src.(Mod.ident) md_tgt.(Mod.ident) wf_src wf_tgt) -> world -> Prop;
          init: forall im_tgt, exists im_src r_shared,
            (I (NatSet.empty, im_src, im_tgt, md_src.(Mod.st_init), md_tgt.(Mod.st_init)) r_shared) /\
              (URA.wf r_shared);

          wf_stt : Type -> Type -> WF;
          funs: forall fn args, match md_src.(Mod.funs) fn, md_tgt.(Mod.funs) fn with
                           | None, _ => True
                           | _, None => False
                           | Some ktr_src, Some ktr_tgt => local_sim I wf_stt (@eq Val) (ktr_src args) (ktr_tgt args)
                           end;
        }.
  End MODSIM.
End ModSim.