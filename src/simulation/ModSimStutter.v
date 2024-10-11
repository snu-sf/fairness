From sflib Require Import sflib.
From Paco Require Import paco.
Require Export Coq.Strings.String.
Require Import Coq.Classes.RelationClasses.
From iris.algebra Require Import cmra.

From Fairness Require Export ITreeLib FairBeh Mod.
From Fairness Require Import pind PCM.

Set Implicit Arguments.

Section PRIMIVIESIM.
  Context `{M: ucmra}.

  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable _ident_src: ID.
  Definition ident_src := sum_tid _ident_src.
  Variable _ident_tgt: ID.
  Definition ident_tgt := sum_tid _ident_tgt.

  Variable wf_src: WF.
  Variable wf_tgt: WF.

  Let srcE := threadE _ident_src state_src.
  Let tgtE := threadE _ident_tgt state_tgt.

  Variable wf_stt: Type -> Type -> WF.

  Definition shared :=
    (TIdSet.t *
       (@imap ident_src wf_src) *
       (@imap ident_tgt wf_tgt) *
       state_src *
       state_tgt)%type.

  Let shared_rel: Type := shared -> Prop.

  Variable I: shared -> (cmra_car M) -> Prop.

  Variant __lsim
          (tid: thread_id) R_src R_tgt (RR: R_src -> R_tgt -> (cmra_car M) -> shared_rel)
          (lsim: bool -> bool -> (cmra_car M) -> ((wf_stt R_src R_tgt).(T) * itree srcE R_src) -> itree tgtE R_tgt -> shared_rel)
          (_lsim: bool -> bool -> (cmra_car M) -> ((wf_stt R_src R_tgt).(T) * itree srcE R_src) -> itree tgtE R_tgt -> shared_rel)
    :
    bool -> bool -> (cmra_car M) -> ((wf_stt R_src R_tgt).(T) * itree srcE R_src) -> itree tgtE R_tgt -> shared_rel :=
  | lsim_ret
      f_src f_tgt r_ctx o o0
      ths im_src im_tgt st_src st_tgt
      r_src r_tgt
      (LT: (wf_stt R_src R_tgt).(lt) o0 o)
      (LSIM: RR r_src r_tgt r_ctx (ths, im_src, im_tgt, st_src, st_tgt))
    :
    __lsim tid RR lsim _lsim f_src f_tgt r_ctx (o, Ret r_src) (Ret r_tgt) (ths, im_src, im_tgt, st_src, st_tgt)

  | lsim_tauL
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt
      itr_src itr_tgt
      (LSIM: _lsim true f_tgt r_ctx (o, itr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt))
    :
    __lsim tid RR lsim _lsim f_src f_tgt r_ctx (o, Tau itr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt)
  | lsim_chooseL
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt
      X ktr_src itr_tgt
      (LSIM: exists x, _lsim true f_tgt r_ctx (o, ktr_src x) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt))
    :
    __lsim tid RR lsim _lsim f_src f_tgt r_ctx (o, trigger (Choose X) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt)
  | lsim_stateL
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt
      X run ktr_src itr_tgt
      (LSIM: _lsim true f_tgt r_ctx (o, ktr_src (snd (run st_src) : X)) itr_tgt (ths, im_src, im_tgt, fst (run st_src), st_tgt))
    :
    __lsim tid RR lsim _lsim f_src f_tgt r_ctx (o, trigger (State run) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt)
  | lsim_tidL
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt
      ktr_src itr_tgt
      (LSIM: _lsim true f_tgt r_ctx (o, ktr_src tid) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt))
    :
    __lsim tid RR lsim _lsim f_src f_tgt r_ctx (o, trigger (GetTid) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt)
  | lsim_UB
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt
      ktr_src itr_tgt
    :
    __lsim tid RR lsim _lsim f_src f_tgt r_ctx (o, trigger (Undefined) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt)
  | lsim_fairL
      f_src f_tgt r_ctx o
      ths im_src0 im_tgt st_src st_tgt
      f ktr_src itr_tgt
      (LSIM: exists im_src1,
          (<<FAIR: fair_update im_src0 im_src1 (prism_fmap inrp f)>>) /\
            (<<LSIM: _lsim true f_tgt r_ctx (o, ktr_src tt) itr_tgt (ths, im_src1, im_tgt, st_src, st_tgt)>>))
    :
    __lsim tid RR lsim _lsim f_src f_tgt r_ctx (o, trigger (Fair f) >>= ktr_src) itr_tgt (ths, im_src0, im_tgt, st_src, st_tgt)

  | lsim_tauR
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt
      itr_src itr_tgt
      (LSIM: _lsim f_src true r_ctx (o, itr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt))
    :
    __lsim tid RR lsim _lsim f_src f_tgt r_ctx (o, itr_src) (Tau itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)
  | lsim_chooseR
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt
      X itr_src ktr_tgt
      (LSIM: forall x, _lsim f_src true r_ctx (o, itr_src) (ktr_tgt x) (ths, im_src, im_tgt, st_src, st_tgt))
    :
    __lsim tid RR lsim _lsim f_src f_tgt r_ctx (o, itr_src) (trigger (Choose X) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)
  | lsim_stateR
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt
      X run itr_src ktr_tgt
      (LSIM: _lsim f_src true r_ctx (o, itr_src) (ktr_tgt (snd (run st_tgt) : X)) (ths, im_src, im_tgt, st_src, fst (run st_tgt)))
    :
    __lsim tid RR lsim _lsim f_src f_tgt r_ctx (o, itr_src) (trigger (State run) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)
  | lsim_tidR
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt
      itr_src ktr_tgt
      (LSIM: _lsim f_src true r_ctx (o, itr_src) (ktr_tgt tid) (ths, im_src, im_tgt, st_src, st_tgt))
    :
    __lsim tid RR lsim _lsim f_src f_tgt r_ctx (o, itr_src) (trigger (GetTid) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)
  | lsim_fairR
      f_src f_tgt r_ctx o
      ths im_src im_tgt0 st_src st_tgt
      f itr_src ktr_tgt
      (LSIM: forall im_tgt1
                   (FAIR: fair_update im_tgt0 im_tgt1 (prism_fmap inrp f)),
          (<<LSIM: _lsim f_src true r_ctx (o, itr_src) (ktr_tgt tt) (ths, im_src, im_tgt1, st_src, st_tgt)>>))
    :
    __lsim tid RR lsim _lsim f_src f_tgt r_ctx (o, itr_src) (trigger (Fair f) >>= ktr_tgt) (ths, im_src, im_tgt0, st_src, st_tgt)

  | lsim_observe
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt
      fn args ktr_src ktr_tgt
      (LSIM: forall ret,
          lsim true true r_ctx (o, ktr_src ret) (ktr_tgt ret) (ths, im_src, im_tgt, st_src, st_tgt))
    :
    __lsim tid RR lsim _lsim f_src f_tgt r_ctx (o, trigger (Observe fn args) >>= ktr_src) (trigger (Observe fn args) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)

  | lsim_call
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt
      fn args ktr_src itr_tgt
    : __lsim tid RR lsim _lsim f_src f_tgt r_ctx (o, trigger (Call fn args) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt)

  | lsim_yieldR
      f_src f_tgt r_ctx0 o0
      ths0 im_src0 im_tgt0 st_src0 st_tgt0
      r_own r_shared
      ktr_src ktr_tgt
      (INV: I (ths0, im_src0, im_tgt0, st_src0, st_tgt0) r_shared)
      (VALID: ✓ (r_shared ⋅ r_own ⋅ r_ctx0))
      o1
      (STUTTER: (wf_stt R_src R_tgt).(lt) o1 o0)
      (LSIM: forall ths1 im_src1 im_tgt1 st_src1 st_tgt1 r_shared1 r_ctx1
               (INV: I (ths1, im_src1, im_tgt1, st_src1, st_tgt1) r_shared1)
               (VALID: ✓ (r_shared1 ⋅ r_own ⋅ r_ctx1))
               im_tgt2
               (TGT: fair_update im_tgt1 im_tgt2 (prism_fmap inlp (tids_fmap tid ths1))),
          (<<LSIM: lsim true true r_ctx1 (o1, trigger (Yield) >>= ktr_src) (ktr_tgt tt) (ths1, im_src1, im_tgt2, st_src1, st_tgt1)>>))
    :
    __lsim tid RR lsim _lsim f_src f_tgt r_ctx0 (o0, trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt) (ths0, im_src0, im_tgt0, st_src0, st_tgt0)
  | lsim_yieldL
      f_src f_tgt r_ctx o0
      ths im_src0 im_tgt st_src st_tgt
      ktr_src itr_tgt
      (LSIM: exists im_src1 o1,
          (<<FAIR: fair_update im_src0 im_src1 (prism_fmap inlp (tids_fmap tid ths))>>) /\
            (<<LSIM: _lsim true f_tgt r_ctx (o1, ktr_src tt) itr_tgt (ths, im_src1, im_tgt, st_src, st_tgt)>>))
    :
    __lsim tid RR lsim _lsim f_src f_tgt r_ctx (o0, trigger (Yield) >>= ktr_src) itr_tgt (ths, im_src0, im_tgt, st_src, st_tgt)

  | lsim_progress
      r_ctx o
      ths im_src im_tgt st_src st_tgt
      itr_src itr_tgt
      (LSIM: lsim false false r_ctx (o, itr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt))
    :
    __lsim tid RR lsim _lsim true true r_ctx (o, itr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt)
  .

  Definition lsim (tid: thread_id)
             R_src R_tgt (RR: R_src -> R_tgt -> (cmra_car M) -> shared_rel):
    bool -> bool -> (cmra_car M) -> ((wf_stt R_src R_tgt).(T) * itree srcE R_src) -> itree tgtE R_tgt -> shared_rel :=
    paco6 (fun r => pind6 (__lsim tid RR r) top6) bot6.

  Lemma __lsim_mon tid R0 R1 (RR: R0 -> R1 -> _ -> _):
    forall r r' (LE: r <6= r'), (__lsim tid RR r) <7= (__lsim tid RR r').
  Proof.
    ii. inv PR; try (econs; eauto; fail).
    eapply lsim_yieldR; eauto. i. hexploit LSIM; eauto.
  Qed.

  Lemma _lsim_mon tid R0 R1 (RR: R0 -> R1 -> _ -> _): forall r, monotone6 (__lsim tid RR r).
  Proof.
    ii. inv IN; try (econs; eauto; fail).
    { des. econs; eauto. }
    { des. econs; eauto. }
    { econs. i. eapply LE. eapply LSIM. eauto. }
    { des. econs; esplits; eauto. }
  Qed.

  Lemma lsim_mon tid R0 R1 (RR: R0 -> R1 -> _ -> _):
    forall q, monotone6 (fun r => pind6 (__lsim tid RR r) q).
  Proof.
    ii. eapply pind6_mon_gen; eauto.
    ii. eapply __lsim_mon; eauto.
  Qed.

  Variant lsim_indC tid R_src R_tgt (RR: R_src -> R_tgt -> (cmra_car M) -> shared_rel)
          (r: bool -> bool -> (cmra_car M) -> ((wf_stt R_src R_tgt).(T) * itree srcE R_src) -> itree tgtE R_tgt -> shared_rel)
    :
    bool -> bool -> (cmra_car M) -> ((wf_stt R_src R_tgt).(T) * itree srcE R_src) -> itree tgtE R_tgt -> shared_rel :=
    | lsim_indC_ret
        f_src f_tgt r_ctx o o0
        ths im_src im_tgt st_src st_tgt
        r_src r_tgt
        (LT: (wf_stt R_src R_tgt).(lt) o0 o)
        (LSIM: RR r_src r_tgt r_ctx (ths, im_src, im_tgt, st_src, st_tgt))
      :
      lsim_indC tid RR r f_src f_tgt r_ctx (o, Ret r_src) (Ret r_tgt) (ths, im_src, im_tgt, st_src, st_tgt)

    | lsim_indC_tauL
        f_src f_tgt r_ctx o
        ths im_src im_tgt st_src st_tgt
        itr_src itr_tgt
        (LSIM: r true f_tgt r_ctx (o, itr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt))
      :
      lsim_indC tid RR r f_src f_tgt r_ctx (o, Tau itr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt)
    | lsim_indC_chooseL
        f_src f_tgt r_ctx o
        ths im_src im_tgt st_src st_tgt
        X ktr_src itr_tgt
        (LSIM: exists x, r true f_tgt r_ctx (o, ktr_src x) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt))
      :
      lsim_indC tid RR r f_src f_tgt r_ctx (o, trigger (Choose X) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt)
    | lsim_indC_stateL
        f_src f_tgt r_ctx o
        ths im_src im_tgt st_src st_tgt
        X run ktr_src itr_tgt
        (LSIM: r true f_tgt r_ctx (o, ktr_src (snd (run st_src) : X)) itr_tgt (ths, im_src, im_tgt, fst (run st_src), st_tgt))
      :
      lsim_indC tid RR r f_src f_tgt r_ctx (o, trigger (State run) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt)
    | lsim_indC_tidL
        f_src f_tgt r_ctx o
        ths im_src im_tgt st_src st_tgt
        ktr_src itr_tgt
        (LSIM: r true f_tgt r_ctx (o, ktr_src tid) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt))
      :
      lsim_indC tid RR r f_src f_tgt r_ctx (o, trigger (GetTid) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt)
    | lsim_indC_UB
        f_src f_tgt r_ctx o
        ths im_src im_tgt st_src st_tgt
        ktr_src itr_tgt
      :
      lsim_indC tid RR r f_src f_tgt r_ctx (o, trigger (Undefined) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt)
    | lsim_indC_fairL
        f_src f_tgt r_ctx o
        ths im_src0 im_tgt st_src st_tgt
        f ktr_src itr_tgt
        (LSIM: exists im_src1,
            (<<FAIR: fair_update im_src0 im_src1 (prism_fmap inrp f)>>) /\
              (<<LSIM: r true f_tgt r_ctx (o, ktr_src tt) itr_tgt (ths, im_src1, im_tgt, st_src, st_tgt)>>))
      :
      lsim_indC tid RR r f_src f_tgt r_ctx (o, trigger (Fair f) >>= ktr_src) itr_tgt (ths, im_src0, im_tgt, st_src, st_tgt)

    | lsim_indC_tauR
        f_src f_tgt r_ctx o
        ths im_src im_tgt st_src st_tgt
        itr_src itr_tgt
        (LSIM: r f_src true r_ctx (o, itr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt))
      :
      lsim_indC tid RR r f_src f_tgt r_ctx (o, itr_src) (Tau itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)
    | lsim_indC_chooseR
        f_src f_tgt r_ctx o
        ths im_src im_tgt st_src st_tgt
        X itr_src ktr_tgt
        (LSIM: forall x, r f_src true r_ctx (o, itr_src) (ktr_tgt x) (ths, im_src, im_tgt, st_src, st_tgt))
      :
      lsim_indC tid RR r f_src f_tgt r_ctx (o, itr_src) (trigger (Choose X) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)
    | lsim_indC_stateR
        f_src f_tgt r_ctx o
        ths im_src im_tgt st_src st_tgt
        X run itr_src ktr_tgt
        (LSIM: r f_src true r_ctx (o, itr_src) (ktr_tgt (snd (run st_tgt) : X)) (ths, im_src, im_tgt, st_src, fst (run st_tgt)))
      :
      lsim_indC tid RR r f_src f_tgt r_ctx (o, itr_src) (trigger (State run) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)
    | lsim_indC_tidR
        f_src f_tgt r_ctx o
        ths im_src im_tgt st_src st_tgt
        itr_src ktr_tgt
        (LSIM: r f_src true r_ctx (o, itr_src) (ktr_tgt tid) (ths, im_src, im_tgt, st_src, st_tgt))
      :
      lsim_indC tid RR r f_src f_tgt r_ctx (o, itr_src) (trigger (GetTid) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)
    | lsim_indC_fairR
        f_src f_tgt r_ctx o
        ths im_src im_tgt0 st_src st_tgt
        f itr_src ktr_tgt
        (LSIM: forall im_tgt1
                 (FAIR: fair_update im_tgt0 im_tgt1 (prism_fmap inrp f)),
            (<<LSIM: r f_src true r_ctx (o, itr_src) (ktr_tgt tt) (ths, im_src, im_tgt1, st_src, st_tgt)>>))
      :
      lsim_indC tid RR r f_src f_tgt r_ctx (o, itr_src) (trigger (Fair f) >>= ktr_tgt) (ths, im_src, im_tgt0, st_src, st_tgt)

    | lsim_indC_observe
        f_src f_tgt r_ctx o
        ths im_src im_tgt st_src st_tgt
        fn args ktr_src ktr_tgt
        (LSIM: forall ret,
            r true true r_ctx (o, ktr_src ret) (ktr_tgt ret) (ths, im_src, im_tgt, st_src, st_tgt))
      :
      lsim_indC tid RR r f_src f_tgt r_ctx (o, trigger (Observe fn args) >>= ktr_src) (trigger (Observe fn args) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)

    | lsim_indC_call
        f_src f_tgt r_ctx o
        ths im_src im_tgt st_src st_tgt
        fn args ktr_src itr_tgt
      : lsim_indC tid RR r f_src f_tgt r_ctx (o, trigger (Call fn args) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt)

    | lsim_indC_yieldR
        f_src f_tgt r_ctx0 o0
        ths0 im_src0 im_tgt0 st_src0 st_tgt0
        r_own r_shared
        ktr_src ktr_tgt
        (INV: I (ths0, im_src0, im_tgt0, st_src0, st_tgt0) r_shared)
        (VALID: ✓ (r_shared ⋅ r_own ⋅ r_ctx0))
        o1
        (STUTTER: (wf_stt R_src R_tgt).(lt) o1 o0)
        (LSIM: forall ths1 im_src1 im_tgt1 st_src1 st_tgt1 r_shared1 r_ctx1
                 (INV: I (ths1, im_src1, im_tgt1, st_src1, st_tgt1) r_shared1)
                 (VALID: ✓ (r_shared1 ⋅ r_own ⋅ r_ctx1))
                 im_tgt2
                 (TGT: fair_update im_tgt1 im_tgt2 (prism_fmap inlp (tids_fmap tid ths1))),
            (<<LSIM: r true true r_ctx1 (o1, trigger (Yield) >>= ktr_src) (ktr_tgt tt) (ths1, im_src1, im_tgt2, st_src1, st_tgt1)>>))
      :
      lsim_indC tid RR r f_src f_tgt r_ctx0 (o0, trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt) (ths0, im_src0, im_tgt0, st_src0, st_tgt0)
    | lsim_indC_yieldL
        f_src f_tgt r_ctx o0
        ths im_src0 im_tgt st_src st_tgt
        ktr_src itr_tgt
        (LSIM: exists im_src1 o1,
            (<<FAIR: fair_update im_src0 im_src1 (prism_fmap inlp (tids_fmap tid ths))>>) /\
              (<<LSIM: r true f_tgt r_ctx (o1, ktr_src tt) itr_tgt (ths, im_src1, im_tgt, st_src, st_tgt)>>))
      :
      lsim_indC tid RR r f_src f_tgt r_ctx (o0, trigger (Yield) >>= ktr_src) itr_tgt (ths, im_src0, im_tgt, st_src, st_tgt)

    | lsim_indC_progress
        r_ctx o
        ths im_src im_tgt st_src st_tgt
        itr_src itr_tgt
        (LSIM: r false false r_ctx (o, itr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt))
      :
      lsim_indC tid RR r true true r_ctx (o, itr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt)
  .

  Lemma lsim_indC_mon tid R0 R1 (RR: R0 -> R1 -> _ -> _): monotone6 (lsim_indC tid RR).
  Proof.
    ii. inv IN; try (econs; eauto; fail).
    { des; econs; eauto. }
    { des; econs; eauto. }
    { econs. i. specialize (LSIM _ FAIR). eauto. }
    { econs; eauto. i. hexploit LSIM; eauto. }
    { des; econs; eauto. esplits; eauto. }
  Qed.

  Hint Resolve lsim_indC_mon: paco.

  Lemma lsim_indC_wrepectful tid R0 R1 (RR: R0 -> R1 -> _ -> _):
    wrespectful6 (fun r => pind6 (__lsim tid RR r) top6) (lsim_indC tid RR).
  Proof.
    econs; eauto with paco.
    i. eapply pind6_fold. inv PR.
    { eapply lsim_ret; eauto. }
    { eapply lsim_tauL; eauto. split; ss.
      eapply GF in LSIM. eapply pind6_mon_gen; ss. eauto.
      i. eapply __lsim_mon. 2: eauto. i. eapply rclo6_base; auto.
    }
    { des. eapply lsim_chooseL; eauto. esplits; eauto. split; ss.
      eapply GF in LSIM. eapply pind6_mon_gen; ss. eauto.
      i. eapply __lsim_mon. 2: eauto. i. eapply rclo6_base; auto.
    }
    { eapply lsim_stateL; eauto. split; ss.
      eapply GF in LSIM. eapply pind6_mon_gen; ss. eauto.
      i. eapply __lsim_mon. 2: eauto. i. eapply rclo6_base; auto.
    }
    { eapply lsim_tidL; eauto. split; ss.
      eapply GF in LSIM. eapply pind6_mon_gen; ss. eauto.
      i. eapply __lsim_mon. 2: eauto. i. eapply rclo6_base; auto.
    }
    { eapply lsim_UB; eauto. }
    { des. eapply lsim_fairL; eauto. esplits; eauto. split; ss.
      eapply GF in LSIM0. eapply pind6_mon_gen; ss. eauto.
      i. eapply __lsim_mon. 2: eauto. i. eapply rclo6_base; auto.
    }
    { eapply lsim_tauR; eauto. split; ss.
      eapply GF in LSIM. eapply pind6_mon_gen; ss. eauto.
      i. eapply __lsim_mon. 2: eauto. i. eapply rclo6_base; auto.
    }
    { eapply lsim_chooseR; eauto. i. specialize (LSIM x). split; ss.
      eapply GF in LSIM. eapply pind6_mon_gen; ss. eauto.
      i. eapply __lsim_mon. 2: eauto. i. eapply rclo6_base; auto.
    }
    { eapply lsim_stateR; eauto. split; ss.
      eapply GF in LSIM. eapply pind6_mon_gen; ss. eauto.
      i. eapply __lsim_mon. 2: eauto. i. eapply rclo6_base; auto.
    }
    { eapply lsim_tidR; eauto. split; ss.
      eapply GF in LSIM. eapply pind6_mon_gen; ss. eauto.
      i. eapply __lsim_mon. 2: eauto. i. eapply rclo6_base; auto.
    }
    { eapply lsim_fairR; eauto. i. specialize (LSIM _ FAIR). split; ss.
      eapply GF in LSIM. eapply pind6_mon_gen; ss. eauto.
      i. eapply __lsim_mon. 2: eauto. i. eapply rclo6_base; auto.
    }
    { eapply lsim_observe; eauto. i. specialize (LSIM ret).
      eapply rclo6_base; auto.
    }
    { eapply lsim_call. }
    { eapply lsim_yieldR; eauto. i. specialize (LSIM _ _ _ _ _ _ _ INV0 VALID0 _ TGT).
      des. esplits; eauto.
      eapply rclo6_base; auto.
    }
    { des. eapply lsim_yieldL; eauto. esplits; eauto. split; ss.
      eapply GF in LSIM0. eapply pind6_mon_gen; ss. eauto.
      i. eapply __lsim_mon. 2: eauto. i. eapply rclo6_base; auto.
    }
    { eapply lsim_progress; eauto. eapply rclo6_base; auto. }
  Qed.

  Lemma lsim_indC_spec tid R0 R1 (RR: R0 -> R1 -> _ -> _):
    (lsim_indC tid RR) <7= gupaco6 (fun r => pind6 (__lsim tid RR r) top6) (cpn6 (fun r => pind6 (__lsim tid RR r) top6)).
  Proof.
    i. eapply wrespect6_uclo; eauto with paco.
    { eapply lsim_mon. }
    eapply lsim_indC_wrepectful.
  Qed.


  Variant lsim_resetC R_src R_tgt (RR: R_src -> R_tgt -> (cmra_car M) -> shared_rel)
          (r: bool -> bool -> (cmra_car M) -> ((wf_stt R_src R_tgt).(T) * itree srcE R_src) -> itree tgtE R_tgt -> shared_rel)
    :
    bool -> bool -> (cmra_car M) -> ((wf_stt R_src R_tgt).(T) * itree srcE R_src) -> itree tgtE R_tgt -> shared_rel :=
    | lsim_resetC_intro
        src tgt shr r_ctx
        ps0 pt0 ps1 pt1
        (REL: r ps1 pt1 r_ctx src tgt shr)
        (SRC: ps1 = true -> ps0 = true)
        (TGT: pt1 = true -> pt0 = true)
      :
      lsim_resetC RR r ps0 pt0 r_ctx src tgt shr
  .

  Lemma lsim_resetC_spec tid R_src R_tgt (RR: R_src -> R_tgt -> (cmra_car M) -> shared_rel)
    :
    lsim_resetC RR <7= gupaco6 (fun r => pind6 (__lsim tid RR r) top6) (cpn6 (fun r => pind6 (__lsim tid RR r) top6)).
  Proof.
    eapply wrespect6_uclo; eauto with paco.
    { eapply lsim_mon. }
    econs.
    { ii. inv IN. econs; eauto. }
    i. inv PR. eapply GF in REL.
    eapply pind6_acc in REL.
    instantiate (1:= (fun ps1 pt1 r_ctx src tgt shr =>
                        forall ps0 pt0,
                          (ps1 = true -> ps0 = true) ->
                          (pt1 = true -> pt0 = true) ->
                          pind6 (__lsim tid RR (rclo6 (lsim_resetC RR) r)) top6 ps0 pt0 r_ctx src tgt shr)) in REL; eauto.
    ss. i. eapply pind6_unfold in PR.
    2:{ eapply _lsim_mon. }
    rename PR into LSIM. inv LSIM.

    { eapply pind6_fold. econs; eauto. }

    { destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      eapply pind6_fold. eapply lsim_tauL. split; ss.
      hexploit IH; eauto.
    }

    { des. eapply pind6_fold. eapply lsim_chooseL. esplits; eauto. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { eapply pind6_fold. eapply lsim_stateL. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { eapply pind6_fold. eapply lsim_tidL. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { eapply pind6_fold. eapply lsim_UB. }

    { des. eapply pind6_fold. eapply lsim_fairL. esplits; eauto. split; ss.
      destruct LSIM as [LSIM IND]. hexploit IH; eauto.
    }

    { destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      eapply pind6_fold. eapply lsim_tauR. split; ss.
      hexploit IH. eauto. all: eauto.
    }

    { eapply pind6_fold. eapply lsim_chooseR. i. split; ss. specialize (LSIM0 x).
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { eapply pind6_fold. eapply lsim_stateR. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { eapply pind6_fold. eapply lsim_tidR. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { eapply pind6_fold. eapply lsim_fairR. i. split; ss. specialize (LSIM0 _ FAIR).
      des. destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { eapply pind6_fold. eapply lsim_observe. i. eapply rclo6_base. auto. }

    { eapply pind6_fold. eapply lsim_call. }

    { eapply pind6_fold. eapply lsim_yieldR; eauto. i.
      hexploit LSIM0; eauto. clear LSIM0. intros LSIM0. des. esplits; eauto.
      eapply rclo6_base. auto.
    }

    { des. eapply pind6_fold. eapply lsim_yieldL. esplits; eauto. split; ss.
      destruct LSIM as [LSIM IND]. hexploit IH; eauto.
    }

    { hexploit H; ss; i. hexploit H0; ss; i. clarify.
      eapply pind6_fold. eapply lsim_progress. eapply rclo6_base; auto. }
  Qed.

  Lemma lsim_reset_prog
        tid
        R0 R1 (RR: R0 -> R1 -> (cmra_car M) -> shared_rel)
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
    { eapply cpn6_wcompat. eapply lsim_mon. }
    guclo lsim_resetC_spec.
    { eapply lsim_mon. }
    econs; eauto. gfinal.
    { eapply lsim_mon. }
    right. auto.
  Qed.

  Lemma lsim_set_prog
        tid
        R0 R1 (RR: R0 -> R1 -> (cmra_car M) -> shared_rel)
        r_ctx src tgt shr
        (LSIM: lsim tid RR true true r_ctx src tgt shr)
    :
    forall ps pt, lsim tid RR ps pt r_ctx src tgt shr.
  Proof.
    i. revert_until RR. pcofix CIH. i.
    remember true as ps0 in LSIM at 1. remember true as pt0 in LSIM at 1.
    move LSIM before CIH. revert_until LSIM. punfold LSIM.
    2:{ eapply lsim_mon. }
    eapply pind6_acc in LSIM.

    { instantiate (1:= (fun ps0 pt0 r_ctx src tgt shr =>
                          ps0 = true ->
                          pt0 = true ->
                          forall ps pt,
                            paco6 (fun r0 => pind6 (__lsim tid RR r0) top6) r ps pt r_ctx src tgt shr)) in LSIM; auto. }

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

    { pfold. eapply pind6_fold. eapply lsim_stateL. split; ss.
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

    { pfold. eapply pind6_fold. eapply lsim_stateR. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind6_fold. eapply lsim_tidR. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind6_fold. eapply lsim_fairR. i. split; ss. specialize (LSIM0 _ FAIR).
      des. destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pfold. eapply pind6_fold. eapply lsim_observe. i. eapply upaco6_mon_bot; eauto. }

    { pfold. eapply pind6_fold. eapply lsim_call. }

    { pfold. eapply pind6_fold. eapply lsim_yieldR; eauto. i.
      hexploit LSIM0; eauto. clear LSIM0. intros LSIM0. des. esplits; eauto.
      eapply upaco6_mon_bot; eauto.
    }

    { des. pfold. eapply pind6_fold. eapply lsim_yieldL. esplits; eauto. split; ss.
      destruct LSIM as [LSIM IND]. hexploit IH; eauto. i. punfold H. eapply lsim_mon.
    }

    { pclearbot. eapply paco6_mon_bot. eapply lsim_reset_prog. eauto. all: ss. }

  Qed.


  Variant lsim_ord_weakC R_src R_tgt (RR: R_src -> R_tgt -> (cmra_car M) -> shared_rel)
          (r: bool -> bool -> (cmra_car M) -> ((wf_stt R_src R_tgt).(T) * itree srcE R_src) -> itree tgtE R_tgt -> shared_rel)
    :
    bool -> bool -> (cmra_car M) -> ((wf_stt R_src R_tgt).(T) * itree srcE R_src) -> itree tgtE R_tgt -> shared_rel :=
    | lsim_ord_weakC_intro
        src tgt shr r_ctx ps pt o0 o1
        (REL: r ps pt r_ctx (o0, src) tgt shr)
        (LE: (wf_stt R_src R_tgt).(le) o0 o1)
      :
      lsim_ord_weakC RR r ps pt r_ctx (o1, src) tgt shr
  .

  Lemma lsim_ord_weakC_spec tid R_src R_tgt (RR: R_src -> R_tgt -> (cmra_car M) -> shared_rel)
    :
    lsim_ord_weakC RR <7= gupaco6 (fun r => pind6 (__lsim tid RR r) top6) (cpn6 (fun r => pind6 (__lsim tid RR r) top6)).
  Proof.
    eapply wrespect6_uclo; eauto with paco.
    { eapply lsim_mon. }
    econs.
    { ii. inv IN. econs; eauto. }
    i. inv PR. destruct LE0 as [EQ | LT].
    { clarify. eapply pind6_mon_gen. eapply GF; eauto. 2: ss.
      i. eapply __lsim_mon. 2: eauto. i. eapply rclo6_base. auto.
    }
    eapply GF in REL.
    remember (o0, src) as osrc. rename REL into LSIM.
    move LSIM before GF. revert_until LSIM.
    pattern x0, x1, x2, osrc, x4, x5.
    revert x0 x1 x2 osrc x4 x5 LSIM. apply pind6_acc.
    intros rr DEC IH. clear DEC. intros ps pt r_ctx osrc tgt shr LSIM.
    i; clarify.
    eapply pind6_unfold in LSIM.
    2:{ eapply _lsim_mon. }
    inv LSIM.

    { eapply pind6_fold. eapply lsim_ret; eauto. }
    { eapply pind6_fold. eapply lsim_tauL; eauto.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND; eauto.
    }
    { eapply pind6_fold. eapply lsim_chooseL; eauto.
      des. exists x.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND; eauto.
    }
    { eapply pind6_fold. eapply lsim_stateL; eauto.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND; eauto.
    }
    { eapply pind6_fold. eapply lsim_tidL; eauto.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND; eauto.
    }
    { eapply pind6_fold. eapply lsim_UB; eauto. }
    { eapply pind6_fold. eapply lsim_fairL; eauto.
      des. esplits; eauto.
      split; ss. destruct LSIM as [LSIM IND]. eapply IH in IND; eauto.
    }
    { eapply pind6_fold. eapply lsim_tauR; eauto.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND; eauto.
    }
    { eapply pind6_fold. eapply lsim_chooseR; eauto.
      i. specialize (LSIM0 x).
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND; eauto.
    }
    { eapply pind6_fold. eapply lsim_stateR; eauto.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND; eauto.
    }
    { eapply pind6_fold. eapply lsim_tidR; eauto.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND; eauto.
    }
    { eapply pind6_fold. eapply lsim_fairR; eauto.
      i. specialize (LSIM0 _ FAIR).
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND; eauto.
    }
    { eapply pind6_fold. eapply lsim_observe; eauto.
      i. specialize (LSIM0 ret).
      eapply rclo6_clo_base. econs; eauto. right. auto.
    }

    { eapply pind6_fold. eapply lsim_call. }

    { eapply pind6_fold. eapply lsim_yieldR; eauto.
      i. hexploit LSIM0; clear LSIM0; eauto; intro LSIM. des. esplits; eauto.
      eapply rclo6_clo_base. econs; eauto. right. auto.
    }

    { eapply pind6_fold. eapply lsim_yieldL; eauto.
      des. esplits; eauto. destruct LSIM as [LSIM IND].
      split; ss. eapply pind6_mon_gen. eapply LSIM. 2: ss.
      i. eapply __lsim_mon. 2: eapply PR. i. eapply rclo6_base; eauto.
    }

    { eapply pind6_fold. eapply lsim_progress.
      eapply rclo6_clo_base. econs; eauto. right. auto.
    }

  Qed.

  Lemma stutter_ord_weak
        tid
        R0 R1 (LRR: R0 -> R1 -> (cmra_car M) -> shared_rel)
        ps pt r_ctx src tgt (shr: shared) o0 o1
        (LE: (wf_stt R0 R1).(le) o0 o1)
        (LSIM: lsim tid LRR ps pt r_ctx (o0, src) tgt shr)
    :
    lsim tid LRR ps pt r_ctx (o1, src) tgt shr.
  Proof.
    ginit.
    { eapply lsim_mon. }
    { eapply cpn6_wcompat. eapply lsim_mon. }
    guclo lsim_ord_weakC_spec.
    { eapply lsim_mon. }
    econs; eauto. gfinal.
    { eapply lsim_mon. }
    right. auto.
  Qed.

  Definition local_RR {R0 R1} (RR: R0 -> R1 -> Prop) tid:
    R0 -> R1 -> (cmra_car M) -> shared_rel :=
    fun (r_src: R0) (r_tgt: R1) (r_ctx: (cmra_car M)) '(ths2, im_src1, im_tgt1, st_src1, st_tgt1) =>
      (exists ths3 r_own r_shared,
          (<<THS: NatMap.remove tid ths2 = ths3>>) /\
            (<<VALID: ✓ (r_shared ⋅ r_own ⋅ r_ctx)>>) /\
            (<<INV: I (ths3, im_src1, im_tgt1, st_src1, st_tgt1) r_shared>>) /\
            (<<RET: RR r_src r_tgt>>)).

  Definition local_sim {R0 R1} (RR: R0 -> R1 -> Prop) src tgt :=
    forall ths0 im_src0 im_tgt0 st_src0 st_tgt0 r_shared0 r_ctx0
      (INV: I (ths0, im_src0, im_tgt0, st_src0, st_tgt0) r_shared0)
      tid ths1
      (THS: TIdSet.add_new tid ths0 ths1)
      (VALID: ✓ (r_shared0 ⋅ r_ctx0)),
    forall im_tgt0'
      (UPD: fair_update im_tgt0 im_tgt0' (prism_fmap inlp (fun t => if (tid_dec t tid) then Flag.success else Flag.emp))),
    exists r_shared1 r_own o im_src0',
      (<<INV: I (ths1, im_src0', im_tgt0', st_src0, st_tgt0) r_shared1>>) /\
        (<<VALID: ✓ (r_shared1 ⋅ r_own ⋅ r_ctx0)>>) /\
        (forall ths im_src1 im_tgt1 st_src st_tgt r_shared2 r_ctx2
           (INV: I (ths, im_src1, im_tgt1, st_src, st_tgt) r_shared2)
           (VALID: ✓ (r_shared2 ⋅ r_own ⋅ r_ctx2))
           im_tgt2
           (TGT: fair_update im_tgt1 im_tgt2 (prism_fmap inlp (tids_fmap tid ths))),
          exists im_src2, (<<SRC: fair_update im_src1 im_src2 (prism_fmap inlp (tids_fmap tid ths))>>) /\
                       (<<LSIM: forall fs ft,
                           lsim
                             tid
                             (@local_RR R0 R1 RR tid)
                             fs ft
                             r_ctx2
                             (o, src) tgt
                             (ths, im_src2, im_tgt2, st_src, st_tgt)
                             >>)).

  Definition local_sim_init {R0 R1} (RR: R0 -> R1 -> Prop) (r_own: (cmra_car M)) tid src tgt o :=
    forall ths im_src im_tgt st_src st_tgt r_shared r_ctx
      (INV: I (ths, im_src, im_tgt, st_src, st_tgt) r_shared)
      (VALID: ✓ (r_shared ⋅ r_own ⋅ r_ctx)),
    forall im_tgt1 (FAIR: fair_update im_tgt im_tgt1 (prism_fmap inlp (tids_fmap tid ths))),
    exists im_src1,
      (<<SRC: fair_update im_src im_src1 (prism_fmap inlp (tids_fmap tid ths))>>) /\
        forall fs ft,
          lsim
            tid
            (@local_RR R0 R1 RR tid)
            fs ft
            r_ctx
            (o, src) tgt
            (ths, im_src1, im_tgt1, st_src, st_tgt).

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

          world: ucmra;

          (* I: (@shared md_src.(Mod.state) md_tgt.(Mod.state) md_src.(Mod.ident) md_tgt.(Mod.ident) wf_src wf_tgt) -> world -> Prop; *)
          wf_stt : Type -> Type -> WF;
          init: forall im_tgt,
          exists (I: (@shared md_src.(Mod.state) md_tgt.(Mod.state) md_src.(Mod.ident) md_tgt.(Mod.ident) wf_src wf_tgt) -> world -> Prop),
          (exists im_src r_shared,
            (I (NatSet.empty, im_src, im_tgt, md_src.(Mod.st_init), md_tgt.(Mod.st_init)) r_shared) /\
              (✓ r_shared)) /\
              (forall fn args, match md_src.(Mod.funs) fn, md_tgt.(Mod.funs) fn with
                          | Some ktr_src, Some ktr_tgt => local_sim wf_stt I (@eq Any.t) (ktr_src args) (ktr_tgt args)
                          | None        , None         => True
                          | _           , _            => False
                          end);
        }.
  End MODSIM.
End ModSim.


From Fairness Require Import Concurrency.

Module UserSim.
  Section MODSIM.

    Variable md_src: Mod.t.
    Variable md_tgt: Mod.t.

    Record sim (p_src: Th.t _) (p_tgt: Th.t _) : Prop :=
      mk {
          wf_src : WF;
          wf_tgt : WF;
          wf_tgt_inhabited: inhabited wf_tgt.(T);
          wf_tgt_open: forall (o0: wf_tgt.(T)), exists o1, wf_tgt.(lt) o0 o1;

          world: ucmra;

          wf_stt : Type -> Type -> WF;
          funs: forall im_tgt,
          exists (I: (@shared md_src.(Mod.state) md_tgt.(Mod.state) md_src.(Mod.ident) md_tgt.(Mod.ident) wf_src wf_tgt) -> world -> Prop),
          exists im_src rs r_shared os,
            (<<INIT: I (key_set p_src, im_src, im_tgt, md_src.(Mod.st_init), md_tgt.(Mod.st_init)) r_shared>>) /\
              (<<SIM: Forall4
                        (fun '(t1, src) '(t2, tgt) '(t3, r) '(t4, o) =>
                           t1 = t2 /\ t1 = t3 /\ t1 = t4 /\
                             @local_sim_init _ md_src.(Mod.state) md_tgt.(Mod.state) md_src.(Mod.ident) md_tgt.(Mod.ident) wf_src wf_tgt wf_stt I _ _ (@eq Any.t) r t1 src tgt o)
                        (Th.elements p_src) (Th.elements p_tgt) (NatMap.elements rs) (NatMap.elements os)>>) /\
              (<<WF: ✓ (r_shared ⋅ NatMap.fold (fun _ r s => r ⋅ s) rs ε)>>)
        }.
  End MODSIM.
End UserSim.
