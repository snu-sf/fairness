From sflib Require Import sflib.
From Paco Require Import paco.
Require Export Coq.Strings.String.
Require Import Coq.Classes.RelationClasses.

From Fairness Require Export ITreeLib FairBeh Mod.
From Fairness Require Import pind PCM WFLib.
From Fairness Require Import ModSim.

Set Implicit Arguments.



Section PRIMIVIESIM.
  Context `{M: URA.t}.

  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable ident_src: ID.
  Variable _ident_tgt: ID.
  Let ident_tgt := @ident_tgt _ident_tgt.

  Variable wf_src: WF.
  Variable wf_tgt: WF.

  Let srcE := ((@eventE ident_src +' cE) +' sE state_src).
  Let tgtE := ((@eventE _ident_tgt +' cE) +' sE state_tgt).

  Let shared := shared state_src state_tgt ident_src _ident_tgt wf_src wf_tgt.

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
          (<<FAIR: fair_update im_src0 im_src1 f>>) /\
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

  | lsim_yieldL
      f_src f_tgt r_ctx
      ths im_src im_tgt st_src st_tgt r_shared
      ktr_src itr_tgt
      (LSIM: _lsim _ _ RR true f_tgt r_ctx (ktr_src tt) (trigger (Yield) >>= itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
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
  | lsim_sync
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
          (<<LSIM: _lsim _ _ RR true true r_ctx1 (ktr_src tt) (ktr_tgt tt) (ths1, im_src1, im_tgt2, st_src1, st_tgt1, r_shared1)>>))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx0 (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt) (ths0, im_src0, im_tgt0, st_src0, st_tgt0, r_shared0)

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
    { eapply lsim_sync; eauto. i. eapply LE. eapply LSIM; eauto. }
  Qed.

  Lemma lsim_mon tid: forall q, monotone9 (fun r => pind9 (__lsim tid r) q).
  Proof.
    ii. eapply pind9_mon_gen; eauto.
    ii. eapply __lsim_mon; eauto.
  Qed.

  Local Hint Constructors __lsim: core.
  Local Hint Unfold lsim: core.
  Local Hint Resolve __lsim_mon: paco.
  Local Hint Resolve _lsim_mon: paco.
  Local Hint Resolve lsim_mon: paco.

  Lemma modsim_implies_gensim
        tid
        R0 R1 (RR: R0 -> R1 -> URA.car -> shared_rel)
        ps pt r_ctx src tgt
        (shr: shared)
        (LSIM: ModSim.lsim I tid RR ps pt r_ctx src tgt shr)
    :
    lsim tid RR ps pt r_ctx src tgt shr.
  Proof.
    revert_until tid. pcofix CIH; i.
    punfold LSIM.
    pattern R0, R1, RR, ps, pt, r_ctx, src, tgt, shr.
    revert R0 R1 RR ps pt r_ctx src tgt shr LSIM. apply pind9_acc.
    intros rr DEC IH. clear DEC. intros R0 R1 RR ps pt r_ctx src tgt shr LSIM.
    eapply pind9_unfold in LSIM.
    2:{ eapply ModSim._lsim_mon. }
    inv LSIM.

    { pfold. eapply pind9_fold. econs 1; eauto. }
    { pfold. eapply pind9_fold. econs 2; eauto.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 3; eauto.
      des. exists x.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 4; eauto.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 5; eauto.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 6; eauto.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 7; eauto. }
    { pfold. eapply pind9_fold. econs 8; eauto.
      des. esplits; eauto.
      split; ss. destruct LSIM as [LSIM IND]. eapply IH in IND. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 9; eauto.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 10; eauto.
      i. specialize (LSIM0 x).
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 11; eauto.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 12; eauto.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 13; eauto.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 14; eauto.
      i. specialize (LSIM0 _ FAIR).
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND.
    }

    { pfold. eapply pind9_fold. econs 15; eauto.
      i. specialize (LSIM0 ret). pclearbot.
      split; ss. eapply pind9_fold. eapply lsim_progress.
      right. eapply CIH; eauto. eapply ModSim.lsim_set_prog. auto.
    }

    { pfold. eapply pind9_fold. eapply lsim_yieldL.
      des. esplits; eauto.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND.
    }

    { pfold. eapply pind9_fold. eapply lsim_yieldR; eauto.
      i. specialize (LSIM0 _ _ _ _ _ _ _ INV0 VALID0 _ TGT).
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND.
    }

    { pfold. eapply pind9_fold. eapply lsim_sync; eauto.
      i. specialize (LSIM0 _ _ _ _ _ _ _ INV0 VALID0 _ TGT).
      split; ss. eapply pind9_fold. eapply lsim_progress. pclearbot.
      right. eapply CIH. apply ModSim.lsim_set_prog; auto.
    }

    { pfold. eapply pind9_fold. eapply lsim_progress. right.
      eapply CIH. pclearbot. auto.
    }

  Qed.

End PRIMIVIESIM.
#[export] Hint Constructors __lsim: core.
#[export] Hint Unfold lsim: core.
#[export] Hint Resolve __lsim_mon: paco.
#[export] Hint Resolve _lsim_mon: paco.
#[export] Hint Resolve lsim_mon: paco.

Section GENORDER.
  Context `{M: URA.t}.

  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable ident_src: ID.
  Variable _ident_tgt: ID.
  Let ident_tgt := @ident_tgt _ident_tgt.

  Variable wf_src: WF.
  Variable wf_tgt: WF.

  Let srcE := ((@eventE ident_src +' cE) +' sE state_src).
  Let tgtE := ((@eventE _ident_tgt +' cE) +' sE state_tgt).

  Let shared := shared state_src state_tgt ident_src _ident_tgt wf_src wf_tgt.
  Let shared_rel: Type := shared -> Prop.
  Variable I: shared_rel.

  Let A R0 R1 := (bool * bool * URA.car * (itree srcE R0) * (itree tgtE R1) * shared)%type.
  Let wf_stt R0 R1 := @ord_tree_WF (A R0 R1).

  Variant _genos
          (tid: thread_id)
          (genos: forall R0 R1 (RR: R0 -> R1 -> URA.car -> shared_rel), bool -> bool -> URA.car -> ((wf_stt R0 R1).(T) * itree srcE R0) -> ((wf_stt R0 R1).(T) * itree tgtE R1) -> shared_rel)
          R0 R1 (RR: R0 -> R1 -> URA.car -> shared_rel)
    :
    bool -> bool -> URA.car -> ((wf_stt R0 R1).(T) * itree srcE R0) -> ((wf_stt R0 R1).(T) * itree tgtE R1) -> shared_rel :=
  | genos_ret
      f_src f_tgt r_ctx os ot
      ths im_src im_tgt st_src st_tgt r_shared
      r_src r_tgt
      (GENOS: RR r_src r_tgt r_ctx (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    _genos tid genos RR f_src f_tgt r_ctx (os, Ret r_src) (ot, Ret r_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)

  | genos_tauL
      f_src f_tgt r_ctx os ot
      ths im_src im_tgt st_src st_tgt r_shared
      itr_src itr_tgt
      (GENOS: genos _ _ RR true f_tgt r_ctx (os, itr_src) (ot, itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    _genos tid genos RR f_src f_tgt r_ctx (os, Tau itr_src) (ot, itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | genos_chooseL
      f_src f_tgt r_ctx os ot
      ths im_src im_tgt st_src st_tgt r_shared
      X ktr_src itr_tgt
      (GENOS: exists x, genos _ _ RR true f_tgt r_ctx (os, ktr_src x) (ot, itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    _genos tid genos RR f_src f_tgt r_ctx (os, trigger (Choose X) >>= ktr_src) (ot, itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | genos_putL
      f_src f_tgt r_ctx os ot
      ths im_src im_tgt st_src st_tgt r_shared
      st ktr_src itr_tgt
      (GENOS: genos _ _ RR true f_tgt r_ctx (os, ktr_src tt) (ot, itr_tgt) (ths, im_src, im_tgt, st, st_tgt, r_shared))
    :
    _genos tid genos RR f_src f_tgt r_ctx (os, trigger (Put st) >>= ktr_src) (ot, itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | genos_getL
      f_src f_tgt r_ctx os ot
      ths im_src im_tgt st_src st_tgt r_shared
      ktr_src itr_tgt
      (GENOS: genos _ _ RR true f_tgt r_ctx (os, ktr_src st_src) (ot, itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    _genos tid genos RR f_src f_tgt r_ctx (os, trigger (@Get _) >>= ktr_src) (ot, itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | genos_tidL
      f_src f_tgt r_ctx os ot
      ths im_src im_tgt st_src st_tgt r_shared
      ktr_src itr_tgt
      (GENOS: genos _ _ RR true f_tgt r_ctx (os, ktr_src tid) (ot, itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    _genos tid genos RR f_src f_tgt r_ctx (os, trigger (GetTid) >>= ktr_src) (ot, itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | genos_UB
      f_src f_tgt r_ctx os ot
      ths im_src im_tgt st_src st_tgt r_shared
      ktr_src itr_tgt
    :
    _genos tid genos RR f_src f_tgt r_ctx (os, trigger (Undefined) >>= ktr_src) (ot, itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | genos_fairL
      f_src f_tgt r_ctx os ot
      ths im_src0 im_tgt st_src st_tgt r_shared
      f ktr_src itr_tgt
      (GENOS: exists im_src1,
          (<<FAIR: fair_update im_src0 im_src1 f>>) /\
            (<<GENOS: genos _ _ RR true f_tgt r_ctx (os, ktr_src tt) (ot, itr_tgt) (ths, im_src1, im_tgt, st_src, st_tgt, r_shared)>>))
    :
    _genos tid genos RR f_src f_tgt r_ctx (os, trigger (Fair f) >>= ktr_src) (ot, itr_tgt) (ths, im_src0, im_tgt, st_src, st_tgt, r_shared)

  | genos_tauR
      f_src f_tgt r_ctx os ot
      ths im_src im_tgt st_src st_tgt r_shared
      itr_src itr_tgt
      (GENOS: genos _ _ RR f_src true r_ctx (os, itr_src) (ot, itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    _genos tid genos RR f_src f_tgt r_ctx (os, itr_src) (ot, Tau itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | genos_chooseR
      f_src f_tgt r_ctx os ot
      ths im_src im_tgt st_src st_tgt r_shared
      X itr_src ktr_tgt
      (GENOS: forall x, genos _ _ RR f_src true r_ctx (os, itr_src) (ot, ktr_tgt x) (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    _genos tid genos RR f_src f_tgt r_ctx (os, itr_src) (ot, trigger (Choose X) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | genos_putR
      f_src f_tgt r_ctx os ot
      ths im_src im_tgt st_src st_tgt r_shared
      st itr_src ktr_tgt
      (GENOS: genos _ _ RR f_src true r_ctx (os, itr_src) (ot, ktr_tgt tt) (ths, im_src, im_tgt, st_src, st, r_shared))
    :
    _genos tid genos RR f_src f_tgt r_ctx (os, itr_src) (ot, trigger (Put st) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | genos_getR
      f_src f_tgt r_ctx os ot
      ths im_src im_tgt st_src st_tgt r_shared
      itr_src ktr_tgt
      (GENOS: genos _ _ RR f_src true r_ctx (os, itr_src) (ot, ktr_tgt st_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    _genos tid genos RR f_src f_tgt r_ctx (os, itr_src) (ot, trigger (@Get _) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | genos_tidR
      f_src f_tgt r_ctx os ot
      ths im_src im_tgt st_src st_tgt r_shared
      itr_src ktr_tgt
      (GENOS: genos _ _ RR f_src true r_ctx (os, itr_src) (ot, ktr_tgt tid) (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    _genos tid genos RR f_src f_tgt r_ctx (os, itr_src) (ot, trigger (GetTid) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | genos_fairR
      f_src f_tgt r_ctx os ot
      ths im_src im_tgt0 st_src st_tgt r_shared
      f itr_src ktr_tgt
      (GENOS: forall im_tgt1 (FAIR: fair_update im_tgt0 im_tgt1 (sum_fmap_r f)),
          (<<GENOS: genos _ _ RR f_src true r_ctx (os, itr_src) (ot, ktr_tgt tt) (ths, im_src, im_tgt1, st_src, st_tgt, r_shared)>>))
    :
    _genos tid genos RR f_src f_tgt r_ctx (os, itr_src) (ot, trigger (Fair f) >>= ktr_tgt) (ths, im_src, im_tgt0, st_src, st_tgt, r_shared)

  | genos_observe
      f_src f_tgt r_ctx os ot
      ths im_src im_tgt st_src st_tgt r_shared
      fn args ktr_src ktr_tgt
      (GENOS: forall ret,
          genos _ _ RR true true r_ctx (os, ktr_src ret) (ot, ktr_tgt ret) (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    _genos tid genos RR f_src f_tgt r_ctx (os, trigger (Observe fn args) >>= ktr_src) (ot, trigger (Observe fn args) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)

  | genos_yieldL
      f_src f_tgt r_ctx os ot
      ths im_src im_tgt st_src st_tgt r_shared
      ktr_src itr_tgt
      (GENOS: exists os1 ot1,
          (<<GENOS: genos _ _ RR true f_tgt r_ctx (os1, ktr_src tt) (ot1, trigger (Yield) >>= itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)>>) /\
            (<<LT: (wf_stt R0 R1).(lt) os1 os>>))
    :
    _genos tid genos RR f_src f_tgt r_ctx (os, trigger (Yield) >>= ktr_src) (ot, trigger (Yield) >>= itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | genos_yieldR
      f_src f_tgt r_ctx0 os ot
      ths0 im_src0 im_tgt0 st_src0 st_tgt0 r_shared0
      r_own r_shared
      ktr_src ktr_tgt
      (INV: I (ths0, im_src0, im_tgt0, st_src0, st_tgt0, r_shared))
      (VALID: URA.wf (r_shared ⋅ r_own ⋅ r_ctx0))
      (GENOS: forall ths1 im_src1 im_tgt1 st_src1 st_tgt1 r_shared1 r_ctx1
               (INV: I (ths1, im_src1, im_tgt1, st_src1, st_tgt1, r_shared1))
               (VALID: URA.wf (r_shared1 ⋅ r_own ⋅ r_ctx1))
               im_tgt2
               (TGT: fair_update im_tgt1 im_tgt2 (sum_fmap_l (tids_fmap tid ths1))),
        exists os1 ot1,
          (<<GENOS: genos _ _ RR f_src true r_ctx1 (os1, trigger (Yield) >>= ktr_src) (ot1, ktr_tgt tt) (ths1, im_src1, im_tgt2, st_src1, st_tgt1, r_shared1)>>) /\
            (<<LT: (wf_stt R0 R1).(lt) ot1 ot>>))
    :
    _genos tid genos RR f_src f_tgt r_ctx0 (os, trigger (Yield) >>= ktr_src) (ot, trigger (Yield) >>= ktr_tgt) (ths0, im_src0, im_tgt0, st_src0, st_tgt0, r_shared0)
  | genos_sync
      f_src f_tgt r_ctx0 os ot
      ths0 im_src0 im_tgt0 st_src0 st_tgt0 r_shared0
      r_own r_shared
      ktr_src ktr_tgt
      (INV: I (ths0, im_src0, im_tgt0, st_src0, st_tgt0, r_shared))
      (VALID: URA.wf (r_shared ⋅ r_own ⋅ r_ctx0))
      (GENOS: forall ths1 im_src1 im_tgt1 st_src1 st_tgt1 r_shared1 r_ctx1
               (INV: I (ths1, im_src1, im_tgt1, st_src1, st_tgt1, r_shared1))
               (VALID: URA.wf (r_shared1 ⋅ r_own ⋅ r_ctx1))
               im_tgt2
               (TGT: fair_update im_tgt1 im_tgt2 (sum_fmap_l (tids_fmap tid ths1))),
        exists os1 ot1,
          (<<GENOS: genos _ _ RR true true r_ctx1 (os1, ktr_src tt) (ot1, ktr_tgt tt) (ths1, im_src1, im_tgt2, st_src1, st_tgt1, r_shared1)>>))
    :
    _genos tid genos RR f_src f_tgt r_ctx0 (os, trigger (Yield) >>= ktr_src) (ot, trigger (Yield) >>= ktr_tgt) (ths0, im_src0, im_tgt0, st_src0, st_tgt0, r_shared0)

  | genos_progress
      r_ctx os ot
      ths im_src im_tgt st_src st_tgt r_shared
      itr_src itr_tgt
      (GENOS: lsim I tid RR false false r_ctx (itr_src) (itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    _genos tid genos RR true true r_ctx (os, itr_src) (ot, itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  .

  Definition genos (tid: thread_id)
             R0 R1 (RR: R0 -> R1 -> URA.car -> shared_rel):
    bool -> bool -> URA.car -> ((wf_stt R0 R1).(T) * itree srcE R0) -> ((wf_stt R0 R1).(T) * itree tgtE R1) -> shared_rel :=
    pind9 (_genos tid) top9 R0 R1 RR.

  Lemma genos_mon tid: monotone9 (_genos tid).
  Proof.
    ii. inv IN; try (econs; eauto; fail).
    { des. econs; eauto. }
    { des. econs; eauto. }
    { econs. i. eapply LE. eapply GENOS. eauto. }
    { des. econs; eauto. esplits; eauto. }
    { eapply genos_yieldR; eauto. i. hexploit GENOS; eauto. i. des. esplits; eauto. }
    { eapply genos_sync; eauto. i. hexploit GENOS; eauto. i. des. esplits; eauto. }
  Qed.

  Local Hint Constructors _genos: core.
  Local Hint Unfold genos: core.
  Local Hint Resolve genos_mon: paco.


  Lemma genos_ord_weakL
        tid R0 R1 (LRR: R0 -> R1 -> URA.car -> shared_rel)
        ps pt r_ctx src tgt (shr: shared)
        os0 os1
        (LT: (wf_stt R0 R1).(lt) os0 os1)
        (GENOS: genos tid LRR ps pt r_ctx (os0, src) tgt shr)
    :
    genos tid LRR ps pt r_ctx (os1, src) tgt shr.
  Proof.
    remember (os0, src) as osrc.
    move GENOS before tid. revert_until GENOS.
    pattern R0, R1, LRR, ps, pt, r_ctx, osrc, tgt, shr.
    revert R0 R1 LRR ps pt r_ctx osrc tgt shr GENOS. apply pind9_acc.
    intros rr DEC IH. clear DEC. intros R0 R1 LRR ps pt r_ctx osrc tgt shr GENOS.
    i; clarify.
    eapply pind9_unfold in GENOS; eauto with paco.
    inv GENOS.

    { eapply pind9_fold. econs 1; eauto. }
    { eapply pind9_fold. econs 2; eauto.
      destruct GENOS0 as [GENOS IND]. eapply IH in IND; eauto. split; ss.
    }
    { eapply pind9_fold. econs 3; eauto.
      des. destruct GENOS0 as [GENOS IND]. eapply IH in IND; eauto. esplits; eauto.
      split; ss; eauto.
    }
    { eapply pind9_fold. econs 4; eauto.
      destruct GENOS0 as [GENOS IND]. eapply IH in IND; eauto. split; ss.
    }
    { eapply pind9_fold. econs 5; eauto.
      destruct GENOS0 as [GENOS IND]. eapply IH in IND; eauto. split; ss.
    }
    { eapply pind9_fold. econs 6; eauto.
      destruct GENOS0 as [GENOS IND]. eapply IH in IND; eauto. split; ss.
    }
    { eapply pind9_fold. econs 7; eauto. }
    { eapply pind9_fold. econs 8; eauto.
      des. destruct GENOS as [GENOS IND]. eapply IH in IND; eauto. esplits; eauto.
      split; ss; eauto.
    }

    { eapply pind9_fold. econs 9; eauto.
      destruct GENOS0 as [GENOS IND]. eapply IH in IND; eauto. split; ss.
    }
    { eapply pind9_fold. econs 10; eauto.
      i. specialize (GENOS0 x).
      destruct GENOS0 as [GENOS IND]. eapply IH in IND; eauto. split; ss.
    }
    { eapply pind9_fold. econs 11; eauto.
      destruct GENOS0 as [GENOS IND]. eapply IH in IND; eauto. split; ss.
    }
    { eapply pind9_fold. econs 12; eauto.
      destruct GENOS0 as [GENOS IND]. eapply IH in IND; eauto. split; ss.
    }
    { eapply pind9_fold. econs 13; eauto.
      destruct GENOS0 as [GENOS IND]. eapply IH in IND; eauto. split; ss.
    }
    { eapply pind9_fold. econs 14; eauto.
      i. specialize (GENOS0 _ FAIR).
      destruct GENOS0 as [GENOS IND]. eapply IH in IND; eauto. split; ss.
    }
    { eapply pind9_fold. econs 15; eauto.
      i. specialize (GENOS0 ret).
      destruct GENOS0 as [GENOS IND]. eapply IH in IND; eauto. split; ss.
    }

    { eapply pind9_fold. econs 16; eauto.
      des. destruct GENOS as [GENOS IND]. eapply IH in IND; eauto.
      esplits. split; ss. eapply IND. auto.
    }

    { eapply pind9_fold. econs 17; eauto.
      i. specialize (GENOS0 _ _ _ _ _ _ _ INV0 VALID0 _ TGT). des. esplits; eauto.
      eapply upind9_mon; eauto. ss.
    }

    { eapply pind9_fold. econs 18; eauto.
      i. specialize (GENOS0 _ _ _ _ _ _ _ INV0 VALID0 _ TGT). des. esplits; eauto.
      eapply upind9_mon; eauto. ss.
    }

    { eapply pind9_fold. econs 19; eauto. }

  Qed.

  Lemma genos_ord_weakR
        tid R0 R1 (LRR: R0 -> R1 -> URA.car -> shared_rel)
        ps pt r_ctx src tgt (shr: shared)
        ot0 ot1
        (LT: (wf_stt R0 R1).(lt) ot0 ot1)
        (GENOS: genos tid LRR ps pt r_ctx src (ot0, tgt) shr)
    :
    genos tid LRR ps pt r_ctx src (ot1, tgt) shr.
  Proof.
    remember (ot0, tgt) as otgt.
    move GENOS before tid. revert_until GENOS.
    pattern R0, R1, LRR, ps, pt, r_ctx, src, otgt, shr.
    revert R0 R1 LRR ps pt r_ctx src otgt shr GENOS. apply pind9_acc.
    intros rr DEC IH. clear DEC. intros R0 R1 LRR ps pt r_ctx src otgt shr GENOS.
    i; clarify.
    eapply pind9_unfold in GENOS; eauto with paco.
    inv GENOS.

    { eapply pind9_fold. econs 1; eauto. }
    { eapply pind9_fold. econs 2; eauto.
      destruct GENOS0 as [GENOS IND]. eapply IH in IND; eauto. split; ss.
    }
    { eapply pind9_fold. econs 3; eauto.
      des. destruct GENOS0 as [GENOS IND]. eapply IH in IND; eauto. esplits; eauto.
      split; ss; eauto.
    }
    { eapply pind9_fold. econs 4; eauto.
      destruct GENOS0 as [GENOS IND]. eapply IH in IND; eauto. split; ss.
    }
    { eapply pind9_fold. econs 5; eauto.
      destruct GENOS0 as [GENOS IND]. eapply IH in IND; eauto. split; ss.
    }
    { eapply pind9_fold. econs 6; eauto.
      destruct GENOS0 as [GENOS IND]. eapply IH in IND; eauto. split; ss.
    }
    { eapply pind9_fold. econs 7; eauto. }
    { eapply pind9_fold. econs 8; eauto.
      des. destruct GENOS as [GENOS IND]. eapply IH in IND; eauto. esplits; eauto.
      split; ss; eauto.
    }

    { eapply pind9_fold. econs 9; eauto.
      destruct GENOS0 as [GENOS IND]. eapply IH in IND; eauto. split; ss.
    }
    { eapply pind9_fold. econs 10; eauto.
      i. specialize (GENOS0 x).
      destruct GENOS0 as [GENOS IND]. eapply IH in IND; eauto. split; ss.
    }
    { eapply pind9_fold. econs 11; eauto.
      destruct GENOS0 as [GENOS IND]. eapply IH in IND; eauto. split; ss.
    }
    { eapply pind9_fold. econs 12; eauto.
      destruct GENOS0 as [GENOS IND]. eapply IH in IND; eauto. split; ss.
    }
    { eapply pind9_fold. econs 13; eauto.
      destruct GENOS0 as [GENOS IND]. eapply IH in IND; eauto. split; ss.
    }
    { eapply pind9_fold. econs 14; eauto.
      i. specialize (GENOS0 _ FAIR).
      destruct GENOS0 as [GENOS IND]. eapply IH in IND; eauto. split; ss.
    }
    { eapply pind9_fold. econs 15; eauto.
      i. specialize (GENOS0 ret).
      destruct GENOS0 as [GENOS IND]. eapply IH in IND; eauto. split; ss.
    }

    { eapply pind9_fold. econs 16; eauto.
      des. esplits; eauto.
      eapply upind9_mon; eauto. ss.
    }

    { eapply pind9_fold. econs 17; eauto.
      i. specialize (GENOS0 _ _ _ _ _ _ _ INV0 VALID0 _ TGT). des.
      destruct GENOS as [GENOS IND]. eapply IH in IND; eauto.
      esplits; eauto. split; ss. eauto.
    }

    { eapply pind9_fold. econs 18; eauto.
      i. specialize (GENOS0 _ _ _ _ _ _ _ INV0 VALID0 _ TGT). des. esplits; eauto.
      eapply upind9_mon; eauto. ss.
    }

    { eapply pind9_fold. econs 19; eauto. }

  Qed.

  Lemma modsim_genos
        tid R0 R1 (RR: R0 -> R1 -> URA.car -> shared_rel)
        ps pt r_ctx src tgt shr
        (LSIM: ModSim.lsim I tid RR ps pt r_ctx src tgt shr)
    :
    exists os ot, genos tid RR ps pt r_ctx (os, src) (ot, tgt) shr.
  Proof.
    eapply modsim_implies_gensim in LSIM.
    punfold LSIM.
    pattern R0, R1, RR, ps, pt, r_ctx, src, tgt, shr.
    revert R0 R1 RR ps pt r_ctx src tgt shr LSIM. apply pind9_acc.
    intros rr DEC IH. clear DEC. intros R0 R1 RR ps pt r_ctx src tgt shr LSIM.
    eapply pind9_unfold in LSIM; eauto with paco.
    set (zero:= @ord_tree_base (A R0 R1)). set (fzero:= fun _: (A R0 R1) => zero). set (one:= ord_tree_cons fzero).
    inv LSIM.

    { exists zero, zero. eapply pind9_fold. econs 1; eauto. }

    { destruct LSIM0 as [LSIM IND]. eapply IH in IND. des.
      exists os, ot. eapply pind9_fold. econs 2; eauto. split; ss.
    }
    { des. destruct LSIM0 as [LSIM IND]. eapply IH in IND. des.
      exists os, ot. eapply pind9_fold. econs 3; eauto. eexists. split; ss. eauto.
    }
    { destruct LSIM0 as [LSIM IND]. eapply IH in IND. des.
      exists os, ot. eapply pind9_fold. econs 4; eauto. split; ss.
    }
    { destruct LSIM0 as [LSIM IND]. eapply IH in IND. des.
      exists os, ot. eapply pind9_fold. econs 5; auto. split; ss.
    }
    { destruct LSIM0 as [LSIM IND]. eapply IH in IND. des.
      exists os, ot. eapply pind9_fold. econs 6; auto. split; ss.
    }
    { exists zero, zero. eapply pind9_fold. econs 7; eauto. }
    { des. destruct LSIM as [LSIM IND]. eapply IH in IND. des.
      exists os, ot. eapply pind9_fold. econs 8; eauto. esplits; eauto. split; ss.
    }

    { destruct LSIM0 as [LSIM IND]. eapply IH in IND. des. exists os, ot.
      eapply pind9_fold. econs 9; eauto. ss.
    }

    { hexploit ord_tree_join.
      { instantiate (2:=A R0 R1).
        instantiate (2:= fun '(ps, pt, rs, src, tgt, shr) => @rr R0 R1 RR ps pt rs src tgt shr).
        i. ss. des_ifs. eapply IH in SAT.
        instantiate (1:= fun '(ps, pt, rs, src, tgt, shr) o =>
                           exists ot, genos tid RR ps pt rs (o, src) (ot, tgt) shr).
        eauto.
      }
      intro JOIN1. des. exists o1.
      hexploit ord_tree_join.
      { instantiate (2:=A R0 R1).
        instantiate (2:= fun '(ps, pt, rs, src, tgt, shr) => @rr R0 R1 RR ps pt rs src tgt shr).
        i. ss. des_ifs. 
        specialize (JOIN1 (b, b0, c, i0, i, s)). destruct JOIN1; auto. des.
        instantiate (1:= fun '(ps, pt, rs, src, tgt, shr) o =>
                           genos tid RR ps pt rs (o1, src) (o, tgt) shr).
        exists ot. eapply genos_ord_weakL; eauto.
      }
      intro JOIN2. des. exists o0.
      eapply pind9_fold. econs 10.
      i. specialize (LSIM0 x). destruct LSIM0 as [LSIM IND].
      specialize (JOIN1 (ps, true, r_ctx, src, (ktr_tgt x), (ths, im_src, im_tgt, st_src, st_tgt, r_shared))).
      destruct JOIN1; auto. des.
      specialize (JOIN2 (ps, true, r_ctx, src, (ktr_tgt x), (ths, im_src, im_tgt, st_src, st_tgt, r_shared))).
      destruct JOIN2; auto. des.
      split; ss.
      eapply genos_ord_weakR; eauto.
    }

    { destruct LSIM0 as [LSIM IND]. eapply IH in IND. des. exists os, ot.
      eapply pind9_fold. econs 11; eauto. ss.
    }
    { destruct LSIM0 as [LSIM IND]. eapply IH in IND. des. exists os, ot.
      eapply pind9_fold. econs 12; eauto. ss.
    }
    { destruct LSIM0 as [LSIM IND]. eapply IH in IND. des. exists os, ot.
      eapply pind9_fold. econs 13; eauto. ss.
    }

    { hexploit ord_tree_join.
      { instantiate (2:=A R0 R1).
        instantiate (2:= fun '(ps, pt, rs, src, tgt, shr) => @rr R0 R1 RR ps pt rs src tgt shr).
        i. ss. des_ifs. eapply IH in SAT.
        instantiate (1:= fun '(ps, pt, rs, src, tgt, shr) o =>
                           exists ot, genos tid RR ps pt rs (o, src) (ot, tgt) shr).
        eauto.
      }
      intro JOIN1. des. exists o1.
      hexploit ord_tree_join.
      { instantiate (2:=A R0 R1).
        instantiate (2:= fun '(ps, pt, rs, src, tgt, shr) => @rr R0 R1 RR ps pt rs src tgt shr).
        i. ss. des_ifs. 
        specialize (JOIN1 (b, b0, c, i0, i, s)). destruct JOIN1; auto. des.
        instantiate (1:= fun '(ps, pt, rs, src, tgt, shr) o =>
                           genos tid RR ps pt rs (o1, src) (o, tgt) shr).
        exists ot. eapply genos_ord_weakL; eauto.
      }
      intro JOIN2. des. exists o0.
      eapply pind9_fold. econs 14.
      i. specialize (LSIM0 _ FAIR). destruct LSIM0 as [LSIM IND].
      specialize (JOIN1 (ps, true, r_ctx, src, (ktr_tgt tt), (ths, im_src, im_tgt1, st_src, st_tgt, r_shared))).
      destruct JOIN1; auto. des.
      specialize (JOIN2 (ps, true, r_ctx, src, (ktr_tgt tt), (ths, im_src, im_tgt1, st_src, st_tgt, r_shared))).
      destruct JOIN2; auto. des.
      split; ss.
      eapply genos_ord_weakR; eauto.
    }

    { hexploit ord_tree_join.
      { instantiate (2:=A R0 R1).
        instantiate (2:= fun '(ps, pt, rs, src, tgt, shr) => @rr R0 R1 RR ps pt rs src tgt shr).
        i. ss. des_ifs. eapply IH in SAT.
        instantiate (1:= fun '(ps, pt, rs, src, tgt, shr) o =>
                           exists ot, genos tid RR ps pt rs (o, src) (ot, tgt) shr).
        eauto.
      }
      intro JOIN1. des. exists o1.
      hexploit ord_tree_join.
      { instantiate (2:=A R0 R1).
        instantiate (2:= fun '(ps, pt, rs, src, tgt, shr) => @rr R0 R1 RR ps pt rs src tgt shr).
        i. ss. des_ifs. 
        specialize (JOIN1 (b, b0, c, i0, i, s)). destruct JOIN1; auto. des.
        instantiate (1:= fun '(ps, pt, rs, src, tgt, shr) o =>
                           genos tid RR ps pt rs (o1, src) (o, tgt) shr).
        exists ot. eapply genos_ord_weakL; eauto.
      }
      intro JOIN2. des. exists o0.
      eapply pind9_fold. econs 15.
      i. specialize (LSIM0 ret). destruct LSIM0 as [LSIM IND].
      specialize (JOIN1 (true, true, r_ctx, (ktr_src ret), (ktr_tgt ret), (ths, im_src, im_tgt, st_src, st_tgt, r_shared))).
      destruct JOIN1; auto. des.
      specialize (JOIN2 (true, true, r_ctx, (ktr_src ret), (ktr_tgt ret), (ths, im_src, im_tgt, st_src, st_tgt, r_shared))).
      destruct JOIN2; auto. des.
      split; ss.
      eapply genos_ord_weakR; eauto.
    }

    { destruct LSIM0 as [LSIM IND]. eapply IH in IND. des.
      set (fos:= fun _: (A R0 R1) => os). exists (ord_tree_cons fos), ot.
      eapply pind9_fold. econs 16; eauto. esplits; eauto.
      split; ss. eauto. ss.
      replace os with (fos (true, pt, r_ctx, (ktr_src tt), (x <- trigger Yield;; itr_tgt x), (ths, im_src, im_tgt, st_src, st_tgt, r_shared))); ss.
    }

    { hexploit ord_tree_join.
      { instantiate (2:=A R0 R1).
        instantiate (2:= fun '(ps, pt, rs, src, tgt, shr) => @rr R0 R1 RR ps pt rs src tgt shr).
        i. ss. des_ifs. eapply IH in SAT.
        instantiate (1:= fun '(ps, pt, rs, src, tgt, shr) o =>
                           exists ot, genos tid RR ps pt rs (o, src) (ot, tgt) shr).
        eauto.
      }
      intro JOIN1. des. exists o1.
      hexploit ord_tree_join.
      { instantiate (2:=A R0 R1).
        instantiate (2:= fun '(ps, pt, rs, src, tgt, shr) => @rr R0 R1 RR ps pt rs src tgt shr).
        i. ss. des_ifs. 
        specialize (JOIN1 (b, b0, c, i0, i, s)). destruct JOIN1; auto. des.
        instantiate (1:= fun '(ps, pt, rs, src, tgt, shr) o =>
                           genos tid RR ps pt rs (o1, src) (o, tgt) shr).
        exists ot. eapply genos_ord_weakL; eauto.
      }
      intro JOIN2. des. exists o0.
      eapply pind9_fold. econs 17. 1,2: eauto.
      i. specialize (LSIM0 _ _ _ _ _ _ _ INV0 VALID0 _ TGT). destruct LSIM0 as [LSIM IND].
      specialize (JOIN1 (ps, true, r_ctx1, (x <- trigger Yield;; ktr_src x), ktr_tgt tt, (ths1, im_src1, im_tgt2, st_src1, st_tgt1, r_shared1))).
      destruct JOIN1; auto. des.
      specialize (JOIN2 (ps, true, r_ctx1, (x <- trigger Yield;; ktr_src x), ktr_tgt tt, (ths1, im_src1, im_tgt2, st_src1, st_tgt1, r_shared1))).
      destruct JOIN2; auto. des.
      exists o1, x0. esplits; eauto.
      split; ss.
    }

    { exists zero, zero. eapply pind9_fold. econs 18; eauto.
      i. specialize (LSIM0 _ _ _ _ _ _ _ INV0 VALID0 _ TGT). destruct LSIM0 as [LSIM IND].
      eapply IH in IND. des. do 2 eexists. split; ss. eapply IND.
    }

    { exists zero, zero. eapply pind9_fold. econs 19. pclearbot. auto. }

  Qed.

End GENORDER.
#[export] Hint Constructors _genos: core.
#[export] Hint Unfold genos: core.
#[export] Hint Resolve genos_mon: paco.
