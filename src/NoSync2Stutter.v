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

  Let RR_rel (R0 R1: Type): Type := R0 -> R1 -> URA.car -> shared_rel.

  (* Let A (R0 R1: Type) (RR: RR_rel R0 R1) := (thread_id * M * (itree srcE R0) * (itree tgtE R1) * shared)%type. *)
  Let A := (URA.car * shared)%type.

  Inductive match_ord (R0 R1: Type) (RR: RR_rel R0 R1):
    thread_id -> URA.car -> (itree srcE R0) -> (itree tgtE R1) -> shared ->
    (@ord_tree_WF A).(T) -> Prop :=
  | match_ord_ret
      tid r_ctx shr
      o
      r0 r1
      (LSIM: RR r0 r1 r_ctx shr)
    :
    match_ord RR tid r_ctx (Ret r0) (Ret r1) shr o
  | match_ord_tauL
      tid r_ctx shr
      o
      itr_src itr_tgt
      (MO: match_ord RR tid r_ctx itr_src itr_tgt shr o)
    :
    match_ord RR tid r_ctx (Tau itr_src) itr_tgt shr o
  | match_ord_chooseL
      tid r_ctx shr
      o
      X ktr_src itr_tgt
      (MO: exists x, match_ord RR tid r_ctx (ktr_src x) itr_tgt shr o)
    :
    match_ord RR tid r_ctx (trigger (Choose X) >>= ktr_src) itr_tgt shr o
  | match_ord_putL
      tid r_ctx
      ths im_src im_tgt st_src st_tgt r_shared
      o
      st ktr_src itr_tgt
      (MO: match_ord RR tid r_ctx (ktr_src tt) itr_tgt (ths, im_src, im_tgt, st, st_tgt, r_shared) o)
    :
    match_ord RR tid r_ctx (trigger (Put st) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared) o
  | match_ord_getL
      tid r_ctx
      ths im_src im_tgt st_src st_tgt r_shared
      o
      ktr_src itr_tgt
      (MO: match_ord RR tid r_ctx (ktr_src st_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared) o)
    :
    match_ord RR tid r_ctx (trigger (@Get _) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared) o
  | match_ord_tidL
      tid r_ctx shr
      o
      ktr_src itr_tgt
      (MO: match_ord RR tid r_ctx (ktr_src tid) itr_tgt shr o)
    :
    match_ord RR tid r_ctx (trigger (GetTid) >>= ktr_src) itr_tgt shr o
  | match_ord_UB
      tid r_ctx shr
      o
      ktr_src itr_tgt
    :
    match_ord RR tid r_ctx (trigger (Undefined) >>= ktr_src) itr_tgt shr o
  | match_ord_fairL
      tid r_ctx
      ths im_src0 im_tgt st_src st_tgt r_shared
      o
      f ktr_src itr_tgt
      (MO: exists im_src1,
          (<<FAIR: fair_update im_src0 im_src1 (sum_fmap_r f)>>) /\
            (<<MO: match_ord RR tid r_ctx (ktr_src tt) itr_tgt (ths, im_src1, im_tgt, st_src, st_tgt, r_shared) o>>))
    :
    match_ord RR tid r_ctx (trigger (Fair f) >>= ktr_src) itr_tgt (ths, im_src0, im_tgt, st_src, st_tgt, r_shared) o

  | match_ord_tauR
      tid r_ctx shr
      o
      itr_src itr_tgt
      (MO: match_ord RR tid r_ctx itr_src itr_tgt shr o)
    :
    match_ord RR tid r_ctx itr_src (Tau itr_tgt) shr o
  | match_ord_chooseR
      tid r_ctx shr
      o
      X itr_src ktr_tgt
      (MO: forall x, match_ord RR tid r_ctx itr_src (ktr_tgt x) shr o)
    :
    match_ord RR tid r_ctx itr_src (trigger (Choose X) >>= ktr_tgt) shr o
  | match_ord_putR
      tid r_ctx
      ths im_src im_tgt st_src st_tgt r_shared
      o
      st itr_src ktr_tgt
      (MO: match_ord RR tid r_ctx itr_src (ktr_tgt tt) (ths, im_src, im_tgt, st_src, st, r_shared) o)
    :
    match_ord RR tid r_ctx itr_src (trigger (Put st) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared) o
  | match_ord_getR
      tid r_ctx
      ths im_src im_tgt st_src st_tgt r_shared
      o
      itr_src ktr_tgt
      (MO: match_ord RR tid r_ctx itr_src (ktr_tgt st_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared) o)
    :
    match_ord RR tid r_ctx itr_src (trigger (@Get _) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared) o
  | match_ord_tidR
      tid r_ctx shr
      o
      itr_src ktr_tgt
      (MO: match_ord RR tid r_ctx itr_src (ktr_tgt tid) shr o)
    :
    match_ord RR tid r_ctx itr_src (trigger (GetTid) >>= ktr_tgt) shr o
  | match_ord_fairR
      tid r_ctx
      ths im_src im_tgt0 st_src st_tgt r_shared
      o
      f itr_src ktr_tgt
      (MO: forall im_tgt1 (FAIR: fair_update im_tgt0 im_tgt1 (sum_fmap_r f)),
          match_ord RR tid r_ctx itr_src (ktr_tgt tt) (ths, im_src, im_tgt1, st_src, st_tgt, r_shared) o)
    :
    match_ord RR tid r_ctx itr_src (trigger (Fair f) >>= ktr_tgt) (ths, im_src, im_tgt0, st_src, st_tgt, r_shared) o

  | match_ord_observe
      tid r_ctx shr
      o
      fn args
      ktr_src ktr_tgt
      (MO: forall ret, match_ord RR tid r_ctx (ktr_src ret) (ktr_tgt ret) shr o)
    :
    match_ord RR tid r_ctx (trigger (Observe fn args) >>= ktr_src) (trigger (Observe fn args) >>= ktr_tgt) shr o

  | match_ord_yieldR
      tid r_ctx0 o0
      ths0 im_src0 im_tgt0 st_src0 st_tgt0 r_shared0
      r_own r_shared
      ktr_src ktr_tgt
      (INV: I (ths0, im_src0, im_tgt0, st_src0, st_tgt0, r_shared))
      (VALID: URA.wf (r_shared ⋅ r_own ⋅ r_ctx0))
      (MO: forall ths1 im_src1 im_tgt1 st_src1 st_tgt1 r_shared1 r_ctx1
             (INV: I (ths1, im_src1, im_tgt1, st_src1, st_tgt1, r_shared1))
             (VALID: URA.wf (r_shared1 ⋅ r_own ⋅ r_ctx1))
             im_tgt2
             (TGT: fair_update im_tgt1 im_tgt2 (sum_fmap_l (tids_fmap tid ths1))),
        exists o1,
          (<<MO: match_ord RR tid r_ctx1 ((trigger (Yield) >>= ktr_src)) (ktr_tgt tt) (ths1, im_src1, im_tgt2, st_src1, st_tgt1, r_shared1) o1>>) /\
            (<<STUTTER: (@ord_tree_WF A).(lt) o1 o0>>))
    :
    match_ord RR tid r_ctx0 (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt) (ths0, im_src0, im_tgt0, st_src0, st_tgt0, r_shared0) o0

  | match_ord_yieldL
      tid r_ctx
      ths im_src0 im_tgt st_src st_tgt r_shared
      o0
      ktr_src itr_tgt
      (MO: exists im_src1 o1,
          (<<FAIR: fair_update im_src0 im_src1 (sum_fmap_l (tids_fmap tid ths))>>) /\
            (<<MO: match_ord RR tid r_ctx (ktr_src tt) itr_tgt (ths, im_src1, im_tgt, st_src, st_tgt, r_shared) o1>>))
    :
    match_ord RR tid r_ctx (trigger (Yield) >>= ktr_src) itr_tgt (ths, im_src0, im_tgt, st_src, st_tgt, r_shared) o0
  .


  Theorem nosync_implies_stutter
          tid
          R0 R1 (RR: RR_rel R0 R1)
          ps pt r_ctx src tgt
          (shr: shared)
          (LSIM: ModSimNoSync.lsim I tid RR ps pt r_ctx src tgt shr)
    :
    exists o, ModSimStutter.lsim (@ord_tree_WF (A R0 R1)) I tid RR ps pt r_ctx (o, src) tgt shr.
  Proof.
    revert_until tid. pcofix CIH; i.
    punfold LSIM.
    pattern R0, R1, RR, ps, pt, r_ctx, src, tgt, shr.
    revert R0 R1 RR ps pt r_ctx src tgt shr LSIM. apply pind9_acc.
    intros rr DEC IH. clear DEC. intros R0 R1 RR ps pt r_ctx src tgt shr LSIM.
    eapply pind9_unfold in LSIM.
    2:{ eapply ModSimNoSync._lsim_mon. }
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
      right. eapply CIH; eauto.
    }

    { pfold. eapply pind9_fold. eapply ModSimNoSync.lsim_yieldL.
      des. esplits; eauto.
      split; ss. destruct LSIM as [LSIM IND]. eapply IH in IND. punfold IND.
    }

    { pfold. eapply pind9_fold. eapply ModSimNoSync.lsim_yieldR; eauto.
      i. specialize (LSIM0 _ _ _ _ _ _ _ INV0 VALID0 _ TGT).
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND.
    }

    { pfold. eapply pind9_fold. eapply ModSimNoSync.lsim_yieldR; eauto.
      i. specialize (LSIM0 _ _ _ _ _ _ _ INV0 VALID0 _ TGT).
      split; ss. eapply pind9_fold. eapply ModSimNoSync.lsim_yieldL.
      des. esplits. eapply FAIR. split; ss. pclearbot.
      eapply pind9_fold. eapply ModSimNoSync.lsim_progress. right.
      eapply CIH. apply ModSimStid.lsim_set_prog; auto.
    }

    { pfold. eapply pind9_fold. eapply ModSimNoSync.lsim_progress. right.
      eapply CIH. pclearbot. auto.
    }

  Qed.

End PROOF.

