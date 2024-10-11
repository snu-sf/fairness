From sflib Require Import sflib.
From Paco Require Import paco.
From Paco Require pacotac_internal.

From iris.algebra Require Import cmra updates.
Require Export Coq.Strings.String.
Require Import Coq.Classes.RelationClasses.

From Fairness Require Export ITreeLib FairBeh Mod.
From Fairness Require Import pind.
From Fairness Require Import PCM.
From Fairness Require Import PindTac.

Set Implicit Arguments.



Section PRIMIVIESIM.
  Context `{M: ucmra}.

  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable ident_src: ID.
  Variable _ident_tgt: ID.
  Definition ident_tgt := sum_tid _ident_tgt.

  Variable wf_src: WF.
  Variable wf_tgt: WF.

  Let srcE := threadE ident_src state_src.
  Let tgtE := threadE _ident_tgt state_tgt.

  Definition shared :=
    (TIdSet.t *
       (@imap ident_src wf_src) *
       (@imap ident_tgt wf_tgt) *
       state_src *
       state_tgt)%type.

  Let shared_rel: Type := shared -> Prop.

  Variable I: shared -> (cmra_car M) -> Prop.

  Variant __lsim
          (tid: thread_id)
          (lsim: forall R_src R_tgt (RR: R_src -> R_tgt -> (cmra_car M) -> shared_rel), bool -> bool -> (cmra_car M) -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel)
          (_lsim: forall R_src R_tgt (RR: R_src -> R_tgt -> (cmra_car M) -> shared_rel),bool -> bool -> (cmra_car M) -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel)
          R_src R_tgt (RR: R_src -> R_tgt -> (cmra_car M) -> shared_rel)
    :
    bool -> bool -> (cmra_car M) -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel :=
  | lsim_ret
      f_src f_tgt r_ctx
      ths im_src im_tgt st_src st_tgt
      r_src r_tgt
      (LSIM: RR r_src r_tgt r_ctx (ths, im_src, im_tgt, st_src, st_tgt))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx (Ret r_src) (Ret r_tgt) (ths, im_src, im_tgt, st_src, st_tgt)

  | lsim_tauL
      f_src f_tgt r_ctx
      ths im_src im_tgt st_src st_tgt
      itr_src itr_tgt
      (LSIM: _lsim _ _ RR true f_tgt r_ctx itr_src itr_tgt (ths, im_src, im_tgt, st_src, st_tgt))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx (Tau itr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt)
  | lsim_chooseL
      f_src f_tgt r_ctx
      ths im_src im_tgt st_src st_tgt
      X ktr_src itr_tgt
      (LSIM: exists x, _lsim _ _ RR true f_tgt r_ctx (ktr_src x) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx (trigger (Choose X) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt)
  | lsim_stateL
      f_src f_tgt r_ctx
      ths im_src im_tgt st_src st_tgt
      X run ktr_src itr_tgt
      (LSIM: _lsim _ _ RR true f_tgt r_ctx (ktr_src (snd (run st_src) : X)) itr_tgt (ths, im_src, im_tgt, fst (run st_src), st_tgt))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx (trigger (State run) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt)
  | lsim_tidL
      f_src f_tgt r_ctx
      ths im_src im_tgt st_src st_tgt
      ktr_src itr_tgt
      (LSIM: _lsim _ _ RR true f_tgt r_ctx (ktr_src tid) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx (trigger (GetTid) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt)
  | lsim_UB
      f_src f_tgt r_ctx
      ths im_src im_tgt st_src st_tgt
      ktr_src itr_tgt
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx (trigger (Undefined) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt)
  | lsim_fairL
      f_src f_tgt r_ctx
      ths im_src0 im_tgt st_src st_tgt
      f ktr_src itr_tgt
      (LSIM: exists im_src1,
          (<<FAIR: fair_update im_src0 im_src1 f>>) /\
            (<<LSIM: _lsim _ _ RR true f_tgt r_ctx (ktr_src tt) itr_tgt (ths, im_src1, im_tgt, st_src, st_tgt)>>))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx (trigger (Fair f) >>= ktr_src) itr_tgt (ths, im_src0, im_tgt, st_src, st_tgt)

  | lsim_tauR
      f_src f_tgt r_ctx
      ths im_src im_tgt st_src st_tgt
      itr_src itr_tgt
      (LSIM: _lsim _ _ RR f_src true r_ctx itr_src itr_tgt (ths, im_src, im_tgt, st_src, st_tgt))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx itr_src (Tau itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)
  | lsim_chooseR
      f_src f_tgt r_ctx
      ths im_src im_tgt st_src st_tgt
      X itr_src ktr_tgt
      (LSIM: forall x, _lsim _ _ RR f_src true r_ctx itr_src (ktr_tgt x) (ths, im_src, im_tgt, st_src, st_tgt))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx itr_src (trigger (Choose X) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)
  | lsim_stateR
      f_src f_tgt r_ctx
      ths im_src im_tgt st_src st_tgt
      X run itr_src ktr_tgt
      (LSIM: _lsim _ _ RR f_src true r_ctx itr_src (ktr_tgt (snd (run st_tgt) : X)) (ths, im_src, im_tgt, st_src, fst (run st_tgt)))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx itr_src (trigger (State run) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)
  | lsim_tidR
      f_src f_tgt r_ctx
      ths im_src im_tgt st_src st_tgt
      itr_src ktr_tgt
      (LSIM: _lsim _ _ RR f_src true r_ctx itr_src (ktr_tgt tid) (ths, im_src, im_tgt, st_src, st_tgt))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx itr_src (trigger (GetTid) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)
  | lsim_fairR
      f_src f_tgt r_ctx
      ths im_src im_tgt0 st_src st_tgt
      f itr_src ktr_tgt
      (LSIM: forall im_tgt1
                   (FAIR: fair_update im_tgt0 im_tgt1 (prism_fmap inrp f)),
          (<<LSIM: _lsim _ _ RR f_src true r_ctx itr_src (ktr_tgt tt) (ths, im_src, im_tgt1, st_src, st_tgt)>>))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx itr_src (trigger (Fair f) >>= ktr_tgt) (ths, im_src, im_tgt0, st_src, st_tgt)

  | lsim_observe
      f_src f_tgt r_ctx
      ths im_src im_tgt st_src st_tgt
      fn args ktr_src ktr_tgt
      (LSIM: forall ret,
          lsim _ _ RR true true r_ctx (ktr_src ret) (ktr_tgt ret) (ths, im_src, im_tgt, st_src, st_tgt))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx (trigger (Observe fn args) >>= ktr_src) (trigger (Observe fn args) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)

  | lsim_call
      f_src f_tgt r_ctx
      ths im_src im_tgt st_src st_tgt
      fn args ktr_src ktr_tgt
      (LSIM : forall ret, lsim _ _ RR true true r_ctx (ktr_src ret) (ktr_tgt ret) (ths, im_src, im_tgt, st_src, st_tgt))
    : __lsim tid lsim _lsim RR f_src f_tgt r_ctx (trigger (Call fn args) >>= ktr_src) (trigger (Call fn args) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)

  | lsim_yieldL
      f_src f_tgt r_ctx
      ths im_src im_tgt st_src st_tgt
      ktr_src itr_tgt
      (LSIM: _lsim _ _ RR true f_tgt r_ctx (ktr_src tt) (trigger (Yield) >>= itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)
  | lsim_yieldR
      f_src f_tgt r_ctx0
      ths0 im_src0 im_tgt0 st_src0 st_tgt0
      r_own r_shared
      ktr_src ktr_tgt
      (INV: I (ths0, im_src0, im_tgt0, st_src0, st_tgt0) r_shared)
      (VALID: ✓ (r_shared ⋅ r_own ⋅ r_ctx0))
      (LSIM: forall ths1 im_src1 im_tgt1 st_src1 st_tgt1 r_shared1 r_ctx1
                    (INV: I (ths1, im_src1, im_tgt1, st_src1, st_tgt1) r_shared1)
                    (VALID: ✓ (r_shared1 ⋅ r_own ⋅ r_ctx1))
                    im_tgt2
                    (TGT: fair_update im_tgt1 im_tgt2 (prism_fmap inlp (tids_fmap tid ths1))),
          _lsim _ _ RR f_src true r_ctx1 (trigger (Yield) >>= ktr_src) (ktr_tgt tt) (ths1, im_src1, im_tgt2, st_src1, st_tgt1))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx0 (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt) (ths0, im_src0, im_tgt0, st_src0, st_tgt0)
  | lsim_sync
      f_src f_tgt r_ctx0
      ths0 im_src0 im_tgt0 st_src0 st_tgt0
      r_own r_shared
      ktr_src ktr_tgt
      (INV: I (ths0, im_src0, im_tgt0, st_src0, st_tgt0) r_shared)
      (VALID: ✓ (r_shared ⋅ r_own ⋅ r_ctx0))
      (LSIM: forall ths1 im_src1 im_tgt1 st_src1 st_tgt1 r_shared1 r_ctx1
               (INV: I (ths1, im_src1, im_tgt1, st_src1, st_tgt1) r_shared1)
               (VALID: ✓ (r_shared1 ⋅ r_own ⋅ r_ctx1))
               im_tgt2
               (TGT: fair_update im_tgt1 im_tgt2 (prism_fmap inlp (tids_fmap tid ths1))),
          (<<LSIM: lsim _ _ RR true true r_ctx1 (ktr_src tt) (ktr_tgt tt) (ths1, im_src1, im_tgt2, st_src1, st_tgt1)>>))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx0 (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt) (ths0, im_src0, im_tgt0, st_src0, st_tgt0)

  | lsim_progress
      r_ctx
      ths im_src im_tgt st_src st_tgt
      itr_src itr_tgt
      (LSIM: lsim _ _ RR false false r_ctx itr_src itr_tgt (ths, im_src, im_tgt, st_src, st_tgt))
    :
    __lsim tid lsim _lsim RR true true r_ctx itr_src itr_tgt (ths, im_src, im_tgt, st_src, st_tgt)
  .

  Definition lsim (tid: thread_id)
             R_src R_tgt (RR: R_src -> R_tgt -> (cmra_car M) -> shared_rel):
    bool -> bool -> (cmra_car M) -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel :=
    paco9 (fun r => pind9 (__lsim tid r) top9) bot9 R_src R_tgt RR.

  Lemma __lsim_mon tid:
    forall r r' (LE: r <9= r'), (__lsim tid r) <10= (__lsim tid r').
  Proof.
    ii. inv PR; try (econs; eauto; fail).
    eapply lsim_sync; eauto. i. hexploit LSIM. eapply INV0. eapply VALID0. all: eauto.
  Qed.

  Lemma _lsim_mon tid: forall r, monotone9 (__lsim tid r).
  Proof.
    ii. inv IN; try (econs; eauto; fail).
    { des. econs; eauto. }
    { des. econs; eauto. }
    { econs. i. eapply LE. eapply LSIM. eauto. }
  Qed.

  Lemma lsim_mon tid: forall q, monotone9 (fun r => pind9 (__lsim tid r) q).
  Proof.
    ii. eapply pind9_mon_gen; eauto.
    ii. eapply __lsim_mon; eauto.
  Qed.
  Hint Resolve lsim_mon: paco.
  Hint Resolve cpn9_wcompat: paco.

  Import pacotac_internal.

  Lemma lsim_acc_gen
        tid r
        (A: Type)
        (f0: forall (a: A), Type)
        (f1: forall (a: A), Type)
        (f2: forall (a: A), f0 a -> f1 a -> (cmra_car M) -> shared_rel)
        (f3: forall (a: A), bool)
        (f4: forall (a: A), bool)
        (f5: forall (a: A), (cmra_car M))
        (f6: forall (a: A), itree srcE (f0 a))
        (f7: forall (a: A), itree tgtE (f1 a))
        (f8: forall (a: A), shared)
        r0 (q: A -> Prop)
        (IND: forall r1
                     (LE: r1 <9= r0)
                     (IH: forall a, @r1 (f0 a) (f1 a) (f2 a) (f3 a) (f4 a) (f5 a) (f6 a) (f7 a) (f8 a) -> q a),
          forall a, pind9 (__lsim tid r) r1 (f0 a) (f1 a) (f2 a) (f3 a) (f4 a) (f5 a) (f6 a) (f7 a) (f8 a) -> q a)
    :
    forall a, pind9 (__lsim tid r) r0 (f0 a) (f1 a) (f2 a) (f3 a) (f4 a) (f5 a) (f6 a) (f7 a) (f8 a) -> q a.
  Proof.
    cut ((pind9 (__lsim tid r) r0) <9= curry9 (fun x => forall a (EQ: @exist9T _ _ _ _ _ _ _ _ _ (f0 a) (f1 a) (f2 a) (f3 a) (f4 a) (f5 a) (f6 a) (f7 a) (f8 a) = x), q a)).
    { exact (fun P a H => uncurry_adjoint2_9 P (@exist9T _ _ _ _ _ _ _ _ _ (f0 a) (f1 a) (f2 a) (f3 a) (f4 a) (f5 a) (f6 a) (f7 a) (f8 a)) H a eq_refl). }
    { exact (@pind9_acc _ _ _ _ _ _ _ _ _ (__lsim tid r) (curry9 (fun x => forall a (EQ: @exist9T _ _ _ _ _ _ _ _ _ (f0 a) (f1 a) (f2 a) (f3 a) (f4 a) (f5 a) (f6 a) (f7 a) (f8 a) = x), q a)) r0 (fun rr LE IH => @uncurry_adjoint1_9 _ _ _ _ _ _ _ _ _ (pind9 (__lsim tid r) rr) (fun x => forall a (EQ: @exist9T _ _ _ _ _ _ _ _ _ (f0 a) (f1 a) (f2 a) (f3 a) (f4 a) (f5 a) (f6 a) (f7 a) (f8 a) = x), q a) (fun x PR a EQ => IND rr LE (fun a H => IH (f0 a) (f1 a) (f2 a) (f3 a) (f4 a) (f5 a) (f6 a) (f7 a) (f8 a) H a eq_refl) a (@eq_rect _ _ (uncurry9 (pind9 (__lsim tid r) rr)) PR _ (eq_sym EQ))))).
    }
  Qed.

  Ltac pind_gen := patterning 9; refine (@lsim_acc_gen
                                           _ _ _
                                           _ _ _ _ _ _ _ _ _
                                           _ _ _).
  Ltac pinduction n := currying n pind_gen.

  (* TODO: add this in pico lib *)
  Lemma lsim_indC_spec tid
    :
    (fun r => __lsim tid r r) <10= gupaco9 (fun r => pind9 (__lsim tid r) top9) (cpn9 (fun r => pind9 (__lsim tid r) top9)).
  Proof.
    eapply wrespect9_uclo; eauto with paco.
    econs.
    { ii. eapply __lsim_mon; eauto. eapply _lsim_mon; eauto. }
    i. eapply pind9_fold.
    eapply __lsim_mon.
    { instantiate (1:=l). i. eapply rclo9_base. eauto. }
    eapply _lsim_mon; eauto. i. split; ss.
    eapply GF in PR0. eapply pind9_mon_gen; eauto.
    i. eapply __lsim_mon.
    { i. eapply rclo9_base. eassumption. }
    eauto.
  Qed.

  Variant lsim_resetC
          (r: forall R_src R_tgt (RR: R_src -> R_tgt -> (cmra_car M) -> shared_rel), bool -> bool -> (cmra_car M) -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel)
          R_src R_tgt (RR: R_src -> R_tgt -> (cmra_car M) -> shared_rel)
    :
    bool -> bool -> (cmra_car M) -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel :=
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
    econs.
    { ii. inv IN. econs; eauto. }
    i. inv PR. eapply GF in REL.

    revert x0 x1 x2 ps1 pt1 x5 x6 x7 x8 REL x3 x4 SRC TGT.
    pinduction 9. i.
    eapply pind9_unfold in PR.
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

    { eapply pind9_fold. eapply lsim_stateL. split; ss.
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

    { eapply pind9_fold. eapply lsim_stateR. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { eapply pind9_fold. eapply lsim_tidR. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { eapply pind9_fold. eapply lsim_fairR. i. split; ss. specialize (LSIM0 _ FAIR).
      des. destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { eapply pind9_fold. eapply lsim_observe. i. eapply rclo9_base. auto. }

    { eapply pind9_fold. eapply lsim_call. i. eapply rclo9_base. auto. }

    { des. eapply pind9_fold. eapply lsim_yieldL. split; ss.
      destruct LSIM0 as [LSIM IND]. hexploit IH; eauto.
    }

    { eapply pind9_fold. eapply lsim_yieldR; eauto. i.
      hexploit LSIM0; eauto. clear LSIM0. intros LSIM0.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. split; ss; eauto.
    }

    { eapply pind9_fold. eapply lsim_sync; eauto. i.
      hexploit LSIM0. eapply INV0. eapply VALID0. all: eauto. i; des. esplits; eauto.
      eapply rclo9_base. auto.
    }

    { pclearbot. hexploit SRC; ss; i. hexploit TGT; ss; i. clarify.
      eapply pind9_fold. eapply lsim_progress. eapply rclo9_base. auto. }
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
    ginit. guclo lsim_resetC_spec.
    econs; eauto. gfinal.
    right. auto.
  Qed.

  Variant lsim_monoC
          (r: forall R_src R_tgt (RR: R_src -> R_tgt -> (cmra_car M) -> shared_rel), bool -> bool -> (cmra_car M) -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel)
          R_src R_tgt (RR1: R_src -> R_tgt -> (cmra_car M) -> shared_rel)
    :
    bool -> bool -> (cmra_car M) -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel :=
    | lsim_monoC_intro
        (RR0: R_src -> R_tgt -> (cmra_car M) -> shared_rel)
        src tgt shr r_ctx ps pt
        (MON: forall r_src r_tgt r_ctx shr (RET: RR0 r_src r_tgt r_ctx shr),
            RR1 r_src r_tgt r_ctx shr)
        (REL: r _ _ RR0 ps pt r_ctx src tgt shr)
      :
      lsim_monoC r RR1 ps pt r_ctx src tgt shr
  .

  Lemma lsim_monoC_spec tid
    :
    lsim_monoC <10= gupaco9 (fun r => pind9 (__lsim tid r) top9) (cpn9 (fun r => pind9 (__lsim tid r) top9)).
  Proof.
    eapply wrespect9_uclo; eauto with paco.
    econs.
    { ii. inv IN. econs; eauto. }
    i. inv PR. eapply GF in REL.
    revert x2 MON.
    pattern x0, x1, RR0, x3, x4, x5, x6, x7, x8.
    revert x0 x1 RR0 x3 x4 x5 x6 x7 x8 REL.
    apply pind9_acc. intros rr _ IH x0 x1 RR0 x3 x4 x5 x6 x7 x8 PR.
    i. eapply pind9_unfold in PR.
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

    { eapply pind9_fold. eapply lsim_stateL. split; ss.
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

    { eapply pind9_fold. eapply lsim_stateR. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { eapply pind9_fold. eapply lsim_tidR. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { eapply pind9_fold. eapply lsim_fairR. i. split; ss. specialize (LSIM0 _ FAIR).
      des. destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { eapply pind9_fold. eapply lsim_observe. i. eapply rclo9_clo_base. econs; eauto. }

    { eapply pind9_fold. eapply lsim_call. i. eapply rclo9_clo_base. econs; eauto. }

    { des. eapply pind9_fold. eapply lsim_yieldL. split; ss.
      destruct LSIM0 as [LSIM IND]. hexploit IH; eauto.
    }

    { eapply pind9_fold. eapply lsim_yieldR; eauto. i.
      hexploit LSIM0; eauto. clear LSIM0. intros LSIM0.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. split; ss; eauto.
    }

    { eapply pind9_fold. eapply lsim_sync; eauto. i.
      hexploit LSIM0. eapply INV0. eapply VALID0. all: eauto. i; des. esplits; eauto.
      eapply rclo9_clo_base. econs; eauto.
    }

    { eapply pind9_fold. eapply lsim_progress. eapply rclo9_clo_base. econs; eauto. }
  Qed.

  Variant lsim_frameC
          (r: forall R_src R_tgt (RR: R_src -> R_tgt -> (cmra_car M) -> shared_rel), bool -> bool -> (cmra_car M) -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel)
          R_src R_tgt
          (RR: R_src -> R_tgt -> (cmra_car M) -> shared_rel)
    :
    bool -> bool -> (cmra_car M) -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel :=
    | lsim_frameC_intro
        src tgt shr r_ctx ps pt r_frame
        (REL: r _ _ (fun r_src r_tgt r_ctx shr =>
                       forall r_ctx' (EQ: r_ctx = r_frame ⋅ r_ctx'),
                         RR r_src r_tgt r_ctx' shr) ps pt (r_frame ⋅ r_ctx) src tgt shr)
      :
      lsim_frameC r RR ps pt r_ctx src tgt shr
  .

  Lemma lsim_frameC_spec tid
    :
    lsim_frameC <10= gupaco9 (fun r => pind9 (__lsim tid r) top9) (cpn9 (fun r => pind9 (__lsim tid r) top9)).
  Proof.
    eapply grespect9_uclo; eauto with paco.
    econs.
    { ii. inv IN. econs; eauto. }
    i. inv PR. eapply GF in REL.
    eapply rclo9_clo_base. eapply cpn9_gupaco.
    { eauto with paco. }

    remember (r_frame ⋅ x5).
    pose (fun r_src r_tgt r_ctx shr =>
            forall r_ctx' (EQ: r_ctx = r_frame ⋅ r_ctx'),
              x2 r_src r_tgt r_ctx' shr) as RR1.
    assert (FRAME: forall r_src r_tgt r_ctx shr
                          (SAT: RR1 r_src r_tgt r_ctx shr),
             forall r_ctx' (EQ: r_ctx = r_frame ⋅ r_ctx'),
               x2 r_src r_tgt r_ctx' shr).
    { subst RR1. auto. }
    fold RR1 in REL.
    remember RR1 as RR'. clear HeqRR' RR1.
    revert x2 r_frame x5 Heqc FRAME.
    pattern x0, x1, RR', x3, x4, c, x6, x7, x8.
    revert x0 x1 RR' x3 x4 c x6 x7 x8 REL.
    apply pind9_acc. intros rr _ IH x0 x1 RR' x3 x4 c x6 x7 x8 PR.
    i. eapply pind9_unfold in PR.
    2:{ eapply _lsim_mon. }
    rename PR into LSIM. inv LSIM.

    { guclo lsim_indC_spec. econs; eauto. }

    { destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      guclo lsim_indC_spec. eapply lsim_tauL.
      hexploit IH; eauto.
    }

    { des. guclo lsim_indC_spec. eapply lsim_chooseL. esplits; eauto.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { guclo lsim_indC_spec. eapply lsim_stateL.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { guclo lsim_indC_spec. eapply lsim_tidL.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { guclo lsim_indC_spec. eapply lsim_UB. }

    { des. guclo lsim_indC_spec. eapply lsim_fairL. esplits; eauto.
      destruct LSIM as [LSIM IND]. hexploit IH; eauto.
    }

    { destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      guclo lsim_indC_spec. eapply lsim_tauR.
      hexploit IH. eauto. all: eauto.
    }

    { guclo lsim_indC_spec. eapply lsim_chooseR. i. specialize (LSIM0 x).
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { guclo lsim_indC_spec. eapply lsim_stateR.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { guclo lsim_indC_spec. eapply lsim_tidR.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { guclo lsim_indC_spec. eapply lsim_fairR. i. specialize (LSIM0 _ FAIR).
      des. destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { gfinal. left. eapply pind9_fold. eapply lsim_observe. i.
      eapply rclo9_clo. left. econs; eauto.
      eapply rclo9_clo_base. right. guclo lsim_monoC_spec. econs.
      2:{ gbase. eauto. }
      { eauto. }
    }

    { gfinal. left. eapply pind9_fold. eapply lsim_call. i.
      eapply rclo9_clo. left. econs; eauto.
      eapply rclo9_clo_base. right. guclo lsim_monoC_spec. econs.
      2:{ gbase. eauto. }
      { eauto. }
    }

    { des. guclo lsim_indC_spec. eapply lsim_yieldL.
      destruct LSIM0 as [LSIM IND]. hexploit IH; eauto.
    }

    { guclo lsim_indC_spec. eapply lsim_yieldR; eauto.
      { instantiate (1:=r_own ⋅ r_frame). rewrite (assoc cmra.op). by rewrite (assoc cmra.op) in VALID. }
      i. hexploit LSIM0; eauto.
      { instantiate (1:=r_frame ⋅ r_ctx1). rewrite (assoc cmra.op). by rewrite !(assoc cmra.op) in VALID0. }
      clear LSIM0. intros LSIM0.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { gfinal. left. eapply pind9_fold. eapply lsim_sync; eauto.
      { instantiate (1:=r_own ⋅ r_frame). rewrite (assoc cmra.op). by rewrite !(assoc cmra.op) in VALID. }
      i. hexploit LSIM0; eauto.
      { instantiate (1:=r_frame ⋅ r_ctx1). rewrite (assoc cmra.op). by rewrite !(assoc cmra.op) in VALID0. }
      i. des.
      eapply rclo9_clo. left. econs; eauto.
      eapply rclo9_clo_base. right. guclo lsim_monoC_spec. econs.
      2:{ gbase. eauto. }
      { eauto. }
    }

    { gfinal. left. eapply pind9_fold. eapply lsim_progress.
      eapply rclo9_clo. left. econs; eauto.
      eapply rclo9_clo_base. right. guclo lsim_monoC_spec. econs.
      2:{ gbase. eauto. }
      { eauto. }
    }
  Qed.

  Variant lsim_bindC'
          (r: forall R_src R_tgt (RR: R_src -> R_tgt -> (cmra_car M) -> shared_rel), bool -> bool -> (cmra_car M) -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel)
          R_src1 R_tgt1
          (RR: R_src1 -> R_tgt1 -> (cmra_car M) -> shared_rel)
    :
    bool -> bool -> (cmra_car M) -> itree srcE R_src1 -> itree tgtE R_tgt1 -> shared_rel :=
    | lsim_bindC'_intro
        R_src0 R_tgt0 (RR0: R_src0 -> R_tgt0 -> (cmra_car M) -> shared_rel)
        itr_src itr_tgt ktr_src ktr_tgt shr r_ctx ps pt
        (REL: r _ _ RR0 ps pt r_ctx itr_src itr_tgt shr)
        (MON: forall r_src r_tgt r_ctx shr
                     (SAT: RR0 r_src r_tgt r_ctx shr),
            r _ _ RR false false r_ctx (ktr_src r_src) (ktr_tgt r_tgt) shr)
      :
      lsim_bindC' r RR ps pt r_ctx (itr_src >>= ktr_src) (itr_tgt >>= ktr_tgt) shr
  .

  Lemma lsim_bindC'_spec tid
    :
    lsim_bindC' <10= gupaco9 (fun r => pind9 (__lsim tid r) top9) (cpn9 (fun r => pind9 (__lsim tid r) top9)).
  Proof.
    assert (HINT: forall r1, monotone9 (fun r0 => pind9 (__lsim tid r0) r1)).
    { ii. eapply pind9_mon_gen; eauto. i. eapply __lsim_mon; eauto. }
    eapply grespect9_uclo; eauto with paco.
    econs.
    { ii. inv IN. econs; eauto. }
    i. inv PR. eapply GF in REL.
    eapply rclo9_clo_base. eapply cpn9_gupaco.
    { eauto with paco. }

    revert ktr_src ktr_tgt MON.
    pattern R_src0, R_tgt0, RR0, x3, x4, x5, itr_src, itr_tgt, x8.
    revert R_src0 R_tgt0 RR0 x3 x4 x5 itr_src itr_tgt x8 REL.
    apply pind9_acc. intros rr _ IH R_src0 R_tgt0 RR0 x3 x4 x5 itr_src itr_tgt x8 PR.
    i. eapply pind9_unfold in PR.
    2:{ eapply _lsim_mon. }
    rename PR into LSIM. inv LSIM; ired.

    { eapply lsim_resetC_spec. econs.
      2:{ instantiate (1:=false). ss. }
      2:{ instantiate (1:=false). ss. }
      eapply MON in LSIM0. eapply GF in LSIM0.
      eapply pind9_mon_gen; eauto. i. ss.
      eapply __lsim_mon.
      { i. eapply rclo9_base. eassumption. }
      eauto.
    }

    Notation cpn := (cpn9 _).
    Notation pind := (fun r => pind9 (__lsim _ r) top9).
    ss.

    { destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      guclo lsim_indC_spec. eapply lsim_tauL.
      hexploit IH; eauto.
    }

    { des. guclo lsim_indC_spec. eapply lsim_chooseL. esplits; eauto.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { guclo lsim_indC_spec. eapply lsim_stateL.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { guclo lsim_indC_spec. eapply lsim_tidL.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { guclo lsim_indC_spec. eapply lsim_UB. }

    { des. guclo lsim_indC_spec. eapply lsim_fairL. esplits; eauto.
      destruct LSIM as [LSIM IND]. hexploit IH; eauto.
    }

    { destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      guclo lsim_indC_spec. eapply lsim_tauR.
      hexploit IH. eauto. all: eauto.
    }

    { guclo lsim_indC_spec. eapply lsim_chooseR. i. specialize (LSIM0 x).
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { guclo lsim_indC_spec. eapply lsim_stateR.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { guclo lsim_indC_spec. eapply lsim_tidR.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { guclo lsim_indC_spec. eapply lsim_fairR. i. specialize (LSIM0 _ FAIR).
      des. destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { gfinal. left. eapply pind9_fold. eapply lsim_observe. i.
      eapply rclo9_clo_base. left. econs; eauto.
    }

    { gfinal. left. eapply pind9_fold. eapply lsim_call. i.
      eapply rclo9_clo_base. left. econs; eauto.
    }

    { des. guclo lsim_indC_spec. eapply lsim_yieldL.
      destruct LSIM0 as [LSIM IND]. hexploit IH; eauto.
      rewrite ! bind_bind. eauto.
    }

    { guclo lsim_indC_spec. eapply lsim_yieldR; eauto.
      i. hexploit LSIM0; eauto.
      clear LSIM0. intros LSIM0.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
      rewrite ! bind_bind. eauto.
    }

    { gfinal. left. eapply pind9_fold. eapply lsim_sync; eauto.
      i. hexploit LSIM0; eauto.
      i. des. eapply rclo9_clo_base. left. econs; eauto.
    }

    { gfinal. left. eapply pind9_fold. eapply lsim_progress. eapply rclo9_clo_base. left. econs; eauto.
    }
  Qed.

  Variant lsim_bindC
          (r: forall R_src R_tgt (RR: R_src -> R_tgt -> (cmra_car M) -> shared_rel), bool -> bool -> (cmra_car M) -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel)
          R_src1 R_tgt1
          (RR: R_src1 -> R_tgt1 -> (cmra_car M) -> shared_rel)
    :
    bool -> bool -> (cmra_car M) -> itree srcE R_src1 -> itree tgtE R_tgt1 -> shared_rel :=
    | lsim_bindC_intro
        R_src0 R_tgt0
        itr_src itr_tgt ktr_src ktr_tgt shr r_ctx ps pt
        (REL: r _ _ (fun (r_src: R_src0) (r_tgt: R_tgt0) r_ctx shr => r _ _ RR false false r_ctx (ktr_src r_src) (ktr_tgt r_tgt) shr) ps pt r_ctx itr_src itr_tgt shr)
      :
      lsim_bindC r RR ps pt r_ctx (itr_src >>= ktr_src) (itr_tgt >>= ktr_tgt) shr
  .

  Lemma lsim_bindC_spec tid
    :
    lsim_bindC <10= gupaco9 (fun r => pind9 (__lsim tid r) top9) (cpn9 (fun r => pind9 (__lsim tid r) top9)).
  Proof.
    i. eapply lsim_bindC'_spec. inv PR. econs; eauto.
  Qed.

  Lemma lsim_set_prog
        tid
        R0 R1 (RR: R0 -> R1 -> (cmra_car M) -> shared_rel)
        r_ctx src tgt shr
        (LSIM: lsim tid RR true true r_ctx src tgt shr)
    :
    forall ps pt, lsim tid RR ps pt r_ctx src tgt shr.
  Proof.
    i. revert_until tid. pcofix CIH. i.
    remember true as ps0 in LSIM at 1. remember true as pt0 in LSIM at 1.
    move LSIM before CIH. revert_until LSIM. punfold LSIM.
    eapply pind9_acc in LSIM.

    { instantiate (1:= (fun R0 R1 (RR: R0 -> R1 -> (cmra_car M) -> shared_rel) ps0 pt0 r_ctx src tgt shr =>
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
      hexploit IH. eauto. all: eauto. i. punfold H.
    }

    { des. pfold. eapply pind9_fold. eapply lsim_chooseL. esplits; eauto. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H.
    }

    { pfold. eapply pind9_fold. eapply lsim_stateL. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H.
    }

    { pfold. eapply pind9_fold. eapply lsim_tidL. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H.
    }

    { pfold. eapply pind9_fold. eapply lsim_UB. }

    { des. pfold. eapply pind9_fold. eapply lsim_fairL. esplits; eauto. split; ss.
      destruct LSIM as [LSIM IND]. hexploit IH; eauto. i. punfold H.
    }

    { destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      pfold. eapply pind9_fold. eapply lsim_tauR. split; ss.
      hexploit IH. eauto. all: eauto. i. punfold H.
    }

    { pfold. eapply pind9_fold. eapply lsim_chooseR. i. split; ss. specialize (LSIM0 x).
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H.
    }

    { pfold. eapply pind9_fold. eapply lsim_stateR. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H.
    }

    { pfold. eapply pind9_fold. eapply lsim_tidR. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H.
    }

    { pfold. eapply pind9_fold. eapply lsim_fairR. i. split; ss. specialize (LSIM0 _ FAIR).
      des. destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H.
    }

    { pfold. eapply pind9_fold. eapply lsim_observe. i. eapply upaco9_mon_bot; eauto. }

    { pfold. eapply pind9_fold. eapply lsim_call. i. eapply upaco9_mon_bot; eauto. }

    { des. pfold. eapply pind9_fold. eapply lsim_yieldL. esplits; eauto. split; ss.
      destruct LSIM0 as [LSIM IND]. hexploit IH; eauto. i. punfold H.
    }

    { pfold. eapply pind9_fold. eapply lsim_yieldR; eauto. i.
      hexploit LSIM0; eauto. clear LSIM0. intros LSIM0.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. split; ss. punfold H.
    }

    { pfold. eapply pind9_fold. eapply lsim_sync; eauto. i.
      hexploit LSIM0. eapply INV0. eapply VALID0. all: eauto. i; des. esplits; eauto.
      eapply upaco9_mon_bot; eauto.
    }

    { pclearbot. eapply paco9_mon_bot. eapply lsim_reset_prog. eauto. all: ss. }

  Qed.

  Lemma lsim_flag_any ps0 pt0
        tid
        R0 R1 (RR: R0 -> R1 -> (cmra_car M) -> shared_rel)
        src tgt shr
        ps1 pt1 r_ctx
        (LSIM: lsim tid RR ps1 pt1 r_ctx src tgt shr)
    :
    lsim tid RR ps0 pt0 r_ctx src tgt shr.
  Proof.
    eapply lsim_set_prog. eapply lsim_reset_prog; eauto.
  Qed.

  Variant lsim_bindRC'
          (r: forall R_src R_tgt (RR: R_src -> R_tgt -> (cmra_car M) -> shared_rel), bool -> bool -> (cmra_car M) -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel)
          R_src1 R_tgt1
          (RR: R_src1 -> R_tgt1 -> (cmra_car M) -> shared_rel)
    :
    bool -> bool -> (cmra_car M) -> itree srcE R_src1 -> itree tgtE R_tgt1 -> shared_rel :=
    | lsim_bindRC'_intro
        R_tgt0 (RR0: R_tgt0 -> (cmra_car M) -> shared_rel)
        itr_tgt ktr_src ktr_tgt shr r_ctx ps pt
        (REL: r _ _ (fun _ => RR0) ps pt r_ctx (trigger Yield) itr_tgt shr)
        (MON: forall r_tgt r_ctx shr
                     (SAT: RR0 r_tgt r_ctx shr),
            r _ _ RR false false r_ctx (trigger Yield >>= ktr_src) (ktr_tgt r_tgt) shr)
      :
      lsim_bindRC' r RR ps pt r_ctx (trigger Yield >>= ktr_src) (itr_tgt >>= ktr_tgt) shr
  .

  Import Program.

  Lemma trigger_yield E `{cE -< E}
    :
    (trigger Yield;;; Ret tt: itree E unit) = trigger Yield.
  Proof.
    eapply observe_eta. ss.
    rewrite bind_trigger. ss.
    f_equal. extensionality x. destruct x. ss.
  Qed.

  Lemma trigger_yield_rev E `{cE -< E}
        ktr
        (EQ: (trigger Yield >>= ktr: itree E unit) = trigger Yield)
    :
    ktr = fun _ => Ret tt.
  Proof.
    eapply f_equal with (f:=observe) in EQ.
    ss. rewrite bind_trigger in EQ. ss.
    dependent destruction EQ.
    extensionality u. destruct u.
    eapply equal_f in x. eauto.
  Qed.

  Lemma trigger_unit_same (E: Type -> Type) (e: E unit) R
        (ktr: unit -> itree E R)
    :
    trigger e >>= (fun x => ktr x) = trigger e >>= (fun x => ktr tt).
  Proof.
    f_equal. extensionality u. destruct u. auto.
  Qed.

  Lemma trigger_eq_rev E R X0 X1 (e0: E X0) (e1: E X1)
        (ktr0: X0 -> itree E R) (ktr1: X1 -> itree E R)
        (EQ: ITree.trigger e0 >>= ktr0 = ITree.trigger e1 >>= ktr1)
    :
    X0 = X1 /\ JMeq e0 e1 /\ JMeq ktr0 ktr1.
  Proof.
    rewrite bind_trigger in EQ.
    rewrite bind_trigger in EQ.
    eapply f_equal with (f:=observe) in EQ. ss.
    dependent destruction EQ. splits; auto.
    assert (ktr0 = ktr1).
    { extensionality a. eapply equal_f in x. eauto. }
    subst. auto.
  Qed.

  Lemma lsim_rev_ret
        tid
        R0 R1 (RR: R0 -> R1 -> (cmra_car M) -> shared_rel)
        r_src r_tgt shr ps pt r_ctx
        (LSIM: lsim tid RR ps pt r_ctx (Ret r_src) (Ret r_tgt) shr)
    :
    RR r_src r_tgt r_ctx shr.
  Proof.
    eapply lsim_reset_prog in LSIM.
    2:{ i. reflexivity. }
    2:{ i. reflexivity. }
    eapply lsim_set_prog in LSIM.
    instantiate (1:=false) in LSIM. instantiate (1:=false) in LSIM. clear ps pt.
    punfold LSIM. eapply pind9_unfold in LSIM; auto.
    2:{ eapply _lsim_mon. }
    inv LSIM; auto.
    { eapply f_equal with (f:=observe) in H3. ss. }
    { eapply f_equal with (f:=observe) in H3. ss. }
    { eapply f_equal with (f:=observe) in H3. ss. }
    { eapply f_equal with (f:=observe) in H3. ss. }
    { eapply f_equal with (f:=observe) in H3. ss. }
    { eapply f_equal with (f:=observe) in H4. ss. }
    { eapply f_equal with (f:=observe) in H4. ss. }
    { eapply f_equal with (f:=observe) in H4. ss. }
    { eapply f_equal with (f:=observe) in H4. ss. }
    { eapply f_equal with (f:=observe) in H4. ss. }
    { eapply f_equal with (f:=observe) in H4. ss. }
    { eapply f_equal with (f:=observe) in H4. ss. }
    { eapply f_equal with (f:=observe) in H4. ss. }
    { eapply f_equal with (f:=observe) in H4. ss. }
  Qed.

  Lemma lsim_rev_tau
        tid
        R0 R1 (RR: R0 -> R1 -> (cmra_car M) -> shared_rel)
        r_src tgt shr ps pt r_ctx
        (LSIM: lsim tid RR ps pt r_ctx (Ret r_src) (Tau tgt) shr)
    :
    lsim tid RR ps pt r_ctx (Ret r_src) tgt shr.
  Proof.
    eapply lsim_reset_prog in LSIM.
    2:{ i. reflexivity. }
    2:{ i. reflexivity. }
    eapply lsim_set_prog in LSIM.
    instantiate (1:=false) in LSIM. instantiate (1:=false) in LSIM.
    punfold LSIM. eapply pind9_unfold in LSIM; auto.
    2:{ eapply _lsim_mon. }
    inv LSIM; auto.
    { eapply f_equal with (f:=observe) in H3. ss. }
    { eapply f_equal with (f:=observe) in H3. ss. }
    { eapply f_equal with (f:=observe) in H3. ss. }
    { eapply f_equal with (f:=observe) in H3. ss. }
    { eapply f_equal with (f:=observe) in H3. ss. }
    { inv LSIM0. eapply lsim_flag_any. pfold. eauto. }
    { eapply f_equal with (f:=observe) in H4. ss. }
    { eapply f_equal with (f:=observe) in H4. ss. }
    { eapply f_equal with (f:=observe) in H4. ss. }
    { eapply f_equal with (f:=observe) in H4. ss. }
    { eapply f_equal with (f:=observe) in H4. ss. }
    { eapply f_equal with (f:=observe) in H4. ss. }
    { eapply f_equal with (f:=observe) in H4. ss. }
    { eapply f_equal with (f:=observe) in H4. ss. }
    { eapply f_equal with (f:=observe) in H4. ss. }
  Qed.

  Lemma lsim_rev_choose
        tid
        R0 R1 (RR: R0 -> R1 -> (cmra_car M) -> shared_rel)
        r_src X tgt shr ps pt r_ctx
        (LSIM: lsim tid RR ps pt r_ctx (Ret r_src) (trigger (Choose X) >>= tgt) shr)
    :
    forall x, lsim tid RR ps pt r_ctx (Ret r_src) (tgt x) shr.
  Proof.
    eapply lsim_reset_prog in LSIM.
    2:{ i. reflexivity. }
    2:{ i. reflexivity. }
    eapply lsim_set_prog in LSIM.
    instantiate (1:=false) in LSIM. instantiate (1:=false) in LSIM.
    punfold LSIM. eapply pind9_unfold in LSIM; auto.
    2:{ eapply _lsim_mon. }
    inv LSIM; auto.
    { eapply f_equal with (f:=observe) in H4. ss. }
    { eapply f_equal with (f:=observe) in H3. ss. }
    { eapply f_equal with (f:=observe) in H3. ss. }
    { eapply f_equal with (f:=observe) in H3. ss. }
    { eapply f_equal with (f:=observe) in H3. ss. }
    { eapply f_equal with (f:=observe) in H3. ss. }
    { eapply f_equal with (f:=observe) in H4. ss. }
    { eapply trigger_eq_rev in H4. des. subst.
      i. specialize (LSIM0 x). inv LSIM0.
      eapply lsim_flag_any. pfold. eauto. }
    { eapply trigger_eq_rev in H4. des. subst. dependent destruction H0. }
    { eapply trigger_eq_rev in H4. des. subst. dependent destruction H0. }
    { eapply trigger_eq_rev in H4. des. subst. dependent destruction H0. }
    { eapply trigger_eq_rev in H4. des. subst. dependent destruction H0. }
    { eapply trigger_eq_rev in H4. des. subst. dependent destruction H0. }
    { eapply trigger_eq_rev in H4. des. subst. dependent destruction H0. }
    { eapply trigger_eq_rev in H4. des. subst. dependent destruction H0. }
    { eapply trigger_eq_rev in H4. des. subst. dependent destruction H0. }
  Qed.

  Lemma inhabited_not_void X
        (INHABITED: inhabited X)
    :
    X <> void.
  Proof.
    ii. subst. inv INHABITED. inv H.
  Qed.

  Lemma lsim_rev_tid
        tid
        R0 R1 (RR: R0 -> R1 -> (cmra_car M) -> shared_rel)
        r_src tgt shr ps pt r_ctx
        (LSIM: lsim tid RR ps pt r_ctx (Ret r_src) (trigger (GetTid) >>= tgt) shr)
    :
    lsim tid RR ps pt r_ctx (Ret r_src) (tgt tid) shr.
  Proof.
    eapply lsim_reset_prog in LSIM.
    2:{ i. reflexivity. }
    2:{ i. reflexivity. }
    eapply lsim_set_prog in LSIM.
    instantiate (1:=false) in LSIM. instantiate (1:=false) in LSIM.
    punfold LSIM. eapply pind9_unfold in LSIM; auto.
    2:{ eapply _lsim_mon. }
    inv LSIM; auto.
    { eapply f_equal with (f:=observe) in H4. ss. }
    { eapply f_equal with (f:=observe) in H3. ss. }
    { eapply f_equal with (f:=observe) in H3. ss. }
    { eapply f_equal with (f:=observe) in H3. ss. }
    { eapply f_equal with (f:=observe) in H3. ss. }
    { eapply f_equal with (f:=observe) in H3. ss. }
    { eapply f_equal with (f:=observe) in H4. ss. }
    { eapply f_equal with (f:=observe) in H4. ss. }
    { eapply f_equal with (f:=observe) in H4. ss. }
    { eapply trigger_eq_rev in H4. des. subst.
      inv LSIM0. eapply lsim_flag_any. pfold. eauto. }
    { eapply f_equal with (f:=observe) in H4. ss. }
    { eapply f_equal with (f:=observe) in H4. ss. }
    { eapply f_equal with (f:=observe) in H4. ss. }
    { eapply f_equal with (f:=observe) in H4. ss. }
    { eapply f_equal with (f:=observe) in H4. ss. }
    { eapply f_equal with (f:=observe) in H4. ss. }
  Qed.

  Lemma lsim_rev_UB
        tid
        R0 R1 (RR: R0 -> R1 -> (cmra_car M) -> shared_rel)
        r_src tgt shr ps pt r_ctx
        (LSIM: lsim tid RR ps pt r_ctx (Ret r_src) (trigger (Undefined) >>= tgt) shr)
    :
    False.
  Proof.
    eapply lsim_reset_prog in LSIM.
    2:{ i. reflexivity. }
    2:{ i. reflexivity. }
    eapply lsim_set_prog in LSIM.
    instantiate (1:=false) in LSIM. instantiate (1:=false) in LSIM.
    punfold LSIM. eapply pind9_unfold in LSIM; auto.
    2:{ eapply _lsim_mon. }
    inv LSIM; auto.
    { eapply f_equal with (f:=observe) in H4. ss. }
    { eapply f_equal with (f:=observe) in H3. ss. }
    { eapply f_equal with (f:=observe) in H3. ss. }
    { eapply f_equal with (f:=observe) in H3. ss. }
    { eapply f_equal with (f:=observe) in H3. ss. }
    { eapply f_equal with (f:=observe) in H3. ss. }
    { eapply f_equal with (f:=observe) in H4. ss. }
    { eapply f_equal with (f:=observe) in H4. ss. }
    { eapply trigger_eq_rev in H4. des. exfalso.
      clear - H4 H0 H1. subst. dependent destruction H0.
    }
    { eapply f_equal with (f:=observe) in H4. ss. }
    { eapply f_equal with (f:=observe) in H4. ss. }
    { eapply f_equal with (f:=observe) in H4. ss. }
    { eapply f_equal with (f:=observe) in H4. ss. }
    { eapply f_equal with (f:=observe) in H4. ss. }
    { eapply f_equal with (f:=observe) in H4. ss. }
    { eapply f_equal with (f:=observe) in H4. ss. }
  Qed.

  Lemma lsim_rev_yield
        tid
        R0 R1 (RR: R0 -> R1 -> (cmra_car M) -> shared_rel)
        r_src tgt shr ps pt r_ctx
        (LSIM: lsim tid RR ps pt r_ctx (Ret r_src) (trigger (Yield) >>= tgt) shr)
    :
    False.
  Proof.
    eapply lsim_reset_prog in LSIM.
    2:{ i. reflexivity. }
    2:{ i. reflexivity. }
    eapply lsim_set_prog in LSIM.
    instantiate (1:=false) in LSIM. instantiate (1:=false) in LSIM.
    punfold LSIM. eapply pind9_unfold in LSIM; auto.
    2:{ eapply _lsim_mon. }
    inv LSIM; auto.
    { eapply f_equal with (f:=observe) in H4. ss. }
    { eapply f_equal with (f:=observe) in H3. ss. }
    { eapply f_equal with (f:=observe) in H3. ss. }
    { eapply f_equal with (f:=observe) in H3. ss. }
    { eapply f_equal with (f:=observe) in H3. ss. }
    { eapply f_equal with (f:=observe) in H3. ss. }
    { eapply f_equal with (f:=observe) in H4. ss. }
    { eapply f_equal with (f:=observe) in H4. ss. }
    { eapply f_equal with (f:=observe) in H4. ss. }
    { eapply f_equal with (f:=observe) in H4. ss. }
    { eapply f_equal with (f:=observe) in H4. ss. }
    { eapply f_equal with (f:=observe) in H3. ss. }
    { eapply f_equal with (f:=observe) in H3. ss. }
    { eapply f_equal with (f:=observe) in H3. ss. }
    { eapply f_equal with (f:=observe) in H3. ss. }
    { eapply f_equal with (f:=observe) in H3. ss. }
  Qed.

  Lemma nat_not_unit
    :
    (nat: Type) <> unit.
  Proof.
    ii. assert (exists (u0 u1: nat), u0 <> u1).
    { exists 0, 1. ss. }
    rewrite comm in H. rewrite <- H in H0. des. destruct u0, u1. ss.
  Qed.

  Lemma lsim_rev_fair
        tid
        R0 R1 (RR: R0 -> R1 -> (cmra_car M) -> shared_rel)
        r_src tgt ths im_src im_tgt st_src st_tgt ps pt r_ctx
        f
        (LSIM: lsim tid RR ps pt r_ctx (Ret r_src) (trigger (Fair f) >>= tgt) (ths, im_src, im_tgt, st_src, st_tgt))
    :
    forall im_tgt1
           (FAIR: fair_update im_tgt im_tgt1 (prism_fmap inrp f)),
      (<<LSIM: lsim tid RR ps pt r_ctx (Ret r_src) (tgt tt) (ths, im_src, im_tgt1, st_src, st_tgt)>>).
  Proof.
    eapply lsim_reset_prog in LSIM.
    2:{ i. reflexivity. }
    2:{ i. reflexivity. }
    eapply lsim_set_prog in LSIM.
    instantiate (1:=false) in LSIM. instantiate (1:=false) in LSIM.
    punfold LSIM. eapply pind9_unfold in LSIM; auto.
    2:{ eapply _lsim_mon. }
    inv LSIM; auto.
    { eapply f_equal with (f:=observe) in H4. ss. }
    { eapply f_equal with (f:=observe) in H3. ss. }
    { eapply f_equal with (f:=observe) in H3. ss. }
    { eapply f_equal with (f:=observe) in H3. ss. }
    { eapply f_equal with (f:=observe) in H3. ss. }
    { eapply f_equal with (f:=observe) in H3. ss. }
    { eapply f_equal with (f:=observe) in H4. ss. }
    { eapply trigger_eq_rev in H4. des. subst. dependent destruction H0. }
    { eapply trigger_eq_rev in H4. des. subst. dependent destruction H0. }
    { eapply trigger_eq_rev in H4. des. exfalso.
      eapply nat_not_unit; ss.
    }
    { eapply trigger_eq_rev in H4. des. subst. dependent destruction H0.
      i. specialize (LSIM0 _ FAIR).
      inv LSIM0. eapply lsim_flag_any. pfold. eauto.
    }
    { eapply trigger_eq_rev in H4. des. exfalso.
      eapply nat_not_unit; eauto.
    }
    { eapply f_equal with (f:=observe) in H3. ss. }
    { eapply f_equal with (f:=observe) in H3. ss. }
    { eapply f_equal with (f:=observe) in H3. ss. }
    { eapply f_equal with (f:=observe) in H3. ss. }
  Qed.

  Lemma lsim_monoR
        tid
        R0 R1 (RR0 RR1: R0 -> R1 -> (cmra_car M) -> shared_rel)
        p_src p_tgt st ps pt r_ctx
        (LSIM: lsim tid RR0 ps pt r_ctx p_src p_tgt st)
        (MON: forall r_src r_tgt r_ctx shr (RET: RR0 r_src r_tgt r_ctx shr),
            RR1 r_src r_tgt r_ctx shr)
    :
    lsim tid RR1 ps pt r_ctx p_src p_tgt st.
  Proof.
    ginit. guclo lsim_monoC_spec. econs; eauto. gfinal. auto.
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
    forall im_tgt1
      (TID_TGT : fair_update im_tgt0 im_tgt1 (prism_fmap inlp (fun i => if tid_dec i tid then Flag.success else Flag.emp))),
    exists r_shared1 r_own,
      (<<INV: I (ths1, im_src0, im_tgt1, st_src0, st_tgt0) r_shared1>>) /\
        (<<VALID: ✓ (r_shared1 ⋅ r_own ⋅ r_ctx0)>>) /\
        (forall ths im_src1 im_tgt2 st_src2 st_tgt2 r_shared2 r_ctx2
           (INV: I (ths, im_src1, im_tgt2, st_src2, st_tgt2) r_shared2)
                (VALID: ✓ (r_shared2 ⋅ r_own ⋅ r_ctx2)),
          forall im_tgt3 (TGT: fair_update im_tgt2 im_tgt3 (prism_fmap inlp (tids_fmap tid ths))),
            (<<LSIM: forall fs ft,
                lsim
                  tid
                  (@local_RR R0 R1 RR tid)
                  fs ft
                  r_ctx2
                  src tgt
                  (ths, im_src1, im_tgt3, st_src2, st_tgt2)
                  >>)).

  Definition local_sim_init {R0 R1} (RR: R0 -> R1 -> Prop) (r_own: (cmra_car M)) tid src tgt :=
    forall ths im_src im_tgt st_src st_tgt r_shared r_ctx
           (INV: I (ths, im_src, im_tgt, st_src, st_tgt) r_shared)
           (VALID: ✓ (r_shared ⋅ r_own ⋅ r_ctx)),
    forall im_tgt1 (FAIR: fair_update im_tgt im_tgt1 (prism_fmap inlp (tids_fmap tid ths))),
    forall fs ft,
      lsim
        tid
        (@local_RR R0 R1 RR tid)
        fs ft
        r_ctx
        src tgt
        (ths, im_src, im_tgt1, st_src, st_tgt).

End PRIMIVIESIM.
#[export] Hint Constructors __lsim: core.
#[export] Hint Unfold lsim: core.
#[export] Hint Resolve __lsim_mon: paco.
#[export] Hint Resolve _lsim_mon: paco.
#[export] Hint Resolve lsim_mon: paco.
#[export] Hint Resolve cpn9_wcompat: paco.

Section EQUIVI.

  Context `{M: ucmra}.

  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable ident_src: ID.
  Variable _ident_tgt: ID.
  Local Notation ident_tgt := (ident_tgt _ident_tgt).

  Variable wf_src: WF.
  Variable wf_tgt: WF.

  Let srcE := threadE ident_src state_src.
  Let tgtE := threadE _ident_tgt state_tgt.

  Local Notation shared := (shared state_src state_tgt ident_src _ident_tgt wf_src wf_tgt).

  Let shared_rel: Type := shared -> Prop.
  (* Variable I: shared -> (cmra_car M) -> Prop. *)

  Lemma __lsim_equivI tid
        (I1 I2 : shared -> (cmra_car M) -> Prop)
        (EQ : forall shr (m : (cmra_car M)) (WF : ✓ m), I1 shr m <-> I2 shr m)
    :
    __lsim I1 tid <11= __lsim I2 tid.
  Proof.
    i. ss. inv PR; try (econs; eauto; fail).
    { eapply lsim_yieldR.
      - eapply EQ. 2: apply INV. do 2 eapply cmra_valid_op_l. eauto.
      - eauto.
      - i. eapply LSIM. 3: apply TGT. 2: apply VALID0. apply EQ; auto. do 2 eapply cmra_valid_op_l. eauto.
    }
    { eapply lsim_sync.
      - eapply EQ. 2: apply INV. do 2 eapply cmra_valid_op_l. eauto.
      - eauto.
      - i. eapply LSIM. 3: apply TGT. 2: apply VALID0. apply EQ; auto. do 2 eapply cmra_valid_op_l. eauto.
    }
  Qed.

  Lemma _lsim_equivI tid
        (I1 I2 : shared -> (cmra_car M) -> Prop)
        (EQ : forall shr (m : (cmra_car M)) (WF : ✓ m), I1 shr m <-> I2 shr m)
        r
    :
    pind9 (__lsim I1 tid r) top9
    <9=
      pind9 (__lsim I2 tid r) top9.
  Proof.
    i. eapply pind9_mon_gen. eapply PR. 2: auto.
    i. eapply __lsim_equivI; eauto.
  Qed.

  Lemma lsim_equivI tid
        (I1 I2 : shared -> (cmra_car M) -> Prop)
        (EQ : forall shr (m : (cmra_car M)) (WF : ✓ m), I1 shr m <-> I2 shr m)
    :
    gpaco9 (fun r => pind9 (__lsim I1 tid r) top9) (cpn9 (fun r => pind9 (__lsim I1 tid r) top9))
            <11=
      gpaco9 (fun r => pind9 (__lsim I2 tid r) top9) (cpn9 (fun r => pind9 (__lsim I2 tid r) top9)).
  Proof.
    ss. i. eapply gpaco9_mon_gen. eapply PR. all: i; ss; auto with paco.
    2:{ inv PR0. econs. 2: apply CLO. inv COM. econs; auto.
        i. exploit compat9_compat.
        { eapply compat9_mon. apply PR0. i. eapply _lsim_equivI. 2: apply PR1. clear - EQ. i. rewrite EQ; auto. }
        { i. eapply _lsim_equivI. 2: apply x30. clear - EQ. i. rewrite EQ; auto. }
    }
    { eapply _lsim_equivI. 2: apply PR0. clear - EQ. i. rewrite EQ; auto. }
  Qed.

End EQUIVI.

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
          init: forall im_tgt,
          exists (I: (@shared md_src.(Mod.state) md_tgt.(Mod.state) md_src.(Mod.ident) md_tgt.(Mod.ident) wf_src wf_tgt) -> world -> Prop),
          (exists im_src r_shared,
            (I (NatSet.empty, im_src, im_tgt, md_src.(Mod.st_init), md_tgt.(Mod.st_init)) r_shared) /\
              (✓ r_shared)) /\
          (forall fn args, match md_src.(Mod.funs) fn, md_tgt.(Mod.funs) fn with
                           | Some ktr_src, Some ktr_tgt => local_sim I (@eq Any.t) (ktr_src args) (ktr_tgt args)
                           | None, None => True
                           | _, _ => False
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

          (* I: (@shared md_src.(Mod.state) md_tgt.(Mod.state) md_src.(Mod.ident) md_tgt.(Mod.ident) wf_src wf_tgt) -> world -> Prop; *)
          funs: forall im_tgt,
            exists (I: (@shared md_src.(Mod.state) md_tgt.(Mod.state) md_src.(Mod.ident) md_tgt.(Mod.ident) wf_src wf_tgt) -> world -> Prop),
          exists im_src rs r_shared,
            (<<INIT: I (key_set p_src, im_src, im_tgt, md_src.(Mod.st_init), md_tgt.(Mod.st_init)) r_shared>>) /\
              (<<SIM: Forall3
                        (fun '(t1, src) '(t2, tgt) '(t3, r) =>
                           t1 = t2 /\ t1 = t3 /\
                           @local_sim_init _ md_src.(Mod.state) md_tgt.(Mod.state) md_src.(Mod.ident) md_tgt.(Mod.ident) wf_src wf_tgt I _ _ (@eq Any.t) r t1 src tgt)
                        (Th.elements p_src) (Th.elements p_tgt) (NatMap.elements rs)>>) /\
              (<<WF: ✓ (r_shared ⋅ NatMap.fold (fun _ r s => r ⋅ s) rs ε)>>)
        }.
  End MODSIM.
End UserSim.
