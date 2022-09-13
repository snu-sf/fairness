From sflib Require Import sflib.
From Paco Require Import paco.
Require Export Coq.Strings.String.
Require Import Coq.Classes.RelationClasses.

From Fairness Require Export ITreeLib FairBeh Mod.
From Fairness Require Import pind.
From Fairness Require Import PCM.
From Fairness Require Import PindTac.

Set Implicit Arguments.



Section PRIMIVIESIM.
  Context `{M: URA.t}.

  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable ident_src: ID.
  Variable _ident_tgt: ID.
  Definition ident_tgt := sum_tid _ident_tgt.

  Variable wf_src: WF.

  Let srcE := ((@eventE ident_src +' cE) +' sE state_src).
  Let tgtE := ((@eventE _ident_tgt +' cE) +' sE state_tgt).

  Definition shared :=
    (TIdSet.t *
       (@imap ident_src wf_src) *
       (@imap ident_tgt nat_wf) *
       state_src *
       state_tgt)%type.

  Let shared_rel: Type := shared -> Prop.

  Variable I: shared -> URA.car -> Prop.

  Variant __lsim
          (tid: thread_id)
          (lsim: forall R_src R_tgt (RR: R_src -> R_tgt -> URA.car -> shared_rel), URA.car -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel)
          (_lsim: forall R_src R_tgt (RR: R_src -> R_tgt -> URA.car -> shared_rel), URA.car -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel)
          R_src R_tgt (RR: R_src -> R_tgt -> URA.car -> shared_rel)
    :
    URA.car -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel :=
  | lsim_ret
      r_ctx
      ths im_src im_tgt st_src st_tgt
      r_src r_tgt
      (LSIM: RR r_src r_tgt r_ctx (ths, im_src, im_tgt, st_src, st_tgt))
    :
    __lsim tid lsim _lsim RR r_ctx (Ret r_src) (Ret r_tgt) (ths, im_src, im_tgt, st_src, st_tgt)

  | lsim_tauL
      r_ctx
      ths im_src im_tgt st_src st_tgt
      itr_src itr_tgt
      (LSIM: _lsim _ _ RR r_ctx itr_src itr_tgt (ths, im_src, im_tgt, st_src, st_tgt))
    :
    __lsim tid lsim _lsim RR r_ctx (Tau itr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt)
  | lsim_chooseL
      r_ctx
      ths im_src im_tgt st_src st_tgt
      X ktr_src itr_tgt
      (LSIM: exists x, _lsim _ _ RR r_ctx (ktr_src x) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt))
    :
    __lsim tid lsim _lsim RR r_ctx (trigger (Choose X) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt)
  | lsim_putL
      r_ctx
      ths im_src im_tgt st_src st_tgt
      st ktr_src itr_tgt
      (LSIM: _lsim _ _ RR r_ctx (ktr_src tt) itr_tgt (ths, im_src, im_tgt, st, st_tgt))
    :
    __lsim tid lsim _lsim RR r_ctx (trigger (Put st) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt)
  | lsim_getL
      r_ctx
      ths im_src im_tgt st_src st_tgt
      ktr_src itr_tgt
      (LSIM: _lsim _ _ RR r_ctx (ktr_src st_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt))
    :
    __lsim tid lsim _lsim RR r_ctx (trigger (@Get _) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt)
  | lsim_tidL
      r_ctx
      ths im_src im_tgt st_src st_tgt
      ktr_src itr_tgt
      (LSIM: _lsim _ _ RR r_ctx (ktr_src tid) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt))
    :
    __lsim tid lsim _lsim RR r_ctx (trigger (GetTid) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt)
  | lsim_UB
      r_ctx
      ths im_src im_tgt st_src st_tgt
      ktr_src itr_tgt
    :
    __lsim tid lsim _lsim RR r_ctx (trigger (Undefined) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt)
  | lsim_fairL
      r_ctx
      ths im_src0 im_tgt st_src st_tgt
      f ktr_src itr_tgt
      (LSIM: exists im_src1,
          (<<FAIR: fair_update im_src0 im_src1 f>>) /\
            (<<LSIM: _lsim _ _ RR r_ctx (ktr_src tt) itr_tgt (ths, im_src1, im_tgt, st_src, st_tgt)>>))
    :
    __lsim tid lsim _lsim RR r_ctx (trigger (Fair f) >>= ktr_src) itr_tgt (ths, im_src0, im_tgt, st_src, st_tgt)

  | lsim_tauR
      r_ctx
      ths im_src im_tgt st_src st_tgt
      itr_src itr_tgt
      (LSIM: _lsim _ _ RR r_ctx itr_src itr_tgt (ths, im_src, im_tgt, st_src, st_tgt))
    :
    __lsim tid lsim _lsim RR r_ctx itr_src (Tau itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)
  | lsim_chooseR
      r_ctx
      ths im_src im_tgt st_src st_tgt
      X itr_src ktr_tgt
      (LSIM: forall x, _lsim _ _ RR r_ctx itr_src (ktr_tgt x) (ths, im_src, im_tgt, st_src, st_tgt))
    :
    __lsim tid lsim _lsim RR r_ctx itr_src (trigger (Choose X) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)
  | lsim_putR
      r_ctx
      ths im_src im_tgt st_src st_tgt
      st itr_src ktr_tgt
      (LSIM: _lsim _ _ RR r_ctx itr_src (ktr_tgt tt) (ths, im_src, im_tgt, st_src, st))
    :
    __lsim tid lsim _lsim RR r_ctx itr_src (trigger (Put st) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)
  | lsim_getR
      r_ctx
      ths im_src im_tgt st_src st_tgt
      itr_src ktr_tgt
      (LSIM: _lsim _ _ RR r_ctx itr_src (ktr_tgt st_tgt) (ths, im_src, im_tgt, st_src, st_tgt))
    :
    __lsim tid lsim _lsim RR r_ctx itr_src (trigger (@Get _) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)
  | lsim_tidR
      r_ctx
      ths im_src im_tgt st_src st_tgt
      itr_src ktr_tgt
      (LSIM: _lsim _ _ RR r_ctx itr_src (ktr_tgt tid) (ths, im_src, im_tgt, st_src, st_tgt))
    :
    __lsim tid lsim _lsim RR r_ctx itr_src (trigger (GetTid) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)
  | lsim_fairR
      r_ctx
      ths im_src im_tgt0 st_src st_tgt
      f itr_src ktr_tgt
      (LSIM: forall im_tgt1
                   (FAIR: fair_update im_tgt0 im_tgt1 (sum_fmap_r f)),
          (<<LSIM: _lsim _ _ RR r_ctx itr_src (ktr_tgt tt) (ths, im_src, im_tgt1, st_src, st_tgt)>>))
    :
    __lsim tid lsim _lsim RR r_ctx itr_src (trigger (Fair f) >>= ktr_tgt) (ths, im_src, im_tgt0, st_src, st_tgt)

  | lsim_observe
      r_ctx
      ths im_src im_tgt st_src st_tgt
      fn args ktr_src ktr_tgt
      (LSIM: forall ret,
          _lsim _ _ RR r_ctx (ktr_src ret) (ktr_tgt ret) (ths, im_src, im_tgt, st_src, st_tgt))
    :
    __lsim tid lsim _lsim RR r_ctx (trigger (Observe fn args) >>= ktr_src) (trigger (Observe fn args) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)

  | lsim_yieldL
      r_ctx
      ths im_src im_tgt st_src st_tgt
      ktr_src itr_tgt
      (LSIM: _lsim _ _ RR r_ctx (ktr_src tt) (trigger (Yield) >>= itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt))
    :
    __lsim tid lsim _lsim RR r_ctx (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)
  | lsim_yieldR
      r_ctx0
      ths0 im_src0 im_tgt0 st_src0 st_tgt0
      r_own r_shared
      ktr_src ktr_tgt
      (INV: I (ths0, im_src0, im_tgt0, st_src0, st_tgt0) r_shared)
      (VALID: URA.wf (r_shared ⋅ r_own ⋅ r_ctx0))
      (LSIM: forall ths1 im_src1 im_tgt1 st_src1 st_tgt1 r_shared1 r_ctx1
                    (INV: I (ths1, im_src1, im_tgt1, st_src1, st_tgt1) r_shared1)
                    (VALID: URA.wf (r_shared1 ⋅ r_own ⋅ r_ctx1))
                    im_tgt2
                    (TGT: fair_update im_tgt1 im_tgt2 (sum_fmap_l (tids_fmap_all ths1))),
          _lsim _ _ RR r_ctx1 (trigger (Yield) >>= ktr_src) (ktr_tgt tt) (ths1, im_src1, im_tgt2, st_src1, st_tgt1))
    :
    __lsim tid lsim _lsim RR r_ctx0 (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt) (ths0, im_src0, im_tgt0, st_src0, st_tgt0)

  | lsim_yield
      r_ctx0
      ths0 im_src0 im_tgt0 st_src0 st_tgt0
      r_own r_shared
      ktr_src ktr_tgt
      (INV: I (ths0, im_src0, im_tgt0, st_src0, st_tgt0) r_shared)
      (VALID: URA.wf (r_shared ⋅ r_own ⋅ r_ctx0))
      (LSIM: forall ths1 im_src1 im_tgt1 st_src1 st_tgt1 r_shared1 r_ctx1
               (INV: I (ths1, im_src1, im_tgt1, st_src1, st_tgt1) r_shared1)
               (VALID: URA.wf (r_shared1 ⋅ r_own ⋅ r_ctx1))
               im_tgt2
               (TGT: fair_update im_tgt1 im_tgt2 (sum_fmap_l (tids_fmap_all ths1))),
          (<<LSIM: _lsim _ _ RR r_ctx1 (ktr_src tt) (ktr_tgt tt) (ths1, im_src1, im_tgt2, st_src1, st_tgt1)>>))
    :
    __lsim tid lsim _lsim RR r_ctx0 (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt) (ths0, im_src0, im_tgt0, st_src0, st_tgt0)

  | lsim_sync
      r_ctx0
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
          (<<LSIM: lsim _ _ RR r_ctx1 (ktr_src tt) (ktr_tgt tt) (ths1, im_src1, im_tgt2, st_src1, st_tgt1)>>))
    :
    __lsim tid lsim _lsim RR r_ctx0 (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt) (ths0, im_src0, im_tgt0, st_src0, st_tgt0)
  .

  Definition lsim (tid: thread_id)
             R_src R_tgt (RR: R_src -> R_tgt -> URA.car -> shared_rel):
    URA.car -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel :=
    paco7 (fun r => pind7 (__lsim tid r) top7) bot7 R_src R_tgt RR.

  Lemma __lsim_mon tid:
    forall r r' (LE: r <7= r'), (__lsim tid r) <8= (__lsim tid r').
  Proof.
    ii. inv PR; try (econs; eauto; fail).
    eapply lsim_sync; eauto. i. hexploit LSIM. eapply INV0. eapply VALID0. all: eauto.
  Qed.

  Lemma _lsim_mon tid: forall r, monotone7 (__lsim tid r).
  Proof.
    ii. inv IN; try (econs; eauto; fail).
    { des. econs; eauto. }
    { des. econs; eauto. }
    { econs. i. eapply LE. eapply LSIM. eauto. }
    { eapply lsim_yield; eauto. i. eapply LE. eapply LSIM; eauto. }
  Qed.

  Lemma lsim_mon tid: forall q, monotone7 (fun r => pind7 (__lsim tid r) q).
  Proof.
    ii. eapply pind7_mon_gen; eauto.
    ii. eapply __lsim_mon; eauto.
  Qed.
  Hint Resolve lsim_mon: paco.
  Hint Resolve cpn7_wcompat: paco.

  From Paco Require Import pacotac_internal.

  Lemma lsim_acc_gen
        tid r
        (A: Type)
        (f0: forall (a: A), Type)
        (f1: forall (a: A), Type)
        (f2: forall (a: A), f0 a -> f1 a -> URA.car -> shared_rel)
        (f3: forall (a: A), URA.car)
        (f4: forall (a: A), itree srcE (f0 a))
        (f5: forall (a: A), itree tgtE (f1 a))
        (f6: forall (a: A), shared)
        r0 (q: A -> Prop)
        (IND: forall r1
                     (LE: r1 <7= r0)
                     (IH: forall a, @r1 (f0 a) (f1 a) (f2 a) (f3 a) (f4 a) (f5 a) (f6 a) -> q a),
          forall a, pind7 (__lsim tid r) r1 (f0 a) (f1 a) (f2 a) (f3 a) (f4 a) (f5 a) (f6 a) -> q a)
    :
    forall a, pind7 (__lsim tid r) r0 (f0 a) (f1 a) (f2 a) (f3 a) (f4 a) (f5 a) (f6 a) -> q a.
  Proof.
    cut ((pind7 (__lsim tid r) r0) <7= curry7 (fun x => forall a (EQ: @exist7T _ _ _ _ _ _ _ (f0 a) (f1 a) (f2 a) (f3 a) (f4 a) (f5 a) (f6 a) = x), q a)).
    { exact (fun P a H => uncurry_adjoint2_7 P (@exist7T _ _ _ _ _ _ _ (f0 a) (f1 a) (f2 a) (f3 a) (f4 a) (f5 a) (f6 a)) H a eq_refl). }
    { exact (@pind7_acc _ _ _ _ _ _ _ (__lsim tid r) (curry7 (fun x => forall a (EQ: @exist7T _ _ _ _ _ _ _ (f0 a) (f1 a) (f2 a) (f3 a) (f4 a) (f5 a) (f6 a) = x), q a)) r0 (fun rr LE IH => @uncurry_adjoint1_7 _ _ _ _ _ _ _ (pind7 (__lsim tid r) rr) (fun x => forall a (EQ: @exist7T _ _ _ _ _ _ _ (f0 a) (f1 a) (f2 a) (f3 a) (f4 a) (f5 a) (f6 a) = x), q a) (fun x PR a EQ => IND rr LE (fun a H => IH (f0 a) (f1 a) (f2 a) (f3 a) (f4 a) (f5 a) (f6 a) H a eq_refl) a (@eq_rect _ _ (uncurry7 (pind7 (__lsim tid r) rr)) PR _ (eq_sym EQ))))).
    }
  Qed.

  Ltac pind_gen := patterning 7; refine (@lsim_acc_gen
                                           _ _ _
                                           _ _ _ _ _ _ _
                                           _ _ _).
  Ltac pinduction n := currying n pind_gen.

  (* TODO: add this in pico lib *)
  Lemma lsim_indC_spec tid
    :
    (fun r => __lsim tid r r) <8= gupaco7 (fun r => pind7 (__lsim tid r) top7) (cpn7 (fun r => pind7 (__lsim tid r) top7)).
  Proof.
    eapply wrespect7_uclo; eauto with paco.
    econs.
    { ii. eapply __lsim_mon; eauto. eapply _lsim_mon; eauto. }
    i. eapply pind7_fold.
    eapply __lsim_mon.
    { instantiate (1:=l). i. eapply rclo7_base. eauto. }
    eapply _lsim_mon; eauto. i. split; ss.
    eapply GF in PR0. eapply pind7_mon_gen; eauto.
    i. eapply __lsim_mon.
    { i. eapply rclo7_base. eassumption. }
    eauto.
  Qed.

  Variant lsim_monoC
          (r: forall R_src R_tgt (RR: R_src -> R_tgt -> URA.car -> shared_rel), URA.car -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel)
          R_src R_tgt (RR1: R_src -> R_tgt -> URA.car -> shared_rel)
    :
    URA.car -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel :=
    | lsim_monoC_intro
        (RR0: R_src -> R_tgt -> URA.car -> shared_rel)
        src tgt shr r_ctx
        (MON: forall r_src r_tgt r_ctx shr (RET: RR0 r_src r_tgt r_ctx shr),
            RR1 r_src r_tgt r_ctx shr)
        (REL: r _ _ RR0 r_ctx src tgt shr)
      :
      lsim_monoC r RR1 r_ctx src tgt shr
  .

  Lemma lsim_monoC_spec tid
    :
    lsim_monoC <8= gupaco7 (fun r => pind7 (__lsim tid r) top7) (cpn7 (fun r => pind7 (__lsim tid r) top7)).
  Proof.
    eapply wrespect7_uclo; eauto with paco.
    econs.
    { ii. inv IN. econs; eauto. }
    i. inv PR. eapply GF in REL.
    revert x2 MON.
    pattern x0, x1, RR0, x3, x4, x5, x6.
    revert x0 x1 RR0 x3 x4 x5 x6 REL.
    apply pind7_acc. intros rr _ IH x0 x1 RR0 x3 x4 x5 x6 PR.
    i. eapply pind7_unfold in PR.
    2:{ eapply _lsim_mon. }
    rename PR into LSIM. inv LSIM.

    { eapply pind7_fold. econs; eauto. }

    { destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      eapply pind7_fold. eapply lsim_tauL. split; ss.
      hexploit IH; eauto.
    }

    { des. eapply pind7_fold. eapply lsim_chooseL. esplits; eauto. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { eapply pind7_fold. eapply lsim_putL. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { eapply pind7_fold. eapply lsim_getL. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { eapply pind7_fold. eapply lsim_tidL. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { eapply pind7_fold. eapply lsim_UB. }

    { des. eapply pind7_fold. eapply lsim_fairL. esplits; eauto. split; ss.
      destruct LSIM as [LSIM IND]. hexploit IH; eauto.
    }

    { destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      eapply pind7_fold. eapply lsim_tauR. split; ss.
      hexploit IH. eauto. all: eauto.
    }

    { eapply pind7_fold. eapply lsim_chooseR. i. split; ss. specialize (LSIM0 x).
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { eapply pind7_fold. eapply lsim_putR. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { eapply pind7_fold. eapply lsim_getR. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { eapply pind7_fold. eapply lsim_tidR. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { eapply pind7_fold. eapply lsim_fairR. i. split; ss. specialize (LSIM0 _ FAIR).
      des. destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { eapply pind7_fold. eapply lsim_observe. i. split; ss. specialize (LSIM0 ret).
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { des. eapply pind7_fold. eapply lsim_yieldL. split; ss.
      destruct LSIM0 as [LSIM IND]. hexploit IH; eauto.
    }

    { eapply pind7_fold. eapply lsim_yieldR; eauto. i.
      hexploit LSIM0; eauto. clear LSIM0. intros LSIM0.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. split; ss; eauto.
    }

    { eapply pind7_fold. eapply lsim_yield; eauto. i.
      hexploit LSIM0; eauto. clear LSIM0. intros LSIM0.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. split; ss; eauto.
    }

    { eapply pind7_fold. eapply lsim_sync; eauto. i.
      hexploit LSIM0. eapply INV0. eapply VALID0. all: eauto. i; des. esplits; eauto.
      eapply rclo7_clo_base. econs; eauto.
    }
  Qed.

  Variant lsim_frameC
          (r: forall R_src R_tgt (RR: R_src -> R_tgt -> URA.car -> shared_rel), URA.car -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel)
          R_src R_tgt
          (RR: R_src -> R_tgt -> URA.car -> shared_rel)
    :
    URA.car -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel :=
    | lsim_frameC_intro
        src tgt shr r_ctx r_frame
        (REL: r _ _ (fun r_src r_tgt r_ctx shr =>
                       forall r_ctx' (EQ: r_ctx = r_frame ⋅ r_ctx'),
                         RR r_src r_tgt r_ctx' shr) (r_frame ⋅ r_ctx) src tgt shr)
      :
      lsim_frameC r RR r_ctx src tgt shr
  .

  Lemma lsim_frameC_spec tid
    :
    lsim_frameC <8= gupaco7 (fun r => pind7 (__lsim tid r) top7) (cpn7 (fun r => pind7 (__lsim tid r) top7)).
  Proof.
    eapply grespect7_uclo; eauto with paco.
    econs.
    { ii. inv IN. econs; eauto. }
    i. inv PR. eapply GF in REL.
    eapply rclo7_clo_base. eapply cpn7_gupaco.
    { eauto with paco. }

    remember (r_frame ⋅ x3).
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
    revert x2 r_frame x3 Heqc FRAME.
    pattern x0, x1, RR', c, x4, x5, x6.
    revert x0 x1 RR' c x4 x5 x6 REL.
    apply pind7_acc. intros rr _ IH x0 x1 RR' c x4 x5 x6 PR.
    i. eapply pind7_unfold in PR.
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

    { guclo lsim_indC_spec. eapply lsim_putL.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { guclo lsim_indC_spec. eapply lsim_getL.
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

    { guclo lsim_indC_spec. eapply lsim_putR.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { guclo lsim_indC_spec. eapply lsim_getR.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { guclo lsim_indC_spec. eapply lsim_tidR.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { guclo lsim_indC_spec. eapply lsim_fairR. i. specialize (LSIM0 _ FAIR).
      des. destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { guclo lsim_indC_spec. eapply lsim_observe. i. specialize (LSIM0 ret).
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { des. guclo lsim_indC_spec. eapply lsim_yieldL.
      destruct LSIM0 as [LSIM IND]. hexploit IH; eauto.
    }

    { guclo lsim_indC_spec. eapply lsim_yieldR; eauto.
      { instantiate (1:=r_own ⋅ r_frame). r_wf VALID. }
      i. hexploit LSIM0; eauto.
      { instantiate (1:=r_frame ⋅ r_ctx1). r_wf VALID0. }
      clear LSIM0. intros LSIM0.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { guclo lsim_indC_spec. eapply lsim_yield; eauto.
      { instantiate (1:=r_own ⋅ r_frame). r_wf VALID. }
      i. hexploit LSIM0; eauto.
      { instantiate (1:=r_frame ⋅ r_ctx1). r_wf VALID0. }
      clear LSIM0. intros LSIM0.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { gfinal. left. eapply pind7_fold. eapply lsim_sync; eauto.
      { instantiate (1:=r_own ⋅ r_frame). r_wf VALID. }
      i. hexploit LSIM0; eauto.
      { instantiate (1:=r_frame ⋅ r_ctx1). r_wf VALID0. }
      i. des.
      eapply rclo7_clo. left. econs; eauto.
      eapply rclo7_clo_base. right. guclo lsim_monoC_spec. econs.
      2:{ gbase. eauto. }
      { eauto. }
    }
  Qed.

  Variant lsim_bindC'
          (r: forall R_src R_tgt (RR: R_src -> R_tgt -> URA.car -> shared_rel), URA.car -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel)
          R_src1 R_tgt1
          (RR: R_src1 -> R_tgt1 -> URA.car -> shared_rel)
    :
    URA.car -> itree srcE R_src1 -> itree tgtE R_tgt1 -> shared_rel :=
    | lsim_bindC'_intro
        R_src0 R_tgt0 (RR0: R_src0 -> R_tgt0 -> URA.car -> shared_rel)
        itr_src itr_tgt ktr_src ktr_tgt shr r_ctx
        (REL: r _ _ RR0 r_ctx itr_src itr_tgt shr)
        (MON: forall r_src r_tgt r_ctx shr
                     (SAT: RR0 r_src r_tgt r_ctx shr),
            r _ _ RR r_ctx (ktr_src r_src) (ktr_tgt r_tgt) shr)
      :
      lsim_bindC' r RR r_ctx (itr_src >>= ktr_src) (itr_tgt >>= ktr_tgt) shr
  .

  Lemma lsim_bindC'_spec tid
    :
    lsim_bindC' <8= gupaco7 (fun r => pind7 (__lsim tid r) top7) (cpn7 (fun r => pind7 (__lsim tid r) top7)).
  Proof.
    assert (HINT: forall r1, monotone7 (fun r0 => pind7 (__lsim tid r0) r1)).
    { ii. eapply pind7_mon_gen; eauto. i. eapply __lsim_mon; eauto. }
    eapply grespect7_uclo; eauto with paco.
    econs.
    { ii. inv IN. econs; eauto. }
    i. inv PR. eapply GF in REL.
    eapply rclo7_clo_base. eapply cpn7_gupaco.
    { eauto with paco. }

    revert ktr_src ktr_tgt MON.
    pattern R_src0, R_tgt0, RR0, x3, itr_src, itr_tgt, x6.
    revert R_src0 R_tgt0 RR0 x3 itr_src itr_tgt x6 REL.
    apply pind7_acc. intros rr _ IH R_src0 R_tgt0 RR0 x3 itr_src itr_tgt x6 PR.
    i. eapply pind7_unfold in PR.
    2:{ eapply _lsim_mon. }
    rename PR into LSIM. inv LSIM; ired.

    { eapply MON in LSIM0. eapply GF in LSIM0.
      gfinal. left. eapply pind7_mon_gen; eauto. i. ss.
      eapply __lsim_mon.
      { i. eapply rclo7_base. eassumption. }
      eauto.
    }

    Notation cpn := (cpn7 _).
    Notation pind := (fun r => pind7 (__lsim _ r) top7).
    ss.

    { destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      guclo lsim_indC_spec. eapply lsim_tauL.
      hexploit IH; eauto.
    }

    { des. guclo lsim_indC_spec. eapply lsim_chooseL. esplits; eauto.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { guclo lsim_indC_spec. eapply lsim_putL.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { guclo lsim_indC_spec. eapply lsim_getL.
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

    { guclo lsim_indC_spec. eapply lsim_putR.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { guclo lsim_indC_spec. eapply lsim_getR.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { guclo lsim_indC_spec. eapply lsim_tidR.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { guclo lsim_indC_spec. eapply lsim_fairR. i. specialize (LSIM0 _ FAIR).
      des. destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { guclo lsim_indC_spec. eapply lsim_observe. i. specialize (LSIM0 ret).
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
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

    { guclo lsim_indC_spec. eapply lsim_yield; eauto.
      i. hexploit LSIM0; eauto.
      clear LSIM0. intros LSIM0.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto.
    }

    { gfinal. left. eapply pind7_fold. eapply lsim_sync; eauto.
      i. hexploit LSIM0; eauto.
      i. des. eapply rclo7_clo_base. left. econs; eauto.
    }
  Qed.

  Variant lsim_bindC
          (r: forall R_src R_tgt (RR: R_src -> R_tgt -> URA.car -> shared_rel), URA.car -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel)
          R_src1 R_tgt1
          (RR: R_src1 -> R_tgt1 -> URA.car -> shared_rel)
    :
    URA.car -> itree srcE R_src1 -> itree tgtE R_tgt1 -> shared_rel :=
    | lsim_bindC_intro
        R_src0 R_tgt0
        itr_src itr_tgt ktr_src ktr_tgt shr r_ctx
        (REL: r _ _ (fun (r_src: R_src0) (r_tgt: R_tgt0) r_ctx shr => r _ _ RR r_ctx (ktr_src r_src) (ktr_tgt r_tgt) shr) r_ctx itr_src itr_tgt shr)
      :
      lsim_bindC r RR r_ctx (itr_src >>= ktr_src) (itr_tgt >>= ktr_tgt) shr
  .

  Lemma lsim_bindC_spec tid
    :
    lsim_bindC <8= gupaco7 (fun r => pind7 (__lsim tid r) top7) (cpn7 (fun r => pind7 (__lsim tid r) top7)).
  Proof.
    i. eapply lsim_bindC'_spec. inv PR. econs; eauto.
  Qed.

  Variant lsim_bindRC'
          (r: forall R_src R_tgt (RR: R_src -> R_tgt -> URA.car -> shared_rel), URA.car -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel)
          R_src1 R_tgt1
          (RR: R_src1 -> R_tgt1 -> URA.car -> shared_rel)
    :
    URA.car -> itree srcE R_src1 -> itree tgtE R_tgt1 -> shared_rel :=
    | lsim_bindRC'_intro
        R_tgt0 (RR0: R_tgt0 -> URA.car -> shared_rel)
        itr_tgt ktr_src ktr_tgt shr r_ctx
        (REL: r _ _ (fun _ => RR0) r_ctx (trigger Yield) itr_tgt shr)
        (MON: forall r_tgt r_ctx shr
                     (SAT: RR0 r_tgt r_ctx shr),
            r _ _ RR r_ctx (trigger Yield >>= ktr_src) (ktr_tgt r_tgt) shr)
      :
      lsim_bindRC' r RR r_ctx (trigger Yield >>= ktr_src) (itr_tgt >>= ktr_tgt) shr
  .

  Require Import Program.

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
    forall im_tgt1
      (TID_TGT : fair_update im_tgt0 im_tgt1 (sum_fmap_l (fun i => if tid_dec i tid then Flag.success else Flag.emp))),
    exists r_shared1 r_own,
      (<<INV: I (ths1, im_src0, im_tgt1, st_src0, st_tgt0) r_shared1>>) /\
        (<<VALID: URA.wf (r_shared1 ⋅ r_own ⋅ r_ctx0)>>) /\
        (forall ths im_src1 im_tgt2 st_src2 st_tgt2 r_shared2 r_ctx2
           (INV: I (ths, im_src1, im_tgt2, st_src2, st_tgt2) r_shared2)
                (VALID: URA.wf (r_shared2 ⋅ r_own ⋅ r_ctx2)),
          forall im_tgt3 (TGT: fair_update im_tgt2 im_tgt3 (sum_fmap_l (tids_fmap tid ths))),
            (<<LSIM: lsim
                       tid
                       (@local_RR R0 R1 RR tid)
                       r_ctx2
                       src tgt
                       (ths, im_src1, im_tgt3, st_src2, st_tgt2)
                       >>)).

End PRIMIVIESIM.
#[export] Hint Constructors __lsim: core.
#[export] Hint Unfold lsim: core.
#[export] Hint Resolve __lsim_mon: paco.
#[export] Hint Resolve _lsim_mon: paco.
#[export] Hint Resolve lsim_mon: paco.
#[export] Hint Resolve cpn7_wcompat: paco.


Module ModSim.
  Section MODSIM.

    Variable md_src: Mod.t.
    Variable md_tgt: Mod.t.

    Record mod_sim: Prop :=
      mk {
          wf_src : WF;

          world: URA.t;

          I: (@shared md_src.(Mod.state) md_tgt.(Mod.state) md_src.(Mod.ident) md_tgt.(Mod.ident) wf_src) -> world -> Prop;
          init: forall im_tgt, exists im_src r_shared,
            (I (NatSet.empty, im_src, im_tgt, md_src.(Mod.st_init), md_tgt.(Mod.st_init)) r_shared) /\
              (URA.wf r_shared);

          funs: forall fn args, match md_src.(Mod.funs) fn, md_tgt.(Mod.funs) fn with
                           | Some ktr_src, Some ktr_tgt => local_sim I (@eq Val) (ktr_src args) (ktr_tgt args)
                           | None, None => True
                           | _, _ => False
                           end;
        }.
  End MODSIM.
End ModSim.
