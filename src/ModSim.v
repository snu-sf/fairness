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

  Variant __lsim
          (tid: thread_id)
          (lsim: forall R_src R_tgt (RR: R_src -> R_tgt -> URA.car -> shared_rel), bool -> bool -> URA.car -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel)
          (_lsim: forall R_src R_tgt (RR: R_src -> R_tgt -> URA.car -> shared_rel),bool -> bool -> URA.car -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel)
          R_src R_tgt (RR: R_src -> R_tgt -> URA.car -> shared_rel)
    :
    bool -> bool -> URA.car -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel :=
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
  | lsim_putL
      f_src f_tgt r_ctx
      ths im_src im_tgt st_src st_tgt
      st ktr_src itr_tgt
      (LSIM: _lsim _ _ RR true f_tgt r_ctx (ktr_src tt) itr_tgt (ths, im_src, im_tgt, st, st_tgt))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx (trigger (Put st) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt)
  | lsim_getL
      f_src f_tgt r_ctx
      ths im_src im_tgt st_src st_tgt
      ktr_src itr_tgt
      (LSIM: _lsim _ _ RR true f_tgt r_ctx (ktr_src st_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx (trigger (@Get _) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt)
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
  | lsim_putR
      f_src f_tgt r_ctx
      ths im_src im_tgt st_src st_tgt
      st itr_src ktr_tgt
      (LSIM: _lsim _ _ RR f_src true r_ctx itr_src (ktr_tgt tt) (ths, im_src, im_tgt, st_src, st))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx itr_src (trigger (Put st) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)
  | lsim_getR
      f_src f_tgt r_ctx
      ths im_src im_tgt st_src st_tgt
      itr_src ktr_tgt
      (LSIM: _lsim _ _ RR f_src true r_ctx itr_src (ktr_tgt st_tgt) (ths, im_src, im_tgt, st_src, st_tgt))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx itr_src (trigger (@Get _) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)
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
                   (FAIR: fair_update im_tgt0 im_tgt1 (sum_fmap_r f)),
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
      (VALID: URA.wf (r_shared ⋅ r_own ⋅ r_ctx0))
      (LSIM: forall ths1 im_src1 im_tgt1 st_src1 st_tgt1 r_shared1 r_ctx1
                    (INV: I (ths1, im_src1, im_tgt1, st_src1, st_tgt1) r_shared1)
                    (VALID: URA.wf (r_shared1 ⋅ r_own ⋅ r_ctx1))
                    im_tgt2
                    (TGT: fair_update im_tgt1 im_tgt2 (sum_fmap_l (tids_fmap tid ths1))),
          _lsim _ _ RR f_src true r_ctx1 (trigger (Yield) >>= ktr_src) (ktr_tgt tt) (ths1, im_src1, im_tgt2, st_src1, st_tgt1))
    :
    __lsim tid lsim _lsim RR f_src f_tgt r_ctx0 (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt) (ths0, im_src0, im_tgt0, st_src0, st_tgt0)
  | lsim_sync
      f_src f_tgt r_ctx0
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
             R_src R_tgt (RR: R_src -> R_tgt -> URA.car -> shared_rel):
    bool -> bool -> URA.car -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel :=
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

  From Paco Require Import pacotac_internal.

  Lemma lsim_acc_gen
        tid r
        (A: Type)
        (f0: forall (a: A), Type)
        (f1: forall (a: A), Type)
        (f2: forall (a: A), f0 a -> f1 a -> URA.car -> shared_rel)
        (f3: forall (a: A), bool)
        (f4: forall (a: A), bool)
        (f5: forall (a: A), URA.car)
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
        R0 R1 (RR: R0 -> R1 -> URA.car -> shared_rel)
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
          (r: forall R_src R_tgt (RR: R_src -> R_tgt -> URA.car -> shared_rel), bool -> bool -> URA.car -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel)
          R_src R_tgt (RR1: R_src -> R_tgt -> URA.car -> shared_rel)
    :
    bool -> bool -> URA.car -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel :=
    | lsim_monoC_intro
        (RR0: R_src -> R_tgt -> URA.car -> shared_rel)
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

    { eapply pind9_fold. eapply lsim_observe. i. eapply rclo9_clo_base. econs; eauto. }

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
          (r: forall R_src R_tgt (RR: R_src -> R_tgt -> URA.car -> shared_rel), bool -> bool -> URA.car -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel)
          R_src R_tgt
          (RR: R_src -> R_tgt -> URA.car -> shared_rel)
    :
    bool -> bool -> URA.car -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel :=
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

    { gfinal. left. eapply pind9_fold. eapply lsim_observe. i.
      eapply rclo9_clo. left. econs; eauto.
      eapply rclo9_clo_base. right. guclo lsim_monoC_spec. econs.
      2:{ gbase. eauto. }
      { eauto. }
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

    { gfinal. left. eapply pind9_fold. eapply lsim_sync; eauto.
      { instantiate (1:=r_own ⋅ r_frame). r_wf VALID. }
      i. hexploit LSIM0; eauto.
      { instantiate (1:=r_frame ⋅ r_ctx1). r_wf VALID0. }
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
          (r: forall R_src R_tgt (RR: R_src -> R_tgt -> URA.car -> shared_rel), bool -> bool -> URA.car -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel)
          R_src1 R_tgt1
          (RR: R_src1 -> R_tgt1 -> URA.car -> shared_rel)
    :
    bool -> bool -> URA.car -> itree srcE R_src1 -> itree tgtE R_tgt1 -> shared_rel :=
    | lsim_bindC'_intro
        R_src0 R_tgt0 (RR0: R_src0 -> R_tgt0 -> URA.car -> shared_rel)
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

    { gfinal. left. eapply pind9_fold. eapply lsim_observe. i.
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
          (r: forall R_src R_tgt (RR: R_src -> R_tgt -> URA.car -> shared_rel), bool -> bool -> URA.car -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel)
          R_src1 R_tgt1
          (RR: R_src1 -> R_tgt1 -> URA.car -> shared_rel)
    :
    bool -> bool -> URA.car -> itree srcE R_src1 -> itree tgtE R_tgt1 -> shared_rel :=
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
        R0 R1 (RR: R0 -> R1 -> URA.car -> shared_rel)
        r_ctx src tgt shr
        (LSIM: lsim tid RR true true r_ctx src tgt shr)
    :
    forall ps pt, lsim tid RR ps pt r_ctx src tgt shr.
  Proof.
    i. revert_until tid. pcofix CIH. i.
    remember true as ps0 in LSIM at 1. remember true as pt0 in LSIM at 1.
    move LSIM before CIH. revert_until LSIM. punfold LSIM.
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
      hexploit IH. eauto. all: eauto. i. punfold H.
    }

    { des. pfold. eapply pind9_fold. eapply lsim_chooseL. esplits; eauto. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H.
    }

    { pfold. eapply pind9_fold. eapply lsim_putL. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H.
    }

    { pfold. eapply pind9_fold. eapply lsim_getL. split; ss.
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

    { pfold. eapply pind9_fold. eapply lsim_putR. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H.
    }

    { pfold. eapply pind9_fold. eapply lsim_getR. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H.
    }

    { pfold. eapply pind9_fold. eapply lsim_tidR. split; ss.
      destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H.
    }

    { pfold. eapply pind9_fold. eapply lsim_fairR. i. split; ss. specialize (LSIM0 _ FAIR).
      des. destruct LSIM0 as [LSIM0 IND]. hexploit IH; eauto. i. punfold H.
    }

    { pfold. eapply pind9_fold. eapply lsim_observe. i. eapply upaco9_mon_bot; eauto. }

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

  Variant lsim_bindRC'
          (r: forall R_src R_tgt (RR: R_src -> R_tgt -> URA.car -> shared_rel), bool -> bool -> URA.car -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel)
          R_src1 R_tgt1
          (RR: R_src1 -> R_tgt1 -> URA.car -> shared_rel)
    :
    bool -> bool -> URA.car -> itree srcE R_src1 -> itree tgtE R_tgt1 -> shared_rel :=
    | lsim_bindRC'_intro
        R_tgt0 (RR0: R_tgt0 -> URA.car -> shared_rel)
        itr_tgt ktr_src ktr_tgt shr r_ctx ps pt
        (REL: r _ _ (fun _ => RR0) ps pt r_ctx (trigger Yield) itr_tgt shr)
        (MON: forall r_tgt r_ctx shr
                     (SAT: RR0 r_tgt r_ctx shr),
            r _ _ RR false false r_ctx (trigger Yield >>= ktr_src) (ktr_tgt r_tgt) shr)
      :
      lsim_bindRC' r RR ps pt r_ctx (trigger Yield >>= ktr_src) (itr_tgt >>= ktr_tgt) shr
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

  Lemma lsim_bindRC'_spec tid
    :
    lsim_bindRC' <10= gupaco9 (fun r => pind9 (__lsim tid r) top9) (cpn9 (fun r => pind9 (__lsim tid r) top9)).
  Proof.
    assert (HINT: forall r1, monotone9 (fun r0 => pind9 (__lsim tid r0) r1)).
    { ii. eapply pind9_mon_gen; eauto. i. eapply __lsim_mon; eauto. }
    eapply grespect9_uclo; eauto with paco.
    econs.
    { ii. inv IN. econs; eauto. }
    i. inv PR. eapply GF in REL.
    eapply rclo9_clo_base. eapply cpn9_gupaco.
    { eauto with paco. }
    revert x0 x1 x2 ktr_src ktr_tgt MON.
    revert x3 x4 x5 x8 R_tgt0 RR0 itr_tgt REL.
    pinduction 7. i.

    eapply pind9_unfold in PR.
    2:{ eapply _lsim_mon. }
    rename PR into LSIM. inv LSIM; ired.

    { eapply f_equal with (f := observe) in H3. ss. }
    { eapply f_equal with (f := observe) in H3. ss. }
    { eapply f_equal with (f := observe) in H3. ss. }
    { eapply f_equal with (f := observe) in H3. ss. }
    { eapply f_equal with (f := observe) in H3. ss. }
    { eapply f_equal with (f := observe) in H3. ss. }
    { destruct LSIM0 as [LSIM0 IND].
      guclo lsim_indC_spec. eapply lsim_tauR.
      hexploit IH; eauto.
    }
    { guclo lsim_indC_spec. eapply lsim_chooseR.
      intros x. specialize (LSIM0 x). destruct LSIM0 as [LSIM0 IND].
      hexploit IH; eauto.
    }
    { destruct LSIM0 as [LSIM0 IND].
      guclo lsim_indC_spec. eapply lsim_putR.
      hexploit IH; eauto.
    }
    { destruct LSIM0 as [LSIM0 IND].
      guclo lsim_indC_spec. eapply lsim_getR.
      hexploit IH; eauto.
    }
    { destruct LSIM0 as [LSIM0 IND].
      guclo lsim_indC_spec. eapply lsim_tidR.
      hexploit IH; eauto.
    }
    { guclo lsim_indC_spec. eapply lsim_fairR.
      i. hexploit LSIM0; eauto. i. des. destruct H as [LSIM IND].
      splits. hexploit IH; eauto.
    }
    { eapply f_equal with (f := observe) in H3. ss. }
    { ss. destruct LSIM0 as [LSIM0 IND].
      eapply trigger_yield_rev in H3. subst.
      ired.
      admit.
    }
    { eapply trigger_yield_rev in H3.
      subst. revert LSIM0. ired. intros LSIM0.

      guclo lsim_indC_spec.
      eapply lsim_yieldR; eauto.
      i. hexploit LSIM0; eauto. i.
      destruct H as [LSIM IND].

      gbase.
  Admitted.

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
            (<<LSIM: forall fs ft,
                lsim
                  tid
                  (@local_RR R0 R1 RR tid)
                  fs ft
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

          funs: forall fn args, match md_src.(Mod.funs) fn, md_tgt.(Mod.funs) fn with
                           | Some ktr_src, Some ktr_tgt => local_sim I (@eq Any.t) (ktr_src args) (ktr_tgt args)
                           | None, None => True
                           | _, _ => False
                           end;
        }.
  End MODSIM.
End ModSim.
