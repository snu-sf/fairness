From sflib Require Import sflib.
From Paco Require Import paco.
Require Export Coq.Strings.String.
Require Import Coq.Classes.RelationClasses.
From iris.algebra Require Import cmra updates.

From Fairness Require Export
  ITreeLib
  FairBeh
  Mod
  pind
  PCM
  ModSim.

From Coq Require Import Relations.Relation_Operators.
From Coq Require Import Relations.Operators_Properties.
From Fairness Require Import WFLibLarge Axioms.

Set Implicit Arguments.

Section SHARED_REL_WF.

  Context `{world : ucmra}.

  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable ident_src: ID.
  Variable _ident_tgt: ID.

  Variable wf_src: WF.
  Variable wf_tgt: WF.

  Let shared_rel := shared state_src state_tgt ident_src _ident_tgt wf_src wf_tgt -> world -> Prop.

  Definition shared_rel_wf (I : shared_rel) : Prop :=
    forall ths im_src0 im_tgt0 st_src st_tgt r_shared
      (INV: I (ths, im_src0, im_tgt0, st_src, st_tgt) r_shared),
    forall im_tgt1
      (TGT: fair_update im_tgt0 im_tgt1 (prism_fmap inlp (tids_fmap_all ths))),
      (<<INV: I (ths, im_src0, im_tgt1, st_src, st_tgt) r_shared>>).

  Definition wf_clos_trans : WF := {| wf := clos_trans_well_founded (wf wf_tgt) |}.

  Variable I : shared_rel.

  Definition lifted : shared_rel :=
    fun '(ths, im_src, im_tgt, st_src, st_tgt) r_shared =>
      exists im_tgt'0, << INV_LE : (forall i, le wf_clos_trans (im_tgt i) (im_tgt'0 i)) >>
                    /\ << INV : I (ths, im_src, im_tgt'0, st_src, st_tgt) r_shared >>.

  Definition lifted_drop_imap :
    forall ths im_src im_tgt st_src st_tgt r_shared
      (INV : lifted (ths, im_src, im_tgt, st_src, st_tgt) r_shared),
    forall im_tgt'
      (LE : forall i, le wf_tgt (im_tgt' i) (im_tgt i)),
      << INV : lifted (ths, im_src, im_tgt', st_src, st_tgt) r_shared >>.
  Proof.
    i. ss. des. exists im_tgt'0. split; ss.
    ii. specialize (INV_LE i). specialize (LE i). destruct LE.
    - rewrite H. ss.
    - right. destruct INV_LE.
      + rewrite <- H0. econs. ss.
      + eapply clos_trans_n1_trans.
        * econs. eauto.
        * eauto.
  Qed.

  Lemma shared_rel_wf_lifted : shared_rel_wf lifted.
  Proof.
    ii. eapply lifted_drop_imap; eauto.
    i. specialize (TGT i). unfold le, tids_fmap_all in *. unfold prism_fmap in *; ss. unfold is_inl in *; ss.
    destruct i as [i|i]; ss; des_ifs; eauto.
  Qed.

End SHARED_REL_WF.


Section TRANS_CLOS.

  Context `{M: ucmra}.

  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable _ident_src: ID.
  Variable _ident_tgt: ID.

  Variable wf_src: WF.
  Variable wf_tgt: WF.

  Hypothesis (inh : inhabited wf_tgt.(T)).

  Let wf_tgt' := wf_clos_trans wf_tgt.

  Let shared_rel: Type := shared state_src state_tgt _ident_src _ident_tgt wf_src wf_tgt -> M -> Prop.
  Let shared_rel': Type := shared state_src state_tgt _ident_src _ident_tgt wf_src wf_tgt' -> M -> Prop.
  Variable I: shared_rel.
  Let I' : shared_rel' := lifted I.

  Lemma fair_break {Id im_tgt im_tgt' im_tgt'' fm}
    (LE : (forall i, le wf_tgt' (im_tgt' i) (im_tgt i)))
    (FAIR : @fair_update Id wf_tgt' im_tgt' im_tgt'' fm)
    : exists im_tgt'0, <<FAIR : @fair_update Id wf_tgt im_tgt im_tgt'0 fm >> /\
                  << LE : forall i, le wf_tgt' (im_tgt'' i) (im_tgt'0 i) >>.
  Proof.
    pose (fun i x => lt wf_tgt x (im_tgt i) /\ le wf_tgt' (im_tgt'' i) x) as P.
    exists (fun i => match fm i with
             | Flag.fail => epsilon inh (P i)
             | Flag.emp => im_tgt i
             | Flag.success => im_tgt'' i
             end).
    assert (forall i, fm i = Flag.fail -> exists x, P i x).
    { i. specialize (LE i). specialize (FAIR i). rewrite H in FAIR.
      destruct LE as [EQ | LT].
      - rewrite EQ in FAIR. eapply clos_trans_step in FAIR; ss.
      - eapply clos_trans_step in LT. destruct LT as [x [LT LE]].
        exists x. subst P; ss. split; eauto. right. des.
        + rewrite LE in FAIR. eauto.
        + eapply clos_trans_n1_trans; eauto.
    }
    split.
    - ii. specialize (H i). des_ifs. hexploit H; ss.
      i. eapply epsilon_spec in H0. destruct H0; eauto.
    - ii. specialize (H i). specialize (LE i). specialize (FAIR i). des_ifs.
      + hexploit H; ss. i. eapply epsilon_spec in H0. destruct H0; eauto.
      + rewrite FAIR. eauto.
      + left. reflexivity.
  Qed.

  Variable R0 R1 : Type.
  Variable RR : R0 -> R1 -> Prop.

  Lemma local_sim_clos_trans src tgt (SIM : local_sim I RR src tgt)
    : local_sim I' RR src tgt.
  Proof.
    ii. ss. des. move SIM at bottom.
    set (im_tgt'1 := fun i =>
                       match i with
                       | inl i => if tid_dec i tid then im_tgt1 (inl i) else im_tgt'0 (inl i)
                       | inr i => im_tgt'0 (inr i)
                       end).
    assert (TID_TGT' : @fair_update _ wf_tgt im_tgt'0 im_tgt'1 (prism_fmap inlp (fun i => if tid_dec i tid then Flag.success else Flag.emp))).
    { ii. subst im_tgt'1. specialize (TID_TGT i). specialize (INV_LE i). unfold prism_fmap in *; ss. unfold is_inl in *; ss. destruct i as [i|i]; ss; des_ifs. }
    specialize (SIM ths0 im_src0 im_tgt'0 st_src0 st_tgt0 r_shared0 r_ctx0 INV0 tid ths1 THS VALID im_tgt'1 TID_TGT').
    des. exists r_shared1, r_own. splits; ss.
    { exists im_tgt'1. splits; ss.
      subst im_tgt'1. i. specialize (TID_TGT i). specialize (INV_LE i).
      unfold prism_fmap in *; ss. unfold is_inl in *; ss. destruct i as [i|i]; ss.
      - des_ifs.
        + reflexivity.
        + rewrite TID_TGT. ss.
      - rewrite TID_TGT. ss.
    }
    i. des. pose proof (fair_break INV1 TGT). des. move SIM1 at bottom.
    specialize (SIM1 ths im_src1 im_tgt'2 st_src2 st_tgt2 r_shared2 r_ctx2 INV2 VALID1 im_tgt'3 FAIR fs ft).
    rename SIM1 into LSIM. clear - inh LSIM LE. revert_until I'. ginit. gcofix CIH. i. gstep.
    remember (local_RR I RR tid) as RR'.
    remember (ths, im_src1, im_tgt'3, st_src2, st_tgt2) as sha.
    revert ths im_src1 im_tgt3 im_tgt'3 st_src2 st_tgt2 LE Heqsha RR HeqRR'.
    unfold lsim in LSIM. punfold LSIM.
    pattern R0, R1, RR', fs, ft, r_ctx2, src, tgt, sha.
    revert R0 R1 RR' fs ft r_ctx2 src tgt sha LSIM.
    eapply pind9_acc. intros rr DEC IH R0 R1 RR' fs ft r_ctx src tgt sha. i. clear DEC. subst.
    eapply pind9_unfold in PR; eauto with paco. eapply pind9_fold. inv PR.
    - econs. ss. des. exists ths3, r_own, r_shared. splits; ss. exists im_tgt'3. split; ss.
    - econs. split; ss. eapply IH; ss. destruct LSIM. ss.
    - econs. des. exists x. split; ss. eapply IH; ss. destruct LSIM. ss.
    - econs. split; ss. eapply IH; ss. destruct LSIM. ss.
    - econs. split; ss. eapply IH; ss. destruct LSIM. ss.
    - econs.
    - econs. des. exists im_src0. splits; ss. split; ss. eapply IH; ss. destruct LSIM0. ss.
    - econs. split; ss. eapply IH; ss. destruct LSIM. ss.
    - econs. i. specialize (LSIM x). split; ss. eapply IH; ss. destruct LSIM. ss.
    - econs. split; ss. eapply IH; ss. destruct LSIM. ss.
    - econs. split; ss. eapply IH; ss. destruct LSIM. ss.
    - econs. i. pose proof (fair_break LE FAIR). des.
      specialize (LSIM im_tgt'0 FAIR0). split; ss. eapply IH; ss. destruct LSIM. ss.
    - econs. i. specialize (LSIM ret). gfinal. left. eapply CIH; ss. pclearbot. eapply LSIM.
    - econs. i. specialize (LSIM ret). gfinal. left. eapply CIH; ss. pclearbot. eapply LSIM.
    - eapply lsim_yieldL. split; ss. eapply IH; ss. destruct LSIM. ss.
    - eapply lsim_yieldR; eauto. { exists im_tgt'3. split; eauto. } i. ss. des.
      pose proof (fair_break INV_LE TGT). des. move LSIM at bottom.
      specialize (LSIM ths1 im_src0 im_tgt'0 st_src1 st_tgt1 r_shared1 r_ctx1 INV1 VALID0 im_tgt'1 FAIR).
      split; ss. eapply IH; ss. destruct LSIM. eapply H0.
    - eapply lsim_sync; eauto. { exists im_tgt'3. split; eauto. } i. ss. des.
      pose proof (fair_break INV_LE TGT). des. move LSIM at bottom.
      specialize (LSIM ths1 im_src0 im_tgt'0 st_src1 st_tgt1 r_shared1 r_ctx1 INV1 VALID0 im_tgt'1 FAIR).
      pclearbot. gfinal. left. eapply CIH; ss.
    - econs. gfinal. left. pclearbot. eapply CIH; ss.
  Qed.

End TRANS_CLOS.

Section WFT_MONO.

  Context `{M: ucmra}.

  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable _ident_src: ID.
  Variable _ident_tgt: ID.

  Variable wf_src  : WF.
  Variable wft_T : Type.
  Variable wft_lt : wft_T -> wft_T -> Prop.
  Variable wft_lt' : wft_T -> wft_T -> Prop.
  Hypothesis wft_wf : well_founded wft_lt.
  Hypothesis wft_wf' : well_founded wft_lt'.
  Hypothesis wft_LE : forall x y, wft_lt' x y -> wft_lt x y.
  Let wf_tgt  := {| wf := wft_wf |}.
  Let wf_tgt' := {| wf := wft_wf' |}.

  Let shared_rel: Type := shared state_src state_tgt _ident_src _ident_tgt wf_src wf_tgt -> M -> Prop.
  Let shared_rel': Type := shared state_src state_tgt _ident_src _ident_tgt wf_src wf_tgt' -> M -> Prop.
  Variable I: shared_rel.
  Let I' : shared_rel' := I.

  Variable R0 R1 : Type.
  Variable RR : R0 -> R1 -> Prop.

  Lemma fair_mono Id m_tgt1 m_tgt2 fm
    (FAIR : @fair_update Id wf_tgt' m_tgt1 m_tgt2 fm)
    : @fair_update Id wf_tgt m_tgt1 m_tgt2 fm.
  Proof. ii. specialize (FAIR i). des_ifs. eapply wft_LE. ss. Qed.

  Lemma local_sim_wft_mono src tgt (SIM : local_sim I RR src tgt)
    : local_sim I' RR src tgt.
  Proof.
    ii. ss. move SIM at bottom.
    assert (TID_TGT' : @fair_update _ wf_tgt im_tgt0 im_tgt1 (prism_fmap inlp (fun i : thread_id => if tid_dec i tid then Flag.success else Flag.emp))).
    { ii. specialize (TID_TGT i). unfold prism_fmap in *; ss. unfold is_inl in *; ss. destruct i as [i|i]; ss. des_ifs. }
    specialize (SIM ths0 im_src0 im_tgt0 st_src0 st_tgt0 r_shared0 r_ctx0 INV tid ths1 THS VALID im_tgt1 TID_TGT').
    des. exists r_shared1, r_own. splits; ss. i. move SIM1 at bottom.
    specialize (SIM1 ths im_src1 im_tgt2 st_src2 st_tgt2 r_shared2 r_ctx2 INV1 VALID1 im_tgt3 (fair_mono TGT) fs ft).
    rename SIM1 into LSIM. clear - LSIM wft_LE. revert_until I'. ginit. gcofix CIH. i. gstep.
    remember (local_RR I RR tid) as RR'.
    match goal with [ LSIM : lsim _ _ _ _ _ _ _ _ ?SHA |- _ ] => remember SHA as sha end.
    revert ths im_src1 im_tgt3 st_src2 st_tgt2 Heqsha RR HeqRR'.
    unfold lsim in LSIM. punfold LSIM.
    pattern R0, R1, RR', fs, ft, r_ctx2, src, tgt, sha.
    revert R0 R1 RR' fs ft r_ctx2 src tgt sha LSIM.
    eapply pind9_acc. intros rr DEC IH R0 R1 RR' fs ft r_ctx src tgt sha. i. clear DEC. subst.
    eapply pind9_unfold in PR; eauto with paco. eapply pind9_fold. inv PR.
    - econs. ss.
    - econs. split; ss. eapply IH; ss. destruct LSIM. ss.
    - econs. des. exists x. split; ss. eapply IH; ss. destruct LSIM. ss.
    - econs. split; ss. eapply IH; ss. destruct LSIM. ss.
    - econs. split; ss. eapply IH; ss. destruct LSIM. ss.
    - econs.
    - econs. des. exists im_src0. splits; ss. split; ss. eapply IH; ss. destruct LSIM0. ss.
    - econs. split; ss. eapply IH; ss. destruct LSIM. ss.
    - econs. i. specialize (LSIM x). split; ss. eapply IH; ss. destruct LSIM. ss.
    - econs. split; ss. eapply IH; ss. destruct LSIM. ss.
    - econs. split; ss. eapply IH; ss. destruct LSIM. ss.
    - econs. i. specialize (LSIM im_tgt1 (fair_mono FAIR)). split; ss. eapply IH; ss. destruct LSIM. ss.
    - econs. i. specialize (LSIM ret). gfinal. left. eapply CIH; ss. pclearbot. eapply LSIM.
    - econs. i. specialize (LSIM ret). gfinal. left. eapply CIH; ss. pclearbot. eapply LSIM.
    - eapply lsim_yieldL. split; ss. eapply IH; ss. destruct LSIM. ss.
    - eapply lsim_yieldR; eauto. i. move LSIM at bottom.
      specialize (LSIM ths1 im_src0 im_tgt1 st_src1 st_tgt1 r_shared1 r_ctx1 INV0 VALID0 im_tgt2 (fair_mono TGT)).
      split; ss. eapply IH; ss. destruct LSIM. ss.
    - eapply lsim_sync; eauto. i. move LSIM at bottom.
      specialize (LSIM ths1 im_src0 im_tgt1 st_src1 st_tgt1 r_shared1 r_ctx1 INV0 VALID0 im_tgt2 (fair_mono TGT)).
      pclearbot. gfinal. left. eapply CIH; ss.
    - econs. gfinal. left. pclearbot. eapply CIH; ss.
  Qed.

End WFT_MONO.
