From sflib Require Import sflib.
From Paco Require Import paco.
Require Export Coq.Strings.String.
Require Import Coq.Classes.RelationClasses.

From Fairness Require Export
  ITreeLib
  FairBeh
  Mod
  pind
  PCM
  ModSim.

From Coq Require Import Relations.Relation_Operators.
From Coq Require Import Relations.Operators_Properties.
From Fairness Require Import WFLib Axioms.

Set Implicit Arguments.

Section TRANS_CLOS.

  Context `{M: URA.t}.

  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable _ident_src: ID.
  Variable _ident_tgt: ID.

  Variable wf_src: WF.
  Variable wf_tgt: WF.

  Hypothesis (inh : inhabited wf_tgt.(T)).

  Let wf_tgt' := {| wf := clos_trans_well_founded wf_tgt.(wf) |}.

  Let shared_rel: Type := shared state_src state_tgt _ident_src _ident_tgt wf_src wf_tgt -> Prop.
  Let shared_rel': Type := shared state_src state_tgt _ident_src _ident_tgt wf_src wf_tgt' -> Prop.
  Variable I: shared_rel.
  Let I' : shared_rel' :=
        fun '(ths, im_src, im_tgt, st_src, st_tgt, w) =>
          exists im_tgt'0, << INV_LE : (forall i, le wf_tgt' (im_tgt i) (im_tgt'0 i)) >>
                    /\ << INV : I (ths, im_src, im_tgt'0, st_src, st_tgt, w) >>.

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
      - rewrite EQ in *. eapply clos_trans_step in FAIR; ss.
      - eapply clos_trans_step in LT. destruct LT as [x [LT LE]].
        exists x. subst P; ss. split; eauto. right. des.
        + rewrite LE in *. eauto.
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
    specialize (SIM ths0 im_src0 im_tgt'0 st_src0 st_tgt0 r_shared0 r_ctx0 INV0 tid ths1 THS VALID).
    des. exists r_shared1, r_own. splits; ss. { exists im_tgt'0. ss. }
    i. des. pose proof (fair_break INV1 TGT). des. move SIM1 at bottom.
    specialize (SIM1 ths im_src1 im_tgt'1 st_src st_tgt r_shared2 r_ctx2 INV2 VALID1 im_tgt'2 FAIR fs ft).
    rename SIM1 into LSIM. clear - inh LSIM LE. revert_until I'. ginit. gcofix CIH. i. gstep.
    remember (local_RR I RR tid) as RR'.
    remember (ths, im_src1, im_tgt'2, st_src, st_tgt, r_shared2) as sha.
    revert ths im_src1 im_tgt2 im_tgt'2 st_src st_tgt r_shared2 LE Heqsha RR HeqRR'.
    unfold lsim in LSIM. punfold LSIM.
    pattern R0, R1, RR', fs, ft, r_ctx2, src, tgt, sha.
    revert R0 R1 RR' fs ft r_ctx2 src tgt sha LSIM.
    eapply pind9_acc. intros rr DEC IH R0 R1 RR' fs ft r_ctx src tgt sha. i. clear DEC. subst.
    eapply pind9_unfold in PR; eauto with paco. eapply pind9_fold. inv PR.
    - econs. ss. des. exists ths3, r_own, r_shared0. splits; ss. exists im_tgt'2. split; ss.
    - econs. split; ss. eapply IH; ss. destruct LSIM. ss.
    - econs. des. exists x. split; ss. eapply IH; ss. destruct LSIM. ss.
    - econs. split; ss. eapply IH; ss. destruct LSIM. ss.
    - econs. split; ss. eapply IH; ss. destruct LSIM. ss.
    - econs. split; ss. eapply IH; ss. destruct LSIM. ss.
    - econs.
    - econs. des. exists im_src0. splits; ss. split; ss. eapply IH; ss. destruct LSIM0. ss.
    - econs. split; ss. eapply IH; ss. destruct LSIM. ss.
    - econs. i. specialize (LSIM x). split; ss. eapply IH; ss. destruct LSIM. ss.
    - econs. split; ss. eapply IH; ss. destruct LSIM. ss.
    - econs. split; ss. eapply IH; ss. destruct LSIM. ss.
    - econs. split; ss. eapply IH; ss. destruct LSIM. ss.
    - econs. i. pose proof (fair_break LE FAIR). des.
      specialize (LSIM im_tgt'0 FAIR0). split; ss. eapply IH; ss. destruct LSIM. ss.
    - econs. i. specialize (LSIM ret). gfinal. left. eapply CIH; ss. pclearbot. eapply LSIM.
    - eapply lsim_yieldL. split; ss. eapply IH; ss. destruct LSIM. ss.
    - eapply lsim_yieldR; eauto. { exists im_tgt'2. split; eauto. } i. ss. des.
      pose proof (fair_break INV_LE TGT). des. move LSIM at bottom.
      specialize (LSIM ths1 im_src0 im_tgt'0 st_src1 st_tgt1 r_shared1 r_ctx1 INV1 VALID0 im_tgt'1 FAIR).
      split; ss. eapply IH; ss. destruct LSIM. eapply H0.
    - eapply lsim_sync; eauto. { exists im_tgt'2. split; eauto. } i. ss. des.
      pose proof (fair_break INV_LE TGT). des. move LSIM at bottom.
      specialize (LSIM ths1 im_src0 im_tgt'0 st_src1 st_tgt1 r_shared1 r_ctx1 INV1 VALID0 im_tgt'1 FAIR).
      pclearbot. gfinal. left. eapply CIH; ss.
    - econs. gfinal. left. pclearbot. eapply CIH; ss.
  Qed.

End TRANS_CLOS.

Section WFT_MONO.

  Context `{M: URA.t}.

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

  Let shared_rel: Type := shared state_src state_tgt _ident_src _ident_tgt wf_src wf_tgt -> Prop.
  Let shared_rel': Type := shared state_src state_tgt _ident_src _ident_tgt wf_src wf_tgt' -> Prop.
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
    specialize (SIM ths0 im_src0 im_tgt0 st_src0 st_tgt0 r_shared0 r_ctx0 INV tid ths1 THS VALID).
    des. exists r_shared1, r_own. splits; ss. i. move SIM1 at bottom.
    specialize (SIM1 ths im_src1 im_tgt1 st_src st_tgt r_shared2 r_ctx2 INV1 VALID1 im_tgt2 (fair_mono TGT) fs ft).
    rename SIM1 into LSIM. clear - LSIM wft_LE. revert_until I'. ginit. gcofix CIH. i. gstep.
    remember (local_RR I RR tid) as RR'.
    match goal with [ LSIM : lsim _ _ _ _ _ _ _ _ ?SHA |- _ ] => remember SHA as sha end.
    revert ths im_src1 im_tgt2 st_src st_tgt r_shared2 Heqsha RR HeqRR'.
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
    - econs. split; ss. eapply IH; ss. destruct LSIM. ss.
    - econs.
    - econs. des. exists im_src0. splits; ss. split; ss. eapply IH; ss. destruct LSIM0. ss.
    - econs. split; ss. eapply IH; ss. destruct LSIM. ss.
    - econs. i. specialize (LSIM x). split; ss. eapply IH; ss. destruct LSIM. ss.
    - econs. split; ss. eapply IH; ss. destruct LSIM. ss.
    - econs. split; ss. eapply IH; ss. destruct LSIM. ss.
    - econs. split; ss. eapply IH; ss. destruct LSIM. ss.
    - econs. i. specialize (LSIM im_tgt1 (fair_mono FAIR)). split; ss. eapply IH; ss. destruct LSIM. ss.
    - econs. i. specialize (LSIM ret). gfinal. left. eapply CIH; ss. pclearbot. eapply LSIM.
    - eapply lsim_yieldL. split; ss. eapply IH; ss. destruct LSIM. ss.
    - eapply lsim_yieldR; eauto. i. move LSIM at bottom.
      specialize (LSIM ths1 im_src0 im_tgt1 st_src1 st_tgt1 r_shared1 r_ctx1 INV0 VALID0 im_tgt0 (fair_mono TGT)).
      split; ss. eapply IH; ss. destruct LSIM. ss.
    - eapply lsim_sync; eauto. i. move LSIM at bottom.
      specialize (LSIM ths1 im_src0 im_tgt1 st_src1 st_tgt1 r_shared1 r_ctx1 INV0 VALID0 im_tgt0 (fair_mono TGT)).
      pclearbot. gfinal. left. eapply CIH; ss.
    - econs. gfinal. left. pclearbot. eapply CIH; ss.
  Qed.

End WFT_MONO.

Module ModSimN.
  Section MODSIMNAT.

    Variable md_src: Mod.t.
    Variable md_tgt: Mod.t.

    Record mod_sim: Prop :=
      mk {
          wf_src : WF;

          world: URA.t;

          I: (@shared world md_src.(Mod.state) md_tgt.(Mod.state) md_src.(Mod.ident) md_tgt.(Mod.ident) wf_src nat_wf) -> Prop;
          init: forall im_tgt, exists im_src r_shared,
            I (NatSet.empty, im_src, im_tgt, md_src.(Mod.st_init), md_tgt.(Mod.st_init), r_shared)
            /\ (URA.wf r_shared);

          funs: forall fn args, match md_src.(Mod.funs) fn, md_tgt.(Mod.funs) fn with
                                | None, _ => True
                                | _, None => False
                                | Some ktr_src, Some ktr_tgt => local_sim I (@eq Val) (ktr_src args) (ktr_tgt args)
                                end;
        }.
  End MODSIMNAT.
End ModSimN.

From Fairness Require Import Axioms.
Section NAT.

  Definition succ_wf := {| wf := succ_rel_well_founded |}.
  Definition succ_wf' := {| wf := clos_trans_well_founded succ_rel_well_founded |}.

  Variable wf_tgt : WF.
  Hypothesis wf_tgt_inhabited: inhabited wf_tgt.(T).
  Hypothesis wf_tgt_open: forall (o0: wf_tgt.(T)), exists o1, wf_tgt.(lt) o0 o1.

  Let zero: wf_tgt.(T) := epsilon wf_tgt_inhabited (fun _ => True).
  Let succ: wf_tgt.(T) -> wf_tgt.(T) :=
        fun o0 => epsilon wf_tgt_inhabited (fun o1 => wf_tgt.(lt) o0 o1).

  Lemma wf_tgt_succ_lt o: lt wf_tgt o (succ o).
  Proof. unfold succ. eapply epsilon_spec; ss. Qed.

  Fixpoint wfemb (n: nat): wf_tgt.(T) :=
    match n with
    | 0 => zero
    | S n => succ (wfemb n)
    end.

  Lemma wfemb_mono Id im_tgt0 im_tgt1 fm
    (FAIR : @fair_update Id succ_wf im_tgt0 im_tgt1 fm)
    : @fair_update Id wf_tgt (wfemb ∘ im_tgt0) (wfemb ∘ im_tgt1) fm.
  Proof.
    ii. unfold compose. specialize (FAIR i). des_ifs.
    - inv FAIR. eapply wf_tgt_succ_lt.
    - eauto.
  Qed.

  Context `{M: URA.t}.

  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable _ident_src: ID.
  Variable _ident_tgt: ID.

  Variable wf_src: WF.

  Let shared_rel: Type := @shared M state_src state_tgt _ident_src _ident_tgt wf_src wf_tgt  -> Prop.
  Let shared_rel_nat: Type := @shared M state_src state_tgt _ident_src _ident_tgt wf_src succ_wf -> Prop.
  Variable I: shared_rel.

  Definition to_shared_rel_nat : shared_rel_nat := 
    fun '(ths, m_src, m_tgt, st_src, st_tgt, w) =>
      I (ths, m_src, wfemb ∘ m_tgt, st_src, st_tgt, w).

  Variable R0 R1 : Type.
  Variable RR : R0 -> R1 -> Prop.

  Lemma local_sim_wft_nat src tgt (SIM : local_sim I RR src tgt)
    : local_sim to_shared_rel_nat RR src tgt.
  Proof.
    ii. move SIM at bottom.
    specialize (SIM ths0 im_src0 (wfemb ∘ im_tgt0) st_src0 st_tgt0 r_shared0 r_ctx0 INV tid ths1 THS VALID).
    des. exists r_shared1, r_own. splits; ss. i. move SIM1 at bottom.
    specialize (SIM1 ths im_src1 (wfemb ∘ im_tgt1) st_src st_tgt r_shared2 r_ctx2 INV1 VALID1 (wfemb ∘ im_tgt2)
                  ltac:(eapply wfemb_mono; ss) fs ft).
    rename SIM1 into LSIM. clear - LSIM wf_tgt_inhabited wf_tgt_open. revert_until I. ginit. gcofix CIH. i. gstep.
    remember (local_RR I RR tid) as RR' in LSIM.
    match goal with [ LSIM : lsim _ _ _ _ _ _ _ _ ?SHA |- _ ] => remember SHA as sha end.
    revert ths im_src1 im_tgt2 st_src st_tgt r_shared2 RR Heqsha HeqRR'.
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
    - econs. split; ss. eapply IH; ss. destruct LSIM. ss.
    - econs.
    - econs. des. exists im_src0. splits; ss. split; ss. eapply IH; ss. destruct LSIM0. ss.
    - econs. split; ss. eapply IH; ss. destruct LSIM. ss.
    - econs. i. specialize (LSIM x). split; ss. eapply IH; ss. destruct LSIM. ss.
    - econs. split; ss. eapply IH; ss. destruct LSIM. ss.
    - econs. split; ss. eapply IH; ss. destruct LSIM. ss.
    - econs. split; ss. eapply IH; ss. destruct LSIM. ss.
    - econs. i. specialize (LSIM (wfemb ∘ im_tgt1) (wfemb_mono FAIR)). split; ss. eapply IH; ss. destruct LSIM. ss.
    - econs. i. specialize (LSIM ret). gfinal. left. eapply CIH; ss. pclearbot. eapply LSIM.
    - eapply lsim_yieldL. split; ss. eapply IH; ss. destruct LSIM. ss.
    - eapply lsim_yieldR; eauto. i. move LSIM at bottom.
      specialize (LSIM ths1 im_src0 (wfemb ∘ im_tgt1) st_src1 st_tgt1 r_shared1 r_ctx1 INV0 VALID0 (wfemb ∘ im_tgt0) (wfemb_mono TGT)).
      split; ss. eapply IH; ss. destruct LSIM. ss.
    - eapply lsim_sync; eauto. i. move LSIM at bottom.
      specialize (LSIM ths1 im_src0 (wfemb ∘ im_tgt1) st_src1 st_tgt1 r_shared1 r_ctx1 INV0 VALID0 (wfemb ∘ im_tgt0) (wfemb_mono TGT)).
      pclearbot. gfinal. left. eapply CIH; ss.
    - econs. gfinal. left. pclearbot. eapply CIH; ss.
  Qed.

End NAT.

Section MODSIMNAT.
  Import Mod.

  Variable M_src M_tgt: Mod.t.

  Lemma modsim_nat_modsim_exist
    (SIM: ModSim.mod_sim M_src M_tgt)
    : ModSimN.mod_sim M_src M_tgt.
  Proof.
    destruct SIM.
    pose (wfemb wf_tgt wf_tgt_inhabited) as wf_emb.
    pose (I' := to_shared_rel_nat wf_tgt_inhabited I).
    pose (fun '(ths, im_src0, im_tgt0, st_src, st_tgt, w) =>
            exists im_tgt'0,
              << LE : forall i, le succ_wf' (im_tgt0 i) (im_tgt'0 i) >>
            /\ << INV : I' (ths, im_src0, im_tgt'0, st_src, st_tgt, w) >>
         ) as I''.
    constructor 1 with wf_src world I''.
    { i. specialize (init (wf_emb ∘ im_tgt)). des. esplits; eauto. ss. esplits; [reflexivity|eauto]. }
    i. specialize (funs0 fn args). des_ifs. rename funs0 into SIM.
    eapply local_sim_wft_mono with (wft_lt' := Peano.lt) (wft_lt := clos_trans_n1 _ succ_rel).
    { eapply succ_clos_trans. }
    eapply local_sim_clos_trans with (wf_tgt := succ_wf) (I := I').
    { econs. exact 0. }
    remember (k args) as src.
    remember (k0 args) as tgt.
    clear - SIM wf_tgt_inhabited wf_tgt_open wf_emb.
    eapply local_sim_wft_nat; ss.
  Qed.

End MODSIMNAT.
