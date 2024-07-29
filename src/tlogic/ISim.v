From sflib Require Import sflib.
From Paco Require Import paco.
From iris.algebra Require Import cmra.
From Fairness.base_logic Require Import upred base_logic.
From Fairness Require Import ITreeLib IPM ModSim ModSimNat PCM.
Require Import Program.

Set Implicit Arguments.

Section SIM.
  Context `{Σ: GRA.t}.
  Notation iProp := (iProp Σ).

  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable ident_src: ID.
  Variable ident_tgt: ID.

  Variable wf_src: WF.

  Let srcE := threadE ident_src state_src.
  Let tgtE := threadE ident_tgt state_tgt.

  Let shared_rel := TIdSet.t -> (@imap ident_src wf_src) -> (@imap (sum_tid ident_tgt) nat_wf) -> state_src -> state_tgt -> iProp.

  Definition liftI (R: shared_rel) : (TIdSet.t *
                               (@imap ident_src wf_src) *
                               (@imap (sum_tid ident_tgt) nat_wf) *
                               state_src *
                               state_tgt) -> Σ -> Prop :=
        fun '(ths, im_src, im_tgt, st_src, st_tgt) r_shared =>
          upred.uPred_holds (to_upred (R ths im_src im_tgt st_src st_tgt)) r_shared.

  Let liftRR R_src R_tgt (RR: R_src -> R_tgt -> shared_rel):
    R_src -> R_tgt -> Σ -> (TIdSet.t *
                              (@imap ident_src wf_src) *
                              (@imap (sum_tid ident_tgt) nat_wf) *
                              state_src *
                              state_tgt) -> Prop :=
        fun r_src r_tgt r_ctx '(ths, im_src, im_tgt, st_src, st_tgt) =>
          exists r,
            (<<WF: ✓ (r ⋅ r_ctx)>>) /\
              upred.uPred_holds (to_upred (RR r_src r_tgt ths im_src im_tgt st_src st_tgt)) r.

  Variable tid: thread_id.
  Variable I: shared_rel.

  Let rel := (forall R_src R_tgt (Q: R_src -> R_tgt -> shared_rel), bool -> bool -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel).

  Let gf := (fun r => pind9 ((@__lsim ( Σ)) _ _ _ _ _ _ (liftI I) tid r) top9).
  Let gf_mon: monotone9 gf.
  Proof.
    eapply lsim_mon.
  Qed.
  Hint Resolve gf_mon: paco.

  Variant unlift (r: rel):
    forall R_src R_tgt (RR: R_src -> R_tgt -> Σ ->
                            (TIdSet.t *
                               (@imap ident_src wf_src) *
                               (@imap (sum_tid ident_tgt) nat_wf) *
                               state_src *
                               state_tgt) -> Prop),
      bool -> bool -> Σ -> itree srcE R_src -> itree tgtE R_tgt ->
      (TIdSet.t *
         (@imap ident_src wf_src) *
         (@imap (sum_tid ident_tgt) nat_wf) *
         state_src *
         state_tgt) -> Prop :=
    | unlift_intro
        R_src R_tgt Q ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt r_ctx r_own
        (REL: upred.uPred_holds (to_upred (r R_src R_tgt Q ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt)) r_own)
        (WF: ✓ (r_own ⋅ r_ctx))
      :
      unlift r (liftRR Q) ps pt r_ctx itr_src itr_tgt (ths, im_src, im_tgt, st_src, st_tgt)
  .

  Program Definition isim: rel -> rel -> rel :=
    fun
      r g
      R_src R_tgt Q ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt =>
        from_upred ({| upred.uPred_holds r_own :=
           forall r_ctx (WF: ✓ (r_own ⋅ r_ctx)),
             gpaco9 gf (cpn9 gf) (@unlift r) (@unlift g) _ _ (liftRR Q) ps pt r_ctx itr_src itr_tgt (ths, im_src, im_tgt, st_src, st_tgt) |}).
  Next Obligation.
    ii. ss. eapply H.
    eapply cmra_valid_included; eauto. eapply RA.extends_add; eauto.
  Qed.

  Tactic Notation "muclo" uconstr(H) :=
    eapply gpaco9_uclo; [auto with paco|apply H|].

  Lemma isim_upd r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (#=> (isim r g Q ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt))
      (isim r g Q ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    split. uPred.unseal. rewrite /bi_entails /upred.uPred_bupd_def.
    intros ? WF FUPD r_ctx WFx. specialize (FUPD r_ctx).
    hexploit FUPD; [done|].
    i. des. by eapply H0.
  Qed.

  Global Instance isim_elim_upd
         r g R_src R_tgt
         (Q: R_src -> R_tgt -> shared_rel)
         ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt p
         P
    :
    ElimModal True p false (#=> P) P (isim r g Q ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt) (isim r g Q ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim.
    i. iIntros "[H0 H1]".
    iApply isim_upd. iMod "H0". iModIntro.
    iApply "H1". iFrame.
  Qed.

  Lemma isim_wand r g R_src R_tgt
        (Q0 Q1: R_src -> R_tgt -> shared_rel)
        ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      ((∀ r_src r_tgt ths im_src im_tgt st_src st_tgt,
           ((Q0 r_src r_tgt ths im_src im_tgt st_src st_tgt) -∗ #=> (Q1 r_src r_tgt ths im_src im_tgt st_src st_tgt))) ∗ (isim r g Q0 ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt))
      (isim r g Q1 ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    split. uPred.unseal.
    intros ? WF SEP r_ctx WFx. destruct SEP as (x1 & x2 & EQ & FORALL & ISIM).
    rewrite EQ in WFx,WF.

    ii. eapply gpaco9_uclo; [auto with paco|apply lsim_frameC_spec|].
    econs.
    instantiate (1:=x1).
    eapply gpaco9_uclo; [auto with paco|apply lsim_monoC_spec|].
    econs.
    2:{ eapply ISIM. r_wf WFx. }
    unfold liftRR. i. subst. des_ifs. des.
    specialize (FORALL r_src r_tgt t i0 i s0 s).
    simpl in *.
    hexploit (FORALL r0); eauto.
    { eapply cmra_valid_op_l. instantiate (1:=r_ctx'). r_wf WF0. }
    i. specialize (H r_ctx').
    hexploit H; eauto.
    { r_wf WF0. }
  Qed.

  Lemma isim_mono r g R_src R_tgt
        (Q0 Q1: R_src -> R_tgt -> shared_rel)
        (MONO: forall r_src r_tgt ths im_src im_tgt st_src st_tgt,
            bi_entails
              (Q0 r_src r_tgt ths im_src im_tgt st_src st_tgt)
              (#=> (Q1 r_src r_tgt ths im_src im_tgt st_src st_tgt)))
        ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (isim r g Q0 ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
      (isim r g Q1 ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    iIntros. iApply isim_wand. iFrame.
    iIntros. iApply MONO. eauto.
  Qed.

  Lemma isim_frame r g R_src R_tgt
        P (Q: R_src -> R_tgt -> shared_rel)
        ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (P ∗ isim r g Q ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
      (isim r g (fun r_src r_tgt ths im_src im_tgt st_src st_tgt =>
                   (P ∗ Q r_src r_tgt ths im_src im_tgt st_src st_tgt)%I)
            ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    iIntros "[H0 H1]". iApply isim_wand. iFrame.
    iIntros. iModIntro. iFrame.
  Qed.

  Lemma isim_bind r g R_src R_tgt S_src S_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        ps pt
        (itr_src: itree srcE S_src) (itr_tgt: itree tgtE S_tgt)
        ktr_src ktr_tgt
        ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (isim r g (fun s_src s_tgt ths im_src im_tgt st_src st_tgt =>
                   isim r g Q false false (ktr_src s_src) (ktr_tgt s_tgt) ths im_src im_tgt st_src st_tgt) ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
      (isim r g Q ps pt (itr_src >>= ktr_src) (itr_tgt >>= ktr_tgt) ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    split. intros x WF ISIM r_ctx WFx.
    eapply gpaco9_uclo; [auto with paco|apply lsim_bindC_spec|].
    econs.
    eapply gpaco9_uclo; [auto with paco|apply lsim_monoC_spec|].
    econs.
    2:{ eapply ISIM; eauto. }
    unfold liftRR. i. des_ifs. des.
    eapply gpaco9_uclo; [auto with paco|apply lsim_monoC_spec|].
    econs.
    2:{ eapply RET0; eauto. }
    unfold liftRR. i. des_ifs.
  Qed.

  Lemma isim_ret r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        ps pt
        r_src r_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (Q r_src r_tgt ths im_src im_tgt st_src st_tgt)
      (isim r g Q ps pt (Ret r_src) (Ret r_tgt) ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    split.
    intros x WF POST r_ctx WFx.
    muclo lsim_indC_spec.
    eapply lsim_ret. unfold liftRR. esplits; eauto.
  Qed.

  Lemma isim_tauL r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (isim r g Q true pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
      (isim r g Q ps pt (Tau itr_src) itr_tgt ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    split.
    intros x WF ISIM r_ctx WFx.
    muclo lsim_indC_spec.
    eapply lsim_tauL. muclo lsim_resetC_spec. econs; eauto.
  Qed.

  Lemma isim_tauR r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (isim r g Q ps true itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
      (isim r g Q ps pt itr_src (Tau itr_tgt) ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    split.
    intros x WF ISIM r_ctx WFx.
    muclo lsim_indC_spec.
    eapply lsim_tauR. muclo lsim_resetC_spec. econs; eauto.
  Qed.

  Lemma isim_chooseL X r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        ps pt ktr_src itr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (∃ x, isim r g Q true pt (ktr_src x) itr_tgt ths im_src im_tgt st_src st_tgt)
      (isim r g Q ps pt (trigger (Choose X) >>= ktr_src) itr_tgt ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    uPred.unseal. split.
    intros x WF ISIM r_ctx WFx.
    muclo lsim_indC_spec.
    eapply lsim_chooseL.
    rr in ISIM. des.
    esplits; eauto.
  Qed.

  Lemma isim_chooseR X r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        ps pt itr_src ktr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (∀ x, isim r g Q ps true itr_src (ktr_tgt x) ths im_src im_tgt st_src st_tgt)
      (isim r g Q ps pt itr_src (trigger (Choose X) >>= ktr_tgt) ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    uPred.unseal. split.
    intros x WF ISIM r_ctx WFx.
    muclo lsim_indC_spec.
    eapply lsim_chooseR.
    i. econs; [eapply ISIM|..]; eauto.
  Qed.

  Lemma isim_stateL X run r g R_src R_tgt
    (Q : R_src -> R_tgt -> shared_rel)
    ps pt ktr_src itr_tgt ths im_src im_tgt st_src st_tgt
    : bi_entails
        (isim r g Q true pt (ktr_src (snd (run st_src) : X)) itr_tgt ths im_src im_tgt (fst (run st_src)) st_tgt)
        (isim r g Q ps pt (trigger (State run) >>= ktr_src) itr_tgt ths im_src im_tgt st_src st_tgt).
  Proof.
    try uPred.unseal. split.
    intros x WF H r_ctx WFx.
    muclo lsim_indC_spec.
    eapply lsim_stateL. muclo lsim_resetC_spec. econs; [eapply H|..]; eauto.
  Qed.

  Lemma isim_stateR X run r g R_src R_tgt
    (Q : R_src -> R_tgt -> shared_rel)
    ps pt itr_src ktr_tgt ths im_src im_tgt st_src st_tgt
    : bi_entails
        (isim r g Q ps true itr_src (ktr_tgt (snd (run st_tgt) : X)) ths im_src im_tgt st_src (fst (run st_tgt)))
        (isim r g Q ps pt itr_src (trigger (State run) >>= ktr_tgt) ths im_src im_tgt st_src st_tgt).
  Proof.
    try uPred.unseal. split.
    intros x WF H r_ctx WFx.
    ii. muclo lsim_indC_spec.
    eapply lsim_stateR. muclo lsim_resetC_spec. econs; [eapply H|..]; eauto.
  Qed.

  Lemma isim_tidL r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        ps pt ktr_src itr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (isim r g Q true pt (ktr_src tid) itr_tgt ths im_src im_tgt st_src st_tgt)
      (isim r g Q ps pt (trigger GetTid >>= ktr_src) itr_tgt ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    try uPred.unseal. split.
    intros x WF H r_ctx WFx.
    ii. muclo lsim_indC_spec.
    eapply lsim_tidL. muclo lsim_resetC_spec. econs; [eapply H|..]; eauto.
  Qed.

  Lemma isim_tidR r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        ps pt itr_src ktr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (isim r g Q ps true itr_src (ktr_tgt tid) ths im_src im_tgt st_src st_tgt)
      (isim r g Q ps pt itr_src (trigger GetTid >>= ktr_tgt) ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    try uPred.unseal. split.
    intros x WF H r_ctx WFx.
    ii. muclo lsim_indC_spec.
    eapply lsim_tidR. muclo lsim_resetC_spec. econs; [eapply H|..]; eauto.
  Qed.

  Lemma isim_fairL f r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        ps pt ktr_src itr_tgt ths im_src0 im_tgt st_src st_tgt
    :
    bi_entails
      (∃ im_src1, ⌜fair_update im_src0 im_src1 f⌝ ∧ isim r g Q true pt (ktr_src tt) itr_tgt ths im_src1 im_tgt st_src st_tgt)
      (isim r g Q ps pt (trigger (Fair f) >>= ktr_src) itr_tgt ths im_src0 im_tgt st_src st_tgt)
  .
  Proof.
    try uPred.unseal. split.
    intros x WF H r_ctx WFx.
    ii. muclo lsim_indC_spec.
    eapply lsim_fairL.
    rr in H. des.
    rr in H. des.
    rr in H.
    esplits; eauto.
  Qed.

  Lemma isim_fairR f r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        ps pt itr_src ktr_tgt ths im_src im_tgt0 st_src st_tgt
    :
    bi_entails
      (∀ im_tgt1, ⌜fair_update im_tgt0 im_tgt1 (prism_fmap inrp f)⌝ -∗ isim r g Q ps true itr_src (ktr_tgt tt) ths im_src im_tgt1 st_src st_tgt)
      (isim r g Q ps pt itr_src (trigger (Fair f) >>= ktr_tgt) ths im_src im_tgt0 st_src st_tgt)
  .
  Proof.
    try uPred.unseal. split.
    intros x WF H r_ctx WFx.
    ii. muclo lsim_indC_spec.
    eapply lsim_fairR. i.
    rr in H.
    hexploit (H im_tgt1 ε); eauto.
    { rewrite right_id. eauto. }
    { rewrite right_id. done. }
  Qed.

  Lemma isim_UB r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        ps pt ktr_src itr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (True)
      (isim r g Q ps pt (trigger Undefined >>= ktr_src) itr_tgt ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    try uPred.unseal. split.
    intros x WF H r_ctx WFx.
    ii. muclo lsim_indC_spec.
    eapply lsim_UB.
  Qed.

  Lemma isim_observe fn args r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        ps pt ktr_src ktr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (∀ ret, isim g g Q true true (ktr_src ret) (ktr_tgt ret) ths im_src im_tgt st_src st_tgt)
      (isim r g Q ps pt (trigger (Observe fn args) >>= ktr_src) (trigger (Observe fn args) >>= ktr_tgt) ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    try uPred.unseal. split.
    intros x WF H r_ctx WFx.
    rr. i.
    ii. gstep. rr. eapply pind9_fold.
    eapply lsim_observe; eauto.
    i. rr in H.
    muclo lsim_resetC_spec. econs; [eapply H|..]; eauto.
  Qed.

  Lemma isim_yieldL r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        ps pt ktr_src ktr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (isim r g Q true pt (ktr_src tt) (trigger (Yield) >>= ktr_tgt) ths im_src im_tgt st_src st_tgt)
      (isim r g Q ps pt (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt) ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    try uPred.unseal. split.
    intros x WF H r_ctx WFx.
    rr. i.
    ii. muclo lsim_indC_spec.
    eapply lsim_yieldL. muclo lsim_resetC_spec. econs; [eapply H|..]; eauto.
  Qed.

  Lemma isim_yieldR r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        ps pt ktr_src ktr_tgt ths0 im_src0 im_tgt0 st_src0 st_tgt0
    :
    bi_entails
      (I ths0 im_src0 im_tgt0 st_src0 st_tgt0 ∗ (∀ ths1 im_src1 im_tgt1 st_src1 st_tgt1 im_tgt2, I ths1 im_src1 im_tgt1 st_src1 st_tgt1 -∗ ⌜fair_update im_tgt1 im_tgt2 (prism_fmap inlp (tids_fmap tid ths1))⌝ -∗ isim r g Q ps true (trigger (Yield) >>= ktr_src) (ktr_tgt tt) ths1 im_src1 im_tgt2 st_src1 st_tgt1))
      (isim r g Q ps pt (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt) ths0 im_src0 im_tgt0 st_src0 st_tgt0)
  .
  Proof.
    try uPred.unseal. split.
    intros x WF H r_ctx WFx.
    rr. i.
    rr in H. des. rename H into EQ.
    rewrite EQ in WF,WFx.
    ii. muclo lsim_indC_spec.
    eapply lsim_yieldR; eauto.
    i. specialize (H1 ths1 im_src1 im_tgt1 st_src1 st_tgt1 im_tgt2).
    hexploit (H1 r_shared1); eauto.
    { eapply cmra_valid_op_l. instantiate (1:=r_ctx1). r_wf VALID. }
    i. rr in H. hexploit (H ε); eauto.
    { eapply cmra_valid_op_l. instantiate (1:=r_ctx1). r_wf VALID. }
    r_wf VALID.
  Qed.

  Lemma isim_sync r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        ps pt ktr_src ktr_tgt ths0 im_src0 im_tgt0 st_src0 st_tgt0
    :
    bi_entails
      (I ths0 im_src0 im_tgt0 st_src0 st_tgt0 ∗ (∀ ths1 im_src1 im_tgt1 st_src1 st_tgt1 im_tgt2, I ths1 im_src1 im_tgt1 st_src1 st_tgt1 -∗ ⌜fair_update im_tgt1 im_tgt2 (prism_fmap inlp (tids_fmap tid ths1))⌝ -∗ isim g g Q true true (ktr_src tt) (ktr_tgt tt) ths1 im_src1 im_tgt2 st_src1 st_tgt1))
      (isim r g Q ps pt (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt) ths0 im_src0 im_tgt0 st_src0 st_tgt0)
  .
  Proof.
    try uPred.unseal. split.
    intros x WF H r_ctx WFx.
    rr in H. des. rename H into EQ.
    rewrite EQ in WF,WFx.
    ii. gstep. eapply pind9_fold. eapply lsim_sync; eauto.
    i. specialize (H1 ths1 im_src1 im_tgt1 st_src1 st_tgt1 im_tgt2).
    hexploit (H1 r_shared1); eauto.
    { eapply cmra_valid_op_l. instantiate (1:=r_ctx1). r_wf VALID. }
    i. rr in H. hexploit (H ε); eauto.
    { eapply cmra_valid_op_l. instantiate (1:=r_ctx1). r_wf VALID. }
    r_wf VALID.
  Qed.

  Lemma isim_base r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (@r _ _ Q ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
      (isim r g Q ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    try uPred.unseal. split.
    intros x WF H r_ctx WFx.
    ii. gbase. econs; eauto.
  Qed.

  Lemma isim_reset r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (isim r g Q false false itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
      (isim r g Q ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    try uPred.unseal. split.
    intros x WF H r_ctx WFx.
    ii. rr in H. muclo lsim_resetC_spec. econs; [eapply H|..]; eauto.
  Qed.

  Lemma isim_stutter_mon r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt
        ps' pt'
        (MONS: ps' = true -> ps = true)
        (MONT: pt' = true -> pt = true)
    :
    bi_entails
      (isim r g Q ps' pt' itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
      (isim r g Q ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    try uPred.unseal. split.
    intros x WF H r_ctx WFx.
    ii. rr in H. muclo lsim_resetC_spec. econs; [eapply H|..]; eauto.
  Qed.

  Lemma isim_progress r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        itr_src itr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (isim g g Q false false itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
      (isim r g Q true true itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    try uPred.unseal. split.
    intros x WF H r_ctx WFx.
    ii. gstep. rr. eapply pind9_fold.
    eapply lsim_progress; eauto.
  Qed.

  Lemma unlift_mon (r0 r1: rel)
        (MON: forall R_src R_tgt (Q: R_src -> R_tgt -> shared_rel)
                     ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt,
            bi_entails
              (@r0 _ _ Q ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
              (#=> (@r1 _ _ Q ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt)))
    :
    unlift r0 <9= unlift r1.
  Proof.
    i. dependent destruction PR.
    hexploit MON; eauto.
    rewrite /bi_entails. try uPred.unseal.
    intros [H].
    hexploit H; [|eauto|..].
    { eapply cmra_valid_op_l. done. }
    i. rr in H0.
    hexploit H0; eauto.
    i. des. econs; eauto.
  Qed.

  Lemma isim_mono_knowledge (r0 g0 r1 g1: rel) R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt
        (MON0: forall R_src R_tgt (Q: R_src -> R_tgt -> shared_rel)
                      ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt,
            bi_entails
              (@r0 _ _ Q ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
              (#=> (@r1 _ _ Q ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt)))
        (MON1: forall R_src R_tgt (Q: R_src -> R_tgt -> shared_rel)
                      ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt,
            bi_entails
              (@g0 _ _ Q ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
              (#=> (@g1 _ _ Q ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt)))
    :
    bi_entails
      (isim r0 g0 Q ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
      (isim r1 g1 Q ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    rewrite /bi_entails /bi_entails /bi.uPredI.
    split.
    ii. hexploit H0; eauto. i.
    eapply gpaco9_mon; eauto.
    { eapply unlift_mon; eauto. }
    { eapply unlift_mon; eauto. }
  Qed.

  Lemma isim_coind A
        (R_src: forall (a: A), Type)
        (R_tgt: forall (a: A), Type)
        (Q: forall (a: A), R_src a -> R_tgt a -> shared_rel)
        (ps pt: forall (a: A), bool)
        (itr_src : forall (a: A), itree srcE (R_src a))
        (itr_tgt : forall (a: A), itree tgtE (R_tgt a))
        (ths: forall (a: A), TIdSet.t)
        (im_src: forall (a: A), imap ident_src wf_src)
        (im_tgt: forall (a: A), imap (sum_tid ident_tgt) nat_wf)
        (st_src: forall (a: A), state_src)
        (st_tgt: forall (a: A), state_tgt)
        (P: forall (a: A), iProp)
        (r g0: rel)
        (COIND: forall (g1: rel) a, bi_entails (□((∀ R_src R_tgt (Q: R_src -> R_tgt -> shared_rel)
                                                     ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt,
                                                      @g0 R_src R_tgt Q ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt -∗ @g1 R_src R_tgt Q ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
                                                    ∗
                                                    (∀ a, P a -∗ @g1 (R_src a) (R_tgt a) (Q a) (ps a) (pt a) (itr_src a) (itr_tgt a) (ths a) (im_src a) (im_tgt a) (st_src a) (st_tgt a))) ∗ P a) (isim r g1 (Q a) (ps a) (pt a) (itr_src a) (itr_tgt a) (ths a) (im_src a) (im_tgt a) (st_src a) (st_tgt a)))
    :
    (forall a, bi_entails (P a) (isim r g0 (Q a) (ps a) (pt a) (itr_src a) (itr_tgt a) (ths a) (im_src a) (im_tgt a) (st_src a) (st_tgt a))).
  Proof.
    rewrite /bi_entails /bi_entails /bi.uPredI. split.
    intros r0 WF H r_ctx WF0.
    clear WF.
    revert a r0 H r_ctx WF0. gcofix CIH. i.
    epose (fun R_src R_tgt (Q: R_src -> R_tgt -> shared_rel)
               ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt =>
            {| upred.uPred_holds r_own :=
                forall r_ctx (WF: ✓ (r_own ⋅ r_ctx)),
                  gpaco9 gf (cpn9 gf) r0 r0 R_src R_tgt (liftRR Q) ps pt r_ctx itr_src itr_tgt (ths, im_src, im_tgt, st_src, st_tgt) |}) as i.
    hexploit (COIND i a). subst i. clear COIND.
    rewrite /bi_entails /bi_entails /bi.uPredI. intros [H].
    revert H. uPred.unseal. intros H. hexploit H.
    { instantiate (1:=r1). eapply cmra_valid_op_l; eauto. }
    { exists ε, r1. splits; eauto.
      { by rewrite left_id. }
      rewrite /bi_intuitionistically /bi_affinely /bi_persistently. uPred.unseal.
      rr. esplits.
      { rr. ss. }
      exists ε, ε. splits.
      { rewrite right_id. apply core_id_total. apply _. }
      { ss. ii. gbase. eapply CIH0. econs; eauto.
        rewrite left_id in WF. done.
      }
      { ss. ii. gbase. eapply CIH; eauto. rewrite left_id in WF. done.
      }
    }
    clear H. i. eapply gpaco9_gpaco.
    { auto. }
    eapply gpaco9_mon.
    { eapply H. eauto. }
    { i. gbase. eauto. }
    { i. dependent destruction PR. subst.
      rr in REL. eapply gpaco9_mon.
      { eapply REL; eauto. }
      { eauto. }
      { eauto. }
    }
    Unshelve.
    { i. ss. i. eapply H; eauto.
      eapply cmra_valid_included; eauto. eapply RA.extends_add; eauto.
    }
  Qed.

End SIM.

Section EQUIVI.

  Context `{Σ: GRA.t}.

  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable ident_src: ID.
  Variable ident_tgt: ID.

  Let srcE := threadE ident_src state_src.
  Let tgtE := threadE ident_tgt state_tgt.

  Variable wf_src: WF.
  Variable tid: thread_id.

  Lemma isim_equivI
        I1 I2
        (EQUIV : forall ths ims imt sts stt, I1 ths ims imt sts stt ⊣⊢ I2 ths ims imt sts stt)
        r g R_src R_tgt Q
        ps pt (itr_src : itree srcE R_src) (itr_tgt : itree tgtE R_tgt)
        ths (im_src : imap ident_src wf_src) (im_tgt : imap (sum_tid ident_tgt) nat_wf) st_src st_tgt
    :
    (isim (Σ:=Σ) tid I1 r g Q ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
      ⊢
      (isim (Σ:=Σ) tid I2 r g Q ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    assert (EQ: forall ths ims imt sts stt (r : Σ) (WF: ✓ r), upred.uPred_holds (to_upred (I1 ths ims imt sts stt)) r <-> upred.uPred_holds (to_upred (I2 ths ims imt sts stt)) r).
    { clear - EQUIV. i. specialize (EQUIV ths ims imt sts stt). rr in EQUIV. inv EQUIV. eauto. }
    split. rr. i.
    ii. rr in H0. eapply lsim_equivI. 2: eapply H0; eauto.
    clear - EQ. i. destruct shr as [[[[ths ims] imt] sts] stt]. unfold liftI. rewrite EQ; auto.
  Qed.

End EQUIVI.
