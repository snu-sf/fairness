From sflib Require Import sflib.
From Paco Require Import paco.
From Fairness Require Import ITreeLib IProp IPM ModSim ModSimNat PCM.
From Fairness Require PCMLarge.
Require Import Program.

Set Implicit Arguments.

Section SIM.
  Context `{Σ: GRA.t}.

  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable ident_src: ID.
  Variable ident_tgt: ID.

  Variable wf_src: WF.

  Let srcE := threadE ident_src state_src.
  Let tgtE := threadE ident_tgt state_tgt.

  Let shared_rel := TIdSet.t -> (@imap ident_src wf_src) -> (@imap (sum_tid ident_tgt) nat_wf) -> state_src -> state_tgt -> iProp.

  Definition liftI (R: shared_rel): (TIdSet.t *
                               (@imap ident_src wf_src) *
                               (@imap (sum_tid ident_tgt) nat_wf) *
                               state_src *
                               state_tgt) -> Σ -> Prop :=
        fun '(ths, im_src, im_tgt, st_src, st_tgt) r_shared =>
          R ths im_src im_tgt st_src st_tgt r_shared.

  Let liftRR R_src R_tgt (RR: R_src -> R_tgt -> shared_rel):
    R_src -> R_tgt -> Σ -> (TIdSet.t *
                              (@imap ident_src wf_src) *
                              (@imap (sum_tid ident_tgt) nat_wf) *
                              state_src *
                              state_tgt) -> Prop :=
        fun r_src r_tgt r_ctx '(ths, im_src, im_tgt, st_src, st_tgt) =>
          exists r,
            (<<WF: URA.wf (r ⋅ r_ctx)>>) /\
              RR r_src r_tgt ths im_src im_tgt st_src st_tgt r.

  Variable tid: thread_id.
  Variable I: shared_rel.

  Let rel := (forall R_src R_tgt (Q: R_src -> R_tgt -> shared_rel), bool -> bool -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel).

  Let gf := (fun r => pind9 ((@__lsim (to_LURA Σ)) _ _ _ _ _ _ (liftI I) tid r) top9).
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
        (REL: r R_src R_tgt Q ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt r_own)
        (WF: URA.wf (r_own ⋅ r_ctx))
      :
      unlift r (liftRR Q) ps pt r_ctx itr_src itr_tgt (ths, im_src, im_tgt, st_src, st_tgt)
  .

  Program Definition isim: rel -> rel -> rel :=
    fun
      r g
      R_src R_tgt Q ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt =>
      iProp_intro
        (fun r_own =>
           forall r_ctx (WF: URA.wf (r_own ⋅ r_ctx)),
             gpaco9 gf (cpn9 gf) (@unlift r) (@unlift g) _ _ (liftRR Q) ps pt r_ctx itr_src itr_tgt (ths, im_src, im_tgt, st_src, st_tgt)) _.
  Next Obligation.
  Proof.
    ii. ss. eapply H.
    eapply URA.wf_extends; eauto. eapply URA.extends_add; eauto.
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
    rr. autorewrite with iprop. i.
    rr in H. autorewrite with iprop in H.
    ii. hexploit H; eauto. i. des. eauto.
  Qed.

  Global Instance isim_elim_upd
         r g R_src R_tgt
         (Q: R_src -> R_tgt -> shared_rel)
         ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt p
         P
    :
    ElimModal True p false (#=> P) P (isim r g Q ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt) (isim r g Q ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt).
  Proof.
    unfold ElimModal. rewrite bi.intuitionistically_if_elim.
    i. iIntros "[H0 H1]".
    iApply isim_upd. iMod "H0". iModIntro.
    iApply "H1". iFrame.
  Qed.

  Lemma Ladd (a b: Σ): @PCMLarge.URA.add (to_LURA Σ) a b = URA.add a b.
  Proof.
    unfold PCMLarge.URA.add. PCMLarge.unseal "ra". ur. auto.
  Qed.

  Lemma Lwf (a: Σ): @PCMLarge.URA.wf (to_LURA Σ) a = URA.wf a.
  Proof.
    unfold PCMLarge.URA.wf. PCMLarge.unseal "ra". ur. auto.
  Qed.

  Lemma Lunit: @PCMLarge.URA.unit (to_LURA Σ) = URA.unit.
  Proof.
    Local Transparent PCMLarge.URA.unit.
    unfold PCMLarge.URA.unit. PCMLarge.unseal "ra". ur. auto.
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
    rr. autorewrite with iprop. i.
    rr in H. autorewrite with iprop in H. des. subst.
    ii. eapply gpaco9_uclo; [auto with paco|apply lsim_frameC_spec|].
    econs.
    instantiate (1:=a).
    eapply gpaco9_uclo; [auto with paco|apply lsim_monoC_spec|].
    econs.
    2:{ eapply H1. r_wf WF0. rewrite Ladd. r_solve. }
    unfold liftRR. i. subst. des_ifs. des.
    rr in H0. autorewrite with iprop in H0. specialize (H0 r_src).
    rr in H0. autorewrite with iprop in H0. specialize (H0 r_tgt).
    rr in H0. autorewrite with iprop in H0. specialize (H0 t).
    rr in H0. autorewrite with iprop in H0. specialize (H0 i0).
    rr in H0. autorewrite with iprop in H0. specialize (H0 i).
    rr in H0. autorewrite with iprop in H0. specialize (H0 s0).
    rr in H0. autorewrite with iprop in H0. specialize (H0 s).
    rr in H0. autorewrite with iprop in H0.
    hexploit (H0 r0); eauto.
    { eapply URA.wf_mon. instantiate (1:=r_ctx'). r_wf WF1. rewrite Ladd. r_solve. }
    i. rr in H. autorewrite with iprop in H.
    hexploit H.
    { instantiate (1:=r_ctx'). r_wf WF1. rewrite Ladd. r_solve. }
    i. des. esplits; eauto.
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
    rr. autorewrite with iprop. i.
    ii. eapply gpaco9_uclo; [auto with paco|apply lsim_bindC_spec|].
    econs.
    eapply gpaco9_uclo; [auto with paco|apply lsim_monoC_spec|].
    econs.
    2:{ eapply H; eauto. }
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
    rr. autorewrite with iprop. i.
    ii. muclo lsim_indC_spec.
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
    rr. autorewrite with iprop. i.
    ii. muclo lsim_indC_spec.
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
    rr. autorewrite with iprop. i.
    ii. muclo lsim_indC_spec.
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
    rr. autorewrite with iprop. i.
    ii. muclo lsim_indC_spec.
    eapply lsim_chooseL.
    rr in H. autorewrite with iprop in H. des.
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
    rr. autorewrite with iprop. i.
    ii. muclo lsim_indC_spec.
    eapply lsim_chooseR.
    rr in H. autorewrite with iprop in H.
    i. econs; [eapply H|..]; eauto.
  Qed.

  Lemma isim_stateL X run r g R_src R_tgt
    (Q : R_src -> R_tgt -> shared_rel)
    ps pt ktr_src itr_tgt ths im_src im_tgt st_src st_tgt
    : bi_entails
        (isim r g Q true pt (ktr_src (snd (run st_src) : X)) itr_tgt ths im_src im_tgt (fst (run st_src)) st_tgt)
        (isim r g Q ps pt (trigger (State run) >>= ktr_src) itr_tgt ths im_src im_tgt st_src st_tgt).
  Proof.
    rr. autorewrite with iprop. i.
    ii. muclo lsim_indC_spec.
    eapply lsim_stateL. muclo lsim_resetC_spec. econs; [eapply H|..]; eauto.
  Qed.

  Lemma isim_stateR X run r g R_src R_tgt
    (Q : R_src -> R_tgt -> shared_rel)
    ps pt itr_src ktr_tgt ths im_src im_tgt st_src st_tgt
    : bi_entails
        (isim r g Q ps true itr_src (ktr_tgt (snd (run st_tgt) : X)) ths im_src im_tgt st_src (fst (run st_tgt)))
        (isim r g Q ps pt itr_src (trigger (State run) >>= ktr_tgt) ths im_src im_tgt st_src st_tgt).
  Proof.
    rr. autorewrite with iprop. i.
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
    rr. autorewrite with iprop. i.
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
    rr. autorewrite with iprop. i.
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
    rr. autorewrite with iprop. i.
    ii. muclo lsim_indC_spec.
    eapply lsim_fairL.
    rr in H. autorewrite with iprop in H. des.
    rr in H. autorewrite with iprop in H. des.
    rr in H. autorewrite with iprop in H.
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
    rr. autorewrite with iprop. i.
    ii. muclo lsim_indC_spec.
    eapply lsim_fairR. i.
    rr in H. autorewrite with iprop in H.
    hexploit H; eauto. i.
    rr in H0. autorewrite with iprop in H0.
    hexploit (H0 URA.unit); eauto.
    { rewrite URA.unit_id. eapply URA.wf_mon; eauto. }
    { rr. autorewrite with iprop. eauto. }
    i. muclo lsim_resetC_spec. econs; [eapply H1|..]; eauto. r_wf WF0.
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
    rr. autorewrite with iprop. i.
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
    rr. autorewrite with iprop. i.
    ii. gstep. rr. eapply pind9_fold.
    eapply lsim_observe; eauto.
    i. rr in H. autorewrite with iprop in H.
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
    rr. autorewrite with iprop. i.
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
    rr. autorewrite with iprop. i.
    rr in H. autorewrite with iprop in H. des. subst.
    ii. muclo lsim_indC_spec.
    eapply lsim_yieldR; eauto.
    { rewrite Lwf. repeat rewrite Ladd. eauto. }
    i. rr in H1. autorewrite with iprop in H1. specialize (H1 ths1).
    rr in H1. autorewrite with iprop in H1. specialize (H1 im_src1).
    rr in H1. autorewrite with iprop in H1. specialize (H1 im_tgt1).
    rr in H1. autorewrite with iprop in H1. specialize (H1 st_src1).
    rr in H1. autorewrite with iprop in H1. specialize (H1 st_tgt1).
    rr in H1. autorewrite with iprop in H1. specialize (H1 im_tgt2).
    rr in H1. autorewrite with iprop in H1.
    hexploit (H1 r_shared1); eauto.
    { eapply URA.wf_mon. instantiate (1:=r_ctx1). rewrite Lwf in VALID. r_wf VALID.
      repeat rewrite Ladd. r_solve.
    }
    i. rr in H. autorewrite with iprop in H. hexploit (H URA.unit); eauto.
    { eapply URA.wf_mon. instantiate (1:=r_ctx1).
      rewrite Lwf in VALID. r_wf VALID.
      repeat rewrite Ladd. r_solve.
    }
    { rr. autorewrite with iprop. eauto. }
    i. muclo lsim_resetC_spec. econs; [eapply H2|..]; eauto.
    rewrite Lwf in VALID. r_wf VALID.
    repeat rewrite Ladd. r_solve.
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
    rr. autorewrite with iprop. i.
    rr in H. autorewrite with iprop in H. des. subst.
    ii. gstep. eapply pind9_fold. eapply lsim_sync; eauto. i.
    { rewrite Lwf. repeat rewrite Ladd. eauto. }
    i.
    rr in H1. autorewrite with iprop in H1. specialize (H1 ths1).
    rr in H1. autorewrite with iprop in H1. specialize (H1 im_src1).
    rr in H1. autorewrite with iprop in H1. specialize (H1 im_tgt1).
    rr in H1. autorewrite with iprop in H1. specialize (H1 st_src1).
    rr in H1. autorewrite with iprop in H1. specialize (H1 st_tgt1).
    rr in H1. autorewrite with iprop in H1. specialize (H1 im_tgt2).
    rr in H1. autorewrite with iprop in H1.
    hexploit (H1 r_shared1); eauto.
    { eapply URA.wf_mon. instantiate (1:=r_ctx1).
      rewrite Lwf in VALID. r_wf VALID.
      repeat rewrite Ladd. r_solve.
    }
    i. rr in H. autorewrite with iprop in H. hexploit (H URA.unit); eauto.
    { eapply URA.wf_mon. instantiate (1:=r_ctx1).
      rewrite Lwf in VALID. r_wf VALID.
      repeat rewrite Ladd. r_solve.
    }
    { rr. autorewrite with iprop. eauto. }
    i. muclo lsim_resetC_spec. econs; [eapply H2|..]; eauto.
    rewrite Lwf in VALID. r_wf VALID.
    repeat rewrite Ladd. r_solve.
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
    rr. autorewrite with iprop.
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
    rr. autorewrite with iprop. i.
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
    rr. autorewrite with iprop. i.
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
    hexploit MON; eauto. i.
    rr in H. autorewrite with iprop in H.
    hexploit H; [|eauto|..].
    { eapply URA.wf_mon. eauto. }
    i. rr in H0. autorewrite with iprop in H0.
    hexploit H0; eauto. i. des. econs; eauto.
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
    rr. autorewrite with iprop. i.
    ii. rr in H. hexploit H; eauto. i.
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
    i. rr. autorewrite with iprop. ii. clear WF.
    revert a r0 H r_ctx WF0. gcofix CIH. i.
    epose (fun R_src R_tgt (Q: R_src -> R_tgt -> shared_rel)
               ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt =>
             @iProp_intro _ (fun r_own => forall r_ctx (WF: URA.wf (r_own ⋅ r_ctx)),
                                 gpaco9 gf (cpn9 gf) r0 r0 R_src R_tgt (liftRR Q) ps pt r_ctx itr_src itr_tgt (ths, im_src, im_tgt, st_src, st_tgt)) _).
    hexploit (COIND i a). subst i. clear COIND. i.
    rr in H. autorewrite with iprop in H. hexploit H.
    { instantiate (1:=r1). eapply URA.wf_mon; eauto. }
    { rr. autorewrite with iprop.
      exists URA.unit, r1. splits; auto.
      { r_solve. }
      rr. autorewrite with iprop. esplits.
      { rr. autorewrite with iprop. ss. }
      rr. autorewrite with iprop.
      rr. autorewrite with iprop.
      exists URA.unit, URA.unit. splits.
      { rewrite URA.unit_core. r_solve. }
      { do 13 (rr; autorewrite with iprop; i).
        ss. i. gbase. eapply CIH0. econs; eauto. r_wf WF.
      }
      { do 2 (rr; autorewrite with iprop; i).
        ss. i. gbase. eapply CIH; eauto. r_wf WF.
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
      eapply URA.wf_extends; eauto. eapply URA.extends_add; eauto.
    }
  Qed.

End SIM.
