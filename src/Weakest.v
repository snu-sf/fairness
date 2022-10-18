From sflib Require Import sflib.
From Paco Require Import paco.
From Fairness Require Import PCM ITreeLib IProp IPM ModSim ModSimNat.
Require Import Program.

Set Implicit Arguments.


Section SIM.
  Context `{Σ: GRA.t}.

  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable ident_src: ID.
  Variable ident_tgt: ID.

  Variable wf_src: WF.

  Let srcE := ((@eventE ident_src +' cE) +' sE state_src).
  Let tgtE := ((@eventE ident_tgt +' cE) +' sE state_tgt).

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

  Let rel := (forall R_src R_tgt (Q: R_src -> R_tgt -> shared_rel), itree srcE R_src -> itree tgtE R_tgt -> shared_rel).

  Let gf := (fun r => pind9 (__lsim (liftI I) tid r) top9).
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
        (REL: r R_src R_tgt Q itr_src itr_tgt ths im_src im_tgt st_src st_tgt r_own)
        (WF: URA.wf (r_own ⋅ r_ctx))
        (PS: ps = false)
        (PT: pt = false)
      :
      unlift r (liftRR Q) ps pt r_ctx itr_src itr_tgt (ths, im_src, im_tgt, st_src, st_tgt)
  .

  Program Definition isim: rel -> rel -> rel :=
    fun
      r g
      R_src R_tgt Q itr_src itr_tgt ths im_src im_tgt st_src st_tgt =>
      iProp_intro
        (fun r_own =>
           forall r_ctx (WF: URA.wf (r_own ⋅ r_ctx)),
             gpaco9 gf (cpn9 gf) (@unlift r) (@unlift g) _ _ (liftRR Q) false false r_ctx itr_src itr_tgt (ths, im_src, im_tgt, st_src, st_tgt)) _.
  Next Obligation.
  Proof.
    ii. ss. eapply H.
    eapply URA.wf_extends; eauto. eapply URA.extends_add; eauto.
  Qed.

  Tactic Notation "muclo" uconstr(H) :=
    eapply gpaco9_uclo; [auto with paco|apply H|].

  Lemma isim_upd r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        itr_src itr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (#=> (isim r g Q itr_src itr_tgt ths im_src im_tgt st_src st_tgt))
      (isim r g Q itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    rr. autorewrite with iprop. i.
    rr in H. autorewrite with iprop in H.
    ii. hexploit H; eauto. i. des. eauto.
  Qed.

  Global Instance isim_elim_upd
         r g R_src R_tgt
         (Q: R_src -> R_tgt -> shared_rel)
         itr_src itr_tgt ths im_src im_tgt st_src st_tgt
         P
    :
    ElimModal True false false (#=> P) P (isim r g Q itr_src itr_tgt ths im_src im_tgt st_src st_tgt) (isim r g Q itr_src itr_tgt ths im_src im_tgt st_src st_tgt).
  Proof.
    unfold ElimModal. i. iIntros "[H0 H1]".
    iApply isim_upd. iMod "H0". iModIntro.
    iApply "H1". iFrame.
  Qed.

  Lemma isim_wand r g R_src R_tgt
        (Q0 Q1: R_src -> R_tgt -> shared_rel)
        itr_src itr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      ((∀ r_src r_tgt ths im_src im_tgt st_src st_tgt,
           ((Q0 r_src r_tgt ths im_src im_tgt st_src st_tgt) -∗ #=> (Q1 r_src r_tgt ths im_src im_tgt st_src st_tgt))) ** (isim r g Q0 itr_src itr_tgt ths im_src im_tgt st_src st_tgt))
      (isim r g Q1 itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    rr. autorewrite with iprop. i.
    rr in H. autorewrite with iprop in H. des. subst.
    ii. eapply gpaco9_uclo; [auto with paco|apply lsim_frameC_spec|].
    econs.
    instantiate (1:=a).
    eapply gpaco9_uclo; [auto with paco|apply lsim_monoC_spec|].
    econs.
    2:{ eapply H1. r_wf WF0. }
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
    { eapply URA.wf_mon. instantiate (1:=r_ctx'). r_wf WF1. }
    i. rr in H. autorewrite with iprop in H.
    hexploit H.
    { instantiate (1:=r_ctx'). r_wf WF1. }
    i. des. esplits; eauto.
  Qed.

  Lemma isim_mono r g R_src R_tgt
        (Q0 Q1: R_src -> R_tgt -> shared_rel)
        (MONO: forall r_src r_tgt ths im_src im_tgt st_src st_tgt,
            bi_entails
              (Q0 r_src r_tgt ths im_src im_tgt st_src st_tgt)
              (#=> (Q1 r_src r_tgt ths im_src im_tgt st_src st_tgt)))
        itr_src itr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (isim r g Q0 itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
      (isim r g Q1 itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    iIntros. iApply isim_wand. iFrame.
    iIntros. iApply MONO. eauto.
  Qed.

  Lemma isim_frame r g R_src R_tgt
        P (Q: R_src -> R_tgt -> shared_rel)
        itr_src itr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (P ** isim r g Q itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
      (isim r g (fun r_src r_tgt ths im_src im_tgt st_src st_tgt =>
                   P ** Q r_src r_tgt ths im_src im_tgt st_src st_tgt)
            itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    iIntros "[H0 H1]". iApply isim_wand. iFrame.
    iIntros. iModIntro. iFrame.
  Qed.

  Lemma isim_bind r g R_src R_tgt S_src S_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        (itr_src: itree srcE S_src) (itr_tgt: itree tgtE S_tgt)
        ktr_src ktr_tgt
        ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (isim r g (fun s_src s_tgt ths im_src im_tgt st_src st_tgt =>
                   isim r g Q (ktr_src s_src) (ktr_tgt s_tgt) ths im_src im_tgt st_src st_tgt) itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
      (isim r g Q (itr_src >>= ktr_src) (itr_tgt >>= ktr_tgt) ths im_src im_tgt st_src st_tgt)
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
        r_src r_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (Q r_src r_tgt ths im_src im_tgt st_src st_tgt)
      (isim r g Q (Ret r_src) (Ret r_tgt) ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    rr. autorewrite with iprop. i.
    ii. muclo lsim_indC_spec.
    eapply lsim_ret. unfold liftRR. esplits; eauto.
  Qed.

  Lemma isim_tauL r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        itr_src itr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (isim r g Q itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
      (isim r g Q (Tau itr_src) itr_tgt ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    rr. autorewrite with iprop. i.
    ii. muclo lsim_indC_spec.
    eapply lsim_tauL. muclo lsim_resetC_spec. econs; eauto.
  Qed.

  Lemma isim_tauR r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        itr_src itr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (isim r g Q itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
      (isim r g Q itr_src (Tau itr_tgt) ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    rr. autorewrite with iprop. i.
    ii. muclo lsim_indC_spec.
    eapply lsim_tauR. muclo lsim_resetC_spec. econs; eauto.
  Qed.

  Lemma isim_chooseL X r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        ktr_src itr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (∃ x, isim r g Q (ktr_src x) itr_tgt ths im_src im_tgt st_src st_tgt)
      (isim r g Q (trigger (Choose X) >>= ktr_src) itr_tgt ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    rr. autorewrite with iprop. i.
    ii. muclo lsim_indC_spec.
    eapply lsim_chooseL.
    rr in H. autorewrite with iprop in H. des.
    esplits; eauto. muclo lsim_resetC_spec. econs; eauto.
  Qed.

  Lemma isim_chooseR X r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        itr_src ktr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (∀ x, isim r g Q itr_src (ktr_tgt x) ths im_src im_tgt st_src st_tgt)
      (isim r g Q itr_src (trigger (Choose X) >>= ktr_tgt) ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    rr. autorewrite with iprop. i.
    ii. muclo lsim_indC_spec.
    eapply lsim_chooseR.
    rr in H. autorewrite with iprop in H.
    i. muclo lsim_resetC_spec. econs; [eapply H|..]; eauto.
  Qed.

  Lemma isim_putL st r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        ktr_src itr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (isim r g Q (ktr_src tt) itr_tgt ths im_src im_tgt st st_tgt)
      (isim r g Q (trigger (Put st) >>= ktr_src) itr_tgt ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    rr. autorewrite with iprop. i.
    ii. muclo lsim_indC_spec.
    eapply lsim_putL. muclo lsim_resetC_spec. econs; [eapply H|..]; eauto.
  Qed.

  Lemma isim_putR st r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        itr_src ktr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (isim r g Q itr_src (ktr_tgt tt) ths im_src im_tgt st_src st)
      (isim r g Q itr_src (trigger (Put st) >>= ktr_tgt) ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    rr. autorewrite with iprop. i.
    ii. muclo lsim_indC_spec.
    eapply lsim_putR. muclo lsim_resetC_spec. econs; [eapply H|..]; eauto.
  Qed.

  Lemma isim_getL r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        ktr_src itr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (isim r g Q (ktr_src st_src) itr_tgt ths im_src im_tgt st_src st_tgt)
      (isim r g Q (trigger (@Get _) >>= ktr_src) itr_tgt ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    rr. autorewrite with iprop. i.
    ii. muclo lsim_indC_spec.
    eapply lsim_getL. muclo lsim_resetC_spec. econs; [eapply H|..]; eauto.
  Qed.

  Lemma isim_getR r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        itr_src ktr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (isim r g Q itr_src (ktr_tgt st_tgt) ths im_src im_tgt st_src st_tgt)
      (isim r g Q itr_src (trigger (@Get _) >>= ktr_tgt) ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    rr. autorewrite with iprop. i.
    ii. muclo lsim_indC_spec.
    eapply lsim_getR. muclo lsim_resetC_spec. econs; [eapply H|..]; eauto.
  Qed.

  Lemma isim_tidL r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        ktr_src itr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (isim r g Q (ktr_src tid) itr_tgt ths im_src im_tgt st_src st_tgt)
      (isim r g Q (trigger GetTid >>= ktr_src) itr_tgt ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    rr. autorewrite with iprop. i.
    ii. muclo lsim_indC_spec.
    eapply lsim_tidL. muclo lsim_resetC_spec. econs; [eapply H|..]; eauto.
  Qed.

  Lemma isim_tidR r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        itr_src ktr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (isim r g Q itr_src (ktr_tgt tid) ths im_src im_tgt st_src st_tgt)
      (isim r g Q itr_src (trigger GetTid >>= ktr_tgt) ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    rr. autorewrite with iprop. i.
    ii. muclo lsim_indC_spec.
    eapply lsim_tidR. muclo lsim_resetC_spec. econs; [eapply H|..]; eauto.
  Qed.

  Lemma isim_fairL f r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        ktr_src itr_tgt ths im_src0 im_tgt st_src st_tgt
    :
    bi_entails
      (∃ im_src1, ⌜fair_update im_src0 im_src1 f⌝ ∧ isim r g Q (ktr_src tt) itr_tgt ths im_src1 im_tgt st_src st_tgt)
      (isim r g Q (trigger (Fair f) >>= ktr_src) itr_tgt ths im_src0 im_tgt st_src st_tgt)
  .
  Proof.
    rr. autorewrite with iprop. i.
    ii. muclo lsim_indC_spec.
    eapply lsim_fairL.
    rr in H. autorewrite with iprop in H. des.
    rr in H. autorewrite with iprop in H. des.
    rr in H. autorewrite with iprop in H.
    esplits; eauto. muclo lsim_resetC_spec. econs; [eapply H0|..]; eauto.
  Qed.

  Lemma isim_fairR f r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        itr_src ktr_tgt ths im_src im_tgt0 st_src st_tgt
    :
    bi_entails
      (∀ im_tgt1, ⌜fair_update im_tgt0 im_tgt1 (sum_fmap_r f)⌝ -* isim r g Q itr_src (ktr_tgt tt) ths im_src im_tgt1 st_src st_tgt)
      (isim r g Q itr_src (trigger (Fair f) >>= ktr_tgt) ths im_src im_tgt0 st_src st_tgt)
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
        ktr_src itr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (True)
      (isim r g Q (trigger Undefined >>= ktr_src) itr_tgt ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    rr. autorewrite with iprop. i.
    ii. muclo lsim_indC_spec.
    eapply lsim_UB.
  Qed.

  Lemma isim_observe fn args r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        ktr_src ktr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (∀ ret, isim g g Q (ktr_src ret) (ktr_tgt ret) ths im_src im_tgt st_src st_tgt)
      (isim r g Q (trigger (Observe fn args) >>= ktr_src) (trigger (Observe fn args) >>= ktr_tgt) ths im_src im_tgt st_src st_tgt)
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
        ktr_src ktr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (isim r g Q (ktr_src tt) (trigger (Yield) >>= ktr_tgt) ths im_src im_tgt st_src st_tgt)
      (isim r g Q (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt) ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    rr. autorewrite with iprop. i.
    ii. muclo lsim_indC_spec.
    eapply lsim_yieldL. muclo lsim_resetC_spec. econs; [eapply H|..]; eauto.
  Qed.

  Lemma isim_yieldR r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        ktr_src ktr_tgt ths0 im_src0 im_tgt0 st_src0 st_tgt0
    :
    bi_entails
      (I ths0 im_src0 im_tgt0 st_src0 st_tgt0 ** (∀ ths1 im_src1 im_tgt1 st_src1 st_tgt1 im_tgt2, I ths1 im_src1 im_tgt1 st_src1 st_tgt1 -* ⌜fair_update im_tgt1 im_tgt2 (sum_fmap_l (tids_fmap tid ths1))⌝ -* isim r g Q (trigger (Yield) >>= ktr_src) (ktr_tgt tt) ths1 im_src1 im_tgt2 st_src1 st_tgt1))
      (isim r g Q (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt) ths0 im_src0 im_tgt0 st_src0 st_tgt0)
  .
  Proof.
    rr. autorewrite with iprop. i.
    rr in H. autorewrite with iprop in H. des. subst.
    ii. muclo lsim_indC_spec.
    eapply lsim_yieldR; eauto. i.
    rr in H1. autorewrite with iprop in H1. specialize (H1 ths1).
    rr in H1. autorewrite with iprop in H1. specialize (H1 im_src1).
    rr in H1. autorewrite with iprop in H1. specialize (H1 im_tgt1).
    rr in H1. autorewrite with iprop in H1. specialize (H1 st_src1).
    rr in H1. autorewrite with iprop in H1. specialize (H1 st_tgt1).
    rr in H1. autorewrite with iprop in H1. specialize (H1 im_tgt2).
    rr in H1. autorewrite with iprop in H1.
    hexploit (H1 r_shared1); eauto.
    { eapply URA.wf_mon. instantiate (1:=r_ctx1). r_wf VALID. }
    i. rr in H. autorewrite with iprop in H. hexploit (H URA.unit); eauto.
    { eapply URA.wf_mon. instantiate (1:=r_ctx1). r_wf VALID. }
    { rr. autorewrite with iprop. eauto. }
    i. muclo lsim_resetC_spec. econs; [eapply H2|..]; eauto. r_wf VALID.
  Qed.

  Lemma isim_sync r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        ktr_src ktr_tgt ths0 im_src0 im_tgt0 st_src0 st_tgt0
    :
    bi_entails
      (I ths0 im_src0 im_tgt0 st_src0 st_tgt0 ** (∀ ths1 im_src1 im_tgt1 st_src1 st_tgt1 im_tgt2, I ths1 im_src1 im_tgt1 st_src1 st_tgt1 -* ⌜fair_update im_tgt1 im_tgt2 (sum_fmap_l (tids_fmap tid ths1))⌝ -* isim g g Q (ktr_src tt) (ktr_tgt tt) ths1 im_src1 im_tgt2 st_src1 st_tgt1))
      (isim r g Q (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt) ths0 im_src0 im_tgt0 st_src0 st_tgt0)
  .
  Proof.
    rr. autorewrite with iprop. i.
    rr in H. autorewrite with iprop in H. des. subst.
    ii. gstep. eapply pind9_fold. eapply lsim_sync; eauto. i.
    rr in H1. autorewrite with iprop in H1. specialize (H1 ths1).
    rr in H1. autorewrite with iprop in H1. specialize (H1 im_src1).
    rr in H1. autorewrite with iprop in H1. specialize (H1 im_tgt1).
    rr in H1. autorewrite with iprop in H1. specialize (H1 st_src1).
    rr in H1. autorewrite with iprop in H1. specialize (H1 st_tgt1).
    rr in H1. autorewrite with iprop in H1. specialize (H1 im_tgt2).
    rr in H1. autorewrite with iprop in H1.
    hexploit (H1 r_shared1); eauto.
    { eapply URA.wf_mon. instantiate (1:=r_ctx1). r_wf VALID. }
    i. rr in H. autorewrite with iprop in H. hexploit (H URA.unit); eauto.
    { eapply URA.wf_mon. instantiate (1:=r_ctx1). r_wf VALID. }
    { rr. autorewrite with iprop. eauto. }
    i. muclo lsim_resetC_spec. econs; [eapply H2|..]; eauto. r_wf VALID.
  Qed.

  Lemma isim_base r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        itr_src itr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (@r _ _ Q itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
      (isim r g Q itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    rr. autorewrite with iprop.
    ii. gbase. econs; eauto.
  Qed.

  Lemma unlift_mon (r0 r1: rel)
        (MON: forall R_src R_tgt (Q: R_src -> R_tgt -> shared_rel)
                     itr_src itr_tgt ths im_src im_tgt st_src st_tgt,
            bi_entails
              (@r0 _ _ Q itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
              (#=> (@r1 _ _ Q itr_src itr_tgt ths im_src im_tgt st_src st_tgt)))
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
        itr_src itr_tgt ths im_src im_tgt st_src st_tgt
        (MON0: forall R_src R_tgt (Q: R_src -> R_tgt -> shared_rel)
                      itr_src itr_tgt ths im_src im_tgt st_src st_tgt,
            bi_entails
              (@r0 _ _ Q itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
              (#=> (@r1 _ _ Q itr_src itr_tgt ths im_src im_tgt st_src st_tgt)))
        (MON1: forall R_src R_tgt (Q: R_src -> R_tgt -> shared_rel)
                      itr_src itr_tgt ths im_src im_tgt st_src st_tgt,
            bi_entails
              (@g0 _ _ Q itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
              (#=> (@g1 _ _ Q itr_src itr_tgt ths im_src im_tgt st_src st_tgt)))
    :
    bi_entails
      (isim r0 g0 Q itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
      (isim r1 g1 Q itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    rr. autorewrite with iprop. i.
    ii. rr in H. hexploit H; eauto. i.
    eapply gpaco9_mon; eauto.
    { eapply unlift_mon; eauto. }
    { eapply unlift_mon; eauto. }
  Qed.

  Lemma isim_coind A
        (R_src: forall (a: A), Prop)
        (R_tgt: forall (a: A), Prop)
        (Q: forall (a: A), R_src a -> R_tgt a -> shared_rel)
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
                                                     itr_src itr_tgt ths im_src im_tgt st_src st_tgt,
                                                      @g0 R_src R_tgt Q itr_src itr_tgt ths im_src im_tgt st_src st_tgt -* @g1 R_src R_tgt Q itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
                                                    **
                                                    (∀ a, P a -* @g1 (R_src a) (R_tgt a) (Q a) (itr_src a) (itr_tgt a) (ths a) (im_src a) (im_tgt a) (st_src a) (st_tgt a))) ** P a) (isim r g1 (Q a) (itr_src a) (itr_tgt a) (ths a) (im_src a) (im_tgt a) (st_src a) (st_tgt a)))
    :
    (forall a, bi_entails (P a) (isim r g0 (Q a) (itr_src a) (itr_tgt a) (ths a) (im_src a) (im_tgt a) (st_src a) (st_tgt a))).
  Proof.
    i. rr. autorewrite with iprop. ii. clear WF.
    revert a r0 H r_ctx WF0. gcofix CIH. i.
    epose (fun R_src R_tgt (Q: R_src -> R_tgt -> shared_rel)
               itr_src itr_tgt ths im_src im_tgt st_src st_tgt =>
             @iProp_intro _ (fun r_own => forall r_ctx (WF: URA.wf (r_own ⋅ r_ctx)),
                                 gpaco9 gf (cpn9 gf) r0 r0 R_src R_tgt (liftRR Q) false false r_ctx itr_src itr_tgt (ths, im_src, im_tgt, st_src, st_tgt)) _).
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

From Fairness Require Import ThreadsRA StateRA FairRA.

Section STATE.
  Context `{Σ: GRA.t}.

  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable ident_src: ID.
  Variable ident_tgt: ID.

  Variable wf_src: WF.

  Let srcE := ((@eventE ident_src +' cE) +' sE state_src).
  Let tgtE := ((@eventE ident_tgt +' cE) +' sE state_tgt).

  Let shared_rel := TIdSet.t -> (@imap ident_src wf_src) -> (@imap (sum_tid ident_tgt) nat_wf) -> state_src -> state_tgt -> iProp.

  Variable I_aux: iProp.

  Context `{MONORA: @GRA.inG monoRA Σ}.
  Context `{THSRA: @GRA.inG ths_RA Σ}.
  Context `{STATESRC: @GRA.inG (stateSrcRA state_src) Σ}.
  Context `{STATETGT: @GRA.inG (stateTgtRA state_tgt) Σ}.
  Context `{IDENTSRC: @GRA.inG (identSrcRA ident_src wf_src) Σ}.
  Context `{IDENTTGT: @GRA.inG (identTgtRA ident_tgt) Σ}.
  Context `{IDENTTHS: @GRA.inG identThsRA Σ}.

  Let I: shared_rel :=
        fun ths im_src im_tgt st_src st_tgt =>
          default_I ths im_src im_tgt st_src st_tgt ** I_aux.

  Let rel := (forall R_src R_tgt (Q: R_src -> R_tgt -> iProp), itree srcE R_src -> itree tgtE R_tgt -> iProp).

  Variable tid: thread_id.

  Let unlift_rel
      (r: forall R_src R_tgt (Q: R_src -> R_tgt -> shared_rel), itree srcE R_src -> itree tgtE R_tgt -> shared_rel): rel :=
        fun R_src R_tgt Q itr_src itr_tgt =>
          (∀ ths im_src im_tgt st_src st_tgt,
              (default_I ths im_src im_tgt st_src st_tgt)
                -*
                (@r R_src R_tgt (fun r_src r_tgt ths im_src im_tgt st_src st_tgt => default_I ths im_src im_tgt st_src st_tgt ** Q r_src r_tgt) itr_src itr_tgt ths im_src im_tgt st_src st_tgt))%I.

  Let lift_rel (rr: rel):
    forall R_src R_tgt (QQ: R_src -> R_tgt -> shared_rel), itree srcE R_src -> itree tgtE R_tgt -> shared_rel :=
        fun R_src R_tgt QQ itr_src itr_tgt ths im_src im_tgt st_src st_tgt =>
          (∃ (Q: R_src -> R_tgt -> iProp)
             (EQ: QQ = (fun r_src r_tgt ths im_src im_tgt st_src st_tgt =>
                          default_I ths im_src im_tgt st_src st_tgt ** Q r_src r_tgt)),
              rr R_src R_tgt Q itr_src itr_tgt ** default_I ths im_src im_tgt st_src st_tgt)%I.

  Let unlift_rel_base r
    :
    forall R_src R_tgt Q itr_src itr_tgt ths im_src im_tgt st_src st_tgt,
      (r R_src R_tgt Q itr_src itr_tgt)
        -∗
        (default_I ths im_src im_tgt st_src st_tgt)
        -∗
        (lift_rel
           r
           (fun r_src r_tgt ths im_src im_tgt st_src st_tgt => default_I ths im_src im_tgt st_src st_tgt ** Q r_src r_tgt)
           itr_src itr_tgt ths im_src im_tgt st_src st_tgt).
  Proof.
    unfold lift_rel, unlift_rel. i.
    iIntros "H D". iExists _, _. Unshelve.
    { iFrame. }
    { auto. }
  Qed.

  Let unlift_lift r
    :
    forall R_src R_tgt Q itr_src itr_tgt ths im_src im_tgt st_src st_tgt,
      (lift_rel (unlift_rel r) Q itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
        ⊢ (r R_src R_tgt Q itr_src itr_tgt ths im_src im_tgt st_src st_tgt).
  Proof.
    unfold lift_rel, unlift_rel. i.
    iIntros "[% [% [H D]]]". subst.
    iApply ("H" with "D").
  Qed.

  Let lift_unlift (r0: rel) (r1: forall R_src R_tgt (Q: R_src -> R_tgt -> shared_rel), itree srcE R_src -> itree tgtE R_tgt -> shared_rel)
    :
    bi_entails
      (∀ R_src R_tgt (Q: R_src -> R_tgt -> shared_rel) itr_src itr_tgt ths im_src im_tgt st_src st_tgt,
          @lift_rel r0 R_src R_tgt Q itr_src itr_tgt ths im_src im_tgt st_src st_tgt -* r1 R_src R_tgt Q itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
      (∀ R_src R_tgt Q itr_src itr_tgt, r0 R_src R_tgt Q itr_src itr_tgt -* unlift_rel r1 Q itr_src itr_tgt).
  Proof.
    unfold lift_rel, unlift_rel.
    iIntros "IMPL" (? ? ? ? ?) "H". iIntros (? ? ? ? ?) "D".
    iApply "IMPL". iExists _, _. Unshelve.
    { iFrame. }
    { auto. }
  Qed.

  Let lift_rel_mon (rr0 rr1: rel)
      (MON: forall R_src R_tgt Q itr_src itr_tgt,
          bi_entails
            (rr0 R_src R_tgt Q itr_src itr_tgt)
            (#=> rr1 R_src R_tgt Q itr_src itr_tgt))
    :
    forall R_src R_tgt (QQ: R_src -> R_tgt -> shared_rel) itr_src itr_tgt ths im_src im_tgt st_src st_tgt,
      bi_entails
        (lift_rel rr0 QQ itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
        (#=> lift_rel rr1 QQ itr_src itr_tgt ths im_src im_tgt st_src st_tgt).
  Proof.
    unfold lift_rel. i.
    iIntros "[% [% [H D]]]". subst.
    iPoseProof (MON with "H") as "> H".
    iModIntro. iExists _, _. Unshelve.
    { iFrame. }
    { auto. }
  Qed.

  Definition stsim: rel -> rel -> rel :=
    fun r g
        R_src R_tgt Q itr_src itr_tgt =>
      (∀ ths im_src im_tgt st_src st_tgt,
          (default_I ths im_src im_tgt st_src st_tgt)
            -*
            (isim
               tid
               I
               (lift_rel r)
               (lift_rel g)
               (fun r_src r_tgt ths im_src im_tgt st_src st_tgt => default_I ths im_src im_tgt st_src st_tgt ** Q r_src r_tgt)
               itr_src itr_tgt
               ths im_src im_tgt st_src st_tgt))%I.

  Record mytype
         (A: Type) :=
    mk_mytype {
        comp_a: A;
        comp_ths: TIdSet.t;
        comp_im_src: imap ident_src wf_src;
        comp_im_tgt: imap (sum_tid ident_tgt) nat_wf;
        comp_st_src: state_src;
        comp_st_tgt: state_tgt;
      }.





  Lemma stsim_base r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        itr_src itr_tgt
    :
    (@r _ _ Q itr_src itr_tgt)
      -∗
      (stsim r g Q itr_src itr_tgt)
  .
  Proof.
    unfold stsim. iIntros "H" (? ? ? ? ?) "D".
    iApply isim_base.
    iApply (unlift_rel_base with "H D").
  Qed.

  Lemma stsim_mono_knowledge (r0 g0 r1 g1: rel) R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        itr_src itr_tgt
        (MON0: forall R_src R_tgt (Q: R_src -> R_tgt -> iProp)
                      itr_src itr_tgt,
            (@r0 _ _ Q itr_src itr_tgt)
              -∗
              (#=> (@r1 _ _ Q itr_src itr_tgt)))
        (MON1: forall R_src R_tgt (Q: R_src -> R_tgt -> iProp)
                      itr_src itr_tgt,
            (@g0 _ _ Q itr_src itr_tgt)
              -∗
              (#=> (@g1 _ _ Q itr_src itr_tgt)))
    :
    bi_entails
      (stsim r0 g0 Q itr_src itr_tgt)
      (stsim r1 g1 Q itr_src itr_tgt)
  .
  Proof.
    unfold stsim. iIntros "H" (? ? ? ? ?) "D".
    iApply isim_mono_knowledge.
    { eapply lift_rel_mon. eauto. }
    { eapply lift_rel_mon. eauto. }
    iApply ("H" with "D").
  Qed.

  Lemma stsim_coind A
        (R_src: forall (a: A), Prop)
        (R_tgt: forall (a: A), Prop)
        (Q: forall (a: A), R_src a -> R_tgt a -> iProp)
        (itr_src : forall (a: A), itree srcE (R_src a))
        (itr_tgt : forall (a: A), itree tgtE (R_tgt a))
        (P: forall (a: A), iProp)
        (r g0: rel)
        (COIND: forall (g1: rel) a,
            (□((∀ R_src R_tgt (Q: R_src -> R_tgt -> iProp)
                  itr_src itr_tgt,
                   @g0 R_src R_tgt Q itr_src itr_tgt -* @g1 R_src R_tgt Q itr_src itr_tgt)
                 **
                 (∀ a, P a -* @g1 (R_src a) (R_tgt a) (Q a) (itr_src a) (itr_tgt a))))
              -∗
              (P a)
              -∗
              (stsim r g1 (Q a) (itr_src a) (itr_tgt a)))
    :
    (forall a, bi_entails (P a) (stsim r g0 (Q a) (itr_src a) (itr_tgt a))).
  Proof.
    cut (forall (m: mytype A),
            bi_entails
              ((fun m => P m.(comp_a) ** default_I m.(comp_ths) m.(comp_im_src) m.(comp_im_tgt) m.(comp_st_src) m.(comp_st_tgt)) m)
              (isim tid I (lift_rel r) (lift_rel g0) ((fun m => fun r_src r_tgt ths im_src im_tgt st_src st_tgt => default_I ths im_src im_tgt st_src st_tgt ** Q m.(comp_a) r_src r_tgt) m)
                    ((fun m => itr_src m.(comp_a)) m) ((fun m => itr_tgt m.(comp_a)) m) (comp_ths m) (comp_im_src m) (comp_im_tgt m) (comp_st_src m) (comp_st_tgt m))).
    { ss. i.
      unfold stsim. iIntros "H" (? ? ? ? ?) "D".
      specialize (H (mk_mytype a ths im_src im_tgt st_src st_tgt)). ss.
      iApply H. iFrame.
    }
    eapply isim_coind. i. iIntros "[# CIH [H D]]".
    unfold stsim in COIND.
    iAssert (□((∀ R_src R_tgt (Q: R_src -> R_tgt -> iProp)
                  itr_src itr_tgt,
                   @g0 R_src R_tgt Q itr_src itr_tgt -* @unlift_rel g1 R_src R_tgt Q itr_src itr_tgt)
                 **
                 (∀ a, P a -* @unlift_rel g1 (R_src a) (R_tgt a) (Q a) (itr_src a) (itr_tgt a))))%I with "[CIH]" as "CIH'".
    { iPoseProof "CIH" as "# [CIH0 CIH1]". iModIntro. iSplitL.
      { iApply (lift_unlift with "CIH0"). }
      { iIntros. unfold unlift_rel. iIntros.
        iSpecialize ("CIH1" $! (mk_mytype _ _ _ _ _ _)). ss.
        iApply "CIH1". iFrame.
      }
    }
    iPoseProof (COIND with "CIH' H D") as "H".
    iApply (isim_mono_knowledge with "H").
    { auto. }
    { i. iIntros "H". iModIntro. iApply unlift_lift. auto. }
  Qed.

  Lemma stsim_upd r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        itr_src itr_tgt
    :
    (#=> (stsim r g Q itr_src itr_tgt))
      -∗
      (stsim r g Q itr_src itr_tgt)
  .
  Proof.
    unfold stsim. iIntros "H" (? ? ? ? ?) "D". iMod "H".
    iApply "H". auto.
  Qed.

  Global Instance stsim_elim_upd
         r g R_src R_tgt
         (Q: R_src -> R_tgt -> iProp)
         itr_src itr_tgt
         P
    :
    ElimModal True false false (#=> P) P (stsim r g Q itr_src itr_tgt) (stsim r g Q itr_src itr_tgt).
  Proof.
    unfold ElimModal. i. iIntros "[H0 H1]".
    iApply stsim_upd. iMod "H0". iModIntro.
    iApply "H1". iFrame.
  Qed.

  Lemma stsim_wand r g R_src R_tgt
        (Q0 Q1: R_src -> R_tgt -> iProp)
        itr_src itr_tgt
    :
    (stsim r g Q0 itr_src itr_tgt)
      -∗
      (∀ r_src r_tgt,
          ((Q0 r_src r_tgt) -∗ #=> (Q1 r_src r_tgt)))
      -∗
      (stsim r g Q1 itr_src itr_tgt)
  .
  Proof.
    unfold stsim. iIntros "H0 H1" (? ? ? ? ?) "D".
    iApply isim_wand.
    iPoseProof ("H0" $! _ _ _ _ _ with "D") as "H0".
    iSplitR "H0"; [|auto]. iIntros (? ? ? ? ? ? ?) "[D H0]".
    iPoseProof ("H1" $! _ _ with "H0") as "> H0". iModIntro. iFrame.
  Qed.

  Lemma stsim_mono r g R_src R_tgt
        (Q0 Q1: R_src -> R_tgt -> iProp)
        (MONO: forall r_src r_tgt,
            (Q0 r_src r_tgt)
              -∗
              (#=> (Q1 r_src r_tgt)))
        itr_src itr_tgt
    :
    (stsim r g Q0 itr_src itr_tgt)
      -∗
      (stsim r g Q1 itr_src itr_tgt)
  .
  Proof.
    iIntros "H". iApply (stsim_wand with "H").
    iIntros. iApply MONO. auto.
  Qed.

  Lemma stsim_frame r g R_src R_tgt
        P (Q: R_src -> R_tgt -> iProp)
        itr_src itr_tgt
    :
    (stsim r g Q itr_src itr_tgt)
      -∗
      P
      -∗
      (stsim r g (fun r_src r_tgt => P ** Q r_src r_tgt) itr_src itr_tgt)
  .
  Proof.
    iIntros "H0 H1". iApply (stsim_wand with "H0").
    iIntros. iModIntro. iFrame.
  Qed.

  Lemma stsim_bind r g R_src R_tgt S_src S_tgt
        (Q: R_src -> R_tgt -> iProp)
        (itr_src: itree srcE S_src) (itr_tgt: itree tgtE S_tgt)
        ktr_src ktr_tgt
    :
    (stsim r g (fun s_src s_tgt => stsim r g Q (ktr_src s_src) (ktr_tgt s_tgt)) itr_src itr_tgt)
      -∗
      (stsim r g Q (itr_src >>= ktr_src) (itr_tgt >>= ktr_tgt))
  .
  Proof.
    unfold stsim. iIntros "H" (? ? ? ? ?) "D".
    iPoseProof ("H" $! _ _ _ _ _ with "D") as "H".
    iApply isim_bind. iApply (isim_mono with "H").
    iIntros (? ? ? ? ? ? ?) "[D H]".
    iPoseProof ("H" $! _ _ _ _ _ with "D") as "H". iModIntro. iFrame.
  Qed.

  Lemma stsim_ret r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        r_src r_tgt
    :
    (Q r_src r_tgt)
      -∗
      (stsim r g Q (Ret r_src) (Ret r_tgt))
  .
  Proof.
    unfold stsim. iIntros "H" (? ? ? ? ?) "D".
    iApply isim_ret. iFrame.
  Qed.

  Lemma stsim_tauL r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        itr_src itr_tgt
    :
    (stsim r g Q itr_src itr_tgt)
      -∗
      (stsim r g Q (Tau itr_src) itr_tgt)
  .
  Proof.
    unfold stsim. iIntros "H" (? ? ? ? ?) "D".
    iPoseProof ("H" $! _ _ _ _ _ with "D") as "H".
    iApply isim_tauL. iFrame.
  Qed.

  Lemma stsim_tauR r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        itr_src itr_tgt
    :
    (stsim r g Q itr_src itr_tgt)
      -∗
      (stsim r g Q itr_src (Tau itr_tgt))
  .
  Proof.
    unfold stsim. iIntros "H" (? ? ? ? ?) "D".
    iPoseProof ("H" $! _ _ _ _ _ with "D") as "H".
    iApply isim_tauR. iFrame.
  Qed.

  Lemma stsim_chooseL X r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ktr_src itr_tgt
    :
    (∃ x, stsim r g Q (ktr_src x) itr_tgt)
      -∗
      (stsim r g Q (trigger (Choose X) >>= ktr_src) itr_tgt)
  .
  Proof.
    unfold stsim. iIntros "[% H]" (? ? ? ? ?) "D".
    iPoseProof ("H" $! _ _ _ _ _ with "D") as "H".
    iApply isim_chooseL. iExists _. iFrame.
  Qed.

  Lemma stsim_chooseR X r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        itr_src ktr_tgt
    :
    (∀ x, stsim r g Q itr_src (ktr_tgt x))
      -∗
      (stsim r g Q itr_src (trigger (Choose X) >>= ktr_tgt))
  .
  Proof.
    unfold stsim. iIntros "H" (? ? ? ? ?) "D".
    iApply isim_chooseR. iIntros (?).
    iPoseProof ("H" $! _ _ _ _ _ _ with "D") as "H". iFrame.
  Qed.

  Lemma stsim_putL st r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ktr_src itr_tgt st_src
    :
    (OwnM (Auth.white (Excl.just st_src: @Excl.t state_src): stateSrcRA state_src))
      -∗
      ((OwnM (Auth.white (Excl.just st: @Excl.t state_src): stateSrcRA state_src))
         -∗ (stsim r g Q (ktr_src tt) itr_tgt))
      -∗
      (stsim r g Q (trigger (Put st) >>= ktr_src) itr_tgt)
  .
  Proof.
    unfold stsim. iIntros "H0 H1" (? ? ? ? ?) "D".
    iPoseProof (default_I_update_st_src with "D H0") as "> [D H0]".
    iApply isim_putL. iApply ("H1" with "D H0").
  Qed.

  Lemma stsim_putR st r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        itr_src ktr_tgt st_tgt
    :
    (OwnM (Auth.white (Excl.just st_tgt: @Excl.t state_tgt): stateSrcRA state_tgt))
      -∗
      ((OwnM (Auth.white (Excl.just st: @Excl.t state_tgt): stateSrcRA state_tgt))
         -∗ (stsim r g Q itr_src (ktr_tgt tt)))
      -∗
      (stsim r g Q itr_src (trigger (Put st) >>= ktr_tgt))
  .
  Proof.
    unfold stsim. iIntros "H0 H1" (? ? ? ? ?) "D".
    iPoseProof (default_I_update_st_tgt with "D H0") as "> [D H0]".
    iApply isim_putR. iApply ("H1" with "D H0").
  Qed.

  Lemma stsim_getL st r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ktr_src itr_tgt
    :
    ((OwnM (Auth.white (Excl.just st: @Excl.t state_src): stateSrcRA state_src)) ∧
       (stsim r g Q (ktr_src st) itr_tgt))
      -∗
      (stsim r g Q (trigger (@Get _) >>= ktr_src) itr_tgt)
  .
  Proof.
    unfold stsim. iIntros "H" (? ? ? ? ?) "D". iApply isim_getL.
    iAssert (⌜st_src = st⌝)%I as "%".
    { iDestruct "H" as "[H _]". iApply (default_I_get_st_src with "D"); eauto. }
    subst. iDestruct "H" as "[_ H]". iApply ("H" with "D").
  Qed.

  Lemma stsim_getR st r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        itr_src ktr_tgt
    :
    ((OwnM (Auth.white (Excl.just st: @Excl.t state_tgt): stateTgtRA state_tgt)) ∧
       (stsim r g Q itr_src (ktr_tgt st)))
      -∗
      (stsim r g Q itr_src (trigger (@Get _) >>= ktr_tgt))
  .
  Proof.
    unfold stsim. iIntros "H" (? ? ? ? ?) "D". iApply isim_getR.
    iAssert (⌜st_tgt = st⌝)%I as "%".
    { iDestruct "H" as "[H _]". iApply (default_I_get_st_tgt with "D"); eauto. }
    subst. iDestruct "H" as "[_ H]". iApply ("H" with "D").
  Qed.

  Lemma stsim_tidL r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ktr_src itr_tgt
    :
    (stsim r g Q (ktr_src tid) itr_tgt)
      -∗
      (stsim r g Q (trigger GetTid >>= ktr_src) itr_tgt)
  .
  Proof.
    unfold stsim. iIntros "H" (? ? ? ? ?) "D".
    iApply isim_tidL. iApply ("H" with "D").
  Qed.

  Lemma stsim_tidR r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        itr_src ktr_tgt
    :
    (stsim r g Q itr_src (ktr_tgt tid))
      -∗
      (stsim r g Q itr_src (trigger GetTid >>= ktr_tgt))
  .
  Proof.
    unfold stsim. iIntros "H" (? ? ? ? ?) "D".
    iApply isim_tidR. iApply ("H" with "D").
  Qed.

  Lemma stsim_fairL f r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ktr_src itr_tgt im_src0
    :
    (OwnM (Auth.white (Excl.just im_src0: @Excl.t _): identSrcRA ident_src wf_src))
      -∗
      (∃ im_src1, ⌜fair_update im_src0 im_src1 f⌝ ∧
                    ((OwnM (Auth.white (Excl.just im_src1: @Excl.t _): identSrcRA ident_src wf_src)) -∗ (stsim r g Q (ktr_src tt) itr_tgt)))
      -∗
      (stsim r g Q (trigger (Fair f) >>= ktr_src) itr_tgt).
  Proof.
    unfold stsim. iIntros "OWN H" (? ? ? ? ?) "D".
    iDestruct "H" as (im_src1) "[% H]".
    iPoseProof (default_I_get_ident_src with "D OWN") as "%". subst.
    iPoseProof (default_I_update_ident_src with "D OWN") as "> [OWN D]".
    iPoseProof ("H" with "OWN D") as "H".
    iApply isim_fairL. iExists _. iSplit; eauto.
  Qed.

  Lemma stsim_fairR f r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        itr_src ktr_tgt im_tgt0
    :
    (OwnM (Auth.white (Excl.just im_tgt0: @Excl.t _): identTgtRA ident_tgt))
      -∗
      (∀ im_tgt1, ⌜fair_update im_tgt0 im_tgt1 f⌝ -* (OwnM (Auth.white (Excl.just im_tgt1: @Excl.t _): identTgtRA ident_tgt)) -* stsim r g Q itr_src (ktr_tgt tt))
      -∗
      (stsim r g Q itr_src (trigger (Fair f) >>= ktr_tgt))
  .
  Proof.
    unfold stsim. iIntros "OWN H"  (? ? ? ? ?) "D".
    iPoseProof (default_I_get_ident_tgt with "D OWN") as "%". subst.
    iApply isim_fairR. iIntros (?) "%".
    iPoseProof (default_I_update_ident_tgt with "D OWN") as "> [OWN D]". ss.
    hexploit imap_proj_update_r; eauto. i. des. rewrite LEFT.
    iAssert (⌜fair_update (imap_proj_id2 im_tgt) (imap_proj_id2 im_tgt1) f⌝)%I as "UPD".
    { auto. }
    iPoseProof ("H" with "UPD OWN D") as "H".
    change (imap_proj_id1 im_tgt1, imap_proj_id2 im_tgt1) with (imap_proj_id im_tgt1).
    rewrite imap_sum_proj_id_inv2. iFrame.
  Qed.

  Lemma stsim_UB r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ktr_src itr_tgt
    :
    ⊢ (stsim r g Q (trigger Undefined >>= ktr_src) itr_tgt)
  .
  Proof.
    unfold stsim. iIntros (? ? ? ? ?) "D".
    iApply isim_UB. auto.
  Qed.

  Lemma stsim_observe fn args r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ktr_src ktr_tgt
    :
    (∀ ret, stsim g g Q (ktr_src ret) (ktr_tgt ret))
      -∗
      (stsim r g Q (trigger (Observe fn args) >>= ktr_src) (trigger (Observe fn args) >>= ktr_tgt))
  .
  Proof.
    unfold stsim. iIntros "H" (? ? ? ? ?) "D".
    iApply isim_observe. iIntros (?). iApply ("H" with "D").
  Qed.

  Lemma stsim_yieldL r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ktr_src ktr_tgt
    :
    (stsim r g Q (ktr_src tt) (trigger (Yield) >>= ktr_tgt))
      -∗
      (stsim r g Q (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt))
  .
  Proof.
    unfold stsim. iIntros "H" (? ? ? ? ?) "D".
    iApply isim_yieldL. iApply ("H" with "D").
  Qed.

  Lemma stsim_yieldR r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ktr_src ktr_tgt
    :
    I_aux
      -∗
      (I_aux -∗ ∃ im_ths0 ths, (OwnM (Auth.white (Excl.just im_ths0: @Excl.t _): identThsRA)) ** (own_threads_white ths ∧ (∀ im_ths1, (⌜fair_update im_ths0 im_ths1 (tids_fmap tid ths)⌝) -* (OwnM (Auth.white (Excl.just im_ths1: @Excl.t _): identThsRA)) -* stsim r g Q (trigger (Yield) >>= ktr_src) (ktr_tgt tt))))
      -∗
      (stsim r g Q (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt))
  .
  Proof.
    unfold stsim. iIntros "INV H" (? ? ? ? ?) "D".
    iApply isim_yieldR. unfold I. iFrame.
    iIntros (? ? ? ? ? ?) "[D INV] %". iPoseProof ("H" with "INV") as "H".
    iPoseProof "H" as (? ?) "[OWN H]".
    iAssert (⌜ths1 = ths0⌝)%I as "%".
    { iDestruct "H" as "[H _]". iApply (default_I_ths_eq with "D H"). }
    subst. iDestruct "H" as "[_ H]".
    iPoseProof (default_I_get_ident_ths with "D OWN") as "%". subst.
    iPoseProof (default_I_update_ident_ths with "D OWN") as "> [OWN D]". ss.
    hexploit imap_proj_update_l; eauto. i. des. rewrite RIGHT.
    iAssert (⌜fair_update (imap_proj_id1 im_tgt1) (imap_proj_id1 im_tgt2) (tids_fmap tid ths0)⌝)%I as "UPD".
    { auto. }
    iPoseProof ("H" with "UPD OWN D") as "H".
    change (imap_proj_id1 im_tgt2, imap_proj_id2 im_tgt2) with (imap_proj_id im_tgt2).
    rewrite imap_sum_proj_id_inv2. iFrame.
  Qed.

  Lemma stsim_sync r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ktr_src ktr_tgt
    :
    I_aux
      -∗
      (I_aux -∗ ∃ im_ths0 ths, (OwnM (Auth.white (Excl.just im_ths0: @Excl.t _): identThsRA)) ** (own_threads_white ths ∧ (∀ im_ths1, (⌜fair_update im_ths0 im_ths1 (tids_fmap tid ths)⌝) -* (OwnM (Auth.white (Excl.just im_ths1: @Excl.t _): identThsRA)) -* stsim g g Q (ktr_src tt) (ktr_tgt tt))))
      -∗
      (stsim r g Q (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt)).
  Proof.
    unfold stsim. iIntros "INV H" (? ? ? ? ?) "D".
    iApply isim_sync. unfold I. iFrame.
    iIntros (? ? ? ? ? ?) "[D INV] %". iPoseProof ("H" with "INV") as "H".
    iPoseProof "H" as (? ?) "[OWN H]".
    iAssert (⌜ths1 = ths0⌝)%I as "%".
    { iDestruct "H" as "[H _]". iApply (default_I_ths_eq with "D H"). }
    subst. iDestruct "H" as "[_ H]".
    iPoseProof (default_I_get_ident_ths with "D OWN") as "%". subst.
    iPoseProof (default_I_update_ident_ths with "D OWN") as "> [OWN D]". ss.
    hexploit imap_proj_update_l; eauto. i. des. rewrite RIGHT.
    iAssert (⌜fair_update (imap_proj_id1 im_tgt1) (imap_proj_id1 im_tgt2) (tids_fmap tid ths0)⌝)%I as "UPD".
    { auto. }
    iPoseProof ("H" with "UPD OWN D") as "H".
    change (imap_proj_id1 im_tgt2, imap_proj_id2 im_tgt2) with (imap_proj_id im_tgt2).
    rewrite imap_sum_proj_id_inv2. iFrame.
  Qed.

End STATE.


From Ordinal Require Import Ordinal Hessenberg Arithmetic.

Definition owf: WF := mk_wf Ord.lt_well_founded.

Section FAIR.
  Context `{Σ: GRA.t}.

  Definition itop5 { T0 T1 T2 T3 T4 } (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) (x4: T4 x0 x1 x2 x3): iProp := True%I.

  Definition itop6 { T0 T1 T2 T3 T4 T5 } (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) (x4: T4 x0 x1 x2 x3) (x5: T5 x0 x1 x2 x3 x4): iProp := True%I.

  Definition itop10 { T0 T1 T2 T3 T4 T5 T6 T7 T8 T9} (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) (x4: T4 x0 x1 x2 x3) (x5: T5 x0 x1 x2 x3 x4) (x6: T6 x0 x1 x2 x3 x4 x5) (x7: T7 x0 x1 x2 x3 x4 x5 x6) (x8: T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: T9 x0 x1 x2 x3 x4 x5 x6 x7 x8): iProp := True%I.

  Definition Pos (k: nat) (n: Ord.t): iProp. Admitted.
  Definition Neg (k: nat) (n: Ord.t): iProp. Admitted.
  Definition Ongoing (k: nat): iProp. Admitted.
  Definition Done (k: nat): iProp. Admitted.

  Lemma Pos_persistent k n
    :
    (Pos k n)
      -∗
      (□ Pos k n).
  Proof.
  Admitted.

  Global Program Instance Persistent_Pos k n: Persistent (Pos k n).
  Next Obligation.
  Proof.
    i. iIntros "POS". iPoseProof (Pos_persistent with "POS") as "POS". auto.
  Qed.

  Definition PosEx k: iProp := ∃ n, Pos k n.

  Lemma PosEx_persistent k
    :
    (PosEx k)
      -∗
      (□ PosEx k).
  Proof.
    iIntros "# H". auto.
  Qed.

  Global Program Instance Persistent_PosEx k: Persistent (PosEx k).

  Lemma PosEx_unfold k
    :
    (PosEx k)
      -∗
      (∃ n, Pos k n).
  Proof.
  Admitted.

  Lemma Neg_split n0 n1 k n
        (DECR: Ord.le (Hessenberg.add n0 n1) n)
    :
    (Neg k n)
      -∗
      (#=> (Neg k n0 ** Neg k n1)).
  Proof.
  Admitted.

  Lemma Pos_Neg_annihilate k n1
    :
    (Pos k n1)
      -∗
      (Neg k (Ord.from_nat 1))
      -∗
      (#=> (∃ n0, Pos k n0 ** ⌜Ord.lt n0 n1⌝)).
  Proof.
  Admitted.

  Lemma Done_persistent k
    :
    (Done k)
      -∗
      (□ Done k).
  Proof.
  Admitted.

  Global Program Instance Persistent_Done k: Persistent (Done k).
  Next Obligation.
  Proof.
    i. iIntros "DONE". iPoseProof (Done_persistent with "DONE") as "DONE". auto.
  Qed.

  Lemma Ongoing_not_Done k
    :
    (Ongoing k)
      -∗
      (Done k)
      -∗
      False.
  Proof.
  Admitted.

  Definition Eventually (k: nat) (P: iProp): iProp :=
    □ PosEx k ** (Ongoing k ∨ ((□ Done k) ** P)).

  Lemma eventually_done k P
    :
    (Done k)
      -∗
      (Eventually k P)
      -∗
      (P ** (P -* Eventually k P)).
  Proof.
  Admitted.

  Lemma eventually_intro_ongoing k P
    :
    (Ongoing k)
      -∗
      (Eventually k P).
  Proof.
  Admitted.

  Lemma eventually_intro_done k P
    :
    (Done k)
      -∗
      P
      -∗
      (Eventually k P).
  Proof.
  Admitted.

  Lemma eventually_finish k P
    :
    (Eventually k P)
      -∗
      ((□ Done k) ∨ (Ongoing k ** (Done k -* P -* Eventually k P))).
  Proof.
  Admitted.

  Lemma eventually_obligation k P
    :
    (Eventually k P)
      -∗
      (□ PosEx k).
  Proof.
  Admitted.

  Variable state_tgt: Type.
  Definition St_tgt: state_tgt -> iProp. Admitted.

  Variable state_src: Type.
  Definition St_src: state_src -> iProp. Admitted.

  Variable ident_src: ID.
  Variable ident_tgt: ID.

  Let srcE := ((@eventE ident_src +' cE) +' sE state_src).
  Let tgtE := ((@eventE ident_tgt +' cE) +' sE state_tgt).

  Variable I: iProp.

  Let rel := (forall R_src R_tgt (Q: R_src -> R_tgt -> list nat -> iProp), itree srcE R_src -> itree tgtE R_tgt -> list nat -> iProp).

  Variable tid: thread_id.

  Definition fsim: rel -> rel -> rel. Admitted.

  Lemma fsim_base r g R_src R_tgt
        (Q: R_src -> R_tgt -> list nat -> iProp)
        os itr_src itr_tgt
    :
    (@r _ _ Q itr_src itr_tgt os)
      -∗
      (fsim r g Q itr_src itr_tgt os)
  .
  Admitted.

  Lemma fsim_mono_knowledge (r0 g0 r1 g1: rel) R_src R_tgt
        (Q: R_src -> R_tgt -> list nat -> iProp)
        os itr_src itr_tgt
        (MON0: forall R_src R_tgt (Q: R_src -> R_tgt -> list nat -> iProp)
                      os itr_src itr_tgt,
            (@r0 _ _ Q itr_src itr_tgt os)
              -∗
              (#=> (@r1 _ _ Q itr_src itr_tgt os)))
        (MON1: forall R_src R_tgt (Q: R_src -> R_tgt -> list nat -> iProp)
                      os itr_src itr_tgt,
            (@g0 _ _ Q itr_src itr_tgt os)
              -∗
              (#=> (@g1 _ _ Q itr_src itr_tgt os)))
    :
    bi_entails
      (fsim r0 g0 Q os itr_src itr_tgt)
      (fsim r1 g1 Q os itr_src itr_tgt)
  .
  Proof.
  Admitted.

  Lemma fsim_coind A
        (R_src: forall (a: A), Prop)
        (R_tgt: forall (a: A), Prop)
        (Q: forall (a: A), R_src a -> R_tgt a -> list nat -> iProp)
        (o : forall (a: A), list nat)
        (itr_src : forall (a: A), itree srcE (R_src a))
        (itr_tgt : forall (a: A), itree tgtE (R_tgt a))
        (P: forall (a: A), iProp)
        (r g0: rel)
        (COIND: forall (g1: rel) a,
            (□((∀ R_src R_tgt (Q: R_src -> R_tgt -> list nat -> iProp)
                  os itr_src itr_tgt,
                   @g0 R_src R_tgt Q itr_src itr_tgt os -* @g1 R_src R_tgt Q itr_src itr_tgt os)
                 **
                 (∀ a, P a -* @g1 (R_src a) (R_tgt a) (Q a) (itr_src a) (itr_tgt a) (o a))))
              -∗
              (P a)
              -∗
              (fsim r g1 (Q a) (itr_src a) (itr_tgt a) (o a)))
    :
    (forall a, bi_entails (P a) (fsim r g0 (Q a) (itr_src a) (itr_tgt a) (o a))).
  Proof.
  Admitted.

  Lemma fsim_upd r g R_src R_tgt
        (Q: R_src -> R_tgt -> list nat -> iProp)
        os itr_src itr_tgt
    :
    (#=> (fsim r g Q itr_src itr_tgt os))
      -∗
      (fsim r g Q itr_src itr_tgt os)
  .
  Proof.
  Admitted.

  Global Instance fsim_elim_upd
         r g R_src R_tgt
         (Q: R_src -> R_tgt -> list nat -> iProp)
         os itr_src itr_tgt
         P
    :
    ElimModal True false false (#=> P) P (fsim r g Q itr_src itr_tgt os) (fsim r g Q itr_src itr_tgt os).
  Proof.
  Admitted.

  Lemma fsim_wand r g R_src R_tgt
        (Q0 Q1: R_src -> R_tgt -> list nat -> iProp)
        os itr_src itr_tgt
    :
    (fsim r g Q0 itr_src itr_tgt os)
      -∗
      (∀ r_src r_tgt os,
          ((Q0 r_src r_tgt os) -∗ #=> (Q1 r_src r_tgt os)))
      -∗
      (fsim r g Q1 itr_src itr_tgt os)
  .
  Proof.
  Admitted.

  Lemma fsim_mono r g R_src R_tgt
        (Q0 Q1: R_src -> R_tgt -> list nat -> iProp)
        (MONO: forall r_src r_tgt os,
            (Q0 r_src r_tgt os)
              -∗
              (#=> (Q1 r_src r_tgt os)))
        os itr_src itr_tgt
    :
    (fsim r g Q0 itr_src itr_tgt os)
      -∗
      (fsim r g Q1 itr_src itr_tgt os)
  .
  Proof.
  Admitted.

  Lemma fsim_frame r g R_src R_tgt
        P (Q: R_src -> R_tgt -> list nat -> iProp)
        os itr_src itr_tgt
    :
    (fsim r g Q itr_src itr_tgt os)
      -∗
      P
      -∗
      (fsim r g (fun r_src r_tgt os => P ** Q r_src r_tgt os) itr_src itr_tgt os)
  .
  Proof.
  Admitted.

  Lemma fsim_bind r g R_src R_tgt S_src S_tgt
        (Q: R_src -> R_tgt -> list nat -> iProp)
        (itr_src: itree srcE S_src) (itr_tgt: itree tgtE S_tgt)
        os ktr_src ktr_tgt
    :
    (fsim r g (fun s_src s_tgt => fsim r g Q (ktr_src s_src) (ktr_tgt s_tgt)) itr_src itr_tgt os)
      -∗
      (fsim r g Q (itr_src >>= ktr_src) (itr_tgt >>= ktr_tgt) os)
  .
  Proof.
  Admitted.

  Lemma fsim_ret r g R_src R_tgt
        (Q: R_src -> R_tgt -> list nat -> iProp)
        os r_src r_tgt
    :
    (Q r_src r_tgt os)
      -∗
      (fsim r g Q (Ret r_src) (Ret r_tgt) os)
  .
  Admitted.

  Lemma fsim_tauL r g R_src R_tgt
        (Q: R_src -> R_tgt -> list nat -> iProp)
        os itr_src itr_tgt
    :
    (fsim r g Q itr_src itr_tgt os)
      -∗
      (fsim r g Q (Tau itr_src) itr_tgt os)
  .
  Proof.
  Admitted.

  Lemma fsim_tauR r g R_src R_tgt
        (Q: R_src -> R_tgt -> list nat -> iProp)
        os itr_src itr_tgt
    :
    (fsim r g Q itr_src itr_tgt os)
      -∗
      (fsim r g Q itr_src (Tau itr_tgt) os)
  .
  Proof.
  Admitted.

  Lemma fsim_chooseL X r g R_src R_tgt
        (Q: R_src -> R_tgt -> list nat -> iProp)
        os ktr_src itr_tgt
    :
    (∃ x, fsim r g Q (ktr_src x) itr_tgt os)
      -∗
      (fsim r g Q (trigger (Choose X) >>= ktr_src) itr_tgt os)
  .
  Proof.
  Admitted.

  Lemma fsim_chooseR X r g R_src R_tgt
        (Q: R_src -> R_tgt -> list nat -> iProp)
        os itr_src ktr_tgt
    :
    (∀ x, fsim r g Q itr_src (ktr_tgt x) os)
      -∗
      (fsim r g Q itr_src (trigger (Choose X) >>= ktr_tgt) os)
  .
  Proof.
  Admitted.

  Lemma fsim_putL st r g R_src R_tgt
        (Q: R_src -> R_tgt -> list nat -> iProp)
        os ktr_src itr_tgt st_src
    :
    (St_src st_src)
      -∗
      (St_src st -∗ fsim r g Q (ktr_src tt) itr_tgt os)
      -∗
      (fsim r g Q (trigger (Put st) >>= ktr_src) itr_tgt os)
  .
  Proof.
  Admitted.

  Lemma fsim_putR st r g R_src R_tgt
        (Q: R_src -> R_tgt -> list nat -> iProp)
        os itr_src ktr_tgt st_tgt
    :
    (St_tgt st_tgt)
      -∗
      (St_tgt st -∗ fsim r g Q itr_src (ktr_tgt tt) os)
      -∗
      (fsim r g Q itr_src (trigger (Put st) >>= ktr_tgt) os)
  .
  Proof.
  Admitted.

  Lemma fsim_getL st r g R_src R_tgt
        (Q: R_src -> R_tgt -> list nat -> iProp)
        os ktr_src itr_tgt
    :
    (St_src st ∧ fsim r g Q (ktr_src st) itr_tgt os)
      -∗
      (fsim r g Q (trigger (@Get _) >>= ktr_src) itr_tgt os)
  .
  Proof.
  Admitted.

  Lemma fsim_getR st r g R_src R_tgt
        (Q: R_src -> R_tgt -> list nat -> iProp)
        os itr_src ktr_tgt
    :
    (St_tgt st  ∧ fsim r g Q itr_src (ktr_tgt st) os)
      -∗
      (fsim r g Q itr_src (trigger (@Get _) >>= ktr_tgt) os)
  .
  Proof.
  Admitted.

  Lemma fsim_tidL r g R_src R_tgt
        (Q: R_src -> R_tgt -> list nat -> iProp)
        os ktr_src itr_tgt
    :
    (fsim r g Q (ktr_src tid) itr_tgt os)
      -∗
      (fsim r g Q (trigger GetTid >>= ktr_src) itr_tgt os)
  .
  Proof.
  Admitted.

  Lemma fsim_tidR r g R_src R_tgt
        (Q: R_src -> R_tgt -> list nat -> iProp)
        os itr_src ktr_tgt
    :
    (fsim r g Q itr_src (ktr_tgt tid) os)
      -∗
      (fsim r g Q itr_src (trigger GetTid >>= ktr_tgt) os)
  .
  Proof.
  Admitted.

  Lemma fsim_UB r g R_src R_tgt
        (Q: R_src -> R_tgt -> list nat -> iProp)
        os ktr_src itr_tgt
    :
    ⊢ (fsim r g Q (trigger Undefined >>= ktr_src) itr_tgt os)
  .
  Proof.
  Admitted.

  Lemma fsim_observe fn args r g R_src R_tgt
        (Q: R_src -> R_tgt -> list nat -> iProp)
        os ktr_src ktr_tgt
    :
    (∀ ret, fsim g g Q (ktr_src ret) (ktr_tgt ret) os)
      -∗
      (fsim r g Q (trigger (Observe fn args) >>= ktr_src) (trigger (Observe fn args) >>= ktr_tgt) os)
  .
  Proof.
  Admitted.

  Lemma fsim_yieldL r g R_src R_tgt
        (Q: R_src -> R_tgt -> list nat -> iProp)
        os ktr_src ktr_tgt
    :
    (fsim r g Q (ktr_src tt) (trigger (Yield) >>= ktr_tgt) os)
      -∗
      (fsim r g Q (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt) os)
  .
  Proof.
  Admitted.

  Lemma fsim_alloc_obligation n
        r g R_src R_tgt
        (Q: R_src -> R_tgt -> list nat -> iProp)
        os itr_src itr_tgt
    :
    (∀ k, Ongoing k -* Neg k n -* (□ Pos k n) -* fsim r g Q itr_src itr_tgt (k::os))
      -∗
      (fsim r g Q itr_src itr_tgt os)
  .
  Proof.
  Admitted.

  Lemma fsim_dealloc_obligation os1
        r g R_src R_tgt
        (Q: R_src -> R_tgt -> list nat -> iProp)
        k os0 itr_src itr_tgt
        (DEALLOC: Permutation (k::os1) os0)
    :
    (Ongoing k)
      -∗
      (□ Done k -* fsim r g Q itr_src itr_tgt os1)
      -∗
      (fsim r g Q itr_src itr_tgt os0)
  .
  Proof.
  Admitted.

  Lemma fsim_obligation_not_done
        r g R_src R_tgt
        (Q: R_src -> R_tgt -> list nat -> iProp)
        k os itr_src itr_tgt
        (IN: List.In k os)
    :
    (Done k)
      -∗
      (fsim r g Q itr_src itr_tgt os)
  .
  Proof.
  Admitted.

  Definition optPos (k: option nat): iProp :=
    match k with
    | Some k => PosEx k
    | None => True
    end.

  Definition optNeg (k: option nat): iProp :=
    match k with
    | Some k => Neg k (Ord.from_nat 1) ∨ Done k
    | None => True
    end.

  Fixpoint recharging (os: list nat): iProp :=
    match os with
    | [] => True
    | k::os => Neg k Ord.omega ** recharging os
    end.

  Lemma fsim_yieldR k r g R_src R_tgt
        (Q: R_src -> R_tgt -> list nat -> iProp)
        os ktr_src ktr_tgt
    :
    (I ** optPos k ** recharging os ** (I -∗ optNeg k -* fsim r g Q (trigger (Yield) >>= ktr_src) (ktr_tgt tt) os))
      -∗
      (fsim r g Q (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt) os)
  .
  Proof.
  Admitted.

  Lemma fsim_sync k r g R_src R_tgt
        (Q: R_src -> R_tgt -> list nat -> iProp)
        os ktr_src ktr_tgt
    :
    (I ** optPos k ** recharging os ** (I -∗ optNeg k -* fsim g g Q (ktr_src tt) (ktr_tgt tt) os))
      -∗
      (fsim r g Q (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt) os).
  Proof.
  Admitted.

  Context `{SRCORD: @GRA.inG (@FairRA.t ident_src Ord.t _) Σ}.
  Context `{TGTORD: @GRA.inG (@FairRA.t ident_tgt nat _) Σ}.

  Lemma fsim_fairL o f r g R_src R_tgt
        (Q: R_src -> R_tgt -> list nat -> iProp)
        os ktr_src itr_tgt
    :
    (Infsum (fun i: sig (fun i => f i = Flag.fail) => FairRA.white (proj1_sig i) (Ord.from_nat 1)))
      -∗
      ((Infsum (fun i: sig (fun i => f i = Flag.success) => FairRA.white (proj1_sig i) o)) -* (fsim r g Q (ktr_src tt) itr_tgt os))
      -∗
      (fsim r g Q (trigger (Fair f) >>= ktr_src) itr_tgt os).
  Proof.
  Admitted.

  Lemma fsim_fairR f r g R_src R_tgt
        (Q: R_src -> R_tgt -> list nat -> iProp)
        os itr_src ktr_tgt
    :
    (Infsum (fun i: sig (fun i => f i = Flag.success) => (∃ a, FairRA.black (proj1_sig i) a)%I))
      -∗
      ((Infsum (fun i: sig (fun i => f i = Flag.fail) => FairRA.white (proj1_sig i) 1)) -* (fsim r g Q itr_src (ktr_tgt tt) os))
      -∗
      (fsim r g Q itr_src (trigger (Fair f) >>= ktr_tgt) os).
  Proof.
  Admitted.
End FAIR.

From Fairness Require Export Red IRed.

Ltac lred := repeat (prw _red_gen 1 3 0).
Ltac rred := repeat (prw _red_gen 1 2 0).
