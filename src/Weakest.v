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

From Fairness Require Export NatMapRA StateRA FairRA MonotonePCM.
Require Import Coq.Sorting.Mergesort.

Section STATE.
  Context `{Σ: GRA.t}.

  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable ident_src: ID.
  Variable ident_tgt: ID.

  Let srcE := ((@eventE ident_src +' cE) +' sE state_src).
  Let tgtE := ((@eventE ident_tgt +' cE) +' sE state_tgt).

  Let shared_rel := TIdSet.t -> (@imap ident_src owf) -> (@imap (sum_tid ident_tgt) nat_wf) -> state_src -> state_tgt -> iProp.

  Variable Invs: list iProp.

  Let topset: mset := List.seq 0 (List.length Invs).

  Context `{MONORA: @GRA.inG monoRA Σ}.
  Context `{THDRA: @GRA.inG ThreadRA Σ}.
  Context `{STATESRC: @GRA.inG (stateSrcRA state_src) Σ}.
  Context `{STATETGT: @GRA.inG (stateTgtRA state_tgt) Σ}.
  Context `{IDENTSRC: @GRA.inG (identSrcRA ident_src) Σ}.
  Context `{IDENTTGT: @GRA.inG (identTgtRA ident_tgt) Σ}.
  Context `{OBLGRA: @GRA.inG ObligationRA.t Σ}.
  Context `{ARROWRA: @GRA.inG (ArrowRA ident_tgt) Σ}.
  Context `{EDGERA: @GRA.inG EdgeRA Σ}.
  Context `{ONESHOTRA: @GRA.inG (@FiniteMap.t (OneShot.t unit)) Σ}.

  Let I: shared_rel :=
        fun ths im_src im_tgt st_src st_tgt =>
          default_I ths im_src im_tgt st_src st_tgt ** mset_all (nth_default True%I Invs) topset.

  Let rel := (forall R_src R_tgt (Q: R_src -> R_tgt -> iProp), itree srcE R_src -> itree tgtE R_tgt -> iProp).

  Variable tid: thread_id.

  Let unlift_rel
      (r: forall R_src R_tgt (Q: R_src -> R_tgt -> shared_rel), itree srcE R_src -> itree tgtE R_tgt -> shared_rel): rel :=
        fun R_src R_tgt Q itr_src itr_tgt =>
          (∀ ths im_src im_tgt st_src st_tgt,
              (default_I ths im_src im_tgt st_src st_tgt ** mset_all (nth_default True%I Invs) topset)
                -*
                (@r R_src R_tgt (fun r_src r_tgt ths im_src im_tgt st_src st_tgt => (default_I ths im_src im_tgt st_src st_tgt ** mset_all (nth_default True%I Invs) topset) ** Q r_src r_tgt) itr_src itr_tgt ths im_src im_tgt st_src st_tgt))%I.

  Let lift_rel (rr: rel):
    forall R_src R_tgt (QQ: R_src -> R_tgt -> shared_rel), itree srcE R_src -> itree tgtE R_tgt -> shared_rel :=
        fun R_src R_tgt QQ itr_src itr_tgt ths im_src im_tgt st_src st_tgt =>
          (∃ (Q: R_src -> R_tgt -> iProp)
             (EQ: QQ = (fun r_src r_tgt ths im_src im_tgt st_src st_tgt =>
                          (default_I ths im_src im_tgt st_src st_tgt ** mset_all (nth_default True%I Invs) topset) ** Q r_src r_tgt)),
              rr R_src R_tgt Q itr_src itr_tgt ** (default_I ths im_src im_tgt st_src st_tgt ** mset_all (nth_default True%I Invs) topset))%I.

  Let unlift_rel_base r
    :
    forall R_src R_tgt Q itr_src itr_tgt ths im_src im_tgt st_src st_tgt,
      (r R_src R_tgt Q itr_src itr_tgt)
        -∗
        (default_I ths im_src im_tgt st_src st_tgt ** mset_all (nth_default True%I Invs) topset)
        -∗
        (lift_rel
           r
           (fun r_src r_tgt ths im_src im_tgt st_src st_tgt => (default_I ths im_src im_tgt st_src st_tgt ** mset_all (nth_default True%I Invs) topset) ** Q r_src r_tgt)
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

  Definition stsim (E: mset): rel -> rel -> rel :=
    fun r g
        R_src R_tgt Q itr_src itr_tgt =>
      (∀ ths im_src im_tgt st_src st_tgt,
          (default_I ths im_src im_tgt st_src st_tgt ** mset_all (nth_default True%I Invs) E)
            -*
            (isim
               tid
               I
               (lift_rel r)
               (lift_rel g)
               (fun r_src r_tgt ths im_src im_tgt st_src st_tgt => (default_I ths im_src im_tgt st_src st_tgt ** mset_all (nth_default True%I Invs) topset) ** Q r_src r_tgt)
               itr_src itr_tgt
               ths im_src im_tgt st_src st_tgt))%I
  .

  Record mytype
         (A: Type) :=
    mk_mytype {
        comp_a: A;
        comp_ths: TIdSet.t;
        comp_im_src: imap ident_src owf;
        comp_im_tgt: imap (sum_tid ident_tgt) nat_wf;
        comp_st_src: state_src;
        comp_st_tgt: state_tgt;
      }.





  Lemma stsim_discard E1 E0 r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        itr_src itr_tgt
        (TOP: mset_sub E0 E1)
    :
    (stsim E0 r g Q itr_src itr_tgt)
      -∗
      (stsim E1 r g Q itr_src itr_tgt)
  .
  Proof.
    unfold stsim. iIntros "H" (? ? ? ? ?) "[D I]".
    iPoseProof (mset_all_sub with "I") as "[I RESTORE]"; [eauto|].
    iPoseProof ("H" with "[D I]") as "H".
    { iFrame. }
    iApply isim_wand. iFrame.
    iIntros (? ? ? ? ? ? ?) "[[D I] Q]".
    iModIntro. iFrame.
  Qed.

  Lemma stsim_base E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        itr_src itr_tgt
        (TOP: mset_sub topset E)
    :
    (@r _ _ Q itr_src itr_tgt)
      -∗
      (stsim E r g Q itr_src itr_tgt)
  .
  Proof.
    rewrite <- stsim_discard; [|eassumption].
    unfold stsim. iIntros "H" (? ? ? ? ?) "D".
    iApply isim_base.
    iApply (unlift_rel_base with "H D").
  Qed.

  Lemma stsim_mono_knowledge E (r0 g0 r1 g1: rel) R_src R_tgt
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
      (stsim E r0 g0 Q itr_src itr_tgt)
      (stsim E r1 g1 Q itr_src itr_tgt)
  .
  Proof.
    unfold stsim. iIntros "H" (? ? ? ? ?) "D".
    iApply isim_mono_knowledge.
    { eapply lift_rel_mon. eauto. }
    { eapply lift_rel_mon. eauto. }
    iApply ("H" with "D").
  Qed.

  Lemma stsim_coind E A
        (R_src: forall (a: A), Prop)
        (R_tgt: forall (a: A), Prop)
        (Q: forall (a: A), R_src a -> R_tgt a -> iProp)
        (itr_src : forall (a: A), itree srcE (R_src a))
        (itr_tgt : forall (a: A), itree tgtE (R_tgt a))
        (P: forall (a: A), iProp)
        (r g0: rel)
        (TOP: mset_sub topset E)
        (COIND: forall (g1: rel) a,
            (□((∀ R_src R_tgt (Q: R_src -> R_tgt -> iProp)
                  itr_src itr_tgt,
                   @g0 R_src R_tgt Q itr_src itr_tgt -* @g1 R_src R_tgt Q itr_src itr_tgt)
                 **
                 (∀ a, P a -* @g1 (R_src a) (R_tgt a) (Q a) (itr_src a) (itr_tgt a))))
              -∗
              (P a)
              -∗
              (stsim topset r g1 (Q a) (itr_src a) (itr_tgt a)))
    :
    (forall a, bi_entails (P a) (stsim E r g0 (Q a) (itr_src a) (itr_tgt a))).
  Proof.
    cut (forall (m: mytype A),
            bi_entails
              ((fun m => P m.(comp_a) ** (default_I m.(comp_ths) m.(comp_im_src) m.(comp_im_tgt) m.(comp_st_src) m.(comp_st_tgt) ** mset_all (nth_default True%I Invs) topset)) m)
              (isim tid I (lift_rel r) (lift_rel g0) ((fun m => fun r_src r_tgt ths im_src im_tgt st_src st_tgt => (default_I ths im_src im_tgt st_src st_tgt ** mset_all (nth_default True%I Invs) topset) ** Q m.(comp_a) r_src r_tgt) m)
                    ((fun m => itr_src m.(comp_a)) m) ((fun m => itr_tgt m.(comp_a)) m) (comp_ths m) (comp_im_src m) (comp_im_tgt m) (comp_st_src m) (comp_st_tgt m))).
    { ss. i. rewrite <- stsim_discard; [|eassumption].
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

  Lemma stsim_upd E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        itr_src itr_tgt
    :
    (#=> (stsim E r g Q itr_src itr_tgt))
      -∗
      (stsim E r g Q itr_src itr_tgt)
  .
  Proof.
    unfold stsim. iIntros "H" (? ? ? ? ?) "D". iMod "H".
    iApply "H". auto.
  Qed.

  Global Instance stsim_elim_upd
         E r g R_src R_tgt
         (Q: R_src -> R_tgt -> iProp)
         itr_src itr_tgt
         P
    :
    ElimModal True false false (#=> P) P (stsim E r g Q itr_src itr_tgt) (stsim E r g Q itr_src itr_tgt).
  Proof.
    typeclasses eauto.
  Qed.

  Lemma stsim_mupd E0 E1 r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        itr_src itr_tgt
    :
    (MUpd (nth_default True%I Invs) E0 E1 (stsim E1 r g Q itr_src itr_tgt))
      -∗
      (stsim E0 r g Q itr_src itr_tgt)
  .
  Proof.
    unfold stsim. iIntros "H" (? ? ? ? ?) "[D C]".
    iMod ("H" with "C") as "[C H]".
    iApply "H". iFrame.
  Qed.

  Lemma stsim_mupd_weaken E0 E1 r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        itr_src itr_tgt
        (SUB: mset_sub E0 E1)
    :
    (MUpd (nth_default True%I Invs) E0 E0 (stsim E1 r g Q itr_src itr_tgt))
      -∗
      (stsim E1 r g Q itr_src itr_tgt)
  .
  Proof.
    iIntros "H". iApply stsim_mupd. iApply MUpd_mask_mono; eauto.
  Qed.

  Global Instance stsim_elim_mupd_gen
         E0 E1 E2 r g R_src R_tgt
         (Q: R_src -> R_tgt -> iProp)
         itr_src itr_tgt
         P
    :
    ElimModal (mset_sub E0 E2) false false (MUpd (nth_default True%I Invs) E0 E1 P) P (stsim E2 r g Q itr_src itr_tgt) (stsim (NatSort.sort (E1 ++ mset_minus E2 E0)) r g Q itr_src itr_tgt).
  Proof.
    unfold ElimModal. i. iIntros "[H0 H1]".
    iPoseProof (MUpd_mask_frame_r with "H0") as "H0".
    iPoseProof (MUpd_permutation with "H0") as "H0".
    { eapply mset_minus_add_eq; eauto. }
    { reflexivity. }
    iApply stsim_mupd. iMod "H0".
    iPoseProof ("H1" with "H0") as "H".
    iModIntro. iApply (stsim_discard with "H").
    rewrite <- NatSort.Permuted_sort. reflexivity.
  Qed.

  Global Instance stsim_elim_mupd_eq
         E1 E2 r g R_src R_tgt
         (Q: R_src -> R_tgt -> iProp)
         itr_src itr_tgt
         P
    :
    ElimModal (mset_sub E1 E2) false false (MUpd (nth_default True%I Invs) E1 E1 P) P (stsim E2 r g Q itr_src itr_tgt) (stsim E2 r g Q itr_src itr_tgt).
  Proof.
    unfold ElimModal. i. iIntros "[H0 H1]".
    iApply stsim_mupd_weaken.
    { eauto. }
    iMod "H0". iModIntro. iApply ("H1" with "H0").
  Qed.

  Global Instance stsim_elim_mupd
         E1 E2 r g R_src R_tgt
         (Q: R_src -> R_tgt -> iProp)
         itr_src itr_tgt
         P
    :
    ElimModal True false false (MUpd (nth_default True%I Invs) E1 E2 P) P (stsim E1 r g Q itr_src itr_tgt) (stsim E2 r g Q itr_src itr_tgt).
  Proof.
    unfold ElimModal. i. iIntros "[H0 H1]".
    iApply stsim_mupd. iMod "H0".
    iModIntro. iApply ("H1" with "H0").
  Qed.

  Global Instance stsim_add_modal_mupd
         E r g R_src R_tgt
         (Q: R_src -> R_tgt -> iProp)
         itr_src itr_tgt
         P
    :
    AddModal (MUpd (nth_default True%I Invs) E E P) P (stsim E r g Q itr_src itr_tgt).
  Proof.
    unfold AddModal. iIntros "[> H0 H1]". iApply ("H1" with "H0").
  Qed.

  Global Instance stsim_elim_iupd_edge
         E r g R_src R_tgt
         (Q: R_src -> R_tgt -> iProp)
         itr_src itr_tgt
         P
    :
    ElimModal True false false (#=(ObligationRA.edges_sat)=> P) P (stsim E r g Q itr_src itr_tgt) (stsim E r g Q itr_src itr_tgt).
  Proof.
    unfold ElimModal. i. iIntros "[H0 H1]" (? ? ? ? ?) "[D C]".
    iPoseProof (IUpd_sub_mon with "[] H0 D") as "> [D P]"; auto.
    { iApply edges_sat_sub. }
    iApply ("H1" with "P"). iFrame.
  Qed.

  Global Instance stsim_elim_iupd_arrow
         E r g R_src R_tgt
         (Q: R_src -> R_tgt -> iProp)
         itr_src itr_tgt
         P
    :
    ElimModal True false false (#=(ObligationRA.arrows_sat (Id:=sum_tid ident_tgt))=> P) P (stsim E r g Q itr_src itr_tgt) (stsim E r g Q itr_src itr_tgt).
  Proof.
    unfold ElimModal. i. iIntros "[H0 H1]" (? ? ? ? ?) "[D C]".
    iPoseProof (IUpd_sub_mon with "[] H0 D") as "> [D P]"; auto.
    { iApply arrows_sat_sub. }
    iApply ("H1" with "P"). iFrame.
  Qed.

  Lemma stsim_wand E r g R_src R_tgt
        (Q0 Q1: R_src -> R_tgt -> iProp)
        itr_src itr_tgt
    :
    (stsim E r g Q0 itr_src itr_tgt)
      -∗
      (∀ r_src r_tgt,
          ((Q0 r_src r_tgt) -∗ #=> (Q1 r_src r_tgt)))
      -∗
      (stsim E r g Q1 itr_src itr_tgt)
  .
  Proof.
    unfold stsim. iIntros "H0 H1" (? ? ? ? ?) "D".
    iApply isim_wand.
    iPoseProof ("H0" $! _ _ _ _ _ with "D") as "H0".
    iSplitR "H0"; [|auto]. iIntros (? ? ? ? ? ? ?) "[D H0]".
    iPoseProof ("H1" $! _ _ with "H0") as "> H0". iModIntro. iFrame.
  Qed.

  Lemma stsim_mono E r g R_src R_tgt
        (Q0 Q1: R_src -> R_tgt -> iProp)
        (MONO: forall r_src r_tgt,
            (Q0 r_src r_tgt)
              -∗
              (#=> (Q1 r_src r_tgt)))
        itr_src itr_tgt
    :
    (stsim E r g Q0 itr_src itr_tgt)
      -∗
      (stsim E r g Q1 itr_src itr_tgt)
  .
  Proof.
    iIntros "H". iApply (stsim_wand with "H").
    iIntros. iApply MONO. auto.
  Qed.

  Lemma stsim_frame E r g R_src R_tgt
        P (Q: R_src -> R_tgt -> iProp)
        itr_src itr_tgt
    :
    (stsim E r g Q itr_src itr_tgt)
      -∗
      P
      -∗
      (stsim E r g (fun r_src r_tgt => P ** Q r_src r_tgt) itr_src itr_tgt)
  .
  Proof.
    iIntros "H0 H1". iApply (stsim_wand with "H0").
    iIntros. iModIntro. iFrame.
  Qed.

  Lemma stsim_bind_top E r g R_src R_tgt S_src S_tgt
        (Q: R_src -> R_tgt -> iProp)
        (itr_src: itree srcE S_src) (itr_tgt: itree tgtE S_tgt)
        ktr_src ktr_tgt
    :
    (stsim E r g (fun s_src s_tgt => stsim topset r g Q (ktr_src s_src) (ktr_tgt s_tgt)) itr_src itr_tgt)
      -∗
      (stsim E r g Q (itr_src >>= ktr_src) (itr_tgt >>= ktr_tgt))
  .
  Proof.
    unfold stsim. iIntros "H" (? ? ? ? ?) "D".
    iPoseProof ("H" $! _ _ _ _ _ with "D") as "H".
    iApply isim_bind. iApply (isim_mono with "H").
    iIntros (? ? ? ? ? ? ?) "[[D I] H]".
    iApply ("H" $! _ _ _ _ _ with "[D I]"). iFrame.
  Qed.

  Lemma stsim_ret E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        r_src r_tgt
    :
    (MUpd (nth_default True%I Invs) E topset (Q r_src r_tgt))
      -∗
      (stsim E r g Q (Ret r_src) (Ret r_tgt))
  .
  Proof.
    iIntros "> H".
    unfold stsim. iIntros (? ? ? ? ?) "D".
    iApply isim_ret. iFrame.
  Qed.

  Lemma stsim_tauL E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        itr_src itr_tgt
    :
    (stsim E r g Q itr_src itr_tgt)
      -∗
      (stsim E r g Q (Tau itr_src) itr_tgt)
  .
  Proof.
    unfold stsim. iIntros "H" (? ? ? ? ?) "D".
    iPoseProof ("H" $! _ _ _ _ _ with "D") as "H".
    iApply isim_tauL. iFrame.
  Qed.

  Lemma stsim_tauR E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        itr_src itr_tgt
    :
    (stsim E r g Q itr_src itr_tgt)
      -∗
      (stsim E r g Q itr_src (Tau itr_tgt))
  .
  Proof.
    unfold stsim. iIntros "H" (? ? ? ? ?) "D".
    iPoseProof ("H" $! _ _ _ _ _ with "D") as "H".
    iApply isim_tauR. iFrame.
  Qed.

  Lemma stsim_chooseL E X r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ktr_src itr_tgt
    :
    (∃ x, stsim E r g Q (ktr_src x) itr_tgt)
      -∗
      (stsim E r g Q (trigger (Choose X) >>= ktr_src) itr_tgt)
  .
  Proof.
    unfold stsim. iIntros "[% H]" (? ? ? ? ?) "D".
    iPoseProof ("H" $! _ _ _ _ _ with "D") as "H".
    iApply isim_chooseL. iExists _. iFrame.
  Qed.

  Lemma stsim_chooseR E X r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        itr_src ktr_tgt
    :
    (∀ x, stsim E r g Q itr_src (ktr_tgt x))
      -∗
      (stsim E r g Q itr_src (trigger (Choose X) >>= ktr_tgt))
  .
  Proof.
    unfold stsim. iIntros "H" (? ? ? ? ?) "D".
    iApply isim_chooseR. iIntros (?).
    iPoseProof ("H" $! _ _ _ _ _ _ with "D") as "H". iFrame.
  Qed.

  Lemma stsim_putL E st r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ktr_src itr_tgt st_src
    :
    (OwnM (Auth.white (Excl.just st_src: @Excl.t state_src): stateSrcRA state_src))
      -∗
      ((OwnM (Auth.white (Excl.just st: @Excl.t state_src): stateSrcRA state_src))
         -∗ (stsim E r g Q (ktr_src tt) itr_tgt))
      -∗
      (stsim E r g Q (trigger (Put st) >>= ktr_src) itr_tgt)
  .
  Proof.
    unfold stsim. iIntros "H0 H1" (? ? ? ? ?) "[D C]".
    iPoseProof (default_I_update_st_src with "D H0") as "> [D H0]".
    iApply isim_putL. iApply ("H1" with "D [H0 C]"). iFrame.
  Qed.

  Lemma stsim_putR E st r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        itr_src ktr_tgt st_tgt
    :
    (OwnM (Auth.white (Excl.just st_tgt: @Excl.t state_tgt): stateSrcRA state_tgt))
      -∗
      ((OwnM (Auth.white (Excl.just st: @Excl.t state_tgt): stateSrcRA state_tgt))
         -∗ (stsim E r g Q itr_src (ktr_tgt tt)))
      -∗
      (stsim E r g Q itr_src (trigger (Put st) >>= ktr_tgt))
  .
  Proof.
    unfold stsim. iIntros "H0 H1" (? ? ? ? ?) "[D C]".
    iPoseProof (default_I_update_st_tgt with "D H0") as "> [D H0]".
    iApply isim_putR. iApply ("H1" with "D [H0 C]"). iFrame.
  Qed.

  Lemma stsim_getL E st r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ktr_src itr_tgt
    :
    ((OwnM (Auth.white (Excl.just st: @Excl.t state_src): stateSrcRA state_src)) ∧
       (stsim E r g Q (ktr_src st) itr_tgt))
      -∗
      (stsim E r g Q (trigger (@Get _) >>= ktr_src) itr_tgt)
  .
  Proof.
    unfold stsim. iIntros "H" (? ? ? ? ?) "[D C]". iApply isim_getL.
    iAssert (⌜st_src = st⌝)%I as "%".
    { iDestruct "H" as "[H _]". iApply (default_I_get_st_src with "D"); eauto. }
    subst. iDestruct "H" as "[_ H]". iApply ("H" with "[D C]"). iFrame.
  Qed.

  Lemma stsim_getR E st r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        itr_src ktr_tgt
    :
    ((OwnM (Auth.white (Excl.just st: @Excl.t state_tgt): stateTgtRA state_tgt)) ∧
       (stsim E r g Q itr_src (ktr_tgt st)))
      -∗
      (stsim E r g Q itr_src (trigger (@Get _) >>= ktr_tgt))
  .
  Proof.
    unfold stsim. iIntros "H" (? ? ? ? ?) "[D C]". iApply isim_getR.
    iAssert (⌜st_tgt = st⌝)%I as "%".
    { iDestruct "H" as "[H _]". iApply (default_I_get_st_tgt with "D"); eauto. }
    subst. iDestruct "H" as "[_ H]". iApply ("H" with "[D C]"). iFrame.
  Qed.

  Lemma stsim_tidL E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ktr_src itr_tgt
    :
    (stsim E r g Q (ktr_src tid) itr_tgt)
      -∗
      (stsim E r g Q (trigger GetTid >>= ktr_src) itr_tgt)
  .
  Proof.
    unfold stsim. iIntros "H" (? ? ? ? ?) "D".
    iApply isim_tidL. iApply ("H" with "D").
  Qed.

  Lemma stsim_tidR E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        itr_src ktr_tgt
    :
    (stsim E r g Q itr_src (ktr_tgt tid))
      -∗
      (stsim E r g Q itr_src (trigger GetTid >>= ktr_tgt))
  .
  Proof.
    unfold stsim. iIntros "H" (? ? ? ? ?) "D".
    iApply isim_tidR. iApply ("H" with "D").
  Qed.

  Lemma stsim_fairL o lf ls
        E fm r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ktr_src itr_tgt
        (FAIL: forall i (IN: fm i = Flag.fail), List.In i lf)
        (SUCCESS: forall i (IN: List.In i ls), fm i = Flag.success)
    :
    (list_prop_sum (fun i => FairRA.white i Ord.one) lf)
      -∗
      ((list_prop_sum (fun i => FairRA.white i o) ls) -∗ (stsim E r g Q (ktr_src tt) itr_tgt))
      -∗
      (stsim E r g Q (trigger (Fair fm) >>= ktr_src) itr_tgt).
  Proof.
    unfold stsim. iIntros "OWN H" (? ? ? ? ?) "[D C]".
    iPoseProof (default_I_update_ident_source with "D OWN") as "> [% [[% WHITES] D]]".
    { eauto. }
    { eauto. }
    iPoseProof ("H" with "WHITES [D C]") as "H".
    { iFrame. }
    iApply isim_fairL. iExists _. iSplit; eauto.
  Qed.

  Lemma stsim_fairR lf ls
        E fm r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        itr_src ktr_tgt
        (SUCCESS: forall i (IN: fm i = Flag.success), List.In i (List.map fst ls))
        (FAIL: forall i (IN: List.In i lf), fm i = Flag.fail)
        (NODUP: List.NoDup lf)
    :
    (list_prop_sum (fun '(i, l) => ObligationRA.duty (inr i) l ** ObligationRA.tax l) ls)
      -∗
      ((list_prop_sum (fun '(i, l) => ObligationRA.duty (inr i) l) ls)
         -*
         (list_prop_sum (fun i => FairRA.white (Id:=_) (inr i) 1) lf)
         -*
         stsim E r g Q itr_src (ktr_tgt tt))
      -∗
      (stsim E r g Q itr_src (trigger (Fair fm) >>= ktr_tgt))
  .
  Proof.
    unfold stsim. iIntros "OWN H"  (? ? ? ? ?) "[D C]".
    iApply isim_fairR. iIntros (?) "%".
    iPoseProof (default_I_update_ident_target with "D OWN") as "> [[DUTY WHITE] D]".    { eauto. }
    { eauto. }
    { eauto. }
    { eauto. }
    iApply ("H" with "DUTY WHITE"). iFrame.
  Qed.

  Lemma stsim_UB E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ktr_src itr_tgt
    :
    ⊢ (stsim E r g Q (trigger Undefined >>= ktr_src) itr_tgt)
  .
  Proof.
    unfold stsim. iIntros (? ? ? ? ?) "D".
    iApply isim_UB. auto.
  Qed.

  Lemma stsim_observe E fn args r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ktr_src ktr_tgt
    :
    (∀ ret, stsim E g g Q (ktr_src ret) (ktr_tgt ret))
      -∗
      (stsim E r g Q (trigger (Observe fn args) >>= ktr_src) (trigger (Observe fn args) >>= ktr_tgt))
  .
  Proof.
    unfold stsim. iIntros "H" (? ? ? ? ?) "D".
    iApply isim_observe. iIntros (?). iApply ("H" with "D").
  Qed.

  Lemma stsim_yieldL E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ktr_src ktr_tgt
    :
    (stsim E r g Q (ktr_src tt) (trigger (Yield) >>= ktr_tgt))
      -∗
      (stsim E r g Q (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt))
  .
  Proof.
    unfold stsim. iIntros "H" (? ? ? ? ?) "D".
    iApply isim_yieldL. iApply ("H" with "D").
  Qed.

  Lemma stsim_yieldR E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ktr_src ktr_tgt l
        (TOP: mset_sub topset E)
    :
    (ObligationRA.duty (inl tid) l ** ObligationRA.tax l)
      -∗
      ((ObligationRA.duty (inl tid) l)
         -*
         (FairRA.white_thread (_Id:=_))
         -*
         stsim topset r g Q (trigger (Yield) >>= ktr_src) (ktr_tgt tt))
      -∗
      (stsim E r g Q (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt))
  .
  Proof.
    iIntros "H K". iApply stsim_discard; [eassumption|].
    unfold stsim. iIntros (? ? ? ? ?) "[D C]".
    iApply isim_yieldR. unfold I. iFrame.
    iIntros (? ? ? ? ? ?) "[D C] %".
    iPoseProof (default_I_update_ident_thread with "D H") as "> [[DUTY WHITE] D]".
    { eauto. }
    iApply ("K" with "DUTY WHITE"). iFrame.
  Qed.

  Lemma stsim_sync E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ktr_src ktr_tgt l
        (TOP: mset_sub topset E)
    :
    (ObligationRA.duty (inl tid) l ** ObligationRA.tax l)
      -∗
      ((ObligationRA.duty (inl tid) l)
         -*
         (FairRA.white_thread (_Id:=_))
         -*
         stsim topset g g Q (ktr_src tt) (ktr_tgt tt))
      -∗
      (stsim E r g Q (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt)).
  Proof.
    iIntros "H K". iApply stsim_discard; [eassumption|].
    unfold stsim. iIntros (? ? ? ? ?) "[D C]".
    iApply isim_sync. unfold I. iFrame.
    iIntros (? ? ? ? ? ?) "[D C] %".
    iPoseProof (default_I_update_ident_thread with "D H") as "> [[DUTY WHITE] D]".
    { eauto. }
    iApply ("K" with "DUTY WHITE"). iFrame.
  Qed.

  Lemma stsim_sort E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        itr_src itr_tgt
    :
    (stsim (NatSort.sort E) r g Q itr_src itr_tgt)
      -∗
      (stsim E r g Q itr_src itr_tgt)
  .
  Proof.
    iApply stsim_discard.
    rewrite <- NatSort.Permuted_sort. reflexivity.
  Qed.
End STATE.

From Fairness Require Export Red IRed.

Ltac lred := repeat (prw _red_gen 1 3 0).
Ltac rred := repeat (prw _red_gen 1 2 0).
