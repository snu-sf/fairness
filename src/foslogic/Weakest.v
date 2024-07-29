From sflib Require Import sflib.
From Paco Require Import paco.
From stdpp Require Import coPset gmap namespaces.
From Fairness Require Import ITreeLib IPropFOS IPMFOS ModSim ModSimNat PCM.
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

  Let gf := (fun r => pind9 ((@__lsim Σ) _ _ _ _ _ _ (liftI I) tid r) top9).
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

  Lemma isim_wand r g R_src R_tgt
        (Q0 Q1: R_src -> R_tgt -> shared_rel)
        ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      ((∀ r_src r_tgt ths im_src im_tgt st_src st_tgt,
           ((Q0 r_src r_tgt ths im_src im_tgt st_src st_tgt) -∗ #=> (Q1 r_src r_tgt ths im_src im_tgt st_src st_tgt))) ** (isim r g Q0 ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt))
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
      (P ** isim r g Q ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
      (isim r g (fun r_src r_tgt ths im_src im_tgt st_src st_tgt =>
                   P ** Q r_src r_tgt ths im_src im_tgt st_src st_tgt)
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
      (∀ im_tgt1, ⌜fair_update im_tgt0 im_tgt1 (prism_fmap inrp f)⌝ -* isim r g Q ps true itr_src (ktr_tgt tt) ths im_src im_tgt1 st_src st_tgt)
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
      (I ths0 im_src0 im_tgt0 st_src0 st_tgt0 ** (∀ ths1 im_src1 im_tgt1 st_src1 st_tgt1 im_tgt2, I ths1 im_src1 im_tgt1 st_src1 st_tgt1 -* ⌜fair_update im_tgt1 im_tgt2 (prism_fmap inlp (tids_fmap tid ths1))⌝ -* isim r g Q ps true (trigger (Yield) >>= ktr_src) (ktr_tgt tt) ths1 im_src1 im_tgt2 st_src1 st_tgt1))
      (isim r g Q ps pt (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt) ths0 im_src0 im_tgt0 st_src0 st_tgt0)
  .
  Proof.
    rr. autorewrite with iprop. i.
    rr in H. autorewrite with iprop in H. des. subst.
    ii. muclo lsim_indC_spec.
    eapply lsim_yieldR; eauto.
    i. rr in H1. autorewrite with iprop in H1. specialize (H1 ths1).
    rr in H1. autorewrite with iprop in H1. specialize (H1 im_src1).
    rr in H1. autorewrite with iprop in H1. specialize (H1 im_tgt1).
    rr in H1. autorewrite with iprop in H1. specialize (H1 st_src1).
    rr in H1. autorewrite with iprop in H1. specialize (H1 st_tgt1).
    rr in H1. autorewrite with iprop in H1. specialize (H1 im_tgt2).
    rr in H1. autorewrite with iprop in H1.
    hexploit (H1 r_shared1); eauto.
    { eapply URA.wf_mon. instantiate (1:=r_ctx1). r_wf VALID.
    }
    i. rr in H. autorewrite with iprop in H. hexploit (H URA.unit); eauto.
    { eapply URA.wf_mon. instantiate (1:=r_ctx1).
      r_wf VALID.
    }
    { rr. autorewrite with iprop. eauto. }
    i. muclo lsim_resetC_spec. econs; [eapply H2|..]; eauto.
    r_wf VALID.
  Qed.

  Lemma isim_sync r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        ps pt ktr_src ktr_tgt ths0 im_src0 im_tgt0 st_src0 st_tgt0
    :
    bi_entails
      (I ths0 im_src0 im_tgt0 st_src0 st_tgt0 ** (∀ ths1 im_src1 im_tgt1 st_src1 st_tgt1 im_tgt2, I ths1 im_src1 im_tgt1 st_src1 st_tgt1 -* ⌜fair_update im_tgt1 im_tgt2 (prism_fmap inlp (tids_fmap tid ths1))⌝ -* isim g g Q true true (ktr_src tt) (ktr_tgt tt) ths1 im_src1 im_tgt2 st_src1 st_tgt1))
      (isim r g Q ps pt (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt) ths0 im_src0 im_tgt0 st_src0 st_tgt0)
  .
  Proof.
    rr. autorewrite with iprop. i.
    rr in H. autorewrite with iprop in H. des. subst.
    ii. gstep. eapply pind9_fold. eapply lsim_sync; eauto. i.
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
      r_wf VALID.
    }
    i. rr in H. autorewrite with iprop in H. hexploit (H URA.unit); eauto.
    { eapply URA.wf_mon. instantiate (1:=r_ctx1).
      r_wf VALID.
    }
    { rr. autorewrite with iprop. eauto. }
    i. muclo lsim_resetC_spec. econs; [eapply H2|..]; eauto.
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
                                                      @g0 R_src R_tgt Q ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt -* @g1 R_src R_tgt Q ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
                                                    **
                                                    (∀ a, P a -* @g1 (R_src a) (R_tgt a) (Q a) (ps a) (pt a) (itr_src a) (itr_tgt a) (ths a) (im_src a) (im_tgt a) (st_src a) (st_tgt a))) ** P a) (isim r g1 (Q a) (ps a) (pt a) (itr_src a) (itr_tgt a) (ths a) (im_src a) (im_tgt a) (st_src a) (st_tgt a)))
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

From Fairness Require Export NatMapRAFOS StateRA FairRA MonotonePCM FancyUpdate.
Require Import Coq.Sorting.Mergesort.

Section STATE.
  Context `{Σ: GRA.t}.

  Class ViewInterp {S V} (l : Lens.t S V) (SI : S -> iProp) (VI : V -> iProp) := {
      view_interp : forall s, (SI s) ⊢ (VI (Lens.view l s) ∗ ∀ x, VI x -∗ SI (Lens.set l x s))
    }.

  Definition interp_prod {A B} (SA: A -> iProp) (SB: B -> iProp):
    (A * B -> iProp) :=
    fun '(sa, sb) => SA sa ** SB sb.

  Global Program Instance ViewInterp_fstl {A B}
         (SA: A -> iProp) (SB: B -> iProp)
    : ViewInterp fstl (interp_prod SA SB) SA.
  Next Obligation.
  Proof.
    iIntros "[H0 H1]". iSplitL "H0".
    { iExact "H0". }
    { iIntros (?) "H0". iFrame. }
  Qed.

  Global Program Instance ViewInterp_sndl {A B}
         (SA: A -> iProp) (SB: B -> iProp)
    : ViewInterp sndl (interp_prod SA SB) SB.
  Next Obligation.
  Proof.
    iIntros "[H0 H1]". iSplitL "H1".
    { iExact "H1". }
    { iIntros (?) "H1". iFrame. }
  Qed.

  Global Program Instance ViewInterp_id {S} (SI: S -> iProp): ViewInterp Lens.id SI SI.
  Next Obligation.
  Proof.
    iIntros "H". iSplitL "H".
    { iExact "H". }
    { iIntros (?) "H". iExact "H". }
  Qed.

  Global Program Instance ViewInterp_compose {A B C}
         {lab: Lens.t A B}
         {lbc: Lens.t B C}
         (SA: A -> iProp) (SB: B -> iProp) (SC: C -> iProp)
         `{VAB: ViewInterp _ _ lab SA SB}
         `{VBC: ViewInterp _ _ lbc SB SC}
    :
    ViewInterp (Lens.compose lab lbc) SA SC.
  Next Obligation.
  Proof.
    iIntros "H".
    iPoseProof (view_interp with "H") as "[H K0]".
    iPoseProof (view_interp with "H") as "[H K1]".
    iSplitL "H"; [auto|]. iIntros (?) "H".
    iApply "K0". iApply "K1". iApply "H".
  Qed.

  Definition N_state_src := (nroot .@ "_state_src").
  Definition E_state_src: coPset := ↑ N_state_src.
  Definition N_state_tgt := (nroot .@ "_state_tgt").
  Definition E_state_tgt: coPset := ↑ N_state_tgt.

  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable ident_src: ID.
  Variable ident_tgt: ID.

  Let srcE := threadE ident_src state_src.
  Let tgtE := threadE ident_tgt state_tgt.

  Let shared_rel := TIdSet.t -> (@imap ident_src owf) -> (@imap (sum_tid ident_tgt) nat_wf) -> state_src -> state_tgt -> iProp.

  Context `{Invs : @InvSet Σ}.

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
  Context `{COPSETRA : @GRA.inG CoPset.t Σ}.
  Context `{GSETRA : @GRA.inG Gset.t Σ}.
  Context `{INVSETRA : @GRA.inG (InvSetRA Var) Σ}.

  Definition St_src (st_src: state_src): iProp :=
    OwnM (Auth.white (Excl.just (Some st_src): @Excl.t (option state_src)): stateSrcRA state_src).

  Definition Vw_src (st: state_src) {V} (l : Lens.t state_src V) (v : V) : iProp :=
    St_src (Lens.set l v st).

  Definition src_interp_as {V} (l: Lens.t state_src V) (VI: V -> iProp) :=
    (∃ SI, (inv N_state_src (∃ st, St_src st ** SI st)) ** ⌜ViewInterp l SI VI⌝)%I.

  Global Program Instance src_interp_as_persistent {V} (l: Lens.t state_src V) (VI: V -> iProp): Persistent (src_interp_as l VI).

  Global Program Instance src_interp_as_acc A E {V} (l: Lens.t state_src V) (VI: V -> iProp):
    IntoAcc
      (src_interp_as l VI)
      (↑N_state_src ⊆ E) True
      (FUpd A E (E ∖ E_state_src)) (FUpd A (E ∖ E_state_src) E) (fun (st: state_src) => ∃ vw, Vw_src st l vw ** VI vw)%I (fun (st: state_src) => ∃ vw, Vw_src st l vw ** VI vw)%I (fun _ => None).
  Next Obligation.
  Proof.
    iIntros "[% [INV %]] _".
    iInv "INV" as "[% [ST INTERP]]" "K". iModIntro.
    iPoseProof (view_interp with "INTERP") as "[INTERP SET]".
    iExists _. iSplitL "ST INTERP".
    { iFrame. iExists _. iFrame.
      unfold Vw_src. iEval (rewrite Lens.set_view). auto.
    }
    iIntros "[% [ST INTERP]]".
    iPoseProof ("SET" with "INTERP") as "INTERP".
    iApply ("K" with "[ST INTERP]").
    iExists _. iFrame.
  Qed.

  Lemma src_interp_as_id A E (SI: state_src -> iProp)
        (IN: InvIn (∃ st, St_src st ** SI st)):
    (∃ st, St_src st ** SI st) ⊢ FUpd A E E (src_interp_as Lens.id (SI)).
  Proof.
    iIntros "H". iPoseProof (FUpd_alloc with "H") as "> H".
    iModIntro. iExists _. iSplit; eauto. iPureIntro. typeclasses eauto.
  Qed.

  Lemma src_interp_as_compose A B
        {la: Lens.t state_src A}
        {lb: Lens.t A B}
        (SA: A -> iProp)
        (SB: B -> iProp)
        `{VAB: ViewInterp _ _ lb SA SB}
    :
    src_interp_as la SA ⊢ src_interp_as (Lens.compose la lb) SB.
  Proof.
    iIntros "[% [H %]]". iExists _. iSplit; [eauto|].
    iPureIntro. typeclasses eauto.
  Qed.



  Definition St_tgt (st_tgt: state_tgt): iProp :=
    OwnM (Auth.white (Excl.just (Some st_tgt): @Excl.t (option state_tgt)): stateTgtRA state_tgt).

  Definition Vw_tgt (st: state_tgt) {V} (l : Lens.t state_tgt V) (v : V) : iProp :=
    St_tgt (Lens.set l v st).

  Definition tgt_interp_as {V} (l: Lens.t state_tgt V) (VI: V -> iProp) :=
    (∃ SI, (inv N_state_tgt (∃ st, St_tgt st ** SI st)) ** ⌜ViewInterp l SI VI⌝)%I.

  Global Program Instance tgt_interp_as_persistent {V} (l: Lens.t state_tgt V) (VI: V -> iProp): Persistent (tgt_interp_as l VI).

  Global Program Instance tgt_interp_as_acc A E {V} (l: Lens.t state_tgt V) (VI: V -> iProp):
    IntoAcc
      (tgt_interp_as l VI)
      (↑N_state_tgt ⊆ E) True
      (FUpd A E (E ∖ E_state_tgt)) (FUpd A (E ∖ E_state_tgt) E) (fun (st: state_tgt) => ∃ vw, Vw_tgt st l vw ** VI vw)%I (fun (st: state_tgt) => ∃ vw, Vw_tgt st l vw ** VI vw)%I (fun _ => None).
  Next Obligation.
  Proof.
    iIntros "[% [INV %]] _".
    iInv "INV" as "[% [ST INTERP]]" "K". iModIntro.
    iPoseProof (view_interp with "INTERP") as "[INTERP SET]".
    iExists _. iSplitL "ST INTERP".
    { iFrame. iExists _. iFrame.
      unfold Vw_tgt. iEval (rewrite Lens.set_view). auto.
    }
    iIntros "[% [ST INTERP]]".
    iPoseProof ("SET" with "INTERP") as "INTERP".
    iApply ("K" with "[ST INTERP]").
    iExists _. iFrame.
  Qed.

  Lemma tgt_interp_as_id A E (SI: state_tgt -> iProp)
        (IN: InvIn (∃ st, St_tgt st ** SI st)):
    (∃ st, St_tgt st ** SI st) ⊢ FUpd A E E (tgt_interp_as Lens.id (SI)).
  Proof.
    iIntros "H". iPoseProof (FUpd_alloc with "H") as "> H".
    iModIntro. iExists _. iSplit; eauto. iPureIntro. typeclasses eauto.
  Qed.

  Lemma tgt_interp_as_compose A B
        {la: Lens.t state_tgt A}
        {lb: Lens.t A B}
        (SA: A -> iProp)
        (SB: B -> iProp)
        `{VAB: ViewInterp _ _ lb SA SB}
    :
    tgt_interp_as la SA ⊢ tgt_interp_as (Lens.compose la lb) SB.
  Proof.
    iIntros "[% [H %]]". iExists _. iSplit; [eauto|].
    iPureIntro. typeclasses eauto.
  Qed.


  Definition default_initial_res
    : Σ :=
    (@GRA.embed _ _ THDRA (Auth.black (Some (NatMap.empty unit): NatMapRAFOS.t unit)))
      ⋅
      (@GRA.embed _ _ STATESRC (Auth.black (Excl.just None: @Excl.t (option state_src)) ⋅ (Auth.white (Excl.just None: @Excl.t (option state_src)): stateSrcRA state_src)))
      ⋅
      (@GRA.embed _ _ STATETGT (Auth.black (Excl.just None: @Excl.t (option state_tgt)) ⋅ (Auth.white (Excl.just None: @Excl.t (option state_tgt)): stateTgtRA state_tgt)))
      ⋅
      (@GRA.embed _ _ IDENTSRC (@FairRA.source_init_resource ident_src))
      ⋅
      (@GRA.embed _ _ IDENTTGT ((fun _ => Fuel.black 0 1%Qp): identTgtRA ident_tgt))
      ⋅
      (@GRA.embed _ _ ARROWRA ((fun _ => OneShot.pending _ 1%Qp): ArrowRA ident_tgt))
      ⋅
      (@GRA.embed _ _ EDGERA ((fun _ => OneShot.pending _ 1%Qp): EdgeRA))
      ⋅
      (@GRA.embed _ _ INVSETRA (@Auth.black (positive ==> URA.agree Var)%ra (fun _ => None)))
      ⋅
      (@GRA.embed _ _ COPSETRA (Some ⊤))
  .

  Lemma own_threads_init ths
    :
    (OwnM (Auth.black (Some (NatMap.empty unit): NatMapRAFOS.t unit)))
      -∗
      (#=>
         ((OwnM (Auth.black (Some ths: NatMapRAFOS.t unit)))
            **
            (natmap_prop_sum ths (fun tid _ => own_thread tid)))).
  Proof.
    pattern ths. revert ths. eapply nm_ind.
    { iIntros "OWN". iModIntro. iFrame. }
    i. iIntros "OWN".
    iPoseProof (IH with "OWN") as "> [OWN SUM]".
    iPoseProof (OwnM_Upd with "OWN") as "> [OWN0 OWN1]".
    { eapply Auth.auth_alloc. eapply (@NatMapRAFOS.add_local_update unit m k v); eauto. }
    iModIntro. iFrame. destruct v. iApply (natmap_prop_sum_add with "SUM OWN1").
  Qed.

  Lemma default_initial_res_init
    :
    (Own (default_initial_res))
      -∗
      (∀ ths st_src st_tgt im_tgt o,
          #=> (∃ im_src,
                  (default_I ths im_src im_tgt st_src st_tgt)
                    **
                    (natmap_prop_sum ths (fun tid _ => ObligationRA.duty inlp tid []))
                    **
                    (natmap_prop_sum ths (fun tid _ => own_thread tid))
                    **
                    (FairRA.whites Prism.id (fun _ => True: Prop) o)
                    **
                    (FairRA.blacks Prism.id (fun i => match i with | inr _ => True | _ => False end: Prop))
                    **
                    (St_src st_src)
                    **
                    (St_tgt st_tgt)
                    **
                    wsat
                    **
                    OwnE ⊤
      )).
  Proof.
    iIntros "OWN" (? ? ? ? ?).
    iDestruct "OWN" as "[[[[[[[[OWN0 [OWN1 OWN2]] [OWN3 OWN4]] OWN5] OWN6] OWN7] OWN8] OWN9] OWN10]".
    iPoseProof (black_white_update with "OWN1 OWN2") as "> [OWN1 OWN2]".
    iPoseProof (black_white_update with "OWN3 OWN4") as "> [OWN3 OWN4]".
    iPoseProof (OwnM_Upd with "OWN6") as "> OWN6".
    { instantiate (1:=FairRA.target_init_resource im_tgt).
      unfold FairRA.target_init_resource.
      erewrite ! (@unfold_pointwise_add (id_sum nat ident_tgt) (Fuel.t nat)).
      apply pointwise_updatable. i.
      rewrite URA.add_comm. exact (@Fuel.success_update nat _ 0 (im_tgt a)).
    }
    iPoseProof (FairRA.target_init with "OWN6") as "[[H0 H1] H2]".
    iPoseProof (FairRA.source_init with "OWN5") as "> [% [H3 H4]]".
    iExists f. unfold default_I. iFrame.
    iPoseProof (wsat_init with "OWN9") as "W". iFrame.
    iPoseProof (own_threads_init with "OWN0") as "> [OWN0 H]". iFrame.
    iModIntro. iSplitR "H2"; [iSplitR "H1"; [iSplitL "OWN8"|]|].
    { iExists _. iSplitL.
      { iApply (OwnM_extends with "OWN8"). instantiate (1:=[]).
        apply pointwise_extends. i. destruct a; ss; reflexivity.
      }
      { ss. }
    }
    { iExists _. iSplitL.
      { iApply (OwnM_extends with "OWN7"). instantiate (1:=[]).
        apply pointwise_extends. i. destruct a; ss; reflexivity.
      }
      { ss. }
    }
    { iApply natmap_prop_sum_impl; [|eauto]. i. ss.
      iApply ObligationRA.black_to_duty. }
    { iPoseProof (FairRA.blacks_prism_id with "H2") as "H".
      iApply (FairRA.blacks_impl with "H").
      i. des_ifs. esplits; eauto.
    }
  Qed.

  Let I: shared_rel :=
        fun ths im_src im_tgt st_src st_tgt =>
          default_I ths im_src im_tgt st_src st_tgt ** (wsat ** OwnE ⊤).

  Let rel := (forall R_src R_tgt (Q: R_src -> R_tgt -> iProp), bool -> bool -> itree srcE R_src -> itree tgtE R_tgt -> iProp).

  Variable tid: thread_id.

  Let unlift_rel
      (r: forall R_src R_tgt (Q: R_src -> R_tgt -> shared_rel), bool -> bool -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel): rel :=
        fun R_src R_tgt Q ps pt itr_src itr_tgt =>
          (∀ ths im_src im_tgt st_src st_tgt,
              (default_I_past tid ths im_src im_tgt st_src st_tgt ** (wsat ** OwnE ⊤))
                -*
                (@r R_src R_tgt (fun r_src r_tgt ths im_src im_tgt st_src st_tgt => (default_I_past tid ths im_src im_tgt st_src st_tgt ** (wsat ** OwnE ⊤)) ** Q r_src r_tgt) ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt))%I.

  Let lift_rel (rr: rel):
    forall R_src R_tgt (QQ: R_src -> R_tgt -> shared_rel), bool -> bool -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel :=
        fun R_src R_tgt QQ ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt =>
          (∃ (Q: R_src -> R_tgt -> iProp)
             (EQ: QQ = (fun r_src r_tgt ths im_src im_tgt st_src st_tgt =>
                          (default_I_past tid ths im_src im_tgt st_src st_tgt ** (wsat ** OwnE ⊤)) ** Q r_src r_tgt)),
              rr R_src R_tgt Q ps pt itr_src itr_tgt ** (default_I_past tid ths im_src im_tgt st_src st_tgt ** (wsat ** OwnE ⊤)))%I.

  Let unlift_rel_base r
    :
    forall R_src R_tgt Q ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt,
      (r R_src R_tgt Q ps pt itr_src itr_tgt)
        -∗
        (default_I_past tid ths im_src im_tgt st_src st_tgt ** (wsat ** OwnE ⊤))
        -∗
        (lift_rel
           r
           (fun r_src r_tgt ths im_src im_tgt st_src st_tgt => (default_I_past tid ths im_src im_tgt st_src st_tgt ** (wsat ** OwnE ⊤)) ** Q r_src r_tgt)
           ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt).
  Proof.
    unfold lift_rel, unlift_rel. i.
    iIntros "H D". iExists _, _. Unshelve.
    { iFrame. }
    { auto. }
  Qed.

  Let unlift_lift r
    :
    forall R_src R_tgt Q ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt,
      (lift_rel (unlift_rel r) Q ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
        ⊢ (r R_src R_tgt Q ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt).
  Proof.
    unfold lift_rel, unlift_rel. i.
    iIntros "[% [% [H D]]]". subst.
    iApply ("H" with "D").
  Qed.

  Let lift_unlift (r0: rel) (r1: forall R_src R_tgt (Q: R_src -> R_tgt -> shared_rel), bool -> bool -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel)
    :
    bi_entails
      (∀ R_src R_tgt (Q: R_src -> R_tgt -> shared_rel) ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt,
          @lift_rel r0 R_src R_tgt Q ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt -* r1 R_src R_tgt Q ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
      (∀ R_src R_tgt Q ps pt itr_src itr_tgt, r0 R_src R_tgt Q ps pt itr_src itr_tgt -* unlift_rel r1 Q ps pt itr_src itr_tgt).
  Proof.
    unfold lift_rel, unlift_rel.
    iIntros "IMPL" (? ? ? ? ? ? ?) "H". iIntros (? ? ? ? ?) "D".
    iApply "IMPL". iExists _, _. Unshelve.
    { iFrame. }
    { auto. }
  Qed.

  Let lift_rel_mon (rr0 rr1: rel)
      (MON: forall R_src R_tgt Q ps pt itr_src itr_tgt,
          bi_entails
            (rr0 R_src R_tgt Q ps pt itr_src itr_tgt)
            (#=> rr1 R_src R_tgt Q ps pt itr_src itr_tgt))
    :
    forall R_src R_tgt (QQ: R_src -> R_tgt -> shared_rel) ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt,
      bi_entails
        (lift_rel rr0 QQ ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
        (#=> lift_rel rr1 QQ ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt).
  Proof.
    unfold lift_rel. i.
    iIntros "[% [% [H D]]]". subst.
    iPoseProof (MON with "H") as "> H".
    iModIntro. iExists _, _. Unshelve.
    { iFrame. }
    { auto. }
  Qed.

  Definition stsim (E : coPset) : rel -> rel -> rel :=
    fun r g
        R_src R_tgt Q ps pt itr_src itr_tgt =>
      (∀ ths im_src im_tgt st_src st_tgt,
          (default_I_past tid ths im_src im_tgt st_src st_tgt ** (wsat ** OwnE E))
            -*
            (isim
               tid
               I
               (lift_rel r)
               (lift_rel g)
               (fun r_src r_tgt ths im_src im_tgt st_src st_tgt => (default_I_past tid ths im_src im_tgt st_src st_tgt ** (wsat ** OwnE ⊤)) ** Q r_src r_tgt)
               ps pt itr_src itr_tgt
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
        ps pt itr_src itr_tgt
        (TOP: E0 ⊆ E1)
    :
    (stsim E0 r g Q ps pt itr_src itr_tgt)
      -∗
      (stsim E1 r g Q ps pt itr_src itr_tgt)
  .
  Proof.
    unfold stsim. iIntros "H" (? ? ? ? ?) "(D & W & E)".
    iApply "H". iFrame. iPoseProof (OwnE_subset with "E") as "[E0 E1]"; [eapply TOP|]. ss.
  Qed.

  Lemma stsim_base E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt itr_src itr_tgt
        (TOP: ⊤ ⊆ E)
    :
    (@r _ _ Q ps pt itr_src itr_tgt)
      -∗
      (stsim E r g Q ps pt itr_src itr_tgt)
  .
  Proof.
    rewrite <- stsim_discard; [|eassumption].
    unfold stsim. iIntros "H" (? ? ? ? ?) "D".
    iApply isim_base.
    iApply (unlift_rel_base with "H D").
  Qed.

  Lemma stsim_mono_knowledge E (r0 g0 r1 g1: rel) R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt itr_src itr_tgt
        (MON0: forall R_src R_tgt (Q: R_src -> R_tgt -> iProp)
                      ps pt itr_src itr_tgt,
            (@r0 _ _ Q ps pt itr_src itr_tgt)
              -∗
              (#=> (@r1 _ _ Q ps pt itr_src itr_tgt)))
        (MON1: forall R_src R_tgt (Q: R_src -> R_tgt -> iProp)
                      ps pt itr_src itr_tgt,
            (@g0 _ _ Q ps pt itr_src itr_tgt)
              -∗
              (#=> (@g1 _ _ Q ps pt itr_src itr_tgt)))
    :
    bi_entails
      (stsim E r0 g0 Q ps pt itr_src itr_tgt)
      (stsim E r1 g1 Q ps pt itr_src itr_tgt)
  .
  Proof.
    unfold stsim. iIntros "H" (? ? ? ? ?) "D".
    iApply isim_mono_knowledge.
    { eapply lift_rel_mon. eauto. }
    { eapply lift_rel_mon. eauto. }
    iApply ("H" with "D").
  Qed.

  Lemma stsim_coind E A
        (R_src: forall (a: A), Type)
        (R_tgt: forall (a: A), Type)
        (Q: forall (a: A), R_src a -> R_tgt a -> iProp)
        (ps pt: forall (a: A), bool)
        (itr_src : forall (a: A), itree srcE (R_src a))
        (itr_tgt : forall (a: A), itree tgtE (R_tgt a))
        (P: forall (a: A), iProp)
        (r g0: rel)
        (TOP: ⊤ ⊆ E)
        (COIND: forall (g1: rel) a,
            (□((∀ R_src R_tgt (Q: R_src -> R_tgt -> iProp)
                  ps pt itr_src itr_tgt,
                   @g0 R_src R_tgt Q ps pt itr_src itr_tgt -* @g1 R_src R_tgt Q ps pt itr_src itr_tgt)
                 **
                 (∀ a, P a -* @g1 (R_src a) (R_tgt a) (Q a) (ps a) (pt a) (itr_src a) (itr_tgt a))))
              -∗
              (P a)
              -∗
              (stsim ⊤ r g1 (Q a) (ps a) (pt a) (itr_src a) (itr_tgt a)))
    :
    (forall a, bi_entails (P a) (stsim E r g0 (Q a) (ps a) (pt a) (itr_src a) (itr_tgt a))).
  Proof.
    cut (forall (m: mytype A),
            bi_entails
              ((fun m => P m.(comp_a) ** (default_I_past tid m.(comp_ths) m.(comp_im_src) m.(comp_im_tgt) m.(comp_st_src) m.(comp_st_tgt) ** (wsat ** OwnE ⊤))) m)
              (isim tid I (lift_rel r) (lift_rel g0) ((fun m => fun r_src r_tgt ths im_src im_tgt st_src st_tgt => (default_I_past tid ths im_src im_tgt st_src st_tgt ** (wsat ** OwnE ⊤)) ** Q m.(comp_a) r_src r_tgt) m)
                    ((fun m => ps m.(comp_a)) m) ((fun m => pt m.(comp_a)) m) ((fun m => itr_src m.(comp_a)) m) ((fun m => itr_tgt m.(comp_a)) m) (comp_ths m) (comp_im_src m) (comp_im_tgt m) (comp_st_src m) (comp_st_tgt m))).
    { ss. i. rewrite <- stsim_discard; [|eassumption].
      unfold stsim. iIntros "H" (? ? ? ? ?) "D".
      specialize (H (mk_mytype a ths im_src im_tgt st_src st_tgt)). ss.
      iApply H. iFrame.
    }
    eapply isim_coind. i. iIntros "[# CIH [H D]]".
    unfold stsim in COIND.
    iAssert (□((∀ R_src R_tgt (Q: R_src -> R_tgt -> iProp)
                  ps pt itr_src itr_tgt,
                   @g0 R_src R_tgt Q ps pt itr_src itr_tgt -* @unlift_rel g1 R_src R_tgt Q ps pt itr_src itr_tgt)
                 **
                 (∀ a, P a -* @unlift_rel g1 (R_src a) (R_tgt a) (Q a) (ps a) (pt a) (itr_src a) (itr_tgt a))))%I with "[CIH]" as "CIH'".
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
        ps pt itr_src itr_tgt
    :
    (#=> (stsim E r g Q ps pt itr_src itr_tgt))
      -∗
      (stsim E r g Q ps pt itr_src itr_tgt)
  .
  Proof.
    unfold stsim. iIntros "H" (? ? ? ? ?) "D". iMod "H".
    iApply "H". auto.
  Qed.

  Global Instance stsim_elim_upd
         E r g R_src R_tgt
         (Q: R_src -> R_tgt -> iProp)
         ps pt itr_src itr_tgt p
         P
    :
    ElimModal True p false (#=> P) P (stsim E r g Q ps pt itr_src itr_tgt) (stsim E r g Q ps pt itr_src itr_tgt).
  Proof.
    typeclasses eauto.
  Qed.

  Lemma stsim_FUpd E0 E1 r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt itr_src itr_tgt
    :
    (FUpd (fairI (ident_tgt:=ident_tgt)) E0 E1 (stsim E1 r g Q ps pt itr_src itr_tgt))
      -∗
      (stsim E0 r g Q ps pt itr_src itr_tgt)
  .
  Proof.
    Local Transparent FUpd.
    unfold stsim. iIntros "H" (? ? ? ? ?) "[[% [% [[D X0] X1]]] (WSAT & E)]".
    iAssert (fairI (ident_tgt:=ident_tgt) ** (wsat ** OwnE E0)) with "[X0 X1 WSAT E]" as "C".
    { iFrame. }
    unfold FUpd.
    iMod ("H" with "C") as "(F & WSAT & E & H)".
    iApply "H". iFrame. iExists _. iFrame. auto.
  Qed.

  Lemma stsim_FUpd_weaken E0 E1 r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt itr_src itr_tgt
        (SUB: E0 ⊆ E1)
    :
    (FUpd (fairI (ident_tgt:=ident_tgt)) E0 E0 (stsim E1 r g Q ps pt itr_src itr_tgt))
      -∗
      (stsim E1 r g Q ps pt itr_src itr_tgt)
  .
  Proof.
    iIntros "H". iApply stsim_FUpd. iApply FUpd_mask_mono; eauto.
  Qed.

  Global Instance stsim_elim_FUpd_gen
         E0 E1 E2 r g R_src R_tgt
         (Q: R_src -> R_tgt -> iProp)
         ps pt itr_src itr_tgt p
         P
    :
    ElimModal (E0 ⊆ E2) p false (FUpd (fairI (ident_tgt:=ident_tgt)) E0 E1 P) P (stsim E2 r g Q ps pt itr_src itr_tgt) (stsim (E1 ∪ (E2 ∖ E0)) r g Q ps pt itr_src itr_tgt).
  Proof.
    unfold ElimModal. rewrite bi.intuitionistically_if_elim.
    i. iIntros "[H0 H1]".
    iPoseProof (FUpd_mask_frame _ _ _ (E2 ∖ E0) with "H0") as "H0".
    { eapply disjoint_difference_r1. set_solver. }
    replace (E0 ∪ E2 ∖ E0) with E2.
    2: { eapply leibniz_equiv. eapply union_difference. ss. }
    iApply stsim_FUpd. iMod "H0". iModIntro. iApply "H1". iFrame.
  Qed.

  Global Instance stsim_elim_FUpd_eq
         E1 E2 r g R_src R_tgt
         (Q: R_src -> R_tgt -> iProp)
         ps pt itr_src itr_tgt p
         P
    :
    ElimModal (E1 ⊆ E2) p false (FUpd (fairI (ident_tgt:=ident_tgt)) E1 E1 P) P (stsim E2 r g Q ps pt itr_src itr_tgt) (stsim E2 r g Q ps pt itr_src itr_tgt).
  Proof.
    unfold ElimModal. rewrite bi.intuitionistically_if_elim.
    i. iIntros "[H0 H1]".
    iApply stsim_FUpd_weaken.
    { eauto. }
    iMod "H0". iModIntro. iApply ("H1" with "H0").
  Qed.

  Global Instance stsim_elim_FUpd
         E1 E2 r g R_src R_tgt
         (Q: R_src -> R_tgt -> iProp)
         ps pt itr_src itr_tgt p
         P
    :
    ElimModal True p false (FUpd (fairI (ident_tgt:=ident_tgt)) E1 E2 P) P (stsim E1 r g Q ps pt itr_src itr_tgt) (stsim E2 r g Q ps pt itr_src itr_tgt).
  Proof.
    unfold ElimModal. rewrite bi.intuitionistically_if_elim.
    i. iIntros "[H0 H1]".
    iApply stsim_FUpd. iMod "H0".
    iModIntro. iApply ("H1" with "H0").
  Qed.

  Global Instance stsim_add_modal_FUpd
         E r g R_src R_tgt
         (Q: R_src -> R_tgt -> iProp)
         ps pt itr_src itr_tgt
         P
    :
    AddModal (FUpd (fairI (ident_tgt:=ident_tgt)) E E P) P (stsim E r g Q ps pt itr_src itr_tgt).
  Proof.
    unfold AddModal. iIntros "[> H0 H1]". iApply ("H1" with "H0").
  Qed.

  Global Instance stsim_elim_iupd_edge
         E r g R_src R_tgt
         (Q: R_src -> R_tgt -> iProp)
         ps pt itr_src itr_tgt p
         P
    :
    ElimModal True p false (#=(ObligationRA.edges_sat)=> P) P (stsim E r g Q ps pt itr_src itr_tgt) (stsim E r g Q ps pt itr_src itr_tgt).
  Proof.
    unfold ElimModal. rewrite bi.intuitionistically_if_elim.
    i. iIntros "[H0 H1]" (? ? ? ? ?) "[[% [% D]] [C E]]".
    iPoseProof (IUpd_sub_mon with "[] H0 D") as "> [D P]"; auto.
    { iApply edges_sat_sub. }
    iApply ("H1" with "P"). iFrame. iExists _. eauto.
  Qed.

  Global Instance stsim_elim_iupd_arrow
         E r g R_src R_tgt
         (Q: R_src -> R_tgt -> iProp)
         ps pt itr_src itr_tgt p
         P
    :
    ElimModal True p false (#=(ObligationRA.arrows_sat (S:=sum_tid ident_tgt))=> P) P (stsim E r g Q ps pt itr_src itr_tgt) (stsim E r g Q ps pt itr_src itr_tgt).
  Proof.
    unfold ElimModal. rewrite bi.intuitionistically_if_elim.
    i. iIntros "[H0 H1]" (? ? ? ? ?) "[[% [% D]] [C E]]".
    iPoseProof (IUpd_sub_mon with "[] H0 D") as "> [D P]"; auto.
    { iApply arrows_sat_sub. }
    iApply ("H1" with "P"). iFrame. iExists _. eauto.
  Qed.

  Global Instance mupd_elim_iupd_edge
         P Q E1 E2 p Inv
    :
    ElimModal True p false (#=(ObligationRA.edges_sat)=> P) P (MUpd Inv (fairI (ident_tgt:=ident_tgt)) E1 E2 Q) (MUpd Inv (fairI (ident_tgt:=ident_tgt)) E1 E2 Q).
  Proof.
    unfold ElimModal. rewrite bi.intuitionistically_if_elim.
    i. iIntros "[H0 H1]".
    iPoseProof (IUpd_sub_mon with "[] H0") as "H0".
    { iApply SubIProp_sep_l. }
    iMod "H0". iApply ("H1" with "H0").
  Qed.

  Global Instance mupd_elim_upd_arrow
         P Q E1 E2 p Inv
    :
    ElimModal True p false (#=(ObligationRA.arrows_sat (S:=sum_tid ident_tgt))=> P) P (MUpd Inv (fairI (ident_tgt:=ident_tgt)) E1 E2 Q) (MUpd Inv (fairI (ident_tgt:=ident_tgt)) E1 E2 Q).
  Proof.
    unfold ElimModal. rewrite bi.intuitionistically_if_elim.
    i. iIntros "[H0 H1]".
    iPoseProof (IUpd_sub_mon with "[] H0") as "H0".
    { iApply SubIProp_sep_r. }
    iMod "H0". iApply ("H1" with "H0").
  Qed.

  Global Instance mupd_elim_fupd_edge
         P Q E1 E2 p
    :
    ElimModal True p false (#=(ObligationRA.edges_sat)=> P) P (FUpd (fairI (ident_tgt:=ident_tgt)) E1 E2 Q) (FUpd (fairI (ident_tgt:=ident_tgt)) E1 E2 Q).
  Proof.
    unfold ElimModal. rewrite bi.intuitionistically_if_elim.
    i. iIntros "[H0 H1]".
    iPoseProof (IUpd_sub_mon with "[] H0") as "H0".
    { iApply SubIProp_sep_l. }
    iMod "H0". iApply ("H1" with "H0").
  Qed.

  Global Instance mupd_elim_fupd_arrow
         P Q E1 E2 p
    :
    ElimModal True p false (#=(ObligationRA.arrows_sat (S:=sum_tid ident_tgt))=> P) P (FUpd (fairI (ident_tgt:=ident_tgt)) E1 E2 Q) (FUpd (fairI (ident_tgt:=ident_tgt)) E1 E2 Q).
  Proof.
    unfold ElimModal. rewrite bi.intuitionistically_if_elim.
    i. iIntros "[H0 H1]".
    iPoseProof (IUpd_sub_mon with "[] H0") as "H0".
    { iApply SubIProp_sep_r. }
    iMod "H0". iApply ("H1" with "H0").
  Qed.

  Lemma stsim_wand E r g R_src R_tgt
        (Q0 Q1: R_src -> R_tgt -> iProp)
        ps pt itr_src itr_tgt
    :
    (stsim E r g Q0 ps pt itr_src itr_tgt)
      -∗
      (∀ r_src r_tgt,
          ((Q0 r_src r_tgt) -∗ #=> (Q1 r_src r_tgt)))
      -∗
      (stsim E r g Q1 ps pt itr_src itr_tgt)
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
        ps pt itr_src itr_tgt
    :
    (stsim E r g Q0 ps pt itr_src itr_tgt)
      -∗
      (stsim E r g Q1 ps pt itr_src itr_tgt)
  .
  Proof.
    iIntros "H". iApply (stsim_wand with "H").
    iIntros. iApply MONO. auto.
  Qed.

  Lemma stsim_frame E r g R_src R_tgt
        P (Q: R_src -> R_tgt -> iProp)
        ps pt itr_src itr_tgt
    :
    (stsim E r g Q ps pt itr_src itr_tgt)
      -∗
      P
      -∗
      (stsim E r g (fun r_src r_tgt => P ** Q r_src r_tgt) ps pt itr_src itr_tgt)
  .
  Proof.
    iIntros "H0 H1". iApply (stsim_wand with "H0").
    iIntros. iModIntro. iFrame.
  Qed.

  Lemma stsim_bind_top E r g R_src R_tgt S_src S_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt (itr_src: itree srcE S_src) (itr_tgt: itree tgtE S_tgt)
        ktr_src ktr_tgt
    :
    (stsim E r g (fun s_src s_tgt => stsim ⊤ r g Q false false (ktr_src s_src) (ktr_tgt s_tgt)) ps pt itr_src itr_tgt)
      -∗
      (stsim E r g Q ps pt (itr_src >>= ktr_src) (itr_tgt >>= ktr_tgt))
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
        ps pt r_src r_tgt
    :
    (FUpd (fairI (ident_tgt:=ident_tgt)) E ⊤ (Q r_src r_tgt))
      -∗
      (stsim E r g Q ps pt (Ret r_src) (Ret r_tgt))
  .
  Proof.
    iIntros "> H".
    unfold stsim. iIntros (? ? ? ? ?) "D".
    iApply isim_ret. iFrame.
  Qed.

  Lemma stsim_tauL E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt itr_src itr_tgt
    :
    (stsim E r g Q true pt itr_src itr_tgt)
      -∗
      (stsim E r g Q ps pt (Tau itr_src) itr_tgt)
  .
  Proof.
    unfold stsim. iIntros "H" (? ? ? ? ?) "D".
    iPoseProof ("H" $! _ _ _ _ _ with "D") as "H".
    iApply isim_tauL. iFrame.
  Qed.

  Lemma stsim_tauR E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt itr_src itr_tgt
    :
    (stsim E r g Q ps true itr_src itr_tgt)
      -∗
      (stsim E r g Q ps pt itr_src (Tau itr_tgt))
  .
  Proof.
    unfold stsim. iIntros "H" (? ? ? ? ?) "D".
    iPoseProof ("H" $! _ _ _ _ _ with "D") as "H".
    iApply isim_tauR. iFrame.
  Qed.

  Lemma stsim_chooseL E X r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src itr_tgt
    :
    (∃ x, stsim E r g Q true pt (ktr_src x) itr_tgt)
      -∗
      (stsim E r g Q ps pt (trigger (Choose X) >>= ktr_src) itr_tgt)
  .
  Proof.
    unfold stsim. iIntros "[% H]" (? ? ? ? ?) "D".
    iPoseProof ("H" $! _ _ _ _ _ with "D") as "H".
    iApply isim_chooseL. iExists _. iFrame.
  Qed.

  Lemma stsim_chooseR E X r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt itr_src ktr_tgt
    :
    (∀ x, stsim E r g Q ps true itr_src (ktr_tgt x))
      -∗
      (stsim E r g Q ps pt itr_src (trigger (Choose X) >>= ktr_tgt))
  .
  Proof.
    unfold stsim. iIntros "H" (? ? ? ? ?) "D".
    iApply isim_chooseR. iIntros (?).
    iPoseProof ("H" $! _ _ _ _ _ _ with "D") as "H". iFrame.
  Qed.

  Lemma stsim_stateL E X run r g R_src R_tgt
    (Q : R_src -> R_tgt -> iProp)
    ps pt ktr_src itr_tgt st_src
    :
    (St_src st_src)
    -∗ (St_src (fst (run st_src)) -∗ stsim E r g Q true pt (ktr_src (snd (run st_src) : X)) itr_tgt)
    -∗ stsim E r g Q ps pt (trigger (State run) >>= ktr_src) itr_tgt.
  Proof.
    unfold stsim. iIntros "H0 H1" (? ? ? ? ?) "(D & C & E)". iApply isim_stateL.
    iAssert (⌜st_src0 = st_src⌝)%I as "%".
    { iApply (default_I_past_get_st_src with "D H0"); eauto. }
    subst.
    iPoseProof (default_I_past_update_st_src with "D H0") as "> [D H0]".
    iApply ("H1" with "D [H0 C E]"). iFrame.
  Qed.

  Lemma stsim_lens_stateL E V (l : Lens.t _ V) X run r g R_src R_tgt
    (Q : R_src -> R_tgt -> iProp)
    ps pt ktr_src itr_tgt st v
    :
    (Vw_src st l v)
    -∗ (Vw_src st l (fst (run v)) -∗ stsim E r g Q true pt (ktr_src (snd (run v) : X)) itr_tgt)
    -∗ stsim E r g Q ps pt (trigger (map_lens l (State run)) >>= ktr_src) itr_tgt.
  Proof.
    iIntros "S H". rewrite map_lens_State. iApply (stsim_stateL with "S").
    iIntros "S". ss. unfold Vw_src.
    rewrite Lens.view_set. rewrite Lens.set_set.
    iApply ("H" with "S").
  Qed.

  Lemma stsim_stateR E X run r g R_src R_tgt
    (Q : R_src -> R_tgt -> iProp)
    ps pt itr_src ktr_tgt st_tgt
    :
    (St_tgt st_tgt)
    -∗ (St_tgt (fst (run st_tgt)) -∗ stsim E r g Q ps true itr_src (ktr_tgt (snd (run st_tgt) : X)))
    -∗ stsim E r g Q ps pt itr_src (trigger (State run) >>= ktr_tgt).
  Proof.
    unfold stsim. iIntros "H0 H1" (? ? ? ? ?) "(D & C & E)". iApply isim_stateR.
    iAssert (⌜st_tgt0 = st_tgt⌝)%I as "%".
    { iApply (default_I_past_get_st_tgt with "D H0"); eauto. }
    subst.
    iPoseProof (default_I_past_update_st_tgt with "D H0") as "> [D H0]".
    iApply ("H1" with "D [H0 C E]"). iFrame.
  Qed.

  Lemma stsim_lens_stateR E V (l : Lens.t _ V) X run r g R_src R_tgt
    (Q : R_src -> R_tgt -> iProp)
    ps pt itr_src ktr_tgt st v
    :
    (Vw_tgt st l v)
    -∗ (Vw_tgt st l (fst (run v)) -∗ stsim E r g Q ps true itr_src (ktr_tgt (snd (run v) : X)))
    -∗ stsim E r g Q ps pt itr_src (trigger (map_lens l (State run)) >>= ktr_tgt).
  Proof.
    iIntros "S H". rewrite map_lens_State. iApply (stsim_stateR with "S").
    iIntros "S". ss. unfold Vw_tgt.
    rewrite Lens.view_set. rewrite Lens.set_set.
    iApply ("H" with "S").
  Qed.

  Lemma stsim_lens_getL V (l : Lens.t _ V) X (p : V -> X) E st v r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src itr_tgt
    :
    ((Vw_src st l v) ∧
       (stsim E r g Q true pt (ktr_src (p v)) itr_tgt))
      -∗
      (stsim E r g Q ps pt (trigger (map_lens l (Get p)) >>= ktr_src) itr_tgt)
  .
  Proof.
    unfold stsim. iIntros "H" (? ? ? ? ?) "[D C]".
    rewrite map_lens_Get. rewrite Get_State. iApply isim_stateL. ss.
    iAssert (⌜Lens.view l st_src = v⌝)%I as "%".
    { iDestruct "H" as "[H1 _]". subst.
      iPoseProof (default_I_past_get_st_src with "D H1") as "%H". subst.
      rewrite Lens.view_set. auto.
    }
    rewrite H. iDestruct "H" as "[_ H]". iApply ("H" with "[D C]"). iFrame.
  Qed.

  Lemma stsim_getL X (p : state_src -> X) E st r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src itr_tgt
    :
    ((St_src st) ∧
       (stsim E r g Q true pt (ktr_src (p st)) itr_tgt))
      -∗
      (stsim E r g Q ps pt (trigger (Get p) >>= ktr_src) itr_tgt)
  .
  Proof.
    iIntros "H". replace (Get p) with (map_lens Lens.id (Get p)) by ss.
    iApply stsim_lens_getL. iSplit.
    - iDestruct "H" as "[H _]". iApply "H".
    - iDestruct "H" as "[_ H]". ss.
    Unshelve. all: eauto.
  Qed.

  Lemma stsim_lens_getR V (l : Lens.t _ V) X (p : V -> X) E st v r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt itr_src ktr_tgt
    :
    ((Vw_tgt st l v) ∧
       (stsim E r g Q ps true itr_src (ktr_tgt (p v))))
      -∗
      (stsim E r g Q ps pt itr_src (trigger (map_lens l (Get p)) >>= ktr_tgt))
  .
  Proof.
    unfold stsim. iIntros "H" (? ? ? ? ?) "[D C]".
    rewrite map_lens_Get. rewrite Get_State. iApply isim_stateR. ss.
    iAssert (⌜Lens.view l st_tgt = v⌝)%I as "%".
    { iDestruct "H" as "[H1 _]". subst.
      iPoseProof (default_I_past_get_st_tgt with "D H1") as "%H". subst.
      rewrite Lens.view_set. auto.
    }
    rewrite H. iDestruct "H" as "[_ H]". iApply ("H" with "[D C]"). iFrame.
  Qed.

  Lemma stsim_getR X (p : state_tgt -> X) E st r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt itr_src ktr_tgt
    :
    ((St_tgt st) ∧
       (stsim E r g Q ps true itr_src (ktr_tgt (p st))))
      -∗
      (stsim E r g Q ps pt itr_src (trigger (Get p) >>= ktr_tgt))
  .
  Proof.
    iIntros "H". replace (Get p) with (map_lens Lens.id (Get p)) by ss.
    iApply stsim_lens_getR. iSplit.
    - iDestruct "H" as "[H _]". iApply "H".
    - iDestruct "H" as "[_ H]". ss.
    Unshelve. all: eauto.
  Qed.

  Lemma stsim_modifyL E f r g R_src R_tgt
    (Q : R_src -> R_tgt -> iProp)
    ps pt ktr_src itr_tgt st_src
    :
    (St_src st_src)
    -∗ (St_src (f st_src) -∗ stsim E r g Q true pt (ktr_src tt) itr_tgt)
    -∗ stsim E r g Q ps pt (trigger (Modify f) >>= ktr_src) itr_tgt.
  Proof.
    rewrite Modify_State. iIntros "H1 H2". iApply (stsim_stateL with "H1"). ss.
  Qed.

  Lemma stsim_lens_modifyL E V (l : Lens.t _ V) f r g R_src R_tgt
    (Q : R_src -> R_tgt -> iProp)
    ps pt ktr_src itr_tgt st v
    :
    (Vw_src st l v)
    -∗ (Vw_src st l (f v) -∗ stsim E r g Q true pt (ktr_src tt) itr_tgt)
    -∗ stsim E r g Q ps pt (trigger (map_lens l (Modify f)) >>= ktr_src) itr_tgt.
  Proof.
    rewrite map_lens_Modify.
    iIntros "H1 H2". iApply (stsim_modifyL with "H1").
    iIntros "H". iApply "H2".
    unfold Lens.modify.
    rewrite Lens.view_set. rewrite Lens.set_set.
    iApply "H".
  Qed.

  Lemma stsim_modifyR E f r g R_src R_tgt
    (Q : R_src -> R_tgt -> iProp)
    ps pt itr_src ktr_tgt st_tgt
    :
    (St_tgt st_tgt)
    -∗ (St_tgt (f st_tgt) -∗ stsim E r g Q ps true itr_src (ktr_tgt tt))
    -∗ stsim E r g Q ps pt itr_src (trigger (Modify f) >>= ktr_tgt).
  Proof.
    rewrite Modify_State. iIntros "H1 H2". iApply (stsim_stateR with "H1"). ss.
  Qed.

  Lemma stsim_lens_modifyR E V (l : Lens.t _ V) f r g R_src R_tgt
    (Q : R_src -> R_tgt -> iProp)
    ps pt itr_src ktr_tgt st v
    :
    (Vw_tgt st l v)
    -∗ (Vw_tgt st l (f v) -∗ stsim E r g Q ps true itr_src (ktr_tgt tt))
    -∗ stsim E r g Q ps pt itr_src (trigger (map_lens l (Modify f)) >>= ktr_tgt).
  Proof.
    rewrite map_lens_Modify.
    iIntros "H1 H2". iApply (stsim_modifyR with "H1").
    iIntros "H". iApply "H2".
    unfold Lens.modify.
    rewrite Lens.view_set. rewrite Lens.set_set.
    iApply "H".
  Qed.

  Lemma stsim_tidL E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src itr_tgt
    :
    (stsim E r g Q true pt (ktr_src tid) itr_tgt)
      -∗
      (stsim E r g Q ps pt (trigger GetTid >>= ktr_src) itr_tgt)
  .
  Proof.
    unfold stsim. iIntros "H" (? ? ? ? ?) "D".
    iApply isim_tidL. iApply ("H" with "D").
  Qed.

  Lemma stsim_tidR E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt itr_src ktr_tgt
    :
    (stsim E r g Q ps true itr_src (ktr_tgt tid))
      -∗
      (stsim E r g Q ps pt itr_src (trigger GetTid >>= ktr_tgt))
  .
  Proof.
    unfold stsim. iIntros "H" (? ? ? ? ?) "D".
    iApply isim_tidR. iApply ("H" with "D").
  Qed.

  Lemma stsim_fairL_prism o
        A lf ls
        (p : Prism.t _ A)
        E fm r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src itr_tgt
        (FAIL: forall i (IN: fm i = Flag.fail), List.In i lf)
        (SUCCESS: forall i (IN: List.In i ls), fm i = Flag.success)
    :
    (list_prop_sum (fun i => FairRA.white p i Ord.one) lf)
      -∗
      ((list_prop_sum (fun i => FairRA.white p i o) ls) -∗ (stsim E r g Q true pt (ktr_src tt) itr_tgt))
      -∗
      (stsim E r g Q ps pt (trigger (Fair (prism_fmap p fm)) >>= ktr_src) itr_tgt).
  Proof.
    unfold stsim. iIntros "OWN H" (? ? ? ? ?) "(D & C & E)".
    iPoseProof (default_I_past_update_ident_source_prism with "D OWN") as "> [% [[% WHITES] D]]".
    { eauto. }
    { eauto. }
    iPoseProof ("H" with "WHITES [D C E]") as "H".
    { iFrame. }
    iApply isim_fairL. iExists _. iSplit; eauto.
  Qed.

  Lemma stsim_fairL o lf ls
        E fm r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src itr_tgt
        (FAIL: forall i (IN: fm i = Flag.fail), List.In i lf)
        (SUCCESS: forall i (IN: List.In i ls), fm i = Flag.success)
    :
    (list_prop_sum (fun i => FairRA.white Prism.id i Ord.one) lf)
      -∗
      ((list_prop_sum (fun i => FairRA.white Prism.id i o) ls) -∗ (stsim E r g Q true pt (ktr_src tt) itr_tgt))
      -∗
      (stsim E r g Q ps pt (trigger (Fair fm) >>= ktr_src) itr_tgt).
  Proof.
    iIntros "WHITES K".
    rewrite <- (prism_fmap_id fm).
    iApply (stsim_fairL_prism with "[WHITES] [K]"); eauto.
  Qed.

  Lemma stsim_fairR_prism A lf ls
        (p : Prism.t _ A)
        E fm r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt itr_src ktr_tgt
        (SUCCESS: forall i (IN: fm i = Flag.success), List.In i (List.map fst ls))
        (FAIL: forall i (IN: List.In i lf), fm i = Flag.fail)
        (NODUP: List.NoDup lf)
    :
    (list_prop_sum (fun '(i, l) => ObligationRA.duty (Prism.compose inrp p) i l ** ObligationRA.tax l) ls)
      -∗
      ((list_prop_sum (fun '(i, l) => ObligationRA.duty (Prism.compose inrp p) i l) ls)
         -*
         (list_prop_sum (fun i => FairRA.white (Prism.compose inrp p) i 1) lf)
         -*
         stsim E r g Q ps true itr_src (ktr_tgt tt))
      -∗
      (stsim E r g Q ps pt itr_src (trigger (Fair (prism_fmap p fm)) >>= ktr_tgt))
  .
  Proof.
    unfold stsim. iIntros "OWN H"  (? ? ? ? ?) "(D & C & E)".
    iApply isim_fairR. iIntros (?) "%".
    iPoseProof (default_I_past_update_ident_target with "D OWN") as "> [[DUTY WHITE] D]".
    { rewrite prism_fmap_compose. eauto. }
    { eauto. }
    { eauto. }
    { eauto. }
    iApply ("H" with "DUTY WHITE"). iFrame.
  Qed.

  Lemma stsim_fairR lf ls
        E fm r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt itr_src ktr_tgt
        (SUCCESS: forall i (IN: fm i = Flag.success), List.In i (List.map fst ls))
        (FAIL: forall i (IN: List.In i lf), fm i = Flag.fail)
        (NODUP: List.NoDup lf)
    :
    (list_prop_sum (fun '(i, l) => ObligationRA.duty inrp i l ** ObligationRA.tax l) ls)
      -∗
      ((list_prop_sum (fun '(i, l) => ObligationRA.duty inrp i l) ls)
         -*
         (list_prop_sum (fun i => FairRA.white inrp i 1) lf)
         -*
         stsim E r g Q ps true itr_src (ktr_tgt tt))
      -∗
      (stsim E r g Q ps pt itr_src (trigger (Fair fm) >>= ktr_tgt))
  .
  Proof.
    iIntros "DUTY K".
    rewrite <- (prism_fmap_id fm).
    iApply (stsim_fairR_prism with "[DUTY] [K]"); eauto.
  Qed.

  Lemma stsim_fairR_simple lf ls
        E fm r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt itr_src ktr_tgt
        (SUCCESS: forall i (IN: fm i = Flag.success), List.In i ls)
        (FAIL: forall i (IN: List.In i lf), fm i = Flag.fail)
        (NODUP: List.NoDup lf)
    :
    (list_prop_sum (fun i => FairRA.black_ex inrp i 1) ls)
      -∗
      ((list_prop_sum (fun i => FairRA.black_ex inrp i 1) ls)
         -*
         (list_prop_sum (fun i => FairRA.white inrp i 1) lf)
         -*
         stsim E r g Q ps true itr_src (ktr_tgt tt))
      -∗
      (stsim E r g Q ps pt itr_src (trigger (Fair fm) >>= ktr_tgt))
  .
  Proof.
    iIntros "A B". iApply (stsim_fairR with "[A]"); eauto.
    { instantiate (1:= List.map (fun i => (i, [])) ls). i. specialize (SUCCESS _ IN). rewrite List.map_map. ss.
      replace (List.map (λ x : ident_tgt, x) ls) with ls; auto. clear. induction ls; ss; eauto. f_equal. auto.
    }
    { iApply list_prop_sum_map. 2: iFrame. i. ss. iIntros "BLK". iSplitL; auto. iApply ObligationRA.black_to_duty. auto. }
    { iIntros "S F". iApply ("B" with "[S]"). 2: iFrame. iApply list_prop_sum_map_inv. 2: iFrame.
      i; ss. iIntros "D". iApply ObligationRA.duty_to_black. iFrame.
    }
  Qed.

  Lemma stsim_UB E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src itr_tgt
    :
    ⊢ (stsim E r g Q ps pt (trigger Undefined >>= ktr_src) itr_tgt)
  .
  Proof.
    unfold stsim. iIntros (? ? ? ? ?) "D".
    iApply isim_UB. auto.
  Qed.

  Lemma stsim_observe E fn args r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src ktr_tgt
    :
    (∀ ret, stsim E g g Q true true (ktr_src ret) (ktr_tgt ret))
      -∗
      (stsim E r g Q ps pt (trigger (Observe fn args) >>= ktr_src) (trigger (Observe fn args) >>= ktr_tgt))
  .
  Proof.
    unfold stsim. iIntros "H" (? ? ? ? ?) "D".
    iApply isim_observe. iIntros (?). iApply ("H" with "D").
  Qed.

  Lemma stsim_yieldL E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src ktr_tgt
    :
    (stsim E r g Q true pt (ktr_src tt) (trigger (Yield) >>= ktr_tgt))
      -∗
      (stsim E r g Q ps pt (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt))
  .
  Proof.
    unfold stsim. iIntros "H" (? ? ? ? ?) "D".
    iApply isim_yieldL. iApply ("H" with "D").
  Qed.

  Lemma stsim_yieldR_strong E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src ktr_tgt l
    :
    (ObligationRA.duty inlp tid l ** ObligationRA.tax l)
      -∗
      ((ObligationRA.duty inlp tid l)
         -*
         (FairRA.white_thread (S:=_))
         -*
         (FUpd (fairI (ident_tgt:=ident_tgt)) E ⊤
               (stsim ⊤ r g Q ps true (trigger (Yield) >>= ktr_src) (ktr_tgt tt))))
      -∗
      (stsim E r g Q ps pt (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt))
  .
  Proof.
    iIntros "H K".
    unfold stsim. iIntros (? ? ? ? ?) "(D & C & E)".
    iPoseProof (default_I_past_update_ident_thread with "D H") as "> [[B W] [[[[[[D0 D1] D2] D3] D4] D5] D6]]".
    iAssert ((fairI (ident_tgt:=ident_tgt)) ** (wsat ** OwnE E)) with "[C D5 D6 E]" as "C".
    { iFrame. }
    iPoseProof ("K" with "B W C") as "> [D5 [D6 [E K]]]".
    iApply isim_yieldR. unfold I, fairI. iFrame. iFrame.
    iIntros (? ? ? ? ? ?) "(D & C & E) %".
    iApply ("K" with "[D C E]"). iFrame. iExists _. eauto.
  Qed.

  Lemma stsim_sync_strong E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src ktr_tgt l
    :
    (ObligationRA.duty inlp tid l ** ObligationRA.tax l)
      -∗
      ((ObligationRA.duty inlp tid l)
         -*
         (FairRA.white_thread (S:=_))
         -*
         (FUpd (fairI (ident_tgt:=ident_tgt)) E ⊤
               (stsim ⊤ g g Q true true (ktr_src tt) (ktr_tgt tt))))
      -∗
      (stsim E r g Q ps pt (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt)).
  Proof.
    iIntros "H K".
    unfold stsim. iIntros (? ? ? ? ?) "(D & C & E)".
    iPoseProof (default_I_past_update_ident_thread with "D H") as "> [[B W] [[[[[[D0 D1] D2] D3] D4] D5] D6]]".
    iAssert ((fairI (ident_tgt:=ident_tgt)) ** (wsat ** OwnE E)) with "[C D5 D6 E]" as "C".
    { iFrame. }
    iPoseProof ("K" with "B W C") as "> (D5 & C & E & K)".
    iApply isim_sync. unfold I. iFrame. iFrame.
    iIntros (? ? ? ? ? ?) "(D & C & E) %".
    iApply ("K" with "[D C E]"). iFrame. iExists _. eauto.
  Qed.

  Lemma stsim_yieldR E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src ktr_tgt l
        (TOP: ⊤ ⊆ E)
    :
    (ObligationRA.duty inlp tid l ** ObligationRA.tax l)
      -∗
      ((ObligationRA.duty inlp tid l)
         -*
         (FairRA.white_thread (S:=_))
         -*
         stsim ⊤ r g Q ps true (trigger (Yield) >>= ktr_src) (ktr_tgt tt))
      -∗
      (stsim E r g Q ps pt (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt))
  .
  Proof.
    iIntros "H K". iApply stsim_discard; [eassumption|].
    iApply (stsim_yieldR_strong with "H"). iIntros "DUTY WHITE".
    iModIntro. iApply ("K" with "DUTY WHITE").
  Qed.

  Lemma stsim_sync E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src ktr_tgt l
        (TOP: ⊤ ⊆ E)
    :
    (ObligationRA.duty inlp tid l ** ObligationRA.tax l)
      -∗
      ((ObligationRA.duty inlp tid l)
         -*
         (FairRA.white_thread (S:=_))
         -*
         stsim ⊤ g g Q true true (ktr_src tt) (ktr_tgt tt))
      -∗
      (stsim E r g Q ps pt (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt)).
  Proof.
    iIntros "H K". iApply stsim_discard; [eassumption|].
    iApply (stsim_sync_strong with "H"). iIntros "DUTY WHITE".
    iModIntro. iApply ("K" with "DUTY WHITE").
  Qed.

  (* Note:  *)
  (*   MUpd _ fairI topset topset P *)
  (*        is a generalized version of I * (I -* P) *)
  Lemma stsim_yieldR_simple r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src ktr_tgt
    :
    FUpd (fairI (ident_tgt:=ident_tgt)) ⊤ ⊤
         ((FairRA.black_ex inlp tid 1)
            **
            ((FairRA.black_ex inlp tid 1)
               -*
               (FairRA.white_thread (S:=_))
               -*
               stsim ⊤ r g Q ps true (trigger (Yield) >>= ktr_src) (ktr_tgt tt)))
         -∗
         (stsim ⊤ r g Q ps pt (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt))
  .
  Proof.
    iIntros "> [H K]". iApply (stsim_yieldR with "[H]").
    { auto. }
    { iPoseProof (ObligationRA.black_to_duty with "H") as "H". iFrame. }
    iIntros "B W". iApply ("K" with "[B] [W]"); ss.
    { iApply ObligationRA.duty_to_black. auto. }
  Qed.

  Lemma stsim_sync_simple r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src ktr_tgt
    :
    FUpd (fairI (ident_tgt:=ident_tgt)) ⊤ ⊤
         ((FairRA.black_ex inlp tid 1)
            **
            ((FairRA.black_ex inlp tid 1)
               -*
               (FairRA.white_thread (S:=_))
               -*
               stsim ⊤ g g Q true true (ktr_src tt) (ktr_tgt tt)))
      -∗
      (stsim ⊤ r g Q ps pt (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt)).
  Proof.
    iIntros "> [H K]". iApply (stsim_sync with "[H]").
    { auto. }
    { iPoseProof (ObligationRA.black_to_duty with "H") as "H". iFrame. }
    iIntros "B W". iApply ("K" with "[B] [W]"); ss.
    { iApply ObligationRA.duty_to_black. auto. }
  Qed.

  Lemma stsim_reset E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt itr_src itr_tgt
    :
    (stsim E r g Q false false itr_src itr_tgt)
      -∗
      (stsim E r g Q ps pt itr_src itr_tgt)
  .
  Proof.
    unfold stsim. iIntros "H" (? ? ? ? ?) "D".
    iApply isim_reset. iApply ("H" with "D").
  Qed.

  Lemma stsim_progress E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        itr_src itr_tgt
    :
    (stsim E g g Q false false itr_src itr_tgt)
      -∗
      (stsim E r g Q true true itr_src itr_tgt)
  .
  Proof.
    unfold stsim. iIntros "H" (? ? ? ? ?) "D".
    iApply isim_progress. iApply ("H" with "D").
  Qed.

  Definition ibot5 { T0 T1 T2 T3 T4} (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) (x4: T4 x0 x1 x2 x3): iProp := False.
  Definition ibot7 { T0 T1 T2 T3 T4 T5 T6} (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) (x4: T4 x0 x1 x2 x3) (x5: T5 x0 x1 x2 x3 x4) (x6: T6 x0 x1 x2 x3 x4 x5): iProp := False.

End STATE.

From Fairness Require Export Red IRed.

Ltac lred := repeat (prw _red_gen 1 2 0).
Ltac rred := repeat (prw _red_gen 1 1 0).

From Fairness Require Export LinkingRed.

Ltac lred2 := (prw ltac:(red_tac itree_class) 1 2 0).
Ltac rred2 := (prw ltac:(red_tac itree_class) 1 1 0).
