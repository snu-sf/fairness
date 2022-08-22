From sflib Require Import sflib.
From Paco Require Import paco.
From Fairness Require Import PCM ITreeLib IProp IPM ModSim ModSimNat.

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

  Let lift (R: shared_rel): (TIdSet.t *
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

  Let coind :=  (bool * bool * rel * rel)%type.

  Let gf := (fun r => pind9 (__lsim (lift I) tid r) top9).
  Let gf_mon: monotone9 gf.
  Proof.
    eapply lsim_mon.
  Qed.
  Hint Resolve gf_mon: paco.

  Program Definition unlift (r: rel):
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
    (fun R_src R_tgt RR ps pt r_ctx itr_src itr_tgt '(ths, im_src, im_tgt, st_src, st_tgt) => exists r_own,
         (<<WF: URA.wf (r_own ⋅ r_ctx)>>) /\
           (<<SAT: @r _ _ (fun r_src r_tgt ths im_src im_tgt st_src st_tgt =>
                             @iProp_intro _ (fun r_own => forall (r_ctx: Σ) (WF: URA.wf (r_own ⋅ r_ctx)),                                                                                     RR r_src r_tgt r_ctx (ths, im_src, im_tgt, st_src, st_tgt)) _) itr_src itr_tgt ths im_src im_tgt st_src st_tgt r_own>>)).
  Next Obligation.
  Proof.
    i. ss. i. eapply H.
    eapply URA.wf_extends; eauto. eapply URA.extends_add; eauto.
  Qed.

  Program Definition isim: coind -> rel :=
    fun
      '(ps, pt, r, g)
      R_src R_tgt Q itr_src itr_tgt ths im_src im_tgt st_src st_tgt =>
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

  Lemma isim_mono ps pt r g R_src R_tgt
        (Q0 Q1: R_src -> R_tgt -> shared_rel)
        (MONO: forall r_src r_tgt ths im_src im_tgt st_src st_tgt,
            bi_entails
              (Q0 r_src r_tgt ths im_src im_tgt st_src st_tgt)
              (#=> (Q1 r_src r_tgt ths im_src im_tgt st_src st_tgt)))
        itr_src itr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (isim (ps, pt, r, g) Q0 itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
      (isim (ps, pt, r, g) Q1 itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    rr. autorewrite with iprop. i.
    ii. exploit H; eauto. i.
    eapply gpaco9_uclo; [auto with paco|apply lsim_monoC_spec|].
    econs; [|eapply x0].
    unfold liftRR. i. des_ifs.
    des. hexploit MONO; eauto.
    intros ENT. rr in ENT. autorewrite with iprop in ENT.
    hexploit (ENT r1); eauto.
    { eapply URA.wf_mon. eauto. }
    i. rr in H0. autorewrite with iprop in H0.
    hexploit (H0 r_ctx0); eauto.
  Qed.

  Lemma isim_upd ps pt r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        itr_src itr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (#=> (isim (ps, pt, r, g) Q itr_src itr_tgt ths im_src im_tgt st_src st_tgt))
      (isim (ps, pt, r, g) Q itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    rr. autorewrite with iprop. i.
    rr in H. autorewrite with iprop in H.
    ii. hexploit H; eauto. i. des. eauto.
  Qed.

  Lemma isim_reset ps0 pt0 ps1 pt1 r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        itr_src itr_tgt ths im_src im_tgt st_src st_tgt
        (PS: ps0 = true -> ps1 = true)
        (PT: pt0 = true -> pt1 = true)
    :
    bi_entails
      (isim (ps0, pt0, r, g) Q itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
      (isim (ps1, pt1, r, g) Q itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    rr. autorewrite with iprop. i.
    ii. muclo lsim_resetC_spec.
    econs; eauto.
  Qed.

  Lemma isim_wand ps pt r g R_src R_tgt
        (Q0 Q1: R_src -> R_tgt -> shared_rel)
        itr_src itr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      ((∀ r_src r_tgt ths im_src im_tgt st_src st_tgt,
           ((Q0 r_src r_tgt ths im_src im_tgt st_src st_tgt) -∗ (Q1 r_src r_tgt ths im_src im_tgt st_src st_tgt))) ** (isim (ps, pt, r, g) Q0 itr_src itr_tgt ths im_src im_tgt st_src st_tgt))
      (isim (ps, pt, r, g) Q1 itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
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
    unfold liftRR. i. subst. des_ifs.
    des. exists (r0 ⋅ a). esplits; eauto.
    { r_wf WF1. }
    { rr in H0. autorewrite with iprop in H0. specialize (H0 r_src).
      rr in H0. autorewrite with iprop in H0. specialize (H0 r_tgt).
      rr in H0. autorewrite with iprop in H0. specialize (H0 t).
      rr in H0. autorewrite with iprop in H0. specialize (H0 i0).
      rr in H0. autorewrite with iprop in H0. specialize (H0 i).
      rr in H0. autorewrite with iprop in H0. specialize (H0 s0).
      rr in H0. autorewrite with iprop in H0. specialize (H0 s).
      rr in H0. autorewrite with iprop in H0.
      hexploit (H0 r0); eauto.
      { eapply URA.wf_mon. instantiate (1:=r_ctx'). r_wf WF1. }
      { i. rewrite URA.add_comm. auto. }
    }
  Qed.

  Lemma isim_bind ps pt r g R_src R_tgt S_src S_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        (itr_src: itree srcE S_src) (itr_tgt: itree tgtE S_tgt)
        ktr_src ktr_tgt
        ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (isim (ps, pt, r, g) (fun s_src s_tgt ths im_src im_tgt st_src st_tgt =>
                   isim (false, false, r, g) Q (ktr_src s_src) (ktr_tgt s_tgt) ths im_src im_tgt st_src st_tgt) itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
      (isim (ps, pt, r, g) Q (itr_src >>= ktr_src) (itr_tgt >>= ktr_tgt) ths im_src im_tgt st_src st_tgt)
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

  Lemma isim_progress r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        itr_src itr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (isim (false, false, g, g) Q itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
      (isim (true, true, r, g) Q itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    rr. autorewrite with iprop.
    ii. gstep. rr. eapply pind9_fold.
    eapply lsim_progress; eauto.
  Qed.

  Lemma isim_ret ps pt r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        r_src r_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (Q r_src r_tgt ths im_src im_tgt st_src st_tgt)
      (isim (ps, pt, r, g) Q (Ret r_src) (Ret r_tgt) ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    rr. autorewrite with iprop. i.
    ii. muclo lsim_indC_spec.
    eapply lsim_ret. unfold liftRR. esplits; eauto.
  Qed.

  Lemma isim_tauL ps pt r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        itr_src itr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (isim (true, pt, r, g) Q itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
      (isim (ps, pt, r, g) Q (Tau itr_src) itr_tgt ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    rr. autorewrite with iprop. i.
    ii. muclo lsim_indC_spec.
    eapply lsim_tauL. eapply H; eauto.
  Qed.

  Lemma isim_tauR ps pt r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        itr_src itr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (isim (ps, true, r, g) Q itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
      (isim (ps, pt, r, g) Q itr_src (Tau itr_tgt) ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    rr. autorewrite with iprop. i.
    ii. muclo lsim_indC_spec.
    eapply lsim_tauR. eapply H; eauto.
  Qed.

  Lemma isim_chooseL X ps pt r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        ktr_src itr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (∃ x, isim (true, pt, r, g) Q (ktr_src x) itr_tgt ths im_src im_tgt st_src st_tgt)
      (isim (ps, pt, r, g) Q (trigger (Choose X) >>= ktr_src) itr_tgt ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    rr. autorewrite with iprop. i.
    ii. muclo lsim_indC_spec.
    eapply lsim_chooseL.
    rr in H. autorewrite with iprop in H. des.
    esplits; eauto.
  Qed.

  Lemma isim_chooseR X ps pt r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        itr_src ktr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (∀ x, isim (ps, true, r, g) Q itr_src (ktr_tgt x) ths im_src im_tgt st_src st_tgt)
      (isim (ps, pt, r, g) Q itr_src (trigger (Choose X) >>= ktr_tgt) ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    rr. autorewrite with iprop. i.
    ii. muclo lsim_indC_spec.
    eapply lsim_chooseR.
    rr in H. autorewrite with iprop in H.
    i. eapply H; eauto.
  Qed.

  Lemma isim_putL st ps pt r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        ktr_src itr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (isim (true, pt, r, g) Q (ktr_src tt) itr_tgt ths im_src im_tgt st st_tgt)
      (isim (ps, pt, r, g) Q (trigger (Put st) >>= ktr_src) itr_tgt ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    rr. autorewrite with iprop. i.
    ii. muclo lsim_indC_spec.
    eapply lsim_putL. eapply H; eauto.
  Qed.

  Lemma isim_putR st ps pt r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        itr_src ktr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (isim (ps, true, r, g) Q itr_src (ktr_tgt tt) ths im_src im_tgt st_src st)
      (isim (ps, pt, r, g) Q itr_src (trigger (Put st) >>= ktr_tgt) ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    rr. autorewrite with iprop. i.
    ii. muclo lsim_indC_spec.
    eapply lsim_putR. eapply H; eauto.
  Qed.

  Lemma isim_getL ps pt r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        ktr_src itr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (isim (true, pt, r, g) Q (ktr_src st_src) itr_tgt ths im_src im_tgt st_src st_tgt)
      (isim (ps, pt, r, g) Q (trigger (@Get _) >>= ktr_src) itr_tgt ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    rr. autorewrite with iprop. i.
    ii. muclo lsim_indC_spec.
    eapply lsim_getL. eapply H; eauto.
  Qed.

  Lemma isim_getR ps pt r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        itr_src ktr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (isim (ps, true, r, g) Q itr_src (ktr_tgt st_tgt) ths im_src im_tgt st_src st_tgt)
      (isim (ps, pt, r, g) Q itr_src (trigger (@Get _) >>= ktr_tgt) ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    rr. autorewrite with iprop. i.
    ii. muclo lsim_indC_spec.
    eapply lsim_getR. eapply H; eauto.
  Qed.

  Lemma isim_tidL ps pt r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        ktr_src itr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (isim (true, pt, r, g) Q (ktr_src tid) itr_tgt ths im_src im_tgt st_src st_tgt)
      (isim (ps, pt, r, g) Q (trigger GetTid >>= ktr_src) itr_tgt ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    rr. autorewrite with iprop. i.
    ii. muclo lsim_indC_spec.
    eapply lsim_tidL. eapply H; eauto.
  Qed.

  Lemma isim_tidR ps pt r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        itr_src ktr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (isim (ps, true, r, g) Q itr_src (ktr_tgt tid) ths im_src im_tgt st_src st_tgt)
      (isim (ps, pt, r, g) Q itr_src (trigger GetTid >>= ktr_tgt) ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    rr. autorewrite with iprop. i.
    ii. muclo lsim_indC_spec.
    eapply lsim_tidR. eapply H; eauto.
  Qed.

  Lemma isim_fairL f ps pt r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        ktr_src itr_tgt ths im_src0 im_tgt st_src st_tgt
    :
    bi_entails
      (∃ im_src1, ⌜fair_update im_src0 im_src1 f⌝ ∧ isim (true, pt, r, g) Q (ktr_src tt) itr_tgt ths im_src1 im_tgt st_src st_tgt)
      (isim (ps, pt, r, g) Q (trigger (Fair f) >>= ktr_src) itr_tgt ths im_src0 im_tgt st_src st_tgt)
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

  Lemma isim_fairR f ps pt r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        itr_src ktr_tgt ths im_src im_tgt0 st_src st_tgt
    :
    bi_entails
      (∀ im_tgt1, ⌜fair_update im_tgt0 im_tgt1 (sum_fmap_r f)⌝ -* isim (ps, true, r, g) Q itr_src (ktr_tgt tt) ths im_src im_tgt1 st_src st_tgt)
      (isim (ps, pt, r, g) Q itr_src (trigger (Fair f) >>= ktr_tgt) ths im_src im_tgt0 st_src st_tgt)
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
    i. eapply H1; eauto. rewrite URA.unit_id. auto.
  Qed.

  Lemma isim_UB ps pt r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        ktr_src itr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (True)
      (isim (ps, pt, r, g) Q (trigger Undefined >>= ktr_src) itr_tgt ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    rr. autorewrite with iprop. i.
    ii. muclo lsim_indC_spec.
    eapply lsim_UB.
  Qed.

  Lemma isim_observe fn args ps pt r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        ktr_src ktr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (∀ ret, isim (true, true, g, g) Q (ktr_src ret) (ktr_tgt ret) ths im_src im_tgt st_src st_tgt)
      (isim (ps, pt, r, g) Q (trigger (Observe fn args) >>= ktr_src) (trigger (Observe fn args) >>= ktr_tgt) ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    rr. autorewrite with iprop. i.
    ii. gstep. rr. eapply pind9_fold.
    eapply lsim_observe; eauto.
    i. rr in H. autorewrite with iprop in H.
    eapply H; eauto.
  Qed.

  Lemma isim_yieldL ps pt r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        ktr_src ktr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (isim (true, pt, r, g) Q (ktr_src tt) (trigger (Yield) >>= ktr_tgt) ths im_src im_tgt st_src st_tgt)
      (isim (ps, pt, r, g) Q (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt) ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    rr. autorewrite with iprop. i.
    ii. muclo lsim_indC_spec.
    eapply lsim_yieldL. eapply H; eauto.
  Qed.

  Lemma isim_yieldR ps pt r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        ktr_src ktr_tgt ths0 im_src0 im_tgt0 st_src0 st_tgt0
    :
    bi_entails
      (I ths0 im_src0 im_tgt0 st_src0 st_tgt0 ** (∀ ths1 im_src1 im_tgt1 st_src1 st_tgt1 im_tgt2, I ths1 im_src1 im_tgt1 st_src1 st_tgt1 -* ⌜fair_update im_tgt1 im_tgt2 (sum_fmap_l (tids_fmap tid ths1))⌝ -* isim (ps, true, r, g) Q (trigger (Yield) >>= ktr_src) (ktr_tgt tt) ths1 im_src1 im_tgt2 st_src1 st_tgt1))
      (isim (ps, pt, r, g) Q (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt) ths0 im_src0 im_tgt0 st_src0 st_tgt0)
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
    i. eapply H2. r_wf VALID.
  Qed.

  Lemma isim_sync ps pt r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        ktr_src ktr_tgt ths0 im_src0 im_tgt0 st_src0 st_tgt0
    :
    bi_entails
      (I ths0 im_src0 im_tgt0 st_src0 st_tgt0 ** (∀ ths1 im_src1 im_tgt1 st_src1 st_tgt1 im_tgt2, I ths1 im_src1 im_tgt1 st_src1 st_tgt1 -* ⌜fair_update im_tgt1 im_tgt2 (sum_fmap_l (tids_fmap tid ths1))⌝ -* isim (true, true, g, g) Q (ktr_src tt) (ktr_tgt tt) ths1 im_src1 im_tgt2 st_src1 st_tgt1))
      (isim (ps, pt, r, g) Q (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt) ths0 im_src0 im_tgt0 st_src0 st_tgt0)
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
    i. eapply H2. r_wf VALID.
  Qed.

  Variant unlift2 (r: rel):
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
    | unlift2_intro
        ps pt
        R_src R_tgt Q itr_src itr_tgt ths im_src im_tgt st_src st_tgt r_ctx r_own
        (REL: r R_src R_tgt Q itr_src itr_tgt ths im_src im_tgt st_src st_tgt r_own)
        (WF: URA.wf (r_own ⋅ r_ctx))
      :
      unlift2 r (liftRR Q) ps pt r_ctx itr_src itr_tgt (ths, im_src, im_tgt, st_src, st_tgt)
  .

  Lemma isim_base ps pt r g R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        itr_src itr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (@r _ _ Q itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
      (isim (ps, pt, r, g) Q itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    rr. autorewrite with iprop.
    ii. gbase.

    unfold liftRR. rr. esplits. eauto.

  (* H : r R_src R_tgt Q itr_src itr_tgt ths im_src im_tgt st_src st_tgt r0 *)
  (* r_ctx : Σ *)
  (* WF0 : URA.wf (r0 ⋅ r_ctx) *)
  (* ============================ *)
  (* unlift r (liftRR Q) ps pt r_ctx itr_src itr_tgt *)
  (*   (ths, im_src, im_tgt, st_src, st_tgt) *)

  Admitted.

  Lemma isim_mono_knowledge (r0 g0 r1 g1: rel) ps pt R_src R_tgt
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
      (isim (ps, pt, r0, g0) Q itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
      (isim (ps, pt, r1, g1) Q itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
  .
  Proof.
  Admitted.

  Ltac espc H :=
    let T := fresh "T" in
    evar (T: Type);
    let x := fresh "x" in
    evar (x: T);
    specialize (H x); subst T; subst x.

  Tactic Notation "rspc" constr(H) := rr in H; autorewrite with iprop in H; espc H.
  Ltac rspc := rr; autorewrite with iprop.

  Lemma unlift_mon (r0 r1: rel)
        (MON: forall R_src R_tgt (Q: R_src -> R_tgt -> shared_rel)
                     itr_src itr_tgt ths im_src im_tgt st_src st_tgt,
            bi_entails
              (@r0 _ _ Q itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
              (#=> (@r1 _ _ Q itr_src itr_tgt ths im_src im_tgt st_src st_tgt)))
    :
    unlift r0 <9= unlift r1.
  Admitted.

  Lemma isim_coind' A
        (ps: forall (a: A), bool)
        (pt: forall (a: A), bool)
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
    :
    bi_entails
      (∀ (g1: rel) a,
          P a -*
            (□(∀ R_src R_tgt (Q: R_src -> R_tgt -> shared_rel)
                itr_src itr_tgt ths im_src im_tgt st_src st_tgt,
                 @g0 R_src R_tgt Q itr_src itr_tgt ths im_src im_tgt st_src st_tgt -* @g1 R_src R_tgt Q itr_src itr_tgt ths im_src im_tgt st_src st_tgt)) -*
            (□(∀ a,
                 P a -* @g1 (R_src a) (R_tgt a) (Q a) (itr_src a) (itr_tgt a) (ths a) (im_src a) (im_tgt a) (st_src a) (st_tgt a))) -*
            isim (ps a, pt a, r, g1) (Q a) (itr_src a) (itr_tgt a) (ths a) (im_src a) (im_tgt a) (st_src a) (st_tgt a))
      (∀ a, P a -* isim (ps a, pt a, r, g0) (Q a) (itr_src a) (itr_tgt a) (ths a) (im_src a) (im_tgt a) (st_src a) (st_tgt a))
  .
  Proof.
    rr. autorewrite with iprop. i.
    rr. autorewrite with iprop. i.
    rr. autorewrite with iprop.
    revert x. gcofix CIH. i. eapply gpaco9_gpaco.
    { auto with paco. }
    epose (fun R_src R_tgt (Q: R_src -> R_tgt -> shared_rel)
               itr_src itr_tgt ths im_src im_tgt st_src st_tgt =>
             @iProp_intro _ (fun r_own => forall r_ctx (WF: URA.wf (r_own ⋅ r_ctx)),
                                 gpaco9 gf (cpn9 gf) r1 r1 R_src R_tgt (liftRR Q) false false r_ctx itr_src itr_tgt (ths, im_src, im_tgt, st_src, st_tgt)) _).
    rr in H. autorewrite with iprop in H. specialize (H i). subst i.
    rspc H.
    rr in H. autorewrite with iprop in H.
    hexploit H; eauto. clear H. i.
    rr in H. autorewrite with iprop in H.
    hexploit (H URA.unit); eauto.
    { r_wf H1. }
    { rr. autorewrite with iprop. split.
      { rr. autorewrite with iprop. auto. }
      rr. autorewrite with iprop.
      do 11 (rr; autorewrite with iprop; i).
      rewrite URA.unit_core. rewrite URA.unit_idl.
      ss. i. gbase. eapply CIH0.
      (* rr. esplits. eauto. eauto. *)

      (* rr in H3. autorewrite with iprop in H3. *)
      (* hexploit H3; eauto. i. des. *)


      (* muclo lsim_monoC_spec. econs. *)
      (* 2:{ gbase. eapply CIH0. *)
      (*     rr. esplits. eauto. eauto. *)

      (* g0 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 rp0 -> forall r_ctx (WF: URA.wf (rp0 ⋅ r_ctx0)), unlift g0 (liftRR x2) false false r_ctx0 x3 x4 (x5, x6, x7, x8, x9) *)
      admit.
    } clear H.
    i. rr in H. autorewrite with iprop in H.
    hexploit (H URA.unit); eauto.
    { r_wf H1. }
    { rr. autorewrite with iprop. split.
      { rr. autorewrite with iprop. auto. }
      rr. autorewrite with iprop.
      do 2 (rr; autorewrite with iprop; i).
      rewrite URA.unit_core. rewrite URA.unit_idl.
      ss. i.
      hexploit CIH.
      2:{ eauto. }
      { admit. }
      { admit. }
      i. muclo lsim_resetC_spec. econs.
      { gbase. eauto. }
      { admit. }
      { admit. }
    }
    i. eapply gpaco9_mon.
    { eapply H0. r_wf WF0. }
    { i. gbase. eauto. }
    { i. gbase. left. eapply CIH0.
      eapply unlift_mon; [|eauto].
      i. ss. rr. autorewrite with iprop. i.
      ss. rr. autorewrite with iprop. i.
      esplits. eauto.



      rr. eapply
      admit. }
  Qed.


  Lemma isim_coind A
        (ps: forall (a: A), bool)
        (pt: forall (a: A), bool)
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
    :
    bi_entails
      (∀ (g1: rel) a,
          P a -*
            (□(∀ R_src R_tgt (Q: R_src -> R_tgt -> shared_rel)
                itr_src itr_tgt ths im_src im_tgt st_src st_tgt,
                 @g0 R_src R_tgt Q itr_src itr_tgt ths im_src im_tgt st_src st_tgt -* @g1 R_src R_tgt Q itr_src itr_tgt ths im_src im_tgt st_src st_tgt)) -*
            (□(∀ a,
                 P a -* @g1 (R_src a) (R_tgt a) (Q a) (itr_src a) (itr_tgt a) (ths a) (im_src a) (im_tgt a) (st_src a) (st_tgt a))) -*
            isim (ps a, pt a, r, g1) (Q a) (itr_src a) (itr_tgt a) (ths a) (im_src a) (im_tgt a) (st_src a) (st_tgt a))
      (∀ a, P a -* isim (ps a, pt a, r, g0) (Q a) (itr_src a) (itr_tgt a) (ths a) (im_src a) (im_tgt a) (st_src a) (st_tgt a))
  .
  Proof.
    rr. autorewrite with iprop. i.
    rr. autorewrite with iprop. i.
    rr. autorewrite with iprop.
    revert x. gcofix CIH. i.
    rspc H. rspc H.
    rr in H. autorewrite with iprop in H.
    hexploit H; eauto. clear H. i.
    rr in H. autorewrite with iprop in H.
    hexploit (H URA.unit); eauto.
    { r_wf H1. }
    { rr. autorewrite with iprop. split.
      { rr. autorewrite with iprop. auto. }
      rr. autorewrite with iprop.
      do 11 (rr; autorewrite with iprop; i).
      rewrite URA.unit_core. rewrite URA.unit_idl.
      instantiate (1:=fun R_src R_tgt (Q: R_src -> R_tgt -> shared_rel)
                          itr_src itr_tgt ths im_src im_tgt st_src st_tgt =>
                        r1 ? false false
                  ).

      instantiate (1:=lift r1).
      eapply H3.

    } clear H.
    i. rr in H. autorewrite with iprop in H.
    hexploit (H URA.unit); eauto.
    { r_wf H1. }
    { rr. autorewrite with iprop. split.
      { rr. autorewrite with iprop. auto. }
      rr. autorewrite with iprop.
      do 2 (rr; autorewrite with iprop; i).
      rewrite URA.unit_core. rewrite URA.unit_idl.
      admit.
    }
    i. eapply gpaco9_mon.
    { eapply H0. r_wf WF0. }
    { i. eauto. }
    { eapply CIH0. }
  Qed.

    rr in H0. eapply gpaco9_mon.
    { eapply H0.


    eapply H0.

    i.

    {




ss.      rewrite URA.unit_id.

      rr. autorewrite with iprop. i.
      rr. autorewrite with iprop. i.
      rr. autorewrite with iprop. i.
      rr. autorewrite with iprop. i.
      rr. autorewrite with iprop. i.
      rr. autorewrite with iprop. i.
      rr. autorewrite with iprop. i.
      rr. autorewrite with iprop. i.
      rr. autorewrite with iprop. i.
      r

      split.
      {


      instantiate (1:=r1).

      instantiate (1:=r1).

    2:{
      i. rr in H0. autorewrite with iprop in H0.
      hexploit H0.

    clear H. i.

    ; [|eauto|..]; eauto. clear H. i.



    { admit. }
    { eauto. }


    espc H.
    rr in H. autorewrite with iprop in H. espc H.
    rr in H.

    ;


      evar (T: Type).
    specialize (H
    s

    i.


  Admitted.
End SIM.
