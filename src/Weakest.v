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

  Variable I: shared_rel.

  Program Definition isim (tid: thread_id) (R_src R_tgt: Type)
          (Q: R_src -> R_tgt -> shared_rel):
    itree srcE R_src -> itree tgtE R_tgt -> shared_rel :=
    fun itr_src itr_tgt ths im_src im_tgt st_src st_tgt =>
      iProp_intro
        (fun r =>
           forall r_ctx (WF: URA.wf (r ⋅ r_ctx)),
             lsim (lift I) tid (liftRR Q) false false r_ctx itr_src itr_tgt (ths, im_src, im_tgt, st_src, st_tgt)) _.
  Next Obligation.
  Proof.
    ii. ss. eapply H.
    eapply URA.wf_extends; eauto. eapply URA.extends_add; eauto.
  Qed.

  Tactic Notation "muclo" uconstr(H) :=
    eapply gpaco9_uclo; [auto with paco|apply H|].


  Lemma isim_mono tid R_src R_tgt
        (Q0 Q1: R_src -> R_tgt -> shared_rel)
        (MONO: forall r_src r_tgt ths im_src im_tgt st_src st_tgt,
            bi_entails
              (Q0 r_src r_tgt ths im_src im_tgt st_src st_tgt)
              (Q1 r_src r_tgt ths im_src im_tgt st_src st_tgt))
        itr_src itr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (isim tid Q0 itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
      (isim tid Q1 itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    rr. autorewrite with iprop. i.
    ii. exploit H; eauto. i.
    ginit.
    eapply gpaco9_uclo; [auto with paco|apply lsim_monoC_spec|].
    econs.
    { instantiate (1:=liftRR Q0). unfold liftRR. i. des_ifs.
      des. esplits; eauto. hexploit MONO; eauto.
      intros ENT. rr in ENT. autorewrite with iprop in ENT.
      eapply ENT; eauto. eapply URA.wf_mon. eauto.
    }
    { gfinal. right. eauto. }
  Qed.

  Lemma isim_upd tid R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        itr_src itr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (#=> (isim tid Q itr_src itr_tgt ths im_src im_tgt st_src st_tgt))
      (isim tid Q itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    rr. autorewrite with iprop. i.
    rr in H. autorewrite with iprop in H.
    ii. hexploit H; eauto. i. des. eauto.
  Qed.

  Lemma isim_wand tid R_src R_tgt
        (Q0 Q1: R_src -> R_tgt -> shared_rel)
        itr_src itr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      ((∀ r_src r_tgt ths im_src im_tgt st_src st_tgt,
           ((Q0 r_src r_tgt ths im_src im_tgt st_src st_tgt) -∗ (Q1 r_src r_tgt ths im_src im_tgt st_src st_tgt))) ** (isim tid Q0 itr_src itr_tgt ths im_src im_tgt st_src st_tgt))
      (isim tid Q1 itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    rr. autorewrite with iprop. i.
    rr in H. autorewrite with iprop in H. des. subst.
    ii. ginit.
    eapply gpaco9_uclo; [auto with paco|apply lsim_frameC_spec|].
    econs.
    instantiate (1:=a).
    eapply gpaco9_uclo; [auto with paco|apply lsim_monoC_spec|].
    econs.
    2:{ gfinal. right. eapply H1. r_wf WF0. }
    unfold liftRR. i. subst. des_ifs.
    des. exists (r ⋅ a). esplits; eauto.
    { r_wf WF1. }
    { rr in H0. autorewrite with iprop in H0. specialize (H0 r_src).
      rr in H0. autorewrite with iprop in H0. specialize (H0 r_tgt).
      rr in H0. autorewrite with iprop in H0. specialize (H0 t).
      rr in H0. autorewrite with iprop in H0. specialize (H0 i0).
      rr in H0. autorewrite with iprop in H0. specialize (H0 i).
      rr in H0. autorewrite with iprop in H0. specialize (H0 s0).
      rr in H0. autorewrite with iprop in H0. specialize (H0 s).
      rr in H0. autorewrite with iprop in H0.
      hexploit (H0 r); eauto.
      { eapply URA.wf_mon. instantiate (1:=r_ctx'). r_wf WF1. }
      { i. rewrite URA.add_comm. auto. }
    }
  Qed.

  Lemma isim_bind tid R_src R_tgt S_src S_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        (itr_src: itree srcE S_src) (itr_tgt: itree tgtE S_tgt)
        ktr_src ktr_tgt
        ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (isim tid (fun s_src s_tgt ths im_src im_tgt st_src st_tgt =>
                   isim tid Q (ktr_src s_src) (ktr_tgt s_tgt) ths im_src im_tgt st_src st_tgt) itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
      (isim tid Q (itr_src >>= ktr_src) (itr_tgt >>= ktr_tgt) ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    rr. autorewrite with iprop. i.
    ii. ginit.
    eapply gpaco9_uclo; [auto with paco|apply lsim_bindC_spec|].
    econs.
    eapply gpaco9_uclo; [auto with paco|apply lsim_monoC_spec|].
    econs.
    2:{ gfinal. right. eapply H; eauto. }
    unfold liftRR. i. des_ifs. des.
    eapply gpaco9_uclo; [auto with paco|apply lsim_monoC_spec|].
    econs.
    2:{ gfinal. right. eapply RET0; eauto. }
    unfold liftRR. i. des_ifs.
  Qed.

  Lemma isim_ret tid R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        r_src r_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (Q r_src r_tgt ths im_src im_tgt st_src st_tgt)
      (isim tid Q (Ret r_src) (Ret r_tgt) ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    rr. autorewrite with iprop. i.
    ii. ginit. muclo lsim_indC_spec.
    eapply lsim_ret. unfold liftRR. esplits; eauto.
  Qed.

  Lemma isim_tauL tid R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        itr_src itr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (isim tid Q itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
      (isim tid Q (Tau itr_src) itr_tgt ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    rr. autorewrite with iprop. i.
    ii. ginit. muclo lsim_indC_spec.
    eapply lsim_tauL. gfinal. right.
    eapply lsim_reset_prog; eauto.
  Qed.

  Lemma isim_tauR tid R_src R_tgt
        (Q: R_src -> R_tgt -> shared_rel)
        itr_src itr_tgt ths im_src im_tgt st_src st_tgt
    :
    bi_entails
      (isim tid Q itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
      (isim tid Q itr_src (Tau itr_tgt) ths im_src im_tgt st_src st_tgt)
  .
  Proof.
    rr. autorewrite with iprop. i.
    ii. ginit. muclo lsim_indC_spec.
    eapply lsim_tauR. gfinal. right.
    eapply lsim_reset_prog; eauto.
  Qed.

End SIM.
