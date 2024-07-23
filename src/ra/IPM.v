From sflib Require Import sflib.
From Fairness Require Import PCM ITreeLib IProp.

Set Implicit Arguments.

From iris.bi Require Import derived_connectives derived_laws updates.
From iris.prelude Require Import options.
From iris.proofmode Require Export tactics.
From iris.algebra Require Import cmra updates proofmode_classes.
Arguments Z.of_nat: simpl nomatch.

Require Import Program.

Section IPM.
  Context {Σ: GRA.t}.

  (* Trivial Ofe Structure *)
  Inductive uPred_equiv' (P Q : (@iProp' Σ)) : Prop :=
    { uPred_in_equiv : ∀ x, ✓ x -> P x <-> Q x }.

  Local Instance uPred_equiv : Equiv iProp' := uPred_equiv'.
  Definition uPred_dist' (n : nat) (P Q : iProp') : Prop := uPred_equiv' P Q.
  Local Instance uPred_dist : Dist iProp' := uPred_dist'.
  Definition uPred_ofe_mixin : OfeMixin iProp'.
  Proof.
    split.
    - intros P Q; split.
      + ii. ss.
      + ii. specialize (H 0). ss.
    - i. split.
      + ii. ss.
      + ii. econs. i. symmetry. apply H. auto.
      + ii. econs. i. transitivity (y x0); [apply H|apply H0]; ss.
    - i. ss.
  Qed.
  Canonical Structure uPredO : ofe := Ofe iProp' uPred_ofe_mixin.

  Program Definition uPred_compl : Compl uPredO := λ c, iProp_intro (fun x => forall n, c n x) _.
  Next Obligation.
    i. ss. i. eapply iProp_mono; eauto.
  Qed.

  Global Program Instance uPred_cofe : Cofe uPredO := {| compl := uPred_compl |}.
  Next Obligation.
    econs. i. split.
    - ii. exploit H0; eauto.
    - ii. destruct (le_ge_dec n n0).
      + apply c in l. apply l in H0; eauto.
      + apply c in g. apply g in H0; eauto.
  Qed.

  Lemma iProp_bi_mixin:
    BiMixin
      Entails Emp Pure And Or Impl
      (@Univ _) (@Ex _) Sepconj Wand
      Persistently.
  Proof.
    econs.
    - exact PreOrder_Entails.
    - econs.
      { uipropall. ii. split; ii; eapply H; eauto. }
      { uipropall. i. econs. i. des. split; i.
        { eapply H; eauto. }
        { eapply H1; eauto. }
      }
    - econs. i. split.
      { uipropall. ii. eapply H. ss. }
      { uipropall. ii. eapply H. ss. }
    - econs. i. split.
      { uipropall. ii. inv H2. split.
        { eapply H; eauto. }
        { eapply H0; eauto. }
      }
      { uipropall. ii. inv H2. split.
        { eapply H; eauto. }
        { eapply H0; eauto. }
      }
    - econs. i. split.
      { uipropall. ii. inv H2.
        { left. eapply H; eauto. }
        { right. eapply H0; eauto. }
      }
      { uipropall. ii. inv H2.
        { left. eapply H; eauto. }
        { right. eapply H0; eauto. }
      }
    - econs. i. split.
      { uipropall. ii. eapply H0; eauto. eapply H2; eauto. eapply H; eauto. }
      { uipropall. ii. eapply H0; eauto. eapply H2; eauto. eapply H; eauto. }
    - econs. i. split.
      { uipropall. ii. exploit H; eauto. i. eapply x3; eauto. }
      { uipropall. ii. exploit H; eauto. i. eapply x3; eauto. }
    - econs. i. split.
      { uipropall. ii. inv H1. exploit H; eauto. i. eexists. eapply x3; eauto. }
      { uipropall. ii. inv H1. exploit H; eauto. i. eexists. eapply x3; eauto. }
    - econs. i. split.
      { uipropall. ii. inv H2. des. subst. eexists. esplits; eauto.
        { eapply H; eauto. eapply cmra_valid_op_l. rewrite H3 in H1. eauto. }
        { eapply H0; eauto. eapply cmra_valid_op_r. rewrite H3 in H1. eauto. }
      }
      { uipropall. ii. inv H2. des. subst. eexists. esplits; eauto.
        { eapply H; eauto. eapply cmra_valid_op_l. rewrite H3 in H1. eauto. }
        { eapply H0; eauto. eapply cmra_valid_op_r. rewrite H3 in H1. eauto. }
      }
    - econs. uipropall. i. split.
      { ii. exploit H2; eauto.
        { eapply H; eauto. eapply cmra_valid_op_r. eauto. }
        { i. eapply H0; eauto. }
      }
      { ii. exploit H2; eauto.
        { eapply H; eauto. eapply cmra_valid_op_r. eauto. }
        { i. eapply H0; eauto. }
      }
    - ii. econs. uipropall. i. split.
      { ii. eapply H; ss. apply cmra_core_valid. auto. }
      { ii. eapply H; ss. apply cmra_core_valid. auto. }
    - exact Pure_intro.
    - exact Pure_elim.
    - exact And_elim_l.
    - exact And_elim_r.
    - exact And_intro.
    - exact Or_intro_l.
    - exact Or_intro_r.
    - exact Or_elim.
    - exact Impl_intro_r.
    - exact Impl_elim_l.
    - exact Univ_intro.
    - exact Univ_elim.
    - exact Ex_intro.
    - exact Ex_elim.
    - exact Sepconj_mono.
    - exact Emp_Sepconj_l.
    - exact Emp_Sepconj_r.
    - exact Sepconj_comm.
    - exact Sepconj_assoc.
    - exact Wand_intro_r.
    - exact Wand_elim_l.
    - exact Persistently_mono.
    - exact Persistently_idem.
    - exact Persistently_emp.
    - exact Persistently_and.
    - exact Persistently_ex.
    - exact Persistently_sep.
    - exact Persistently_sep_and.
  Qed.

  Lemma iProp_bi_later_mixin:
    BiLaterMixin
      Entails Pure Or Impl
      (@Univ _) (@Ex _) Sepconj Persistently Later.
  Proof.
    eapply bi.interface.bi_later_mixin_id.
    { intros []. uipropall. }
    apply iProp_bi_mixin.
  Qed.

  Canonical Structure iProp: bi :=
    {| bi_bi_mixin := iProp_bi_mixin;
       bi_bi_later_mixin := iProp_bi_later_mixin |}.

  Definition OwnM (M: ucmra) `{@GRA.inG M Σ} (r: M): iProp := Own (GRA.embed r).

  (** extra BI instances *)
  Lemma iProp_bupd_mixin: BiBUpdMixin iProp Upd.
  Proof.
    econs.
    - ii. econs. unfold bupd. uipropall. i. split.
      { ii. exploit H1; eauto. i. des. esplits; eauto.
        eapply H; eauto. eapply cmra_valid_op_l. eauto. }
      { ii. exploit H1; eauto. i. des. esplits; eauto.
        eapply H; eauto. eapply cmra_valid_op_l. eauto. }
    - exact Upd_intro.
    - exact Upd_mono.
    - exact Upd_trans.
    - exact Upd_frame_r.
  Qed.
  Global Instance iProp_bi_bupd: BiBUpd iProp := {| bi_bupd_mixin := iProp_bupd_mixin |}.

  Global Instance iProp_absorbing (P: iProp): Absorbing P.
  Proof.
    rr. uipropall. i. rr in H. uipropall. des. eapply iProp_mono; eauto.
    eapply iProp_mono; [done| |exact H1].
    exists a. rewrite H. by rewrite (comm op).
  Qed.

  Global Instance iProp_affine (P: iProp): Affine P.
  Proof.
    rr. uipropall. i. rr. uipropall.
  Qed.

  Global Instance iProp_timeless (P: iProp): Timeless P.
  Proof.
    rr. uipropall. i. rr. uipropall. rr in H. uipropall. by right.
  Qed.

  Global Instance iProp_is_excpet_0 (P: iProp): IsExcept0 P.
  Proof.
    rr. uipropall. i. rr. uipropall. rr in H. uipropall. des; [|done].
    rr in H. uipropall. rr in H. uipropall.
  Qed.

  Global Instance iProp_pure_forall: BiPureForall iProp.
  Proof.
    ii. rr. uipropall. i. rr. rr in H. uipropall.
    i. specialize (H a). rr in H. uipropall.
  Qed.

  Global Instance iProp_bi_affine : BiAffine (iProp) | 0.
  Proof. exact iProp_affine. Qed.

  Global Instance iProp_bi_persistently_forall : BiPersistentlyForall iProp.
  Proof.
    ii. rr. uipropall. i. rr. rr in H. uipropall.
    i. rr. uipropall. i. specialize (H x). rr in H. uipropall.
  Qed.

End IPM.
Global Arguments iProp : clear implicits.

Global Hint Immediate iProp_bi_affine : core.
Arguments OwnM: simpl never.

Section TEST.
  Context {Σ: GRA.t}.
  Notation iProp := (iProp Σ).

  Goal forall (P Q R: iProp) (PQ: P -∗ Q) (QR: Q -∗ R), P -∗ R.
  Proof.
    i. iStartProof. iIntros "H".
    iApply QR. iApply PQ. iApply "H".
  Qed.

  Goal forall (P Q: iProp), ((bupd P) ∗ Q) -∗ (bupd Q).
  Proof.
    i. iStartProof.
    iIntros "[Hxs Hys]". iMod "Hxs". iApply "Hys".
  Qed.
End TEST.

Notation "#=> P" := ((@bupd (bi_car (iProp _)) (@bi_bupd_bupd (iProp _) iProp_bi_bupd)) P) (at level 99).

Section IUPD.
  Context {Σ: GRA.t}.
  Notation iProp := (iProp Σ).

  Definition IUpd (I: iProp): iProp -> iProp :=
    fun P => (I -∗ #=> (I ∗ P))%I.

  Lemma IUpd_intro I: forall P, P ⊢ IUpd I P.
  Proof.
    ii. iIntros "H INV". iModIntro. iFrame.
  Qed.

  Lemma IUpd_mono I: forall P Q, (P ⊢ Q) -> (IUpd I P ⊢ IUpd I Q).
  Proof.
    ii. unfold IUpd. iIntros "H INV".
    iPoseProof ("H" with "INV") as "> [H0 H1]". iModIntro.
    iFrame. iApply H. auto.
  Qed.

  Lemma IUpd_trans I: forall P, (IUpd I (IUpd I P)) ⊢ (IUpd I P).
  Proof.
    ii. unfold IUpd. iIntros "H INV".
    iPoseProof ("H" with "INV") as "> [H0 H1]".
    iApply "H1". auto.
  Qed.

  Lemma IUpd_frame_r I: forall P R, ((IUpd I P) ∗ R) ⊢ (IUpd I (P ∗ R)).
  Proof.
    ii. unfold IUpd. iIntros "[H0 H1] INV".
    iPoseProof ("H0" with "INV") as "> [H0 H2]".
    iModIntro. iFrame.
  Qed.

  Lemma Upd_IUpd I: forall P, #=> P ⊢ (IUpd I P).
  Proof.
    ii. unfold IUpd. iIntros "H INV". iFrame.
  Qed.

  Lemma iProp_bupd_mixin_IUpd I: BiBUpdMixin iProp (IUpd I).
  Proof.
    econs.
    - ii. unfold bupd. unfold IUpd. rewrite H. auto.
    - apply IUpd_intro.
    - apply IUpd_mono.
    - apply IUpd_trans.
    - apply IUpd_frame_r.
  Qed.
  Global Instance iProp_bi_bupd_IUpd I: BiBUpd iProp := {| bi_bupd_mixin := iProp_bupd_mixin_IUpd I |}.
End IUPD.
Notation "#=( Q )=> P" := ((@bupd (bi_car (iProp _)) (@bi_bupd_bupd (iProp _) (iProp_bi_bupd_IUpd Q))) P) (at level 99).
Notation "P =( I ) =∗ Q" := (P ⊢ #=( I )=> Q) (only parsing, at level 99) : stdpp_scope.
Notation "P =( I )=∗ Q" := (P -∗ #=( I )=> Q)%I (at level 99): bi_scope.

#[export] Hint Unfold bi_entails bi_sep bi_and bi_or bi_wand bupd bi_bupd_bupd: iprop.

Section class_instances.
  Context `{Σ: GRA.t}.
  Notation iProp := (iProp Σ).

  Global Instance Own_proper :
    Proper ((≡) ==> (⊣⊢)) (@Own Σ).
  Proof.
    intros x y EQ. uipropall. split. ss. by setoid_rewrite EQ.
  Qed.

  Lemma Own_op (a1 a2: Σ) :
    (Own (a1 ⋅ a2)) ⊣⊢ (Own a1 ∗ Own a2).
  Proof.
    uipropall. split. simpl. intros x WFx. split.
    - intros [z ?]; exists (a1), (a2 ⋅ z).
      split; [by rewrite (assoc op)|].
      split.
      + by exists ε; rewrite right_id.
      + by exists z.
    - intros (y1&y2&Hx&[z1 Hy1]&[z2 Hy2]); exists (z1 ⋅ z2).
      by rewrite (assoc op _ z1) -(comm op z1) (assoc op z1)
          -(assoc op _ a2) (comm op z1) -Hy1 -Hy2.
  Qed.

  Lemma Own_valid (a : Σ) :
    Own a -∗ ⌜✓a⌝.
  Proof.
    rr. uipropall. i. red. rr. uipropall.
    by eapply cmra_valid_included; [exact WF|].
  Qed.

  Global Instance from_sep_own (a b1 b2 : Σ) :
    IsOp a b1 b2 →
    FromSep (Own a) (Own b1) (Own b2).
  Proof. intros. by rewrite /FromSep -Own_op -is_op. Qed.

  Global Instance into_and_own p (a b1 b2 : Σ) :
    IsOp a b1 b2 → IntoAnd p (Own a) (Own b1) (Own b2).
  Proof. intros. by rewrite /IntoAnd (is_op a) Own_op bi.sep_and. Qed.

  Global Instance into_sep_own (a b1 b2 : Σ) :
    IsOp a b1 b2 → IntoSep (Own a) (Own b1) (Own b2).
  Proof. intros. by rewrite /IntoSep (is_op a) Own_op. Qed.

  Lemma OwnM_op (M: ucmra) `{@GRA.inG M Σ} (a1 a2: M) :
    (OwnM (a1 ⋅ a2)) ⊣⊢ (OwnM a1 ∗ OwnM a2).
  Proof. by rewrite /OwnM -GRA.embed_add Own_op. Qed.

  Global Instance OwnM_proper (M: ucmra) `{@GRA.inG M Σ} :
    Proper ((≡) ==> (⊣⊢)) (@OwnM Σ M _).
  Proof. intros x y EQ. by rewrite /OwnM EQ. Qed.

  Global Instance from_sep_ownM (M: ucmra) `{@GRA.inG M Σ} (a b1 b2 : M) :
    IsOp a b1 b2 →
    FromSep (OwnM a) (OwnM b1) (OwnM b2).
  Proof. intros. by rewrite /FromSep -OwnM_op -is_op. Qed.

  Global Instance into_and_ownM (M: ucmra) `{@GRA.inG M Σ} p (a b1 b2 : M) :
    IsOp a b1 b2 → IntoAnd p (OwnM a) (OwnM b1) (OwnM b2).
  Proof. intros. by rewrite /IntoAnd (is_op a) OwnM_op bi.sep_and. Qed.

  Global Instance into_sep_ownM (M: ucmra) `{@GRA.inG M Σ} (a b1 b2 : M) :
    IsOp a b1 b2 → IntoSep (OwnM a) (OwnM b1) (OwnM b2).
  Proof. intros. by rewrite /IntoSep (is_op a) OwnM_op. Qed.
End class_instances.



Section ILEMMAS.
  Context `{Σ: GRA.t}.
  Notation iProp := (iProp Σ).

  Lemma from_semantic (a: Σ) (P: iProp') (SAT: P a)
    :
      Own a ⊢ #=> P.
  Proof.
    uipropall. ss. i. exists r. split; [done|].
    eapply iProp_mono; [| |exact SAT]; done.
  Qed.

  Lemma to_semantic (a: Σ) (P: iProp') (SAT: Own a ⊢ P) (WF: ✓ a)
    :
      P a.
  Proof. uipropall. eapply SAT; eauto. Qed.

  Lemma OwnM_valid (M: ucmra) `{@GRA.inG M Σ} (m: M):
    OwnM m -∗ ⌜✓ m⌝.
  Proof.
    iIntros "H". iDestruct (Own_valid with "H") as %WF.
    iPureIntro. eapply GRA.embed_wf. done.
  Qed.

  Lemma Upd_Pure P
    :
      #=> (⌜P⌝ : iProp) ⊢ ⌜P⌝.
  Proof.
    rr. uipropall. i. rr. uipropall.
    hexploit (H ε).
    { by rewrite right_id. }
    i. des. rr in H1. uipropall.
  Qed.

  Lemma Own_Upd_set
        (r1: Σ) B
        (UPD: r1 ~~>: B)
    :
      (Own r1) ⊢ (#=> (∃ b, ⌜B b⌝ ∗ (Own b)))
  .
  Proof.
    cut (Entails (Own r1) (Upd (Ex (fun b => Sepconj (Pure (B b)) (Own b))))); ss.
    uipropall. i. red in H. des. rewrite H in H0.
    exploit (UPD 0 (Some (z ⋅ ctx))).
    { simpl. apply cmra_valid_validN. rewrite (assoc op). done. }
    i. des. exists (y ⋅ z). split.
    { apply cmra_discrete_valid in x1.  rewrite -(assoc op). eauto. }
    { exists y. uipropall. esplits; [|auto|reflexivity].
      eapply (comm op). }
  Qed.

  Lemma Own_Upd
        (r1 r2: Σ)
        (UPD: r1 ~~> r2)
    :
      (Own r1) ⊢ (#=> (Own r2))
  .
  Proof.
    iStartProof. iIntros "H".
    iAssert (#=> (∃ b, ⌜((eq r2) b)⌝ ∗ (Own b)))%I with "[H]" as "H".
    { iApply Own_Upd_set; [|iFrame].
      red. red in UPD. i. hexploit UPD; eauto. }
    iMod "H". iDestruct "H" as (b) "[#H0 H1]".
    iPure "H0" as Hs. subst. iApply "H1".
  Qed.

  Lemma Own_extends
        (a b: Σ)
        (EXT: a ≼ b)
    :
      Own b ⊢ Own a
  .
  Proof.
    red. uipropall. ii. etrans; eauto.
  Qed.

  Lemma Own_persistently (r : Σ) : Own r ⊢ <pers> Own (core r).
  Proof.
    uipropall. i. rr; uipropall. apply cmra_core_mono. ss.
  Qed.

  Lemma OwnM_persistently {M : ucmra} `{@GRA.inG M Σ} (r : M) : OwnM r ⊢ <pers> OwnM (core r).
  Proof.
    unfold OwnM. rewrite GRA.embed_core. apply Own_persistently.
  Qed.

  Lemma OwnM_unit {M : ucmra} `{@GRA.inG M Σ} : ⊢ OwnM ε.
  Proof.
    rr; uipropall. i. rr; uipropall. rr. exists r.
    rewrite GRA.embed_unit. rewrite left_id. ss.
  Qed.

  Lemma OwnM_Upd_set (M: ucmra) `{IN: @GRA.inG M Σ}
        (r1: M) B
        (UPD: r1 ~~>: B)
    :
      (OwnM r1) ⊢ (#=> (∃ b, ⌜B b⌝ ∗ (OwnM b)))
  .
  Proof.
    iIntros "H".
    iPoseProof (Own_Upd_set with "H") as "> H".
    { eapply GRA.embed_updatable_set. apply UPD. }
    iDestruct "H" as (b) "[%Hm H1]". destruct Hm as [m [? ?]]. subst.
    iModIntro. iExists m. iFrame. ss.
  Qed.

  Lemma OwnM_Upd (M: ucmra) `{@GRA.inG M Σ}
        (r1 r2: M)
        (UPD: r1 ~~> r2)
    :
      (OwnM r1) ⊢ (#=> (OwnM r2))
  .
  Proof.
    iStartProof. iIntros "H".
    iAssert (#=> (∃ b, ⌜((eq r2) b)⌝ ∗ (OwnM b)))%I with "[H]" as "H".
    { iApply OwnM_Upd_set; [|iFrame].
      red. red in UPD. i. hexploit UPD; eauto. }
    iMod "H". iDestruct "H" as (b) "[#H0 H1]".
    iPure "H0" as Hs. subst. iApply "H1".
  Qed.

  Lemma OwnM_extends (M: ucmra) `{@GRA.inG M Σ}
        (a b: M)
        (EXT: a ≼ b)
    :
      OwnM b ⊢ OwnM a
  .
  Proof.
    red. unfold OwnM. uipropall. i. unfold included in *.
    des. setoid_rewrite H0. setoid_rewrite EXT.
    eexists. rewrite -GRA.embed_add.
    rewrite -(assoc op). eauto.
  Qed.

  Lemma IUpd_unfold (I P : iProp)
    :
    #=(I)=> P ⊢ (I -∗ #=> (I ∗ P)).
  Proof.
    reflexivity.
  Qed.

  Lemma IUpd_fold (I P : iProp)
    :
    (I -∗ #=> (I ∗ P)) ⊢ #=(I)=> P.
  Proof.
    reflexivity.
  Qed.

  Definition SubIProp P Q: iProp :=
    Q -∗ #=> (P ∗ (P -∗ #=> Q)).

  Lemma SubIProp_refl P
    :
    ⊢ SubIProp P P.
  Proof.
    iIntros "H". iFrame. auto.
  Qed.

  Lemma SubIProp_trans P Q R
    :
    (SubIProp P Q)
      -∗
      (SubIProp Q R)
      -∗
      (SubIProp P R).
  Proof.
    iIntros "H0 H1 H2".
    iPoseProof ("H1" with "H2") as "> [H1 H2]".
    iPoseProof ("H0" with "H1") as "> [H0 H1]".
    iFrame. iModIntro. iIntros "H".
    iPoseProof ("H1" with "H") as "> H".
    iPoseProof ("H2" with "H") as "H". auto.
  Qed.

  Lemma SubIProp_sep_l P Q
    :
    ⊢ (SubIProp P (P ∗ Q)).
  Proof.
    iIntros "[H0 H1]". iFrame. auto.
  Qed.

  Lemma SubIProp_sep_r P Q
    :
    ⊢ (SubIProp Q (P ∗ Q)).
  Proof.
    iIntros "[H0 H1]". iFrame. auto.
  Qed.

  Lemma IUpd_sub_mon P Q R
    :
    (SubIProp P Q)
      -∗
      (#=(P)=> R)
      -∗
      (#=(Q)=> R).
  Proof.
    iIntros "H0 H1 H2".
    iPoseProof (IUpd_unfold with "H1") as "H1".
    iPoseProof ("H0" with "H2") as "> [H0 H2]".
    iPoseProof ("H1" with "H0") as "> [H0 H1]".
    iPoseProof ("H2" with "H0") as "H0". iFrame. auto.
  Qed.
End ILEMMAS.

Global Instance upd_elim_iupd `{Σ : GRA.t} (I P Q : iProp Σ)
       `{ElimModal _ True false false (#=(I)=> P) P Q R}
  :
  ElimModal True false false (#=> P) P Q R.
Proof.
  unfold ElimModal. i. iIntros "[H0 H1]".
  iPoseProof (Upd_IUpd with "H0") as "> H0". iApply "H1". auto.
Qed.

Global Instance iupd_elim_upd `{Σ : GRA.t} (I P Q : iProp Σ) b
  :
  ElimModal True b false (#=> P) P (#=(I)=> Q) (#=(I)=> Q).
Proof.
  unfold ElimModal. i. iIntros "[H0 H1]".
  iPoseProof (Upd_IUpd with "H0") as "H0".
  iIntros "H". iPoseProof ("H0" with "H") as "> [H0 H2]".
  destruct b; ss.
  { iPoseProof ("H2") as "# > H2". iPoseProof ("H1" with "H2") as "H".
    iApply ("H" with "H0").
  }
  { iPoseProof ("H2") as "> H2". iPoseProof ("H1" with "H2") as "H".
    iApply ("H" with "H0").
  }
Qed.

Global Instance subiprop_elim_upd `{Σ : GRA.t} (I J P Q : iProp Σ) b
  :
  ElimModal True b false ((SubIProp I J) ∗ #=(I)=> P) P (#=(J)=> Q) (#=(J)=> Q).
Proof.
  rewrite /ElimModal bi.intuitionistically_if_elim.
  iIntros (_) "[[SUB P] K] J".
  iMod ("SUB" with "J") as "[I IJ]". iMod ("P" with "I") as "[I P]".
  iMod ("IJ" with "I") as "J". iPoseProof ("K" with "P J") as "K". iFrame.
Qed.

Ltac iOwnWf' H :=
  iPoseProof (OwnM_valid with H) as "%".

Tactic Notation "iOwnWf" constr(H) :=
  iOwnWf' H.

Tactic Notation "iOwnWf" constr(H) "as" ident(WF) :=
  iOwnWf' H;
  match goal with
  | H0: @valid _ _ _ |- _ => rename H0 into WF
  end
.

Section AUX.

  Context {Σ: GRA.t}.
  Notation iProp := (iProp Σ).

  Fixpoint sep_conjs (Ps : nat -> iProp) (n : nat) : iProp :=
    match n with
    | O => emp%I
    | S m => ((sep_conjs Ps m) ∗ (Ps m))%I
    end.

End AUX.
