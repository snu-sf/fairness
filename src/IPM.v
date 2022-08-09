From sflib Require Import sflib.
From Fairness Require Import PCM ITreeLib IProp.

Set Implicit Arguments.

From iris.bi Require Import derived_connectives updates.
From iris.prelude Require Import options.
From iris.proofmode Require Export tactics.
From Fairness Require Export DisableSsreflect.
Arguments Z.of_nat: simpl nomatch.

Require Import Program.

Section IPM.
  Context {Σ: GRA.t}.

  (* Trivial Ofe Structure *)
  Inductive uPred_equiv' (P Q : iProp') : Prop :=
    { uPred_in_equiv : ∀ x, URA.wf x -> P x <-> Q x }.

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
        { eapply H; eauto. eapply URA.wf_mon; eauto. }
        { eapply H0; eauto. eapply URA.wf_mon; eauto. rewrite URA.add_comm. eauto. }
      }
      { uipropall. ii. inv H2. des. subst. eexists. esplits; eauto.
        { eapply H; eauto. eapply URA.wf_mon; eauto. }
        { eapply H0; eauto. eapply URA.wf_mon; eauto. rewrite URA.add_comm. eauto. }
      }
    - econs. uipropall. i. split.
      { ii. exploit H2; eauto.
        { eapply H; eauto. eapply URA.wf_mon; eauto. rewrite URA.add_comm. eauto. }
        { i. eapply H0; eauto. }
      }
      { ii. exploit H2; eauto.
        { eapply H; eauto. eapply URA.wf_mon; eauto. rewrite URA.add_comm. eauto. }
        { i. eapply H0; eauto. }
      }
    - ii. econs. uipropall. i. split.
      { ii. eapply H; ss. eapply URA.wf_core. auto. }
      { ii. eapply H; ss. eapply URA.wf_core. auto. }
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
    econs.
    - ii. uipropall. rr. split. ii. ss. apply H. auto.
    - ii. uipropall.
    - ii. uipropall.
    - ii. uipropall. ii. specialize (H x). uipropall.
    - ii. uipropall. ii. right. des. exists x. uipropall.
    - ii. uipropall.
    - ii. uipropall.
    - ii. uipropall.
    - ii. uipropall.
    - ii. uipropall. ii. right. ss.
  Qed.

  Canonical Structure iProp: bi :=
    {| bi_bi_mixin := iProp_bi_mixin;
       bi_bi_later_mixin := iProp_bi_later_mixin |}.

  Definition OwnM (M: URA.t) `{@GRA.inG M Σ} (r: M): iProp := Own (GRA.embed r).

  (** extra BI instances *)
  Lemma iProp_bupd_mixin: BiBUpdMixin iProp Upd.
  Proof.
    econs.
    - ii. econs. unfold bupd. uipropall. i. split.
      { ii. exploit H1; eauto. i. des. esplits; eauto.
        eapply H; eauto. eapply URA.wf_mon; eauto. }
      { ii. exploit H1; eauto. i. des. esplits; eauto.
        eapply H; eauto. eapply URA.wf_mon; eauto. }
    - exact Upd_intro.
    - exact Upd_mono.
    - exact Upd_trans.
    - exact Upd_frame_r.
  Qed.
  Global Instance iProp_bi_bupd: BiBUpd iProp := {| bi_bupd_mixin := iProp_bupd_mixin |}.

  Global Instance iProp_absorbing (P: iProp): Absorbing P.
  Proof.
    rr. uipropall. i. rr in H. uipropall. des. eapply iProp_mono; eauto.
    exists a. rewrite H. r_solve.
  Qed.

  Global Instance iProp_pure_forall: BiPureForall iProp.
  Proof.
    ii. rr. uipropall. i. rr. rr in H. uipropall.
    i. specialize (H a). rr in H. uipropall.
  Qed.
End IPM.
Arguments OwnM: simpl never.

Section TEST.
  Context {Σ: GRA.t}.

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

Infix "⊢" := (@bi_entails iProp).
Infix "**" := bi_sep (at level 99).
Infix "-*" := bi_wand (at level 99, right associativity).
Notation "#=> P" := ((@bupd (bi_car (@iProp _)) (@bi_bupd_bupd (@iProp _) (@iProp_bi_bupd _))) P) (at level 99).

Class IsOp {A : URA.t} (a b1 b2 : A) := is_op : a = b1 ⋅ b2.
Global Arguments is_op {_} _ _ _ {_}.
Global Hint Mode IsOp + - - - : typeclass_instances.

Global Instance is_op_op {A : URA.t} (a b : A) : IsOp (URA.add a b) a b | 100.
Proof. by rewrite /IsOp. Qed.

Class IsOp' {A : URA.t} (a b1 b2 : A) := is_op' :> IsOp a b1 b2.
Global Hint Mode IsOp' + ! - - : typeclass_instances.
Global Hint Mode IsOp' + - ! ! : typeclass_instances.

Class IsOp'LR {A : URA.t} (a b1 b2 : A) := is_op_lr : IsOp a b1 b2.
Existing Instance is_op_lr | 0.
Global Hint Mode IsOp'LR + ! - - : typeclass_instances.
Global Instance is_op_lr_op {A : URA.t} (a b : A) : IsOp'LR (URA.add a b) a b | 0.
Proof. by rewrite /IsOp'LR /IsOp. Qed.

#[export] Hint Unfold bi_entails bi_sep bi_and bi_or bi_wand bupd bi_bupd_bupd: iprop.

Section class_instances.
  Context `{Σ: GRA.t}.

  Global Instance from_sep_own (a b1 b2 : Σ) :
    IsOp a b1 b2 →
    FromSep (Own a) (Own b1) (Own b2).
  Proof.
    ii. inv H. red. uipropall. i. des. subst.
    unfold URA.extends in *. des. subst.
    exists (URA.add ctx0 ctx). repeat rewrite URA.add_assoc.
    f_equal. rewrite URA.add_comm. rewrite URA.add_assoc. f_equal.
    eapply URA.add_comm.
  Qed.

  Global Instance into_and_own p (a b1 b2 : Σ) :
    IsOp a b1 b2 → IntoAnd p (Own a) (Own b1) (Own b2).
  Proof.
    ii. apply bi.intuitionistically_if_mono. inv H.
    uipropall. i. unfold URA.extends in *. des. subst. split.
    { exists (URA.add b2 ctx). eapply URA.add_assoc. }
    { exists (URA.add b1 ctx). rewrite URA.add_assoc.
      f_equal. eapply URA.add_comm. }
  Qed.

  Global Instance into_sep_own (a b1 b2 : Σ) :
    IsOp a b1 b2 → IntoSep (Own a) (Own b1) (Own b2).
  Proof.
    ii. red. inv H. uipropall. i.
    unfold URA.extends in *. des. subst.
    exists b1, (URA.add b2 ctx). split.
    { symmetry. eapply URA.add_assoc. }
    esplits.
    { eapply URA.unit_id. }
    { eauto. }
  Qed.

  Global Instance from_sep_ownM (M: URA.t) `{@GRA.inG M Σ} (a b1 b2 : M) :
    IsOp a b1 b2 →
    FromSep (OwnM a) (OwnM b1) (OwnM b2).
  Proof.
    ii. red. unfold OwnM. inv H0.
    iIntros "[H1 H2]". iCombine "H1 H2" as "H".
    rewrite GRA.embed_add. iApply "H".
  Qed.

  Global Instance into_and_ownM (M: URA.t) `{@GRA.inG M Σ} p (a b1 b2 : M) :
    IsOp a b1 b2 → IntoAnd p (OwnM a) (OwnM b1) (OwnM b2).
  Proof.
    ii. red. apply bi.intuitionistically_if_mono. inv H0.
    unfold OwnM. rewrite <- GRA.embed_add. iIntros "[H1 H2]". iSplit.
    { iApply "H1". }
    { iApply "H2". }
  Qed.

  Global Instance into_sep_ownM (M: URA.t) `{@GRA.inG M Σ} (a b1 b2 : M) :
    IsOp a b1 b2 → IntoSep (OwnM a) (OwnM b1) (OwnM b2).
  Proof.
    ii. red. inv H0. unfold OwnM.
    rewrite <- GRA.embed_add. iIntros "[H1 H2]". iSplitL "H1"; iFrame.
  Qed.
End class_instances.



Section ILEMMAS.
  Context `{Σ: GRA.t}.

  Lemma from_semantic (a: Σ) (P: iProp') (SAT: P a)
    :
      Own a ⊢ #=> P.
  Proof.
    uipropall. ss. i. unfold URA.extends in *. des. subst.
    uipropall. i. esplits; [|apply SAT]. eapply URA.wf_mon.
    instantiate (1:=ctx0). replace (a ⋅ ctx ⋅ ctx0) with (a ⋅ ctx0 ⋅ ctx); eauto.
    repeat rewrite <- URA.add_assoc. f_equal. eapply URA.add_comm.
  Qed.

  Lemma to_semantic (a: Σ) (P: iProp') (SAT: Own a ⊢ P) (WF: URA.wf a)
    :
      P a.
  Proof.
    uipropall. eapply SAT; eauto. reflexivity.
  Qed.

  Lemma OwnM_valid (M: URA.t) `{@GRA.inG M Σ} (m: M):
    OwnM m -∗ ⌜URA.wf m⌝.
  Proof.
    rr. uipropall. i. red. rr. unfold OwnM, Own in *. uipropall.
    unfold URA.extends in *. des. subst.
    eapply URA.wf_mon in WF. eapply GRA.embed_wf. eauto.
  Qed.

  Lemma Upd_Pure P
    :
      #=> ⌜P⌝ ⊢ ⌜P⌝.
  Proof.
    rr. uipropall. i. rr. uipropall.
    hexploit (H URA.unit).
    { rewrite URA.unit_id. eauto. }
    i. des. rr in H1. uipropall.
  Qed.

  Lemma Own_Upd_set
        (r1: Σ) B
        (UPD: URA.updatable_set r1 B)
    :
      (Own r1) ⊢ (#=> (∃ b, ⌜B b⌝ ** (Own b)))
  .
  Proof.
    cut (Entails (Own r1) (Upd (Ex (fun b => Sepconj (Pure (B b)) (Own b))))); ss.
    uipropall. i. red in H. des. subst.
    exploit (UPD (ctx0 ⋅ ctx)).
    { rewrite URA.add_assoc. eauto. }
    i. des. exists (b ⋅ ctx0). split.
    { rewrite <- URA.add_assoc. eauto. }
    { exists b. uipropall. esplits; [|apply IN|reflexivity].
      eapply URA.add_comm. }
  Qed.

  Lemma Own_Upd
        (r1 r2: Σ)
        (UPD: URA.updatable r1 r2)
    :
      (Own r1) ⊢ (#=> (Own r2))
  .
  Proof.
    iStartProof. iIntros "H".
    iAssert (#=> (∃ b, ⌜((eq r2) b)⌝ ** (Own b)))%I with "[H]" as "H".
    { iApply Own_Upd_set; [|iFrame].
      red. red in UPD. i. hexploit UPD; eauto. }
    iMod "H". iDestruct "H" as (b) "[#H0 H1]".
    iPure "H0" as Hs. subst. iApply "H1".
  Qed.

  Lemma Own_extends
        (a b: Σ)
        (EXT: URA.extends a b)
    :
      Own b ⊢ Own a
  .
  Proof.
    red. uipropall. ii. etrans; eauto.
  Qed.

  Lemma OwnM_Upd_set (M: URA.t) `{@GRA.inG M Σ}
        (r1: M) B
        (UPD: URA.updatable_set r1 B)
    :
      (OwnM r1) ⊢ (#=> (∃ b, ⌜B b⌝ ** (OwnM b)))
  .
  Proof.
    assert (UPDM: URA.updatable_set
                    (GRA.embed r1)
                    (fun r => exists m, r = GRA.embed m /\ B m)).
    { red. i. red in UPD.
      unshelve hexploit UPD.
      { eapply (@eq_rect URA.t (Σ (@GRA.inG_id _ _ H)) (@URA.car)).
        { eapply (ctx (@GRA.inG_id _ _ H)). }
        { symmetry. eapply (@GRA.inG_prf _ _ H). }
      }
      Local Transparent GRA.to_URA.
      { ur in WF. ss. specialize (WF GRA.inG_id).
        destruct H. subst. ss.
        unfold GRA.embed in WF. ss.
        replace (PeanoNat.Nat.eq_dec inG_id inG_id)
          with (@left (inG_id = inG_id) (inG_id <> inG_id) eq_refl) in WF; ss.
        { des_ifs. repeat f_equal. eapply proof_irrelevance. }
      }
      i. des. exists (GRA.embed b). esplits; eauto.
      ur. Local Transparent GRA.to_URA. ss.
      i. unfold GRA.embed. des_ifs.
      { ss. unfold PCM.GRA.cast_ra. destruct  H. subst. ss. }
      { ur in WF. specialize (WF k). rewrite URA.unit_idl.
        eapply URA.wf_mon. rewrite URA.add_comm. eauto.
      }
    }
    iIntros "H".
    iPoseProof (Own_Upd_set with "H") as "> H".
    { eapply UPDM. }
    iDestruct "H" as (b) "[% H1]". des. subst.
    iModIntro. iExists m. iFrame. ss.
  Qed.

  Lemma OwnM_Upd (M: URA.t) `{@GRA.inG M Σ}
        (r1 r2: M)
        (UPD: URA.updatable r1 r2)
    :
      (OwnM r1) ⊢ (#=> (OwnM r2))
  .
  Proof.
    iStartProof. iIntros "H".
    iAssert (#=> (∃ b, ⌜((eq r2) b)⌝ ** (OwnM b)))%I with "[H]" as "H".
    { iApply OwnM_Upd_set; [|iFrame].
      red. red in UPD. i. hexploit UPD; eauto. }
    iMod "H". iDestruct "H" as (b) "[#H0 H1]".
    iPure "H0" as Hs. subst. iApply "H1".
  Qed.

  Lemma OwnM_extends (M: URA.t) `{@GRA.inG M Σ}
        (a b: M)
        (EXT: URA.extends a b)
    :
      OwnM b ⊢ OwnM a
  .
  Proof.
    red. unfold OwnM. uipropall. i. unfold URA.extends in *.
    des. subst. rewrite <- GRA.embed_add.
    rewrite <- URA.add_assoc. eauto.
  Qed.

End ILEMMAS.

Ltac iOwnWf' H :=
  iPoseProof (OwnM_valid with H) as "%".

Tactic Notation "iOwnWf" constr(H) :=
  iOwnWf' H.

Tactic Notation "iOwnWf" constr(H) "as" ident(WF) :=
  iOwnWf' H;
  match goal with
  | H0: @URA.wf _ _ |- _ => rename H0 into WF
  end
.
