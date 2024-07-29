From sflib Require Import sflib.
From Fairness.base_logic Require Import bi derived.
From iris.proofmode Require Export tactics.
From iris.algebra Require Import proofmode_classes.

From Fairness Require Import PCM.

From iris.prelude Require Import options.

Arguments Z.of_nat: simpl nomatch.

Section uPredI.
  (** extra BI instances *)

  Global Instance uPredI_absorbing {M : ucmra} (P: uPredI M): Absorbing P.
  Proof. apply _. Qed.

  Global Instance uPredI_affine {M : ucmra} (P: uPredI M): Affine P.
  Proof. apply _. Qed.

  Global Instance uPredI_except_0 {M : ucmra} (P: uPredI M): IsExcept0 P.
  Proof.
    rewrite /IsExcept0 /bi_except_0. uPred.unseal.
    split=> x WFn. intros [|]; done.
  Qed.

End uPredI.
(* uPredI_affine is added so that IPM can also resolve pure predicates with evars. *)
Global Hint Immediate uPredI_affine : core.

Section iProp.
Context `{Σ: GRA.t}.
Definition iProp := uPredI Σ.

Local Definition Own_def (a: Σ) : iProp := uPred_ownM a.
Local Definition Own_aux : seal (@Own_def). Proof. by eexists. Qed.
Definition Own := Own_aux.(unseal).
Definition Own_eq : @Own = @Own_def := Own_aux.(seal_eq).

Definition OwnM {M : ucmra} `{!GRA.inG M Σ} (a : M) : iProp := Own (GRA.embed a).

Global Instance iProp_bi_bupd : BiBUpd iProp := {| bi_bupd_mixin := uPred_bupd_mixin Σ |}.

Definition from_upred (P : uPred Σ) : iProp := P.
Definition to_upred (P : iProp) : uPred Σ := P.

End iProp.
Global Arguments iProp : clear implicits.

Arguments OwnM: simpl never.

Section TEST.
  Context {Σ: GRA.t}.
  Notation iProp := (iProp Σ).

  Goal forall (P Q R: iProp) (PQ: P -∗ Q) (QR: Q -∗ R), P -∗ R.
  Proof.
    iIntros (P Q R PQ QR) "H".
    iApply QR. iApply PQ. iApply "H".
  Qed.

  Goal forall (P Q: iProp), ((bupd P) ∗ Q) -∗ (bupd Q).
  Proof.
    i. iStartProof.
    iIntros "[Hxs Hys]". iMod "Hxs". iApply "Hys".
  Qed.
End TEST.

Notation "#=> P" := (|==> P)%I (at level 99).

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
  Proof. intros x y EQ. by rewrite Own_eq EQ. Qed.

  Lemma Own_op (a1 a2: Σ) :
    (Own (a1 ⋅ a2)) ⊣⊢ (Own a1 ∗ Own a2).
  Proof. by rewrite Own_eq /Own_def uPred.ownM_op. Qed.

  (* NOTE: We have this instance as [iDestruct (uPred.ownM_valid with "H")] doesn't work for some reason.   *)
  Local Lemma Own_valid' (a : Σ) :
    Own a -∗ ✓ a.
  Proof. rewrite Own_eq /Own_def. apply uPred.ownM_valid. Qed.
  Lemma Own_valid (a : Σ) :
    Own a -∗ ⌜✓ a⌝.
  Proof.
    iIntros "H".
    iDestruct (Own_valid' with "H") as "V".
    iEval (rewrite uPred.discrete_valid) in "V". iFrame "V".
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

  (* Lemma from_semantic (a: Σ) (P: iProp') (SAT: P a)
    :
      Own a ⊢ #=> P.
  Proof.
    uipropall. ss. i. exists r. split; [done|].
    eapply iProp_mono; [| |exact SAT]; done.
  Qed.

  Lemma to_semantic (a: Σ) (P: iProp') (SAT: Own a ⊢ P) (WF: ✓ a)
    :
      P a.
  Proof. uipropall. eapply SAT; eauto. Qed. *)

  Lemma OwnM_valid (M: ucmra) `{@GRA.inG M Σ} (m: M):
    OwnM m -∗ ⌜✓ m⌝.
  Proof.
    iIntros "H". iDestruct (Own_valid with "H") as %WF.
    iPureIntro. eapply GRA.embed_wf. done.
  Qed.

  (* Lemma Upd_Pure P
    :
      #=> (⌜P⌝ : iProp) ⊢ ⌜P⌝.
  Proof. iIntros. iModIntro.
    rr. uipropall. i. rr. uipropall.
    hexploit (H ε).
    { by rewrite right_id. }
    i. des. rr in H1. uipropall.
  Qed. *)

  Local Lemma bupd_Own_updateP
        (x: Σ) Φ
        (UPD: x ~~>: Φ)
    :
     Own x -∗ #=> (∃ y : Σ, ⌜Φ y⌝ ∧ Own y).
  Proof. rewrite Own_eq /Own_def. apply uPred.bupd_ownM_updateP; [apply _|done]. Qed.
  Lemma Own_Upd_set
        (r1: Σ) B
        (UPD: r1 ~~>: B)
    :
      (Own r1) ⊢ (#=> (∃ b, ⌜B b⌝ ∗ (Own b)))
  .
  Proof.
    iIntros "H".
    iMod (bupd_Own_updateP _ _ UPD with "H") as (y) "[%Hy H]".
    iModIntro. iExists y. by iFrame.
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
    { iApply Own_Upd_set; [|iFrame]. by apply cmra_update_updateP. }
    iMod "H". iDestruct "H" as (b) "[%H0 H1]". subst. by iFrame.
  Qed.

  Lemma Own_extends
        (a b: Σ)
        (EXT: a ≼ b)
    :
      Own b ⊢ Own a
  .
  Proof. rewrite Own_eq /Own_def. apply uPred.ownM_mono. done. Qed.

  Lemma Own_persistently (r : Σ) : Own r ⊢ <pers> Own (core r).
  Proof. rewrite Own_eq /Own_def. apply uPred.persistently_ownM_core. Qed.

  Lemma OwnM_persistently {M : ucmra} `{@GRA.inG M Σ} (r : M) : OwnM r ⊢ <pers> OwnM (core r).
  Proof. rewrite /OwnM GRA.embed_core. apply Own_persistently. Qed.

  Lemma Own_unit : ⊢ Own (Σ:=Σ) ε.
  Proof. rewrite Own_eq /Own_def /bi_emp_valid. apply (uPred.ownM_unit emp). Qed.

  Lemma OwnM_unit {M : ucmra} `{@GRA.inG M Σ} : ⊢ OwnM ε.
  Proof. rewrite /OwnM GRA.embed_unit. apply Own_unit. Qed.

  Lemma OwnM_Upd_set `{M: ucmra} `{IN: @GRA.inG M Σ}
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

  Lemma OwnM_Upd `{M: ucmra} `{@GRA.inG M Σ}
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

  Lemma OwnM_extends `{M: ucmra} `{@GRA.inG M Σ}
        {a b: M}
        (EXT: a ≼ b)
    :
      OwnM b ⊢ OwnM a
  .
  Proof.
    rewrite /OwnM. apply Own_extends.
    unfold included in *.
    des. setoid_rewrite EXT.
    eexists. by rewrite -GRA.embed_add.
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
  rewrite /ElimModal bi.intuitionistically_if_elim.
  i. iIntros "[H0 H1]".
  iPoseProof (Upd_IUpd with "H0") as "H0".
  iIntros "H". iPoseProof ("H0" with "H") as "> [H0 H2]".
  iPoseProof ("H1" with "H2") as "H".
  iApply ("H" with "H0").
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
    | O => True
    | S m => (sep_conjs Ps m) ∗ (Ps m)
    end.

End AUX.
