From sflib Require Import sflib.
From iris.algebra Require Import proofmode_classes.
From iris.proofmode Require Export proofmode.

From Fairness.base_logic Require Import bi derived.

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

Global Instance iProp_bi_bupd : BiBUpd iProp := uPred_bi_bupd Σ.

Definition from_upred (P : uPred Σ) : iProp := P.
Definition to_upred (P : iProp) : uPred Σ := P.

End iProp.
Global Arguments iProp : clear implicits.

Arguments OwnM: simpl never.

Local Ltac unseal := rewrite ?Own_eq /Own_def.

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

#[export] Hint Unfold bi_entails bi_sep bi_and bi_or bi_wand bupd bi_bupd_bupd: iprop.

Section class_instances.
  Context `{Σ: GRA.t}.
  Notation iProp := (iProp Σ).

  Global Instance Own_ne : NonExpansive (@Own Σ).
  Proof. unseal. solve_proper. Qed.
  Global Instance Own_proper :
    Proper ((≡) ==> (⊣⊢)) (@Own Σ) := ne_proper _.

  Global Instance Own_core_persistent a : CoreId a →  Persistent (@Own Σ a).
  Proof. rewrite !Own_eq /Own_def; apply _. Qed.

  Lemma Own_op (a1 a2: Σ) :
    (Own (a1 ⋅ a2)) ⊣⊢ (Own a1 ∗ Own a2).
  Proof. unseal. by rewrite uPred.ownM_op. Qed.

  Lemma Own_valid (a : Σ) :
    Own a ⊢ ⌜✓ a⌝.
  Proof.
    unseal. iIntros "H". iDestruct (uPred.ownM_valid with "H") as "V".
    iEval (rewrite uPred.discrete_valid) in "V". iFrame "V".
  Qed.

  Global Instance into_sep_own (a b1 b2 : Σ) :
    IsOp a b1 b2 → IntoSep (Own a) (Own b1) (Own b2).
  Proof. intros. by rewrite /IntoSep (is_op a) Own_op. Qed.

  Global Instance into_and_own p (a b1 b2 : Σ) :
    IsOp a b1 b2 → IntoAnd p (Own a) (Own b1) (Own b2).
  Proof. intros. by rewrite /IntoAnd (is_op a) Own_op bi.sep_and. Qed.

  Global Instance from_sep_own (a b1 b2 : Σ) :
    IsOp a b1 b2 →
    FromSep (Own a) (Own b1) (Own b2).
  Proof. intros. by rewrite /FromSep -Own_op -is_op. Qed.

  (* TODO: Improve this instance with generic own simplification machinery
  once https://gitlab.mpi-sws.org/iris/iris/-/issues/460 is fixed *)
  (* Cost > 50 to give priority to [combine_sep_as_fractional]. *)
  Global Instance combine_sep_as_own (a b1 b2 : Σ) :
    IsOp a b1 b2 → CombineSepAs (Own b1) (Own b2) (Own a) | 60.
  Proof. intros. by rewrite /CombineSepAs -Own_op -is_op. Qed.
  (* TODO: Improve this instance with generic own validity simplification
  machinery once https://gitlab.mpi-sws.org/iris/iris/-/issues/460 is fixed *)
  Global Instance combine_sep_gives_own (b1 b2 : Σ) :
    CombineSepGives (Own b1) (Own b2) (⌜✓ (b1 ⋅ b2)⌝).
  Proof.
    intros. rewrite /CombineSepGives -Own_op Own_valid.
    by apply: bi.persistently_intro.
  Qed.
  (* Global Instance from_and_own_persistent (a b1 b2 : Σ) :
    IsOp a b1 b2 → TCOr (CoreId b1) (CoreId b2) →
    FromAnd (Own a) (Own b1) (Own b2).
  Proof.
    intros ? Hb. rewrite /FromAnd (is_op a) Own_op.
    destruct Hb; by rewrite persistent_and_sep.
  Qed. *)

  Lemma OwnM_op (M: ucmra) `{@GRA.inG M Σ} (a1 a2: M) :
    (OwnM (a1 ⋅ a2)) ⊣⊢ (OwnM a1 ∗ OwnM a2).
  Proof. by rewrite /OwnM -GRA.embed_add Own_op. Qed.

  Global Instance OwnM_ne `{GRA.inG M Σ} : NonExpansive (@OwnM Σ M _).
  Proof. solve_proper. Qed.
  Global Instance OwnM_proper (M: ucmra) `{@GRA.inG M Σ} :
    Proper ((≡) ==> (⊣⊢)) (@OwnM Σ M _) := ne_proper _.

  Global Instance OwnM_core_persistent `{GRA.inG M Σ} (a : M) :
    CoreId a → Persistent (OwnM a).
  Proof.
    rewrite /OwnM => CORE. apply Own_core_persistent.
    rewrite core_id_total -GRA.embed_core core_id_core //.
  Qed.

  Lemma OwnM_valid (M: ucmra) `{@GRA.inG M Σ} (m: M):
    OwnM m ⊢ ⌜✓ m⌝.
  Proof.
    iIntros "H". iDestruct (Own_valid with "H") as %WF.
    iPureIntro. eapply GRA.embed_wf. done.
  Qed.


  Global Instance into_sep_ownM (M: ucmra) `{@GRA.inG M Σ} (a b1 b2 : M) :
    IsOp a b1 b2 → IntoSep (OwnM a) (OwnM b1) (OwnM b2).
  Proof. intros. by rewrite /IntoSep (is_op a) OwnM_op. Qed.

  Global Instance into_and_ownM (M: ucmra) `{@GRA.inG M Σ} p (a b1 b2 : M) :
    IsOp a b1 b2 → IntoAnd p (OwnM a) (OwnM b1) (OwnM b2).
  Proof. intros. by rewrite /IntoAnd (is_op a) OwnM_op bi.sep_and. Qed.

  Global Instance from_sep_ownM (M: ucmra) `{@GRA.inG M Σ} (a b1 b2 : M) :
    IsOp a b1 b2 →
    FromSep (OwnM a) (OwnM b1) (OwnM b2).
  Proof. intros. by rewrite /FromSep -OwnM_op -is_op. Qed.

  (* TODO: Improve this instance with generic own simplification machinery
  once https://gitlab.mpi-sws.org/iris/iris/-/issues/460 is fixed *)
  (* Cost > 50 to give priority to [combine_sep_as_fractional]. *)
  Global Instance combine_sep_as_ownM (M: ucmra) `{@GRA.inG M Σ} (a b1 b2 : M) :
    IsOp a b1 b2 → CombineSepAs (OwnM b1) (OwnM b2) (OwnM a) | 60.
  Proof. intros. by rewrite /CombineSepAs -OwnM_op -is_op. Qed.
  (* TODO: Improve this instance with generic own validity simplification
  machinery once https://gitlab.mpi-sws.org/iris/iris/-/issues/460 is fixed *)
  Global Instance combine_sep_gives_ownM (M: ucmra) `{@GRA.inG M Σ} (b1 b2 : M) :
    CombineSepGives (OwnM b1) (OwnM b2) (⌜✓ (b1 ⋅ b2)⌝).
  Proof.
    intros. rewrite /CombineSepGives -OwnM_op OwnM_valid.
    by apply: bi.persistently_intro.
  Qed.
  (* Global Instance from_and_own_persistent (a b1 b2 : Σ) :
    IsOp a b1 b2 → TCOr (CoreId b1) (CoreId b2) →
    FromAnd (Own a) (Own b1) (Own b2).
  Proof.
    intros ? Hb. rewrite /FromAnd (is_op a) Own_op.
    destruct Hb; by rewrite persistent_and_sep.
  Qed. *)

End class_instances.



Section ILEMMAS.
  Context `{Σ: GRA.t}.
  (* Notation iProp := (iProp Σ). *)

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

  (* Lemma Upd_Pure P
    :
      #=> (⌜P⌝ : iProp) ⊢ ⌜P⌝.
  Proof. iIntros. iModIntro.
    rr. uipropall. i. rr. uipropall.
    hexploit (H ε).
    { by rewrite right_id. }
    i. des. rr in H1. uipropall.
  Qed. *)

  Lemma Own_Upd_set
        (r1: Σ) B
        (UPD: r1 ~~>: B)
    :
      (Own r1) ⊢ (#=> (∃ b, ⌜B b⌝ ∧ (Own b)))
  .
  Proof. unseal. by apply: uPred.bupd_ownM_updateP. Qed.

  Lemma Own_Upd
        (r1 r2: Σ)
        (UPD: r1 ~~> r2)
    :
      (Own r1) ⊢ (#=> (Own r2))
  .
  Proof.
    intros. iIntros "?".
    iMod (Own_Upd_set _ (r2 =.) with "[$]") as (a'') "[-> $]".
    { by apply cmra_update_updateP. }
    done.
  Qed.

  Lemma Own_extends
        (a b: Σ)
        (EXT: a ≼ b)
    :
      Own b ⊢ Own a
  .
  Proof. unseal. apply uPred.ownM_mono. done. Qed.

  Lemma Own_persistently (r : Σ) : Own r ⊢ <pers> Own (core r).
  Proof. unseal. apply uPred.persistently_ownM_core. Qed.

  Lemma OwnM_persistently {M : ucmra} `{@GRA.inG M Σ} (r : M) : OwnM r ⊢ <pers> OwnM (core r).
  Proof. rewrite /OwnM GRA.embed_core Own_persistently //. Qed.

  Lemma Own_unit : ⊢ Own (Σ:=Σ) ε.
  Proof. unseal. rewrite /bi_emp_valid. apply (uPred.ownM_unit emp). Qed.

  Lemma OwnM_unit {M : ucmra} `{@GRA.inG M Σ} : ⊢ OwnM ε.
  Proof. rewrite /OwnM GRA.embed_unit. apply Own_unit. Qed.

  Lemma OwnM_Upd_set `{M: ucmra} `{IN: @GRA.inG M Σ}
        (r1: M) B
        (UPD: r1 ~~>: B)
    :
      (OwnM r1) ⊢ (#=> (∃ b, ⌜B b⌝ ∧ (OwnM b)))
  .
  Proof.
    iIntros "H".
    iMod (Own_Upd_set with "H") as (b) "[%Hm H1]".
    { apply GRA.embed_updatable_set, UPD. }
    destruct Hm as [m [? ?]]. subst.
    iModIntro. iExists m. iFrame. ss.
  Qed.

  Lemma OwnM_Upd `{M: ucmra} `{@GRA.inG M Σ}
        (r1 r2: M)
        (UPD: r1 ~~> r2)
    :
      (OwnM r1) ⊢ (#=> (OwnM r2))
  .
  Proof. apply Own_Upd, GRA.embed_updatable, UPD. Qed.

  Lemma OwnM_extends `{M: ucmra} `{@GRA.inG M Σ}
        {a b: M}
        (EXT: a ≼ b)
    :
      OwnM b ⊢ OwnM a
  .
  Proof. revert EXT. move=> [c ->]. by rewrite OwnM_op bi.sep_elim_l. Qed.
End ILEMMAS.

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
