From sflib Require Import sflib.
From iris.algebra Require Import proofmode_classes.
From iris.proofmode Require Export proofmode.

From Fairness.base_logic Require Import base_logic.

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
  Proof. rewrite /IsExcept0 bi.except_0_into_later uPred.later_eq //. Qed.

End uPredI.
(* uPredI_affine is added so that IPM can also resolve pure predicates with evars. *)
Global Hint Immediate uPredI_affine : core.

Section iProp.
Context `{Σ: GRA.t}.
Definition iProp := uPredI Σ.

Local Definition OwnM_def {M : ucmra} `{!GRA.inG M Σ} (a : M) : iProp := uPred_ownM (GRA.embed a).
Local Definition OwnM_aux : seal (@OwnM_def). Proof. by eexists. Qed.
Definition OwnM := OwnM_aux.(unseal).
Definition OwnM_eq : @OwnM = @OwnM_def := OwnM_aux.(seal_eq).

Global Instance iProp_bi_bupd : BiBUpd iProp := uPred_bi_bupd Σ.

Definition from_upred (P : uPred Σ) : iProp := P.
Definition to_upred (P : iProp) : uPred Σ := P.

End iProp.
Global Arguments OwnM {Σ M _} a.
Global Arguments iProp : clear implicits.

Local Ltac unseal := rewrite ?OwnM_eq /OwnM_def.

Notation "#=> P" := (|==> P)%I (at level 99, only parsing).


Section class_instances.
  Context `{Σ: GRA.t}.

  Lemma OwnM_uPred_ownM_eq `{!GRA.inG M Σ} (a: M) : OwnM a = uPred_ownM (GRA.embed a).
  Proof. rewrite OwnM_eq //. Qed.

  Lemma OwnM_op `{!GRA.inG M Σ} (a1 a2: M) :
    (OwnM (a1 ⋅ a2)) ⊣⊢ (OwnM a1 ∗ OwnM a2).
  Proof. unseal. by rewrite -GRA.embed_add uPred.ownM_op. Qed.

  Global Instance OwnM_ne `{!GRA.inG M Σ} : NonExpansive (@OwnM Σ M _).
  Proof. unseal. solve_proper. Qed.
  Global Instance OwnM_proper `{!GRA.inG M Σ} :
    Proper ((≡) ==> (⊣⊢)) (@OwnM Σ M _) := ne_proper _.

  Global Instance OwnM_core_persistent `{!GRA.inG M Σ} (a : M) :
    CoreId a → Persistent (OwnM a).
  Proof. unseal. apply _. Qed.

  Lemma OwnM_valid (M: ucmra) `{!GRA.inG M Σ} (m: M):
    OwnM m ⊢ ⌜✓ m⌝.
  Proof. unseal. rewrite uPred.ownM_valid uPred.discrete_valid. apply bi.pure_mono, GRA.embed_wf. Qed.

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
  Global Instance from_and_ownM_persistent (M: ucmra) `{@GRA.inG M Σ} (a b1 b2 : M) :
    IsOp a b1 b2 → TCOr (CoreId b1) (CoreId b2) →
    FromAnd (OwnM a) (OwnM b1) (OwnM b2).
  Proof.
    intros ? Hb. rewrite /FromAnd (is_op a) OwnM_op.
    destruct Hb; by rewrite bi.persistent_and_sep.
  Qed.

End class_instances.



Section ILEMMAS.
  Context `{Σ: GRA.t}.
  (* Notation iProp := (iProp Σ) (only parsing). *)

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

  Lemma OwnM_unit `{!GRA.inG M Σ} (P : iProp Σ) : P ⊢ OwnM ε.
  Proof. unseal. by rewrite GRA.embed_unit (uPred.ownM_unit P). Qed.

  Lemma OwnM_Upd_set `{!GRA.inG M Σ}
        (r1: M) B
        (UPD: r1 ~~>: B)
    :
      (OwnM r1) ⊢ (#=> (∃ b, ⌜B b⌝ ∧ (OwnM b)))
  .
  Proof.
    unseal. iIntros "?".
    iMod (uPred.bupd_ownM_updateP with "[$]") as (b) "[%Hm ?]".
    { apply GRA.embed_updatable_set, UPD. }
    destruct Hm as [? [-> ?]]. by iFrame "∗%".
  Qed.

  Lemma OwnM_Upd `{M: ucmra} `{@GRA.inG M Σ}
        (r1 r2: M)
        (UPD: r1 ~~> r2)
    :
      (OwnM r1) ⊢ (#=> (OwnM r2))
  .
  Proof.
    intros. iIntros "?".
    iMod (OwnM_Upd_set _ (r2 =.) with "[$]") as (r3) "[-> $]".
    { by apply cmra_update_updateP. }
    done.
  Qed.

  Global Instance OwnM_mono `{!GRA.inG M Σ} : Proper (flip (≼) ==> (⊢)) (@OwnM Σ M _).
  Proof. intros a b [c ->]. by rewrite OwnM_op bi.sep_elim_l. Qed.

  Lemma OwnM_extends `{M: ucmra} `{@GRA.inG M Σ}
        {a b: M}
        (EXT: a ≼ b)
    :
      OwnM b ⊢ OwnM a
  .
  Proof. by apply OwnM_mono. Qed.
End ILEMMAS.
