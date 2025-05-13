From sflib Require Import sflib.
From Fairness Require Import PCM IPM.

Section IUPD.
  Context {Σ: GRA.t}.
  Notation iProp := (iProp Σ) (only parsing).

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
Notation "#=( Q )=> P" := ((@bupd (bi_car (iProp _)) (@bi_bupd_bupd _ (@iProp_bi_bupd_IUpd _ Q))) P) (at level 99).
Notation "P =( I ) =∗ Q" := (P ⊢ #=( I )=> Q) (only parsing, at level 99) : stdpp_scope.
Notation "P =( I )=∗ Q" := (P -∗ #=( I )=> Q)%I (at level 99): bi_scope.

Section lemmas.
  Context {Σ: GRA.t}.
  Lemma IUpd_eq (I P : iProp Σ)
      :
      (#=(I)=> P) ⊣⊢ (I -∗ #=> (I ∗ P)).
    Proof.
      reflexivity.
    Qed.

    Lemma IUpd_unfold (I P : iProp Σ)
      :
      #=(I)=> P ⊢ (I -∗ #=> (I ∗ P)).
    Proof.
      reflexivity.
    Qed.

    Lemma IUpd_fold (I P : iProp Σ)
      :
      (I -∗ #=> (I ∗ P)) ⊢ #=(I)=> P.
    Proof.
      reflexivity.
    Qed.

    Lemma Upd_IUpd (I : iProp Σ) : forall P, #=> P ⊢ (#=(I)=> P).
    Proof.
      ii. iIntros "H". iApply IUpd_fold. iIntros "INV". iFrame.
    Qed.

    Definition SubIProp P Q: iProp Σ :=
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
      rewrite !IUpd_eq. iIntros "H0 H1 H2".
      iPoseProof ("H0" with "H2") as "> [H0 H2]".
      iPoseProof ("H1" with "H0") as "> [H0 H1]".
      iPoseProof ("H2" with "H0") as "H0". iFrame. auto.
    Qed.

  End lemmas.

  Section class_instances.
  Global Instance upd_elim_iupd `{Σ : GRA.t} (I P Q : iProp Σ)
        `{ElimModal _ True false false (#=(I)=> P) P Q R}
    :
    ElimModal True false false (#=> P) P Q R.
  Proof.
    unfold ElimModal. i. iIntros "[H0 H1]".
    iPoseProof (Upd_IUpd with "H0") as ">H0". iApply "H1". auto.
  Qed.

  Global Instance iupd_elim_upd `{Σ : GRA.t} (I P Q : iProp Σ) b
    :
    ElimModal True b false (#=> P) P (#=(I)=> Q) (#=(I)=> Q).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim IUpd_eq.
    i. iIntros "[H0 H1] H". iMod "H0".
    iApply ("H1" with "H0 H").
  Qed.

  Global Instance subiprop_elim_upd `{Σ : GRA.t} (I J P Q : iProp Σ) b
    :
    ElimModal True b false ((SubIProp I J) ∗ #=(I)=> P) P (#=(J)=> Q) (#=(J)=> Q).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim !IUpd_eq.
    iIntros (_) "[[SUB P] K] J".
    iMod ("SUB" with "J") as "[I IJ]". iMod ("P" with "I") as "[I P]".
    iMod ("IJ" with "I") as "J". iPoseProof ("K" with "P J") as "K". iFrame.
  Qed.
End class_instances.

(* TODO: move this? *)
Section UPDATING.
  Context `{Σ: @GRA.t}.
  Notation iProp := (iProp Σ) (only parsing).

  Definition updating (I: iProp) (P Q R: iProp): iProp :=
    I -∗ (#=> (P ∗ (Q -∗ #=> (I ∗ R)))).

  Lemma updating_sub_mon (I0 I1: iProp) (P Q R: iProp)
    :
    (SubIProp I0 I1)
      -∗
      (updating I0 P Q R)
      -∗
      (updating I1 P Q R).
  Proof.
    iIntros "SUB UPD INV".
    iPoseProof ("SUB" with "INV") as "> [INV K]".
    iPoseProof ("UPD" with "INV") as "> [INV FIN]".
    iFrame. iModIntro. iIntros "H".
    iPoseProof ("FIN" with "H") as "> [INV H]".
    iPoseProof ("K" with "INV") as "> INV".
    iModIntro. iFrame.
  Qed.
End UPDATING.
