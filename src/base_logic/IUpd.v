From sflib Require Import sflib.
From Fairness.base_logic Require Import bi derived lib.own.

From Fairness Require Import iprop_extra.
From iris.proofmode Require Export tactics.
From iris.algebra Require Import proofmode_classes.

From iris.prelude Require Import options.

Section IUPD.
  Context {Σ : gFunctors}.
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

  Lemma iProp_bupd_mixin_IUpd I: BiBUpdMixin iProp (IUpd I).
  Proof.
    econs.
    - ii. unfold bupd. unfold IUpd. rewrite H. auto.
    - apply IUpd_intro.
    - apply IUpd_mono.
    - apply IUpd_trans.
    - apply IUpd_frame_r.
  Qed.

  Global Instance iProp_bi_bupd_IUpd I: BiBUpd iProp :=
  {| bi_bupd_mixin := iProp_bupd_mixin_IUpd I |}.
End IUPD.

Notation "#=( Q )=> P" := ((@bupd (bi_car _) (@bi_bupd_bupd _ (@iProp_bi_bupd_IUpd _ Q))) P) (at level 99).
Notation "P =( I )=∗ Q" := (P -∗ #=( I )=> Q)%I (at level 99): bi_scope.

#[export] Hint Unfold bi_entails bi_sep bi_and bi_or bi_wand bupd bi_bupd_bupd: iprop.

Section lemmas.
  Context `{Σ: gFunctors}.

  Implicit Types I P Q : iProp Σ.

  Lemma IUpd_eq I P
    :
    (#=(I)=> P) ⊣⊢ (I -∗ #=> (I ∗ P)).
  Proof.
    reflexivity.
  Qed.

  Lemma IUpd_unfold I P
    :
    #=(I)=> P ⊢ (I -∗ #=> (I ∗ P)).
  Proof.
    reflexivity.
  Qed.

  Lemma IUpd_fold I P
    :
    (I -∗ #=> (I ∗ P)) ⊢ #=(I)=> P.
  Proof.
    reflexivity.
  Qed.

  Lemma Upd_IUpd (I : iProp Σ) : forall P, #=> P ⊢ (#=(I)=> P).
  Proof.
    ii. iIntros "?". iApply IUpd_fold. iIntros "$". iFrame.
  Qed.

  Lemma IUpd_Upd_elim (I : iProp Σ) : forall P, (I ∗ #=(I)=> P) ⊢ (#=> I ∗ P).
  Proof.
    iIntros (P) "[I IP]". rewrite IUpd_eq.
    by iApply "IP".
  Qed.

  Definition SubIProp (P Q : iProp Σ) : Prop :=
    Q ⊢ #=> (P ∗ (P -∗ #=> Q)).

  Global Instance SubIProp_reflexive : Reflexive SubIProp.
  Proof. intros P. iIntros "H". iFrame. auto. Qed.

  Global Instance SubIProp_transitive : Transitive SubIProp.
  Proof.
    intros P Q R HPQ HQR.
    iIntros "R".
    iMod (HQR with "R") as "[Q QR]".
    iMod (HPQ with "Q") as "[$ PQ]".
    iIntros "!> P".
    iMod ("PQ" with "P") as "Q".
    iMod ("QR" with "Q") as "$".
    done.
  Qed.

  Lemma SubIProp_sep_l P Q
    :
    (SubIProp P (P ∗ Q)).
  Proof.
    iIntros "[H0 H1]". iFrame. auto.
  Qed.

  Lemma SubIProp_sep_r P Q
    :
    (SubIProp Q (P ∗ Q)).
  Proof.
    iIntros "[H0 H1]". iFrame. auto.
  Qed.

  Lemma IUpd_sub_mon P Q {R}
    :
    (SubIProp P Q)
      →
      (#=(P)=> R)
      ⊢
      (#=(Q)=> R).
  Proof.
    rewrite !IUpd_eq. iIntros (HPQ) "PR Q".
    iMod (HPQ with "Q") as "[P PQ]".
    iMod ("PR" with "P") as "[P $]".
    iMod ("PQ" with "P") as "$".
    done.
  Qed.
End lemmas.

(* TODO: the cond generization might be very bad... *)
Global Instance upd_elim_iupd `{Σ : gFunctors} (I P Q : iProp Σ)
       `{ElimModal _ Cond b false (#=(I)=> P) P Q R}
  :
  ElimModal Cond b false (#=> P) P Q R | 60.
Proof.
  rewrite /ElimModal. iIntros (HCond) "[Upd Wand]".
  destruct b; simpl in *; [iDestruct "Upd" as "#Upd"|].
  all: iMod (Upd_IUpd with "Upd") as "IUpd"; by iApply "Wand".
Qed.

(* Ensure the weight makes this instance go first. *)
Global Instance upd_elim_iupd' `{Σ : gFunctors} (I P Q : iProp Σ)
       `{ElimModal _ True b false (#=(I)=> P) P Q R}
  :
  ElimModal True b false (#=> P) P Q R | 50.
Proof. apply _. Qed.

Global Instance iupd_elim_upd `{Σ : gFunctors} (I P Q : iProp Σ) b
  :
  ElimModal True b false (#=> P) P (#=(I)=> Q) (#=(I)=> Q).
Proof.
  rewrite /ElimModal bi.intuitionistically_if_elim IUpd_eq.
  iIntros (_) "[>P Vsw] I". iApply ("Vsw" with "P I").
Qed.

(* TODO: might need to add some weight to this *)
Global Instance subiprop_elim_iupd `{Σ : gFunctors} (I J P Q : iProp Σ) b
  :
  ElimModal (SubIProp I J) b false (#=(I)=> P) P (#=(J)=> Q) (#=(J)=> Q).
Proof.
  rewrite /ElimModal bi.intuitionistically_if_elim.
  iIntros (HIJ) "[IP PJQ]".
  iMod (IUpd_sub_mon I J HIJ with "IP") as "P".
  by iApply "PJQ".
Qed.

Global Instance upd_elim_iupd_with_I `{Σ : gFunctors} (I P Q : iProp Σ) b
  :
  ElimModal True b false (I ∗ #=(I)=> P) (I ∗ P) (#=> Q) (#=> Q).
Proof.
  rewrite /ElimModal bi.intuitionistically_if_elim.
  iIntros (_) "[[I IP] PQ]".
  iMod (IUpd_Upd_elim I P with "[$I $IP]") as "I".
  by iApply "PQ".
Qed.
