From sflib Require Import sflib.
Require Import Program.
From Fairness Require Import PCM IPM.
From Fairness Require Import Axioms.

From iris.algebra Require Import cmra lib.excl_auth functions.
Set Implicit Arguments.

Section AUX.
  Fixpoint sep_conjs `{Σ: GRA.t} (Ps : nat -> iProp Σ) (n : nat) : iProp Σ :=
    match n with
    | O => True
    | S m => (sep_conjs Ps m) ∗ (Ps m)
    end.
End AUX.

Definition maps_to {Σ} {A: Type} {M: ucmra} `{ING: @GRA.inG (A -d> M) Σ}
           (a: A) (m: M): iProp Σ :=
  OwnM (maps_to_res a m).

Section UPD.
  Variable A: Type.
  Context `{IN: @GRA.inG (excl_authUR $ leibnizO A) Σ}.

  Lemma black_white_update (a0 a' a1 : A)
    :
    (OwnM (●E (a0 : leibnizO A)))
      -∗
      (OwnM (◯E (a' : leibnizO A)))
      -∗
      #=> (OwnM (●E (a1 : leibnizO A))) ∗ OwnM (◯E (a1 : leibnizO A)).
  Proof.
    rewrite bi.wand_curry -!OwnM_op.
    apply bi.entails_wand, OwnM_Upd, excl_auth_update.
  Qed.

  Lemma black_white_equal (a a' : A)
    :
    (OwnM (●E (a : leibnizO A)))
      -∗
      (OwnM (◯E (a' : leibnizO A)))
      -∗
      ⌜a = a'⌝.
  Proof.
    iIntros "H0 H1". by iCombine "H0 H1" gives %?%excl_auth_agree_L.
  Qed.

  Lemma white_white_excl a a'
    :
    (OwnM (excl_auth_frag a))
      -∗
      (OwnM (excl_auth_frag a' ))
      -∗
      ⌜False⌝.
  Proof.
    iIntros "H0 H1". by iCombine "H0 H1" gives %?%excl_auth_frag_op_valid.
  Qed.

End UPD.
