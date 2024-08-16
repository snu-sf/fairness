(** Some more useful instances for BI.  *)

From Fairness.base_logic Require Import base_logic lib.own.
From iris.proofmode Require Export tactics.

From iris.prelude Require Import options.
Import uPred.

Section uPredI.
  (** extra BI instances *)

  Global Instance uPredI_absorbing {M : ucmra} (P: uPredI M): Absorbing P.
  Proof. apply _. Qed.

  Global Instance uPredI_affine {M : ucmra} (P: uPredI M): Affine P.
  Proof. apply _. Qed.

  Global Instance uPredI_except_0 {M : ucmra} (P: uPredI M): IsExcept0 P.
  Proof.
    rewrite /IsExcept0 /bi_except_0. uPred.unseal.
    split=> x Hx. intros [|]; done.
  Qed.

End uPredI.
(* uPredI_affine is added so that IPM can also resolve pure predicates with evars. *)
Global Hint Immediate uPredI_affine : core.

(* Backward compatible notation. *)
Notation "#=> P" := (|==> P)%I (at level 99).

(* This may seem to belong to [own.v]. However, that would make it go out of sync from Iris's [own.v] *)
Lemma own_valid' `{!inG Σ A} (γ : gname) (x : A) :
  own γ x ⊢ ⌜✓ x⌝.
Proof. etrans; [apply own_valid|rewrite discrete_valid //]. Qed.

Ltac iOwnWf' H :=
  iDestruct (own_valid' with H) as %?.

Tactic Notation "iOwnWf" constr(H) :=
  iOwnWf' H.

Tactic Notation "iOwnWf" constr(H) "as" ident(WF) :=
  let WF' := fresh WF in
  iDestruct (own_valid' with H) as %WF'.
