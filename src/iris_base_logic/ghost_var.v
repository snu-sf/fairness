From sflib Require Import sflib.
(* Port of https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris/base_logic/lib/ghost_var.v into FOS style iProp *)
(** A simple "ghost variable" of arbitrary type with fractional ownership.
Can be mutated when fully owned. *)

From Fairness Require Import IPM PCM IProp IPropAux.
From Fairness Require Import MonotoneRA.
From Fairness Require Import agree cmra updates dfrac_agree proofmode_classes frac.
From Fairness Require Import TemporalLogic.

From Fairness Require Export dfrac.

From iris.prelude Require Import prelude options.

Local Open Scope iris_algebra_scope.

Definition ghost_varURA (A : Type) : ucmra := @FiniteMap.t (of_RA.t (of_IrisRA.t (dfrac_agreeR A))).

Section definitions.
  Context {A : Type}.
  Context `{GHOSTVARURA : @GRA.inG (ghost_varURA A) Σ}.

  Definition ghost_var_ra
    (γ : nat) (q : Qp) (a : A) : ghost_varURA A :=
    FiniteMap.singleton γ
      (of_RA.to_ura (of_IrisRA.to_ra (to_frac_agree q a)) : of_RA.t (of_IrisRA.t (dfrac_agreeR A))).
  Definition ghost_var
      (γ : nat) (q : Qp) (a : A) : iProp :=
    OwnM (ghost_var_ra γ q a).
End definitions.

Local Ltac unseal :=
  repeat unfold ghost_var_ra,ghost_var,ghost_varURA.

Section lemmas.
  Context `{Σ : GRA.t}.
  Context `{GHOSTVARURA : @GRA.inG (ghost_varURA A) Σ}.
  Implicit Types (a b : A) (q : Qp).

  Lemma ghost_var_alloc a :
    ⊢ |==> ∃ γ, ghost_var γ 1 a.
  Proof.
    iDestruct (@OwnM_unit _ _ GHOSTVARURA) as "H".

    iMod (OwnM_Upd_set with "H") as "[%RES [%HGvar Gvar]]".
    { apply FiniteMap.singleton_alloc.
      instantiate (1 := of_RA.to_ura (of_IrisRA.to_ra (to_frac_agree 1 a)): of_RA.t (of_IrisRA.t (dfrac_agreeR A))).
      apply of_RA.to_ura_wf, of_IrisRA.to_ra_wf,frac_agree_valid.
      done.
    }
    simpl in *. destruct HGvar as [γ ->].
    iModIntro. iExists γ. unseal.
    iFrame.
  Qed.

  Lemma ghost_var_valid_2 γ a1 q1 a2 q2 :
    ghost_var γ q1 a1 -∗ ghost_var γ q2 a2 -∗ ⌜(q1 + q2 ≤ 1)%Qp ∧ a1 = a2⌝.
  Proof.
    unseal. iIntros "Hvar1 Hvar2".
    iCombine "Hvar1 Hvar2" as "Hvar".
    rewrite FiniteMap.singleton_add.
    rewrite of_RA.to_ura_add.
    rewrite of_IrisRA.to_ra_add.
    iDestruct (OwnM_valid with "Hvar") as %[Hq Ha]%FiniteMap.singleton_wf%of_RA.to_ura_wf%of_IrisRA.to_ra_wf%frac_agree_op_valid.
    done.
  Qed.
  (** Almost all the time, this is all you really need. *)
  Lemma ghost_var_agree γ a1 q1 a2 q2 :
    ghost_var γ q1 a1 -∗ ghost_var γ q2 a2 -∗ ⌜a1 = a2⌝.
  Proof.
    iIntros "Hvar1 Hvar2".
    iDestruct (ghost_var_valid_2 with "Hvar1 Hvar2") as %[_ ?]. done.
  Qed.


  (** This is just an instance of fractionality above, but that can be hard to find. *)
  Lemma ghost_var_split γ a q1 q2 :
    ghost_var γ (q1 + q2) a -∗ ghost_var γ q1 a ∗ ghost_var γ q2 a.
  Proof.
    iIntros "V". unseal.
    iApply OwnM_op.
    rewrite FiniteMap.singleton_add.
    rewrite of_RA.to_ura_add.
    rewrite of_IrisRA.to_ra_add.
    rewrite -dfrac_agree_op. rewrite dfrac_op_own.
    iFrame.
  Qed.

  (** Update the ghost variable to new value [b]. *)
  Lemma ghost_var_update b γ a :
    ghost_var γ 1 a ==∗ ghost_var γ 1 b.
  Proof.
    unseal. iApply OwnM_Upd.
    apply FiniteMap.singleton_updatable,
    of_RA.to_ura_updatable, of_IrisRA.to_ra_updatable.
    apply cmra_update_exclusive,frac_agree_valid.
    done.
  Qed.
  Lemma ghost_var_update_2 b γ a1 q1 a2 q2 :
    (q1 + q2 = 1)%Qp →
    ghost_var γ q1 a1 -∗ ghost_var γ q2 a2 ==∗ ghost_var γ q1 b ∗ ghost_var γ q2 b.
  Proof.
    iIntros (Hq) "V1 V2". unseal.
    iCombine "V1 V2" as "V".
    rewrite -OwnM_op. iApply Own_Upd; [|iFrame].
    rewrite !FiniteMap.singleton_add.
    rewrite !of_RA.to_ura_add.
    rewrite !of_IrisRA.to_ra_add.

    apply GRA.embed_updatable, FiniteMap.singleton_updatable,
    of_RA.to_ura_updatable, of_IrisRA.to_ra_updatable.

    apply frac_agree_update_2. done.
  Qed.
  Lemma ghost_var_update_halves b γ a1 a2 :
    ghost_var γ (1/2) a1 -∗
    ghost_var γ (1/2) a2 ==∗
    ghost_var γ (1/2) b ∗ ghost_var γ (1/2) b.
  Proof. iApply ghost_var_update_2. apply Qp.half_half. Qed.

End lemmas.

Section SPROP.

Context {A : Type}.
Context {STT : StateTypes}.
Context `{sub : @SRA.subG Γ Σ}.
Context {TLRASs : TLRAs_small STT Γ}.
Context {TLRAS : TLRAs STT Γ Σ}.

Context `{HasGhostVar : @GRA.inG (ghost_varURA A) Γ}.

  Definition syn_ghost_var {n} γ q a : sProp n := (➢(ghost_var_ra γ q a))%S.

  Lemma red_syn_ghost_var n γ q a :
    ⟦syn_ghost_var γ q a, n⟧ = ghost_var γ q a.
  Proof.
    unfold syn_ghost_var. red_tl. ss.
  Qed.

End SPROP.

Ltac red_tl_ghost_var := try rewrite ! red_syn_ghost_var.
