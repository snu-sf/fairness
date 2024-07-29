From sflib Require Import sflib.
(* Port of https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris/base_logic/lib/ghost_var.v into FOS style iProp *)
(** A simple "ghost variable" of arbitrary type with fractional ownership.
Can be mutated when fully owned. *)

From Fairness Require Import IPM PCM  IPropAux TemporalLogic.
From iris.algebra Require Import dfrac_agree proofmode_classes frac.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import proofmode.
From Fairness Require Import OwnGhost.
From iris.prelude Require Import options.

Definition ghost_varURA (A : Type) : ucmra := OwnG.t (dfrac_agreeR (leibnizO A)).

Section definitions.
  Context {A : Type}.
  Context `{GHOSTVARURA : @GRA.inG (ghost_varURA A) Σ}.

  Local Definition ghost_var_ra_def
    (γ : nat) (q : Qp) (a : A) : ghost_varURA A :=
    OwnG.ra γ (to_frac_agree q (a : leibnizO A)).
  Local Definition ghost_var_ra_aux : seal (@ghost_var_ra_def).
  Proof. by eexists. Qed.
  Definition ghost_var_ra := ghost_var_ra_aux.(unseal).
  Local Definition ghost_var_ra_unseal :
    @ghost_var_ra = @ghost_var_ra_def := ghost_var_ra_aux.(seal_eq).

  Local Definition ghost_var_def
      (γ : nat) (q : Qp) (a : A) : iProp Σ :=
    OwnG.to_t γ (to_frac_agree q (a : leibnizO A)).
  Local Definition ghost_var_aux : seal (@ghost_var_def).
  Proof. by eexists. Qed.
  Definition ghost_var := ghost_var_aux.(unseal).
  Local Definition ghost_var_unseal :
    @ghost_var = @ghost_var_def := ghost_var_aux.(seal_eq).
End definitions.

Local Ltac unseal := rewrite
  ?ghost_var_ra_unseal /ghost_var_ra_def
  ?ghost_var_unseal /ghost_var_def.

Section lemmas.
  Context `{Σ : GRA.t}.
  Context `{GHOSTVARURA : @GRA.inG (ghost_varURA A) Σ}.
  Implicit Types (a b : A) (q : Qp).

  Global Instance ghost_var_fractional γ a : Fractional (λ q, ghost_var γ q a).
  Proof. intros q1 q2. unseal. rewrite -own_op -frac_agree_op //. Qed.
  Global Instance ghost_var_as_fractional γ a q :
    AsFractional (ghost_var γ q a) (λ q, ghost_var γ q a) q.
  Proof. split; [done|]. apply _. Qed.

  Lemma ghost_var_alloc a :
    ⊢ |==> ∃ γ, ghost_var γ 1 a.
  Proof. unseal. iApply own_alloc. done. Qed.

  Lemma ghost_var_valid_2 γ a1 q1 a2 q2 :
    ghost_var γ q1 a1 -∗ ghost_var γ q2 a2 -∗ ⌜(q1 + q2 ≤ 1)%Qp ∧ a1 = a2⌝.
  Proof.
    unseal. iIntros "Hvar1 Hvar2".
    iCombine "Hvar1 Hvar2" as "Hvar".
    iDestruct (own_valid with "Hvar") as %[Hq Ha]%frac_agree_op_valid.
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
  Proof. iIntros "[$$]". Qed.

  (** Update the ghost variable to new value [b]. *)
  Lemma ghost_var_update b γ a :
    ghost_var γ 1 a ==∗ ghost_var γ 1 b.
  Proof.
    unseal. iApply own_update. apply cmra_update_exclusive. done.
  Qed.
  Lemma ghost_var_update_2 b γ a1 q1 a2 q2 :
    (q1 + q2 = 1)%Qp →
    ghost_var γ q1 a1 -∗ ghost_var γ q2 a2 ==∗ ghost_var γ q1 b ∗ ghost_var γ q2 b.
  Proof.
    intros Hq. unseal. rewrite -own_op. iApply own_update_2.
    apply frac_agree_update_2. done.
  Qed.
  Lemma ghost_var_update_halves b γ a1 a2 :
    ghost_var γ (1/2) a1 -∗
    ghost_var γ (1/2) a2 ==∗
    ghost_var γ (1/2) b ∗ ghost_var γ (1/2) b.
  Proof. iApply ghost_var_update_2. apply Qp.half_half. Qed.

  (** Framing support *)
  Global Instance frame_ghost_var p γ a q1 q2 RES :
    FrameFractionalHyps p (ghost_var γ q1 a) (λ q, ghost_var γ q a)%I RES q1 q2 →
    Frame p (ghost_var γ q1 a) (ghost_var γ q2 a) RES | 5.
  Proof. apply: frame_fractional. Qed.
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
    unfold syn_ghost_var. red_tl. unseal. rewrite own_to_t_eq. ss.
  Qed.

End SPROP.

Ltac red_tl_ghost_var := try rewrite ! red_syn_ghost_var.
