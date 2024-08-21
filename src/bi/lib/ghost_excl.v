From sflib Require Import sflib.

From Fairness Require Import IPM PCM  IPropAux TemporalLogic.
From iris.algebra Require Import excl proofmode_classes.
From iris.proofmode Require Import proofmode.
From Fairness Require Import OwnGhost.
From iris.prelude Require Import options.

Definition ghost_exclURA (A : Type) : ucmra := ownRA (exclR (leibnizO A)).

Section definitions.
  Context `{Σ : GRA.t}.
  Context {A : Type}.
  Implicit Types a : A.
  Context `{GEXCLRA : @GRA.inG (ghost_exclURA A) Σ}.

  Definition ghost_excl_ra (γ : nat) a : ghost_exclURA A :=
    to_own γ (Excl (a : leibnizO A)).

  Definition ghost_excl (γ : nat) a : iProp Σ :=
    own γ (Excl (a : leibnizO A)).
End definitions.

Notation "'GEx' γ a " := (ghost_excl γ a) (at level 90, γ,a at level 1) : bi_scope.

Local Ltac unseal :=
  rewrite /ghost_excl_ra /ghost_excl.

Section lemmas.
  Context `{Σ : GRA.t}.
  Context {A : Type}.
  Implicit Types a : A.
  Context `{GEXCLRA : @GRA.inG (ghost_exclURA A) Σ}.

  Lemma ghost_excl_alloc a :
    ⊢ |==> ∃ γ, GEx γ a.
  Proof. iApply own_alloc. done. Qed.

  Lemma ghost_excl_exclusive γ a b :
    ⊢ GEx γ a -∗ GEx γ b -∗ False.
  Proof.
    iIntros "H1 H2". unseal.
    iDestruct (own_valid_2 with "H1 H2") as %[].
  Qed.
End lemmas.

Section SPROP.

Context {A : Type}.
Implicit Types a : A.

Context {STT : StateTypes}.
Context `{sub : @SRA.subG Γ Σ}.
Context {TLRASs : TLRAs_small STT Γ}.
Context {TLRAS : TLRAs STT Γ Σ}.

Context `{GEXCLRA : @GRA.inG (ghost_exclURA A) Γ}.

  Definition syn_ghost_excl {n} γ a : sProp n := (➢(ghost_excl_ra γ a))%S.

  Lemma red_syn_ghost_excl n γ a :
    ⟦syn_ghost_excl γ a, n⟧ = ghost_excl γ a.
  Proof.
    unfold syn_ghost_excl. red_tl. unseal. rewrite own_to_own_eq. ss.
  Qed.

End SPROP.

Ltac red_tl_ghost_excl := (try rewrite ! red_syn_ghost_excl).

Notation "'GEx' γ a " := (syn_ghost_excl γ a) (at level 90, γ,a at level 1) : sProp_scope.
