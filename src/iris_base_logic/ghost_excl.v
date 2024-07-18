From sflib Require Import sflib.
From Fairness Require Import IPM PCM IProp IPropAux.
From Fairness Require Import MonotoneRA.
From Fairness Require Import TemporalLogic.
From Fairness Require Export excl cmra.
From iris.prelude Require Import prelude options.

Local Open Scope iris_algebra_scope.

Definition ghost_exclURA (A : Type) : URA.t := @FiniteMap.t (of_RA.t (of_IrisRA.t (exclR A))).

Section definitions.
  Context `{Σ : GRA.t}.
  Context {A : Type}.
  Implicit Types a : A.
  Context `{GEXCLRA : @GRA.inG (ghost_exclURA A) Σ}.

  Definition ghost_excl_ra (γ : nat) a : ghost_exclURA A :=
    FiniteMap.singleton γ
      (of_RA.to_ura (of_IrisRA.to_ra (Excl a))).

  Definition ghost_excl (γ : nat) a : iProp :=
    OwnM (ghost_excl_ra γ a).
End definitions.

Notation "'GEx' γ a " := (ghost_excl γ a) (at level 90, γ,a at level 1) : bi_scope.

Local Ltac unseal :=
  repeat unfold ghost_exclURA,ghost_excl_ra,ghost_excl.

Section lemmas.
  Context `{Σ : GRA.t}.
  Context {A : Type}.
  Implicit Types a : A.
  Context `{GEXCLRA : @GRA.inG (ghost_exclURA A) Σ}.

  Lemma ghost_excl_alloc a :
    ⊢ |==> ∃ γ, GEx γ a.
  Proof.
    iDestruct (@OwnM_unit _ _ GEXCLRA) as "H".

    iMod (OwnM_Upd_set with "H") as "[%RES [%HGmap Gmap]]".
    { apply FiniteMap.singleton_alloc.
      instantiate (1 := of_RA.to_ura (of_IrisRA.to_ra (Excl a)): of_RA.t (of_IrisRA.t (exclR A))).
      apply of_RA.to_ura_wf, of_IrisRA.to_ra_wf.
      done.
    }
    simpl in *. destruct HGmap as [γ ->].
    iModIntro. iExists γ. unseal.
    done.
  Qed.

  Lemma ghost_excl_exclusive γ a b :
    ⊢ GEx γ a -∗ GEx γ b -∗ False.
  Proof.
    iIntros "H1 H2". unseal.
    iCombine "H1" "H2" as "H".
    rewrite FiniteMap.singleton_add.
    rewrite of_RA.to_ura_add.
    rewrite of_IrisRA.to_ra_add.
    iDestruct (OwnM_valid with "H") as %H%FiniteMap.singleton_wf%of_RA.to_ura_wf%of_IrisRA.to_ra_wf.
    done.
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
    unfold syn_ghost_excl. red_tl. ss.
  Qed.

End SPROP.

Ltac red_tl_ghost_excl := (try rewrite ! red_syn_ghost_excl).

Notation "'GEx' γ a " := (syn_ghost_excl γ a) (at level 90, γ,a at level 1) : sProp_scope.
