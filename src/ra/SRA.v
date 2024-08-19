From sflib Require Import sflib.
From Fairness.base_logic Require Import lib.iprop lib.own.

From iris.prelude Require Import options.

Module SRA.
(** Small resource algebras *)

(** It is a bit annoying to make things work with iris's CMRA
    management mechanism.

    Ideally, we would have an instance of
    [@SRA.subG Γ Σ → cmraG Γ → cmraG Σ],

    but since [Γ] is an [SRA.t], typeclass search gets stuck on

    the goal [cmraG Γ]. What is werid is that such statements can still type-check.

    The current hack is to explicitly use [to_gf] to convert
    [SRA.t] to [gFunctors]. Thus the above instance is something like

    [@SRA.subG Γ Σ → cmraG (to_gf Γ) → cmraG Σ]

    FIXME: actual solution seems to be the following setup.

    Class libGpreS Σ := {
      libGpreS_inG : inG Σ M;
    }.

    Class libGS Σ := LibGS  {
      libGS_inG :: inG Σ M;
      lib_name : gname
    }.

    Local Existing Instances libGS_inG libGpreS_inG.

    Section lib_lemmas.

    Context `{SRA.subG Γ Σ}
    Context `{!libGS Γ}.
    Notation iProp := (iProp Σ).

    ...

    End lib_lemmas.

    Section sProp.
    Context `{SRA.subG Γ Σ}
    Context `{!libGS Γ}.
    Context `{TLRASs : !TLRAs_small STT Γ}.
    Context `{TLRAS : !TLRAs STT Γ Σ}.
    Notation iProp := (iProp Σ).

    ...

    End sProp.

    Note that we force the libGS to live in SRA, not GRA.

    This ensures that when libGS_inG is embedded into Σ, the proof used in SRA.sub_inG.

    I still need to see if this works for composed libraries.
    I.e, need to see if stack proofs work.

    For this, it might help to seal everything to block definitions from leaking out.

    This also forces minimal code modifications in [bi/lib].

    Enforcing the libGS to live in SRA is not limiting as all libGS that are sound must live in it.
*)

  Section SRA.

    Class t := SRA_INTERNAL : gFunctors.
    (** Sub of an a [Γ : SRA.t] and [Σ : gfunctors]
      In particualr we **do not** use the subG typeclass from [iprop.v]. To ensure that werid unification failures don't happen.

      FIXME: this should be removed. However, it is needed for
      the sra_subG classes for fairness RAs, since they
      can't have definitions syntactically defined.
      Solution will be to overhaul TLogic atoms to be minimal, and change the dependency of
      fairness RA → tlogic
      to
      tlogic → fairness RA
    *)
    Class subG (Γ : t) (Σ : gFunctors) : Type := {
        subG_map : (fin (gFunctors_len Γ)) -> (fin (gFunctors_len Σ));
        subG_prf : forall i, gFunctors_lookup Σ (subG_map i) = gFunctors_lookup Γ i;
      }.

    Definition to_gf (Γ : SRA.t) : gFunctors := Γ.

    Coercion subG_map : subG >-> Funclass.
    Global Arguments subG _ _ : clear implicits.
  End SRA.

  Section SUB.

    Context `{sub : @subG Γ Σ}.

    Global Program Instance embed (i : fin (gFunctors_len Γ)) : inG Σ (gFunctors_lookup Γ i)
    := {
        inG_id := sub i;
      }.
    Next Obligation.
      ii. destruct sub as [Smap Sprf].
      rewrite -Sprf //.
    Qed.

    (* TODO: does this require to_gf or no? *)
    Global Program Instance in_subG `{M : cmra} `{emb : inG Γ M} : inG Σ M := {
        inG_id := sub (emb.(inG_id));
      }.
    Next Obligation.
      ii. destruct emb. subst. destruct sub as [? EQ].
      ss. rewrite EQ //.
    Qed.

  End SUB.

End SRA.
