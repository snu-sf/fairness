From sflib Require Import sflib.
From Fairness Require Import PCM IProp IPM IndexedInvariants.
From Fairness Require Import ISim SimDefaultRA LiveObligations SimWeakest LogicSyntaxHOAS.
From Fairness Require Export TemporalLogic.
From stdpp Require Export coPset gmap namespaces.
From Fairness Require Import SCMem.
Require Import Program.

(** User-defined auxiliary atoms. *)

Section AUXRAS.

  Definition ExclUnitsRA : URA.t := (nat ==> (Excl.t unit))%ra.
  Definition AuthExclRA (A : Type) : URA.t := (Auth.t (Excl.t A)).

End AUXRAS.

Section XADEF.

  Variant xatom :=
    (* SCMem related. *)
    | scm_points_to (p v : SCMem.val)
    | scm_points_tos (p : SCMem.val) (vs : list SCMem.val)
    | scm_memory_black (m : SCMem.t)
    (* Map from nat to Excl unit. *)
    | excls_auth
    | excls (k : nat)
    (* Auth Excl Qp *)
    | auex_b_Qp (q : Qp)
    | auex_w_Qp (q : Qp)
  .

  Global Instance XAtom : AuxAtom := { aAtom := xatom }.

End XADEF.

Section AUXRAS.

  Class AUXRAs (Σ : GRA.t) :=
    {
      (* SCMem related RAs *)
      _MEMRA: @GRA.inG memRA Σ;
      (* Map from nat to Excl unit RA. *)
      _EXCLUNITS: @GRA.inG ExclUnitsRA Σ;
      (* Auth Excl Qp RA. *)
      _AUEX_QP: @GRA.inG (AuthExclRA Qp) Σ;
    }.

End AUXRAS.

Section EXPORT.

  Context `{Σ : GRA.t}.
  Context {AUXRAS : AUXRAs Σ}.

  (* SCMem related RAs *)
  #[export] Instance MEMRA: @GRA.inG memRA Σ:= _MEMRA.
  (* Map from nat to Excl unit RA. *)
  #[export] Instance EXCLUNITS: @GRA.inG ExclUnitsRA Σ:= _EXCLUNITS.
  (* Auth Excl Qp RA. *)
  #[export] Instance AUEX_QP: @GRA.inG (AuthExclRA Qp) Σ:= _AUEX_QP.

End EXPORT.

Section XAINTERP.

  Context `{Σ : GRA.t}.
  Context {AUXRAS : AUXRAs Σ}.

  Definition xatom_sem (xa : xatom) : iProp :=
    match xa with
    | scm_points_to p v => points_to p v
    | scm_points_tos p vs => points_tos p vs
    | scm_memory_black m => memory_black m
    | excls_auth => (∃ (X : gset nat), OwnM ((fun k => if (gset_elem_of_dec k X) then ε else (Some tt : Excl.t unit)) : ExclUnitsRA))
    | excls k => OwnM ((maps_to_res k (Some tt : Excl.t unit)) : ExclUnitsRA)
    | auex_b_Qp q => OwnM (Auth.black ((Some q) : Excl.t Qp) : AuthExclRA Qp)
    | auex_w_Qp q => OwnM (Auth.white ((Some q) : Excl.t Qp) : AuthExclRA Qp)
    end.

  Global Instance XAInterp : AAInterp := { aaintp := xatom_sem }.

End XAINTERP.

(** Notations. *)
Notation "'➢' s" := (⟨Atom.aux (AA:=XAtom) s⟩)%F (at level 50) : formula_scope.
Notation "l ↦ v" := (➢ (scm_points_to l v))%F (at level 90) : formula_scope.


Section TLFULL.

  Context {STT : StateTypes}.

  Context `{Σ : GRA.t}.
  Context {TLRAS : @TLRAs XAtom STT Σ}.
  Context {AUXRAS : AUXRAs Σ}.

  Global Instance TLSet : @IInvSet Σ (@Formula XAtom STT) := SynIISet.

End TLFULL.
