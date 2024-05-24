From sflib Require Import sflib.
From Fairness Require Import PCM IProp IPM IndexedInvariants.
From Fairness Require Import ISim SimDefaultRA LiveObligations SimWeakest LogicSyntaxHOAS.
From Fairness Require Export TemporalLogic.
From stdpp Require Export coPset gmap namespaces.
From Fairness Require Import SCMem.
Require Import Program.


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

  Definition ExclUnitsRA : URA.t := (nat ==> (Excl.t unit))%ra.
  Definition AuthExclRA (A : Type) : URA.t := (Auth.t (Excl.t A)).

End AUXRAS.

Section XAINTERP.

  Context `{Σ : GRA.t}.
  (* SCMem related RAs. *)
  Context `{MEMRA: @GRA.inG memRA Σ}.
  (* Map from nat to Excl unit RA. *)
  Context `{EXCLUNITS: @GRA.inG ExclUnitsRA Σ}.
  (* Auth Excl Qp RA. *)
  Context `{AUEX_QP: @GRA.inG (AuthExclRA Qp) Σ}.

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
Notation "'➢' s" := (⟨Atom.aux (AA:=XAtom) s⟩)%F (at level 90) : formula_scope.
Notation "l ↦ v" := (➢ (scm_points_to l v))%F (at level 90) : formula_scope.

Section TLRAS.

  Class TLRAs (STT : StateTypes) (Σ : GRA.t) :=
    {
      (* Invariant related default RAs *)
      _OWNESRA : @GRA.inG OwnEsRA Σ;
      _OWNDSRA : @GRA.inG OwnDsRA Σ;
      _IINVSETRA : @GRA.inG (IInvSetRA (@Formula XAtom STT)) Σ;
      (* State related default RAs *)
      _THDRA: @GRA.inG ThreadRA Σ;
      _STATESRC: @GRA.inG (stateSrcRA st_src_type) Σ;
      _STATETGT: @GRA.inG (stateTgtRA st_tgt_type) Σ;
      _IDENTSRC: @GRA.inG (identSrcRA id_src_type) Σ;
      _IDENTTGT: @GRA.inG (identTgtRA id_tgt_type) Σ;
      (* Liveness logic related default RAs *)
      _OBLGRA: @GRA.inG ObligationRA.t Σ;
      _EDGERA: @GRA.inG EdgeRA Σ;
      _ARROWSHOTRA: @GRA.inG ArrowShotRA Σ;
      _ARROWRA: @GRA.inG (@ArrowRA id_tgt_type Formula) Σ;
      (* SCMem related RAs *)
      _MEMRA: @GRA.inG memRA Σ;
      (* Map from nat to Excl unit RA. *)
      _EXCLUNITS: @GRA.inG ExclUnitsRA Σ;
      (* Auth Excl Qp RA. *)
      _AUEX_QP: @GRA.inG (AuthExclRA Qp) Σ;
    }.

End TLRAS.

Section EXPORT.

  Context {STT : StateTypes}.
  Context `{Σ : GRA.t}.
  Context {TLRAS : TLRAs STT Σ}.

  (* Invariant related default RAs *)
  #[export] Instance OWNESRA : @GRA.inG OwnEsRA Σ := _OWNESRA.
  #[export] Instance OWNDSRA : @GRA.inG OwnDsRA Σ:= _OWNDSRA.
  #[export] Instance IINVSETRA : @GRA.inG (IInvSetRA Formula) Σ:= _IINVSETRA.
  (* State related default RAs *)
  #[export] Instance THDRA: @GRA.inG ThreadRA Σ:= _THDRA.
  #[export] Instance STATESRC: @GRA.inG (stateSrcRA st_src_type) Σ:= _STATESRC.
  #[export] Instance STATETGT: @GRA.inG (stateTgtRA st_tgt_type) Σ:= _STATETGT.
  #[export] Instance IDENTSRC: @GRA.inG (identSrcRA id_src_type) Σ:= _IDENTSRC.
  #[export] Instance IDENTTGT: @GRA.inG (identTgtRA id_tgt_type) Σ:= _IDENTTGT.
  (* Liveness logic related default RAs *)
  #[export] Instance OBLGRA: @GRA.inG ObligationRA.t Σ:= _OBLGRA.
  #[export] Instance EDGERA: @GRA.inG EdgeRA Σ:= _EDGERA.
  #[export] Instance ARROWSHOTRA: @GRA.inG ArrowShotRA Σ:= _ARROWSHOTRA.
  #[export] Instance ARROWRA: @GRA.inG (@ArrowRA id_tgt_type Formula) Σ:= _ARROWRA.
  (* SCMem related RAs *)
  #[export] Instance MEMRA: @GRA.inG memRA Σ:= _MEMRA.
  (* Map from nat to Excl unit RA. *)
  #[export] Instance EXCLUNITS: @GRA.inG ExclUnitsRA Σ:= _EXCLUNITS.
  (* Auth Excl Qp RA. *)
  #[export] Instance AUEX_QP: @GRA.inG (AuthExclRA Qp) Σ:= _AUEX_QP.

End EXPORT.

Section TL.

  Context {STT : StateTypes}.

  Context `{Σ : GRA.t}.
  (* (* Invariant related default RAs *) *)
  (* Context `{OWNESRA : @GRA.inG OwnEsRA Σ}. *)
  (* Context `{OWNDSRA : @GRA.inG OwnDsRA Σ}. *)
  (* Context `{IINVSETRA : @GRA.inG (IInvSetRA Formula) Σ}. *)
  (* (* State related default RAs *) *)
  (* Context `{THDRA: @GRA.inG ThreadRA Σ}. *)
  (* Context `{STATESRC: @GRA.inG (stateSrcRA st_src_type) Σ}. *)
  (* Context `{STATETGT: @GRA.inG (stateTgtRA st_tgt_type) Σ}. *)
  (* Context `{IDENTSRC: @GRA.inG (identSrcRA id_src_type) Σ}. *)
  (* Context `{IDENTTGT: @GRA.inG (identTgtRA id_tgt_type) Σ}. *)
  (* (* Liveness logic related default RAs *) *)
  (* Context `{OBLGRA: @GRA.inG ObligationRA.t Σ}. *)
  (* Context `{EDGERA: @GRA.inG EdgeRA Σ}. *)
  (* Context `{ONESHOTRA: @GRA.inG ArrowShotRA Σ}. *)
  (* Context `{ARROWRA: @GRA.inG (@ArrowRA id_tgt_type Formula) Σ}. *)
  (* (* SCMem related RAs *) *)
  (* Context `{MEMRA: @GRA.inG memRA Σ}. *)
  (* (* Map from nat to Excl unit RA. *) *)
  (* Context `{EXCLUNITS: @GRA.inG ExclUnitsRA Σ}. *)
  (* (* Auth Excl Qp RA. *) *)
  (* Context `{AUEX_QP: @GRA.inG (AuthExclRA Qp) Σ}. *)

  Context {TLRAS : TLRAs STT Σ}.

  Global Instance TLSet : @IInvSet Σ (@Formula XAtom STT) := SynIISet.

End TL.
