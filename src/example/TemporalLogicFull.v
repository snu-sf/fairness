From sflib Require Import sflib.
From Fairness Require Import PCM IProp IPM IndexedInvariants.
From Fairness Require Import ISim SimDefaultRA LiveObligations SimWeakest LogicSyntaxHOAS.
From Fairness Require Export TemporalLogic.
From stdpp Require Export coPset gmap namespaces.
From Fairness Require Export AuthExclAnysRA LifetimeRA.
From Fairness Require Export SCMem TicketLockRA.
Require Import Program.

(** User-defined auxiliary atoms. *)

Section AUXRAS.

  Definition ExclUnitRA : URA.t := ((Excl.t unit))%ra.
  Definition ExclUnitsRA : URA.t := (nat ==> (Excl.t unit))%ra.
  Definition AuthExclRA (A : Type) : URA.t := (Auth.t (Excl.t A)).

End AUXRAS.

Section XADEF.

  Variant xatom :=
    (* SCMem related. *)
    | scm_points_to (p v : SCMem.val)
    | scm_points_tos (p : SCMem.val) (vs : list SCMem.val)
    | scm_memory_black (m : SCMem.t)
    (* Lifetime RA. *)
    | live (k : nat) {T : Type} (t : T) (q : Qp)
    | dead (k : nat) {T : Type} (t : T)
    (* Map from nat to Auth Excl Any. *)
    | auexa
    | auexa_b (r : nat) {T : Type} (t : T)
    | auexa_w (r : nat) {T : Type} (t : T)
    (* For ticket lock. *)
    | tk_auth
    | tk_b (r : nat) (o : nat) (D : gset nat)
    | tk_locked (r : nat) (o : nat)
    | tk_issued (r : nat) (m : nat)
    | otk_auth
    | otk_b (r : nat) (m tid k : nat)
    | otk_w (r : nat) (m tid k : nat)
    (* Excl unit. *)
    | excl
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
      _MEMRA : @GRA.inG memRA Σ;
      (* Lifetime RA. *)
      _HasLifetime : @GRA.inG Lifetime.t Σ;
      (* Map from nat to Auth Excl Any. *)
      _AuthExclAnys : @GRA.inG AuthExclAnysRA Σ;
      (* For ticket lock. *)
      _HasTicket : @GRA.inG TicketRA Σ;
      _HasOblTicket : @GRA.inG OblTicketRA Σ;
      (* Excl unit RA. *)
      _EXCLUNIT : @GRA.inG ExclUnitRA Σ;
      (* Map from nat to Excl unit RA. *)
      _EXCLUNITS : @GRA.inG ExclUnitsRA Σ;
      (* Auth Excl Qp RA. *)
      _AUEX_QP : @GRA.inG (AuthExclRA Qp) Σ;
    }.

End AUXRAS.

Section EXPORT.

  Context `{Σ : GRA.t}.
  Context {AUXRAS : AUXRAs Σ}.

  (* SCMem related RAs *)
  #[export] Instance MEMRA : @GRA.inG memRA Σ:= _MEMRA.
  (* Lifetime RA. *)
  #[export] Instance HasLifetime : @GRA.inG Lifetime.t Σ:= _HasLifetime.
  (* Excl unit RA. *)
  #[export] Instance EXCLUNIT : @GRA.inG ExclUnitRA Σ:= _EXCLUNIT.
  (* Map from nat to Excl unit RA. *)
  #[export] Instance EXCLUNITS : @GRA.inG ExclUnitsRA Σ:= _EXCLUNITS.
  (* Auth Excl Qp RA. *)
  #[export] Instance AUEX_QP : @GRA.inG (AuthExclRA Qp) Σ:= _AUEX_QP.
  (* Map from nat to Auth Excl Any. *)
  #[export] Instance AuthExclAnys : @GRA.inG AuthExclAnysRA Σ := _AuthExclAnys.
  (* For ticket lock. *)
  #[export] Instance HasTicket : @GRA.inG TicketRA Σ:= _HasTicket.
  #[export] Instance HasOblTicket : @GRA.inG OblTicketRA Σ:= _HasOblTicket.

End EXPORT.

Section XAINTERP.

  Context `{Σ : GRA.t}.
  Context {AUXRAS : AUXRAs Σ}.

  Definition xatom_sem (xa : xatom) : iProp :=
    match xa with
    | scm_points_to p v => points_to p v
    | scm_points_tos p vs => points_tos p vs
    | scm_memory_black m => memory_black m
    (* Lifetime RA. *)
    | live k t q => Lifetime.pending k t q
    | dead k t => Lifetime.shot k t
    (* Map from nat to Auth Excl Any. *)
    | auexa => AuExAny_gt
    | auexa_b r t => AuExAnyB r t
    | auexa_w r t => AuExAnyW r t
    (* For ticket lock. *)
    | tk_auth => TicketRA_Auth
    | tk_b r o D => Ticket_black r o D
    | tk_locked r o => Ticket_locked r o
    | tk_issued r m => Ticket_issued r m
    | otk_auth => OblTicketRA_Auth
    | otk_b r tk tid obl => OblTicket_black r tk tid obl
    | otk_w r tk tid obl => OblTicket_white r tk tid obl
    (* Excl unit. *)
    | excl => OwnM (Some tt : ExclUnitRA)
    | excls_auth =>
        (∃ (U : nat), OwnM ((fun k => if (lt_dec k U) then ε else (Some tt : Excl.t unit)) : ExclUnitsRA))
    | excls k => OwnM ((maps_to_res k (Some tt : Excl.t unit)) : ExclUnitsRA)
    | auex_b_Qp q => OwnM (Auth.black ((Some q) : Excl.t Qp) : AuthExclRA Qp)
    | auex_w_Qp q => OwnM (Auth.white ((Some q) : Excl.t Qp) : AuthExclRA Qp)
    end.

  Global Instance XAInterp : AAInterp := { aaintp := xatom_sem }.

End XAINTERP.

(** Notations. *)
Notation "'➢' s" := (⟨Atom.aux (AA:=XAtom) s⟩)%F (at level 50) : formula_scope.
Notation "l ↦ v" := (➢(scm_points_to l v))%F (at level 90) : formula_scope.

Section TLFULL.

  Context {STT : StateTypes}.

  Context `{Σ : GRA.t}.
  Context {TLRAS : @TLRAs XAtom STT Σ}.
  Context {AUXRAS : AUXRAs Σ}.

  Global Instance TLSet : @IInvSet Σ (@Formula XAtom STT) := SynIISet.

End TLFULL.
