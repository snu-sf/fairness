From sflib Require Import sflib.
From Fairness Require Import PCM IProp IPM IndexedInvariants.
From Fairness Require Import ISim SimDefaultRA LiveObligations SimWeakest LogicSyntaxHOAS.
From Fairness Require Export TemporalLogic.
From stdpp Require Export coPset gmap namespaces.
From Fairness Require Export AuthExclAnysRA LifetimeRA.
From Fairness Require Export SCMem TicketLockRA.
Require Import Program.

(** Collection of some useful auxiliary atoms. *)

Section AUXRAS.

  Class AUXRAs (Γ : SRA.t) :=
    {
      (* SCMem related RAs *)
      _MEMRA : @GRA.inG memRA Γ;
      (* Lifetime RA. *)
      _HasLifetime : @GRA.inG Lifetime.t Γ;
      (* Map from nat to Auth Excl Any. *)
      _AuthExclAnys : @GRA.inG AuthExclAnysRA Γ;
      (* For ticket lock. *)
      _HasTicketLock : @GRA.inG TicketLockRA Γ;
    }.

End AUXRAS.

Section EXPORT.

  Context `{AUXRAS : AUXRAs}.

  (* SCMem related RAs *)
  #[export] Instance MEMRA : @GRA.inG memRA Γ:= _MEMRA.
  (* Lifetime RA. *)
  #[export] Instance HasLifetime : @GRA.inG Lifetime.t Γ:= _HasLifetime.
  (* Excl unit RA. *)
  (* Map from nat to Auth Excl Any. *)
  #[export] Instance AuthExclAnys : @GRA.inG AuthExclAnysRA Γ := _AuthExclAnys.
  (* For ticket lock. *)
  #[export] Instance HasTicketLock : @GRA.inG TicketLockRA Γ:= _HasTicketLock.

End EXPORT.

Section XA.

  Context `{AUXRAS : AUXRAs}.

  (* SCMem related. *)

  Definition memory_black (m: SCMem.t): iProp :=
    OwnM (memory_resource_black m) ∧ ⌜SCMem.wf m⌝.

  Definition points_to (p: SCMem.val) (v: SCMem.val): iProp :=
    match p with
    | SCMem.val_ptr (blk, ofs) => OwnM (points_to_white blk ofs v)
    | _ => False
    end.

  Fixpoint points_tos (p: SCMem.val) (vs: list SCMem.val): iProp :=
    match vs with
    | vhd::vtl =>
        points_to p vhd ∗ points_tos (SCMem.val_add p 1) vtl
    | [] => True
    end.
  
  Definition scm_points_to p v => points_to p v
    | scm_points_tos p vs => points_tos p vs
    | scm_memory_black m => memory_black m

  Definition xatom_sem (xa : xatom) : iProp :=
    match xa with
    (* Lifetime RA. *)
    | live k t q => Lifetime.pending k t q
    | dead k t => Lifetime.shot k t
    (* Map from nat to Auth Excl Any. *)
    | auexa => AuExAny_gt
    | auexa_b r t => AuExAnyB r t
    | auexa_w r t => AuExAnyW r t
    (* For ticket lock. *)
    | tkl_auth => TicketLockRA_Auth
    | tkl_b r o D => tklockB r o D
    | tkl_locked r o => tklock_locked r o
    | tkl_issued r m tid k => tklock_issued r m tid k
    | tkl_wait r m tid k => tklock_wait r m tid k
    (* Excl unit. *)
    | excl => OwnM (Some tt : ExclUnitRA)
    | excls_auth =>
        (∃ (U : nat), OwnM ((fun k => if (lt_dec k U) then ε else (Some tt : Excl.t unit)) : ExclUnitsRA))
    | excls k => OwnM ((maps_to_res k (Some tt : Excl.t unit)) : ExclUnitsRA)
    | auex_b_Qp q => OwnM (Auth.black ((Some q) : Excl.t Qp) : AuthExclRA Qp)
    | auex_w_Qp q => OwnM (Auth.white ((Some q) : Excl.t Qp) : AuthExclRA Qp)
    end.

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
    | tkl_auth
    | tkl_b (r : nat) (o : nat) (D : gset nat)
    | tkl_locked (r : nat) (o : nat)
    | tkl_issued (r : nat) (m tid k : nat)
    | tkl_wait (r : nat) (m tid k : nat)
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

End XA.


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
    | tkl_auth => TicketLockRA_Auth
    | tkl_b r o D => tklockB r o D
    | tkl_locked r o => tklock_locked r o
    | tkl_issued r m tid k => tklock_issued r m tid k
    | tkl_wait r m tid k => tklock_wait r m tid k
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
