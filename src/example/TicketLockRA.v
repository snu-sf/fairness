From sflib Require Import sflib.
From Fairness Require Import Any PCM IProp IPM IPropAux.
From Fairness Require Export AuthExclAnysRA.
From stdpp Require Import gmap.


Section TKLOCK.

  Definition _TicketLockRA : URA.t := URA.prod (Auth.t (URA.prod (Excl.t nat) (GsetK.t (K:=nat)))) AuthExclAnysRA.
  Definition TicketLockRA : URA.t := (nat ==> _TicketLockRA)%ra.

  Context `{Σ : GRA.t}.
  Context {HasTicketLockRA : @GRA.inG TicketLockRA Σ}.

  Definition TicketLockRA_Auth_base : _TicketLockRA :=
    (((@Auth.black (URA.prod _ _) (Some 0 : Excl.t nat, Some ∅ : GsetK.t))
        ⋅ (@Auth.white (URA.prod _ _) (Some 0 : Excl.t nat, Some ∅ : GsetK.t))),
      ((fun k => (Auth.black (Some (tt ↑) : Excl.t Any.t) ⋅ Auth.white (Some (tt ↑) : Excl.t Any.t))) : AuthExclAnysRA)
    ).

  Definition TicketLockRA_Auth : iProp :=
    (∃ (U : nat), OwnM ((fun k => if (lt_dec k U)
                             then ε
                             else TicketLockRA_Auth_base) : TicketLockRA)).


  Definition tklockB_ra (r : nat) (o : nat) (D : gset nat) : TicketLockRA :=
    (maps_to_res r (((Auth.black (((Some o) : Excl.t nat, Some D : GsetK.t) : URA.prod _ _)),
                      AuExAny_ra (fun k => gset_elem_of_dec k D)) : URA.prod _ _)).
  Definition tklockB r o D := OwnM (tklockB_ra r o D).

  Definition tklock_locked_ra (r : nat) (o : nat) : TicketLockRA :=
    (maps_to_res r ((Auth.white (((Some o) : Excl.t nat, Some ∅ : GsetK.t) : URA.prod _ _), ε) : URA.prod _ _)).
  Definition tklock_locked r o := OwnM (tklock_locked_ra r o).

  (* The issuing thread holds my ticket -> (my thread id, and my obligation id). *)
  Definition tklock_issued_ra (r : nat) (m tid k : nat) : TicketLockRA :=
    (maps_to_res r ((Auth.white ((ε : Excl.t nat, Some {[m]} : GsetK.t) : URA.prod _ _), AuExAnyW_ra m (tid, k)) : URA.prod _ _)).
  Definition tklock_issued r m tid k := OwnM (tklock_issued_ra r m tid k).

  (* The invariant holds ticket -> (thread id, obligation id) for the waiting threads. *)
  Definition tklock_wait_ra (r : nat) (m tid k : nat) : TicketLockRA :=
    (maps_to_res r ((Auth.white ((ε : Excl.t nat, Some ∅ : GsetK.t) : URA.prod _ _), AuExAnyB_ra m (tid, k)) : URA.prod _ _)).
  Definition tklock_wait r m tid k := OwnM (tklock_wait_ra r m tid k).


  (** Properties. *)

  (* TODO : prove lemmas. *)

End TKLOCK.
