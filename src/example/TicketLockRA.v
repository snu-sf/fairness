From sflib Require Import sflib.
From Fairness Require Import Any PCM IProp IPM IPropAux.
From Fairness Require Export AuthExclAnysRA.
From stdpp Require Import gmap.


Section Ticket.

  Definition _TicketRA : URA.t := Auth.t (URA.prod (Excl.t nat) (GsetK.t (K:=nat))).
  Definition TicketRA : URA.t := (nat ==> _TicketRA)%ra.

  Context `{Σ : GRA.t}.
  Context {HasTicketRA : @GRA.inG TicketRA Σ}.

  Definition TicketRA_Auth_base : _TicketRA :=
    (@Auth.black (URA.prod _ _) (Some 0 : Excl.t nat, Some ∅ : GsetK.t))
    ⋅ (@Auth.white (URA.prod _ _) (Some 0 : Excl.t nat, Some ∅ : GsetK.t)).

  Definition TicketRA_Auth : iProp :=
    (∃ (U : nat), OwnM ((fun k => if (lt_dec k U)
                             then ε
                             else TicketRA_Auth_base) : TicketRA)).

  Definition Ticket_black_ra (r : nat) (o : nat) (D : gset nat) : TicketRA :=
    maps_to_res r (Auth.black (((Some o) : Excl.t nat, Some D : GsetK.t) : URA.prod _ _)).
  Definition Ticket_black r o D := OwnM (Ticket_black_ra r o D).

  Definition Ticket_locked_ra (r : nat) (o : nat) : TicketRA :=
    maps_to_res r (Auth.white (((Some o) : Excl.t nat, Some ∅ : GsetK.t) : URA.prod _ _)).
  Definition Ticket_locked r o := OwnM (Ticket_locked_ra r o).

  Definition Ticket_issued_ra (r : nat) (m tid k : nat) : TicketRA :=
    maps_to_res r (Auth.white ((ε : Excl.t nat, Some {[m]} : GsetK.t) : URA.prod _ _)).
  Definition Ticket_issued r m tid k := OwnM (Ticket_issued_ra r m tid k).

  Lemma Ticket_alloc o D :
    TicketRA_Auth ⊢ |==> TicketRA_Auth ∗ (∃ r, Ticket_black r o D ∗ Ticket_locked r o).
  Proof.
    iIntros "[%U BASE]".
    assert (URA.updatable
      ((λ k, if lt_dec k U then ε else TicketRA_Auth_base) : TicketRA)
      (((λ k, if lt_dec k (S U) then ε else TicketRA_Auth_base) : TicketRA)
        ⋅ (maps_to_res U TicketRA_Auth_base))) as UPD.
    { ur. apply pointwise_updatable. i. unfold maps_to_res. des_ifs; try lia.
      - rewrite URA.unit_idl. reflexivity.
      - rewrite URA.unit_idl. reflexivity.
      - rewrite URA.unit_id. reflexivity.  }
    iMod (OwnM_Upd with "BASE") as "[A B]". apply UPD.
    assert (URA.updatable
      (maps_to_res U TicketRA_Auth_base)
      (Ticket_black_ra U o D
        ⋅ maps_to_res U (Auth.white ((Some o : Excl.t nat, Some D : GsetK.t) : URA.prod _ _)))).
    { ur. apply pointwise_updatable. i.
      unfold Ticket_black_ra, Ticket_locked_ra, maps_to_res, TicketRA_Auth_base.
      des_ifs; cycle 1. rewrite URA.unit_id. reflexivity.
      apply Auth.auth_update. ii. des. split. ur. split; ur; auto.
      ur in FRAME. des_ifs. ur in H1. des_ifs. ur in H0. des_ifs. ur. f_equal. ur. auto.
      set_unfold. ur. des_ifs. f_equal. set_solver. set_solver. }
    iMod (OwnM_Upd with "B") as "[C D]". apply H.
    assert (URA.updatable
      (maps_to_res U (Auth.white ((Some o : Excl.t nat, Some D : GsetK.t) : URA.prod _ _)))
      (maps_to_res U (Auth.white ((Some o : Excl.t nat, Some ∅ : GsetK.t) : URA.prod _ _)))).
    { apply maps_to_updatable. etrans.
      { apply Auth.auth_dup_white. instantiate (1:=(ε, Some ∅)). ur. f_equal; ur; des_ifs.
        f_equal. set_solver. set_solver. }
      rewrite <- URA.unit_id. apply URA.updatable_add; cycle 1. apply URA.updatable_unit.
      ii. ur in H0. des_ifs.
      { destruct f0. ur in H0. des. ur in H0. des_ifs.
        ur in H1. des_ifs. ur. rewrite unfold_prod_add. ur. split; ur; auto.
        des_ifs. set_solver. }
      { des. ur. split; auto. destruct H0. destruct x.
        exists (c, c0 ⋅ Some D). repeat (rewrite unfold_prod_add; des_ifs). f_equal.
        destruct c4; destruct c0; ur; des_ifs; ss; des_ifs. f_equal. all:set_solver. } }
    iMod (OwnM_Upd with "D") as "E". apply H0.
    iModIntro. iSplitL "A".
    { iExists (S U). auto. }
    { iExists U. iSplitL "C". auto. unfold Ticket_locked, Ticket_locked_ra. auto. }
    
  (** Properties. *)
  (* TODO : prove lemmas. *)
  Lemma ticketlockB_alloc :
    TicketLockRA_Auth ⊢ |==> (TicketLockRA_Auth ∗ (∃ r, tklockB r 0 ∅ ∗ tklock_locked r 0)).
  Proof.
    iIntros "[%U BASE]". iModIntro. iSplitL.
    { iExists (S U). }

End Ticket.
Section TICKETS.
  Definition TicketsRA : URA.t := (nat ==> AuthExclAnysRA)%ra.
  
End TICKETS.
