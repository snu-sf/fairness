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

  Definition Ticket_issued_ra (r : nat) (m : nat) : TicketRA :=
    maps_to_res r (Auth.white ((ε : Excl.t nat, Some {[m]} : GsetK.t) : URA.prod _ _)).
  Definition Ticket_issued r m := OwnM (Ticket_issued_ra r m).

  (** Properties. *)

  Lemma TicketRA_alloc o D :
    TicketRA_Auth ⊢ ∃ r, |==> TicketRA_Auth ∗ Ticket_black r o D ∗ Ticket_locked r o.
  Proof.
    iIntros "[%U BASE]". iExists U.
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
    { iSplitL "C". auto. unfold Ticket_locked, Ticket_locked_ra. auto. }
  Qed.

End Ticket.

Section OblTicket.
  Definition OblTicketRA : URA.t := (nat ==> AuthExclAnysRA)%ra.

  Context `{HasOblTicketRA : @GRA.inG OblTicketRA Σ}.

  Definition OblTicketRA_base : AuthExclAnysRA :=
    (fun k =>
      (Auth.black (Some (tt ↑) : Excl.t Any.t) ⋅ Auth.white (Some (tt ↑) : Excl.t Any.t))).

  Definition OblTicketRA_Auth : iProp :=
    ∃ (U : nat), OwnM ((fun k => if (lt_dec k U) then ε else OblTicketRA_base) : OblTicketRA).
  
  Definition OblTicket_black_ra (r tk: nat) (tid obl : nat) : OblTicketRA :=
    maps_to_res r (AuExAnyB_ra tk (tid, obl)).
  Definition OblTicket_black (r tk tid obl : nat) : iProp :=
    OwnM (OblTicket_black_ra r tk tid obl).

  Definition OblTicket_white_ra (r tk: nat) (tid obl : nat) : OblTicketRA :=
    maps_to_res r (AuExAnyW_ra tk (tid, obl)).
  Definition OblTicket_white (r tk tid obl : nat) : iProp :=
    OwnM (OblTicket_white_ra r tk tid obl).
  
  
  Lemma OblTicket_alloc tk tid obl :
    OblTicketRA_Auth ⊢
      ∃ r, |==> OblTicketRA_Auth ∗ OblTicket_black r tk tid obl ∗ OblTicket_white r tk tid obl.
  Proof.
    iIntros "[%U BASE]". iExists U.
    assert (URA.updatable
      ((λ k, if lt_dec k U then ε else OblTicketRA_base) : OblTicketRA)
      (((λ k, if lt_dec k (S U) then ε else OblTicketRA_base) : OblTicketRA)
        ⋅ (maps_to_res U OblTicketRA_base))) as UPD.
    { ur. apply pointwise_updatable. i. unfold maps_to_res. des_ifs; try lia.
      - rewrite URA.unit_idl. reflexivity.
      - rewrite URA.unit_idl. reflexivity.
      - rewrite URA.unit_id. reflexivity.  }
    iMod (OwnM_Upd with "BASE") as "[A B]". apply UPD.
    assert (URA.updatable
      (maps_to_res U OblTicketRA_base)
      (OblTicket_black_ra U tk tid obl ⋅ OblTicket_white_ra U tk tid obl)).
    { unfold OblTicket_black_ra, OblTicket_white_ra.
      setoid_rewrite maps_to_res_add. apply maps_to_updatable.
      unfold OblTicketRA_base, AuExAnyB_ra, AuExAnyW_ra.
      setoid_rewrite maps_to_res_add.
      apply pointwise_updatable. i. unfold maps_to_res. des_ifs; cycle 1.
      { repeat rewrite URA.unit_idl. apply URA.updatable_unit. }
      apply Auth.auth_update. ii. des. ur in FRAME. des_ifs. split.
      { ur. clarify. } { ur. ss. } }
    iMod (OwnM_Upd with "B") as "[C D]". apply H.
    iModIntro. iSplitL "A".
    { iExists (S U). auto. }
    { iSplitL "C". auto. auto. }
  Qed.
End OblTicket.
