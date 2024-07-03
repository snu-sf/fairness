From sflib Require Import sflib.
From Fairness Require Import Any PCM IProp IPM IPropAux.
From Fairness Require Import TemporalLogic.
From Fairness Require Export AuthExclAnysRA AuthExclsRA.
From stdpp Require Import gmap.

Section Ticket.

  (* Resource for each ticket lock *)
  Definition _TicketRA : URA.t := (URA.prod (Auth.t (GsetK.t (K:=nat))) AuthExclAnysRA)%ra.
  Definition TicketRA : URA.t := (nat ==> _TicketRA)%ra.

  Context `{Σ : GRA.t}.
  Context {HasTicketRA : @GRA.inG TicketRA Σ}.
  Context {AuthExclAnys : @GRA.inG (AuthExcls.t (nat * nat * nat))%ra Σ}.

  Definition TicketRA_Auth_base : _TicketRA :=
    (((Auth.black (Some ∅ : GsetK.t)) ⋅ (Auth.white (Some ∅ : GsetK.t))),
      (AuExAny_ra (fun k => gset_elem_of_dec k ∅))).

  Definition TicketRA_Auth : iProp :=
    (∃ (U : nat),
      OwnM ((fun k => if (lt_dec k U) then ε else TicketRA_Auth_base) : TicketRA)
        ∗ AuthExcls.rest (fun k => lt_dec k U) (0, 0, 0)).

  Definition Ticket_black_ra (γt : nat) (D : gset nat) : TicketRA :=
    (maps_to_res γt (((Auth.black (Some D : GsetK.t)),
                      (AuExAny_ra (fun k => gset_elem_of_dec k D))) : _TicketRA))%ra.
  Definition Ticket_black γt D := OwnM (Ticket_black_ra γt D).

  (* The issuing thread holds my ticket -> (my thread id, and my obligation id). *)
  Definition Ticket_issued_ra (γt : nat) (tk : nat) (l : list nat) : TicketRA :=
    (maps_to_res γt (((Auth.white (Some {[tk]} : GsetK.t)), AuExAnyW_ra tk l) : _TicketRA)).
  Definition Ticket_issued γt tk l := OwnM (Ticket_issued_ra γt tk l).

  (* The invariant holds ticket -> (thread id, obligation id) for the waiting threads. *)
  Definition Ticket_wait_ra (γt : nat) (tk : nat) (l : list nat) : TicketRA :=
    (maps_to_res γt ((Auth.white (Some ∅ : GsetK.t), AuExAnyB_ra tk l) : _TicketRA)).
  Definition Ticket_wait γt tk l := OwnM (Ticket_wait_ra γt tk l).

  (** Properties. *)
  Lemma Ticket_issued_twice (γt tk : nat) (l l' : list nat) :
    Ticket_issued γt tk l -∗ Ticket_issued γt tk l' -∗ False.
  Proof.
    iStartProof. iIntros "T1 T2". unfold Ticket_issued, Ticket_issued_ra.
    iCombine "T1" "T2" as "T3".  iPoseProof (OwnM_valid with "T3") as "%T".
    setoid_rewrite maps_to_res_add in T. ur in T.
    specialize (T γt). ur in T. unfold maps_to_res in T. des_ifs. des.
    repeat ur in T. des_ifs. set_solver.
  Qed.

  Lemma Ticket_black_issued (γt tk : nat) l D :
    Ticket_black γt D -∗ Ticket_issued γt tk l -∗ ⌜tk ∈ D⌝.
  Proof.
    iStartProof. iIntros "BLACK ISSUED". unfold Ticket_black, Ticket_issued.
    iCombine "BLACK" "ISSUED" as "H". unfold Ticket_black_ra, Ticket_issued_ra.
    iPoseProof (OwnM_valid with "H") as "%H". setoid_rewrite maps_to_res_add in H.
    ur in H. specialize (H γt). unfold maps_to_res in H. des_ifs.
    ur in H. des. rewrite URA.unit_idl in H. ur in H. des. destruct H.
    ur in H. des_ifs. iPureIntro; set_solver.
  Qed.

  Lemma Ticket_black_wait (γt tk : nat) l D :
    Ticket_black γt D -∗ Ticket_wait γt tk l -∗ ⌜tk ∈ D⌝.
  Proof.
    iStartProof. iIntros "BLACK WAIT". unfold Ticket_black, Ticket_wait.
    iCombine "BLACK" "WAIT" as "H". unfold Ticket_black_ra, Ticket_wait_ra, AuExAnyB_ra, AuExAny_ra.
    iPoseProof (OwnM_valid with "H") as "%H". setoid_rewrite maps_to_res_add in H.
    ur in H. specialize (H γt). unfold maps_to_res in H. des_ifs.
    ur in H. des. des_ifs. ur in H0. specialize (H0 tk). des_ifs. ur in H0. auto.
  Qed.

  Lemma TicketRA_alloc κu γs b :
    TicketRA_Auth ⊢ ∃ γt, |==> TicketRA_Auth ∗ Ticket_black γt ∅ ∗ ● γt (κu, γs, b) ∗ ○ γt (κu, γs, b).
  Proof.
    iIntros "[%U [BASE BASE2]]". iExists U.
    assert (URA.updatable
      (((λ k, if lt_dec k U then ε else TicketRA_Auth_base) : TicketRA))
      (((λ k, if lt_dec k (S U) then ε else TicketRA_Auth_base) : TicketRA)
        ⋅ (maps_to_res U TicketRA_Auth_base))) as UPD.
    { ur. apply pointwise_updatable. i. unfold maps_to_res. des_ifs; try lia.
      - rewrite URA.unit_idl. reflexivity.
      - rewrite URA.unit_idl. reflexivity.
      - rewrite URA.unit_id. reflexivity.
    }
    iMod (OwnM_Upd with "BASE") as "[A B]". apply UPD.
    assert (URA.updatable (maps_to_res U TicketRA_Auth_base) (Ticket_black_ra U ∅)).
    { unfold TicketRA_Auth_base, Ticket_black_ra.
      apply maps_to_updatable. apply URA.prod_updatable; [ | reflexivity].
      apply Auth.auth_dealloc. ii. des. ur in FRAME. des_ifs. split; ss.
      rewrite URA.unit_idl. f_equal. set_solver.
    }
    iMod (OwnM_Upd with "B") as "D". apply H.
    assert (URA.updatable (maps_to_res U TicketRA_Auth_base) (Ticket_black_ra U ∅)).
    { unfold TicketRA_Auth_base, Ticket_black_ra.
      apply maps_to_updatable. apply URA.prod_updatable; [ | reflexivity].
      apply Auth.auth_dealloc. ii. des. ur in FRAME. des_ifs. split; ss.
      rewrite URA.unit_idl. f_equal. set_solver.
    }
    iMod (AuthExcls.alloc_gen (gt_dec U) (gt_dec (S U)) with "BASE2") as "(BASE2 & B)".
    { ii; des_ifs. lia. }
    iAssert (#=> OwnM (AuthExcls.black_ra U (κu, γs, b) ⋅ AuthExcls.white_ra U (κu, γs, b)))%I with "[B]" as "> B".
    { unfold AuthExcls.black_ra, AuthExcls.white_ra. setoid_rewrite maps_to_res_add.
      iApply (OwnM_Upd with "B"). unfold maps_to_res. apply pointwise_updatable. i.
      des_ifs; try lia. apply Auth.auth_update. ii. des. ur in FRAME. des_ifs. ur; split; auto. }
    iModIntro; iFrame. iSplitR "B".
    { iExists (S U). iFrame. }
    iDestruct "B" as "[B B']". iSplitL "B"; done.
  Qed.

  Lemma Ticket_alloc γt D new l
    (NOTIN : new ∉ D)
    :
    Ticket_black γt D ⊢ |==> Ticket_black γt (D ∪ {[new]}) ∗ Ticket_issued γt new l ∗ Ticket_wait γt new l.
  Proof.
    iIntros "TB". unfold Ticket_black, Ticket_issued, Ticket_wait.
    assert (URA.updatable (Ticket_black_ra γt D)
      (Ticket_black_ra γt (D ∪ {[new]}) ⋅ Ticket_issued_ra γt new l ⋅ Ticket_wait_ra γt new l)).
    { unfold Ticket_black_ra, Ticket_issued_ra, Ticket_wait_ra. do 2 setoid_rewrite maps_to_res_add.
      apply maps_to_updatable. ur. apply URA.prod_updatable.
      etrans.
      { apply Auth.auth_alloc2. instantiate (1:= (Some ({[new]}))). ur.
        ur; des_ifs. set_solver. }
      { setoid_rewrite <- URA.add_assoc. ur.
        rewrite ! URA.unit_idl. ur. des_ifs; cycle 1. set_solver. set_solver. set_solver.
        enough (({[new]} ∪ ∅ : gset nat) = {[new]}). rewrite H; auto. reflexivity. set_solver.
      }
      unfold AuExAny_ra, AuExAnyW_ra, AuExAnyB_ra, maps_to_res. apply pointwise_updatable. i. ur.
      des_ifs; try (rewrite ! URA.unit_id); try (rewrite ! URA.unit_idl); try apply URA.updatable_unit.
      { exploit n. set_solver. intros c; inv c. }
      { ii. ur in H. des_ifs. des. ur. split. rewrite URA.unit_id. destruct H. exists x.
        ur in H. des_ifs. ur. auto. ur. auto. }
      { exploit n0. set_solver. intros C; inv C. }
      ii. auto.
    }
    iMod (OwnM_Upd with "TB") as "[[TB TI] TW]". apply H.
    iModIntro. iFrame.
  Qed.

  Lemma Ticket_return γt D old l
    :
    Ticket_black γt D -∗ Ticket_issued γt old l -∗ Ticket_wait γt old l ==∗ Ticket_black γt (D ∖ {[old]}).
  Proof.
    iIntros "TB IS WA".
    unfold Ticket_black, Ticket_issued, Ticket_wait.
    iCombine "TB" "IS" as "TB". iCombine "TB" "WA" as "TB".
    assert (URA.updatable (Ticket_black_ra γt D ⋅ Ticket_issued_ra γt old l ⋅ Ticket_wait_ra γt old l)
      (Ticket_black_ra γt (D ∖ {[old]}))).
    { unfold Ticket_black_ra, Ticket_issued_ra, Ticket_wait_ra. do 2 setoid_rewrite maps_to_res_add.
      apply maps_to_updatable. ur. apply URA.prod_updatable.
      ur. rewrite URA.unit_idl. ur. des_ifs. 2:{ set_solver. }
      ii. ur in H. des_ifs. des. destruct H. ur in H. des_ifs. ur in H. des_ifs.
      ur. split. exists (Some g0). rewrite URA.unit_idl. ur. des_ifs. 2:{ set_solver. }
      f_equal. set_solver. ur. auto.
      unfold AuExAny_ra, AuExAnyW_ra, AuExAnyB_ra, maps_to_res. apply pointwise_updatable. i. ur.
      des_ifs; try (rewrite ! URA.unit_id); try (rewrite ! URA.unit_idl); try apply URA.updatable_unit.
      { ur. rewrite URA.unit_id. ii. ur in H. des_ifs. des. ur in H. des_ifs; destruct H; ur in H; des_ifs.
        ur. split; ur; auto. exists URA.unit. ur. des_ifs. }
      { exploit n0. set_solver. intros C; inv C. }
      { ii. ur in H. des_ifs. }
      { reflexivity. }
    }
    iMod (OwnM_Upd with "TB") as "TB". apply H. done.
  Qed.

  Lemma Ticket_issued_wait γt tk l l' :
    Ticket_issued γt tk l -∗ Ticket_wait γt tk l' -∗ ⌜l = l'⌝.
  Proof.
    iIntros "I W". unfold Ticket_issued, Ticket_wait, Ticket_issued_ra, Ticket_wait_ra.
    iCombine "I" "W" as "IW". iPoseProof (OwnM_valid with "IW") as "%IW". setoid_rewrite maps_to_res_add in IW.
    ur in IW. specialize (IW γt). unfold maps_to_res in IW. des_ifs. ur in IW. des.
    ur in IW0. des. specialize (IW0 tk). unfold AuExAnyW_ra, AuExAnyB_ra, maps_to_res in IW0. des_ifs.
    ur in Heq. inv Heq. inv Heq0. ur in IW0. des_ifs. des. destruct IW0. ur in H. des_ifs.
    apply Any.upcast_inj in H. des. apply JMeq.JMeq_eq in EQ0. inv EQ0. iPureIntro; auto.
  Qed.

End Ticket.

Section SPROP.

  Context {STT : StateTypes}.
  Context `{sub : @SRA.subG Γ Σ}.
  Context {TLRASs : TLRAs_small STT Γ}.
  Context {TLRAS : TLRAs STT Γ Σ}.

  Context {HasTicket : @GRA.inG TicketRA Γ}.
  Context {AuthExclAnys : @GRA.inG (AuthExcls.t (nat * nat * nat))%ra Γ}.

  Definition s_ticket_auth {n} : sProp n :=
    (∃ (U : τ{nat, n}),
      (➢((fun k => if (lt_dec k U) then ε else TicketRA_Auth_base) : TicketRA))
      ∗ SAuthExcls.s_rest (fun k => lt_dec k U) (0, 0, 0))%S.
  Lemma red_s_ticket_auth n :
    ⟦s_ticket_auth, n⟧ = TicketRA_Auth.
  Proof.
    unfold s_ticket_auth, TicketRA_Auth. red_tl; simpl. f_equal. extensionalities r.
    red_tl. red_tl_authexcls. auto.
  Qed.

  Definition s_ticket_black {n} (γt : nat) (D : gset nat) : sProp n :=
    (➢(Ticket_black_ra γt D))%S.
  Lemma red_s_ticket_black n γt D :
    ⟦s_ticket_black γt D, n⟧ = Ticket_black γt D.
  Proof.
    unfold s_ticket_black. red_tl; simpl. ss.
  Qed.

  Definition s_ticket_issued {n} (γt tk : nat) (l : list nat) : sProp n :=
    (➢(Ticket_issued_ra γt tk l))%S.
  Lemma red_s_ticket_issued n γt tk l :
    ⟦s_ticket_issued γt tk l, n⟧ = Ticket_issued γt tk l.
  Proof.
    unfold s_ticket_issued. red_tl; simpl. ss.
  Qed.

  Definition s_ticket_wait {n} (γt tk : nat) (l : list nat) : sProp n :=
    (➢(Ticket_wait_ra γt tk l))%S.
  Lemma red_s_ticket_wait n γt tk l :
    ⟦s_ticket_wait γt tk l, n⟧ = Ticket_wait γt tk l.
  Proof.
    unfold s_ticket_wait. red_tl; simpl. ss.
  Qed.

End SPROP.

Ltac red_tl_ticket := (try rewrite ! red_s_ticket_auth;
                       try rewrite ! red_s_ticket_black;
                       try rewrite ! red_s_ticket_issued;
                       try rewrite ! red_s_ticket_wait
                      ).

Ltac red_tl_lifetime_s := (try setoid_rewrite red_s_ticket_auth;
                           try setoid_rewrite red_s_ticket_black;
                           try setoid_rewrite red_s_ticket_issued;
                           try setoid_rewrite red_s_ticket_wait
                          ).