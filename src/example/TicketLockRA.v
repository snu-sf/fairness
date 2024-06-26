From sflib Require Import sflib.
From Fairness Require Import Any PCM IProp IPM IPropAux.
From Fairness Require Import TemporalLogic.
From Fairness Require Export AuthExclAnysRA.
From stdpp Require Import gmap.


Section Ticket.
  (* Resource for each ticket lock *)
  Definition _TicketRA : URA.t :=
    URA.prod (Auth.t (URA.prod (Excl.t nat) (GsetK.t (K:=nat)))) AuthExclAnysRA.
  Definition TicketRA : URA.t := (nat ==> _TicketRA)%ra.

  Context `{Σ : GRA.t}.
  Context {HasTicketRA : @GRA.inG TicketRA Σ}.

  Definition TicketRA_Auth_base : _TicketRA :=
    (((@Auth.black (URA.prod _ _) (Some 0 : Excl.t nat, Some ∅ : GsetK.t))
        ⋅ (@Auth.white (URA.prod _ _) (Some 0 : Excl.t nat, Some ∅ : GsetK.t))),
     ((fun k => (Auth.black (Some (tt ↑) : Excl.t Any.t) ⋅ Auth.white (Some (tt ↑) : Excl.t Any.t))) : AuthExclAnysRA)
    ).

  Definition TicketRA_Auth : iProp :=
    (∃ (U : nat), OwnM ((fun k => if (lt_dec k U)
                        then ε
                        else TicketRA_Auth_base) : TicketRA)).

  Definition Ticket_black_ra (r : nat) (o : nat) (D : gset nat) : TicketRA :=
    (maps_to_res r (((Auth.black (((Some o) : Excl.t nat, Some D : GsetK.t) : URA.prod _ _)),
                      AuExAny_ra (fun k => gset_elem_of_dec k D)) : URA.prod _ _)).
  Definition Ticket_black r o D := OwnM (Ticket_black_ra r o D).

  Definition Ticket_locked_ra (r o : nat) : TicketRA :=
    (maps_to_res r ((Auth.white (((Some o) : Excl.t nat, Some ∅ : GsetK.t) : URA.prod _ _), ε) : URA.prod _ _)).
  Definition Ticket_locked r o := OwnM (Ticket_locked_ra r o).

  (* The issuing thread holds my ticket -> (my thread id, and my obligation id). *)
  Definition Ticket_issued_ra (r : nat) (m κu κack : nat) : TicketRA :=
    (maps_to_res r ((Auth.white ((ε : Excl.t nat, Some {[m]} : GsetK.t) : URA.prod _ _),
                     AuExAnyW_ra m (κu, κack)) : URA.prod _ _)).
  Definition Ticket_issued r m κu κack := OwnM (Ticket_issued_ra r m κu κack).

  (* The invariant holds ticket -> (thread id, obligation id) for the waiting threads. *)
  Definition Ticket_wait_ra (r : nat) (m κu κack : nat) : TicketRA :=
    (maps_to_res r ((Auth.white ((ε : Excl.t nat, Some ∅ : GsetK.t) : URA.prod _ _),
                     AuExAnyB_ra m (κu, κack)) : URA.prod _ _)).
  Definition Ticket_wait r m κu κack := OwnM (Ticket_wait_ra r m κu κack).

  (** Properties. *)
  Lemma Ticket_locked_twice (r m1 m2: nat) : Ticket_locked r m1 ∗ Ticket_locked r m2 ⊢ False.
  Proof.
    iStartProof. iIntros "[T1 T2]". unfold Ticket_locked, Ticket_locked_ra.
    iCombine "T1" "T2" as "T3".  iPoseProof (OwnM_valid with "T3") as "%T".
    setoid_rewrite maps_to_res_add in T. ur in T.
    specialize (T r). ur in T. unfold maps_to_res in T. des_ifs. des.
    ur in T. ur in T. des. ur in T. clarify.
  Qed.

  Lemma Ticket_issued_twice (r m κu κack κu' κack' : nat) :
    Ticket_issued r m κu κack ∗ Ticket_issued r m κu' κack' ⊢ False.
  Proof.
    iStartProof. iIntros "[T1 T2]". unfold Ticket_issued, Ticket_issued_ra.
    iCombine "T1" "T2" as "T3".  iPoseProof (OwnM_valid with "T3") as "%T".
    setoid_rewrite maps_to_res_add in T. ur in T.
    specialize (T r). ur in T. unfold maps_to_res in T. des_ifs. des.
    repeat ur in T. des_ifs. set_solver. des. auto.
  Qed.

  Lemma Ticket_black_locked (r m1 m2: nat) D : Ticket_locked r m1 ∗ Ticket_black r m2 D ⊢ ⌜m1 = m2⌝.
  Proof.
    iStartProof. iIntros "[T1 T2]". unfold Ticket_locked, Ticket_locked_ra, Ticket_black, Ticket_black_ra.
    iCombine "T1" "T2" as "T3".  iPoseProof (OwnM_valid with "T3") as "%T".
    setoid_rewrite maps_to_res_add in T. ur in T.
    specialize (T r). ur in T. unfold maps_to_res in T. des_ifs. des.
    ur in T. des_ifs. des.
    destruct T. ur in H. des_ifs. ur in H1. des_ifs.
    set_solver.
  Qed.

  Lemma Ticket_black_issued (r m1 m2 κu κack : nat) D :
    Ticket_black r m1 D ∗ Ticket_issued r m2 κu κack ⊢ ⌜m2 ∈ D⌝.
  Proof.
    iStartProof. iIntros "[BLACK ISSUED]". unfold Ticket_black, Ticket_issued.
    iCombine "BLACK" "ISSUED" as "H". unfold Ticket_black_ra, Ticket_issued_ra.
    iPoseProof (OwnM_valid with "H") as "%H". setoid_rewrite maps_to_res_add in H.
    ur in H. specialize (H r). unfold maps_to_res in H. des_ifs.
    ur in H. des. ur in H. des. destruct H. des_ifs.
    ur in H. des_ifs. destruct c0; ss. des_ifs; ss. 2:{ ur in H. ss. }
    destruct c2; ss. 2:{ ur in H. ss. } ur in H. des_ifs. iPureIntro. set_solver.
  Qed.

  Lemma TicketRA_alloc o :
    TicketRA_Auth ⊢ ∃ r, |==> TicketRA_Auth ∗ Ticket_black r o ∅ ∗ Ticket_locked r o.
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
      (Ticket_black_ra U o ∅
        ⋅ maps_to_res U ((Auth.white ((Some o : Excl.t nat, Some ∅ : GsetK.t) : URA.prod _ _), ε) : URA.prod _ _))).
    { ur. apply pointwise_updatable. i.
      unfold Ticket_black_ra, Ticket_locked_ra, maps_to_res, TicketRA_Auth_base.
      des_ifs; cycle 1. rewrite URA.unit_id. reflexivity.
      rewrite ! URA.unfold_add. do 2 rewrite <- URA.unfold_add. ss. apply URA.prod_updatable.
      { apply Auth.auth_update. ii. des. ur in FRAME. des_ifs. ur in H0. ur in H1. des_ifs. split.
        ur. split; ur; auto. ur. f_equal. ur; auto. ur. des_ifs. rewrite <- H0; auto. }
      unfold AuExAny_ra.
      apply pointwise_updatable. ii. ss. ur in H. des_ifs. des.
      rewrite URA.unit_idl in H. destruct H. ur in H.  des_ifs. rewrite URA.unit_id. ur. des_ifs.
      split. exists ε. ur. des_ifs. ur. auto. }
    iMod (OwnM_Upd with "B") as "[C D]". apply H.
    iModIntro. iSplitL "A".
    { iExists (S U). auto. }
    { iSplitL "C". auto. unfold Ticket_locked, Ticket_locked_ra. auto. }
  Qed.

  Lemma Ticket_alloc r o D new κu κack
    (NOTIN : new ∉ D)
    :
    Ticket_black r o D ⊢
      |==> Ticket_black r o (D ∪ {[new]}) ∗ Ticket_issued r new κu κack ∗ Ticket_wait r new κu κack.
  Proof.
    iIntros "TB". unfold Ticket_black, Ticket_issued.
    assert (URA.updatable (Ticket_black_ra r o D)
      (Ticket_black_ra r o (D ∪ {[new]}) ⋅ Ticket_issued_ra r new κu κack ⋅ Ticket_wait_ra r new κu κack)).
    { unfold Ticket_black_ra, Ticket_issued_ra, Ticket_wait_ra. do 2 setoid_rewrite maps_to_res_add.
      apply maps_to_updatable. ur. apply URA.prod_updatable.
      { etrans.
        { apply Auth.auth_alloc2. instantiate (1:= (ε, Some ({[new]}))). ur.
          split; ur; des_ifs. set_solver. }
        { setoid_rewrite <- URA.add_assoc. ur.
          rewrite ! URA.unit_id. rewrite ! URA.unit_idl. ur. des_ifs; cycle 1. set_solver.
          rewrite ! URA.unit_id. rewrite URA.unfold_add. ss. des_ifs; cycle 1. set_solver.
          ii. ur in H. des_ifs. des. ur. split; cycle 1. ur. split; ur; auto.
          destruct H. exists x. ur. des_ifs. ur in H. inv H. rewrite H2. rewrite H3. f_equal.
          rewrite <- H3. enough (({[new]} ∪ ∅ : gset nat) = {[new]}). rewrite H; auto. set_solver. }
      }
      unfold AuExAny_ra, AuExAnyW_ra, AuExAnyB_ra, maps_to_res. apply pointwise_updatable. i. ur.
      des_ifs; try (rewrite ! URA.unit_id); try (rewrite ! URA.unit_idl); try apply URA.updatable_unit.
      { exploit n. set_solver. intros c; inv c. }
      { ii. ur in H. des_ifs. des. ur. split. rewrite URA.unit_id. destruct H. exists x.
        ur in H. des_ifs. ur. auto. ur. auto. }
      { exploit n0. set_solver. intros C; inv C. }
      ii. auto. }
    iMod (OwnM_Upd with "TB")  as "[[TB TI] TW]". apply H.
    iModIntro. iFrame.
  Qed.

  Lemma Ticket_update r o o' D
    :
    Ticket_black r o D ∗ Ticket_locked r o ⊢
      |==> Ticket_black r o' D ∗ Ticket_locked r o'.
  Proof.
    iIntros "[TB TL]". unfold Ticket_black, Ticket_locked. iCombine "TB" "TL" as "BL".
    assert (URA.updatable (Ticket_black_ra r o D ⋅ Ticket_locked_ra r o)
      (Ticket_black_ra r o' D ⋅ Ticket_locked_ra r o')).
    { unfold Ticket_black_ra, Ticket_issued_ra. setoid_rewrite maps_to_res_add.
      apply maps_to_updatable. ur. apply URA.prod_updatable.
      { apply Auth.auth_update. ii. des. ur in FRAME.
        des_ifs. ur in H0. des_ifs. ur in H1. des_ifs. split.
        { ur. split; ur; auto. }
        { ur. f_equal. ur; auto. ur; auto. des_ifs. }
      }
      ii; auto.
    }
    iMod (OwnM_Upd with "BL") as "BL". apply H. iModIntro. iDestruct "BL" as "[TB TL]". iFrame.
  Qed.

  Lemma Ticket_issued_wait r tk κu κack κu' κack' :
    Ticket_issued r tk κu κack ∗ Ticket_wait r tk κu' κack' ⊢ ⌜κu = κu' ∧ κack = κack'⌝.
  Proof.
    iIntros "[I W]". unfold Ticket_issued, Ticket_wait, Ticket_issued_ra, Ticket_wait_ra.
    iCombine "I" "W" as "IW". iPoseProof (OwnM_valid with "IW") as "%IW". setoid_rewrite maps_to_res_add in IW.
    ur in IW. specialize (IW r). unfold maps_to_res in IW. des_ifs. ur in IW. des.
    ur in IW0. specialize (IW0 tk). unfold AuExAnyW_ra, AuExAnyB_ra, maps_to_res in IW0. des_ifs.
    ur in Heq. inv Heq. inv Heq0. ur in IW0. des_ifs. des. destruct IW0. ur in H. des_ifs.
    apply Any.upcast_inj in H. des. apply JMeq.JMeq_eq in EQ0. inv EQ0. iPureIntro; auto.
  Qed.

End Ticket.

Section Shots.
  Definition _ShotsRA : URA.t := (nat ==> (URA.prod (OneShot.t nat) (OneShot.t unit)))%ra.
  Definition ShotsRA : URA.t := (nat ==> _ShotsRA)%ra.

  Context `{Σ : GRA.t}.
  Context {HasShotsRA : @GRA.inG ShotsRA Σ}.

  Definition ShotsRA_Auth_base : _ShotsRA :=
    (fun k => (OneShot.pending _ 1, OneShot.pending _ 1)).
  Definition ShotsRA_Auth : iProp :=
    (∃ (U : nat), OwnM ((fun k => if (lt_dec k U) then ε else ShotsRA_Auth_base) : ShotsRA)).

  Definition Shots_base_ra sr U : ShotsRA :=
    maps_to_res sr ((fun k => if (lt_dec k U) then ε else (OneShot.pending _ 1, OneShot.pending _ 1)) : _ShotsRA).
  Definition Shots_base sr U : iProp := OwnM (Shots_base_ra sr U).

  Definition Shots_pending_ra (sr tk κu : nat) : ShotsRA :=
    maps_to_res sr (maps_to_res tk ((OneShot.shot κu, OneShot.pending _ 1) : URA.prod _ _)).
  Definition Shots_pending (sr tk κu : nat) : iProp := OwnM (Shots_pending_ra sr tk κu).

  Definition Shots_shot_ra (sr tk κu : nat) : ShotsRA :=
    maps_to_res sr (maps_to_res tk ((OneShot.shot κu, OneShot.shot tt) : URA.prod _ _)).
  Definition Shots_shot (sr tk κu : nat) : iProp := OwnM (Shots_shot_ra sr tk κu).

  Lemma Shots_shot_persistent sr tk κu :
    Shots_shot sr tk κu ⊢ □ Shots_shot sr tk κu.
  Proof.
    iIntros "H". unfold Shots_shot. iPoseProof (own_persistent with "H") as "H".
    enough (URA.core (Shots_shot_ra sr tk κu) = Shots_shot_ra sr tk κu). rewrite H. done.
    unfold Shots_shot_ra, maps_to_res. ur. repeat extensionalities. des_ifs.
    { destruct s; destruct s0; ur; ss. }
    { destruct s; destruct s0; ur; ss. }
  Qed.

  Global Program Instance Persistent_Shots_shot sr tk κu : Persistent (Shots_shot sr tk κu).
  Next Obligation.
    iIntros (sr tk κu) "S". iApply (Shots_shot_persistent with "S").
  Qed.

  Lemma ShotsRA_alloc o :
    ShotsRA_Auth ⊢ ∃ r, |==> ShotsRA_Auth ∗ Shots_base r o.
  Proof.
    iIntros "[%U BASE]". iExists U.
    assert (URA.updatable
      ((λ k, if lt_dec k U then ε else ShotsRA_Auth_base) : ShotsRA)
      (((λ k, if lt_dec k (S U) then ε else ShotsRA_Auth_base) : ShotsRA)
        ⋅ (maps_to_res U ShotsRA_Auth_base))) as UPD.
    { ur. apply pointwise_updatable. i. unfold maps_to_res. des_ifs; try lia.
      - rewrite URA.unit_idl. reflexivity.
      - rewrite URA.unit_idl. reflexivity.
      - rewrite URA.unit_id. reflexivity.  }
    iMod (OwnM_Upd with "BASE") as "[A B]". apply UPD.
    assert (URA.updatable (maps_to_res U ShotsRA_Auth_base) (Shots_base_ra U o)).
    { unfold ShotsRA_Auth_base, Shots_base_ra, maps_to_res. apply pointwise_updatable. i.
      des_ifs; cycle 1. apply pointwise_updatable. i. des_ifs. apply URA.updatable_unit. }
    iMod (OwnM_Upd with "B") as "C". apply H.
    iModIntro. iSplitL "A".
    { iExists (S U). auto. }
    { auto. }
  Qed.

  Lemma Shots_alloc κu r o : Shots_base r o ⊢ |==> Shots_base r (1 + o) ∗ Shots_pending r o κu.
  Proof.
    iIntros "B". unfold Shots_base, Shots_pending.
    assert (URA.updatable (Shots_base_ra r o) (Shots_base_ra r (1 + o) ⋅ Shots_pending_ra r o κu)).
    { unfold Shots_base_ra, Shots_pending_ra. setoid_rewrite maps_to_res_add.
      apply maps_to_updatable. unfold maps_to_res. apply pointwise_updatable. i. ur.
      des_ifs; try rewrite URA.unit_id; try rewrite URA.unit_idl; try apply URA.updatable_unit;
        try reflexivity; try lia.
      apply URA.prod_updatable. apply OneShot.pending_shot. reflexivity. }
    iMod (OwnM_Upd with "B") as "C". apply H.
    iModIntro. iDestruct "C" as "[D E]"; iFrame.
  Qed.

  Lemma Shots_pending_not_shot sr tk κu κu' :
    Shots_pending sr tk κu ∗ Shots_shot sr tk κu' ⊢ False.
  Proof.
    iIntros "[P S]". unfold Shots_pending, Shots_shot. iCombine "P" "S" as "PS".
    unfold Shots_pending_ra, Shots_shot_ra. iPoseProof (OwnM_valid with "PS") as "%PS".
    unfold maps_to_res in PS. ur in PS. specialize (PS sr). ur in PS. specialize (PS tk).
    des_ifs. ur in PS. des. ur in PS0. done.
  Qed.

  Lemma Shots_pending_shot κu sr tk :
    Shots_pending sr tk κu ⊢ |==> Shots_shot sr tk κu.
  Proof.
    iIntros "P". unfold Shots_pending, Shots_shot.
    assert (URA.updatable (Shots_pending_ra sr tk κu) (Shots_shot_ra sr tk κu)).
    {
      unfold Shots_pending_ra, Shots_shot_ra. do 2 apply maps_to_updatable.
      apply URA.prod_updatable. reflexivity. apply OneShot.pending_shot.
    }
    iMod (OwnM_Upd with "P"). apply H. done.
  Qed.
End Shots.

Section SPROP.

  Context {STT : StateTypes}.
  Context `{sub : @SRA.subG Γ Σ}.
  Context {TLRASs : TLRAs_small STT Γ}.
  Context {TLRAS : TLRAs STT Γ Σ}.

  Context {HasTicket : @GRA.inG TicketRA Γ}.
  Context {HasShots : @GRA.inG ShotsRA Γ}.

  Definition s_ticket_auth {n} : sProp n :=
    (∃ (U : τ{nat, n}), (➢((fun k => if (lt_dec k U) then ε else TicketRA_Auth_base) : TicketRA)))%S.
  Lemma red_s_ticket_auth n :
    ⟦s_ticket_auth, n⟧ = TicketRA_Auth.
  Proof.
    unfold s_ticket_auth, TicketRA_Auth. red_tl; simpl. f_equal. extensionalities r.
    red_tl. auto.
  Qed.

  Definition s_ticket_black {n} (r o : nat) (D : gset nat) : sProp n :=
    (➢(Ticket_black_ra r o D))%S.
  Lemma red_s_ticket_black n r o D :
    ⟦s_ticket_black r o D, n⟧ = Ticket_black r o D.
  Proof.
    unfold s_ticket_black. red_tl; simpl. ss.
  Qed.

  Definition s_ticket_locked {n} (r o : nat) : sProp n :=
    (➢(Ticket_locked_ra r o))%S.
  Lemma red_s_ticket_locked n r o :
    ⟦s_ticket_locked r o, n⟧ = Ticket_locked r o.
  Proof.
    unfold s_ticket_locked. red_tl; simpl. ss.
  Qed.

  Definition s_ticket_issued {n} (r o tid obl : nat) : sProp n :=
    (➢(Ticket_issued_ra r o tid obl))%S.
  Lemma red_s_ticket_issued n r o tid obl :
    ⟦s_ticket_issued r o tid obl, n⟧ = Ticket_issued r o tid obl.
  Proof.
    unfold s_ticket_issued. red_tl; simpl. ss.
  Qed.

  Definition s_ticket_wait {n} (r o tid obl : nat) : sProp n :=
    (➢(Ticket_wait_ra r o tid obl))%S.
  Lemma red_s_ticket_wait n r o tid obl :
    ⟦s_ticket_wait r o tid obl, n⟧ = Ticket_wait r o tid obl.
  Proof.
    unfold s_ticket_wait. red_tl; simpl. ss.
  Qed.

  Definition s_shots_auth {n} : sProp n :=
    (∃ (U : τ{nat, n}), (➢((fun k => if (lt_dec k U) then ε else ShotsRA_Auth_base) : ShotsRA)))%S.
  Lemma red_s_shots_auth n :
    ⟦s_shots_auth, n⟧ = ShotsRA_Auth.
  Proof.
    unfold s_shots_auth, ShotsRA_Auth. red_tl; simpl. f_equal. extensionalities r.
    red_tl. auto.
  Qed.

  Definition s_shots_base {n} sr U : sProp n :=
    (➢(Shots_base_ra sr U))%S.
  Lemma red_s_shots_base sr U n : ⟦s_shots_base sr U, n⟧ = Shots_base sr U.
  Proof.
    unfold s_shots_base, Shots_base. red_tl; simpl. f_equal.
  Qed.

  Definition s_shots_pending {n} (sr tk κu : nat) : sProp n :=
    (➢(Shots_pending_ra sr tk κu))%S.
  Lemma red_s_shots_pending n sr tk κu :
    ⟦s_shots_pending sr tk κu, n⟧ = Shots_pending sr tk κu.
  Proof.
    unfold s_shots_pending. red_tl; simpl. ss.
  Qed.

  Definition s_shots_shot {n} (sr tk κu : nat) : sProp n :=
    (➢(Shots_shot_ra sr tk κu))%S.
  Lemma red_s_shots_shot n sr tk κu :
    ⟦s_shots_shot sr tk κu, n⟧ = Shots_shot sr tk κu.
  Proof.
    unfold s_shots_shot. red_tl; simpl. ss.
  Qed.

End SPROP.

Ltac red_tl_ticket := (try rewrite ! red_s_ticket_auth;
                       try rewrite ! red_s_ticket_black;
                       try rewrite ! red_s_ticket_issued;
                       try rewrite ! red_s_ticket_locked;
                       try rewrite ! red_s_ticket_wait;
                       try rewrite ! red_s_shots_auth;
                       try rewrite ! red_s_shots_base;
                       try rewrite ! red_s_shots_pending;
                       try rewrite ! red_s_shots_shot
                      ).

Ltac red_tl_lifetime_s := (try setoid_rewrite red_s_ticket_auth;
                           try setoid_rewrite red_s_ticket_black;
                           try setoid_rewrite red_s_ticket_issued;
                           try setoid_rewrite red_s_ticket_locked;
                           try setoid_rewrite red_s_ticket_wait;
                           try setoid_rewrite red_s_shots_base;
                           try setoid_rewrite red_s_shots_auth;
                           try setoid_rewrite red_s_shots_pending;
                           try setoid_rewrite red_s_shots_shot
                          ).