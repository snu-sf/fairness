From iris.algebra Require Import cmra gset updates local_updates auth lib.excl_auth.
From sflib Require Import sflib.
From Fairness Require Import Any PCM IProp IPM IPropAux.
From Fairness Require Import TemporalLogic.
From Fairness Require Export AuthExclAnysRA AuthExclsRA.
From stdpp Require Import gmap.

Section Ticket.

  (* Resource for each ticket lock *)
  Definition _TicketRA : ucmra := (prodUR (authUR (gset_disjUR nat)) AuthExclAnysRA)%ra.
  Definition TicketRA : ucmra := (nat ==> _TicketRA)%ra.

  Context `{Σ : GRA.t}.
  Notation iProp := (iProp Σ).
  Context {HasTicketRA : @GRA.inG TicketRA Σ}.
  Context {AuthExclAnys : @GRA.inG (AuthExcls.t (nat * nat * nat))%ra Σ}.

  Definition TicketRA_Auth_base : _TicketRA :=
    (((auth_auth (DfracOwn 1) (GSet ∅)) ⋅ (auth_frag (GSet ∅))),
      (AuExAny_ra (fun k => gset_elem_of_dec k ∅))).

  Definition TicketRA_Auth : iProp :=
    (∃ (U : nat),
      OwnM ((fun k => if (lt_dec k U) then ε else TicketRA_Auth_base) : TicketRA)
        ∗ AuthExcls.rest (fun k => lt_dec k U) (0, 0, 0)).

  Definition Ticket_black_ra (γt : nat) (D : gset nat) : TicketRA :=
    (maps_to_res γt (((auth_auth (DfracOwn 1) (GSet D)),
                      (AuExAny_ra (fun k => gset_elem_of_dec k D))) : _TicketRA))%ra.
  Definition Ticket_black γt D := OwnM (Ticket_black_ra γt D).

  (* The issuing thread holds my ticket -> (my thread id, and my obligation id). *)
  Definition Ticket_issued_ra (γt : nat) (tk : nat) (l : list nat) : TicketRA :=
    (maps_to_res γt (((◯ (GSet {[tk]})), AuExAnyW_ra tk l) : _TicketRA)).
  Definition Ticket_issued γt tk l := OwnM (Ticket_issued_ra γt tk l).

  (* The invariant holds ticket -> (thread id, obligation id) for the waiting threads. *)
  Definition Ticket_wait_ra (γt : nat) (tk : nat) (l : list nat) : TicketRA :=
    (maps_to_res γt ((◯ (GSet ∅), AuExAnyB_ra tk l) : _TicketRA)).
  Definition Ticket_wait γt tk l := OwnM (Ticket_wait_ra γt tk l).

  (** Properties. *)
  Lemma Ticket_issued_twice (γt tk : nat) (l l' : list nat) :
    Ticket_issued γt tk l -∗ Ticket_issued γt tk l' -∗ False.
  Proof.
    iStartProof. iIntros "T1 T2". unfold Ticket_issued, Ticket_issued_ra.
    iCombine "T1" "T2" as "T3".  iPoseProof (OwnM_valid with "T3") as "%T".
    rewrite maps_to_res_add /maps_to_res in T.
    specialize (T γt). simpl in *. des_ifs.
    rewrite pair_valid /AuExAnyW_ra /AuthExcls.white_ra in T. des. simpl in *.
    exfalso.
    rewrite maps_to_res_add /maps_to_res in T0.
    specialize (T0 tk). simpl in *. des_ifs.
    by apply excl_auth_frag_op_valid in T0.
  Qed.

  Lemma Ticket_black_issued (γt tk : nat) l D :
    Ticket_black γt D -∗ Ticket_issued γt tk l -∗ ⌜tk ∈ D⌝.
  Proof.
    iStartProof. iIntros "BLACK ISSUED". unfold Ticket_black, Ticket_issued.
    iCombine "BLACK" "ISSUED" as "H". unfold Ticket_black_ra, Ticket_issued_ra.
    iOwnWf "H" as H. iPureIntro. rewrite maps_to_res_add /maps_to_res in H.
    specialize (H γt). simpl in *. des_ifs.
    apply pair_valid in H. destruct H as [H H0]. simpl in *.
    apply auth_both_dfrac_valid_discrete in H.
    des. apply gset_disj_included in H1. set_solver.
  Qed.

  Lemma Ticket_black_wait (γt tk : nat) l D :
    Ticket_black γt D -∗ Ticket_wait γt tk l -∗ ⌜tk ∈ D⌝.
  Proof.
    iStartProof. iIntros "BLACK WAIT". unfold Ticket_black, Ticket_wait.
    iCombine "BLACK" "WAIT" as "H". unfold Ticket_black_ra, Ticket_wait_ra, AuExAnyB_ra, AuExAny_ra.
    iOwnWf "H" as H. iPureIntro. rewrite maps_to_res_add /maps_to_res in H.
    specialize (H γt). simpl in *. des_ifs.
    apply pair_valid in H. destruct H as [H H0]. simpl in *.
    specialize (H0 tk). simpl in *.
    rewrite /AuthExcls.rest_ra /AuthExcls.black_ra /maps_to_res in H0.
    rewrite discrete_fun_lookup_op in H0. des_ifs.
    rewrite (comm cmra.op (●E _)) in H0.
    rewrite <- (assoc cmra.op) in H0.
    by apply cmra_valid_op_r,excl_auth_auth_op_valid in H0.
  Qed.

  Lemma TicketRA_alloc κu γs b :
    TicketRA_Auth ⊢ ∃ γt, |==> TicketRA_Auth ∗ Ticket_black γt ∅ ∗ AuthExcls.black γt (κu, γs, b) ∗ AuthExcls.white γt (κu, γs, b).
  Proof.
    iIntros "[%U [BASE BASE2]]". iExists U.
    assert (
      ((λ k, if lt_dec k U then ε else TicketRA_Auth_base) : TicketRA) ~~>
      ((λ k, if lt_dec k (S U) then ε else TicketRA_Auth_base) : TicketRA)
        ⋅ (maps_to_res U TicketRA_Auth_base)) as UPD.
    { apply pointwise_updatable. i. unfold maps_to_res.
      rewrite !discrete_fun_lookup_op. des_ifs; try lia.
      - rewrite left_id. reflexivity.
      - rewrite left_id. reflexivity.
      - rewrite right_id. reflexivity.
    }
    iMod (OwnM_Upd with "BASE") as "[A B]".
    { apply UPD. }
    assert ((maps_to_res U TicketRA_Auth_base) ~~> (Ticket_black_ra U ∅)).
    { unfold TicketRA_Auth_base, Ticket_black_ra.
      apply maps_to_updatable. apply prod_update; [ | reflexivity].
      simpl. apply auth_update_dealloc. reflexivity.
    }
    iMod (OwnM_Upd with "B") as "D". apply H.
    assert ((maps_to_res U TicketRA_Auth_base) ~~> (Ticket_black_ra U ∅)).
    { unfold TicketRA_Auth_base, Ticket_black_ra.
      apply maps_to_updatable. apply prod_update; [ | reflexivity].
      apply auth_update_dealloc. reflexivity.
    }
    iMod (AuthExcls.alloc_gen (gt_dec U) (gt_dec (S U)) with "BASE2") as "(BASE2 & B)".
    { ii; des_ifs. lia. }
    iAssert (#=> OwnM (AuthExcls.black_ra U (κu, γs, b) ⋅ AuthExcls.white_ra U (κu, γs, b)))%I with "[B]" as "> [$ $]".
    { rewrite /AuthExcls.black_ra /AuthExcls.white_ra maps_to_res_add /maps_to_res /=.
      iApply (OwnM_Upd with "B"). apply pointwise_updatable => ?.
      des_ifs; try lia. apply excl_auth_update. }
    iModIntro; iFrame. iExists (S U). iFrame.
  Qed.

  Lemma Ticket_alloc γt D new l
    (NOTIN : new ∉ D)
    :
    Ticket_black γt D ⊢ |==> Ticket_black γt (D ∪ {[new]}) ∗ Ticket_issued γt new l ∗ Ticket_wait γt new l.
  Proof.
    iIntros "TB". unfold Ticket_black, Ticket_issued, Ticket_wait.
    assert ((Ticket_black_ra γt D) ~~>
      (Ticket_black_ra γt ({[new]} ∪ D) ⋅ Ticket_issued_ra γt new l ⋅ Ticket_wait_ra γt new l)).
    { rewrite /Ticket_black_ra /Ticket_issued_ra /Ticket_wait_ra !maps_to_res_add.
      apply maps_to_updatable,prod_update. simpl.
      etrans.
      { apply auth_update_alloc. instantiate (1:= (GSet ({[new]}))).
        apply gset_disj_alloc_empty_local_update.
        set_solver.
      }
      { rewrite <-(assoc cmra.op). rewrite -auth_frag_op right_id. reflexivity. }
      unfold AuExAny_ra, AuExAnyW_ra, AuExAnyB_ra, maps_to_res. apply pointwise_updatable. i. simpl.
      rewrite /AuthExcls.rest_ra /AuthExcls.white_ra /AuthExcls.black_ra /maps_to_res.
      rewrite !discrete_fun_lookup_op. des_ifs.
      { exfalso. clear -n e. rewrite not_elem_of_union in n. des. set_solver. }
      { rewrite left_id. apply excl_auth_update. }
      { exfalso. clear -n0 n e. set_solver. }
      { exfalso. clear -NOTIN n0. set_solver. }
    }
    iMod (OwnM_Upd with "TB") as "[[TB TI] TW]". apply H.
    iModIntro. iFrame.
    replace (D ∪ {[new]}) with ({[new]} ∪ D) by set_solver.
    done.
  Qed.

  Lemma Ticket_return γt D old l
    :
    Ticket_black γt D -∗ Ticket_issued γt old l -∗ Ticket_wait γt old l ==∗ Ticket_black γt (D ∖ {[old]}).
  Proof.
    iIntros "TB IS WA".
    unfold Ticket_black, Ticket_issued, Ticket_wait.
    iCombine "TB IS WA" as "TB".
    iMod (OwnM_Upd with "TB") as "$"; [|done].
    rewrite (assoc cmra.op) /Ticket_black_ra /Ticket_issued_ra /Ticket_wait_ra !maps_to_res_add.
    apply maps_to_updatable,prod_update; simpl in *.
    { rewrite <-(assoc cmra.op).
      rewrite -auth_frag_op right_id.
      apply auth_update_dealloc,gset_disj_dealloc_local_update.
    }
    unfold AuExAny_ra, AuExAnyW_ra, AuExAnyB_ra, maps_to_res. apply pointwise_updatable. i.
    rewrite /AuthExcls.rest_ra /AuthExcls.white_ra /AuthExcls.black_ra /maps_to_res.
    rewrite !discrete_fun_lookup_op. des_ifs.
    { exfalso. clear -e0. set_solver. }
    { rewrite left_id. apply excl_auth_update. }
    { exfalso. clear -e n n0. set_solver. }
    { exfalso. clear -e. set_solver. }
    { clear. apply cmra_discrete_update => ? WF.
      setoid_rewrite <- (assoc cmra.op (●E _)) in WF.
      by apply cmra_valid_op_l,cmra_valid_op_l,
        cmra_valid_op_r,excl_auth_frag_op_valid in WF.
    }
    { exfalso. clear -n e n0. set_solver. }
  Qed.

  Lemma Ticket_issued_wait γt tk l l' :
    Ticket_issued γt tk l -∗ Ticket_wait γt tk l' -∗ ⌜l = l'⌝.
  Proof.
    iIntros "I W". unfold Ticket_issued, Ticket_wait, Ticket_issued_ra, Ticket_wait_ra.
    iCombine "I W" as "IW". iOwnWf "IW" as IW.
    rewrite maps_to_res_add /maps_to_res in IW.
    specialize (IW γt). simpl in *. des_ifs.
    rewrite pair_valid /= in IW. des.
    specialize (IW0 tk).
    rewrite discrete_fun_lookup_op
      /AuExAnyW_ra /AuExAnyB_ra /maps_to_res
      /AuthExcls.white_ra /AuthExcls.black_ra
      /maps_to_res /=
    in IW0.
    des_ifs. apply excl_auth_agree_L, Any.upcast_inj in IW0.
    des. apply JMeq.JMeq_eq in EQ0. inv EQ0. iPureIntro; auto.
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