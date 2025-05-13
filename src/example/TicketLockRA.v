From iris.algebra Require Import cmra gset updates local_updates auth lib.excl_auth functions.
From sflib Require Import sflib.
From Fairness Require Import Any PCM IPM IPropAux.
From Fairness Require Import TemporalLogic.
From Fairness Require Export AuthExclAnysRA AuthExclsRA.
From stdpp Require Import gmap.

Section Ticket.

  (* Resource for each ticket lock *)
  Definition _TicketRA : ucmra := prodUR (authUR (gset_disjUR nat)) AuthExclAnysRA.
  Definition TicketRA : ucmra := nat -d> _TicketRA.

  Context `{Σ : GRA.t}.
  Notation iProp := (iProp Σ) (only parsing).
  Context {HasTicketRA : @GRA.inG TicketRA Σ}.
  Context {AuthExclAnys : @GRA.inG (AuthExcls.t (nat * nat * nat)) Σ}.

  Definition TicketRA_Auth_base : _TicketRA :=
    (● (GSet ∅) ⋅ ◯ (GSet ∅),
      AuExAny_ra (λ k, gset_elem_of_dec k ∅)).

  Definition TicketRA_Auth : iProp :=
    ∃ (U : nat),
      OwnM ((fun k => if (lt_dec k U) then ε else TicketRA_Auth_base) : TicketRA)
        ∗ AuthExcls.rest (fun k => lt_dec k U) (0, 0, 0).

  Definition Ticket_black_ra (γt : nat) (D : gset nat) : TicketRA :=
    discrete_fun_singleton γt ((● (GSet D),
                      AuExAny_ra (fun k => gset_elem_of_dec k D)) : _TicketRA).
  Definition Ticket_black γt D := OwnM (Ticket_black_ra γt D).

  (* The issuing thread holds my ticket -> (my thread id, and my obligation id). *)
  Definition Ticket_issued_ra (γt : nat) (tk : nat) (l : list nat) : TicketRA :=
    discrete_fun_singleton γt ((◯ (GSet {[tk]}), AuExAnyW_ra tk l) : _TicketRA).
  Definition Ticket_issued γt tk l := OwnM (Ticket_issued_ra γt tk l).

  (* The invariant holds ticket -> (thread id, obligation id) for the waiting threads. *)
  Definition Ticket_wait_ra (γt : nat) (tk : nat) (l : list nat) : TicketRA :=
    discrete_fun_singleton γt ((◯ (GSet ∅), AuExAnyB_ra tk l) : _TicketRA).
  Definition Ticket_wait γt tk l := OwnM (Ticket_wait_ra γt tk l).

  (** Properties. *)
  Lemma Ticket_issued_twice (γt tk : nat) (l l' : list nat) :
    Ticket_issued γt tk l -∗ Ticket_issued γt tk l' -∗ False.
  Proof.
    iStartProof. iIntros "T1 T2".
    iCombine "T1" "T2" gives %T.
    iPureIntro.

    rewrite discrete_fun_singleton_op discrete_fun_singleton_valid
      pair_valid /= in T.
    des.

    rewrite discrete_fun_singleton_op discrete_fun_singleton_valid in T0.
    by apply excl_auth_frag_op_valid in T0.
  Qed.

  Lemma Ticket_black_issued (γt tk : nat) l D :
    Ticket_black γt D -∗ Ticket_issued γt tk l -∗ ⌜tk ∈ D⌝.
  Proof.
    iStartProof. iIntros "BLACK ISSUED".
    iCombine "BLACK" "ISSUED" gives %H.
    iPureIntro.

    rewrite discrete_fun_singleton_op discrete_fun_singleton_valid
      pair_valid /= in H.
    des.

    apply auth_both_dfrac_valid_discrete in H as [_ [?%gset_disj_included _]].
    set_solver.
  Qed.

  Lemma Ticket_black_wait (γt tk : nat) l D :
    Ticket_black γt D -∗ Ticket_wait γt tk l -∗ ⌜tk ∈ D⌝.
  Proof.
    iStartProof. iIntros "BLACK WAIT".
    iCombine "BLACK" "WAIT" gives %H.
    iPureIntro.

    rewrite discrete_fun_singleton_op discrete_fun_singleton_valid
      pair_valid /= in H.
    des.

    specialize (H0 tk).

    rewrite /AuExAny_ra /AuExAnyB_ra /AuthExcls.rest_ra /AuthExcls.black_ra in H0.
    rewrite discrete_fun_lookup_op discrete_fun_lookup_singleton in H0. des_ifs.

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
        ⋅ (discrete_fun_singleton U TicketRA_Auth_base)) as UPD.
    { apply discrete_fun_update. i.
      rewrite !discrete_fun_lookup_op.
      destruct (decide (U = a)) as [->|];
        rewrite ?discrete_fun_lookup_singleton ?discrete_fun_lookup_singleton_ne //;
      des_ifs; try lia.
    }
    iMod (OwnM_Upd with "BASE") as "[A B]".
    { apply UPD. }
    clear UPD.
    assert ((discrete_fun_singleton U TicketRA_Auth_base) ~~> (Ticket_black_ra U ∅)) as UPD.
    { apply discrete_fun_singleton_update, prod_update.
      - apply auth_update_dealloc. reflexivity.
      - reflexivity.
    }
    iMod (OwnM_Upd with "B") as "D".
    { apply UPD. }
    clear UPD.
    assert ((discrete_fun_singleton U TicketRA_Auth_base) ~~> (Ticket_black_ra U ∅)).
    { apply discrete_fun_singleton_update, prod_update.
      - apply auth_update_dealloc. reflexivity.
      - reflexivity.
    }
    iMod (AuthExcls.alloc_gen (gt_dec U) (gt_dec (S U)) with "BASE2") as "($ & B)".
    { ii; des_ifs. lia. }
    iFrame.
    iMod (OwnM_Upd with "B") as "[$ $]"; [|done].
    rewrite /AuthExcls.black_ra /AuthExcls.white_ra discrete_fun_singleton_op.
    apply discrete_fun_update => U'.
    destruct (decide (U = U')) as [->|];
      rewrite ?discrete_fun_lookup_singleton ?discrete_fun_lookup_singleton_ne //;
    des_ifs; try lia. apply excl_auth_update.
  Qed.

  Lemma Ticket_alloc γt D new l
    (NOTIN : new ∉ D)
    :
    Ticket_black γt D ⊢ |==> Ticket_black γt (D ∪ {[new]}) ∗ Ticket_issued γt new l ∗ Ticket_wait γt new l.
  Proof.
    iIntros "TB". unfold Ticket_black, Ticket_issued, Ticket_wait.
    assert ((Ticket_black_ra γt D) ~~>
      (Ticket_black_ra γt ({[new]} ∪ D) ⋅ Ticket_issued_ra γt new l ⋅ Ticket_wait_ra γt new l)).
    { rewrite !discrete_fun_singleton_op.
      apply discrete_fun_singleton_update,prod_update; simpl.
      - etrans.
        { apply auth_update_alloc,gset_disj_alloc_empty_local_update,
            disjoint_singleton_l,NOTIN.
        }
        { rewrite <-(assoc (⋅)). rewrite -auth_frag_op right_id. reflexivity. }
      - rewrite /AuExAny_ra /AuExAnyW_ra /AuExAnyB_ra /AuthExcls.rest_ra /AuthExcls.white_ra /AuthExcls.black_ra -assoc discrete_fun_singleton_op.
        apply discrete_fun_update => U.
        rewrite !discrete_fun_lookup_op.
        des_ifs; destruct (decide (new = U)) as [<-|];
          rewrite ?discrete_fun_lookup_singleton ?discrete_fun_lookup_singleton_ne //=.
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
    rewrite !discrete_fun_singleton_op.
    apply discrete_fun_singleton_update,prod_update; simpl in *.
    { rewrite -auth_frag_op right_id.
      apply auth_update_dealloc,gset_disj_dealloc_local_update.
    }
    rewrite discrete_fun_singleton_op.
    unfold AuExAny_ra, AuExAnyW_ra, AuExAnyB_ra. apply discrete_fun_update. i.
    rewrite /AuthExcls.rest_ra !discrete_fun_lookup_op.
    des_ifs; destruct (decide (old = a)) as [<-|];
          rewrite ?discrete_fun_lookup_singleton ?discrete_fun_lookup_singleton_ne //=.
    { exfalso. clear -e0. set_solver. }
    { rewrite left_id. apply excl_auth_update. }
    { exfalso. clear -e n n0. set_solver. }
    { exfalso. clear -e. set_solver. }
    { exfalso. clear -n e n0. set_solver. }
    { clear.
      rewrite assoc. setoid_rewrite <-(assoc (⋅) (●E _)).
      apply cmra_discrete_total_update => ? WF.
      by apply cmra_valid_op_l, cmra_valid_op_l,
        cmra_valid_op_r,excl_auth_frag_op_valid in WF.
    }
  Qed.

  Lemma Ticket_issued_wait γt tk l l' :
    Ticket_issued γt tk l -∗ Ticket_wait γt tk l' -∗ ⌜l = l'⌝.
  Proof.
    iIntros "I W".
    iCombine "I W" gives %IW.
    iPureIntro.
    rewrite discrete_fun_singleton_op discrete_fun_singleton_valid pair_valid /= in IW.

    des.

    rewrite discrete_fun_singleton_op discrete_fun_singleton_valid in IW0.

    apply excl_auth_agree_L, Any.upcast_inj in IW0.
    des. apply JMeq.JMeq_eq in EQ0. inv EQ0. done.
  Qed.

End Ticket.

Section SPROP.

  Context {STT : StateTypes}.
  Context `{sub : @SRA.subG Γ Σ}.
  Context {TLRASs : TLRAs_small STT Γ}.
  Context {TLRAS : TLRAs STT Γ Σ}.

  Context {HasTicket : @GRA.inG TicketRA Γ}.
  Context {AuthExclAnys : @GRA.inG (AuthExcls.t (nat * nat * nat)) Γ}.

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
