From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From iris Require Import bi.big_op.
From Fairness Require Import pind ITreeLib Red TRed IRed2 WFLibLarge.
From Fairness Require Import FairBeh Mod Linking.
From Fairness Require Import elimstack.Code.
From Fairness Require Import PCM IProp IPM IPropAux.
From Fairness Require Import IndexedInvariants OpticsInterp SimWeakest.
From Fairness Require Import TemporalLogic SCMemSpec ghost_var ghost_map ghost_excl.

Inductive maybe_null_ptr :=
| Null
| Ptr (p : SCMem.pointer)
.

Global Instance maybe_null_ptr_eq_dec : EqDecision maybe_null_ptr.
Proof. solve_decision. Qed.

Section SPEC.

  Context {src_state : Type}.
  Context {src_ident : Type}.
  Context {Client : Mod.t}.
  Context {gvs : list nat}.
  Context (elimN : namespace) `{DISJ: (↑N_state_tgt :coPset) ## (↑elimN : coPset)}.
  Notation tgt_state := (OMod.closed_state Client (SCMem.mod gvs)).
  Notation tgt_ident := (OMod.closed_ident Client (SCMem.mod gvs)).

  Local Instance STT : StateTypes := Build_StateTypes src_state tgt_state src_ident tgt_ident.

  Context `{sub : @SRA.subG Γ Σ}.
  Context {TLRASs : TLRAs_small STT Γ}.
  Context {TLRAS : TLRAs STT Γ Σ}.

  Context {HasMEMRA: @GRA.inG memRA Γ}.
  Context {HasAuthExcl : @GRA.inG (ghost_varURA (list SCMem.val)) Γ}.
  Context {HasExcl : @GRA.inG (ghost_exclURA unit) Γ}.
  Context {HasGhostMap : @GRA.inG (ghost_mapURA nat maybe_null_ptr) Γ}.

  Let stackN := elimN .@ "stack".
  Let offerN := elimN .@ "offer".

  Ltac red_tl_all := red_tl_every; red_tl_memra; red_tl_ghost_var; red_tl_ghost_map; red_tl_ghost_excl.

  Definition to_val mnp : SCMem.val :=
    match mnp with
    | Null => SCMem.val_null
    | Ptr p => SCMem.val_ptr p
    end.

  Fixpoint phys_list n l L : sProp n := (
    match L,l with
    | [],Null => emp
    | v::tL,Ptr p => ∃ (r : τ{maybe_null_ptr}), (p ↦∗□ [(to_val r); v]) ∗ (phys_list n r tL)
    | _,_ => ⌜False⌝
    end
  )%S.

  Definition EStack n γs St : sProp n := (
    syn_ghost_var γs (1/2) St
  )%S.

  Definition LInv n k γl h m : sProp n  := (
    syn_ghost_map_auth γl 1 m ∗
    [∗ n, maybe_null_ptr map] i ↦ p ∈ m, (
      if (decide (h=p)) then
        emp
      else
        ◇[k](0,1)
    )
  )%S.

  Inductive offer_state := OfferPending | OfferRevoked | OfferAccepted | OfferAcked.

  Local Instance offer_state_eq_dec : EqDecision offer_state.
  Proof. solve_decision. Qed.

  Local Instance: Inhabited offer_state := populate OfferPending.

  Definition offer_state_rep (st : offer_state) : nat :=
    match st with
    | OfferPending => 0
    | OfferRevoked => 1
    | OfferAccepted => 1
    | OfferAcked => 1
    end.

  Definition offer_st n (offer_loc : SCMem.pointer) (γo : nat) (P Q : τ{Φ,1+n}%stype) : sProp n :=
    (∃ (st : τ{offer_state,n}),
      offer_loc ↦ (offer_state_rep st) ∗
      match st with
      | OfferPending => P
      | OfferAccepted => Q
      | _ => GEx γo tt
      end)%S.

  (* TODO: accuratly defining this might be a bit annoying. *)
  Definition stack_push_au n γs val (Q : τ{Φ,2+n}%stype) : sProp (1+n) :=
    (AU <{ ∃∃ St, ⤉ EStack n γs St }> @ n, (⊤∖↑elimN), ∅ <{ ∀∀ (_ : unit), ⤉ EStack n γs (val::St), COMM Q}>)%S.

  Definition IsO (n : nat) (γs : nat) (offer_rep : maybe_null_ptr) : sProp (2+n) :=
    (match offer_rep with
    | Null => emp
    | Ptr p => ∃ (Q : τ{Φ,2+n}%stype) (v : τ{SCMem.val}) (γo : τ{nat}),
        (⤉ syn_inv (1+n) offerN (offer_st (1+n) p γo (stack_push_au n γs v Q) Q)) ∗
        (⤉⤉ ((SCMem.val_add p 1) ↦□ v))
    end
    )%S.

  Definition OInv n (s : SCMem.val) (γs : nat) : sProp (2+n) :=(
    ∃ (offer_rep : τ{maybe_null_ptr,2+n}),
    (⤉⤉ ((SCMem.val_add s 1) ↦ (to_val offer_rep))) ∗
    IsO n γs offer_rep
  )%S.

  Definition Inv n (s : SCMem.val) (k γs γl : nat) : sProp (2+n) := (
    ∃ (h : τ{maybe_null_ptr,2+n}) (L : τ{list SCMem.val,2+n}) (m : τ{gmap nat maybe_null_ptr,2+n}),
      (⤉⤉ (s ↦ (to_val h))) ∗
      (⤉⤉ syn_ghost_var γs (1/2) L) ∗
      (⤉⤉ phys_list n h L) ∗
      (⤉⤉ LInv n k γl h m) ∗
      OInv n s γs
  )%S.

  Definition IsES n l a s k γs : sProp (2+n) := (
    ∃ (γl : τ{nat,2+n}), ◆[k,l,a] ∗ syn_inv (2+n) stackN (Inv n s k γs γl)
  )%S.

  Global Instance IsES_persistent n l a s k γs :
    Persistent ⟦ IsES n l a s k γs, 2+n⟧.
  Proof. unfold Persistent,IsES. red_tl.
    iIntros "[%γl H]". iExists γl. red_tl.
    rewrite red_syn_inv.
    iDestruct "H" as "#$".
  Qed.

  Lemma Inv_unfold n s k γs γl :
    (⟦ Inv n s k γs γl, 2+n ⟧) -∗
    ∃ h L m,
      s ↦ (to_val h) ∗ ghost_var γs (1/2) L ∗
      ⟦ phys_list n h L, n⟧ ∗ ⟦ LInv n k γl h m, n⟧ ∗ ⟦ OInv n s γs, 2+n⟧.
  Proof.
    unfold Inv. iIntros "Inv".
    repeat (red_tl; iDestruct "Inv" as "[% Inv]"). simpl.
    red_tl_all. eauto.
  Qed.

  Lemma Inv_fold n s k γs γl h L m :
    s ↦ (to_val h) -∗ ghost_var γs (1/2) L -∗
    ⟦ phys_list n h L, n⟧ -∗ ⟦ LInv n k γl h m, n⟧ -∗ ⟦ OInv n s γs, 2+n⟧
    -∗ ⟦ Inv n s k γs γl, 2+n ⟧.
  Proof.
    unfold Inv. iIntros "? ? ? ? ?". simpl.
    repeat (red_tl; iExists _).
    red_tl_all. iFrame.
  Qed.

  Lemma LInv_unfold n k γl h m :
    ⟦ LInv n k γl h m, n ⟧ -∗
    ghost_map_auth γl 1 m ∗
    [∗ map] a ∈ m,
      if decide (h = a) then
          emp
        else
          ◇[k](0, 1)
        .
  Proof.
    unfold LInv. red_tl_all. iIntros "[$ H]".
    rewrite red_syn_big_sepM.
    iApply (big_sepM_mono with "H").
    ii. des_ifs.
  Qed.

  Lemma LInv_fold n k γl h m :
    ghost_map_auth γl 1 m -∗
    ([∗ map] a ∈ m,
      if decide (h = a) then
          emp
        else
          ◇[k](0, 1)
        )
    -∗ ⟦ LInv n k γl h m, n ⟧.
  Proof.
    unfold LInv. red_tl_all. iIntros "$ H".
    rewrite red_syn_big_sepM.
    iApply (big_sepM_mono with "H").
    ii. des_ifs.
  Qed.

  Lemma phys_list_unfold n l L :
    ⟦ phys_list n l L, n ⟧ -∗
    match L,l with
    | [],Null => emp
    | v::tL,Ptr p => ∃ r, p ↦∗□ [to_val r; v] ∗ ⟦phys_list n r tL,n⟧
    | _,_ => ⌜False⌝
    end.
  Proof.
    iIntros "H". des_ifs. simpl. destruct p.
    red_tl_all; iDestruct "H" as (r) "H".
    red_tl_all; iDestruct "H" as "[(l.n↦ & l.d↦ & _) Phys]".
    iExists _. iFrame.
  Qed.

  Lemma phys_list_fold n l L :
    (match L,l with
    | [],Null => emp
    | v::tL,Ptr p => ∃ r, p ↦∗□ [to_val r; v] ∗ ⟦phys_list n r tL,n⟧
    | _,_ => ⌜False⌝
    end) -∗
    ⟦ phys_list n l L, n ⟧.
  Proof.
    iIntros "H". des_ifs. simpl. destruct p.
    red_tl_all; iDestruct "H" as (r) "[(l.n↦ & l.d↦ & _) Phys]".
    red_tl_all. iExists r.
    red_tl_all. iFrame.
  Qed.

  Lemma phys_list_get_head n l L :
    ⟦ phys_list n l L, n ⟧ -∗
    □ if decide (l = Null) then
        emp
      else ∃ r h, (to_val l) ↦∗□ [to_val r; h]
    .
  Proof.
    iIntros "H". iDestruct (phys_list_unfold with "H") as "H".
    des_ifs.
    iDestruct "H" as (r) "[#H _]".
    red_tl_all. iExists r, v. iFrame "H".
  Qed.

  Lemma OInv_unfold n s γs :
    ⟦ OInv n s γs, 2+n ⟧ -∗
    ∃ offer_rep,
      (SCMem.val_add s 1) ↦ (to_val offer_rep) ∗ ⟦ IsO n γs offer_rep, 2+n ⟧.
  Proof. unfold OInv. simpl. red_tl_all. iIntros "[% H]". red_tl_all. eauto. Qed.

  Lemma OInv_fold n s γs offer_rep :
    (SCMem.val_add s 1) ↦ (to_val offer_rep) -∗
    ⟦ IsO n γs offer_rep, 2+n ⟧
    -∗ ⟦ OInv n s γs, 2+n ⟧.
  Proof. unfold OInv. simpl. red_tl_all. iIntros "? ?". iExists _. red_tl_all. iFrame. Qed.

  Lemma IsO_unfold n γs offer_rep :
    ⟦ IsO n γs offer_rep, 2+n ⟧ -∗
    match offer_rep with
    | Null => emp
    | Ptr p => ∃ Q v γo,
        inv (1+n) offerN (offer_st (1+n) p γo (stack_push_au n γs v Q) Q) ∗
        (SCMem.val_add p 1 ↦□ v)
    end.
  Proof.
    unfold IsO. simpl. iIntros "H". des_ifs; eauto.
    repeat (red_tl; iDestruct "H" as "[% H]").
    red_tl_all. rewrite red_syn_inv.
    iExists _,_,_. iFrame "H".
  Qed.

  Lemma IsO_fold n γs offer_rep :
    match offer_rep with
    | Null => emp
    | Ptr p => ∃ Q v γo,
        inv (1+n) offerN (offer_st (1+n) p γo (stack_push_au n γs v Q) Q) ∗
        (SCMem.val_add p 1 ↦□ v)
    end -∗
    ⟦ IsO n γs offer_rep, 2+n ⟧.
  Proof.
    unfold IsO. simpl. iIntros "H". des_ifs; eauto.
    iDestruct "H" as (???) "#H".
    repeat (red_tl; iExists _). red_tl_all. rewrite red_syn_inv.
    done.
  Qed.

  Lemma offer_st_unfold n offer_rep γo γs Q v :
    ⟦offer_st (1+n) offer_rep γo (stack_push_au n γs v Q) Q, 1+n⟧ -∗
    ∃ st,
      offer_rep ↦ (offer_state_rep st) ∗
      match st with
      | OfferPending => ⟦stack_push_au n γs v Q,1+n⟧
      | OfferAccepted => ⟦Q,1+n⟧
      | _ => GEx γo tt
      end.
  Proof.
    iIntros "H". unfold offer_st. red_tl_all.
    iDestruct "H" as (st) "H".
    iExists st. des_ifs; red_tl_all; ss.
  Qed.

  Lemma offer_st_fold st offer_rep n γo γs Q v  :
    (SCMem.val_ptr offer_rep) ↦ (offer_state_rep st) -∗
    match st with
    | OfferPending => ⟦stack_push_au n γs v Q,1+n⟧
    | OfferAccepted => ⟦Q,1+n⟧
    | _ => GEx γo tt
    end
    -∗ ⟦offer_st (1+n) offer_rep γo (stack_push_au n γs v Q) Q, 1+n⟧.
  Proof.
    iIntros "? ?". unfold offer_st. red_tl_all.
    iExists st. red_tl_all. iFrame.
    des_ifs; red_tl_all; ss.
  Qed.

  Lemma alloc_ElimStack n s l a :
    ⊢ s ↦ SCMem.val_null -∗ (SCMem.val_add s 1) ↦ SCMem.val_null =|3 + n|={∅}=∗ ∃ k γs, ⟦IsES n l a s k γs,2 + n⟧ ∗ ⟦EStack n γs [],n⟧ ∗ ◇[k](l,a).
  Proof.
    simpl. iIntros "s↦ s.o↦".
    iMod (alloc_obligation_fine l a) as (k) "(#Ob_kb & PCs & _)".
    iMod ghost_map_alloc_empty as (γl) "M".
    iMod (ghost_var_alloc []) as (γs) "V".
    iEval (rewrite -Qp.half_half) in "V".
    iEval (rewrite ghost_var_split) in "V".
    iDestruct "V" as "[VI VS]".
    iMod (FUpd_alloc _ _ _ (2+n) (stackN) (Inv n s k γs γl) with "[VI s↦ s.o↦ M]") as "#Inv"; [lia| |].
    { iApply (Inv_fold _ _ _ _ _ Null with "s↦ VI [] [M]").
      - iApply phys_list_fold. done.
      - iApply (LInv_fold with "M"). done.
      - iApply (OInv_fold _ _ _ Null with "s.o↦ []").
        iApply IsO_fold. done.
    }
    iModIntro. iExists _,_. iFrame. unfold IsES,EStack. red_tl_all.
    iFrame. iExists _. red_tl. rewrite red_syn_inv. iFrame "#".
  Qed.

  Lemma Elim_pop_spec
        {n} (Q : (option SCMem.val) → sProp (1+n)) tid :
    ∀ s k γs l a (ds : list (nat * nat * sProp n)),
    ⊢ [@ tid,n,2,⊤ @]
          ⧼⟦(
            syn_tgt_interp_as (2+n) sndl (fun m => s_memory_black m) ∗
            (⤉ IsES n l a s k γs) ∗
            (⤉⤉⤉ Duty(tid) ds) ∗
            (⤉⤉ AU <{ ∃∃ St, ⤉ EStack n γs St }>
                    @ n, (⊤∖↑elimN), ∅
                    <{ ∀∀ (_ : unit), ⤉ EStack n γs (tail St), COMM Q (hd_error St) }>) ∗
            ◇[k](1,1) ∗
            ◇{List.map fst ds}(2+l,2+a)
            )%S, 3+n⟧⧽
            (OMod.close_itree Client (SCMem.mod gvs) (ElimStack.pop s))
          ⧼rv, ⟦(
            (⤉⤉ Q rv) ∗ (⤉⤉⤉ Duty(tid) ds) ∗
            match rv with
            | Some _ => emp
            | None => ◇[k](1,1)
            end
            )%S, 3+n⟧⧽
  .
  Proof.
    ii. iStartTriple. red_tl_all.
    unfold IsES,EStack. simpl. rewrite red_syn_tgt_interp_as. red_tl. simpl. rewrite red_syn_atomic_update.
    iIntros "(#Mem & IsES & Duty & AU & Ob_ks & PCS)".
    set POST := (POST in (POST -∗ _)%I).
    iIntros "Post".
    iDestruct "IsES" as (γl) "IsES".
    red_tl. rewrite red_syn_inv. iDestruct "IsES" as "#[Ob_kb IsES]".

    iMod (pcs_decr _ _ 1 (1+a) with "PCS") as "[Ys PCS]"; [lia|].
    iMod (pcs_decr _ _ 1 a with "PCS") as "[PCS CCS]"; [lia|].
    iMod (pcs_drop _ _ 1 ltac:(lia) 1 102 with "Ys") as "Ys"; [lia|].
    iMod (ccs_make_fine _ _ _ _ 2 with "[$Ob_kb $CCS]") as "CCS".

    iEval (unfold ElimStack.pop). rred2r.

    iMod (pcs_decr _ _ 101 1 with "Ys") as "[Ys Y]"; [lia|].
    iApply (wpsim_yieldR with "[$Duty $Y]"); [lia..|].
    iIntros "Duty _". rred2r.

    iApply wpsim_tauR. rred2r.

    iRevert "Post Duty Ys AU Ob_ks". iRevert "PCS".

    iMod (ccs_ind2 with "CCS [-]") as "Ind".
    2:{ iIntros "PCS". destruct l; last first.
        - iMod (pcs_drop _ _ 1 ltac:(auto) 2 1 with "PCS") as "PCS"; [lia|].
        iApply ("Ind" with "PCS").
        - iApply ("Ind" with "PCS").
    }

    iModIntro. iExists 0. iIntros "IH !> PCS Post Duty Ys AU Ob_ks".
    iEval (rewrite ElimStack.pop_loop_red). rred2r.

    iMod (pcs_decr _ _ 100 1 with "Ys") as "[Ys Y]"; [lia|].
    iApply (wpsim_yieldR with "[$Duty $Y]"); [lia..|].
    iIntros "Duty _". rred2r.

    iInv "IsES" as "Inv" "Close". simpl.
    iDestruct (Inv_unfold with "Inv") as (h St m) "(s↦ & γs & Phys & LInv & OInv)".

    iApply (SCMem_load_fun_spec_gen _ _ _ _ n 2 with "[$Mem $s↦] [-]"); [lia|solve_ndisj|].
    iIntros (?) "[%EQ s↦]".
    subst. rred2r. iApply wpsim_tauR. rred2r.
    iMod (pcs_decr _ _ 99 1 with "Ys") as "[Ys Y]"; [lia|].

    destruct (decide (h = Null)) as [->|NEQ].
    { (* Head is null, so stack is empty. *)
      simpl in *.
      iEval (rewrite phys_list_unfold) in "Phys".
      des_ifs. iClear "Phys".
      iMod (fupd_mask_subseteq (⊤ ∖ ↑elimN)) as "CloseE"; [solve_ndisj|].
      iMod "AU" as (?) "[γs' Commit]". red_tl_all.
      iDestruct (ghost_var_agree with "γs γs'") as %<-.
      iMod ("Commit" $! tt with "γs'") as "Q".
      iMod "CloseE" as "_".
      iDestruct (Inv_fold with "[s↦] γs [] LInv OInv") as "Inv".
      { unfold to_val. iFrame. }
      { iApply phys_list_fold. done. }
      iMod ("Close" with "Inv") as "_". rred2r.

      iApply (wpsim_yieldR with "[$Duty $Y]"); [lia..|].
      iIntros "Duty _". rred2r.

      iApply (SCMem_compare_fun_spec_gen _ _ _ _ n 2 with "[Mem] [-]"); [|solve_ndisj| |].
      2:{ iApply (tgt_interp_as_equiv with "Mem"). clear.
          iStartProof. iIntros (m). simpl. red_tl_all. iSplit.
          - iIntros "$". iPureIntro. done.
          - iIntros "[$ _]".
        }
      1: lia.
      iIntros (?) "%EQ". destruct EQ as [EQ _].
      specialize (EQ ltac:(auto)) as ->. rred2r.

      iApply wpsim_tauR. rred2r.
      iApply "Post". red_tl_all. iFrame.
    }

    iDestruct (phys_list_get_head with "Phys") as "#h↦□".
    case_decide; [done|].
    iDestruct "h↦□" as (r d) "[h.n↦□ [h.d↦□ _]]".
    (* Update Linv by adding myself to the ghost map, in the same way as push *)

    iDestruct (LInv_unfold with "LInv") as "[GMap LivC]".
    set (i := fresh (dom m)).
    iMod (ghost_map_insert i h with "[$GMap]") as "[GMap i↪]".
    { apply not_elem_of_dom. apply is_fresh. }

    iDestruct (LInv_fold with "GMap [LivC]") as "LInv".
    { erewrite big_sepM_insert; last first.
      { apply not_elem_of_dom. apply is_fresh. }
      iFrame. case_decide; done.
    }

    iDestruct (Inv_fold with "s↦ γs Phys LInv OInv") as "Inv".
    iMod ("Close" with "Inv") as "_". move: i=>i. clear dependent St m.

    iApply (wpsim_yieldR with "[$Duty $Y]"); [lia..|].
    iIntros "Duty _". rred2r.

    iApply (SCMem_compare_loc_null_fun_spec_gen _ _ _ _ n 2 with "[$Mem $h.n↦□] [-]"); [lia|solve_ndisj|].
    iIntros (?) "[_ %EQ]". subst. rred2r.

    iApply wpsim_tauR. rred2r.

    iMod ((pcs_decr _ _ 98 1) with "Ys") as "[Ys Y]"; [lia|].
    iApply (wpsim_yieldR with "[$Duty $Y]"); [lia..|].
    iIntros "Duty _". rred2r.

    iApply (SCMem_load_fun_spec_gen _ _ _ _ n 2 with "[$Mem $h.n↦□] [-]"); [lia|solve_ndisj|].
    iIntros (?) "[%EQ _]". subst. rred2r.

    iApply wpsim_tauR. rred2r.

    iMod ((pcs_decr _ _ 97 1) with "Ys") as "[Ys Y]"; [lia|].
    iApply (wpsim_yieldR with "[$Duty $Y]"); [lia..|].
    iIntros "Duty _". rred2r.

    iInv "IsES" as "Inv" "Close". simpl.
    iDestruct (Inv_unfold with "Inv") as (h' L m) "(s↦ & γs & Phys & LInv & OInv)".
    iDestruct (phys_list_get_head with "Phys") as "#h'↦□".
    destruct (decide (h = h')) as [<-|NEQhh'].
    { des_ifs. iDestruct "h'↦□" as (r' d') "[h'.n↦□ [h'.d↦□ _]]". subst.
      iDestruct (memory_ra_points_to_agree with "h.d↦□ h'.d↦□") as %<-.
      iDestruct (memory_ra_points_to_agree with "h.n↦□ h'.n↦□") as %<-.

      iDestruct (phys_list_unfold with "Phys") as "Phys".
      destruct L as [|v tL], h as [|[h]]; try done.
      iDestruct "Phys" as (r_new) "[[#h.n↦□' [#h.d↦□' _]] Phys]".

      iDestruct (memory_ra_points_to_agree with "h.d↦□ h.d↦□'") as %<-.
      iDestruct (memory_ra_points_to_agree with "h.n↦□ h.n↦□'") as %->.
      clear r. iClear "h.n↦□' h.d↦□' h'.n↦□ h'.d↦□".

      (* Equal, CAS success *)
      iApply (SCMem_cas_loc_fun_spec_gen_gen _ _ _ _ n 2 with "[$Mem $s↦] [-]"); [lia|solve_ndisj| |].
      { des_ifs. iSplit; iExists _; iFrame "h.n↦□". }

      iIntros (b) "POST".

      iDestruct "POST" as (u) "(%EQ & s↦ & _ & _)".
      des_ifs. destruct EQ as [-> ->].

      (* Update logical & physical stack state. *)
      iMod (fupd_mask_subseteq (⊤ ∖ ↑elimN)) as "CloseE"; [solve_ndisj|].

      simpl.
      iMod "AU" as (?) "[γs' Commit]". red_tl_all.
      iDestruct (ghost_var_agree with "γs γs'") as %<-.
      iMod (ghost_var_update_halves with "γs γs'") as "[γs γs']".
      iMod ("Commit" $! tt with "γs'") as "Q".
      iMod "CloseE" as "_".

      (* Update liveness invariant *)
      iDestruct (LInv_unfold with "LInv") as "[GMap LivC]".

      iDestruct (ghost_map_lookup with "GMap i↪") as "%Lookup_i".
      iMod (ghost_map_delete with "GMap i↪") as "GMap".

      (** Create a big_opM of ◇[k](0,1). *)
      iMod (pc_drop _ 0 1 ltac:(lia) (size (delete i m)) with "Ob_ks") as "Ob_ks"; [lia|].
      iAssert ([∗ map] _ ∈ delete i m, ◇[k](0,1))%I with "[Ob_ks]" as "Ob_ks".
      { set (m' := delete i m). move: m' => m'.
        iClear "Mem IsES h.n↦□ h.d↦□ Ob_kb". clear.
        simpl in *.
        iInduction (m') as [|id op m NotIN] "IH" using map_ind.
        { done. }
        rewrite big_sepM_insert; [|done].
        rewrite map_size_insert_None; [|done].
        iDestruct (pc_split _ _ 1 (size m) with "Ob_ks") as "[$ Ob_ks]".
        iApply ("IH" with "Ob_ks").
      }

      (** Add it to the invariant. *)
      iDestruct (big_sepM_delete with "LivC") as "[_ LivC]"; [apply Lookup_i|].
      iDestruct (LInv_fold _ _ _ r_new with "GMap [LivC Ob_ks]") as "LInv".
      { iDestruct (big_sepM_sep_2 with "LivC Ob_ks") as "LivC".
        iApply (big_sepM_mono with "LivC").
        iIntros (i' p' Lookup_i') "[H C]". des_ifs.
      }

      iDestruct (Inv_fold with "s↦ γs Phys LInv OInv") as "Inv".
      iMod ("Close" with "Inv") as "_". rred2r.

      iMod ((pcs_decr _ _ 96 1) with "Ys") as "[Ys Y]"; [lia|].
      iApply wpsim_tauR. rred2r.
      iApply (wpsim_yieldR with "[$Y $Duty]"); [lia|].
      iIntros "Duty _". rred2r.

      iApply (SCMem_load_fun_spec_gen _ _ _ _ n 2 with "[$Mem $h.d↦□] [-]"); [lia|solve_ndisj|].
      iIntros (?) "[%EQ _]". subst. rred2r.

      iApply wpsim_tauR. rred2r.

      iApply "Post". red_tl. iFrame.
    }
    (* Different, CAS fail *)
    iApply (SCMem_cas_loc_fun_spec_gen_gen _ _ _ _ n 2 with "[$Mem $s↦ h.n↦□ h'↦□] [-]"); [lia|solve_ndisj| |].
    { unfold to_val. des_ifs.
      2,4: iDestruct "h'↦□" as (??) "[h'↦□ _]".
      all: iSplit; try done; iExists _; iFrame "#".
    }
    iClear "h'↦□".
    iIntros (b) "POST". iDestruct "POST" as (u) "(%EQ & s↦ & _ & _)".
    destruct (SCMem.val_eq_dec (to_val h') (to_val h)).
    all: destruct EQ as [-> ->].
    { exfalso. unfold to_val in e. des_ifs. }

    (* Update ◇[k](0,1) to use for induction *)
    iDestruct (LInv_unfold with "LInv") as "[GMap LivC]".

    iDestruct (ghost_map_lookup with "GMap i↪") as "%Lookup_i".
    iMod (ghost_map_delete with "GMap i↪") as "GMap".

    iDestruct (big_sepM_delete with "LivC") as "[Ob_k LivC]"; [apply Lookup_i|].
    case_decide; [done|].
    red_tl. simpl.

    iDestruct (LInv_fold with "GMap LivC") as "LInv".
    iDestruct (Inv_fold with "s↦ γs Phys LInv OInv") as "Inv".
    iMod ("Close" with "Inv") as "_". rred2r. clear dependent h' L m.

    iApply wpsim_tauR. rred2r.

    iMod ((pcs_decr _ _ 96 1) with "Ys") as "[Ys Y]"; [lia|].
    iApply (wpsim_yieldR with "[$Y $Duty]"); [lia|].
    iIntros "Duty _". rred2r.

    (* Check offer *)

    iInv "IsES" as "Inv" "Close". simpl.
    iDestruct (Inv_unfold with "Inv") as (h' L m) "(s↦ & γs & Phys & LInv & OInv)".

    iDestruct (OInv_unfold with "OInv") as (offer_rep) "(s.o↦ & IsO)".

    iApply (SCMem_load_fun_spec_gen _ _ _ _ n 2 with "[$Mem $s.o↦] [-]"); [lia|solve_ndisj|].
    iIntros (?) "[%EQ s.o↦]". subst. rred2r.

    iApply wpsim_tauR. rred2r.

    destruct offer_rep as [|offer_rep].
    { (* No offer *)
      iDestruct (OInv_fold _ _ _ Null with "[s.o↦] IsO") as "OInv".
      { unfold to_val. iFrame. }
      iDestruct (Inv_fold with "s↦ γs Phys LInv OInv") as "Inv".
      iMod ("Close" with "Inv") as "_".

      iMod ((pcs_decr _ _ 95 1) with "Ys") as "[Ys Y]"; [lia|].
      iApply (wpsim_yieldR with "[$Y $Duty]"); [lia|].
      iIntros "Duty _". rred2r.

      iApply (SCMem_compare_fun_spec_gen _ _ _ _ n 2 with "[Mem] [-]"); [|solve_ndisj| |].
      2:{ simpl. iApply (tgt_interp_as_equiv with "Mem"). clear.
          intros m. simpl. red_tl_all. iSplit.
          - iIntros "$". iPureIntro. done.
          - iIntros "[$ _]".
        }
      1: lia.
      iIntros (rv) "%EQ". destruct EQ as [EQ _].
      specialize (EQ ltac:(auto)) as ->.
      rred2r.

      iApply wpsim_tauR. rred2r.
      iApply wpsim_tauR. rred2r.

      (* Do Induction *)
      iMod (pcs_drop _ _ 1 ltac:(lia) 1 101 with "[$PCS]") as "PCS"; [lia|].
      iMod ("IH" with "Ob_k Post Duty PCS AU Ob_ks") as "IH".
      iApply "IH".
    }

    iDestruct (IsO_unfold with "IsO") as "Of".
    iDestruct "Of" as (Q' v γo) "#[OfInv OfD]".

    iDestruct (IsO_fold _ _ (Ptr offer_rep) with "[]") as "IsO".
    { iExists _,_,_. iFrame "#". }
    iDestruct (OInv_fold _ _ _ (Ptr offer_rep) with "s.o↦ IsO") as "OInv".
    iDestruct (Inv_fold with "s↦ γs Phys LInv OInv") as "Inv".
    iMod ("Close" with "Inv") as "_".

    iMod (pcs_decr _ _ 95 1 with "Ys") as "[Ys Y]"; [lia|].
    iApply (wpsim_yieldR with "[$Y $Duty]"); [lia|].
    iIntros "Duty _". rred2r.

    iInv "OfInv" as "Of" "CloseOf". simpl.
    iDestruct (offer_st_unfold with "Of") as (offer_state) "(n.o↦ & Of)".

    iApply (SCMem_compare_loc_null_fun_spec_gen _ _ _ _ n 2 with "[$Mem $n.o↦] [-]"); [lia|solve_ndisj|].
    iIntros (?) "[n.o↦ %EQ]". subst. rred2r.

    iApply wpsim_tauR. rred2r.

    iDestruct (offer_st_fold with "n.o↦ Of") as "Of".
    iMod ("CloseOf" with "Of") as "_".

    iMod ((pcs_decr _ _ 94 1) with "Ys") as "[Ys Y]"; [lia|].
    iApply (wpsim_yieldR with "[$Y $Duty]"); [lia|].
    iIntros "Duty _". rred2r. clear dependent offer_state.

    iInv "OfInv" as "Of" "CloseOf". simpl.
    iDestruct (offer_st_unfold with "Of") as (offer_state) "(n.o↦ & Of)".
    iApply (SCMem_cas_fun_spec_gen _ _ _ _ n 2 with "[Mem $n.o↦] [-]"); [|solve_ndisj| |].
    2:{ simpl in *. iApply (tgt_interp_as_equiv with "Mem").
        clear. intros m. simpl. red_tl_all. iSplit.
        - iIntros "$". done.
        - iIntros "[$ _]".
    }
    1: lia.
    iIntros (b) "POST". iDestruct "POST" as (u) "[%EQ n.o↦]".
    destruct offer_state; simpl in *.
    - (* OfferPending *)
      iRename "Of" into "AU'". iClear "IH".
      destruct (SCMem.val_eq_dec 0 0); [|done]. destruct EQ as [-> ->]. rred2r.
      iApply wpsim_tauR. rred2r.

      iInv "IsES" as "Inv" "Close". simpl. clear dependent h' L m.
      iDestruct (Inv_unfold with "Inv") as (h' L m) "(s↦ & γs & Phys & LInv & OInv)".

      iEval (unfold stack_push_au,EStack; rewrite red_syn_atomic_update) in "AU'".

      iMod (fupd_mask_subseteq (⊤ ∖ ↑elimN)) as "CloseE"; [solve_ndisj|].

      iMod "AU'" as (?) "[γs' Commit]". red_tl_all.
      iDestruct (ghost_var_agree with "γs γs'") as %<-.
      iMod (ghost_var_update_halves with "γs γs'") as "[γs γs']".
      iMod ("Commit" $! tt with "γs'") as "Q'".
      iMod "AU" as (?) "[γs' Commit]". red_tl_all.
      iDestruct (ghost_var_agree with "γs γs'") as %<-.
      iMod (ghost_var_update_halves with "γs γs'") as "[γs γs']".
      iMod ("Commit" $! tt with "γs'") as "Q".
      iMod "CloseE" as "_".

      iDestruct (Inv_fold with "s↦ γs Phys LInv OInv") as "Inv".
      iMod ("Close" with "Inv") as "_".

      iDestruct (offer_st_fold OfferAccepted with "n.o↦ Q'") as "Of".
      iMod ("CloseOf" with "Of") as "_".

      iMod ((pcs_decr _ _ 93 1) with "Ys") as "[Ys Y]"; [lia|].
      iApply (wpsim_yieldR with "[$Y $Duty]"); [lia|].
      iIntros "Duty _". rred2r.

      iApply (SCMem_load_fun_spec_gen _ _ _ _ n 2 with "[$Mem $OfD] [-]"); [lia|set_solver|].
      iIntros (?) "[%EQ _]". subst. rred2r.

      iApply wpsim_tauR. rred2r.
      iApply "Post". red_tl. iFrame.
    - (* OfferRevoked *)
      destruct (SCMem.val_eq_dec 1 0); [done|].
      destruct EQ as [-> ->]. rred2r.
      iDestruct (offer_st_fold OfferRevoked with "n.o↦ Of") as "Of".
      iMod ("CloseOf" with "Of") as "_".

      iApply wpsim_tauR. rred2r.

      iApply wpsim_tauR. rred2r.


      iMod (pcs_drop _ _ 1 ltac:(auto) 1 101 with "PCS") as "PCS"; [lia|].
      iMod ("IH" with "Ob_k Post Duty PCS AU Ob_ks") as "IH".
      iApply "IH".
    - (* OfferAccepted *)
      destruct (SCMem.val_eq_dec 1 0); [done|].
      destruct EQ as [-> ->]. rred2r.
      iDestruct (offer_st_fold OfferAccepted with "n.o↦ Of") as "Of".
      iMod ("CloseOf" with "Of") as "_".

      iApply wpsim_tauR. rred2r.

      iApply wpsim_tauR. rred2r.

      iMod (pcs_drop _ _ 1 ltac:(auto) 1 101 with "PCS") as "PCS"; [lia|].
      iMod ("IH" with "Ob_k Post Duty PCS AU Ob_ks") as "IH".
      iApply "IH".
    - (* OfferAcked *)
      destruct (SCMem.val_eq_dec 1 0); [done|].
      destruct EQ as [-> ->]. rred2r.
      iDestruct (offer_st_fold OfferAcked with "n.o↦ Of") as "Of".
      iMod ("CloseOf" with "Of") as "_".

      iApply wpsim_tauR. rred2r.

      iApply wpsim_tauR. rred2r.

      iMod (pcs_drop _ _ 1 ltac:(auto) 1 101 with "PCS") as "PCS"; [lia|].
      iMod ("IH" with "Ob_k Post Duty PCS AU Ob_ks") as "IH".
      iApply "IH".
  Qed.

  Lemma Elim_push_spec {n} (Q : sProp (1+n)) tid :
    ∀ s k γs val l a (ds : list (nat * nat * sProp n)),
    ⊢ [@ tid, n, 2, ⊤ @]
          ⧼⟦(
            (syn_tgt_interp_as (2+n) sndl (fun m => s_memory_black m))
            ∗ (⤉ IsES n l a s k γs)
            ∗ (⤉⤉⤉ Duty(tid) ds)
            ∗ (⤉⤉ AU <{ ∃∃ (St : list SCMem.val), ⤉ EStack n γs (St : list SCMem.val)}>
                    @ n, (⊤∖↑elimN), ∅
                    <{ ∀∀ (_ : unit), (⤉ EStack n γs (val::St)), COMM Q}>)
            ∗ ◇[k](1,1)
            ∗ ◇{List.map fst ds}(2+l,2+a)
            )%S, 3+n⟧⧽
            (OMod.close_itree Client (SCMem.mod gvs) (ElimStack.push (s,val)))
          ⧼_, ⟦(
            (⤉⤉ Q) ∗ (⤉⤉⤉ Duty(tid) ds)
            )%S, 3+n⟧⧽
  .
  Proof.
    ii. iStartTriple. red_tl_all.
    unfold IsES,EStack. simpl. rewrite red_syn_tgt_interp_as. red_tl. simpl.
    rewrite red_syn_atomic_update.
    iIntros "(#Mem & IsES & Duty & AU & Ob_ks & PCS)".
    set POST := (POST in (POST -∗ _)%I).
    iIntros "POST".
    iDestruct "IsES" as (γl) "IsES".
    red_tl. rewrite red_syn_inv. iDestruct "IsES" as "#[Ob_kb IsES]".

    rred2r.

    iMod (pcs_decr _ _ 1 (1+a) with "PCS") as "[Ys PCS]"; [lia|].
    iMod (pcs_decr _ _ 1 a with "PCS") as "[PCS CCS]"; [lia|].
    iMod (pcs_drop _ _ 1 ltac:(lia) 1 102 with "Ys") as "Ys"; [lia|].
    iMod (ccs_make_fine _ _ _ _ 2 with "[$Ob_kb $CCS]") as "CCS".

    iMod (pcs_decr _ _ 1 101 with "Ys") as "[Y Ys]"; [lia|].

    iApply (wpsim_yieldR with "[$Duty $Y]"); [lia|].
    iIntros "Duty _". rred2r.

    iApply wpsim_tauR. rred2r.

    iRevert "POST Duty Ys AU Ob_ks". iRevert "PCS".

    iMod (ccs_ind2 with "CCS [-]") as "Ind".
    2:{ iIntros "PCS". destruct l; last first.
        - iMod (pcs_drop _ _ 1 ltac:(auto) 2 1 with "PCS") as "PCS"; [lia|].
          iApply ("Ind" with "PCS").
        - iApply ("Ind" with "PCS").
    }

    iModIntro. iExists 0.
    set IH := (IH in (IH ==∗ _)%I).
    iIntros "IH !> Pcs Post Duty Ys AU Ob_ks".
    iEval (rewrite ElimStack.push_loop_red). rred2r.

    iMod ((pcs_decr _ _ 100 1) with "Ys") as "[Ys Y]"; [lia|].
    iApply (wpsim_yieldR with "[$Y $Duty]"); [lia|].
    iIntros "Duty _". rred2r.

    iInv "IsES" as "Inv" "Close".
    iDestruct (Inv_unfold with "Inv") as (h L m) "(s↦ & γs & Phys & LInv & OInv)". simpl.

    iApply (SCMem_load_fun_spec_gen _ _ _ _ n 2 with "[$Mem $s↦] [-]"); [lia|solve_ndisj|].
    iIntros (load_v) "[%EQ s↦]". subst.
    (* Get proof that h is live for future use. *)
    iDestruct (phys_list_get_head with "Phys") as "#h↦□".

    (* Register this thread to the current waiting list for h. *)
    iDestruct (LInv_unfold with "LInv") as "[GMap LivC]".
    set (i := fresh (dom m)).
    iMod (ghost_map_insert i h with "[$GMap]") as "[GMap i↪]".
    { apply not_elem_of_dom. apply is_fresh. }

    (* Close Invs *)
    iDestruct (LInv_fold with "GMap [LivC]") as "LInv".
    { erewrite big_sepM_insert; last first.
      { apply not_elem_of_dom. apply is_fresh. }
      iFrame. iClear "h↦□". case_decide; done.
    }

    iDestruct (Inv_fold with "s↦ γs Phys LInv OInv") as "Inv".
    iMod ("Close" with "Inv") as "_". move: i => i. clear dependent L m. rred2r.

    iApply wpsim_tauR. rred2r.

    iMod ((pcs_decr _ _ 99 1) with "Ys") as "[Ys Y]"; [lia|].
    iApply (wpsim_yieldR with "[$Y $Duty]"); [lia|].
    iIntros "Duty _". rred2r.

    iApply (SCMem_alloc_fun_spec_gen _ _ _ _ n 2 with "[$Mem] [-]"); [lia|set_solver|].
    iIntros (node) "(n.n↦ & n.d↦ & _)".
    rred2r. iApply wpsim_tauR. rred2r.

    iMod ((pcs_decr _ _ 98 1) with "Ys") as "[Ys Y]"; [lia|].
    iApply (wpsim_yieldR with "[$Y $Duty]"); [lia|].
    iIntros "Duty _". rred2r.

    iApply (SCMem_store_fun_spec_gen _ _ _ _ n 2 with "[$Mem $n.n↦] [-]"); [lia|set_solver|].
    iIntros (?) "n.n↦". rred2r. iApply wpsim_tauR. rred2r.

    iMod ((pcs_decr _ _ 97 1) with "Ys") as "[Ys Y]"; [lia|].
    iApply (wpsim_yieldR with "[$Y $Duty]"); [lia|].
    iIntros "Duty _". rred2r.

    iApply (SCMem_store_fun_spec_gen _ _ _ _ n 2 with "[$Mem $n.d↦] [-]"); [lia|set_solver|].
    iIntros (?) "n.d↦". rred2r. iApply wpsim_tauR. rred2r.

    iMod ((pcs_decr _ _ 96 1) with "Ys") as "[Ys Y]"; [lia|].
    iApply (wpsim_yieldR with "[$Y $Duty]"); [lia|].
    iIntros "Duty _". rred2r.

    iInv "IsES" as "Inv" "Close". simpl.
    iDestruct (Inv_unfold with "Inv") as (h' L m) "(s↦ & γs & Phys & LInv & OInv)".
    iDestruct (phys_list_get_head with "Phys") as "#h'↦□".
    destruct (decide (h = h')) as [<-|NEQ].
    { (* Equal, CAS success *)
      iApply (SCMem_cas_loc_fun_spec_gen_gen _ _ _ _ n 2 with "[$Mem $s↦ h↦□ h'↦□] [-]"); [lia|solve_ndisj| |].
      { des_ifs.
        iDestruct "h↦□" as (??) "[h↦□ _]".
        iSplit; iExists _; iFrame "h↦□".
      }
      iClear "h↦□ h'↦□".
      iIntros (b) "POST".
      iDestruct "POST" as (u) "(%EQ & s↦ & _ & _)".
      des_ifs. destruct EQ as [-> ->].
      rred2r. iApply wpsim_tauR. rred2r.

      (* Update logical stack state. *)
      iMod (fupd_mask_subseteq (⊤ ∖ ↑elimN)) as "CloseE"; [solve_ndisj|]. simpl.
      iMod "AU" as (?) "[γs' Commit]". red_tl_all.
      iDestruct (ghost_var_agree with "γs γs'") as %<-.
      iMod (ghost_var_update_halves with "γs γs'") as "[γs γs']".
      iMod ("Commit" $! tt with "γs'") as "Q".
      iMod "CloseE" as "_".

      (* Update physical stack state. *)
      iMod (SCMem.points_to_persist with "n.n↦") as "#n.n↦".
      iMod (SCMem.points_to_persist with "n.d↦") as "#n.d↦".
      destruct node as [|node]; [done|].
      iAssert (⟦ phys_list n (Ptr node) (val::L), n⟧)%I with "[Phys]" as "Phys".
      { iApply phys_list_fold. iExists _. iFrame "∗#". }

      (* Update liveness invariant *)
      iDestruct (LInv_unfold with "LInv") as "[GMap LivC]".

      iDestruct (ghost_map_lookup with "GMap i↪") as "%Lookup_i".
      iMod (ghost_map_delete with "GMap i↪") as "GMap".

      (** Create a big_opM of ◇[k](0,1). *)
      iMod (pc_drop _ 0 1 ltac:(auto) (size (delete i m)) with "Ob_ks") as "Ob_ks"; [lia|].
      iAssert ([∗ map] _ ∈ delete i m, ◇[k](0,1))%I with "[Ob_ks]" as "Ob_ks".
      { set (m' := delete i m). move: m' => m'.
        iClear "Mem IsES n.n↦ n.d↦". clear.
        simpl in *.
        iInduction (m') as [|id op m NotIN] "IH" using map_ind.
        { done. }
        rewrite big_sepM_insert; [|done].
        rewrite map_size_insert_None; [|done].
        iDestruct (pc_split _ _ 1 (size m) with "Ob_ks") as "[$ Ob_ks]".
        iApply ("IH" with "Ob_ks").
      }

      (** Add it to the invariant. *)
      iDestruct (big_sepM_delete with "LivC") as "[_ LivC]"; [apply Lookup_i|].
      iDestruct (LInv_fold _ _ _ (Ptr node) with "GMap [LivC Ob_ks]") as "LInv".
      { iDestruct (big_sepM_sep_2 with "LivC Ob_ks") as "LivC".
        iApply (big_sepM_mono with "LivC").
        iIntros (i' p' Lookup_i') "[H C]". des_ifs.
      }

      iDestruct (Inv_fold with "[s↦] γs Phys LInv OInv") as "Inv".
      { unfold to_val. iFrame. }
      iMod ("Close" with "Inv") as "_".

      iApply "Post". iFrame.
    }
    (* Different, CAS fail *)
    iApply (SCMem_cas_loc_fun_spec_gen_gen _ _ _ _ n 2 with "[$Mem $s↦ h↦□ h'↦□] [-]"); [lia|solve_ndisj| |].
    { unfold to_val. des_ifs.
      1,3: iDestruct "h'↦□" as (??) "[h'↦□ _]".
      2,3: iDestruct "h↦□" as (??) "[h↦□ _]".
      all: iSplit; try done; iExists _; iFrame "#".
    }
    iClear "h↦□ h'↦□".
    iIntros (b) "POST".
    iDestruct "POST" as (u) "(%EQ & s↦ & _ & _)".
    des_ifs. all: destruct EQ as [-> ->].
    { exfalso. clear - e NEQ. unfold to_val in e. des_ifs. }

    (* Update ◇[k](0,1) to use for induction *)
    iDestruct (LInv_unfold with "LInv") as "[GMap LivC]".

    iDestruct (ghost_map_lookup with "GMap i↪") as "%Lookup_i".
    iMod (ghost_map_delete with "GMap i↪") as "GMap".

    iDestruct (big_sepM_delete with "LivC") as "[Ob_k LivC]"; [apply Lookup_i|].
    case_decide; [done|].
    red_tl. simpl.

    iDestruct (LInv_fold with "GMap LivC") as "LInv".
    iDestruct (Inv_fold with "s↦ γs Phys LInv OInv") as "Inv".
    iMod ("Close" with "Inv") as "_". rred2r.
    clear dependent h' L m.

    iApply wpsim_tauR. rred2r.

    iMod ((pcs_decr _ _ 95 1) with "Ys") as "[Ys Y]"; [lia|].
    iApply (wpsim_yieldR with "[$Y $Duty]"); [lia|].
    iIntros "Duty _". rred2r.

    (* Offer *)
    iApply (SCMem_store_fun_spec_gen _ _ _ _ n 2 with "[$Mem $n.n↦] [-]"); [lia|set_solver|].
    iIntros (?) "n.n↦". rred2r. iApply wpsim_tauR. rred2r.

    iMod ((pcs_decr _ _ 94 1) with "Ys") as "[Ys Y]"; [lia|].
    iApply (wpsim_yieldR with "[$Y $Duty]"); [lia|].
    iIntros "Duty _". rred2r.

    (* Open Invariant *)
    iInv "IsES" as "Inv" "Close". simpl.
    iDestruct (Inv_unfold with "Inv") as (h' L m) "(s↦ & γs & Phys & LInv & OInv)".

    (* Open OInv *)
    iDestruct (OInv_unfold with "OInv") as (offer_rep) "(s.o↦ & IsO)".

    (* We don't need the old offer *)
    iClear "IsO".

    iApply (SCMem_store_fun_spec_gen _ _ _ _ n 2 with "[$Mem $s.o↦] [-]"); [lia|solve_ndisj|].
    iIntros (?) "s.o↦". rred2r. iApply wpsim_tauR. rred2r.

    (* Add AU to the invariant. *)
    iMod (ghost_excl_alloc tt) as (γo) "GEx".
    iMod (SCMem.points_to_persist with "n.d↦") as "#n.d↦□".

    destruct node as [|node]; [done|].

    iMod (FUpd_alloc _ _ _ (1+n) (offerN) (offer_st (1 + n) node γo (stack_push_au n _ _ _) Q : sProp (1+n))%S with "[AU n.n↦]") as "#InvOf"; [lia| |].
    { simpl. iApply (offer_st_fold OfferPending node with "n.n↦ [-]").
      unfold stack_push_au. rewrite red_syn_atomic_update. iFrame.
    }

    iDestruct (OInv_fold n _ _ (Ptr node) with "s.o↦ []") as "OInv".
    { iApply IsO_fold. iExists _,_,_. iFrame "#". }

    iDestruct (Inv_fold with "s↦ γs Phys LInv OInv") as "Inv".
    iMod ("Close" with "Inv") as "_".

    iMod ((pcs_decr _ _ 93 1) with "Ys") as "[Ys Y]"; [lia|].
    iApply (wpsim_yieldR with "[$Y $Duty]"); [lia|].
    iIntros "Duty _". rred2r. clear dependent offer_rep h' L m.

    (* Open invariant *)
    iInv "IsES" as "Inv" "Close". simpl.
    iDestruct (Inv_unfold with "Inv") as (h' L m) "(s↦ & γs & Phys & LInv & OInv)".

    (* Open OInv *)
    iDestruct (OInv_unfold with "OInv") as (offer_rep) "(s.o↦ & IsO)".

    iApply (SCMem_store_fun_spec_gen _ _ _ _ n 2 with "[$Mem $s.o↦] [-]"); [lia|solve_ndisj|].
    iIntros (?) "s.o↦". rred2r.

    (* Close Invariant *)
    iDestruct (OInv_fold _ _ _ Null with "s.o↦ []") as "OInv".
    { iApply IsO_fold. done. }
    iDestruct (Inv_fold with "s↦ γs Phys LInv OInv") as "Inv".
    iMod ("Close" with "Inv") as "_". clear dependent h' L m.

    iApply wpsim_tauR. rred2r.

    iMod ((pcs_decr _ _ 92 1) with "Ys") as "[Ys Y]"; [lia|].
    iApply (wpsim_yieldR with "[$Y $Duty]"); [lia|].
    iIntros "Duty _". rred2r.

    (* Open Invariant *)
    iInv "IsES" as "Inv" "Close". simpl.
    iDestruct (Inv_unfold with "Inv") as (h' L m) "(s↦ & γs & Phys & LInv & OInv)".
    iInv "InvOf" as "Of" "CloseOf".
    simpl.
    iDestruct (offer_st_unfold n node γo with "Of") as (offer_state) "(n.o↦ & Of)".
    iApply (SCMem_cas_fun_spec_gen _ _ _ _ n 2 with "[Mem $n.o↦] [-]"); [|solve_ndisj| |].
    2:{ simpl in *. iApply (tgt_interp_as_equiv with "Mem").
        clear. intros m. simpl. red_tl_all. iSplit.
        - iIntros "$". done.
        - iIntros "[$ _]".
    }
    1: lia.
    iIntros (b) "POST". iDestruct "POST" as (u) "[%EQ n.o↦]".
    destruct offer_state; simpl in *.
    - (* OfferPending *)
      iRename "Of" into "AU".
      unfold stack_push_au. rewrite red_syn_atomic_update.
      des_ifs. destruct EQ as [-> ->]. rred2r.

      iApply wpsim_tauR. rred2r. iApply wpsim_tauR.

      iDestruct (offer_st_fold OfferRevoked with "n.o↦ GEx") as "Of".
      iMod ("CloseOf" with "Of") as "_".

      iDestruct (Inv_fold with "s↦ γs Phys LInv OInv") as "Inv".
      iMod ("Close" with "Inv") as "_".

      iMod (pcs_drop _ _ 1 ltac:(auto) 1 101 with "Pcs") as "Pcs"; [lia|].

      iMod ("IH" with "Ob_k Post Duty Pcs AU Ob_ks") as "IH".
      iApply "IH".
    - iDestruct (ghost_excl_exclusive with "GEx Of") as %[].
    - (* OfferAccepted *)
      iRename "Of" into "Q". iClear (IH) "IH". des_ifs. destruct EQ as [-> ->]. rred2r.
      iApply wpsim_tauR. rred2r.

      iDestruct (offer_st_fold OfferAcked with "n.o↦ GEx") as "Of".
      iMod ("CloseOf" with "Of") as "_".

      iDestruct (Inv_fold with "s↦ γs Phys LInv OInv") as "Inv".
      iMod ("Close" with "Inv") as "_".

      iApply "Post". iFrame.
    - iDestruct (ghost_excl_exclusive with "GEx Of") as %[].
  Qed.

End SPEC.

Global Opaque IsES EStack ElimStack.pop ElimStack.push.
