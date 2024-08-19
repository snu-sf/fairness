From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From iris Require Import bi.big_op.
From Fairness Require Import pind ITreeLib Red TRed IRed2 WFLibLarge.
From Fairness Require Import FairBeh Mod Linking.
From Fairness Require Import treiber.Code.
From Fairness Require Import PCM IPM IPropAux.
From Fairness Require Import IndexedInvariants OpticsInterp SimWeakest.
From Fairness Require Import TemporalLogic SCMemSpec ghost_var ghost_map.

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
  Context (treiberN : namespace) `(DISJ: (↑N_state_tgt :coPset) ## (↑treiberN : coPset)).
  Notation tgt_state := (OMod.closed_state Client (SCMem.mod gvs)).
  Notation tgt_ident := (OMod.closed_ident Client (SCMem.mod gvs)).

  Local Instance STT : StateTypes := Build_StateTypes src_state tgt_state src_ident tgt_ident.

  Context `{sub : @SRA.subG Γ Σ}.
  Context {TLRASs : TLRAs_small STT Γ}.
  Context {TLRAS : TLRAs STT Γ Σ}.

  Context {HasMEMRA: @GRA.inG memRA Γ}.
  Context {HasAuthExcl : @GRA.inG (ghost_varURA (list SCMem.val)) Γ}.
  Context {HasGhostMap : @GRA.inG (ghost_mapURA nat maybe_null_ptr) Γ}.

  Ltac red_tl_all := red_tl_every; red_tl_memra; red_tl_ghost_var; red_tl_ghost_map.

  Definition to_val (mnp : maybe_null_ptr) : SCMem.val :=
    match mnp with
    | Null => SCMem.val_null
    | Ptr p => SCMem.val_ptr p
    end
    .

  (* Physical list matches the logical list. *)
  Fixpoint phys_list n (l : maybe_null_ptr) (L : list SCMem.val) : sProp n := (
    match L,l with
    | [],Null => emp
    | v::tL,Ptr p => ∃ (r : τ{maybe_null_ptr}), (p ↦∗□ [(to_val r); v]) ∗ (phys_list n r tL)
    | _,_ => ⌜False⌝
    end
  )%S.

  (* Half of abstract state *)
  Definition TStack n γs St : sProp n := (
    syn_ghost_var γs (1/2) St
  )%S.

  (** Liveness invariant: collection of thread i with local head snapshot p
    If i's p is stale, it can obtain a progress credit from here.
    Since its CAS must fail, it uses said credit for induction.
  *)
  Definition LInv (n k γs : nat) (h : maybe_null_ptr) (m : gmap nat maybe_null_ptr) : sProp n  := (
    syn_ghost_map_auth γs 1 m ∗
    [∗ n, maybe_null_ptr map] i ↦ p ∈ m, (
      if (decide (h=p)) then
        emp
      else
        ◇[k](0,1)
    )
  )%S.

  (* Invariant of physical head, other half of abstract state, and other stuffs. *)
  Definition Inv (n : nat) (s : SCMem.val) (k γs γl : nat) : sProp n := (
    ∃ (h : τ{maybe_null_ptr}) (L : τ{list SCMem.val}) (m : τ{gmap nat maybe_null_ptr,n}),
      s ↦ (to_val h) ∗ syn_ghost_var γs (1/2) L ∗
      phys_list n h L ∗ LInv n k γl h m
  )%S.

  Definition IsT n l a s k γs : sProp n := (
    ∃ (γl : τ{nat,n}), ◆[k,l,a] ∗ syn_inv n treiberN (Inv n s k γs γl)
  )%S.

  Global Instance IsT_persistent n l a s k γs :
    Persistent (⟦ IsT n l a s k γs, n⟧).
  Proof. unfold Persistent,IsT. red_tl.
    iIntros "[%γl H]". iExists γl. red_tl.
    rewrite red_syn_inv.
    iDestruct "H" as "#$".
  Qed.

  Lemma Inv_unfold n s k γs γl :
    ⟦ Inv n s k γs γl, n ⟧ -∗
    ∃ h L m,
      (s ↦ (to_val h)) ∗ ghost_var γs (1/2) L ∗
      ⟦ phys_list n h L, n⟧ ∗ ⟦ LInv n k γl h m, n⟧.
  Proof.
    unfold Inv. iIntros "Inv".
    repeat (red_tl; iDestruct "Inv" as "[% Inv]").
    red_tl_all. eauto.
  Qed.

  Lemma Inv_fold n s k γs γl h L m :
    s ↦ (to_val h) -∗ ghost_var γs (1/2) L -∗
    ⟦ phys_list n h L, n⟧ -∗ ⟦ LInv n k γl h m, n⟧
    -∗ ⟦ Inv n s k γs γl, n ⟧.
  Proof.
    unfold Inv. iIntros "? ? ? ?".
    repeat (red_tl; iExists _).
    red_tl_all. iFrame.
  Qed.

  Lemma LInv_unfold n k γs h m :
    ⟦ LInv n k γs h m, n ⟧ -∗
    ghost_map_auth γs 1 m ∗
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
    | v::tL,Ptr p => ∃ r, p ↦∗□ [(to_val r); v] ∗ ⟦phys_list n r tL,n⟧
    | _,_ => ⌜False⌝
    end.
  Proof.
    iIntros "H". des_ifs. simpl. destruct p.
    red_tl_all; iDestruct "H" as (r) "H".
    red_tl_all; iDestruct "H" as "[(l.n↦ & l.d↦ & _) Phys]".
    iExists _. iFrame.
  Qed.

  Lemma phys_list_fold n l L :
    match L,l with
    | [],Null => emp
    | v::tL,Ptr p => ∃ r, p ↦∗□ [(to_val r); v] ∗ ⟦phys_list n r tL,n⟧
    | _,_ => ⌜False⌝
    end -∗
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
      else ∃ r h, to_val l ↦∗□ [(to_val r); h]
    .
  Proof.
    iIntros "H". iDestruct (phys_list_unfold with "H") as "H".
    des_ifs.
    iDestruct "H" as (r) "[#H _]".
    iExists r, v. iFrame "H".
  Qed.

  Lemma alloc_Treiber n s l a :
    ⊢ s ↦ SCMem.val_null =|S n|={∅}=∗ ∃ k γs, ⟦IsT n l a s k γs,n⟧ ∗ ⟦TStack n γs [],n⟧ ∗ ◇[k](l,a).
  Proof.
    iIntros "s↦".
    iMod (alloc_obligation_fine l a) as (k) "(#Ob_kb & PCs & _)".
    iMod ghost_map_alloc_empty as (γl) "M".
    iMod (ghost_var_alloc []) as (γs) "V".
    iEval (rewrite -Qp.half_half) in "V".
    iDestruct (ghost_var_split with "V") as "[VI VS]".
    iMod (FUpd_alloc _ _ _ n (treiberN) (Inv n s k γs γl) with "[VI s↦ M]") as "#Inv"; [lia| |].
    { iApply (Inv_fold _ _ _ _ _ Null with "s↦ VI [] [M]").
      - iApply phys_list_fold. done.
      - iApply (LInv_fold with "M"). done.
    }
    iModIntro. iExists _,_. iFrame. unfold IsT,TStack. red_tl_all.
    iFrame. iExists _. red_tl. rewrite red_syn_inv. iFrame "#".
  Qed.

  Lemma Treiber_push_spec {n} (Q : sProp (1+n)) tid :
    ∀ s k γs val l a (ds : list (nat * nat * sProp n)),
    ⊢ [@ tid, n, ⊤ @]
          ⧼⟦(
            (syn_tgt_interp_as n sndl (fun m => s_memory_black m))
            ∗ (⤉ IsT n l a s k γs)
            ∗ (⤉ Duty(tid) ds)
            ∗ AU <{ ∃∃ St, ⤉ TStack n γs St }> @ n, (⊤∖↑treiberN), ∅
                <{ ∀∀ (_ : unit), ⤉ TStack n γs (val::St), COMM Q }>
            ∗ ◇[k](1,1)
            ∗ ◇{List.map fst ds}(2+l,2+a)
            )%S, 1+n⟧⧽
            (OMod.close_itree Client (SCMem.mod gvs) (TreiberStack.push (s,val)))
          ⧼_, ⟦(
            Q ∗ (⤉ Duty(tid) ds)
            )%S, 1+n⟧⧽
  .
  Proof.
    ii. iStartTriple. red_tl_all.
    unfold IsT,TStack. rewrite red_syn_tgt_interp_as. rewrite red_syn_atomic_update. red_tl. simpl.
    iIntros "(#Mem & IsT & Duty & AU & Ob_ks & PCS)".
    set POST := (POST in (POST -∗ _)%I). iIntros "Post".
    iDestruct "IsT" as (γl) "IsT".
    red_tl. rewrite red_syn_inv. iDestruct "IsT" as "#[Ob_kb IsT]".

    iMod (pcs_decr 1 (1+a) with "PCS") as "[Ys PCS]"; [lia|].
    iMod (pcs_decr 1 a with "PCS") as "[PCS CCS]"; [lia|].
    iMod (pcs_drop 1 100 with "Ys") as "Ys"; [lia..|].
    iMod (ccs_make_fine _ _ _ _ 2 with "[$Ob_kb $CCS]") as "CCS".

    iEval (unfold TreiberStack.push). rred2r.

    iMod ((pcs_decr 99 1) with "Ys") as "[Ys Y]"; [lia|].
    iApply (wpsim_yieldR with "[$Duty $Y]"); [lia|].
    iIntros "Duty _". rred2r.

    iApply (SCMem_alloc_fun_spec with "[$Mem] [-]"); [lia|set_solver|].
    iIntros (node) "(n.n↦ & n.d↦ & _)".
    rred2r. iApply wpsim_tauR. rred2r.

    iMod ((pcs_decr 98 1) with "Ys") as "[Ys Y]"; [lia|].
    iApply (wpsim_yieldR with "[$Y $Duty]"); [lia|].
    iIntros "Duty _". rred2r.

    iApply (SCMem_store_fun_spec with "[$Mem $n.d↦] [-]"); [lia|set_solver|].
    iIntros (?) "n.d↦". rred2r. iApply wpsim_tauR. rred2r.

    move: (SCMem.val_nat 0) => next.

    iRevert "n.n↦ Post Duty Ys AU n.d↦ Ob_ks". iRevert (next). iRevert "PCS".

    iMod (ccs_ind2 with "CCS [-]") as "Ind".
    2:{ iIntros "PCS". destruct l; last first.
        - iMod (pcs_drop 2 1 with "PCS") as "PCS"; [lia..|].
          iApply ("Ind" with "PCS").
        - iApply ("Ind" with "PCS").
    }

    iModIntro. iExists 0.
    set IH := (IH in (IH ==∗ _)%I).
    iIntros "IH !> Pcs %next n.n↦ Post Duty Ys AU n.d↦ Ob_ks".
    rewrite TreiberStack.push_loop_red.
    rred2r.
    iMod (pcs_decr 97 1 with "Ys") as "[Ys Y]"; [lia|].

    iApply (wpsim_yieldR with "[$Y $Duty]"); [lia|].
    iIntros "Duty _". rred2r.

    iInv "IsT" as "Inv" "Close". simpl.
    iDestruct (Inv_unfold with "Inv") as (h L m) "(s↦ & γs & Phys & LInv)".
    iApply (SCMem_load_fun_spec with "[$Mem $s↦] [-]"); [lia|solve_ndisj|].
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
    { rewrite big_sepM_insert; last first.
      { apply not_elem_of_dom. apply is_fresh. }
      iFrame. iClear "h↦□". case_decide; done.
    }
    iDestruct (Inv_fold with "s↦ γs Phys LInv") as "Inv".
    iMod ("Close" with "Inv") as "_". move: i => i. clear dependent L m rv. rred2r.

    iApply wpsim_tauR. rred2r.

    iMod ((pcs_decr 96 1) with "Ys") as "[Ys Y]"; [lia|].
    iApply (wpsim_yieldR with "[$Y $Duty]"); [lia|].
    iIntros "Duty _". rred2r.

    iApply (SCMem_store_fun_spec with "[$Mem $n.n↦] [-]"); [lia|solve_ndisj|].
    iIntros (?) "n.n↦". rred2r. iApply wpsim_tauR. rred2r.

    iMod ((pcs_decr 95 1) with "Ys") as "[Ys Y]"; [lia|].
    iApply (wpsim_yieldR with "[$Y $Duty]"); [lia|].
    iIntros "Duty _". rred2r.

    iMod ((pcs_decr 94 1) with "Ys") as "[Ys Y]"; [lia|].

    iInv "IsT" as "Inv" "Close". simpl.
    iDestruct (Inv_unfold with "Inv") as (h' L m) "(s↦ & γs & Phys & LInv)".
    iDestruct (phys_list_get_head with "Phys") as "#h'↦□".
    destruct (decide (h = h')) as [<-|NEQ].
    { (* Equal, CAS success *)
      iApply (SCMem_cas_loc_fun_spec_gen with "[$Mem $s↦ h↦□ h'↦□] [-]"); [lia|solve_ndisj| |].
      { des_ifs.
        iDestruct "h↦□" as (??) "[h↦□ _]".
        iSplit; iExists _; iFrame "h↦□".
      }
      iClear "h↦□ h'↦□".
      iIntros (b) "POST".
      iDestruct "POST" as (u) "(%EQ & s↦ & _ & _)".
      des_ifs. destruct EQ as [-> ->].

      (* Update logical stack state. *)
      iMod "AU" as (?) "[γs' Commit]".
      red_tl_all.
      iDestruct (ghost_var_agree with "γs γs'") as %<-.
      iMod (ghost_var_update_halves with "γs γs'") as "[γs γs']".

      iMod ("Commit" $! tt with "γs'") as "Q".

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
        iClear "Mem IsT n.n↦ n.d↦". clear.
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

      iDestruct (Inv_fold with "[s↦] γs Phys LInv") as "Inv".
      { unfold to_val. iFrame. }
      iMod ("Close" with "Inv") as "_". rred2r.

      iApply wpsim_tauR. rred2r.

      iApply (wpsim_yieldR with "[$Y $Duty]"); [lia|].
      iIntros "Duty _". rred2r. iApply wpsim_tauR. rred2r.
      iApply "Post". iFrame.
    }
    (* Different, CAS fail *)
    iApply (SCMem_cas_loc_fun_spec_gen with "[$Mem $s↦ h↦□ h'↦□] [-]"); [lia|solve_ndisj| |].
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
    iDestruct (Inv_fold with "s↦ γs Phys LInv") as "Inv".
    iMod ("Close" with "Inv") as "_". rred2r.

    iApply wpsim_tauR. rred2r. iApply wpsim_tauR.

    (* Do Induction *)
    iMod (pcs_drop 1 98 with "Pcs") as "Pcs"; [lia..|].
    iMod ("IH" with "Ob_k n.n↦ Post Duty Pcs AU n.d↦ Ob_ks") as "IH".
    iApply "IH".
  Qed.

  Lemma Treiber_pop_spec
        {n} (Q : (option SCMem.val) → sProp (1+n)) tid :
    ∀ s k γs l a (ds : list (nat * nat * sProp n)),
    ⊢ [@ tid, n, ⊤ @]
          ⧼⟦(
            syn_tgt_interp_as n sndl (fun m => s_memory_black m) ∗
            (⤉ IsT n l a s k γs) ∗
            (⤉ Duty(tid) ds) ∗
            AU <{ ∃∃ St, ⤉ TStack n γs St }> @ n, (⊤∖↑treiberN), ∅
                <{ ∀∀ (_ : unit), ⤉ TStack n γs (tail St), COMM Q (hd_error St) }> ∗
            ◇[k](1,1) ∗
            ◇{List.map fst ds}(2+l,2+a)
            )%S, 1+n⟧⧽
            (OMod.close_itree Client (SCMem.mod gvs) (TreiberStack.pop s))
          ⧼rv, ⟦(
            Q rv ∗ (⤉ Duty(tid) ds) ∗
            match rv with
            | Some _ => emp
            | None => ◇[k](1,1)
            end
            )%S, 1+n⟧⧽
  .
  Proof.
    ii. iStartTriple. red_tl_all.
    unfold IsT,TStack. rewrite red_syn_tgt_interp_as. rewrite red_syn_atomic_update. red_tl. simpl.
    iIntros "(#Mem & IsT & Duty & AU & Ob_ks & PCS)".
    set POST := (POST in (POST -∗ _)%I).
    iIntros "Post".
    iDestruct "IsT" as (γl) "IsT".
    red_tl. rewrite red_syn_inv. iDestruct "IsT" as "#[Ob_kb IsT]".

    iMod (pcs_decr 1 (1+a) with "PCS") as "[Ys PCS]"; [lia|].
    iMod (pcs_decr 1 a with "PCS") as "[PCS CCS]"; [lia|].
    iMod (pcs_drop 1 102 with "Ys") as "Ys"; [lia..|].
    iMod (ccs_make_fine _ _ _ _ 2 with "[$Ob_kb $CCS]") as "CCS".

    iEval (unfold TreiberStack.pop). rred2r.

    iMod ((pcs_decr 101 1) with "Ys") as "[Ys Y]"; [lia|].
    iApply (wpsim_yieldR with "[$Duty $Y]"); [lia..|].
    iIntros "Duty _". rred2r.

    iApply wpsim_tauR. rred2r.

    iRevert "Post Duty Ys AU Ob_ks". iRevert "PCS".

    iMod (ccs_ind2 with "CCS [-]") as "Ind".
    2:{ iIntros "PCS". destruct l; last first.
        - iMod (pcs_drop 2 1 with "PCS") as "PCS"; [lia..|].
        iApply ("Ind" with "PCS").
        - iApply ("Ind" with "PCS").
    }

    iModIntro. iExists 0.
    set IH := (IH in (IH ==∗ _)%I).
    iIntros "IH !> PCS Post Duty Ys AU Ob_ks".
    iEval (rewrite TreiberStack.pop_loop_red). rred2r.

    iMod ((pcs_decr 100 1) with "Ys") as "[Ys Y]"; [lia|].
    iApply (wpsim_yieldR with "[$Duty $Y]"); [lia..|].
    iIntros "Duty _". rred2r.

    iInv "IsT" as "Inv" "Close". simpl.
    iDestruct (Inv_unfold with "Inv") as (h St m) "(s↦ & γs & Phys & LInv)".

    iApply (SCMem_load_fun_spec with "[$Mem $s↦] [-]"); [lia|solve_ndisj|].
    iIntros (?) "[%EQ s↦]".
    subst. rred2r. iApply wpsim_tauR. rred2r.
    iMod ((pcs_decr 99 1) with "Ys") as "[Ys Y]"; [lia|].

    destruct (decide (h = Null)) as [->|NEQ].
    { (* Head is null, so stack is empty. *)
      simpl in *.
      iDestruct (phys_list_unfold with "Phys") as "Phys".
      des_ifs. iClear "Phys".
      iMod "AU" as (?) "[γs' Commit]". red_tl_all.
      iDestruct (ghost_var_agree with "γs γs'") as %<-.
      iMod ("Commit" $! tt with "γs'") as "Q".
      iDestruct (Inv_fold with "[s↦] γs [] LInv") as "Inv".
      { unfold to_val. iFrame. }
      { iApply phys_list_fold. done. }
      iMod ("Close" with "Inv") as "_". rred2r.

      iApply (wpsim_yieldR with "[$Duty $Y]"); [lia..|].
      iIntros "Duty _". rred2r.

      iApply (SCMem_compare_fun_spec with "[Mem] [-]"); [|solve_ndisj| |].
      2:{ iApply (tgt_interp_as_equiv with "Mem"). clear.
          iStartProof. iIntros (m). simpl. red_tl_all. iSplit.
          - iIntros "$". iPureIntro. done.
          - iIntros "[$ _]".
        }
      1: lia.
      iIntros (?) "%EQ". destruct EQ as [EQ _].
      specialize (EQ ltac:(auto)) as ->. rred2r.

      iApply (wpsim_tauR). rred2r.
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
    { rewrite big_sepM_insert; last first.
      { apply not_elem_of_dom. apply is_fresh. }
      iFrame. case_decide; done.
    }

    iDestruct (Inv_fold with "s↦ γs Phys LInv") as "Inv".
    iMod ("Close" with "Inv") as "_". move: i=>i. clear dependent St m.

    iApply (wpsim_yieldR with "[$Duty $Y]"); [lia..|].
    iIntros "Duty _". rred2r.

    iApply (SCMem_compare_loc_null_fun_spec with "[$Mem $h.n↦□] [-]"); [lia|solve_ndisj|].
    iIntros (?) "[_ %EQ]". subst. rred2r.

    iApply wpsim_tauR. rred2r.

    iMod (pcs_decr 98 1 with "Ys") as "[Ys Y]"; [lia|].
    iApply (wpsim_yieldR with "[$Duty $Y]"); [lia..|].
    iIntros "Duty _". rred2r.

    iApply (SCMem_load_fun_spec with "[$Mem $h.n↦□] [-]"); [lia|solve_ndisj|].
    iIntros (?) "[%EQ _]". subst. rred2r.

    iApply (wpsim_tauR). rred2r.

    iMod (pcs_decr 97 1 with "Ys") as "[Ys Y]"; [lia|].
    iApply (wpsim_yieldR with "[$Duty $Y]"); [lia..|].
    iIntros "Duty _". rred2r.

    iInv "IsT" as "Inv" "Close". simpl.
    iDestruct (Inv_unfold with "Inv") as (h' L m) "(s↦ & γs & Phys & LInv)".
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
      iApply (SCMem_cas_loc_fun_spec_gen with "[$Mem $s↦] [-]"); [lia|solve_ndisj| |].
      { des_ifs. iSplit; iExists _; iFrame "h.n↦□". }
      iIntros (b) "POST".

      iDestruct "POST" as (u) "(%EQ & s↦ & _ & _)".
      des_ifs. destruct EQ as [-> ->].

      (* Update logical & physical stack state. *)
      iMod "AU" as (?) "[γs' Commit]". red_tl_all.
      iDestruct (ghost_var_agree with "γs γs'") as %<-.
      iMod (ghost_var_update_halves with "γs γs'") as "[γs γs']".
      iMod ("Commit" $! tt with "γs'") as "Q".
      rred2r. iApply wpsim_tauR. rred2r.

      (* Update liveness invariant *)
      iDestruct (LInv_unfold with "LInv") as "[GMap LivC]".

      iDestruct (ghost_map_lookup with "GMap i↪") as "%Lookup_i".
      iMod (ghost_map_delete with "GMap i↪") as "GMap".

      (** Create a big_opM of ◇[k](0,1). *)
      iMod (pc_drop _ 0 1 ltac:(auto) (size (delete i m)) with "Ob_ks") as "Ob_ks"; [lia|].
      iAssert ([∗ map] _ ∈ delete i m, ◇[k](0,1))%I with "[Ob_ks]" as "Ob_ks".
      { set (m' := delete i m). move: m' => m'.
        iClear "Mem IsT h.n↦□ h.d↦□ Ob_kb". clear.
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

      iDestruct (Inv_fold with "s↦ γs Phys LInv") as "Inv".
      iMod ("Close" with "Inv") as "_". rred2r.

      iMod (pcs_decr 96 1 with "Ys") as "[Ys Y]"; [lia|].
      iApply (wpsim_yieldR with "[$Y $Duty]"); [lia|].
      iIntros "Duty _". rred2r.

      iApply (SCMem_load_fun_spec with "[$Mem $h.d↦□] [-]"); [lia|solve_ndisj|].
      iIntros (?) "[%EQ _]". subst. rred2r.

      iApply wpsim_tauR. rred2r.

      iApply "Post". red_tl. iFrame.
    }
    (* Different, CAS fail *)
    iApply (SCMem_cas_loc_fun_spec_gen with "[$Mem $s↦ h.n↦□ h'↦□] [-]"); [lia|solve_ndisj| |].
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
    iDestruct (Inv_fold with "s↦ γs Phys LInv") as "Inv".
    iMod ("Close" with "Inv") as "_". rred2r.

    iApply wpsim_tauR. rred2r.

    iApply wpsim_tauR.

    (* Do Induction *)
    iMod (pcs_drop 1 101 with "[$PCS]") as "PCS"; [lia..|].
    iMod ("IH" with "Ob_k Post Duty PCS AU Ob_ks") as "IH".
    iApply "IH".
Qed.

End SPEC.

Global Opaque IsT TStack TreiberStack.pop TreiberStack.push.
