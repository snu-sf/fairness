From sflib Require Import sflib.
Require Import Coq.Classes.RelationClasses Lia Program.
From iris Require Import bi.big_op.
From Fairness Require Import pind ITreeLib Red TRed IRed2 WFLibLarge.
From Fairness Require Import FairBeh Mod Linking.
From Fairness Require Import treiber.Code.
From Fairness Require Import PCM IPM IPropAux.
From Fairness Require Import IndexedInvariants OpticsInterp SimWeakest.
From Fairness Require Export TemporalLogic SCMemSpec ghost_var ghost_map.

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
  Context {HasGhostMap : @GRA.inG (ghost_mapURA nat maybe_null_ptr) Γ}.
  Context {HasGhostVar : @GRA.inG (ghost_varURA (list SCMem.val)) Γ}.

  Local Ltac red_tl_all := red_tl_every; red_tl_memra; red_tl_ghost_map; red_tl_ghost_var.

  Local Definition to_val (mnp : maybe_null_ptr) : SCMem.val :=
    match mnp with
    | Null => SCMem.val_null
    | Ptr p => SCMem.val_ptr p
    end
  .

  Definition TStack n γs St : sProp n :=
    syn_ghost_var γs (1/2) St.

  Local Fixpoint phys_list n (l : maybe_null_ptr) (St : list SCMem.val) : sProp n := (
    match St,l with
    | [],Null => emp
    | v::tSt,Ptr p => ∃ (r : τ{maybe_null_ptr}),((to_val l) ↦∗□ [(to_val r); v]) ∗ (phys_list n r tSt)
    | _,_ => ⌜False⌝
    end
  )%S.

  Local Definition LInv (n k γl : nat) (h : maybe_null_ptr) (m : gmap nat maybe_null_ptr) : sProp n  := (
    syn_ghost_map_auth γl 1 m ∗
    [∗ n, maybe_null_ptr map] i ↦ p ∈ m, (
      if (decide (h=p)) then
        emp
      else
        ◇[k](0,1)
    )
  )%S.

  Local Definition Inv (n : nat) (s : SCMem.val) (k γs γl : nat) : sProp n := (
    ∃ (h : τ{maybe_null_ptr}) (St : τ{list SCMem.val}) (m : τ{gmap nat maybe_null_ptr,n}),
      s ↦ (to_val h) ∗ syn_ghost_var γs (1/2) (St : list SCMem.val) ∗
      phys_list n h St ∗ LInv n k γl h m
  )%S.

  Definition IsT n l a s k γs : sProp n := (
    ∃ (γl : τ{nat,n}), ◆[k,l,a] ∗ syn_inv n treiberN (Inv n s k γs γl)
  )%S.

  Global Instance IsT_persistent n l a s k γs :
    Persistent ⟦ IsT n l a s k γs, n⟧.
  Proof. unfold Persistent,IsT. red_tl.
    iIntros "[%γl IsT]". iExists γl. red_tl. rewrite red_syn_inv.
    iDestruct "IsT" as "#$".
  Qed.

  Local Lemma Inv_unfold n s k γs γl :
    ⟦ Inv n s k γs γl, n ⟧ -∗
    (∃ (h : τ{maybe_null_ptr,n}) (L : τ{list SCMem.val,n}) (m : τ{gmap nat maybe_null_ptr,n}),
      (s ↦ (to_val h)) ∗ ghost_var γs (1/2) (L : list SCMem.val) ∗
      ⟦ (phys_list n h L), n⟧ ∗ ⟦ LInv n k γl h m, n⟧).
  Proof.
    unfold Inv. iIntros "Inv".
    repeat (red_tl; iDestruct "Inv" as "[% Inv]").
    red_tl_all. eauto.
  Qed.

  Local Lemma Inv_fold n s k γs γl h L m :
    s ↦ (to_val h) -∗ ghost_var γs (1/2) L -∗
    ⟦ phys_list n h L, n⟧ -∗ ⟦ LInv n k γl h m, n⟧
    -∗ ⟦ Inv n s k γs γl, n ⟧.
  Proof.
    unfold Inv. iIntros "? ? ? ?".
    repeat (red_tl; iExists _).
    red_tl_all. iFrame.
  Qed.

  Local Lemma LInv_unfold n k γl h m :
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
    ii. des_ifs; red_tl_all.
  Qed.

  Local Lemma LInv_fold n k γl h m :
    ghost_map_auth γl 1 m -∗
    ([∗ map] a ∈ m,
      if decide (h = a) then
          emp
        else
          ◇[k](0, 1)
        )
    -∗ ⟦ LInv n k γl h m, n ⟧.
  Proof.
    unfold LInv. iIntros "? H". red_tl_all.
    rewrite red_syn_big_sepM. iFrame.
    iApply (big_sepM_mono with "H").
    ii. des_ifs; red_tl_all.
  Qed.

  Local Lemma phys_list_unfold n l L :
    ⟦ phys_list n l L, n ⟧ -∗
    match L,l with
    | [],Null => emp
    | v::tL,Ptr p => ∃ r, (to_val l) ↦∗□ [to_val r; v] ∗ ⟦phys_list n r tL,n⟧
    | _,_ => False
    end.
  Proof.
    iIntros "H". des_ifs. destruct p. simpl.
    red_tl_all; iDestruct "H" as (r) "H".
    red_tl_all; iDestruct "H" as "[(l.n↦ & l.d↦ & _) Phys]".
    iExists _. iFrame.
  Qed.

  Local Lemma phys_list_fold n l L :
    (match L,l with
    | [],Null => emp
    | v::tL,Ptr p => ∃ r, (to_val l) ↦∗□ [to_val r; v] ∗ ⟦phys_list n r tL,n⟧
    | _,_ => ⌜False⌝
    end) -∗
    ⟦ phys_list n l L, n ⟧.
  Proof.
    iIntros "H". des_ifs. destruct p. simpl.
    red_tl_all; iDestruct "H" as (r) "[(l.n↦ & l.d↦ & _) Phys]".
    red_tl_all. iExists r.
    red_tl_all. iFrame.
  Qed.

  Local Lemma phys_list_get_head n l L :
    ⟦ phys_list n l L, n ⟧ -∗
    □ if decide (l = Null) then
        emp
      else ∃ r h, (to_val l) ↦∗□ [to_val r; h]
    .
  Proof.
    iIntros "H". iDestruct (phys_list_unfold with "H") as "H". des_ifs. iDestruct "H" as (r) "[#H _]".
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

  Lemma Treiber_push_spec {n} tid :
    ∀ s k γs val l a (ds : list (nat * nat * sProp n)),
    ⊢ ⟦(
      syn_tgt_interp_as n sndl (fun m => s_memory_black m) ∗
      (⤉ IsT n l a s k γs) ∗
      (⤉ Duty(tid) ds) ∗
      ◇[k](1,1) ∗
      ◇{List.map fst ds}(2+l, 2+a)
      )%S,1+n⟧ -∗
      <<{ ∀∀ St, ⟦TStack n γs St,n⟧ }>>
        (OMod.close_itree Client (SCMem.mod gvs) (TreiberStack.push (s,val)))
        @
        tid, n, ↑treiberN
      <<{
        ∃∃ (_ : unit), ⟦TStack n γs (val::St),n⟧ | (_ : unit), RET tt ; Duty(tid) ds
      }>>.
  Proof.
    ii.
    red_tl. unfold IsT. rewrite red_syn_tgt_interp_as. red_tl.
    iIntros "(#Mem & IsT & Duty & Ob_ks & PCS)".
    iDestruct "IsT" as (γl) "IsT"; red_tl. rewrite red_syn_inv.
    iDestruct "IsT" as "#[Ob_kb IsT]".
    iIntros (? ? ? ? ?).
    set AtU := (AtU in (AtU -∗_)%I).
    iIntros "AU".

    rred2r.

    iMod (pcs_decr 1 (1+a) with "PCS") as "[Ys PCS]"; [lia|].
    iMod (pcs_decr 1 a with "PCS") as "[PCS CCS]"; [lia|].
    iMod (pcs_drop 1 100 with "Ys") as "Ys"; [lia..|].
    iMod (pcs_decr 1 99 with "Ys") as "[Y Ys]"; [lia|].

    iApply (wpsim_yieldR with "[$Duty $Y]"); [lia|].
    iIntros "Duty _". rred2r.

    iMod (ccs_make_fine _ _ _ _ 2 with "[$Ob_kb $CCS]") as "CCS".

    iApply (SCMem_alloc_fun_spec with "[$Mem] [-]"); [lia|set_solver|].
    iIntros (node) "(n.n↦ & n.d↦ & _)".
    rred2r. iApply wpsim_tauR. rred2r.

    iMod (pcs_decr 98 1 with "Ys") as "[Ys Y]"; [lia|].
    iApply (wpsim_yieldR with "[$Y $Duty]"); [lia|].
    iIntros "Duty _". rred2r.

    iApply (SCMem_store_fun_spec with "[$Mem $n.d↦] [-]"); [lia|set_solver|].
    iIntros (?) "n.d↦". rred2r. iApply wpsim_tauR. rred2r.

    move: (SCMem.val_nat 0) => next.

    iRevert "n.n↦ Duty Ys AU n.d↦ Ob_ks". iRevert (next). iRevert "PCS".

    iMod (ccs_ind2 with "CCS [-]") as "Ind".
    2:{ iIntros "PCS". destruct l; last first.
        - iMod (pcs_drop 2 1 with "PCS") as "PCS"; [lia..|].
          iApply ("Ind" with "PCS").
        - iApply ("Ind" with "PCS").
    }

    iModIntro. iExists 0.
    set IH := (IH in (IH ==∗ _)%I).
    iIntros "IH !> Pcs %next n.n↦ Duty Ys AU n.d↦ Ob_ks".
    rewrite TreiberStack.push_loop_red.
    rred2r.

    iMod (pcs_decr 97 1 with "Ys") as "[Ys Y]"; [lia|].

    iApply (wpsim_yieldR with "[$Y $Duty]"); [lia|].
    iIntros "Duty _". rred2r.

    iInv "IsT" as "Inv" "Close". simpl.
    iDestruct (Inv_unfold with "Inv") as (h L m) "(s↦ & γs & Phys & LInv)".
    iApply (SCMem_load_fun_spec with "[$Mem $s↦] [-]"); [lia|solve_ndisj|].
    iIntros (load_v) "[%EQ s↦]". subst load_v.
    (* Get proof that h is live for future use. *)
    iDestruct (phys_list_get_head with "Phys") as "#h↦□".

    (* Register this thread to the current waiting list for h. *)
    iDestruct (LInv_unfold with "LInv") as "[GMap LivC]".
    set (i := fresh (dom m)).
    iMod (ghost_map_insert i h with "GMap") as "[GMap i↪]".
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

    iMod (pcs_decr 96 1 with "Ys") as "[Ys Y]"; [lia|].
    iApply (wpsim_yieldR with "[$Y $Duty]"); [lia|].
    iIntros "Duty _". rred2r.

    iApply (SCMem_store_fun_spec with "[$Mem $n.n↦] [-]"); [lia|solve_ndisj|].
    iIntros (?) "n.n↦". rred2r. iApply wpsim_tauR. rred2r.

    iMod (pcs_decr 95 1 with "Ys") as "[Ys Y]"; [lia|].
    iApply (wpsim_yieldR with "[$Y $Duty]"); [lia|].
    iIntros "Duty _". rred2r.

    iMod (pcs_decr 94 1 with "Ys") as "[Ys Y]"; [lia|].

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
      rred2r. iApply wpsim_tauR. rred2r.

      iMod "AU" as (L') "[γs' Commit]".
      iEval (unfold TStack; red_tl_all) in "γs'".
      iDestruct (ghost_var_agree with "γs γs'") as %<-.
      iMod (ghost_var_update_halves with "γs γs'") as "[γs γs']".

      (* Update logical stack state. *)
      iMod ("Commit" $! tt with "[γs']") as "Post".
      { iEval (unfold TStack; red_tl_all). iFrame. }

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

      iApply (wpsim_yieldR with "[$Y $Duty]"); [lia|].
      iIntros "Duty _". rred2r. iApply wpsim_tauR. rred2r.
      iApply ("Post" $! tt with "Duty").
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
    des_ifs; destruct EQ as [-> ->].
    { exfalso. clear - e NEQ. unfold to_val in e. des_ifs. }

    (* Update ◇[k](0,1) to use for induction *)
    iDestruct (LInv_unfold with "LInv") as "[GMap LivC]".

    iDestruct (ghost_map_lookup with "GMap i↪") as "%Lookup_i".
    iMod (ghost_map_delete with "GMap i↪") as "GMap".

    iDestruct (big_sepM_delete with "LivC") as "[Ob_k LivC]"; [apply Lookup_i|].
    case_decide; [done|].

    iDestruct (LInv_fold with "GMap LivC") as "LInv".
    iDestruct (Inv_fold with "s↦ γs Phys LInv") as "Inv".
    iMod ("Close" with "Inv") as "_". rred2r.

    iApply wpsim_tauR. rred2r. iApply wpsim_tauR.

    (* Do Induction *)
    iMod (pcs_drop 1 98 with "Pcs") as "Pcs"; [lia..|].
    iMod ("IH" with "Ob_k n.n↦ Duty Pcs AU n.d↦ Ob_ks") as "IH".
    iApply "IH".
  Qed.

  Lemma Treiber_pop_spec {n} tid :
    ∀ s k γs l a (ds : list (nat * nat * sProp n)),
    ⊢ ⟦(
      syn_tgt_interp_as n sndl (fun m => s_memory_black m) ∗
      (⤉ IsT n l a s k γs) ∗
      (⤉ Duty(tid) ds) ∗
      ◇[k](1,1) ∗
      ◇{List.map fst ds}(2+l,2+a)
    )%S,1+n⟧ -∗
      <<{ ∀∀ St, ⟦TStack n γs St,n⟧ }>>
        (OMod.close_itree Client (SCMem.mod gvs) (TreiberStack.pop s))
        @
        tid, n, ↑treiberN
      <<{
        ∃∃ (_ : unit), ⟦TStack n γs (tail St),n⟧
        | (_ : unit), RET (hd_error St) ;
        Duty(tid) ds ∗
        match (hd_error St) with
        | Some _ => emp
        | None => ◇[k](1,1)
        end
      }>>.
  Proof.
    ii.
    red_tl. unfold IsT. rewrite red_syn_tgt_interp_as. red_tl. simpl.
    iIntros "(#Mem & IsT & Duty & Ob_ks & PCS)".
    iDestruct "IsT" as (γl) "IsT"; red_tl. rewrite red_syn_inv.
    iDestruct "IsT" as "#[Ob_kb IsT]".
    iIntros (? ? ? ? ?).
    set AtUpd := (AtUpd in (AtUpd -∗ _)%I).
    iIntros "AU".

    iMod (pcs_decr 1 (1+a) with "PCS") as "[Ys PCS]"; [lia|].
    iMod (pcs_decr 1 a with "PCS") as "[PCS CCS]"; [lia|].
    iMod (pcs_drop 1 102 with "Ys") as "Ys"; [lia..|].
    iMod (ccs_make_fine _ _ _ _ 2 with "[$Ob_kb $CCS]") as "CCS".

    rred2r.

    iMod (pcs_decr 101 1 with "Ys") as "[Ys Y]"; [lia|].
    iApply (wpsim_yieldR with "[$Duty $Y]"); [lia..|].
    iIntros "Duty _". rred2r.

    iApply wpsim_tauR. rred2r.

    iRevert "Duty Ys AU Ob_ks". iRevert "PCS".

    iMod (ccs_ind2 with "CCS [-]") as "Ind".
    2:{ iIntros "PCS". destruct l; last first.
        - iMod (pcs_drop 2 with "PCS") as "PCS"; [lia..|].
          iApply ("Ind" with "PCS").
        - iApply ("Ind" with "PCS").
    }

    iModIntro. iExists 0.
    set IH := (IH in (IH ==∗ _)%I).
    iIntros "IH !> PCS Duty Ys AU Ob_ks".
    rewrite TreiberStack.pop_loop_red.
    rred2r.

    iMod (pcs_decr 100 1 with "Ys") as "[Ys Y]"; [lia|].
    iApply (wpsim_yieldR with "[$Duty $Y]"); [lia..|].
    iIntros "Duty _". rred2r.

    iInv "IsT" as "Inv" "Close". simpl.
    iDestruct (Inv_unfold with "Inv") as (h St m) "(s↦ & γs & Phys & LInv)".

    iApply (SCMem_load_fun_spec with "[$Mem $s↦] [-]"); [lia|solve_ndisj|].
    iIntros (load_v) "[%EQ s↦]".
    subst load_v. rred2r. iApply wpsim_tauR. rred2r.
    iMod (pcs_decr 99 1 with "Ys") as "[Ys Y]"; [lia|].

    destruct (decide (h = Null)) as [->|NEQ].
    { (* Head is null, so stack is empty. *)
      iDestruct (phys_list_unfold with "Phys") as "Phys".
      des_ifs.
      iMod "AU" as (?) "[γs' Commit]".
      iEval (unfold TStack; red_tl_all) in "γs'".
      iDestruct (ghost_var_agree with "γs γs'") as %<-.

      iMod ("Commit" $! tt with "[γs']") as "Post".
      { iEval (unfold TStack; red_tl_all). by iFrame. }
      iDestruct (Inv_fold with "s↦ γs [] LInv") as "Inv".
      { by iApply phys_list_fold. }
      iMod ("Close" with "Inv") as "_". rred2r.

      iApply (wpsim_yieldR with "[$Duty $Y]"); [lia..|].
      iIntros "Duty _". rred2r.

      iApply (SCMem_compare_fun_spec with "[Mem] [-]"); [|solve_ndisj| |].
      2:{ iApply (tgt_interp_as_equiv with "Mem"). clear.
          move=> m /=. red_tl. rewrite is_Some_alt right_id //.
        }
      1: lia.
      iIntros (? [EQ _]).
      specialize (EQ ltac:(auto)) as ->. rred2r.

      iApply wpsim_tauR. rred2r.
      iApply ("Post" $! tt). iFrame.
    }

    iDestruct (phys_list_get_head with "Phys") as "#h↦□".
    case_decide; [done|].
    iDestruct "h↦□" as (r d) "[h.n↦□ [h.d↦□ _]]".
    (* Update Linv by adding myself to the ghost map, in the same way as push *)

    iDestruct (LInv_unfold with "LInv") as "[GMap LivC]".
    set (i := fresh (dom m)).
    iMod (ghost_map_insert i h with "GMap") as "[GMap i↪]".
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

    iApply wpsim_tauR. rred2r.

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
      destruct L as [|v tL], h as [|h]; try done.
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

      rred2r. iApply wpsim_tauR. rred2r.

      iEval (unfold atomic_update) in "AU".
      iMod "AU" as (L') "[γs' Commit]".
      iEval (unfold TStack; red_tl_all) in "γs'".
      iDestruct (ghost_var_agree with "γs γs'") as %<-.
      iMod (ghost_var_update_halves with "γs γs'") as "[γs γs']".
      iMod ("Commit" $! tt with "[γs']") as "Post".
      { iEval (unfold TStack; red_tl_all). by iFrame. }

      (* Update liveness invariant *)
      iDestruct (LInv_unfold with "LInv") as "[GMap LivC]".

      iDestruct (ghost_map_lookup with "GMap i↪") as "%Lookup_i".
      iMod (ghost_map_delete with "GMap i↪") as "GMap".

      (** Create a big_opM of ◇[k](0,1). *)
      iMod (pc_drop _ 0 1 ltac:(auto) (size (delete i m)) with "Ob_ks") as "Ob_ks"; [lia|].
      iAssert ([∗ map] _ ∈ delete i m, ◇[k](0,1))%I with "[Ob_ks]" as "Ob_ks".
      { move: (delete i m) => m'.
        iClear "Mem IsT h.n↦□ h.d↦□ Ob_kb". clear.
        simpl in *.
        iInduction (m') as [|id op m NotIN] "IH" using map_ind.
        { done. }
        rewrite big_sepM_insert // map_size_insert_None //.
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

      iApply ("Post" $! tt). iFrame.
    }
    (* Different, CAS fail *)
    iApply (SCMem_cas_loc_fun_spec_gen with "[$Mem $s↦ h.n↦□ h'↦□] [-]"); [lia|solve_ndisj| |].
    { unfold to_val. des_ifs.
      2,4: iDestruct "h'↦□" as (??) "[h'↦□ _]".
      all: iSplit; try done; iExists _; iFrame "#".
    }
    iClear "h'↦□".
    iIntros (b) "POST". iDestruct "POST" as (u) "(%EQ & s↦ & _ & _)".
    des_ifs; destruct EQ as [-> ->].
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
    iMod (pcs_drop 1 101 with "PCS") as "PCS"; [lia..|].
    iMod ("IH" with "Ob_k Duty PCS AU Ob_ks") as "IH".
    iApply "IH".
Qed.

End SPEC.

Global Opaque TStack IsT TreiberStack.pop TreiberStack.push.
