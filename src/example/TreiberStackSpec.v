From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From iris Require Import bi.big_op.
From Fairness Require Import pind Axioms ITreeLib Red TRed IRed2 WFLibLarge.
From Fairness Require Import FairBeh Mod Linking.
From Fairness Require Import TreiberStack.
From Fairness Require Import PCM IProp IPM IPropAux.
From Fairness Require Import IndexedInvariants OpticsInterp SimWeakest.
From Fairness Require Import TemporalLogic SCMemSpec AuthExclsRA ghost_map ExclsRA.

Record maybe_null_ptr := {
  ptr :> SCMem.val;
  ptr_mabye_null : ptr = SCMem.val_null \/ (∃ (p : SCMem.pointer), ptr = SCMem.val_ptr p);
}.
Global Instance maybe_null_ptr_eq_dec : EqDecision maybe_null_ptr.
Proof.
  intros [p1 Pp1] [p2 Pp2].
  unfold Decision. destruct (decide (p1 = p2)) as [->|NEQ].
  - left. f_equal. apply proof_irrelevance.
  - right. intros H. apply NEQ. injection H. done.
Qed.

Definition to_mnp_null : maybe_null_ptr := {| ptr := SCMem.val_null; ptr_mabye_null := or_introl eq_refl |}.

Definition to_mnp_ptr ptr
  (IsPtr : (∃ (p : SCMem.pointer), ptr = SCMem.val_ptr p)) :=
  {| ptr := ptr; ptr_mabye_null := or_intror IsPtr |}.

Section SPEC.

  Context {src_state : Type}.
  Context {src_ident : Type}.
  Context {Client : Mod.t}.
  Context {gvs : list nat}.
  Context (treiberN : namespace) `{DISJ: (↑N_state_tgt :coPset) ## (↑treiberN : coPset)}.
  Notation tgt_state := (OMod.closed_state Client (SCMem.mod gvs)).
  Notation tgt_ident := (OMod.closed_ident Client (SCMem.mod gvs)).

  Local Instance STT : StateTypes := Build_StateTypes src_state tgt_state src_ident tgt_ident.

  Context `{sub : @SRA.subG Γ Σ}.
  Context {TLRASs : TLRAs_small STT Γ}.
  Context {TLRAS : TLRAs STT Γ Σ}.

  Context {HasMEMRA: @GRA.inG memRA Γ}.
  Context {HasAuthExcl : @GRA.inG (AuthExcls.t (list SCMem.val)) Γ}.
  Context {HasExcl : @GRA.inG (Excls.t unit) Γ}.
  Context {HasGhostMap : @GRA.inG (ghost_mapURA nat maybe_null_ptr) Γ}.

  Ltac red_tl_all := red_tl_every; red_tl_memra; red_tl_authexcls; red_tl_ghost_map_ura.

  Definition to_val (mnp : maybe_null_ptr) : SCMem.val :=
    ptr mnp.

  Fixpoint phys_list n (l : maybe_null_ptr) (L : list SCMem.val) : sProp n := (
    match L with
    | [] => ⌜to_val l = SCMem.val_null⌝
    | v::tL => ∃ (p : τ{SCMem.pointer}) (r : τ{maybe_null_ptr}), ⌜to_val l = SCMem.val_ptr p⌝ ∗ (l ↦∗□ [(to_val r); v]) ∗ (phys_list n r tL)
    end
  )%S.

  Definition LInv (n k γs : nat) (h : maybe_null_ptr) (m : gmap nat maybe_null_ptr) : sProp n  := (
    s_ghost_map_auth γs 1 m ∗
    [∗ n, maybe_null_ptr map] i ↦ p ∈ m, (
      if (decide (h=p)) then
        emp
      else
        ◇[k](0,1)
    )
  )%S.

  Definition Inv (n : nat) (s : SCMem.val) (k γs : nat) : sProp n := (
    ∃ (h : τ{maybe_null_ptr}) (L : τ{list SCMem.val}) (m : τ{gmap nat maybe_null_ptr,n}),
      s ↦ (to_val h) ∗ ● γs (L : list SCMem.val) ∗
      phys_list n h L ∗ LInv n k γs h m
  )%S.

  Definition IsT n s k γs : sProp n := (
    syn_inv n treiberN (Inv n s k γs)
  )%S.

  Global Instance IsT_persistent n s k γs :
    Persistent (⟦ IsT n s k γs, n⟧).
  Proof. unfold Persistent,IsT. rewrite red_syn_inv. by iIntros "#?". Qed.

  (* Lemma isSpinlock_unfold n x γx γe k L :
    (⟦isSpinlock n x γx γe k L, n⟧) -∗ (◆[k, L] ∗ inv n N_Spinlock (spinlockInv n x γx γe)).
  Proof.
    iEval (unfold isSpinlock; red_tl). iIntros "[LO INV]". eauto.
  Qed. *)

  Lemma Inv_unfold n s k γs :
    (⟦ Inv n s k γs, n ⟧) -∗
    (∃ (h : τ{maybe_null_ptr,n}) (L : τ{list SCMem.val,n}) (m : τ{gmap nat maybe_null_ptr,n}),
      (s ↦ (to_val h)) ∗ (● γs (L : list SCMem.val)) ∗
      ⟦ (phys_list n h L), n⟧ ∗ ⟦ LInv n k γs h m, n⟧).
  Proof.
    unfold Inv. iIntros "Inv".
    repeat (red_tl; iDestruct "Inv" as "[% Inv]").
    red_tl_all. eauto.
  Qed.

  Lemma Inv_fold n s k γs h L m :
    (s ↦ (to_val h)) -∗ (● γs (L : list SCMem.val)) -∗
    ⟦ (phys_list n h L), n⟧ -∗ ⟦ LInv n k γs h m, n⟧
    -∗ (⟦ Inv n s k γs, n ⟧).
  Proof.
    unfold Inv. iIntros "? ? ? ?".
    repeat (red_tl; iExists _).
    red_tl_all. iFrame.
  Qed.

  Lemma LInv_unfold n k γs h m :
    (⟦ LInv n k γs h m, n ⟧) -∗
    (ghost_map_auth γs 1 m ∗
    [∗ map] a ∈ m,
      ⟦(if decide (h = a) then
          emp
        else
          ◇[k](0, 1)
        )%S,n ⟧).
  Proof.
    unfold LInv. iIntros "H". red_tl_all.
    rewrite red_syn_big_sepM. done.
  Qed.

  Lemma LInv_fold n k γs h m :
    ghost_map_auth γs 1 m -∗
    ([∗ map] a ∈ m,
      ⟦(if decide (h = a) then
          emp
        else
          ◇[k](0, 1)
        )%S,n ⟧)
    -∗ (⟦ LInv n k γs h m, n ⟧).
  Proof.
    unfold LInv. iIntros "? ?". red_tl_all.
    rewrite red_syn_big_sepM. iFrame.
  Qed.

  Lemma phys_list_unfold n l L :
    (⟦ phys_list n l L, n ⟧) -∗
    match L with
    | [] => ⌜to_val l = SCMem.val_null⌝
    | v::tL => ∃ (p : τ{SCMem.pointer,n}) (r : τ{maybe_null_ptr,n}), ⌜to_val l = SCMem.val_ptr p⌝ ∗ (l ↦∗□ [(to_val r); v]) ∗ (⟦phys_list n r tL,n⟧)
    end.
  Proof.
    iIntros "H". des_ifs. simpl.
    red_tl_all; iDestruct "H" as "[%x H]".
    red_tl_all; iDestruct "H" as "[%r H]".
    red_tl_all; iDestruct "H" as "[%EQ [(l.n↦ & l.d↦ & _) Phys]]".
    iExists _,_. iFrame. done.
  Qed.

  Lemma phys_list_fold n l L :
    (match L with
    | [] => ⌜to_val l = SCMem.val_null⌝
    | v::tL => ∃ (p : τ{SCMem.pointer,n}) (r : τ{maybe_null_ptr,n}), ⌜to_val l = SCMem.val_ptr p⌝ ∗ (l ↦∗□ [(to_val r); v]) ∗ (⟦phys_list n r tL,n⟧)
    end) -∗
    ⟦ phys_list n l L, n ⟧.
  Proof.
    iIntros "H". des_ifs. simpl.
    red_tl_all; iDestruct "H" as "[%x [%r [%EQ [(l.n↦ & l.d↦ & _) Phys]]]]".
    red_tl_all. iExists x. red_tl_all. iExists r.
    red_tl_all. iFrame. done.
  Qed.

  Lemma phys_list_get_head n l L :
    ⟦ phys_list n l L, n ⟧ -∗
    □ if (decide (to_val l = SCMem.val_null)) then
        emp
      else (∃ (r : τ{maybe_null_ptr,n}) (h : τ{SCMem.val,n}),
                 (l ↦∗□ [(to_val r); h]))
    .
  Proof.
    iIntros "H". iDestruct (phys_list_unfold with "H") as "H". destruct L; try done.
    all: case_decide; try done.
    - iDestruct "H" as %EQ. done.
    - iDestruct "H" as (p r) "[%EQ [#H _]]".
      red_tl_all. iExists r, v. iFrame "H".
  Qed.

  Lemma Treiber_push_spec {n} (Q : SCMem.val → sProp n) (P : sProp n) tid :
    ∀ s k γs val lv (ds : list (nat * nat * sProp n)),
    ⊢ [@ tid, n, ⊤ @]
          ⧼⟦(
            (syn_tgt_interp_as n sndl (fun m => s_memory_black m))
            ∗ (⤉ IsT n s k γs)
            ∗ (⤉ Duty(tid) ds)
            ∗ (⤉ P)
            ∗ (∀ (S : τ{list SCMem.val, 1+n}), (⤉ (● γs (S : list SCMem.val) ∗ P))
                  =|1+n|={⊤ ∖ ↑treiberN}=∗ (⤉ (● γs (val::S) ∗ Q val))
              )
            ∗ ◇[k](1,1)
            (* TODO: Proper ord level. *)
            ∗ ◇{List.map fst ds}(2 + lv, 1)
            )%S, 1+n⟧⧽
            (OMod.close_itree Client (SCMem.mod gvs) (TreiberStack.push (s,val)))
          ⧼_, ⟦(
            (⤉ (Q val ∗ Duty(tid) ds))
            )%S, 1+n⟧⧽
  .
  Proof.
    ii. iStartTriple. red_tl_all.
    unfold IsT. rewrite red_syn_tgt_interp_as. rewrite red_syn_inv. simpl.
    iIntros "(#Mem & #IsT & Duty & P & AU & Ob_k & Pcs) Post".
    red_tl_all.
    iEval (unfold TreiberStack.push).

    iMod (pcs_drop _ _ _ _ 1 (100 + 1) with "Pcs") as "Pcs"; [lia|].
    Unshelve. 2: lia.
    rred2r.

    iMod ((pcs_decr _ _ 100 1) with "Pcs") as "[Pcs Pcs_Y]"; [lia|].
    iApply (wpsim_yieldR with "[$Duty $Pcs_Y]"); [lia..|].
    iIntros "Duty _". rred2r.

    iApply (SCMem_alloc_fun_spec with "[$Mem] [-]"); [lia|set_solver|].
    iIntros (node) "(n.n↦ & n.d↦ & _)".
    rred2r. iApply wpsim_tauR. rred2r.

    iMod ((pcs_decr _ _ 99 1) with "Pcs") as "[Pcs Pcs_Y]"; [lia|].
    iApply (wpsim_yieldR with "[$Pcs_Y $Duty]"); [lia|].
    iIntros "Duty _".
    rred2r.

    iApply (SCMem_store_fun_spec with "[$Mem $n.d↦] [-]"); [lia|set_solver|].
    iIntros (?) "n.d↦". rred2r. iApply wpsim_tauR. rred2r.

    iEval (rewrite unfold_iter_eq). rred2r.

    iMod ((pcs_decr _ _ 98 1) with "Pcs") as "[Pcs Pcs_Y]"; [lia|].
    iApply (wpsim_yieldR with "[$Pcs_Y $Duty]"); [lia|].
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

    iMod ((pcs_decr _ _ 97 1) with "Pcs") as "[Pcs Pcs_Y]"; [lia|].
    iApply (wpsim_yieldR with "[$Pcs_Y $Duty]"); [lia|].
    iIntros "Duty _". rred2r.

    iApply (SCMem_store_fun_spec with "[$Mem $n.n↦] [-]"); [lia|solve_ndisj|].
    iIntros (?) "n.n↦". rred2r. iApply wpsim_tauR. rred2r.

    iMod ((pcs_decr _ _ 96 1) with "Pcs") as "[Pcs Pcs_Y]"; [lia|].
    iApply (wpsim_yieldR with "[$Pcs_Y $Duty]"); [lia|].
    iIntros "Duty _".
    rred2r.

    iMod ((pcs_decr _ _ 95 1) with "Pcs") as "[Pcs Pcs_Y]"; [lia|].

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
      iSpecialize ("AU" $! L).
      iEval (red_tl) in "AU".
      iEval (rewrite red_syn_fupd) in "AU".
      iEval (red_tl_all) in "AU".
      rred2r. iApply wpsim_tauR. rred2r.

      (* Update logical stack state. *)
      iMod ("AU" with "[$γs $P]") as "[γs Q]".

      (* Update physical stack state. *)
      iMod (SCMem.points_to_persist with "n.n↦") as "#n.n↦".
      iMod (SCMem.points_to_persist with "n.d↦") as "#n.d↦".
      iAssert (⌜∃ p : τ{SCMem.pointer,n}, node = SCMem.val_ptr p⌝)%I as %IsPtr.
      { destruct node; try done. iPureIntro. eauto. }
      iAssert (⟦ phys_list n (to_mnp_ptr node IsPtr) (val::L), n⟧)%I with "[Phys]" as "Phys".
      { iApply phys_list_fold. simpl. des. iExists _,_. iFrame "∗#". done. }

      (* Update liveness invariant *)
      iDestruct (LInv_unfold with "LInv") as "[GMap LivC]".

      iDestruct (ghost_map_lookup with "GMap i↪") as "%Lookup_i".
      iMod (ghost_map_delete with "GMap i↪") as "GMap".

      (** Create a big_opM of ◇[k](0,1). *)
      iMod (pc_drop _ 0 _ _ (size (delete i m)) with "Ob_k") as "Ob_k"; [lia|].
      Unshelve. 2: lia.
      iAssert ([∗ map] _ ∈ delete i m, ◇[k](0,1))%I with "[Ob_k]" as "Ob_k".
      { set (m' := delete i m). move: m' => m'.
        iClear "Mem IsT n.n↦ n.d↦". clear.
        simpl in *.
        iInduction (m') as [|id op m NotIN] "IH" using map_ind.
        { done. }
        rewrite big_sepM_insert; [|done].
        rewrite map_size_insert_None; [|done].
        iDestruct (pc_split _ _ 1 (size m) with "Ob_k") as "[$ Ob_k]".
        iApply ("IH" with "Ob_k").
      }

      (** Add it to the invariant. *)
      iDestruct (big_sepM_delete with "LivC") as "[_ LivC]"; [apply Lookup_i|].
      iDestruct (LInv_fold _ _ _ (to_mnp_ptr node IsPtr) with "GMap [LivC Ob_k]") as "LInv".
      { iDestruct (big_sepM_sep_2 with "LivC Ob_k") as "LivC".
        iApply (big_sepM_mono with "LivC").
        iIntros (i' p' Lookup_i') "[H C]". des_ifs.
      }

      iDestruct (Inv_fold with "[s↦] γs Phys LInv") as "Inv".
      { unfold to_val. iFrame. }
      iMod ("Close" with "Inv") as "_". rred2r.

      iApply (wpsim_yieldR with "[$Pcs_Y $Duty]"); [lia|].
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
    { exfalso. clear - e NEQ. unfold to_val in e.
      destruct h as [h Ph],h' as [h' Ph']. simpl in *. clarify.
      assert (Ph = Ph') as -> by apply proof_irrelevance. done.
    }

    (* Update liveness invariant *)
    iDestruct (LInv_unfold with "LInv") as "[GMap LivC]".

    iDestruct (ghost_map_lookup with "GMap i↪") as "%Lookup_i".
    iMod (ghost_map_delete with "GMap i↪") as "GMap".

    iDestruct (big_sepM_delete with "LivC") as "[iC LivC]"; [apply Lookup_i|].
    case_decide; [done|].
    red_tl. simpl.
    (* TODO: uhh... now what? actually set up induction and stuff. *)

    iDestruct (LInv_fold with "GMap LivC") as "LInv".
    iDestruct (Inv_fold with "s↦ γs Phys LInv") as "Inv".
    iMod ("Close" with "Inv") as "_". rred2r.

    iApply wpsim_tauR. rred2r. iApply wpsim_tauR.
  Admitted.
(*
∀ (S : τ{list SCMem.val}), (⤉ (● γs (S : list SCMem.val) ∗ P))
                  =|1+n|={E}=∗
                  (∃ (S' : τ{list SCMem.val}) (ov : τ{option SCMem.val}),
                    (⤉ (● γs (S' : list SCMem.val) ∗ Q (ov : option SCMem.val) ∗ ⌜ov = hd_error S⌝)))
*)
  Lemma Treiber_pop_spec
        {n} (Q : (option SCMem.val) → sProp n) (P : sProp n) tid :
    ∀ s k γs L (ds : list (nat * nat * sProp n)),
    ⊢ [@ tid, n, ⊤ @]
          ⧼⟦(
            (syn_tgt_interp_as n sndl (fun m => s_memory_black m))
            ∗ (⤉ IsT n s k γs)
            ∗ (⤉ Duty(tid) ds)
            ∗ (⤉ P)
            (* TODO: masks? *)
            ∗ (∀ (S : τ{list SCMem.val, 1+n}), (⤉ (● γs (S : list SCMem.val) ∗ P))
                  =|1+n|={⊤∖↑treiberN}=∗
                  match S with
                  | [] => (⤉ (● γs ([] : list SCMem.val) ∗ Q None))
                  | h::t => (⤉ (● γs t ∗ Q (Some h)))
                  end
              )
            (* TODO: Proper ord level. *)
            ∗ ◇{List.map fst ds}(2 + L, 1)
            )%S, 1+n⟧⧽
            (OMod.close_itree Client (SCMem.mod gvs) (TreiberStack.pop s))
          ⧼rv, ⟦(
            (⤉ (Q rv ∗ Duty(tid) ds))
            )%S, 1+n⟧⧽
  .
  Proof.
  Admitted.

End SPEC.

Global Opaque TreiberStack.pop TreiberStack.push.
