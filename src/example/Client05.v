From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Import pind Axioms ITreeLib Red TRed IRed2 WFLibLarge.
From Fairness Require Import FairBeh Mod Concurrency Linking.
From Fairness Require Import PCM IPM IPropAux.
From Fairness Require Import IndexedInvariants OpticsInterp SimWeakest SimWeakestAdequacy.
From Fairness Require Import TemporalLogic SCMemSpec.
From Fairness Require Import Spinlock SpinlockSpec0 AuthExclsRA ExclsRA OneShotsRA.

Module Client05.

  Definition gvs : list nat := [1; 1].
  Definition L := SCMem.val_ptr (0, 0).
  Definition D := SCMem.val_ptr (1, 0).
  Global Opaque L D.

  Section CODE.

    Notation state := unit.
    Notation ident := void.

    Definition thread1 :
      ktree (threadE ident state) unit unit
      :=
      fun _ =>
        let d := (SCMem.val_nat 0) in
        ITree.iter (fun (d : SCMem.val) =>
                    b <- (OMod.call (R:=bool) "compare" (d, (SCMem.val_nat 0)));;
                    if b
                    then (_ <- trigger Yield;;
                          _ <- Spinlock.lock L;;
                          d <- (OMod.call (R:=SCMem.val) "load" D);;
                          _ <- trigger Yield;;
                          _ <- Spinlock.unlock L;;
                          Ret (inl d))
                    else Ret (inr tt)) d.

    Definition thread2 :
      ktree (threadE ident state) unit unit
      :=
      fun _ =>
        _ <- OMod.call (R:=unit) "store" (D, (SCMem.val_nat 1));;
        Ret tt.

    Definition omod : Mod.t :=
      Mod.mk
        tt
        (Mod.get_funs [("thread1", Mod.wrap_fun thread1);
                       ("thread2", Mod.wrap_fun thread2)])
    .

    Definition module : Mod.t :=
      OMod.close
        (omod)
        (SCMem.mod gvs)
    .

  End CODE.

End Client05.

Module Client05Spec.

  Section SPEC.

    Notation state := unit.
    Notation ident := void.

    Definition thread1 :
      ktree (threadE ident state) unit unit
      :=
      fun _ =>
        _ <- trigger Yield;; Ret tt.

    Definition thread2:
      ktree (threadE void unit) unit unit
      :=
      fun _ =>
        _ <- trigger Yield;; Ret tt.

    Definition module : Mod.t :=
      Mod.mk
        tt
        (Mod.get_funs [("thread1", Mod.wrap_fun thread1);
                       ("thread2", Mod.wrap_fun thread2)])
    .

  End SPEC.

End Client05Spec.

Section SPEC.

  Import Client05.

  Notation src_state := (Mod.state Client05Spec.module).
  Notation src_ident := (Mod.ident Client05Spec.module).
  Notation tgt_state := (Mod.state Client05.module).
  Notation tgt_ident := (Mod.ident Client05.module).

  Local Instance STT : StateTypes := Build_StateTypes src_state tgt_state src_ident tgt_ident.
  Context `{sub : @SRA.subG Γ Σ}.
  Context {TLRASs : TLRAs_small STT Γ}.
  Context {TLRAS : TLRAs STT Γ Σ}.

  Context {HasMEMRA: @GRA.inG memRA Γ}.
  (* Context {HasAuthExcls : @GRA.inG (AuthExcls.t nat) Γ}. *)
  Context {HasOneShots : @GRA.inG (OneShots.t unit) Γ}.
  Context {HasAuthExcls2 : @GRA.inG (AuthExcls.t (nat * nat)) Γ}.
  (* Context {HasExcls : @GRA.inG (Excls.t unit) Γ}. *)

  Ltac red_tl_all := red_tl; red_tl_memra; red_tl_authexcls; red_tl_excls; red_tl_oneshots.

  (** Invariants. *)

  (* Namespace for Client05 invariants. *)
  Definition N_Client05 : namespace := (nroot .@ "Client05").
  (* Definition N_t2_write : namespace := (nroot .@ "t2_write"). *)
  Context (spinlockN : namespace) `{DISJ: (↑N_state_tgt :coPset) ## (↑spinlockN : coPset)}.

  Lemma mask_disjoint_N_Client05_state_tgt : (↑N_Client05 : coPset) ## (↑N_state_tgt : coPset).
  Proof. apply ndot_ne_disjoint. ss. Qed.
  (* Lemma mask_disjoint_N_t2_write_state_tgt : (↑N_t2_write : coPset) ## (↑N_state_tgt : coPset).
  Proof. apply ndot_ne_disjoint. ss. Qed.
  Lemma mask_disjoint_N_Client05_N_t2_write : (↑N_Client05 : coPset) ## (↑N_t2_write : coPset).
  Proof. apply ndot_ne_disjoint. ss. Qed. *)

  (* Definition t2_write n : sProp n :=
    syn_inv n N_t2_write (D ↦ 1)%S. *)

  (* Global Instance t2_write_persistent n : Persistent (⟦t2_write n, n⟧).
  Proof.
    unfold Persistent. iIntros "H". unfold t2_write. rewrite red_syn_inv.
    iDestruct "H" as "#H". auto.
  Qed. *)

  Definition client05Inv n γw : sProp n := (((△ γw (1/2)) ∗ (D ↦ 0)) ∨ ((▿ γw tt) ∗ (D ↦ 1)))%S.

  (** Simulation proof. *)
  Lemma Client05_thread1_spec
        tid n
    :
    ⊢ ⟦(∀ (γw κw γL : τ{nat, 1+n}),
           ((⤉ syn_inv n N_Client05 (client05Inv n γw))
              ∗ (syn_tgt_interp_as n sndl (fun m => (s_memory_black m)))
              ∗ (⤉ isSpinlock spinlockN n κw L γL emp 3 3)
              ∗ TID(tid)
              ∗ ◇[κw](2, 1)
              ∗ (⤉ Duty(tid) [])
              ∗ (⤉ -[κw](2)-◇ (▿ γw tt)))
             -∗
             syn_wpsim (S n) tid ⊤
             (fun rs rt => (⤉ (syn_term_cond n tid _ rs rt))%S)
             false false
             (fn2th Client05Spec.module "thread1" (tt ↑))
             (fn2th Client05.module "thread1" (tt ↑)))%S, 1+n⟧.
  Proof.
    iIntros. red_tl. iIntros "%γw". red_tl. iIntros "%κw". red_tl. iIntros "%γL".
    red_tl_all; simpl. rewrite red_syn_inv; rewrite red_syn_tgt_interp_as; rewrite red_syn_wpsim.

    iIntros "(#INV & #MEM & #SPIN & TID & PC & DUTY & #PRM)".
    iPoseProof (isSpinlock_unfold with "SPIN") as "[#OBL _]".

    unfold fn2th. simpl. unfold thread1, Client05Spec.thread1. rred2r. lred2r.

    iRevert "TID PC DUTY".
    iMod (tpromise_ind with "[] []") as "IH"; cycle 2. iApply "IH".
    { iSplit; auto. iExists 3; auto. }
    iModIntro. iIntros "IH". iModIntro. iIntros "TID PC DUTY".

    iMod (pc_drop _ 1 _ _ 10 with "PC") as "PC". lia.
    iEval (rewrite unfold_iter_eq). rred2r.
    iApply (wpsim_yieldR_gen with "[DUTY] [-]"). auto. iSplitL; done.
    iIntros "DUTY CRED". iModIntro. rred2r.
    iMod ("IH" with "CRED") as "IH".
    iApply (SCMem_compare_fun_spec with "[] [-]"). instantiate (1:=n). auto. set_solver.
    { simpl. des_ifs. iApply (tgt_interp_as_equiv with "MEM"). iIntros. iSplit.
      { iIntros. simpl. red_tl; simpl. iSplit; [done | iPureIntro; auto]. }
      { simpl. red_tl; simpl. iIntros "[? _]". done. }
    }
    iIntros (rv) "[%EQ _]". exploit EQ. auto. i; subst. rred2r. iApply wpsim_tauR. rred2r.
    iApply (wpsim_yieldR_gen with "[DUTY] [-]"). auto. iSplitL; done.
    iIntros "DUTY CRED". iModIntro. rred2r. iApply wpsim_tauR. rred2r.

    iApply (Spinlock_lock_spec with "[] [PC DUTY]"). set_solver.
    2:{ red_tl_all. rewrite red_syn_tgt_interp_as. iFrame. repeat iSplit; auto. } auto.
    iIntros (_) "POST". iEval (red_tl; simpl) in "POST".
    iDestruct "POST" as (γs) "POST". iEval (red_tl; simpl) in "POST".
    iDestruct "POST" as (κu) "POST". iEval (red_tl_all; simpl) in "POST".
    iDestruct "POST" as "(LW & _ & DUTY & PC)". rred2r.

    iPoseProof (pc_split _ _ 1 with "PC") as "[PC' PC]".
    iApply (wpsim_yieldR_gen with "[DUTY PC'] [-]"). auto.
    { iSplitL "DUTY"; [done | ]. iApply pcs_cons_fold. iSplitL; done. }
    iIntros "DUTY _". iModIntro. rred2r.

    iInv "INV" as "CI" "CI_CLOSE".
    iEval (unfold client05Inv; simpl; red_tl_all; simpl) in "CI".
    iDestruct "CI" as "[[LIVE PTD] | [#SHOT PTD]]".
    { iApply (SCMem_load_fun_spec with "[PTD]"). auto.
      { pose proof mask_disjoint_N_Client05_state_tgt. set_solver. }
      { iSplitR; done. }
      iIntros (rv) "[%EQ' PTD]"; subst. clear EQ. rred2r. iApply wpsim_tauR. rred2r.

      iMod (tpromise_progress with "[CRED]") as "[PC' | #SHOT]".
      { iSplitR; done. }
      2:{ iEval (simpl; red_tl_all) in "SHOT".
          iExFalso; iApply (OneShots.pending_not_shot with "LIVE"). done.
      }

      iDestruct "IH" as "[IH | #SHOT]"; cycle 1.
      { iEval (simpl; red_tl_all) in "SHOT".
        iExFalso; iApply (OneShots.pending_not_shot with "LIVE"). done.
      }

      iMod ("CI_CLOSE" with "[LIVE PTD]") as "_".
      { unfold client05Inv; simpl; red_tl_all; simpl. iLeft; iFrame. }

      iPoseProof (pc_split _ _ 1 with "PC") as "[PC'' PC]".
      iApply (wpsim_yieldR_gen with "[DUTY PC''] [-]"). auto.
      { iSplitL "DUTY"; [done | ]. iApply pcs_cons_fold. iSplitL; done. }
      iIntros "DUTY _". iModIntro. rred2r. iApply wpsim_tauR. rred2r.

      iPoseProof (pc_split _ _ 1 with "PC") as "[PC'' PC]".
      iApply (Spinlock_unlock_spec with "[PC'' DUTY LW]"). set_solver.
      { iEval (red_tl_all; rewrite red_syn_tgt_interp_as; simpl). iFrame. iSplitR; [done | iSplitR; [done | ]].
        iApply pcs_cons_fold; iSplitL; done.
      }
      iIntros (_) "DUTY". iEval (red_tl; simpl) in "DUTY". rred2r. iApply wpsim_tauR.

      iApply wpsim_reset. iApply ("IH" with "TID PC' DUTY").
    }
    { iApply (SCMem_load_fun_spec with "[PTD]"). auto.
      { pose proof mask_disjoint_N_Client05_state_tgt. set_solver. }
      { iSplitR; done. }
      iIntros (rv) "[%EQ' PTD]"; subst. clear EQ. rred2r. iApply wpsim_tauR. rred2r.

      iMod ("CI_CLOSE" with "[PTD]") as "_".
      { unfold client05Inv; simpl; red_tl_all; simpl. iRight; iFrame. done. }

      iPoseProof (pc_split _ _ 1 with "PC") as "[PC'' PC]".
      iApply (wpsim_yieldR_gen with "[DUTY PC''] [-]"). auto.
      { iSplitL "DUTY"; [done | ]. iApply pcs_cons_fold. iSplitL; done. }
      iIntros "DUTY _". iModIntro. rred2r. iApply wpsim_tauR. rred2r.

      iPoseProof (pc_split _ _ 1 with "PC") as "[PC'' PC]".
      iApply (Spinlock_unlock_spec with "[PC'' DUTY LW]"). set_solver.
      { iEval (red_tl_all; rewrite red_syn_tgt_interp_as; simpl). iFrame. iSplitR; [done | iSplitR; [done | ]].
        iApply pcs_cons_fold; iSplitL; done.
      }
      iIntros (_) "DUTY". iEval (red_tl; simpl) in "DUTY". rred2r. iApply wpsim_tauR.

      iEval (rewrite unfold_iter_eq). rred2r.
      iApply (wpsim_sync_gen with "[DUTY] [-]"). auto. iSplitL; done.
      iIntros "DUTY _". iModIntro. rred2r.

      iApply (SCMem_compare_fun_spec); auto.
      { simpl. iApply (tgt_interp_as_equiv with "MEM"). iIntros. iSplit.
        { iIntros. simpl. red_tl; simpl. iSplit; [done | iPureIntro; auto]. }
        { simpl. red_tl; simpl. iIntros "[? _]". done. }
      }
      iIntros (rv) "[_ %NEQ]". exploit NEQ. ii. clarify. i; subst.
      rred2r. iApply wpsim_tauR. rred2r. lred2r. iApply wpsim_ret. auto. iModIntro.
      iFrame. auto.
    }
  Unshelve. auto.
  Qed.

  Lemma Client05_thread2_spec
        tid n
    :
    ⊢ ⟦(∀ (γw κw γL : τ{nat, 1+n}),
      ((⤉ syn_inv n N_Client05 (client05Inv n γw))
        ∗ (syn_tgt_interp_as n sndl (fun m => (s_memory_black m)))
        ∗ (⤉ isSpinlock spinlockN n κw L γL emp 3 3)
        ∗ TID(tid)
        ∗ ◇[κw](3, 1)
        ∗ (⤉ △ γw (1/2))
        ∗ (⤉ Duty(tid) [(κw, 2, (▿ γw tt)%S)])
        ∗ (⤉ -[κw](2)-◇ (▿ γw tt)))
      -∗
        syn_wpsim (S n) tid ⊤
        (fun rs rt => (⤉ (syn_term_cond n tid _ rs rt))%S)
        false false
        (fn2th Client05Spec.module "thread2" (tt ↑))
        (fn2th Client05.module "thread2" (tt ↑)))%S, 1+n⟧.
  Proof.
    iIntros. red_tl. iIntros "%γw". red_tl. iIntros "%κw". red_tl. iIntros "%γL".
    red_tl_all; simpl. rewrite red_syn_inv; rewrite red_syn_tgt_interp_as; rewrite red_syn_wpsim.

    iIntros "(#INV & #MEM & #SPIN & TID & PC & PEND & DUTY & #PRM)".

    unfold fn2th. simpl. unfold thread2, Client05Spec.thread2. rred2r. lred2r.
    iApply (wpsim_sync with "[DUTY PC]"). auto. iFrame. iApply pcs_cons_fold; iFrame.
    iIntros "DUTY _".
    rred2r.
    iInv "INV" as "TI" "TI_CLOSE". iEval (simpl; unfold client05Inv; red_tl_all; simpl) in "TI".
    iDestruct "TI" as "[[PEND' PTD] | [#SHOT _]]"; cycle 1.
    { iExFalso. iApply (OneShots.pending_not_shot with "PEND SHOT"). }

    iPoseProof (OneShots.pending_merge _ (1/2) (1/2) with "PEND PEND'") as "PEND". rewrite Qp.half_half.
    iMod (OneShots.pending_shot with "PEND") as "#SHOT".
    iMod (duty_fulfill with "[DUTY]") as "DUTY".
    { iFrame. simpl; red_tl_all. iSplitR; auto. iPoseProof (unfold_tpromise with "PRM") as "[_ #AO]". auto. }
    iApply (SCMem_store_fun_spec with "[PTD] [-]"). auto.
    { pose proof mask_disjoint_N_Client05_state_tgt; set_solver. }
    { iSplitR; done. }
    iIntros (rv) "PTD". rred2r. iApply wpsim_tauR. rred2r. lred2r.
    iMod ("TI_CLOSE" with "[PTD]") as "_".
    { unfold client05Inv; simpl; red_tl_all; simpl. iRight; auto. }

    iApply wpsim_ret. auto. iModIntro. unfold term_cond; iFrame; iPureIntro; reflexivity.
  Qed.


  Section INITIAL.

    Variable tid1 tid2 : thread_id.
    Let init_ord := Ord.O.
    Let init_ths :=
          (NatStructsLarge.NatMap.add
             tid1 tt
             (NatStructsLarge.NatMap.add
                tid2 tt
                (NatStructsLarge.NatMap.empty unit))).

    Let idx := 1.

    Lemma init_sat E (H_TID : tid1 <> tid2) :
      (OwnM (Σ:=Σ) (memory_init_resource Client05.gvs))
        ∗ (OwnM (Σ:=Σ) (AuthExcls.rest_ra (gt_dec 0) (0, 0)))
        (* ∗ (OwnM (Excls.rest_ra (gt_dec 0) tt)) *)
        ∗
        (WSim.initial_prop
           Client05Spec.module Client05.module
           (Vars:=@sProp STT Γ) (Σ:=Σ)
           (STATESRC:=@SRA.in_subG Γ Σ sub _ _STATESRC)
           (STATETGT:=@SRA.in_subG Γ Σ sub _ _STATETGT)
           (IDENTSRC:=@SRA.in_subG Γ Σ sub _ _IDENTSRC)
           (IDENTTGT:=@SRA.in_subG Γ Σ sub _ _IDENTTGT)
           (ARROWRA:=@_ARROWRA STT Γ Σ TLRAS)
           idx init_ths init_ord)
        ⊢
        =| 1+idx |=(⟦syn_fairI (1+idx), 1+idx⟧)={ E, E }=>
            (∃ γw κw γL,
                (inv idx N_Client05 (client05Inv idx γw))
                  ∗ (⟦syn_tgt_interp_as idx sndl (fun m => (s_memory_black m)), 1+idx⟧)
                  ∗ (⟦isSpinlock spinlockN idx κw L γL emp%S 3 3, idx⟧)
                  ∗ (own_thread tid1
                      ∗ (⟦Duty(tid1) [], idx⟧)
                      ∗ (◇[κw](2, 1))
                      ∗ (-[κw](2)-◇ (▿ γw tt : @sProp STT Γ idx)%S))
                  ∗ ((own_thread tid2)
                      ∗ (⟦Duty(tid2) [(κw, 2, (▿ γw tt : @sProp STT Γ idx)%S)], idx⟧)
                      ∗ (◇[κw](3, 1))
                      ∗ (△ γw (1/2))
                      ∗ (-[κw](2)-◇ (▿ γw tt : @sProp STT Γ idx)%S))
            ).
    Proof.
      iIntros "(MEM & REST & INIT)". rewrite red_syn_fairI.
      iPoseProof (memory_init_iprop with "MEM") as "[MEM PTS]".

      iMod (alloc_obligation_fine 3 3) as "(%kw & #LO & PC & PENDING)".
      iEval (rewrite <- Qp.half_half) in "PENDING".
      iPoseProof (pending_split _ (1/2) (1/2) with "PENDING") as "(PENDING1 & PENDING2)".

      iMod (OneShots.alloc) as "(%γw & LIVE)".
      iEval (rewrite <- Qp.half_half) in "LIVE".
      iPoseProof (OneShots.pending_split _ (1/2) (1/2) with "LIVE") as "(LIVE1 & LIVE2)".
      iMod (AuthExcls.alloc_gt _ (0, 0) with "[REST]") as "[REST (%γl & LB & LW)]".
      { iExists 0. done. }

      unfold WSim.initial_prop.
      iDestruct "INIT" as "(INIT0 & INIT1 & INIT2 & INIT3 & INIT4 & INIT5)".
      (* make thread_own, duty *)
      assert (NatStructsLarge.NatMap.find tid1 init_ths = Some tt).
      { unfold init_ths. apply NatStructsLarge.nm_find_add_eq. }
      iPoseProof (natmap_prop_remove_find _ _ _ H with "INIT2") as "[DU1 INIT2]".
      iPoseProof (natmap_prop_remove_find _ _ _ H with "INIT3") as "[TH1 INIT3]".
      clear H.
      assert (NatStructsLarge.NatMap.find tid2 (NatStructsLarge.NatMap.remove tid1 init_ths) = Some tt).
      { unfold init_ths.
        rewrite NatStructsLarge.NatMapP.F.remove_neq_o; ss.
        rewrite NatStructsLarge.nm_find_add_neq; ss.
        rewrite NatStructsLarge.nm_find_add_eq. ss.
      }
      iPoseProof (natmap_prop_remove_find _ _ _ H with "INIT2") as "[DU2 INIT2]".
      iPoseProof (natmap_prop_remove_find _ _ _ H with "INIT3") as "[TH2 INIT3]".
      clear H.

      iPoseProof (pc_split _ _ 1 with "PC") as "[PC' PC]".
      iMod (duty_add with "[DU2 PENDING2 PC'] []") as "DU2".
      { instantiate (4:=[]). iFrame. }
      { instantiate (1:=(▿ γw tt : @sProp STT Γ idx)%S).
        iModIntro. simpl; red_tl. iIntros "H". red_tl_all.
        iPoseProof "H" as "#H". iModIntro; red_tl_all; auto.
      }
      iPoseProof (duty_delayed_tpromise with "DU2") as "#DPRM2".
      { ss. eauto. }
      iMod (activate_tpromise with "DPRM2 PENDING1") as "[#TPRM _]".
      iPoseProof (pc_split _ _ 1 with "PC") as "[PC' PC]".
      iMod (pc_drop _ 2 _ _ 1 with "PC'") as "PC'". auto.

      iMod (tgt_interp_as_id _ _ (n:=idx) with "[INIT5 MEM]") as "TGT_ST".
      auto.
      2:{ iExists _. iFrame. instantiate (1:=fun '(_, m) => s_memory_black m). simpl.
          red_tl_all. iFrame.
      }
      { simpl. instantiate (1:= (∃ (st : τ{st_tgt_type, idx}), ⟨Atom.ow_st_tgt st⟩ ∗ (let '(_, m) := st in s_memory_black (n:=idx) m))%S).
        red_tl_all. f_equal.
      }
      iPoseProof (tgt_interp_as_compose (n:=idx) (la:=Lens.id) (lb:=sndl) with "TGT_ST") as "TGT_ST".
      { ss. econs. iIntros ([x m]) "MEM". unfold Lens.view. ss. iFrame.
        iIntros (m') "MEM". iFrame.
      }
      iEval (rewrite Lens.left_unit) in "TGT_ST".

      simpl. unfold SCMem.init_gvars, gvs. ss. des_ifs.
      iDestruct "PTS" as "((PT & _) & (PT2 & _) & _)".
      iMod (FUpd_alloc _ _ _ idx N_Client05 (client05Inv idx γw) with "[PT LIVE1]") as "INV1".
      lia.
      { simpl. unfold client05Inv. red_tl_all. iLeft; iFrame.
        ss. clarify.
        Local Transparent SCMem.alloc.
        unfold SCMem.alloc in Heq1. ss; des_ifs. unfold SCMem.alloc in Heq2; ss; des_ifs.
        Local Opaque SCMem.alloc.
      }
      iMod (FUpd_alloc _ _ _ idx spinlockN (spinlockInv idx kw L γl emp%S) with "[PT2 LB LW]") as "SI".
      lia.
      { simpl. unfold spinlockInv. red_tl_all. iExists 0. red_tl. iExists 0. red_tl_all. iFrame. iLeft. iFrame.
        (* TODO : make lemmas *)
        Local Transparent SCMem.alloc.
        unfold SCMem.alloc in Heq1. ss; des_ifs.
        unfold SCMem.alloc in Heq2; ss; des_ifs.
        Local Opaque SCMem.alloc.
      }
      (* iMod (FUpd_alloc _ _ _ idx N_SpinlockUse1 (spinlockUse1 idx kw γl γL emp%S 1)
        with "[WL BS WS]") as "#S1I".
      lia.
      { simpl. unfold spinlockUse1. do 2 (red_tl_all; iExists 0). red_tl_all; simpl.
        iSplitL "BS"; iFrame. iLeft; iFrame.
      } *)
      iModIntro. iExists γw, kw, γl. red_tl_all.
      rewrite red_syn_tgt_interp_as. unfold isSpinlock.
      red_tl_all; rewrite ! red_syn_inv; simpl.
      iFrame "#∗".
    Unshelve. auto.
    Qed.

  End INITIAL.

End SPEC.