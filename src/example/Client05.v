From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Import pind Axioms ITreeLib Red TRed IRed2 WFLibLarge.
From Fairness Require Import FairBeh Mod Concurrency Linking.
From Fairness Require Import PCM IProp IPM IPropAux.
From Fairness Require Import IndexedInvariants OpticsInterp SimWeakest SimWeakestAdequacy.
From Fairness Require Import TemporalLogic SCMemSpec.
From Fairness Require Import Spinlock SpinlockSpec SpinlockSpec1 AuthExclsRA ExclsRA OneShotsRA.

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
  Context {HasAuthExcls : @GRA.inG (AuthExcls.t nat) Γ}.
  Context {HasOneShots : @GRA.inG (OneShots.t unit) Γ}.
  Context {HasAuthExcls2 : @GRA.inG (AuthExcls.t (nat * nat)) Γ}.
  Context {HasExcls : @GRA.inG (Excls.t unit) Γ}.

  Ltac red_tl_all := red_tl; red_tl_memra; red_tl_authexcls; red_tl_excls; red_tl_oneshots.

  (** Invariants. *)

  (* Namespace for Client05 invariants. *)
  Definition N_Client05 : namespace := (nroot .@ "Client05").
  Definition N_t2_write : namespace := (nroot .@ "t2_write").

  Lemma mask_disjoint_N_Client05_state_tgt : (↑N_Client05 : coPset) ## (↑N_state_tgt : coPset).
  Proof. apply ndot_ne_disjoint. ss. Qed.
  Lemma mask_disjoint_N_t2_write_state_tgt : (↑N_t2_write : coPset) ## (↑N_state_tgt : coPset).
  Proof. apply ndot_ne_disjoint. ss. Qed.
  Lemma mask_disjoint_N_Client05_N_t2_write : (↑N_Client05 : coPset) ## (↑N_t2_write : coPset).
  Proof. apply ndot_ne_disjoint. ss. Qed.

  Definition t2_write n : sProp n :=
    syn_inv n N_t2_write (D ↦ 1)%S.

  Global Instance t2_write_persistent n : Persistent (⟦t2_write n, n⟧).
  Proof.
    unfold Persistent. iIntros "H". unfold t2_write. rewrite red_syn_inv.
    iDestruct "H" as "#H". auto.
  Qed.

  Definition client05Inv γw kw n : sProp n :=
    (◆[kw, 4] ∗ (((△ γw (1/2)) ∗ (D ↦ 0)) -U-[kw](3)-◇ ((▿ γw tt) ∗ t2_write n)))%S.

  (** Simulation proof. *)
  Lemma Client05_thread1_spec
        tid n
    :
    ⊢ ⟦(∀ (γw kw γL γe γs : τ{nat, 1+n}),
           ((⤉ syn_inv n N_Client05 (client05Inv γw kw n))
              ∗ (syn_tgt_interp_as n sndl (fun m => (s_memory_black m)))
              ∗ (⤉ isSpinlock n L γL γe kw 4)
              ∗ (⤉ isSpinlockUse1 n kw γs γL emp 2)
              ∗ TID(tid)
              ∗ ◇[kw](3, 1)
              ∗ (⤉ Duty(tid) []))
             -∗
             syn_wpsim (S n) tid ⊤
             (fun rs rt => (⤉ (syn_term_cond n tid _ rs rt))%S)
             false false
             (fn2th Client05Spec.module "thread1" (tt ↑))
             (fn2th Client05.module "thread1" (tt ↑)))%S, 1+n⟧.
  Proof.
    iIntros. red_tl. iIntros "%γw". red_tl. iIntros "%kw".
    red_tl. iIntros "%γL". red_tl. iIntros "%γe". red_tl. iIntros "%γs".
    red_tl_all; simpl. rewrite red_syn_inv; rewrite red_syn_tgt_interp_as; rewrite red_syn_wpsim.

    iIntros "(#INV & #MEM & #SPIN & #SPIN1 & TID & PC & DUTY)".

    unfold fn2th. simpl. unfold thread1, Client05Spec.thread1. rred2r. lred2r.

    iEval (rewrite unfold_iter_eq). rred2r.
    iApply (wpsim_yieldR_gen with "[DUTY] [-]"). auto. iSplitL; done.
    iIntros "DUTY CRED". iModIntro. rred2r.
    iApply (SCMem_compare_fun_spec with "[] [-]"). instantiate (1:=n). auto. set_solver.
    { simpl. des_ifs. iApply (tgt_interp_as_equiv with "MEM"). iIntros. iSplit.
      { iIntros. simpl. red_tl; simpl. iSplit; [done | iPureIntro; auto]. }
      { simpl. red_tl; simpl. iIntros "[? _]". done. }
    }
    iIntros (rv) "[%EQ _]". exploit EQ. auto. i; subst. rred2r. iApply wpsim_tauR. rred2r.
    iApply (wpsim_yieldR_gen with "[DUTY] [-]"). auto. iSplitL; done.
    iIntros "DUTY CRED2". iModIntro. rred2r. iApply wpsim_tauR. rred2r.

    iApply (Spinlock_lock_spec_use1 with "[PC DUTY]"). auto.
    { iEval (red_tl_all; rewrite red_syn_tgt_interp_as; simpl). iFrame. iSplit; [done | iSplit; done]. }
    iIntros (_) "POST". iEval (red_tl; simpl) in "POST".
    iDestruct "POST" as (γu) "POST". iEval (red_tl; simpl) in "POST".
    iDestruct "POST" as (u) "POST". iEval (red_tl_all; simpl) in "POST".
    iDestruct "POST" as "(EX & _ & WS & DUTY & PC)". rred2r.

    iMod (pc_drop _ 1 _ _ 3 with "PC") as "PC". auto.
    iPoseProof (pc_split _ _ 1 2 with "PC") as "[PC1 PC]".
    iApply (wpsim_yieldR_gen with "[DUTY PC1] [-]"). auto.
    { iSplitL "DUTY"; [done | ]. iApply pcs_cons_fold. iSplitL; done. }
    iIntros "DUTY CRED3". iModIntro. rred2r.

    iInv "INV" as "CI" "CI_CLOSE".
    iEval (unfold client05Inv; simpl; red_tl_all; simpl; rewrite red_syn_until_tpromise) in "CI".
    iDestruct "CI" as "[#OBL UPRM]".
    iPoseProof (until_tpromise_get_tpromise with "UPRM") as "#PRM".
    (* Induction point *)
    iRevert (γu u) "DUTY TID EX WS CI_CLOSE PC".
    iMod (until_tpromise_ind with "[UPRM] [-]") as "IH"; cycle 2.
    { done. }
    { iSplit; done. }
    iSplit.
    { iModIntro. iIntros "IH". iModIntro. iIntros "PRE" (γu u) "DUTY TID EX WS CI_CLOSE PC".
      iEval (simpl; red_tl_all) in "PRE". iDestruct "PRE" as "[PEND PTD]".
      iApply (SCMem_load_fun_spec with "[PTD]"). auto.
      { pose proof mask_disjoint_N_Client05_state_tgt. set_solver. }
      { iSplitR; done. }
      iIntros (rv) "[%EQ' PTD]"; subst. clear EQ. rred2r. iApply wpsim_tauR. rred2r.

      iPoseProof (pc_split _ _ 1 1 with "PC") as "[PC1 PC]".
      iApply (wpsim_yieldR_gen with "[DUTY PC1] [-]"). auto.
      { iSplitL "DUTY"; [done | ]. iApply pcs_cons_fold. iSplitL; done. }
      iIntros "DUTY CRED".

      iMod (tpromise_progress with "[CRED]") as "[PCk | #DEAD]".
      { iSplitR; done. }
      2:{ iEval (simpl; red_tl_all) in "DEAD". iDestruct "DEAD" as "[SHOT _]".
          iExFalso; iApply (OneShots.pending_not_shot with "PEND"). done.
      }

      iMod ("CI_CLOSE" with "[PEND PTD]") as "_".
      { unfold client05Inv; simpl; red_tl_all; simpl; rewrite red_syn_until_tpromise. iSplit; [done | ].
        iApply (until_tpromise_make1 with "[PEND PTD]"). iSplitR. done. simpl; red_tl_all; simpl. iFrame.
      }
      iModIntro. rred2r. iApply wpsim_tauR. rred2r.
      iApply (Spinlock_unlock_spec_use1 with "[PC DUTY EX WS]"). auto.
      { iEval (red_tl_all; rewrite red_syn_tgt_interp_as; simpl). iFrame. iSplitR; [done | iSplitR; [done | ]].
        iSplitR; [done | iApply pcs_cons_fold; iSplitL; done].
      }
      iIntros (_) "DUTY". iEval (red_tl; simpl) in "DUTY". rred2r. iApply wpsim_tauR.

      iEval (rewrite unfold_iter_eq). rred2r.
      iApply (wpsim_yieldR_gen with "[DUTY] [-]"). auto. iSplitL; done.
      iIntros "DUTY CRED". iModIntro. rred2r.
      iApply (SCMem_compare_fun_spec with "[] [-]"). instantiate (1:=n). auto. set_solver.
      { simpl. des_ifs. iApply (tgt_interp_as_equiv with "MEM"). iIntros. iSplit.
        { iIntros. simpl. red_tl; simpl. iSplit; [done | iPureIntro; auto]. }
        { simpl. red_tl; simpl. iIntros "[? _]". done. }
      }
      iIntros (rv) "[%EQ _]". exploit EQ. auto. i; subst. rred2r. iApply wpsim_tauR. rred2r.
      iApply (wpsim_yieldR_gen with "[DUTY] [-]"). auto. iSplitL; done.
      iIntros "DUTY CRED2". iModIntro. rred2r. iApply wpsim_tauR. rred2r.

      iApply (Spinlock_lock_spec_use1 with "[PCk DUTY]"). auto.
      { iEval (red_tl_all; rewrite red_syn_tgt_interp_as; simpl). iFrame. iSplit; [done | iSplit; done]. }
      iIntros (_) "POST". iEval (red_tl; simpl) in "POST". clear γu u.
      iDestruct "POST" as (γu) "POST". iEval (red_tl; simpl) in "POST".
      iDestruct "POST" as (u) "POST". iEval (red_tl_all; simpl) in "POST".
      iDestruct "POST" as "(EX & _ & WS & DUTY & PC)". rred2r.
      
      iMod (pc_drop _ 1 _ _ 3 with "PC") as "PC". auto.
      iPoseProof (pc_split _ _ 1 2 with "PC") as "[PC1 PC]".
      iApply (wpsim_yieldR_gen with "[DUTY PC1] [-]"). auto.
      { iSplitL "DUTY"; [done | ]. iApply pcs_cons_fold. iSplitL; done. }
      iIntros "DUTY CRED3". iModIntro. rred2r.

      iInv "INV" as "CI" "CI_CLOSE".
      iEval (unfold client05Inv; simpl; red_tl_all; simpl; rewrite red_syn_until_tpromise) in "CI".
      iDestruct "CI" as "[_ UPRM]".
      iMod ("IH" with "[CRED UPRM]") as "IH". iFrame.
      iApply ("IH" $! γu u with "DUTY TID EX WS CI_CLOSE PC").
    }
    {
      iModIntro. iIntros "#DONE" (γu u) "DUTY TID EX WS CI_CLOSE PC".
      iEval (unfold t2_write; simpl; red_tl_all; rewrite red_syn_inv) in "DONE".
      iDestruct "DONE" as "[#SHOT #TINV]".
      iInv "TINV" as "TI" "TI_CLOSE". iEval (simpl; red_tl_all) in "TI".
      iApply (SCMem_load_fun_spec with "[TI]"). auto.
      { pose proof mask_disjoint_N_Client05_N_t2_write; pose proof mask_disjoint_N_Client05_state_tgt;
          pose proof mask_disjoint_N_t2_write_state_tgt. set_solver.
      }
      { iSplitR; done. }
      iIntros (rv) "[%EQ' PTD]"; subst. clear EQ. rred2r. iApply wpsim_tauR. rred2r.

      iPoseProof (pc_split _ _ 1 1 with "PC") as "[PC1 PC]".
      iApply (wpsim_yieldR_gen with "[DUTY PC1] [-]"). auto.
      { iSplitL "DUTY"; [done | ]. iApply pcs_cons_fold. iSplitL; done. }
      iIntros "DUTY CRED".

      iMod ("TI_CLOSE" with "[PTD]") as "_".
      { simpl; red_tl_all; done. }
      iMod ("CI_CLOSE" with "[]") as "_".
      { unfold client05Inv; simpl; red_tl_all; simpl; rewrite red_syn_until_tpromise. iSplit; [done | ].
        iApply (until_tpromise_make2 with "[]"). iSplitR. done. iModIntro.
        unfold t2_write; simpl; red_tl_all; simpl; rewrite red_syn_inv. iSplit; done.
      }
      iModIntro. rred2r. iApply wpsim_tauR. rred2r.

      iApply (Spinlock_unlock_spec_use1 with "[PC DUTY EX WS]"). auto.
      { iEval (red_tl_all; rewrite red_syn_tgt_interp_as; simpl). iFrame. iSplitR; [done | iSplitR; [done | ]].
        iSplitR; [done | iApply pcs_cons_fold; iSplitL; done].
      }
      iIntros (_) "DUTY". iEval (red_tl; simpl) in "DUTY". rred2r. iApply wpsim_tauR.

      iEval (rewrite unfold_iter_eq). rred2r.
      iApply (wpsim_sync_gen with "[DUTY] [-]"). auto. iSplitL; done.
      iIntros "DUTY _". iModIntro. rred2r.
      iApply (SCMem_compare_fun_spec with "[] [-]"). instantiate (1:=n). auto. set_solver.
      { simpl. des_ifs. iApply (tgt_interp_as_equiv with "MEM"). iIntros. iSplit.
        { iIntros. simpl. red_tl; simpl. iSplit; [done | iPureIntro; auto]. }
        { simpl. red_tl; simpl. iIntros "[? _]". done. }
      }
      iIntros (rv) "[_ %NEQ]". exploit NEQ. auto. i; subst. rred2r. iApply wpsim_tauR. rred2r. lred2r.
      iApply (wpsim_ret). auto. iModIntro. unfold term_cond. iFrame. iPureIntro; reflexivity.
    }
  Unshelve. all: auto.
  Qed.

  Lemma Client05_thread2_spec
        tid n
    :
    ⊢ ⟦(∀ (γw kw γL γe γs : τ{nat, 1+n}),
           ((⤉ syn_inv n N_Client05 (client05Inv γw kw n))
              ∗ (syn_tgt_interp_as n sndl (fun m => (s_memory_black m)))
              ∗ (⤉ isSpinlock n L γL γe kw 4)
              ∗ (⤉ isSpinlockUse1 n kw γs γL emp 2)
              ∗ TID(tid)
              ∗ (⤉ Duty(tid) [(kw, 3, (▿ γw tt) ∗ t2_write n)])
              ∗ ◇[kw](4, 2)
              ∗ (⤉ △ γw (1/2)))
             -∗
             syn_wpsim (S n) tid ⊤
             (fun rs rt => (⤉ (syn_term_cond n tid _ rs rt))%S)
             false false
             (fn2th Client05Spec.module "thread2" (tt ↑))
             (fn2th Client05.module "thread2" (tt ↑)))%S, 1+n⟧.
  Proof.
    iIntros. red_tl. iIntros "%γw". red_tl. iIntros "%kw".
    red_tl. iIntros "%γL". red_tl. iIntros "%γe". red_tl. iIntros "%γs".
    red_tl_all; simpl. rewrite red_syn_inv; rewrite red_syn_tgt_interp_as; rewrite red_syn_wpsim.

    iIntros "(#INV & #MEM & #SPIN & #SPIN1 & TID & DUTY & PC & PEND)".

    unfold fn2th. simpl. unfold thread2, Client05Spec.thread2. rred2r. lred2r.
    iPoseProof (pc_split _ _ 1 1 with "PC") as "[PC1 PC]".
    iApply (wpsim_sync with "[DUTY PC1]"). auto. iFrame. iApply pcs_cons_fold; iFrame.
    iIntros "DUTY CRED".
    rred2r.
    iInv "INV" as "TI" "TI_CLOSE". iEval (simpl; unfold client05Inv; red_tl_all; simpl) in "TI".
    iDestruct "TI" as "[#OBL UPRM]". iEval (rewrite red_syn_until_tpromise) in "UPRM".

    unfold until_thread_promise. iDestruct "UPRM" as "[#PRM [YET | #DONE]]"; cycle 1.
    { iEval (simpl; red_tl_all) in "DONE".
      iDestruct "DONE" as "[SHOT _]"; iExFalso; iApply (OneShots.pending_not_shot with "PEND"); done.
    }
    iEval (simpl; red_tl_all) in "YET". iDestruct "YET" as "[PEND2 PTD]".
    iPoseProof (OneShots.pending_merge _ (1/2) (1/2) with "PEND PEND2") as "PEND". rewrite Qp.half_half.
    iMod (OneShots.pending_shot with "PEND") as "#SHOT".
    iApply (SCMem_store_fun_spec with "[PTD] [-]"). auto.
    { pose proof mask_disjoint_N_Client05_state_tgt; set_solver. }
    { iSplitR; done. }
    iIntros (rv) "PTD".
    rred2r. iApply wpsim_tauR. rred2r. lred2r.

    iMod (FUpd_alloc _ _ _ n N_t2_write (D ↦ 1)%S with "[PTD]") as "#CI". auto.
    { simpl; red_tl_all; auto. }

    iMod (duty_fulfill with "[DUTY]") as "DUTY".
    { iFrame. simpl; red_tl_all. iSplitR; auto. }

    iMod ("TI_CLOSE" with "[]") as "_".
    { unfold client05Inv; simpl; red_tl_all; simpl. iSplitR; [done | ]. rewrite red_syn_until_tpromise.
      iApply (until_tpromise_make2). iSplit; [done | ].
      iModIntro; simpl; unfold t2_write; red_tl_all; iSplit; done.
    }
    
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
      (OwnM (memory_init_resource Client05.gvs))
        ∗ (OwnM (AuthExcls.rest_ra (gt_dec 0) 0))
        ∗ (OwnM (AuthExcls.rest_ra (gt_dec 0) (0, 0)))
        ∗ (OwnM (Excls.rest_ra (gt_dec 0) tt))
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
            (∃ γw kw γL γe γs,
                (inv idx N_Client05 (client05Inv γw kw idx))
                  ∗ (⟦syn_tgt_interp_as idx sndl (fun m => (s_memory_black m)), 1+idx⟧)
                  ∗ (⟦isSpinlock idx L γL γe kw 4, idx⟧)
                  ∗ (⟦isSpinlockUse1 idx kw γs γL emp%S 2, idx⟧)
                  ∗ (own_thread tid1
                      ∗ (⟦Duty(tid1) [], idx⟧)
                      ∗ ◇[kw](3, 1))
                  ∗ ((own_thread tid2)
                      ∗ (⟦Duty(tid2) [(kw, 3, ((▿ γw tt : @sProp STT Γ idx) ∗ t2_write idx)%S)], idx⟧)
                      ∗ ◇[kw](4, 2) ∗ (△ γw (1/2)))
            ).
    Proof.
      iIntros "(MEM & REST1 & REST2 & REST & INIT)". rewrite red_syn_fairI.
      iPoseProof (memory_init_iprop with "MEM") as "[MEM PTS]".

      iMod (alloc_obligation 4 4) as "(%kw & #LO & PC)".
      iMod (OneShots.alloc) as "(%γw & LIVE)".
      iEval (rewrite <- Qp.half_half) in "LIVE".
      iPoseProof (OneShots.pending_split _ (1/2) (1/2) with "LIVE") as "(LIVE1 & LIVE2)".
      iMod (AuthExcls.alloc_gt _ (0) with "[REST1]") as "[REST1 (%γL & BL & WL)]".
      { iExists 0. done. }
      iMod (AuthExcls.alloc_gt _ (0, 0) with "[REST2]") as "[REST2 (%γs & BS & WS)]".
      { iExists 0. done. }
      iMod (Excls.alloc_gt tt with "[REST]") as "[REST (%γe & EX)]".
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

      iEval (replace 4 with (2+2) at 2 by lia) in "PC".
      iPoseProof (pc_split with "PC") as "[PC1 PC2]".
      iEval (replace 2 with (1+1) at 2 by lia) in "PC2".
      iPoseProof (pc_split with "PC2") as "[PC2 PC3]".
      iMod (pc_drop _ 3 _ _ 1 with "PC3") as "PC3". auto.
      (* iEval (replace 3 with (2+1) at 2 by lia) in "PC3".
      iPoseProof (pc_split with "PC3") as "[PC3 PC4]". *)
      iMod (duty_add (v:=idx) with "[DU2 PC2] []") as "DU2".
      { iSplitL "DU2". instantiate (1:=[]). iApply "DU2". iFrame. }
      { instantiate (1:=((▿ γw tt : @sProp STT Γ idx) ∗ t2_write idx)%S). simpl. red_tl_all.
        unfold t2_write. rewrite red_syn_inv. iModIntro. iIntros "#P". auto.
      }
      iPoseProof (duty_tpromise with "DU2") as "#PROM2".
      { ss. eauto. }

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
      iMod (FUpd_alloc _ _ _ idx N_Client05 (client05Inv γw kw idx) with "[PT LIVE1]") as "INV1".
      lia.
      { simpl. unfold client05Inv. red_tl_all. rewrite red_syn_until_tpromise. simpl.
        iSplitR. eauto. iSplitR. auto. simpl. iLeft. red_tl_all. iFrame.
        ss. clarify.
        Local Transparent SCMem.alloc.
        unfold SCMem.alloc in Heq1. ss; des_ifs. unfold SCMem.alloc in Heq2; ss; des_ifs.
        Local Opaque SCMem.alloc.
      }
      iMod (FUpd_alloc _ _ _ idx N_Spinlock (spinlockInv idx L γL γe) with "[PT2 BL EX]") as "SI".
      lia.
      { simpl. unfold spinlockInv. red_tl_all. iLeft; iFrame.
        (* TODO : make lemmas *)
        Local Transparent SCMem.alloc.
        unfold SCMem.alloc in Heq1. ss; des_ifs.
        unfold SCMem.alloc in Heq2; ss; des_ifs.
        Local Opaque SCMem.alloc.
      }
      iMod (FUpd_alloc _ _ _ idx N_SpinlockUse1 (spinlockUse1 idx kw γs γL emp%S 1)
        with "[WL BS WS]") as "#S1I".
      lia.
      { simpl. unfold spinlockUse1. do 2 (red_tl_all; iExists 0). red_tl_all; simpl.
        iSplitL "BS"; iFrame. iLeft; iFrame.
      }
      iModIntro. iExists γw, kw, γL, γe, γs. red_tl_all.
      rewrite red_syn_tgt_interp_as. unfold isSpinlock, isSpinlockUse1.
      red_tl_all; rewrite ! red_syn_inv; simpl. iFrame. iSplitR; [done | iSplit; [iPureIntro; lia | done]].
    Unshelve. auto.
    Qed.

  End INITIAL.

End SPEC.