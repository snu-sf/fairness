From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Import pind Axioms ITreeLib Red TRed IRed2 WFLibLarge.
From Fairness Require Import FairBeh Mod Concurrency Linking.
From Fairness Require Import PCM IPM IPropAux.
From Fairness Require Import IndexedInvariants OpticsInterp SimWeakest SimWeakestAdequacy.
From Fairness Require Import Spinlock.
From Fairness Require Import TemporalLogic SCMemSpec SpinlockSpec0.
From Fairness Require Import AuthExclsRA OneShotsRA.

Module ClientSpinlock2.

  Definition gvs : list nat := [1; 1].
  Definition L : SCMem.val := SCMem.val_ptr (0, 0).
  Definition D : SCMem.val := SCMem.val_ptr (1, 0).

  Section CODE.

    Definition state := unit.
    Definition ident := void.

    Definition thread1 :
      ktree (threadE ident state) unit SCMem.val
      :=
      fun _ =>
        _ <- (trigger Yield;;; Spinlock.lock L);;
        _ <- (OMod.call (R:=unit) "store" (D, SCMem.val_nat 1));;
        _ <- trigger Yield;;
        Ret (SCMem.val_nat 0).

    Definition thread2 :
      ktree (threadE ident state) unit SCMem.val
      :=
      fun _ =>
        _ <- trigger Yield;;
        _ <- (ITree.iter (fun _ =>
                           d <- (OMod.call (R:=SCMem.val) "load" D);;
                           b <- (OMod.call (R:=bool) "compare" (d, 1 : SCMem.val));;
                           r <- (if b
                                then Ret (inr tt)
                                else Ret (inl tt));;
                           Ret r) tt);;
        _ <- (trigger Yield;;; Spinlock.unlock L);;
        _ <- trigger Yield;;
        Ret (SCMem.val_nat 0).

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

End ClientSpinlock2.

Module ClientSpinlock2Spec.

  Section SPEC.

    Definition state := unit.
    Definition ident := void.

    Definition thread1 :
      ktree (threadE ident state) unit SCMem.val
      :=
      fun _ =>
        _ <- trigger Yield;; Ret (0 : SCMem.val).

    Definition thread2:
      ktree (threadE void unit) unit SCMem.val
      :=
      fun _ =>
        _ <- trigger Yield;; Ret (0 : SCMem.val).

    Definition module : Mod.t :=
      Mod.mk
        tt
        (Mod.get_funs [("thread1", Mod.wrap_fun thread1);
                       ("thread2", Mod.wrap_fun thread2)])
    .

  End SPEC.

End ClientSpinlock2Spec.

Section SIM.

  Notation src_state := (Mod.state ClientSpinlock2Spec.module).
  Notation src_ident := (Mod.ident ClientSpinlock2Spec.module).
  Notation tgt_state := (Mod.state ClientSpinlock2.module).
  Notation tgt_ident := (Mod.ident ClientSpinlock2.module).

  Local Instance STT : StateTypes := Build_StateTypes src_state tgt_state src_ident tgt_ident.
  Context `{sub : @SRA.subG Γ Σ}.
  Context {TLRASs : TLRAs_small STT Γ}.
  Context {TLRAS : TLRAs STT Γ Σ}.

  Context {HasMEMRA: @GRA.inG memRA Γ}.

  Context {HasOneShotsNat : @GRA.inG (OneShots.t unit) Γ}.
  Context {HasAuthExcls : @GRA.inG (AuthExcls.t (nat * nat)) Γ}.

  Ltac red_tl_all := red_tl; red_tl_memra; red_tl_authexcls; red_tl_oneshots.

  Import ClientSpinlock2.

  Local Opaque L D.

  (** Invariants. *)

  Definition N_ClientSpinlock2 : namespace := (nroot .@ "ClientSpinlock2").
  Definition N_Spinlock : namespace := (nroot .@ "Spinlock").
  (* Notation E_Spinlock := (↑N_Spinlock : coPset). *)

  Lemma md_N_ClientSpinlock2_state_tgt : (↑N_ClientSpinlock2 : coPset) ## (↑N_state_tgt : coPset).
  Proof. apply ndot_ne_disjoint. ss. Qed.

  Lemma md_N_ClientSpinlock2_Spinlock : (↑N_ClientSpinlock2 : coPset) ## (↑N_Spinlock : coPset).
  Proof. apply ndot_ne_disjoint. ss. Qed.

  Lemma md_Spinlock_state_tgt : (↑N_Spinlock : coPset) ## (↑N_state_tgt : coPset).
  Proof. apply ndot_ne_disjoint. ss. Qed.

  (* Definition clientSpinlock2_inv n (tid2 : thread_id) (ℓL : nat) (γX γe κs : nat) (κl γκl κw γκw κu γκu : nat) (γr : nat) : sProp n :=
    (
      ((○G γX 0) ∗ (D ↦ 0)
                ∗ (-[κl](0)-◇ (▿ γκl γκw))
                ∗ (△ γκl (1/2)) ∗ (△ γκw (1/2)) ∗ (△ γκu (1/2))
                ∗ ⧖[κu, 1/2]
                ∗ (-[κu](0)-⧖ (▿ γκu 0))
                ∗ (κu -(0)-◇ κs)
                ∗ (∃ (ℓl : τ{nat}), ◆[κl, ℓl])
      )
      ∨
        ((○G γX 1) ∗ (D ↦ 0)
                  ∗ (-[κw](0)-◇ (▿ γκw γκu))
                  ∗ (△ γκw (1/2)) ∗ (△ γκu (1/2)) ∗ (▿ γκl γκw)
                  ∗ ⧖[κu, 1/2]
                  ∗ (-[κu](0)-⧖ (▿ γκu 0))
                  ∗ (κu -(0)-◇ κs)
                  ∗ (△ γκu (1/2))
                  ∗ (∃ (ℓw : τ{nat}), ◆[κw, ℓw] ∗ ⌜ℓw <= ℓL⌝)
        )
      ∨
        ((○G γX 1) ∗ (D ↦ 1)
                  ∗ (-[κu](0)-◇ (▿ γκu 0))
                  ∗ (△ γκu (1/2)) ∗ (▿ γκl γκw) ∗ (▿ γκw γκu)
                  ∗ ⋈[κu] ∗ (κu -(0)-◇ κs)
                  ∗ (((EX γe tt) ∨ (▿ γr 0)))
        )
      ∨
        ((○G γX 0) ∗ (D ↦ 1)
                  ∗ (▿ γκl γκw) ∗ (▿ γκw γκu) ∗ (▿ γr 0) ∗ (▿ γκu 0))
    )%S. *)
  Definition clientSpinlock2_inv n (γl : nat) (κw γκw κu γκu : nat) (γr : nat) : sProp n :=
      (
        ((D ↦ 0)
          ∗ (◆[κw, 4, 3]) ∗ (-[κw](0)-◇ (▿ γκw tt)) ∗ (△ γκw (1/2))
          ∗ (◆[κu, 2, 2]) ∗ (-[κu](0)-⧖ (▿ γκu tt)) ∗ ⧖[κu, 1/2] ∗ (△ γκu 1))
        ∨
        ((D ↦ 1)
          ∗ (▿ γκw tt)
          ∗ (○G γl (γκu, κu) ∨ ▿ γr tt))
      )%S.

  (* Obligation dependencies: (κl at >= (2 + ℓL) + c) → (κw at 2) → (κu at 2 (=ℓl)) → (κs at >= 3) *)

  Lemma ClientSpinlock2_thread1_sim
        tid n
    :
    ⊢ ⟦(∀ (γl κs κw γκw κu γκu γr : τ{nat, 1+n}),
           ((⤉ syn_inv n N_ClientSpinlock2 (clientSpinlock2_inv n γl κw γκw κu γκu γr))
              ∗ (syn_tgt_interp_as n sndl (fun m => (s_memory_black m)))
              ∗ (⤉ isSpinlock N_Spinlock n κs L γl emp 3 1)
              ∗ TID(tid)
              ∗ (⤉ Duty(tid) [(κw, 0, (▿ γκw tt))])
              ∗ ◇[κs](3, 1)
              ∗ ◇[κw](4, 2)
              ∗ (⤉ △ γκw (1/2))
           )
             -∗
             syn_wpsim (S n) tid ⊤
             (fun rs rt => (⤉(syn_term_cond n tid _ rs rt))%S)
             false false
             (fn2th ClientSpinlock2Spec.module "thread1" (tt ↑))
             (fn2th ClientSpinlock2.module "thread1" (tt ↑)))%S, 1+n⟧.
  Proof.
    iIntros.
    red_tl. iIntros (γl). red_tl. iIntros (κs).
    red_tl. iIntros (κw). red_tl. iIntros (γκw).
    red_tl. iIntros (κu). red_tl. iIntros (γκu). red_tl. iIntros (γr).
    iEval (red_tl_all; simpl; rewrite red_syn_inv; rewrite red_syn_wpsim; rewrite red_syn_tgt_interp_as).
    iIntros "(#INV & #MEM & #SPIN & TID & DUTY & PCs & PCw & LIVE)".
    unfold fn2th. simpl. unfold thread1, ClientSpinlock2Spec.thread1. rred2r. lred2r.

    iPoseProof (pc_split _ _ 1 with "PCw") as "[PCw' PCw]".
    iMod (pc_drop _ 1 _ _ 5 with "PCw") as "PCw". Unshelve. 1,3: lia.
    iPoseProof (pcs_cons_fold κw 0 [] 1 5 with "[PCw]") as "PCS". iFrame.
    iPoseProof (pcs_cons_fold κw 0 [] 4 1 with "[PCw']") as "PCS'". iFrame.

    iMod (pc_drop _ 2 _ _ 3 with "PCs") as "PCs". Unshelve. 1, 3: lia.
    iPoseProof (pc_split _ _ 1 with "PCs") as "[PCs' PCs]".
    iMod (pc_drop _ 1 _ _ 2 with "PCs'") as "PCs'". Unshelve. 1, 3: lia.

    iApply (wpsim_yieldR2 with "[DUTY PCS]"). auto. 2: { iFrame. done. } auto.
    iIntros "DUTY _ PCS". simpl. rred2r. iApply wpsim_tauR. rred2r.

    iMod (pcs_decr 1 3 with "PCS") as "[PCS'' PCS]". auto.
    iApply (Spinlock_lock_spec with "[] [PCs' DUTY PCS' PCS''] [-]").
    { pose proof md_Spinlock_state_tgt. set_solver. }
    { instantiate (1:=1). auto. }
    { red_tl_all. rewrite red_syn_tgt_interp_as.
      iFrame "#". iFrame "PCs' DUTY PCS' PCS''".
    }
    iIntros (_) "POST". iEval (red_tl; simpl) in "POST".
    iDestruct "POST" as (γκu') "POST". iEval (red_tl; simpl) in "POST".
    iDestruct "POST" as (κu') "POST". iEval (red_tl_all; simpl) in "POST".
    iDestruct "POST" as "(LW & _ & DUTY & PC)". rred2r.

    iMod (pcs_decr 1 2 with "PCS") as "[PCS' PCS]". auto.
    iApply (wpsim_yieldR with "[DUTY PCS' PC]"). auto.
    { iFrame. iApply (pcs_cons_fold with "[PCS' PC]"). iFrame. }
    iIntros "DUTY _". rred2r.

    iInv "INV" as "CI" "CI_CLOSE".
    iEval (unfold clientSpinlock2_inv; simpl; red_tl_all; simpl) in "CI".
    iDestruct "CI" as "[(PTD & #OBLw & #PRMw & LIVE' & #OBLu & #DPRMu & PO2 & LIVE2) | (_ & #SHOT & _)]"; cycle 1.
    { iExFalso. iApply (OneShots.pending_not_shot with "LIVE SHOT"). }

    iApply (SCMem_store_fun_spec with "[PTD]"). auto.
    { pose proof md_N_ClientSpinlock2_state_tgt. set_solver. }
    { iFrame. auto. }
    iIntros (rv) "PTD". rred2r. iApply wpsim_tauR. rred2r.

    iPoseProof (pass_lock with "[LW DUTY PCs PO2 LIVE2]") as "PASS".
    2:{ red_tl_all. iFrame "#". iFrame. }
    { instantiate (1 := ⊤ ∖ ↑N_ClientSpinlock2). pose proof md_N_ClientSpinlock2_Spinlock. set_solver. }
    iEval (rewrite red_syn_fairI) in "PASS". iMod "PASS".
    iEval (red_tl_all; simpl) in "PASS". iDestruct "PASS" as "(LW & DUTY & _)".

    iPoseProof (OneShots.pending_merge _ (1/2) (1/2) with "LIVE LIVE'") as "LIVE". rewrite Qp.half_half.
    iMod (OneShots.pending_shot _ tt with "LIVE") as "#SHOTw".
    iPoseProof (unfold_tpromise with "PRMw") as "[_ #AOw]".
    iMod (duty_fulfill with "[DUTY]") as "DUTY".
    { iFrame. simpl; red_tl_all; iSplit; auto. }

    iMod ("CI_CLOSE" with "[PTD LW]") as "_".
    { iEval (unfold clientSpinlock2_inv; simpl). red_tl_all. iRight. iFrame. done. }

    iApply (wpsim_sync2 with "[DUTY]"). auto. auto. iFrame.
    iIntros "DUTY _ _". simpl. rred2r. iApply wpsim_tauR. rred2r. lred2r.

    iApply wpsim_ret. auto. iModIntro. iFrame. auto.
  Qed.

  Lemma ClientSpinlock2_thread2_sim
        tid n
    :
    ⊢ ⟦(∀ (γl κs κw γκw κu γκu γr : τ{nat, 1+n}),
           ((⤉ syn_inv n N_ClientSpinlock2 (clientSpinlock2_inv n γl κw γκw κu γκu γr))
              ∗ (syn_tgt_interp_as n sndl (fun m => (s_memory_black m)))
              ∗ (⤉ isSpinlock N_Spinlock n κs L γl emp 3 1)
              ∗ TID(tid)
              ∗ (⤉ Duty(tid) [(κu, 0, (▿ γκu tt))])
              ∗ ◆[κw, 4, 3]
              ∗ ◇[κu](2, 1)
              ∗ (⤉ △ γr 1))
             -∗
             syn_wpsim (S n) tid ⊤
             (fun rs rt => (⤉(syn_term_cond n tid _ rs rt))%S)
             false false
             (fn2th ClientSpinlock2Spec.module "thread2" (tt ↑))
             (fn2th ClientSpinlock2.module "thread2" (tt ↑)))%S, 1+n⟧.
  Proof.
    iIntros.
    red_tl. iIntros (γl). red_tl. iIntros (κs).
    red_tl. iIntros (κw). red_tl. iIntros (γκw).
    red_tl. iIntros (κu). red_tl. iIntros (γκu). red_tl. iIntros (γr).
    iEval (red_tl_all; simpl; rewrite red_syn_inv; rewrite red_syn_wpsim; rewrite red_syn_tgt_interp_as).
    iIntros "(#INV & #MEM & #SPIN & TID & DUTY & #OBLw & PCu & LIVE)".
    unfold fn2th. simpl. unfold thread2, ClientSpinlock2Spec.thread2. rred2r. lred2r.

    iMod (pc_drop _ 1 _ _ 10 with "PCu") as "PCu". Unshelve. 1,3: lia.
    iPoseProof (pcs_cons_fold κu 0 [] 1 10 with "[PCu]") as "PCS". iFrame.

    iApply (wpsim_yieldR2 with "[DUTY PCS]"). auto. 2: { iFrame. done. } lia.
    iIntros "DUTY _ PCS". simpl. rred2r. iApply wpsim_tauR. rred2r.

    (* Induction *)
    iRevert "TID DUTY LIVE PCS".
    iMod (lo_ind_fine with "OBLw []") as "IH".
    2: { iApply "IH". }
    iModIntro. iExists 0. iIntros "IH". iModIntro.
    iIntros "TID DUTY LIVE PCS".

    iEval (rewrite unfold_iter_eq). rred2r.

    iInv "INV" as "CI" "CI_CLOSE".
    iEval (unfold clientSpinlock2_inv; simpl; red_tl_all; simpl) in "CI".
    iDestruct "CI" as
      "[(PTD & _ & #PRMw & LIVEw & #OBLu & #DPRMu & POu & LIVEu) | (PTD & #SHOTw & [LW | #SHOTu])]"; cycle 2.
    { iExFalso. iApply (OneShots.pending_not_shot with "LIVE SHOTu"). }
    { (* Not yet *)
      iApply (wpsim_yieldR_gen_pending with "DUTY [POu]"). auto. erewrite app_nil_r. auto.
      3:{ iApply (pps_cons_fold with "[POu]"). iFrame. iApply pps_nil. } 1,2,3 : auto.
      iIntros "DUTY CRED PPS _".
      iPoseProof (pps_cons_unfold with "PPS") as "[POu _]".
      iMod (tpromise_progress with "[CRED]") as "[PCw | #SHOTw]". iFrame. done.
      2:{ iExFalso. iEval (simpl; red_tl_all) in "SHOTw". iApply (OneShots.pending_not_shot with "LIVEw SHOTw"). }
      iMod ("IH" with "PCw") as "IH".
      iMod ("CI_CLOSE" with "[PTD LIVEw LIVEu POu]") as "_".
      { iEval (unfold clientSpinlock2_inv; simpl). red_tl_all. iLeft. iFrame. simpl. repeat iSplit; auto. }
      iModIntro. rred2r.
      iInv "INV" as "CI" "CI_CLOSE".
      iEval (unfold clientSpinlock2_inv; simpl; red_tl_all; simpl) in "CI".
      iDestruct "CI" as
        "[(PTD & _ & _ & LIVEw & _ & _ & POu & LIVEu) | (PTD & #SHOTw & [LW | #SHOTu])]"; cycle 2.
      { iExFalso. iApply (OneShots.pending_not_shot with "LIVE SHOTu"). }
      { (* Not yet*)
        iApply (SCMem_load_fun_spec with "[PTD] [-]"). auto.
        { pose proof md_N_ClientSpinlock2_state_tgt. set_solver. }
        { iSplitR; done. }
        iIntros (rv) "[%EQ PTD]"; subst. rred2r. iApply wpsim_tauR. rred2r.
        iApply (wpsim_yieldR_gen_pending with "DUTY [POu]"). auto. erewrite app_nil_r. auto.
        3:{ iApply (pps_cons_fold with "[POu]"). iFrame. iApply pps_nil. } 1,2,3 : auto.
        iIntros "DUTY CRED PPS _".
        iPoseProof (pps_cons_unfold with "PPS") as "[POu _]".
        iMod ("CI_CLOSE" with "[PTD LIVEw LIVEu POu]") as "_".
        { iEval (unfold clientSpinlock2_inv; simpl). red_tl_all. iLeft. iFrame. simpl. repeat iSplit; auto. }
        iModIntro. rred2r.
        iApply SCMem_compare_fun_spec; auto.
        { simpl. iApply (tgt_interp_as_equiv with "MEM"). iIntros. iSplit.
          { iIntros. simpl. red_tl; simpl. iSplit; [done | iPureIntro; auto]. }
          { simpl. red_tl; simpl. iIntros "[? _]". done. }
        }
        iIntros (rv) "[_ %NEQ]". exploit NEQ. ii. clarify. i; subst.
        rred2r. iApply wpsim_tauR. rred2r. iApply wpsim_tauR.
        iApply ("IH" with "TID DUTY LIVE PCS").
      }
      { (* Th1 has stored *)
        iClear "IH".
        iApply (SCMem_load_fun_spec with "[PTD] [-]"). auto.
        { pose proof md_N_ClientSpinlock2_state_tgt. set_solver. }
        { iSplitR; done. }
        iIntros (rv) "[%EQ PTD]"; subst. rred2r. iApply wpsim_tauR. rred2r.

        iMod (OneShots.pending_shot _ tt with "LIVE") as "#SHOT".
        iMod ("CI_CLOSE" with "[PTD]") as "_".
        { iEval (unfold clientSpinlock2_inv; simpl). red_tl_all. iRight. iFrame. repeat iSplit; auto. }

        iApply (wpsim_yieldR2 with "[DUTY PCS]"). auto. 2: { iFrame. done. } lia.
        iIntros "DUTY _ PCS". simpl. rred2r.

        iApply SCMem_compare_fun_spec; auto.
        { simpl. iApply (tgt_interp_as_equiv with "MEM"). iIntros. iSplit.
          { iIntros. simpl. red_tl; simpl. iSplit; [done | iPureIntro; auto]. }
          { simpl. red_tl; simpl. iIntros "[? _]". done. }
        }
        iIntros (rv) "[%EQ _]". exploit EQ. auto. ii. clarify.
        rred2r. iApply wpsim_tauR. rred2r.

        iApply (wpsim_yieldR2 with "[DUTY PCS]"). auto. 2: { iFrame. done. } lia.
        iIntros "DUTY _ PCS". simpl. rred2r.
        iApply wpsim_tauR. rred2r.

        iMod (pcs_decr 1 with "PCS") as "[PCS' PCS]". left.
        iApply (Spinlock_unlock_spec with "[DUTY LW PCS']").
        { pose proof md_Spinlock_state_tgt. set_solver. }
        { iEval (red_tl_all; rewrite red_syn_tgt_interp_as; simpl). iFrame. simpl. iFrame. iSplit; auto. }
        iIntros (_) "DUTY". iEval (red_tl; simpl) in "DUTY". rred2r.

        iApply (wpsim_sync with "[DUTY]"). auto. iFrame.
        iIntros "DUTY _". rred2r. iApply wpsim_tauR. rred2r. lred2r.
        iApply wpsim_ret. auto. iModIntro. iFrame. auto.
      }
    }
    {
      iClear "IH".

      iMod (OneShots.pending_shot _ tt with "LIVE") as "#SHOT".
      iMod ("CI_CLOSE" with "[PTD]") as "_".
      { iEval (unfold clientSpinlock2_inv; simpl). red_tl_all. iRight. iFrame. repeat iSplit; auto. }

      iApply (wpsim_yieldR2 with "[DUTY PCS]"). auto. 2: { iFrame. done. } lia.
      iIntros "DUTY _ PCS". simpl. rred2r.

      iInv "INV" as "CI" "CI_CLOSE".
      iEval (unfold clientSpinlock2_inv; simpl; red_tl_all; simpl) in "CI".
      iDestruct "CI" as "[(_ & _ & _ & LIVEw & _) | (PTD & _ & [LW' | #SHOTu])]".
      { iExFalso. iApply (OneShots.pending_not_shot with "LIVEw SHOTw"). }
      { iExFalso. iApply (AuthExcls.w_w_false with "LW LW'"). }

      iApply (SCMem_load_fun_spec with "[PTD] [-]"). auto.
      { pose proof md_N_ClientSpinlock2_state_tgt. set_solver. }
      { iSplitR; done. }
      iIntros (rv) "[%EQ PTD]"; subst. rred2r. iApply wpsim_tauR. rred2r.

      iMod ("CI_CLOSE" with "[PTD]") as "_".
      { iEval (unfold clientSpinlock2_inv; simpl). red_tl_all. iRight. iFrame. repeat iSplit; auto. }

      iApply (wpsim_yieldR2 with "[DUTY PCS]"). auto. 2: { iFrame. done. } lia.
      iIntros "DUTY _ PCS". simpl. rred2r.

      iApply SCMem_compare_fun_spec; auto.
      { simpl. iApply (tgt_interp_as_equiv with "MEM"). iIntros. iSplit.
        { iIntros. simpl. red_tl; simpl. iSplit; [done | iPureIntro; auto]. }
        { simpl. red_tl; simpl. iIntros "[? _]". done. }
      }
      iIntros (rv) "[%EQ _]". exploit EQ. auto. ii. clarify.
      rred2r. iApply wpsim_tauR. rred2r.

      iApply (wpsim_yieldR2 with "[DUTY PCS]"). auto. 2: { iFrame. done. } lia.
      iIntros "DUTY _ PCS". simpl. rred2r.
      iApply wpsim_tauR. rred2r.

      iMod (pcs_decr 1 with "PCS") as "[PCS' PCS]". left.
      iApply (Spinlock_unlock_spec with "[DUTY LW PCS']").
      { pose proof md_Spinlock_state_tgt. set_solver. }
      { iEval (red_tl_all; rewrite red_syn_tgt_interp_as; simpl). iFrame. simpl. iFrame. iSplit; auto. }
      iIntros (_) "DUTY". iEval (red_tl; simpl) in "DUTY". rred2r.

      iApply (wpsim_sync with "[DUTY]"). auto. iFrame.
      iIntros "DUTY _". rred2r. iApply wpsim_tauR. rred2r. lred2r.
      iApply wpsim_ret. auto. iModIntro. iFrame. auto.
    }
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
    (OwnM (Σ:=Σ) (memory_init_resource ClientSpinlock2.gvs))
      ∗ (OwnM (Σ:=Σ) (AuthExcls.rest_ra (gt_dec 0) (0, 0)))
      ∗
      (WSim.initial_prop
         ClientSpinlock2Spec.module ClientSpinlock2.module
         (Vars:=@sProp STT Γ) (Σ:=Σ)
         (STATESRC:=@SRA.in_subG Γ Σ sub _ _STATESRC)
         (STATETGT:=@SRA.in_subG Γ Σ sub _ _STATETGT)
         (IDENTSRC:=@SRA.in_subG Γ Σ sub _ _IDENTSRC)
         (IDENTTGT:=@SRA.in_subG Γ Σ sub _ _IDENTTGT)
         (ARROWRA:=@_ARROWRA STT Γ Σ TLRAS)
         idx init_ths init_ord)
      ⊢
      =| 1+idx |=(⟦syn_fairI (1+idx), 1+idx⟧)={ E, E }=>
          (∃ γl κs κw γκw κu γκu γr,
              (inv idx N_ClientSpinlock2 (clientSpinlock2_inv idx γl κw γκw κu γκu γr))
                ∗ (⟦syn_tgt_interp_as idx sndl (fun m => (s_memory_black m)), 1+idx⟧)
                ∗ (⟦isSpinlock N_Spinlock idx κs L γl emp%S 3 1, idx⟧)
                ∗ (own_thread tid1
                  ∗ (⟦Duty(tid1) [(κw, 0, (▿ γκw tt : @sProp STT Γ idx))], idx⟧)
                  ∗ ◇[κs](3, 1)
                  ∗ ◇[κw](4, 2)
                  ∗ (△ γκw (1/2)))
                ∗ ((own_thread tid2)
                  ∗ (⟦Duty(tid2) [(κu, 0, (▿ γκu tt : @sProp STT Γ idx))], idx⟧)
                  ∗ ◆[κw, 4, 3]
                  ∗ ◇[κu](2, 1)
                  ∗ (△ γr 1))
          ).
  Proof.
    iIntros "(MEM & REST & INIT)". rewrite red_syn_fairI.
    iPoseProof (memory_init_iprop with "MEM") as "[MEM PTS]".

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

    iMod (alloc_obligation_fine 2 2) as "(%κu & #OBLu & PCu & POu)".
    iEval (rewrite <- Qp.half_half) in "POu".
    iPoseProof (pending_split _ (1/2) (1/2) with "POu") as "(POu & POu')".
    iMod (OneShots.alloc) as "(%γr & LIVE)".
    iMod (OneShots.alloc) as "(%γκu & LIVEu)".
    iPoseProof (pc_split _ _ 1 with "PCu") as "[PCu' PCu]".
    iMod (pc_drop _ 1 _ _ 1 with "PCu'") as "PCu'". Unshelve. 1, 3: lia.
    iMod (duty_add with "[DU2 POu' PCu'] []") as "DU2".
    { instantiate (4:=[]). iFrame. }
    { instantiate (1:=(▿ γκu tt : @sProp STT Γ idx)%S).
      iModIntro. simpl; red_tl. iIntros "H". red_tl_all.
      iPoseProof "H" as "#H". iModIntro; red_tl_all; auto.
    }
    iPoseProof (duty_delayed_tpromise with "DU2") as "#DPRM2".
    { ss. eauto. }

    iMod (alloc_obligation_fine 3 1) as "(%κs & #OBLs & PCs & _)".

    iMod (alloc_obligation_fine 4 3) as "(%κw & #OBLw & PCw & POw)".
    iEval (rewrite <- Qp.half_half) in "POw".
    iPoseProof (pending_split _ (1/2) (1/2) with "POw") as "(POw & POw')".
    iMod (OneShots.alloc) as "(%γκw & LIVEw)".
    iEval (rewrite <- Qp.half_half) in "LIVEw".
    iPoseProof (OneShots.pending_split _ (1/2) (1/2) with "LIVEw") as "(LIVEw & LIVEw')".
    iPoseProof (pc_split _ _ 1 with "PCw") as "[PCw' PCw]".
    iMod (pc_drop _ 1 _ _ 1 with "PCw'") as "PCw'". Unshelve. 1, 3: lia.
    iMod (duty_add with "[DU1 POw' PCw'] []") as "DU1".
    { instantiate (4:=[]). iFrame. }
    { instantiate (1:=(▿ γκw tt : @sProp STT Γ idx)%S).
      iModIntro. simpl; red_tl. iIntros "H". red_tl_all.
      iPoseProof "H" as "#H". iModIntro; red_tl_all; auto.
    }
    iPoseProof (duty_delayed_tpromise with "DU1") as "#DPRM1".
    { ss. eauto. }
    iMod (activate_tpromise with "DPRM1 POw") as "[#PRM1 _]".

    iMod (AuthExcls.alloc_gt _ (0, 0) with "[REST]") as "[REST (%γl & LB & LW)]".
    { iExists 0. done. }

    iMod (tgt_interp_as_id _ _ (n:=idx) with "[INIT5 MEM]") as "TGT_ST_PRE".
    auto.
    2:{ iExists _. iFrame. instantiate (1:=fun '(_, m) => s_memory_black m). simpl.
        red_tl_all. iFrame.
    }
    { simpl. instantiate (1:= (∃ (st : τ{st_tgt_type, idx}), ⟨Atom.ow_st_tgt st⟩ ∗ (let '(_, m) := st in s_memory_black (n:=idx) m))%S).
      red_tl_all. f_equal.
    }
    iDestruct (tgt_interp_as_compose (n:=idx) (la:=Lens.id) (lb:=sndl) with "TGT_ST_PRE") as "#TGT_ST".
    { ss. econs. iIntros ([x m]) "MEM". unfold Lens.view. ss. iFrame.
      iIntros (m') "MEM". iFrame.
    }
    iClear "TGT_ST_PRE".
    iEval (rewrite Lens.left_unit) in "TGT_ST".

    simpl. unfold SCMem.init_gvars, gvs. ss. des_ifs.
    iDestruct "PTS" as "((PT & _) & (PT2 & _) & _)".
    iMod (FUpd_alloc _ _ _ idx N_ClientSpinlock2 (clientSpinlock2_inv idx γl κw γκw κu γκu γr)
      with "[PT POu LIVEu LIVEw']") as "#INV1".
    lia.
    { simpl. unfold clientSpinlock2_inv. red_tl_all. iLeft; iFrame.
      ss. clarify.
      Local Transparent SCMem.alloc.
      unfold SCMem.alloc in Heq1. ss; des_ifs. unfold SCMem.alloc in Heq2; ss; des_ifs.
      Local Opaque SCMem.alloc.
      iFrame. repeat iSplit; auto.
    }
    iMod (FUpd_alloc _ _ _ idx N_Spinlock (spinlockInv idx κs L γl emp%S) with "[PT2 LB LW]") as "#SI".
    lia.
    { simpl. unfold spinlockInv. red_tl_all. iExists 0. red_tl. iExists 0. red_tl_all. iFrame. iLeft. iFrame.
      Local Transparent SCMem.alloc.
      unfold SCMem.alloc in Heq1. ss; des_ifs.
      unfold SCMem.alloc in Heq2; ss; des_ifs.
      Local Opaque SCMem.alloc.
    }
    iModIntro. iExists γl, κs, κw, γκw, κu, γκu, γr. red_tl_all.
    rewrite red_syn_tgt_interp_as. unfold isSpinlock.
    red_tl_all; rewrite ! red_syn_inv; simpl.
    iFrame "# TH1 DU1 PCs PCw ∗".
  Qed.

End INITIAL.

End SIM.

