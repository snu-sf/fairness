From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Import pind Axioms ITreeLib Red TRed IRed2 WFLibLarge.
From Fairness Require Import FairBeh Mod Concurrency Linking.
From Fairness Require Import PCM IProp IPM IPropAux.
From Fairness Require Import IndexedInvariants OpticsInterp SimWeakest SimWeakestAdequacy.
From Fairness Require Import Spinlock.
From Fairness Require Import TemporalLogic SCMemSpec SpinlockSpec.
From Fairness Require Import AuthExclsRA ExclsRA OneShotsRA.

Module ClientSpinlock2.

  Definition gvs : list nat := [2].
  Definition X : SCMem.val := SCMem.val_ptr (0, 0).
  Definition D : SCMem.val := SCMem.val_ptr (1, 0).

  Section CODE.

    Definition state := unit.
    Definition ident := void.

    Definition thread1 :
      ktree (threadE ident state) unit SCMem.val
      :=
      fun _ =>
        _ <- (trigger Yield;;; Spinlock.lock X);;
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
        _ <- (trigger Yield;;; Spinlock.unlock X);;
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
  Context {HasAuthExcls : @GRA.inG (AuthExcls.t nat) Γ}.
  Context {HasExcls : @GRA.inG (Excls.t unit) Γ}.

  Context {HasOneShotsNat : @GRA.inG (OneShots.t nat) Γ}.

  Ltac red_tl_all := red_tl; red_tl_memra; red_tl_authexcls; red_tl_excls; red_tl_oneshots.

  Import ClientSpinlock2.

  Local Opaque X D.

  (** Invariants. *)

  Definition N_ClientSpinlock2 : namespace := (nroot .@ "ClientSpinlock2").

  Lemma md_N_ClientSpinlock2_state_tgt : (↑N_ClientSpinlock2 : coPset) ## (↑N_state_tgt : coPset).
  Proof. apply ndot_ne_disjoint. ss. Qed.

  Lemma md_N_ClientSpinlock2_Spinlock : (↑N_ClientSpinlock2 : coPset) ## (↑N_Spinlock : coPset).
  Proof. apply ndot_ne_disjoint. ss. Qed.


  Definition clientSpinlock2_inv n (tid2 : thread_id) (ℓL ℓl : nat) (γX γe κs : nat) (κl γκl : nat) (γr : nat) : sProp n :=
    (
      ((○ γX 0) ∗ (D ↦ 0)
                ∗ (-[κl](0)-◇ (∃ (γκw : τ{nat}), ▿ γκl γκw)) ∗ (△ γκl (1/2))
                ∗ ◇[κs](ℓL, 2)
                ∗ (Duty(tid2) [])
      )
      ∨
        ((○ γX 1) ∗ (D ↦ 0)
                  ∗ (∃ (κw γκw : τ{nat}),
                        (-[κw](0)-◇ (∃ (γκu : τ{nat}), ▿ γκw γκu))
                          ∗ (△ γκw (1/2)) ∗ (κw -(0)-◇ κs) ∗ (▿ γκl γκw)
                          ∗ ◇[κs](ℓL, 1)
                          ∗ (Duty(tid2) []))
        )
      ∨
        ((○ γX 1) ∗ (D ↦ 1)
                  ∗ (∃ (γκw κu γκu : τ{nat}),
                        (-[κu](0)-◇ (▿ γκu 0))
                          ∗ (△ γκu (1/2)) ∗ (κu -(0)-◇ κs) ∗ (▿ γκl γκw) ∗ (▿ γκw γκu)
                          ∗ ((Duty(tid2) [(κu, 0, (▿ γκu 0))] ∗ ◇[κu](ℓl, 1) ∗ (EX γe tt)) ∨ (▿ γr 0)))
        )
      ∨
        ((○ γX 0) ∗ (D ↦ 1)
                  ∗ (∃ (γκw γκu : τ{nat}),
                        (▿ γκl γκw) ∗ (▿ γκw γκu) ∗ (▿ γr 0) ∗ (▿ γκu 0)))
    )%S.

  (* Obligation dependencies: (κl at >= (2 + ℓL) + c) → (κw at 2) → (κu at 2 (=ℓl)) → (κs at >= 3) *)

  Lemma ClientSpinlock2_thread1_sim
        tid n tid2
        ℓL ℓl
        (LAYER_L : ℓL = 3)
        (LAYER_l : ℓL = 2)
    :
    ⊢ ⟦(∀ (γX γe κs κl γκl γr : τ{nat, 1+n}),
           ((⤉ syn_inv n N_ClientSpinlock2 (clientSpinlock2_inv n tid2 ℓL ℓl γX γe κs κl γκl γr))
              ∗ (syn_tgt_interp_as n sndl (fun m => (s_memory_black m)))
              ∗ (⤉ isSpinlock n X γX γe κs ℓL)
              ∗ TID(tid)
              ∗ (⤉ Duty(tid) [(κl, 0, (∃ (γκw : τ{nat, n}), ▿ γκl γκw))])
              ∗ ◇[κl](2, 1)
              ∗ ◇[κl](2 + ℓL, 1)
              ∗ (⤉ △ γκl (1/2)))
             -∗
             syn_wpsim (S n) tid ⊤
             (fun rs rt => (⤉(syn_term_cond n tid _ rs rt))%S)
             false false
             (fn2th ClientSpinlock2Spec.module "thread1" (tt ↑))
             (fn2th ClientSpinlock2.module "thread1" (tt ↑)))%S, 1+n⟧.
  Proof.
    iIntros.
    red_tl. iIntros (γX). red_tl. iIntros (γe). red_tl. iIntros (κs).
    red_tl. iIntros (κl). red_tl. iIntros (γκl). red_tl. iIntros (γr).
    iEval (red_tl_all; simpl; rewrite red_syn_inv; rewrite red_syn_wpsim; rewrite red_syn_tgt_interp_as).
    iIntros "(#INV_CL & #MEM & #ISL & TID & DUTY & PC & PC2 & LIVE_l)".
    unfold fn2th. simpl. unfold thread1, ClientSpinlock2Spec.thread1. rred2r. lred2r.

    iMod (pc_drop _ 1 _ _ 100 with "PC") as "PC".
    Unshelve.
    1,3: lia.
    iPoseProof (pcs_cons_fold κl 0 [] 1 100 with "[PC]") as "PCS".
    { iFrame. }
    iApply (wpsim_yieldR2 with "[DUTY PCS]").
    3:{ iFrame. iFrame. }
    1,2: lia.
    iEval (simpl). iIntros "DUTY _ PCS". rred2r. iApply wpsim_tauR. rred2r.

    iPoseProof ((Spinlock_lock_spec tid n ⊤) $! X γX γe κs ℓL) as "SPEC".
    set (P0 := (△ γκl (1/2))%S : sProp n).
    set (R0 := ((△ γκl (1/2)) ∗ Duty(tid) [(κl, 0, (∃ (γκw : τ{nat, n}), ▿ γκl γκw))])%S : sProp n).
    set (Q0 := (∃ (κw γκw : τ{nat, n}),
                   (▿ γκl γκw) ∗ Duty(tid) [(κw, 0, (∃ (γκu : τ{nat}), ▿ γκw γκu))])%S : sProp n).
    (* iSpecialize ("SPEC" $! [(κl, 0, (∃ (γκw : τ{nat, n}), ▿ γκl γκw)%S)] P0 R0 Q0 2). *)
    iSpecialize ("SPEC" $! _ P0 R0 Q0 2).
    iApply ("SPEC" with "[PC2 LIVE_l DUTY] [TID PCS]").
    (* PRE. *)
    { Local Opaque env_live_inv.
      iEval (red_tl_all; simpl).
      iSplitR. eauto. iSplitR. eauto. iSplitL "LIVE_l".
      { subst P0. iEval (red_tl_all). iFrame. }
      iSplitL "DUTY PC2".
      { iFrame. iApply pcs_cons_fold. iFrame. }
      iSplitR.
      - (* ELI. *)
        Local Transparent env_live_inv.
        assert (exists a, a = 1). eauto. des. replace 2 with (1 + a) by auto. iEval simpl. subst a.
        iModIntro. iIntros "FC A". iEval (red_tl_all; simpl; rewrite red_syn_inv) in "A".
        iDestruct "A" as "(#INV_SL & INV_SL_CLOSE & SL)".
        iEval (unfold spinlockInv; red_tl_all; simpl) in "SL". iDestruct "SL" as "[(PTX & LX & EX) | (PTX & LX)]".
        { iModIntro. do 2 iRight. iEval (red_tl_all; simpl; rewrite red_syn_inv). iSplitR. eauto. iFrame. }
        iInv "INV_CL" as "CL" "INV_CL_CLOSE".
        iEval (unfold clientSpinlock2_inv; simpl; red_tl_all; simpl) in "CL".
        iDestruct "CL" as "[CL1 | [CL2 | [CL3 | CL4]]]".
        + iExFalso. iDestruct "CL1" as "(LXw & _)". iPoseProof (AuthExcls.b_w_eq with "LX LXw") as "%F". inv F.
        + iDestruct "CL2" as "(LXw & PTD & %κw & CL2)". iEval (red_tl) in "CL2". iDestruct "CL2" as "[%γκw CL2]".
          iEval (red_tl_all; simpl) in "CL2". iDestruct "CL2" as "(#PROM_w & LIVE_w & #LINK_w & #DEAD_l & PC_spin & DUTY2)".
          iMod (tpromise_progress with "[FC]") as "[PC_w | #FULF_w]".
          { iFrame. iApply "PROM_w". }
          { iMod (link_amplify with "[PC_w]") as "PC_s".
            { iFrame. iApply "LINK_w". }
            iMod ("INV_CL_CLOSE" with "[LXw PTD LIVE_w PC_spin DUTY2]") as "_".
            { iEval (unfold clientSpinlock2_inv; simpl; red_tl_all; simpl). iRight. iLeft. iFrame.
              iExists _. iEval (red_tl_all). iExists _. iEval (red_tl_all; simpl). iFrame. iSplit. iApply "PROM_w". iSplit; auto.
            }
            iModIntro. iLeft. iEval (red_tl; rewrite red_syn_inv). iFrame. iSplitR. auto.
            iEval (unfold spinlockInv; red_tl_all; simpl). iRight. iFrame.
          }
          { iEval (simpl; red_tl_all) in "FULF_w". iDestruct "FULF_w" as "(%γκu & DEAD_w)".
            iEval (red_tl_all) in "DEAD_w". iPoseProof (OneShots.pending_not_shot with "LIVE_w DEAD_w") as "%F". inv F.
          }
        + iDestruct "CL3" as "(LXw & PTD & %γκw & CL3)". iEval (red_tl) in "CL3". iDestruct "CL3" as "[%κu CL3]".
          iEval (red_tl) in "CL3". iDestruct "CL3" as "[%γκu CL3]".
          iEval (red_tl_all; simpl) in "CL3". iDestruct "CL3" as "(#PROM_u & LIVE_u & #LINK_u & #DEAD_l & #DEAD_w & PASS)".
          iMod (tpromise_progress with "[FC]") as "[PC_u | #FULF_u]".
          { iFrame. iApply "PROM_u". }
          { iMod (link_amplify with "[PC_u]") as "PC_s".
            { iFrame. iApply "LINK_u". }
            iMod ("INV_CL_CLOSE" with "[LXw PTD LIVE_u PASS]") as "_".
            { iEval (unfold clientSpinlock2_inv; simpl; red_tl_all; simpl). do 2 iRight. iLeft. iFrame.
              iExists _. iEval (red_tl_all). iExists _. iEval (red_tl_all). iExists _.
              iEval (red_tl_all; simpl). iFrame. iSplit. iApply "PROM_u". iSplit; eauto.
            }
            iModIntro. iLeft. iEval (red_tl; rewrite red_syn_inv). iFrame. iSplitR. auto.
            iEval (unfold spinlockInv; red_tl_all; simpl). iRight. iFrame.
          }
          { iEval (simpl; red_tl_all) in "FULF_u".
            iPoseProof (OneShots.pending_not_shot with "LIVE_u FULF_u") as "%F". inv F.
          }
        + iExFalso. iDestruct "CL4" as "(LXw & _)". iPoseProof (AuthExcls.b_w_eq with "LX LXw") as "%F". inv F.

      -
        
          




End SIM.

