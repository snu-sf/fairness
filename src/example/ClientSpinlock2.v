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

  Definition clientSpinlock2_inv n (tid2 : thread_id) (ℓL ℓl : nat) (γX γe κs : nat) (κl γκl κu γκu : nat) (γr : nat) : sProp n :=
    (
      ((○ γX 0) ∗ (D ↦ 0)
                ∗ (-[κl](0)-◇ (∃ (γκw : τ{nat}), ▿ γκl γκw)) ∗ (△ γκl (1/2))
                ∗ ⧖[κu, 1/2]
                ∗ (-[κu](0)-⧖ (▿ γκu 0))
                ∗ (κu -(0)-◇ κs)
                ∗ (∃ (ℓl : τ{nat}), ◆[κl, ℓl])
      )
      ∨
        ((○ γX 1) ∗ (D ↦ 0)
                  ∗ (∃ (κw γκw : τ{nat}),
                        (-[κw](0)-◇ (▿ γκw γκu))
                          ∗ (△ γκw (1/2)) ∗ (▿ γκl γκw)
                          ∗ ⧖[κu, 1/2]
                          ∗ (-[κu](0)-⧖ (▿ γκu 0))
                          ∗ (κu -(0)-◇ κs)
                          ∗ (∃ (ℓw : τ{nat}), ◆[κw, ℓw] ∗ ⌜ℓw <= ℓL⌝))
        )
      ∨
        ((○ γX 1) ∗ (D ↦ 1)
                  ∗ (∃ (γκw κu γκu : τ{nat}),
                        (-[κu](0)-◇ (▿ γκu 0))
                          ∗ (△ γκu (1/2)) ∗ ⋈[κu] ∗ (κu -(0)-◇ κs) ∗ (▿ γκl γκw) ∗ (▿ γκw γκu)
                          ∗ (((△ γκu (1/2)) ∗ (EX γe tt)) ∨ (▿ γr 0)))
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
        (LAYER_l : ℓl = 2)
    :
    ⊢ ⟦(∀ (γX γe κs κl γκl κu γκu γr : τ{nat, 1+n}),
           ((⤉ syn_inv n N_ClientSpinlock2 (clientSpinlock2_inv n tid2 ℓL ℓl γX γe κs κl γκl κu γκu γr))
              ∗ (syn_tgt_interp_as n sndl (fun m => (s_memory_black m)))
              ∗ (⤉ isSpinlock n X γX γe κs ℓL)
              ∗ TID(tid)
              ∗ (⤉ Duty(tid) [(κl, 0, (∃ (γκw : τ{nat, n}), ▿ γκl γκw))])
              ∗ ◇[κl](2, 1)
              ∗ ◇[κl](2 + ℓL, 5)
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
    red_tl. iIntros (κl). red_tl. iIntros (γκl). red_tl. iIntros (κu). red_tl. iIntros (γκu).
    red_tl. iIntros (γr).
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
                   (▿ γκl γκw) ∗ (△ γκw (1/2)) ∗ (Duty(tid) [(κw, 0, (∃ (γκu : τ{nat}), ▿ γκw γκu))]) ∗ ◇[κw](ℓl, 1)
               )%S : sProp n).
    iSpecialize ("SPEC" $! _ P0 R0 Q0 1).
    iApply ("SPEC" with "[PC2 LIVE_l DUTY] [TID]").

    (* PRE. *)
    { Local Opaque env_live_chain.
      iEval (red_tl_all; simpl).
      iSplitR. eauto. iSplitR. eauto. iSplitL "LIVE_l".
      { subst P0. iEval (red_tl_all). iFrame. }
      iSplitL "DUTY PC2".
      { iFrame. iApply pcs_cons_fold. iFrame. }
      iSplitR.
      { (* ELC. *)
        Local Transparent env_live_chain. Local Opaque env_live_chain0.
        iEval (simpl). iModIntro. iIntros "FC A". iEval (red_tl_all; simpl; rewrite red_syn_inv) in "A".
        iDestruct "A" as "(#INV_SL & INV_SL_CLOSE & SL)".
        iEval (unfold spinlockInv; red_tl_all; simpl) in "SL". iDestruct "SL" as "[(PTX & LX & EX) | (PTX & LX)]".
        { iModIntro. iRight. iLeft. iEval (red_tl_all; simpl; rewrite red_syn_inv). iSplitR. eauto. iFrame. }
        iInv "INV_CL" as "CL" "INV_CL_CLOSE".
        iEval (unfold clientSpinlock2_inv; simpl; red_tl_all; simpl) in "CL".
        iDestruct "CL" as "[CL1 | [CL2 | [CL3 | CL4]]]".
        - iExFalso. iDestruct "CL1" as "(LXw & _)". iPoseProof (AuthExcls.b_w_eq with "LX LXw") as "%F". inv F.

        - iDestruct "CL2" as "(LXw & PTD & %κw & CL2)". iEval (red_tl) in "CL2". iDestruct "CL2" as "[%γκw CL2]".
          iEval (red_tl_all; simpl) in "CL2". iDestruct "CL2" as "(#PROM_w & LIVE_w & #DEAD_l & DUTY2 & PC_spin & LO_w)".
          iDestruct "LO_w" as "[% LO]". iEval (red_tl; simpl) in "LO". iPoseProof "LO" as "[#LO %LAY]".
          iMod ("INV_CL_CLOSE" with "[LXw PTD LIVE_w DUTY2 PC_spin]") as "_".
          { iEval (unfold clientSpinlock2_inv; simpl; red_tl_all; simpl). iRight. iLeft. iFrame.
            iExists _. iEval (red_tl_all). iExists _. iEval (red_tl_all; simpl). iFrame. iSplit. iApply "PROM_w".
            iSplit. eauto. iExists _. iEval (red_tl; simpl). eauto.
          }
          iModIntro. do 2 iRight. iSplitL.
          { iEval (unfold spinlockInv; red_tl_all; simpl). iSplitR. rewrite red_syn_inv. auto.
            iSplitL "INV_SL_CLOSE".
            { iEval (unfold spinlockInv; red_tl_all; simpl) in "INV_SL_CLOSE". iFrame. }
            iRight. iFrame.
          }
          iExists κw, x, (((⤉ syn_inv n N_Spinlock (spinlockInv n X γX γe)) ∗ ((⤉ spinlockInv n X γX γe =| S n |={ ⊤ ∖ ↑N_Spinlock, ⊤ }=∗ emp) ∗ ⤉ spinlockInv n X γX γe)) ∗ (⤉ (∃ (γκu : τ{nat}), ▿ γκw γκu)))%S.
          iSplitR. auto. iSplitR. auto. iSplitR.
          { iModIntro. iIntros "B". iModIntro. iEval (red_tl; simpl) in "B". iDestruct "B" as "(A & C)".
            iSplitL "A".
            { iEval (red_tl). iFrame. }
            iModIntro. iEval (red_tl; simpl). iIntros "A". iModIntro. iFrame.
          }
          Local Transparent env_live_chain0.
          iSplitR.
          { (* ELC at 0. *)
            iModIntro. iEval (simpl; red_tl; simpl). iIntros "FC A".
            iMod (tpromise_progress with "[FC]") as "[PC_w | #FULF_w]".
            { iSplitR. iApply "PROM_w". iFrame. }
            { iModIntro. iLeft. iFrame. }
            { iEval (simpl; red_tl_all) in "FULF_w". iDestruct "FULF_w" as "[%γκu DEAD_w]".
              iModIntro. iRight. iFrame. iExists _. eauto.
            }
          }
          (* ELC continuation. *)
          iModIntro. iEval (simpl; red_tl; simpl). iIntros "FC [A [%γκu B]]".
          iEval (red_tl_all) in "B". iPoseProof "B" as "#DEAD_w". iClear "INV_SL".
          iEval (red_tl_all; simpl; rewrite red_syn_inv) in "A". iDestruct "A" as "(#INV_SL & INV_SL_CLOSE & SL)".
          iEval (unfold spinlockInv; red_tl_all; simpl) in "SL". iDestruct "SL" as "[(PTX & LX & EX) | (PTX & LX)]".
          { iModIntro. iRight. iEval (red_tl_all; simpl; rewrite red_syn_inv). iSplitR. eauto. iFrame. }
          iInv "INV_CL" as "CL" "INV_CL_CLOSE".
          iEval (unfold clientSpinlock2_inv; simpl; red_tl_all; simpl) in "CL".
          iDestruct "CL" as "[CL1 | [CL2 | [CL3 | CL4]]]".
          + iExFalso. iDestruct "CL1" as "(LXw & _)". iPoseProof (AuthExcls.b_w_eq with "LX LXw") as "%F". inv F.
          + iExFalso. iDestruct "CL2" as "(_ & _ & [% CL2])". iEval (red_tl) in "CL2". iDestruct "CL2" as "[% CL2]".
            iEval (red_tl_all; simpl) in "CL2". iDestruct "CL2" as "(_ & LIVE_w & DEAD_l2 & _)".
            iPoseProof (OneShots.shot_agree with "DEAD_l DEAD_l2") as "%EQ". subst x1.
            iPoseProof (OneShots.pending_not_shot with "LIVE_w DEAD_w") as "%F". inv F.
          + iDestruct "CL3" as "(LXw & PTD & % & CL3)". iEval (red_tl) in "CL3". iDestruct "CL3" as "[%κu CL3]".
            iEval (red_tl) in "CL3". iDestruct "CL3" as "[% CL3]".
            iEval (red_tl_all; simpl) in "CL3". iDestruct "CL3" as "(#PROM_u & LIVE_u & #LINK_u & #DEAD_l2 & #DEAD_w2 & PASS)".
            iPoseProof (OneShots.shot_agree with "DEAD_l DEAD_l2") as "%EQ". subst x0.
            iPoseProof (OneShots.shot_agree with "DEAD_w DEAD_w2") as "%EQ". subst x1.
            iMod (tpromise_progress with "[FC]") as "[PC_u | #FULF_u]".
            { iFrame. iApply "PROM_u". }
            { iMod (link_amplify with "[PC_u]") as "PC_s".
              { iFrame. iApply "LINK_u". }
              iMod ("INV_CL_CLOSE" with "[LXw PTD LIVE_u PASS]") as "_".
              { iEval (unfold clientSpinlock2_inv; simpl; red_tl_all; simpl). do 2 iRight. iLeft. iFrame.
                iExists _. iEval (red_tl_all). iExists _. iEval (red_tl_all). iExists _.
                iEval (red_tl_all; simpl). iFrame. iSplit. iApply "PROM_u". iSplit; eauto.
              }
              iModIntro. iLeft. iEval (red_tl; rewrite red_syn_inv). iFrame.
              { iSplitL. iSplitR. auto. iEval (unfold spinlockInv; red_tl_all; simpl). iRight. iFrame.
                iExists _. iEval (red_tl_all). eauto.
              }
            }
            { iEval (simpl; red_tl_all) in "FULF_u".
              iPoseProof (OneShots.pending_not_shot with "LIVE_u FULF_u") as "%F". inv F.
            }
          + iExFalso. iDestruct "CL4" as "(LXw & _)". iPoseProof (AuthExcls.b_w_eq with "LX LXw") as "%F". inv F.

        - iDestruct "CL3" as "(LXw & PTD & %γκw & CL3)". iEval (red_tl) in "CL3". iDestruct "CL3" as "[%κu CL3]".
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
            iModIntro. iLeft. iEval (red_tl; rewrite red_syn_inv). iFrame.
            iSplitR. auto. iEval (unfold spinlockInv; red_tl_all; simpl). iRight. iFrame.
          }
          { iEval (simpl; red_tl_all) in "FULF_u".
            iPoseProof (OneShots.pending_not_shot with "LIVE_u FULF_u") as "%F". inv F.
          }
        - iExFalso. iDestruct "CL4" as "(LXw & _)". iPoseProof (AuthExcls.b_w_eq with "LX LXw") as "%F". inv F.
      }
      iSplitR.
      { (* AU. *)
        subst R0 Q0. iEval (red_tl_all; simpl). iIntros "(LX & LIVE_l & DUTY)".
        iInv "INV_CL" as "CL" "INV_CL_CLOSE".
        iEval (unfold clientSpinlock2_inv; simpl; red_tl_all; simpl) in "CL".
        iDestruct "CL" as "[CL1 | [CL2 | [CL3 | CL4]]]".
        - iDestruct "CL1" as "(LXw & PTD & #PROM_l & LIVE_l2 & PC_spin & DUTY2 & LO_l)".
          iMod (AuthExcls.b_w_update _ _ _ 1 with "LX LXw") as "[LX LXw]".
          iMod (alloc_obligation ℓl 2) as "(%κw & #LO_w & PC_w)".
          iMod (OneShots.alloc) as "[%γκw LIVE_w]".
          iEval (replace 1%Qp with (1/2 + 1/2)%Qp by apply Qp.div_2) in "LIVE_w".
          iPoseProof (OneShots.pending_split with "LIVE_w") as "[LIVE_w LIVE_w2]".
          iMod (OneShots.pending_shot _ γκw with "[LIVE_l LIVE_l2]") as "#DEAD_l".
          { iEval (replace 1%Qp with (1/2 + 1/2)%Qp by apply Qp.div_2). iApply (OneShots.pending_merge with "LIVE_l LIVE_l2"). }
          iMod (duty_fulfill with "[DUTY]") as "DUTY".
          { iFrame. iEval (simpl; red_tl_all). iExists _. iEval (red_tl_all). eauto. }
          iPoseProof (pc_split _ _ 1 1 with "PC_w") as "[PC_w PC_w2]".
          iMod (pc_drop _ 1 _ _ 1 _ with "PC_w2") as "PC_w2".
          Unshelve. 1,3: lia.
          iMod (duty_add with "[DUTY PC_w2] []") as "DUTY".
          { iSplitL "DUTY". iFrame. subst ℓl. iFrame. }
          { instantiate (1:= ((∃ (γκu : τ{nat}), ▿ γκw γκu)%S : sProp n)). iModIntro. iEval (simpl; red_tl_all).
            iIntros "[% DEAD_w]". iEval (red_tl_all) in "DEAD_w". iPoseProof "DEAD_w" as "#Dw".
            iModIntro. iExists _. iEval (red_tl_all). iApply "Dw".
          }
          iPoseProof (duty_tpromise with "DUTY") as "#PROM_w".
          { ss. eauto. }
          (* iPoseProof (pc_split _ _ 1 1 with "PC_spin") as "[PC_spin PC_spin2]". *)
          (* iMod (link_new _ _ _ 0 1 with "[PC_spin2]") as "[#LINK_w _]". *)
          (* { subst ℓl ℓL. iSplitR. iApply "LO_w". iFrame. } *)
          iMod ("INV_CL_CLOSE" with "[LXw PTD LIVE_w2 PC_spin DUTY2 LO_l]") as "_".
          { iEval (unfold clientSpinlock2_inv; simpl; red_tl_all; simpl). iRight. iLeft. iFrame.
            iExists κw. iEval (red_tl_all). iExists γκw. iEval (red_tl_all; simpl). iFrame.
            iSplit. auto. iSplit. auto. iExists ℓl. iEval (red_tl). subst. iSplit; auto.
          }
          iModIntro. iFrame. iExists κw. iEval (red_tl). iExists γκw. iEval (red_tl_all; simpl). iFrame. auto.
        - iExFalso. iDestruct "CL2" as "(LXw & _)". iPoseProof (AuthExcls.b_w_eq with "LX LXw") as "%F". inv F.
        - iExFalso. iDestruct "CL3" as "(LXw & _)". iPoseProof (AuthExcls.b_w_eq with "LX LXw") as "%F". inv F.
        - iExFalso. iDestruct "CL4" as "(_ & _ & % & CL4)". iEval (red_tl) in "CL4". iDestruct "CL4" as "[% CL4]".
          iEval (red_tl_all) in "CL4". iDestruct "CL4" as "(D & _)".
          iPoseProof (OneShots.pending_not_shot with "LIVE_l D") as "%F". inv F.
      }
      iSplitR.
      { iModIntro. subst P0 R0. iEval (red_tl_all). iIntros "A". iModIntro. iFrame. }
      { iModIntro. subst P0 R0. iEval (red_tl_all). iIntros "A". iModIntro. iFrame. }
    }

    (* POST. *)
    iEval (red_tl_all). iIntros (_) "[Q EX]". rred2r. subst Q0.
    iEval (red_tl_all) in "Q". iDestruct "Q" as "[%κw Q]". iEval (red_tl_all) in "Q". iDestruct "Q" as "[%γκw Q]".
    iEval (red_tl_all; simpl) in "Q". iDestruct "Q" as "(#DEAD_l & LIVE_w & DUTY & PC)".
    iMod (pc_drop _ 1 _ _ 100 with "PC") as "PC".
    Unshelve. 1,3: lia.
    iApply (wpsim_yieldR_gen2 with "[DUTY PC]").
    3:{ iFrame. iApply pcs_cons_fold. iFrame. }
    1,2: lia.
    iIntros "DUTY _ PCS". iEval (simpl) in "PCS".
    iModIntro. rred2r.
    iInv "INV_CL" as "CL" "INV_CL_CLOSE".
    iEval (unfold clientSpinlock2_inv; simpl; red_tl_all; simpl) in "CL".
    iDestruct "CL" as "[CL1 | [CL2 | [CL3 | CL4]]]".
    { iExFalso. iDestruct "CL1" as "(_ & _ & _ & LIVE_l & _)".
      iPoseProof (OneShots.pending_not_shot with "LIVE_l DEAD_l") as "%F". inv F.
    }
    { iDestruct "CL2" as "(LXw & PTD & %κw0 & CL2)". iEval (red_tl) in "CL2". iDestruct "CL2" as "[%γκw0 CL2]".
      iEval (red_tl_all; simpl) in "CL2". iDestruct "CL2" as "(#PROM_w & LIVE_w2 & #DEAD_l2 & DUTY2 & PC_spin & LO_w)".
      iDestruct "LO_w" as "[% LO]". iEval (red_tl; simpl) in "LO". iPoseProof "LO" as "[#LO %LAY]".
      iPoseProof (OneShots.shot_agree with "DEAD_l DEAD_l2") as "%EQ". subst γκw0.
      iApply (SCMem_store_fun_spec with "[PTD] [-]").
      3:{ iFrame. eauto. }
      lia.
      { pose md_N_ClientSpinlock2_state_tgt. set_solver. }
      iIntros (rv) "PTD". rred2. iApply wpsim_tauR. rred2r.
      iMod (alloc_obligation ℓl 2) as "(%κu & LOu & PCu)".
      iMod (OneShots.alloc) as "[%γκu LIVEu]".
      iPoseProof (OneShots.pending_split with "[LIVEu]") as "[LIVEu LIVEu2]".
      { iEval (rewrite Qp.div_2). iFrame. }
      iEval (replace 2 with (1+1) by lia) in "PCu". iPoseProof (pc_split with "PCu") as "[PCu PCu2]".
      iMod (pc_drop _ 1 _ _ 1 with "PCu2") as "PCu2".
      Unshelve. 1,3: lia.
      iMod (duty_add with "[DUTY2 PCu2] []") as "DUTY2".
      { subst ℓl. iFrame. }
      { instantiate (1:= (▿ γκu 0)%S). iModIntro. iEval (simpl; red_tl_all). iIntros "#A". auto. }
      iPoseProof (duty_tpromise with "DUTY2") as "#PROMu".
      { simpl. eauto. }
      iMod (OneShots.pending_shot with "[LIVE_w LIVE_w2]") as "#DEADw".
      { iEval (rewrite <- (Qp.div_2 1)). iApply (OneShots.pending_merge with "LIVE_w LIVE_w2"). }
      iMod (link_new _ _ _ 0 with "[LOu PC_spin]") as "[#LINKu _]".
      { iSplitL "LOu". iFrame. subst. iFrame. }
      iMod ("INV_CL_CLOSE" with "[LXw PTD LIVEu DUTY2 PCu LIVEu2 EX]") as "_".
      { iEval (unfold clientSpinlock2_inv; simpl; red_tl_all; simpl). do 2 iRight. iLeft. iFrame.
        iExists γκw. iEval (red_tl). iExists κu. iEval (red_tl). iExists γκu. iEval (red_tl_all; simpl).
        iSplitR. auto. iSplitL "LIVEu". iFrame. iSplitR. auto. iSplitR. auto. iSplitR. auto. iLeft. iFrame.
      }
      iMod (duty_fulfill with "[DUTY]") as "DUTY".
      { iFrame. iEval (simpl; red_tl). iExists _. iEval (red_tl_all). eauto. }
      iApply (wpsim_sync with "[DUTY]").
      2:{ iFrame. }
      Unshelve. lia. 2: auto.
      iIntros "DUTY FC". rred2r. iApply wpsim_tauR. rred2r. lred2r.
      iApply wpsim_ret.
      2:{ iModIntro. iFrame. iPureIntro. auto. }
      reflexivity.
    }
    { iDestruct "CL3" as "(LXw & PTD & %γκw0 & CL3)". iEval (red_tl) in "CL3". iDestruct "CL3" as "[%κu CL3]".
      iEval (red_tl) in "CL3". iDestruct "CL3" as "[%γκu CL3]".
      iEval (red_tl_all; simpl) in "CL3". iDestruct "CL3" as "(#PROM_u & LIVE_u & #LINK_u & #DEAD_l2 & #DEAD_w & PASS)".
      iPoseProof (OneShots.shot_agree with "DEAD_l DEAD_l2") as "%EQ". subst γκw0.
      iPoseProof (OneShots.pending_not_shot with "LIVE_w DEAD_w") as "%F". inv F.
    }
    { iDestruct "CL4" as "(LXw & PTD & %γκw0 & CL4)". iEval (red_tl) in "CL4". iDestruct "CL4" as "[%γκu CL4]".
      iEval (red_tl_all; simpl) in "CL4". iDestruct "CL4" as "(#DEAD_l2 & #DEAD_w & _)".
      iPoseProof (OneShots.shot_agree with "DEAD_l DEAD_l2") as "%EQ". subst γκw0.
      iPoseProof (OneShots.pending_not_shot with "LIVE_w DEAD_w") as "%F". inv F.
    }
  Qed.

  Lemma not_case4 n γX γκl γr :
    (○ γX 0) ∗ (D ↦ 1) ∗ (∃ x : nat, ⟦ ∃ γκu : τ{nat}, (▿ γκl x) ∗ (▿ x γκu) ∗ (▿ γr 0) ∗ (▿ γκu 0), n ⟧)
             ⊢ △ γr 1 -∗ ⌜False⌝%I.
  Proof.
    iIntros "CL4 Lr".
    iDestruct "CL4" as "(LXw & PTD & %γκw0 & CL4)". iEval (red_tl) in "CL4". iDestruct "CL4" as "[%γκu CL4]".
    iEval (red_tl_all; simpl) in "CL4". iDestruct "CL4" as "(_ & _ & Dr & _)".
    iPoseProof (OneShots.pending_not_shot with "Lr Dr") as "%F". inv F.
  Qed.

  Lemma data_case3 n γX κs γκl tid2 ℓl γe γr :
    ((○ γX 1) ∗ (D ↦ 1) ∗
              (∃ x : nat,
                  ⟦ ∃ κu γκu : τ{nat, n}, -[κu](0)-◇ (▿ γκu 0) ∗ (△ γκu (1 / 2)) ∗ κu -(0)-◇ κs ∗ (▿ γκl x) ∗ (▿ x γκu) ∗
                                                                                           (Duty(tid2) [(κu, 0, ▿ γκu 0)] ∗ ◇[κu](ℓl, 1) ∗ (△ γκu (1 / 2)) ∗ (EX γe ()) ∨ (▿ γr 0)), n ⟧))
      ⊢ (△ γr 1) ==∗ (∃ γκw κu γκu, 
                         ⟦ (-[κu](0)-◇ (▿ γκu 0) ∗ κu -(0)-◇ κs ∗ (▿ γκl γκw) ∗ (▿ γκw γκu) ∗ (Duty(tid2) [(κu, 0, ▿ γκu 0)] ∗ ◇[κu](ℓl, 1) ∗ (△ γκu (1 / 2)) ∗ (EX γe ())))%S, n⟧) ∗ (▿ γr 0) ∗
      ((○ γX 1) ∗ (D ↦ 1) ∗
                (∃ x : nat,
                    ⟦ ∃ κu γκu : τ{nat, n}, -[κu](0)-◇ (▿ γκu 0) ∗ (△ γκu (1 / 2)) ∗ κu -(0)-◇ κs ∗ (▿ γκl x) ∗ (▿ x γκu) ∗
                                                                                             (Duty(tid2) [(κu, 0, ▿ γκu 0)] ∗ ◇[κu](ℓl, 1) ∗ (△ γκu (1 / 2)) ∗ (EX γe ()) ∨ (▿ γr 0)), n ⟧)).
  Proof.
    iIntros "CL3 Lr".
    iDestruct "CL3" as "(LXw & PTD & %γκw & CL3)". iEval (red_tl) in "CL3". iDestruct "CL3" as "[%κu CL3]".
    iEval (red_tl) in "CL3". iDestruct "CL3" as "[%γκu CL3]".
    iEval (red_tl_all; simpl) in "CL3". iDestruct "CL3" as "(#PROM_u & LIVE_u & #LINK_u & #DEAD_l2 & #DEAD_w2 & [PASS | Dr])".
    2:{ iPoseProof (OneShots.pending_not_shot with "Lr Dr") as "%F". inv F. }
    iMod (OneShots.pending_shot _ 0 with "Lr") as "#Dr". iModIntro.
    iFrame. iSplitL "PASS".
    { iExists γκw, κu, γκu. iEval (red_tl_all; simpl). iFrame. eauto. }
    { iSplitR. auto. iExists _. iEval (red_tl). iExists _. iEval (red_tl). iExists _. iEval (red_tl_all; simpl).
      iFrame. iSplit. auto. iSplit. auto. iSplit. auto. iSplit. auto. iRight. auto.
    }
  Qed.

  Lemma data_case3_after n tid2 ℓL ℓl γX γe κs κl γκl γr γκw γκu :
    ⊢
      (▿ γκl γκw)
      -∗
      (▿ γκw γκu)
      -∗
      (▿ γr 0)
      -∗
      (△ γκu (1 / 2))
      -∗
      (prop n (clientSpinlock2_inv n tid2 ℓL ℓl γX γe κs κl γκl γr))
      -∗
      ((○ γX 1) ∗ (D ↦ 1) ∗ (△ γκu (1/2)) ∗ (△ γκu (1/2))).
  Proof.
    iIntros "#Dl #Dw #Dr Lu CL".
    iEval (unfold clientSpinlock2_inv; simpl; red_tl_all; simpl) in "CL".
    iDestruct "CL" as "[CL1 | [CL2 | [CL3 | CL4]]]".
    - iDestruct "CL1" as "(_ & _ & _ & Ll & _)".
      iPoseProof (OneShots.pending_not_shot with "Ll Dl") as "%F". inv F.
    - iDestruct "CL2" as "(_ & _ & % & CL2)".
      iEval (red_tl) in "CL2". iDestruct "CL2" as "(% & CL2)".
      iEval (red_tl_all; simpl) in "CL2". iDestruct "CL2" as "(_ & Lw & #Dl2 & _)".
      iPoseProof (OneShots.shot_agree with "Dl Dl2") as "%EQ". subst x0.
      iPoseProof (OneShots.pending_not_shot with "Lw Dw") as "%F". inv F.
    - iDestruct "CL3" as "(LXw & PTD & % & CL2)".
      iEval (red_tl) in "CL2". iDestruct "CL2" as "(% & CL2)".
      iEval (red_tl) in "CL2". iDestruct "CL2" as "(% & CL2)".
      iEval (red_tl_all; simpl) in "CL2". iDestruct "CL2" as "(_ & Lu2 & _ & Dl2 & Dw2 & _)".
      iPoseProof (OneShots.shot_agree with "Dl Dl2") as "%EQ". subst x.
      iPoseProof (OneShots.shot_agree with "Dw Dw2") as "%EQ". subst x1.
      iFrame.
    - iDestruct "CL4" as "(_ & _ & % & CL4)".
      iEval (red_tl) in "CL4". iDestruct "CL4" as "(% & CL4)".
      iEval (red_tl_all; simpl) in "CL4". iDestruct "CL4" as "(Dl2 & Dw2 & Dr2 & Du)".
      iPoseProof (OneShots.shot_agree with "Dl Dl2") as "%EQ". subst x.
      iPoseProof (OneShots.shot_agree with "Dw Dw2") as "%EQ". subst x0.
      iPoseProof (OneShots.pending_not_shot with "Lu Du") as "%F". inv F.
  Qed.

  Lemma loop_case3_in
        (tid2 n ℓL ℓl : nat)
        (LAYER_L : ℓL = 3)
        (LAYER_l : ℓl = 2)
        (γX γe κs κl γκl γr : nat)
        (γκw κu γκu : nat)
    :
    ⊢
      (inv n N_ClientSpinlock2 (clientSpinlock2_inv n tid2 ℓL ℓl γX γe κs κl γκl γr))
      -∗
      (⟦(syn_tgt_interp_as n sndl (λ m : SCMem.t, s_memory_black m))%S, 1+n⟧)
      -∗
      (⟦ isSpinlock n X γX γe κs ℓL, n ⟧)
      -∗
      (⟦((TID(tid2))
           ∗
           (-[κu](0)-◇ (▿ γκu 0)%S)
           ∗
           (κu -(0)-◇ κs)
           ∗
           (▿ γκl γκw)
           ∗
           (▿ γκw γκu)
           ∗
           (△ γκu (1 / 2))
           ∗
           (EX γe ())
           ∗
           (▿ γr 0)
           ∗
           (Duty(tid2) [(κu, 0, (▿ γκu 0)%S)])
           ∗
           (◇{([(κu, 0)])%S}(1, 9)))%S, n⟧)
      -∗
  ⟦(syn_wpsim (S n) tid2 ⊤ (λ rs rt : Any.t, ( ⤉ syn_term_cond n tid2 Any.t rs rt)) false true
    (trigger Yield;;; ` x : SCMem.val <- Ret (SCMem.val_nat 0);; Ret (Any.upcast x))
    (` r : SCMem.val <- map_event (OMod.emb_callee omod (SCMem.mod gvs)) (SCMem.load_fun D);;
     ` x : Any.t <- map_event (OMod.emb_callee omod (SCMem.mod gvs)) (Ret (Any.upcast r));;
     ` x0 : SCMem.val <- (tau;; unwrap (Any.downcast x));;
     ` x1 : () + () <-
     OMod.close_itree omod (SCMem.mod gvs)
       (` b : bool <- OMod.call "compare" (x0, 1 : SCMem.val);; ` r0 : () + () <- (if b then Ret (inr ()) else Ret (inl ()));; Ret r0);;
     OMod.close_itree omod (SCMem.mod gvs)
       match x1 with
       | inl l =>
           tau;; ITree.iter
                   (λ _ : (),
                      ` d : SCMem.val <- OMod.call "load" D;;
                      ` b : bool <- OMod.call "compare" (d, 1 : SCMem.val);;
                      ` r0 : () + () <- (if b then Ret (inr ()) else Ret (inl ()));; Ret r0) l
       | inr r0 => Ret r0
       end;;;
     ` x3 : SCMem.val <- OMod.close_itree omod (SCMem.mod gvs) ((trigger Yield;;; Spinlock.unlock X);;; trigger Yield;;; Ret (0 : SCMem.val));;
            OMod.close_itree omod (SCMem.mod gvs) (Ret (Any.upcast x3))))%S, 1+n⟧.
  Proof.
    iEval (red_tl_all; rewrite red_syn_tgt_interp_as; rewrite red_syn_wpsim; simpl).
    iIntros "#INV_CL #MEM #ISL (TID & #PRu & #LINKu & #Dl & #Dw & Lu & EX & #Dr & DUTY & PCS)".
    iInv "INV_CL" as "CL" "INV_CL_CLOSE".
    iPoseProof (data_case3_after with "Dl Dw Dr Lu CL") as "(LXw & PTD & Lu1 & Lu2)".
    iApply (SCMem_load_fun_spec with "[PTD] [-]").
    3:{ iSplitR. auto. iFrame. }
    lia.
    { pose md_N_ClientSpinlock2_state_tgt. set_solver. }
    iIntros (rv) "[%RV PTD]". subst rv. rred2r. iApply wpsim_tauR. rred2r.
    iMod ("INV_CL_CLOSE" with "[LXw Lu2 PTD]") as "_".
    { iEval (unfold clientSpinlock2_inv; simpl; red_tl_all; simpl). do 2 iRight. iLeft. iFrame.
      iExists _. iEval (red_tl). iExists _. iEval (red_tl). iExists _. iEval (red_tl_all; simpl).
      iFrame. do 4 (iSplitR; [eauto | ]). iRight. auto.
    }
    iApply (wpsim_yieldR2 with "[DUTY PCS]").
    3:{ iFrame. iFrame. }
    1,2: lia.
    iIntros "DUTY _ PCS". rred2r. 
    iApply (SCMem_compare_fun_spec). auto. set_solver. simpl.
    iApply (tgt_interp_as_equiv with "MEM").
    { iIntros (a). iStartProof. simpl; red_tl_all; simpl. iSplit.
      { iIntros "MB"; iSplit; iFrame. iPureIntro; auto. }
      { iIntros "[MB _]"; iFrame. }
    }
    iIntros (rv) "[%EQ1 _]". specialize (EQ1 eq_refl). subst rv.
    rred2r. iApply wpsim_tauR. rred2r.
    iApply (wpsim_yieldR2 with "[DUTY PCS]").
    3:{ iFrame. }
    1,2: lia.
    iIntros "DUTY _ PCS". rred2r. iApply wpsim_tauR. rred2r.

    (* Unlock. *)
    iPoseProof ((Spinlock_unlock_spec tid2 n ⊤) $! X γX γe κs ℓL) as "SPEC".
    set (P0 := ((△ γκu (1/2)))%S : sProp n).
    set (R0 := ((△ γκu (1/2)) ∗ Duty(tid2) [(κu, 0, (▿ γκu 0)%S)])%S : sProp n).
    set (Q0 := ((▿ γκu 0) ∗ Duty(tid2) [])%S : sProp n).
    iSpecialize ("SPEC" $! _ P0 R0 Q0).
    iEval (simpl) in "PCS". iMod (pcs_decr _ _ 1 0 with "PCS") as "[PCS _]".
    lia.
    iApply ("SPEC" with "[EX Lu1 DUTY PCS] [-]").
    { subst P0 R0 Q0. iEval (red_tl_all; simpl). do 2 (iSplitR; [auto | ]). iFrame. iFrame.
      iSplitR.
      { iIntros "(LX & Lu & DUTY)". iInv "INV_CL" as "CL" "INV_CL_CLOSE".
        iPoseProof (data_case3_after with "Dl Dw Dr Lu CL") as "(LXw & PTD & Lu1 & Lu2)".
        iMod (AuthExcls.b_w_update _ _ _ 0 with "LX LXw") as "[LX LXw]".
        iMod (OneShots.pending_shot _ 0 with "[Lu1 Lu2]") as "#Du".
        { iEval (replace 1%Qp with (1/2 + 1/2)%Qp by apply Qp.div_2). iApply (OneShots.pending_merge with "Lu1 Lu2"). }
        iMod ("INV_CL_CLOSE" with "[LXw PTD]") as "_".
        { iEval (unfold clientSpinlock2_inv; simpl; red_tl_all; simpl). do 3 iRight. iFrame.
          iExists γκw. iEval (red_tl). iExists γκu. iEval (red_tl_all). auto.
        }
        iMod (duty_fulfill with "[DUTY]") as "DUTY".
        { iFrame. iEval (simpl; red_tl_all). auto. }
        iModIntro. iFrame. auto.
      }
      iSplitR.
      { iModIntro. iIntros "(Lu & DUTY)". iModIntro. iFrame. }
      { iModIntro. iIntros "(Lu & DUTY)". iModIntro. iFrame. }
    }
    subst Q0. iEval (red_tl_all; simpl). iIntros (_) "[Du DUTY]". rred2r.
    iApply (wpsim_sync with "[DUTY]").
    2:{ iFrame. }
    lia.
    iIntros "DUTY _". rred2r. iApply wpsim_tauR. rred2r. lred2r.
    iApply wpsim_ret.
    2:{ iModIntro. iFrame. iPureIntro. auto. }
    reflexivity.
  Qed.

  Lemma loop_case3
        (tid2 n ℓL ℓl : nat)
        (LAYER_L : ℓL = 3)
        (LAYER_l : ℓl = 2)
        (γX γe κs κl γκl γr : nat)
        (γκw κu γκu : nat)
    :
    ⊢
      (inv n N_ClientSpinlock2 (clientSpinlock2_inv n tid2 ℓL ℓl γX γe κs κl γκl γr))
      -∗
      (⟦(syn_tgt_interp_as n sndl (λ m : SCMem.t, s_memory_black m))%S, 1+n⟧)
      -∗
      (⟦ isSpinlock n X γX γe κs ℓL, n ⟧)
      -∗
      (⟦((TID(tid2))
           ∗
           (-[κu](0)-◇ (▿ γκu 0)%S)
           ∗
           (κu -(0)-◇ κs)
           ∗
           (▿ γκl γκw)
           ∗
           (▿ γκw γκu)
           ∗
           (△ γκu (1 / 2))
           ∗
           (EX γe ())
           ∗
           (▿ γr 0)
           ∗
           (Duty(tid2) [(κu, 0, (▿ γκu 0)%S)])
           ∗
           (◇{([(κu, 0)])%S}(1, 10)))%S, n⟧)
      -∗
      ⟦(syn_wpsim (S n) tid2 ⊤ (λ rs rt : Any.t, (⤉ syn_term_cond n tid2 Any.t rs rt)) false true
                  (trigger Yield;;; x <- Ret (0 : SCMem.val);; Ret (Any.upcast x))
                  (OMod.close_itree omod (SCMem.mod gvs)
                                    (ITree.iter
                                       (λ _ : (),
                                           ` d : SCMem.val <- OMod.call "load" D;;
                                                 ` b : bool <- OMod.call "compare" (d, 1 : SCMem.val);; ` r : () + () <- (if b then Ret (inr ()) else Ret (inl ()));; Ret r) ());;;
                                    ` x : SCMem.val <- OMod.close_itree omod (SCMem.mod gvs) ((trigger Yield;;; Spinlock.unlock X);;; trigger Yield;;; Ret (0 : SCMem.val));;
                                          OMod.close_itree omod (SCMem.mod gvs) (Ret (Any.upcast x)))
       )%S, 1+n⟧
  .
  Proof.
    iEval (red_tl_all; rewrite red_syn_tgt_interp_as; rewrite red_syn_wpsim; simpl).
    iIntros "#INV_CL #MEM #ISL (TID & #PRu & #LINKu & #Dl & #Dw & Lu & EX & #Dr & DUTY & PC)".
    iEval (rewrite unfold_iter_eq). rred2r.
    iApply (wpsim_yieldR2 with "[DUTY PC]").
    3:{ iFrame. iFrame. }
    1,2: lia.
    iIntros "DUTY _ PCS". rred2r.
    iPoseProof (loop_case3_in with "INV_CL [MEM] ISL [-]") as "SIM".
    5:{ iEval (rewrite red_syn_wpsim) in "SIM". iFrame. }
    1,2: auto.
    { iEval (rewrite red_syn_tgt_interp_as). auto. }
    iEval (red_tl_all; simpl). iFrame. eauto.
  Qed.

  Lemma data_case2 n γX γκl tid2 κs ℓL :
    ((○ γX 1) ∗ (D ↦ 0) ∗
              (∃ x : nat,
                  ⟦ ∃ γκw : τ{nat}, -[x](0)-◇ (∃ γκu : τ{nat}, ▿ γκw γκu) ∗ (△ γκw (1 / 2)) ∗ (▿ γκl γκw) ∗ Duty(tid2) [] ∗ ◇[κs](ℓL, 1) ∗
                                            (∃ ℓw : τ{nat}, ◆[x, ℓw] ∗ ⌜ℓw ≤ ℓL⌝), n ⟧))
      ⊢
      ((○ γX 1) ∗ (D ↦ 0) ∗
                (∃ κw γκw,
                    ⟦ (-[κw](0)-◇ (∃ γκu : τ{nat}, ▿ γκw γκu) ∗ (△ γκw (1 / 2)) ∗ (▿ γκl γκw) ∗ Duty(tid2) [] ∗ ◇[κs](ℓL, 1) ∗
                                  (∃ ℓw : τ{nat}, ◆[κw, ℓw] ∗ ⌜ℓw ≤ ℓL⌝))%S, n ⟧)).
  Proof.
    iIntros "CL2". iDestruct "CL2" as "(LXw & PTD & %κw & CL2)". iEval (red_tl) in "CL2". iDestruct "CL2" as "[%γκw CL2]".
    iEval (red_tl_all; simpl) in "CL2". iDestruct "CL2" as "(#PROM_w & LIVE_w & #DEAD_l & DUTY2 & PC_spin & LO_w)".
    iFrame. iExists κw, γκw. iEval (red_tl_all; simpl). iFrame. eauto.
  Qed.

  Lemma loop_case2
        (tid2 n ℓL ℓl : nat)
        (LAYER_L : ℓL = 3)
        (LAYER_l : ℓl = 2)
        (γX γe κs κl γκl γr κw ℓw : nat)
        (γκw : nat)
        (LAYw : ℓw ≤ ℓL)
    :
    ⊢
      (inv n N_ClientSpinlock2 (clientSpinlock2_inv n tid2 ℓL ℓl γX γe κs κl γκl γr))
      -∗
      (⟦(syn_tgt_interp_as n sndl (λ m : SCMem.t, s_memory_black m))%S, 1+n⟧)
      -∗
      (⟦ isSpinlock n X γX γe κs ℓL, n ⟧)
      -∗
      (⟦(-[κw](0)-◇ (∃ γκu : τ{nat}, ▿ γκw γκu))%S, n⟧)
      -∗
      (▿ γκl γκw)
      -∗
      (◆[κw, ℓw])
      -∗
      (own_thread tid2)
      -∗
      (△ γr 1)
      -∗
      ((○ γX 1) ∗ (D ↦ 0) ∗
                (∃ x : nat,
                    ⟦ ∃ γκw0 : τ{nat}, -[x](0)-◇ (∃ γκu : τ{nat}, ▿ γκw0 γκu) ∗ (△ γκw0 (1 / 2)) ∗ (▿ γκl γκw0) ∗ Duty(tid2) [] ∗ ◇[κs](ℓL, 1) ∗
                                               (∃ ℓw : τ{nat}, ◆[x, ℓw] ∗ ⌜ℓw ≤ ℓL⌝), n ⟧))
      -∗
      (prop n (clientSpinlock2_inv n tid2 ℓL ℓl γX γe κs κl γκl γr) =| S n |={ ⊤ ∖ ↑N_ClientSpinlock2, ⊤ }=∗ emp)
      -∗
      ⟦(syn_wpsim (S n) tid2 (⊤ ∖ ↑N_ClientSpinlock2) (λ rs rt : Any.t, (⤉ syn_term_cond n tid2 Any.t rs rt)) false true
                  (trigger Yield;;; ` x : SCMem.val <- Ret (0 : SCMem.val);; Ret (Any.upcast x))
                  (OMod.close_itree omod (SCMem.mod gvs)
                                    (ITree.iter
                                       (λ _ : (),
                                           ` d : SCMem.val <- OMod.call "load" D;;
                                                 ` b : bool <- OMod.call "compare" (d, 1 : SCMem.val);; ` r : () + () <- (if b then Ret (inr ()) else Ret (inl ()));; Ret r) ());;;
                                    ` x : SCMem.val <- OMod.close_itree omod (SCMem.mod gvs) ((trigger Yield;;; Spinlock.unlock X);;; trigger Yield;;; Ret (0 : SCMem.val));;
                                          OMod.close_itree omod (SCMem.mod gvs) (Ret (Any.upcast x))))%S, 1+n⟧
  .
  Proof.
    iEval (red_tl_all; rewrite red_syn_tgt_interp_as; rewrite red_syn_wpsim; simpl).
    iIntros "#INV_CL #MEM #ISL #PRw #Dl #LOw TID Lr CL2 INV_CL_CLOSE".
    iRevert "TID Lr CL2 INV_CL_CLOSE". iMod (tpromise_ind2 with "[] []") as "IH".
    { eauto. }
    2:{ iApply "IH". }
    iSplit; iModIntro.
    2:{ iEval (simpl; red_tl_all; simpl). iIntros "#[% Dw]".
        iEval (red_tl_all) in "Dw".
        iModIntro. iIntros "_ _ CL2". iExFalso.
        iPoseProof (data_case2 with "CL2") as "(LXw & PTD & % & % & CL2)".
        iEval (red_tl_all; simpl) in "CL2".
        iDestruct "CL2" as "(_ & Lw & #Dl2 & DUTY & PCspin & _)".
        iPoseProof (OneShots.shot_agree with "Dl Dl2") as "%EQ". subst γκw0. iClear "Dl2".
        iPoseProof (OneShots.pending_not_shot with "Lw Dw") as "%F". inv F.
    }
    iIntros "IH". iModIntro. iIntros "TID Lr CL2 INV_CL_CLOSE".
    iPoseProof (data_case2 with "CL2") as "(LXw & PTD & % & % & CL2)".
    iEval (red_tl_all; simpl) in "CL2".
    iDestruct "CL2" as "(_ & Lw & #Dl2 & DUTY & PCspin & _)".
    iPoseProof (OneShots.shot_agree with "Dl Dl2") as "%EQ". subst γκw0. iClear "Dl2".
    iEval (rewrite unfold_iter_eq). rred2r.
    iApply (wpsim_yieldR_gen with "[DUTY]").
    2:{ iFrame. }
    auto.
    iIntros "DUTY FC".
    iMod ("INV_CL_CLOSE" with "[LXw PTD Lw PCspin DUTY]") as "_".
    { iEval (unfold clientSpinlock2_inv; simpl; red_tl_all; simpl). do 1 iRight. iLeft. iFrame.
      iExists _. iEval (red_tl). iExists _. iEval (red_tl_all; simpl). iFrame. do 2 (iSplit; [auto|]).
      iExists _. iEval (red_tl; simpl). eauto.
    }
    iModIntro. rred2r.
    iInv "INV_CL" as "CL" "INV_CL_CLOSE".
    iEval (unfold clientSpinlock2_inv; simpl; red_tl_all; simpl) in "CL".
    iDestruct "CL" as "[CL1 | [CL2 | [CL3 | CL4]]]".
    4:{ iPoseProof (not_case4 with "CL4 Lr") as "%F". inv F. }
    1:{ iExFalso. iDestruct "CL1" as "(_ & _ & _ & Ll & _)".
        iPoseProof (OneShots.pending_not_shot with "Ll Dl") as "%F". inv F.
    }
    2:{ iClear "IH". 
        iMod (data_case3 with "CL3 Lr") as "((%γκw0 & %κu & %γκu & A) & Dr & CL3)".
        iMod ("INV_CL_CLOSE" with "[CL3]") as "_".
        { iEval (unfold clientSpinlock2_inv; simpl; red_tl_all; simpl). do 2 iRight. iLeft. iFrame. }
        iEval (red_tl_all; simpl) in "A". iDestruct "A" as "(PRu & LINKu & Dl2 & Dw & DUTY & PC & Lu & EX)".
        iMod (pc_drop _ 1 _ _ 9 with "PC") as "PC".
        Unshelve. 1,3: subst; auto.
        iPoseProof (pcs_cons_fold _ 0 [] 1 9 with "[PC]") as "PCS".
        { iFrame. }
        iPoseProof (OneShots.shot_agree with "Dl Dl2") as "%EQ". subst γκw0.
        iPoseProof (loop_case3_in with "INV_CL [MEM] ISL [-]") as "SIM".
        5:{ iEval (rewrite red_syn_wpsim) in "SIM". iFrame. }
        1,2: auto.
        { iEval (rewrite red_syn_tgt_interp_as). auto. }
        iEval (red_tl_all; simpl).
        iSplitL "TID"; [done|]. iSplitL "PRu"; [iApply "PRu"|]. iFrame.
    }
    iPoseProof (data_case2 with "CL2") as "(LXw & PTD & % & % & CL2)".
    iEval (red_tl_all; simpl) in "CL2".
    iDestruct "CL2" as "(_ & Lw & #Dl2 & DUTY & PCspin & _)".
    iPoseProof (OneShots.shot_agree with "Dl Dl2") as "%EQ". subst γκw0. iClear "Dl2".
    iApply (SCMem_load_fun_spec with "[PTD] [-]").
    3:{ iFrame. auto. }
    auto.
    { pose md_N_ClientSpinlock2_state_tgt. set_solver. }
    iIntros (rv) "[%RV PTD]". subst rv.
    rred2r. iApply wpsim_tauR. rred2r.
    iApply (wpsim_yieldR_gen with "[DUTY]").
    2:{ iFrame. }
    auto.
    iIntros "DUTY _".
    iMod ("INV_CL_CLOSE" with "[LXw PTD Lw PCspin DUTY]") as "_".
    { iEval (unfold clientSpinlock2_inv; simpl; red_tl_all; simpl). do 1 iRight. iLeft. iFrame.
      iExists _. iEval (red_tl). iExists _. iEval (red_tl_all; simpl). iFrame. do 2 (iSplit; [auto|]).
      iExists _. iEval (red_tl; simpl). eauto.
    }
    iModIntro. rred2r.
    iApply (SCMem_compare_fun_spec).
    2: set_solver.
    2:{ simpl. iApply (tgt_interp_as_equiv with "MEM"). iIntros (a). iStartProof.
        simpl; red_tl_all; simpl. iSplit.
        { iIntros "MB"; iSplit; iFrame. iPureIntro; auto. }
        { iIntros "[MB _]"; iFrame. }
    }
    auto.
    iIntros (rv) "[_ %RES]". exploit RES. auto. intros. subst rv. clear RES.
    rred2r. iApply wpsim_tauR. rred2r. iApply wpsim_tauR.
    iMod ("IH" with "FC") as "IH".
    iInv "INV_CL" as "CL" "INV_CL_CLOSE".
    iEval (unfold clientSpinlock2_inv; simpl; red_tl_all; simpl) in "CL".
    iDestruct "CL" as "[CL1 | [CL2 | [CL3 | CL4]]]".
    4:{ iPoseProof (not_case4 with "CL4 Lr") as "%F". inv F. }
    1:{ iExFalso. iDestruct "CL1" as "(_ & _ & _ & Ll & _)".
        iPoseProof (OneShots.pending_not_shot with "Ll Dl") as "%F". inv F.
    }
    { iApply ("IH" with "TID Lr CL2 INV_CL_CLOSE"). }
    { iClear "IH". 
      iMod (data_case3 with "CL3 Lr") as "((%γκw0 & %κu & %γκu & A) & Dr & CL3)".
      iMod ("INV_CL_CLOSE" with "[CL3]") as "_".
      { iEval (unfold clientSpinlock2_inv; simpl; red_tl_all; simpl). do 2 iRight. iLeft. iFrame. }
      iEval (red_tl_all; simpl) in "A". iDestruct "A" as "(PRu & LINKu & Dl2 & Dw & DUTY & PC & Lu & EX)".
      iPoseProof (OneShots.shot_agree with "Dl Dl2") as "%EQ". subst γκw0. iClear "Dl2".
      iMod (pc_drop _ 1 _ _ 10 with "PC") as "PC".
      Unshelve. 1,3: subst; auto.
      iPoseProof (pcs_cons_fold _ 0 [] 1 10 with "[PC]") as "PCS".
      { iFrame. }
      iPoseProof (loop_case3 with "INV_CL [MEM] ISL [-]") as "SIM".
      5:{ iEval (rewrite red_syn_wpsim) in "SIM". iFrame. }
      1,2: auto.
      { iEval (rewrite red_syn_tgt_interp_as). auto. }
      iEval (red_tl_all; simpl).
      iSplitL "TID"; [done|]. iSplitL "PRu"; [iApply "PRu"|]. iFrame. auto.
    }
  Qed.

  Lemma loop_case1
        (tid2 n ℓL ℓl : nat)
        (LAYER_L : ℓL = 3)
        (LAYER_l : ℓl = 2)
        (γX γe κs κl γκl γr ℓl0 : nat)
    :
    ⊢
      (inv n N_ClientSpinlock2 (clientSpinlock2_inv n tid2 ℓL ℓl γX γe κs κl γκl γr))
      -∗
      (⟦(syn_tgt_interp_as n sndl (λ m : SCMem.t, s_memory_black m))%S, 1+n⟧)
      -∗
      (⟦ isSpinlock n X γX γe κs ℓL, n ⟧)
      -∗
      (⟦(-[κl](0)-◇ (∃ γκw : τ{nat}, ▿ γκl γκw))%S, n⟧)
      -∗
      (◆[κl, ℓl0])
      -∗
      (own_thread tid2)
      -∗
      (△ γr 1)
      -∗
      (⟦((○ γX 0) ∗ (D ↦ 0) ∗ (-[κl](0)-◇ ((∃ γκw : τ{nat}, ▿ γκl γκw)%S : sProp n)) ∗ (△ γκl (1 / 2)) ∗ Duty(tid2) [] ∗ ◇[κs](ℓL, 1) ∗
                  (∃ x : τ{nat}, ◆[κl, x]))%S, n⟧)
      -∗
      (prop n (clientSpinlock2_inv n tid2 ℓL ℓl γX γe κs κl γκl γr) =| S n |={ ⊤ ∖ ↑N_ClientSpinlock2, ⊤ }=∗ emp)
      -∗
      ⟦(syn_wpsim (S n) tid2 (⊤ ∖ ↑N_ClientSpinlock2) (λ rs rt : Any.t, (⤉ syn_term_cond n tid2 Any.t rs rt)) false true
                  (trigger Yield;;; ` x : SCMem.val <- Ret (0 : SCMem.val);; Ret (Any.upcast x))
                  (OMod.close_itree omod (SCMem.mod gvs)
                                    (ITree.iter
                                       (λ _ : (),
                                           ` d : SCMem.val <- OMod.call "load" D;;
                                                 ` b : bool <- OMod.call "compare" (d, 1 : SCMem.val);; ` r : () + () <- (if b then Ret (inr ()) else Ret (inl ()));; Ret r) ());;;
                                    ` x : SCMem.val <- OMod.close_itree omod (SCMem.mod gvs) ((trigger Yield;;; Spinlock.unlock X);;; trigger Yield;;; Ret (0 : SCMem.val));;
                                          OMod.close_itree omod (SCMem.mod gvs) (Ret (Any.upcast x))))%S, 1+n⟧
  .
  Proof.
    iEval (red_tl_all; rewrite red_syn_tgt_interp_as; rewrite red_syn_wpsim; simpl).
    iIntros "#INV_CL #MEM #ISL #PRl #LOl TID Lr CL1 INV_CL_CLOSE".
    iRevert "TID Lr CL1 INV_CL_CLOSE". iMod (tpromise_ind2 κl with "[] []") as "IH".
    { eauto. }
    2:{ iApply "IH". }
    iSplit; iModIntro.
    2:{ iEval (simpl; red_tl_all; simpl). iIntros "#[% Dl]".
        iEval (red_tl_all) in "Dl".
        iModIntro. iIntros "_ _ CL1". iExFalso.
        iDestruct "CL1" as "(LXw & PTD & _ & Ll & DUTY & PCspin & _)".
        iPoseProof (OneShots.pending_not_shot with "Ll Dl") as "%F". inv F.
    }
    iIntros "IH". iModIntro. iIntros "TID Lr CL1 INV_CL_CLOSE".
    iDestruct "CL1" as "(LXw & PTD & _ & Ll & DUTY & PCspin & _)".
    iEval (rewrite unfold_iter_eq). rred2r.
    iApply (wpsim_yieldR_gen with "[DUTY]").
    2:{ iFrame. }
    auto.
    iIntros "DUTY FC".
    iMod ("INV_CL_CLOSE" with "[LXw PTD Ll PCspin DUTY]") as "_".
    { iEval (unfold clientSpinlock2_inv; simpl; red_tl_all; simpl). iLeft. iFrame. auto. }
    iModIntro. rred2r.
    iInv "INV_CL" as "CL" "INV_CL_CLOSE".
    iEval (unfold clientSpinlock2_inv; simpl; red_tl_all; simpl) in "CL".
    iDestruct "CL" as "[CL1 | [CL2 | [CL3 | CL4]]]".
    4:{ iPoseProof (not_case4 with "CL4 Lr") as "%F". inv F. }
    3:{ iClear "IH". 
        iMod (data_case3 with "CL3 Lr") as "((%γκw & %κu & %γκu & A) & Dr & CL3)".
        iMod ("INV_CL_CLOSE" with "[CL3]") as "_".
        { iEval (unfold clientSpinlock2_inv; simpl; red_tl_all; simpl). do 2 iRight. iLeft. iFrame. }
        iEval (red_tl_all; simpl) in "A". iDestruct "A" as "(PRu & LINKu & Dl & Dw & DUTY & PC & Lu & EX)".
        iMod (pc_drop _ 1 _ _ 9 with "PC") as "PC".
        Unshelve. 1,3: subst; auto.
        iPoseProof (pcs_cons_fold _ 0 [] 1 9 with "[PC]") as "PCS".
        { iFrame. }
        iPoseProof (loop_case3_in with "INV_CL [MEM] ISL [-]") as "SIM".
        5:{ iEval (rewrite red_syn_wpsim) in "SIM". iFrame. }
        1,2: auto.
        { iEval (rewrite red_syn_tgt_interp_as). auto. }
        iEval (red_tl_all; simpl).
        iSplitL "TID"; [done|]. iSplitL "PRu"; [iApply "PRu"|]. iFrame.
    }
    2:{ iClear "IH PRl LOl".
        iPoseProof (data_case2 with "CL2") as "(LXw & PTD & % & % & CL2)". iEval (red_tl_all; simpl) in "CL2".
        iDestruct "CL2" as "(#PRw & Lw & #Dl & DUTY & PCspin & (% & LO))".
        iEval (red_tl_all; simpl) in "LO". iDestruct "LO" as "[#LOw %LAYw]".
        iApply (SCMem_load_fun_spec with "[PTD] [-]").
        3:{ iSplitR. auto. iFrame. }
        auto.
        { pose md_N_ClientSpinlock2_state_tgt. set_solver. }
        iIntros (rv) "[%RV PTD]". subst rv. rred2r. iApply wpsim_tauR. rred2r.
        iApply (wpsim_yieldR_gen with "[DUTY]").
        2: iFrame.
        auto.
        iIntros "DUTY _". iMod ("INV_CL_CLOSE" with "[LXw PTD Lw PCspin DUTY]") as "_".
        { iEval (unfold clientSpinlock2_inv; simpl; red_tl_all; simpl). do 1 iRight. iLeft. iFrame.
          iExists _. iEval (red_tl). iExists _. iEval (red_tl_all; simpl). iFrame. do 2 (iSplit; [auto|]).
          iExists _. iEval (red_tl; simpl). eauto.
        }
        iModIntro. rred2r. iApply (SCMem_compare_fun_spec).
        2: set_solver.
        2:{ simpl. iApply (tgt_interp_as_equiv with "MEM"). iIntros (a). iStartProof.
            simpl; red_tl_all; simpl. iSplit.
            { iIntros "MB"; iSplit; iFrame. iPureIntro; auto. }
            { iIntros "[MB _]"; iFrame. }
        }
        auto.
        iIntros (rv) "[_ %RES]". exploit RES. auto. intros. subst rv. clear RES.
        rred2r. iApply wpsim_tauR. rred2r. iApply wpsim_tauR.
        iInv "INV_CL" as "CL" "INV_CL_CLOSE".
        iEval (unfold clientSpinlock2_inv; simpl; red_tl_all; simpl) in "CL".
        iDestruct "CL" as "[CL1 | [CL2 | [CL3 | CL4]]]".
        4:{ iPoseProof (not_case4 with "CL4 Lr") as "%F". inv F. }
        1:{ iExFalso. iDestruct "CL1" as "(_ & _ & _ & Ll & _)".
            iPoseProof (OneShots.pending_not_shot with "Ll Dl") as "%F". inv F.
        }
        { iDestruct "CL2" as "(LXw & PTD & %κw0 & CL2)". iEval (red_tl) in "CL2". iDestruct "CL2" as "[%γκw0 CL2]".
          iEval (red_tl_all; simpl) in "CL2". iDestruct "CL2" as "(_ & Lw & #Dl2 & DUTY & PCspin & _)".
          iPoseProof (OneShots.shot_agree with "Dl Dl2") as "%EQ". subst γκw0. iClear "Dl2".
          iPoseProof (loop_case2 with "INV_CL [MEM] ISL [PRw] Dl LOw TID Lr [LXw PTD Lw DUTY PCspin] [-]") as "SIM".
          8:{ iEval (rewrite red_syn_wpsim) in "SIM". iFrame. }
          1,2,3: subst; auto.
          { iEval (rewrite red_syn_tgt_interp_as). auto. }
          { iEval (red_tl_all). auto. }
          { iFrame. iExists κw. iEval (red_tl). iExists γκw. iEval (red_tl_all; simpl). iFrame. do 2 (iSplit; [auto|]).
            iExists _. iEval (red_tl). eauto.
          }
          done.
        }
        { iMod (data_case3 with "CL3 Lr") as "((%γκw0 & %κu & %γκu & A) & Dr & CL3)".
          iMod ("INV_CL_CLOSE" with "[CL3]") as "_".
          { iEval (unfold clientSpinlock2_inv; simpl; red_tl_all; simpl). do 2 iRight. iLeft. iFrame. }
          iEval (red_tl_all; simpl) in "A". iDestruct "A" as "(PRu & LINKu & Dl2 & Dw & DUTY & PC & Lu & EX)".
          iPoseProof (OneShots.shot_agree with "Dl Dl2") as "%EQ". subst γκw0. iClear "Dl2".
          iMod (pc_drop _ 1 _ _ 10 with "PC") as "PC".
          Unshelve. 1,3: subst; auto.
          iPoseProof (pcs_cons_fold _ 0 [] 1 10 with "[PC]") as "PCS".
          { iFrame. }
          iPoseProof (loop_case3 with "INV_CL [MEM] ISL [-]") as "SIM".
          5:{ iEval (rewrite red_syn_wpsim) in "SIM". iFrame. }
          1,2: auto.
          { iEval (rewrite red_syn_tgt_interp_as). auto. }
          iEval (red_tl_all; simpl).
          iSplitL "TID"; [done|]. iSplitL "PRu"; [iApply "PRu"|]. iFrame. auto.
        }
    }
    iDestruct "CL1" as "(LXw & PTD & _ & Ll & DUTY & PCspin & _)".
    iApply (SCMem_load_fun_spec with "[PTD] [-]").
    3:{ iSplitR. auto. iFrame. }
    auto.
    { pose md_N_ClientSpinlock2_state_tgt. set_solver. }
    iIntros (rv) "[%RV PTD]". subst rv. rred2r. iApply wpsim_tauR. rred2r.
    iApply (wpsim_yieldR_gen with "[DUTY]").
    2: iFrame.
    auto.
    iIntros "DUTY _". iMod ("INV_CL_CLOSE" with "[LXw PTD Ll PCspin DUTY]") as "_".
    { iEval (unfold clientSpinlock2_inv; simpl; red_tl_all; simpl). iLeft. iFrame. auto. }
    iModIntro. rred2r. iApply (SCMem_compare_fun_spec).
    2: set_solver.
    2:{ simpl. iApply (tgt_interp_as_equiv with "MEM"). iIntros (a). iStartProof.
        simpl; red_tl_all; simpl. iSplit.
        { iIntros "MB"; iSplit; iFrame. iPureIntro; auto. }
        { iIntros "[MB _]"; iFrame. }
    }
    auto.
    iIntros (rv) "[_ %RES]". exploit RES. auto. intros. subst rv. clear RES.
    rred2r. iApply wpsim_tauR. rred2r. iApply wpsim_tauR.
    iInv "INV_CL" as "CL" "INV_CL_CLOSE".
    iEval (unfold clientSpinlock2_inv; simpl; red_tl_all; simpl) in "CL".
    iDestruct "CL" as "[CL1 | [CL2 | [CL3 | CL4]]]".
    4:{ iPoseProof (not_case4 with "CL4 Lr") as "%F". inv F. }
    { iMod ("IH" with "FC") as "IH". iApply ("IH" with "TID Lr CL1 INV_CL_CLOSE"). }
    { iClear "IH FC".
      iPoseProof (data_case2 with "CL2") as "(LXw & PTD & % & % & CL2)". iEval (red_tl_all; simpl) in "CL2".
      iDestruct "CL2" as "(#PRw & Lw & #Dl & DUTY & PCspin & (% & LO))".
      iEval (red_tl_all; simpl) in "LO". iDestruct "LO" as "[#LOw %LAYw]".
      iPoseProof (loop_case2 with "INV_CL [MEM] ISL [PRw] Dl LOw TID Lr [LXw PTD Lw DUTY PCspin] [-]") as "SIM".
      8:{ iEval (rewrite red_syn_wpsim) in "SIM". iFrame. }
      1,2,3: subst; auto.
      { iEval (rewrite red_syn_tgt_interp_as). auto. }
      { iEval (red_tl_all). auto. }
      { iFrame. iExists κw. iEval (red_tl). iExists γκw. iEval (red_tl_all; simpl). iFrame. do 2 (iSplit; [auto|]).
        iExists _. iEval (red_tl). eauto.
      }
      done.
    }
    { iClear "IH FC".
      iMod (data_case3 with "CL3 Lr") as "((%γκw & %κu & %γκu & A) & Dr & CL3)".
      iMod ("INV_CL_CLOSE" with "[CL3]") as "_".
      { iEval (unfold clientSpinlock2_inv; simpl; red_tl_all; simpl). do 2 iRight. iLeft. iFrame. }
      iEval (red_tl_all; simpl) in "A". iDestruct "A" as "(PRu & LINKu & Dl & Dw & DUTY & PC & Lu & EX)".
      iMod (pc_drop _ 1 _ _ 10 with "PC") as "PC".
      Unshelve. 1,3: subst; auto.
      iPoseProof (pcs_cons_fold _ 0 [] 1 10 with "[PC]") as "PCS".
      { iFrame. }
      iPoseProof (loop_case3 with "INV_CL [MEM] ISL [-]") as "SIM".
      5:{ iEval (rewrite red_syn_wpsim) in "SIM". iFrame. }
      1,2: auto.
      { iEval (rewrite red_syn_tgt_interp_as). auto. }
      iEval (red_tl_all; simpl).
      iSplitL "TID"; [done|]. iSplitL "PRu"; [iApply "PRu"|]. iFrame.
    }
  Qed.

  Lemma ClientSpinlock2_thread2_sim
        tid2 n
        ℓL ℓl
        (LAYER_L : ℓL = 3)
        (LAYER_l : ℓl = 2)
    :
    ⊢ ⟦(∀ (γX γe κs κl γκl γr : τ{nat, 1+n}),
           ((⤉ syn_inv n N_ClientSpinlock2 (clientSpinlock2_inv n tid2 ℓL ℓl γX γe κs κl γκl γr))
              ∗ (syn_tgt_interp_as n sndl (fun m => (s_memory_black m)))
              ∗ (⤉ isSpinlock n X γX γe κs ℓL)
              ∗ (⤉ -[κl](0)-◇ (∃ (γκw : τ{nat}), ▿ γκl γκw))
              ∗ (∃ (ℓl : τ{nat}), ◆[κl, ℓl])
              ∗ TID(tid2)
              ∗ (⤉ △ γr 1))
             -∗
             syn_wpsim (S n) tid2 ⊤
             (fun rs rt => (⤉(syn_term_cond n tid2 _ rs rt))%S)
             false false
             (fn2th ClientSpinlock2Spec.module "thread2" (tt ↑))
             (fn2th ClientSpinlock2.module "thread2" (tt ↑)))%S, 1+n⟧.
  Proof.
    iIntros.
    red_tl. iIntros (γX). red_tl. iIntros (γe). red_tl. iIntros (κs).
    red_tl. iIntros (κl). red_tl. iIntros (γκl). red_tl. iIntros (γr).
    iEval (red_tl_all; simpl; rewrite red_syn_inv; rewrite red_syn_wpsim; rewrite red_syn_tgt_interp_as).
    iIntros "(#INV_CL & #MEM & #ISL & #PROMl & [%ℓl0 LOl] & TID & LIVE_r)".
    iEval (red_tl; simpl) in "LOl". iPoseProof "LOl" as "#LOl".
    unfold fn2th. simpl. unfold thread2, ClientSpinlock2Spec.thread2. rred2r. lred2r.
    iInv "INV_CL" as "CL" "INV_CL_CLOSE".
    iEval (unfold clientSpinlock2_inv; simpl; red_tl_all; simpl) in "CL".
    iDestruct "CL" as "[CL1 | [CL2 | [CL3 | CL4]]]".
    4:{ iPoseProof (not_case4 with "CL4 LIVE_r") as "%F". inv F. }
    3:{ iMod (data_case3 with "CL3 LIVE_r") as "((%γκw & %κu & %γκu & A) & Dr & CL3)".
        iMod ("INV_CL_CLOSE" with "[CL3]") as "_".
        { iEval (unfold clientSpinlock2_inv; simpl; red_tl_all; simpl). do 2 iRight. iLeft. iFrame. }
        iEval (red_tl_all; simpl) in "A". iDestruct "A" as "(PRu & LINKu & Dl & Dw & DUTY & PC & Lu & EX)".
        iMod (pc_drop _ 1 _ _ 100 with "PC") as "PC".
        Unshelve. 1,3: lia.
        iApply (wpsim_yieldR2 with "[DUTY PC]").
        3:{ iFrame. iApply pcs_cons_fold. iFrame. }
        1,2: lia.
        iIntros "DUTY _ PCS". rred2r. iApply wpsim_tauR. rred2r.
        iMod (pcs_decr _ _ 10 0 with "PCS") as "[PCS _]".
        lia.
        iPoseProof (loop_case3 with "INV_CL [MEM] ISL [-]") as "SIM".
        5:{ iEval (rewrite red_syn_wpsim) in "SIM". iFrame. }
        1,2: auto.
        { iEval (rewrite red_syn_tgt_interp_as). auto. }
        iEval (red_tl_all; simpl). iFrame.
    }
    2:{ iPoseProof (data_case2 with "CL2") as "(LXw & PTD & % & % & CL2)". iEval (red_tl_all; simpl) in "CL2".
        iDestruct "CL2" as "(#PRw & Lw & #Dl & DUTY & PCspin & (% & LO))".
        iEval (red_tl_all; simpl) in "LO". iDestruct "LO" as "[#LOw %LAYw]".
        iApply (wpsim_yieldR_gen with "[DUTY]").
        2: iFrame.
        lia.
        iIntros "DUTY _". iMod ("INV_CL_CLOSE" with "[LXw PTD Lw PCspin DUTY]") as "_".
        { iEval (unfold clientSpinlock2_inv; simpl; red_tl_all; simpl). do 1 iRight. iLeft. iFrame.
          iExists _. iEval (red_tl). iExists _. iEval (red_tl_all; simpl). iFrame. do 2 (iSplit; [auto|]).
          iExists _. iEval (red_tl; simpl). eauto.
        }
        iModIntro. rred2r. iApply wpsim_tauR. rred2r.
        iInv "INV_CL" as "CL" "INV_CL_CLOSE".
        iEval (unfold clientSpinlock2_inv; simpl; red_tl_all; simpl) in "CL".
        iDestruct "CL" as "[CL1 | [CL2 | [CL3 | CL4]]]".
        4:{ iPoseProof (not_case4 with "CL4 LIVE_r") as "%F". inv F. }
        3:{ iMod (data_case3 with "CL3 LIVE_r") as "((%γκw0 & %κu & %γκu & A) & #Dr & CL3)".
            iMod ("INV_CL_CLOSE" with "[CL3]") as "_".
            { iEval (unfold clientSpinlock2_inv; simpl; red_tl_all; simpl). do 2 iRight. iLeft. iFrame. }
            iEval (red_tl_all; simpl) in "A". iDestruct "A" as "(PRu & LINKu & #Dl2 & #Dw & DUTY & PC & Lu & EX)".
            iPoseProof (OneShots.shot_agree with "Dl Dl2") as "%EQ". subst γκw0.
            iMod (pc_drop _ 1 _ _ 10 with "PC") as "PC".
            Unshelve. 1,3: lia.
            iPoseProof (pcs_cons_fold _ 0 [] 1 10 with "[PC]") as "PCS".
            { iFrame. }
            iPoseProof (loop_case3 with "INV_CL [MEM] ISL [-]") as "SIM".
            5:{ iEval (rewrite red_syn_wpsim) in "SIM". iFrame. }
            1,2: auto.
            { iEval (rewrite red_syn_tgt_interp_as). auto. }
            iEval (red_tl_all; simpl). iFrame. eauto.
        }
        2:{ iPoseProof (loop_case2 with "INV_CL [MEM] ISL [PRw] Dl LOw TID LIVE_r CL2 [-]") as "SIM".
            7:{ iEval (rewrite red_syn_wpsim) in "SIM". iFrame. }
            1,2,3: subst; auto.
            { iEval (rewrite red_syn_tgt_interp_as). auto. }
            { iEval (red_tl_all). auto. }
            iFrame.
        }
        { iExFalso. iDestruct "CL1" as "(_ & _ & _ & Ll & _)".
          iPoseProof (OneShots.pending_not_shot with "Ll Dl") as "%F". inv F.
        }
    }
    { iDestruct "CL1" as "(LXw & PTD & #PRl & Ll & DUTY & PCspin & _)".
      iApply (wpsim_yieldR_gen with "[DUTY]").
      2: iFrame.
      lia.
      iIntros "DUTY _". iMod ("INV_CL_CLOSE" with "[LXw PTD Ll PCspin DUTY]") as "_".
      { iEval (unfold clientSpinlock2_inv; simpl; red_tl_all; simpl). iLeft. iFrame. eauto. }
      iModIntro. rred2r. iApply wpsim_tauR. rred2r.
      iInv "INV_CL" as "CL" "INV_CL_CLOSE".
      iEval (unfold clientSpinlock2_inv; simpl; red_tl_all; simpl) in "CL".
      iDestruct "CL" as "[CL1 | [CL2 | [CL3 | CL4]]]".
      4:{ iPoseProof (not_case4 with "CL4 LIVE_r") as "%F". inv F. }
      3:{ iMod (data_case3 with "CL3 LIVE_r") as "((%γκw & %κu & %γκu & A) & #Dr & CL3)".
          iMod ("INV_CL_CLOSE" with "[CL3]") as "_".
          { iEval (unfold clientSpinlock2_inv; simpl; red_tl_all; simpl). do 2 iRight. iLeft. iFrame. }
          iEval (red_tl_all; simpl) in "A". iDestruct "A" as "(PRu & LINKu & #Dl & #Dw & DUTY & PC & Lu & EX)".
          iMod (pc_drop _ 1 _ _ 10 with "PC") as "PC".
          Unshelve. 1,3: lia.
          iPoseProof (pcs_cons_fold _ 0 [] 1 10 with "[PC]") as "PCS".
          { iFrame. }
          iPoseProof (loop_case3 with "INV_CL [MEM] ISL [-]") as "SIM".
          5:{ iEval (rewrite red_syn_wpsim) in "SIM". iFrame. }
          1,2: auto.
          { iEval (rewrite red_syn_tgt_interp_as). auto. }
          iEval (red_tl_all; simpl). iFrame. eauto.
      }
      2:{ iDestruct "CL2" as "(LXw & PTD & %κw & CL2)". iEval (red_tl) in "CL2". iDestruct "CL2" as "[%γκw CL2]".
          iEval (red_tl_all; simpl) in "CL2". iDestruct "CL2" as "(#PRw & Lw & #Dl & DUTY & PCspin & LO_w)".
          iDestruct "LO_w" as "[% LO]". iEval (red_tl; simpl) in "LO". iPoseProof "LO" as "[#LOw %LAY]".
          iPoseProof (loop_case2 with "INV_CL [MEM] ISL [PRw] Dl LOw TID LIVE_r [LXw PTD Lw DUTY PCspin] [-]") as "SIM".
          8:{ iEval (rewrite red_syn_wpsim) in "SIM". iFrame. }
          1,2,3: subst; auto.
          { iEval (rewrite red_syn_tgt_interp_as). auto. }
          { iEval (red_tl_all). auto. }
          { iFrame. iExists κw. iEval (red_tl). iExists γκw. iEval (red_tl_all; simpl). iFrame. do 2 (iSplit; [auto|]).
            iExists _. iEval (red_tl). eauto.
          }
          done.
      }
      { iClear "PROMl". iPoseProof (loop_case1 with "INV_CL [MEM] ISL [PRl] LOl TID LIVE_r [CL1] INV_CL_CLOSE") as "SIM".
        6:{ iEval (rewrite red_syn_wpsim) in "SIM". iFrame. }
        1,2: auto.
        { iEval (rewrite red_syn_tgt_interp_as). auto. }
        { iEval (red_tl_all). auto. }
        { iEval (red_tl_all; simpl). iFrame. }
      }
    }
  Qed.

End SIM.

