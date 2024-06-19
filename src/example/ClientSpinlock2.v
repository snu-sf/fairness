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
                ∗ (Duty(tid2) [])
                ∗ ◇[κs](ℓL, 1)
                ∗ (∃ (ℓl : τ{nat}), ◆[κl, ℓl])
      )
      ∨
        ((○ γX 1) ∗ (D ↦ 0)
                  ∗ (∃ (κw γκw : τ{nat}),
                        (-[κw](0)-◇ (∃ (γκu : τ{nat}), (▿ γκw γκu)))
                          ∗ (△ γκw (1/2)) ∗ (▿ γκl γκw)
                          ∗ (Duty(tid2) [])
                          ∗ ◇[κs](ℓL, 1)
                          ∗ (∃ (ℓw : τ{nat}), ◆[κw, ℓw] ∗ ⌜ℓw <= ℓL⌝))
        )
      ∨
        ((○ γX 1) ∗ (D ↦ 1)
                  ∗ (∃ (γκw κu γκu : τ{nat}),
                        (-[κu](0)-◇ (▿ γκu 0))
                          ∗ (△ γκu (1/2)) ∗ (κu -(0)-◇ κs) ∗ (▿ γκl γκw) ∗ (▿ γκw γκu)
                          ∗ ((Duty(tid2) [(κu, 0, (▿ γκu 0))] ∗ ◇[κu](ℓl, 1) ∗ (△ γκu (1/2)) ∗ (EX γe tt)) ∨ (▿ γr 0)))
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
    ⊢ ⟦(∀ (γX γe κs κl γκl γr : τ{nat, 1+n}),
           ((⤉ syn_inv n N_ClientSpinlock2 (clientSpinlock2_inv n tid2 ℓL ℓl γX γe κs κl γκl γr))
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
                                                 ` b : bool <- OMod.call "compare" (d, 1);; ` r : () + () <- (if b then Ret (inr ()) else Ret (inl ()));; Ret r) ());;;
                                    x <- OMod.close_itree omod (SCMem.mod gvs) ((trigger Yield;;; Spinlock.unlock X);;; Ret (0 : SCMem.val));;
                   OMod.close_itree omod (SCMem.mod gvs) (Ret (Any.upcast x))))%S, 1+n⟧
  .
  Proof.
    iEval (red_tl_all; rewrite red_syn_tgt_interp_as; rewrite red_syn_wpsim; simpl).
    iIntros "#INV_CL #MEM #ISL (TID & #PRu & #LINKu & #Dl & #Dw & Lu & EX & #Dr & DUTY & PC)".

    TODO


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






  Definition clientSpinlock2_inv n (tid2 : thread_id) (ℓL ℓl : nat) (γX γe κs : nat) (κl γκl : nat) (γr : nat) : sProp n :=
    (
      ((○ γX 0) ∗ (D ↦ 0)
                ∗ (-[κl](0)-◇ (∃ (γκw : τ{nat}), ▿ γκl γκw)) ∗ (△ γκl (1/2))
                ∗ (Duty(tid2) [])
                ∗ ◇[κs](ℓL, 1)
                ∗ (∃ (ℓl : τ{nat}), ◆[κl, ℓl])
      )
      ∨
        ((○ γX 1) ∗ (D ↦ 0)
                  ∗ (∃ (κw γκw : τ{nat}),
                        (-[κw](0)-◇ (∃ (γκu : τ{nat}), (▿ γκw γκu)))
                          ∗ (△ γκw (1/2)) ∗ (▿ γκl γκw)
                          ∗ (Duty(tid2) [])
                          ∗ ◇[κs](ℓL, 1)
                          ∗ (∃ (ℓw : τ{nat}), ◆[κw, ℓw] ∗ ⌜ℓw <= ℓL⌝))
        )
      ∨
        ((○ γX 1) ∗ (D ↦ 1)
                  ∗ (∃ (γκw κu γκu : τ{nat}),
                        (-[κu](0)-◇ (▿ γκu 0))
                          ∗ (△ γκu (1/2)) ∗ (κu -(0)-◇ κs) ∗ (▿ γκl γκw) ∗ (▿ γκw γκu)
                          ∗ ((Duty(tid2) [(κu, 0, (▿ γκu 0))] ∗ ◇[κu](ℓl, 1) ∗ (△ γκu (1/2)) ∗ (EX γe tt)) ∨ (▿ γr 0)))
        )
      ∨
        ((○ γX 0) ∗ (D ↦ 1)
                  ∗ (∃ (γκw γκu : τ{nat}),
                        (▿ γκl γκw) ∗ (▿ γκw γκu) ∗ (▿ γr 0) ∗ (▿ γκu 0)))
    )%S.

End SIM.

