From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Export ITreeLib WFLib FairBeh NatStructs Mod pind OpenMod SCM Red IRed.
From Ordinal Require Export ClassicalHessenberg.

Set Implicit Arguments.


Section MOD.
  Definition loc_l: SCMem.val := SCMem.val_ptr (0, 0).
  Definition loc_f: SCMem.val := SCMem.val_ptr (1, 0).

  Definition example_fun:
    ktree ((((@eventE void) +' cE) +' (sE unit)) +' OpenMod.callE) unit unit :=
    fun _ =>
      b <- OMod.call "cas" (loc_l, SCMem.val_nat 0, SCMem.val_nat 1);;
      if (b: bool) then
        _ <- trigger Yield;;
        _ <- trigger Yield;;
        `_: unit <- OMod.call "store" (loc_f, SCMem.val_nat 1);;
        trigger Yield
      else
        ITree.iter
          (fun _ =>
             _ <- trigger Yield;;
             f <- OMod.call "load" loc_f;;
             _ <- trigger Yield;;
             b <- OMod.call "compare" (f: SCMem.val, SCMem.val_nat 1);;
             _ <- trigger Yield;;
             if (b: bool) then Ret (inr tt) else Ret (inl tt)) tt
  .

  Definition example_omod: OMod.t :=
    OMod.mk
      tt
      (Mod.get_funs [("example", Mod.wrap_fun example_fun)])
  .

  Definition example_mod: Mod.t :=
    OMod.close
      (example_omod)
      (SCMem.mod [1; 1])
  .

  Definition example_spec_fun:
    ktree ((((@eventE void) +' cE) +' (sE unit))) unit unit :=
    fun _ =>
      trigger Yield
  .

  Definition example_spec_mod: Mod.t :=
    Mod.mk
      tt
      (Mod.get_funs [("example", Mod.wrap_fun example_spec_fun)])
  .
End MOD.

From Fairness Require Import IProp IPM Weakest.
From Fairness Require Import ModSim PCM MonotonePCM StateRA FairRA.

Section SIM.
  Context `{Σ: GRA.t}.
  Context `{MONORA: @GRA.inG monoRA Σ}.
  Context `{THDRA: @GRA.inG ThreadRA Σ}.
  Context `{STATESRC: @GRA.inG (stateSrcRA unit) Σ}.
  Context `{STATETGT: @GRA.inG (stateTgtRA (unit * SCMem.t)) Σ}.
  Context `{IDENTSRC: @GRA.inG (identSrcRA void) Σ}.
  Context `{IDENTTGT: @GRA.inG (identTgtRA (void + SCMem.val)%type) Σ}.
  Context `{OBLGRA: @GRA.inG ObligationRA.t Σ}.
  Context `{ARROWRA: @GRA.inG (ArrowRA (void + SCMem.val)%type) Σ}.
  Context `{EDGERA: @GRA.inG EdgeRA Σ}.
  Context `{ONESHOTSRA: @GRA.inG (@FiniteMap.t (OneShot.t unit)) Σ}.

  Context `{MEMRA: @GRA.inG memRA Σ}.

  Context `{EXCL: @GRA.inG (Excl.t unit) Σ}.
  Context `{ONESHOTRA: @GRA.inG (OneShot.t thread_id) Σ}.

  Let I: list iProp := [
      (∃ m,
          (memory_black m)
            **
            (St_tgt (tt, m)));
      (((points_to loc_l (SCMem.val_nat 0))
          **
          (points_to loc_f (SCMem.val_nat 0))
          **
          (OwnM (OneShot.pending thread_id 1)))
       ∨
         (∃ k,
             (OwnM (OneShot.shot k))
               **
               (ObligationRA.correl_thread k 1%ord)
               **
               (∃ n, ObligationRA.black k n)
               **
               (points_to loc_l (SCMem.val_nat 1))
               **
               ((points_to loc_f (SCMem.val_nat 0) ** ObligationRA.pending k (/2)%Qp)
                ∨
                  (points_to loc_f (SCMem.val_nat 1) ** ObligationRA.shot k))))]%I.

  Lemma sim: ModSim.mod_sim example_spec_mod example_mod.
  Proof.
    Abort.
  (*   refine (@ModSim.mk _ _ nat_wf nat_wf _ _ Σ _ _ _). *)
  (*   { econs. exact 0. } *)
  (*   { i. exists (S o0). ss. } *)
  (*   { admit. } *)
  (*   { cut (forall tid, *)
  (*             (own_thread tid ** ObligationRA.duty (inl tid) []) ⊢ stsim I tid [0; 1] ibot7 ibot7 (fun r_src r_tgt => own_thread tid ** ObligationRA.duty (inl tid) [] ** ⌜r_src = r_tgt⌝) false false (example_spec_fun tt) (OMod.close_itree (example_omod) (SCMem.mod [1; 1]) (example_fun tt))). *)
  (*     { admit. } *)
  (*     iIntros (?) "[TH DUTY]". unfold example_spec_fun, example_fun. *)
  (*     lred. rred. rewrite close_itree_call. ss. rred. *)
  (*     iApply (stsim_yieldR with "[DUTY]"); [msubtac|iFrame|]. iIntros "DUTY _". *)
  (*     rred. unfold SCMem.cas_fun, Mod.wrap_fun. rred. *)
  (*     iopen 0 "[% [MEM ST]]" "K0". *)
  (*     iApply stsim_getR. iSplit. *)
  (*     { iFrame. } *)
  (*     rred. iApply stsim_tauR. rred. *)
  (*     unfold SCMem.cas. *)
  (*     iopen 1 "[[[POINTL POINTF] PEND]|[% H]]" "K1". *)
  (*     { iPoseProof (memory_ra_load with "MEM POINTL") as "%". des; clarify. *)
  (*       rewrite H. ss. *)
  (*       iPoseProof (memory_ra_store with "MEM POINTL") as "[% [% > [MEM POINTL]]]". *)
  (*       rewrite H1. ss. *)
  (*       rred. iApply stsim_getR. iSplit. *)
  (*       { iFrame. } *)
  (*       rred. iApply (stsim_putR with "ST"). iIntros "ST". *)
  (*       rred. iApply stsim_tauR. *)
  (*       rred. iApply stsim_tauR. *)
  (*       rred. *)
  (*       iPoseProof (@ObligationRA.alloc _ _ ((1 × Ord.omega) × 10)%ord) as "> [% [[# BLACK WHITES] OBL]]". *)
  (*       iPoseProof (ObligationRA.cut_white with "WHITES") as "[WHITES WHITE]". *)
  (*       iPoseProof (ObligationRA.duty_alloc with "DUTY WHITE") as "> DUTY". *)
  (*       iPoseProof (ObligationRA.duty_correl_thread with "DUTY") as "# CORR"; [ss; eauto|]. *)
  (*       iPoseProof (OwnM_Upd with "PEND") as "> SHOT". *)
  (*       { eapply (OneShot.pending_shot k). } *)
  (*       iPoseProof (own_persistent with "SHOT") as "# SHOTP". iClear "SHOT". ss. *)
  (*       iMod ("K0" with "[MEM ST]") as "_". *)
  (*       { iExists _. iFrame. } *)
  (*       iPoseProof (ObligationRA.pending_split with "[OBL]") as "[OBL0 OBL1]". *)
  (*       { rewrite Qp.inv_half_half. iFrame. } *)
  (*       iMod ("K1" with "[POINTF POINTL OBL1]") as "_". *)
  (*       { iRight. iExists _. iFrame. iSplitR. *)
  (*         { iSplit; [iSplit; [iApply "SHOTP"|iApply "CORR"]|eauto]. } *)
  (*         { iLeft. iFrame. } *)
  (*       } *)
  (*       { msubtac. } *)
  (*       iPoseProof (ObligationRA.cut_white with "WHITES") as "[WHITES WHITE]". *)
  (*       msimpl. iApply (stsim_yieldR with "[DUTY WHITE]"). *)
  (*       { msubtac. } *)
  (*       { iFrame. iSplit; auto. } *)
  (*       iIntros "DUTY _". *)
  (*       rred. iApply stsim_tauR. *)
  (*       iPoseProof (ObligationRA.cut_white with "WHITES") as "[WHITES WHITE]". *)
  (*       rred. iApply (stsim_yieldR with "[DUTY WHITE]"). *)
  (*       { msubtac. } *)
  (*       { iFrame. iSplit; auto. } *)
  (*       iIntros "DUTY _". *)
  (*       rred. iApply stsim_tauR. *)
  (*       rred. rewrite close_itree_call. ss. *)
  (*       iPoseProof (ObligationRA.cut_white with "WHITES") as "[WHITES WHITE]". *)
  (*       rred. iApply (stsim_yieldR with "[DUTY WHITE]"). *)
  (*       { msubtac. } *)
  (*       { iFrame. iSplit; auto. } *)
  (*       iIntros "DUTY _". *)
  (*       unfold SCMem.store_fun, Mod.wrap_fun. rred. *)
  (*       iopen 0 "[% [MEM ST]]" "K0". *)
  (*       iApply stsim_getR. iSplit. *)
  (*       { iFrame. } *)
  (*       rred. iApply stsim_tauR. rred. *)
  (*       iopen 1 "[[[POINTL POINTF] PEND]|[% [H H1]]]" "K1". *)
  (*       { iExFalso. iApply OneShotP.pending_not_shot. iSplit; iFrame. auto. } *)
  (*       { iPoseProof (OneShotP.shot_agree with "[H]") as "%". *)
  (*         { iSplit. *)
  (*           { iApply "SHOTP". } *)
  (*           { iDestruct "H" as "[[[H _] _] _]". iApply "H". } *)
  (*         } *)
  (*         subst. *)
  (*         iDestruct "H1" as "[[POINTF PEND]|[POINTF OBL1]]". *)
  (*         { iPoseProof (memory_ra_store with "MEM POINTF") as "[% [% > [MEM POINTF]]]". *)
  (*           rewrite H2. ss. *)
  (*           rred. iApply stsim_getR. iSplit. *)
  (*           { iFrame. } *)
  (*           rred. iApply (stsim_putR with "ST"). iIntros "ST". *)
  (*           rred. iApply stsim_tauR. *)
  (*           rred. iApply stsim_tauR. rred. *)
  (*           iMod ("K0" with "[MEM ST]") as "_". *)
  (*           { iExists _. iFrame. } *)
  (*           iPoseProof (ObligationRA.pending_shot with "[OBL0 PEND]") as "> # OSHOT". *)
  (*           { rewrite <- Qp.inv_half_half. iApply (ObligationRA.pending_sum with "OBL0 PEND"). } *)
  (*           iMod ("K1" with "[POINTF H OSHOT]") as "_". *)
  (*           { iRight. iExists _. iFrame. iRight. iFrame. auto. } *)
  (*           { msubtac. } *)
  (*           iPoseProof (ObligationRA.duty_done with "DUTY OSHOT") as "> DUTY". *)
  (*           iApply (stsim_sync with "[DUTY]"). *)
  (*           { msubtac. } *)
  (*           { iFrame. } *)
  (*           iIntros "DUTY _". *)
  (*           iApply stsim_tauR. *)
  (*           iApply stsim_ret. iModIntro. iFrame. auto. *)
  (*         } *)
  (*         { iExFalso. iApply (ObligationRA.pending_not_shot with "OBL0 OBL1"). } *)
  (*       } *)
  (*     } *)
  (*     { iDestruct "H" as "[[[[# SHOTK # CORR] [% # BLACK]] POINTL] F]". *)
  (*       iPoseProof (memory_ra_load with "MEM POINTL") as "%". des; clarify. *)
  (*       rewrite H. ss. *)
  (*       rred. iApply stsim_tauR. *)
  (*       iMod ("K0" with "[MEM ST]") as "_". *)
  (*       { iExists _. iFrame. } *)
  (*       iMod ("K1" with "[POINTL F]") as "_". *)
  (*       { iRight. iExists _. iFrame. auto. } *)
  (*       { msubtac. } *)
  (*       rred. iStopProof. pattern n. revert n. *)
  (*       apply (well_founded_induction Ord.lt_well_founded). intros o IH. *)
  (*       iIntros "[# [SHOTK [CORR BLACK]] [TH DUTY]]". *)
  (*       rewrite OpenMod.unfold_iter. rred. *)
  (*       iApply (stsim_yieldR with "[DUTY]"). *)
  (*       { msubtac. } *)
  (*       { iFrame. } *)
  (*       iIntros "DUTY WHITE". *)
  (*       rred. iApply stsim_tauR. rred. *)
  (*       rewrite close_itree_call. ss. *)
  (*       unfold SCMem.load_fun, Mod.wrap_fun. *)
  (*       rred. iApply (stsim_yieldR with "[DUTY]"). *)
  (*       { msubtac. } *)
  (*       { iFrame. } *)
  (*       iIntros "DUTY _". *)
  (*       iopen 0 "[% [MEM ST]]" "K0". *)
  (*       rred. iApply stsim_getR. iSplit. *)
  (*       { iFrame. } *)
  (*       rred. iApply stsim_tauR. rred. *)
  (*       iopen 1 "[FALSE|[% H]]" "K1". *)
  (*       { iExFalso. iApply OneShotP.pending_not_shot. iSplit; [|iApply "SHOTK"]. *)
  (*         iDestruct "FALSE" as "[[? ?] ?]". iFrame. *)
  (*       } *)
  (*       iDestruct "H" as "[X [Y|Y]]". *)
  (*       { iPoseProof (OneShotP.shot_agree with "[X]") as "%". *)
  (*         { iSplit. *)
  (*           { iApply "SHOTK". } *)
  (*           { iDestruct "X" as "[[[H ?] ?] ?]". iApply "H". } *)
  (*         } *)
  (*         subst. *)
  (*         iPoseProof (ObligationRA.correl_thread_correlate with "CORR WHITE") as "> [WHITE|WHITE]"; cycle 1. *)
  (*         { iExFalso. iApply (ObligationRA.pending_not_shot with "[Y] WHITE"). *)
  (*           iDestruct "Y" as "[_ ?]". eauto. *)
  (*         } *)
  (*         iPoseProof (memory_ra_load with "MEM [Y]") as "%". *)
  (*         { iDestruct "Y" as "[? _]". iFrame. } *)
  (*         des. rewrite H1. *)
  (*         rred. iApply stsim_tauR. *)
  (*         iMod ("K0" with "[MEM ST]") as "_". *)
  (*         { iExists _. iFrame. } *)
  (*         iMod ("K1" with "[X Y]") as "_". *)
  (*         { iRight. iExists _. iFrame. } *)
  (*         { msubtac. } *)
  (*         rred. iApply (stsim_yieldR with "[DUTY]"). *)
  (*         { msubtac. } *)
  (*         { iFrame. } *)
  (*         iIntros "DUTY _". *)
  (*         rred. iApply stsim_tauR. *)
  (*         rred. rewrite close_itree_call. ss. *)
  (*         unfold SCMem.compare_fun, Mod.wrap_fun. *)
  (*         rred. iApply (stsim_yieldR with "[DUTY]"). *)
  (*         { msubtac. } *)
  (*         { iFrame. } *)
  (*         iIntros "DUTY _". *)
  (*         iopen 0 "[% [MEM ST]]" "K0". *)
  (*         rred. iApply stsim_getR. iSplit. *)
  (*         { iFrame. } *)
  (*         iMod ("K0" with "[MEM ST]") as "_". *)
  (*         { iExists _. iFrame. } *)
  (*         { msubtac. } *)
  (*         rred. iApply stsim_tauR. *)
  (*         rred. iApply stsim_tauR. *)
  (*         rred. iApply (stsim_yieldR with "[DUTY]"). *)
  (*         { msubtac. } *)
  (*         { iFrame. } *)
  (*         iIntros "DUTY _". *)
  (*         rred. iApply stsim_tauR. *)
  (*         rred. iApply stsim_tauR. *)
  (*         iPoseProof (ObligationRA.black_white_decr_one with "BLACK WHITE") as "> [% [# BLACK1 %]]". *)
  (*         iApply IH; eauto. iFrame. iModIntro. iSplit; auto. *)
  (*       } *)
  (*       { iPoseProof (memory_ra_load with "MEM [Y]") as "%". *)
  (*         { iDestruct "Y" as "[? _]". iFrame. } *)
  (*         des. rewrite H1. *)
  (*         rred. iApply stsim_tauR. *)
  (*         iMod ("K0" with "[MEM ST]") as "_". *)
  (*         { iExists _. iFrame. } *)
  (*         iMod ("K1" with "[X Y]") as "_". *)
  (*         { iRight. iExists _. iFrame. } *)
  (*         { msubtac. } *)
  (*         rred. iApply (stsim_yieldR with "[DUTY]"). *)
  (*         { msubtac. } *)
  (*         { iFrame. } *)
  (*         iIntros "DUTY _". *)
  (*         rred. iApply stsim_tauR. *)
  (*         rred. rewrite close_itree_call. ss. *)
  (*         unfold SCMem.compare_fun, Mod.wrap_fun. *)
  (*         rred. iApply (stsim_yieldR with "[DUTY]"). *)
  (*         { msubtac. } *)
  (*         { iFrame. } *)
  (*         iIntros "DUTY _". *)
  (*         iopen 0 "[% [MEM ST]]" "K0". *)
  (*         rred. iApply stsim_getR. iSplit. *)
  (*         { iFrame. } *)
  (*         iMod ("K0" with "[MEM ST]") as "_". *)
  (*         { iExists _. iFrame. } *)
  (*         { msubtac. } *)
  (*         rred. iApply stsim_tauR. *)
  (*         rred. iApply stsim_tauR. *)
  (*         rred. iApply (stsim_sync with "[DUTY]"). *)
  (*         { msubtac. } *)
  (*         { iFrame. } *)
  (*         iIntros "DUTY _". *)
  (*         rred. iApply stsim_tauR. *)
  (*         rred. iApply stsim_ret. *)
  (*         iModIntro. iFrame. auto. *)
  (*       } *)
  (*     } *)
  (*   } *)
  (* Admitted. *)
End SIM.
