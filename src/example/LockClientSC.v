From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
Unset Universe Checking.

From Fairness Require Export
     ITreeLib WFLib FairBeh NatStructs Mod pind Axioms
     OpenMod SCM Red IRed Wrapper WeakestAdequacy FairLock Concurrency.
From Ordinal Require Export ClassicalHessenberg.

Set Implicit Arguments.

Definition ord_wf: WF := mk_wf (@Ord.lt_well_founded).

Section INIT.

  Definition gvs : list nat := [1].

  Definition loc_X := SCMem.val_ptr (0, 0).

  Definition const_0 := SCMem.val_nat 0.
  Definition const_42 := SCMem.val_nat 42.

End INIT.

Module ClientImpl.

  Definition thread1:
    ktree ((((@eventE void) +' cE) +' (sE unit)) +' OpenMod.callE) unit unit
    :=
    fun _ =>
      `_: unit <- (OMod.call "lock" tt);;
      `_: unit <- (OMod.call "store" (loc_X, const_42));;
      `_: unit <- (OMod.call "unlock" tt);;
      Ret tt.

  Definition thread2:
    ktree ((((@eventE void) +' cE) +' (sE unit)) +' OpenMod.callE) unit unit
    :=
    fun _ =>
      _ <- ITree.iter
            (fun (_: unit) =>
               `_: unit <- (OMod.call "lock" tt);;
               x <- (OMod.call "load" loc_X);;
               `_: unit <- (OMod.call "unlock" tt);;
               b <- OMod.call "compare" (x: SCMem.val, SCMem.val_nat 0);;
               if (b: bool) then Ret (inl tt) else Ret (inr tt)) tt;;
      x <- (OMod.call "load" loc_X);;
      match x with
      | SCMem.val_nat n => _ <- trigger (Observe 0 [n]);; Ret tt
      | _ => UB
      end.

  Definition omod: OMod.t :=
    OMod.mk
      tt
      (Mod.get_funs [("thread1", Mod.wrap_fun thread1);
                     ("thread2", Mod.wrap_fun thread2)])
  .

  Definition mod: Mod.t :=
    OMod.close
      (omod)
      (ModAdd (SCMem.mod gvs) ABSLock.mod)
  .

End ClientImpl.


Module ClientSpec.
  Definition thread1:
    ktree ((((@eventE void) +' cE) +' (sE unit))) unit unit
    :=
    fun _ =>
      _ <- trigger Yield;; Ret tt.

  Definition thread2:
    ktree ((((@eventE void) +' cE) +' (sE unit))) unit unit
    :=
    fun _ =>
      _ <- trigger Yield;;
      _ <- trigger (Observe 0 [42]);;
      _ <- trigger Yield;;
      Ret tt.

  Definition mod: Mod.t :=
    Mod.mk
      tt
      (Mod.get_funs [("thread1", Mod.wrap_fun thread1);
                     ("thread2", Mod.wrap_fun thread2)])
  .

End ClientSpec.



From Fairness Require Import
     IProp IPM Weakest ModSim PCM MonotonePCM StateRA FairRA.

Section SIM.

  Context `{Σ: GRA.t}.

  Context `{MONORA: @GRA.inG monoRA Σ}.
  Context `{THDRA: @GRA.inG ThreadRA Σ}.
  Context `{STATESRC: @GRA.inG (stateSrcRA (unit)) Σ}.
  (* Context `{STATETGT: @GRA.inG (stateTgtRA (unit * (SCMem.t * (bool * NatMap.t unit)))) Σ}. *)
  Context `{STATETGT: @GRA.inG (stateTgtRA ((OMod.closed_state ClientImpl.omod (ModAdd (SCMem.mod gvs) ABSLock.mod)))) Σ}.
  Context `{IDENTSRC: @GRA.inG (identSrcRA (void)) Σ}.
  (* Context `{IDENTTGT: @GRA.inG (identTgtRA (void + (SCMem.val + thread_id))%type) Σ}. *)
  Context `{IDENTTGT: @GRA.inG (identTgtRA (OMod.closed_ident ClientImpl.omod (ModAdd (SCMem.mod gvs) ABSLock.mod))%type) Σ}.

  Context `{OBLGRA: @GRA.inG ObligationRA.t Σ}.
  (* Context `{ARROWRA: @GRA.inG (ArrowRA (void + (SCMem.val + thread_id))%type) Σ}. *)
  Context `{ARROWRA: @GRA.inG (ArrowRA (OMod.closed_ident ClientImpl.omod (ModAdd (SCMem.mod gvs) ABSLock.mod))%type) Σ}.
  Context `{EDGERA: @GRA.inG EdgeRA Σ}.
  Context `{ONESHOTSRA: @GRA.inG (@FiniteMap.t (OneShot.t unit)) Σ}.

  Context `{MEMRA: @GRA.inG memRA Σ}.

  Context `{EXCL: @GRA.inG (Excl.t unit) Σ}.
  Context `{ONESHOTRA: @GRA.inG (OneShot.t nat) Σ}.
  Context `{REGIONRA: @GRA.inG (Region.t (thread_id * nat)) Σ}.
  Context `{CONSENTRA: @GRA.inG (@FiniteMap.t (Consent.t nat)) Σ}.
  Context `{AUTHNRA: @GRA.inG (Auth.t (Excl.t nat)) Σ}.
  Context `{AUTHNMRA: @GRA.inG (Auth.t (NatMapRA.t unit)) Σ}.
  Context `{AUTHNMNRA: @GRA.inG (Auth.t (NatMapRA.t nat)) Σ}.
  Context `{AUTHNMNN: @GRA.inG (Auth.t (NatMapRA.t (nat * nat))) Σ}.

  Definition thread1_will_write : iProp :=
    ∃ k, (∃ n, ObligationRA.black k n)
           ∗
           (ObligationRA.correl_thread k 1%ord)
           ∗
           (OwnM (OneShot.shot k))
           ∗
           ((ObligationRA.pending k (/2)%Qp ∗ points_to loc_X const_0)
            ∨
              (ObligationRA.shot k ∗ points_to loc_X const_42)).

  Definition lock_will_unlock : iProp :=
    ∃ (own: bool) (ths wait: TIdSet.t) (f: NatMap.t nat) (j: nat),
      (OwnM (Auth.black (Some f: NatMapRA.t nat)))
        ∗
        (OwnM (Auth.black (Excl.just j: Excl.t nat)))
        ∗
        (⌜nm_wf_pair f wait⌝)
        ∗
        (natmap_prop_sum ths (fun tid _ => (⌜~ NatMap.In tid wait⌝) -∗ ObligationRA.duty (inr (inr (inr tid))) []))
        ∗
        (natmap_prop_sum f (fun tid idx => (ObligationRA.correl (inr (inr (inr tid))) idx (Ord.omega ^ 2)%ord)
                                          ∗
                                          (ObligationRA.pending idx 1)
                                          ∗
                                          (ObligationRA.duty (inr (inr (inr tid))) [(idx, Ord.omega)])
        ))
        ∗
        ((⌜own = false⌝ ∗ OwnM (Auth.white (Excl.just j: Excl.t nat)))
         ∨
           ((⌜own = true⌝)
              ∗ (ObligationRA.pending j 1)
              ∗ (ObligationRA.correl_thread j 1%ord)
              ∗ (natmap_prop_sum f (fun tid idx => ObligationRA.amplifier j idx 1%ord))
           )
        )
  .

  Definition lock_holding: iProp :=
    ∃ (j: nat) (n: Ord.t),
      (OwnM (Auth.black (Excl.just j: Excl.t nat))) ∗ (ObligationRA.white j n).

  Definition lock_waiting: iProp :=
    ∃ (tid: thread_id) (i: nat) m,
      (OwnM (Auth.white (NatMapRA.singleton tid i: NatMapRA.t nat)))
        ∗
        (ObligationRA.correl (inr (inr (inr tid))) i (Ord.omega ^ 2)%ord)
        ∗
        (ObligationRA.black i m).

  Let I: list iProp :=
        [thread1_will_write; lock_will_unlock; lock_holding; lock_waiting].

  Lemma correct_thread1:
    (own_thread 0 ∗ ObligationRA.duty (inl 0) []) ⊢
          (stsim I 0 [0; 1; 2; 3] ibot5 ibot5
                (fun r_src r_tgt => own_thread 0 ** ObligationRA.duty (inl 1) [] ** ⌜r_src = r_tgt⌝)
                (ClientSpec.thread1 tt)
                (OMod.close_itree ClientImpl.omod (ModAdd (SCMem.mod gvs) ABSLock.mod) (ClientImpl.thread1 tt))).
  Proof.
    iIntros "[TH DUTY]". unfold ClientSpec.thread1, ClientImpl.thread1.
    rred. rewrite close_itree_call. ss. rred.
    iApply (stsim_yieldR with "[DUTY]"). msubtac. iFrame.
    iIntros "DUTY _". rred.
    unfold ABSLock.lock_fun, Mod.wrap_fun. rred.
    iApply stsim_tidR. rred. iApply stsim_tauR. rred.
    (*TODO*)

      iIntros (?) "[TH DUTY]". unfold example_spec_fun, example_fun.
      lred. rred. rewrite close_itree_call. ss. rred.
      iApply (stsim_yieldR with "[DUTY]"); [msubtac|iFrame|]. iIntros "DUTY _".
      rred. unfold SCMem.cas_fun, Mod.wrap_fun. rred.
      iopen 0 "[% [MEM ST]]" "K0".
      iApply stsim_getR. iSplit.
      { iFrame. }
      rred. iApply stsim_tauR. rred.
      unfold SCMem.cas.
      iopen 1 "[[[POINTL POINTF] PEND]|[% H]]" "K1".
      { iPoseProof (memory_ra_load with "MEM POINTL") as "%". des; clarify.
        rewrite H. ss.
        iPoseProof (memory_ra_store with "MEM POINTL") as "[% [% > [MEM POINTL]]]".
        rewrite H1. ss.
        rred. iApply stsim_getR. iSplit.
        { iFrame. }
        rred. iApply (stsim_putR with "ST"). iIntros "ST".
        rred. iApply stsim_tauR.
        rred. iApply stsim_tauR.
        rred.
        iPoseProof (@ObligationRA.alloc _ _ ((1 × Ord.omega) × 10)%ord) as "> [% [[# BLACK WHITES] OBL]]".
        iPoseProof (ObligationRA.cut_white with "WHITES") as "[WHITES WHITE]".
        iPoseProof (ObligationRA.duty_alloc with "DUTY WHITE") as "> DUTY".
        iPoseProof (ObligationRA.duty_correl_thread with "DUTY") as "# CORR"; [ss; eauto|].
        iPoseProof (OwnM_Upd with "PEND") as "> SHOT".
        { eapply (OneShot.pending_shot k). }
        iPoseProof (own_persistent with "SHOT") as "# SHOTP". iClear "SHOT". ss.
        iMod ("K0" with "[MEM ST]") as "_".
        { iExists _. iFrame. }
        iPoseProof (ObligationRA.pending_split with "[OBL]") as "[OBL0 OBL1]".
        { rewrite Qp_inv_half_half. iFrame. }
        iMod ("K1" with "[POINTF POINTL OBL1]") as "_".
        { iRight. iExists _. iFrame. iSplitR.
          { iSplit; [iSplit; [iApply "SHOTP"|iApply "CORR"]|eauto]. }
          { iLeft. iFrame. }
        }
        { msubtac. }
        iPoseProof (ObligationRA.cut_white with "WHITES") as "[WHITES WHITE]".
        msimpl. iApply (stsim_yieldR with "[DUTY WHITE]").
        { msubtac. }
        { iFrame. iSplit; auto. }
        iIntros "DUTY _".
        rred. iApply stsim_tauR.
        iPoseProof (ObligationRA.cut_white with "WHITES") as "[WHITES WHITE]".
        rred. iApply (stsim_yieldR with "[DUTY WHITE]").
        { msubtac. }
        { iFrame. iSplit; auto. }
        iIntros "DUTY _".
        rred. iApply stsim_tauR.
        rred. rewrite close_itree_call. ss.
        iPoseProof (ObligationRA.cut_white with "WHITES") as "[WHITES WHITE]".
        rred. iApply (stsim_yieldR with "[DUTY WHITE]").
        { msubtac. }
        { iFrame. iSplit; auto. }
        iIntros "DUTY _".
        unfold SCMem.store_fun, Mod.wrap_fun. rred.
        iopen 0 "[% [MEM ST]]" "K0".
        iApply stsim_getR. iSplit.
        { iFrame. }
        rred. iApply stsim_tauR. rred.
        iopen 1 "[[[POINTL POINTF] PEND]|[% [H H1]]]" "K1".
        { iExFalso. iApply OneShotP.pending_not_shot. iSplit; iFrame. auto. }
        { iPoseProof (OneShotP.shot_agree with "[H]") as "%".
          { iSplit.
            { iApply "SHOTP". }
            { iDestruct "H" as "[[[H _] _] _]". iApply "H". }
          }
          subst.
          iDestruct "H1" as "[[POINTF PEND]|[POINTF OBL1]]".
          { iPoseProof (memory_ra_store with "MEM POINTF") as "[% [% > [MEM POINTF]]]".
            rewrite H2. ss.
            rred. iApply stsim_getR. iSplit.
            { iFrame. }
            rred. iApply (stsim_putR with "ST"). iIntros "ST".
            rred. iApply stsim_tauR.
            rred. iApply stsim_tauR. rred.
            iMod ("K0" with "[MEM ST]") as "_".
            { iExists _. iFrame. }
            iPoseProof (ObligationRA.pending_shot with "[OBL0 PEND]") as "> # OSHOT".
            { rewrite <- Qp_inv_half_half. iApply (ObligationRA.pending_sum with "OBL0 PEND"). }
            iMod ("K1" with "[POINTF H OSHOT]") as "_".
            { iRight. iExists _. iFrame. iRight. iFrame. auto. }
            { msubtac. }
            iPoseProof (ObligationRA.duty_done with "DUTY OSHOT") as "> DUTY".
            iApply (stsim_sync with "[DUTY]").
            { msubtac. }
            { iFrame. }
            iIntros "DUTY _".
            iApply stsim_tauR.
            iApply stsim_ret. iModIntro. iFrame. auto.
          }
          { iExFalso. iApply (ObligationRA.pending_not_shot with "OBL0 OBL1"). }
        }
      }
      { iDestruct "H" as "[[[[# SHOTK # CORR] [% # BLACK]] POINTL] F]".
        iPoseProof (memory_ra_load with "MEM POINTL") as "%". des; clarify.
        rewrite H. ss.
        rred. iApply stsim_tauR.
        iMod ("K0" with "[MEM ST]") as "_".
        { iExists _. iFrame. }
        iMod ("K1" with "[POINTL F]") as "_".
        { iRight. iExists _. iFrame. auto. }
        { msubtac. }
        rred. iStopProof. pattern n. revert n.
        apply (well_founded_induction Ord.lt_well_founded). intros o IH.
        iIntros "[# [SHOTK [CORR BLACK]] [TH DUTY]]".
        rewrite OpenMod.unfold_iter. rred.
        iApply (stsim_yieldR with "[DUTY]").
        { msubtac. }
        { iFrame. }
        iIntros "DUTY WHITE".
        rred. iApply stsim_tauR. rred.
        rewrite close_itree_call. ss.
        unfold SCMem.load_fun, Mod.wrap_fun.
        rred. iApply (stsim_yieldR with "[DUTY]").
        { msubtac. }
        { iFrame. }
        iIntros "DUTY _".
        iopen 0 "[% [MEM ST]]" "K0".
        rred. iApply stsim_getR. iSplit.
        { iFrame. }
        rred. iApply stsim_tauR. rred.
        iopen 1 "[FALSE|[% H]]" "K1".
        { iExFalso. iApply OneShotP.pending_not_shot. iSplit; [|iApply "SHOTK"].
          iDestruct "FALSE" as "[[? ?] ?]". iFrame.
        }
        iDestruct "H" as "[X [Y|Y]]".
        { iPoseProof (OneShotP.shot_agree with "[X]") as "%".
          { iSplit.
            { iApply "SHOTK". }
            { iDestruct "X" as "[[[H ?] ?] ?]". iApply "H". }
          }
          subst.
          iPoseProof (ObligationRA.correl_thread_correlate with "CORR WHITE") as "> [WHITE|WHITE]"; cycle 1.
          { iExFalso. iApply (ObligationRA.pending_not_shot with "[Y] WHITE").
            iDestruct "Y" as "[_ ?]". eauto.
          }
          iPoseProof (memory_ra_load with "MEM [Y]") as "%".
          { iDestruct "Y" as "[? _]". iFrame. }
          des. rewrite H1.
          rred. iApply stsim_tauR.
          iMod ("K0" with "[MEM ST]") as "_".
          { iExists _. iFrame. }
          iMod ("K1" with "[X Y]") as "_".
          { iRight. iExists _. iFrame. }
          { msubtac. }
          rred. iApply (stsim_yieldR with "[DUTY]").
          { msubtac. }
          { iFrame. }
          iIntros "DUTY _".
          rred. iApply stsim_tauR.
          rred. rewrite close_itree_call. ss.
          unfold SCMem.compare_fun, Mod.wrap_fun.
          rred. iApply (stsim_yieldR with "[DUTY]").
          { msubtac. }
          { iFrame. }
          iIntros "DUTY _".
          iopen 0 "[% [MEM ST]]" "K0".
          rred. iApply stsim_getR. iSplit.
          { iFrame. }
          iMod ("K0" with "[MEM ST]") as "_".
          { iExists _. iFrame. }
          { msubtac. }
          rred. iApply stsim_tauR.
          rred. iApply stsim_tauR.
          rred. iApply (stsim_yieldR with "[DUTY]").
          { msubtac. }
          { iFrame. }
          iIntros "DUTY _".
          rred. iApply stsim_tauR.
          rred. iApply stsim_tauR.
          iPoseProof (ObligationRA.black_white_decr_one with "BLACK WHITE") as "> [% [# BLACK1 %]]".
          iApply IH; eauto. iFrame. iModIntro. iSplit; auto.
        }
        { iPoseProof (memory_ra_load with "MEM [Y]") as "%".
          { iDestruct "Y" as "[? _]". iFrame. }
          des. rewrite H1.
          rred. iApply stsim_tauR.
          iMod ("K0" with "[MEM ST]") as "_".
          { iExists _. iFrame. }
          iMod ("K1" with "[X Y]") as "_".
          { iRight. iExists _. iFrame. }
          { msubtac. }
          rred. iApply (stsim_yieldR with "[DUTY]").
          { msubtac. }
          { iFrame. }
          iIntros "DUTY _".
          rred. iApply stsim_tauR.
          rred. rewrite close_itree_call. ss.
          unfold SCMem.compare_fun, Mod.wrap_fun.
          rred. iApply (stsim_yieldR with "[DUTY]").
          { msubtac. }
          { iFrame. }
          iIntros "DUTY _".
          iopen 0 "[% [MEM ST]]" "K0".
          rred. iApply stsim_getR. iSplit.
          { iFrame. }
          iMod ("K0" with "[MEM ST]") as "_".
          { iExists _. iFrame. }
          { msubtac. }
          rred. iApply stsim_tauR.
          rred. iApply stsim_tauR.
          rred. iApply (stsim_sync with "[DUTY]").
          { msubtac. }
          { iFrame. }
          iIntros "DUTY _".
          rred. iApply stsim_tauR.
          rred. iApply stsim_ret.
          iModIntro. iFrame. auto.
        }
      }

  Abort.

  Let config := [("thread1", tt↑); ("thread2", tt↑)].

  Lemma client_correct:
    UserSim.sim ClientSpec.mod ClientImpl.mod
                (prog2ths ClientSpec.mod config)
                (prog2ths ClientImpl.mod config).
  Proof.
    refine (@UserSim.mk _ _ _ _ ord_wf nat_wf _ _ Σ _ _).
    { econs. exact 0. }
    { i. exists (S o0). ss. }
    ss.
    cut (forall tid,
            (own_thread tid ** ObligationRA.duty (inl tid) []) ⊢ stsim I tid [0; 1] ibot5 ibot5 (fun r_src r_tgt => own_thread tid ** ObligationRA.duty (inl tid) [] ** ⌜r_src = r_tgt⌝) (example_spec_fun tt) (OMod.close_itree (example_omod) (SCMem.mod [1; 1]) (example_fun tt))).
    { admit. }
    iIntros (?) "[TH DUTY]". unfold example_spec_fun, example_fun.
    lred. rred. rewrite close_itree_call. ss. rred.
    iApply (stsim_yieldR with "[DUTY]"); [msubtac|iFrame|]. iIntros "DUTY _".
    rred. unfold SCMem.cas_fun, Mod.wrap_fun. rred.
    iopen 0 "[% [MEM ST]]" "K0".
    iApply stsim_getR. iSplit.
    { iFrame. }
    rred. iApply stsim_tauR. rred.
    unfold SCMem.cas.
    iopen 1 "[[[POINTL POINTF] PEND]|[% H]]" "K1".
  Abort.

End SIM.
