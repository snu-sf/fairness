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
From Fairness Require Import ModSim PCM MonotonePCM ThreadsRA StateRA FairRA.

Section SIM.
  Context `{Σ: GRA.t}.
  Context `{EXCL: @GRA.inG (Excl.t unit) Σ}.
  Context `{MONORA: @GRA.inG monoRA Σ}.
  Context `{THSRA: @GRA.inG ths_RA Σ}.
  Context `{STATESRC: @GRA.inG (stateSrcRA unit) Σ}.
  Context `{STATETGT: @GRA.inG (stateTgtRA (unit * SCMem.t)) Σ}.
  Context `{IDENTSRC: @GRA.inG (identSrcRA void nat_wf) Σ}.
  Context `{IDENTTGT: @GRA.inG (identTgtRA (void + SCMem.pointer)%type) Σ}.
  Context `{IDENTTHS: @GRA.inG identThsRA Σ}.
  Context `{MEMRA: @GRA.inG memRA Σ}.

  Variant W: Type :=
    | W_bot
    | W_own (k: nat)
  .

  Variant W_le: W -> W -> Prop :=
    | W_le_bot
        w
      :
      W_le W_bot w
    | W_le_th
        k
      :
      W_le (W_own k) (W_own k)
  .

  Global Program Instance le_PreOrder: PreOrder Nat.le.

  Program Instance W_le_PreOrder: PreOrder W_le.
  Next Obligation.
  Proof.
    ii. destruct x; econs.
  Qed.
  Next Obligation.
  Proof.
    ii. inv H; inv H0; try econs; eauto.
  Qed.

  Let I_aux (w: W): iProp :=
        (match w with
         | W_bot => points_to loc_l (SCMem.val_nat 0) ** points_to loc_f (SCMem.val_nat 0) ** (OwnM (Excl.just tt: @URA.car (Excl.t unit)))
         | W_own k =>
             (points_to loc_l (SCMem.val_nat 1))
               **
               Eventually k (points_to loc_f (SCMem.val_nat 0)) (points_to loc_f (SCMem.val_nat 1))
         end)
  .

  Let I: iProp :=
        (∃ m,
            (memory_black m)
              **
              (St_tgt (tt, m)))
          **
          (∃ w,
              (monoBlack 0 W_le_PreOrder w)
                **
                I_aux w).

  Lemma sim: ModSim.mod_sim example_spec_mod example_mod.
  Proof.
    refine (@ModSim.mk _ _ nat_wf nat_wf _ _ Σ _ _ _).
    { econs. exact 0. }
    { i. exists (S o0). ss. }
    { admit. }
    { cut (forall tid,
              I ⊢ fsim I tid itop6 itop6 (fun r_src r_tgt os => I ** ⌜r_src = r_tgt /\ os = []⌝) (example_spec_fun tt) (OMod.close_itree (example_omod) (SCMem.mod [1; 1]) (example_fun tt)) []).
      { admit. }
      i. iIntros "INV". ss. unfold example_spec_fun, example_fun.

      lred. rred. rewrite close_itree_call. ss. rred.
      iApply (@fsim_yieldR _ _ _ _ _ _ _ None). ss. iFrame. iIntros "INV _".
      rred. unfold SCMem.cas_fun, Mod.wrap_fun. rred.
      iDestruct "INV" as "[[%m [MEM ST]] [%w [MONO H]]]".
      iApply fsim_getR. iSplit.
      { iFrame. }
      rred. iApply fsim_tauR. rred.

      unfold SCMem.cas.
      destruct w; ss.
      { iDestruct "H" as "[[POINTL POINTF] EXCL]".
        iPoseProof (memory_ra_load with "MEM POINTL") as "%". ss. des; clarify.
        rewrite H. ss.
        iPoseProof (memory_ra_store with "MEM POINTL") as "[% [% > [MEM POINTL]]]".
        rewrite H1. ss.
        rred. iApply fsim_getR. iSplit.
        { iFrame. }
        rred. iApply (fsim_putR with "ST"). iIntros "ST".
        rred. iApply fsim_tauR.
        rred. iApply fsim_tauR.

        iApply (@fsim_alloc_obligation _ _ _ _ _ _ _ (Ord.large × 10)%ord). iIntros "% PEND NEG # POS".
        iPoseProof (pending_eventually with "PEND POINTF") as "> EVT".
        iPoseProof (black_updatable with "MONO") as "> MONO".
        { instantiate (1:=W_own k). econs. }
        iPoseProof (black_persistent_white with "MONO") as "# MWHITE".
        iPoseProof (Neg_split with "NEG") as "> [FUEL NEG]". { eapply ord_mult_split. }

        rred. iApply (@fsim_yieldR _ _ _ _ _ _ _ None). iSplitR "EXCL NEG".
        { ss. iFrame. iSplitL; auto. iSplit; auto. iSplitL "MEM ST".
          { iExists _. iFrame. }
          iExists _. iFrame.
        }
        iIntros "INV _".
        iPoseProof (Neg_split with "NEG") as "> [FUEL NEG]". { eapply ord_mult_split. }
        rred. iApply fsim_tauR.
        rred. iApply (@fsim_yieldR _ _ _ _ _ _ _ None). ss. iFrame. iSplitR; auto.
        iIntros "INV _".
        iPoseProof (Neg_split with "NEG") as "> [FUEL NEG]". { eapply ord_mult_split. }

        rred. iApply fsim_tauR.
        rred. rewrite close_itree_call. ss.
        rred. iApply (@fsim_yieldR _ _ _ _ _ _ _ None). ss. iFrame. iSplitR; auto.
        iIntros "INV _".
        iPoseProof (Neg_split with "NEG") as "> [FUEL NEG]". { eapply ord_mult_split. }

        unfold SCMem.store_fun, Mod.wrap_fun.
        iDestruct "INV" as "[[% [MEM ST]] [% [MONO H]]]".
        rred. iApply fsim_getR. iSplit.
        { iFrame. }
        rred. iApply fsim_tauR. rred.

        iPoseProof (black_white_compare with "MWHITE MONO") as "%". inv H2.
        ss. iDestruct "H" as "[POINTL EVT]".
        iPoseProof (eventually_unfold with "EVT") as "[[[ONG POINTF] [EVT _]]|[[DONE POINTF] EVT]]".
        2:{ iApply (fsim_obligation_not_done with "DONE"); ss. auto. }
        iPoseProof (memory_ra_store with "MEM POINTF") as "[% [% > [MEM POINTF]]]".
        rewrite H2. ss.
        rred. iApply fsim_getR. iSplit.
        { iFrame. }
        rred. iApply (fsim_putR with "ST"). iIntros "ST".
        rred. iApply fsim_tauR.
        rred. iApply fsim_tauR.
        iApply (fsim_dealloc_obligation with "ONG").
        { ss. }
        iIntros "# DONE". iPoseProof ("EVT" with "DONE POINTF") as "EVT".
        rred. iApply (@fsim_sync _ _ _ _ _ _ _ None). iSplitR "".
        { ss. unfold I. iSplit; auto. iSplit; auto. iSplitL "MEM ST".
          { iExists _. iFrame. }
          iExists _. iFrame. ss. iFrame.
        }
        iIntros "INV _". iApply fsim_tauR. iApply fsim_ret. auto.
      }

      { iDestruct "H" as "[POINTL EVT]".
        iPoseProof (memory_ra_load with "MEM POINTL") as "%". des; clarify.
        iPoseProof  (eventually_obligation with "EVT") as "# READY".
        iPoseProof (Ready_Pos with "READY") as "[% OBL]".
        rewrite H. ss.
        rred. iApply fsim_tauR.
        rred.
        iPoseProof (black_persistent_white with "MONO") as "# WHITE".
        iAssert I with "[MEM ST MONO POINTL EVT]" as "INV".
        { unfold I. iSplitL "MEM ST".
          { iExists _. iFrame. }
          iExists (W_own _). ss. iFrame.
        }
        iStopProof.
        pattern n. revert n. eapply (well_founded_induction Ord.lt_well_founded). intros o IH.
        iIntros "[# [READY [OBL WHITE]] INV]".
        rewrite unfold_iter_eq. rred.
        iApply (@fsim_yieldR _ _ _ _ _ _ _ (Some k)).
        ss. iFrame. iSplitL; auto. iIntros "INV FUEL".
        rred. iApply fsim_tauR.
        rred. rewrite close_itree_call. ss.
        unfold SCMem.load_fun, Mod.wrap_fun. ss.
        rred. iApply (@fsim_yieldR _ _ _ _ _ _ _ None). ss. iFrame. iIntros "INV _".
        iDestruct "INV" as "[[% [MEM ST]] [% [MONO H]]]".
        rred. iApply fsim_getR. iSplit. { iFrame. }
        rred. iApply fsim_tauR. rred.
        iPoseProof (black_white_compare with "WHITE MONO") as "%". inv H1.
        ss. iDestruct "H" as "[POINTL EVT]".
        iPoseProof (eventually_unfold with "EVT") as "[[[ONG POINTF] [_ EVT]]|[[DONE POINTF] EVT]]".
        { iDestruct "FUEL" as "[FUEL|#DONE]"; cycle 1.
          { iExFalso. iApply (Ongoing_not_Done with "ONG DONE"). }
          iPoseProof (memory_ra_load with "MEM POINTF") as "%". des. rewrite H1.
          rred. iApply fsim_tauR.
          rred. iApply (@fsim_yieldR _ _ _ _ _ _ _ None). ss. iSplitR "FUEL".
          { iSplit; auto. iSplit; auto. unfold I. iSplitL "MEM ST".
            { iExists _. iFrame. }
            iExists (W_own _). ss. iFrame. iApply ("EVT" with "ONG POINTF").
          }
          iIntros "INV _".
          rred. iApply fsim_tauR.
          rred. rewrite close_itree_call. ss.
          unfold SCMem.compare_fun, Mod.wrap_fun. ss.
          rred. iApply (@fsim_yieldR _ _ _ _ _ _ _ None). ss. iFrame. iIntros "INV _".
          rred. iDestruct "INV" as "[[% [MEM ST]] [% [MONO H]]]".
          iApply fsim_getR. iSplit. { iFrame. }
          rred. iApply fsim_tauR.
          rred. iApply fsim_tauR.
          rred. iApply (@fsim_yieldR _ _ _ _ _ _ _ None). ss. iSplitR "FUEL".
          { iSplit; auto. iSplit; auto. unfold I. iSplitL "MEM ST".
            { iExists _. iFrame. }
            { iExists _. iFrame. }
          }
          iIntros "INV _".
          rred. iApply fsim_tauR.
          rred. iApply fsim_tauR.
          iPoseProof (Pos_Neg_annihilate with "OBL FUEL") as "> [% [H %]]".
          iClear "OBL". iPoseProof (Pos_persistent with "H") as "# OBL".
          iApply IH; eauto. iSplit; auto. iClear "INV H". auto.
        }
        { iPoseProof (memory_ra_load with "MEM POINTF") as "%". des. rewrite H1.
          rred. iApply fsim_tauR.
          rred. iApply (@fsim_yieldR _ _ _ _ _ _ _ None). ss. iSplitL.
          { iSplit; auto. iSplit; auto. unfold I. iSplitL "MEM ST".
            { iExists _. iFrame. }
            iExists (W_own _). ss. iFrame. iApply ("EVT" with "POINTF").
          }
          iIntros "INV _".
          rred. iApply fsim_tauR.
          rred. rewrite close_itree_call. ss.
          unfold SCMem.compare_fun, Mod.wrap_fun.
          rred. iApply (@fsim_yieldR _ _ _ _ _ _ _ None). ss. iFrame. iIntros "INV _".
          iDestruct "INV" as "[[% [MEM ST]] [% [MONO H]]]".
          rred. iApply fsim_getR. iSplit; [eauto|].
          rred. iApply fsim_tauR.
          rred. iApply fsim_tauR.
          rred. iApply (@fsim_sync _ _ _ _ _ _ _ None). ss. iSplitL.
          { iSplit; auto. iSplit; auto. unfold I. iSplitL "MEM ST".
            { iExists _. iFrame. }
            { iExists _. iFrame. }
          }
          iIntros "INV _". rred. iApply fsim_tauR.
          rred. iApply fsim_ret. auto.
        }
      }
    }
  Admitted.
End SIM.
