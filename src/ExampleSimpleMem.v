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


  Require Import Coq.Sorting.Mergesort.

  Create HintDb mset.
  Hint Unfold NatSort.sort: mset.
  Ltac msimpl := autounfold with mset; simpl.

  Ltac iopen i H K :=
    let str := constr:(String.append "[" (String.append H (String.append " " (String.append K "]")))) in
    let Inv := fresh "I" in
    evar (Inv: nat -> iProp);
    ((iPoseProof (@MUpd_open _ Inv i) as "> _H";
      [mset_sub_tac|
        let x := (eval cbn in (Inv i)) in
        change (Inv i) with x;
        subst Inv;
        msimpl;
        iDestruct "_H" as str])
     +
       (iPoseProof (@MUpd_open _ Inv i) as "> _H";
        [let x := (eval cbn in (Inv i)) in
         change (Inv i) with x;
         subst Inv;
         msimpl;
         iDestruct "_H" as str])).

  Lemma cut_white k n o
    :
    (ObligationRA.white k (o × (S n))%ord)
      -∗
      (ObligationRA.white k (o × n)%ord ** ObligationRA.white k o).
  Proof.
    iIntros "WHITE".
    iApply (ObligationRA.white_split_eq with "[WHITE]").
    iApply (ObligationRA.white_eq with "WHITE").
    rewrite Ord.from_nat_S. rewrite Jacobsthal.mult_S.
    rewrite Hessenberg.add_comm. reflexivity.
  Qed.


  Global Program Instance oneshot_shot_persistent (A: Type)
         `{@GRA.inG (OneShot.t A) Σ}
         (a: A)
    :
    Persistent (OwnM (OneShot.shot a)).
  Next Obligation.
    i. iIntros "H". iPoseProof (own_persistent with "H") as "# G". ss.
  Qed.

  Lemma oneshot_agree (A: Type)
        `{@GRA.inG (OneShot.t A) Σ}
        (a0 a1: A)
    :
    (OwnM (OneShot.shot a0) ∧ (OwnM (OneShot.shot a1)))
      -∗
      (⌜a0 = a1⌝).
  Proof.
    iIntros "[# H0 # H1]".
    iCombine "H0 H1" as "H". iOwnWf "H". apply OneShot.shot_agree in H0. auto.
  Qed.

  Lemma oneshot_pending_not_shot (A: Type)
        `{@GRA.inG (OneShot.t A) Σ}
        (a: A) q
    :
    (OwnM (OneShot.pending A q) ∧ (OwnM (OneShot.shot a)))
      -∗
      False.
  Proof.
    iIntros "[H0 # H1]".
    iCombine "H0 H1" as "H". iOwnWf "H". apply OneShot.pending_not_shot in H0. auto.
  Qed.


  Lemma sim: ModSim.mod_sim example_spec_mod example_mod.
  Proof.
    refine (@ModSim.mk _ _ nat_wf nat_wf _ _ Σ _ _ _).
    { econs. exact 0. }
    { i. exists (S o0). ss. }
    { admit. }
    { cut (forall tid,
              (own_thread tid ** ObligationRA.duty (inl tid) []) ⊢ stsim I tid [0; 1] ibot5 ibot5 (fun r_src r_tgt => own_thread tid ** ObligationRA.duty (inl tid) [] ** ⌜r_src = r_tgt⌝) (example_spec_fun tt) (OMod.close_itree (example_omod) (SCMem.mod [1; 1]) (example_fun tt))).
      { admit. }
      iIntros (?) "[TH DUTY]". unfold example_spec_fun, example_fun.
      lred. rred. rewrite close_itree_call. ss. rred.
      iApply (stsim_yieldR with "[DUTY]"); [mset_sub_tac|iFrame|]. iIntros "DUTY _".
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
        iPoseProof (cut_white with "WHITES") as "[WHITES WHITE]".
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
        { mset_sub_tac. }
        iPoseProof (cut_white with "WHITES") as "[WHITES WHITE]".
        msimpl. iApply (stsim_yieldR with "[DUTY WHITE]").
        { mset_sub_tac. }
        { iFrame. iSplit; auto. }
        iIntros "DUTY _".
        rred. iApply stsim_tauR.
        iPoseProof (cut_white with "WHITES") as "[WHITES WHITE]".
        rred. iApply (stsim_yieldR with "[DUTY WHITE]").
        { mset_sub_tac. }
        { iFrame. iSplit; auto. }
        iIntros "DUTY _".
        rred. iApply stsim_tauR.
        rred. rewrite close_itree_call. ss.
        iPoseProof (cut_white with "WHITES") as "[WHITES WHITE]".
        rred. iApply (stsim_yieldR with "[DUTY WHITE]").
        { mset_sub_tac. }
        { iFrame. iSplit; auto. }
        iIntros "DUTY _".
        unfold SCMem.store_fun, Mod.wrap_fun. rred.
        iopen 0 "[% [MEM ST]]" "K0".
        iApply stsim_getR. iSplit.
        { iFrame. }
        rred. iApply stsim_tauR. rred.
        iopen 1 "[[[POINTL POINTF] PEND]|[% [H H1]]]" "K1".
        { iExFalso. iApply oneshot_pending_not_shot. iSplit; iFrame. auto. }
        { iPoseProof (oneshot_agree with "[H]") as "%".
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
            { mset_sub_tac. }
            iPoseProof (ObligationRA.duty_done with "DUTY OSHOT") as "> DUTY".
            iApply (stsim_sync with "[DUTY]").
            { mset_sub_tac. }
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
        { mset_sub_tac. }
        rred. iStopProof. pattern n. revert n.
        apply (well_founded_induction Ord.lt_well_founded). intros o IH.
        iIntros "[# [SHOTK [CORR BLACK]] [TH DUTY]]".
        rewrite OpenMod.unfold_iter. rred.
        iApply (stsim_yieldR with "[DUTY]").
        { mset_sub_tac. }
        { iFrame. }
        iIntros "DUTY WHITE".
        rred. iApply stsim_tauR. rred.
        rewrite close_itree_call. ss.
        unfold SCMem.load_fun, Mod.wrap_fun.
        rred. iApply (stsim_yieldR with "[DUTY]").
        { mset_sub_tac. }
        { iFrame. }
        iIntros "DUTY _".
        iopen 0 "[% [MEM ST]]" "K0".
        rred. iApply stsim_getR. iSplit.
        { iFrame. }
        rred. iApply stsim_tauR. rred.
        iopen 1 "[FALSE|[% H]]" "K1".
        { iExFalso. iApply oneshot_pending_not_shot. iSplit; [|iApply "SHOTK"].
          iDestruct "FALSE" as "[[? ?] ?]". iFrame.
        }
        iDestruct "H" as "[X [Y|Y]]".
        { iPoseProof (memory_ra_load with "MEM [Y]") as "%".
          { iDestruct "Y" as "[? _]". iFrame. }
          des. rewrite H1.
          rred. iApply stsim_tauR.
          iMod ("K0" with "[MEM ST]") as "_".
          { iExists _. iFrame. }
          iMod ("K1" with "[X Y]") as "_".
          { iRight. iExists _. iFrame. }
          { mset_sub_tac. }
          rred. iApply (stsim_yieldR with "[DUTY]").
          { mset_sub_tac. }
          { iFrame. }
          iIntros "DUTY _".
          rred. iApply stsim_tauR.
          rred. rewrite close_itree_call. ss.
          unfold SCMem.compare_fun, Mod.wrap_fun.
          rred. iApply (stsim_yieldR with "[DUTY]").
          { mset_sub_tac. }
          { iFrame. }
          iIntros "DUTY _".
          iopen 0 "[% [MEM ST]]" "K0".
          rred. iApply stsim_getR. iSplit.
          { iFrame. }
          iMod ("K0" with "[MEM ST]") as "_".
          { iExists _. iFrame. }
          { mset_sub_tac. }
          rred. iApply stsim_tauR.
          rred. iApply stsim_tauR.
          rred. iApply (stsim_yieldR with "[DUTY]").
          { mset_sub_tac. }
          { iFrame. }
          iIntros "DUTY _".
          rred. iApply stsim_tauR.
          rred. iApply stsim_tauR.
          iPoseProof (ObligationRA.black_white_decr_one with "BLACK WHITE

          iApply IH.

          rred.


 ss.

iApply (stsim_yieldR with "[DUTY]").
          { mset_sub_tac. }
          { iFrame. }
          iIntros "DUTY _".

iApply stsim_tauR.

clarify.
          i.

des; clarify.


iApply st
        {

[[[[# SHOTK # CORR] [% # BLACK]] POINTL] F]

        rred. iApply stsim_tauR. rred.
        iopen 1 "[FALSE|[% H]]" "K1".
        { iExFalso. iApply oneshot_pending_not_shot. iSplit; [|iApply "SHOTK"].
          iDestruct "FALSE" as "[[? ?] ?]". iFrame.
        }

OneShot.pending_not_shot.

        rred.

iApply (stsim_yieldR with "[DUTY]").
        { mset_sub_tac. }
        { iFrame. }
        iIntros "DUTY _".

        rred.

        iApply (stsi        iopen 0 "[% [MEM ST]]" "K0".
                iApply stsim_getR. iSplit.
                { iFrame. }
                rred. iApply stsim_tauR. rred.
                unfold SCMem.cas.
                iopen 1 "[[[POINTL POINTF] PEND]|[% H]]" "K1".

iFrame. iSplit; auto. }

ired.

  "SHOTK" : OwnM (OneShot.shot k)
  "CORR" : ObligationRA.correl_thread k 1
  "BLACK" : ObligationRA.black k n
  --------------------------------------□
  "TH" : own_thread tid
  "DUTY" : ObligationRA.duty (inl tid) []


        iPoseProof (memory_ra_store with "MEM POINTL") as "[% [% > [MEM POINTL]]]".
        rewrite H1. ss.
        rred. iApply stsim_getR. iSplit.
        { iFrame. }
        rred. iApply (stsim_putR with "ST"). iIntros "ST".
        rred. iApply stsim_tauR.
        rred. iApply stsim_tauR.
        rred.
        iPoseProof (@ObligationRA.alloc _ _ ((1 × Ord.omega) × 10)%ord) as "> [% [[BLACK WHITES] OBL]]".
        iPoseProof (cut_white with "WHITES") as "[WHITES WHITE]".
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
          { iSplit; [iApply "SHOTP"|iApply "CORR"]. }
          { iLeft. iFrame. }
        }
        { mset_sub_tac. }
        iPoseProof (cut_white with "WHITES") as "[WHITES WHITE]".
        msimpl. iApply (stsim_yieldR with "[DUTY WHITE]").
        { mset_sub_tac. }
        { iFrame. iSplit; auto. }
        iIntros "DUTY _".
        rred. iApply stsim_tauR.
        iPoseProof (cut_white with "WHITES") as "[WHITES WHITE]".
        rred. iApply (stsim_yieldR with "[DUTY WHITE]").
        { mset_sub_tac. }
        { iFrame. iSplit; auto. }
        iIntros "DUTY _".
        rred. iApply stsim_tauR.
        rred. rewrite close_itree_call. ss.
        iPoseProof (cut_white with "WHITES") as "[WHITES WHITE]".
        rred. iApply (stsim_yieldR with "[DUTY WHITE]").
        { mset_sub_tac. }
        { iFrame. iSplit; auto. }
        iIntros "DUTY _".
        unfold SCMem.store_fun, Mod.wrap_fun. rred.
        iopen 0 "[% [MEM ST]]" "K0".
        iApply stsim_getR. iSplit.
        { iFrame. }
        rred. iApply stsim_tauR. rred.
        iopen 1 "[[[POINTL POINTF] PEND]|[% [H H1]]]" "K1".
        { iExFalso. iCombine "PEND SHOTP" as "SHOT". iOwnWf "SHOT".
          apply OneShot.pending_not_shot in H2. ss.
        }
        { iAssert (OwnM (OneShot.shot k0)) with "[H]" as "# SHOT".
          { iDestruct "H" as "[[H _] _]". iApply "H". }
          iCombine "SHOTP SHOT" as "SHOTEQ". iOwnWf "SHOTEQ".
          apply OneShot.shot_agree in H2. subst.
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
            { mset_sub_tac. }
            iPoseProof (ObligationRA.duty_done with "DUTY OSHOT") as "> DUTY".
            iApply (stsim_sync with "[DUTY]").
            { mset_sub_tac. }
            { iFrame. }
            iIntros "DUTY _".
            iApply stsim_tauR.
            iApply stsim_ret. iModIntro. iFrame. auto.
          }
          { iExFalso. iApply (ObligationRA.pending_not_shot with "OBL0 OBL1"). }
        }
      }

iCombine "


iExfalso
rred.

        iPoseProof (memory_ra_store with "MEM POINTF") as "[% [% > [MEM POINTF]]]".
        rewrite H2. ss.
        rred. iApply stsim_getR. iSplit.
        { iFrame. }
        rred. iApply (stsim_putR with "ST"). iIntros "ST".
        rred. iApply stsim_tauR.
        rred. iApply stsim_tauR.
        iApply (stsim_dealloc_obligation with "ONG").
        { ss. }
        iIntros "# DONE". iPoseProof ("EVT" with "DONE POINTF") as "EVT".
        iAssert I with "[MEM POINTL ST MONO EVT]" as "INV".
        { unfold I. iSplitL "MEM ST".
          { iExists _. iFrame. }
          iExists (W_own _). ss. iFrame.
        }
        rred. iApply (@stsim_sync _ _ _ _ _ _ _ None). iSplitR "".
        { ss. auto. }
        iIntros "INV _". iApply stsim_tauR. iApply stsim_ret. auto.
      }


        unfold SCMem.cas.


        iDestruct "INV" as "[[% [MEM ST]] [% [MONO H]]]".
        rred. iApply stsim_getR. iSplit.
        { iFrame. }
        rred. iApply stsim_tauR. rred.
iApply stsim_tauR.
        rred. rewrite close_itree_call. ss.
        rred.

iPoseP

        rred.


ss. unfold ObligationRA.tax. ss.
        {

 _ _ _ _ _ _ _ None). iSplitR "EXCL NEG".
        { ss. iFrame. auto. }
        iIntros "INV _".
        iPoseProof (Neg_split with "NEG") as "> [FUEL NEG]". { eapply ord_mult_split. }


ObligationRA.duty_correl with "DUTY") as "# CORR"; [ss; eauto|].


        ObligationRA.white

        iApply (@stsim_alloc_obligation _ _ _ _ _ _ _ (Ord.large × 10)%ord). iIntros "% PEND NEG # POS".
        iPoseProof (pending_eventually with "PEND POINTF") as "> EVT".
        iPoseProof (black_updatable with "MONO") as "> MONO".
        { instantiate (1:=W_own k). econs. }
        iPoseProof (black_persistent_white with "MONO") as "# MWHITE".
        iPoseProof (Neg_split with "NEG") as "> [FUEL NEG]". { eapply ord_mult_split. }
        iAssert I with "[MEM POINTL ST MONO EVT]" as "INV".
        { unfold I. iSplitL "MEM ST".
          { iExists _. iFrame. }
          iExists (W_own _). ss. iFrame.
        }

        rred. iApply (@stsim_yieldR _ _ _ _ _ _ _ None). iSplitR "EXCL NEG".
        { ss. iFrame. auto. }
        iIntros "INV _".
        iPoseProof (Neg_split with "NEG") as "> [FUEL NEG]". { eapply ord_mult_split. }
        rred. iApply stsim_tauR.
        rred. iApply (@stsim_yieldR _ _ _ _ _ _ _ None). ss. iFrame. iSplitR; auto.
        iIntros "INV _".
        iPoseProof (Neg_split with "NEG") as "> [FUEL NEG]". { eapply ord_mult_split. }

        rred. iApply stsim_tauR.
        rred. rewrite close_itree_call. ss.
        rred. iApply (@stsim_yieldR _ _ _ _ _ _ _ None). ss. iFrame. iSplitR; auto.
        iIntros "INV _".
        iPoseProof (Neg_split with "NEG") as "> [FUEL NEG]". { eapply ord_mult_split. }

        unfold SCMem.store_fun, Mod.wrap_fun.
        iDestruct "INV" as "[[% [MEM ST]] [% [MONO H]]]".
        rred. iApply stsim_getR. iSplit.
        { iFrame. }
        rred. iApply stsim_tauR. rred.

        iPoseProof (black_white_compare with "MWHITE MONO") as "%". inv H2.
        ss. iDestruct "H" as "[POINTL EVT]".
        iPoseProof (eventually_unfold with "EVT") as "[[[ONG POINTF] [EVT _]]|[[DONE POINTF] EVT]]".
        2:{ iApply (stsim_obligation_not_done with "DONE"); ss. auto. }
        iPoseProof (memory_ra_store with "MEM POINTF") as "[% [% > [MEM POINTF]]]".
        rewrite H2. ss.
        rred. iApply stsim_getR. iSplit.
        { iFrame. }
        rred. iApply (stsim_putR with "ST"). iIntros "ST".
        rred. iApply stsim_tauR.
        rred. iApply stsim_tauR.
        iApply (stsim_dealloc_obligation with "ONG").
        { ss. }
        iIntros "# DONE". iPoseProof ("EVT" with "DONE POINTF") as "EVT".
        iAssert I with "[MEM POINTL ST MONO EVT]" as "INV".
        { unfold I. iSplitL "MEM ST".
          { iExists _. iFrame. }
          iExists (W_own _). ss. iFrame.
        }
        rred. iApply (@stsim_sync _ _ _ _ _ _ _ None). iSplitR "".
        { ss. auto. }
        iIntros "INV _". iApply stsim_tauR. iApply stsim_ret. auto.
      }

      { iDestruct "H" as "[POINTL EVT]".
        iPoseProof (memory_ra_load with "MEM POINTL") as "%". des; clarify.
        iPoseProof  (eventually_obligation with "EVT") as "# READY".
        iPoseProof (Ready_Pos with "READY") as "[% OBL]".
        rewrite H. ss.
        rred. iApply stsim_tauR.
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
        iApply (@stsim_yieldR _ _ _ _ _ _ _ (Some k)).
        ss. iFrame. iSplitL; auto. iIntros "INV FUEL".
        rred. iApply stsim_tauR.
        rred. rewrite close_itree_call. ss.
        unfold SCMem.load_fun, Mod.wrap_fun. ss.
        rred. iApply (@stsim_yieldR _ _ _ _ _ _ _ None). ss. iFrame. iIntros "INV _".
        iDestruct "INV" as "[[% [MEM ST]] [% [MONO H]]]".
        rred. iApply stsim_getR. iSplit. { iFrame. }
        rred. iApply stsim_tauR. rred.
        iPoseProof (black_white_compare with "WHITE MONO") as "%". inv H1.
        ss. iDestruct "H" as "[POINTL EVT]".
        iPoseProof (eventually_unfold with "EVT") as "[[[ONG POINTF] [_ EVT]]|[[DONE POINTF] EVT]]".
        { iDestruct "FUEL" as "[FUEL|#DONE]"; cycle 1.
          { iExFalso. iApply (Ongoing_not_Done with "ONG DONE"). }
          iPoseProof (memory_ra_load with "MEM POINTF") as "%". des. rewrite H1.
          rred. iApply stsim_tauR.
          iAssert I with "[MEM POINTL ST MONO EVT ONG POINTF]" as "INV".
          { unfold I. iSplitL "MEM ST".
            { iExists _. iFrame. }
            iExists (W_own _). ss. iFrame. iApply ("EVT" with "ONG POINTF").
          }
          rred. iApply (@stsim_yieldR _ _ _ _ _ _ _ None). ss. iSplitR "FUEL".
          { iSplit; auto. }
          iIntros "INV _".
          rred. iApply stsim_tauR.
          rred. rewrite close_itree_call. ss.
          unfold SCMem.compare_fun, Mod.wrap_fun. ss.
          rred. iApply (@stsim_yieldR _ _ _ _ _ _ _ None). ss. iFrame. iIntros "INV _".
          rred. iDestruct "INV" as "[[% [MEM ST]] [% [MONO H]]]".
          iApply stsim_getR. iSplit. { iFrame. }
          rred. iApply stsim_tauR.
          rred. iApply stsim_tauR.
          iAssert I with "[MEM ST MONO H]" as "INV".
          { unfold I. iSplitL "MEM ST".
            { iExists _. iFrame. }
            iExists _. iFrame.
          }
          rred. iApply (@stsim_yieldR _ _ _ _ _ _ _ None). ss. iSplitR "FUEL".
          { iSplit; auto. }
          iIntros "INV _".
          rred. iApply stsim_tauR.
          rred. iApply stsim_tauR.
          iPoseProof (Pos_Neg_annihilate with "OBL FUEL") as "> [% [H %]]".
          iClear "OBL". iPoseProof (Pos_persistent with "H") as "# OBL".
          iApply IH; eauto. iSplit; auto. iClear "INV H". auto.
        }
        { iPoseProof (memory_ra_load with "MEM POINTF") as "%". des. rewrite H1.
          rred. iApply stsim_tauR.
          iAssert I with "[MEM POINTL ST MONO EVT POINTF]" as "INV".
          { unfold I. iSplitL "MEM ST".
            { iExists _. iFrame. }
            iExists (W_own _). ss. iFrame. iApply "EVT". auto.
          }
          rred. iApply (@stsim_yieldR _ _ _ _ _ _ _ None). ss. iSplitL.
          { iSplit; auto. }
          iIntros "INV _".
          rred. iApply stsim_tauR.
          rred. rewrite close_itree_call. ss.
          unfold SCMem.compare_fun, Mod.wrap_fun.
          rred. iApply (@stsim_yieldR _ _ _ _ _ _ _ None). ss. iFrame. iIntros "INV _".
          iDestruct "INV" as "[[% [MEM ST]] [% [MONO H]]]".
          rred. iApply stsim_getR. iSplit; [eauto|].
          rred. iApply stsim_tauR.
          rred. iApply stsim_tauR.
          iAssert I with "[MEM ST MONO H]" as "INV".
          { unfold I. iSplitL "MEM ST".
            { iExists _. iFrame. }
            iExists _. iFrame.
          }
          rred. iApply (@stsim_sync _ _ _ _ _ _ _ None). ss. iSplitL.
          { iSplit; auto. }
          iIntros "INV _". rred. iApply stsim_tauR.
          rred. iApply stsim_ret. auto.
        }
      }
    }
  Admitted.
End SIM.
