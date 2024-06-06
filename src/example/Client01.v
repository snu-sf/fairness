From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Import pind Axioms ITreeLib Red TRed IRed2 WFLibLarge.
From Fairness Require Import FairBeh Mod Concurrency Linking.
From Fairness Require Import PCM IProp IPM IPropAux.
From Fairness Require Import IndexedInvariants OpticsInterp SimWeakest.
From Fairness Require Import TemporalLogic TemporalLogicFull SCMemSpec.

Module Client01.

  Definition gvs : list nat := [1].
  Definition X := SCMem.val_ptr (0, 0).

  Section CODE.

    Notation state := unit.
    Notation ident := void.

    Definition thread1 :
      ktree (threadE ident state) unit SCMem.val
      :=
      fun _ =>
        _ <- trigger Yield;;
        _ <- (OMod.call (R:=unit) "store" (X, (1 : SCMem.val)));; (*TODO : val_nat*)
        _ <- trigger Yield;;
        Ret (0 : SCMem.val).

    Definition thread2 :
      ktree (threadE ident state) unit SCMem.val
      :=
      fun _ =>
        _ <- trigger Yield;;
        a <- (ITree.iter (fun (_ : unit) =>
                            a <- (OMod.call (R:=SCMem.val) "load" X);;
                            b <- (OMod.call (R:=bool) "compare" (a, (SCMem.val_nat 0)));;
                              if b then Ret (inl tt) else Ret (inr a))) tt;;
        _ <- trigger Yield;;
        Ret a.

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

End Client01.

Module Client01Spec.

  Section SPEC.

    Notation state := unit.
    Notation ident := void.

    Definition thread1 :
      ktree (threadE ident state) unit SCMem.val
      :=
      fun _ =>
        _ <- trigger Yield;; Ret (0 : SCMem.val).

    Definition thread2:
      ktree (threadE void unit) unit SCMem.val
      :=
      fun _ =>
        _ <- trigger Yield;; Ret (1 : SCMem.val).

    Definition module : Mod.t :=
      Mod.mk
        tt
        (Mod.get_funs [("thread1", Mod.wrap_fun thread1);
                       ("thread2", Mod.wrap_fun thread2)])
    .

  End SPEC.

End Client01Spec.

Section SPEC.

  Import Client01.

  Notation src_state := (Mod.state Client01Spec.module).
  Notation src_ident := (Mod.ident Client01Spec.module).
  Notation tgt_state := (Mod.state Client01.module).
  Notation tgt_ident := (Mod.ident Client01.module).

  Local Instance STT : StateTypes := Build_StateTypes src_state tgt_state src_ident tgt_ident.
  Context `{Σ : GRA.t}.
  Context {TLRAS : @TLRAs XAtom STT Σ}.
  Context {AUXRAS : AUXRAs Σ}.

  (** Invariants. *)

  (* Namespace for Client01 invariants. *)
  Definition N_Client01 : namespace := (nroot .@ "Client01").
  Definition N_t1_write : namespace := (nroot .@ "t1_write").

  Lemma mask_disjoint_client01 : (↑N_Client01 : coPset) ## (↑N_t1_write : coPset).
  Proof. apply ndot_ne_disjoint. ss. Qed.

  Lemma mask_disjoint_N_Client01_state_tgt : (↑N_Client01 : coPset) ## (↑N_state_tgt : coPset).
  Proof. apply ndot_ne_disjoint. ss. Qed.

  Lemma mask_disjoint_t1_write_state_tgt : (↑N_t1_write : coPset) ## (↑N_state_tgt : coPset).
  Proof. apply ndot_ne_disjoint. ss. Qed.

  Definition t1_write n : Formula n :=
    syn_inv n N_t1_write (X ↦ 1)%F.

  Global Instance t1_write_persistent n : Persistent (⟦t1_write n, n⟧).
  Proof.
    unfold Persistent. iIntros "H". unfold t1_write. rewrite red_syn_inv.
    iDestruct "H" as "#H". auto.
  Qed.

  Definition client01Inv γk k n : Formula n :=
    (◆[k, 2] ∗ ((➢(live γk k (1/2)) ∗ (X ↦ 0)) -U-[k](0)-◇ (➢(dead γk k) ∗ t1_write n)))%F.

  (** Simulation proof. *)

  Lemma Client01_thread1_spec
        tid n
    :
    ⊢ ⟦(∀ (γk k : τ{nat, 1+n}),
           ((⤉ syn_inv n N_Client01 (client01Inv γk k n))
              ∗ (syn_tgt_interp_as n sndl (fun m => (➢ (scm_memory_black m))))
              ∗ TID(tid)
              ∗ (⤉ Duty(tid) [(k, 0, ➢(@dead γk nat k) ∗ t1_write n)])
              ∗ ◇[k](2, 1) ∗ ➢(@live γk nat k (1/2)))
             -∗
             syn_wpsim (S n) tid ∅
             (fun rs rt => (⤉(syn_term_cond n tid _ rs rt))%F)
             false false
             (fn2th Client01Spec.module "thread1" (tt ↑))
             (fn2th Client01.module "thread1" (tt ↑)))%F, 1+n⟧.
  Proof.
    iIntros. red_tl. iIntros (γk). red_tl. iIntros (k). red_tl. simpl.
    iEval (rewrite red_syn_inv; rewrite red_syn_wpsim; rewrite red_syn_tgt_interp_as).

    iIntros "(#INV & #MEM & THDW & DUTY & PCk & LIVE)".

    unfold fn2th. simpl. unfold thread1, Client01Spec.thread1.
    rred2r. lred2r.

    (* Yield *)
    iPoseProof (pc_drop _ 1 _ _ 3 with "PCk") as "DROP". eauto. iMod "DROP".
    iPoseProof (pc_split _ _ 1 2 with "DROP") as "[PC1 PC2]".
    iApply (wpsim_yieldR with "[DUTY PC1]").
    { eauto. }
    { iFrame. simpl. iPoseProof (pcs_cons_fold with "[PC1]") as "FOLD". 2: iFrame. simpl. iFrame. }
    Unshelve. 2: auto.
    iIntros "DUTY CRD". iModIntro. rred2r. iApply wpsim_tauR. rred2r. (*TODO:rred2r?*)
    
    iPoseProof (pc_split _ _ 1 1 with "PC2") as "[PC1 PC2]".
    iApply (wpsim_yieldR with "[DUTY PC1]").
    { eauto. }
    { iFrame. simpl. iPoseProof (pcs_cons_fold with "[PC1]") as "FOLD". 2: iFrame. simpl. iFrame. }
    iIntros "DUTY CRD2". iModIntro. rred2r.

    (* Opening invariant *)
    iInv "INV" as "CI" "CI_CLOSE".
    iEval (unfold client01Inv; simpl; red_tl; simpl; rewrite red_syn_until_tpromise) in "CI".
    iDestruct "CI" as "[#OBL UPROMISE]".

    iEval (unfold until_thread_promise; red_tl; simpl) in "UPROMISE".
    iDestruct "UPROMISE" as "[#PRM [BF | #AF]]"; simpl.
    { (* Live *)
      iEval (red_tl; simpl) in "BF". iDestruct "BF" as "[LIVE2 PT]".
      (* Store *)
      iApply (SCMem_store_fun_spec _ _ _ n with "[PT MEM] [ - ]"). auto.
      { rewrite lookup_insert. pose mask_disjoint_N_Client01_state_tgt. set_solver. }
      { iFrame. auto. }
      iIntros (?) "PTS". rred2r. iApply wpsim_tauR. rred2r.

      iMod ((FUpd_alloc _ _ _ n (N_t1_write) ((X ↦ 1) : Formula n)%F) with "[PTS]") as "#TI". auto.
      { iEval (simpl; red_tl; simpl). auto. }
      iPoseProof (Lifetime.pending_merge with "LIVE LIVE2") as "LIVE".
      iEval (rewrite Qp.half_half) in "LIVE". iMod (Lifetime.pending_shot with "LIVE") as "#DEAD".
      iMod (duty_fulfill with "[DEAD DUTY]") as "DUTY".
      { iSplitL. iFrame. simpl. red_tl. auto. }

      (* Closing the invariant *)
      iMod ("CI_CLOSE" with "[]") as "_".
      { iEval (unfold client01Inv; simpl; red_tl; simpl).
        iSplit; [iApply "OBL" | iEval (rewrite red_syn_until_tpromise)].
        iApply (until_tpromise_make2 with "[]"). simpl. iSplit; auto.
        iEval (red_tl; simpl). iModIntro; iSplit; auto. }

      iApply (wpsim_sync with "[DUTY PC2]").
      { eauto. }
      { iFrame. }
      iIntros "DUTY CRD3". iModIntro. lred2r. rred2r. iApply wpsim_tauR. rred2r.
      iApply wpsim_ret. eauto. iModIntro.
      iEval (unfold term_cond). iSplit; iFrame. iPureIntro; auto. }
    (* After store *)
    { iEval (unfold t1_write; simpl; red_tl; simpl; rewrite red_syn_inv; simpl) in "AF".
      iDestruct "AF" as "[DEAD _]".
      iExFalso. iPoseProof (Lifetime.pending_not_shot with "LIVE DEAD") as "%F". auto.
    }
  Qed.

  Lemma Client01_thread2_spec
        tid n
    :
    ⊢ ⟦(∀ (γk k : τ{nat, 1+n}),
           ((⤉ syn_inv n N_Client01 (client01Inv γk k n))
              ∗ (syn_tgt_interp_as n sndl (fun m => (➢ (scm_memory_black m))))
              ∗ TID(tid) ∗ (⤉ Duty(tid) nil) ∗ ◇[k](2, 1))
             -∗
             syn_wpsim (S n) tid ∅
             (fun rs rt => (⤉(syn_term_cond n tid _ rs rt))%F)
             false false
             (fn2th Client01Spec.module "thread2" (tt ↑))
             (fn2th Client01.module "thread2" (tt ↑)))%F, 1+n⟧.
  Proof.
    iIntros. red_tl. iIntros (γk). red_tl. iIntros (k). red_tl. simpl.
    iEval (rewrite red_syn_inv; rewrite red_syn_wpsim; rewrite red_syn_tgt_interp_as).

    iIntros "(#INV & #MEM & THDW & DUTY & PC)".

    unfold fn2th. simpl. unfold thread2, Client01Spec.thread2.
    rred2r. lred2r.

    (* Take steps until the induction point *)
    iApply (wpsim_yieldR with "[DUTY]").
    { eauto. }
    { iFrame. }
    iIntros "DUTY CRD". iModIntro. rred2r. iApply wpsim_tauR. rred2r.
    iEval (rewrite unfold_iter_eq; rred2r).
    iApply (wpsim_yieldR with "[DUTY]").
    { eauto. }
    { iFrame. }
    iIntros "DUTY CRD2". iModIntro. rred2r.

    (* Induction on until_thread_promise *)
    iInv "INV" as "CI" "CI_CLOSE".
    iEval (unfold client01Inv; simpl; red_tl; simpl; rewrite red_syn_until_tpromise; simpl) in "CI".
    iDestruct "CI" as "[#LOBL UPRM]".
    iPoseProof (until_tpromise_get_tpromise with "UPRM") as "#TPRM".
    iRevert "THDW PC DUTY CI_CLOSE".
    iMod (until_tpromise_ind with "[LOBL UPRM] [-]") as "IND"; cycle 2.
    { iApply "IND". }
    { iSplit; iFrame; auto. }
    iSplit.
    (* Not written *)
    { iModIntro. iIntros "IH". iModIntro. iIntros "PRE THDW PC DUTY CI_CLOSE".
      iEval (simpl; red_tl; simpl) in "PRE". iDestruct "PRE" as "[LIVE PT]".
      iApply (SCMem_load_fun_spec _ _ _ n with "[PT MEM] [-]"). auto.
      { rewrite lookup_insert. pose mask_disjoint_N_Client01_state_tgt. set_solver. }
      { iFrame. auto. }
      iIntros (rv) "[%EQ PTS]"; subst. rred2r. iApply wpsim_tauR. rred2r.
      (* Yield *)
      iMod ("CI_CLOSE" with "[LIVE PTS]") as "_".
      { iEval (unfold client01Inv; simpl; red_tl; simpl; unfold until_thread_promise).
        iSplit; auto.
        iEval (rewrite red_syn_until_tpromise; simpl; unfold until_thread_promise; simpl;
            red_tl; simpl). iSplit; auto. iLeft. iFrame. }
      iApply (wpsim_yieldR with "[DUTY]").
      { eauto. }
      { iFrame. }
      iIntros "DUTY CRD". iModIntro. rred2r.
      (* Compare *)
      iApply (SCMem_compare_fun_spec). auto. set_solver. simpl.
      iApply (tgt_interp_as_equiv with "MEM").
      { iIntros (a). iStartProof. simpl; red_tl; simpl. iSplit.
        { iIntros "MB"; iSplit; iFrame. iPureIntro; auto. }
        { iIntros "[MB _]"; iFrame. } }
      iIntros (rv) "[%EQ1 %EQ2]"; hexploit EQ1; auto; intro; subst.
      rred2r. iApply wpsim_tauR. rred2r. iApply wpsim_tauR.
      iEval (rewrite unfold_iter_eq; rred2r).
      iApply (wpsim_yieldR with "[DUTY]").
      { eauto. }
      { iFrame. }
      iIntros "DUTY CRD2". iModIntro. rred2r.
      
      (* Appeal to the inductive hypothesis *)
      iInv "INV" as "CI" "CI_CLOSE".
      iEval (unfold client01Inv; simpl; red_tl; rewrite red_syn_until_tpromise; simpl) in "CI".
      iDestruct "CI" as "[_ UPRM]".
      iMod ("IH" with "[CRD UPRM] ") as "IH". iFrame.
      iApply ("IH" with "THDW PC DUTY CI_CLOSE"); iFrame.
    }

    (* Written *)
    iModIntro. iIntros "#DEAD THDW PC DUTY CI_CLOSE".
    iEval (red_tl; unfold t1_write; simpl; red_tl; simpl; rewrite red_syn_inv) in "DEAD".
    iDestruct "DEAD" as "[DEAD WRITE]".
    iInv "WRITE" as "WI" "WI_CLOSE".
    { rewrite lookup_insert. pose mask_disjoint_client01. set_solver. }
    iEval (simpl; red_tl; simpl) in "WI".
    (* Load *)
    iApply (SCMem_load_fun_spec _ _ _ n with "[WI MEM] [-]"). auto.
    { rewrite lookup_insert. pose mask_disjoint_N_Client01_state_tgt.
      pose mask_disjoint_t1_write_state_tgt.
      pose mask_disjoint_client01. unfold IndexedInvariants.lookup_def, default. set_unfold.
      intros. split.
      { rewrite lookup_insert. set_solver. }
      { set_solver. } }
    { iFrame; auto. }
    iIntros (rv) "[%EQ PTS]"; subst. rred2r. iApply wpsim_tauR. rred2r.
    iMod ("WI_CLOSE" with "[PTS]") as "_".
    { simpl; iEval (red_tl; simpl); auto. }
    iMod ("CI_CLOSE" with "[]") as "_".
    { iEval (unfold client01Inv; simpl; red_tl; simpl; rewrite red_syn_until_tpromise;
        unfold until_thread_promise; simpl; red_tl; simpl).
      iSplit; iFrame; auto. }

    iApply (wpsim_yieldR with "[DUTY]").
    { eauto. }
    { iFrame. }
    iIntros "DUTY CRD". iModIntro. rred2r.
    (* Compare *)
    iApply (SCMem_compare_fun_spec). auto. set_solver.
    iApply (tgt_interp_as_equiv with "MEM").
    { iIntros (a). simpl. iSplit; iIntros "H"; unfold t1_write; simpl; red_tl; simpl; iFrame.
      { iPureIntro. auto. } { iDestruct "H" as "[MB _]"; iFrame. } }
    iIntros (rv) "[_ %EQ2]"; hexploit EQ2; auto; intro; subst. rred2r.
    iApply wpsim_tauR. rred2r.

    iApply (wpsim_sync with "[DUTY]").
    { eauto. }
    { iFrame. }
    iIntros "DUTY CRD2". iModIntro. rred2r.
    iApply wpsim_tauR. rred2r. lred2r.

    (* Return *)
    iApply wpsim_ret. auto. iModIntro. iFrame. iPureIntro; auto.
  Qed.

End SPEC.
