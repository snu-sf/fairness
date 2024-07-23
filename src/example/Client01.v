From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Import pind Axioms ITreeLib Red TRed IRed2 WFLibLarge.
From Fairness Require Import FairBeh Mod Concurrency Linking.
From Fairness Require Import PCM IProp IPM IPropAux.
From Fairness Require Import IndexedInvariants OpticsInterp SimWeakest SimWeakestAdequacy.
From Fairness Require Import TemporalLogic SCMemSpec LifetimeRA.

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
  Context `{sub : @SRA.subG Γ Σ}.
  Context {TLRASs : TLRAs_small STT Γ}.
  Context {TLRAS : TLRAs STT Γ Σ}.

  Context {HasMEMRA: @GRA.inG memRA Γ}.
  Context {HasLifetime : @GRA.inG Lifetime.t Γ}.

  Ltac red_tl_all := red_tl; red_tl_memra; red_tl_lifetime.

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

  Definition t1_write n : sProp n :=
    syn_inv n N_t1_write (X ↦ 1)%S.

  Global Instance t1_write_persistent n : Persistent (⟦t1_write n, n⟧).
  Proof.
    unfold Persistent. iIntros "H". unfold t1_write. rewrite red_syn_inv.
    iDestruct "H" as "#H". auto.
  Qed.

  Definition client01Inv γk k n : sProp n :=
    (◆[k, 2] ∗ (((live γk k (1/2)) ∗ (X ↦ 0)) -U-[k](0)-◇ ((dead γk k) ∗ t1_write n)))%S.

  (** Simulation proof. *)

  Lemma Client01_thread1_spec
        tid n
    :
    ⊢ ⟦(∀ (γk k : τ{nat, 1+n}),
           ((⤉ syn_inv n N_Client01 (client01Inv γk k n))
              ∗ (syn_tgt_interp_as n sndl (fun m => (s_memory_black m)))
              ∗ TID(tid)
              ∗ (⤉ Duty(tid) [(k, 0, (dead γk (k : nat)) ∗ t1_write n)])
              ∗ ◇[k](2, 1) ∗ ⤉(live γk (k : nat) (1/2)) ∗ ⋈[k])
             -∗
             syn_wpsim (S n) tid ⊤
             (fun rs rt => (⤉(syn_term_cond n tid _ rs rt))%S)
             false false
             (fn2th Client01Spec.module "thread1" (tt ↑))
             (fn2th Client01.module "thread1" (tt ↑)))%S, 1+n⟧.
  Proof.
    iIntros. red_tl_all. iIntros (γk). red_tl_all. iIntros (k). red_tl_all. simpl.
    iEval (rewrite red_syn_inv; rewrite red_syn_wpsim; rewrite red_syn_tgt_interp_as).

    iIntros "(#INV & #MEM & THDW & DUTY & PCk & LIVE & #ACTk)".

    unfold fn2th. simpl. unfold thread1, Client01Spec.thread1.
    rred2r. lred2r.

    (* Yield *)
    iPoseProof (pc_drop _ 1 _ _ 3 with "PCk") as "DROP". eauto. iMod "DROP".
    iPoseProof (pc_split _ _ 1 2 with "DROP") as "[PC1 PC2]".
    iApply (wpsim_yieldR with "[DUTY PC1]").
    { eauto. }
    { iFrame. simpl. iPoseProof (pcs_cons_fold with "[PC1]") as "FOLD". 2: iFrame. simpl. iFrame. }
    Unshelve. 2: auto.
    iIntros "DUTY CRD". rred2r. iApply wpsim_tauR. rred2r.

    iPoseProof (pc_split _ _ 1 1 with "PC2") as "[PC1 PC2]".
    iApply (wpsim_yieldR with "[DUTY PC1]").
    { eauto. }
    { iFrame. simpl. iPoseProof (pcs_cons_fold with "[PC1]") as "FOLD". 2: iFrame. simpl. iFrame. }
    iIntros "DUTY CRD2". rred2r.

    (* Opening invariant *)
    iInv "INV" as "CI" "CI_CLOSE".
    iEval (unfold client01Inv; simpl; red_tl_all; simpl; rewrite red_syn_until_tpromise) in "CI".
    iDestruct "CI" as "[#OBL UPROMISE]".

    iEval (unfold until_thread_promise; red_tl_all; simpl) in "UPROMISE".
    iDestruct "UPROMISE" as "[#PRM [BF | #AF]]"; simpl.
    { (* Live *)
      iEval (red_tl_all; simpl) in "BF". iDestruct "BF" as "[LIVE2 PT]".
      (* Store *)
      iApply (SCMem_store_fun_spec _ _ _ n with "[PT MEM] [ - ]"). auto.
      { pose mask_disjoint_N_Client01_state_tgt. set_solver. }
      { iFrame. auto. }
      iIntros (?) "PTS". rred2r. iApply wpsim_tauR. rred2r.

      iMod ((FUpd_alloc _ _ _ n (N_t1_write) ((X ↦ 1) : sProp n)%S) with "[PTS]") as "#TI". auto.
      { iEval (simpl; red_tl_all; simpl). auto. }
      iPoseProof (Lifetime.pending_merge with "LIVE LIVE2") as "LIVE".
      iEval (rewrite Qp.half_half) in "LIVE". iMod (Lifetime.pending_shot with "LIVE") as "#DEAD".
      iMod (duty_fulfill with "[DEAD DUTY]") as "DUTY".
      { iSplitL. iFrame. simpl. red_tl_all. auto. }

      (* Closing the invariant *)
      iMod ("CI_CLOSE" with "[]") as "_".
      { iEval (unfold client01Inv; simpl; red_tl_all; simpl).
        iSplit; [iApply "OBL" | iEval (rewrite red_syn_until_tpromise)].
        iApply (until_tpromise_make2 with "[]"). simpl. iSplit; auto.
        iEval (red_tl_all; simpl). iModIntro; iSplit; auto. }

      iApply (wpsim_sync with "[DUTY PC2]").
      { eauto. }
      { iFrame. }
      iIntros "DUTY CRD3". lred2r. rred2r. iApply wpsim_tauR. rred2r.
      iApply wpsim_ret. eauto. iModIntro.
      iEval (unfold term_cond). iSplitL; iFrame. iPureIntro; auto. }
    (* After store *)
    { iEval (unfold t1_write; simpl; red_tl_all; simpl; rewrite red_syn_inv; simpl) in "AF".
      iDestruct "AF" as "[DEAD _]".
      iExFalso. iPoseProof (Lifetime.pending_not_shot with "LIVE DEAD") as "%S". auto.
    }
  Qed.

  Lemma Client01_thread2_spec
        tid n
    :
    ⊢ ⟦(∀ (γk k : τ{nat, 1+n}),
           ((⤉ syn_inv n N_Client01 (client01Inv γk k n))
              ∗ (syn_tgt_interp_as n sndl (fun m => (s_memory_black m)))
              ∗ TID(tid) ∗ (⤉ Duty(tid) []))
             -∗
             syn_wpsim (S n) tid ⊤
             (fun rs rt => (⤉(syn_term_cond n tid _ rs rt))%S)
             false false
             (fn2th Client01Spec.module "thread2" (tt ↑))
             (fn2th Client01.module "thread2" (tt ↑)))%S, 1+n⟧.
  Proof.
    iIntros. red_tl_all. iIntros (γk). red_tl_all. iIntros (k). red_tl_all. simpl.
    iEval (rewrite red_syn_inv; rewrite red_syn_wpsim; rewrite red_syn_tgt_interp_as).

    iIntros "(#INV & #MEM & THDW & DUTY)".

    unfold fn2th. simpl. unfold thread2, Client01Spec.thread2.
    rred2r. lred2r.

    (* Take steps until the induction point *)
    iApply (wpsim_yieldR with "[DUTY]").
    { eauto. }
    { iFrame. }
    iIntros "DUTY CRD". rred2r. iApply wpsim_tauR. rred2r.
    iEval (rewrite unfold_iter_eq; rred2r).
    iApply (wpsim_yieldR with "[DUTY]").
    { eauto. }
    { iFrame. }
    iIntros "DUTY CRD2". rred2r.

    (* Induction on until_thread_promise *)
    iInv "INV" as "CI" "CI_CLOSE".
    iEval (unfold client01Inv; simpl; red_tl_all; simpl; rewrite red_syn_until_tpromise; simpl) in "CI".
    iDestruct "CI" as "[#LOBL UPRM]".
    iPoseProof (until_tpromise_get_tpromise with "UPRM") as "#TPRM".
    iRevert "THDW DUTY CI_CLOSE".
    iMod (until_tpromise_ind with "[LOBL UPRM] [-]") as "IND"; cycle 2.
    { iApply "IND". }
    { iSplit; iFrame; auto. }
    iSplit.
    (* Not written *)
    { iModIntro. iIntros "IH". iModIntro. iIntros "PRE THDW DUTY CI_CLOSE".
      iEval (simpl; red_tl_all; simpl) in "PRE". iDestruct "PRE" as "[LIVE PT]".
      iApply (SCMem_load_fun_spec _ _ _ n with "[PT MEM] [-]"). auto.
      { pose mask_disjoint_N_Client01_state_tgt. set_solver. }
      { iFrame. auto. }
      iIntros (rv) "[%EQ PTS]"; subst. rred2r. iApply wpsim_tauR. rred2r.
      (* Yield *)
      iMod ("CI_CLOSE" with "[LIVE PTS]") as "_".
      { iEval (unfold client01Inv; simpl; red_tl_all; simpl; unfold until_thread_promise).
        iSplit; auto.
        iEval (rewrite red_syn_until_tpromise; simpl; unfold until_thread_promise; simpl;
            red_tl_all; simpl). iFrame "TPRM". iLeft. iFrame. }
      iApply (wpsim_yieldR with "[DUTY]").
      { eauto. }
      { iFrame. }
      iIntros "DUTY CRD". rred2r.
      (* Compare *)
      iApply (SCMem_compare_fun_spec). auto. set_solver. simpl.
      iApply (tgt_interp_as_equiv with "MEM").
      { iIntros (a). iStartProof. simpl; red_tl_all; simpl. iSplit.
        { iIntros "MB"; iSplit; iFrame. iPureIntro; auto. }
        { iIntros "[MB _]"; iFrame. } }
      iIntros (rv) "[%EQ1 %EQ2]"; hexploit EQ1; auto; intro; subst.
      rred2r. iApply wpsim_tauR. rred2r. iApply wpsim_tauR.
      iEval (rewrite unfold_iter_eq; rred2r).
      iApply (wpsim_yieldR with "[DUTY]").
      { eauto. }
      { iFrame. }
      iIntros "DUTY CRD2". rred2r.

      (* Appeal to the inductive hypothesis *)
      iInv "INV" as "CI" "CI_CLOSE".
      iEval (unfold client01Inv; simpl; red_tl_all; rewrite red_syn_until_tpromise; simpl) in "CI".
      iDestruct "CI" as "[_ UPRM]".
      iMod ("IH" with "[CRD UPRM] ") as "IH". iFrame.
      iApply ("IH" with "THDW DUTY CI_CLOSE"); iFrame.
    }

    (* Written *)
    iModIntro. iIntros "#DEAD THDW DUTY CI_CLOSE".
    iEval (red_tl_all; unfold t1_write; simpl; red_tl_all; simpl; rewrite red_syn_inv) in "DEAD".
    iDestruct "DEAD" as "[DEAD WRITE]".
    iInv "WRITE" as "WI" "WI_CLOSE".
    iEval (simpl; red_tl_all; simpl) in "WI".
    (* Load *)
    iApply (SCMem_load_fun_spec _ _ _ n with "[WI MEM] [-]"). auto.
    { pose mask_disjoint_N_Client01_state_tgt.
      pose mask_disjoint_t1_write_state_tgt.
      pose mask_disjoint_client01. set_solver.
    }
    { iFrame; auto. }
    iIntros (rv) "[%EQ PTS]"; subst. rred2r. iApply wpsim_tauR. rred2r.
    iMod ("WI_CLOSE" with "[PTS]") as "_".
    { simpl; iEval (red_tl_all; simpl); auto. }
    iMod ("CI_CLOSE" with "[]") as "_".
    { iEval (unfold client01Inv; simpl; red_tl_all; simpl; rewrite red_syn_until_tpromise;
        unfold until_thread_promise; simpl; red_tl_all; simpl).
      iSplit; iFrame; auto. }

    iApply (wpsim_yieldR with "[DUTY]").
    { eauto. }
    { iFrame. }
    iIntros "DUTY CRD". rred2r.
    (* Compare *)
    iApply (SCMem_compare_fun_spec). auto. set_solver.
    iApply (tgt_interp_as_equiv with "MEM").
    { iIntros (a). simpl. iSplit; iIntros "H"; unfold t1_write; simpl; red_tl_all; simpl; iFrame.
      { iPureIntro. auto. } { iDestruct "H" as "[MB _]"; iFrame. } }
    iIntros (rv) "[_ %EQ2]"; hexploit EQ2; auto; intro; subst. rred2r.
    iApply wpsim_tauR. rred2r.

    iApply (wpsim_sync with "[DUTY]").
    { eauto. }
    { iFrame. }
    iIntros "DUTY CRD2". rred2r.
    iApply wpsim_tauR. rred2r. lred2r.

    (* Return *)
    iApply wpsim_ret. auto. iModIntro. iFrame. iPureIntro; auto.
  Qed.


  Section INITIAL.

    Variable tid1 tid2 : thread_id.
    Let init_ord := Ord.O.
    (* Let init_ord := layer 2 1. *)
    Let init_ths :=
          (NatStructs.NatMap.add
             tid1 tt
             (NatStructs.NatMap.add
                tid2 tt
                (NatStructs.NatMap.empty unit))).

    Let idx := 1.

    (* Lemma init_sat E (H_TID : tid1 <> tid2) : *)
    (*   (OwnM (memory_init_resource Client01.gvs)) *)
    (*     ∗ *)
    (*     (WSim.initial_prop *)
    (*        Client01Spec.module Client01.module *)
    (*        (Vars:=@sProp STT Γ) (Σ:=Σ) *)
    (*        (STATESRC:=@SRA.in_subG Γ Σ sub _ _STATESRC) *)
    (*        (STATETGT:=@SRA.in_subG Γ Σ sub _ _STATETGT) *)
    (*        (IDENTSRC:=@SRA.in_subG Γ Σ sub _ _IDENTSRC) *)
    (*        (IDENTTGT:=@SRA.in_subG Γ Σ sub _ _IDENTTGT) *)
    (*        (ARROWRA:=@_ARROWRA STT Γ Σ TLRAS) *)
    (*        idx init_ths init_ord) *)
    (*     ⊢ *)
    (*     =| 1+idx |=(fairI *)
    (*                   (IDENTTGT:=@SRA.in_subG Γ Σ sub _ _IDENTTGT) *)
    (*                   (ARROWRA:=@_ARROWRA STT Γ Σ TLRAS) *)
    (*                   (1+idx) (ident_tgt:=tgt_ident))={ E, E }=> *)
    (*         (∃ γk k, *)
    (*             (inv idx N_Client01 (client01Inv γk k idx)) *)
    (*               ∗ (tgt_interp_as *)
    (*                    (STATETGT:=@SRA.in_subG Γ Σ sub _ _STATETGT) *)
    (*                    (n:=idx) sndl (fun m => (s_memory_black m))) *)
    (*               ∗ ((own_thread tid1) *)
    (*                    ∗ (duty *)
    (*                           (IDENTTGT:=@SRA.in_subG Γ Σ sub _ _IDENTTGT) *)
    (*                           (ARROWRA:=@_ARROWRA STT Γ Σ TLRAS) *)
    (*                           (v:=idx) inlp tid1 *)
    (*                           [(k, 0, ((((dead γk (k : nat)) : @sProp STT Γ idx) ∗ t1_write idx))%S)]) *)
    (*                    (* ∗ (Duty(tid1) *) *)
    (*                    (*        (IDENTTGT:=@SRA.in_subG Γ Σ sub _ _IDENTTGT) *) *)
    (*                    (*        (ARROWRA:=@_ARROWRA STT Γ Σ TLRAS) *) *)
    (*                    (*        [(k, 0, ((((dead γk (k : nat)) : @sProp STT Γ idx) ∗ t1_write idx))%S)]) *) *)
    (*                    ∗ ◇[k](2, 1) ∗ (live γk (k : nat) (1/2)) *)
    (*                 ) *)
    (*               ∗ *)
    (*               ((own_thread tid2) ∗ (duty (v:=idx) inlp tid2 [])) *)
    (*         ). *)

    Lemma init_sat E (H_TID : tid1 <> tid2) :
      (OwnM (Σ:=Σ) (memory_init_resource Client01.gvs))
        ∗
        (WSim.initial_prop
           Client01Spec.module Client01.module
           (Vars:=@sProp STT Γ) (Σ:=Σ)
           (STATESRC:=@SRA.in_subG Γ Σ sub _ _STATESRC)
           (STATETGT:=@SRA.in_subG Γ Σ sub _ _STATETGT)
           (IDENTSRC:=@SRA.in_subG Γ Σ sub _ _IDENTSRC)
           (IDENTTGT:=@SRA.in_subG Γ Σ sub _ _IDENTTGT)
           (ARROWRA:=@_ARROWRA STT Γ Σ TLRAS)
           idx init_ths init_ord)
        ⊢
        =| 1+idx |=(⟦syn_fairI (1+idx), 1+idx⟧)={ E, E }=>
            (∃ γk k,
                (inv idx N_Client01 (client01Inv γk k idx))
                  ∗ (⟦syn_tgt_interp_as idx sndl (fun m => (s_memory_black m)), 1+idx⟧)
                  ∗ ((own_thread tid1)
                       ∗ (⟦Duty(tid1) [(k, 0, ((((dead γk (k : nat)) : @sProp STT Γ idx) ∗ t1_write idx))%S)], idx⟧)
                       ∗ ◇[k](2, 1) ∗ (live γk (k : nat) (1/2)) ∗ ⋈[k]
                    )
                  ∗
                  ((own_thread tid2) ∗ (⟦Duty(tid2) [], idx⟧))
            ).
    Proof.
      iIntros "(MEM & INIT)". rewrite red_syn_fairI.
      iPoseProof (memory_init_iprop with "MEM") as "[MEM PTS]".

      iMod (alloc_obligation 2 2) as "(%k & #LO & PC & PENDk)".
      iMod (Lifetime.alloc k) as "[%γk LIVE]".
      iPoseProof (Lifetime.pending_split with "[LIVE]") as "[LIVE1 LIVE2]".
      { iEval (erewrite Qp.div_2). iFrame. }
      (* iEval (unfold gvs, SCMem.init_gvars; ss) in "PTS". *)

      unfold WSim.initial_prop.
      iDestruct "INIT" as "(INIT0 & INIT1 & INIT2 & INIT3 & INIT4 & INIT5)".
      (* make thread_own, duty *)
      assert (NatStructs.NatMap.find tid1 init_ths = Some tt).
      { unfold init_ths. apply NatStructs.nm_find_add_eq. }
      iPoseProof (natmap_prop_remove_find _ _ _ H with "INIT2") as "[DU1 INIT2]".
      iPoseProof (natmap_prop_remove_find _ _ _ H with "INIT3") as "[TH1 INIT3]".
      clear H.
      assert (NatStructs.NatMap.find tid2 (NatStructs.NatMap.remove tid1 init_ths) = Some tt).
      { unfold init_ths.
        rewrite NatStructs.NatMapP.F.remove_neq_o; ss.
        rewrite NatStructs.nm_find_add_neq; ss.
        rewrite NatStructs.nm_find_add_eq. ss.
      }
      iPoseProof (natmap_prop_remove_find _ _ _ H with "INIT2") as "[DU2 INIT2]".
      iPoseProof (natmap_prop_remove_find _ _ _ H with "INIT3") as "[TH2 INIT3]".
      clear H.

      iEval (replace 2 with (1+1) at 2 by lia) in "PC".
      iPoseProof (pc_split with "PC") as "[PC1 PC2]".
      iMod (pc_drop _ 1 _ _ 1 with "PC2") as "PC2". lia.

      iEval (rewrite <- (Qp.div_2 1)) in "PENDk".
      iPoseProof (pending_split with "PENDk") as "[PENDk1 PENDk2]".
      iMod (duty_add (v:=idx) with "[DU1 PC2 PENDk2] []") as "DU1".
      { iSplitL "DU1". instantiate (1:=[]). iApply "DU1". iFrame. }
      { instantiate (1:=((dead γk k : sProp idx) ∗ (t1_write idx))%S). simpl. red_tl_all.
        unfold t1_write. rewrite red_syn_inv. iModIntro. iIntros "[P H]".
        iDestruct "H" as "#H".
        iDestruct "P" as "#P".
        iModIntro. auto.
      }
      iPoseProof (duty_delayed_tpromise with "DU1") as "#DPROM".
      { ss. eauto. }
      iMod (activate_tpromise with "DPROM PENDk1") as "[#PROM1 #SHOTk]".

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

      iMod (FUpd_alloc _ _ _ idx N_Client01 (client01Inv γk k idx) with "[PTS LIVE1]") as "INV1".
      lia.
      { simpl. unfold SCMem.init_gvars, gvs. ss. des_ifs. iDestruct "PTS" as "((PT & _) & _)".
        unfold client01Inv. red_tl_all. rewrite red_syn_until_tpromise.
        iSplitR. eauto. iSplitR. auto. simpl. iLeft. red_tl_all. iFrame.
        ss. clarify.
        (* TODO : make lemmas *)
        Local Transparent SCMem.alloc.
        unfold SCMem.alloc in Heq0. ss. des_ifs.
        Local Opaque SCMem.alloc.
      }

      iModIntro. iExists γk, k. red_tl_all. rewrite red_syn_tgt_interp_as. iFrame. auto.
      Unshelve. lia.
    Qed.

  End INITIAL.

End SPEC.
