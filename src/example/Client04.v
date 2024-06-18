From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Import pind Axioms ITreeLib Red TRed IRed2 WFLibLarge.
From Fairness Require Import FairBeh Mod Concurrency Linking.
From Fairness Require Import PCM IProp IPM IPropAux.
From Fairness Require Import IndexedInvariants OpticsInterp SimWeakest SimWeakestAdequacy.
From Fairness Require Import TemporalLogic SCMemSpec LifetimeRA AuthExclsRA.

Module Client04.

  Definition gvs : list nat := [1].
  Definition X := SCMem.val_ptr (0, 0).

  Section CODE.

    Notation state := unit.
    Notation ident := void.

    Definition load_loop :
      ktree (threadE ident state) SCMem.val SCMem.val
      :=
      fun v =>
        ITree.iter
          (fun (_: unit) =>
             a <- (OMod.call (R:=SCMem.val) "load" X);;
             b <- (OMod.call (R:=bool) "compare" (a, v));;
             if b then Ret (inl tt) else Ret (inr a)) tt.

    Definition thread1 :
      ktree (threadE ident state) unit unit
      :=
      fun _ =>
        ITree.iter (fun (_ : unit) =>
                      _ <- (OMod.call (R:=unit) "store" (X, (SCMem.val_nat 1)));;
                      a <- load_loop (SCMem.val_nat 1);;
                      _ <- (match a with
                            | SCMem.val_nat n => trigger (Observe 0 [n])
                            | _ => UB
                            end);;
                      Ret (inl tt)) tt.

    Definition thread2 :
      ktree (threadE ident state) unit SCMem.val
      :=
      fun _ =>
        ITree.iter (fun (_ : unit) =>
                      _ <- (OMod.call (R:=unit) "store" (X, (SCMem.val_nat 2)));;
                      a <- load_loop (SCMem.val_nat 2);;
                      _ <- (match a with
                            | SCMem.val_nat n => trigger (Observe 0 [n])
                            | _ => UB
                            end);;
                      Ret (inl tt)) tt.

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

End Client04.

Module Client04Spec.

  Section SPEC.

    Notation state := unit.
    Notation ident := void.

    Definition thread1 :
      ktree (threadE ident state) unit unit
      :=
      fun _ => ITree.iter (fun _ => _ <- trigger Yield;; _ <- trigger (Observe 0 [2]);; Ret (inl tt)) tt.

    Definition thread2:
      ktree (threadE void unit) unit SCMem.val
      :=
      fun _ => ITree.iter (fun _ => _ <- trigger Yield;; _ <- trigger (Observe 0 [1]);; Ret (inl tt)) tt.

    Definition module : Mod.t :=
      Mod.mk
        tt
        (Mod.get_funs [("thread1", Mod.wrap_fun thread1);
                       ("thread2", Mod.wrap_fun thread2)])
    .

  End SPEC.

End Client04Spec.

Section SPEC.

  Import Client04.

  Notation src_state := (Mod.state Client04Spec.module).
  Notation src_ident := (Mod.ident Client04Spec.module).
  Notation tgt_state := (Mod.state Client04.module).
  Notation tgt_ident := (Mod.ident Client04.module).

  Local Instance STT : StateTypes := Build_StateTypes src_state tgt_state src_ident tgt_ident.
  Context `{sub : @SRA.subG Γ Σ}.
  Context {TLRASs : TLRAs_small STT Γ}.
  Context {TLRAS : TLRAs STT Γ Σ}.

  Context {HasMEMRA: @GRA.inG memRA Γ}.
  Context {HasLifetime : @GRA.inG Lifetime.t Γ}.
  Context {HasAuthExcls : @GRA.inG (AuthExcls.t (nat * nat * nat)) Γ}.

  Ltac red_tl_all := red_tl; red_tl_memra; red_tl_lifetime; red_tl_authexcls.

  (** Invariants. *)

  (* Namespace for Client01 invariants. *)
  Definition N_Client04 : namespace := (nroot .@ "Client04").

  Lemma mask_disjoint_N_Client04_state_tgt : (↑N_Client04 : coPset) ## (↑N_state_tgt : coPset).
  Proof. apply ndot_ne_disjoint. ss. Qed.

  Definition client04Inv n γi γs1 γs2 γm1 γm2 : sProp (1+n) :=
    (∃ (tid1 tid2 γ1 γ2 k1 k2 : τ{nat, 1+n}),
      (⤉ ● γs1 (tid1, k1, γ1))
      ∗ (⤉ ● γs2 (tid2, k2, γ2))
      ∗ (⤉ ● γm1 (tid1, k2, γ2))
      ∗ (⤉ ● γm2 (tid2, k1, γ1))
      ∗ ((⤉ (X ↦ 0))
          ∗ (⤉ live γi tt 1)
          ∗ (⤉ Duty (tid1) []) ∗ (⤉ Duty (tid2) [])
          ∗ (⤉ ○ γs1 (tid1, k1, γ1)) ∗ (⤉ ○ γs2 (tid2, k2, γ2)))
        ∨
        (⤉ dead γi tt)
          ∗ ((⤉ (X ↦ 1))
              ∗ (⤉ live γ2 tt 1)
              ∗ (⤉ (○ γs1 (tid1, k1, γ1)))
              ∗ (⤉ Duty (tid1) [])
              ∗ ((⤉ Duty (tid2) [(k2, 1, dead γ2 tt)])
                  ∗ (◇[k2](2, 1))
                  ∗ (⤉ (○ γs2 (tid2, k2, γ2))))
                ∨ (⤉ (○ γm2 (tid2, k1, γ1))))
            ∨
            ((⤉ (X ↦ 2))
              ∗ (⤉ live γ1 tt 1)
              ∗ (⤉ ○ γs2 (tid2, k2, γ2))
              ∗ (⤉ Duty (tid2) [])
              ∗ ((⤉ Duty (tid1) [(k1, 1, dead γ1 tt)])
                  ∗ (◇[k1](2, 1))
                  ∗ (⤉ ○ γs1 (tid1, k1, γ1)))
                ∨ (⤉ (○ γm1 (tid1, k2, γ2)))))%S.

  (** Simulation proof. *)
  (* Lemma Client04_load_loop_spec
        tid1 n
    :
    ⊢ ⟦(∀ (γi γs1 γs2 γm1 γm2 k2 γ2 : τ{nat, 2+n}),
           ((⤉ syn_inv (1+n) N_Client04 (client04Inv n γi γs1 γs2 γm1 γm2))
              ∗ (⤉ syn_tgt_interp_as n sndl (fun m => (s_memory_black m)))
              ∗ (⤉⤉ ○ γm1 (tid1, k2, γ2))
              ∗ (⤉⤉ dead γi tt))
             -∗
             syn_wpsim (2+n) tid1 ⊤
             (fun rs rt => (⤉ (syn_term_cond (1+n) tid1 _ rs rt))%S)
             false false
             (trigger Yield;;;
             ` x : () <-
             (` x : () + () <- (trigger (Observe 0 [2]);;; Ret (inl ()));;
              match x with
              | inl l => tau;; ITree.iter (λ _ : (), trigger Yield;;; trigger (Observe 0 [2]);;; Ret (inl ())) l
              | inr r0 => Ret r0
              end);; Ret (Any.upcast x))
            (trigger Yield;;;
             (` rv : Any.t <- map_event (OMod.emb_callee omod (SCMem.mod gvs)) (Mod.wrap_fun SCMem.store_fun (Any.upcast (X, 1)));;
              (tau;; unwrap (Any.downcast rv)));;;
             ` x0 : () + () <-
             OMod.close_itree omod (SCMem.mod gvs)
               (` a : SCMem.val <- load_loop 1;;
                match a with
                | SCMem.val_nat n0 => trigger (Observe 0 [n0])
                | SCMem.val_ptr _ => UB
                end;;; Ret (inl ()));;
             ` x1 : () <-
             OMod.close_itree omod (SCMem.mod gvs)
               match x0 with
               | inl l =>
                   tau;; ITree.iter
                           (λ _ : (),
                              OMod.call "store" (X, 1);;;
                              ` a : SCMem.val <- load_loop 1;;
                              match a with
                              | SCMem.val_nat n0 => trigger (Observe 0 [n0])
                              | SCMem.val_ptr _ => UB
                              end;;; Ret (inl ())) l
               | inr r0 => Ret r0
               end;; OMod.close_itree omod (SCMem.mod gvs) (Ret (Any.upcast x1))))%S, 2+n⟧.
  Admitted. *)

  Lemma Client04_thread1_spec
        tid1 n
    :
    ⊢ ⟦(∀ (γi γs1 γs2 γm1 γm2 k2 γ2 : τ{nat, 2+n}),
           ((⤉ syn_inv (1+n) N_Client04 (client04Inv n γi γs1 γs2 γm1 γm2))
              ∗ (⤉ syn_tgt_interp_as n sndl (fun m => (s_memory_black m)))
              ∗ (⤉⤉ ○ γm1 (tid1, k2, γ2)))
             -∗
             syn_wpsim (2+n) tid1 ⊤
             (fun rs rt => (⤉ (syn_term_cond (1+n) tid1 _ rs rt))%S)
             false false
             (fn2th Client04Spec.module "thread1" (tt ↑))
             (fn2th Client04.module "thread1" (tt ↑)))%S, 2+n⟧.
  Proof.
    iIntros. red_tl_all. iIntros (γi). red_tl_all. iIntros (γs1).
    red_tl_all. iIntros (γs2). red_tl_all. iIntros (γm1).
    red_tl_all. iIntros (γm2). red_tl_all. iIntros (k2).
    red_tl_all. iIntros (γ2). red_tl_all. simpl. red_tl.
    iEval (rewrite red_syn_inv; rewrite red_syn_wpsim; rewrite red_syn_tgt_interp_as).

    iIntros "(#INV & #MEM & MY_W)".

    unfold fn2th. simpl. unfold thread1, Client04Spec.thread1.
    rred2r. lred2r. rewrite ! unfold_iter_eq. rred2r. lred2r.
    
    (* Coinduction *)
    iStopProof. revert k2.
    eapply wpsim_coind. auto.
    ii. iIntros "[#HG1 #CIH] [[#INV #MEM] MY_W]".
    (* Yield *)
    iEval (rewrite ! unfold_iter_eq). rred2r.
    iInv "INV" as "CI" "CI_CLOSE".
    iEval (unfold client04Inv; red_tl_all; simpl; red_tl) in "CI".
    iDestruct "CI" as "[%tid1' CI]". iEval (red_tl) in "CI".
    iDestruct "CI" as "[%tid2 CI]". iEval (red_tl) in "CI".
    iDestruct "CI" as "[%γ1 CI]". iEval (red_tl) in "CI".
    iDestruct "CI" as "[%γ2' CI]". iEval (red_tl) in "CI".
    iDestruct "CI" as "[%k1 CI]". iEval (red_tl) in "CI".
    iDestruct "CI" as "[%k2 CI]". iEval (red_tl_all; simpl) in "CI".
    iDestruct "CI" as "[H0 | [H1 | H2]]"; cycle 1.
    iDestruct "H1" as "(_ & _ & _ & _ & _ & _ & _ &)

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
      iEval (unfold term_cond). iSplit; iFrame. iPureIntro; auto. }
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
           ((⤉ syn_inv n N_Client04 (client01Inv γk k n))
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
            red_tl_all; simpl). iSplit; auto. iLeft. iFrame. }
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
          (NatStructsLarge.NatMap.add
             tid1 tt
             (NatStructsLarge.NatMap.add
                tid2 tt
                (NatStructsLarge.NatMap.empty unit))).

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
    (*             (inv idx N_Client04 (client01Inv γk k idx)) *)
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
      (OwnM (memory_init_resource Client01.gvs))
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
                (inv idx N_Client04 (client01Inv γk k idx))
                  ∗ (⟦syn_tgt_interp_as idx sndl (fun m => (s_memory_black m)), 1+idx⟧)
                  ∗ ((own_thread tid1)
                       ∗ (⟦Duty(tid1) [(k, 0, ((((dead γk (k : nat)) : @sProp STT Γ idx) ∗ t1_write idx))%S)], idx⟧)
                       ∗ ◇[k](2, 1) ∗ (live γk (k : nat) (1/2))
                    )
                  ∗
                  ((own_thread tid2) ∗ (⟦Duty(tid2) [], idx⟧))
            ).
    Proof.
      iIntros "(MEM & INIT)". rewrite red_syn_fairI.
      iPoseProof (memory_init_iprop with "MEM") as "[MEM PTS]".

      iMod (alloc_obligation 2 2) as "(%k & #LO & PC)".
      iMod (Lifetime.alloc k) as "[%γk LIVE]".
      iPoseProof (Lifetime.pending_split with "[LIVE]") as "[LIVE1 LIVE2]".
      { iEval (rewrite Qp.div_2). iFrame. }
      (* iEval (unfold gvs, SCMem.init_gvars; ss) in "PTS". *)

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

      iEval (replace 2 with (1+1) at 2 by lia) in "PC".
      iPoseProof (pc_split with "PC") as "[PC1 PC2]".
      iMod (pc_drop _ 1 _ _ 1 with "PC2") as "PC2". lia.
      iMod (duty_add (v:=idx) with "[DU1 PC2] []") as "DU1".
      { iSplitL "DU1". instantiate (1:=[]). iApply "DU1". iFrame. }
      { instantiate (1:=((dead γk k : sProp idx) ∗ (t1_write idx))%S). simpl. red_tl_all.
        unfold t1_write. rewrite red_syn_inv. iModIntro. iIntros "#P". auto.
      }
      iPoseProof (duty_tpromise with "DU1") as "#PROM1".
      { ss. eauto. }

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

      iMod (FUpd_alloc _ _ _ idx N_Client04 (client01Inv γk k idx) with "[PTS LIVE1]") as "INV1".
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

      iModIntro. iExists γk, k. red_tl_all. rewrite red_syn_tgt_interp_as. iFrame.
      Unshelve. lia.
    Qed.

  End INITIAL.

End SPEC.
