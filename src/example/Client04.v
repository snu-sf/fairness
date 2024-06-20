From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Import pind Axioms ITreeLib Red TRed IRed2 WFLibLarge.
From Fairness Require Import FairBeh Mod Concurrency Linking.
From Fairness Require Import PCM IProp IPM IPropAux.
From Fairness Require Import IndexedInvariants OpticsInterp SimWeakest SimWeakestAdequacy.
From Fairness Require Import TemporalLogic SCMemSpec LifetimeRA AuthExclsRA.
Require Import Setoid.

Module Client04.

  Definition gvs : list nat := [1].
  Definition X := SCMem.val_ptr (0, 0).
  Global Opaque X.

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
                      _ <- trigger Yield;;
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
                      _ <- trigger Yield;;
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

  Definition client04Inv n γi γi1 γi2 γs1 γs2 γm1 γm2 : sProp (1+n) :=
    (∃ (tid1 tid2 γ1 γ2 k1 k2 : τ{nat, 1+n}),
      (⤉ ● γs1 (tid1, k1, γ1))
      ∗ (⤉ ● γs2 (tid2, k2, γ2))
      ∗ (⤉ ● γm1 (tid1, k2, γ2))
      ∗ (⤉ ● γm2 (tid2, k1, γ1))
      ∗ (((⤉ (X ↦ 0))
          ∗ (⤉ live γi tt 1)
          ∗ (Duty (tid1) []) ∗ (Duty (tid2) [])
          ∗ (⤉ ○ γs1 (tid1, k1, γ1)) ∗ (⤉ ○ γs2 (tid2, k2, γ2)))
        ∨
        ((⤉ dead γi tt)
          ∗
          ((⤉ (X ↦ 1))
            ∗ (⤉ dead γi1 tt)
            ∗ (⤉ live γ2 tt 1)
            ∗ (⤉ (○ γs1 (tid1, k1, γ1)))
            ∗ (Duty (tid1) []) 
            ∗ (((Duty (tid2) [(k2, 0, dead γ2 tt : sProp (1+n))])
                ∗ (◇[k2](2, 1))
                ∗ (⤉ (○ γs2 (tid2, k2, γ2))))
              ∨ (⤉ (○ γm2 (tid2, k1, γ1))))
          ∨
          ((⤉ (X ↦ 2))
            ∗ (⤉ dead γi2 tt)
            ∗ (⤉ live γ1 tt 1)
            ∗ (⤉ ○ γs2 (tid2, k2, γ2))
            ∗ (Duty (tid2) [])
            ∗ (((Duty (tid1) [(k1, 0, dead γ1 tt : sProp (1+n))])
                ∗ (◇[k1](2, 1))
                ∗ (⤉ ○ γs1 (tid1, k1, γ1)))
              ∨ (⤉ (○ γm1 (tid1, k2, γ2)))))))))%S.

  (** Simulation proof. *)
  Lemma Client04_load_loop_spec1
        tid n
  :
  ⊢ ∀ (γi γi1 γi2 γs1 γs2 γm1 γm2 k2 γ2 : τ{nat, 2+n}),
    [@ tid, 1+n, ⊤ @]
      ⧼⟦((⤉ syn_inv (1+n) N_Client04 (client04Inv n γi γi1 γi2 γs1 γs2 γm1 γm2))
        ∗ (⤉ syn_tgt_interp_as n sndl (fun m => s_memory_black m))
        ∗ (⤉⤉ ○ γm1 (tid, k2, γ2))
        ∗ (⤉⤉ dead γi ())
        ∗ (⤉⤉ dead γi1 ())
        ∗ (◆[k2, 2])
        ∗ (⤉ -[k2](0)-◇ (dead γ2 () : sProp (1+n))))%S, 2+n⟧⧽
        (OMod.close_itree omod (SCMem.mod gvs) (load_loop 1))
        ⧼rv, ⌜rv = 2⌝
          ∗ ∃ k1 γ1, ⟦((⤉⤉ dead γi2 ())
            ∗ (⤉ Duty (tid) [(k1, 0, dead γ1 tt : sProp (1+n))])
            ∗ (◇[k1](1, 2))
            ∗ (⤉⤉ ○ γs1 (tid, k1, γ1)))%S, 2+n⟧⧽
  .
  Proof.
    iIntros. iStartTriple. simpl. red_tl_all; simpl. rewrite red_syn_inv; rewrite red_syn_tgt_interp_as.
    iIntros "(#INV & #MEM & WM1 & #DEADI & #DEADI1 & #OBL2 & #PRM2)". iIntros "POST".
    (* Induction point *)
    iRevert "WM1 POST".
    iMod (tpromise_ind with "[] [-]") as "IH"; cycle 2. done. iSplit; done. iModIntro. iIntros "IH". iModIntro.
    iIntros "WM1 POST". iEval (unfold load_loop at 1; rewrite -> unfold_iter_eq). rred2r.
    (* clear tid2 γ1 k1. *)
    iInv "INV" as "CI" "CI_CLOSE".
    iEval (unfold client04Inv; red_tl_all; simpl; red_tl) in "CI".
    iDestruct "CI" as "[%tid1' CI]". iEval (red_tl) in "CI".
    iDestruct "CI" as "[%tid2 CI]". iEval (red_tl) in "CI".
    iDestruct "CI" as "[%γ1 CI]". iEval (red_tl) in "CI".
    iDestruct "CI" as "[%γ2' CI]". iEval (red_tl) in "CI".
    iDestruct "CI" as "[%k1 CI]". iEval (red_tl) in "CI".
    iDestruct "CI" as "[%k2' CI]". iEval (red_tl_all; simpl) in "CI".
    iDestruct "CI" as "(BS1 & BS2 & BM1 & BM2 & [H0 | [_ [H1 | H2]]])".
    { iDestruct "H0" as "(_ & LIVE & _)". iExFalso; iApply (Lifetime.pending_not_shot with "LIVE"). done. }
    (* Case 1-1-1 : no one has written when I'm yielding *)
    { iPoseProof (AuthExcls.b_w_eq with "BM1 WM1") as "%EQ". clarify.
      iDestruct "H1" as "(PTX & _ & LIVE2 & WS1 & DUTY1 & REST)".
      (* Yield *)
      iApply (wpsim_yieldR_gen with "[DUTY1]"). instantiate (1:=1+n). auto. iFrame. iIntros "DUTY1 CRED".
      iMod ("IH" with "CRED") as "[IH | #DEAD]"; cycle 1.
      { iExFalso; iApply (Lifetime.pending_not_shot with "LIVE2"). simpl; red_tl_lifetime. done. }
      iMod ("CI_CLOSE" with "[- WM1 IH POST]") as "_".
      { iEval (unfold client04Inv; simpl; red_tl).
        do 6 (iExists _; red_tl); red_tl_all. 
        iSplitL "BS1"; [done|]. iSplitL "BS2"; [done|]. iSplitL "BM1"; [done|]. iSplitL "BM2"; [done|].
        iRight. iSplitR; [done | ]. iLeft. simpl. iFrame. done.
      }
      iModIntro. rred2r.
      clear tid2 γ1 k1.
      iInv "INV" as "CI" "CI_CLOSE".
      iEval (unfold client04Inv; red_tl_all; simpl; red_tl) in "CI".
      iDestruct "CI" as "[%tid1' CI]". iEval (red_tl) in "CI".
      iDestruct "CI" as "[%tid2 CI]". iEval (red_tl) in "CI".
      iDestruct "CI" as "[%γ1 CI]". iEval (red_tl) in "CI".
      iDestruct "CI" as "[%γ2' CI]". iEval (red_tl) in "CI".
      iDestruct "CI" as "[%k1 CI]". iEval (red_tl) in "CI".
      iDestruct "CI" as "[%k2' CI]". iEval (red_tl_all; simpl) in "CI".
      iDestruct "CI" as "(BS1 & BS2 & BM1 & BM2 & [H0 | [_ [H1 | H2]]])".
      { iDestruct "H0" as "(_ & LIVE & _)". iExFalso; iApply (Lifetime.pending_not_shot with "LIVE"). done. }
      { iPoseProof (AuthExcls.b_w_eq with "BM1 WM1") as "%EQ". clarify.
        iDestruct "H1" as "(PTX & _ & LIVE_2 & WS1 & DUTY1 & REST)".
        (* Load 1 - induction by tpromise *)
        iApply (SCMem_load_fun_spec with "[PTX]"). instantiate (1:=n). auto.
        { pose mask_disjoint_N_Client04_state_tgt; set_solver. }
        { iFrame. done. }
        iIntros (rv') "[% PTX]". subst. rred2r. iApply wpsim_tauR. rred2r.
        iApply (wpsim_yieldR_gen with "[DUTY1]"). instantiate (1:=1+n). auto. iFrame. iIntros "DUTY1 CRED".
        iMod ("CI_CLOSE" with "[- WM1 IH POST]") as "_".
        { iEval (unfold client04Inv; simpl; red_tl).
          do 6 (iExists _; red_tl); red_tl_all. 
          iSplitL "BS1"; [done|]. iSplitL "BS2"; [done|]. iSplitL "BM1"; [done|]. iSplitL "BM2"; [done|].
          iRight. iSplitR; [done | ]. iLeft. simpl. iFrame. done.
        }
        iModIntro. rred2r.
        iApply SCMem_compare_fun_spec. instantiate (1:=n). auto. set_solver.
        { simpl. des_ifs. iApply (tgt_interp_as_equiv with "MEM"). iIntros. iSplit.
          { iIntros. simpl. red_tl; simpl. iSplit; [done | iPureIntro; auto]. }
          { simpl. red_tl; simpl. iIntros "[? _]". done. }
        }
        iIntros (rv) "[%EQ _]". exploit EQ. auto. i; subst. rred2r.
        iApply wpsim_tauR. rred2r. iApply wpsim_tauR. fold (load_loop 1).
        iApply wpsim_stutter_mon. instantiate (1:=ps); auto. instantiate (1:=pt); auto.
        iApply ("IH" with "WM1"). done.
      }
      { iPoseProof (AuthExcls.b_w_eq with "BM1 WM1") as "%EQ". clarify.
        iDestruct "H2" as "(PTX & #DEADI2 & LIVE_1 & WS2 & DUTY2 & [(DUTY1 & PC1 & WS1) | MY_W2])"; cycle 1.
        { iExFalso; iApply (AuthExcls.w_w_false with "WM1 MY_W2"). }
        iApply (SCMem_load_fun_spec with "[PTX]"). instantiate (1:=n). auto.
        { pose mask_disjoint_N_Client04_state_tgt; set_solver. }
        { iFrame. done. }
        iIntros (rv') "[% PTX]". subst. rred2r. iApply wpsim_tauR. rred2r.
        iMod (pc_drop _ 1 _ _ 3 with "PC1") as "PC1". auto.
        iPoseProof (pc_split _ _ 1 2 with "PC1") as "[PC11 PC1]".
        iApply (wpsim_yieldR_gen with "[DUTY1 PC11]"). instantiate (1:=1+n). auto. iFrame.
        { iApply pcs_cons_fold. iFrame. } iIntros "DUTY1 CRED".
        iMod ("CI_CLOSE" with "[- DUTY1 PC1 WS1 POST CRED]") as "_".
        { iEval (unfold client04Inv; simpl; red_tl).
          do 6 (iExists _; red_tl); red_tl_all. 
          iSplitL "BS1"; [done|]. iSplitL "BS2"; [done|]. iSplitL "BM1"; [done|]. iSplitL "BM2"; [done|].
          iRight. iSplitR; [done | ]. iRight. simpl. iFrame. done.
        }
        iModIntro. rred2r.
        iApply SCMem_compare_fun_spec. instantiate (1:=n). auto. set_solver.
        { simpl. des_ifs. iApply (tgt_interp_as_equiv with "MEM"). iIntros. iSplit.
          { iIntros. simpl. red_tl; simpl. iSplit; [done | iPureIntro; auto]. }
          { simpl. red_tl; simpl. iIntros "[? _]". done. }
        }
        iIntros (rv) "[_ %NEQ]". exploit NEQ. auto. i; subst. rred2r.
        iApply wpsim_tauR. rred2r.
        iApply ("POST" with "[-]").
        { iSplit; auto. iExists k1, γ1. red_tl_all; simpl. iFrame. done. }
      }
    }
    (* Case 1-1-2 : thread 2 has written when I'm yielding *)
    iPoseProof (AuthExcls.b_w_eq with "BM1 WM1") as "%EQ". clarify.
    iDestruct "H2" as "(PTX & #DEADI2 & LIVE_1 & WS2 & DUTY2 & [(DUTY1 & PC1 & WS1) | MY_W2])"; cycle 1.
    { iExFalso; iApply (AuthExcls.w_w_false with "WM1 MY_W2"). }
    (* Load 2 *)
    iMod (pc_drop _ 1 _ _ 4 with "PC1") as "PC1". auto.
    iPoseProof (pc_split _ _ 1 3 with "PC1") as "[PC11 PC1]".
    iApply (wpsim_yieldR_gen with "[DUTY1 PC11]"). instantiate (1:=1+n). auto. iFrame.
    { iApply pcs_cons_fold. iFrame. } iIntros "DUTY1 CRED".
    iMod ("CI_CLOSE" with "[- DUTY1 PC1 WS1 POST]") as "_".
    { iEval (unfold client04Inv; simpl; red_tl).
      do 6 (iExists _; red_tl); red_tl_all. 
      iSplitL "BS1"; [done|]. iSplitL "BS2"; [done|]. iSplitL "BM1"; [done|]. iSplitL "BM2"; [done|].
      iRight. iSplitR; [done | ]. iRight. simpl. iFrame. done.
    }
    iModIntro. rred2r.
    iClear "OBL2 PRM2". clear tid2 γ2 k2.
    iInv "INV" as "CI" "CI_CLOSE".
    iEval (unfold client04Inv; red_tl_all; simpl; red_tl) in "CI".
    iDestruct "CI" as "[%tid1' CI]". iEval (red_tl) in "CI".
    iDestruct "CI" as "[%tid2 CI]". iEval (red_tl) in "CI".
    iDestruct "CI" as "[%γ1' CI]". iEval (red_tl) in "CI".
    iDestruct "CI" as "[%γ2 CI]". iEval (red_tl) in "CI".
    iDestruct "CI" as "[%k1' CI]". iEval (red_tl) in "CI".
    iDestruct "CI" as "[%k2 CI]". iEval (red_tl_all; simpl) in "CI".
    iDestruct "CI" as "(BS1 & BS2 & BM1 & BM2 & [H0 | [_ [H1 | H2]]])".
    { iDestruct "H0" as "(_ & LIVE & _)". iExFalso; iApply (Lifetime.pending_not_shot with "LIVE"). done. }
    { iDestruct "H1" as "(PTX & _ & LIVE_2 & WS1_2 & DUTY1_2 & _)".
      iExFalso; iApply (AuthExcls.w_w_false with "WS1 WS1_2").
    }
    iDestruct "H2" as "(PTX & _ & LIVE1 & WS2 & DUTY2 & [(_ & _ & WS1_2) | MY_W2])".
    { iExFalso; iApply (AuthExcls.w_w_false with "WS1 WS1_2"). }
    iApply (SCMem_load_fun_spec with "[PTX]"). instantiate (1:=n). auto.
    { pose mask_disjoint_N_Client04_state_tgt; set_solver. }
    { iFrame. done. }
    iIntros (rv') "[% PTX]". subst. rred2r. iApply wpsim_tauR. rred2r.
    iPoseProof (pc_split _ _ 1 2 with "PC1") as "[PC11 PC1]".
    iApply (wpsim_yieldR_gen with "[DUTY1 PC11]"). instantiate (1:=1+n). auto. iFrame.
    { iApply pcs_cons_fold. iFrame. } iIntros "DUTY1 _".
    iMod ("CI_CLOSE" with "[- DUTY1 PC1 WS1 POST]") as "_".
    { iEval (unfold client04Inv; simpl; red_tl).
      do 6 (iExists _; red_tl); red_tl_all. 
      iSplitL "BS1"; [done|]. iSplitL "BS2"; [done|]. iSplitL "BM1"; [done|]. iSplitL "BM2"; [done|].
      iRight. iSplitR; [done | ]. iRight. simpl. iFrame. done.
    }
    iModIntro. rred2r. lred2r.
    iApply SCMem_compare_fun_spec. instantiate (1:=n). auto. set_solver.
    { simpl. des_ifs. iApply (tgt_interp_as_equiv with "MEM"). iIntros. iSplit.
      { iIntros. simpl. red_tl; simpl. iSplit; [done | iPureIntro; auto]. }
      { simpl. red_tl; simpl. iIntros "[? _]". done. }
    }
    iIntros (rv) "[_ %NEQ]". exploit NEQ. auto. i; subst. rred2r.
    iApply wpsim_tauR. rred2r.
    iApply ("POST" with "[-]").
    { iSplit; auto. iExists k1, γ1. red_tl_all; simpl. iFrame. done. }
  Unshelve. all: auto.
  Qed.

  Lemma Client04_thread1_spec
        tid1 n
    :
    ⊢ ⟦(∀ (γi γi1 γi2 γs1 γs2 γm1 γm2 k2 γ2 : τ{nat, 2+n}),
           ((⤉ syn_inv (1+n) N_Client04 (client04Inv n γi γi1 γi2 γs1 γs2 γm1 γm2))
              ∗ (⤉ syn_tgt_interp_as n sndl (fun m => (s_memory_black m)))
              ∗ (⤉⤉ ○ γm1 (tid1, k2, γ2))
              ∗ (⤉⤉ live γi1 tt 1))
             -∗
             syn_wpsim (2+n) tid1 ⊤
             (fun rs rt => (⤉ (syn_term_cond (1+n) tid1 _ rs rt))%S)
             false false
             (fn2th Client04Spec.module "thread1" (tt ↑))
             (fn2th Client04.module "thread1" (tt ↑)))%S, 2+n⟧.
  Proof.
    iIntros. red_tl_all. iIntros (γi). red_tl_all. iIntros (γi1).
    red_tl_all. iIntros (γi2). red_tl_all. iIntros (γs1).
    red_tl_all. iIntros (γs2). red_tl_all. iIntros (γm1).
    red_tl_all. iIntros (γm2). red_tl_all. iIntros (k2).
    red_tl_all. iIntros (γ2). red_tl_all. simpl. red_tl_all.
    iEval (rewrite red_syn_inv; rewrite red_syn_wpsim; rewrite red_syn_tgt_interp_as).

    iIntros "(#INV & #MEM & MY_W & LIVEI1)".

    unfold fn2th. simpl. unfold thread1, Client04Spec.thread1.
    rred2r. lred2r.
    
    (* Yield *)
    iEval (do 2 rewrite unfold_iter_eq). rred2r. lred2r.
    iInv "INV" as "CI" "CI_CLOSE".
    iEval (unfold client04Inv; red_tl_all; simpl; red_tl) in "CI".
    iDestruct "CI" as "[%tid1' CI]". iEval (red_tl) in "CI".
    iDestruct "CI" as "[%tid2 CI]". iEval (red_tl) in "CI".
    iDestruct "CI" as "[%γ1 CI]". iEval (red_tl) in "CI".
    iDestruct "CI" as "[%γ2' CI]". iEval (red_tl) in "CI".
    iDestruct "CI" as "[%k1 CI]". iEval (red_tl) in "CI".
    iDestruct "CI" as "[%k2' CI]". iEval (red_tl_all; simpl) in "CI".
    iDestruct "CI" as "(BS1 & BS2 & BM1 & BM2 & [H0 | [#DEADI [H1 | H2]]])".
    2:{ iDestruct "H1" as "(_ & #DEAD & _)". iExFalso; iApply (Lifetime.pending_not_shot with "LIVEI1 DEAD "). }
    (* Case 1 : initialization *)
    { iDestruct "H0" as "(PTX & LIVEI & DUTY1 & DUTY2 & WS1 & WS2)".
      iPoseProof (AuthExcls.b_w_eq with "BM1 MY_W") as "%EQ". clarify.
      iApply (wpsim_yieldR_gen with "[DUTY1]"). instantiate (1:=1+n). auto. iFrame.
      iIntros "DUTY1 CRED".
      iMod ("CI_CLOSE" with "[- MY_W CRED LIVEI1]") as "_".
      { iEval (unfold client04Inv; simpl; red_tl).
        do 6 (iExists _; red_tl); red_tl_all.
        iSplitL "BS1"; [done|]. iSplitL "BS2"; [done|]. iSplitL "BM1"; [done|]. iSplitL "BM2"; [done|].
        iLeft. iFrame.
      }
      iModIntro. rred2r. clear tid2 γ1 k1.
      iInv "INV" as "CI" "CI_CLOSE".
      iEval (unfold client04Inv; red_tl_all; simpl; red_tl) in "CI".
      iDestruct "CI" as "[%tid1' CI]". iEval (red_tl) in "CI".
      iDestruct "CI" as "[%tid2 CI]". iEval (red_tl) in "CI".
      iDestruct "CI" as "[%γ1 CI]". iEval (red_tl) in "CI".
      iDestruct "CI" as "[%γ2' CI]". iEval (red_tl) in "CI".
      iDestruct "CI" as "[%k1 CI]". iEval (red_tl) in "CI".
      iDestruct "CI" as "[%k2' CI]". iEval (red_tl_all; simpl) in "CI".
      iDestruct "CI" as "(BS1 & BS2 & BM1 & BM2 & [H0 | [#DEADI [H1 | H2]]])".
      2:{ iDestruct "H1" as "(_ & #DEAD & _)".
          iExFalso; iApply (Lifetime.pending_not_shot with "LIVEI1 DEAD ").
      }
      (* Case 1-1 : no one has written when I'm storing *)
      { iDestruct "H0" as "(PTX & LIVEI & DUTY1 & DUTY2 & WS1 & WS2)".
        iPoseProof (AuthExcls.b_w_eq with "BM1 MY_W") as "%EQ". clarify.
        iApply (SCMem_store_fun_spec with "[PTX] [-]"). instantiate (1:=n). auto.
        { pose proof mask_disjoint_N_Client04_state_tgt; set_solver. }
        { iFrame. done. }
        iIntros (rv) "PTX". rred2r. iApply wpsim_tauR. rred2r.
        iMod (Lifetime.pending_shot with "LIVEI") as "#DEADI".
        iMod (Lifetime.pending_shot with "LIVEI1") as "#DEADI1".
        iMod (Lifetime.alloc tt) as "[%γ2' LIVE2]".
        iMod (alloc_obligation 2 2) as "[%obl_2 [#OBL_2 PC_2]]".
        iPoseProof (pc_split _ _ 1 1 with "[PC_2]") as "[PC_21 PC_22]". done.
        iMod (pc_drop _ 1 _ _ 1 with "PC_22") as "PC_22"; auto.
        iMod (duty_add (v:=1+n) with "[DUTY2 PC_22] []") as "DUTY2". iFrame.
        { instantiate (1 := (dead γ2' tt)%S). iEval (simpl; red_tl_all). iModIntro. iIntros "#D". iModIntro. done. }
        iPoseProof (duty_tpromise with "[DUTY2]") as "#PRM2". 2: done. simpl; left; auto.
        iMod (AuthExcls.b_w_update _ _ _ (tid2, obl_2, γ2') with "BS2 WS2") as "[BS2 WS2]".
        iMod (AuthExcls.b_w_update _ _ _ (tid1, obl_2, γ2') with "BM1 MY_W") as "[BM1 MY_W]".
        clear γ2 k2. rename γ2' into γ2. rename obl_2 into k2.
        iMod ("CI_CLOSE" with "[- MY_W]") as "_".
        { iEval (unfold client04Inv; simpl; red_tl).
          do 6 (iExists _; red_tl); red_tl_all.
          iSplitL "BS1"; [done|]. iSplitL "BS2"; [done|]. iSplitL "BM1"; [done|]. iSplitL "BM2"; [done|].
          iRight. iSplitR; [done | ]. iLeft. simpl. iFrame. iSplitR; [done|]. iLeft. iFrame.
        }
        (* Coinduction point *)
        iApply wpsim_reset. iStopProof.
        pose (k2, γ2) as p. replace k2 with (p.1) by ss. replace γ2 with (p.2) by ss. generalize p. clear p.
        eapply wpsim_coind. auto. clear k2 γ2.
        ii. destruct a as [k2 γ2].
        iIntros "[#HG1 #CIH] [(#INV & #MEM & #DEADI & #DEADI1 & #OBL_2 & #PRM_2) MY_W]". simpl.
        iApply (Client04_load_loop_spec1 with "[MY_W] [-]").
        { simpl. red_tl_all; simpl. rewrite red_syn_inv; rewrite red_syn_tgt_interp_as; red_tl_all.
          iFrame. do 5 (iSplit; [done | ]). done. }
        iIntros (rv') "(%EQ & %k0 & %γ0 & POST)"; subst. iEval (simpl; red_tl_all; simpl) in "POST".
        iDestruct "POST" as "(#DEADI2 & DUTY1 & PC1 & WS1)". rred2r.
        iPoseProof (pc_split _ _ 1 1 with "PC1") as "[PC11 PC1]".
        iApply (wpsim_sync_gen with "[DUTY1 PC11]"). instantiate (1:=1+n). auto.
        { iFrame. iApply pcs_cons_fold; iFrame. }
        iIntros "DUTY1 _". iModIntro. lred2r. rred2r. iApply wpsim_tauR. rred2r.
        iApply wpsim_observe. iIntros. rred2r. lred2r.
        iApply wpsim_tauR. iApply wpsim_tauL. rred2r. lred2r. iApply wpsim_tauR.
        do 2 rewrite unfold_iter_eq. lred2r. rred2r.
        iApply (wpsim_yieldR_gen with "[DUTY1 PC1]"). instantiate (1:=1+n). auto. iFrame.
        { iApply pcs_cons_fold; iFrame. }
        iIntros "DUTY1 _". iModIntro. rred2r.
        (* Write 1 *)
        iClear "OBL_2 PRM_2". clear tid2 γ2 k2.
        iInv "INV" as "CI" "CI_CLOSE".
        iEval (unfold client04Inv; red_tl_all; simpl; red_tl) in "CI".
        iDestruct "CI" as "[%tid1' CI]". iEval (red_tl) in "CI".
        iDestruct "CI" as "[%tid2 CI]". iEval (red_tl) in "CI".
        iDestruct "CI" as "[%γ1' CI]". iEval (red_tl) in "CI".
        iDestruct "CI" as "[%γ2 CI]". iEval (red_tl) in "CI".
        iDestruct "CI" as "[%k1' CI]". iEval (red_tl) in "CI".
        iDestruct "CI" as "[%k2 CI]". iEval (red_tl_all; simpl) in "CI".
        iDestruct "CI" as "(BS1 & BS2 & BM1 & BM2 & [H0 | [_ [H1 | H2]]])".
        { iDestruct "H0" as "(_ & LIVE & _)". iExFalso; iApply (Lifetime.pending_not_shot with "LIVE"). done. }
        { iDestruct "H1" as "(PTX & _ & LIVE_2 & WS1_2 & DUTY1_2 & _)".
          iExFalso; iApply (AuthExcls.w_w_false with "WS1 WS1_2").
        }
        iDestruct "H2" as "(PTX & _ & LIVE_1 & WS2 & DUTY2 & [(_ & _ & WS1_2) | MY_W2])".
        { iExFalso; iApply (AuthExcls.w_w_false with "WS1 WS1_2"). }
        iPoseProof (AuthExcls.b_w_eq with "BS1 WS1") as "%EQ". clarify.
        iApply (SCMem_store_fun_spec with "[PTX] [-]"). instantiate (1:=n). auto.
        { pose proof mask_disjoint_N_Client04_state_tgt; set_solver. }
        { iFrame. done. }
        iIntros (rv') "PTX". rred2r. iApply wpsim_tauR. rred2r.
        iMod (Lifetime.pending_shot with "LIVE_1") as "#DEAD_1".
        iMod (duty_fulfill (v:=1+n) with "[DUTY1]") as "DUTY1". iFrame. simpl; red_tl_lifetime; done.
        iMod (Lifetime.alloc tt) as "[%γ2' LIVE2]".
        iMod (alloc_obligation 2 2) as "[%obl_2 [#OBL_2 PC_2]]".
        iPoseProof (pc_split _ _ 1 1 with "[PC_2]") as "[PC_21 PC_22]". done.
        iMod (pc_drop _ 1 _ _ 1 with "PC_22") as "PC_22"; auto.
        iMod (duty_add (v:=1+n) with "[DUTY2 PC_22] []") as "DUTY2". iFrame.
        { instantiate (1 := (dead γ2' tt)%S). iEval (simpl; red_tl_all).
          iModIntro. iIntros "#D". iModIntro. done.
        }
        iPoseProof (duty_tpromise with "[DUTY2]") as "#PRM2". 2: done. simpl; left; auto.
        iMod (AuthExcls.b_w_update _ _ _ (tid2, obl_2, γ2') with "BS2 WS2") as "[BS2 WS2]".
        iMod (AuthExcls.b_w_update _ _ _ (tid1, obl_2, γ2') with "BM1 MY_W2") as "[BM1 WM1]".
        clear γ2 k2. rename γ2' into γ2. rename obl_2 into k2.
        iMod ("CI_CLOSE" with "[- WM1]") as "_".
        { iEval (unfold client04Inv; simpl; red_tl).
          do 6 (iExists _; red_tl); red_tl_all. 
          iSplitL "BS1"; [done|]. iSplitL "BS2"; [done|]. iSplitL "BM1"; [done|]. iSplitL "BM2"; [done|].
          iRight. iSplitR; [done | ]. iLeft. simpl. iFrame. iSplitR; [done | ]. iLeft. iFrame.
        }
        iApply wpsim_reset. iApply wpsim_base. auto.
        iApply "CIH". instantiate (1:=(k2, γ2)). iSplitR; iFrame. iModIntro; iFrame.
        iSplit; [done|]. iSplit; [done|]. iSplit; [done|]. iSplit; [done|]. iSplit; done.
      }
      { (* Case 1-2 : thread 2 has written when I'm storing *)
        iDestruct "H2" as "(PTX & #DEADI2 & LIVE_1 & WS2 & DUTY2 & [(DUTY1 & PC1 & WS1) | MY_W2])"; cycle 1.
        { iExFalso; iApply (AuthExcls.w_w_false with "MY_W MY_W2"). }
        iPoseProof (AuthExcls.b_w_eq with "BM1 MY_W") as "%EQ". clarify.
        iApply (SCMem_store_fun_spec with "[PTX] [-]"). instantiate (1:=n). auto.
        { pose proof mask_disjoint_N_Client04_state_tgt; set_solver. }
        { iFrame. done. }
        iIntros (rv) "PTX". rred2r. iApply wpsim_tauR. rred2r.
        iMod (Lifetime.pending_shot with "LIVE_1") as "#DEAD_1".
        iMod (Lifetime.pending_shot with "LIVEI1") as "#DEADI1".
        iMod (duty_fulfill (v:=1+n) with "[DUTY1]") as "DUTY1". iFrame. simpl; red_tl_lifetime; done.
        iMod (Lifetime.alloc tt) as "[%γ2' LIVE2]".
        iMod (alloc_obligation 2 2) as "[%obl_2 [#OBL_2 PC_2]]".
        iPoseProof (pc_split _ _ 1 1 with "[PC_2]") as "[PC_21 PC_22]". done.
        iMod (pc_drop _ 1 _ _ 1 with "PC_22") as "PC_22"; auto.
        iMod (duty_add (v:=1+n) with "[DUTY2 PC_22] []") as "DUTY2". iFrame.
        { instantiate (1 := (dead γ2' tt)%S). iEval (simpl; red_tl_all).
          iModIntro. iIntros "#D". iModIntro. done.
        }
        iPoseProof (duty_tpromise with "[DUTY2]") as "#PRM2". 2: done. simpl; left; auto.
        iMod (AuthExcls.b_w_update _ _ _ (tid2, obl_2, γ2') with "BS2 WS2") as "[BS2 WS2]".
        iMod (AuthExcls.b_w_update _ _ _ (tid1, obl_2, γ2') with "BM1 MY_W") as "[BM1 WM1]".
        iMod ("CI_CLOSE" with "[- WM1]") as "_".
        { iEval (unfold client04Inv; simpl; red_tl).
          do 6 (iExists _; red_tl); red_tl_all. 
          iSplitL "BS1"; [done|]. iSplitL "BS2"; [done|]. iSplitL "BM1"; [done|]. iSplitL "BM2"; [done|].
          iRight. iSplitR; [done | ]. iLeft. simpl. iFrame. iSplitR; [done | ]. iLeft. iFrame.
        }
        (* Coinduction point *)
        clear γ2 k2. rename γ2' into γ2. rename obl_2 into k2. iClear "DEAD_1".
        iApply wpsim_reset. iStopProof.
        pose (k2, γ2) as p. replace k2 with (p.1) by ss. replace γ2 with (p.2) by ss. generalize p. clear p.
        eapply wpsim_coind. auto. clear k2 γ2.
        ii. destruct a as [k2 γ2].
        iIntros "[#HG1 #CIH] [(#INV & #MEM & #DEADI & #OBL_2 & #DEADI1 & #OBL2 & #PRM2) MY_W]". simpl.
        iApply (Client04_load_loop_spec1 with "[MY_W] [-]").
        { simpl. red_tl_all; simpl. rewrite red_syn_inv; rewrite red_syn_tgt_interp_as; red_tl_all.
          iFrame. do 5 (iSplit; [done | ]). done. }
        iIntros (rv') "(%EQ & %k0 & %γ0 & POST)"; subst. iEval (simpl; red_tl_all; simpl) in "POST".
        iDestruct "POST" as "(#DEADI2 & DUTY1 & PC1 & WS1)". rred2r.
        iPoseProof (pc_split _ _ 1 1 with "PC1") as "[PC11 PC1]".
        iApply (wpsim_sync_gen with "[DUTY1 PC11]"). instantiate (1:=1+n). auto.
        { iFrame. iApply pcs_cons_fold; iFrame. }
        iIntros "DUTY1 _". iModIntro. lred2r. rred2r. iApply wpsim_tauR. rred2r.
        iApply wpsim_observe. iIntros. rred2r. lred2r.
        iApply wpsim_tauR. iApply wpsim_tauL. rred2r. lred2r. iApply wpsim_tauR.
        do 2 rewrite unfold_iter_eq. lred2r. rred2r.
        iApply (wpsim_yieldR_gen with "[DUTY1 PC1]"). instantiate (1:=1+n). auto. iFrame.
        { iApply pcs_cons_fold; iFrame. }
        iIntros "DUTY1 _". iModIntro. rred2r.
        (* Write 1 *)
        iClear "OBL2 PRM2 OBL_2". clear tid2 γ2 k2.
        iInv "INV" as "CI" "CI_CLOSE".
        iEval (unfold client04Inv; red_tl_all; simpl; red_tl) in "CI".
        iDestruct "CI" as "[%tid1' CI]". iEval (red_tl) in "CI".
        iDestruct "CI" as "[%tid2 CI]". iEval (red_tl) in "CI".
        iDestruct "CI" as "[%γ1' CI]". iEval (red_tl) in "CI".
        iDestruct "CI" as "[%γ2 CI]". iEval (red_tl) in "CI".
        iDestruct "CI" as "[%k1' CI]". iEval (red_tl) in "CI".
        iDestruct "CI" as "[%k2 CI]". iEval (red_tl_all; simpl) in "CI".
        iDestruct "CI" as "(BS1 & BS2 & BM1 & BM2 & [H0 | [_ [H1 | H2]]])".
        { iDestruct "H0" as "(_ & LIVE & _)". iExFalso; iApply (Lifetime.pending_not_shot with "LIVE"). done. }
        { iDestruct "H1" as "(PTX & _ & LIVE_2 & WS1_2 & DUTY1_2 & _)".
          iExFalso; iApply (AuthExcls.w_w_false with "WS1 WS1_2").
        }
        iDestruct "H2" as "(PTX & _ & LIVE_1 & WS2 & DUTY2 & [(_ & _ & WS1_2) | MY_W2])".
        { iExFalso; iApply (AuthExcls.w_w_false with "WS1 WS1_2"). }
        iPoseProof (AuthExcls.b_w_eq with "BS1 WS1") as "%EQ". clarify.
        iApply (SCMem_store_fun_spec with "[PTX] [-]"). instantiate (1:=n). auto.
        { pose proof mask_disjoint_N_Client04_state_tgt; set_solver. }
        { iFrame. done. }
        iIntros (rv') "PTX". rred2r. iApply wpsim_tauR. rred2r.
        iMod (Lifetime.pending_shot with "LIVE_1") as "#DEAD_1".
        iMod (duty_fulfill (v:=1+n) with "[DUTY1]") as "DUTY1". iFrame. simpl; red_tl_lifetime; done.
        iMod (Lifetime.alloc tt) as "[%γ2' LIVE2]".
        iMod (alloc_obligation 2 2) as "[%obl_2 [#OBL_2 PC_2]]".
        iPoseProof (pc_split _ _ 1 1 with "[PC_2]") as "[PC_21 PC_22]". done.
        iMod (pc_drop _ 1 _ _ 1 with "PC_22") as "PC_22"; auto.
        iMod (duty_add (v:=1+n) with "[DUTY2 PC_22] []") as "DUTY2". iFrame.
        { instantiate (1 := (dead γ2' tt)%S). iEval (simpl; red_tl_all).
          iModIntro. iIntros "#D". iModIntro. done.
        }
        iPoseProof (duty_tpromise with "[DUTY2]") as "#PRM2". 2: done. simpl; left; auto.
        iMod (AuthExcls.b_w_update _ _ _ (tid2, obl_2, γ2') with "BS2 WS2") as "[BS2 WS2]".
        iMod (AuthExcls.b_w_update _ _ _ (tid1, obl_2, γ2') with "BM1 MY_W2") as "[BM1 WM1]".
        clear γ2 k2. rename γ2' into γ2. rename obl_2 into k2.
        iMod ("CI_CLOSE" with "[- WM1]") as "_".
        { iEval (unfold client04Inv; simpl; red_tl).
          do 6 (iExists _; red_tl); red_tl_all. 
          iSplitL "BS1"; [done|]. iSplitL "BS2"; [done|]. iSplitL "BM1"; [done|]. iSplitL "BM2"; [done|].
          iRight. iSplitR; [done | ]. iLeft. simpl. iFrame. iSplitR; [done | ]. iLeft. iFrame.
        }
        iApply wpsim_reset. iApply wpsim_base. auto.
        iApply "CIH". instantiate (1:=(k2, γ2)). iSplitR; iFrame. iModIntro; iFrame.
        iSplit; [done|]. iSplit; [done|]. iSplit; [done|]. iSplit; [done|]. iSplit; [done | ]. iSplit; done.
      }
    }
    (* Case 2 : x points to 2 *)
    { iPoseProof (AuthExcls.b_w_eq with "BM1 MY_W") as "%EQ". clarify.
      iDestruct "H2" as "(PTX & #DEADI2 & LIVE1 & WM2 & DUTY2 & [(DUTY1 & PC1 & WS1) | WM1])"; cycle 1.
      { iExFalso; iApply (AuthExcls.w_w_false with "MY_W WM1"). }
      iMod (pc_drop _ 1 _ _ 3 with "PC1") as "PC1". auto.
      iPoseProof (pc_split _ _ 1 2 with "PC1") as "[PC11 PC1]".
      iApply (wpsim_yieldR_gen with "[DUTY1 PC11]"). instantiate (1:=1+n). auto. iFrame.
      { iApply (pcs_cons_fold). iFrame. }
      iIntros "DUTY1 CRED".
      iMod ("CI_CLOSE" with "[- DUTY1 PC1 WS1 LIVEI1]") as "_".
      { iEval (unfold client04Inv; simpl; red_tl).
        do 6 (iExists _; red_tl); red_tl_all.
        iSplitL "BS1"; [done|]. iSplitL "BS2"; [done|]. iSplitL "BM1"; [done|].
        iSplitL "BM2"; [done|]. iRight. iSplitR; [done | ]. iRight. simpl.
        iSplitL "PTX"; [done | ]. iSplitR; [done | ]. iSplitL "LIVE1"; [done | ].
        iSplitL "WM2"; [done | ]. iSplitL "DUTY2"; [done | ]. iRight. done.
      }
      iModIntro. rred2r. clear tid2.
      iInv "INV" as "CI" "CI_CLOSE".
      iEval (unfold client04Inv; red_tl_all; simpl; red_tl) in "CI".
      iDestruct "CI" as "[%tid1' CI]". iEval (red_tl) in "CI".
      iDestruct "CI" as "[%tid2 CI]". iEval (red_tl) in "CI".
      iDestruct "CI" as "[%γ1' CI]". iEval (red_tl) in "CI".
      iDestruct "CI" as "[%γ2' CI]". iEval (red_tl) in "CI".
      iDestruct "CI" as "[%k1' CI]". iEval (red_tl) in "CI".
      iDestruct "CI" as "[%k2' CI]". iEval (red_tl_all; simpl) in "CI".
      iDestruct "CI" as "(BS1 & BS2 & BM1 & BM2 & [H0 | [_ [H1 | H2]]])".
      { iDestruct "H0" as "(_ & LIVE & _)". iExFalso; iApply (Lifetime.pending_not_shot with "LIVE"). done. }
      { iDestruct "H1" as "(PTX & _ & _ & WS1' & _)".
        iExFalso; iApply (AuthExcls.w_w_false with "WS1 WS1'").
      }
      iDestruct "H2" as "(PTX & _ & LIVE1 & WS2 & DUTY2 & [(_ & _ & WS1') | WM1])".
      { iExFalso; iApply (AuthExcls.w_w_false with "WS1 WS1'"). }
      iPoseProof (AuthExcls.b_w_eq with "BS1 WS1") as "%EQ". clarify.
      iApply (SCMem_store_fun_spec with "[PTX] [-]"). instantiate (1:=n). auto.
      { pose proof mask_disjoint_N_Client04_state_tgt; set_solver. }
      { iFrame. done. }
      iIntros (rv) "PTX". rred2r. iApply wpsim_tauR. rred2r.
      iMod (Lifetime.pending_shot with "LIVE1") as "#DEAD1".
      iMod (Lifetime.pending_shot with "LIVEI1") as "#DEADI1".
      iMod (duty_fulfill (v:=1+n) with "[DUTY1]") as "DUTY1". iFrame. simpl; red_tl_lifetime; done.
      clear γ2 k2. iMod (Lifetime.alloc tt) as "[%γ2 LIVE2]".
      iMod (alloc_obligation 2 2) as "[%k2 [#OBL2 PC2]]".
      iPoseProof (pc_split _ _ 1 1 with "[PC2]") as "[PC21 PC22]". done.
      iMod (pc_drop _ 1 _ _ 1 with "PC22") as "PC22"; auto.
      iMod (duty_add (v:=1+n) with "[DUTY2 PC22] []") as "DUTY2". iFrame.
      { instantiate (1 := (dead γ2 tt)%S). iEval (simpl; red_tl_all).
        iModIntro. iIntros "#D". iModIntro. done.
      }
      iPoseProof (duty_tpromise with "[DUTY2]") as "#PRM2". 2: done. simpl; left; auto.
      iMod (AuthExcls.b_w_update _ _ _ (tid2, k2, γ2) with "BS2 WS2") as "[BS2 WS2]".
      iMod (AuthExcls.b_w_update _ _ _ (tid1, k2, γ2) with "BM1 WM1") as "[BM1 WM1]".
      iMod ("CI_CLOSE" with "[- WM1]") as "_".
      { iEval (unfold client04Inv; simpl; red_tl).
        do 6 (iExists _; red_tl); red_tl_all. 
        iSplitL "BS1"; [done|]. iSplitL "BS2"; [done|].
        iSplitL "BM1"; [done|]. iSplitL "BM2"; [done|].
        iRight. iSplitR; [done | ]. iLeft. simpl. iFrame. iSplitR; [done | ]. iLeft. iFrame.
      }
      (* Coinduction point *)
      iClear "DEAD1".
      iApply wpsim_reset. iStopProof.
      pose (k2, γ2) as p. replace k2 with (p.1) by ss. replace γ2 with (p.2) by ss. generalize p. clear p.
      eapply wpsim_coind. auto. clear k2 γ2.
      ii. destruct a as [k2 γ2].
      iIntros "[#HG1 #CIH] [(#INV & #MEM & #DEADI & #OBL_2 & #DEADI1 & #OBL2 & #PRM2) WM1]". simpl.
      iApply (Client04_load_loop_spec1 with "[WM1] [-]").
      { simpl. red_tl_all; simpl. rewrite red_syn_inv; rewrite red_syn_tgt_interp_as; red_tl_all.
        iFrame. do 5 (iSplit; [done | ]). done. }
      iIntros (rv') "(%EQ & %k0 & %γ0 & POST)"; subst. iEval (simpl; red_tl_all; simpl) in "POST".
      iDestruct "POST" as "(#DEADI2 & DUTY1 & PC1 & WS1)". rred2r.
      iPoseProof (pc_split _ _ 1 1 with "PC1") as "[PC11 PC1]".
      iApply (wpsim_sync_gen with "[DUTY1 PC11]"). instantiate (1:=1+n). auto.
      { iFrame. iApply pcs_cons_fold; iFrame. }
      iIntros "DUTY1 _". iModIntro. lred2r. rred2r. iApply wpsim_tauR. rred2r.
      iApply wpsim_observe. iIntros. rred2r. lred2r.
      iApply wpsim_tauR. iApply wpsim_tauL. rred2r. lred2r. iApply wpsim_tauR.
      do 2 rewrite unfold_iter_eq. lred2r. rred2r.
      iApply (wpsim_yieldR_gen with "[DUTY1 PC1]"). instantiate (1:=1+n). auto. iFrame.
      { iApply pcs_cons_fold; iFrame. }
      iIntros "DUTY1 _". iModIntro. rred2r.
      (* Write 1 *)
      iClear "OBL2 PRM2 OBL_2". clear tid2 γ2 k2 γ2'.
      iInv "INV" as "CI" "CI_CLOSE".
      iEval (unfold client04Inv; red_tl_all; simpl; red_tl) in "CI".
      iDestruct "CI" as "[%tid1' CI]". iEval (red_tl) in "CI".
      iDestruct "CI" as "[%tid2 CI]". iEval (red_tl) in "CI".
      iDestruct "CI" as "[%γ1' CI]". iEval (red_tl) in "CI".
      iDestruct "CI" as "[%γ2 CI]". iEval (red_tl) in "CI".
      iDestruct "CI" as "[%k1' CI]". iEval (red_tl) in "CI".
      iDestruct "CI" as "[%k2 CI]". iEval (red_tl_all; simpl) in "CI".
      iDestruct "CI" as "(BS1 & BS2 & BM1 & BM2 & [H0 | [_ [H1 | H2]]])".
      { iDestruct "H0" as "(_ & LIVE & _)". iExFalso; iApply (Lifetime.pending_not_shot with "LIVE"). done. }
      { iDestruct "H1" as "(PTX & _ & LIVE_2 & WS1_2 & DUTY1_2 & _)".
        iExFalso; iApply (AuthExcls.w_w_false with "WS1 WS1_2").
      }
      iDestruct "H2" as "(PTX & _ & LIVE_1 & WS2 & DUTY2 & [(_ & _ & WS1_2) | MY_W2])".
      { iExFalso; iApply (AuthExcls.w_w_false with "WS1 WS1_2"). }
      iPoseProof (AuthExcls.b_w_eq with "BS1 WS1") as "%EQ". clarify.
      iApply (SCMem_store_fun_spec with "[PTX] [-]"). instantiate (1:=n). auto.
      { pose proof mask_disjoint_N_Client04_state_tgt; set_solver. }
      { iFrame. done. }
      iIntros (rv') "PTX". rred2r. iApply wpsim_tauR. rred2r.
      iMod (Lifetime.pending_shot with "LIVE_1") as "#DEAD_1".
      iMod (duty_fulfill (v:=1+n) with "[DUTY1]") as "DUTY1". iFrame. simpl; red_tl_lifetime; done.
      iMod (Lifetime.alloc tt) as "[%γ2' LIVE2]".
      iMod (alloc_obligation 2 2) as "[%obl_2 [#OBL_2 PC_2]]".
      iPoseProof (pc_split _ _ 1 1 with "[PC_2]") as "[PC_21 PC_22]". done.
      iMod (pc_drop _ 1 _ _ 1 with "PC_22") as "PC_22"; auto.
      iMod (duty_add (v:=1+n) with "[DUTY2 PC_22] []") as "DUTY2". iFrame.
      { instantiate (1 := (dead γ2' tt)%S). iEval (simpl; red_tl_all).
        iModIntro. iIntros "#D". iModIntro. done.
      }
      iPoseProof (duty_tpromise with "[DUTY2]") as "#PRM2". 2: done. simpl; left; auto.
      iMod (AuthExcls.b_w_update _ _ _ (tid2, obl_2, γ2') with "BS2 WS2") as "[BS2 WS2]".
      iMod (AuthExcls.b_w_update _ _ _ (tid1, obl_2, γ2') with "BM1 MY_W2") as "[BM1 WM1]".
      clear γ2 k2. rename γ2' into γ2. rename obl_2 into k2.
      iMod ("CI_CLOSE" with "[- WM1]") as "_".
      { iEval (unfold client04Inv; simpl; red_tl).
        do 6 (iExists _; red_tl); red_tl_all. 
        iSplitL "BS1"; [done|]. iSplitL "BS2"; [done|]. iSplitL "BM1"; [done|]. iSplitL "BM2"; [done|].
        iRight. iSplitR; [done | ]. iLeft. simpl. iFrame. iSplitR; [done | ]. iLeft. iFrame.
      }
      iApply wpsim_reset. iApply wpsim_base. auto.
      iApply "CIH". instantiate (1:=(k2, γ2)). iSplitR; iFrame. iModIntro; iFrame.
      iSplit; [done|]. iSplit; [done|]. iSplit; [done|]. iSplit; [done|]. iSplit; [done | ]. iSplit; done.
    }
    Unshelve. all: auto.
  Qed.

  Lemma Client04_load_loop_spec2
        tid n
  :
  ⊢ ∀ (γi γi1 γi2 γs1 γs2 γm1 γm2 k1 γ1 : τ{nat, 2+n}),
    [@ tid, 1+n, ⊤ @]
      ⧼⟦((⤉ syn_inv (1+n) N_Client04 (client04Inv n γi γi1 γi2 γs1 γs2 γm1 γm2))
        ∗ (⤉ syn_tgt_interp_as n sndl (fun m => s_memory_black m))
        ∗ (⤉⤉ ○ γm2 (tid, k1, γ1))
        ∗ (⤉⤉ dead γi ())
        ∗ (⤉⤉ dead γi2 ())
        ∗ (◆[k1, 2])
        ∗ (⤉ -[k1](0)-◇ (dead γ1 () : sProp (1+n))))%S, 2+n⟧⧽
        (OMod.close_itree omod (SCMem.mod gvs) (load_loop 2))
        ⧼rv, ⌜rv = 1⌝
          ∗ ∃ k2 γ2, ⟦((⤉⤉ dead γi1 ())
            ∗ (⤉ Duty (tid) [(k2, 0, dead γ2 tt : sProp (1+n))])
            ∗ (◇[k2](1, 2))
            ∗ (⤉⤉ ○ γs2 (tid, k2, γ2)))%S, 2+n⟧⧽
  .
  Proof.
    iIntros. iStartTriple. simpl. red_tl_all; simpl. rewrite red_syn_inv; rewrite red_syn_tgt_interp_as.
    iIntros "(#INV & #MEM & WM2 & #DEADI & #DEADI2 & #OBL1 & #PRM1)". iIntros "POST".
    (* Induction point *)
    iRevert "WM2 POST".
    iMod (tpromise_ind with "[] [-]") as "IH"; cycle 2. done. iSplit; done. iModIntro. iIntros "IH". iModIntro.
    iIntros "WM2 POST". iEval (unfold load_loop at 1; rewrite -> unfold_iter_eq). rred2r.
    iInv "INV" as "CI" "CI_CLOSE".
    iEval (unfold client04Inv; red_tl_all; simpl; red_tl) in "CI".
    iDestruct "CI" as "[%tid1 CI]". iEval (red_tl) in "CI".
    iDestruct "CI" as "[%tid2 CI]". iEval (red_tl) in "CI".
    iDestruct "CI" as "[%γ1' CI]". iEval (red_tl) in "CI".
    iDestruct "CI" as "[%γ2 CI]". iEval (red_tl) in "CI".
    iDestruct "CI" as "[%k1' CI]". iEval (red_tl) in "CI".
    iDestruct "CI" as "[%k2 CI]". iEval (red_tl_all; simpl) in "CI".
    iDestruct "CI" as "(BS1 & BS2 & BM1 & BM2 & [H0 | [_ [H1 | H2]]])".
    { iDestruct "H0" as "(_ & LIVE & _)". iExFalso; iApply (Lifetime.pending_not_shot with "LIVE"). done. }
    { (* Case 1 : thread 1 has written when loading *)
      iPoseProof (AuthExcls.b_w_eq with "BM2 WM2") as "%EQ". clarify.
      iDestruct "H1" as "(PTX & #DEADI1 & LIVE2 & WS1 & DUTY1 & [(DUTY2 & PC2 & WS2) | WM2'])"; cycle 1.
      { iExFalso; iApply (AuthExcls.w_w_false with "WM2 WM2'"). }
      (* Load 2 *)
      iMod (pc_drop _ 1 _ _ 4 with "PC2") as "PC2". auto.
      iPoseProof (pc_split _ _ 1 3 with "PC2") as "[PC21 PC2]".
      iApply (wpsim_yieldR_gen with "[DUTY2 PC21]"). instantiate (1:=1+n). auto. iFrame.
      { iApply pcs_cons_fold. iFrame. } iIntros "DUTY2 CRED".
      iMod ("CI_CLOSE" with "[- DUTY2 PC2 WS2 POST]") as "_".
      { iEval (unfold client04Inv; simpl; red_tl).
        do 6 (iExists _; red_tl); red_tl_all. 
        iSplitL "BS1"; [done|]. iSplitL "BS2"; [done|]. iSplitL "BM1"; [done|]. iSplitL "BM2"; [done|].
        iRight. iSplitR; [done | ]. iLeft. simpl. iFrame. done.
      }
      iModIntro. rred2r.
      iClear "OBL1 PRM1". clear tid1 γ1 k1.
      iInv "INV" as "CI" "CI_CLOSE".
      iEval (unfold client04Inv; red_tl_all; simpl; red_tl) in "CI".
      iDestruct "CI" as "[%tid1 CI]". iEval (red_tl) in "CI".
      iDestruct "CI" as "[%tid2' CI]". iEval (red_tl) in "CI".
      iDestruct "CI" as "[%γ1 CI]". iEval (red_tl) in "CI".
      iDestruct "CI" as "[%γ2' CI]". iEval (red_tl) in "CI".
      iDestruct "CI" as "[%k1 CI]". iEval (red_tl) in "CI".
      iDestruct "CI" as "[%k2' CI]". iEval (red_tl_all; simpl) in "CI".
      iDestruct "CI" as "(BS1 & BS2 & BM1 & BM2 & [H0 | [_ [H1 | H2]]])".
      { iDestruct "H0" as "(_ & LIVE & _)". iExFalso; iApply (Lifetime.pending_not_shot with "LIVE"). done. }
      2:{ iDestruct "H2" as "(PTX & _ & _ & WS2' & _)".
        iExFalso; iApply (AuthExcls.w_w_false with "WS2 WS2'").
      }
      iDestruct "H1" as "(PTX & _ & LIVE2 & WS1 & DUTY1 & [(_ & _ & WS2') | WM2])".
      { iExFalso; iApply (AuthExcls.w_w_false with "WS2 WS2'"). }
      iApply (SCMem_load_fun_spec with "[PTX]"). instantiate (1:=n). auto.
      { pose mask_disjoint_N_Client04_state_tgt; set_solver. }
      { iFrame. done. }
      iIntros (rv') "[% PTX]". subst. rred2r. iApply wpsim_tauR. rred2r.
      iPoseProof (pc_split _ _ 1 2 with "PC2") as "[PC21 PC2]".
      iApply (wpsim_yieldR_gen with "[DUTY2 PC21]"). instantiate (1:=1+n). auto. iFrame.
      { iApply pcs_cons_fold. iFrame. } iIntros "DUTY2 _".
      iMod ("CI_CLOSE" with "[- DUTY2 PC2 WS2 POST]") as "_".
      { iEval (unfold client04Inv; simpl; red_tl).
        do 6 (iExists _; red_tl); red_tl_all. 
        iSplitL "BS1"; [done|]. iSplitL "BS2"; [done|]. iSplitL "BM1"; [done|]. iSplitL "BM2"; [done|].
        iRight. iSplitR; [done | ]. iLeft. simpl. iFrame. done.
      }
      iModIntro. rred2r. lred2r.
      iApply SCMem_compare_fun_spec. instantiate (1:=n). auto. set_solver.
      { simpl. des_ifs. iApply (tgt_interp_as_equiv with "MEM"). iIntros. iSplit.
        { iIntros. simpl. red_tl; simpl. iSplit; [done | iPureIntro; auto]. }
        { simpl. red_tl; simpl. iIntros "[? _]". done. }
      }
      iIntros (rv) "[_ %NEQ]". exploit NEQ. auto. i; subst. rred2r.
      iApply wpsim_tauR. rred2r.
      iApply ("POST" with "[-]").
      { iSplit; auto. iExists k2, γ2. red_tl_all; simpl. iFrame. done. }
    }
    { (* Case 2 : no one has written when I'm loading *)
      iPoseProof (AuthExcls.b_w_eq with "BM2 WM2") as "%EQ". clarify.
      iDestruct "H2" as "(PTX & _ & LIVE1 & WS2 & DUTY2 & REST)".
      (* Yield *)
      iApply (wpsim_yieldR_gen with "[DUTY2]"). instantiate (1:=1+n). auto. iFrame. iIntros "DUTY2 CRED".
      iMod ("IH" with "CRED") as "[IH | #DEAD]"; cycle 1.
      { iExFalso; iApply (Lifetime.pending_not_shot with "LIVE1"). simpl; red_tl_lifetime. done. }
      iMod ("CI_CLOSE" with "[- WM2 IH POST]") as "_".
      { iEval (unfold client04Inv; simpl; red_tl).
        do 6 (iExists _; red_tl); red_tl_all.
        iSplitL "BS1"; [done|]. iSplitL "BS2"; [done|]. iSplitL "BM1"; [done|]. iSplitL "BM2"; [done|].
        iRight. iSplitR; [done | ]. iRight. simpl. iFrame. done.
      }
      iModIntro. rred2r.
      clear tid1 γ2 k2.
      iInv "INV" as "CI" "CI_CLOSE".
      iEval (unfold client04Inv; red_tl_all; simpl; red_tl) in "CI".
      iDestruct "CI" as "[%tid1 CI]". iEval (red_tl) in "CI".
      iDestruct "CI" as "[%tid2' CI]". iEval (red_tl) in "CI".
      iDestruct "CI" as "[%γ1' CI]". iEval (red_tl) in "CI".
      iDestruct "CI" as "[%γ2 CI]". iEval (red_tl) in "CI".
      iDestruct "CI" as "[%k1' CI]". iEval (red_tl) in "CI".
      iDestruct "CI" as "[%k2 CI]". iEval (red_tl_all; simpl) in "CI".
      iDestruct "CI" as "(BS1 & BS2 & BM1 & BM2 & [H0 | [_ [H1 | H2]]])".
      { iDestruct "H0" as "(_ & LIVE & _)". iExFalso; iApply (Lifetime.pending_not_shot with "LIVE"). done. }
      { iPoseProof (AuthExcls.b_w_eq with "BM2 WM2") as "%EQ". clarify.
        iDestruct "H1" as "(PTX & #DEADI1 & LIVE2 & WS1 & DUTY1 & [(DUTY2 & PC2 & WS2) | WM2'])"; cycle 1.
        { iExFalso; iApply (AuthExcls.w_w_false with "WM2 WM2'"). }
        iApply (SCMem_load_fun_spec with "[PTX]"). instantiate (1:=n). auto.
        { pose mask_disjoint_N_Client04_state_tgt; set_solver. }
        { iFrame. done. }
        iIntros (rv') "[% PTX]". subst. rred2r. iApply wpsim_tauR. rred2r.
        iMod (pc_drop _ 1 _ _ 3 with "PC2") as "PC2". auto.
        iPoseProof (pc_split _ _ 1 2 with "PC2") as "[PC21 PC2]".
        iApply (wpsim_yieldR_gen with "[DUTY2 PC21]"). instantiate (1:=1+n). auto. iFrame.
        { iApply pcs_cons_fold. iFrame. } iIntros "DUTY2 CRED".
        iMod ("CI_CLOSE" with "[- DUTY2 PC2 WS2 POST CRED]") as "_".
        { iEval (unfold client04Inv; simpl; red_tl).
          do 6 (iExists _; red_tl); red_tl_all. 
          iSplitL "BS1"; [done|]. iSplitL "BS2"; [done|]. iSplitL "BM1"; [done|]. iSplitL "BM2"; [done|].
          iRight. iSplitR; [done | ]. iLeft. simpl. iFrame. done.
        }
        iModIntro. rred2r.
        iApply SCMem_compare_fun_spec. instantiate (1:=n). auto. set_solver.
        { simpl. des_ifs. iApply (tgt_interp_as_equiv with "MEM"). iIntros. iSplit.
          { iIntros. simpl. red_tl; simpl. iSplit; [done | iPureIntro; auto]. }
          { simpl. red_tl; simpl. iIntros "[? _]". done. }
        }
        iIntros (rv) "[_ %NEQ]". exploit NEQ. auto. i; subst. rred2r.
        iApply wpsim_tauR. rred2r.
        iApply ("POST" with "[-]").
        { iSplit; auto. iExists k2, γ2. red_tl_all; simpl. iFrame. done. }
      }
      { iPoseProof (AuthExcls.b_w_eq with "BM2 WM2") as "%EQ". clarify.
        iDestruct "H2" as "(PTX & _ & LIVE1 & WS2 & DUTY2 & REST)".
        (* Load 1 - induction by tpromise *)
        iApply (SCMem_load_fun_spec with "[PTX]"). instantiate (1:=n). auto.
        { pose mask_disjoint_N_Client04_state_tgt; set_solver. }
        { iFrame. done. }
        iIntros (rv') "[% PTX]". subst. rred2r. iApply wpsim_tauR. rred2r.
        iApply (wpsim_yieldR_gen with "[DUTY2]"). instantiate (1:=1+n). auto. iFrame. iIntros "DUTY2 CRED".
        iMod ("CI_CLOSE" with "[- WM2 IH POST]") as "_".
        { iEval (unfold client04Inv; simpl; red_tl).
          do 6 (iExists _; red_tl); red_tl_all. 
          iSplitL "BS1"; [done|]. iSplitL "BS2"; [done|]. iSplitL "BM1"; [done|]. iSplitL "BM2"; [done|].
          iRight. iSplitR; [done | ]. iRight. simpl. iFrame. done.
        }
        iModIntro. rred2r.
        iApply SCMem_compare_fun_spec. instantiate (1:=n). auto. set_solver.
        { simpl. des_ifs. iApply (tgt_interp_as_equiv with "MEM"). iIntros. iSplit.
          { iIntros. simpl. red_tl; simpl. iSplit; [done | iPureIntro; auto]. }
          { simpl. red_tl; simpl. iIntros "[? _]". done. }
        }
        iIntros (rv) "[%EQ _]". exploit EQ. auto. i; subst. rred2r.
        iApply wpsim_tauR. rred2r. iApply wpsim_tauR. fold (load_loop 1).
        iApply wpsim_stutter_mon. instantiate (1:=ps); auto. instantiate (1:=pt); auto.
        iApply ("IH" with "WM2"). done.
      }
    }
  Unshelve. all: auto.
  Qed.

  Lemma Client04_thread2_spec
        tid2 n
    :
    ⊢ ⟦(∀ (γi γi1 γi2 γs1 γs2 γm1 γm2 k1 γ1 : τ{nat, 2+n}),
           ((⤉ syn_inv (1+n) N_Client04 (client04Inv n γi γi1 γi2 γs1 γs2 γm1 γm2))
              ∗ (⤉ syn_tgt_interp_as n sndl (fun m => (s_memory_black m)))
              ∗ (⤉⤉ ○ γm2 (tid2, k1, γ1))
              ∗ (⤉⤉ live γi2 tt 1))
             -∗
             syn_wpsim (2+n) tid2 ⊤
             (fun rs rt => (⤉ (syn_term_cond (1+n) tid2 _ rs rt))%S)
             false false
             (fn2th Client04Spec.module "thread2" (tt ↑))
             (fn2th Client04.module "thread2" (tt ↑)))%S, 2+n⟧.
  Proof.
    iIntros. red_tl_all. iIntros (γi). red_tl_all. iIntros (γi1).
    red_tl_all. iIntros (γi2). red_tl_all. iIntros (γs1).
    red_tl_all. iIntros (γs2). red_tl_all. iIntros (γm1).
    red_tl_all. iIntros (γm2). red_tl_all. iIntros (k1).
    red_tl_all. iIntros (γ1). red_tl_all. simpl. red_tl_all.
    iEval (rewrite red_syn_inv; rewrite red_syn_wpsim; rewrite red_syn_tgt_interp_as).

    iIntros "(#INV & #MEM & WM2 & LIVEI2)".

    unfold fn2th. simpl. unfold thread2, Client04Spec.thread2.
    rred2r. lred2r.
    
    (* Yield *)
    iEval (do 2 rewrite unfold_iter_eq). rred2r. lred2r.
    iInv "INV" as "CI" "CI_CLOSE".
    iEval (unfold client04Inv; red_tl_all; simpl; red_tl) in "CI".
    iDestruct "CI" as "[%tid1 CI]". iEval (red_tl) in "CI".
    iDestruct "CI" as "[%tid2' CI]". iEval (red_tl) in "CI".
    iDestruct "CI" as "[%γ1' CI]". iEval (red_tl) in "CI".
    iDestruct "CI" as "[%γ2 CI]". iEval (red_tl) in "CI".
    iDestruct "CI" as "[%k1' CI]". iEval (red_tl) in "CI".
    iDestruct "CI" as "[%k2 CI]". iEval (red_tl_all; simpl) in "CI".
    iDestruct "CI" as "(BS1 & BS2 & BM1 & BM2 & [H0 | [#DEADI [H1 | H2]]])".
    3:{ iDestruct "H2" as "(_ & #DEAD & _)". iExFalso; iApply (Lifetime.pending_not_shot with "LIVEI2 DEAD "). }
    (* Case 1 : initialization *)
    { iDestruct "H0" as "(PTX & LIVEI & DUTY1 & DUTY2 & WS1 & WS2)".
      iPoseProof (AuthExcls.b_w_eq with "BM2 WM2") as "%EQ". clarify.
      iApply (wpsim_yieldR_gen with "[DUTY2]"). instantiate (1:=1+n). auto. iFrame.
      iIntros "DUTY2 CRED".
      iMod ("CI_CLOSE" with "[- WM2 CRED LIVEI2]") as "_".
      { iEval (unfold client04Inv; simpl; red_tl).
        do 6 (iExists _; red_tl); red_tl_all.
        iSplitL "BS1"; [done|]. iSplitL "BS2"; [done|]. iSplitL "BM1"; [done|]. iSplitL "BM2"; [done|].
        iLeft. iFrame.
      }
      iModIntro. rred2r. clear tid1 γ2 k2.
      iInv "INV" as "CI" "CI_CLOSE".
      iEval (unfold client04Inv; red_tl_all; simpl; red_tl) in "CI".
      iDestruct "CI" as "[%tid1 CI]". iEval (red_tl) in "CI".
      iDestruct "CI" as "[%tid2' CI]". iEval (red_tl) in "CI".
      iDestruct "CI" as "[%γ1' CI]". iEval (red_tl) in "CI".
      iDestruct "CI" as "[%γ2 CI]". iEval (red_tl) in "CI".
      iDestruct "CI" as "[%k1' CI]". iEval (red_tl) in "CI".
      iDestruct "CI" as "[%k2 CI]". iEval (red_tl_all; simpl) in "CI".
      iDestruct "CI" as "(BS1 & BS2 & BM1 & BM2 & [H0 | [#DEADI [H1 | H2]]])".
      3:{ iDestruct "H2" as "(_ & #DEAD & _)".
          iExFalso; iApply (Lifetime.pending_not_shot with "LIVEI2 DEAD ").
      }
      (* Case 1-1 : no one has written when I'm storing *)
      { iDestruct "H0" as "(PTX & LIVEI & DUTY1 & DUTY2 & WS1 & WS2)".
        iPoseProof (AuthExcls.b_w_eq with "BM2 WM2") as "%EQ". clarify.
        iApply (SCMem_store_fun_spec with "[PTX] [-]"). instantiate (1:=n). auto.
        { pose proof mask_disjoint_N_Client04_state_tgt; set_solver. }
        { iFrame. done. }
        iIntros (rv) "PTX". rred2r. iApply wpsim_tauR. rred2r.
        iMod (Lifetime.pending_shot with "LIVEI") as "#DEADI".
        iMod (Lifetime.pending_shot with "LIVEI2") as "#DEADI2".
        iMod (Lifetime.alloc tt) as "[%γ1' LIVE1]".
        iMod (alloc_obligation 2 2) as "[%obl1 [#OBL1 PC1]]".
        iPoseProof (pc_split _ _ 1 1 with "[PC1]") as "[PC11 PC12]". done.
        iMod (pc_drop _ 1 _ _ 1 with "PC12") as "PC12"; auto.
        iMod (duty_add (v:=1+n) with "[DUTY1 PC12] []") as "DUTY1". iFrame.
        { instantiate (1 := (dead γ1' tt)%S). iEval (simpl; red_tl_all). iModIntro. iIntros "#D". iModIntro. done. }
        iPoseProof (duty_tpromise with "[DUTY1]") as "#PRM2". 2: done. simpl; left; auto.
        iMod (AuthExcls.b_w_update _ _ _ (tid1, obl1, γ1') with "BS1 WS1") as "[BS1 WS1]".
        iMod (AuthExcls.b_w_update _ _ _ (tid2, obl1, γ1') with "BM2 WM2") as "[BM2 WM2]".
        clear γ1 k1. rename γ1' into γ1. rename obl1 into k1.
        iMod ("CI_CLOSE" with "[- WM2]") as "_".
        { iEval (unfold client04Inv; simpl; red_tl).
          do 6 (iExists _; red_tl); red_tl_all.
          iSplitL "BS1"; [done|]. iSplitL "BS2"; [done|]. iSplitL "BM1"; [done|]. iSplitL "BM2"; [done|].
          iRight. iSplitR; [done | ]. iRight. simpl. iFrame. iSplitR; [done|]. iLeft. iFrame.
        }
        (* Coinduction point *)
        iApply wpsim_reset. iStopProof.
        pose (k1, γ1) as p. replace k1 with (p.1) by ss. replace γ1 with (p.2) by ss. generalize p. clear p.
        eapply wpsim_coind. auto. clear k1 γ1.
        ii. destruct a as [k1 γ1].
        iIntros "[#HG1 #CIH] [(#INV & #MEM & #DEADI & #DEADI2 & #OBL1 & #PRM1) WM2]". simpl.
        iApply (Client04_load_loop_spec2 with "[WM2] [-]").
        { simpl. red_tl_all; simpl. rewrite red_syn_inv; rewrite red_syn_tgt_interp_as; red_tl_all.
          iFrame. do 5 (iSplit; [done | ]). done. }
        iIntros (rv') "(%EQ & %k0 & %γ0 & POST)"; subst. iEval (simpl; red_tl_all; simpl) in "POST".
        iDestruct "POST" as "(#DEADI1 & DUTY2 & PC2 & WS2)". rred2r.
        iPoseProof (pc_split _ _ 1 1 with "PC2") as "[PC21 PC2]".
        iApply (wpsim_sync_gen with "[DUTY2 PC21]").
        { instantiate (1:=1+n). auto. }
        { iFrame. iApply (pcs_cons_fold). iSplitL; done. }
        iIntros "DUTY2 CRED". iModIntro. lred2r. rred2r. iApply wpsim_tauR. rred2r.
        iApply wpsim_observe. iIntros (ret). lred2r; rred2r.
        iApply wpsim_tauL; iApply wpsim_tauR. lred2r; rred2r. iApply wpsim_tauR.
        do 2 rewrite unfold_iter_eq. lred2r. rred2r.
        iApply (wpsim_yieldR_gen with "[DUTY2 PC2]"). instantiate (1:=1+n). auto. iFrame.
        { iApply pcs_cons_fold; iFrame. }
        iIntros "DUTY2 _". iModIntro. rred2r.
         iClear "OBL1 PRM1". clear tid1 γ1 k1.
        iInv "INV" as "CI" "CI_CLOSE".
        iEval (unfold client04Inv; red_tl_all; simpl; red_tl) in "CI".
        iDestruct "CI" as "[%tid1 CI]". iEval (red_tl) in "CI".
        iDestruct "CI" as "[%tid2' CI]". iEval (red_tl) in "CI".
        iDestruct "CI" as "[%γ1 CI]". iEval (red_tl) in "CI".
        iDestruct "CI" as "[%γ2' CI]". iEval (red_tl) in "CI".
        iDestruct "CI" as "[%k1 CI]". iEval (red_tl) in "CI".
        iDestruct "CI" as "[%k2' CI]". iEval (red_tl_all; simpl) in "CI".
        iDestruct "CI" as "(BS1 & BS2 & BM1 & BM2 & [H0 | [_ [H1 | H2]]])".
        { iDestruct "H0" as "(_ & LIVE & _)". iExFalso; iApply (Lifetime.pending_not_shot with "LIVE"). done. }
        2:{ iDestruct "H2" as "(PTX & _ & LIVE1 & WS2' & DUTY2' & _)".
          iExFalso; iApply (AuthExcls.w_w_false with "WS2 WS2'").
        }
        iDestruct "H1" as "(PTX & _ & LIVE2 & WS1 & DUTY1 & [(_ & _ & WS2') | WM2])".
        { iExFalso; iApply (AuthExcls.w_w_false with "WS2 WS2'"). }
        iPoseProof (AuthExcls.b_w_eq with "BS2 WS2") as "%EQ". clarify.
        iApply (SCMem_store_fun_spec with "[PTX] [-]"). instantiate (1:=n). auto.
        { pose proof mask_disjoint_N_Client04_state_tgt; set_solver. }
        { iFrame. done. }
        iIntros (rv') "PTX". rred2r. iApply wpsim_tauR. rred2r.
        iMod (Lifetime.pending_shot with "LIVE2") as "#DEAD2".
        iMod (duty_fulfill (v:=1+n) with "[DUTY2]") as "DUTY2". iFrame. simpl; red_tl_lifetime; done.
        iMod (Lifetime.alloc tt) as "[%γ1' LIVE1]".
        iMod (alloc_obligation 2 2) as "[%obl1 [#OBL1 PC1]]".
        iPoseProof (pc_split _ _ 1 1 with "[PC1]") as "[PC11 PC12]". done.
        iMod (pc_drop _ 1 _ _ 1 with "PC11") as "PC11"; auto.
        iMod (duty_add (v:=1+n) with "[DUTY1 PC11] []") as "DUTY1". iFrame.
        { instantiate (1 := (dead γ1' tt)%S). iEval (simpl; red_tl_all).
          iModIntro. iIntros "#D". iModIntro. done.
        }
        iPoseProof (duty_tpromise with "[DUTY1]") as "#PRM1". 2: done. simpl; left; auto.
        iMod (AuthExcls.b_w_update _ _ _ (tid2, obl1, γ1') with "BM2 WM2") as "[BM2 WM2]".
        iMod (AuthExcls.b_w_update _ _ _ (tid1, obl1, γ1') with "BS1 WS1") as "[BS1 WS1]".
        clear γ1 k1. rename γ1' into γ1. rename obl1 into k1.
        iMod ("CI_CLOSE" with "[- WM2]") as "_".
        { iEval (unfold client04Inv; simpl; red_tl).
          do 6 (iExists _; red_tl); red_tl_all. 
          iSplitL "BS1"; [done|]. iSplitL "BS2"; [done|]. iSplitL "BM1"; [done|]. iSplitL "BM2"; [done|].
          iRight. iSplitR; [done | ]. iRight. simpl. iFrame. iSplitR; [done | ]. iLeft. iFrame.
        }
        iApply wpsim_reset. iApply wpsim_base. auto.
        iApply "CIH". instantiate (1:=(k1, γ1)). iSplitR; iFrame. iModIntro; iFrame.
        iSplit; [done|]. iSplit; [done|]. iSplit; [done|]. iSplit; [done|]. iSplit; done.
      }
      { (* Case 1-2 : thread 1 has written when I'm storing *)
        iDestruct "H1" as "(PTX & #DEADI1 & LIVE2 & WS1 & DUTY1 & [(DUTY2 & PC2 & WS2) | WM2'])"; cycle 1.
        { iExFalso; iApply (AuthExcls.w_w_false with "WM2 WM2'"). }
        iPoseProof (AuthExcls.b_w_eq with "BM2 WM2") as "%EQ". clarify.
        iApply (SCMem_store_fun_spec with "[PTX] [-]"). instantiate (1:=n). auto.
        { pose proof mask_disjoint_N_Client04_state_tgt; set_solver. }
        { iFrame. done. }
        iIntros (rv) "PTX". rred2r. iApply wpsim_tauR. rred2r.
        iMod (Lifetime.pending_shot with "LIVE2") as "#DEAD2".
        iMod (Lifetime.pending_shot with "LIVEI2") as "#DEADI2".
        iMod (duty_fulfill (v:=1+n) with "[DUTY2]") as "DUTY2". iFrame. simpl; red_tl_lifetime; done.
        iMod (Lifetime.alloc tt) as "[%γ1' LIVE1]".
        iMod (alloc_obligation 2 2) as "[%obl1 [#OBL1 PC1]]".
        iPoseProof (pc_split _ _ 1 1 with "[PC1]") as "[PC11 PC12]". done.
        iMod (pc_drop _ 1 _ _ 1 with "PC11") as "PC11"; auto.
        iMod (duty_add (v:=1+n) with "[DUTY1 PC11] []") as "DUTY1". iFrame.
        { instantiate (1 := (dead γ1' tt)%S). iEval (simpl; red_tl_all).
          iModIntro. iIntros "#D". iModIntro. done.
        }
        iPoseProof (duty_tpromise with "[DUTY1]") as "#PRM1". 2: done. simpl; left; auto.
        iMod (AuthExcls.b_w_update _ _ _ (tid2, obl1, γ1') with "BM2 WM2") as "[BM2 WM2]".
        iMod (AuthExcls.b_w_update _ _ _ (tid1, obl1, γ1') with "BS1 WS1") as "[BS1 WS1]".
        iMod ("CI_CLOSE" with "[- WM2]") as "_".
        { iEval (unfold client04Inv; simpl; red_tl).
          do 6 (iExists _; red_tl); red_tl_all.
          iSplitL "BS1"; [done|]. iSplitL "BS2"; [done|]. iSplitL "BM1"; [done|]. iSplitL "BM2"; [done|].
          iRight. iSplitR; [done | ]. iRight. simpl. iFrame. iSplitR; [done | ]. iLeft. iFrame.
        }
        (* Coinduction point *)
        clear γ1 k1. rename γ1' into γ1. rename obl1 into k1. iClear "DEAD2".
        iApply wpsim_reset. iStopProof.
        pose (k1, γ1) as p. replace k1 with (p.1) by ss. replace γ1 with (p.2) by ss. generalize p. clear p.
        eapply wpsim_coind. auto. clear k1 γ1.
        ii. destruct a as [k1 γ1].
        iIntros "[#HG1 #CIH] [(#INV & #MEM & #DEADI & #DEADI1 & #DEADI2 & #OBL1 & #PRM1) WM2]". simpl.
        iApply (Client04_load_loop_spec2 with "[WM2] [-]").
        { simpl. red_tl_all; simpl. rewrite red_syn_inv; rewrite red_syn_tgt_interp_as; red_tl_all.
          iFrame. do 5 (iSplit; [done | ]). done. }
        iIntros (rv') "(%EQ & %k0 & %γ0 & POST)"; subst. iEval (simpl; red_tl_all; simpl) in "POST".
        iDestruct "POST" as "(_ & DUTY2 & PC2 & WS2)". rred2r.
        iPoseProof (pc_split _ _ 1 1 with "PC2") as "[PC21 PC2]".
        iApply (wpsim_sync_gen with "[DUTY2 PC21]").
        { instantiate (1:=1+n). auto. }
        { iFrame. iApply (pcs_cons_fold). iSplitL; done. }
        iIntros "DUTY2 CRED". iModIntro. lred2r. rred2r. iApply wpsim_tauR. rred2r.
        iApply wpsim_observe. iIntros (ret). lred2r; rred2r.
        iApply wpsim_tauL; iApply wpsim_tauR. lred2r; rred2r. iApply wpsim_tauR.
        do 2 rewrite unfold_iter_eq. lred2r. rred2r.
        iApply (wpsim_yieldR_gen with "[DUTY2 PC2]"). instantiate (1:=1+n). auto. iFrame.
        { iApply pcs_cons_fold; iFrame. }
        iIntros "DUTY2 _". iModIntro. rred2r.
         iClear "OBL1 PRM1". clear tid1 γ1 k1.
        iInv "INV" as "CI" "CI_CLOSE".
        iEval (unfold client04Inv; red_tl_all; simpl; red_tl) in "CI".
        iDestruct "CI" as "[%tid1 CI]". iEval (red_tl) in "CI".
        iDestruct "CI" as "[%tid2' CI]". iEval (red_tl) in "CI".
        iDestruct "CI" as "[%γ1 CI]". iEval (red_tl) in "CI".
        iDestruct "CI" as "[%γ2' CI]". iEval (red_tl) in "CI".
        iDestruct "CI" as "[%k1 CI]". iEval (red_tl) in "CI".
        iDestruct "CI" as "[%k2' CI]". iEval (red_tl_all; simpl) in "CI".
        iDestruct "CI" as "(BS1 & BS2 & BM1 & BM2 & [H0 | [_ [H1 | H2]]])".
        { iDestruct "H0" as "(_ & LIVE & _)". iExFalso; iApply (Lifetime.pending_not_shot with "LIVE"). done. }
        2:{ iDestruct "H2" as "(PTX & _ & LIVE1 & WS2' & DUTY2' & _)".
          iExFalso; iApply (AuthExcls.w_w_false with "WS2 WS2'").
        }
        iDestruct "H1" as "(PTX & _ & LIVE2 & WS1 & DUTY1 & [(_ & _ & WS2') | WM2])".
        { iExFalso; iApply (AuthExcls.w_w_false with "WS2 WS2'"). }
        iPoseProof (AuthExcls.b_w_eq with "BS2 WS2") as "%EQ". clarify.
        iApply (SCMem_store_fun_spec with "[PTX] [-]"). instantiate (1:=n). auto.
        { pose proof mask_disjoint_N_Client04_state_tgt; set_solver. }
        { iFrame. done. }
        iIntros (rv') "PTX". rred2r. iApply wpsim_tauR. rred2r.
        iMod (Lifetime.pending_shot with "LIVE2") as "#DEAD2".
        iMod (duty_fulfill (v:=1+n) with "[DUTY2]") as "DUTY2". iFrame. simpl; red_tl_lifetime; done.
        iMod (Lifetime.alloc tt) as "[%γ1' LIVE1]".
        iMod (alloc_obligation 2 2) as "[%obl1 [#OBL1 PC1]]".
        iPoseProof (pc_split _ _ 1 1 with "[PC1]") as "[PC11 PC12]". done.
        iMod (pc_drop _ 1 _ _ 1 with "PC11") as "PC11"; auto.
        iMod (duty_add (v:=1+n) with "[DUTY1 PC11] []") as "DUTY1". iFrame.
        { instantiate (1 := (dead γ1' tt)%S). iEval (simpl; red_tl_all).
          iModIntro. iIntros "#D". iModIntro. done.
        }
        iPoseProof (duty_tpromise with "[DUTY1]") as "#PRM1". 2: done. simpl; left; auto.
        iMod (AuthExcls.b_w_update _ _ _ (tid2, obl1, γ1') with "BM2 WM2") as "[BM2 WM2]".
        iMod (AuthExcls.b_w_update _ _ _ (tid1, obl1, γ1') with "BS1 WS1") as "[BS1 WS1]".
        clear γ1 k1. rename γ1' into γ1. rename obl1 into k1.
        iMod ("CI_CLOSE" with "[- WM2]") as "_".
        { iEval (unfold client04Inv; simpl; red_tl).
          do 6 (iExists _; red_tl); red_tl_all. 
          iSplitL "BS1"; [done|]. iSplitL "BS2"; [done|]. iSplitL "BM1"; [done|]. iSplitL "BM2"; [done|].
          iRight. iSplitR; [done | ]. iRight. simpl. iFrame. iSplitR; [done | ]. iLeft. iFrame.
        }
        iApply wpsim_reset. iApply wpsim_base. auto.
        iApply "CIH". instantiate (1:=(k1, γ1)). iSplitR; iFrame. iModIntro; iFrame.
        iSplit; [done|]. iSplit; [done|]. iSplit; [done|]. iSplit; [done|]. iSplit; [done | ]. iSplit; done.
      }
    }
    (* Case 2 : x points to 1 *)
    { iPoseProof (AuthExcls.b_w_eq with "BM2 WM2") as "%EQ". clarify.
      iDestruct "H1" as "(PTX & #DEADI1 & LIVE2 & WM1 & DUTY1 & [(DUTY2 & PC2 & WS2) | WM2'])"; cycle 1.
      { iExFalso; iApply (AuthExcls.w_w_false with "WM2 WM2'"). }
      iMod (pc_drop _ 1 _ _ 3 with "PC2") as "PC2". auto.
      iPoseProof (pc_split _ _ 1 2 with "PC2") as "[PC21 PC2]".
      iApply (wpsim_yieldR_gen with "[DUTY2 PC21]"). instantiate (1:=1+n). auto. iFrame.
      { iApply (pcs_cons_fold). iFrame. }
      iIntros "DUTY2 CRED".
      iMod ("CI_CLOSE" with "[- DUTY2 PC2 WS2 LIVEI2]") as "_".
      { iEval (unfold client04Inv; simpl; red_tl).
        do 6 (iExists _; red_tl); red_tl_all.
        iSplitL "BS1"; [done|]. iSplitL "BS2"; [done|]. iSplitL "BM1"; [done|].
        iSplitL "BM2"; [done|]. iRight. iSplitR; [done | ]. iLeft. simpl.
        iSplitL "PTX"; [done | ]. iSplitR; [done | ]. iSplitL "LIVE2"; [done | ].
        iSplitL "WM1"; [done | ]. iSplitL "DUTY1"; [done | ]. iRight. done.
      }
      iModIntro. rred2r. clear tid1.
      iInv "INV" as "CI" "CI_CLOSE".
      iEval (unfold client04Inv; red_tl_all; simpl; red_tl) in "CI".
      iDestruct "CI" as "[%tid1 CI]". iEval (red_tl) in "CI".
      iDestruct "CI" as "[%tid2' CI]". iEval (red_tl) in "CI".
      iDestruct "CI" as "[%γ1' CI]". iEval (red_tl) in "CI".
      iDestruct "CI" as "[%γ2' CI]". iEval (red_tl) in "CI".
      iDestruct "CI" as "[%k1' CI]". iEval (red_tl) in "CI".
      iDestruct "CI" as "[%k2' CI]". iEval (red_tl_all; simpl) in "CI".
      iDestruct "CI" as "(BS1 & BS2 & BM1 & BM2 & [H0 | [_ [H1 | H2]]])".
      { iDestruct "H0" as "(_ & LIVE & _)". iExFalso; iApply (Lifetime.pending_not_shot with "LIVE"). done. }
      2:{ iDestruct "H2" as "(PTX & _ & _ & WS2' & _)".
        iExFalso; iApply (AuthExcls.w_w_false with "WS2 WS2'").
      }
      iDestruct "H1" as "(PTX & _ & LIVE2 & WS1 & DUTY1 & [(_ & _ & WS2') | WM2])".
      { iExFalso; iApply (AuthExcls.w_w_false with "WS2 WS2'"). }
      iPoseProof (AuthExcls.b_w_eq with "BS2 WS2") as "%EQ". clarify.
      iApply (SCMem_store_fun_spec with "[PTX] [-]"). instantiate (1:=n). auto.
      { pose proof mask_disjoint_N_Client04_state_tgt; set_solver. }
      { iFrame. done. }
      iIntros (rv) "PTX". rred2r. iApply wpsim_tauR. rred2r.
      iMod (Lifetime.pending_shot with "LIVE2") as "#DEAD2".
      iMod (Lifetime.pending_shot with "LIVEI2") as "#DEADI2".
      iMod (duty_fulfill (v:=1+n) with "[DUTY2]") as "DUTY2". iFrame. simpl; red_tl_lifetime; done.
      clear γ1 k1. iMod (Lifetime.alloc tt) as "[%γ1 LIVE2]".
      iMod (alloc_obligation 2 2) as "[%k1 [#OBL1 PC1]]".
      iPoseProof (pc_split _ _ 1 1 with "[PC1]") as "[PC11 PC12]". done.
      iMod (pc_drop _ 1 _ _ 1 with "PC12") as "PC12"; auto.
      iMod (duty_add (v:=1+n) with "[DUTY1 PC12] []") as "DUTY1". iFrame.
      { instantiate (1 := (dead γ1 tt)%S). iEval (simpl; red_tl_all).
        iModIntro. iIntros "#D". iModIntro. done.
      }
      iPoseProof (duty_tpromise with "[DUTY1]") as "#PRM1". 2: done. simpl; left; auto.
      iMod (AuthExcls.b_w_update _ _ _ (tid2, k1, γ1) with "BM2 WM2") as "[BM2 WM2]".
      iMod (AuthExcls.b_w_update _ _ _ (tid1, k1, γ1) with "BS1 WS1") as "[BS1 WS1]".
      iMod ("CI_CLOSE" with "[- WM2]") as "_".
      { iEval (unfold client04Inv; simpl; red_tl).
        do 6 (iExists _; red_tl); red_tl_all. 
        iSplitL "BS1"; [done|]. iSplitL "BS2"; [done|].
        iSplitL "BM1"; [done|]. iSplitL "BM2"; [done|].
        iRight. iSplitR; [done | ]. iRight. simpl. iFrame. iSplitR; [done | ]. iLeft. iFrame.
      }
      (* Coinduction point *)
      iClear "DEAD2".
      iApply wpsim_reset. iStopProof.
      pose (k1, γ1) as p. replace k1 with (p.1) by ss. replace γ1 with (p.2) by ss. generalize p. clear p.
      eapply wpsim_coind. auto. clear k1 γ1.
      ii. destruct a as [k1 γ1].
      iIntros "[#HG1 #CIH] [(#INV & #MEM & #DEADI & #DEADI1 & #DEADI2 & #OBL1 & #PRM1) WM2]". simpl.
      iApply (Client04_load_loop_spec2 with "[WM2] [-]").
      { simpl. red_tl_all; simpl. rewrite red_syn_inv; rewrite red_syn_tgt_interp_as; red_tl_all.
        iFrame. do 5 (iSplit; [done | ]). done. }
      iIntros (rv') "(%EQ & %k0 & %γ0 & POST)"; subst. iEval (simpl; red_tl_all; simpl) in "POST".
      iDestruct "POST" as "(_ & DUTY2 & PC2 & WS2)". rred2r.
      iPoseProof (pc_split _ _ 1 1 with "PC2") as "[PC21 PC2]".
      iApply (wpsim_sync_gen with "[DUTY2 PC21]").
      { instantiate (1:=1+n). auto. }
      { iFrame. iApply (pcs_cons_fold). iSplitL; done. }
      iIntros "DUTY2 CRED". iModIntro. lred2r. rred2r. iApply wpsim_tauR. rred2r.
      iApply wpsim_observe. iIntros (ret). lred2r; rred2r.
      iApply wpsim_tauL; iApply wpsim_tauR. lred2r; rred2r. iApply wpsim_tauR.
      do 2 rewrite unfold_iter_eq. lred2r. rred2r.
      iApply (wpsim_yieldR_gen with "[DUTY2 PC2]"). instantiate (1:=1+n). auto. iFrame.
      { iApply pcs_cons_fold; iFrame. }
      iIntros "DUTY2 _". iModIntro. rred2r.
      iClear "OBL1 PRM1". clear tid1 γ1 γ1' k1.
      iInv "INV" as "CI" "CI_CLOSE".
      iEval (unfold client04Inv; red_tl_all; simpl; red_tl) in "CI".
      iDestruct "CI" as "[%tid1 CI]". iEval (red_tl) in "CI".
      iDestruct "CI" as "[%tid2' CI]". iEval (red_tl) in "CI".
      iDestruct "CI" as "[%γ1 CI]". iEval (red_tl) in "CI".
      iDestruct "CI" as "[%γ2' CI]". iEval (red_tl) in "CI".
      iDestruct "CI" as "[%k1 CI]". iEval (red_tl) in "CI".
      iDestruct "CI" as "[%k2' CI]". iEval (red_tl_all; simpl) in "CI".
      iDestruct "CI" as "(BS1 & BS2 & BM1 & BM2 & [H0 | [_ [H1 | H2]]])".
      { iDestruct "H0" as "(_ & LIVE & _)". iExFalso; iApply (Lifetime.pending_not_shot with "LIVE"). done. }
      2:{ iDestruct "H2" as "(PTX & _ & LIVE1 & WS2' & DUTY2' & _)".
        iExFalso; iApply (AuthExcls.w_w_false with "WS2 WS2'").
      }
      iDestruct "H1" as "(PTX & _ & LIVE2 & WS1 & DUTY1 & [(_ & _ & WS2') | WM2])".
      { iExFalso; iApply (AuthExcls.w_w_false with "WS2 WS2'"). }
      iPoseProof (AuthExcls.b_w_eq with "BS2 WS2") as "%EQ". clarify.
      iApply (SCMem_store_fun_spec with "[PTX] [-]"). instantiate (1:=n). auto.
      { pose proof mask_disjoint_N_Client04_state_tgt; set_solver. }
      { iFrame. done. }
      iIntros (rv') "PTX". rred2r. iApply wpsim_tauR. rred2r.
      iMod (Lifetime.pending_shot with "LIVE2") as "#DEAD2".
      iMod (duty_fulfill (v:=1+n) with "[DUTY2]") as "DUTY2". iFrame. simpl; red_tl_lifetime; done.
      iMod (Lifetime.alloc tt) as "[%γ1' LIVE1]".
      iMod (alloc_obligation 2 2) as "[%obl1 [#OBL1 PC1]]".
      iPoseProof (pc_split _ _ 1 1 with "[PC1]") as "[PC11 PC12]". done.
      iMod (pc_drop _ 1 _ _ 1 with "PC11") as "PC11"; auto.
      iMod (duty_add (v:=1+n) with "[DUTY1 PC11] []") as "DUTY1". iFrame.
      { instantiate (1 := (dead γ1' tt)%S). iEval (simpl; red_tl_all).
        iModIntro. iIntros "#D". iModIntro. done.
      }
      iPoseProof (duty_tpromise with "[DUTY1]") as "#PRM1". 2: done. simpl; left; auto.
      iMod (AuthExcls.b_w_update _ _ _ (tid2, obl1, γ1') with "BM2 WM2") as "[BM2 WM2]".
      iMod (AuthExcls.b_w_update _ _ _ (tid1, obl1, γ1') with "BS1 WS1") as "[BS1 WS1]".
      clear γ1 k1. rename γ1' into γ1. rename obl1 into k1.
      iMod ("CI_CLOSE" with "[- WM2]") as "_".
      { iEval (unfold client04Inv; simpl; red_tl).
        do 6 (iExists _; red_tl); red_tl_all. 
        iSplitL "BS1"; [done|]. iSplitL "BS2"; [done|]. iSplitL "BM1"; [done|]. iSplitL "BM2"; [done|].
        iRight. iSplitR; [done | ]. iRight. simpl. iFrame. iSplitR; [done | ]. iLeft. iFrame.
      }
      iApply wpsim_reset. iApply wpsim_base. auto.
      iApply "CIH". instantiate (1:=(k1, γ1)). iSplitR; iFrame. iModIntro; iFrame.
      iSplit; [done|]. iSplit; [done|]. iSplit; [done|]. iSplit; [done|]. iSplit; [done | ]. iSplit; done.
    }
  Unshelve. all: auto.
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

    Lemma init_sat E (H_TID : tid1 <> tid2) :
      (OwnM (memory_init_resource Client04.gvs))
        ∗ (AuthExcls.rest_gt (0, 0, 0))
        ∗
        (WSim.initial_prop
           Client04Spec.module Client04.module
           (Vars:=@sProp STT Γ) (Σ:=Σ)
           (STATESRC:=@SRA.in_subG Γ Σ sub _ _STATESRC)
           (STATETGT:=@SRA.in_subG Γ Σ sub _ _STATETGT)
           (IDENTSRC:=@SRA.in_subG Γ Σ sub _ _IDENTSRC)
           (IDENTTGT:=@SRA.in_subG Γ Σ sub _ _IDENTTGT)
           (ARROWRA:=@_ARROWRA STT Γ Σ TLRAS)
           (1+idx) init_ths init_ord)
        ⊢
        =| 2+idx |=(⟦syn_fairI (2+idx), 2+idx⟧)={ E, E }=>
            (∃ γi γi1 γi2 γs1 γs2 γm1 γm2 k1 k2 γ1 γ2,
                (inv (1+idx) N_Client04 (client04Inv idx γi γi1 γi2 γs1 γs2 γm1 γm2))
                  ∗ (⟦syn_tgt_interp_as idx sndl (fun m => (s_memory_black m)), 1+idx⟧)
                  ∗ ((own_thread tid1) ∗ (live γi1 tt 1) ∗ ○ γm1 (tid1, k2, γ2))
                  ∗ ((own_thread tid2) ∗ (live γi2 tt 1) ∗ ○ γm2 (tid2, k1, γ1))
            ).
    Proof.
      iIntros "(MEM & REST & INIT)". rewrite red_syn_fairI.
      iPoseProof (memory_init_iprop with "MEM") as "[MEM PTS]".

      iMod (Lifetime.alloc tt) as "[%γi LIVEI]".
      iMod (Lifetime.alloc tt) as "[%γi1 LIVEI1]".
      iMod (Lifetime.alloc tt) as "[%γi2 LIVEI2]".
      (* iAssert (OwnM ((fun k => Auth.frag (Excl.unit : Excl.t (nat * nat * nat))) : AuthExcls.t _))%I as "H".
      { 
      } *)
      iMod (AuthExcls.alloc_gt _ (tid1, 0, 0) with "REST") as "[REST (%γs1 & BS1 & WS1)]".
      iMod (AuthExcls.alloc_gt _ (tid2, 0, 0) with "REST") as "[REST (%γs2 & BS2 & WS2)]".
      iMod (AuthExcls.alloc_gt _ (tid1, 0, 0) with "REST") as "[REST (%γm1 & BM1 & WM1)]".
      iMod (AuthExcls.alloc_gt _ (tid2, 0, 0) with "REST") as "[REST (%γm2 & BM2 & WM2)]".

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

      iMod (tgt_interp_as_id _ _ (n:=idx) with "[INIT5 MEM]") as "TGT_ST".
      auto. lia.
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

      iMod (FUpd_alloc _ _ _ (1+idx) N_Client04 (client04Inv idx γi γi1 γi2 γs1 γs2 γm1 γm2)
        with "[PTS LIVEI BS1 WS1 BS2 WS2 BM1 BM2 DU1 DU2]") as "INV1".
      lia.
      Local Transparent X.
      { simpl. unfold SCMem.init_gvars, gvs. ss. des_ifs. iDestruct "PTS" as "((PT & _) & _)".
        unfold client04Inv. red_tl_all.
        iExists tid1; red_tl; iExists tid2; red_tl; do 4 (iExists 0; red_tl). simpl; red_tl_all.
        iSplitL "BS1"; [done | ]. iSplitL "BS2"; [done | ]. iSplitL "BM1"; [done | ]. iSplitL "BM2"; [done | ].
        iLeft. iFrame.
        Local Transparent SCMem.alloc.
        unfold SCMem.alloc in Heq0. ss. des_ifs.
        Local Opaque SCMem.alloc.
      }
      iModIntro. iExists γi, γi1, γi2, γs1, γs2, γm1, γm2. rewrite red_syn_tgt_interp_as. iFrame.
      iExists 0, 0, 0, 0. iFrame.
    Qed.

  End INITIAL.

End SPEC.