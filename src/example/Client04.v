From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Import pind Axioms ITreeLib Red TRed IRed2 WFLibLarge.
From Fairness Require Import FairBeh Mod Concurrency Linking.
From Fairness Require Import PCM IPM IPropAux.
From Fairness Require Import IndexedInvariants OpticsInterp SimWeakest SimWeakestAdequacy.
From Fairness Require Import TemporalLogic SCMemSpec OneShotsRA AuthExclsRA.

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
  Context {HasOneShotsNat : @GRA.inG (OneShots.t nat) Γ}.
  Context {HasAuthExclsNat3 : @GRA.inG (AuthExcls.t (nat * nat * nat)) Γ}.
  (* Context {HasAuthExclsNat : @GRA.inG (AuthExcls.t nat) Γ}. *)

  Ltac red_tl_all := red_tl; red_tl_memra; red_tl_oneshots; red_tl_authexcls.

  (** Invariants. *)

  (* Namespace for Client01 invariants. *)
  Definition N_Client04 : namespace := (nroot .@ "Client04").

  Lemma mask_disjoint_N_Client04_state_tgt : (↑N_Client04 : coPset) ## (↑N_state_tgt : coPset).
  Proof. apply ndot_ne_disjoint. ss. Qed.

  Definition client04Inv n γi γi1 γi2 γm1 γm2 : sProp n :=
    (∃ (k1 k2 γ1 γ2 γ1' γ2' : τ{nat, n}),
      (-[k1](0)-⧖ ∃ (k2' : τ{nat, n}), ▿ γ1 k2')
      ∗ (-[k2](0)-⧖ ∃ (k1' : τ{nat, n}), ▿ γ2 k1')
      ∗ ◆[k1, 1] ∗ ◆[k2, 1]
      ∗ △ γ1 (1/2) ∗ △ γ2 (1/2)
      ∗ ((X ↦ 0
          ∗ ●G γm1 (k1, γ1, γ2) ∗ ●G γm2 (k2, γ2, γ1)
          ∗ △ γi 1
          ∗ ⧖ [k1, (1/2)] ∗ ⧖ [k2, (1/2)])
        ∨
        (▿ γi 0)
          ∗ (((X ↦ 1)
              ∗ ●G γm1 (k1, γ1, γ2) ∗ ●G γm2 (k2, γ2, γ1')
              ∗ (∃ (k2 : τ{nat, n}), ▿ γi1 k2) ∗ (▿ γ1' k2) ∗ (⧖ [k1, (1/2)]) ∗ (⋈ [k2]))
            ∨ ((X ↦ 2)
              ∗ ●G γm1 (k1, γ1, γ2') ∗ ●G γm2 (k2, γ2, γ1)
              ∗ (∃ (k1 : τ{nat, n}), ▿ γi2 k1) ∗ (▿ γ2' k1) ∗ (⧖ [k2, (1/2)]) ∗ (⋈ [k1]))
            )
        )
    )%S.


    Lemma client04Inv_unfold n γi γi1 γi2 γm1 γm2 :
      ⟦client04Inv n γi γi1 γi2 γm1 γm2,n⟧ -∗
      ∃ k1 k2 γ1 γ2 γ1' γ2',
        (-[k1](0)-⧖ (∃ (k2' : τ{nat, n}), ▿ γ1 k2')%S)
        ∗ (-[k2](0)-⧖ (∃ (k1' : τ{nat, n}), ▿ γ2 k1')%S)
        ∗ ◆[k1, 1] ∗ ◆[k2, 1]
        ∗ △ γ1 (1/2) ∗ △ γ2 (1/2)
        ∗ ((X ↦ 0
            ∗ ●G γm1 (k1, γ1, γ2) ∗ ●G γm2 (k2, γ2, γ1)
            ∗ △ γi 1
            ∗ ⧖ [k1, (1/2)] ∗ ⧖ [k2, (1/2)])
          ∨
          (▿ γi 0)
            ∗ (((X ↦ 1)
                ∗ ●G γm1 (k1, γ1, γ2) ∗ ●G γm2 (k2, γ2, γ1')
                ∗ (∃ (k2 : τ{nat, n}), ▿ γi1 k2) ∗ (▿ γ1' k2) ∗ (⧖ [k1, (1/2)]) ∗ (⋈ [k2]))
              ∨ ((X ↦ 2)
                ∗ ●G γm1 (k1, γ1, γ2') ∗ ●G γm2 (k2, γ2, γ1)
                ∗ (∃ (k1 : τ{nat, n}), ▿ γi2 k1) ∗ (▿ γ2' k1) ∗ (⧖ [k2, (1/2)]) ∗ (⋈ [k1]))
              )
          ).
    Proof.
      iIntros "CI".
      iEval (unfold client04Inv; red_tl_all; simpl; red_tl) in "CI".
      iDestruct "CI" as "[%k1'' CI]". iEval (red_tl) in "CI".
      iDestruct "CI" as "[%k2'' CI]". iEval (red_tl) in "CI".
      iDestruct "CI" as "[%γ1'' CI]". iEval (red_tl) in "CI".
      iDestruct "CI" as "[%γ2'' CI]". iEval (red_tl) in "CI".
      iDestruct "CI" as "[%γ1''' CI]". iEval (red_tl) in "CI".
      iDestruct "CI" as "[%γ2''' CI]". iEval (red_tl_all; simpl) in "CI".
      iExists _,_,_,_,_,_.
      iDestruct "CI" as
        "($ & $ & $ & $ & $ & $ & [?|CI])".
      - iLeft. iFrame.
      - iRight. iDestruct "CI" as "($ & [CI|CI])".
        + iLeft. iDestruct "CI" as "($ & $ & $ & CI & $)".
          iDestruct "CI" as (?) "H". red_tl_all. iExists _. iFrame.
        + iRight. iDestruct "CI" as "($ & $ & $ & CI & $)".
          iDestruct "CI" as (?) "H". red_tl_all. iExists _. iFrame.
    Qed.

    Lemma client04Inv_fold n γi γi1 γi2 γm1 γm2 k1 k2 γ1 γ2 γ1' γ2' :
      ((-[k1](0)-⧖ (∃ (k2' : τ{nat, n}), ▿ γ1 k2')%S)
      ∗ (-[k2](0)-⧖ (∃ (k1' : τ{nat, n}), ▿ γ2 k1')%S)
      ∗ ◆[k1, 1] ∗ ◆[k2, 1]
      ∗ △ γ1 (1/2) ∗ △ γ2 (1/2)
      ∗ ((X ↦ 0
          ∗ ●G γm1 (k1, γ1, γ2) ∗ ●G γm2 (k2, γ2, γ1)
          ∗ △ γi 1
          ∗ ⧖ [k1, (1/2)] ∗ ⧖ [k2, (1/2)])
        ∨
        (▿ γi 0)
          ∗ (((X ↦ 1)
              ∗ ●G γm1 (k1, γ1, γ2) ∗ ●G γm2 (k2, γ2, γ1')
              ∗ (∃ (k2 : τ{nat, n}), ▿ γi1 k2) ∗ (▿ γ1' k2) ∗ (⧖ [k1, (1/2)]) ∗ (⋈ [k2]))
            ∨ ((X ↦ 2)
              ∗ ●G γm1 (k1, γ1, γ2') ∗ ●G γm2 (k2, γ2, γ1)
              ∗ (∃ (k1 : τ{nat, n}), ▿ γi2 k1) ∗ (▿ γ2' k1) ∗ (⧖ [k2, (1/2)]) ∗ (⋈ [k1]))
            )
        )) -∗ ⟦client04Inv n γi γi1 γi2 γm1 γm2,n⟧.
    Proof.
      iIntros "CI". unfold client04Inv.
      do 6 (red_tl;iExists _). red_tl_all.
      iDestruct "CI" as "($ & $ & $ & $ & $ & $ & [?|CI])".
      - iLeft. iFrame.
      - iRight. iDestruct "CI" as "($ & [CI|CI])".
        + iLeft. iDestruct "CI" as "($ & $ & $ & CI & $)".
          iDestruct "CI" as (?) "H". iExists _. red_tl_all. iFrame.
        + iRight. iDestruct "CI" as "($ & $ & $ & CI & $)".
          iDestruct "CI" as (?) "H". iExists _. red_tl_all. iFrame.
    Qed.

  (* Definition client04Inv n γi γi1 γi2 γs1 γs2 γm1 γm2 : sProp (1+n) :=
    (∃ (tid1 tid2 γ1 γ2 k1 k2 : τ{nat, 1+n}),
      (⤉ ●G γs1 (tid1, k1, γ1))
      ∗ (⤉ ●G γs2 (tid2, k2, γ2))
      ∗ (⤉ ●G γm1 (tid1, k2, γ2))
      ∗ (⤉ ●G γm2 (tid2, k1, γ1))
      ∗ (((⤉ (X ↦ 0))
          ∗ (⤉ live γi tt 1)
          ∗ (Duty (tid1) []) ∗ (Duty (tid2) [])
          ∗ (⤉ ○G γs1 (tid1, k1, γ1)) ∗ (⤉ ○G γs2 (tid2, k2, γ2)))
        ∨
        ((⤉ dead γi tt)
          ∗
          ((⤉ (X ↦ 1))
            ∗ (⤉ dead γi1 tt)
            ∗ (⤉ live γ2 tt 1)
            ∗ (⤉ (○G γs1 (tid1, k1, γ1)))
            ∗ (Duty (tid1) [])
            ∗ (((Duty (tid2) [(k2, 0, dead γ2 tt : sProp (1+n))])
                ∗ (◇[k2](2, 1))
                ∗ (⤉ (○G γs2 (tid2, k2, γ2))))
              ∨ (⤉ (○G γm2 (tid2, k1, γ1))))
          ∨
          ((⤉ (X ↦ 2))
            ∗ (⤉ dead γi2 tt)
            ∗ (⤉ live γ1 tt 1)
            ∗ (⤉ ○G γs2 (tid2, k2, γ2))
            ∗ (Duty (tid2) [])
            ∗ (((Duty (tid1) [(k1, 0, dead γ1 tt : sProp (1+n))])
                ∗ (◇[k1](2, 1))
                ∗ (⤉ ○G γs1 (tid1, k1, γ1)))
              ∨ (⤉ (○G γm1 (tid1, k2, γ2)))))))))%S. *)

  (** Simulation proof. *)
  Lemma Client04_load_loop_spec1
        tid n
  :
  ⊢ ∀ (γi γi1 γi2 γm1 γm2 k1 γ1 γ2 k2 k2' : τ{nat, 1+n}),
    [@ tid, n, ⊤ @]
      ⧼⟦((⤉ syn_inv n N_Client04 (client04Inv n γi γi1 γi2 γm1 γm2))
        ∗ (syn_tgt_interp_as n sndl (fun m => s_memory_black m))
        ∗ (⤉ ○G γm1 (k1, γ1, γ2))
        ∗ (⤉ Duty(tid)[(k1, 0, ∃ (k2' : τ{nat, n}), ▿ γ1 k2')])
        ∗ (⤉ ▿ γi 0)
        ∗ (⤉ ▿ γi1 k2')
        ∗ (⤉ ◆[k2, 1])
        ∗ (⤉ ◇[k1](1, 2))
        ∗ (⤉ -[k2](0)-◇ ∃ (k1' : τ{nat, n}), ▿ γ2 k1'))%S, 1+n⟧⧽
        (OMod.close_itree omod (SCMem.mod gvs) (load_loop 1))
        ⧼rv, ⌜rv = 2⌝
          ∗ ⟦((⤉ Duty(tid)[(k1, 0, ∃ (k2' : τ{nat, n}), ▿ γ1 k2')])
            ∗ (⤉ ▿ γ2 k1)
            ∗ (⤉ ⋈ [k1])
            ∗ (⤉ ○G γm1 (k1, γ1, γ2)))%S, 1+n⟧⧽
  .
  Proof.
    iIntros. iStartTriple. simpl. red_tl_all; simpl. rewrite red_syn_inv; rewrite red_syn_tgt_interp_as.
    iIntros "(#INV & #MEM & WM1 & DUTY & #DEADI & #DEADI1 & #OBL2 & PC & #PRM2)". iIntros "POST".
    (* Induction point *)
    iRevert "WM1 PC DUTY POST".
    iMod (tpromise_ind2 with "[] [-]") as "IH"; cycle 2. iApply "IH". iFrame "#".
    iSplit.
    { (* Inductive case *)
      iModIntro. iIntros "IH". iModIntro.
      iIntros "WM1 PC DUTY POST". iEval (unfold load_loop at 1; rewrite -> unfold_iter_eq). rred2r.
      iInv "INV" as "CI" "CI_CLOSE".
      iDestruct (client04Inv_unfold with "CI") as
        (k1'' k2'' γ1'' γ2'' γ1''' γ2''') "(#DPRM1 & #DPRM2 & #OBL1 & #OBL2' & LIVE1 & LIVE2 &
          [(_ & _ & _ & LIVE & _) | [_ [(PTX & BM1 & BM2 & _ & #DEAD1 & PO & #AO2) | H]]])".
      { iExFalso. iApply (OneShots.pending_not_shot with "LIVE DEADI"). }
      { iPoseProof (AuthExcls.b_w_eq with "BM1 WM1") as "%EQ"; des; clarify.
        iApply (wpsim_yieldR_gen_pending with "DUTY [PO]"). auto.
        { instantiate (1:=nil). rewrite app_nil_r. auto. }
        3:{ iApply (pps_cons_fold with "[PO]"). iSplitL; [done | iApply pps_nil]. }
        auto. auto. auto.
        iIntros "DUTY CRED PO _". iMod ("IH" with "CRED") as "IH".
        iMod ("CI_CLOSE" with "[- WM1 PC POST DUTY IH]") as "_".
        { iApply client04Inv_fold.
          iSplitR; [iApply "DPRM1"|]. iSplitR; [iApply "DPRM2"|]. iSplitR; [done|]. iSplitR; [done|].
          iSplitL "LIVE1"; [done|]. iSplitL "LIVE2"; [done|].
          iRight. iSplitR; [done |]. iLeft. iFrame. iSplitR. iExists k2'; red_tl_all; auto. iSplitR; auto.
          iSplitL. iPoseProof (pps_cons_unfold with "PO") as "[PO _]". done. done.
        }
        iModIntro. rred2r. iClear "DPRM1 DPRM2 OBL1 OBL2' DEAD1 AO2". clear k2'' γ1''' γ2'''.
        iInv "INV" as "CI" "CI_CLOSE".
        iDestruct (client04Inv_unfold with "CI") as
          (k1'' k2'' γ1'' γ2'' γ1''' γ2''') "(#DPRM1 & #DPRM2 & #OBL1 & #OBL2' & LIVE1 & LIVE2 &
            [(_ & _ & _ & LIVE & _) | [_ [(PTX & BM1 & BM2 & _ & #DEAD1 & PO & #AO2) | (PTX & REST)]]])".
        { iExFalso. iApply (OneShots.pending_not_shot with "LIVE DEADI"). }
        { iApply (SCMem_load_fun_spec with "[PTX]"). auto.
          { pose proof mask_disjoint_N_Client04_state_tgt. set_solver. }
          { iFrame. done. }
          iIntros (rv) "[%EQ PTX]"; clarify. rred2r. iApply wpsim_tauR. rred2r.
          iPoseProof (AuthExcls.b_w_eq with "BM1 WM1") as "%EQ"; des; clarify.
          iApply (wpsim_yieldR_gen_pending with "DUTY [PO]"). auto.
          { instantiate (1:=nil). rewrite app_nil_r. auto. }
          3:{ iApply (pps_cons_fold with "[PO]"). iSplitL; [done | iApply pps_nil]. }
          auto. auto. auto.
          iIntros "DUTY _ PPS _". iPoseProof (pps_cons_unfold with "PPS") as "[PO _]".
          iMod ("CI_CLOSE" with "[- WM1 PC POST DUTY IH]") as "_".
          { iApply client04Inv_fold.
            iSplitR; [iApply "DPRM1"|]. iSplitR; [iApply "DPRM2"|]. iSplitR; [done|]. iSplitR; [done|].
            iSplitL "LIVE1"; [done|]. iSplitL "LIVE2"; [done|].
            iRight. iSplitR; [done |]. iLeft. iFrame. repeat iSplit; auto.
          }
          iModIntro. rred2r.
          iApply SCMem_compare_fun_spec. instantiate (1:=n). auto. set_solver.
          { simpl. des_ifs. iApply (tgt_interp_as_equiv with "MEM"). iIntros. iSplit.
            { iIntros. simpl. red_tl; simpl. iSplit; [done | iPureIntro; auto]. }
            { simpl. red_tl; simpl. iIntros "[? _]". done. }
          }
          iIntros (rv) "[%EQ _]". exploit EQ. auto. i; subst. rred2r.
          iApply wpsim_tauR. rred2r. iApply wpsim_tauR.
          fold (load_loop 1). iApply wpsim_stutter_mon. instantiate (1:=ps); auto. instantiate (1:=pt); auto.
          iApply ("IH" with "WM1 PC DUTY POST").
        }
        { iDestruct "REST" as "(BM1 & BM2 & DEADI2 & #DEAD2 & PO2 & #AO1)".
          iPoseProof (AuthExcls.b_w_eq with "BM1 WM1") as "%EQ"; des; clarify.
          iApply (SCMem_load_fun_spec with "[PTX]"). auto.
          { pose proof mask_disjoint_N_Client04_state_tgt. set_solver. }
          { iFrame. done. }
          iIntros (rv) "[%EQ PTX]"; clarify. rred2r. iApply wpsim_tauR. rred2r.
          iMod ("CI_CLOSE" with "[- WM1 PC POST DUTY]") as "_".
          { iApply client04Inv_fold.
            iSplitR; [iApply "DPRM1"|]. iSplitR; [iApply "DPRM2"|]. iSplitR; [done|]. iSplitR; [done|].
            iSplitL "LIVE1"; [done|]. iSplitL "LIVE2"; [done|].
            iRight. iSplitR; [done |]. iRight. iFrame "# PTX DEADI2 BM1 BM2 PO2".
          }
          iPoseProof (pc_split _ _ 1 with "PC") as "[PC' PC]".
          iApply (wpsim_yieldR with "[DUTY PC']"). auto. iFrame. iApply (pcs_cons_fold with "[PC']"). iFrame.
          iIntros "DUTY _". rred2r.
          iApply SCMem_compare_fun_spec. instantiate (1:=n). auto. set_solver.
          { simpl. des_ifs. iApply (tgt_interp_as_equiv with "MEM"). iIntros. iSplit.
            { iIntros. simpl. red_tl; simpl. iSplit; [done | iPureIntro; auto]. }
            { simpl. red_tl; simpl. iIntros "[? _]". done. }
          }
          iIntros (rv) "[_ %NEQ]". exploit NEQ. auto. i; subst. rred2r.
          iApply wpsim_tauR. rred2r. iApply ("POST" with "[DUTY WM1]"). iSplitR; [done|]. iFrame "#∗".
        }
      }
      { iDestruct "H" as "(PTX & BM1 & BM2 & DEADI2 & #DEAD2 & PO2 & #AO1)".
        iPoseProof (AuthExcls.b_w_eq with "BM1 WM1") as "%EQ"; des; clarify.
        iMod ("CI_CLOSE" with "[- WM1 PC POST DUTY]") as "_".
        { iApply client04Inv_fold.
          iSplitR; [iApply "DPRM1"|]. iSplitR; [iApply "DPRM2"|]. iSplitR; [done|]. iSplitR; [done|].
          iSplitL "LIVE1"; [done|]. iSplitL "LIVE2"; [done|].
          iRight. iSplitR; [done |]. iRight. iFrame "#∗".
        }
        iPoseProof (pc_split _ _ 1 with "PC") as "[PC' PC]".
        iApply (wpsim_yieldR with "[DUTY PC']"). auto. iFrame. iApply (pcs_cons_fold with "[PC']"). iFrame.
        iIntros "DUTY _". rred2r.
        iClear "DPRM1 DPRM2 OBL1 OBL2'". clear k2'' γ1''' γ2''.
        iInv "INV" as "CI" "CI_CLOSE".
        iDestruct (client04Inv_unfold with "CI") as
          (k1'' k2'' γ1'' γ2'' γ1''' γ2''') "(#DPRM1 & #DPRM2 & #OBL1 & #OBL2' & LIVE1 & LIVE2 &
            [(_ & _ & _ & LIVE & _) | [_ [(_ & BM1 & _ & _ & _ & PO & _) | (PTX & REST)]]])".
        { iExFalso. iApply (OneShots.pending_not_shot with "LIVE DEADI"). }
        { iExFalso. iPoseProof (AuthExcls.b_w_eq with "BM1 WM1") as "%EQ"; des; clarify.
          iApply (pending_not_active with "PO AO1").
        }
        { iApply (SCMem_load_fun_spec with "[PTX]"). auto.
          { pose proof mask_disjoint_N_Client04_state_tgt. set_solver. }
          { iFrame. done. }
          iIntros (rv) "[%EQ PTX]"; clarify. rred2r. iApply wpsim_tauR. rred2r.
          iMod ("CI_CLOSE" with "[- WM1 PC POST DUTY]") as "_".
          { iApply client04Inv_fold.
            iSplitR; [iApply "DPRM1"|]. iSplitR; [iApply "DPRM2"|]. iSplitR; [done|]. iSplitR; [done|].
            iSplitL "LIVE1"; [done|]. iSplitL "LIVE2"; [done|].
            iRight. iSplitR; [done |]. iRight. iFrame "#∗".
          }
          iApply (wpsim_yieldR with "[DUTY PC]"). auto. iFrame. iApply (pcs_cons_fold with "[PC]"). iFrame.
          iIntros "DUTY _". rred2r.
          iApply SCMem_compare_fun_spec. instantiate (1:=n). auto. set_solver.
          { simpl. des_ifs. iApply (tgt_interp_as_equiv with "MEM"). iIntros. iSplit.
            { iIntros. simpl. red_tl; simpl. iSplit; [done | iPureIntro; auto]. }
            { simpl. red_tl; simpl. iIntros "[? _]". done. }
          }
          iIntros (rv) "[_ %NEQ]". exploit NEQ. auto. i; subst. rred2r.
          iApply wpsim_tauR. rred2r. iApply ("POST" with "[DUTY WM1]"). iSplitR; [done|]. iFrame "#∗".
        }
      }
    }
    { (* Base case *)
      iModIntro. iIntros "#DEAD2".
      iEval (simpl; red_tl) in "DEAD2". iDestruct "DEAD2" as (k1') "DEAD2". iEval (red_tl_all) in "DEAD2".
      iModIntro. iIntros "WM1 PC DUTY POST".
      iEval (unfold load_loop at 1; rewrite -> unfold_iter_eq). rred2r.
      iInv "INV" as "CI" "CI_CLOSE".
      iDestruct (client04Inv_unfold with "CI") as
        (k1'' k2'' γ1'' γ2'' γ1''' γ2''')
          "(#DPRM1 & #DPRM2 & #OBL1 & #OBL2' & LIVE1 & LIVE2 &
            [(_ & _ & _ & LIVE & _) | [_ [(PTX & BM1 & BM2 & _ & #DEAD1 & PO & #AO2) | H]]])".
      { iExFalso. iApply (OneShots.pending_not_shot with "LIVE DEADI"). }
      { iExFalso. iPoseProof (AuthExcls.b_w_eq with "BM1 WM1") as "%EQ"; des; clarify.
        iApply (OneShots.pending_not_shot with "LIVE2 DEAD2"). }
      { iDestruct "H" as "(PTX & BM1 & BM2 & DEADI2 & #DEAD2' & PO2 & #AO1)".
        iPoseProof (AuthExcls.b_w_eq with "BM1 WM1") as "%EQ"; des; clarify.
        iMod ("CI_CLOSE" with "[- WM1 PC POST DUTY]") as "_".
        { iApply client04Inv_fold.
          iSplitR; [iApply "DPRM1"|]. iSplitR; [iApply "DPRM2"|]. iSplitR; [done|]. iSplitR; [done|].
          iSplitL "LIVE1"; [done|]. iSplitL "LIVE2"; [done|].
          iRight. iSplitR; [done |]. iRight. iFrame "#∗".
        }
        iClear "DEAD2 DPRM1 DPRM2 OBL1 OBL2'". iRename "DEAD2'" into "DEAD2". clear k2'' γ1''' γ2''.
        iPoseProof (pc_split _ _ 1 with "PC") as "[PC' PC]".
        iApply (wpsim_yieldR with "[DUTY PC']"). auto. iFrame. iApply (pcs_cons_fold with "[PC']"). iFrame.
        iIntros "DUTY _". rred2r.
        iInv "INV" as "CI" "CI_CLOSE".
        iDestruct (client04Inv_unfold with "CI") as
        (k1'' k2'' γ1'' γ2'' γ1''' γ2''')
          "(#DPRM1 & #DPRM2 & #OBL1 & #OBL2' & LIVE1 & LIVE2 &
            [(_ & _ & _ & LIVE & _) | [_ [(PTX & BM1 & BM2 & _ & #DEAD1 & PO & #AO2) | (PTX & REST)]]])".
        { iExFalso. iApply (OneShots.pending_not_shot with "LIVE DEADI"). }
        { iExFalso. iPoseProof (AuthExcls.b_w_eq with "BM1 WM1") as "%EQ"; des; clarify.
          iApply (pending_not_active with "PO AO1").
        }
        { iApply (SCMem_load_fun_spec with "[PTX]"). auto.
          { pose proof mask_disjoint_N_Client04_state_tgt. set_solver. }
          { iFrame. done. }
          iIntros (rv) "[%EQ PTX]"; clarify. rred2r. iApply wpsim_tauR. rred2r.
          iMod ("CI_CLOSE" with "[- WM1 PC POST DUTY]") as "_".
          { iApply client04Inv_fold.
            iSplitR; [iApply "DPRM1"|]. iSplitR; [iApply "DPRM2"|]. iSplitR; [done|]. iSplitR; [done|].
            iSplitL "LIVE1"; [done|]. iSplitL "LIVE2"; [done|].
            iRight. iSplitR; [done |]. iRight. iFrame.
          }
          iApply (wpsim_yieldR with "[DUTY PC]"). auto. iFrame. iApply (pcs_cons_fold with "[PC]"). iFrame.
          iIntros "DUTY _". rred2r.
          iApply SCMem_compare_fun_spec. instantiate (1:=n). auto. set_solver.
          { simpl. des_ifs. iApply (tgt_interp_as_equiv with "MEM"). iIntros. iSplit.
            { iIntros. simpl. red_tl; simpl. iSplit; [done | iPureIntro; auto]. }
            { simpl. red_tl; simpl. iIntros "[? _]". done. }
          }
          iIntros (rv) "[_ %NEQ]". exploit NEQ. auto. i; subst. rred2r.
          iApply wpsim_tauR. rred2r. iApply ("POST" with "[DUTY WM1]"). iSplitR; [done|]. iFrame.
          iFrame "#".
        }
      }
    }
    Unshelve. all: auto.
  Qed.

  Lemma Client04_thread1_spec
        tid1 n
    :
    ⊢ ⟦(∀ (γi γi1 γi2 γm1 γm2 k1 γ1 : τ{nat, 1+n}),
           ((⤉ syn_inv n N_Client04 (client04Inv n γi γi1 γi2 γm1 γm2))
              ∗ (syn_tgt_interp_as n sndl (fun m => (s_memory_black m)))
              ∗ (⤉ Duty(tid1)[(k1, 0, ∃ (k2' : τ{nat, n}), ▿ γi1 k2')])
              ∗ (⤉ ○G γm1 (k1, γi1, γi2))
              ∗ (⤉ △ γi1 (1/2))
              ∗ ◇[k1](1, 1))
             -∗
             syn_wpsim (1+n) tid1 ⊤
             (fun rs rt => (⤉ (syn_term_cond n tid1 _ rs rt))%S)
             false false
             (fn2th Client04Spec.module "thread1" (tt ↑))
             (fn2th Client04.module "thread1" (tt ↑)))%S, 1+n⟧.
  Proof.
    iIntros. red_tl_all. iIntros (γi). red_tl_all. iIntros (γi1).
    red_tl_all. iIntros (γi2). red_tl_all. iIntros (γm1).
    red_tl_all. iIntros (γm2). red_tl_all. iIntros (k1).
    red_tl_all. iIntros (γ1). red_tl_all. simpl.
    iEval (rewrite red_syn_inv; rewrite red_syn_wpsim; rewrite red_syn_tgt_interp_as).

    iIntros "(#INV & #MEM & DUTY & WM & LIVEI1 & PC)".

    unfold fn2th. simpl. unfold thread1, Client04Spec.thread1.
    rred2r. lred2r.

    iEval (do 2 rewrite unfold_iter_eq). rred2r. lred2r.
    iApply (wpsim_yieldR_gen with "[DUTY PC]"). auto.
    { iSplitL "DUTY"; iFrame. iApply pcs_cons_fold. iSplitL; done. }
    iIntros "DUTY _". iModIntro. rred2r.

    iInv "INV" as "CI" "CI_CLOSE".
    iDestruct (client04Inv_unfold with "CI") as
      (k1' k2 γ1' γ2 γ1'' γ2')
      "(#DPRM1 & #DPRM2 & #OBL1 & #OBL2 & LIVE1 & LIVE2 &
        [(PTX & BM1 & BM2 & LIVEI & PO1 & PO2)
          | (#DEADI & [(PTX & BM1 & BM2 & DEADI1 & _) | (PTX & BM1 & BM2 & DEADI2 & DEAD2 & PO2 & #AO1)])])".
    { iPoseProof (AuthExcls.b_w_eq with "BM1 WM") as "%EQ". clarify.
      iApply (SCMem_store_fun_spec with "[PTX] [-]"). auto.
      { pose proof mask_disjoint_N_Client04_state_tgt; set_solver. }
      { iSplitR; auto. }
      iIntros (rv) "PTX". rred2r. iApply wpsim_tauR. rred2r. clear rv.
      iMod (OneShots.pending_shot _ 0 with "LIVEI") as "#DEADI".
      iPoseProof (OneShots.pending_merge _ (1/2) (1/2) with "LIVEI1 LIVE1") as "LIVEI1". rewrite Qp.half_half.
      iMod (OneShots.pending_shot _ k2 with "LIVEI1") as "#DEADI1".
      iMod (activate_tpromise with "DPRM2 PO2") as "[#PRM2 #AO2]".
      iMod (activate_tpromise with "DPRM1 PO1") as "[_ #AO1]".
      iMod (duty_fulfill with "[DUTY DEADI1]") as "DUTY".
      { iFrame. simpl; red_tl_all. iSplit. iExists k2; red_tl_all; done. done. }
      iClear "OBL1 DPRM1 AO1".
      iMod (alloc_obligation 1 5) as (k1') "(#OBL1 & PC & PO1)".
      iMod OneShots.alloc as "[%γ1' LIVE1]".
      iEval (rewrite <- Qp.half_half) in "LIVE1".
      iPoseProof (OneShots.pending_split _ (1/2) (1/2) with "LIVE1") as "[LIVE1 LIVE1']".
      iMod (AuthExcls.b_w_update _ _ _ (k1', γ1', γi2) with "BM1 WM") as "[BM1 WM]".
      iPoseProof (pending_split _ (1/2) (1/2) with "[PO1]") as "[PO1' PO1]". rewrite Qp.half_half. done.
      iPoseProof (pc_split _ _ 1 4 with "[PC]") as "[PC' PC]". done.
      iMod (duty_add (v:=n) with "[DUTY PO1' PC'] []") as "DUTY". iFrame.
      { instantiate (1 := (∃ (k2' : τ{nat, n}), ▿ γ1' k2')%S). iModIntro. simpl; red_tl_all.
        iIntros "[% D]". red_tl_all. iPoseProof "D" as "#D". iModIntro. iExists x; red_tl_all; done.
      }
      iPoseProof (duty_delayed_tpromise with "DUTY") as "#DPRM1". simpl; left; auto.
      iMod ("CI_CLOSE" with "[- WM PC DUTY LIVE1]") as "_".
      { iApply client04Inv_fold.
        iSplitR; [iApply "DPRM1"|]. iSplitR; [iApply "DPRM2"|]. iSplitR; [done|]. iSplitR; [done|].
        iSplitL "LIVE1'"; [done|]. iSplitL "LIVE2"; [done|].
        iRight. iSplitR; [done |]. iLeft. iFrame. iSplit; auto.
      }

      iClear "DPRM2 DPRM1 OBL1 AO2". clear k1 γ1 γ1'' γ2'. rename k1' into k1. rename γ1' into γ1.
      iApply wpsim_reset. iStopProof.
      pose (k1, γ1, γi2, k2) as p.
      replace k1 with (p.1.1.1) by ss. replace γ1 with (p.1.1.2) by ss.
      replace γi2 with (p.1.2) by ss. replace k2 with (p.2) by ss.
      assert (TEMP : p.1.2 = γi2) by ss; setoid_rewrite TEMP at 1; clear TEMP.
      assert (TEMP : p.2 = k2) by ss; setoid_rewrite TEMP at 2; clear TEMP.
      generalize p. clear p.
      eapply wpsim_coind. auto. clear k1 γ1.
      ii. destruct a as [[[k1 γ1] γ2] k2'].
      iIntros "[#HG1 #CIH] [(#INV & #MEM & #OBL2 & #DEADI & #DEADI1 & #PRM2) (WM & PC & DUTY & LIVE1)]". simpl.
      iPoseProof (pc_split _ _ 2 2 with "[PC]") as "[PC' PC]". done.
      iApply (Client04_load_loop_spec1 with "[WM DUTY PC'] [-]").
      { simpl. red_tl_all; simpl. rewrite red_syn_inv; rewrite red_syn_tgt_interp_as; red_tl_all.
        iFrame "#∗".
      }
      iIntros (rv') "(%EQ & POST)"; subst. iEval (simpl; red_tl_all; simpl) in "POST".
      iDestruct "POST" as "(DUTY & #DEAD2 & #AO1 & WM)". rred2r. iClear "OBL2".
      iPoseProof (pc_split _ _ 1 1 with "[PC]") as "[PC' PC]". done.
      iApply (wpsim_sync with "[DUTY PC']"). auto.
      { iFrame. iApply pcs_cons_fold. iFrame. }
      iIntros "DUTY _". rred2r. iApply wpsim_tauR. lred2r. rred2r.

      iApply wpsim_observe. iIntros (ret). lred2r. rred2r.
      iApply wpsim_tauL; iApply wpsim_tauR. rred2r. iApply wpsim_tauR.
      iEval (do 2 rewrite unfold_iter_eq). rred2r. lred2r.
      iApply (wpsim_yieldR with "[DUTY PC]"). auto.
      { iFrame. iApply pcs_cons_fold. iFrame. }
      iIntros "DUTY _". rred2r.

      iInv "INV" as "CI" "CI_CLOSE".
      iDestruct (client04Inv_unfold with "CI") as
        (k1' k2'' γ1' γ2' γ1'' γ2'')
        "(_ & #DPRM2 & _ & #OBL2 & LIVE1' & LIVE2 &
          [(_ & _ & _ & LIVEI & _)
            | (_ & [(PTX & BM1 & _ & _ & _ & PO1 & _) | (PTX & BM1 & BM2 & DEADI2 & _ & PO2 & _)])])".
      { iExFalso. iApply (OneShots.pending_not_shot with "LIVEI DEADI"). }
      { iPoseProof (AuthExcls.b_w_eq with "BM1 WM") as "%EQ". clarify.
        iExFalso. iApply (pending_not_active with "PO1"). done.
      }
      { iPoseProof (AuthExcls.b_w_eq with "BM1 WM") as "%EQ". clarify.
        iApply (SCMem_store_fun_spec with "[PTX] [-]"). auto.
        { pose proof mask_disjoint_N_Client04_state_tgt; set_solver. }
        { iSplitR; auto. }
        iIntros (rv) "PTX". rred2r. iApply wpsim_tauR. rred2r. clear rv.
        iPoseProof (OneShots.pending_merge _ (1/2) (1/2) with "LIVE1 LIVE1'") as "LIVE1". rewrite Qp.half_half.
        iMod (OneShots.pending_shot _ k2'' with "LIVE1") as "#DEAD1".
        iClear "PRM2". iMod (activate_tpromise with "DPRM2 PO2") as "[#PRM2 #AO2]".
        iMod (duty_fulfill with "[DUTY DEAD1]") as "DUTY".
        { iFrame. simpl; red_tl_all. iSplit. iExists k2''; red_tl_all; done. done. }
        iMod (alloc_obligation 1 5) as (k1') "(#OBL & PC & PO1)".
        iMod OneShots.alloc as "[%γ1' LIVE1]".
        iEval (rewrite <- Qp.half_half) in "LIVE1".
        iPoseProof (OneShots.pending_split _ (1/2) (1/2) with "LIVE1") as "[LIVE1 LIVE1']".
        iMod (AuthExcls.b_w_update _ _ _ (k1', γ1', γ2') with "BM1 WM") as "[BM1 WM]".
        iPoseProof (pending_split _ (1/2) (1/2) with "[PO1]") as "[PO1' PO1]". rewrite Qp.half_half. done.
        iPoseProof (pc_split _ _ 1 with "[PC]") as "[PC' PC]". done.
        iMod (duty_add (v:=n) with "[DUTY PO1' PC'] []") as "DUTY". iFrame.
        { instantiate (1 := (∃ (k2' : τ{nat, n}), ▿ γ1' k2')%S). iModIntro. simpl; red_tl_all.
          iIntros "[% D]". red_tl_all. iPoseProof "D" as "#D". iModIntro. iExists x; red_tl_all; done.
        }
        iPoseProof (duty_delayed_tpromise with "DUTY") as "#DPRM1". simpl; left; auto.
        iMod ("CI_CLOSE" with "[- WM PC DUTY LIVE1]") as "_".
        { iApply client04Inv_fold.
          iSplitR; [iApply "DPRM1"|]. iSplitR; [iApply "DPRM2"|]. iSplitR; [done|]. iSplitR; [done|].
          iSplitL "LIVE1'"; [done|]. iSplitL "LIVE2"; [done|].
          iRight. iSplitR; [done |]. iLeft. iFrame. iSplit; auto.
        }
        iApply wpsim_reset. iApply wpsim_base. auto. iApply ("CIH" $! (k1', γ1', γ2', k2'') with "[-]").
        iSplitR.
        { iModIntro. repeat iSplit; auto. }
        { simpl. iFrame. }
      }
    }
    { iDestruct "DEADI1" as (?) "DEADI1". iEval (red_tl_all; simpl) in "DEADI1".
      iExFalso. iPoseProof (AuthExcls.b_w_eq with "BM1 WM") as "%EQ". des; clarify.
      iApply (OneShots.pending_not_shot with "LIVEI1 DEADI1").
    }
    { iPoseProof (AuthExcls.b_w_eq with "BM1 WM") as "%EQ". clarify.
      iApply (SCMem_store_fun_spec with "[PTX] [-]"). auto.
      { pose proof mask_disjoint_N_Client04_state_tgt; set_solver. }
      { iSplitR; auto. }
      iIntros (rv) "PTX". rred2r. iApply wpsim_tauR. rred2r. clear rv.
      iPoseProof (OneShots.pending_merge _ (1/2) (1/2) with "LIVEI1 LIVE1") as "LIVEI1". rewrite Qp.half_half.
      iMod (OneShots.pending_shot _ k2 with "LIVEI1") as "#DEADI1".
      iMod (activate_tpromise with "DPRM2 PO2") as "[#PRM2 #AO2]".
      iMod (duty_fulfill with "[DUTY DEADI1]") as "DUTY".
      { iFrame. simpl; red_tl_all. iSplit. iExists k2; red_tl_all; done. done. }
      iClear "OBL1 DPRM1 AO1".
      iMod (alloc_obligation 1 5) as (k1') "(#OBL1 & PC & PO1)".
      iMod OneShots.alloc as "[%γ1' LIVE1]".
      iEval (rewrite <- Qp.half_half) in "LIVE1".
      iPoseProof (OneShots.pending_split _ (1/2) (1/2) with "LIVE1") as "[LIVE1 LIVE1']".
      iMod (AuthExcls.b_w_update _ _ _ (k1', γ1', γ2) with "BM1 WM") as "[BM1 WM]".
      iPoseProof (pending_split _ (1/2) (1/2) with "[PO1]") as "[PO1' PO1]". rewrite Qp.half_half. done.
      iPoseProof (pc_split _ _ 1 with "[PC]") as "[PC' PC]". done.
      iMod (duty_add (v:=n) with "[DUTY PO1' PC'] []") as "DUTY". iFrame.
      { instantiate (1 := (∃ (k2' : τ{nat, n}), ▿ γ1' k2')%S). iModIntro. simpl; red_tl_all.
        iIntros "[% D]". red_tl_all. iPoseProof "D" as "#D". iModIntro. iExists x; red_tl_all; done.
      }
      iPoseProof (duty_delayed_tpromise with "DUTY") as "#DPRM1". simpl; left; auto.
      iMod ("CI_CLOSE" with "[- WM PC DUTY LIVE1]") as "_".
      { iApply client04Inv_fold.
        iSplitR; [iApply "DPRM1"|]. iSplitR; [iApply "DPRM2"|]. iSplitR; [done|]. iSplitR; [done|].
        iSplitL "LIVE1'"; [done|]. iSplitL "LIVE2"; [done|].
        iRight. iSplitR; [done |]. iLeft. iFrame. iSplit; auto.
      }

      iClear "DPRM2 DPRM1 OBL1 AO2". clear k1 γ1 γ1''. rename k1' into k1. rename γ1' into γ1.
      iApply wpsim_reset. iStopProof.
      pose (k1, γ1, γ2, k2) as p.
      replace k1 with (p.1.1.1) by ss. replace γ1 with (p.1.1.2) by ss.
      replace γ2 with (p.1.2) by ss. replace k2 with (p.2) by ss.
      assert (TEMP : p.2 = k2) by ss; setoid_rewrite TEMP at 2; clear TEMP.
      generalize p. clear p.
      eapply wpsim_coind. auto. clear k1 γ1 γ2.
      ii. destruct a as [[[k1 γ1] γ2] k2'].
      iIntros "[#HG1 #CIH] [(#INV & #MEM & #OBL2 & #DEADI & #DEADI1 & #PRM2) (WM & PC & DUTY & LIVE1)]". simpl.
      iPoseProof (pc_split _ _ 2 2 with "[PC]") as "[PC' PC]". done.
      iApply (Client04_load_loop_spec1 with "[WM DUTY PC'] [-]").
      { simpl. red_tl_all; simpl. rewrite red_syn_inv; rewrite red_syn_tgt_interp_as; red_tl_all.
        iFrame "#∗".
      }
      iIntros (rv') "(%EQ & POST)"; subst. iEval (simpl; red_tl_all; simpl) in "POST".
      iDestruct "POST" as "(DUTY & #DEAD2 & #AO1 & WM)". rred2r. iClear "OBL2".
      iPoseProof (pc_split _ _ 1 1 with "[PC]") as "[PC' PC]". done.
      iApply (wpsim_sync with "[DUTY PC']"). auto.
      { iFrame. iApply pcs_cons_fold. iFrame. }
      iIntros "DUTY _". rred2r. iApply wpsim_tauR. lred2r. rred2r.

      iApply wpsim_observe. iIntros (ret). lred2r. rred2r.
      iApply wpsim_tauL; iApply wpsim_tauR. rred2r. iApply wpsim_tauR.
      iEval (do 2 rewrite unfold_iter_eq). rred2r. lred2r.
      iApply (wpsim_yieldR with "[DUTY PC]"). auto.
      { iFrame. iApply pcs_cons_fold. iFrame. }
      iIntros "DUTY _". rred2r.

      iInv "INV" as "CI" "CI_CLOSE".
      iDestruct (client04Inv_unfold with "CI") as
        (k1' k2'' γ1' γ2' γ1'' γ2'')
        "(_ & #DPRM2 & _ & #OBL2 & LIVE1' & LIVE2 &
          [(_ & _ & _ & LIVEI & _)
            | (_ & [(PTX & BM1 & _ & _ & _ & PO1 & _) | (PTX & BM1 & BM2 & DEADI2 & _ & PO2 & _)])])".
      { iExFalso. iApply (OneShots.pending_not_shot with "LIVEI DEADI"). }
      { iPoseProof (AuthExcls.b_w_eq with "BM1 WM") as "%EQ". clarify.
        iExFalso. iApply (pending_not_active with "PO1"). done.
      }
      { iPoseProof (AuthExcls.b_w_eq with "BM1 WM") as "%EQ". clarify.
        iApply (SCMem_store_fun_spec with "[PTX] [-]"). auto.
        { pose proof mask_disjoint_N_Client04_state_tgt; set_solver. }
        { iSplitR; auto. }
        iIntros (rv) "PTX". rred2r. iApply wpsim_tauR. rred2r. clear rv.
        iPoseProof (OneShots.pending_merge _ (1/2) (1/2) with "LIVE1 LIVE1'") as "LIVE1". rewrite Qp.half_half.
        iMod (OneShots.pending_shot _ k2'' with "LIVE1") as "#DEAD1".
        iClear "PRM2". iMod (activate_tpromise with "DPRM2 PO2") as "[#PRM2 #AO2]".
        iMod (duty_fulfill with "[DUTY DEAD1]") as "DUTY".
        { iFrame. simpl; red_tl_all. iSplit. iExists k2''; red_tl_all; done. done. }
        iMod (alloc_obligation 1 5) as (k1') "(#OBL & PC & PO1)".
        iMod OneShots.alloc as "[%γ1' LIVE1]".
        iEval (rewrite <- Qp.half_half) in "LIVE1".
        iPoseProof (OneShots.pending_split _ (1/2) (1/2) with "LIVE1") as "[LIVE1 LIVE1']".
        iMod (AuthExcls.b_w_update _ _ _ (k1', γ1', γ2') with "BM1 WM") as "[BM1 WM]".
        iPoseProof (pending_split _ (1/2) (1/2) with "[PO1]") as "[PO1' PO1]". rewrite Qp.half_half. done.
        iPoseProof (pc_split _ _ 1 with "[PC]") as "[PC' PC]". done.
        iMod (duty_add (v:=n) with "[DUTY PO1' PC'] []") as "DUTY". iFrame.
        { instantiate (1 := (∃ (k2' : τ{nat, n}), ▿ γ1' k2')%S). iModIntro. simpl; red_tl_all.
          iIntros "[% D]". red_tl_all. iPoseProof "D" as "#D". iModIntro. iExists x; red_tl_all; done.
        }
        iPoseProof (duty_delayed_tpromise with "DUTY") as "#DPRM1". simpl; left; auto.
        iMod ("CI_CLOSE" with "[- WM PC DUTY LIVE1]") as "_".
        { iApply client04Inv_fold.
          iSplitR; [iApply "DPRM1"|]. iSplitR; [iApply "DPRM2"|]. iSplitR; [done|]. iSplitR; [done|].
          iSplitL "LIVE1'"; [done|]. iSplitL "LIVE2"; [done|].
          iRight. iSplitR; [done |]. iLeft. iFrame. iSplit; auto.
        }
        iApply wpsim_reset. iApply wpsim_base. auto. iApply ("CIH" $! (k1', γ1', γ2', k2'') with "[-]").
        iSplitR.
        { iModIntro. repeat iSplit; auto. }
        { simpl. iFrame. }
      }
    }
  Unshelve. all: auto.
  Qed.

  Lemma Client04_load_loop_spec2
        tid n
  :
  ⊢ ∀ (γi γi1 γi2 γm1 γm2 k1 γ1 γ2 k2 k1' : τ{nat, 1+n}),
    [@ tid, n, ⊤ @]
      ⧼⟦((⤉ syn_inv n N_Client04 (client04Inv n γi γi1 γi2 γm1 γm2))
        ∗ (syn_tgt_interp_as n sndl (fun m => s_memory_black m))
        ∗ (⤉ ○G γm2 (k2, γ2, γ1))
        ∗ (⤉ Duty(tid)[(k2, 0, ∃ (k1' : τ{nat, n}), ▿ γ2 k1')])
        ∗ (⤉ ▿ γi 0)
        ∗ (⤉ ▿ γi2 k1')
        ∗ (⤉ ◆[k1, 1])
        ∗ (⤉ ◇[k2](1, 2))
        ∗ (⤉ -[k1](0)-◇ ∃ (k2' : τ{nat, n}), ▿ γ1 k2'))%S, 1+n⟧⧽
        (OMod.close_itree omod (SCMem.mod gvs) (load_loop 2))
        ⧼rv, ⌜rv = 1⌝
          ∗ ⟦((⤉ Duty(tid)[(k2, 0, ∃ (k1' : τ{nat, n}), ▿ γ2 k1')])
            ∗ (⤉ ▿ γ1 k2)
            ∗ (⤉ ⋈ [k2])
            ∗ (⤉ ○G γm2 (k2, γ2, γ1)))%S, 1+n⟧⧽
  .
  Proof.
    iIntros. iStartTriple. simpl. red_tl_all; simpl. rewrite red_syn_inv; rewrite red_syn_tgt_interp_as.
    iIntros "(#INV & #MEM & WM2 & DUTY & #DEADI & #DEADI2 & #OBL1 & PC & #PRM1)". iIntros "POST".
    (* Induction point *)
    iRevert "WM2 PC DUTY POST".
    iMod (tpromise_ind2 with "[] [-]") as "IH"; cycle 2. iApply "IH". iSplit; done.
    iSplit.
    { (* Inductive case *)
      iModIntro. iIntros "IH". iModIntro.
      iIntros "WM2 PC DUTY POST". iEval (unfold load_loop at 1; rewrite -> unfold_iter_eq). rred2r.
      iInv "INV" as "CI" "CI_CLOSE".
      iDestruct (client04Inv_unfold with "CI") as
        (k1'' k2'' γ1'' γ2'' γ1''' γ2''')
        "(#DPRM1 & #DPRM2 & #OBL1' & #OBL2 & LIVE1 & LIVE2 &
          [(_ & _ & _ & LIVE & _) | [_ [H | (PTX & BM1 & BM2 & _ & #DEAD2 & PO & #AO1)]]])".
      { iExFalso. iApply (OneShots.pending_not_shot with "LIVE DEADI"). }
      { iDestruct "H" as "(PTX & BM1 & BM2 & DEADI1 & #DEAD1 & PO1 & #AO2)".
        iPoseProof (AuthExcls.b_w_eq with "BM2 WM2") as "%EQ"; des; clarify.
        iMod ("CI_CLOSE" with "[- WM2 PC POST DUTY]") as "_".
        { iApply client04Inv_fold.
          iSplitR; [iApply "DPRM1"|]. iSplitR; [iApply "DPRM2"|]. iSplitR; [done|]. iSplitR; [done|].
          iSplitL "LIVE1"; [done|]. iSplitL "LIVE2"; [done|].
          iRight. iSplitR; [done |]. iLeft. iFrame. iSplit; done.
        }
        iPoseProof (pc_split _ _ 1 with "PC") as "[PC' PC]".
        iApply (wpsim_yieldR with "[DUTY PC']"). auto. iFrame. iApply (pcs_cons_fold with "[PC']"). iFrame.
        iIntros "DUTY _". rred2r.
        iClear "DPRM1 DPRM2 OBL1' OBL2". clear k1'' γ2''' γ1''.
        iInv "INV" as "CI" "CI_CLOSE".
        iDestruct (client04Inv_unfold with "CI") as
          (k1'' k2'' γ1'' γ2'' γ1''' γ2''')
          "(#DPRM1 & #DPRM2 & #OBL1' & #OBL2 & LIVE1 & LIVE2 &
            [(_ & _ & _ & LIVE & _) | [_ [(PTX & REST) | (_ & _ & BM2 & _ & _ & PO & _)]]])".
        { iExFalso. iApply (OneShots.pending_not_shot with "LIVE DEADI"). }
        { iApply (SCMem_load_fun_spec with "[PTX]"). auto.
          { pose proof mask_disjoint_N_Client04_state_tgt. set_solver. }
          { iFrame. done. }
          iIntros (rv) "[%EQ PTX]"; clarify. rred2r. iApply wpsim_tauR. rred2r.
          iMod ("CI_CLOSE" with "[- WM2 PC POST DUTY]") as "_".
          { iApply client04Inv_fold.
            iSplitR; [iApply "DPRM1"|]. iSplitR; [iApply "DPRM2"|]. iSplitR; [done|]. iSplitR; [done|].
            iSplitL "LIVE1"; [done|]. iSplitL "LIVE2"; [done|].
            iRight. iSplitR; [done |]. iLeft. iFrame.
          }
          iApply (wpsim_yieldR with "[DUTY PC]"). auto. iFrame. iApply (pcs_cons_fold with "[PC]"). iFrame.
          iIntros "DUTY _". rred2r.
          iApply SCMem_compare_fun_spec. instantiate (1:=n). auto. set_solver.
          { simpl. des_ifs. iApply (tgt_interp_as_equiv with "MEM"). iIntros. iSplit.
            { iIntros. simpl. red_tl; simpl. iSplit; [done | iPureIntro; auto]. }
            { simpl. red_tl; simpl. iIntros "[? _]". done. }
          }
          iIntros (rv) "[_ %NEQ]". exploit NEQ. auto. i; subst. rred2r.
          iApply wpsim_tauR. rred2r. iApply ("POST" with "[DUTY WM2]"). iSplitR; [done|]. iFrame. iSplit; auto.
        }
        { iExFalso. iPoseProof (AuthExcls.b_w_eq with "BM2 WM2") as "%EQ"; des; clarify.
          iApply (pending_not_active with "PO AO2").
        }
      }
      { iPoseProof (AuthExcls.b_w_eq with "BM2 WM2") as "%EQ"; des; clarify.
        iApply (wpsim_yieldR_gen_pending with "DUTY [PO]"). auto.
        { instantiate (1:=nil). rewrite app_nil_r. auto. }
        3:{ iApply (pps_cons_fold with "[PO]"). iSplitL; [done | iApply pps_nil]. }
        auto. auto. auto.
        iIntros "DUTY CRED PO _". iMod ("IH" with "CRED") as "IH".
        iMod ("CI_CLOSE" with "[- WM2 PC POST DUTY IH]") as "_".
        { iApply client04Inv_fold.
          iSplitR; [iApply "DPRM1"|]. iSplitR; [iApply "DPRM2"|]. iSplitR; [done|]. iSplitR; [done|].
          iSplitL "LIVE1"; [done|]. iSplitL "LIVE2"; [done|].
          iRight. iSplitR; [done |]. iRight. iFrame "#∗". iSplitR. iExists k1'; red_tl_all; auto.
          iPoseProof (pps_cons_unfold with "PO") as "[PO _]". done.
        }
        iModIntro. rred2r. iClear "DPRM1 DPRM2 OBL1' OBL2 DEAD2 AO1". clear k1'' γ2''' γ1'''.
        iInv "INV" as "CI" "CI_CLOSE".
        iDestruct (client04Inv_unfold with "CI") as
          (k1'' k2'' γ1'' γ2'' γ1''' γ2''')
          "(#DPRM1 & #DPRM2 & #OBL1' & #OBL2 & LIVE1 & LIVE2 &
            [(_ & _ & _ & LIVE & _) | [_ [(PTX & REST) | (PTX & BM1 & BM2 & _ & #DEAD2 & PO & #AO1)]]])".
        { iExFalso. iApply (OneShots.pending_not_shot with "LIVE DEADI"). }
        { iDestruct "REST" as "(BM1 & BM2 & DEADI1 & #DEAD1 & PO1 & #AO2)".
          iPoseProof (AuthExcls.b_w_eq with "BM2 WM2") as "%EQ"; des; clarify.
          iApply (SCMem_load_fun_spec with "[PTX]"). auto.
          { pose proof mask_disjoint_N_Client04_state_tgt. set_solver. }
          { iFrame. done. }
          iIntros (rv) "[%EQ PTX]"; clarify. rred2r. iApply wpsim_tauR. rred2r.
          iMod ("CI_CLOSE" with "[- WM2 PC POST DUTY]") as "_".
          { iApply client04Inv_fold.
            iSplitR; [iApply "DPRM1"|]. iSplitR; [iApply "DPRM2"|]. iSplitR; [done|]. iSplitR; [done|].
            iSplitL "LIVE1"; [done|]. iSplitL "LIVE2"; [done|].
            iRight. iSplitR; [done |]. iLeft. iFrame. iSplit; done.
          }
          iPoseProof (pc_split _ _ 1 with "PC") as "[PC' PC]".
          iApply (wpsim_yieldR with "[DUTY PC']"). auto. iFrame. iApply (pcs_cons_fold with "[PC']"). iFrame.
          iIntros "DUTY _". rred2r.
          iApply SCMem_compare_fun_spec. instantiate (1:=n). auto. set_solver.
          { simpl. des_ifs. iApply (tgt_interp_as_equiv with "MEM"). iIntros. iSplit.
            { iIntros. simpl. red_tl; simpl. iSplit; [done | iPureIntro; auto]. }
            { simpl. red_tl; simpl. iIntros "[? _]". done. }
          }
          iIntros (rv) "[_ %NEQ]". exploit NEQ. auto. i; subst. rred2r.
          iApply wpsim_tauR. rred2r. iApply ("POST" with "[DUTY WM2]"). iSplitR; [done|]. iFrame "#∗".
        }
        { iApply (SCMem_load_fun_spec with "[PTX]"). auto.
          { pose proof mask_disjoint_N_Client04_state_tgt. set_solver. }
          { iFrame. done. }
          iIntros (rv) "[%EQ PTX]"; clarify. rred2r. iApply wpsim_tauR. rred2r.
          iPoseProof (AuthExcls.b_w_eq with "BM2 WM2") as "%EQ"; des; clarify.
          iApply (wpsim_yieldR_gen_pending with "DUTY [PO]"). auto.
          { instantiate (1:=nil). rewrite app_nil_r. auto. }
          3:{ iApply (pps_cons_fold with "[PO]"). iSplitL; [done | iApply pps_nil]. }
          auto. auto. auto.
          iIntros "DUTY _ PPS _". iPoseProof (pps_cons_unfold with "PPS") as "[PO _]".
          iMod ("CI_CLOSE" with "[- WM2 PC POST DUTY IH]") as "_".
          { iApply client04Inv_fold.
            iSplitR; [iApply "DPRM1"|]. iSplitR; [iApply "DPRM2"|]. iSplitR; [done|]. iSplitR; [done|].
            iSplitL "LIVE1"; [done|]. iSplitL "LIVE2"; [done|].
            iRight. iSplitR; [done |]. iRight. iFrame "#∗". iExists k1'; red_tl_all; auto.
          }
          iModIntro. rred2r.
          iApply SCMem_compare_fun_spec. instantiate (1:=n). auto. set_solver.
          { simpl. des_ifs. iApply (tgt_interp_as_equiv with "MEM"). iIntros. iSplit.
            { iIntros. simpl. red_tl; simpl. iSplit; [done | iPureIntro; auto]. }
            { simpl. red_tl; simpl. iIntros "[? _]". done. }
          }
          iIntros (rv) "[%EQ _]". exploit EQ. auto. i; subst. rred2r.
          iApply wpsim_tauR. rred2r. iApply wpsim_tauR.
          fold (load_loop 1). iApply wpsim_stutter_mon. instantiate (1:=ps); auto. instantiate (1:=pt); auto.
          iApply ("IH" with "WM2 PC DUTY POST").
        }
      }
    }
    { (* Base case *)
      iModIntro. iIntros "#DEAD1".
      iEval (simpl; red_tl) in "DEAD1". iDestruct "DEAD1" as (k2') "DEAD1". iEval (red_tl_all) in "DEAD1".
      iModIntro. iIntros "WM2 PC DUTY POST".
      iEval (unfold load_loop at 1; rewrite -> unfold_iter_eq). rred2r.
      iInv "INV" as "CI" "CI_CLOSE".
      iDestruct (client04Inv_unfold with "CI") as
        (k1'' k2'' γ1'' γ2'' γ1''' γ2''')
        "(#DPRM1 & #DPRM2 & #OBL1' & #OBL2 & LIVE1 & LIVE2 &
          [(_ & _ & _ & LIVE & _) | [_ [H | (PTX & BM1 & BM2 & _ & #DEAD2 & PO & #AO1)]]])".
      { iExFalso. iApply (OneShots.pending_not_shot with "LIVE DEADI"). }
      { iDestruct "H" as "(PTX & BM1 & BM2 & DEADI1 & #DEAD1' & PO1 & #AO2)".
        iPoseProof (AuthExcls.b_w_eq with "BM2 WM2") as "%EQ"; des; clarify.
        iMod ("CI_CLOSE" with "[- WM2 PC POST DUTY]") as "_".
        { iApply client04Inv_fold.
          iSplitR; [iApply "DPRM1"|]. iSplitR; [iApply "DPRM2"|]. iSplitR; [done|]. iSplitR; [done|].
          iSplitL "LIVE1"; [done|]. iSplitL "LIVE2"; [done|].
          iRight. iSplitR; [done |]. iLeft. iFrame. iSplit; done.
        }
        iClear "DEAD1 DPRM1 DPRM2 OBL2 OBL1'". iRename "DEAD1'" into "DEAD1". clear k1'' γ2''' γ1''.
        iPoseProof (pc_split _ _ 1 with "PC") as "[PC' PC]".
        iApply (wpsim_yieldR with "[DUTY PC']"). auto. iFrame. iApply (pcs_cons_fold with "[PC']"). iFrame.
        iIntros "DUTY _". rred2r.
        iInv "INV" as "CI" "CI_CLOSE".
        iDestruct (client04Inv_unfold with "CI") as
          (k1'' k2'' γ1'' γ2'' γ1''' γ2''')
          "(#DPRM1 & #DPRM2 & #OBL1' & #OBL2 & LIVE1 & LIVE2 &
            [(_ & _ & _ & LIVE & _) | [_ [(PTX & REST) | (_ & _ & BM2 & _ & _ & PO & _)]]])".
        { iExFalso. iApply (OneShots.pending_not_shot with "LIVE DEADI"). }
        { iApply (SCMem_load_fun_spec with "[PTX]"). auto.
          { pose proof mask_disjoint_N_Client04_state_tgt. set_solver. }
          { iFrame. done. }
          iIntros (rv) "[%EQ PTX]"; clarify. rred2r. iApply wpsim_tauR. rred2r.
          iMod ("CI_CLOSE" with "[- WM2 PC POST DUTY]") as "_".
          { iApply client04Inv_fold.
            iSplitR; [iApply "DPRM1"|]. iSplitR; [iApply "DPRM2"|]. iSplitR; [done|]. iSplitR; [done|].
            iSplitL "LIVE1"; [done|]. iSplitL "LIVE2"; [done|].
            iRight. iSplitR; [done |]. iLeft. iFrame.
          }
          iApply (wpsim_yieldR with "[DUTY PC]"). auto. iFrame. iApply (pcs_cons_fold with "[PC]"). iFrame.
          iIntros "DUTY _". rred2r.
          iApply SCMem_compare_fun_spec. instantiate (1:=n). auto. set_solver.
          { simpl. des_ifs. iApply (tgt_interp_as_equiv with "MEM"). iIntros. iSplit.
            { iIntros. simpl. red_tl; simpl. iSplit; [done | iPureIntro; auto]. }
            { simpl. red_tl; simpl. iIntros "[? _]". done. }
          }
          iIntros (rv) "[_ %NEQ]". exploit NEQ. auto. i; subst. rred2r.
          iApply wpsim_tauR. rred2r. iApply ("POST" with "[DUTY WM2]"). iSplitR; [done|]. iFrame "#∗".
        }
        { iExFalso. iPoseProof (AuthExcls.b_w_eq with "BM2 WM2") as "%EQ"; des; clarify.
          iApply (pending_not_active with "PO AO2").
        }
      }
      { iExFalso. iPoseProof (AuthExcls.b_w_eq with "BM2 WM2") as "%EQ"; des; clarify.
        iApply (OneShots.pending_not_shot with "LIVE1 DEAD1").
      }
    }
  Unshelve. all: auto.
  Qed.

  Lemma Client04_thread2_spec
        tid2 n
    :
    ⊢ ⟦(∀ (γi γi1 γi2 γm1 γm2 k2 γ1 : τ{nat, 1+n}),
           ((⤉ syn_inv n N_Client04 (client04Inv n γi γi1 γi2 γm1 γm2))
              ∗ (syn_tgt_interp_as n sndl (fun m => (s_memory_black m)))
              ∗ (⤉ Duty(tid2)[(k2, 0, ∃ (k1' : τ{nat, n}), ▿ γi2 k1')])
              ∗ (⤉ ○G γm2 (k2, γi2, γi1))
              ∗ (⤉ △ γi2 (1/2))
              ∗ ◇[k2](1, 1))
             -∗
             syn_wpsim (1+n) tid2 ⊤
             (fun rs rt => (⤉ (syn_term_cond n tid2 _ rs rt))%S)
             false false
             (fn2th Client04Spec.module "thread2" (tt ↑))
             (fn2th Client04.module "thread2" (tt ↑)))%S, 1+n⟧.
  Proof.
    iIntros. red_tl_all. iIntros (γi). red_tl_all. iIntros (γi1).
    red_tl_all. iIntros (γi2). red_tl_all. iIntros (γm1).
    red_tl_all. iIntros (γm2). red_tl_all. iIntros (k2).
    red_tl_all. iIntros (γ2). red_tl_all. simpl.
    iEval (rewrite red_syn_inv; rewrite red_syn_wpsim; rewrite red_syn_tgt_interp_as).

    iIntros "(#INV & #MEM & DUTY & WM & LIVEI2 & PC)".

    unfold fn2th. simpl. unfold thread2, Client04Spec.thread2.
    rred2r. lred2r.

    iEval (do 2 rewrite unfold_iter_eq). rred2r. lred2r.
    iApply (wpsim_yieldR_gen with "[DUTY PC]"). auto.
    { iSplitL "DUTY"; iFrame. iApply pcs_cons_fold. iSplitL; done. }
    iIntros "DUTY _". iModIntro. rred2r.

    iInv "INV" as "CI" "CI_CLOSE".
    iDestruct (client04Inv_unfold with "CI") as
      (k1 k2' γ1 γ2' γ1' γ2'')
      "(#DPRM1 & #DPRM2 & #OBL1 & #OBL2 & LIVE1 & LIVE2 &
        [(PTX & BM1 & BM2 & LIVEI & PO1 & PO2)
          | (#DEADI & [(PTX & BM1 & BM2 & DEADI1 & DEAD1 & PO1 & #AO2) | (PTX & BM1 & BM2 & DEADI2 & _)])])".
    { iPoseProof (AuthExcls.b_w_eq with "BM2 WM") as "%EQ". clarify.
      iApply (SCMem_store_fun_spec with "[PTX] [-]"). auto.
      { pose proof mask_disjoint_N_Client04_state_tgt; set_solver. }
      { iSplitR; auto. }
      iIntros (rv) "PTX". rred2r. iApply wpsim_tauR. rred2r. clear rv.
      iMod (OneShots.pending_shot _ 0 with "LIVEI") as "#DEADI".
      iPoseProof (OneShots.pending_merge _ (1/2) (1/2) with "LIVEI2 LIVE2") as "LIVEI2". rewrite Qp.half_half.
      iMod (OneShots.pending_shot _ k1 with "LIVEI2") as "#DEADI2".
      iMod (activate_tpromise with "DPRM1 PO1") as "[#PRM1 #AO1]".
      iMod (activate_tpromise with "DPRM2 PO2") as "[_ #AO2]".
      iMod (duty_fulfill with "[DUTY DEADI2]") as "DUTY".
      { iFrame. simpl; red_tl_all. iSplit. iExists k1; red_tl_all; done. done. }
      iClear "OBL2 DPRM2 AO2".
      iMod (alloc_obligation 1 5) as (k2') "(#OBL2 & PC & PO2)".
      iMod OneShots.alloc as "[%γ2' LIVE2]".
      iEval (rewrite <- Qp.half_half) in "LIVE2".
      iPoseProof (OneShots.pending_split _ (1/2) (1/2) with "LIVE2") as "[LIVE2 LIVE2']".
      iMod (AuthExcls.b_w_update _ _ _ (k2', γ2', γi1) with "BM2 WM") as "[BM2 WM]".
      iPoseProof (pending_split _ (1/2) (1/2) with "[PO2]") as "[PO2' PO2]". rewrite Qp.half_half. done.
      iPoseProof (pc_split _ _ 1 4 with "[PC]") as "[PC' PC]". done.
      iMod (duty_add (v:=n) with "[DUTY PO2' PC'] []") as "DUTY". iFrame.
      { instantiate (1 := (∃ (k1' : τ{nat, n}), ▿ γ2' k1')%S). iModIntro. simpl; red_tl_all.
        iIntros "[% D]". red_tl_all. iPoseProof "D" as "#D". iModIntro. iExists x; red_tl_all; done.
      }
      iPoseProof (duty_delayed_tpromise with "DUTY") as "#DPRM2". simpl; left; auto.
      iMod ("CI_CLOSE" with "[- WM PC DUTY LIVE2]") as "_".
      { iApply client04Inv_fold.
        iSplitR; [iApply "DPRM1"|]. iSplitR; [iApply "DPRM2"|]. iSplitR; [done|]. iSplitR; [done|].
        iSplitL "LIVE1"; [done|]. iSplitL "LIVE2'"; [done|].
        iRight. iSplitR; [done |]. iRight. iFrame "#∗". iExists k1; red_tl_all; auto.
      }

      iClear "DPRM1 DPRM2 OBL2 AO1". clear k2 γ2 γ2'' γ1'. rename k2' into k2. rename γ2' into γ2.
      iApply wpsim_reset. iStopProof.
      pose (k2, γ2, γi1, k1) as p.
      replace k2 with (p.1.1.1) by ss. replace γ2 with (p.1.1.2) by ss.
      replace γi1 with (p.1.2) by ss. replace k1 with (p.2) by ss.
      assert (TEMP : p.1.2 = γi1) by ss; setoid_rewrite TEMP at 1; clear TEMP.
      assert (TEMP : p.2 = k1) by ss; setoid_rewrite TEMP at 2; clear TEMP.
      generalize p. clear p.
      eapply wpsim_coind. auto. clear k2 γ2.
      ii. destruct a as [[[k2 γ2] γ1] k1'].
      iIntros "[#HG1 #CIH] [(#INV & #MEM & #OBL1 & #DEADI & #DEADI2 & #PRM1) (WM & PC & DUTY & LIVE2)]". simpl.
      iPoseProof (pc_split _ _ 2 2 with "[PC]") as "[PC' PC]". done.
      iApply (Client04_load_loop_spec2 with "[WM DUTY PC'] [-]").
      { simpl. red_tl_all; simpl. rewrite red_syn_inv; rewrite red_syn_tgt_interp_as; red_tl_all.
        iFrame "#∗".
      }
      iIntros (rv') "(%EQ & POST)"; subst. iEval (simpl; red_tl_all; simpl) in "POST".
      iDestruct "POST" as "(DUTY & #DEAD1 & #AO2 & WM)". rred2r. iClear "OBL1".
      iPoseProof (pc_split _ _ 1 1 with "[PC]") as "[PC' PC]". done.
      iApply (wpsim_sync with "[DUTY PC']"). auto.
      { iFrame. iApply pcs_cons_fold. iFrame. }
      iIntros "DUTY _". rred2r. iApply wpsim_tauR. lred2r. rred2r.

      iApply wpsim_observe. iIntros (ret). lred2r. rred2r.
      iApply wpsim_tauL; iApply wpsim_tauR. rred2r. iApply wpsim_tauR.
      iEval (do 2 rewrite unfold_iter_eq). rred2r. lred2r.
      iApply (wpsim_yieldR with "[DUTY PC]"). auto.
      { iFrame. iApply pcs_cons_fold. iFrame. }
      iIntros "DUTY _". rred2r.

      iInv "INV" as "CI" "CI_CLOSE".
      iDestruct (client04Inv_unfold with "CI") as
        (k1'' k2' γ1' γ2' γ1'' γ2'')
        "(#DPRM1 & _ & #OBL1 & _ & LIVE1 & LIVE2' &
          [(_ & _ & _ & LIVEI & _)
            | (_ & [(PTX & BM1 & BM2 & DEADI1 & _ & PO1 & _) | (PTX & _ & BM2 & _ & _ & PO2 & _)])])".
      { iExFalso. iApply (OneShots.pending_not_shot with "LIVEI DEADI"). }
      { iPoseProof (AuthExcls.b_w_eq with "BM2 WM") as "%EQ". clarify.
        iApply (SCMem_store_fun_spec with "[PTX] [-]"). auto.
        { pose proof mask_disjoint_N_Client04_state_tgt; set_solver. }
        { iSplitR; auto. }
        iIntros (rv) "PTX". rred2r. iApply wpsim_tauR. rred2r. clear rv.
        iPoseProof (OneShots.pending_merge _ (1/2) (1/2) with "LIVE2 LIVE2'") as "LIVE2". rewrite Qp.half_half.
        iMod (OneShots.pending_shot _ k1'' with "LIVE2") as "#DEAD2".
        iClear "PRM1". iMod (activate_tpromise with "DPRM1 PO1") as "[#PRM1 #AO1]".
        iMod (duty_fulfill with "[DUTY DEAD2]") as "DUTY".
        { iFrame. simpl; red_tl_all. iSplit. iExists k1''; red_tl_all; done. done. }
        iMod (alloc_obligation 1 5) as (k2') "(#OBL & PC & PO2)".
        iMod OneShots.alloc as "[%γ2' LIVE2]".
        iEval (rewrite <- Qp.half_half) in "LIVE2".
        iPoseProof (OneShots.pending_split _ (1/2) (1/2) with "LIVE2") as "[LIVE2 LIVE2']".
        iMod (AuthExcls.b_w_update _ _ _ (k2', γ2', γ1') with "BM2 WM") as "[BM2 WM]".
        iPoseProof (pending_split _ (1/2) (1/2) with "[PO2]") as "[PO2' PO2]". rewrite Qp.half_half. done.
        iPoseProof (pc_split _ _ 1 with "[PC]") as "[PC' PC]". done.
        iMod (duty_add (v:=n) with "[DUTY PO2' PC'] []") as "DUTY". iFrame.
        { instantiate (1 := (∃ (k1' : τ{nat, n}), ▿ γ2' k1')%S). iModIntro. simpl; red_tl_all.
          iIntros "[% D]". red_tl_all. iPoseProof "D" as "#D". iModIntro. iExists x; red_tl_all; done.
        }
        iPoseProof (duty_delayed_tpromise with "DUTY") as "#DPRM2". simpl; left; auto.
        iMod ("CI_CLOSE" with "[- WM PC DUTY LIVE2]") as "_".
        { iApply client04Inv_fold.
          iSplitR; [iApply "DPRM1"|]. iSplitR; [iApply "DPRM2"|]. iSplitR; [done|]. iSplitR; [done|].
          iSplitL "LIVE1"; [done|]. iSplitL "LIVE2'"; [done|].
          iRight. iSplitR; [done |]. iRight. iFrame "#∗".
          iExists k1; red_tl_all; auto.
        }
        iApply wpsim_reset. iApply wpsim_base. auto. iApply ("CIH" $! (k2', γ2', γ1', k1'') with "[-]").
        iSplitR.
        { iModIntro. repeat iSplit; auto. }
        { simpl. iFrame. }
      }
      { iPoseProof (AuthExcls.b_w_eq with "BM2 WM") as "%EQ". clarify.
        iExFalso. iApply (pending_not_active with "PO2"). done.
      }
    }
    { iPoseProof (AuthExcls.b_w_eq with "BM2 WM") as "%EQ". clarify.
      iApply (SCMem_store_fun_spec with "[PTX] [-]"). auto.
      { pose proof mask_disjoint_N_Client04_state_tgt; set_solver. }
      { iSplitR; auto. }
      iIntros (rv) "PTX". rred2r. iApply wpsim_tauR. rred2r. clear rv.
      iPoseProof (OneShots.pending_merge _ (1/2) (1/2) with "LIVEI2 LIVE2") as "LIVEI2". rewrite Qp.half_half.
      iMod (OneShots.pending_shot _ k1 with "LIVEI2") as "#DEADI2".
      iMod (activate_tpromise with "DPRM1 PO1") as "[#PRM1 #AO1]".
      iMod (duty_fulfill with "[DUTY DEADI2]") as "DUTY".
      { iFrame. simpl; red_tl_all. iSplit. iExists k1; red_tl_all; done. done. }
      iClear "OBL2 DPRM2 AO2".
      iMod (alloc_obligation 1 5) as (k2') "(#OBL2 & PC & PO2)".
      iMod OneShots.alloc as "[%γ2' LIVE2]".
      iEval (rewrite <- Qp.half_half) in "LIVE2".
      iPoseProof (OneShots.pending_split _ (1/2) (1/2) with "LIVE2") as "[LIVE2 LIVE2']".
      iMod (AuthExcls.b_w_update _ _ _ (k2', γ2', γ1) with "BM2 WM") as "[BM2 WM]".
      iPoseProof (pending_split _ (1/2) (1/2) with "[PO2]") as "[PO2' PO2]". rewrite Qp.half_half. done.
      iPoseProof (pc_split _ _ 1 with "[PC]") as "[PC' PC]". done.
      iMod (duty_add (v:=n) with "[DUTY PO2' PC'] []") as "DUTY". iFrame.
      { instantiate (1 := (∃ (k1' : τ{nat, n}), ▿ γ2' k1')%S). iModIntro. simpl; red_tl_all.
        iIntros "[% D]". red_tl_all. iPoseProof "D" as "#D". iModIntro. iExists x; red_tl_all; done.
      }
      iPoseProof (duty_delayed_tpromise with "DUTY") as "#DPRM2". simpl; left; auto.
      iMod ("CI_CLOSE" with "[- WM PC DUTY LIVE2]") as "_".
      { iApply client04Inv_fold.
        iSplitR; [iApply "DPRM1"|]. iSplitR; [iApply "DPRM2"|]. iSplitR; [done|]. iSplitR; [done|].
        iSplitL "LIVE1"; [done|]. iSplitL "LIVE2'"; [done|].
        iRight. iSplitR; [done |]. iRight. iFrame "#∗".
        iExists k1; red_tl_all; auto.
      }

      iClear "DPRM2 DPRM1 OBL2 AO1". clear k2 γ2 γ2''. rename k2' into k2. rename γ2' into γ2.
      iApply wpsim_reset. iStopProof.
      pose (k2, γ2, γ1, k1) as p.
      replace k2 with (p.1.1.1) by ss. replace γ2 with (p.1.1.2) by ss.
      replace γ1 with (p.1.2) by ss. replace k1 with (p.2) by ss.
      assert (TEMP : p.2 = k1) by ss; setoid_rewrite TEMP at 2; clear TEMP.
      generalize p. clear p.
      eapply wpsim_coind. auto. clear k2 γ2 γ1.
      ii. destruct a as [[[k2 γ2] γ1] k1'].
      iIntros "[#HG1 #CIH] [(#INV & #MEM & #OBL1 & #DEADI & #DEADI2 & #PRM1) (WM & PC & DUTY & LIVE2)]". simpl.
      iPoseProof (pc_split _ _ 2 2 with "[PC]") as "[PC' PC]". done.
      iApply (Client04_load_loop_spec2 with "[WM DUTY PC'] [-]").
      { simpl. red_tl_all; simpl. rewrite red_syn_inv; rewrite red_syn_tgt_interp_as; red_tl_all.
        iFrame "#∗".
      }
      iIntros (rv') "(%EQ & POST)"; subst. iEval (simpl; red_tl_all; simpl) in "POST".
      iDestruct "POST" as "(DUTY & #DEAD1 & #AO2 & WM)". rred2r. iClear "OBL1".
      iPoseProof (pc_split _ _ 1 1 with "[PC]") as "[PC' PC]". done.
      iApply (wpsim_sync with "[DUTY PC']"). auto.
      { iFrame. iApply pcs_cons_fold. iFrame. }
      iIntros "DUTY _". rred2r. iApply wpsim_tauR. lred2r. rred2r.

      iApply wpsim_observe. iIntros (ret). lred2r. rred2r.
      iApply wpsim_tauL; iApply wpsim_tauR. rred2r. iApply wpsim_tauR.
      iEval (do 2 rewrite unfold_iter_eq). rred2r. lred2r.
      iApply (wpsim_yieldR with "[DUTY PC]"). auto.
      { iFrame. iApply pcs_cons_fold. iFrame. }
      iIntros "DUTY _". rred2r.

      iInv "INV" as "CI" "CI_CLOSE".
      iDestruct (client04Inv_unfold with "CI") as
        (k1'' k2' γ1' γ2' γ1'' γ2'')
        "(#DPRM1 & _ & #OBL1 & _ & LIVE1 & LIVE2' &
          [(_ & _ & _ & LIVEI & _)
            | (_ & [(PTX & BM1 & BM2 & DEADI1 & _ & PO1 & _) | (PTX & _ & BM2 & _ & _ & PO2 & _)])])".
      { iExFalso. iApply (OneShots.pending_not_shot with "LIVEI DEADI"). }
      { iPoseProof (AuthExcls.b_w_eq with "BM2 WM") as "%EQ". clarify.
        iApply (SCMem_store_fun_spec with "[PTX] [-]"). auto.
        { pose proof mask_disjoint_N_Client04_state_tgt; set_solver. }
        { iSplitR; auto. }
        iIntros (rv) "PTX". rred2r. iApply wpsim_tauR. rred2r. clear rv.
        iPoseProof (OneShots.pending_merge _ (1/2) (1/2) with "LIVE2 LIVE2'") as "LIVE2". rewrite Qp.half_half.
        iMod (OneShots.pending_shot _ k1'' with "LIVE2") as "#DEAD2".
        iClear "PRM1". iMod (activate_tpromise with "DPRM1 PO1") as "[#PRM1 #AO1]".
        iMod (duty_fulfill with "[DUTY DEAD2]") as "DUTY".
        { iFrame. simpl; red_tl_all. iSplit. iExists k1''; red_tl_all; done. done. }
        iMod (alloc_obligation 1 5) as (k2') "(#OBL & PC & PO2)".
        iMod OneShots.alloc as "[%γ2' LIVE2]".
        iEval (rewrite <- Qp.half_half) in "LIVE2".
        iPoseProof (OneShots.pending_split _ (1/2) (1/2) with "LIVE2") as "[LIVE2 LIVE2']".
        iMod (AuthExcls.b_w_update _ _ _ (k2', γ2', γ1') with "BM2 WM") as "[BM2 WM]".
        iPoseProof (pending_split _ (1/2) (1/2) with "[PO2]") as "[PO2' PO2]". rewrite Qp.half_half. done.
        iPoseProof (pc_split _ _ 1 with "[PC]") as "[PC' PC]". done.
        iMod (duty_add (v:=n) with "[DUTY PO2' PC'] []") as "DUTY". iFrame.
        { instantiate (1 := (∃ (k1' : τ{nat, n}), ▿ γ2' k1')%S). iModIntro. simpl; red_tl_all.
          iIntros "[% D]". red_tl_all. iPoseProof "D" as "#D". iModIntro. iExists x; red_tl_all; done.
        }
        iPoseProof (duty_delayed_tpromise with "DUTY") as "#DPRM2". simpl; left; auto.
        iMod ("CI_CLOSE" with "[- WM PC DUTY LIVE2]") as "_".
        { iApply client04Inv_fold.
          iSplitR; [iApply "DPRM1"|]. iSplitR; [iApply "DPRM2"|]. iSplitR; [done|]. iSplitR; [done|].
          iSplitL "LIVE1"; [done|]. iSplitL "LIVE2'"; [done|].
          iRight. iSplitR; [done |]. iRight. iFrame "#∗".
          iExists k1; red_tl_all; auto.
        }
        iApply wpsim_reset. iApply wpsim_base. auto. iApply ("CIH" $! (k2', γ2', γ1', k1'') with "[-]").
        iSplitR.
        { iModIntro. repeat iSplit; auto. }
        { simpl. iFrame. }
      }
      { iPoseProof (AuthExcls.b_w_eq with "BM2 WM") as "%EQ". clarify.
        iExFalso. iApply (pending_not_active with "PO2"). done.
      }
    }
    { iDestruct "DEADI2" as (?) "DEADI2". iEval (red_tl_all; simpl) in "DEADI2".
      iExFalso. iPoseProof (AuthExcls.b_w_eq with "BM2 WM") as "%EQ". des; clarify.
      iApply (OneShots.pending_not_shot with "LIVE2 DEADI2").
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
      (OwnM (Σ:=Σ) (memory_init_resource Client04.gvs))
        ∗ (AuthExcls.rest_gt (Σ:=Σ) (0, 0, 0))
        ∗
        (WSim.initial_prop
           Client04Spec.module Client04.module
           (Vars:=@sProp STT Γ) (Σ:=Σ)
           (STATESRC:=@SRA.in_subG Γ Σ sub _ _STATESRC)
           (STATETGT:=@SRA.in_subG Γ Σ sub _ _STATETGT)
           (IDENTSRC:=@SRA.in_subG Γ Σ sub _ _IDENTSRC)
           (IDENTTGT:=@SRA.in_subG Γ Σ sub _ _IDENTTGT)
           (ARROWRA:=@_ARROWRA STT Γ Σ TLRAS)
           idx init_ths init_ord)
        ⊢
        =| 1+idx |=(⟦syn_fairI (1+idx), 1+idx⟧)={ E, E }=>
            (∃ γi γi1 γi2 γm1 γm2 k1 k2,
                (inv idx N_Client04 (client04Inv idx γi γi1 γi2 γm1 γm2))
                  ∗ (⟦syn_tgt_interp_as idx sndl (fun m => (s_memory_black m)), 1+idx⟧)
                  ∗ ((own_thread tid1)
                    ∗ △ γi1 (1/2)
                    ∗ ○G γm1 (k1, γi1, γi2)
                    ∗ (⟦Duty(tid1)[(k1, 0, ∃ (k2' : τ{nat, idx}), ▿ γi1 k2' : @sProp STT Γ idx)], idx⟧)
                    ∗ ◇[k1](1, 1))
                  ∗ ((own_thread tid2)
                    ∗ △ γi2 (1/2)
                    ∗ ○G γm2 (k2, γi2, γi1)
                    ∗ (⟦Duty(tid2)[(k2, 0, ∃ (k1' : τ{nat, idx}), ▿ γi2 k1' : @sProp STT Γ idx)], idx⟧)
                    ∗ ◇[k2](1, 1))
            ).
    Proof.
      iIntros "(MEM & REST & INIT)". rewrite red_syn_fairI.
      iPoseProof (memory_init_iprop with "MEM") as "[MEM PTS]".

      iMod (alloc_obligation 1 2) as "(%k1 & OBL1 & PC1 & PO1)".
      iMod (alloc_obligation 1 2) as "(%k2 & OBL2 & PC2 & PO2)".
      iPoseProof (pc_split _ _ 1 with "PC1") as "[PC1 PC1']".
      iPoseProof (pc_split _ _ 1 with "PC2") as "[PC2 PC2']".
      iEval (rewrite <- Qp.half_half) in "PO1".
      iPoseProof (pending_split _ (1/2) (1/2) with "PO1") as "[PO1' PO1]".
      iEval (rewrite <- Qp.half_half) in "PO2".
      iPoseProof (pending_split _ (1/2) (1/2) with "PO2") as "[PO2' PO2]".

      iMod (OneShots.alloc) as "[%γi LIVEI]".
      iMod (OneShots.alloc) as "[%γi1 LIVEI1]".
      iMod (OneShots.alloc) as "[%γi2 LIVEI2]".
      iEval (rewrite <- Qp.half_half) in "LIVEI1".
      iEval (rewrite <- Qp.half_half) in "LIVEI2".
      iPoseProof (OneShots.pending_split with "LIVEI1") as "[LIVEI1 LIVEI1']".
      iPoseProof (OneShots.pending_split with "LIVEI2") as "[LIVEI2 LIVEI2']".
      iMod (AuthExcls.alloc_gt _ (k1, γi1, γi2) with "REST") as "[REST (%γm1 & BM1 & WM1)]".
      iMod (AuthExcls.alloc_gt _ (k2, γi2, γi1) with "REST") as "[REST (%γm2 & BM2 & WM2)]".

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

      iMod (duty_add with "[DU1 PO1' PC1'] []") as "DU1".
      { instantiate (4:=[]). iFrame. }
      { instantiate (1:=(∃ (k2' : τ{nat, idx}), ▿ γi1 k2' : @sProp STT Γ idx)%S).
        iModIntro. simpl; red_tl. iIntros "H". iDestruct "H" as (k2') "H". red_tl_all.
        iPoseProof "H" as "#H". iModIntro; iExists _; red_tl_all; auto.
      }
      iMod (duty_add with "[DU2 PO2' PC2'] []") as "DU2".
      { instantiate (4:=[]). iFrame. }
      { instantiate (1:=(∃ (k1' : τ{nat, idx}), ▿ γi2 k1' : @sProp STT Γ idx)%S).
        iModIntro. simpl; red_tl. iIntros "H". iDestruct "H" as (k1') "H". red_tl_all.
        iPoseProof "H" as "#H". iModIntro; iExists _; red_tl_all; auto.
      }
      iPoseProof (duty_delayed_tpromise with "DU1") as "#DPRM1". simpl; left; auto.
      iPoseProof (duty_delayed_tpromise with "DU2") as "#DPRM2". simpl; left; auto.
      iMod (FUpd_alloc _ _ _ idx N_Client04 (client04Inv idx γi γi1 γi2 γm1 γm2)
        with "[PTS LIVEI BM1 BM2 LIVEI1' LIVEI2' PO1 PO2 DPRM1 DPRM2 OBL1 OBL2]") as "INV1".
      lia.
      Local Transparent X.
      { simpl. unfold SCMem.init_gvars, gvs. ss. des_ifs. iDestruct "PTS" as "((PT & _) & _)".
        iApply (client04Inv_fold _ _ _ _ _ _ k1 k2).
        iFrame "# OBL1 OBL2 LIVEI1' LIVEI2'".
        iLeft. iFrame.
        Local Transparent SCMem.alloc.
        unfold SCMem.alloc in Heq0. ss. des_ifs.
        Local Opaque SCMem.alloc.
      }
      iModIntro. iExists γi, γi1, γi2, γm1, γm2, k1, k2. rewrite red_syn_tgt_interp_as. iFrame.
      Unshelve. all: exact 0.
    Qed.

  End INITIAL.

End SPEC.