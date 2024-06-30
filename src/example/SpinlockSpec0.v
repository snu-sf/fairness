From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Import pind Axioms ITreeLib Red TRed IRed2 WFLibLarge.
From Fairness Require Import FairBeh Mod Linking.
From Fairness Require Import Spinlock.
From Fairness Require Import PCM IProp IPM IPropAux.
From Fairness Require Import IndexedInvariants OpticsInterp SimWeakest.
From Fairness Require Import TemporalLogic SCMemSpec.
From Fairness Require Import OneShotsRA AuthExclsRA ExclsRA.

Section SPEC.

  Context {src_state : Type}.
  Context {src_ident : Type}.
  Context {Client : Mod.t}.
  Context {gvs : list nat}.
  Notation tgt_state := (OMod.closed_state Client (SCMem.mod gvs)).
  Notation tgt_ident := (OMod.closed_ident Client (SCMem.mod gvs)).

  Local Instance STT : StateTypes := Build_StateTypes src_state tgt_state src_ident tgt_ident.

  Context `{sub : @SRA.subG Γ Σ}.
  Context {TLRASs : TLRAs_small STT Γ}.
  Context {TLRAS : TLRAs STT Γ Σ}.

  Context {HasMEMRA: @GRA.inG memRA Γ}.
  Context {HasOneShots : @GRA.inG (OneShots.t unit) Γ}.
  Context {HasAuthExcl : @GRA.inG (AuthExcls.t nat) Γ}.
  Context {HasAuthExcl2 : @GRA.inG (AuthExcls.t (nat * nat)) Γ}.
  Context {HasExcls : @GRA.inG (Excls.t unit) Γ}.

  Ltac red_tl_all := red_tl; red_tl_memra; red_tl_authexcls; red_tl_excls; red_tl_oneshots.

  Context (spinlockN : namespace) `{DISJ: (↑N_state_tgt :coPset) ## (↑spinlockN : coPset)}.

  (** Invariants. *)
  Definition spinlockInv (n : nat) κs (x : SCMem.val) (γx γl : nat) (P : sProp n)
    : sProp n :=
    (∃ (l γκu κu : τ{nat}),
        ((x ↦ l) ∗ (● γx l) ∗ (● γl (γκu, κu)))
          ∗
          ((⌜l = 0⌝ ∗ (○ γl (γκu, κu)) ∗ P)
           ∨ (⌜l = 1⌝ ∗ (△ γκu 1) ∗ (-[κu](0)-◇ (▿ γκu tt)) ∗ (κu -(0)-◇ κs)))
    )%S.

  Definition isSpinlock n κs (x : SCMem.val) (γx γl : nat) (P : sProp n) (ℓL μn : nat)
    : sProp n :=
    (◆[κs, ℓL, μn] ∗ syn_inv n spinlockN (spinlockInv n κs x γx γl P))%S.

  Global Instance isSpinlock_persistent n κs (x : SCMem.val) (γx γl : nat) (P : sProp n) ℓL μn :
    Persistent (⟦isSpinlock n κs x γx γl P ℓL μn, n⟧).
  Proof.
    unfold Persistent. iIntros "H". unfold isSpinlock. red_tl.
    rewrite red_syn_inv. iDestruct "H" as "#H". auto.
  Qed.

  Lemma isSpinlock_unfold
        n κs (x : SCMem.val) (γx γl : nat) (P : sProp n) (ℓL μn : nat)
    :
    ⟦(isSpinlock n κs x γx γl P ℓL μn), n⟧
      ⊢ (◆[κs, ℓL, μn] ∗ inv n spinlockN (spinlockInv n κs x γx γl P))%I.
  Proof.
    unfold isSpinlock. red_tl. rewrite red_syn_inv. iIntros "[A B]". iFrame.
  Qed.

  Lemma pass_lock
        n κs (x : SCMem.val) (γx γl : nat) (P : sProp n) (ℓL μn : nat)
        tid γκu κu ϕ
        ℓl μa γκu' κu'
        E
        (SUB : (↑spinlockN) ⊆ E)
    :
    ⊢
      (⟦((isSpinlock n κs x γx γl P ℓL μn)
           ∗ (○ γl (γκu, κu)) ∗ (Duty(tid) ((κu, 0, ▿ γκu tt) :: ϕ))
           ∗ ◇[κs](ℓl, μa)
           ∗ ◆[κu', ℓl, μa] ∗ ⧖[κu', (1/2)] ∗ (△ γκu' 1) ∗ (-[κu'](0)-⧖ (▿ γκu' tt))
        )%S, n⟧)
      =|1+n|=(⟦syn_fairI (1+n), 1+n⟧)={E}=∗ (⟦((○ γl (γκu', κu')) ∗ (Duty(tid) ϕ) ∗ (▿ γκu tt) ∗ (⋈[κu']))%S, n⟧).
  Proof.
    rewrite red_syn_fairI. red_tl_all. simpl.
    iIntros "(#ISL & LK & DUTY & PCs & #LOu' & POu' & PENDu' & DPu')".
    iPoseProof (isSpinlock_unfold with "ISL") as "[_ #INV_SL]".
    iInv "INV_SL" as "SL" "INV_SL_CL".
    iEval (simpl; unfold spinlockInv; red_tl_all) in "SL".
    iDestruct "SL" as "[%l SL]". iEval (red_tl) in "SL".
    iDestruct "SL" as "[%γκu0 SL]". iEval (red_tl) in "SL".
    iDestruct "SL" as "[%κu0 SL]". iEval (red_tl) in "SL".
    iEval (red_tl_all; simpl) in "SL".
    iDestruct "SL" as "((PTx & Lx & LKb) & CASES)".
    iPoseProof (AuthExcls.b_w_eq with "LKb LK") as "%EQ". inv EQ.
    iDestruct "CASES" as "[(_ & LK2 & _) | (%LS & PENDu & PRu & LINKu)]".
    { iExFalso. iPoseProof (AuthExcls.w_w_false with "LK LK2") as "%F". inv F. }
    iMod (OneShots.pending_shot _ tt with "PENDu") as "#SHOTu".
    iPoseProof (unfold_tpromise with "PRu") as "[_ #ACTu]".
    iMod (duty_fulfill with "[DUTY]") as "DUTY".
    { iFrame. iEval (simpl; red_tl_all). auto. }
    iMod (activate_tpromise with "DPu' POu'") as "[#PRu' ACTu']".
    iMod (link_new_fine _ _ _ _ 0 with "[PCs]") as "#LINKu'".
    { iSplitR. iApply "LOu'". iFrame. }
    iMod (AuthExcls.b_w_update _ _ _ (γκu', κu') with "LKb LK") as "[LKb LK]".
    iMod ("INV_SL_CL" with "[PENDu' PTx Lx LKb]") as "_".
    { iEval (unfold spinlockInv; simpl; red_tl_all). iExists l.
      iEval (red_tl). iExists γκu'. iEval (red_tl). iExists κu'.
      iEval (red_tl_all; simpl). iFrame. iRight. iFrame. auto.
    }
    iModIntro. iFrame. auto.
  Qed.


  TODO

  Lemma Spinlock_lock_spec
        tid n
        (Es : coPsets)
        (MASK_TOP : OwnEs_top Es)
        (MASK_STTGT : mask_has_st_tgt Es n)
    :
    ⊢ ∀ γ x (P : Formula n) γk k L l q (ds : list (nat * nat * Formula n)),
        [@ tid, n, Es @]
          ⧼⟦(((syn_tgt_interp_as n sndl (fun m => (➢ (scm_memory_black m))))
                ∗ (⤉ isSpinlock n γ x P γk k L l)
                ∗ ➢(live γk k q) ∗ (⤉ Duty(tid) ds)
                ∗ ◇{List.map fst ds}(2 + L, 1))%F), 1+n⟧⧽
            (OMod.close_itree Client (SCMem.mod gvs) (Spinlock.lock x))
            ⧼rv, ⟦(∃ (γu u : τ{nat, 1+n}),
                      (⤉ P) ∗ ➢(auexa_w γ (((q/2)%Qp, γu, u) : Qp * nat * nat)) ∗ ➢(live γk k (q/2))
                       ∗ (⤉ Duty(tid) ((u, 0, ➢(@dead γu nat u)) :: ds)) ∗ ➢(@live γu nat u (1/2)) ∗ ◇[u](l, 1))%F, 1+n⟧⧽
  .
  Proof.
    iIntros (? ? ? ? ? ? ? ? ?).
    iStartTriple. iIntros "PRE POST". unfold Spinlock.lock.
    (* Preprocess for induction. *)
    iApply wpsim_free_all. auto.
    unfold isSpinlock.
    iEval (red_tl) in "PRE". iEval (rewrite red_syn_tgt_interp_as) in "PRE".
    iDestruct "PRE" as "(#STINTP & (%N & SL) & LIVE & DUTY & PCS)".
    iEval (red_tl; simpl) in "SL". iDestruct "SL" as "(%IN & #LO & %POS & INV)".
    iEval (rewrite red_syn_inv) in "INV". iPoseProof "INV" as "#INV".
    iMod (ccs_make k L _ 1 1 with "[PCS]") as "[CCS PCS]". iFrame. auto.
    (* Set up induction hypothesis. *)
    iMod (pcs_drop_le _ _ _ _ 1 with "PCS") as "PCS". lia. Unshelve. 2: lia.
    iRevert "LIVE DUTY POST". iMod (ccs_ind2 with "CCS [] PCS") as "IND".
    2:{ iApply "IND". }
    iModIntro. iExists 0. iIntros "IH". iModIntro. simpl. iIntros "PCS LIVE DUTY POST".
    (* Start an iteration. *)
    iEval (rewrite unfold_iter_eq). rred2r.
    (* Number of Yield = 1. *)
    iApply (wpsim_yieldR with "[DUTY PCS]").
    2:{ iSplitL "DUTY". iApply "DUTY". iFrame. }
    auto.
    iIntros "DUTY FC". iModIntro. rred2r.
    (* Case analysis on lock variable. *)
    iInv "INV" as "SLI" "SLI_CLOSE". iEval (unfold spinlockInv; simpl; red_tl; simpl) in "SLI".
    iDestruct "SLI" as "[[%q0 SLI] | DEAD]".
    2:{ iExFalso. iPoseProof (Lifetime.pending_not_shot with "LIVE DEAD") as "%F". iFrame. auto. }
    iEval (red_tl; simpl) in "SLI". iDestruct "SLI" as "[%γu0 SLI]".
    iEval (red_tl; simpl) in "SLI". iDestruct "SLI" as "[%u0 SLI]".
    iEval (red_tl; simpl) in "SLI". iDestruct "SLI" as "[qISB [ACQ|WAIT]]".

    (** Case 1. Acquire the lock. *)
    { iClear "IH". iDestruct "ACQ" as "(PT & PCk & qISW & PROP)".
      iApply (SCMem_cas_fun_spec _ _ _ n with "[PT]"). auto.
      { unfold mask_has_st_tgt. rewrite lookup_insert. pose mask_disjoint_spinlock_state_tgt. clear - d IN. set_solver. }
      { iFrame. iApply tgt_interp_as_equiv. 2: iApply "STINTP".
        iIntros. iEval (simpl; red_tl; simpl). iSplit; iIntros "P".
        - iFrame. ss.
        - iDestruct "P" as "[MB _]". iFrame.
      }
      iIntros (b) "(%u & %RES & PT)". destruct (SCMem.val_eq_dec 0 0).
      2:{ exfalso. ss. }
      clear e. des. subst. rred2r. iApply wpsim_tauR. rred2r.
      (* Close the invariant spinlockInv: *)
      (* 1. Allocate new obligation: I will release the lock. *)
      iMod (alloc_obligation l 2) as "(%k1 & #LO1 & PC1)".
      iMod (Lifetime.alloc k1) as "[%γk1 LIVE1]".
      (* 2. Preprocess. *)
      iPoseProof (Lifetime.pending_split _ (1/2)%Qp (1/2)%Qp with "[LIVE1]") as "[LIVE1 LIVE1']".
      { iEval (rewrite Qp.half_half). iFrame. }
      iEval (replace 2 with (1+1) by lia) in "PC1".
      iPoseProof (pc_split with "PC1") as "[PC1 PC_POST]".
      iMod (pc_mon _ 1 _ 1 _ _ with "PC1") as "PC1". Unshelve.
      2:{ apply layer_drop_eq; auto. }
      iMod (duty_add _ _ _ _ 0 ((➢ dead γk1 k1)%F : Formula n) with "[DUTY PC1] []") as "DUTY".
      { iFrame. }
      { iModIntro. iEval (ss; red_tl). auto. }
      iPoseProof (duty_tpromise with "DUTY") as "#PROM1".
      { simpl. left. auto. }
      iMod (link_new k1 k l 0 0 with "[PCk]") as "[#LINK1 _]".
      { iFrame. eauto. }
      iPoseProof ((Lifetime.pending_split _ (q/2)%Qp (q/2)%Qp) with "[LIVE]") as "[MYLIVE LIVE]".
      { rewrite Qp.div_2. iFrame. }
      iMod (auexa_b_w_update with "qISB qISW") as "[qISB qISW]".
      (* Now close with SLI_CLOSE. *)
      iMod ("SLI_CLOSE" with "[LIVE PT LIVE1' qISB]") as "_".
      { iEval (unfold spinlockInv; simpl; red_tl; simpl).
        iLeft. iExists (q/2)%Qp.
        iEval (red_tl; simpl). iExists γk1. iEval (red_tl; simpl). iExists k1. iEval (red_tl; simpl).
        iSplitL "qISB"; [iFrame|]. iRight. iFrame. auto.
      }
      (* Finish with POST. *)
      iApply "POST". iEval (red_tl; simpl). iExists γk1. iEval (red_tl; simpl). iExists k1.
      iEval (red_tl; simpl). iFrame.
    }

    (** Case 2. Miss the lock and loops. *)
    { iDestruct "WAIT" as "(PT & LIVE_SL & LIVE_O & #OATH & #LINK)".
      iApply (SCMem_cas_fun_spec _ _ _ n with "[PT]"). auto.
      { unfold mask_has_st_tgt. rewrite lookup_insert. pose mask_disjoint_spinlock_state_tgt. clear - d IN. set_solver. }
      { iFrame. iApply tgt_interp_as_equiv. 2: iApply "STINTP".
        iIntros. iEval (simpl; red_tl; simpl). iSplit; iIntros "P".
        - iFrame. ss.
        - iDestruct "P" as "[MB _]". iFrame.
      }
      iIntros (b) "(%u & %RES & PT)". destruct (SCMem.val_eq_dec 1 0).
      { exfalso. ss. }
      clear n0. des. subst. rred2r. iApply wpsim_tauR. rred2r. iApply wpsim_tauR.
      (* Get credits from IH and the invariant. *)
      iMod (tpromise_progress with "[FC]") as "[PC | DEAD]".
      { iFrame. iApply "OATH". }
      2:{ iExFalso. iPoseProof (Lifetime.pending_not_shot with "LIVE_O DEAD") as "%FALSE". auto. }
      iMod (link_amplify with "[PC]") as "PC".
      { iFrame. iApply "LINK". }
      iMod ("IH" with "PC") as "IH".
      (* Close the invariant spinlockInv. *)
      iMod ("SLI_CLOSE" with "[qISB LIVE_SL LIVE_O PT]") as "_".
      { iEval (unfold spinlockInv; simpl; red_tl; simpl).
        iLeft. iExists q0. iEval (red_tl; simpl).
        iExists γu0. iEval (red_tl; simpl). iExists u0. iEval (red_tl; simpl).
        iSplitL "qISB"; [iFrame|]. iRight. iFrame. auto.
      }
      (* Finish with IH. *)
      iApply wpsim_stutter_mon. i; eauto. instantiate (1:=pt). i; auto.
      iApply ("IH" with "LIVE DUTY POST").
    }
  Qed.

  Lemma red_syn_Spinlock_lock_spec
        tid n
        (Es : coPsets)
    :
    ⟦(∀ (γ : τ{nat})
        (x : τ{SCMem.val})
        (P : τ{Φ, 1+n})
        (γk k L l : τ{nat})
        (q : τ{Qp})
        (ds : τ{ listT (nat * nat * Φ)%ftype, 1+n})
       ,
         [@ tid, n, Es @]
           ⧼((syn_tgt_interp_as n sndl (fun m => (➢ (scm_memory_black m))))
                ∗ (⤉ isSpinlock n γ x P γk k L l)
                ∗ ➢(@live γk nat k q) ∗ (⤉ Duty(tid) ds)
                ∗ ◇{List.map fst ds}(2 + L, 1))⧽
             (OMod.close_itree Client (SCMem.mod gvs) (Spinlock.lock x))
             ⧼rv, (∃ (γu u : τ{nat, 1+n}),
                      (⤉ P) ∗ ➢(auexa_w γ (((q/2)%Qp, γu, u) : Qp * nat * nat)) ∗ ➢(@live γk nat k (q/2))
                            ∗ (⤉ Duty(tid) ((u, 0, ➢(@dead γu nat u)) :: ds)) ∗ ➢(@live γu nat u (1/2)) ∗ ◇[u](l, 1))⧽)%F, 1+n⟧
    =
      (∀ γ x (P : Formula n) γk k L l q (ds : list (nat * nat * Formula n)),
          [@ tid, n, Es @]
            ⧼⟦((syn_tgt_interp_as n sndl (fun m => (➢ (scm_memory_black m))))
                  ∗ (⤉ isSpinlock n γ x P γk k L l)
                  ∗ ➢(live γk k q) ∗ (⤉ Duty(tid) ds)
                  ∗ ◇{List.map fst ds}(2 + L, 1))%F, 1+n⟧⧽
              (OMod.close_itree Client (SCMem.mod gvs) (Spinlock.lock x))
              ⧼rv, ⟦(∃ (γu u : τ{nat, 1+n}),
                        (⤉ P) ∗ ➢(auexa_w γ (((q/2)%Qp, γu, u) : Qp * nat * nat)) ∗ ➢(live γk k (q/2))
                              ∗ (⤉ Duty(tid) ((u, 0, ➢(@dead γu nat u)) :: ds)) ∗ ➢(@live γu nat u (1/2)) ∗ ◇[u](l, 1))%F, 1+n⟧⧽)%I
  .
  Proof.
    simpl.
    red_tl. apply f_equal. extensionalities γ.
    red_tl. apply f_equal. extensionalities x.
    red_tl. apply f_equal. extensionalities P.
    red_tl. apply f_equal. extensionalities γk.
    red_tl. apply f_equal. extensionalities k.
    red_tl. apply f_equal. extensionalities L.
    red_tl. apply f_equal. extensionalities l.
    red_tl. apply f_equal. extensionalities q.
    red_tl. apply f_equal. extensionalities ds.
    apply red_syn_non_atomic_triple.
  Qed.

  Lemma Spinlock_lock_syn_spec
        tid n
        (Es : coPsets)
        (MASK_TOP : OwnEs_top Es)
        (MASK_STTGT : mask_has_st_tgt Es n)
    :
    ⊢ ⟦(∀ (γ : τ{nat})
          (x : τ{SCMem.val})
          (P : τ{Φ, 1+n})
          (γk k L l : τ{nat})
          (q : τ{Qp})
          (ds : τ{ listT (nat * nat * Φ)%ftype, 1+n})
         ,
           [@ tid, n, Es @]
             ⧼((syn_tgt_interp_as n sndl (fun m => (➢ (scm_memory_black m))))
                  ∗ (⤉ isSpinlock n γ x P γk k L l)
                  ∗ ➢(@live γk nat k q) ∗ (⤉ Duty(tid) ds)
                  ∗ ◇{List.map fst ds}(2 + L, 1))⧽
               (OMod.close_itree Client (SCMem.mod gvs) (Spinlock.lock x))
               ⧼rv, (∃ (γu u : τ{nat, 1+n}),
                        (⤉ P) ∗ ➢(auexa_w γ (((q/2)%Qp, γu, u) : Qp * nat * nat)) ∗ ➢(@live γk nat k (q/2))
                              ∗ (⤉ Duty(tid) ((u, 0, ➢(@dead γu nat u)) :: ds)) ∗ ➢(@live γu nat u (1/2)) ∗ ◇[u](l, 1))⧽)%F, 1+n⟧
  .
  Proof.
    rewrite red_syn_Spinlock_lock_spec. iApply Spinlock_lock_spec. all: auto.
  Qed.

  Lemma Spinlock_unlock_spec
        tid n
        (Es : coPsets)
        (MASK_TOP : OwnEs_top Es)
        (MASK_STTGT : mask_has_st_tgt Es n)
    :
    ⊢ ∀ γ x (P : Formula n) γk k L l q (ds : list (nat * nat * Formula n)) γu u,
        [@ tid, n, Es @]
          ⧼⟦(((syn_tgt_interp_as n sndl (fun m => (➢ (scm_memory_black m))))
                ∗ (⤉ isSpinlock n γ x P γk k L l) ∗ (⤉ P)
                ∗ ➢(auexa_w γ (((q/2)%Qp, γu, u) : Qp * nat * nat)) ∗ ➢(live γk k (q/2))
                ∗ (⤉ Duty(tid) ((u, 0, ➢(dead γu u)) :: ds)) ∗ ➢(live γu u (1/2))
                ∗ ◇{List.map fst ((u, 0, ➢(dead γu u)) :: ds)}(1, 1)
                ∗ ◇[k](1 + l, 1)))%F, 1+n⟧⧽
            (OMod.close_itree Client (SCMem.mod gvs) (Spinlock.unlock x))
            ⧼rv, ⟦((⤉ Duty(tid) ds) ∗ ➢(live γk k q))%F, 1+n⟧⧽
  .
  Proof.
    iIntros (? ? ? ? ? ? ? ? ? ? ?).
    iStartTriple. iIntros "PRE POST". unfold Spinlock.unlock.
    (* Preprocess. *)
    iApply wpsim_free_all. auto.
    unfold isSpinlock. ss.
    iEval (red_tl; simpl) in "PRE". iEval (rewrite red_syn_tgt_interp_as) in "PRE".
    iDestruct "PRE" as "(#STINTP & (%N & SL) & P & WQ & LIVE & DUTY & LIVEU & PCS & PCk)".
    iEval (red_tl; simpl) in "SL". iDestruct "SL" as "(%IN & #LO & %POS & INV)".
    iEval (rewrite red_syn_inv) in "INV". iPoseProof "INV" as "#INV".
    rred2r. iApply (wpsim_yieldR with "[DUTY PCS]").
    2:{ iSplitL "DUTY". iFrame. iFrame. }
    auto.
    iIntros "DUTY FC". iModIntro.
    (* Open invariant. *)
    iInv "INV" as "SLI" "SLI_CLOSE". iEval (unfold spinlockInv; simpl; red_tl; simpl) in "SLI".
    iDestruct "SLI" as "[[%q0 SLI] | DEAD]".
    2:{ iExFalso. iPoseProof (Lifetime.pending_not_shot with "LIVE DEAD") as "%F". auto. }
    iEval (red_tl; simpl) in "SLI". iDestruct "SLI" as "[%γu0 SLI]".
    iEval (red_tl; simpl) in "SLI". iDestruct "SLI" as "[%u0 SLI]".
    iEval (red_tl; simpl) in "SLI". iDestruct "SLI" as "[BQ [ACQ | WAIT]]".
    { iExFalso. iDestruct "ACQ" as "(_ & _ & WQ2 & _)".
      iPoseProof (auexa_w_w_false with "WQ WQ2") as "%F". inv F.
    }
    iDestruct "WAIT" as "(PT & LIVE2 & LIVEU2 & _)". rred2r.
    (* Proceed simulation. *)
    iApply (SCMem_store_fun_spec _ _ _ n with "[PT]"). auto.
    { rewrite lookup_insert. pose mask_disjoint_spinlock_state_tgt. clear - d IN. set_solver. }
    { iFrame. auto. }
    iIntros (rv) "PT". rred2r. destruct rv. iApply wpsim_tauR. rred2r.
    (* Close invariant. *)
    iPoseProof (auexa_b_w_eq with "BQ WQ") as "%EQ". clarify.
    iMod ("SLI_CLOSE" with "[P WQ PCk BQ PT]") as "_".
    { simpl. iEval (unfold spinlockInv). red_tl. iLeft.
      iExists (q/2)%Qp. red_tl. iExists γu. red_tl. iExists u.
      red_tl. iSplitL "BQ". iFrame. iLeft. iFrame.
    }
    (* Postconditions. *)
    iMod (Lifetime.pending_shot with "[LIVEU LIVEU2]") as "#DEADU".
    { iEval (rewrite <- Qp.half_half). iApply (Lifetime.pending_merge with "LIVEU LIVEU2"). }
    iMod (duty_fulfill with "[DUTY DEADU]") as "DUTY".
    { iFrame. auto. }
    iPoseProof (Lifetime.pending_merge with "LIVE LIVE2") as "LIVE".
    iEval (rewrite Qp.div_2) in "LIVE". iApply "POST". red_tl. iFrame.
  Qed.

  Lemma red_syn_Spinlock_unlock_spec
        tid n
        (Es : coPsets)
    :
    ⟦(∀ (γ : τ{nat})
        (x : τ{SCMem.val})
        (P : τ{Φ, 1+n})
        (γk k L l : τ{nat})
        (q : τ{Qp})
        (ds : τ{ listT (nat * nat * Φ)%ftype, 1+n})
        (γu u : τ{nat, 1+n})
       ,
         [@ tid, n, Es @]
           ⧼((syn_tgt_interp_as n sndl (fun m => (➢(scm_memory_black m))))
               ∗ (⤉ isSpinlock n γ x P γk k L l) ∗ (⤉ P)
               ∗ ➢(auexa_w γ (((q/2)%Qp, γu, u) : Qp * nat * nat)) ∗ ➢(@live γk nat k (q/2))
               ∗ (⤉ Duty(tid) ((u, 0, ➢(@dead γu nat u)) :: ds)) ∗ ➢(@live γu nat u (1/2))
               ∗ ◇{List.map fst ((u, 0, ➢(@dead γu nat u)) :: ds)}(1, 1)
               ∗ ◇[k](1 + l, 1))⧽
             (OMod.close_itree Client (SCMem.mod gvs) (Spinlock.unlock x))
             ⧼rv, ((⤉ Duty(tid) ds) ∗ ➢(@live γk nat k q))⧽)%F, 1+n⟧
    =
      (∀ γ x (P : Formula n) γk k L l q (ds : list (nat * nat * Formula n)) γu u,
          [@ tid, n, Es @]
            ⧼⟦(((syn_tgt_interp_as n sndl (fun m => (➢ (scm_memory_black m))))
                  ∗ (⤉ isSpinlock n γ x P γk k L l) ∗ (⤉ P)
                  ∗ ➢(auexa_w γ (((q/2)%Qp, γu, u) : Qp * nat * nat)) ∗ ➢(live γk k (q/2))
                  ∗ (⤉ Duty(tid) ((u, 0, ➢(dead γu u)) :: ds)) ∗ ➢(live γu u (1/2))
                  ∗ ◇{List.map fst ((u, 0, ➢(dead γu u)) :: ds)}(1, 1)
                  ∗ ◇[k](1 + l, 1)))%F, 1+n⟧⧽
              (OMod.close_itree Client (SCMem.mod gvs) (Spinlock.unlock x))
              ⧼rv, ⟦((⤉ Duty(tid) ds) ∗ ➢(live γk k q))%F, 1+n⟧⧽)%I
  .
  Proof.
    red_tl. apply f_equal. extensionalities γ.
    red_tl. apply f_equal. extensionalities x.
    red_tl. apply f_equal. extensionalities P.
    red_tl. apply f_equal. extensionalities γk.
    red_tl. apply f_equal. extensionalities k.
    red_tl. apply f_equal. extensionalities L.
    red_tl. apply f_equal. extensionalities l.
    red_tl. apply f_equal. extensionalities q.
    red_tl. apply f_equal. extensionalities ds.
    rewrite @red_tl_univ. apply f_equal. extensionalities γu.
    rewrite @red_tl_univ. apply f_equal. extensionalities u.
    apply red_syn_non_atomic_triple.
  Qed.

  Lemma Spinlock_unlock_syn_spec
        tid n
        (Es : coPsets)
        (MASK_TOP : OwnEs_top Es)
        (MASK_STTGT : mask_has_st_tgt Es n)
    :
    ⊢ ⟦(∀ (γ : τ{nat})
          (x : τ{SCMem.val})
          (P : τ{Φ, 1+n})
          (γk k L l : τ{nat})
          (q : τ{Qp})
          (ds : τ{ listT (nat * nat * Φ)%ftype, 1+n})
          (γu u : τ{nat, 1+n})
         ,
           [@ tid, n, Es @]
             ⧼((syn_tgt_interp_as n sndl (fun m => (➢(scm_memory_black m))))
                 ∗ (⤉ isSpinlock n γ x P γk k L l) ∗ (⤉ P)
                 ∗ ➢(auexa_w γ (((q/2)%Qp, γu, u) : Qp * nat * nat)) ∗ ➢(@live γk nat k (q/2))
                 ∗ (⤉ Duty(tid) ((u, 0, ➢(@dead γu nat u)) :: ds)) ∗ ➢(@live γu nat u (1/2))
                 ∗ ◇{List.map fst ((u, 0, ➢(@dead γu nat u )) :: ds)}(1, 1)
                 ∗ ◇[k](1 + l, 1))⧽
               (OMod.close_itree Client (SCMem.mod gvs) (Spinlock.unlock x))
               ⧼rv, ((⤉ Duty(tid) ds) ∗ ➢(@live γk nat k q))⧽)%F, 1+n⟧
  .
  Proof.
    rewrite red_syn_Spinlock_unlock_spec. iApply Spinlock_unlock_spec. all: auto.
  Qed.

End SPEC.
Global Opaque Spinlock.lock Spinlock.unlock.
