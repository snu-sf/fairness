From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Import pind Axioms ITreeLib Red TRed IRed2 WFLibLarge.
From Fairness Require Import FairBeh Mod Linking.
From Fairness Require Import Spinlock.
From Fairness Require Import PCM IPM IPropAux.
From Fairness Require Import IndexedInvariants OpticsInterp SimWeakest.
From Fairness Require Import TemporalLogic SCMemSpec.
From Fairness Require Import OneShotsRA AuthExclsRA.

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
  Context {HasAuthExcl3 : @GRA.inG (AuthExcls.t (nat * nat * Qp)) Γ}.

  Ltac red_tl_all := red_tl; red_tl_memra; red_tl_authexcls; red_tl_oneshots.

  (* Namespace for Spinlock invariants. *)
  Context (N_Spinlock : namespace) `{DISJ: (↑N_state_tgt :coPset) ## (↑N_Spinlock : coPset)}.
  (* Definition N_Spinlock : namespace := (nroot .@ "Spinlock"). *)
  (* Let mask_disjoint_spinlock_state_tgt : ↑N_Spinlock ## (↑N_state_tgt : coPset).
  Proof. apply ndot_ne_disjoint. ss. Qed. *)

  (** Invariants. *)
  Definition spinlockInv (n : nat) κs (x : SCMem.val) (γl γs: nat) (P : sProp n)
    : sProp n :=
    ((∃ (γκu κu : τ{nat}) (q : τ{Qp}),
        (●G γl (γκu, κu, q))
          ∗
          (((x ↦ 0) ∗ (○G γl (γκu, κu, q)) ∗ P)
           ∨ ((x ↦ 1) ∗ (△ γκu 1) ∗ (-[κu](0)-◇ (▿ γκu tt)) ∗ (κu -(0)-◇ κs) ∗ (△ γs q))))
      ∨ (▿ γs tt)
    )%S.
  (* Definition spinlockInv (n : nat) κs (x : SCMem.val) (γx γl : nat) (P : sProp n) *)
  (*   : sProp n := *)
  (*   (∃ (l γκu κu : τ{nat}), *)
  (*       ((x ↦ l) ∗ (●G γx l) ∗ (●G γl (γκu, κu))) *)
  (*         ∗ *)
  (*         ((⌜l = 0⌝ ∗ (○G γl (γκu, κu)) ∗ P) *)
  (*          ∨ (⌜l = 1⌝ ∗ (△ γκu 1) ∗ (-[κu](0)-◇ (▿ γκu tt)) ∗ (κu -(0)-◇ κs))) *)
  (*   )%S. *)

  Definition isSpinlock n κs (x : SCMem.val) (γl γs : nat) (P : sProp n) (ℓL μn : nat)
    : sProp n :=
    (◆[κs, ℓL, μn] ∗ syn_inv n N_Spinlock (spinlockInv n κs x γl γs P))%S.

  Global Instance isSpinlock_persistent n κs (x : SCMem.val) (γl γs : nat) (P : sProp n) ℓL μn :
    Persistent (⟦isSpinlock n κs x γl γs P ℓL μn, n⟧).
  Proof.
    unfold Persistent. iIntros "H". unfold isSpinlock. red_tl.
    rewrite red_syn_inv. iDestruct "H" as "#H". auto.
  Qed.

  Lemma isSpinlock_unfold
        n κs (x : SCMem.val) (γl γs : nat) (P : sProp n) (ℓL μn : nat)
    :
    ⟦(isSpinlock n κs x γl γs P ℓL μn), n⟧
      ⊢ (◆[κs, ℓL, μn] ∗ inv n N_Spinlock (spinlockInv n κs x γl γs P))%I.
  Proof.
    unfold isSpinlock. red_tl. rewrite red_syn_inv. iIntros "[A B]". iFrame.
  Qed.

  Lemma make_isSpinlock
        n κs x γl γs P ℓL μn
        κu γκu q
        E
  :
  ⊢
    ⟦((⤉ (x ↦ 0)) ∗ (⤉ ●G γl (κu, γκu, q)) ∗ (⤉ ○G γl (κu, γκu, q)) ∗ (⤉P) ∗ ◆[κs, ℓL, μn])%S, 1+n⟧
      -∗
      ⟦( =|1+n|={E}=> (⤉ (isSpinlock n κs x γl γs P ℓL μn)))%S, 1+n⟧.
  Proof.
    red_tl_all. simpl. iIntros "(PT & LB & LW & P & #OBL)".
    rewrite red_syn_fupd. red_tl.
    iMod ((FUpd_alloc _ _ _ n (N_Spinlock) (spinlockInv n κs x γl γs P)) with "[PT LB LW P]") as "#SINV".
    auto.
    { simpl. unfold spinlockInv. red_tl. iLeft. iExists κu. red_tl. iExists γκu. red_tl. iExists q.
      red_tl_all. iFrame. iLeft. iFrame.
    }
    iModIntro. unfold isSpinlock. red_tl. auto.
  Qed.

  Lemma pass_lock
        n κs (x : SCMem.val) (γl γs : nat) (P : sProp n) (ℓL μn : nat) (q qs : Qp)
        tid γκu κu ϕ
        ℓl μa γκu' κu'
        E
        (SUB : (↑N_Spinlock) ⊆ E)
    :
    ⊢
      (⟦((isSpinlock n κs x γl γs P ℓL μn)
          ∗ (△ γs qs)
          ∗ (○G γl (γκu, κu, q)) ∗ (Duty(tid) ((κu, 0, ▿ γκu tt) :: ϕ))
          ∗ ◇[κs](ℓl, μa)
          ∗ ◆[κu', ℓl, μa] ∗ ⧖[κu', (1/2)] ∗ (△ γκu' 1) ∗ (-[κu'](0)-⧖ (▿ γκu' tt))
        )%S, n⟧)
      =|1+n|=(⟦syn_fairI (1+n), 1+n⟧)={E}=∗
        (⟦((○G γl (γκu', κu', q)) ∗ (△ γs qs) ∗ (Duty(tid) ϕ) ∗ (▿ γκu tt) ∗ (⋈[κu']))%S, n⟧).
  Proof.
    rewrite red_syn_fairI. red_tl_all. simpl.
    iIntros "(#ISL & LIVE & LK & DUTY & PCs & #LOu' & POu' & PENDu' & DPu')".
    iPoseProof (isSpinlock_unfold with "ISL") as "[_ #INV_SL]".
    iInv "INV_SL" as "SL" "INV_SL_CL".
    iEval (simpl; unfold spinlockInv; red_tl_all) in "SL".
    iDestruct "SL" as "[[%γκu0 SL] | #SHOT]"; cycle 1.
    { iExFalso. iApply (OneShots.pending_not_shot with "LIVE SHOT"). }
    iEval (red_tl) in "SL".
    iDestruct "SL" as "[%κu0 SL]". iEval (red_tl) in "SL". iDestruct "SL" as "[%qu SL]". iEval (red_tl) in "SL".
    iEval (red_tl_all; simpl) in "SL".
    iDestruct "SL" as "(LKb & CASES)".
    iPoseProof (AuthExcls.b_w_eq with "LKb LK") as "%EQ". inv EQ.
    iDestruct "CASES" as "[(_ & LK2 & _) | (PTx & PENDu & PRu & LINKu & LIVEu)]".
    { iExFalso. iPoseProof (AuthExcls.w_w_false with "LK LK2") as "%F". inv F. }
    iMod (OneShots.pending_shot _ tt with "PENDu") as "#SHOTu".
    iPoseProof (unfold_tpromise with "PRu") as "[_ #ACTu]".
    iMod (duty_fulfill with "[DUTY]") as "DUTY".
    { iFrame. iEval (simpl; red_tl_all). auto. }
    iMod (activate_tpromise with "DPu' POu'") as "[#PRu' ACTu']".
    iMod (link_new_fine _ _ _ _ 0 with "[PCs]") as "#LINKu'".
    { iSplitR. iApply "LOu'". iFrame. }
    iMod (AuthExcls.b_w_update _ _ _ (γκu', κu', q) with "LKb LK") as "[LKb LK]".
    iMod ("INV_SL_CL" with "[PENDu' PTx LKb LIVEu]") as "_".
    { iEval (unfold spinlockInv; simpl; red_tl_all). iLeft.
      iExists γκu'. iEval (red_tl). iExists κu'. iEval (red_tl). iExists q.
      iEval (red_tl_all; simpl). iFrame. iRight. iFrame. auto.
    }
    iModIntro. iFrame. auto.
  Qed.

  Lemma update_isSpinlock
        n κs x γl γs P ℓL μn
        κs' ℓL' μn' γs'
        E
        (MASK_SL : (↑N_Spinlock) ⊆ E)
    :
    ⊢ ⟦((⤉ isSpinlock n κs x γl γs P ℓL μn) ∗ (⤉ △ γs 1) ∗ (⤉ △ γs' 1) ∗ ◆[κs', ℓL', μn'])%S, 1+n⟧
        =|1+n|=(⟦syn_fairI (1+n), 1+n⟧)={E}=∗
          (⟦((⤉ isSpinlock n κs' x γl γs' P ℓL' μn') ∗ (⤉ ▿ γs tt))%S, 1+n⟧).
  Proof.
    red_tl_all. simpl. iIntros "(#SPIN & LIVE & LIVEnew & #OBLnew)".
    rewrite red_syn_fairI. iPoseProof (isSpinlock_unfold with "SPIN") as "[#OBL INV]".
    iInv "INV" as "SI" "SI_CLOSE". iEval (unfold spinlockInv; simpl; red_tl_all) in "SI".
    iDestruct "SI" as "[SI | #SHOT]"; cycle 1.
    { iExFalso. iApply (OneShots.pending_not_shot with "LIVE SHOT"). }
    iDestruct "SI" as (κu) "SI". red_tl.
    iDestruct "SI" as (γκu) "SI". red_tl.
    iDestruct "SI" as (qs) "SI". red_tl_all.
    iDestruct "SI" as "[LB [(PTX & LW & P) | (PTX & LIVEu & #PRMu & #LINKu & LIVEs)]]"; cycle 1.
    { iPoseProof (OneShots.pending_merge with "LIVE LIVEs") as "LIVE".
      iPoseProof (OneShots.pending_wf with "LIVE") as "%F". exfalso.
      eapply Qp_add_lt_one. eauto.
    }
    iMod (OneShots.pending_shot _ tt with "LIVE") as "#SHOT".
    iMod ("SI_CLOSE" with "[]") as "_".
    { unfold spinlockInv. simpl. red_tl_all. iRight. done. }
    iPoseProof (make_isSpinlock n κs' x γl γs' P ℓL' μn' κu γκu qs E with "[PTX LB LW P]") as "SPINnew".
    { red_tl_all. iFrame. auto. }
    iEval (rewrite red_syn_fupd) in "SPINnew". iMod "SPINnew". iModIntro. unfold isSpinlock; red_tl_all; auto.
  Qed.

  Lemma Spinlock_lock_spec
        tid n
    :
    ⊢ ∀ κs x γl γs qs (P : sProp n) ℓL μn (ds : list (nat * nat * sProp n)) ℓu μu,
      (⌜0 < ℓu⌝) →
        [@ tid, n, ⊤ @]
          ⧼⟦((syn_tgt_interp_as n sndl (fun m => (s_memory_black m)))
               ∗ (⤉ isSpinlock n κs x γl γs P ℓL μn)
               ∗ (⤉ △ γs qs)
               ∗ ◇[κs](ℓu, 1 + μu)
               ∗ (⤉ Duty(tid) ds)
               ∗ ◇{ds@1}(1 + ℓL, μn)
               ∗ ◇{ds@1}(1, 1)
            )%S, 1+n⟧⧽
            (OMod.close_itree Client (SCMem.mod gvs) (Spinlock.lock x))
            ⧼rv, ⟦(∃ (γκu κu : τ{nat, 1+n}),
                      (⤉ ○G γl (γκu, κu, (qs/2)%Qp))
                        ∗ (⤉ △ γs (qs/2))
                        ∗ (⤉ P)
                        ∗ (⤉ Duty(tid) ((κu, 0, ▿ γκu tt) :: ds))
                        ∗ ◇[κu](ℓu, μu)
                  )%S, 1+n⟧⧽
  .
  Proof.
    iIntros (? ? ? ? ? ? ? ? ? ? ? ?).
    iStartTriple. iIntros "PRE POST".
    iEval (red_tl_all; rewrite red_syn_tgt_interp_as) in "PRE"; simpl.
    iDestruct "PRE" as "(#MEM & #SPIN & LIVEs & PCs & DUTY & PCS & PCS')".
    iPoseProof (isSpinlock_unfold with "SPIN") as "[#OBL #INV]". iClear "SPIN".
    unfold Spinlock.lock.
    (* Preprocess for induction. *)
    iMod (ccs_make_fine with "[OBL PCS]") as "CCS". iSplitR. done. instantiate (1:=1). done.
    iRevert "PCS' PCs DUTY LIVEs POST". iMod (ccs_ind2 with "[CCS] []") as "IH". done. 2: iApply "IH".
    iModIntro. iExists 0. iIntros "IH". iModIntro. iIntros "PCS PCs DUTY LIVEs POST".
    (* Yield *)
    iEval (rewrite unfold_iter_eq). rred2r.
    iApply (wpsim_yieldR2 with "[DUTY PCS]"). auto. auto. iFrame.
    iIntros "DUTY CRED _". rred2r.
    (* Open invariant *)
    iInv "INV" as "SI" "SI_CLOSE".
    iEval (unfold spinlockInv; simpl; red_tl_all) in "SI".
    iDestruct "SI" as "[SI | #SHOT]"; cycle 1.
    { iExFalso. iApply (OneShots.pending_not_shot with "LIVEs SHOT"). }
    iDestruct "SI" as (γκu) "SI". iEval (red_tl) in "SI".
    iDestruct "SI" as (κu) "SI". iEval (red_tl) in "SI".
    iDestruct "SI" as (qs') "SI". iEval (red_tl_all; simpl) in "SI".
    iDestruct "SI" as "(LB & [(PTX & LW & P) | (PTX & LIVE & #PRM & #LINK & LIVEs')])".
    { (* Success *)
      iApply (SCMem_cas_fun_spec with "[PTX] [-]"). auto. set_solver. iFrame.
      { simpl. iApply (tgt_interp_as_equiv with "MEM"). iIntros. iSplit.
        { iIntros. simpl. red_tl; simpl. iSplit; [done | iPureIntro; auto]. }
        { simpl. red_tl; simpl. iIntros "[? _]". done. }
      }
      iIntros (rv) "[%u [%H' PTX]]". des_ifs. des; clarify. rred2r. iApply wpsim_tauR. rred2r.
      (* Allocate unlocking obligation *)
      iMod OneShots.alloc as "[%γs' LIVE]".
      iMod (alloc_obligation_fine ℓu (1 + μu)) as "(%κu' & #OBL' & PC & PENDING)".
      iPoseProof (pc_split _  _ 1 with "PC") as "[PC' PC]".
      iAssert (#=> ◇[κu'](1, 1))%I with "[PC']" as "> PC'".
      { destruct (Nat.eq_dec ℓu 1). subst; done.
        iMod (pc_drop _ 1 _ _ 1 1 with "[PC']") as "PC'". auto. done. done.
      }
      iEval (rewrite <- Qp.half_half) in "PENDING".
      iPoseProof (pending_split with "PENDING") as "[PENDING PENDING']".
      iMod (duty_add with "[DUTY PC' PENDING] []") as "DUTY". iFrame.
      { instantiate (1:= (▿ γs' tt)%S). simpl. iModIntro. red_tl_all. iIntros "#H". iModIntro. done. }
      iPoseProof (duty_delayed_tpromise with "DUTY") as "#DPRM". simpl; left; auto.
      iEval (setoid_rewrite <- (Qp.div_2 qs)) in "LIVEs".
      iPoseProof (OneShots.pending_split with "LIVEs") as "[LIVEs LIVEs']".
      iMod (activate_tpromise with "DPRM PENDING'") as "[#PRM _]". iClear "DPRM".
      iMod (AuthExcls.b_w_update _ _ _ (γs', κu', (qs/2)%Qp) with "LB LW") as "[LB LW]".
      iMod (link_new_fine _ _ _ _ 0 with "[PCs]") as "#LINK".
      { iSplitR; cycle 1. iApply "PCs". done. }
      (* Close the invariant *)
      iMod ("SI_CLOSE" with "[PTX LIVE LIVEs' LB]") as "_".
      { iEval (simpl; unfold spinlockInv; red_tl_all). iLeft. iExists γs'. red_tl. iExists κu'. red_tl_all.
        iExists (qs/2)%Qp. red_tl_all. iFrame. iRight; iFrame. iSplit; auto.
      }
      iApply ("POST" with "[-]").
      { do 2 (red_tl; iExists _); red_tl_all; iFrame. }
    }
    { (* Failure *)
      iApply (SCMem_cas_fun_spec with "[PTX] [-]"). auto. set_solver. iFrame.
      { simpl. iApply (tgt_interp_as_equiv with "MEM"). iIntros. iSplit.
        { iIntros. simpl. red_tl; simpl. iSplit; [done | iPureIntro; auto]. }
        { simpl. red_tl; simpl. iIntros "[? _]". done. }
      }
      iIntros (rv) "[%u [%H' PTX]]". des_ifs. des; clarify. rred2r. iApply wpsim_tauR. rred2r. iApply wpsim_tauR.
      iMod (tpromise_progress with "[PRM CRED]") as "[PC | #SHOT]". iFrame. done.
      2:{ iExFalso. iEval (simpl; red_tl_all) in "SHOT". iApply (OneShots.pending_not_shot with "LIVE SHOT"). }
      iMod (link_amplify with "[LINK PC]") as "PC". iFrame. done. simpl.
      iMod ("IH" with "PC") as "IH".
      (* Close the invariant *)
      iMod ("SI_CLOSE" with "[PTX LIVE LIVEs' LB]") as "_".
      { iEval (simpl; unfold spinlockInv; red_tl_all). iLeft. iExists γκu. red_tl. iExists κu. red_tl_all.
        iExists qs'; red_tl_all. iFrame. iRight; iFrame. repeat iSplit; auto.
      }
      iApply wpsim_stutter_mon. instantiate (1:=ps); auto. instantiate (1:=pt); auto.
      iApply ("IH" with "PCs DUTY LIVEs POST").
    }
  Unshelve. lia.
  Qed.

  Lemma Spinlock_unlock_spec
        tid n
    :
    ⊢ ∀ κs x γl γs qs (P : sProp n) ℓL μn (ds : list (nat * nat * sProp n)) γκu κu,
        [@ tid, n, ⊤ @]
          ⧼⟦((syn_tgt_interp_as n sndl (fun m => (s_memory_black m)))
               ∗ (⤉ isSpinlock n κs x γl γs P ℓL μn)
               ∗ (⤉ △ γs (qs/2)%Qp)
               ∗ (⤉ ○G γl (γκu, κu, (qs/2)%Qp))
               ∗ (⤉ P)
               ∗ (⤉ Duty(tid) ((κu, 0, ▿ γκu tt) :: ds))
               ∗ ◇{((κu, 0, ▿ κu tt) :: ds)@1}(1, 1)
            )%S, 1+n⟧⧽
            (OMod.close_itree Client (SCMem.mod gvs) (Spinlock.unlock x))
            ⧼rv, ⟦((⤉ Duty(tid) ds) ∗ (⤉ △ γs qs))%S, 1+n⟧⧽
  .
  Proof.
    iIntros (? ? ? ? ? ? ? ? ? ? ?).
    iStartTriple. iIntros "PRE POST".
    (* Preprocess. *)
    iEval (red_tl_all; rewrite red_syn_tgt_interp_as) in "PRE"; simpl.
    iDestruct "PRE" as "(#MEM & #SPIN & LIVEs & LW & P & DUTY & PCS)".
    iPoseProof (isSpinlock_unfold with "SPIN") as "[#OBL #INV]". iClear "SPIN".
    unfold Spinlock.unlock.
    (* Yield *)
    rred2r. iApply (wpsim_yieldR with "[DUTY PCS]"). auto. iFrame. done.
    iIntros "DUTY _". rred2r.
    (* Open invariant *)
    iInv "INV" as "SI" "SI_CLOSE".
    iEval (unfold spinlockInv; simpl; red_tl_all) in "SI".
    iDestruct "SI" as "[SI | #SHOT]"; cycle 1.
    { iExFalso. iApply (OneShots.pending_not_shot with "LIVEs SHOT"). }
    iDestruct "SI" as (γs') "SI". iEval (red_tl) in "SI".
    iDestruct "SI" as (κu') "SI". iEval (red_tl) in "SI".
    iDestruct "SI" as (qs') "SI". iEval (red_tl_all; simpl) in "SI".
    iDestruct "SI" as "(LB & [(PTX & LW' & _) | (PTX & LIVE & #PRM & #LINK & LIVEs')])".
    { iExFalso. iApply (AuthExcls.w_w_false with "LW LW'"). }
    iPoseProof (AuthExcls.b_w_eq with "LB LW") as "%EQ"; clarify.
    (* Store *)
    iApply (SCMem_store_fun_spec with "[PTX] [-]"). auto. set_solver.
    { iFrame. done. }
    iIntros (rv) "PTX". rred2r. iApply wpsim_tauR. rred2r.
    (* Close invariant *)
    iPoseProof (unfold_tpromise with "PRM") as "[_ #AO]".
    iMod (OneShots.pending_shot _ tt with "LIVE") as "#SHOT".
    iMod (duty_fulfill with "[DUTY]") as "DUTY".
    { iFrame. simpl; red_tl_all. iSplit; done. }
    iPoseProof (OneShots.pending_merge with "LIVEs LIVEs'") as "LIVEs". iEval (rewrite Qp.div_2) in "LIVEs".
    iMod ("SI_CLOSE" with "[PTX LB LW P]") as "_".
    { iEval (simpl; unfold spinlockInv; red_tl_all). iLeft. do 3 (iExists _; red_tl_all). iFrame. iLeft; iFrame. }
    iApply "POST". red_tl_all. iFrame.
  Qed.

  (* Lemma red_syn_Spinlock_unlock_spec *)
  (*       tid n *)
  (*       (Es : coPsets) *)
  (*   : *)
  (*   ⟦(∀ (γ : τ{nat}) *)
  (*       (x : τ{SCMem.val}) *)
  (*       (P : τ{Φ, 1+n}) *)
  (*       (γk k L l : τ{nat}) *)
  (*       (q : τ{Qp}) *)
  (*       (ds : τ{ listT (nat * nat * Φ)%ftype, 1+n}) *)
  (*       (γu u : τ{nat, 1+n}) *)
  (*      , *)
  (*        [@ tid, n, Es @] *)
  (*          ⧼((syn_tgt_interp_as n sndl (fun m => (➢(scm_memory_black m)))) *)
  (*              ∗ (⤉ isSpinlock n γ x P γk k L l) ∗ (⤉ P) *)
  (*              ∗ ➢(auexa_w γ (((q/2)%Qp, γu, u) : Qp * nat * nat)) ∗ ➢(@live γk nat k (q/2)) *)
  (*              ∗ (⤉ Duty(tid) ((u, 0, ➢(@dead γu nat u)) :: ds)) ∗ ➢(@live γu nat u (1/2)) *)
  (*              ∗ ◇{List.map fst ((u, 0, ➢(@dead γu nat u)) :: ds)}(1, 1) *)
  (*              ∗ ◇[k](1 + l, 1))⧽ *)
  (*            (OMod.close_itree Client (SCMem.mod gvs) (Spinlock.unlock x)) *)
  (*            ⧼rv, ((⤉ Duty(tid) ds) ∗ ➢(@live γk nat k q))⧽)%F, 1+n⟧ *)
  (*   = *)
  (*     (∀ γ x (P : Formula n) γk k L l q (ds : list (nat * nat * Formula n)) γu u, *)
  (*         [@ tid, n, Es @] *)
  (*           ⧼⟦(((syn_tgt_interp_as n sndl (fun m => (➢ (scm_memory_black m)))) *)
  (*                 ∗ (⤉ isSpinlock n γ x P γk k L l) ∗ (⤉ P) *)
  (*                 ∗ ➢(auexa_w γ (((q/2)%Qp, γu, u) : Qp * nat * nat)) ∗ ➢(live γk k (q/2)) *)
  (*                 ∗ (⤉ Duty(tid) ((u, 0, ➢(dead γu u)) :: ds)) ∗ ➢(live γu u (1/2)) *)
  (*                 ∗ ◇{List.map fst ((u, 0, ➢(dead γu u)) :: ds)}(1, 1) *)
  (*                 ∗ ◇[k](1 + l, 1)))%F, 1+n⟧⧽ *)
  (*             (OMod.close_itree Client (SCMem.mod gvs) (Spinlock.unlock x)) *)
  (*             ⧼rv, ⟦((⤉ Duty(tid) ds) ∗ ➢(live γk k q))%F, 1+n⟧⧽)%I *)
  (* . *)
  (* Proof. *)
  (*   red_tl. apply f_equal. extensionalities γ. *)
  (*   red_tl. apply f_equal. extensionalities x. *)
  (*   red_tl. apply f_equal. extensionalities P. *)
  (*   red_tl. apply f_equal. extensionalities γk. *)
  (*   red_tl. apply f_equal. extensionalities k. *)
  (*   red_tl. apply f_equal. extensionalities L. *)
  (*   red_tl. apply f_equal. extensionalities l. *)
  (*   red_tl. apply f_equal. extensionalities q. *)
  (*   red_tl. apply f_equal. extensionalities ds. *)
  (*   rewrite @red_tl_univ. apply f_equal. extensionalities γu. *)
  (*   rewrite @red_tl_univ. apply f_equal. extensionalities u. *)
  (*   apply red_syn_non_atomic_triple. *)
  (* Qed. *)

  (* Lemma Spinlock_unlock_syn_spec *)
  (*       tid n *)
  (*       (Es : coPsets) *)
  (*       (MASK_TOP : OwnEs_top Es) *)
  (*       (MASK_STTGT : mask_has_st_tgt Es n) *)
  (*   : *)
  (*   ⊢ ⟦(∀ (γ : τ{nat}) *)
  (*         (x : τ{SCMem.val}) *)
  (*         (P : τ{Φ, 1+n}) *)
  (*         (γk k L l : τ{nat}) *)
  (*         (q : τ{Qp}) *)
  (*         (ds : τ{ listT (nat * nat * Φ)%ftype, 1+n}) *)
  (*         (γu u : τ{nat, 1+n}) *)
  (*        , *)
  (*          [@ tid, n, Es @] *)
  (*            ⧼((syn_tgt_interp_as n sndl (fun m => (➢(scm_memory_black m)))) *)
  (*                ∗ (⤉ isSpinlock n γ x P γk k L l) ∗ (⤉ P) *)
  (*                ∗ ➢(auexa_w γ (((q/2)%Qp, γu, u) : Qp * nat * nat)) ∗ ➢(@live γk nat k (q/2)) *)
  (*                ∗ (⤉ Duty(tid) ((u, 0, ➢(@dead γu nat u)) :: ds)) ∗ ➢(@live γu nat u (1/2)) *)
  (*                ∗ ◇{List.map fst ((u, 0, ➢(@dead γu nat u )) :: ds)}(1, 1) *)
  (*                ∗ ◇[k](1 + l, 1))⧽ *)
  (*              (OMod.close_itree Client (SCMem.mod gvs) (Spinlock.unlock x)) *)
  (*              ⧼rv, ((⤉ Duty(tid) ds) ∗ ➢(@live γk nat k q))⧽)%F, 1+n⟧ *)
  (* . *)
  (* Proof. *)
  (*   rewrite red_syn_Spinlock_unlock_spec. iApply Spinlock_unlock_spec. all: auto. *)
  (* Qed. *)

End SPEC.
Global Opaque Spinlock.lock Spinlock.unlock.
