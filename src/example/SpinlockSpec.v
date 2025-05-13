From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Import pind Axioms ITreeLib Red TRed IRed2 WFLibLarge.
From Fairness Require Import FairBeh Mod Linking.
From Fairness Require Import Spinlock.
From Fairness Require Import PCM IPM IPropAux.
From Fairness Require Import IndexedInvariants OpticsInterp SimWeakest.
From Fairness Require Import TemporalLogic SCMemSpec.
From Fairness Require Import AuthExclsRA ExclsRA.

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
  Context {HasAuthExcls : @GRA.inG (AuthExcls.t nat) Γ}.
  Context {HasExcls : @GRA.inG (Excls.t unit) Γ}.

  Ltac red_tl_all := red_tl; red_tl_memra; red_tl_authexcls; red_tl_excls.

  (** Invariants. *)
  Definition spinlockInv (n : nat) (x : SCMem.val) (γx γe : nat)
    : sProp n :=
    (((x ↦ 0) ∗ (●G γx 0) ∗ (EX γe tt)) ∨ ((x ↦ 1) ∗ (●G γx 1)))%S.

  (* Namespace for Spinlock invariants. *)
  Definition N_Spinlock : namespace := (nroot .@ "Spinlock").
  Notation E_Spinlock := (↑N_Spinlock : coPset).

  Definition isSpinlock n (x : SCMem.val) (γx γe : nat) (k L : nat)
    : sProp n :=
    (◆[k, L] ∗ syn_inv n N_Spinlock (spinlockInv n x γx γe))%S.

  Global Instance isSpinlock_persistent n x γx γe k L :
    Persistent (⟦isSpinlock n x γx γe k L, n⟧).
  Proof.
    unfold Persistent. iIntros "H". unfold isSpinlock. red_tl.
    rewrite red_syn_inv. iDestruct "H" as "#H". auto.
  Qed.

  Lemma isSpinlock_get_data n x γx γe k L :
    (⟦isSpinlock n x γx γe k L, n⟧) -∗ (◆[k, L] ∗ inv n N_Spinlock (spinlockInv n x γx γe)).
  Proof.
    iEval (unfold isSpinlock; red_tl). iIntros "[LO INV]". eauto.
  Qed.

  Lemma Spinlock_lock_spec
        tid n
        (E : coPset)
    :
    ⊢ ∀ x γx γe k L (ds : list (nat * nat * sProp n)) (P R Q : sProp n) v,
        [@ tid, n, E @]
          ⧼(tgt_interp_as (state_tgt:=st_tgt_type) sndl (fun m => ((s_memory_black m) : sProp n)%S))
             ∗ (⟦isSpinlock n x γx γe k L, n⟧)
             ∗ (⟦P, n⟧)
             ∗ (⟦Duty(tid) ds, n⟧ ∗ ◇{List.map fst ds}(2 + L, 1 + (1+v)^2))
             ∗ ((((⤉ syn_inv n N_Spinlock (spinlockInv n x γx γe))
                    ∗ ((⤉ spinlockInv n x γx γe) =|1+n|={⊤ ∖ E_Spinlock, ⊤}=∗ emp)
                    ∗ (⤉ spinlockInv n x γx γe))%S : sProp (1+n))
                  ~{v, 1+n, (⊤ ∖ E_Spinlock), k, L}~◇
                  (((⤉ syn_inv n N_Spinlock (spinlockInv n x γx γe))
                      ∗ ((⤉ spinlockInv n x γx γe) =|1+n|={⊤ ∖ E_Spinlock, ⊤}=∗ emp)
                      ∗ (⤉ ((x ↦ 0) ∗ (●G γx 0) ∗ (EX γe tt))))%S : sProp (1+n))
               )
             ∗ (⟦((●G γx 0) ∗ R)%S, n⟧ =|1+n|=(fairI (1+n))={⊤ ∖ E_Spinlock}=∗ ⟦((●G γx 1) ∗ Q)%S, n⟧)
             ∗ (□((⟦P, n⟧ ∗ ⟦Duty(tid) ds, n⟧) =|1+n|={E, ⊤}=∗ ⟦R, n⟧))
             ∗ (□(⟦R, n⟧ =|1+n|={⊤, E}=∗ (⟦P, n⟧ ∗ ⟦Duty(tid) ds, n⟧)))
          ⧽
            (OMod.close_itree Client (SCMem.mod gvs) (Spinlock.lock x))
            ⧼rv, ⟦(Q ∗ (EX γe tt))%S, n⟧⧽
  .
  Proof.
    iIntros (? ? ? ? ? ? ? ? ? ?).
    iStartTriple. iIntros "PRE POST". unfold Spinlock.lock.
    (* Preprocess for induction: right after the cas call's yield. *)
    iEval (rewrite unfold_iter_eq). rred2r.
    iDestruct "PRE" as "(#MEM & #ISL & P & [DUTY PCS] & #ELI & AU & #PUT_D & #GET_D)".
    iMod (pcs_decr 1 ((1+v)^2) with "PCS") as "[PCS PCS_ELI]".
    { lia. }
    iMod (pcs_drop 1 (100 + (1+v)^2) with "PCS") as "PCS".
    { lia. }
    { lia. }
    iMod (pcs_decr 2 ((1+v)^2) with "PCS") as "[PCS PCS_ELI2]".
    { lia. }
    iApply (wpsim_yieldR_gen2 with "[DUTY PCS]").
    3:{ iFrame. }
    1,2: lia.
    iIntros "DUTY _ PCS".
    iMod ("PUT_D" with "[P DUTY]") as "R".
    { iFrame. }
    iModIntro. rred2r.
    (* Set up for ELI induction. *)
    iEval (simpl) in "PCS".
    iPoseProof (isSpinlock_get_data with "ISL") as "[#LO #INV_SL]".
    iInv "INV_SL" as "SL" "INV_SL_CLOSE". iEval (simpl) in "SL".

    (* Do induction. *)
    iRevert "PCS R AU POST".
    iPoseProof (elc_ccs_ind with "[PCS_ELI PCS_ELI2] [] [] [SL INV_SL_CLOSE]") as "RES".
    5:{ iSplitL; cycle 1. eauto. simpl. iEval (red_tl_all; rewrite red_syn_inv; rewrite red_syn_fupd). iFrame. done. }
    5:{ iIntros "PCS R AU POST". iMod "RES". iRevert "R AU POST". iApply ("RES" with "PCS"). }
    lia.
    { iSplitR. auto. iSplitL "PCS_ELI"; done. }

    - (* Inductive case. *)
      iModIntro. iIntros "IH".
      iIntros "A". iEval (simpl; red_tl_all; rewrite red_syn_inv; rewrite red_syn_fupd) in "A".
      iDestruct "A" as "(_ & INV_SL_CLOSE & SL)".
      iModIntro. iIntros "PCS R AU POST".
      (* Open invariant. *)
      iEval (unfold spinlockInv; red_tl_all) in "SL".
      iDestruct "SL" as "[(PTx & Lx & EX) | (PTx & Lx)]"; cycle 1.

      + (* Iterating case. *)
        iApply (SCMem_cas_fun_spec with "[PTx] [-]").
        3:{ iFrame. iApply (tgt_interp_as_equiv with "MEM"). ss. i.
            red_tl_all. iSplit; [iIntros "A" | iIntros "[A M]"]; iFrame. ss.
        }
        lia.
        { assert (↑N_Spinlock ## (↑N_state_tgt : coPset)).
          { apply ndot_ne_disjoint. ss. }
          set_solver.
        }
        iIntros (rv) "(% & %CASE & PTx)". destruct (SCMem.val_eq_dec 1 0).
        { exfalso. ss. }
        des; subst. rred2r. iApply wpsim_tauR. rred2r. iApply wpsim_tauR. rred2r.
        iEval (rewrite unfold_iter_eq). rred2r.
        iMod ("INV_SL_CLOSE" with "[PTx Lx]") as "_".
        { iEval (simpl; unfold spinlockInv; red_tl_all). iRight. iFrame. }
        iMod ("GET_D" with "R") as "[P DUTY]".
        iApply (wpsim_yieldR_gen with "[DUTY PCS]").
        2:{ iFrame. }
        lia.
        iIntros "DUTY FC". iMod ("PUT_D" with "[P DUTY]") as "R".
        { iFrame. }
        iModIntro. rred2r.
        iInv "INV_SL" as "SL" "INV_SL_CLOSE".
        (* Finish with IH. *)
        iMod ("IH" with "FC [SL INV_SL_CLOSE]") as "IH".
        { simpl. iEval (red_tl_all; rewrite red_syn_inv; rewrite red_syn_fupd). iFrame. done. }
        iApply ("IH" with "R AU POST").

      + (* Terminating case. *)
        iClear "IH".
        iApply (SCMem_cas_fun_spec with "[PTx] [-]").
        3:{ iFrame. iApply (tgt_interp_as_equiv with "MEM"). ss. i.
            red_tl_all. iSplit; [iIntros "A" | iIntros "[A M]"]; iFrame. ss.
        }
        lia.
        { assert (↑N_Spinlock ## (↑N_state_tgt : coPset)).
          { apply ndot_ne_disjoint. ss. }
          set_solver.
        }
        iIntros (rv) "(% & %CASE & PTx)". destruct (SCMem.val_eq_dec 0 0).
        2:{ exfalso. ss. }
        des; subst. rred2r. iApply wpsim_tauR. rred2r.
        (* Post conditions. *)
        iPoseProof ("AU" with "[Lx R]") as "AU".
        { iEval red_tl_all. iFrame. }
        iMod "AU". iEval (red_tl_all) in "AU". iDestruct "AU" as "[Lx Q]".
        iMod ("INV_SL_CLOSE" with "[PTx Lx]") as "_".
        { iEval (simpl; unfold spinlockInv; red_tl_all). iRight. iFrame. }
        iApply "POST". iEval red_tl_all. iFrame.

    - (* Terminating case. *)
      iIntros "T". iEval (simpl; red_tl_all; rewrite red_syn_inv; rewrite red_syn_fupd) in "T".
      iDestruct "T" as "(_ & INV_SL_CLOSE & PTx & Lx & EX)".
      iModIntro. iIntros "R AU POST".
      iApply (SCMem_cas_fun_spec with "[PTx] [-]").
      3:{ iFrame. iApply (tgt_interp_as_equiv with "MEM"). ss. i.
          red_tl_all. iSplit; [iIntros "A" | iIntros "[A M]"]; iFrame. ss.
      }
      lia.
      { assert (↑N_Spinlock ## (↑N_state_tgt : coPset)).
        { apply ndot_ne_disjoint. ss. }
        set_solver.
      }
      iIntros (rv) "(% & %CASE & PTx)". destruct (SCMem.val_eq_dec 0 0).
      2:{ exfalso. ss. }
      des; subst. rred2r. iApply wpsim_tauR. rred2r.
      (* Post conditions. *)
      iPoseProof ("AU" with "[Lx R]") as "AU".
      { iEval red_tl_all. iFrame. }
      iMod "AU". iEval (red_tl_all) in "AU". iDestruct "AU" as "[Lx Q]".
      iMod ("INV_SL_CLOSE" with "[PTx Lx]") as "_".
      { iEval (simpl; unfold spinlockInv; red_tl_all). iRight. iFrame. }
      iApply "POST". iEval red_tl_all. iFrame.

  Qed.

  Lemma Spinlock_unlock_spec
        tid n
        (E : coPset)
    :
    ⊢ ∀ x γx γe k L (ds : list (nat * nat * sProp n)) (P R Q : sProp n),
        [@ tid, n, E @]
          ⧼(tgt_interp_as (state_tgt:=st_tgt_type) sndl (fun m => ((s_memory_black m) : sProp n)%S))
             ∗ (⟦isSpinlock n x γx γe k L, n⟧)
             ∗ (⟦P, n⟧)
             ∗ (⟦(EX γe tt)%S, n⟧)
             ∗ (⟦Duty(tid) ds, n⟧ ∗ ◇{List.map fst ds}(1, 1))
             ∗ (⟦((●G γx 1) ∗ R)%S, n⟧ =|1+n|=(fairI (1+n))={⊤ ∖ E_Spinlock}=∗ ⟦((●G γx 0) ∗ Q)%S, n⟧)
             ∗ (□((⟦P, n⟧ ∗ ⟦Duty(tid) ds, n⟧) =|1+n|={E, ⊤}=∗ ⟦R, n⟧))
             ∗ (□(⟦R, n⟧ =|1+n|={⊤, E}=∗ (⟦P, n⟧ ∗ ⟦Duty(tid) ds, n⟧)))
          ⧽
            (OMod.close_itree Client (SCMem.mod gvs) (Spinlock.unlock x))
            ⧼rv, ⟦Q, n⟧⧽
  .
  Proof.
    iIntros (? ? ? ? ? ? ? ? ?).
    iStartTriple. iIntros "PRE POST". unfold Spinlock.unlock.
    rred2r.
    iDestruct "PRE" as "(#MEM & #ISL & P & EX & [DUTY PCS] & AU & #PUT_D & #GET_D)".
    iApply (wpsim_yieldR_gen with "[DUTY PCS]").
    2:{ iFrame. }
    lia.
    iIntros "DUTY _".
    iMod ("PUT_D" with "[P DUTY]") as "R".
    { iFrame. }
    iModIntro. rred2r.
    iPoseProof (isSpinlock_get_data with "ISL") as "[_ #INV_SL]".
    iInv "INV_SL" as "SL" "INV_SL_CLOSE". iEval (simpl) in "SL".
    iEval (unfold spinlockInv; red_tl_all) in "SL".
    iDestruct "SL" as "[(PTx & Lx & EX2) | (PTx & Lx)]".
    { iExFalso. iEval (red_tl_all) in "EX". iApply (Excls.exclusive with "EX EX2"). }
    iApply (SCMem_store_fun_spec with "[PTx] [-]").
    3:{ iFrame. eauto. }
    lia.
    { assert (↑N_Spinlock ## (↑N_state_tgt : coPset)).
      { apply ndot_ne_disjoint. ss. }
      set_solver.
    }
    iIntros (rv) "PTx". rred2r. iApply wpsim_tauR. rred2r.
    (* Postcondition. *)
    iMod ("AU" with "[Lx R]") as "AU".
    { iEval red_tl_all. iFrame. }
    iEval (red_tl_all) in "AU". iDestruct "AU" as "[Lx Q]".
    iMod ("INV_SL_CLOSE" with "[PTx Lx EX]") as "_".
    { iEval (unfold spinlockInv; simpl; red_tl_all). iEval (red_tl_all) in "EX". iLeft. iFrame. }
    iApply "POST". iFrame.
  Qed.

End SPEC.
Global Opaque Spinlock.lock Spinlock.unlock.
