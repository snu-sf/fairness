From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Import pind Axioms ITreeLib Red TRed IRed2 WFLibLarge.
From Fairness Require Import FairBeh Mod Linking.
From Fairness Require Import Spinlock.
From Fairness Require Import PCM IProp IPM IPropAux.
From Fairness Require Import IndexedInvariants OpticsInterp SimWeakest.
From Fairness Require Import TemporalLogic SCMemSpec.
From Fairness Require Import AuthExclsRA ExclsRA.
(* For Use1 *)
From Fairness Require Import OneShotsRA.

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

  Ltac red_tl_all := red_tl; red_tl_memra; red_tl_authexcls; red_tl_excls; red_tl_oneshots.
  (* Ltac red_tl_all := red_tl; red_tl_memra; red_tl_authexcls; red_tl_excls. *)

  (** Invariants. *)
  Definition spinlockInv (n : nat) (x : SCMem.val) (γx γe : nat)
    : sProp n :=
    (((x ↦ 0) ∗ (● γx 0) ∗ (EX γe tt)) ∨ ((x ↦ 1) ∗ (● γx 1)))%S.

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
             ∗ (⟦Duty(tid) ds, n⟧ ∗ ◇{List.map fst ds}(2 + L, 1))
             ∗ (env_live_inv v (1+n) (⊤ ∖ E_Spinlock) k
                             (((⤉ syn_inv n N_Spinlock (spinlockInv n x γx γe))
                                 ∗ ((⤉ spinlockInv n x γx γe) =|1+n|={⊤ ∖ E_Spinlock, ⊤}=∗ emp)
                                 ∗ (⤉ spinlockInv n x γx γe)) : sProp (1+n))%S
                             (((⤉ syn_inv n N_Spinlock (spinlockInv n x γx γe))
                                 ∗ ((⤉ spinlockInv n x γx γe) =|1+n|={⊤ ∖ E_Spinlock, ⊤}=∗ emp)
                                 ∗ (⤉ ((x ↦ 0) ∗ (● γx 0) ∗ (EX γe tt)))) : sProp (1+n))%S
               )
             ∗ (⟦((● γx 0) ∗ R)%S, n⟧ =|1+n|=(fairI (1+n))={⊤ ∖ E_Spinlock}=∗ ⟦((● γx 1) ∗ Q)%S, n⟧)
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
    iMod (ccs_make _ _ _ 1 (100+v) with "[PCS]") as "[CCS PCS]".
    { iFrame. iEval (unfold isSpinlock; red_tl) in "ISL". iDestruct "ISL" as "[LO _]". eauto. }
    iMod (pcs_drop_le _ _ _ _ 1 with "PCS") as "PCS".
    lia.
    Unshelve. 2: lia.
    iMod (pcs_decr _ _ 2 v with "PCS") as "[PCS PCS_ELI]".
    lia.
    iApply (wpsim_yieldR_gen2 with "[DUTY PCS]").
    3:{ iFrame. }
    lia.
    lia.
    iIntros "DUTY _ PCS".
    iMod ("PUT_D" with "[P DUTY]") as "R".
    { iFrame. }
    iModIntro. rred2r.
    (* Set up for ELI induction. *)
    iEval (simpl) in "PCS".
    iPoseProof (isSpinlock_get_data with "ISL") as "[_ #INV_SL]".
    iInv "INV_SL" as "SL" "INV_SL_CLOSE". iEval (simpl) in "SL".

    (* Do induction. *)
    iRevert "PCS R AU POST".
    iPoseProof (eli_ccs_ind with "[CCS PCS_ELI] [] [] [SL INV_SL_CLOSE]") as "RES".
    5:{ iSplitL; cycle 1. eauto. simpl. iEval (red_tl_all; rewrite red_syn_inv; rewrite red_syn_fupd). iFrame. done. }
    5:{ iIntros "PCS R AU POST". iMod "RES".
        iRevert "R AU POST". iApply ("RES" with "PCS").
    }
    lia.
    { iFrame. }

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
             ∗ (⟦((● γx 1) ∗ R)%S, n⟧ =|1+n|=(fairI (1+n))={⊤ ∖ E_Spinlock}=∗ ⟦((● γx 0) ∗ Q)%S, n⟧)
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



  Section SPEC1.

    Context {HasOneShots : @GRA.inG (OneShots.t bool) Γ}.
    Context {HasAuthExcls2 : @GRA.inG (AuthExcls.t (nat * nat)) Γ}.

    Definition spinlockUse1 (n : nat) k (γ γx : nat) (P : sProp n) (l : nat)
      : sProp n :=
      (∃ (γu u : τ{nat}),
           (● γ (γu, u))
            ∗
            (((○ γx 0) ∗ (○ γ (γu, u)) ∗ P)
             ∨ ((○ γx 1) ∗ (△ γu 1) ∗ (-[u](0)-◇ (▿ γu true)) ∗ (u -(0)-◇ k)))
      )%S.

    (* Namespace for Spinlock invariants. *)
    Definition N_SpinlockUse1 : namespace := (nroot .@ "SpinlockUse1").

    Definition isSpinlockUse1 n k (γ γx : nat) (P : sProp n) (l : nat)
      : sProp n :=
      ((⌜0 < l⌝) ∗ syn_inv n N_SpinlockUse1 (spinlockUse1 n k γ γx P l))%S.

    Global Instance isSpinlockUse1_persistent n k γ γx P l :
      Persistent (⟦isSpinlockUse1 n k γ γx P l, n⟧).
    Proof.
      unfold Persistent. iIntros "H". unfold isSpinlockUse1. red_tl.
      rewrite red_syn_inv. iDestruct "H" as "#H". auto.
    Qed.

    Lemma isSpinlockUse1_get_data n k (γ γx : nat) (P : sProp n) (l : nat) :
      ⟦isSpinlockUse1 n k γ γx P l, n⟧ -∗ ((⌜0 < l⌝) ∗ inv n N_SpinlockUse1 (spinlockUse1 n k γ γx P l)).
    Proof.
      iEval (unfold isSpinlockUse1; red_tl). iIntros "[L INV]". eauto.
    Qed.

    Lemma Spinlock_lock_spec_use1
          tid n
          (E : coPset)
          (TOP : ⊤ ⊆ E)
      :
      ⊢ ∀ x γx γe k L γ (P : sProp n) l (ds : list (nat * nat * sProp n)),
          [@ tid, n, E @]
            ⧼⟦(((syn_tgt_interp_as n sndl (fun m => (s_memory_black m)))
                  ∗ (⤉ isSpinlock n x γx γe k L)
                  ∗ (⤉ isSpinlockUse1 n k γ γx P l)
                  ∗ (⤉ Duty(tid) ds)
                  ∗ ◇{ds@1}(2 + L, 1)
                  ∗ ◇[k](1 + l, 1)
               )%S), 1+n⟧⧽
              (OMod.close_itree Client (SCMem.mod gvs) (Spinlock.lock x))
              ⧼rv, ⟦(∃ (γu u : τ{nat, 1+n}),
                        (⤉ EX γe tt)
                          ∗ (⤉ P)
                          ∗ (⤉ ○ γ (γu, u))
                          ∗ (⤉ Duty(tid) ((u, 0, (▿ γu true)) :: ds))
                          ∗ ◇[u](l, 1))%S, 1+n⟧⧽
    .
    Proof.
      iIntros (? ? ? ? ? ? ? ? ?).
      iStartTriple. iIntros "PRE POST".
      iPoseProof ((Spinlock_lock_spec tid n E) $! x γx γe k L) as "SPEC".
      iEval (red_tl; rewrite red_syn_tgt_interp_as; simpl) in "PRE".
      iDestruct "PRE" as "(#MEM & #ISL & #ISLU1 & DUTY & PCS & PCk)".

      set (P0 := (◇[k](1+l, 1))%S : sProp n).
      set (R0 := (Duty(tid) ds ∗ ◇[k](1+l, 1))%S : sProp n).
      set (Q0 := (∃ (γu u : τ{nat, n}),
                       (P)
                       ∗ (○ γ (γu, u))
                       ∗ (Duty(tid) ((u, 0, (▿ γu true)) :: ds))
                       ∗ (◇[u](l, 1)))%S : sProp n).
      iSpecialize ("SPEC" $! ds P0 R0 Q0 1).
      iApply ("SPEC" with "[DUTY PCS PCk] [POST]").

      - (* PRE. *)
        iEval red_tl_all. iSplitR. eauto. iSplitR. eauto.
        iSplitL "PCk".
        { subst P0. iEval (red_tl; simpl). done. }
        iSplitL "DUTY PCS". iFrame.
        iSplitR.
        { (* ELI. *)
          iModIntro. iExists emp%S. iEval (simpl; red_tl). iSplitR. eauto.
          iIntros "[_ FC]". iEval (rewrite red_syn_inv; rewrite red_syn_fupd). iIntros "(#INV_SL & INV_SL_CLOSE & SLI)".
          iPoseProof (isSpinlockUse1_get_data with "ISLU1") as "[%GTl INV_SLU1]".
          iInv "INV_SLU1" as "SLU1" "INV_SLU1_CLOSE". iEval (simpl; unfold spinlockUse1; red_tl_all) in "SLU1".
          iDestruct "SLU1" as "[%γu SLU1]". iEval (red_tl) in "SLU1".
          iDestruct "SLU1" as "[%u SLU1]". iEval (red_tl_all; simpl) in "SLU1". iDestruct "SLU1" as "(TKB & SLU1)".
          iEval (unfold spinlockInv; red_tl_all) in "SLI". iDestruct "SLI" as "[(PTx & Lx & EX) | (PTx & Lx)]".
          - (* Target state. *)
            iDestruct "SLU1" as "[(Lxw & TKW & PP) | (Lxw & _)]".
            2:{ iExFalso. iPoseProof (AuthExcls.b_w_eq with "Lx Lxw") as "%F". inv F. }
            iMod ("INV_SLU1_CLOSE" with "[TKB Lxw TKW PP]") as "_".
            { iEval (unfold spinlockUse1; simpl; red_tl_all; simpl). iExists _. iEval (red_tl_all). iExists _.
              iEval (red_tl_all; simpl). iSplitL "TKB". iFrame. iLeft. iFrame.
            }
            iModIntro. do 2 iRight. iSplitR. eauto. iEval red_tl_all. iFrame.
          - (* Live case. *)
            iDestruct "SLU1" as "[(Lxw & _) | (Lxw & LIVE & #PROM & #LINK)]".
            { iExFalso. iPoseProof (AuthExcls.b_w_eq with "Lx Lxw") as "%F". inv F. }
            iMod (tpromise_progress with "[PROM FC]") as "[PC | #DEAD]".
            { iFrame. iApply "PROM". }
            2:{ iExFalso. iEval (simpl; red_tl_all) in "DEAD". iPoseProof (OneShots.pending_not_shot with "LIVE DEAD") as "%F". ss. }
            iMod (link_amplify with "[PC]") as "PC".
            { iFrame. iApply "LINK". }
            iMod ("INV_SLU1_CLOSE" with "[TKB Lxw LIVE]") as "_".
            { iEval (unfold spinlockUse1; simpl; red_tl_all; simpl). iExists _. iEval (red_tl_all). iExists _.
              iEval (red_tl_all; simpl). iSplitL "TKB". iFrame. iRight. iFrame. iSplit; eauto.
            }
            iModIntro. iLeft. iSplitR "PC"; iFrame. iSplitR. auto.
            iEval (unfold spinlockInv; red_tl_all). iRight. iFrame.
        }
        iSplitR.
        { (* Atomic Update. *)
          subst R0 Q0. iEval (red_tl_all; simpl). iIntros "(Lx & DUTY & PCk)".
          iPoseProof (isSpinlockUse1_get_data with "ISLU1") as "[%GTl INV_SLU1]".
          iInv "INV_SLU1" as "SLU1" "INV_SLU1_CLOSE". iEval (simpl; unfold spinlockUse1; red_tl_all) in "SLU1".
          iDestruct "SLU1" as "[%γu SLU1]". iEval (red_tl) in "SLU1".
          iDestruct "SLU1" as "[%u SLU1]". iEval (red_tl_all; simpl) in "SLU1". iDestruct "SLU1" as "(TKB & SLU1)".
          iDestruct "SLU1" as "[(Lxw & TKW & PP) | (Lxw & _)]".
          2:{ iExFalso. iPoseProof (AuthExcls.b_w_eq with "Lx Lxw") as "%F". ss. }
          iMod (alloc_obligation l 2) as "(%k1 & #LO1 & PC1)".
          iMod (OneShots.alloc) as "[%γk1 LIVE1]".
          iEval (replace 2 with (1+1) by lia) in "PC1".
          iPoseProof (pc_split with "PC1") as "[PC1 PC_POST]".
          iMod (pc_mon _ 1 _ 1 _ _ with "PC1") as "PC1". Unshelve.
          2:{ apply layer_drop_eq; auto. }
          iMod (duty_add _ _ _ _ 0 ((▿ γk1 true)%S : sProp n) with "[DUTY PC1] []") as "DUTY".
          { iFrame. }
          { iModIntro. iEval (simpl; red_tl_all). auto. }
          iPoseProof (duty_tpromise with "DUTY") as "#PROM1".
          { simpl. left. auto. }
          iMod (link_new k1 k l 0 0 with "[PCk]") as "[#LINK1 _]".
          { iFrame. eauto. }
          iMod (AuthExcls.b_w_update _ _ _ (γk1, k1) with "TKB TKW") as "[TKB TKW]".
          iMod (AuthExcls.b_w_update _ _ _ 1 with "Lx Lxw") as "[Lx Lxw]".
          iMod ("INV_SLU1_CLOSE" with "[TKB Lxw LIVE1]") as "_".
          { iEval (unfold spinlockUse1; simpl; red_tl_all; simpl). iExists _. iEval (red_tl_all). iExists _.
            iEval (red_tl_all; simpl). iSplitL "TKB". iFrame. iRight. iFrame. iSplit; eauto.
          }
          iModIntro. iFrame. iExists _. iEval (red_tl; simpl). iExists _. iEval (red_tl_all; simpl). iFrame.
        }
        iSplitR.
        { (* Put Duty. *)
          iModIntro. subst P0 R0. iEval (red_tl_all; simpl). iIntros "[A B]". iModIntro. iFrame.
        }
        { (* Get Duty. *)
          iModIntro. subst P0 R0. iEval (red_tl_all; simpl). iIntros "[A B]". iModIntro. iFrame.
        }

      - (* POST. *)
        iIntros (rv) "A". iEval (red_tl_all; simpl) in "A". iDestruct "A" as "[Q EX]". iApply "POST". subst Q0.
        iEval (red_tl; simpl) in "Q". iDestruct "Q" as "[%γu Q]". iEval (red_tl; simpl) in "Q". iDestruct "Q" as "[%u Q]".
        iEval (red_tl_all; simpl) in "Q". iDestruct "Q" as "(P & TKW & DUTY & PCu)".
        iEval (red_tl; simpl). iExists γu. iEval (red_tl; simpl). iExists u. iEval (red_tl_all; simpl).
        iFrame.

    Qed.

    Lemma Spinlock_unlock_spec_use1
          tid n
          (E : coPset)
          (TOP : ⊤ ⊆ E)
      :
      ⊢ ∀ x γx γe k L γ (P : sProp n) l (ds : list (nat * nat * sProp n)) γu u,
          [@ tid, n, E @]
            ⧼⟦(((syn_tgt_interp_as n sndl (fun m => (s_memory_black m)))
                  ∗ (⤉ isSpinlock n x γx γe k L)
                  ∗ (⤉ isSpinlockUse1 n k γ γx P l)
                  ∗ (⤉ EX γe tt)
                  ∗ (⤉ P)
                  ∗ (⤉ ○ γ (γu, u))
                  ∗ (⤉ Duty(tid) ((u, 0, (▿ γu true)) :: ds))
                  ∗ ◇{((u, 0, (▿ γu true)) :: ds)@1}(1, 1)
               )%S), 1+n⟧⧽
              (OMod.close_itree Client (SCMem.mod gvs) (Spinlock.unlock x))
              ⧼rv, ⟦((⤉ Duty(tid) ds))%S, 1+n⟧⧽
    .
    Proof.
      iIntros (? ? ? ? ? ? ? ? ? ? ?).
      iStartTriple. iIntros "PRE POST".
      iPoseProof ((Spinlock_unlock_spec tid n E) $! x γx γe k L) as "SPEC".
      iEval (red_tl; rewrite red_syn_tgt_interp_as; simpl) in "PRE".
      iDestruct "PRE" as "(#MEM & #ISL & #ISLU1 & EX & P & TKW & DUTY & PCS)".

      set (P0 := (P ∗ (○ γ (γu, u)))%S : sProp n).
      set (R0 := (P ∗ (○ γ (γu, u)) ∗ (Duty(tid) ((u, 0, (▿ γu true)) :: ds)))%S : sProp n).
      set (Q0 := (Duty(tid) ds)%S : sProp n).
      iSpecialize ("SPEC" $! ((u, 0, (▿ γu true)%S) :: ds) P0 R0 Q0).
      iApply ("SPEC" with "[EX P TKW DUTY PCS] [POST]").

      - (* PRE. *)
        iEval red_tl_all. iSplitR. eauto. iSplitR. eauto.
        iSplitL "P TKW".
        { subst P0. iEval (red_tl; simpl). iFrame. }
        iSplitL "EX".
        { iEval (red_tl_all) in "EX". iFrame. }
        iSplitL "DUTY PCS". iFrame.
        iSplitR.
        { (* Atomic update. *)
          subst R0. iEval (red_tl_all; simpl). iIntros "(Lx & P & TKW & DUTY)".
          iPoseProof (isSpinlockUse1_get_data with "ISLU1") as "[%GTl INV_SLU1]".
          iInv "INV_SLU1" as "SLU1" "INV_SLU1_CLOSE". iEval (simpl; unfold spinlockUse1; red_tl_all) in "SLU1".
          iDestruct "SLU1" as "[%γu1 SLU1]". iEval (red_tl) in "SLU1".
          iDestruct "SLU1" as "[%u1 SLU1]". iEval (red_tl_all; simpl) in "SLU1". iDestruct "SLU1" as "(TKB & SLU1)".
          iDestruct "SLU1" as "[(Lxw & _) | (Lxw & LIVE & _)]".
          { iExFalso. iPoseProof (AuthExcls.b_w_eq with "Lx Lxw") as "%F". inv F. }
          iPoseProof (AuthExcls.b_w_eq with "TKB TKW") as "%EQu". clarify.
          iMod (AuthExcls.b_w_update _ _ _ 0 with "Lx Lxw") as "[Lx Lxw]".
          iMod ("INV_SLU1_CLOSE" with "[TKB Lxw TKW P]") as "_".
          { iEval (unfold spinlockUse1; simpl; red_tl_all; simpl). iExists _. iEval (red_tl_all). iExists _.
            iEval (red_tl_all; simpl). iSplitL "TKB". iFrame. iLeft. iFrame.
          }
          subst Q0. iEval (red_tl; simpl).
          iMod (OneShots.pending_shot with "LIVE") as "#DEAD".
          iMod (duty_fulfill with "[DUTY DEAD]") as "DUTY".
          { iSplitL "DUTY". iFrame. iEval (simpl; red_tl_all). eauto. }
          iModIntro. iFrame.
        }
        iSplitR.
        { (* Put Duty. *)
          iModIntro. subst P0 R0. iEval (red_tl_all; simpl). iIntros "((A & B) & C)". iModIntro. iFrame.
        }
        { (* Get Duty. *)
          iModIntro. subst P0 R0. iEval (red_tl_all; simpl). iIntros "(A & B & C)". iModIntro. iFrame.
        }

      - (* POST. *)
        iIntros (rv) "Q". iApply "POST". subst Q0.
        iEval (red_tl; simpl) in "Q". iEval (red_tl; simpl). iFrame.

    Qed.

  End SPEC1.

End SPEC.
Global Opaque Spinlock.lock Spinlock.unlock.
