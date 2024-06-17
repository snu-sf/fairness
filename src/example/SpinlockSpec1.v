From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Import pind Axioms ITreeLib Red TRed IRed2 WFLibLarge.
From Fairness Require Import FairBeh Mod Linking.
From Fairness Require Import Spinlock.
From Fairness Require Import PCM IProp IPM IPropAux.
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
  (* Context {HasOneShots : @GRA.inG (OneShots.t unit) Γ}. *)
  (* Context {HasAuthExcls1 : @GRA.inG (AuthExcls.t (nat * nat)) Γ}. *)
  Context {HasAuthExcls : @GRA.inG (AuthExcls.t nat) Γ}.

  Ltac red_tl_all := red_tl; red_tl_memra; red_tl_authexcls.
  (* Ltac red_tl_all := red_tl; red_tl_memra; red_tl_oneshots; red_tl_authexcls. *)

  (** Invariants. *)
  Definition spinlockInv (n : nat) (x : SCMem.val) (γx : nat)
    : sProp n :=
    (((x ↦ 0) ∗ (● γx 0)) ∨ ((x ↦ 1) ∗ (● γx 1)))%S.

  (* Definition spinlockInv (n : nat) (γ : nat) (x : SCMem.val) (P : sProp n) (k l : nat) *)
  (*   : sProp n := *)
  (*   ((∃ (γu u : τ{nat}), *)
  (*        (● γ (γu, u)) *)
  (*          ∗ *)
  (*          (((x ↦ 0) ∗ (○ γ (γu, u)) ∗ P) *)
  (*           ∨ ((x ↦ 1) ∗ (△ γu 1) ∗ (-[u](0)-◇ (▿ γu tt)) ∗ (u -(0)-◇ k)))) *)
  (*   )%S. *)
  (* Definition spinlockInv (n : nat) (γ : nat) (x : SCMem.val) (P : sProp n) (k l : nat) *)
  (*   : sProp n := *)
  (*   ((∃ (γu u : τ{nat}), *)
  (*        (● γ (γu, u)) *)
  (*          ∗ *)
  (*          (((x ↦ 0) ∗ ◇[k](1 + l, 1) ∗ (○ γ (γu, u)) ∗ P) *)
  (*           ∨ ((x ↦ 1) ∗ (△ γu 1) ∗ (-[u](0)-◇ (▿ γu tt)) ∗ (u -(0)-◇ k)))) *)
  (*   )%S. *)

  (* Namespace for Spinlock invariants. *)
  Definition N_Spinlock : namespace := (nroot .@ "Spinlock").
  Notation E_Spinlock := (↑N_Spinlock : coPset).

  Definition isSpinlock n (x : SCMem.val) (γx : nat) (k L : nat)
    : sProp n :=
    (◆[k, L] ∗ syn_inv n N_Spinlock (spinlockInv n x γx))%S.

  Global Instance isSpinlock_persistent n x γx k L :
    Persistent (⟦isSpinlock n x γx k L, n⟧).
  Proof.
    unfold Persistent. iIntros "H". unfold isSpinlock. red_tl.
    rewrite red_syn_inv. iDestruct "H" as "#H". auto.
  Qed.

  (* Lemma mask_disjoint_spinlock_state_tgt : ↑N_Spinlock1 ## (↑N_state_tgt : coPset). *)
  (* Proof. apply ndot_ne_disjoint. ss. Qed. *)

  (* Lemma make_isSpinlock *)
  (*       n γ x P γk k L l (LT : 0 < l) *)
  (*       (q : Qp) (γu u : nat) Es *)
  (*   : *)
  (*   ⊢ *)
  (*     ⟦((x ↦ 0) ∗ ➢(auexa_b γ (q, γu, u)) ∗ ➢(auexa_w γ (q, γu, u)) ∗ (⤉P) ∗ ◆[k, L] ∗ ◇[k](1+l, 1))%S, 1+n⟧ *)
  (*       -∗ *)
  (*       ⟦( =|1+n|={Es}=> (⤉(isSpinlock n γ x P γk k L l)))%S, 1+n⟧. *)
  (* Proof. *)
  (*   red_tl. simpl. iIntros "(PT & BQ & WQ & P & #LO & PC)". *)
  (*   rewrite red_syn_fupd. red_tl. *)
  (*   iMod ((FUpd_alloc _ _ _ n (↑(N_Spinlock.@"a")) (spinlockInv n γ x P γk k l)) *)
  (*          with "[PT BQ WQ P PC]") as "#SINV". *)
  (*   auto. *)
  (*   { simpl. unfold spinlockInv. red_tl. iLeft. iExists q. red_tl. iExists γu. red_tl. iExists u. *)
  (*     red_tl. iSplitL "BQ". iFrame. iLeft. iFrame. *)
  (*   } *)
  (*   iModIntro. unfold isSpinlock. red_tl. *)
  (*   iExists (↑(N_Spinlock.@"a")). red_tl. iSplit. *)
  (*   { iPureIntro. apply nclose_subseteq. } *)
  (*   simpl. rewrite red_syn_inv. auto. *)
  (* Qed. *)

  (* Lemma init_isSpinlock *)
  (*       n x P γk k L l (LT : 0 < l) *)
  (*       Es *)
  (*   : *)
  (*   ⊢ *)
  (*     ⟦(➢(auexa) ∗ (x ↦ 0) ∗ (⤉P) ∗ ◆[k, L] ∗ ◇[k](1+l, 1))%S, 1+n⟧ *)
  (*       -∗ *)
  (*       ⟦( =|1+n|={Es}=> (➢(auexa) ∗ ∃ (γ : τ{nat}), ⤉(isSpinlock n γ x P γk k L l)))%S, 1+n⟧. *)
  (* Proof. *)
  (*   red_tl. simpl. iIntros "(AEA & PT & P & #LO & PC)". *)
  (*   rewrite red_syn_fupd. red_tl. *)
  (*   iMod (auexa_alloc_gt _ ((1%Qp, 0, 0)) with "AEA") as "[AEA (%γ & BQ & BW)]". *)
  (*   iPoseProof (make_isSpinlock n γ x P γk k L l with "[PT BQ BW P PC]") as "ISL". *)
  (*   auto. *)
  (*   { red_tl. iFrame. iApply "LO". } *)
  (*   iEval (rewrite red_syn_fupd) in "ISL". iMod "ISL". *)
  (*   iModIntro. iSplitL "AEA". iFrame. iExists γ. iFrame. *)
  (* Qed. *)

  (* Lemma update_isSpinlock *)
  (*       n γ x P γk k L l *)
  (*       Es *)
  (*       (MASK_SL : mask_has_Spinlock Es n) *)
  (*       γk' k' L' l' (LT' : 0 < l') *)
  (*   : *)
  (*   ⊢ ⟦((⤉(isSpinlock n γ x P γk k L l)) ∗ ➢(live γk k 1) ∗ ◆[k', L'] ∗ ◇[k'](1+ l', 1))%S, 1+n⟧ *)
  (*      -∗ *)
  (*      ⟦( =|1+n|={Es}=>((⤉ isSpinlock n γ x P γk' k' L' l') ∗ ➢(dead γk k)))%S, 1+n⟧. *)
  (* Proof. *)
  (*   red_tl. simpl. iIntros "(ISL & LIVE & LO' & PC')". rewrite red_syn_fupd. red_tl. *)
  (*   iEval (unfold isSpinlock) in "ISL". red_tl. *)
  (*   iDestruct "ISL" as "[%N ISL]". iEval red_tl in "ISL". *)
  (*   iDestruct "ISL" as "(%IN & _ & %LT & SI)". rewrite red_syn_inv. *)
  (*   iInv "SI" as "SI" "K". *)
  (*   { unfold mask_has_Spinlock in MASK_SL. des_ifs. set_solver. } *)
  (*   simpl. iEval (unfold spinlockInv; red_tl) in "SI". *)
  (*   iDestruct "SI" as "[[%q SI] | DEAD]". *)
  (*   2:{ iExFalso. simpl. iPoseProof (Lifetime.pending_not_shot with "LIVE DEAD") as "F". auto. } *)
  (*   red_tl. iDestruct "SI" as "[%γu SI]". red_tl. iDestruct "SI" as "[%u SI]". *)
  (*   red_tl. iDestruct "SI" as "[BQ [(PT & _ & WQ & P) | (_ & LIVE2 & _)]]". *)
  (*   2:{ iPoseProof (Lifetime.pending_merge with "LIVE LIVE2") as "LIVE". *)
  (*       iPoseProof (Lifetime.pending_wf with "LIVE") as "%S". exfalso. *)
  (*       eapply Qp_add_lt_one. eauto. *)
  (*   } *)
  (*   iMod (Lifetime.pending_shot with "LIVE") as "#DEAD". iMod ("K" with "[DEAD]") as "_". *)
  (*   { unfold spinlockInv. red_tl. iRight. eauto. } *)
  (*   iPoseProof (make_isSpinlock n γ x P γk' k' L' l' LT' with "[PT BQ WQ P LO' PC']") as "ISL". *)
  (*   { red_tl. iFrame. } *)
  (*   rewrite red_syn_fupd. iMod "ISL". iModIntro. iFrame. auto. *)
  (* Qed. *)

  Lemma isSpinlock_get_data n x γx k L :
    (⟦isSpinlock n x γx k L, n⟧) -∗ (◆[k, L] ∗ inv n N_Spinlock (spinlockInv n x γx)).
  Proof.
    iEval (unfold isSpinlock; red_tl). iIntros "[LO INV]". eauto.
  Qed.

  Lemma Spinlock_lock_spec
        tid n
        (E : coPset)
    :
    ⊢ ∀ x γx k L v (ds : list (nat * nat * sProp n)) (P R Q : sProp n),
        [@ tid, n, E @]
          ⧼(tgt_interp_as (state_tgt:=st_tgt_type) sndl (fun m => ((s_memory_black m) : sProp n)%S))
             ∗ (⟦isSpinlock n x γx k L, n⟧)
             ∗ (⟦P, n⟧)
             ∗ (⟦Duty(tid) ds, n⟧ ∗ ◇{List.map fst ds}(2 + L, 1))
             ∗ (env_live_inv v (1+n) (⊤ ∖ E_Spinlock) k
                             (((⤉ syn_inv n N_Spinlock (spinlockInv n x γx))
                                 ∗ ((⤉ spinlockInv n x γx) =|1+n|={⊤ ∖ E_Spinlock, ⊤}=∗ emp)
                                 ∗ (⤉ spinlockInv n x γx)) : sProp (1+n))%S
                             (((⤉ syn_inv n N_Spinlock (spinlockInv n x γx))
                                 ∗ ((⤉ spinlockInv n x γx) =|1+n|={⊤ ∖ E_Spinlock, ⊤}=∗ emp)
                                 ∗ (⤉ ((x ↦ 0) ∗ (● γx 0)))) : sProp (1+n))%S
               )
             ∗ (⟦((● γx 0) ∗ R)%S, n⟧ =|1+n|={⊤ ∖ E_Spinlock}=∗ ⟦((● γx 1) ∗ Q)%S, n⟧)
             ∗ (□((⟦P, n⟧ ∗ ⟦Duty(tid) ds, n⟧) =|1+n|={E, ⊤}=∗ ⟦R, n⟧))
             ∗ (□(⟦R, n⟧ =|1+n|={⊤, E}=∗ (⟦P, n⟧ ∗ ⟦Duty(tid) ds, n⟧)))
          ⧽
            (OMod.close_itree Client (SCMem.mod gvs) (Spinlock.lock x))
            ⧼rv, ⟦Q, n⟧⧽
  .
  Proof.
    iIntros (? ? ? ? ? ? ? ? ?).
    iStartTriple. iIntros "PRE POST". unfold Spinlock.lock.
    (* Preprocess for induction: right after the cas call's yield. *)
    iEval (rewrite unfold_iter_eq). rred2r.
    iDestruct "PRE" as "(#MEM & #ISL & P & [DUTY PCS] & #ELI & AU & #PUT_D & #GET_D)".
    iMod (ccs_make _ _ _ 1 (100+v) with "[PCS]") as "[CCS PCS]".
    { iFrame. iEval (unfold isSpinlock; red_tl) in "ISL". iDestruct "ISL" as "[LO _]". eauto. }
    iMod (pcs_drop_le _ _ _ _ 1 with "PCS") as "PCS".
    lia.
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
      iDestruct "SL" as "[(PTx & Lx) | (PTx & Lx)]"; cycle 1.

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
        iApply "POST". iFrame.

    - (* Terminating case. *)
      iIntros "T". iEval (simpl; red_tl_all; rewrite red_syn_inv; rewrite red_syn_fupd) in "T".
      iDestruct "T" as "(_ & INV_SL_CLOSE & PTx & Lx)".
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
      iApply "POST". iFrame.

      Unshelve. lia.
  Qed.

End SPEC.
Global Opaque Spinlock.lock Spinlock.unlock.
