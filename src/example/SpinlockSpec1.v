From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Import pind Axioms ITreeLib Red TRed IRed2 WFLibLarge.
From Fairness Require Import FairBeh Mod Linking.
From Fairness Require Import Spinlock.
From Fairness Require Import PCM IPM IPropAux.
From Fairness Require Import IndexedInvariants OpticsInterp SimWeakest.
From Fairness Require Import TemporalLogic SCMemSpec SpinlockSpec.
From Fairness Require Import AuthExclsRA ExclsRA.
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

  Context {HasOneShots : @GRA.inG (OneShots.t unit) Γ}.
  Context {HasAuthExcls2 : @GRA.inG (AuthExcls.t (nat * nat)) Γ}.

  Ltac red_tl_all := red_tl; red_tl_memra; red_tl_authexcls; red_tl_excls; red_tl_oneshots.

  Definition spinlockUse1 (n : nat) k (γ γx : nat) (P : sProp n) (l : nat)
    : sProp n :=
    (∃ (γu u : τ{nat}),
        (●G γ (γu, u))
          ∗
          (((○G γx 0) ∗ (○G γ (γu, u)) ∗ P)
           ∨ ((○G γx 1) ∗ (△ γu 1) ∗ (-[u](0)-◇ (▿ γu tt)) ∗ (u -(0)-◇ k)))
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
                ∗ ◇{ds@1}(2 + L, 2)
                ∗ ◇[k](1 + l, 1)
             )%S), 1+n⟧⧽
            (OMod.close_itree Client (SCMem.mod gvs) (Spinlock.lock x))
            ⧼rv, ⟦(∃ (γu u : τ{nat, 1+n}),
                      (⤉ EX γe tt)
                        ∗ (⤉ P)
                        ∗ (⤉ ○G γ (γu, u))
                        ∗ (⤉ Duty(tid) ((u, 0, (▿ γu tt)) :: ds))
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
                     ∗ (○G γ (γu, u))
                     ∗ (Duty(tid) ((u, 0, (▿ γu tt)) :: ds))
                     ∗ (◇[u](l, 1)))%S : sProp n).
    iSpecialize ("SPEC" $! ds P0 R0 Q0 0).
    iApply ("SPEC" with "[DUTY PCS PCk] [POST]").

    - (* PRE. *)
      iEval red_tl_all. iSplitR. eauto. iSplitR. eauto.
      iSplitL "PCk".
      { subst P0. iEval (red_tl; simpl). done. }
      iSplitL "DUTY PCS". iFrame.
      iSplitR.
      { (* ELI. *)
        iModIntro. iEval (simpl; red_tl). iIntros "FC".
        iEval (rewrite red_syn_inv; rewrite red_syn_fupd). iIntros "(#INV_SL & INV_SL_CLOSE & SLI)".
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
          iModIntro. iRight. iSplitR. eauto. iEval red_tl_all. iFrame.
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
          iModIntro. iLeft. iSplitR "PC"; iFrame.
          { iSplitR. auto. iEval (unfold spinlockInv; red_tl_all). iRight. iFrame. }
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
        iMod (alloc_obligation l 2) as "(%k1 & #LO1 & PC1 & PPk1)".
        iMod (OneShots.alloc) as "[%γk1 LIVE1]".
        iEval (replace 2 with (1+1) by lia) in "PC1".
        iPoseProof (pc_split with "PC1") as "[PC1 PC_POST]".
        iMod (pc_mon _ 1 _ 1 _ _ with "PC1") as "PC1". Unshelve.
        2:{ apply layer_drop_eq; auto. }
        iEval (rewrite <- (Qp.div_2 1)) in "PPk1".
        iPoseProof (pending_split with "PPk1") as "[PPk1 PPk2]".
        iMod (duty_add _ _ _ _ 0 ((▿ γk1 tt)%S : sProp n) with "[DUTY PC1 PPk2] []") as "DUTY".
        { iFrame. }
        { iModIntro. iEval (simpl; red_tl_all). auto. }
        iPoseProof (duty_delayed_tpromise with "DUTY") as "#DPROM1".
        { simpl. left. auto. }
        iMod (activate_tpromise with "DPROM1 PPk1") as "[#PROM1 #SHOTk]".
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
                ∗ (⤉ ○G γ (γu, u))
                ∗ (⤉ Duty(tid) ((u, 0, (▿ γu tt)) :: ds))
                ∗ ◇{((u, 0, (▿ γu tt)) :: ds)@1}(1, 1)
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

    set (P0 := (P ∗ (○G γ (γu, u)))%S : sProp n).
    set (R0 := (P ∗ (○G γ (γu, u)) ∗ (Duty(tid) ((u, 0, (▿ γu tt)) :: ds)))%S : sProp n).
    set (Q0 := (Duty(tid) ds)%S : sProp n).
    iSpecialize ("SPEC" $! ((u, 0, (▿ γu tt)%S) :: ds) P0 R0 Q0).
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
        iDestruct "SLU1" as "[(Lxw & _) | (Lxw & LIVE & PROM & _)]".
        { iExFalso. iPoseProof (AuthExcls.b_w_eq with "Lx Lxw") as "%F". inv F. }
        iPoseProof (unfold_tpromise with "PROM") as "[_ #ACT]".
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

End SPEC.
