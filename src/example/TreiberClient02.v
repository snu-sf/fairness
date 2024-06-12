From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Import pind Axioms ITreeLib Red TRed IRed2 WFLibLarge.
From Fairness Require Import FairBeh Mod Concurrency Linking.
From Fairness Require Import PCM IProp IPM IPropAux.
From Fairness Require Import IndexedInvariants OpticsInterp SimWeakest.
From Fairness Require Import TemporalLogic SCMemSpec AuthExclAnysRA TreiberStack.

Module TreiberClient2.

  Definition gvs : list nat := [2].
  Definition s : SCMem.val := SCMem.val_ptr (0, 0).

  Section CODE.

    Definition state := unit.
    Definition ident := void.

    Definition thread_push :
      ktree (threadE ident state) unit unit
      := fun _ =>
      _ <- (trigger Yield;;; TreiberStack.push (s,SCMem.val_nat 1));;
      Ret tt.

    Definition thread_pop :
      ktree (threadE ident state) unit (option (SCMem.val))
      := fun _ =>
      ov1 <- (trigger Yield;;; TreiberStack.pop s);;
      Ret ov1.

    Definition omod : Mod.t :=
      Mod.mk
        tt
        (Mod.get_funs [("thread_push", Mod.wrap_fun thread_push);
                       ("thread_pop", Mod.wrap_fun thread_pop)])
    .

    Definition module : Mod.t :=
      OMod.close
        (omod)
        (SCMem.mod gvs)
    .

  End CODE.

End TreiberClient2.

Section SPEC.

  Context {src_state : Type}.
  Context {src_ident : Type}.
  Notation tgt_state := (Mod.state TreiberClient2.module).
  Notation tgt_ident := (Mod.ident TreiberClient2.module).

  Local Instance STT : StateTypes := Build_StateTypes src_state tgt_state src_ident tgt_ident.
  Context `{sub : @SRA.subG Γ Σ}.
  Context {TLRASs : TLRAs_small STT Γ}.
  Context {TLRAS : TLRAs STT Γ Σ}.

  Context {HasMemRA: @GRA.inG memRA Γ}.
  Context {HasAuthExclAnysRA : @GRA.inG AuthExclAnysRA Γ}.

  Ltac red_tl_all := red_tl; red_tl_memra; red_tl_auexa.

  Import TreiberClient2.

  (** Invariants. *)

  (* Namespace for TreiberClient2 invariants. *)
  Definition N_TreiberClient2 : namespace := (nroot .@ "Treiber" .@ "TreiberClient2").

  Definition Client2StackState n γs γtok : sProp n :=
    ((○ γs [SCMem.val_nat 1] ∗ ● γtok tt)∨ ○ γs ([] : list SCMem.val))%S.

  Definition C2Inv n γs γtok : sProp n :=
    (syn_inv n N_TreiberClient2 (Client2StackState n γs γtok))%S.

  Global Instance C2Inv_persistent n γs γtok : Persistent ⟦C2Inv n γs γtok, n⟧.
  Proof.
    unfold Persistent. iIntros "H". unfold C2Inv. rewrite red_syn_inv.
    iDestruct "H" as "#H". auto.
  Qed.

  (** Simulation proof. *)

  Lemma TreiberClient2_push_spec tid n :
    ⊢ ∀ γs γtok (L : τ{nat, 1+n}) (ds : list (nat * nat * sProp n)),
    [@ tid, n, ⊤ @]
      ⧼⟦(
        (syn_tgt_interp_as n sndl (fun m => s_memory_black m)) ∗
        (⤉ IsTreiber n s γs) ∗
        (⤉ C2Inv n γs γtok) ∗
        (⤉ ● γtok tt) ∗
        (⤉ Duty(tid) ds) ∗
        ◇{ds@1}(2+L, 2)
        )%S, 1+n⟧⧽
        (OMod.close_itree omod (SCMem.mod gvs) (thread_push tt))
        ⧼_, ⟦(⤉ Duty(tid) ds)%S, 1+n⟧⧽
  .
  Proof.
    iIntros. iStartTriple. unfold C2Inv.
    red_tl_all. simpl. rewrite red_syn_tgt_interp_as;
    rewrite red_syn_inv. simpl.
    iIntros "(#Mem & #IsTreiber & #C2Inv & Tok & Duty & Pcs)".
    simpl.
    iMod (pcs_decr _ _ 1 1 with "Pcs") as "[Pcs PcsPush]"; [lia|].
    iMod (pcs_drop _ _ _ _ 1 100 with "Pcs") as "Pcs"; [lia|].
    Unshelve. 2:lia.
    iIntros "Post". unfold thread_push. rred.
    iApply (wpsim_yieldR2 with "[$Duty $Pcs]"); [lia..|].
    iIntros "Duty _ Pcs". rred2r.
    iApply wpsim_tauR. rred2r.
    iApply (Treiber_push_spec _ (λ v, ⌜ True ⌝)%S with "[Duty PcsPush Tok] [-]"); [ss..| |].
    { red_tl_all. rewrite red_syn_tgt_interp_as. iSplit; [eauto|]. iSplitR; [iFrame "#"|].
      iFrame. iIntros (s_st). red_tl_all. iIntros "[TStackInv _]".
      rewrite red_syn_fupd. red_tl_all.
      iInv "C2Inv" as "TStackC" "CloseC2Inv".
      iEval (unfold Client2StackState; simpl; red_tl_all; simpl) in "TStackC".
      (* Prove that the stack is empty. *)
      iDestruct "TStackC" as "[[TStackC Tok'] | TStackC]".
      { by iDestruct (auexa_b_b_false with "Tok Tok'") as %?. }
      iDestruct (auexa_b_w_eq with "TStackInv TStackC") as "%EQ".
      subst s_st.
      iMod (auexa_b_w_update with "TStackInv TStackC") as "[TStackInv TStackC]".
      iMod ("CloseC2Inv" with "[TStackC Tok]") as "_".
      { iEval (unfold Client2StackState; simpl; red_tl_all; simpl).
        iLeft. iFrame.
      }
      iModIntro. iFrame.
    }
    iEval (red_tl_all;simpl). iIntros (_) "[_ Duty]".
    rred2r.
    iApply "Post". iFrame.
  Qed.

  Lemma TreiberClient2_pop_spec tid n :
    ⊢ ∀ γs γtok (L : τ{nat, 1+n}) (ds : list (nat * nat * sProp n)),
    [@ tid, n, ⊤ @]
      ⧼⟦(
        (syn_tgt_interp_as n sndl (fun m => s_memory_black m)) ∗
        (⤉ IsTreiber n s γs) ∗
        (⤉ C2Inv n γs γtok) ∗
        (⤉ Duty(tid) ds) ∗
        ◇{ds@1}(2+L, 2)
        )%S, 1+n⟧⧽
        (OMod.close_itree omod (SCMem.mod gvs) (thread_pop tt))
      ⧼rv, ⟦(
        ⌜ if rv is Some v then
            v = SCMem.val_nat 1
          else
            True ⌝ ∗
        (⤉ Duty(tid) ds)
        )%S, 1+n⟧⧽
  .
  Proof.
    iIntros. iStartTriple. unfold C2Inv.
    red_tl_all. simpl. rewrite red_syn_tgt_interp_as; rewrite red_syn_inv; simpl.
    iIntros "(#Mem & #IsTreiber & #C2Inv & Duty & Pcs)".
    iMod (pcs_decr _ _ 1 1 with "Pcs") as "[Pcs PcsPush]"; [lia|].
    iMod (pcs_drop _ _ _ _ 1 100 with "Pcs") as "Pcs"; [lia|].
    Unshelve. 2:lia.
    iIntros "Post". unfold thread_pop. rred.
    iApply (wpsim_yieldR2 with "[$Duty $Pcs]"); [lia..|].
    iIntros "Duty _ Pcs". rred2r. iApply wpsim_tauR. rred2r.
    iApply (Treiber_pop_spec _ (λ ov, ⌜ if ov is Some v then v = 1 else True ⌝)%S with "[Duty PcsPush] [-]"); [ss..| |].
    { red_tl_all. rewrite red_syn_tgt_interp_as. iSplit; [eauto|]. iSplitR; [iFrame "#"|].
      iFrame. iIntros (s_st). red_tl_all. iIntros "[TStackInv _]".
      rewrite red_syn_fupd. red_tl_all.
      iInv "C2Inv" as "TStackC" "CloseC2Inv".
      iEval (unfold Client2StackState; simpl; red_tl_all; simpl) in "TStackC".
      (* Case analysis on the current state of the stack. *)
      iDestruct "TStackC" as "[[TStackC Tok] | TStackC]".
      all: iDestruct (auexa_b_w_eq with "TStackInv TStackC") as "%EQ".
      all: subst s_st; red_tl_all.
      - iMod (auexa_b_w_update with "TStackInv TStackC") as "[TStackInv TStackC]".
        iMod ("CloseC2Inv" with "[TStackC]") as "_".
        { iEval (unfold Client2StackState; simpl; red_tl_all; simpl).
          iRight. iFrame.
        }
        iModIntro. iFrame. done.
      - iMod ("CloseC2Inv" with "[TStackC]") as "_".
        { iEval (unfold Client2StackState; simpl; red_tl_all; simpl).
          iRight. iFrame.
        }
        iModIntro. iFrame.
    }
    iIntros (ov). red_tl_all. iIntros "[%Hrv Duty]".

    iEval (red_tl_all;simpl).
    rred2r.
    iApply "Post". red_tl_all. iFrame. done.
  Qed.

End SPEC.
