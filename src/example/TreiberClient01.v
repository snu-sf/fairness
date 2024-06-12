From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Import pind Axioms ITreeLib Red TRed IRed2 WFLibLarge.
From Fairness Require Import FairBeh Mod Concurrency Linking.
From Fairness Require Import PCM IProp IPM IPropAux.
From Fairness Require Import IndexedInvariants OpticsInterp SimWeakest.
From Fairness Require Import TemporalLogic SCMemSpec TreiberStack AuthExclAnysRA.

Module TreiberClient1.

  Definition gvs : list nat := [1].
  Definition s : SCMem.val := SCMem.val_ptr (0, 0).

  Section CODE.

    Definition state := unit.
    Definition ident := void.

    Definition push_two :
      ktree (threadE ident state) unit unit
      :=
      fun _ =>
        _ <- (trigger Yield;;; TreiberStack.push (s,(SCMem.val_nat 0)));;
        _ <- (trigger Yield;;; TreiberStack.push (s,(SCMem.val_nat 1)));;
        _ <- trigger Yield;;
      Ret tt.

    Definition omod : Mod.t :=
      Mod.mk
        tt
        (Mod.get_funs [("push_two", Mod.wrap_fun push_two)])
    .

    Definition module : Mod.t :=
      OMod.close
        (omod)
        (SCMem.mod gvs)
    .

  End CODE.

End TreiberClient1.

Section SPEC.

  Context {src_state : Type}.
  Context {src_ident : Type}.
  Notation tgt_state := (Mod.state TreiberClient1.module).
  Notation tgt_ident := (Mod.ident TreiberClient1.module).

  Local Instance STT : StateTypes := Build_StateTypes src_state tgt_state src_ident tgt_ident.
  Context `{sub : @SRA.subG Γ Σ}.
  Context {TLRASs : TLRAs_small STT Γ}.
  Context {TLRAS : TLRAs STT Γ Σ}.

  Context {HasMemRA: @GRA.inG memRA Γ}.
  Context {HasAuthExclAnysRA : @GRA.inG AuthExclAnysRA Γ}.

  Ltac red_tl_all := red_tl; red_tl_memra; red_tl_auexa.

  Import TreiberClient1.

  Lemma push_two_spec
        tid n
        (* (TOP : OwnEs_top E) *)
    :
    ⊢ ∀ γs L (ds : list (nat * nat * sProp n)),
    [@ tid, n, ⊤ @]
      ⧼⟦(
        (syn_tgt_interp_as n sndl (fun m => s_memory_black m)) ∗
        (⤉ IsTreiber n s γs) ∗
        (⤉ ○ γs ([] : list SCMem.val)) ∗
        (⤉ Duty(tid) ds) ∗
        ◇{List.map fst ds}(2 + L, 3)
        )%S, 1+n⟧⧽
        (OMod.close_itree omod (SCMem.mod gvs) (TreiberClient1.push_two tt))
        ⧼_, ⟦(
          (⤉ Duty(tid) ds) ∗
          (⤉ ○ γs [SCMem.val_nat 1;SCMem.val_nat 0])
        )%S, 1+n⟧⧽
  .
  Proof.
    iIntros. iStartTriple.
    red_tl_all. rewrite red_syn_tgt_interp_as; simpl.
    iIntros "(#Mem & #IsTStack & TStack & Duty &Pcs)".
    iMod (pcs_decr _ _ 2 1 with "Pcs") as "[Pcs PcsPush]"; [lia|].
    iMod (pcs_decr _ _ 1 1 with "Pcs") as "[Pcs PcsPush']"; [lia|].
    iMod (pcs_drop _ _ _ _ 1 100 with "Pcs") as "Pcs"; [lia|]. Unshelve. 2:lia.
    iIntros "Post".
    unfold push_two. rred.
    iApply (wpsim_yieldR2 with "[$Duty $Pcs]"); [lia..|].
    iIntros "Duty _ Pcs". rred2r. iApply wpsim_tauR. rred2r.
    iApply (Treiber_push_spec _ (λ v, (○ γs [SCMem.val_nat 0]))%S with "[Duty PcsPush TStack] [-]"); [ss..| |].
    { red_tl_all. rewrite red_syn_tgt_interp_as. iSplit; [eauto|]. iSplitR; [iFrame "#"|].
      iFrame. iIntros (s_st).
      red_tl_all; rewrite red_syn_fupd; red_tl_all; simpl.
      iIntros "[TStackInv _]". simpl.
      iDestruct (auexa_b_w_eq with "TStackInv TStack") as "%EQ".
      subst s_st.
      iMod (auexa_b_w_update with "TStackInv TStack") as "[TStackInv TStack]".
      iModIntro. iFrame.
    }
    iEval (red_tl_all;simpl). iIntros (_) "[TStack Duty]".
    rred2r.
    iApply (wpsim_yieldR2 with "[$Duty $Pcs]"); [lia..|].
    iIntros "Duty _ Pcs". rred2r.
    iApply wpsim_tauR. rred2r.
    iApply (Treiber_push_spec _ (λ v, ○ γs [SCMem.val_nat 1; SCMem.val_nat 0])%S with "[Duty PcsPush' TStack] [-]"); [ss..| |].
    { red_tl_all. rewrite red_syn_tgt_interp_as. iSplit; [eauto|]. iSplitR; [iFrame "#"|].
      iFrame. iIntros (s_st).
      red_tl_all; rewrite red_syn_fupd; red_tl_all; simpl.
      iIntros "[TStackInv _]".
      iDestruct (auexa_b_w_eq with "TStackInv TStack") as "%EQ".
      subst s_st.
      iMod (auexa_b_w_update with "TStackInv TStack") as "[TStackInv TStack]".
      iModIntro. iFrame.
    }
    iEval (red_tl_all;simpl). iIntros (_) "[TStack Duty]".
    rred2r.
    iApply (wpsim_yieldR2 with "[$Duty $Pcs]"); [lia..|].
    iIntros "Duty _ Pcs". rred2r.
    iApply wpsim_tauR. rred2r.
    iApply "Post". iFrame.
  Qed.

End SPEC.
