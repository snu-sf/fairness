From sflib Require Import sflib.
From Paco Require Import paco.
From Fairness Require Import pind Axioms ITreeLib Red TRed IRed2 WFLibLarge.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Import FairBeh Mod Concurrency Linking.
From Fairness Require Import PCM IPM IPropAux.
From Fairness Require Import IndexedInvariants OpticsInterp SimWeakest SimWeakestAdequacy.
From Fairness Require Import TemporalLogic SCMemSpec Spinlock SpinlockSpec0.
From Fairness Require Import AuthExclsRA OneShotsRA.

Module DoubleIncr.

  Section CODE.

    Context {state : Type}.
    Context {ident : ID}.

    Definition double_incr :
    ktree (threadE ident state) (SCMem.val * SCMem.val * SCMem.val * SCMem.val) unit
    :=
    fun x =>
      let '(a_loc, b_loc, x_loc, y_loc) := x in
        _ <- (trigger Yield;;; Spinlock.lock x_loc);;
        _ <- (trigger Yield;;; Spinlock.lock y_loc);;
        my_tk <- (OMod.call (R:=SCMem.val) "faa" (a_loc, 1));;
        my_tk <- (OMod.call (R:=SCMem.val) "faa" (b_loc, 1));;
        _ <- (trigger Yield;;; Spinlock.unlock y_loc);;
        _ <- (trigger Yield;;; Spinlock.unlock x_loc);;
        Ret tt
    .

  End CODE.

End DoubleIncr.

Section SPEC.

  Import DoubleIncr.

  (* boilerplates *)
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

  (* memory ra *)
  Context {HasMEMRA: @GRA.inG memRA Γ}.
  (* spinlock ra *)
  Context {HasOneShotsNat : @GRA.inG (OneShots.t unit) Γ}.
  Context {HasAuthExcls : @GRA.inG (AuthExcls.t (nat * nat)) Γ}.
  (* spinlock namespaces *)
  Definition N_Spinlock_x : namespace := nroot .@ "Spinlock_x".
  Definition N_Spinlock_y : namespace := nroot .@ "Spinlock_y".

  (* sprop interpretation tactics *)
  Ltac red_tl_all := red_tl; red_tl_memra; red_tl_authexcls; red_tl_oneshots.

  (* number of yields for lock y : (1, 4)
     lock obligation bound for y : (1, 4 + 1) (+ 1 accounts for internal yield)
     progress credits for lock x :
     (2, 6) =
       (2, 5) : matching the lock obligation bound of y
     + (1, 8) : number of yields for lock x
     lock obligation bound for x : (2, 6 + 1) (+ 1 accounts for internal yield) *)
  Lemma double_incr_spec
      tid i
  :
  ⊢ ∀ (loc_a loc_b a b loc_x loc_y : SCMem.val) κx γlx κy γly (ds : list (nat * nat * sProp i)),
      [@ tid, i, ⊤ @]
        ⧼⟦(syn_tgt_interp_as i sndl (fun m => (s_memory_black m))
          ∗ (⤉ isSpinlock N_Spinlock_x i κx loc_x γlx emp 2 7)
          ∗ ◇[κx](2, 7)
          ∗ (⤉ isSpinlock N_Spinlock_y i κy loc_y γly emp 1 5)
          ∗ ◇[κy](1, 5)
          ∗ (⤉ Duty(tid) ds)
          ∗ (⤉ ◇{ds@1}(1, 10))
          ∗ (⤉ ◇{ds@1}(3, 7))
          ∗ (⤉ ◇{ds@1}(2, 5))
          ∗ (⤉ (loc_a ↦ a))
          ∗ (⤉ (loc_b ↦ b)))%S, 1+i⟧⧽
          (OMod.close_itree Client (SCMem.mod gvs) (double_incr (loc_a, loc_b, loc_x, loc_y)))
          ⧼rv, ⟦(⤉ (loc_a ↦ (SCMem.val_add a 1))
                ∗ ⤉ (loc_b ↦ (SCMem.val_add b 1))
                ∗ (⤉ Duty(tid) ds))%S, 1+i⟧⧽.
  Proof.
    iIntros (? ? ? ? ? ? ? ? ? ? ?). iStartTriple.
    red_tl_all; rewrite red_syn_tgt_interp_as; ss.
    iIntros "(#MEM & #LINVx & PCx & #LINVy & PCy & DUTY & PCs & PCsx & PCsy & PTa & PTb) POST". rred2r.
    (* Preprocessing *)
    (* iPoseProof (pcs_decr _ _ 1 with "PCs") as "> [PCs2 PCs]"; first by apply le_n. rred2r. *)
    iApply (wpsim_yieldR2 with "[DUTY PCs]"). 3:iFrame. all: try lia. iIntros "DUTY _ PCs"; rred2r; ss.
    iApply wpsim_tauR; rred2r.
    (* Lock x *)
    (* iApply (wpsim_yieldR2 with "[DUTY PCs]"). 3:iFrame. all: try lia. iIntros "DUTY CRED"; rred2r. *)
    iPoseProof (pcs_decr 1 with "PCs") as "> [PCs2 PCs]"; first by apply le_n.
    iApply (Spinlock_lock_spec with "[] [PCx DUTY PCs2 PCsx] [-]").
    { instantiate (1:=N_Spinlock_x). solve_ndisj. }
    { instantiate (1:=2). auto. }
    { red_tl_all. rewrite red_syn_tgt_interp_as /=. repeat iSplit; auto. simpl. iFrame. }
    iIntros "_ LPOST".
    iEval (red_tl; simpl) in "LPOST"; iDestruct "LPOST" as (γκux) "LPOST".
    iEval (red_tl; simpl) in "LPOST"; iDestruct "LPOST" as (κux) "LPOST".
    iEval (red_tl_all; ss) in "LPOST"; iDestruct "LPOST" as "(LX & _ & DUTY & PCx)". rred2r.
    (* Yield *)
    iPoseProof (pc_split _ _ 1 with "PCx") as "[PCx2 PCx]".
    iPoseProof (pc_drop _ 1 2 ltac:(lia) 8 with "[PCx2]") as "> PCx2"; ss.
    (* iPoseProof (pcs_decr _ _ 1 with "PCs") as "> [PCax PCs]"; first by apply le_n. *)
    iPoseProof (pcs_cons_fold _ 0 _ 1 with "[PCx2 PCs]") as "PCs"; iFrame.
    iApply (wpsim_yieldR2 with "[DUTY PCs]"). 3: iFrame; simpl; iFrame. all: try lia.
    iIntros "DUTY _ PCs"; rred2r; ss. iApply wpsim_tauR; rred2r.
    (* Lock y *)
    iPoseProof (pcs_decr 1 with "PCs") as "> [PCs2 PCs]"; first by apply le_n.
    iPoseProof (pcs_cons_fold _ 0 _ 2 with "[PCx PCsy]") as "PCsy"; iFrame.
    iApply (Spinlock_lock_spec with "[] [PCy DUTY PCs2 PCsy] [-]").
    { instantiate (1:=N_Spinlock_y). solve_ndisj. }
    { instantiate (1:=1). auto. }
    { red_tl_all. rewrite red_syn_tgt_interp_as. repeat iSplit; auto. simpl.
      iSplitL "PCy"; [iFrame|]. iSplitL "DUTY"; [iFrame|]. iSplitL "PCsy"; iFrame.
    }
    iIntros "_ LPOST".
    iEval (red_tl; simpl) in "LPOST"; iDestruct "LPOST" as (γκuy) "LPOST".
    iEval (red_tl; simpl) in "LPOST"; iDestruct "LPOST" as (κuy) "LPOST".
    iEval (red_tl_all; ss) in "LPOST"; iDestruct "LPOST" as "(LY & _ & DUTY & PCy)". rred2r.
    iPoseProof (pcs_decr 2 with "PCs") as "> [PCay PCs]"; first by apply le_n.
    (* Yield *)
    iPoseProof (pcs_cons_fold _ 0 _ 1 with "[PCy PCs]") as "PCs"; iFrame.
    iApply (wpsim_yieldR2 with "[DUTY PCs]"). 3: iFrame; simpl; iFrame. all: try lia.
    iIntros "DUTY _ PCs"; rred2r; ss.
    (* FAA a *)
    iApply (SCMem_faa_fun_spec with "[PTa MEM]"). auto.
    { set_solver. }
    { iSplitR "PTa"; done. }
    iIntros (rv) "(%EQ & PTa)". subst. iEval (ss) in "PTa". rred2r. iApply wpsim_tauR. rred2r.
    (* Yield *)
    iApply (wpsim_yieldR2 with "[DUTY PCs]"). 3: iFrame; simpl; iFrame. all: try lia.
    iIntros "DUTY _ PCs"; rred2r; ss.
    (* FAA b *)
    iApply (SCMem_faa_fun_spec with "[PTb MEM]"). auto.
    { set_solver. }
    { iSplitR "PTb"; done. }
    iIntros (rv) "(%EQ & PTb)". subst. iEval (ss) in "PTb". rred2r. iApply wpsim_tauR. rred2r.
    (* Yield *)
    iApply (wpsim_yieldR2 with "[DUTY PCs]"). 3: iFrame; simpl; iFrame. all: try lia.
    iIntros "DUTY _ PCs"; rred2r; ss. iApply wpsim_tauR; rred2r.
    (* Unlock y *)
    iApply (Spinlock_unlock_spec with "[DUTY LY PCs]").
    { instantiate (1:=N_Spinlock_y). solve_ndisj. }
    { iEval (red_tl_all; rewrite red_syn_tgt_interp_as; simpl). iFrame. simpl. iFrame. iSplit; auto. }
    iIntros (_) "DUTY". iEval (red_tl; simpl) in "DUTY". rred2r.
    (* Yield *)
    iApply (wpsim_yieldR2 with "[DUTY PCay]"). 3: iFrame; simpl; iFrame. all: try lia.
    iIntros "DUTY _ PCs"; rred2r; ss. iApply wpsim_tauR; rred2r.
    (* Unlock x *)
    iApply (Spinlock_unlock_spec with "[DUTY LX PCs]").
    { instantiate (1:=N_Spinlock_x). solve_ndisj. }
    { iEval (red_tl_all; rewrite red_syn_tgt_interp_as; simpl). iFrame. simpl. iFrame. iSplit; auto. }
    iIntros (_) "DUTY". iEval (red_tl; simpl) in "DUTY". rred2r.
    (* POST *)
    iApply ("POST" with "[-]"); iFrame.
  Qed.

End SPEC.