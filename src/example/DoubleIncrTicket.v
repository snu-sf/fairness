From sflib Require Import sflib.
From Paco Require Import paco.
From Fairness Require Import pind Axioms ITreeLib Red TRed IRed2 WFLibLarge.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Import FairBeh Mod Concurrency Linking.
From Fairness Require Import PCM IPM IPropAux.
From Fairness Require Import IndexedInvariants OpticsInterp SimWeakest SimWeakestAdequacy.
From Fairness Require Import TemporalLogic SCMemSpec TicketLock.
From Fairness Require Import AuthExclsRA OneShotsRA.

Module DoubleIncrTicket.

  Section CODE.

    Context {state : Type}.
    Context {ident : ID}.

    (* Ticketlock (x); Ticketlock (y); a++; b++; Ticketunlock (y); Ticketunlock(x) *)
    Definition double_incr_ticket :
    ktree (threadE ident state) (SCMem.val * SCMem.val * (SCMem.val * SCMem.val) * (SCMem.val * SCMem.val)) unit
    :=
    fun x =>
      let '(a_loc, b_loc, x_loc, y_loc) := x in
        _ <- (trigger Yield;;; TicketLock.lock x_loc);;
        _ <- (trigger Yield;;; TicketLock.lock y_loc);;
        a <- (OMod.call (R:=SCMem.val) "load" a_loc);;
        _ <- (OMod.call (R:=unit) "store" (a_loc, SCMem.val_add a 1));;
        b <- (OMod.call (R:=SCMem.val) "load" b_loc);;
        _ <- (OMod.call (R:=unit) "store" (b_loc, SCMem.val_add b 1));;
        _ <- (trigger Yield;;; TicketLock.unlock y_loc);;
        _ <- (trigger Yield;;; TicketLock.unlock x_loc);;
        Ret tt
    .

  End CODE.

End DoubleIncrTicket.

Section SPEC.

  Import DoubleIncrTicket.

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
  (* Ticketlock ra *)
  Context {HasTicket : @GRA.inG TicketRA Γ}.
  Context {HasAuthExclAnys : @GRA.inG (AuthExcls.t (nat * nat * nat)) Γ}.
  Context {HasOneShots : @GRA.inG (OneShots.t unit) Γ}.
  (* Ticketlock namespaces *)
  Definition N_Ticketlock_x : namespace := nroot .@ "Ticketlock_x".
  Definition N_Ticketlock_y : namespace := nroot .@ "Ticketlock_y".

  (* sprop interpretation tactics *)
  Ltac red_tl_all := red_tl; red_tl_memra; red_tl_authexcls; red_tl_oneshots; red_tl_ticket.

  (* number of yields for lock y     : (1,  4)
     lock obligation level for y     : (2,  1)
     required progress credits for y : (6,  1)
     lock obligation level for x     : (7,  1)
     required progress credits for x : (11, 1)
     required progress credits       : (1, 10) + (6, 1) + (11, 1) (or (12, 1)) *)
  Lemma double_incr_spec
        tid i
  :
  ⊢ ∀ (loc_a loc_b a b : SCMem.val) loc_x loc_y γx γy (ds : list (nat * nat * sProp i)),
      [@ tid, i, ⊤ @]
        ⧼⟦(syn_tgt_interp_as i sndl (fun m => (s_memory_black m))
          ∗ (⤉ isTicketLock i γx loc_x emp 7 1)
          ∗ (⤉ isTicketLock i γy loc_y emp 2 1)
          ∗ (⤉ Duty(tid) ds)
          ∗ (⤉ ◇{ds@1}(1, 14))
          ∗ (⤉ ◇{ds@1}(11, 1))
          ∗ (⤉ ◇{ds@1}(6, 1))
          ∗ (⤉ (loc_a ↦ a))
          ∗ (⤉ (loc_b ↦ b)))%S, 1+i⟧⧽
          (OMod.close_itree Client (SCMem.mod gvs) (double_incr_ticket (loc_a, loc_b, loc_x, loc_y)))
          ⧼rv, ⟦(⤉ (loc_a ↦ (SCMem.val_add a 1))
                ∗ ⤉ (loc_b ↦ (SCMem.val_add b 1))
                ∗ (⤉ Duty(tid) ds))%S, 1+i⟧⧽.
  Proof.
    iIntros. iStartTriple.
    red_tl_all; rewrite red_syn_tgt_interp_as; ss.
    iIntros "(#MEM & #LINVx & #LINVy & DUTY & PCs & PCsx & PCsy & PTa & PTb) POST". rred2r.
    (* Preprocessing *)
    iApply (wpsim_yieldR2 with "[DUTY PCs]"). 3:iFrame. all: try lia. iIntros "DUTY _ PCs"; rred2r; ss.
    iApply wpsim_tauR; rred2r.
    (* Lock x *)
    iApply (TicketLock_lock_spec with "[DUTY PCsx] [-]"); [set_solver|..].
    { red_tl_all. rewrite red_syn_tgt_interp_as. repeat iSplit; auto. simpl. iFrame. }
    iIntros "_ LPOST".
    iEval (red_tl; simpl) in "LPOST"; iDestruct "LPOST" as (κux) "LPOST".
    iEval (red_tl; simpl) in "LPOST"; iDestruct "LPOST" as (γux) "LPOST".
    iEval (red_tl_all; ss) in "LPOST"; iDestruct "LPOST" as "(_ & LX & DUTY & PCx)". rred2r.
    (* Yield *)
    iPoseProof (pc_drop _ 6 _ _ 2 with "[PCx]") as "> PCx"; ss.
    iPoseProof (pc_split _ _ 1 with "PCx") as "[PCx2 PCx]".
    iPoseProof (pc_drop _ 1 _ _ 13 with "[PCx2]") as "> PCx2"; ss.
    iPoseProof (pcs_cons_fold _ 0 _ 1 with "[PCx2 PCs]") as "PCs"; iFrame.
    iApply (wpsim_yieldR2 with "[DUTY PCs]"). 3: iFrame; simpl; iFrame. all: try lia.
    iIntros "DUTY _ PCs"; rred2r; ss. iApply wpsim_tauR; rred2r.
    (* Lock y *)
    iApply (TicketLock_lock_spec with "[DUTY PCsy PCx] [-]"); [set_solver|..].
    { red_tl_all. rewrite red_syn_tgt_interp_as. repeat iSplit; auto. simpl.
      iSplitL "DUTY"; [done|]. iApply pcs_cons_fold; iFrame.
    }
    iIntros "_ LPOST".
    iEval (red_tl; simpl) in "LPOST"; iDestruct "LPOST" as (κuy) "LPOST".
    iEval (red_tl; simpl) in "LPOST"; iDestruct "LPOST" as (γuy) "LPOST".
    iEval (red_tl_all; ss) in "LPOST"; iDestruct "LPOST" as "(_ & LY & DUTY & PCy)". rred2r.
    iPoseProof (pc_drop _ 1 _ _ 12 with "[PCy]") as "> PCy2"; ss.

    (* Yield *)
    iPoseProof (pcs_cons_fold _ 0 with "[PCy2 PCs]") as "PCs".
    { iSplitL "PCy2"; iFrame. }
    iApply (wpsim_yieldR2 with "[DUTY PCs]"). 3: iFrame; simpl; iFrame. all: try lia.
    iIntros "DUTY _ PCs"; rred2r; ss.
    (* Load a *)
    iApply (SCMem_load_fun_spec with "[PTa MEM]"); auto.
    iIntros (rv) "(%EQ & PTa)"; subst. rred2r. iApply wpsim_tauR. rred2r.
    (* Yield *)
    iApply (wpsim_yieldR2 with "[DUTY PCs]"). 3: iFrame; simpl; iFrame. all: try lia.
    iIntros "DUTY _ PCs"; rred2r; ss.
    (* Store a *)
    iApply (SCMem_store_fun_spec with "[PTa MEM]"); auto.
    iIntros (rv) "PTa"; subst. rred2r. iApply wpsim_tauR. rred2r.
    (* Yield *)
    iApply (wpsim_yieldR2 with "[DUTY PCs]"). 3: iFrame; simpl; iFrame. all: try lia.
    iIntros "DUTY _ PCs"; rred2r; ss.
    (* Load b *)
    iApply (SCMem_load_fun_spec with "[PTb MEM]"); auto.
    iIntros (rv') "(%EQ & PTb)"; subst. rred2r. iApply wpsim_tauR. rred2r.
    (* Yield *)
    iApply (wpsim_yieldR2 with "[DUTY PCs]"). 3: iFrame; simpl; iFrame. all: try lia.
    iIntros "DUTY _ PCs"; rred2r; ss.
    (* Store b *)
    iApply (SCMem_store_fun_spec with "[PTb MEM]"); auto.
    iIntros (rv') "PTb"; subst. rred2r. iApply wpsim_tauR. rred2r.
    (* Yield *)
    iApply (wpsim_yieldR2 with "[DUTY PCs]"). 3: iFrame; simpl; iFrame. all: try lia.
    iIntros "DUTY _ PCs"; rred2r; ss. iApply wpsim_tauR; rred2r.

    (* Unlock y *)
    iPoseProof (pcs_decr 3 4 with "PCs") as "> [PCs1 PCS2]"; auto.
    iApply (TicketLock_unlock_spec with "[DUTY LY PCs1] [-]"); auto.
    { iEval (red_tl_all; rewrite red_syn_tgt_interp_as; simpl). iFrame. simpl. iFrame. iSplit; auto. }
    iIntros (_) "DUTY". iEval (red_tl; simpl) in "DUTY". rred2r.
    iPoseProof (pcs_cons_unfold with "PCS2") as "[_ PCS]"; simpl.
    (* Yield *)
    iApply (wpsim_yieldR2 with "[DUTY PCS]"). 3: iFrame; simpl; iFrame. all: try lia.
    iIntros "DUTY _ PCs"; rred2r; ss. iApply wpsim_tauR; rred2r.
    (* Unlock x *)
    iApply (TicketLock_unlock_spec with "[DUTY LX PCs]"); auto.
    { iEval (red_tl_all; rewrite red_syn_tgt_interp_as; simpl). iFrame. iSplit; auto. }
    iIntros (_) "DUTY". iEval (red_tl; simpl) in "DUTY". rred2r.
    (* POST *)
    iApply ("POST" with "[-]"); iFrame.
  Unshelve. all: lia.
  Qed.

End SPEC.