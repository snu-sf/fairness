From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Import pind Axioms ITreeLib Red TRed IRed2 WFLibLarge.
From Fairness Require Import FairBeh Mod Linking.
From Fairness Require Import PCM IPM IPropAux.
From Fairness Require Import IndexedInvariants OpticsInterp SimWeakest.
From Fairness Require Import TemporalLogic SCMemSpec OneShotsRA AuthExclsRA.
From Fairness Require Export TicketLockRA.

Module TicketLock.

  Section TICKET.

    Context {state : Type}.
    Context {ident : ID}.

    Definition lock_loop :
      ktree (threadE ident state) (SCMem.val * SCMem.val) unit
      :=
      fun x =>
        let '(own_loc, my_tk) := x in
        ITree.iter
          (fun (_: unit) =>
             own <- (OMod.call (R:=SCMem.val) "load" own_loc);;
             b <- (OMod.call (R:=bool) "compare" (own, my_tk));;
             if b then Ret (inr tt) else Ret (inl tt)) tt.

    Definition lock :
      ktree (threadE ident state) (SCMem.val * SCMem.val) unit
      :=
      fun x =>
        let '(own_loc, next_loc) := x in
        my_tk <- (OMod.call (R:=SCMem.val) "faa" (next_loc, 1));;
        _ <- lock_loop (own_loc, my_tk);;
        trigger Yield.

    Definition unlock :
      ktree (threadE ident state) (SCMem.val * SCMem.val) unit
      :=
      fun x =>
        let '(own_loc, next_loc) := x in
        now <- (OMod.call (R:=SCMem.val) "load" own_loc);;
        _ <- (OMod.call (R:=unit) "store" (own_loc, SCMem.val_add now 1));;
        trigger Yield
    .

  End TICKET.

End TicketLock.

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

  Context {HasTicket : @GRA.inG TicketRA Γ}.
  Context {AuthExclAnys : @GRA.inG (AuthExcls.t (nat * nat * nat)) Γ}.
  Context {HasOneShots : @GRA.inG (OneShots.t unit) Γ}.

  Ltac red_tl_all := red_tl; red_tl_memra; red_tl_ticket; red_tl_authexcls; red_tl_oneshots.

  Lemma lock_loop_red own_loc my_tk :
    @TicketLock.lock_loop tgt_state tgt_ident (own_loc, my_tk)
    =
      own <- (OMod.call (R:=SCMem.val) "load" (own_loc));;
      b <- (OMod.call (R:=bool) "compare" (own, my_tk));;
      if b then Ret tt else tau;; TicketLock.lock_loop (own_loc, my_tk).
  Proof.
    unfold TicketLock.lock_loop. etransitivity.
    { apply unfold_iter_eq. }
    grind.
  Qed.

  (* Progress credits allocated for unlock obligation *)
  Local Definition υ : nat := 5.
  Local Opaque υ.

  (** Invariants. *)
  Definition tklockInv (i : nat) (γt : nat) (lo ln : SCMem.val) (P : sProp i) (l b : nat) : sProp i :=
    (∃ (o n κu γs pass : τ{nat, i}) (D : τ{gset nat, i}),
      (lo ↦ o)
      ∗ (ln ↦ n)
      ∗ (s_ticket_black γt D)
      ∗ ⌜forall tk, (o <= tk < n) <-> (tk ∈ D)⌝
      ∗ ⌜pass <= b⌝
      ∗ (●G γt (κu, γs, pass))
      ∗ ((⌜o = n⌝ ∗ (○G γt (κu, γs, pass)) ∗ P)
        ∨ ◆[κu, l, υ] ∗ (-[κu](0)-◇ ▿ γs tt) ∗ (⋈ [κu]) ∗ (△ γs 1) (* Promise to unlock *)
          ∗ (∃ (κack : τ{nat, i}),
              (s_ticket_wait γt o [κu; γs; κack; pass])
              ∗ (s_ticket_issued γt o [κu; γs; κack; pass] ∨ (○G γt (κu, γs, pass) ∗ P))))
      ∗ ([∗ i set] tk ∈ D,
          ⌜tk = o⌝
          ∨ ⌜tk > o⌝
            ∗ (∃ (κu' κack' γs' : τ{nat}),
              ◆[κu', l, υ] ∗ (-[κu'](0)-⧖ ▿ γs' tt) ∗ ⧖ [κu', (1/2)] ∗ (△ γs' 1) (* Delayed promises to unlock *)
              ∗ (s_ticket_wait γt tk [κu'; γs'; κack'; b])
              ∗ (◇[κack'](l, υ * (pass + (b + 1) * (tk - o)))) ∗ (κu -(0)-◇ κack'))) (* Dependent obligations *)
    )%S.

  (* Namespace for TicketLock invariants. *)
  Definition N_TicketLock : namespace := (nroot .@ "TicketLock").

  Lemma mask_disjoint_ticketlock_state_tgt : ↑N_TicketLock ## (↑N_state_tgt : coPset).
  Proof. apply ndot_ne_disjoint. ss. Qed.

  Definition isTicketLock i (γt : nat) (v : SCMem.val * SCMem.val) (P : sProp i) (l b : nat)
    : sProp i :=
    (∃ (lo ln : τ{SCMem.val}) (N : τ{namespace, i}),
        (⌜(↑N ⊆ (↑N_TicketLock : coPset))⌝)
          ∗ (⌜0 < l⌝) ∗ (⌜v = (lo, ln)⌝) ∗ syn_inv i N (tklockInv i γt lo ln P l b))%S.

  Global Instance isSpinlock_persistent i γt v P l b : Persistent (⟦isTicketLock i γt v P l b, i⟧).
  Proof.
    unfold Persistent. iIntros "H". unfold isTicketLock.
    red_tl. iDestruct "H" as "[%lo H]". iExists lo.
    red_tl. iDestruct "H" as "[%ln H]". iExists ln.
    red_tl. iDestruct "H" as "[%N H]". iExists N.
    red_tl. rewrite red_syn_inv. iDestruct "H" as "#H". auto.
  Qed.

  Lemma make_isTicketLock
        i lo ln P l b (LT : 0 < l)
        Es
    :
    ⊢
      ⟦((⤉ (lo ↦ 0)) ∗ (⤉ (ln ↦ 0)) ∗ (⤉ P) ∗ (⤉ s_ticket_auth))%S, 1+i⟧
        -∗
        ⟦(∃ (γt : τ{nat, 1+i}), =|1+i|={Es}=> (⤉ isTicketLock i γt (lo, ln) P l b))%S, 1+i⟧.
  Proof.
    simpl. red_tl_all; simpl. iIntros "(LO & LN & P & TAUTH)".
    iPoseProof (TicketRA_alloc 0 0 b with "TAUTH") as "(%γt & ALLOC)". iExists γt.
    rewrite red_syn_fupd; simpl. iMod "ALLOC" as "(TAUTH & TB & LB & LW)".
    iMod ((FUpd_alloc _ _ _ i (N_TicketLock)) (tklockInv i γt lo ln P l b) with "[-]") as "#TINV". auto.
    { unfold tklockInv. simpl. red_tl.
      iExists 0. red_tl; simpl. iExists 0. red_tl; simpl.
      iExists 0. red_tl; simpl. iExists 0. red_tl; simpl. iExists b; red_tl. iExists ∅. red_tl_all; simpl.
      iFrame. iSplit.
      { iPureIntro. split; i; inv H. lia. }
      iSplit; [done|].
      iSplitL; cycle 1. auto.
      iLeft. iSplitR; [done|]. iFrame.
    }
    iModIntro.
    unfold isTicketLock. red_tl; simpl. iExists lo. red_tl; simpl. iExists ln. red_tl; simpl.
    iExists N_TicketLock. red_tl.
    iSplitL ""; try (iPureIntro; set_solver).
    iSplitL ""; try iPureIntro; auto.
  Qed.

  Lemma TicketLock_lock_loop_spec
        tid i N
        (NIN : ↑N ⊆ (↑N_TicketLock : coPset))
  :
  ⊢ ∀ γt lo ln (P : sProp i) l b n κu γs κack (ds : list (nat * nat * sProp i)),
    [@ tid, i, ⊤ @]
      ⧼⟦((⤉ syn_inv i N (tklockInv i γt lo ln P l b))
        ∗ (syn_tgt_interp_as i sndl (fun m => s_memory_black m))
        ∗ (⤉ Duty(tid)((κu, 0, ▿ γs tt) :: ds))
        ∗ (◇{(ds@1)}(2, 1)) (* for yields when acquiring the lock *)
        ∗ (⤉ ⦃◆[κack] & ◇{(ds@1)%S}(2)⦄)
        ∗ (◇[κu](1, 2)) (* for yields when acquiring the lock *)
        ∗ (⤉ s_ticket_issued γt n [κu; γs; κack; b]))%S, 1+i⟧⧽
        (OMod.close_itree Client (SCMem.mod gvs) (TicketLock.lock_loop (lo, SCMem.val_nat n)))
        ⧼rv, ⟦((⤉ Duty(tid)((κu, 0, ▿ γs tt) :: ds))
            ∗ (⤉ ○G γt (κu, γs, b))
            ∗ (⤉ P))%S, 1+i⟧⧽
  .
  Proof.
    iIntros. iStartTriple. simpl. red_tl_all; simpl. rewrite red_syn_inv; rewrite red_syn_tgt_interp_as.
    iIntros "(#INV & #MEM & DUTY & PCS & CCS & PC & ISSUED) POST".

    iRevert "PCS DUTY PC ISSUED POST".
    iMod (ccs_ind2 with "CCS [-]") as "IND".
    2:{ iApply "IND". }
    iModIntro. iExists 0. iIntros "IH". iModIntro. iIntros "PCS DUTY PC ISSUED POST".
    iMod (pcs_drop 1 2 with "PCS") as "PCS"; [lia..|].

    iEval (rewrite unfold_iter_eq; rred2r).
    iInv "INV" as "TI" "TI_CLOSE". iEval (simpl; unfold tklockInv; red_tl_all; simpl) in "TI".
    iDestruct "TI" as (o2) "TI"; iEval (red_tl_all; simpl) in "TI".
    iDestruct "TI" as (n2) "TI"; iEval (red_tl_all; simpl) in "TI".
    iDestruct "TI" as (κu2) "TI"; iEval (red_tl_all; simpl) in "TI".
    iDestruct "TI" as (γs2) "TI"; iEval (red_tl_all; simpl) in "TI".
    iDestruct "TI" as (b2) "TI"; iEval (red_tl_all; simpl) in "TI".
    iDestruct "TI" as (D2) "TI"; iEval (red_tl_all; simpl) in "TI".
    iDestruct "TI" as "(LOPT & LNPT & TB & %HD & %HB & LB & HOWNER & HWAIT)".
    iPoseProof (Ticket_black_issued with "TB ISSUED") as "%HIND2".
    iDestruct "HOWNER" as "[(%EQ & _) | (#OBL2 & #PRM2 & #AO2 & PENDING2 & %κack2 & REST)]".
    { subst; apply HD in HIND2; lia. }
    assert (D2 = D2 ∖ {[n]} ∪ {[n]}).
    { set_unfold. split; ii. destruct (Nat.eq_dec x n). subst. right; auto. left; auto.
      des; subst; auto.
    }
    iEval (setoid_rewrite H; rewrite red_tl_big_sepS) in "HWAIT". rewrite big_opS_union; cycle 1. set_solver.
    iDestruct "HWAIT" as "[HWAIT Hn]". rewrite big_sepS_singleton.
    iEval (red_tl_all; simpl) in "Hn". iDestruct "Hn" as "[%EQ | (%HGT & %κu' & Hn)]".
    { (* My turn *)
      subst.
      iEval (red_tl_all; simpl) in "REST". iDestruct "REST" as "(WAIT & [ISSUED' | LW])".
      { iExFalso. iApply (Ticket_issued_twice with "ISSUED ISSUED'"). }
      iPoseProof (Ticket_issued_wait with "ISSUED WAIT") as "%EQ". clarify.
      iMod ("TI_CLOSE" with "[- POST DUTY PC ISSUED PCS]") as "_".
      { iEval (unfold tklockInv; simpl; red_tl_all).
        iExists o2. iEval (red_tl; simpl). iExists n2. iEval (red_tl; simpl).
        iExists κu2. iEval (red_tl; simpl). iExists γs2. iEval (red_tl; simpl).
        iExists b2. iEval (red_tl; simpl). iExists D2. iEval (red_tl_all; simpl). iFrame.
        iSplit; [done|]. iSplit; [done|].
        iSplitR "HWAIT".
        { iRight. iFrame. repeat iSplitR; try done. iExists κack2. red_tl_all; simpl. iFrame. }
        iEval (rewrite H; rewrite red_tl_big_sepS). rewrite big_opS_union; cycle 1. set_solver.
        iSplitL; auto. iApply big_sepS_singleton. red_tl; iLeft; auto.
      }
      iApply (wpsim_yieldR2 with "[DUTY PCS PC]"). auto. instantiate (1:=2); auto.
      { iSplitL "DUTY"; auto. iApply (pcs_cons_fold with "[PCS PC]"). iFrame. }
      iIntros "DUTY _ PCS". simpl. rred2r.
      clear n2 D2 HD HIND2 H HB. iClear "OBL2 PRM2".
      iInv "INV" as "TI" "TI_CLOSE". iEval (simpl; unfold tklockInv; red_tl_all; simpl) in "TI".
      iDestruct "TI" as (o3) "TI"; iEval (red_tl_all; simpl) in "TI".
      iDestruct "TI" as (n3) "TI"; iEval (red_tl_all; simpl) in "TI".
      iDestruct "TI" as (κu3) "TI"; iEval (red_tl_all; simpl) in "TI".
      iDestruct "TI" as (γs3) "TI"; iEval (red_tl_all; simpl) in "TI".
      iDestruct "TI" as (b3) "TI"; iEval (red_tl_all; simpl) in "TI".
      iDestruct "TI" as (D3) "TI"; iEval (red_tl_all; simpl) in "TI".
      iDestruct "TI" as "(LOPT & LNPT & TB & %HD & %HB & LB & HOWNER & HWAIT)".
      iPoseProof (Ticket_black_issued with "TB ISSUED") as "%HIND3".
      iDestruct "HOWNER" as "[(%EQ & _) | (#OBL & #PRM & _ & PENDING & %κack3 & REST)]".
      { subst; apply HD in HIND3; lia. }
      assert (D3 = D3 ∖ {[o2]} ∪ {[o2]}).
      { set_unfold. split; ii. destruct (Nat.eq_dec x o2). subst. right; auto. left; auto.
        des; subst; auto.
      }
      iEval (setoid_rewrite H; rewrite red_tl_big_sepS) in "HWAIT". rewrite big_opS_union; cycle 1. set_solver.
      iDestruct "HWAIT" as "[HWAIT Ho2]". rewrite big_sepS_singleton.
      iEval (red_tl_all; simpl) in "Ho2". iDestruct "Ho2" as "[%EQ | (%HGT & %κu2' & Ho2)]"; cycle 1.
      { iEval (red_tl; simpl) in "Ho2". iDestruct "Ho2" as (κack2') "Ho2".
        iEval (red_tl; simpl) in "Ho2". iDestruct "Ho2" as (γ2') "Ho2".
        iEval (red_tl_all; simpl) in "Ho2". iDestruct "Ho2" as "(_ & _ & PO2 & _ & WAIT & _)".
        iPoseProof (Ticket_issued_wait with "ISSUED WAIT") as "%EQ". clarify.
        iExFalso. iApply (pending_not_active with "PO2 AO2").
      }
      subst. iApply (SCMem_load_fun_spec with "[LOPT] [-]"). auto.
      { pose proof mask_disjoint_ticketlock_state_tgt. set_solver. }
      { iFrame. done. }
      iIntros (rv) "[%EQ LOPT]". subst. rred2r. iApply wpsim_tauR. rred2r.
      iEval (red_tl_all; simpl) in "REST". iDestruct "REST" as "(WAIT & [ISSUED' | [LW P]])".
      { iExFalso. iApply (Ticket_issued_twice with "ISSUED ISSUED'"). }
      iPoseProof (Ticket_issued_wait with "ISSUED WAIT") as "%EQ". clarify.
      iMod (AuthExcls.b_w_update _ _ _ (κu3, γs3, b3) with "LB LW") as "(LB & LW)".
      iMod ("TI_CLOSE" with "[- POST DUTY PCS LW P]") as "_".
      { iEval (unfold tklockInv; simpl; red_tl_all).
        iExists o3. iEval (red_tl; simpl). iExists n3. iEval (red_tl; simpl).
        iExists κu3. iEval (red_tl; simpl). iExists γs3. iEval (red_tl; simpl).
        iExists b3. iEval (red_tl; simpl). iExists D3. iEval (red_tl_all; simpl). iFrame.
        iSplitR; [done|]. iSplitR; [done|]. iSplitR "HWAIT".
        { iRight. iFrame. repeat iSplitR; try done. iExists κack3. red_tl_all; simpl. iFrame. }
        iEval (setoid_rewrite H; rewrite red_tl_big_sepS). rewrite big_opS_union; cycle 1. set_solver.
        iSplitL; auto. iApply big_sepS_singleton. red_tl; iLeft; auto.
      }
      iApply (wpsim_yieldR2 with "[DUTY PCS]"). auto. left.
      { iSplitL "DUTY"; auto. }
      iIntros "DUTY _ _". rred2r.
      iApply (SCMem_compare_fun_spec with "[MEM]"). auto.
      { pose proof mask_disjoint_ticketlock_state_tgt. set_solver. }
      { simpl. des_ifs. iApply (tgt_interp_as_equiv with "MEM"). iIntros. iSplit.
        { iIntros. simpl. red_tl; simpl. iSplit; [done | iPureIntro; auto]. }
        { simpl. red_tl; simpl. iIntros "[? _]". done. }
      }
      iIntros (rv) "[%EQ _]". exploit EQ. auto. i; subst. rred2r. iApply wpsim_tauR. rred2r.
      iApply ("POST" $! tt with "[DUTY LW P]"). iFrame.
    }

    iEval (red_tl) in "Hn". iDestruct "Hn" as (κack') "Hn".
    iEval (red_tl) in "Hn". iDestruct "Hn" as (γs') "Hn".
    iEval (red_tl_all; simpl) in "Hn". iDestruct "Hn" as "(#OBL & #PRM & PO & PENDING & WAIT & PCa & #LINK)".
    iPoseProof (Ticket_issued_wait with "ISSUED WAIT") as "%EQ". clarify.
    iApply (wpsim_yieldR_gen_pending with "DUTY [PO] [PCS]"). auto.
    instantiate (1:=ds). instantiate (1:=[(κu', 0, (▿ γs' ())%S)]). f_equal.
    3:{ iApply (pps_cons_fold with "[PO]"). iSplitL; auto. iApply pps_nil. }
    econs; auto. instantiate (1:=2). auto. done.
    iIntros "DUTY CRED PPS PCS".
    iMod (tpromise_progress with "[CRED]") as "[PCa' | #CONTRA]".
    { iFrame. iApply "PRM2". }
    2:{ iEval (simpl; red_tl_all) in "CONTRA".
        iExFalso. iApply (OneShots.pending_not_shot with "PENDING2 CONTRA").
    }
    iMod (link_amplify with "[PCa']") as "PCa'". iFrame. done.
    iMod ("IH" with "PCa'") as "IH".
    iMod ("TI_CLOSE" with "[- IH POST PC ISSUED DUTY PCS]") as "_".
    { iEval (unfold tklockInv; simpl; red_tl_all).
      iExists o2. iEval (red_tl; simpl). iExists n2. iEval (red_tl; simpl).
      iExists κu2. iEval (red_tl; simpl). iExists γs2. iEval (red_tl; simpl).
      iExists b2. iEval (red_tl; simpl). iExists D2. iEval (red_tl_all; simpl). iFrame.
      iSplit; [done|]. iSplit; [done|]. iSplitR "HWAIT PENDING WAIT PCa PPS".
      { iRight. iFrame. repeat iSplitR; try done. iExists κack2. red_tl_all; simpl. iFrame. }
      iEval (setoid_rewrite H; rewrite red_tl_big_sepS). rewrite big_opS_union; cycle 1. set_solver.
      iSplitL "HWAIT"; auto. iApply big_sepS_singleton. red_tl; iRight; auto. iSplit; auto.
      iExists κu'. red_tl. iExists κack'. red_tl. iExists γs'. red_tl_all; simpl; iFrame.
      iPoseProof (pps_cons_unfold with "PPS") as "[PO _]". iFrame. repeat iSplit; auto.
    }
    iModIntro. rred2r.
    iClear "OBL2 PRM2 AO2 LINK OBL PRM". clear o2 n2 D2 HD HIND2 H HGT κu2 κack2 γs2 b2 HB.
    iInv "INV" as "TI" "TI_CLOSE". iEval (simpl; unfold tklockInv; red_tl_all; simpl) in "TI".
    iDestruct "TI" as (o2) "TI"; iEval (red_tl_all; simpl) in "TI".
    iDestruct "TI" as (n2) "TI"; iEval (red_tl_all; simpl) in "TI".
    iDestruct "TI" as (κu2) "TI"; iEval (red_tl_all; simpl) in "TI".
    iDestruct "TI" as (γs2) "TI"; iEval (red_tl_all; simpl) in "TI".
    iDestruct "TI" as (b2) "TI"; iEval (red_tl_all; simpl) in "TI".
    iDestruct "TI" as (D2) "TI"; iEval (red_tl_all; simpl) in "TI".
    iDestruct "TI" as "(LOPT & LNPT & TB & %HD & %HB & LB & HOWNER & HWAIT)".
    iApply (SCMem_load_fun_spec with "[LOPT] [-]"). auto.
    { pose proof mask_disjoint_ticketlock_state_tgt. set_solver. }
    { iFrame. done. }
    iIntros (rv) "[%EQ LOPT]". subst. rred2r. iApply wpsim_tauR. rred2r.
    iPoseProof (Ticket_black_issued with "TB ISSUED") as "%HIND2".
    iDestruct "HOWNER" as "[(%EQ & _) | (#OBL2 & #PRM2 & #AO2 & PENDING2 & %κack2 & REST)]".
    { subst; apply HD in HIND2; lia. }
    assert (D2 = D2 ∖ {[n]} ∪ {[n]}).
    { set_unfold. split; ii. destruct (Nat.eq_dec x n). subst. right; auto. left; auto.
      des; subst; auto.
    }
    iEval (setoid_rewrite H; rewrite red_tl_big_sepS) in "HWAIT". rewrite big_opS_union; cycle 1. set_solver.
    iDestruct "HWAIT" as "[HWAIT Ho2]". rewrite big_sepS_singleton.
    iEval (red_tl_all; simpl) in "Ho2". iDestruct "Ho2" as "[%EQ | (%HGT & %κu & Ho2)]".
    { (* My turn *)
      subst.
      iEval (red_tl_all; simpl) in "REST". iDestruct "REST" as "(WAIT & [ISSUED' | [LW P]])".
      { iExFalso. iApply (Ticket_issued_twice with "ISSUED ISSUED'"). }
      iPoseProof (Ticket_issued_wait with "ISSUED WAIT") as "%EQ". clarify.
      iPoseProof (pc_split _ _ 1 with "PC") as "[PC _]".
      iMod ("TI_CLOSE" with "[- POST PC DUTY PCS LW P]") as "_".
      { iEval (unfold tklockInv; simpl; red_tl_all).
        iExists o2. iEval (red_tl; simpl). iExists n2. iEval (red_tl; simpl).
        iExists κu2. iEval (red_tl; simpl). iExists γs2. iEval (red_tl; simpl).
        iExists b2. iEval (red_tl; simpl). iExists D2. iEval (red_tl_all; simpl). iFrame.
        iSplit; [done|]. iSplit; [done|]. iSplitR "HWAIT".
        { iRight. iFrame. repeat iSplitR; try done. iExists κack2. red_tl_all; simpl. iFrame. }
        iEval (setoid_rewrite H; rewrite red_tl_big_sepS). rewrite big_opS_union; cycle 1. set_solver.
        iSplitL "HWAIT"; auto. iApply big_sepS_singleton. red_tl; iLeft; auto.
      }
      iApply (wpsim_yieldR2 with "[DUTY PC PCS]"). auto. left.
      { iSplitL "DUTY"; auto. iApply (pcs_cons_fold with "[PCS PC]"). iFrame. }
      iIntros "DUTY _ _". rred2r.
      iApply (SCMem_compare_fun_spec with "[MEM]"). auto.
      { pose proof mask_disjoint_ticketlock_state_tgt. set_solver. }
      { simpl. des_ifs. iApply (tgt_interp_as_equiv with "MEM"). iIntros. iSplit.
        { iIntros. simpl. red_tl; simpl. iSplit; [done | iPureIntro; auto]. }
        { simpl. red_tl; simpl. iIntros "[? _]". done. }
      }
      iIntros (rv) "[%EQ _]". exploit EQ. auto. i; subst. rred2r. iApply wpsim_tauR. rred2r.
      iApply ("POST" with "[DUTY LW P]"). iFrame.
    }
    {
      iEval (red_tl) in "Ho2". iDestruct "Ho2" as (κack) "Ho2".
      iEval (red_tl) in "Ho2". iDestruct "Ho2" as (γs) "Ho2".
      iEval (red_tl_all; simpl) in "Ho2". iDestruct "Ho2" as "(#OBL & #PRM & PO & PENDING & WAIT & PCa & #LINK)".
      iPoseProof (Ticket_issued_wait with "ISSUED WAIT") as "%EQ". clarify.
      iApply (wpsim_yieldR_gen_pending with "DUTY [PO] [PCS]"). auto.
      instantiate (1:=ds). instantiate (1:=[(κu, 0, (▿ γs ())%S)]). f_equal.
      3:{ iApply (pps_cons_fold with "[PO]"). iSplitL; auto. iApply pps_nil. }
      econs; auto. instantiate (1:=1). auto. done.
      iIntros "DUTY _ PPS _".
      iPoseProof (pps_cons_unfold with "PPS") as "[PO _]".
      iMod ("TI_CLOSE" with "[- IH POST PC ISSUED DUTY]") as "_".
      { iEval (unfold tklockInv; simpl; red_tl_all).
        iExists o2. iEval (red_tl; simpl). iExists n2. iEval (red_tl; simpl).
        iExists κu2. iEval (red_tl; simpl). iExists γs2. iEval (red_tl; simpl).
        iExists b2. iEval (red_tl; simpl). iExists D2. iEval (red_tl_all; simpl). iFrame.
        iSplit; [done|]. iSplit; [done|]. iSplitR "HWAIT PENDING WAIT PCa PO".
        { iRight. iFrame. repeat iSplitR; try done. iExists κack2. iFrame. }
        iEval (setoid_rewrite H; rewrite red_tl_big_sepS). rewrite big_opS_union; cycle 1. set_solver.
        iSplitL "HWAIT"; auto. iApply big_sepS_singleton. red_tl; iRight; auto. iSplit; auto.
        iExists κu. red_tl. iExists κack. red_tl. iExists γs. red_tl_all; simpl; iFrame. repeat iSplit; auto.
      }
      iModIntro. rred2r.
      iApply (SCMem_compare_fun_spec); auto.
      { simpl. des_ifs. lia. iApply (tgt_interp_as_equiv with "MEM"). iIntros. iSplit.
        { iIntros. simpl. red_tl; simpl. iSplit; [done | iPureIntro; auto]. }
        { simpl. red_tl; simpl. iIntros "[? _]". done. }
      }
      iIntros (rv) "[_ %NEQ]". exploit NEQ. ii. inv H0. lia. i; subst.
      rred2r. iApply wpsim_tauR. rred2r. iApply wpsim_tauR.
      iApply wpsim_stutter_mon. instantiate (1:=ps); auto. auto.
      iApply ("IH" with "DUTY PC ISSUED POST").
    }
  Unshelve. all: auto; try lia.
  Qed.

  Lemma TicketLock_lock_spec
        tid i
        (E : coPset)
        (IN : ⊤ ⊆ E)
    :
    ⊢ ∀ γt loc (P : sProp i) l b (ds : list (nat * nat * sProp i)),
        [@ tid, i, E @]
          ⧼⟦((syn_tgt_interp_as i sndl (fun m => (s_memory_black m))
              ∗ (⤉ isTicketLock i γt loc P l b)
              ∗ (⤉ (Duty(tid) ds))
              ∗ ⤉ ◇{ds@1}(4 + l, 1))%S), 1+i⟧⧽
            (OMod.close_itree Client (SCMem.mod gvs) (TicketLock.lock loc))
            ⧼rv, ⟦(∃ (κu γs : τ{nat, 1+i}),
                    (⤉ P)
                    ∗ (⤉ ○G γt (κu, γs, b))
                    ∗ (⤉ (Duty(tid) ((κu, 0, ▿ γs tt) :: ds)))
                    ∗ ◇[κu](l, 1))%S, 1+i⟧⧽
  .
  Proof.
    iIntros. iStartTriple. iIntros "PRE POST". unfold TicketLock.lock.
    iApply wpsim_discard. apply IN.
    unfold isTicketLock. iEval (red_tl_all; simpl; rewrite red_syn_tgt_interp_as) in "PRE".
    iDestruct "PRE" as "(#MEM & PRE & DUTY & PCS)".
    iDestruct "PRE" as (lo) "PRE". iEval (red_tl_all; simpl) in "PRE".
    iDestruct "PRE" as (ln) "PRE". iEval (red_tl_all; simpl) in "PRE".
    iDestruct "PRE" as (N) "PRE". iEval (red_tl_all; simpl; rewrite red_syn_inv) in "PRE".
    iDestruct "PRE" as "(%SUB & %GT & %EQ & #TINV)". clarify.

    (* YIELD *)
    rred2r.
    iMod (pcs_drop (3+l) 2 with "PCS") as "PCS"; [lia..|].
    iMod (pcs_decr 1 _ with "PCS") as "[PCS' PCS]". auto.
    iMod (pcs_drop 2 2 with "PCS'") as "PCS'"; [lia..|].
    iMod (pcs_decr 1 _ with "PCS'") as "[PCS'' PCS']". auto.
    iMod (pcs_drop 1 2 with "PCS'") as "PCS'"; [lia..|].
    iCombine "DUTY" "PCS'" as "DUTY".
    iApply (wpsim_yieldR2 with "DUTY"). auto. lia.
    iIntros "DUTY CRED PCS'". simpl.

    (* OPEN *)
    iInv "TINV" as "TI" "TI_CLOSE".
    iEval (unfold tklockInv; simpl; red_tl_all) in "TI".
    iDestruct "TI" as (o) "TI"; iEval (red_tl_all; simpl) in "TI".
    iDestruct "TI" as (n) "TI"; iEval (red_tl_all; simpl) in "TI".
    iDestruct "TI" as (κu) "TI"; iEval (red_tl_all; simpl) in "TI".
    iDestruct "TI" as (γs) "TI"; iEval (red_tl_all; simpl) in "TI".
    iDestruct "TI" as (pass) "TI"; iEval (red_tl_all; simpl) in "TI".
    iDestruct "TI" as (D) "TI"; iEval (red_tl_all; simpl) in "TI".

    subst. iClear "CRED".
    iDestruct "TI" as "(LOPT & LNPT & TB & %HD & %HB & LB & HOWNER & HWAIT)". rred2r.
    (* FAA *)
    iApply (SCMem_faa_fun_spec with "[LNPT MEM]"). auto.
    { pose proof mask_disjoint_ticketlock_state_tgt. set_solver. }
    { iSplitR "LNPT"; done. }
    iIntros (rv) "(%EQ & LNPT)". subst. iEval (ss) in "LNPT". rred2r. iApply wpsim_tauR. rred2r.
    (* Allocate delayed promise *)
    iMod (OneShots.alloc) as "(%γs2 & PENDING2)".
    (* (l, 5) = (l, 1) for making a promise
                (l, 2) for yields in acuiqre loop
                (l, 1) for last yield
                (l, 1) for the user *)
    iMod (alloc_obligation_fine l 5) as "(%κu2 & #OBL2 & PC2 & PO2)". iEval (rewrite <- Qp.half_half) in "PO2".
    iPoseProof (pending_split _ (1/2) (1/2) with "PO2") as "[PO2 PO2']".
    iPoseProof (pc_split _ _ 1 _ with "[PC2]") as "[PC2' PC2]". simpl. done.
    iAssert (#=> ◇[κu2](1, 4))%I with "[PC2]" as "> PC2".
    { destruct (Nat.eq_dec l 1); [subst; done | ].
      iMod (pc_drop _ 1 l _ 4 4 with "[PC2]") as "PC2". auto. done. done.
    }
    iPoseProof (pc_split _ _ 1 _ with "[PC2]") as "[PC2'' PC2]". simpl. done.
    iPoseProof (duty_add with "[DUTY PC2'' PO2'] []") as "> DUTY".
    { iSplitL "DUTY"; [done | ]. iSplitL "PC2''"; done. }
    { instantiate (1:=(▿ γs2 tt)%S). iModIntro. simpl.
      red_tl_all. simpl. iIntros. iModIntro. done.
    }
    iPoseProof (duty_delayed_tpromise with "DUTY") as "#DPRM2".
    { simpl. left; auto. }
    iMod (alloc_obligation l (υ + υ * (pass + (b + 1) * (n - o)))) as "(%κack2 & #OBLa2 & PCa2 & _)". (* (l, ...) *)
    iPoseProof (pc_split _ _ υ with "PCa2") as "[PCa2' PCa2]".
    iMod (ccs_make κack2 l _ 2 _ with "[PCS]") as "[CCS _]". (* (2, 1) + (1, 1) *)
    { simpl. auto. }
    iRename "PCS'" into "PCS".
    iDestruct "HOWNER" as "[(%EQ & LW & P) | (#OBL & #PRM & #AO & PENDING & %κack & REST)]".
    { subst.
      iMod (Ticket_alloc _ D n [κu2; γs2; κack2; b] with "TB") as "(TB & ISSUED & WAIT)".
      { ii. apply HD in H. lia. }
      iMod (activate_tpromise with "DPRM2 PO2") as "[#PRM2 #AO2]". iClear "DPRM2".
      iMod (link_new_fine κu2 κack2 l υ 0 with "[PCa2']") as "#LINK". iFrame. auto.
      iMod (AuthExcls.b_w_update _ _ _ (κu2, γs2, b) with "LB LW") as "(LB & LW)".
      iMod ("TI_CLOSE" with "[- POST PCS PCS'' PC2 PC2' DUTY CCS ISSUED]") as "_".
      { iEval (unfold tklockInv; simpl; red_tl_all).
        iExists n. iEval (red_tl; simpl). iExists (n+1). iEval (red_tl; simpl).
        iExists κu2. iEval (red_tl; simpl). iExists γs2. iEval (red_tl; simpl).
        iExists b. iEval (red_tl; simpl). iExists (D ∪ {[n]}). iEval (red_tl_all; simpl). iFrame.
        iSplit.
        { iPureIntro; auto. split; ii.
          { enough (tk = n). subst; set_solver. lia. }
          { rewrite elem_of_union in H; destruct H.
            { apply HD in H; lia. }
            { rewrite elem_of_singleton in H; clarify; lia. }
          }
        }
        iSplit; [done|].
        iSplitR "HWAIT".
        { iRight. iFrame. repeat iSplitR; try done. iExists κack2. iEval (red_tl_all). iFrame. iRight. iFrame. }
        assert (D = ∅). apply elem_of_equiv_empty_L. ii. apply HD in H; lia. subst.
        rewrite ! red_tl_big_sepS; simpl. rewrite big_opS_union. iSplitR.
        { iApply big_sepS_empty. done. }
        iApply (big_sepS_singleton); red_tl_all; iLeft. auto. set_solver.
      }
      iPoseProof (pc_split _ _ 2 with "PC2") as "[PC2'' PC2]".
      iApply (TicketLock_lock_loop_spec _ _ N with "[DUTY PCS'' PC2'' CCS ISSUED]"). auto.
      { red_tl_all. iEval (rewrite red_syn_inv; rewrite red_syn_tgt_interp_as; simpl). iFrame. iSplit; done. }
      red_tl_all; simpl. iIntros (_) "(DUTY & WL & P)". rred2r.
      iApply (wpsim_yieldR with "[DUTY PCS PC2]"). auto.
      { iSplitL "DUTY". done. iApply (pcs_cons_fold with "[PCS PC2]"). iFrame. }
      iIntros "DUTY _". rred2r. iApply wpsim_tauR. rred2r.
      iApply ("POST" with "[-]"). iExists κu2. red_tl. iExists γs2. red_tl_all. iFrame.
    }
    { iMod (link_new_fine κu κack2 l υ 0 with "[PCa2']") as "#LINK". auto.
      iAssert (⌜o < n⌝)%I with "[REST TB]" as "%HON".
      { iEval (red_tl_all) in "REST". iDestruct "REST" as "[WAIT _]".
        iPoseProof (Ticket_black_wait with "TB WAIT") as "%H". iPureIntro. apply HD. auto.
      }
      iMod (Ticket_alloc _ D n [κu2; γs2; κack2; b] with "TB") as "(TB & ISSUED & WAIT)".
      { ii. apply HD in H. lia. }
      iMod ("TI_CLOSE" with "[- POST PCS PCS'' PC2 PC2' DUTY CCS ISSUED]") as "_".
      { iEval (unfold tklockInv; simpl; red_tl_all).
        iExists o. iEval (red_tl; simpl). iExists (n+1). iEval (red_tl; simpl).
        iExists κu. iEval (red_tl; simpl). iExists γs. iEval (red_tl; simpl).
        iExists pass. iEval (red_tl; simpl). iExists (D ∪ {[n]}). iEval (red_tl_all; simpl). iFrame.
        iSplitR.
        { iPureIntro; auto. split; ii.
          { destruct (Nat.eq_dec tk n). subst; set_solver. rewrite elem_of_union. left. apply HD. lia. }
          { rewrite elem_of_union in H; destruct H.
            { apply HD in H; lia. }
            { rewrite elem_of_singleton in H; clarify; lia. }
          }
        }
        iSplit; [done|].
        iSplitR "HWAIT PENDING2 PO2 WAIT PCa2".
        { iRight. iFrame. repeat iSplitR; try done. iExists κack. done. }
        rewrite ! red_tl_big_sepS; simpl. rewrite big_opS_union. iSplitL "HWAIT"; auto.
        iApply (big_sepS_singleton); red_tl_all; iRight. iSplit; auto.
        iExists κu2. red_tl. iExists κack2. red_tl. iExists γs2. red_tl_all; simpl. iFrame.
        repeat iSplit; auto.
        ii. apply HD in H. apply elem_of_singleton in H0; subst. lia.
      }
      iPoseProof (pc_split _ _ 2 with "PC2") as "[PC2'' PC2]".
      iApply (TicketLock_lock_loop_spec _ _ N with "[DUTY PCS'' PC2'' CCS ISSUED]"). auto.
      { red_tl_all. iEval (rewrite red_syn_inv; rewrite red_syn_tgt_interp_as; simpl). iFrame. iSplit; done. }
      red_tl_all; simpl. iIntros (_) "(DUTY & WL & P)". rred2r.
      iApply (wpsim_yieldR with "[DUTY PCS PC2]"). auto.
      { iSplitL "DUTY". done. iApply (pcs_cons_fold with "[PCS PC2]"). iFrame. }
      iIntros "DUTY _". rred2r. iApply wpsim_tauR. rred2r.
      iApply ("POST" with "[-]"). iExists κu2. red_tl. iExists γs2. red_tl_all. iFrame.
    }
  Unshelve. all: auto; lia.
  Qed.

  Lemma TicketLock_unlock_spec
        tid i
        (E : coPset)
        (IN : ⊤ ⊆ E)
    :
    ⊢ ∀ γt loc (P : sProp i) l b pass (ds : list (nat * nat * sProp i)) κu γs,
        [@ tid, i, E @]
          ⧼⟦((syn_tgt_interp_as i sndl (fun m => (s_memory_black m)))
              ∗ (⤉ isTicketLock i γt loc P l b)
              ∗ (⤉ P)
              ∗ (⤉ ○G γt (κu, γs, pass))
              ∗ (⤉ Duty(tid) ((κu, 0, ▿ γs tt) :: ds))
              ∗ ◇{((κu, 0, emp) :: ds)@1}(1, 3))%S, 1+i⟧⧽
            (OMod.close_itree Client (SCMem.mod gvs) (TicketLock.unlock loc))
              ⧼rv, ⟦((⤉ Duty(tid) ds))%S, 1+i⟧⧽
  .
  Proof.
    (* PREPROCESS *)
    iIntros. iStartTriple.
    iIntros "PRE POST". unfold TicketLock.unlock.
    iApply wpsim_discard. apply IN.
    iEval (red_tl_all; simpl; rewrite red_syn_tgt_interp_as; simpl; red_tl_all; simpl) in "PRE".
    iDestruct "PRE" as "(#MEM & ISLOCK & P & LW & DUTY & PCS)".
    iEval (unfold isTicketLock; red_tl_all; simpl) in "ISLOCK".
    iDestruct "ISLOCK" as (lo) "ISLOCK". iEval (red_tl_all; simpl) in "ISLOCK".
    iDestruct "ISLOCK" as (ln) "ISLOCK". iEval (red_tl_all; simpl) in "ISLOCK".
    iDestruct "ISLOCK" as (N) "ISLOCK". iEval (red_tl_all; simpl) in "ISLOCK".
    iDestruct "ISLOCK" as "(%NAME & %HLGT & %HEQ & INV)". clarify. rred2r.
    iEval (rewrite red_syn_inv; simpl) in "INV". iPoseProof "INV" as "#INV".
    (* YIELD *)
    iApply (wpsim_yieldR2 with "[DUTY PCS]").
    instantiate (1:=i); auto. instantiate (1:=3); auto. iFrame. done.
    iIntros "DUTY _ PCS". simpl. rred2r.
    (* OPEN INVARIANT *)
    iInv "INV" as "TI" "TI_CLOSE".
    iEval (unfold tklockInv; simpl; red_tl_all; simpl) in "TI".
    iDestruct "TI" as (o) "TI". iEval (red_tl; simpl) in "TI".
    iDestruct "TI" as (n) "TI". iEval (red_tl; simpl) in "TI".
    iDestruct "TI" as (κu') "TI". iEval (red_tl; simpl) in "TI".
    iDestruct "TI" as (γs') "TI". iEval (red_tl; simpl) in "TI".
    iDestruct "TI" as (pass') "TI". iEval (red_tl; simpl) in "TI".
    iDestruct "TI" as (D) "TI". iEval (red_tl_all; simpl) in "TI".
    iDestruct "TI" as
      "(LOPT & LNPT & TB & %HD & %HB & LB &
        [(_ & LW' & _) | (#OBL & #PRM & #AO & PENDING & %κack' & REST)] & HWAIT)".
    { iExFalso. iApply (AuthExcls.w_w_false with "LW LW'"). }
    iEval (red_tl_all; simpl) in "REST". iDestruct "REST" as "(WAIT & [ISSUED | [LW' _]])"; cycle 1.
    { iExFalso. iApply (AuthExcls.w_w_false with "LW LW'"). }
    iPoseProof (AuthExcls.b_w_eq with "LB LW") as "%EQ"; clarify. rename κack' into κack.
    (* LOAD *)
    iApply (SCMem_load_fun_spec with "[LOPT]"). instantiate (1:=i); auto.
    { pose proof mask_disjoint_ticketlock_state_tgt; set_solver. }
    { iFrame. done. }
    iIntros (rv) "[%EQ LOPT]". subst. rred2r. iApply wpsim_tauR. rred2r.
    (* CLOSE INVARIANT *)
    iMod ("TI_CLOSE" with "[- POST DUTY PCS ISSUED]") as "_".
    { iEval (unfold tklockInv; simpl; red_tl; simpl).
      iExists o. iEval (red_tl; simpl). iExists n. iEval (red_tl; simpl).
      iExists κu. iEval (red_tl; simpl). iExists γs. iEval (red_tl; simpl).
      iExists pass. iEval (red_tl; simpl). iExists D. iEval (red_tl_all; simpl).
      iFrame. iSplit; auto. iSplit; auto. iRight. iFrame. repeat iSplit; auto.
      iExists κack. red_tl_all. iFrame. iRight. iFrame.
    }
    (* YIELD *)
    iApply (wpsim_yieldR2 with "[DUTY PCS]").
    instantiate (1:=i); auto. instantiate (1:=2); auto. iSplitL "DUTY"; iFrame.
    iIntros "DUTY _ PCS". rred2r. simpl.
    (* OPEN INVARIANT *)
    clear HD HB n D.
    iInv "INV" as "TI" "TI_CLOSE". iEval (simpl; unfold tklockInv; red_tl_all; simpl) in "TI".
    iDestruct "TI" as (o2) "TI"; iEval (red_tl_all; simpl) in "TI".
    iDestruct "TI" as (n2) "TI"; iEval (red_tl_all; simpl) in "TI".
    iDestruct "TI" as (κu2) "TI"; iEval (red_tl_all; simpl) in "TI".
    iDestruct "TI" as (γs2) "TI"; iEval (red_tl_all; simpl) in "TI".
    iDestruct "TI" as (pass2) "TI"; iEval (red_tl_all; simpl) in "TI".
    iDestruct "TI" as (D2) "TI"; iEval (red_tl_all; simpl) in "TI".
    iDestruct "TI" as "(LOPT & LNPT & TB & %HD & %HB & LB & HOWNER & HWAIT)".
    iPoseProof (Ticket_black_issued with "TB ISSUED") as "%HIND2".
    iDestruct "HOWNER" as "[(%EQ & _) | (#OBL2 & #PRM2 & #AO2 & PENDING2 & %κack2 & REST)]".
    { subst; apply HD in HIND2; lia. }
    assert (D2 = D2 ∖ {[o]} ∪ {[o]}).
    { set_unfold. split; ii. destruct (Nat.eq_dec x o). subst. right; auto. left; auto.
      des; subst; auto.
    }
    iEval (setoid_rewrite H; rewrite red_tl_big_sepS) in "HWAIT". rewrite big_opS_union; cycle 1. set_solver.
    iDestruct "HWAIT" as "[HWAIT Ho]". rewrite big_sepS_singleton.
    iEval (red_tl_all; simpl) in "Ho". iDestruct "Ho" as "[%EQ | (%HGT & %κu'' & Ho)]"; cycle 1.
    { iEval (red_tl; simpl) in "Ho". iDestruct "Ho" as (κack'') "Ho".
      iEval (red_tl; simpl) in "Ho". iDestruct "Ho" as (γs'') "Ho".
      iEval (red_tl_all; simpl) in "Ho". iDestruct "Ho" as "(_ & _ & PO & _ & WAIT & _)".
      iPoseProof (Ticket_issued_wait with "ISSUED WAIT") as "%EQ". clarify.
      iExFalso. iApply (pending_not_active with "PO AO").
    }
    subst.
    iEval (red_tl_all; simpl) in "REST". iDestruct "REST" as "(WAIT & [ISSUED' | [LW P]])".
    { iExFalso. iApply (Ticket_issued_twice with "ISSUED ISSUED'"). }
    iPoseProof (Ticket_issued_wait with "ISSUED WAIT") as "%EQ". clarify.
    iClear "OBL PRM AO".
    iApply (SCMem_store_fun_spec with "[LOPT]"). instantiate (1:=i); auto.
    { pose proof mask_disjoint_ticketlock_state_tgt; set_solver. }
    { iFrame. done. }
    iIntros (rv) "LOPT". rred2r. iApply wpsim_tauR. rred2r.
    (* Fulfill the unlocking duty *)
    iMod (OneShots.pending_shot _ tt with "PENDING2") as "#DEAD2".
    iMod (duty_fulfill with "[DUTY]") as "DUTY".
    { iSplitL; auto. simpl; red_tl_all. iSplit; auto. }
    iPoseProof (pcs_cons_unfold with "PCS") as "[_ PCS]".
    iMod (Ticket_return with "TB ISSUED WAIT") as "TB".
    (* CLOSE INVARIANT *)
    destruct (Nat.eq_dec n2 (o2 + 1)).
    (* CASE 1 : NO ONE WAITING *)
    { subst.
      iMod ("TI_CLOSE" with "[- POST PCS DUTY]") as "_".
      { iEval (unfold tklockInv; simpl; red_tl; simpl).
        iExists (o2 + 1). iEval (red_tl; simpl). iExists (o2 + 1). iEval (red_tl; simpl).
        iExists κu2. iEval (red_tl; simpl). iExists γs2. iEval (red_tl; simpl).
        iExists pass2. iEval (red_tl; simpl). iExists (D2 ∖ {[o2]}). iEval (red_tl_all; simpl).
        iFrame. iSplit.
        { iPureIntro. split; ii. lia. set_unfold in H0. des. apply HD in H0. lia. }
        iSplit; [done|]. iSplitL "LW P".
        { iLeft. iFrame. auto. }
        assert (D2 ∖ {[o2]} = ∅).
        { apply elem_of_equiv_empty_L. ii. set_unfold in H0. des. apply HD in H0; lia. }
        rewrite H0. rewrite red_tl_big_sepS. iApply big_sepS_empty. done.
      }
      iApply (wpsim_yieldR2 with "[DUTY PCS]").
      instantiate (1:=i); auto. instantiate (1:=1); auto. iFrame.
      iIntros "DUTY _ _". rred2r. iApply wpsim_tauR. rred2r.
      iApply ("POST" with "[DUTY]"). red_tl; simpl. done.
    }
    (* CASE 2 : SOMEONE WAITING *)
    assert (D2 ∖ {[o2]} = {[1+o2]} ∪ list_to_set (seq (2 + o2) (n2 - (2 + o2)))).
    { set_unfold. split; ii. des.
      { apply HD in H0. destruct (lt_dec x (2+o2)). left. lia. right. apply elem_of_list_In. apply in_seq. lia. }
      des. subst. split; auto. apply HD in HIND2. apply HD. lia.
      apply elem_of_list_In in H0. apply in_seq in H0. split. apply HD. all: lia.
    }
    iEval (setoid_rewrite H0) in "HWAIT".
    rewrite ! big_opS_union; cycle 1.
    { set_unfold. ii. apply elem_of_list_In in H2. apply in_seq in H2. lia. }
    iDestruct "HWAIT" as "[HNEXT HWAIT]".
    iEval (rewrite big_sepS_singleton; red_tl_all; simpl) in "HNEXT".
    iDestruct "HNEXT" as "[%HNEXT | (_ & %κu3 & HNEXT)]"; [lia | ].
    iEval (red_tl) in "HNEXT". iDestruct "HNEXT" as (κack3) "HNEXT".
    iEval (red_tl) in "HNEXT". iDestruct "HNEXT" as (γs3) "HNEXT".
    iEval (red_tl_all; simpl) in "HNEXT". iDestruct "HNEXT" as "(#OBL3 & #DPRM3 & PO3 & PENDING3 & WAIT3 & _)".
    iPoseProof (activate_tpromise with "DPRM3 PO3") as "> [#PRM3 #AO3]". iClear "DPRM3". iClear "OBL2 PRM2 AO2".
    iMod (AuthExcls.b_w_update _ _ _ (κu3, γs3, b) with "LB LW") as "[LB LW]".
    (* Make new links *)
    iAssert ([∗ set] y ∈ (list_to_set (seq (2+o2) (n2 - (2+o2)))),
              #=( ObligationRA.edges_sat )=>
                (⌜y > o2 + 1⌝
                  ∗ (∃ (κu4 κack4 γs4 : nat),
                    (◆[κu4, l, υ]) ∗ (-[κu4](0)-⧖ (▿ γs4 tt)%S) ∗ (⧖ [κu4, (1/2)]) ∗ (△ γs4 1)
                    ∗ (Ticket_wait γt y [κu4; γs4; κack4; b])
                    ∗ (◇[κack4](l, υ * (b + (b + 1) * (y - (o2 + 1))))) ∗ (κu3 -(0)-◇ κack4))))%I
      with "[HWAIT]" as "HWAIT".
    { iApply (big_sepS_impl with "[HWAIT]"); iFrame. iModIntro. iIntros (x) "%XIN H".
      red_tl. iDestruct "H" as "[%HEQ | [%HGT HWAIT]]".
      { set_unfold in XIN. apply elem_of_list_In in XIN. apply in_seq in XIN. lia. }
      iDestruct "HWAIT" as (κu4) "HWAIT". red_tl. iDestruct "HWAIT" as (κack4) "HWAIT". red_tl.
      iDestruct "HWAIT" as (γs4) "HWAIT". red_tl_all. simpl.
      iDestruct "HWAIT" as "(#OBL4 & #DPRM4 & PO4 & PENDING4 & WAIT4 & PC4 & _)".
      iPoseProof (pc_split _ _ υ _ with "[PC4]") as "[PC4' PC4]".
      { iEval (rewrite Nat.mul_add_distr_l) in "PC4".
        iPoseProof (pc_split _ _ (υ * pass2) with "PC4") as "[_ PC4]".
        replace ((b + 1) * (x - o2)) with (1 + b + (b + 1) * (x - (o2 + 1))).
        iEval (rewrite !Nat.mul_add_distr_l) in "PC4". done.
        replace (x - (o2 + 1)) with (x - o2 - 1) by lia.
        assert (H': x - o2 > 0). lia. revert H'. generalize (x - o2). induction n0; ii; try lia.
      }
      iSplitR.
      { iModIntro; iPureIntro. set_unfold in XIN; apply elem_of_list_In in XIN; apply in_seq in XIN. lia. }
      { iPoseProof (link_new_fine with "[PC4']") as "LINK".
        iSplit. iApply "OBL3". instantiate (1:=0). done. iMod "LINK". iModIntro.
        iExists κu4, κack4, γs4. rewrite Nat.mul_add_distr_l. iFrame. repeat iSplit; done.
      }
    }
    iMod (big_sepS_bupd with "HWAIT") as "HWAIT".
    iMod ("TI_CLOSE" with "[- POST PCS DUTY]") as "_".
    { simpl. iEval (unfold tklockInv; simpl; red_tl; simpl).
      iExists (o2 + 1). iEval (red_tl; simpl). iExists n2. iEval (red_tl; simpl).
      iExists κu3. iEval (red_tl; simpl). iExists γs3. iEval (red_tl; simpl).
      iExists b. iEval (red_tl; simpl). iExists (D2 ∖ {[o2]}). iEval (red_tl_all; simpl). iFrame.
      iSplit.
      { iPureIntro. rewrite H0. split; ii.
        { apply elem_of_union. destruct (Nat.eq_dec tk (1 + o2)). left; set_solver.
          right. set_unfold. apply elem_of_list_In. apply in_seq. lia.
        }
        { apply HD in HIND2. apply elem_of_union in H1; des. apply elem_of_singleton in H1; subst; lia.
          set_unfold in H1. apply elem_of_list_In in H1. apply in_seq in H1. lia.
        }
      }
      iSplit; [done|].
      iSplitR "HWAIT".
      { iRight. repeat iSplit; auto. iFrame.
        iExists κack3. red_tl_all; simpl. do 2 replace (o2 + 1) with (S o2) by lia. iFrame. iRight. iFrame.
      }
      rewrite ! red_tl_big_sepS.
      rewrite H0. rewrite ! big_opS_union; cycle 1.
      { set_unfold. ii. apply elem_of_list_In in H2. apply in_seq in H2. lia. }
      iSplitR "HWAIT".
      { rewrite big_sepS_singleton. red_tl_all. iLeft; iPureIntro; lia. }
      iApply (big_sepS_impl with "HWAIT"). iModIntro. iIntros (x) "%XIN H".
      iDestruct "H" as "(%HXO & %κu4 & %κack4 & %γs4 & #OBL4 & #DPRM4 & PO4 & PENDING4 & WAIT4 & PC4 & #LINK4)".
      red_tl_all. iRight. iSplit; auto.
      iExists κu4; red_tl; iExists κack4; red_tl; iExists γs4; red_tl_all; simpl; iFrame. repeat iSplit; done.
    }
    iApply (wpsim_yieldR2 with "[DUTY PCS]").
    instantiate (1:=i); auto. instantiate (1:=1); auto. iFrame.
    iIntros "DUTY _ _". rred2r. iApply wpsim_tauR. rred2r.
    iApply ("POST" with "[DUTY]"). simpl. red_tl; simpl. done.
  Unshelve. all: auto.
  Qed.

End SPEC.
Global Opaque TicketLock.lock TicketLock.unlock.