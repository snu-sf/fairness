From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Import pind Axioms ITreeLib Red TRed IRed2 WFLibLarge.
From Fairness Require Import FairBeh Mod Linking.
From Fairness Require Import PCM IProp IPM IPropAux.
From Fairness Require Import IndexedInvariants OpticsInterp SimWeakest.
From Fairness Require Import TemporalLogic SCMemSpec LifetimeRA TicketLockRA.

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

    (** TODO : more rules for module composition. *)
    (* Definition omod : Mod.t := *)
    (*   Mod.mk *)
    (*     (* tt *) *)
    (*     (Mod.st_init Client) *)
    (*     (Mod.get_funs [("lock", Mod.wrap_fun lock); *)
    (*                    ("unlock", Mod.wrap_fun unlock)]) *)
    (* . *)

    (* Definition module gvs : Mod.t := *)
    (*   OMod.close *)
    (*     (omod) *)
    (*     (SCMem.mod gvs) *)
    (* . *)

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
  Context {HasShots : @GRA.inG ShotsRA Γ}.

  Ltac red_tl_all := red_tl; red_tl_memra; red_tl_ticket.

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

  (** Invariants. *)
  (* Ref: Lecture Notes on Iris. *)
  (* Definition tklockInv (i : nat) (r sr: nat) (lo ln : SCMem.val) (P : sProp i) (l : nat)
    : sProp (1+i) :=
    (∃ (o n o_obl : τ{nat, 1+i}) (D : τ{gset nat, 1+i}),
        (⤉ (lo ↦ o))
          ∗ (⤉ (ln ↦ n))
          ∗ (⤉ (s_ticket_black r o D))
          ∗ (⤉ (s_shots_base sr n))
          ∗ (⌜forall tk, (tk < n) <-> (tk ∈ D)⌝)
          ∗ (((⤉ s_ticket_locked r o) ∗ (⤉P) ∗
               ((⌜o = n⌝) ∨ (⌜o < n⌝ ∗ ∃ (tid obl: τ{nat, 1+i}) (ds : τ{ listT (nat * nat * Φ)%stype, 1+i }),
                                        (⤉ Duty(tid) ((o_obl, 0, s_shots_shot sr o) :: ds))
                                        ∗ (⤉ ○Duty(tid) ds)
                                        ∗ ◇[o_obl](l, 4)
                                        ∗ (⤉ s_ticket_wait r o tid obl)
                                        ∗ (⤉ s_shots_pending sr o)
                                        ∗ ◆[o_obl, l])))
             ∨ (∃ (tid obl: τ{nat, 1+i}), ((⤉ s_ticket_issued r o tid obl)
                ∗ (⤉ s_shots_pending sr o)
                ∗ ◆[o_obl, l]
                ∗ (⤉ -[o_obl](0)-◇ s_shots_shot sr o)))
            )
          ∗ ([∗ (1+i) set] tk ∈ D,
              (⌜tk < o⌝ ∗ ∃ (tid obl : τ{nat}), (⤉ s_ticket_issued r (tk : nat) tid obl))
              ∨ (⌜tk = o⌝)
              ∨ (⌜tk > o⌝) ∗ (∃ (tid obl : τ{nat}) (ds : τ{ listT (nat * nat * Φ)%stype, 1+i}),
                  (⤉ Duty(tid) ds)
                  ∗ (⤉ ○Duty(tid) ds)
                  ∗ (⤉ s_ticket_wait r tk tid obl)
                  ∗ (⤉ s_shots_pending sr tk)
                  ∗ (◇[obl](1 + l, tk - o))
                  ∗ (o_obl -(0)-◇ obl))
            )
    )%S. *)

    Definition tklockInv (i : nat) (γt γs: nat) (lo ln : SCMem.val) (P : sProp i) (l : nat)
    : sProp i :=
    (∃ (o n κu : τ{nat, i}) (D : τ{gset nat, i}),
        (lo ↦ o)
          ∗ (ln ↦ n)
          ∗ (s_ticket_black γt o D)
          ∗ (s_shots_base γs n)
          ∗ ⌜forall tk, (tk < n) <-> (tk ∈ D)⌝
          ∗ ((s_ticket_locked γt o ∗ P ∗
               ((⌜o = n⌝) ∨ (⌜o < n⌝ ∗ ∃ (κack : τ{nat, i}),
                                        (s_ticket_wait γt o κu κack)
                                        ∗ (-[κu](0)-◇ s_shots_shot γs o κu)
                                        ∗ (⋈ [κu])
                                        ∗ (s_shots_pending γs o κu)
                                        ∗ ◆[κu, l])))
             ∨ (∃ (κack: τ{nat, i}),
                (s_ticket_issued γt o κu κack)
                ∗ (-[κu](0)-◇ s_shots_shot γs o κu)
                ∗ (⋈ [κu])
                ∗ (s_shots_pending γs o κu)
                ∗ ◆[κu, l])
            )
          ∗ ([∗ i set] tk ∈ D,
              (⌜tk < o⌝ ∗ ∃ (κu κack : τ{nat}), (s_ticket_issued γt (tk : nat) κu κack))
              ∨ (⌜tk = o⌝)
              ∨ (⌜tk > o⌝) ∗ (∃ (κu' κack' : τ{nat}),
                  (-[κu'](0)-⧖ s_shots_shot γs tk κu')
                  ∗ (⧖ [κu', (1/2)])
                  ∗ (s_ticket_wait γt tk κu' κack')
                  ∗ (s_shots_pending γs tk κu')
                  ∗ (◇[κack'](1 + l, tk - o))
                  ∗ (κu -(0)-◇ κack')
                  ∗ ◆[κu', l])
            )
    )%S.

  (* Namespace for TicketLock invariants. *)
  Definition N_TicketLock : namespace := (nroot .@ "TicketLock").

  Lemma mask_disjoint_ticketlock_state_tgt : ↑N_TicketLock ## (↑N_state_tgt : coPset).
  Proof. apply ndot_ne_disjoint. ss. Qed.

  Definition isTicketLock i (γt γs: nat) (v : SCMem.val * SCMem.val) (P : sProp i) (l : nat)
    : sProp i :=
    (∃ (lo ln : τ{SCMem.val}) (N : τ{namespace, i}),
        (⌜(↑N ⊆ (↑N_TicketLock : coPset))⌝)
          ∗ (⌜0 < l⌝) ∗ (⌜v = (lo, ln)⌝) ∗ syn_inv i N (tklockInv i γt γs lo ln P l))%S.

  Global Instance isSpinlock_persistent i r or v P l : Persistent (⟦isTicketLock i r or v P l, i⟧).
  Proof.
    unfold Persistent. iIntros "H". unfold isTicketLock.
    red_tl. iDestruct "H" as "[%lo H]". iExists lo.
    red_tl. iDestruct "H" as "[%ln H]". iExists ln.
    red_tl. iDestruct "H" as "[%N H]". iExists N.
    red_tl. rewrite red_syn_inv. iDestruct "H" as "#H". auto.
  Qed.

  Lemma make_isTicketLock
        i lo ln P l (LT : 0 < l)
        Es
    :
    ⊢
      ⟦((⤉ (lo ↦ 0)) ∗ (⤉ (ln ↦ 0)) ∗ (⤉ P) ∗ (⤉ s_ticket_auth) ∗ (⤉ s_shots_auth))%S, 1+i⟧
        -∗
        ⟦(∃ (γr γs : τ{nat, 1+i}), =|1+i|={Es}=> (⤉ isTicketLock i γr γs (lo, ln) P l))%S, 1+i⟧.
  Proof.
    simpl. red_tl_all; simpl. iIntros "(LO & LN & P & TAUTH & OTAUTH)".
    iPoseProof (TicketRA_alloc 0 with "TAUTH") as "(%r & ALLOC)". iExists r. red_tl; simpl.
    iPoseProof (ShotsRA_alloc with "OTAUTH") as "(%sr & OALLOC)". iExists sr.
    rewrite red_syn_fupd; simpl. iMod "ALLOC" as "(TAUTH & TB & TL)". iMod "OALLOC" as "(OAUTH & OBASE)".
    iMod ((FUpd_alloc _ _ _ i (N_TicketLock)) (tklockInv i r sr lo ln P l) with "[-]") as "#TINV". auto.
    { unfold tklockInv. simpl. red_tl. iExists 0. red_tl; simpl. iExists 0.
      red_tl; simpl. iExists 0. red_tl; simpl. iExists ∅.
      red_tl_all; simpl. iFrame. iSplit; auto.
      (* iSplit. *)
      { iPureIntro. split; i; inv H. }
      iSplitL; cycle 1. auto.
      iLeft. iSplitL "TL"; auto. iSplitL "P"; auto.
    }
    iModIntro.
    unfold isTicketLock. red_tl; simpl. iExists lo. red_tl; simpl. iExists ln. red_tl; simpl.
    iExists N_TicketLock. red_tl.
    iSplitL ""; try (iPureIntro; set_solver).
    iSplitL ""; try iPureIntro; auto.
  Qed.

  Lemma TicketLock_lock_spec
        tid i
        (E : coPset)
        (IN : ⊤ ⊆ E)
    :
    ⊢ ∀ γt γs lo ln (P : sProp i) l (ds : list (nat * nat * sProp i)),
        [@ tid, i, E @]
          ⧼⟦(((syn_tgt_interp_as i sndl (fun m => (s_memory_black m)))
                ∗ (⤉ isTicketLock i γt γs (lo, ln) P l)
                ∗ (⤉ (Duty(tid) ds))
                ∗ ⤉ ◇{ds@1}(5 + l, 1))%S), 1+i⟧⧽
            (OMod.close_itree Client (SCMem.mod gvs) (TicketLock.lock (lo, ln)))
            ⧼rv, ⟦(∃ (o κu : τ{nat, 1+i}),
                    (⤉ P)
                    ∗ (⤉ s_ticket_locked γt o)
                    ∗ (⤉ (Duty(tid) ((κu, 0, s_shots_shot γs o κu) :: ds)))
                    ∗ ◇[κu](l, 1))%S, 1+i⟧⧽
  .
  Proof.
    iIntros. iStartTriple. iIntros "PRE POST". unfold TicketLock.lock.
    iApply wpsim_discard. apply IN.
    unfold isTicketLock. iEval (red_tl_all; simpl; rewrite red_syn_tgt_interp_as) in "PRE".
    iEval (red_tl_all; simpl) in "PRE".
    iDestruct "PRE" as "(#MEM & PRE & DUTY & PCS)".
    iDestruct "PRE" as (lo') "PRE". iEval (red_tl_all; simpl) in "PRE".
    iDestruct "PRE" as (ln') "PRE". iEval (red_tl_all; simpl) in "PRE".
    iDestruct "PRE" as (N) "PRE". iEval (red_tl_all; simpl; rewrite red_syn_inv) in "PRE".
    iDestruct "PRE" as "(%SUB & %GT & %EQ & #TINV)". symmetry in EQ. clarify.

    (* YIELD *)
    rred2r.
    iMod (pcs_drop _ _ 1 _ (4+l) 3 with "[PCS]") as "PCS". 2:{ iFrame. } auto.
    iMod (pcs_decr _ _ 1 _ with "PCS") as "[PCS' PCS]". auto.
    iMod (pcs_drop _ _ 1 _ 1 4 with "PCS'") as "PCS'". lia.
    iCombine "DUTY" "PCS'" as "DUTY".
    iApply (wpsim_yieldR2 with "DUTY"). auto. auto.
    iIntros "DUTY CRED PCS'".

    (* OPEN *)
    iInv "TINV" as "TI" "TI_CLOSE".
    iEval (unfold tklockInv; simpl; red_tl_all) in "TI".
    iDestruct "TI" as (o) "TI"; iEval (red_tl_all; simpl) in "TI".
    iDestruct "TI" as (n) "TI"; iEval (red_tl_all; simpl) in "TI".
    iDestruct "TI" as (κu) "TI"; iEval (red_tl_all; simpl) in "TI".
    iDestruct "TI" as (D) "TI"; iEval (red_tl_all; simpl) in "TI".

    destruct (Nat.eq_dec o n).
    (* SUCCESS *) (* Required pcs : (1+l, 1) *)
    { subst. iClear "CRED".
      iDestruct "TI" as "(LOPT & LNPT & TB & SHOTS_BASE & %HD & HCOND & HWAIT)". rred2r.
      (* FAA *)
      iApply (SCMem_faa_fun_spec with "[LNPT MEM]"). auto.
      { pose proof mask_disjoint_ticketlock_state_tgt. set_solver. }
      { iSplitR "LNPT"; done. }
      iIntros (rv) "(%EQ & LNPT)". subst. iEval (ss) in "LNPT". rred2r. iApply wpsim_tauR. rred2r.
      (* ALLOCATE TICKETS AND OBLIGATIONS TO PUT IN *)
      iMod (alloc_obligation l 5) as "(%κu' & #OBL & PC & PO)". iEval (rewrite <- Qp.half_half) in "PO".
      iPoseProof (pending_split _ (1/2) (1/2) with "PO") as "[PO PO']".
      iPoseProof (pc_split _ _ 1 _ with "[PC]") as "[PC' PC]". simpl. done.
      iAssert (#=> ◇[κu'](1, 1))%I with "[PC']" as "> PC'".
      { destruct (Nat.eq_dec l 1); [subst; done | ].
        iMod (pc_drop _ 1 l _ 1 1 with "[PC']") as "PC'". auto. done. done.
      }
      iPoseProof (duty_add with "[DUTY PC' PO'] []") as "> DUTY".
      { iSplitL "DUTY"; [done | ]. iSplitL "PC'"; done. }
      { instantiate (1:=(s_shots_shot γs n κu' : sProp i)%S). iModIntro. simpl.
        red_tl_all. simpl. iIntros. iModIntro. done.
      }
      iPoseProof (duty_delayed_tpromise with "DUTY") as "#DPRM".
      { simpl. left; auto. }
      iMod (activate_tpromise with "DPRM PO") as "[#PRM #AO]". iClear "DPRM".
      iMod (Ticket_alloc γt n D n κu' with "TB") as "(TB & ISSUED1 & WAIT)".
      { intros H; apply HD in H; lia. }
      iDestruct "HCOND" as "[TKL | [%κack' TCONT]]"; cycle 1.
      { iEval (red_tl_all; simpl) in "TCONT". iDestruct "TCONT" as "(ISSUED2 & _)".
        iExFalso. iApply (Ticket_issued_twice γt n with "[ISSUED1 ISSUED2]"). iFrame.
      }
      iDestruct "TKL" as "(TKL & P & [_ | [%NEQ _]])"; cycle 1. lia.
      iMod (Shots_alloc κu' with "SHOTS_BASE") as "[SHOTS_BASE PENDING]".
      (* CLOSE *)
      iMod ("TI_CLOSE" with "[- POST PCS PCS' PC TKL P DUTY WAIT]") as "_".
      { iEval (unfold tklockInv; simpl; red_tl_all). iExists n.
        iEval (red_tl; simpl). iExists (n+1). iEval (red_tl; simpl). iExists κu'.
        iEval (red_tl; simpl). iExists (D ∪ {[n]}). iEval (red_tl_all; simpl). iFrame.
        iSplitL "SHOTS_BASE". { iEval (rewrite Nat.add_comm). done. }
        iSplit.
        { iPureIntro; auto. split; ii.
          { destruct (Nat.eq_dec tk n); [set_solver|].
            assert (HLT : tk < n) by lia; apply HD in HLT; set_solver.
          }
          { rewrite elem_of_union in H; destruct H.
            { apply HD in H; lia. } { rewrite elem_of_singleton in H; clarify; lia. }
          }
        }
        iSplitL "ISSUED1 PENDING".
        { iRight. iExists κu'. red_tl_all. iFrame. simpl. iSplit; [done | iSplit; done]. }
        { repeat rewrite red_tl_big_sepS. rewrite big_opS_union. iSplitL; cycle 1.
          { rewrite big_sepS_singleton. red_tl_all. iRight; iLeft. done. }
          { iApply (big_sepS_impl with "HWAIT"). iModIntro. iIntros "%x %HXD PRE".
            red_tl_all. iLeft. iSplitR.
            { iPureIntro. apply HD in HXD. lia. }
            { iDestruct "PRE" as "[[%HLT H] | [%HEQ | [%HGT H]]]".
              { done. }
              { subst. apply HD in HXD; lia. }
              { apply HD in HXD; lia. }
            }
          }
          set_unfold. ii. subst. apply HD in H; lia.
        }
      }
      clear κu. rename κu' into κu.
      iEval (rewrite unfold_iter_eq; rred2r).
      (* YIELD *)
      iPoseProof (pc_split _ _ 3 _ with "PC") as "[PC' PC]".
      iAssert (#=> ◇[κu](1, 3))%I with "[PC']" as "> PC'".
      { destruct (Nat.eq_dec l 1); [subst; done | ].
        iMod (pc_drop _ 1 l _ 3 3 with "[PC']") as "PC'". auto. done. done.
      }
      iApply (wpsim_yieldR2 with "[DUTY PCS' PC']").
      { instantiate (1 := i). auto. }
      { instantiate (1 := 3). auto. }
      { iSplitL "DUTY". done.
        iApply (pcs_cons_fold with "[PCS' PC']").
        { iEval (rewrite Nat.add_comm). simpl. iSplitL "PC'"; done. }
      }
      iIntros "DUTY _ PCS'". simpl. rred2r.
      (* LOAD - OPEN INVARIANT *)
      iInv "TINV" as "TI" "TI_CLOSE".
      iEval (unfold tklockInv; simpl; red_tl_all) in "TI".
      iDestruct "TI" as (o') "TI"; iEval (red_tl_all; simpl) in "TI".
      iDestruct "TI" as (n') "TI"; iEval (red_tl_all; simpl) in "TI".
      iDestruct "TI" as (κu') "TI"; iEval (red_tl_all; simpl) in "TI".
      iDestruct "TI" as (D') "TI"; iEval (red_tl_all; simpl) in "TI".
      iDestruct "TI"
        as "(LOPT & LNPT & TB & SHOTS_BASE & %HD' & [(TKL' & P' & _) | TISSUED] & HWAIT)".
      { iExFalso; iApply (Ticket_locked_twice with "[TKL TKL']"). iSplitL "TKL"; done. }
      iPoseProof (Ticket_black_locked with "[TKL TB]") as "%EQ".
      iSplitL "TKL"; done. symmetry in EQ; subst.
      (* LOAD *)
      iApply (SCMem_load_fun_spec with "[LOPT]"). auto.
      { pose proof mask_disjoint_ticketlock_state_tgt. set_solver. }
      { iSplitR "LOPT"; done. }
      iIntros (rv) "[%EQ LOPT]"; subst. rred2r. iApply (wpsim_tauR). rred2r.
      (* CLOSE *)
      iMod ("TI_CLOSE" with "[- POST PCS TKL P PC DUTY PCS' WAIT]") as "_".
      { iEval (unfold tklockInv; simpl; red_tl_all). iExists n.
        iEval (red_tl_all; simpl). iExists n'.
        iEval (red_tl_all; simpl). iExists κu'.
        iEval (red_tl_all; simpl). iExists D'.
        iEval (red_tl_all; simpl).
        iSplitL "LOPT"; auto. iSplitL "LNPT"; auto.
        iSplitL "TB"; auto. iSplitL "SHOTS_BASE"; try done. iSplit. auto.
        iSplitL "TISSUED". iRight. done. done.
      }
      clear n' HD' D' κu'.
      (* YIELD *)
      iCombine "DUTY" "PCS'" as "DUTY".
      iApply (wpsim_yieldR2 with "DUTY"). auto. auto.
      iIntros "DUTY _ PCS'".  rred2r.
      (* COMPARE *)
      iApply (SCMem_compare_fun_spec with "[MEM]"). auto.
      { pose proof mask_disjoint_ticketlock_state_tgt. set_solver. }
      { simpl. des_ifs. iApply (tgt_interp_as_equiv with "MEM"). iIntros. iSplit.
        { iIntros. simpl. red_tl; simpl. iSplit; [done | iPureIntro; auto]. }
        { simpl. red_tl; simpl. iIntros "[? _]". done. }
      }
      iIntros (rv) "[%EQ _]". exploit EQ. auto. i; subst. rred2r. iApply wpsim_tauR. rred2r.
      (* SYNC *)
      iCombine "DUTY" "PCS'" as "DUTY".
      iApply (wpsim_yieldR2 with "DUTY"). auto. auto.
      iIntros "DUTY _ PCS'".  rred2r. simpl. iApply wpsim_tauR. rred2r.
      (* POST *)
      iEval (red_tl) in "POST".
      iApply ("POST" with "[-]").
      { iExists n. red_tl. iExists κu. simpl. red_tl. iExists κu. red_tl_all; simpl. iFrame. }
    }
    Unshelve. all: auto; try lia.

    (* FAILURE *)
    iDestruct "TI" as "(LOPT & LNPT & TB & SHOTS_BASE & %HD' & HCOND & HWAIT)". rred2r.
    iApply (SCMem_faa_fun_spec with "[MEM LNPT]"). auto.
    { pose proof mask_disjoint_ticketlock_state_tgt. set_solver. }
    { iSplitR "LNPT"; done. }
    iIntros (rv) "[%EQ LNPT]". subst. iEval (simpl) in "LNPT".
    rred2r. iApply wpsim_tauR. rred2r.
    iEval (rewrite unfold_iter_eq; simpl). rred2r.
    iCombine "DUTY" "PCS'" as "DUTY".
    iApply (wpsim_yieldR_gen2 with "DUTY"). auto. simpl. auto.
    iIntros "DUTY _ PCS'". iEval (simpl) in "PCS'".
    (* Add a delayed promise to the duty *)
    iMod (alloc_obligation l 5) as "(%κu' & #OBLu' & PCu' & POu')".
    iEval (rewrite <- Qp.half_half) in "POu'".
    iPoseProof (pending_split _ (1/2) (1/2) with "POu'") as "[POu' POu'']".
    iPoseProof (pc_split _ _ 1 _ with "[PCu']") as "[PCu'' PCu']". done. simpl.
    iAssert (#=> ◇[κu'](1, 1))%I with "[PCu'']" as "> PCu''".
    { destruct (Nat.eq_dec l 1). subst; auto. destruct (gt_dec l 1); try lia.
      iMod (pc_drop _ 1 with "PCu''"); auto.
    }
    iPoseProof (duty_add with "[DUTY PCu'' POu'] []") as "> DUTY".
    { iSplitL "DUTY"; [done | ]. iSplitL "PCu''"; done. }
    { instantiate (1:=(s_shots_shot γs n κu' : sProp i)%S). iModIntro. simpl.
      red_tl_all. simpl. iIntros. iModIntro. done.
    }
    iPoseProof (duty_delayed_tpromise with "DUTY") as "#DPRM".
    { simpl. left; auto. }
    (* Allocate obligation for acquiring the lock *)
    iMod (alloc_obligation (1+l) (1 + (n - o))) as "(%κack' & #OBLack' & PCack' & POack')".
    (* Allocate my ticket and shot ra *)
    iMod (Ticket_alloc γt _ _ n κu' κack' with "TB") as "(TB & ISSUED & WAIT)".
    { intros H; apply HD' in H; lia. }
    iMod (Shots_alloc κu' with "SHOTS_BASE") as "(SHOTS_BASE & PENDING)".
    (* Make a ccs to do inductive reasoning on *)
    iMod (pcs_decr _ _ 1 _ with "PCS") as "[PCS'' PCS]". auto.
    iMod (ccs_make with "[PCS'']") as "[CCS _]".
    { iSplitR "PCS''". done. instantiate (1:=2). simpl. done. }
    (* Extract a link and a promise from the lock holder *)
    iAssert (⌜o < n⌝ ∗ ◆[κu, l] ∗ -[κu](0)-◇ ((s_shots_shot γs o κu : sProp i))%S)%I with "[TB HCOND]" as
      "(%HGT & #OBLu & #PRMu)".
    { iDestruct "HCOND" as
        "[(TKL & P & [%EQ | (%NEQ & %obl_o & COND)]) | (%κack & HCOND)]".
      { clarify. }
      { iEval (red_tl_all; simpl) in "COND".
        iDestruct "COND" as "(_ & #PRMU & _ & _ & #OBL_O)". iSplit; auto.
      }
      { red_tl. iDestruct "HCOND" as "(H & #PRMU & _ & _ & #OBL_O)". red_tl_all; simpl.
        iPoseProof (Ticket_black_issued with "[H TB]") as "%H". iFrame.
        enough (o ∈ D). apply HD' in H0. auto. set_solver.
      }
    }
    iPoseProof (pc_split _ _ 1 _ with "[PCack']") as "[PCack'' PCack']". done.
    iMod (link_new κu κack' l 0 0 with "[PCack'']") as "[#LINK1 _]".
    { iFrame. done. }
    (* CLOSING THE INVARIANT *)
    iMod ("TI_CLOSE" with "[- POST PCS' PCu' DUTY POack' ISSUED PCS CCS]") as "_".
    { iEval (unfold tklockInv; simpl; red_tl). iExists o.
      iEval (red_tl; simpl). iExists (n + 1).
      iEval (red_tl; simpl). iExists κu.
      iEval (red_tl; simpl). iExists (D ∪ {[n]}).
      iEval (red_tl_all; simpl). iFrame.
      iSplitL "SHOTS_BASE". { iEval (rewrite Nat.add_comm). done. }
      iSplit.
      { iPureIntro. split; i.
        { destruct (Nat.eq_dec tk n); [set_solver|].
          assert (HLT : tk < n) by lia; apply HD' in HLT; set_solver.
        }
        { rewrite elem_of_union in H; destruct H.
          { apply HD' in H; lia. } { rewrite elem_of_singleton in H; clarify; lia. }
        }
      }
      iSplitL "HCOND".
      { iDestruct "HCOND" as
        "[(LOCKED_O & P & [ %EQ | (%NEQ & COND) ]) | HCOND]".
        { lia. }
        { iLeft. iFrame. iRight. iFrame. iPureIntro. lia. }
        { iRight. iFrame. }
      }
      { repeat rewrite red_tl_big_sepS. rewrite big_opS_union. iSplitL "HWAIT"; cycle 1.
        { rewrite big_sepS_singleton. red_tl. iRight. iRight. iSplit.
          { iPureIntro. lia. }
          iExists κu'. red_tl_all; simpl. iExists κack'. red_tl_all; simpl. iFrame.
          repeat iSplit; done.
        }
        done. set_unfold. ii. subst. apply HD' in H; lia.
      }
    }
    clear HD'. iClear "PRMu OBLu LINK1 POack' PCS' DPRM". clear κu D o n0 HGT.
    iModIntro. rred2r.
    (* Induction on CCS *)
    iRevert "PCS DUTY POST ISSUED PCu'".
    iMod (ccs_ind2 with "CCS [-]") as "IND".
    2:{ iIntros "PCS". iMod (pcs_drop _ _ _ _ 2 1 with "PCS"). lia. iApply "IND". done. }
    iModIntro. iExists 0. iIntros "IH". iModIntro. iIntros "PCS DUTY POST ISSUED PC".
    (* Opening invariant *)
    iInv "TINV" as "TI" "TI_CLOSE".
    iEval (unfold tklockInv; simpl; red_tl) in "TI".
    iDestruct "TI" as (o') "TI"; iEval (red_tl; simpl) in "TI".
    iDestruct "TI" as (n') "TI"; iEval (red_tl; simpl) in "TI".
    iDestruct "TI" as (κu) "TI"; iEval (red_tl; simpl) in "TI".
    (* iDestruct "TI" as (γo') "TI"; iEval (red_tl; simpl) in "TI". *)
    iDestruct "TI" as (D) "TI"; iEval (red_tl_all; simpl) in "TI".
    iDestruct "TI" as "(LOPT & LNPT & TB & SHOTS_BASE & %HD' & TO & HWAIT)".
    (* Load *)
    iApply (SCMem_load_fun_spec with "[LOPT]"). auto.
    { pose proof mask_disjoint_ticketlock_state_tgt; set_solver. }
    { iSplit; iFrame. done. }
    iIntros (rv) "[%EQ LOPT]". subst. rred2r. iApply wpsim_tauR. rred2r.
    (* Yield *)
    destruct (Nat.eq_dec o' n).
    { (* Case 1 : My turn has arrived *)
      subst. iDestruct "TO" as "[(LOCKED_N & P & [%HNN' | H]) | (%κu'' & WAIT)]".
      { subst. iPoseProof (Ticket_black_issued with "[TB ISSUED]") as "%HIN". iFrame.
        apply HD' in HIN. lia.
      }
      2:{ iEval (red_tl_all; simpl) in "WAIT".
          iExFalso; iApply (Ticket_issued_twice with "[ISSUED WAIT]"). iDestruct "WAIT" as "[WAIT _]". iFrame.
      }
      iDestruct "H" as "(%HNN' & %κack & H)". iEval (red_tl_all; simpl) in "H".
      iDestruct "H" as "(WAIT & #PRM & #AO & PENDING & _)".
      iPoseProof (Ticket_issued_wait with "[ISSUED WAIT]") as "%EQ". iFrame. des; clarify.
      iMod (pcs_drop _ _ _ _ 1 2 with "PCS") as "PCS". lia.
      iPoseProof (pc_split _ _ 2 with "PC") as "[PC' PC]".
      iAssert (#=> ◇[κu](1, 2))%I with "[PC]" as "> PC".
      { destruct (Nat.eq_dec l 1). subst; auto. destruct (gt_dec l 1); try lia.
        iMod (pc_drop _ 1 with "PC"); auto.
      }
      iApply (wpsim_yieldR_gen2 with "[PCS PC DUTY]"). instantiate (1:=i). auto. instantiate (1:=2); auto.
      { iSplitL "DUTY". done. iApply (pcs_cons_fold); simpl. iSplitL "PC". iFrame. done. }
      iIntros "DUTY _ PCS". simpl.
      iMod ("TI_CLOSE" with "[- POST LOCKED_N P WAIT DUTY PCS PC']") as "_".
      { iEval (unfold tklockInv; simpl; red_tl). iExists n.
        iEval (red_tl; simpl). iExists n'. iEval (red_tl; simpl). iExists κu.
        iEval (red_tl; simpl). iExists D. red_tl_all. iFrame.
        iSplitR. auto. iRight. iExists κack. red_tl_all. simpl. iFrame.
        iSplit; [done | iSplit; done].
      }
      iModIntro. rred2r.
      iApply (SCMem_compare_fun_spec); auto.
      { simpl. des_ifs. iApply (tgt_interp_as_equiv with "MEM"). iIntros. iSplit.
        { iIntros. simpl. red_tl; simpl. iSplit; [done | iPureIntro; auto]. }
        { simpl. red_tl; simpl. iIntros "[? _]". done. }
      }
      iIntros (rv) "[%EQ _]". exploit EQ. auto. i; subst. rred2r. iApply wpsim_tauR. rred2r.
      iCombine "DUTY" "PCS" as "DUTY".
      iApply (wpsim_yieldR2 with "DUTY"). auto. auto.
      iIntros "DUTY _ PCS". rred2r. iApply (wpsim_tauR). rred2r.
      iEval (red_tl) in "POST".
      iApply ("POST" with "[-]").
      { iExists n. red_tl. iExists κu. red_tl_all; iExists κack. red_tl_all; simpl. iFrame.
        iPoseProof (pc_split _ l 1 1 with "PC'") as "[_ PC']". done. }
    }
    (* Case 2 : Not my turn yet *)
    (* Get my duty out of invariant *)
    iEval (rewrite red_tl_big_sepS) in "HWAIT".
    iPoseProof (Ticket_black_issued with "[TB ISSUED]") as "%HNN'".
    { iFrame. }
    assert (D = ((D ∖ {[n]}) ∪ {[n]})).
    { set_unfold. split; ii. destruct (Nat.eq_dec x n); auto. des; clarify; auto. }
    iEval (setoid_rewrite H) in "HWAIT".
    iEval (rewrite <- red_tl_big_sepS) in "HWAIT".
    iEval (rewrite red_tl_big_sepS; red_tl; simpl) in "HWAIT".
    rewrite big_opS_union; cycle 1. set_solver.
    iDestruct "HWAIT" as "[H1 H2]".
    rewrite big_sepS_singleton. iEval (red_tl_all; simpl) in "H2".
    iDestruct "H2" as "[ (_ & % & ISSUED2) | H2 ]".
    { iEval (red_tl_all; simpl) in "ISSUED2". iDestruct "ISSUED2" as "[% ISSUED2]".
      iExFalso; iApply (Ticket_issued_twice with "[ISSUED ISSUED2]"). red_tl_all; simpl. iFrame.
    }
    iDestruct "H2" as "[%HNO | (%HNO & %κu'' & H2) ]".
    { lia. }
    iEval (red_tl; simpl) in "H2". iDestruct "H2" as (κack'') "H2".
    iEval (red_tl_all; simpl) in "H2".
    iDestruct "H2" as "(#DPRM & PO & WAIT & PENDING & PC' & #LINK & #OBL)".
    iPoseProof (Ticket_issued_wait with "[ISSUED WAIT]") as "%EQ". iFrame. des; symmetry in EQ, EQ0; des; clarify.
    iMod (pcs_drop _ _ _ _ 1 4 with "PCS") as "PCS". lia. Unshelve. all: auto.
    iAssert (◆[κu, l] ∗ -[κu](0)-◇ (s_shots_shot γs o' κu)%S)%I with "[TO]" as "[#OBLu #PRMu']".
    { iDestruct "TO" as "[(TKL & P & [%EQ | (%NEQ & %κack & COND)]) | (%κack & ISSUED)]".
      { clarify. apply HD' in HNN'. lia. }
      { iEval (red_tl_all; simpl) in "COND".
        iDestruct "COND" as "(_ & ? & _ & _ & #?)". iSplit; done.
      }
      { red_tl_all. iDestruct "ISSUED" as "(_ & ? & _ & _ & ?)". iSplit; done. }
    }
    (* Yield *)
    iApply (wpsim_yieldR_gen_pending with "DUTY [PO] [PCS]"). auto.
    { instantiate (2:=[(κu', 0, s_shots_shot γs n κu')]). f_equal. }
    3:{ iApply (pps_cons_fold with "[PO]"). iSplitL; auto. iApply pps_nil. }
    { auto. } 2: done. auto.
    iIntros "DUTY CRED PPS PCS".
    iCombine "PRMu'" "CRED" as "C".
    iMod (tpromise_progress with "C") as "PC_O".
    iDestruct "PC_O" as "[PC_O | #DEAD]"; cycle 1.
    { iEval (simpl; red_tl_all) in "DEAD".
      iDestruct "TO" as "[(TKL & P & [%EQ | (%NEQ & %obl_o & COND)]) | (%tid' & ISSUED')]".
      { clarify. apply HD' in HNN'. lia. }
      { iEval (red_tl_all; simpl) in "COND".
        iDestruct "COND" as "(_ & _ & _ & PENDINGu' & _)".
        iExFalso. iApply (Shots_pending_not_shot with "[PENDINGu' DEAD]"). iFrame. done.
      }
      { iEval (red_tl_all; simpl) in "ISSUED'". iDestruct "ISSUED'" as "(_ & _ & _ & PENDING' & _)".
        iExFalso; iApply (Shots_pending_not_shot with "[PENDING' DEAD]"). iFrame. done.
      }
    }
    iMod (link_amplify with "[PC_O LINK]") as "PC_W". iFrame. done.
    (* Close the invariant *)
    iMod ("TI_CLOSE" with "[-IH POST ISSUED PC DUTY PCS PC_W]") as "_".
    { iEval (unfold tklockInv; simpl; red_tl). iExists o'.
      iEval (red_tl; simpl). iExists n'. iEval (red_tl; simpl). iExists κu.
      iEval (red_tl; simpl). iExists D. red_tl_all; simpl. iFrame.
      iSplitR. auto. iEval (rewrite H; rewrite red_tl_big_sepS).
      rewrite big_opS_union; cycle 1. set_solver. iFrame.
      rewrite big_sepS_singleton. red_tl. iRight. iRight. iSplit. auto.
      iExists κu'. red_tl; simpl. iExists κack'. red_tl; simpl. red_tl_all; simpl. iFrame.
      iSplitR; [done |]. iSplitL; [|iSplit; done].
      iPoseProof (pps_cons_unfold with "PPS") as "[PO _]". done.
    }
    iModIntro. rred2r.
    iApply (SCMem_compare_fun_spec); auto.
    { simpl. des_ifs. iApply (tgt_interp_as_equiv with "MEM"). iIntros. iSplit.
      { iIntros. simpl. red_tl; simpl. iSplit; [done | iPureIntro; auto]. }
      { simpl. red_tl; simpl. iIntros "[? _]". done. }
    }
    iIntros (rv) "[_ %NEQ]". exploit NEQ. ii. inv H0. lia. i; subst.
    rred2r. iApply wpsim_tauR. rred2r. iApply wpsim_tauR.
    iEval (rewrite unfold_iter_eq). rred2r.

    iInv "TINV" as "TI" "TI_CLOSE".
    iEval (unfold tklockInv; simpl; red_tl) in "TI".
    iDestruct "TI" as (o'') "TI"; iEval (red_tl; simpl) in "TI".
    iDestruct "TI" as (n'') "TI"; iEval (red_tl; simpl) in "TI".
    iDestruct "TI" as (κu'') "TI"; iEval (red_tl; simpl) in "TI".
    iDestruct "TI" as (D'') "TI"; iEval (red_tl_all; simpl) in "TI". clear HD' HNN'.
    iDestruct "TI" as "(LOPT & LNPT & TB & SHOTS_BASE & %HD' & TO & HWAIT)".
    
    destruct (Nat.eq_dec o'' n).
    { (* My turn has arrived *)
      subst. iDestruct "TO" as "[ (LOCKED_N & P & [ %HNN' | H ]) | [%tid' HISSUED]]".
      { subst. iPoseProof (Ticket_black_issued with "[TB ISSUED]") as "%HIN". iFrame.
        apply HD' in HIN. lia.
      }
      2:{ iEval (red_tl_all; simpl) in "HISSUED".
          iDestruct "HISSUED" as "(ISSUED' & _)".
          iExFalso; iApply (Ticket_issued_twice with "[ISSUED ISSUED']"). iFrame.
      }
      iDestruct "H" as "(%HNN' & %κack'' & H)". iEval (red_tl_all; simpl) in "H".
      iDestruct "H" as "(WAIT & #PRMu'' & #AOu'' & PENDING & #OBLu'')".
      iPoseProof (Ticket_issued_wait with "[WAIT ISSUED]") as "%EQ"; auto. iFrame. des; clarify.
      iPoseProof (pc_split _ _ 1 with "PC") as "[PC' PC]".
      iMod (pcs_decr _ _ 1 with "PCS") as "[PCS' PCS]". instantiate (1:=2). auto.
      iAssert (#=> ◇[κu''](1, 1))%I with "[PC']" as "> PC'".
      { destruct (Nat.eq_dec l 1). subst; auto. destruct (gt_dec l 1); try lia.
        iMod (pc_drop _ 1 with "PC'"); auto.
      }
      iApply (wpsim_yieldR_gen with "[PCS' PC' DUTY]"). instantiate (1:=i). auto.
      { iSplitL "DUTY". done. iApply (pcs_cons_fold); simpl. iSplitL "PC'". iFrame. done. }
      iIntros "DUTY CRED2".
      iMod ("TI_CLOSE" with "[LNPT TB SHOTS_BASE HWAIT PENDING LOPT ISSUED]") as "_".
      { iEval (unfold tklockInv; simpl; red_tl). iExists n.
        iEval (red_tl; simpl). iExists n''. iEval (red_tl; simpl). iExists κu''.
        iEval (red_tl; simpl). iExists D''. red_tl_all; simpl. iFrame.
        iSplitR. auto. iRight. iExists κack''. red_tl_all. iFrame. repeat iSplit; done.
      }
      iModIntro. rred2r.
      iInv "TINV" as "TI" "TI_CLOSE".
      iEval (unfold tklockInv; simpl; red_tl) in "TI".
      iDestruct "TI" as (o''') "TI"; iEval (red_tl; simpl) in "TI".
      iDestruct "TI" as (n''') "TI"; iEval (red_tl; simpl) in "TI".
      iDestruct "TI" as (κu''') "TI"; iEval (red_tl; simpl) in "TI".
      iDestruct "TI" as (D''') "TI"; iEval (red_tl_all; simpl) in "TI". clear HD' HNN'.
      iDestruct "TI" as "(LOPT & LNPT & TB & TI)".
      iPoseProof (Ticket_black_locked with "[LOCKED_N TB]") as "%EQ".
      iSplitL "LOCKED_N"; done. symmetry in EQ; subst.
      (* LOAD *)
      iApply (SCMem_load_fun_spec with "[LOPT]"). auto.
      { pose proof mask_disjoint_ticketlock_state_tgt. set_solver. }
      { iSplitR "LOPT"; done. }
      iIntros (rv) "[%EQ LOPT]"; subst. rred2r. iApply (wpsim_tauR). rred2r.
      iPoseProof (pc_split _ _ 1 with "PC") as "[PC' PC]".
      iAssert (#=> ◇[κu''](1, 1))%I with "[PC']" as "PC'".
      { destruct (Nat.eq_dec l 1). subst; auto. destruct (gt_dec l 1); try lia.
        iMod (pc_drop _ 1 with "PC'"); auto.
      }
      iMod "PC'". iMod (pcs_decr _ _ 1 with "PCS") as "[PCS' PCS]". auto.
      iApply (wpsim_yieldR_gen with "[PCS' PC' DUTY]"). instantiate (1:=i). auto.
      { iSplitL "DUTY". done. iApply (pcs_cons_fold); simpl. iSplitL "PC'". iFrame. done. }
      iIntros "DUTY _".
      iMod ("TI_CLOSE" with "[TB TI LNPT LOPT]") as "_".
      { iEval (unfold tklockInv; simpl; red_tl). iExists n.
        iEval (red_tl; simpl). iExists n'''. iEval (red_tl; simpl). iExists κu'''.
        iEval (red_tl; simpl). iExists D'''. red_tl_all. iFrame.
      }
      iModIntro. rred2r.
      iApply (SCMem_compare_fun_spec); auto.
      { simpl. des_ifs. iApply (tgt_interp_as_equiv with "MEM"). iIntros. iSplit.
        { iIntros. simpl. red_tl; simpl. iSplit; [done | iPureIntro; auto]. }
        { simpl. red_tl; simpl. iIntros "[? _]". done. }
      }
      iIntros (rv) "[%EQ _]". exploit EQ. auto. i; subst. rred2r. iApply wpsim_tauR. rred2r.
      iPoseProof (pc_split _ _ 1 with "PC") as "[PC' PC]".
      iAssert (#=> ◇[κu''](1, 1))%I with "[PC']" as "PC'".
      { destruct (Nat.eq_dec l 1). subst; auto. destruct (gt_dec l 1); try lia.
        iMod (pc_drop _ 1 with "PC'"); auto.
      }
      iMod "PC'".
      iApply (wpsim_yieldR with "[PCS PC' DUTY]"). instantiate (1:=i). auto.
      { iSplitL "DUTY". done. iApply (pcs_cons_fold); simpl. iSplitL "PC'". iFrame. done. }
      iIntros "DUTY _". rred2r. iApply (wpsim_tauR). rred2r.
      iEval (red_tl) in "POST".
      iApply ("POST" with "[-]").
      { iExists n. red_tl. iExists κu''. red_tl. iExists κack''. red_tl_all; simpl. iFrame. }
    }

    iPoseProof (Ticket_black_issued with "[ISSUED TB]") as "%HNN'".
    { iFrame. }
    assert (D'' = ((D'' ∖ {[n]}) ∪ {[n]})).
    { set_unfold. split; ii. destruct (Nat.eq_dec x n); auto. des; clarify; auto. }
    iEval (setoid_rewrite H0; red_tl_all; simpl) in "HWAIT".
    iEval (rewrite red_tl_big_sepS; red_tl; simpl) in "HWAIT".
    rewrite big_opS_union; cycle 1. set_solver.
    iDestruct "HWAIT" as "[H1 H2]".
    rewrite big_sepS_singleton. iEval (red_tl_all; simpl) in "H2".
    iDestruct "H2" as "[ (_ & TISSUED2) | H2 ]".
    { iDestruct "TISSUED2" as (tid') "T". iEval (red_tl_all) in "T".
      iDestruct "T" as (obl') "ISSUED2".
      iExFalso; iApply (Ticket_issued_twice with "[ISSUED ISSUED2]"). red_tl_all. iFrame.
    }
    iDestruct "H2" as "[%HNO' | (%HNO' & %κu''' & H2) ]".
    { lia. }
    iEval (red_tl; simpl) in "H2". iDestruct "H2" as (obl_w'') "H2".
    iEval (red_tl_all; simpl) in "H2".
    iDestruct "H2" as "(#DPRMo' & PO & WAIT & PENDING & PCo' & #LINK1 & #OBLo')".
    iPoseProof (Ticket_issued_wait with "[ISSUED WAIT]") as "%EQ". iFrame. des; clarify.
    iApply (wpsim_yieldR_gen_pending with "DUTY [PO] [PCS]"). auto.
    { instantiate (2:=[(κu''', 0, s_shots_shot γs n κu''')]). f_equal. }
    3:{ iApply (pps_cons_fold with "[PO]"). iSplitL; auto. iApply pps_nil. }
    { auto. } 2: done. lia.
    iIntros "DUTY CRED PPS PCS".
    iMod ("TI_CLOSE" with "[- POST IH ISSUED PC_W PC DUTY]") as "_".
    { iEval (unfold tklockInv; simpl; red_tl). iExists o''.
      iEval (red_tl; simpl). iExists n''. iEval (red_tl; simpl). iExists κu''.
      iEval (red_tl; simpl). iExists D''. red_tl_all; simpl. iFrame.
      iSplitR. auto. iEval (rewrite H0; rewrite red_tl_big_sepS).
      rewrite big_opS_union; cycle 1. set_solver. iFrame.
      rewrite big_sepS_singleton. red_tl. iRight. iRight. iSplit. auto.
      iExists κu'''. red_tl; simpl. iExists obl_w''. red_tl; simpl.
      red_tl_all; simpl. iFrame. repeat iSplit; auto.
      iPoseProof (pps_cons_unfold with "PPS") as "[PO _]". done.
    }
    iModIntro. rred2r.
    iMod ("IH" with "PC_W") as "IH". iApply ("IH" with "DUTY POST ISSUED PC").
  Unshelve. all: auto.
  Qed.

  Lemma TicketLock_unlock_spec
        tid i
        (E : coPset)
        (IN : ⊤ ⊆ E)
    :
    ⊢ ∀ γt γs lo ln (P : sProp i) l (ds : list (nat * nat * sProp i)) o κu κack,
        [@ tid, i, E @]
          ⧼⟦((syn_tgt_interp_as i sndl (fun m => (s_memory_black m)))
               ∗ (⤉ isTicketLock i γt γs (lo, ln) P l)
               ∗ (⤉ P)
               ∗ (⤉ s_ticket_locked γt o)
               ∗ (⤉ Duty(tid) ((κu, 0, s_shots_shot γs o κu) :: ds))
               ∗ ◇{((κu, 0, emp) :: ds)@1}(1, 3))%S, 1+i⟧⧽
            (OMod.close_itree Client (SCMem.mod gvs) (TicketLock.unlock (lo, ln)))
            ⧼rv, ⟦((⤉ Duty(tid) ds))%S, 1+i⟧⧽
  .
  Proof.
    (* PREPROCESS *)
    iIntros. iStartTriple.
    iIntros "PRE POST". unfold TicketLock.unlock. rred2r.
    iApply wpsim_discard. apply IN.
    iEval (red_tl_all; simpl; rewrite red_syn_tgt_interp_as; simpl; red_tl_all; simpl) in "PRE".
    iDestruct "PRE" as "(#MEM & ISLOCK & P & LOCKED & WAIT & DUTY & PCS)".
    iEval (unfold isTicketLock; red_tl_all; simpl) in "ISLOCK".
    iDestruct "ISLOCK" as (lo') "ISLOCK". iEval (red_tl_all; simpl) in "ISLOCK".
    iDestruct "ISLOCK" as (ln') "ISLOCK". iEval (red_tl_all; simpl) in "ISLOCK".
    iDestruct "ISLOCK" as (N) "ISLOCK". iEval (red_tl_all; simpl) in "ISLOCK".
    iDestruct "ISLOCK" as "(%NAME & %HLGT & %HEQ & TINV)". symmetry in HEQ. inv HEQ.
    iEval (rewrite red_syn_inv; simpl) in "TINV". iPoseProof "TINV" as "#TINV".
    (* YIELD *)
    iApply (wpsim_yieldR2 with "[DUTY PCS]").
    instantiate (1:=i); auto. instantiate (1:=3); auto. iFrame. done.
    iIntros "DUTY CRED PCS". rred2r.
    (* OPEN INVARIANT *)
    iInv "TINV" as "TI" "TI_CLOSE".
    iEval (unfold tklockInv; simpl; red_tl_all; simpl) in "TI".
    iDestruct "TI" as (o') "TI". iEval (red_tl; simpl) in "TI".
    iDestruct "TI" as (n') "TI". iEval (red_tl; simpl) in "TI".
    iDestruct "TI" as (κu') "TI". iEval (red_tl; simpl) in "TI".
    iDestruct "TI" as (D) "TI". iEval (red_tl_all; simpl) in "TI".
    iDestruct "TI" as "(LOPT & LNPT & TKB & SHOTS_BASE & %HD & [[LOCKED2 _] | [%κack' TI]] & HWAIT)".
    { iExFalso; iApply (Ticket_locked_twice with "[LOCKED LOCKED2]"). iFrame. }
    iPoseProof (Ticket_black_locked with "[TKB LOCKED]") as "%EQ". iFrame. symmetry in EQ; subst.
    iEval (red_tl_all; simpl) in "TI". iDestruct "TI" as "(ISSUED & TI)".
    iPoseProof (Ticket_issued_wait with "[ISSUED WAIT]") as "%EQ". iFrame. des; clarify.
    (* LOAD *)
    iApply (SCMem_load_fun_spec with "[LOPT]"). instantiate (1:=i); auto.
    { pose proof mask_disjoint_ticketlock_state_tgt; set_solver. }
    { iFrame. done. }
    iIntros (rv) "[%EQ LOPT]". subst. rred2r. iApply wpsim_tauR. rred2r.
    (* CLOSE INVARIANT *)
    iMod ("TI_CLOSE" with "[LNPT TKB SHOTS_BASE ISSUED TI HWAIT LOPT]") as "_".
    { iEval (unfold tklockInv; simpl; red_tl; simpl). iExists o.
      iEval (red_tl; simpl). iExists n'. iEval (red_tl; simpl). iExists κu.
      iEval (red_tl; simpl). iExists D.
      iEval (red_tl_all; simpl). iFrame. iSplit; auto. iRight. iExists κack. red_tl_all. iFrame.
    }
    (* YIELD *)
    iApply (wpsim_yieldR2 with "[DUTY PCS]").
    instantiate (1:=i); auto. instantiate (1:=2); auto. iFrame.
    iIntros "DUTY CRED2 PCS". rred2r. iEval (simpl) in "PCS".
    (* OPEN INVARIANT *)
    clear HD n' D.
    iInv "TINV" as "TI" "TI_CLOSE".
    iEval (unfold tklockInv; simpl; red_tl_all; simpl) in "TI".
    iDestruct "TI" as (o') "TI". iEval (red_tl; simpl) in "TI".
    iDestruct "TI" as (n) "TI". iEval (red_tl; simpl) in "TI".
    iDestruct "TI" as (κu') "TI". iEval (red_tl; simpl) in "TI".
    iDestruct "TI" as (D) "TI". iEval (red_tl_all; simpl) in "TI".
    iDestruct "TI" as "(LOPT & LNPT & TKB & SHOTS_BASE & %HD & [[LOCKED2 _] | [%κack' TI]] & HWAIT)".
    { iExFalso; iApply (Ticket_locked_twice with "[LOCKED LOCKED2]"). iFrame. }
    iEval (red_tl_all; simpl) in "TI".
    iDestruct "TI" as "(ISSUED & #PRM & #AO & PENDING & #OBL)".
    iPoseProof (Ticket_black_locked with "[TKB LOCKED]") as "%EQ". iFrame. symmetry in EQ; subst.
    iPoseProof (Ticket_issued_wait with "[ISSUED WAIT]") as "%EQ". iFrame. des; clarify.
    iMod (Shots_pending_shot with "PENDING") as "#DEAD".
    iMod (duty_fulfill (v:=i) with "[DUTY]") as "DUTY".
    { simpl. iSplitL "DUTY". done. red_tl_all. iSplit; done. }
    (* STORE *)
    iApply (SCMem_store_fun_spec with "[LOPT]"). instantiate (1:=i); auto.
    { pose proof mask_disjoint_ticketlock_state_tgt; set_solver. }
    { iFrame. done. }
    iIntros (rv) "LOPT". rred2r. iApply wpsim_tauR. rred2r.
    (* ALLOCATE OBLIGATIONS *)
    iMod (Ticket_update γt o (o + 1) with "[TKB LOCKED]") as "[TKB LOCKED]". iFrame.
    (* CLOSE INVARIANT *)
    destruct (Nat.eq_dec n (o + 1)).
    (* CASE 1 : NO ONE WAITING *)
    { subst.
      iMod ("TI_CLOSE" with "[- POST PCS DUTY]") as "_".
      { iEval (unfold tklockInv; simpl; red_tl; simpl). iExists (o + 1).
        iEval (red_tl; simpl). iExists (o + 1). iEval (red_tl; simpl). iExists κu.
        iEval (red_tl; simpl). iExists D. iEval (red_tl_all; simpl).
        iFrame. iSplit; auto. iSplitL "LOCKED P".
        { iLeft. iFrame. iLeft. auto. }
        rewrite ! red_tl_big_sepS.
        assert (D = D ∖ {[o]} ∪ {[o]}).
        { assert (o ∈ D) by (apply HD; lia). set_unfold. split; ii.
          destruct (Nat.eq_dec x o); [right | left]; auto. des; clarify; auto. }
        rewrite H. rewrite ! big_opS_union; cycle 1. set_solver. set_solver.
        iDestruct "HWAIT" as "[HWAIT HO]". iSplitL "HWAIT".
        { iPoseProof (big_sepS_impl with "HWAIT") as "IMPL".
          iApply "IMPL". iModIntro. iIntros (x) "%HIN HWAIT". red_tl_all.
          iDestruct "HWAIT" as "[[%LT ISSUED] | HWAIT]".
          { iLeft; iFrame. iPureIntro; lia. }
          iDestruct "HWAIT" as "[%EQ | [%HGT HWAIT]]".
          { subst. set_solver. }
          enough (x < o). lia.
          set_unfold in HIN. des. apply HD in HIN. lia.
        }
        rewrite ! big_sepS_singleton. red_tl_all. iLeft. iSplitR "ISSUED". iPureIntro; lia.
        iExists κu. red_tl. iExists κack. red_tl_all. done.
      }
      iPoseProof (pcs_cons_unfold with "PCS") as "[_ PCS]". simpl.
      iApply (wpsim_yieldR2 with "[DUTY PCS]").
      instantiate (1:=i); auto. instantiate (1:=1); auto. iFrame.
      iIntros "DUTY CRED3 PCS". rred2r. iApply wpsim_tauR. rred2r.
      iApply ("POST" with "[DUTY]"). simpl. red_tl; simpl. done.
    }
    (* CASE 2 : SOMEONE WAITING *)
    iPoseProof (Ticket_black_issued with "[TKB ISSUED]") as "%HOIND". iFrame.
    apply HD in HOIND.
    assert (D = list_to_set (seq 0 o) ∪ {[o]} ∪ {[1+o]} ∪ list_to_set (seq (2 + o) (n - (2 + o)))).
    { set_unfold. split; ii.
      { apply HD in H. destruct (lt_dec x o).
        { left. left. left. apply elem_of_list_In. apply in_seq. lia. }
        { destruct (lt_dec x (1+o)).
          { left. left. right. lia. }
          destruct (lt_dec x (2+o)). left; right; auto. lia.
          right. apply elem_of_list_In. apply in_seq. lia.
        }
      }
      apply HD. destruct H.
      { destruct H. destruct H. apply elem_of_list_In in H. apply in_seq in H. lia. lia. lia. }
      apply elem_of_list_In in H. apply in_seq in H. lia.
    }
    (* assert (D = ((D ∖ {[o + 1]}) ∪ {[o + 1]})). *)
    (* { set_unfold. split; ii. destruct (Nat.eq_dec x (o + 1)); auto. des; clarify; auto. apply HD. lia. } *)
    iEval (setoid_rewrite H) in "HWAIT".
    iEval (rewrite red_tl_big_sepS; red_tl; simpl) in "HWAIT".
    rewrite ! big_opS_union; cycle 1.
    { set_unfold. ii. apply elem_of_list_In in H0. apply in_seq in H0. lia. }
    { set_unfold. ii. destruct H0. apply elem_of_list_In in H0. apply in_seq in H0. lia. lia. }
    { set_unfold. ii. destruct H0. destruct H0. apply elem_of_list_In in H0, H1. apply in_seq in H0, H1. lia.
      apply elem_of_list_In in H1; apply in_seq in H1; lia. 
      clarify. apply elem_of_list_In in H1. apply in_seq in H1. lia. }
    iDestruct "HWAIT" as "[[[HW1 HW2] HW3] HW4]".
    iEval (rewrite big_sepS_singleton; red_tl_all; simpl) in "HW2".
    iEval (rewrite big_sepS_singleton; red_tl_all; simpl) in "HW3".
    iDestruct "HW2" as "[[%HW2 _]| [%HW2 | (%H' & % & HW2)]]"; [lia | | lia].
    iDestruct "HW3" as "[[%HW3 _]| [%HW3 | (%H' & %κu' & HW3)]]"; [lia | lia | ].
    iEval (red_tl; simpl) in "HW3". iDestruct "HW3" as (κack') "HW3".
    iEval (red_tl_all; simpl) in "HW3".
    iDestruct "HW3" as "(#DPRM' & PO' & WAIT' & PENDING' & PC' & #LINK' & #OBL')".
    replace (S o - o) with 1 by lia.
    iPoseProof (activate_tpromise with "DPRM' PO'") as "> [#PRM' #AO']".
    (* Make new links *)
    iAssert ([∗ set] y ∈ (list_to_set (seq (2+o) (n - (2+o)))),
              #=( ObligationRA.edges_sat )=>  
                (⌜y > o + 1⌝
                  ∗ (∃ κu κack,
                    -[κu](0)-⧖ (s_shots_shot γs y)
                    ∗ ⧖ [κu, (1/2)]
                    ∗ Ticket_wait γt y κu κack
                    ∗ Shots_pending γs y
                    ∗ ◇[κack](S l, y - (o + 1))
                    ∗ κu' -(0)-◇ κack
                    ∗ ◆[κu, l])))%I with "[HW4]" as "HW4".
    { iApply (big_sepS_impl with "[HW4]"); iFrame. iModIntro. iIntros (x) "%XIN H".
      red_tl. iDestruct "H" as "[[%HLT HI] | [%HEQ | [%HGT HWAIT]]]".
      { set_unfold in XIN. apply elem_of_list_In in XIN. apply in_seq in XIN. lia. }
      { subst. set_unfold in XIN. apply elem_of_list_In in XIN. apply in_seq in XIN. lia. }
      iDestruct "HWAIT" as (κu'') "HWAIT". red_tl. iDestruct "HWAIT" as (κack'') "HWAIT". red_tl.
      iDestruct "HWAIT" as "(#DPRM'' & PO'' & WAIT'' & PENDING'' & PC'' & #LINK'' & #OBL'')".
      iPoseProof (pc_split _ _ 1 _ with "[PC'']") as "[PC''1 PC''2]".
      { replace (x - o) with (1 + (x - (o + 1))) by lia. done. }
      iSplitR.
      { iModIntro; iPureIntro. set_unfold in XIN; apply elem_of_list_In in XIN; apply in_seq in XIN. lia. }
      { iPoseProof (link_new with "[PC''1]") as "[LINK _]".
        iSplit. iApply "OBL'". instantiate (1:=0). done. iMod "LINK". iModIntro. red_tl_all; simpl.
        iExists κu'', κack''. iFrame. iSplit; done.
      }
    }
    iMod (big_sepS_bupd with "HW4") as "HW4".
    iMod ("TI_CLOSE" with "[- POST PCS DUTY]") as "_".
    { simpl. iEval (unfold tklockInv; simpl; red_tl; simpl). iExists (o + 1).
      iEval (red_tl; simpl). iExists n. iEval (red_tl; simpl). iExists κu'.
      iEval (red_tl; simpl). iExists D. iEval (red_tl_all; simpl).
      iSplitL "LOPT"; auto. iSplitL "LNPT"; auto. iSplitL "TKB"; auto. iSplitL "SHOTS_BASE"; auto.
      iSplitR; auto.
      iSplitR "ISSUED HW1 HW4".
      { iLeft. iFrame. iRight. iSplit. iPureIntro; lia.
        iExists κack'. red_tl_all; simpl. do 2 replace (o + 1) with (S o) by lia. iFrame.
        repeat iSplit; done.
      }
      rewrite ! red_tl_big_sepS.
      rewrite H. rewrite ! big_opS_union; cycle 1.
      { set_unfold. ii. apply elem_of_list_In in H0. apply in_seq in H0. lia. }
      { set_unfold. ii. destruct H0. apply elem_of_list_In in H0. apply in_seq in H0. lia. lia. }
      { set_unfold. ii. destruct H0. destruct H0. apply elem_of_list_In in H0, H1. apply in_seq in H0, H1. lia.
        apply elem_of_list_In in H1; apply in_seq in H1; lia. 
        clarify. apply elem_of_list_In in H1. apply in_seq in H1. lia. }
      iSplitR "HW4".
      { iSplitL. iSplitL "HW1". iApply (big_sepS_impl with "HW1"). iModIntro. iIntros (x) "%XIN H".
        red_tl. iDestruct "H" as "[[%HLT HI] | [%HEQ | [%HGT HWAIT]]]".
        { iDestruct "HI" as (κux) "HI". red_tl.
          iDestruct "HI" as (κackx) "HI". iLeft. iSplit; auto. iPureIntro; lia.
          iExists κux. red_tl_all. iExists κackx; red_tl_all. done.
        }
        { subst. set_unfold in XIN. apply elem_of_list_In in XIN. apply in_seq in XIN. lia. }
        { set_unfold in XIN. apply elem_of_list_In in XIN. apply in_seq in XIN. lia. }
        { rewrite big_sepS_singleton. red_tl_all. iLeft. iSplit; auto. iPureIntro; lia.
          iExists κu; red_tl; iExists κack; red_tl_all; done.
        }
        rewrite big_sepS_singleton. red_tl_all. iRight; iLeft; iPureIntro; lia.
      }
      iApply (big_sepS_impl with "HW4"). iModIntro. iIntros (x) "%XIN H".
      iDestruct "H" as "(%HXO & %κux & %κackx & #DPRMx & POx & WAITx & PENDINGx & PCx & LINKx)".
      red_tl_all. iRight; iRight. iSplit; [iPureIntro; auto | ].
      iExists κux; red_tl; iExists κackx; red_tl_all; simpl; iFrame. done.
    }
    iPoseProof (pcs_cons_unfold with "PCS") as "[PC PCS]". simpl.
    iApply (wpsim_yieldR2 with "[DUTY PCS]").
    instantiate (1:=i); auto. instantiate (1:=1); auto. iFrame.
    iIntros "DUTY CRED3 PCS". rred2r. iApply wpsim_tauR. rred2r.
    iApply ("POST" with "[DUTY]"). simpl. red_tl; simpl. done.
  Unshelve. all: auto.
  Qed.
      
End SPEC.
Global Opaque TicketLock.lock TicketLock.unlock.