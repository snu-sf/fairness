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
  Definition tklockInv (i : nat) (r sr: nat) (lo ln : SCMem.val) (P : sProp i) (l : nat)
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
    )%S.

  (* Namespace for TicketLock invariants. *)
  Definition N_TicketLock : namespace := (nroot .@ "TicketLock").

  Lemma mask_disjoint_ticketlock_state_tgt : ↑N_TicketLock ## (↑N_state_tgt : coPset).
  Proof. apply ndot_ne_disjoint. ss. Qed.

  Definition isTicketLock i (r or: nat) (v : SCMem.val * SCMem.val) (P : sProp i) (l : nat)
    : sProp (1+i) :=
    (∃ (lo ln : τ{SCMem.val}) (N : τ{namespace, 1+i}),
        (⌜(↑N ⊆ (↑N_TicketLock : coPset))⌝)
          ∗ (⌜0 < l⌝) ∗ (⌜v = (lo, ln)⌝) ∗ syn_inv (1+i) N (tklockInv i r or lo ln P l))%S.

  Global Instance isSpinlock_persistent i r or v P l : Persistent (⟦isTicketLock i r or v P l, 1+i⟧).
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
      ⟦((⤉⤉ (lo ↦ 0)) ∗ (⤉⤉ (ln ↦ 0)) ∗ (⤉⤉ P) ∗ (⤉⤉ s_ticket_auth) ∗ (⤉⤉ s_shots_auth))%S, 2+i⟧
        -∗
        ⟦(∃ (r or : τ{nat, 2+i}), =|2+i|={Es}=> (⤉(isTicketLock i r or (lo, ln) P l)))%S, 2+i⟧.
  Proof.
    simpl. red_tl_all; simpl. iIntros "(LO & LN & P & TAUTH & OTAUTH)".
    iPoseProof (TicketRA_alloc 0 with "TAUTH") as "(%r & ALLOC)". iExists r. red_tl; simpl.
    iPoseProof (ShotsRA_alloc with "OTAUTH") as "(%sr & OALLOC)". iExists sr.
    rewrite red_syn_fupd; simpl. iMod "ALLOC" as "(TAUTH & TB & TL)". iMod "OALLOC" as "(OAUTH & OBASE)".
    iMod ((FUpd_alloc _ _ _ (S i) (N_TicketLock)) (tklockInv i r sr lo ln P l) with "[-]") as "#TINV". auto.
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
    ⊢ ∀ r sr lo ln (P : sProp i) l (ds : list (nat * nat * sProp i)),
        [@ tid, 1+i, E @]
          ⧼⟦(((syn_tgt_interp_as (1+i) sndl (fun m => ((s_memory_black m))))
                ∗ (⤉ isTicketLock i r sr (lo, ln) P l)
                ∗ (⤉⤉ (Duty(tid) ds))
                ∗ (⤉⤉ (○Duty(tid) ds))
                ∗ (⤉⤉ ●Duty(tid) ds)
                ∗ ⤉ ◇{ds@1}(5 + l, 1))%S), 2+i⟧⧽
            (OMod.close_itree Client (SCMem.mod gvs) (TicketLock.lock (lo, ln)))
            ⧼rv, ⟦(∃ (o u γo : τ{nat, 2+i}),
                      (⤉⤉ P)
                        ∗ (⤉⤉ (s_ticket_locked r o))
                        ∗ (⤉⤉ (Duty(tid) ((u, 0, s_shots_shot sr o) :: ds)))
                        ∗ (⤉⤉ (○Duty(tid) ds))
                        ∗ (⤉⤉ (●Duty(tid) ds))
                        ∗ ◇[u](l, 1))%S, 2+i⟧⧽
  .
  Proof.
    (* iIntros. iStartTriple. iIntros "PRE POST". unfold TicketLock.lock.
    iApply wpsim_discard. apply IN.
    unfold isTicketLock. iEval (red_tl_all; simpl; rewrite red_syn_tgt_interp_as) in "PRE".
    iEval (red_tl_all; simpl) in "PRE".
    iDestruct "PRE" as "(#MEM & PRE & DUTY & WDUTY & BDUTY & PCS)".
    iDestruct "PRE" as (lo') "PRE". iEval (red_tl_all; simpl) in "PRE".
    iDestruct "PRE" as (ln') "PRE". iEval (red_tl_all; simpl) in "PRE".
    iDestruct "PRE" as (N) "PRE". iEval (red_tl_all; simpl; rewrite red_syn_inv) in "PRE".
    iDestruct "PRE" as "(%SUB & %GT & %EQ & #TINV)". symmetry in EQ. clarify.

    (* YIELD *)
    rred2r.
    iMod (pcs_drop _ _ 1 _ (4+l) 3 with "[PCS]") as "PCS". 2:{ iFrame. } auto.
    iMod (pcs_decr _ _ 1 _ with "PCS") as "[PCS1 PCS]". auto.
    iMod (pcs_decr _ _ 1 _ with "PCS") as "[PCS PCS']". auto.
    iMod (pcs_drop _ _ 1 _ 1 4 with "PCS1") as "PCS1". lia.
    iMod (pcs_decr _ _ 1 _ with "PCS1") as "[PCS1 PCS2]". auto.
    iApply (wpsim_yieldR with "[DUTY PCS1]"). { instantiate (1:= i). auto. }
    { iSplitL "DUTY"; iFrame. }
    iIntros "DUTY CRED".

    (* OPEN *)
    iInv "TINV" as "TI" "TI_CLOSE".
    iEval (unfold tklockInv; simpl; red_tl_all) in "TI".
    iDestruct "TI" as (o) "TI"; iEval (red_tl_all; simpl) in "TI".
    iDestruct "TI" as (n) "TI"; iEval (red_tl_all; simpl) in "TI".
    iDestruct "TI" as (u) "TI"; iEval (red_tl_all; simpl) in "TI".
    (* iDestruct "TI" as (γo) "TI"; iEval (red_tl_all; simpl) in "TI". *)
    iDestruct "TI" as (D) "TI"; iEval (red_tl_all; simpl) in "TI".

    destruct (Nat.eq_dec o n).
    (* SUCCESS *)
    { subst. iClear "CRED".
      iDestruct "TI" as "(LOPT & LNPT & TB & SHOTS_BASE & %HD & HCOND & HWAIT)". rred2r.
      (* FAA *)
      iApply (SCMem_faa_fun_spec with "[LNPT MEM]"). auto.
      { pose proof mask_disjoint_ticketlock_state_tgt. set_solver. }
      { iSplitR "LNPT"; done. }
      iIntros (rv) "(%EQ & LNPT)". subst. iEval (ss) in "LNPT". rred2r. iApply wpsim_tauR.
      (* ALLOCATE TICKETS AND OBLIGATIONS TO PUT IN *)
      rred2r. iMod (alloc_obligation l 5) as "(%o_obl & #OBL & PC)".
      iMod (Ticket_alloc r n D n tid o_obl with "TB") as "(TB & ISSUED1 & _)".
      { intros H; apply HD in H; lia. }
      iDestruct "HCOND" as "[TKL | [%tid' TCONT]]"; cycle 1.
      { iEval (red_tl_all; simpl) in "TCONT". iDestruct "TCONT" as "[%obl' TCONT]".
        iEval (red_tl_all; simpl) in "TCONT". iDestruct "TCONT" as "(ISSUED2 & _)".
        iExFalso. iApply (Ticket_issued_twice with "[ISSUED1 ISSUED2]"). iFrame.
      }
      iDestruct "TKL" as "(TKL & P & [_ | [%NEQ _]])"; cycle 1. lia.
      iPoseProof (pc_split _ _ 1 _ with "[PC]") as "[PC1 PC2]". simpl. done.
      iAssert (#=> ◇[o_obl](1, 4))%I with "[PC2]" as "> PC".
      { destruct (Nat.eq_dec l 1); subst; auto. destruct (gt_dec l 1); try lia.
        iMod (pc_drop _ 1 with "PC2") as "PC". all: auto.
      }
      iPoseProof (pc_split _ _ 1 _ with "[PC]") as "[PC2 PC3]". simpl. done.
      iMod (Shots_alloc with "SHOTS_BASE") as "[SHOTS_BASE PENDING]".
      iPoseProof (duty_add with "[DUTY PC2] []") as "DUTY".
      { iSplitL "DUTY"; done. }
      { instantiate (1:=(s_shots_shot sr n : sProp i)%S). iModIntro. simpl.
        red_tl_all. simpl. iIntros. iModIntro. done. }
      iMod "DUTY".
      iPoseProof (duty_tpromise with "DUTY") as "#ULKPRM".
      { simpl. left; auto. }
      (* CLOSE *)
      iMod ("TI_CLOSE" with "[LOPT LNPT TB SHOTS_BASE ISSUED1 HWAIT PENDING]") as "_".
      { iEval (unfold tklockInv; simpl; red_tl_all). iExists n.
        iEval (red_tl; simpl). iExists (n+1).
        iEval (red_tl; simpl). iExists o_obl.
        (* iEval (red_tl; simpl). iExists γn. *)
        iEval (red_tl; simpl). iExists (D ∪ {[n]}).
        iEval (red_tl_all; simpl). iFrame.
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
        { iRight. iExists tid. red_tl. iExists o_obl. red_tl_all. iFrame. iSplit; done. }
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
      iEval (rewrite unfold_iter_eq; rred2r).
      (* YIELD *)
      iPoseProof (pc_split _ _ 1 _ with "PC3") as "[PC2 PC3]".
      iMod (pcs_decr _ _ 1 _ with "PCS2") as "[PCS1 PCS2]". auto.
      iApply (wpsim_yieldR with "[DUTY PCS1 PC2]").
      { instantiate (1:= i). auto. }
      { iSplitL "DUTY". done.
        iApply (pcs_cons_fold with "[PCS1 PC2]").
        { iEval (rewrite Nat.add_comm). simpl. iSplitL "PC2"; done. }
      }
      iIntros "DUTY _". rred2r.
      (* LOAD - OPEN INVARIANT *)
      iInv "TINV" as "TI" "TI_CLOSE".
      iEval (unfold tklockInv; simpl; red_tl_all) in "TI".
      iDestruct "TI" as (o') "TI"; iEval (red_tl_all; simpl) in "TI".
      iDestruct "TI" as (n') "TI"; iEval (red_tl_all; simpl) in "TI".
      iDestruct "TI" as (obl_o') "TI"; iEval (red_tl_all; simpl) in "TI".
      (* iDestruct "TI" as (γo') "TI"; iEval (red_tl_all; simpl) in "TI". *)
      iDestruct "TI" as (D') "TI"; iEval (red_tl_all; simpl) in "TI".
      iDestruct "TI"
        as "(LOPT & LNPT & TB & SHOTS_BASE & %HD' & [(TKL' & P' & _) | TISSUED] & HWAIT)".
      { iExFalso; iApply (Ticket_locked_twice with "[TKL TKL']"). iSplitL "TKL"; done. }
      (* iEval (red_tl; simpl) in "TISSUED". iDestruct "TISSUED" as "(%obl_o'' & TISSUED)". *)
      (* iEval (red_tl_all; simpl) in "TISSUED". *)
      (* iDestruct "TISSUED" as "(ISSUED & PENDING & OBL' & PRM')". *)
      iPoseProof (Ticket_black_locked with "[TKL TB]") as "%EQ".
      iSplitL "TKL"; done. symmetry in EQ; subst.
      (* LOAD *)
      iApply (SCMem_load_fun_spec with "[LOPT]"). auto.
      { pose proof mask_disjoint_ticketlock_state_tgt. set_solver. }
      { iSplitR "LOPT"; done. }
      iIntros (rv) "[%EQ LOPT]"; subst. rred2r. iApply (wpsim_tauR). rred2r.
      (* CLOSE *)
      iMod ("TI_CLOSE" with "[LOPT LNPT TB SHOTS_BASE TISSUED HWAIT]") as "_".
      { iEval (unfold tklockInv; simpl; red_tl_all). iExists n.
        iEval (red_tl_all; simpl). iExists n'.
        iEval (red_tl_all; simpl). iExists obl_o'.
        (* iEval (red_tl_all; simpl). iExists γo'. *)
        iEval (red_tl_all; simpl). iExists D'.
        iEval (red_tl_all; simpl).
        iSplitL "LOPT"; auto. iSplitL "LNPT"; auto.
        iSplitL "TB"; auto. iSplitL "SHOTS_BASE"; try done. iSplit. auto.
        iSplitL "TISSUED". iRight. done. done.
        (* { iRight. do 2 (iExists _; red_tl_all). iFrame. done. } *)
        (* { done. } *)
      }
      clear n' HD' D'.
      (* YIELD *)
      iMod (pcs_decr _ _ 1 _ with "PCS2") as "[PCS1 PCS2]". auto.
      iPoseProof (pc_split _ _ 1 _ with "PC3") as "[PC2 PC3]".
      iApply (wpsim_yieldR with "[DUTY PCS1 PC3]").
      { instantiate (1:=i); auto. }
      { iSplitL "DUTY". done.
        iApply (pcs_cons_fold with "[PCS1 PC3]").
        { iEval (rewrite Nat.add_comm). iSplitL "PC3"; done. }
      }
      iIntros "DUTY _".  rred2r.
      (* COMPARE *)
      iApply (SCMem_compare_fun_spec with "[MEM]"). auto.
      { pose proof mask_disjoint_ticketlock_state_tgt. set_solver. }
      { simpl. des_ifs. iApply (tgt_interp_as_equiv with "MEM"). iIntros. iSplit.
        { iIntros. simpl. red_tl; simpl. iSplit; [done | iPureIntro; auto]. }
        { simpl. red_tl; simpl. iIntros "[? _]". done. }
      }
      iIntros (rv) "[%EQ _]". exploit EQ. auto. i; subst. rred2r. iApply wpsim_tauR. rred2r.
      (* SYNC *)
      iApply (wpsim_yieldR with "[DUTY PCS2 PC2]").
      { instantiate (1:=i); auto. }
      { iSplitL "DUTY". done.
        iApply (pcs_cons_fold with "[PCS2 PC2]").
        { iEval (rewrite Nat.add_comm). iSplitL "PC2"; done. }
      }
      iIntros "DUTY _". rred2r. iApply wpsim_tauR. rred2r.
      (* POST *)
      iEval (red_tl) in "POST".
      iApply ("POST" with "[-]").
      { iExists n. red_tl. iExists o_obl. simpl. red_tl_all; simpl. iFrame. iExists _; done. }
    }

    (* FAILURE *)
    iDestruct "TI" as "(LOPT & LNPT & TB & SHOTS_BASE & %HD' & HCOND & HWAIT)". rred2r.
    iApply (SCMem_faa_fun_spec with "[MEM LNPT]"). auto.
    { pose proof mask_disjoint_ticketlock_state_tgt. set_solver. }
    { iSplitR "LNPT"; done. }
    iIntros (rv) "[%EQ LNPT]". subst. iEval (simpl) in "LNPT".
    rred2r. iApply wpsim_tauR. rred2r.
    (* ISSUE A TICKET *)
    iMod (alloc_obligation (1+l) (2 + (n - o))) as "(%obl_w & #WOBL & PC)".
    iPoseProof (pc_split _ _ 1 _ with "[PC]") as "[PC1 PC]". done. simpl.
    iPoseProof (pc_split _ _ 1 _ with "[PC]") as "[PC2 PC]". done.
    iMod (Ticket_alloc r _ _ n tid obl_w with "TB") as "(TB & ISSUED & WAIT)".
    { intros H; apply HD' in H; lia. }
    (* ALLOCATE OBLIGATION - SOMEBODY GIVE ME THE LOCK *)
    iMod (Shots_alloc with "SHOTS_BASE") as "(SHOTS_BASE & PENDING)".
    (* iMod (Lifetime.alloc n) as "[%γn LIVE]". *)
    (* iPoseProof (Lifetime.pending_split _ (1/2) (1/2) with "[LIVE]") as "[LIVE1 LIVE2]". *)
    (* { rewrite Qp.half_half. done. } *)
    iMod (ccs_make with "[PCS]") as "[CCS _]".
    { iSplitR "PCS". done. instantiate (1:=2). simpl. done. }
    (* iMod (OblTicket_alloc _ _ tid obl_w γn with "SHOTS_BASE") as "(OBASE & SHOTS_BASE & OW)". *)
    iAssert (⌜o < n⌝ ∗ ◆[u, l] ∗ -[u](0)-◇ ((s_shots_shot sr o : sProp i))%S)%I with "[TB HCOND]" as
      "(%HGT & #OBL_O & #PRM_O)".
    { iDestruct "HCOND" as
        "[(TKL & P & [%EQ | (%NEQ & %obl_o & COND)]) | (%tid_o & HCOND)]".
      { clarify. }
      { iEval (red_tl; simpl) in "COND". iDestruct "COND" as (tid_o) "COND".
        iEval (red_tl; simpl) in "COND". iDestruct "COND" as (ds_o) "COND".
        iEval (red_tl_all; simpl) in "COND".
        iDestruct "COND" as "(DUTY & _ & _ & _ & _ & #OBL_O)".
        iPoseProof (duty_tpromise with "DUTY") as "#PRM_O". simpl; left; done. iSplit; iFrame. done.
        iSplit; iFrame; done.
      }
      { red_tl. iDestruct "HCOND" as "[%obl_o HCOND]". red_tl_all; simpl. iDestruct "HCOND" as "(H & ? & ?)".
        iFrame. iPoseProof (Ticket_black_issued with "[H TB]") as "%H". iFrame.
        enough (o ∈ D). apply HD' in H0. auto. set_solver.
      }
    }
    iMod (link_new u obl_w l 0 0 with "[PC2]") as "[#LINK1 _]".
    { iFrame. done. }
    (* YIELD *)
    iEval (rewrite unfold_iter_eq; simpl). rred2r.
    iMod (pcs_decr _ _ 1 _ with "PCS2") as "[PCS1 PCS2]". auto.
    iApply (wpsim_yieldR_gen with "[DUTY PCS1]").
    { instantiate (1:=i); auto. }
    { iSplitL "DUTY"; done. }
    iIntros "DUTY CRED2".
    (* iAssert (⌜o < n⌝)%I with "[HCOND TB]" as "%HON". *)
    (* { iDestruct "HCOND" as *)
        (* "[(TKL & P & [%EQ | (%NEQ & %obl_o & COND)]) | (OISSUED & LIVEO & #OBLO & #PRMO)]". *)
      (* { clarify. } *)
      (* { iEval (red_tl; simpl) in "COND". iDestruct "COND" as (tid_o) "COND". *)
        (* iEval (red_tl; simpl) in "COND". iDestruct "COND" as (ds_o) "COND". *)
        (* iEval (red_tl_all; simpl) in "COND". auto. *)
      (* } *)
      (* { iPoseProof (Ticket_black_issued with "[TB OISSUED]") as "%HIN". iSplitL "TB"; done. *)
        (* iPureIntro. apply elem_of_union in HIN. des; auto. *)
        (* apply HD' in HIN. auto. apply elem_of_singleton in HIN; clarify. } *)
    (* } *)
    (* CLOSING THE INVARIANT *)
    iMod ("TI_CLOSE" with "[LOPT LNPT HCOND HWAIT WAIT TB PC PC1 SHOTS_BASE DUTY WDUTY CRED2 PENDING]") as "_".
    { iEval (unfold tklockInv; simpl; red_tl). iExists o.
      iEval (red_tl; simpl). iExists (n + 1).
      iEval (red_tl; simpl). iExists u.
      (* iEval (red_tl; simpl). iExists γo. *)
      iEval (red_tl; simpl). iExists (D ∪ {[n]}).
      iEval (red_tl_all; simpl). iFrame.
      (* iSplitL "". iPureIntro; lia. *)
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
          iExists tid. red_tl; simpl. iExists obl_w. red_tl; simpl.
          iExists ds. red_tl_all; simpl. iFrame. done.
        }
        done. set_unfold. ii. subst. apply HD' in H; lia.
      }
    }
    clear HD'. iClear "PRM_O OBL_O LINK1".
    iModIntro. rred2r.
    (* Induction on CCS *)
    iRevert "PCS' BDUTY POST ISSUED".
    iMod (ccs_ind2 with "CCS [-]") as "IND".
    2:{ iIntros "PCS". iMod (pcs_drop _ _ _ _ 2 1 with "PCS"). lia. iApply "IND". done. }
    iModIntro. iExists 0. iIntros "IH". iModIntro. iIntros "PCS SDUTY_B POST ISSUED".
    (* Opening invariant *)
    iInv "TINV" as "TI" "TI_CLOSE".
    iEval (unfold tklockInv; simpl; red_tl) in "TI".
    iDestruct "TI" as (o') "TI"; iEval (red_tl; simpl) in "TI".
    iDestruct "TI" as (n') "TI"; iEval (red_tl; simpl) in "TI".
    iDestruct "TI" as (obl_o') "TI"; iEval (red_tl; simpl) in "TI".
    (* iDestruct "TI" as (γo') "TI"; iEval (red_tl; simpl) in "TI". *)
    iDestruct "TI" as (D') "TI"; iEval (red_tl_all; simpl) in "TI".
    iDestruct "TI" as "(LOPT & LNPT & TB & SHOTS_BASE & %HD' & TO & HWAIT)".
    (* Load *)
    iApply (SCMem_load_fun_spec with "[LOPT]"). auto.
    { pose proof mask_disjoint_ticketlock_state_tgt; set_solver. }
    { iSplit; iFrame. done. }
    iIntros (rv) "[%EQ LOPT]". subst. rred2r. iApply wpsim_tauR. rred2r.
    (* Yield *)
    destruct (Nat.eq_dec o' n).
    { (* Case 1 : My turn has arrived *)
      subst. iDestruct "TO" as "[ (LOCKED_N & P & [ %HNN' | H ]) | (%tid' & WAIT) ]".
      { subst. iPoseProof (Ticket_black_issued with "[TB ISSUED]") as "%HIN". iFrame.
        apply HD' in HIN. lia.
      }
      2:{ iEval (red_tl_all; simpl) in "WAIT". iDestruct "WAIT" as (obl') "WAIT".
          iEval (red_tl_all; simpl) in "WAIT".
          iExFalso; iApply (Ticket_issued_twice with "[ISSUED WAIT]"). iDestruct "WAIT" as "[WAIT _]".
          iFrame.
      }
      iDestruct "H" as "(%HNN' & %tid' & H)". iEval (red_tl; simpl) in "H".
      iDestruct "H" as "[%obl_w' H]". iEval (red_tl; simpl) in "H".
      iDestruct "H" as "[%ds' H]". iEval (red_tl_all; simpl) in "H".
      iDestruct "H" as "(DUTY & SDUTY_W & PC & WAIT & PENDING & #OBL_O')".
      iPoseProof (Ticket_issued_wait with "[ISSUED WAIT]") as "%EQ". iFrame. des; clarify.
      (* iPoseProof (Lifetime.pending_merge with "LIVE LIVE2") as "LIVE". iEval (rewrite Qp.half_half) in "LIVE". *)
      iPoseProof (Shareduty_black_white with "[SDUTY_B SDUTY_W]") as "%EQ". iFrame. subst.
      iPoseProof (pc_split _ _ 1 with "PC") as "[PC' PC]".
      iMod (pcs_drop _ _ _ _ 1 3 with "PCS") as "PCS". lia.
      iMod (pcs_decr _ _ 1 with "PCS") as "[PCS' PCS]". auto.
      iAssert (#=> ◇[obl_o'](1, 1))%I with "[PC']" as "PC'".
      { destruct (Nat.eq_dec l 1). subst; auto. destruct (gt_dec l 1); try lia.
        iMod (pc_drop _ 1 with "PC'"); auto.
      }
      iMod "PC'".
      iApply (wpsim_yieldR_gen with "[PCS' PC' DUTY]"). instantiate (1:=i). auto.
      { iSplitL "DUTY". done. iApply (pcs_cons_fold); simpl. iSplitL "PC'". iFrame. done. }
      iIntros "DUTY _".
      iPoseProof (duty_tpromise with "DUTY") as "#PRM_O'". simpl; left; auto.
      iMod ("TI_CLOSE" with "[ISSUED TB SHOTS_BASE LNPT LOPT PENDING HWAIT]") as "_".
      { iEval (unfold tklockInv; simpl; red_tl). iExists n.
        iEval (red_tl; simpl). iExists n'. iEval (red_tl; simpl). iExists obl_o'.
        iEval (red_tl; simpl). iExists D'. red_tl_all. iFrame.
        iSplitR. auto. iRight. iExists tid'. red_tl. iExists obl_w'. red_tl_all. simpl. iFrame.
        iSplit; done.
      }
      iModIntro. rred2r.
      iApply (SCMem_compare_fun_spec); auto.
      { simpl. des_ifs. iApply (tgt_interp_as_equiv with "MEM"). iIntros. iSplit.
        { iIntros. simpl. red_tl; simpl. iSplit; [done | iPureIntro; auto]. }
        { simpl. red_tl; simpl. iIntros "[? _]". done. }
      }
      iIntros (rv) "[%EQ _]". exploit EQ. auto. i; subst. rred2r. iApply wpsim_tauR. rred2r.
      iPoseProof (pc_split _ _ 1 with "PC") as "[PC' PC]".
      iAssert (#=> ◇[obl_o'](1, 1))%I with "[PC']" as "PC'".
      { destruct (Nat.eq_dec l 1). subst; auto. destruct (gt_dec l 1); try lia.
        iMod (pc_drop _ 1 with "PC'"); auto.
      }
      iMod "PC'". iMod (pcs_decr _ _ 1 with "PCS") as "[PCS' PCS]". auto.
      iApply (wpsim_yieldR with "[PCS' PC' DUTY]"). instantiate (1:=i). auto.
      { iSplitL "DUTY". done. iApply (pcs_cons_fold); simpl. iSplitL "PC'". iFrame. done. }
      iIntros "DUTY _". rred2r. iApply (wpsim_tauR). rred2r.
      iEval (red_tl) in "POST".
      iApply ("POST" with "[-]").
      { iExists n. red_tl. iExists obl_o'. red_tl_all; simpl. iExists _. iFrame.
        iPoseProof (pc_split _ _ 1 with "PC") as "[? ?]"; iFrame.
      }
    }
    (* Case 2 : Not my turn yet *)
    (* Get my duty out of invariant *)
    iEval (rewrite red_tl_big_sepS) in "HWAIT".
    iPoseProof (Ticket_black_issued with "[TB ISSUED]") as "%HNN'".
    { iFrame. }
    (* iAssert (⌜n ∈ D'⌝)%I as "%HD".
    { iPureIntro. apply HD'. auto. } *)
    assert (D' = ((D' ∖ {[n]}) ∪ {[n]})).
    { set_unfold. split; ii. destruct (Nat.eq_dec x n); auto. des; clarify; auto. }
    iEval (setoid_rewrite H) in "HWAIT".
    iEval (rewrite <- red_tl_big_sepS) in "HWAIT".
    iEval (rewrite red_tl_big_sepS; red_tl; simpl) in "HWAIT".
    rewrite big_opS_union; cycle 1. set_solver.
    iDestruct "HWAIT" as "[H1 H2]".
    rewrite big_sepS_singleton. iEval (red_tl_all; simpl) in "H2".
    iDestruct "H2" as "[ (_ & %tid' & ISSUED2) | H2 ]".
    { iEval (red_tl_all; simpl) in "ISSUED2". iDestruct "ISSUED2" as "[%obl' ISSUED2]".
      iExFalso; iApply (Ticket_issued_twice with "[ISSUED ISSUED2]"). red_tl_all; simpl. iFrame.
    }
    iDestruct "H2" as "[%HNO | (%HNO & %tid_o & H2) ]".
    { lia. }
    iEval (red_tl; simpl) in "H2". iDestruct "H2" as (obl_w') "H2".
    (* iEval (red_tl; simpl) in "H2". iDestruct "H2" as (γn') "H2". *)
    iEval (red_tl; simpl) in "H2". iDestruct "H2" as (ds') "H2".
    iEval (red_tl_all; simpl) in "H2".
    iDestruct "H2" as "(DUTY & SDUTY_W & WAIT & PENDING & PC & #LINK)".
    iPoseProof (Ticket_issued_wait with "[ISSUED WAIT]") as "%EQ". iFrame. des; clarify.
    (* iPoseProof (OblTicket_black_white or n with "[OTKB OTK_W]") as "%EQ"; auto. iFrame. des; clarify. *)
    iPoseProof (Shareduty_black_white with "[SDUTY_B SDUTY_W]") as "%EQ". iFrame. subst.
    iMod (pcs_drop _ _ _ _ 1 4 with "PCS") as "PCS". lia.
    iMod (pcs_decr _ _ 1 with "PCS") as "[PCS' PCS]". auto.
    iAssert (◆[obl_o', l] ∗ -[obl_o'](0)-◇ (s_shots_shot sr o')%S)%I with "[TO]" as "[#OBL_O' #PRM_O']".
    { iDestruct "TO" as "[(TKL & P & [%EQ | (%NEQ & %obl_o & COND)]) | (%tid' & ISSUED)]".
      { clarify. apply HD' in HNN'. lia. }
      { iEval (red_tl; simpl) in "COND". iDestruct "COND" as (tid_o') "COND".
        iEval (red_tl; simpl) in "COND". iDestruct "COND" as (ds_o') "COND".
        iEval (red_tl_all; simpl) in "COND".
        iDestruct "COND" as "(DUTY & _ & _ & _ & _ & #OBL_O')".
        iPoseProof (duty_tpromise with "DUTY") as "#PRM_O'". simpl; left; done. iSplit; iFrame. done. done.
        }
      { red_tl_all. iDestruct "ISSUED" as "[%obl' ISSUED]". red_tl_all; simpl.
        iDestruct "ISSUED" as "(ISSUED & PENDING & OBL' & LINK')". iSplit; done.
      }
    }
    (* Yield *)
    iApply (wpsim_yieldR_gen with "[PCS' DUTY]"). instantiate (1:=i). auto.
    { iSplitL "DUTY"; done. }
    iIntros "DUTY CRED". iCombine "PRM_O'" "CRED" as "C".
    iMod (tpromise_progress with "C") as "PC_O".
    iDestruct "PC_O" as "[PC_O | #DEAD]"; cycle 1.
    { iEval (simpl; red_tl_all) in "DEAD".
      iDestruct "TO" as "[(TKL & P & [%EQ | (%NEQ & %obl_o & COND)]) | (%tid' & ISSUED')]".
      { clarify. apply HD' in HNN'. lia. }
      { iEval (red_tl; simpl) in "COND". iDestruct "COND" as (tid_o') "COND".
        iEval (red_tl; simpl) in "COND". iDestruct "COND" as (ds_o') "COND".
        iEval (red_tl_all; simpl) in "COND".
        iDestruct "COND" as "(_ & _ & _ & _ & PENDING_O & _)".
        iExFalso. iApply (Shots_pending_not_shot with "[PENDING_O DEAD]"). iFrame. done.
      }
      { iEval (red_tl_all; simpl) in "ISSUED'". iDestruct "ISSUED'" as (obl') "ISSUED'".
        iEval (red_tl_all; simpl) in "ISSUED'". iDestruct "ISSUED'" as "(_ & PENDING' & _)".
        iExFalso; iApply (Shots_pending_not_shot with "[PENDING' DEAD]"). iFrame. done.
      }
    }
    iMod (link_amplify with "[PC_O LINK]") as "PC_W". iFrame. done.
    (* Close the invariant *)
    iMod ("TI_CLOSE" with "[LNPT TB SHOTS_BASE TO H1 SDUTY_W PC PENDING LOPT DUTY WAIT]") as "_".
    { iEval (unfold tklockInv; simpl; red_tl). iExists o'.
      iEval (red_tl; simpl). iExists n'. iEval (red_tl; simpl). iExists obl_o'.
      iEval (red_tl; simpl). iExists D'. red_tl_all; simpl. iFrame.
      iSplitR. auto. iEval (rewrite H; rewrite red_tl_big_sepS).
      rewrite big_opS_union; cycle 1. set_solver. iFrame.
      rewrite big_sepS_singleton. red_tl. iRight. iRight. iSplit. auto.
      iExists tid_o. red_tl; simpl. iExists obl_w'. red_tl; simpl.
      iExists ds'. red_tl_all; simpl. iFrame. done.
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
    iDestruct "TI" as (obl_o'') "TI"; iEval (red_tl; simpl) in "TI".
    (* iDestruct "TI" as (γo'') "TI"; iEval (red_tl; simpl) in "TI". *)
    iDestruct "TI" as (D'') "TI"; iEval (red_tl_all; simpl) in "TI". clear HD' HNN'.
    iDestruct "TI" as "(LOPT & LNPT & TB & SHOTS_BASE & %HD' & TO & HWAIT)".
    
    destruct (Nat.eq_dec o'' n).
    { (* My turn has arrived *)
      subst. iDestruct "TO" as "[ (LOCKED_N & P & [ %HNN' | H ]) | [%tid' HISSUED]]".
      { subst. iPoseProof (Ticket_black_issued with "[TB ISSUED]") as "%HIN". iFrame.
        apply HD' in HIN. lia.
      }
      2:{ iEval (red_tl_all; simpl) in "HISSUED". iDestruct "HISSUED" as (obl') "HISSUED".
          iEval (red_tl_all; simpl) in "HISSUED".
          iDestruct "HISSUED" as "(ISSUED' & PENDING & OBL'' & PRM'')".
          iExFalso; iApply (Ticket_issued_twice with "[ISSUED ISSUED']"). iFrame.
      }
      iDestruct "H" as "(%HNN' & %tid' & H)". iEval (red_tl; simpl) in "H".
      iDestruct "H" as "[%obl_w'' H]". iEval (red_tl; simpl) in "H".
      iDestruct "H" as "[%ds'' H]". iEval (red_tl_all; simpl) in "H".
      iDestruct "H" as "(DUTY & SDUTY_W & PC & WAIT & PENDING & #OBL_O'')".
      iPoseProof (Ticket_issued_wait with "[WAIT ISSUED]") as "%EQ"; auto. iFrame. des; clarify.
      (* iPoseProof (Lifetime.pending_merge with "LIVE LIVE2") as "LIVE". iEval (rewrite Qp.half_half) in "LIVE". *)
      iPoseProof (Shareduty_black_white with "[SDUTY_B SDUTY_W]") as "%EQ'". iFrame. subst.
      iPoseProof (pc_split _ _ 1 with "PC") as "[PC' PC]".
      iMod (pcs_decr _ _ 1 with "PCS") as "[PCS' PCS]". auto.
      iAssert (#=> ◇[obl_o''](1, 1))%I with "[PC']" as "PC'".
      { destruct (Nat.eq_dec l 1). subst; auto. destruct (gt_dec l 1); try lia.
        iMod (pc_drop _ 1 with "PC'"); auto.
      }
      iMod "PC'".
      iApply (wpsim_yieldR_gen with "[PCS' PC' DUTY]"). instantiate (1:=i). auto.
      { iSplitL "DUTY". done. iApply (pcs_cons_fold); simpl. iSplitL "PC'". iFrame. done. }
      iIntros "DUTY CRED2".
      iPoseProof (duty_tpromise with "DUTY") as "#PRM_O''". simpl; left; auto.
      iMod ("TI_CLOSE" with "[LNPT TB SHOTS_BASE HWAIT PENDING LOPT ISSUED]") as "_".
      { iEval (unfold tklockInv; simpl; red_tl). iExists n.
        iEval (red_tl; simpl). iExists n''. iEval (red_tl; simpl). iExists obl_o''.
        iEval (red_tl; simpl). iExists D''. red_tl_all; simpl. iFrame.
        iSplitR. auto. iRight. iExists tid'. red_tl. iExists obl_w''. red_tl_all. iFrame. iSplit; done.
      }
      iModIntro. rred2r.
      iInv "TINV" as "TI" "TI_CLOSE".
      iEval (unfold tklockInv; simpl; red_tl) in "TI".
      iDestruct "TI" as (o''') "TI"; iEval (red_tl; simpl) in "TI".
      iDestruct "TI" as (n''') "TI"; iEval (red_tl; simpl) in "TI".
      iDestruct "TI" as (obl_o''') "TI"; iEval (red_tl; simpl) in "TI".
      (* iDestruct "TI" as (γo''') "TI"; iEval (red_tl; simpl) in "TI". *)
      iDestruct "TI" as (D''') "TI"; iEval (red_tl_all; simpl) in "TI". clear HD' HNN'.
      (* iDestruct "TI" as "(LOPT & LNPT & TB & SHOTS_BASE & %HD' & TO & HWAIT)". *)
      iDestruct "TI" as "(LOPT & LNPT & TB & TI)".
      (* { iExFalso; iApply (Ticket_locked_twice with "[LOCKED_N TKL']"). iSplitL "TKL'"; done. } *)
      iPoseProof (Ticket_black_locked with "[LOCKED_N TB]") as "%EQ".
      iSplitL "LOCKED_N"; done. symmetry in EQ; subst.
      (* LOAD *)
      iApply (SCMem_load_fun_spec with "[LOPT]"). auto.
      { pose proof mask_disjoint_ticketlock_state_tgt. set_solver. }
      { iSplitR "LOPT"; done. }
      iIntros (rv) "[%EQ LOPT]"; subst. rred2r. iApply (wpsim_tauR). rred2r.
      iPoseProof (pc_split _ _ 1 with "PC") as "[PC' PC]".
      iAssert (#=> ◇[obl_o''](1, 1))%I with "[PC']" as "PC'".
      { destruct (Nat.eq_dec l 1). subst; auto. destruct (gt_dec l 1); try lia.
        iMod (pc_drop _ 1 with "PC'"); auto.
      }
      iMod "PC'". iMod (pcs_decr _ _ 1 with "PCS") as "[PCS' PCS]". auto.
      iApply (wpsim_yieldR_gen with "[PCS' PC' DUTY]"). instantiate (1:=i). auto.
      { iSplitL "DUTY". done. iApply (pcs_cons_fold); simpl. iSplitL "PC'". iFrame. done. }
      iIntros "DUTY _".
      iMod ("TI_CLOSE" with "[TB TI LNPT LOPT]") as "_".
      { iEval (unfold tklockInv; simpl; red_tl). iExists n.
        iEval (red_tl; simpl). iExists n'''. iEval (red_tl; simpl). iExists obl_o'''.
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
      iAssert (#=> ◇[obl_o''](1, 1))%I with "[PC']" as "PC'".
      { destruct (Nat.eq_dec l 1). subst; auto. destruct (gt_dec l 1); try lia.
        iMod (pc_drop _ 1 with "PC'"); auto.
      }
      iMod "PC'".
      iApply (wpsim_yieldR with "[PCS PC' DUTY]"). instantiate (1:=i). auto.
      { iSplitL "DUTY". done. iApply (pcs_cons_fold); simpl. iSplitL "PC'". iFrame. done. }
      iIntros "DUTY _". rred2r. iApply (wpsim_tauR). rred2r.
      iEval (red_tl) in "POST".
      iApply ("POST" with "[-]").
      { iExists n. red_tl. iExists obl_o''. red_tl_all; simpl. iExists _. iFrame. }
    }

    iPoseProof (Ticket_black_issued with "[ISSUED TB]") as "%HNN'".
    { iFrame. }
    (* iPoseProof (OblTicket_issued with "[SHOTS_BASE OTKB]") as "%HNN'". *)
    (* { iFrame. } *)
    (* iAssert (⌜n ∈ D''⌝)%I as "%HD". *)
    (* { iPureIntro. apply HD'. auto. } *)
    assert (D'' = ((D'' ∖ {[n]}) ∪ {[n]})).
    { set_unfold. split; ii. destruct (Nat.eq_dec x n); auto. des; clarify; auto. }
    iEval (setoid_rewrite H0; red_tl_all; simpl) in "HWAIT".
    (* iEval (rewrite red_tl_big_sepS) in "HWAIT". *)
    iEval (rewrite red_tl_big_sepS; red_tl; simpl) in "HWAIT".
    rewrite big_opS_union; cycle 1. set_solver.
    iDestruct "HWAIT" as "[H1 H2]".
    rewrite big_sepS_singleton. iEval (red_tl_all; simpl) in "H2".
    iDestruct "H2" as "[ (_ & TISSUED2) | H2 ]".
    { iDestruct "TISSUED2" as (tid') "T". iEval (red_tl_all) in "T".
      iDestruct "T" as (obl') "ISSUED2".
      iExFalso; iApply (Ticket_issued_twice with "[ISSUED ISSUED2]"). red_tl_all. iFrame.
    }
    iDestruct "H2" as "[%HNO' | (%HNO' & %tid_o' & H2) ]".
    { lia. }
    iEval (red_tl; simpl) in "H2". iDestruct "H2" as (obl_w'') "H2".
    (* iEval (red_tl; simpl) in "H2". iDestruct "H2" as (γn'') "H2". *)
    iEval (red_tl; simpl) in "H2". iDestruct "H2" as (ds'') "H2".
    iEval (red_tl_all; simpl) in "H2".
    iDestruct "H2" as "(DUTY & SDUTY_W & WAIT & PENDING & PC & #LINK')".
    iPoseProof (Ticket_issued_wait with "[ISSUED WAIT]") as "%EQ". iFrame. des; clarify.
    (* iPoseProof (OblTicket_black_white or n with "[OTKB OTK_W]") as "%EQ"; auto. iFrame. des; clarify. *)
    iPoseProof (Shareduty_black_white with "[SDUTY_B SDUTY_W]") as "%EQ". iFrame. subst.
    iMod (pcs_decr _ _ 1 with "PCS") as "[PCS' PCS]". auto.
    iApply (wpsim_yieldR_gen with "[PCS' DUTY]"). instantiate (1:=i). auto.
    { iSplitL "DUTY"; done. }
    iIntros "DUTY CRED".
    iMod ("TI_CLOSE" with "[LNPT TB SHOTS_BASE TO H1 SDUTY_W PC PENDING LOPT DUTY WAIT]") as "_".
    { iEval (unfold tklockInv; simpl; red_tl). iExists o''.
      iEval (red_tl; simpl). iExists n''. iEval (red_tl; simpl). iExists obl_o''.
      iEval (red_tl; simpl). iExists D''. red_tl_all; simpl. iFrame.
      iSplitR. auto. iEval (rewrite H0; rewrite red_tl_big_sepS).
      rewrite big_opS_union; cycle 1. set_solver. iFrame.
      rewrite big_sepS_singleton. red_tl. iRight. iRight. iSplit. auto.
      iExists tid_o'. red_tl; simpl. iExists obl_w''. red_tl; simpl.
      iExists ds''. red_tl_all; simpl. iFrame. done.
    }
    iModIntro. rred2r.
    iMod ("IH" with "PC_W") as "IH". iApply ("IH" with "SDUTY_B POST ISSUED").
  Unshelve. all: auto.
  Qed. *)
  Admitted.

  Lemma TicketLock_unlock_spec
        tid i
        (E : coPset)
        (IN : ⊤ ⊆ E)
    :
    ⊢ ∀ r sr lo ln (P : sProp i) l (ds : list (nat * nat * sProp i)) u o,
        [@ tid, 1+i, E @]
          ⧼⟦((syn_tgt_interp_as (1+i) sndl (fun m => (s_memory_black m)))
               ∗ (⤉ isTicketLock i r sr (lo, ln) P l)
               ∗ (⤉⤉ P)
               ∗ (⤉⤉ s_ticket_locked r o)
               ∗ (⤉⤉ Duty(tid) ((u, 0, s_shots_shot sr (o : nat)) :: ds))
               ∗ ◇{((u, 0, emp) :: ds)@1}(1, 3))%S, 2+i⟧⧽
            (OMod.close_itree Client (SCMem.mod gvs) (TicketLock.unlock (lo, ln)))
            ⧼rv, ⟦((⤉ (⤉ Duty(tid) ds)))%S, 2+i⟧⧽
  .
  Proof.
    (* PREPROCESS *)
    iIntros. iStartTriple.
    iIntros "PRE POST". unfold TicketLock.unlock. rred2r.
    iApply wpsim_discard. apply IN.
    iEval (red_tl_all; simpl; rewrite red_syn_tgt_interp_as; simpl; red_tl_all; simpl) in "PRE".
    iDestruct "PRE" as "(#MEM & ISLOCK & P & LOCKED_O & DUTY & PCS)".
    iEval (unfold isTicketLock; red_tl_all; simpl) in "ISLOCK".
    iDestruct "ISLOCK" as (lo') "ISLOCK". iEval (red_tl_all; simpl) in "ISLOCK".
    iDestruct "ISLOCK" as (ln') "ISLOCK". iEval (red_tl_all; simpl) in "ISLOCK".
    iDestruct "ISLOCK" as (N) "ISLOCK". iEval (red_tl_all; simpl) in "ISLOCK".
    iDestruct "ISLOCK" as "(%NAME & %HLGT & %HEQ & TINV)". inv HEQ.
    iEval (rewrite red_syn_inv; simpl) in "TINV". iPoseProof "TINV" as "#TINV".
    (* YIELD *)
    iApply (wpsim_yieldR2 with "[DUTY PCS]").
    instantiate (1:=i); auto. instantiate (1:=3); auto. iFrame. done.
    iIntros "DUTY CRED PCS". rred2r.
    (* OPEN INVARIANT *)
    iInv "TINV" as "TI" "TI_CLOSE".
    iEval (unfold tklockInv; simpl; red_tl_all; simpl) in "TI".
    iDestruct "TI" as (o') "TI". iEval (red_tl; simpl) in "TI".
    iDestruct "TI" as (n) "TI". iEval (red_tl; simpl) in "TI".
    iDestruct "TI" as (obl_o) "TI". iEval (red_tl; simpl) in "TI".
    (* iDestruct "TI" as (γo') "TI". iEval (red_tl; simpl) in "TI". *)
    iDestruct "TI" as (D) "TI". iEval (red_tl_all; simpl) in "TI".
    iDestruct "TI" as "(LOPT & LNPT & TCK_B & SHOTS_BASE & %HD & [[LOCKED2 _] | [%tid' TI]] & HWAIT)".
    { iExFalso; iApply (Ticket_locked_twice with "[LOCKED_O LOCKED2]"). iFrame. }
    iPoseProof (Ticket_black_locked with "[TCK_B LOCKED_O]") as "%EQ". iFrame. symmetry in EQ; subst.
    (* LOAD *)
    iApply (SCMem_load_fun_spec with "[LOPT]"). instantiate (1:=1+i); auto.
    { pose proof mask_disjoint_ticketlock_state_tgt; set_solver. }
    { iFrame. done. }
    iIntros (rv) "[%EQ LOPT]". subst. rred2r. iApply wpsim_tauR. rred2r.
    (* CLOSE INVARIANT *)
    iMod ("TI_CLOSE" with "[LNPT TCK_B SHOTS_BASE TI HWAIT LOPT]") as "_".
    { iEval (unfold tklockInv; simpl; red_tl; simpl). iExists o.
      iEval (red_tl; simpl). iExists n. iEval (red_tl; simpl). iExists obl_o.
      iEval (red_tl; simpl). iExists D.
      iEval (red_tl_all; simpl). iFrame. iSplit; auto.
    }
    (* YIELD *)
    iApply (wpsim_yieldR2 with "[DUTY PCS]").
    instantiate (1:=i); auto. instantiate (1:=2); auto. iFrame.
    iIntros "DUTY CRED2 PCS". rred2r. iEval (simpl) in "PCS".
    (* OPEN INVARIANT *)
    clear HD n obl_o D.
    iInv "TINV" as "TI" "TI_CLOSE".
    iEval (unfold tklockInv; simpl; red_tl_all; simpl) in "TI".
    iDestruct "TI" as (o') "TI". iEval (red_tl; simpl) in "TI".
    iDestruct "TI" as (n) "TI". iEval (red_tl; simpl) in "TI".
    iDestruct "TI" as (obl_o) "TI". iEval (red_tl; simpl) in "TI".
    (* iDestruct "TI" as (γo') "TI". iEval (red_tl; simpl) in "TI". *)
    iDestruct "TI" as (D) "TI". iEval (red_tl_all; simpl) in "TI".
    iDestruct "TI" as "(LOPT & LNPT & TCK_B & OTCK_BASE & %HD & [[LOCKED2 _] | TI] & HWAIT)".
    { iExFalso; iApply (Ticket_locked_twice with "[LOCKED_O LOCKED2]"). iFrame. }
    (* iPoseProof (OblTicket_black_white or n with "[OTKB OTK_W]") as "%EQ"; auto. iFrame. des; clarify. *)
    iDestruct "TI" as (tid'') "TI". iEval (red_tl; simpl) in "TI".
    iDestruct "TI" as (obl'') "TI". iEval (red_tl_all; simpl) in "TI".
    iDestruct "TI" as "(TISSUED & PENDING & #OBL & #PRM)".
    iPoseProof (Ticket_black_locked with "[TCK_B LOCKED_O]") as "%EQ". iFrame. symmetry in EQ; subst.
    iMod (Shots_pending_shot with "PENDING") as "#DEAD".
    iMod (duty_fulfill (v:=i) with "[DUTY]") as "DUTY".
    { simpl. iSplitL "DUTY". done. red_tl_all. done. }
    (* STORE *)
    iApply (SCMem_store_fun_spec with "[LOPT]"). instantiate (1:=1+i); auto.
    { pose proof mask_disjoint_ticketlock_state_tgt; set_solver. }
    { iFrame. done. }
    iIntros (rv) "LOPT". rred2r. iApply wpsim_tauR. rred2r.
    (* ALLOCATE OBLIGATIONS *)
    iMod (Ticket_update r o (o + 1) with "[TCK_B LOCKED_O]") as "[TCK_B LOCKED_O]". iFrame.
    (* CLOSE INVARIANT *)
    destruct (Nat.eq_dec n (o + 1)).
    (* CASE 1 : NO ONE WAITING *)
    { subst.
      iMod ("TI_CLOSE" with "[P LNPT TCK_B OTCK_BASE LOCKED_O HWAIT LOPT TISSUED]") as "_".
      { iEval (unfold tklockInv; simpl; red_tl; simpl). iExists (o + 1).
        iEval (red_tl; simpl). iExists (o + 1). iEval (red_tl; simpl). iExists obl_o.
        iEval (red_tl; simpl). iExists D. iEval (red_tl_all; simpl).
        iFrame. iSplit; auto. iSplitL "LOCKED_O P".
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
        rewrite ! big_sepS_singleton. red_tl_all. iLeft. iSplitR "TISSUED". iPureIntro; lia.
        iExists tid''. red_tl. iExists obl''. red_tl_all. done.
      }
      iPoseProof (pcs_cons_unfold with "PCS") as "[PC PCS]". simpl.
      iApply (wpsim_yieldR2 with "[DUTY PCS]").
      instantiate (1:=i); auto. instantiate (1:=1); auto. iFrame.
      iIntros "DUTY CRED3 PCS". rred2r. iApply wpsim_tauR. rred2r.
      iApply ("POST" with "[DUTY]"). simpl. red_tl; simpl. done.
    }
    (* CASE 2 : SOMEONE WAITING *)
    iPoseProof (Ticket_black_issued with "[TCK_B TISSUED]") as "%HOIND". iFrame.
    apply HD in HOIND.
    assert (D = ((D ∖ {[o + 1]}) ∪ {[o + 1]})).
    { set_unfold. split; ii. destruct (Nat.eq_dec x (o + 1)); auto. des; clarify; auto. apply HD. lia. }
    iEval (setoid_rewrite H) in "HWAIT".
    iEval (rewrite red_tl_big_sepS; red_tl; simpl) in "HWAIT".
    rewrite big_opS_union; cycle 1. set_solver.
    iDestruct "HWAIT" as "[HWAIT HO1]".
    iEval (rewrite big_sepS_singleton; red_tl_all; simpl) in "HO1".
    iDestruct "HO1" as "[[%HO1 _]| [%HO1 | (_ & %tid''' & HO1)]]"; [ lia | lia | ].
    iEval (red_tl; simpl) in "HO1". iDestruct "HO1" as (obl''') "HO1".
    iEval (red_tl; simpl) in "HO1". iDestruct "HO1" as (ds''') "HO1".
    iEval (red_tl_all; simpl) in "HO1". iDestruct "HO1" as "(DUTY_O & SDUTY_W_O & WAIT_O & PENDING_O & PC_O & #PRM_O)".
    replace (o + 1 - o) with 1 by lia.
    (* ALLOC OBLIGATION FOR THE NEXT WINNER *)
    iMod (alloc_obligation l 5) as "(%obl_n & #OBL_n & PC_n)".
    iPoseProof (pc_split _ _ 1 _ with "[PC_n]") as "[PC_n1 PC_n]". simpl. done.
    iAssert (#=> ◇[obl_n](1, 1))%I with "[PC_n1]" as "PC_n1".
    { destruct (Nat.eq_dec l 1).
      { subst; iModIntro; iFrame. }
      assert (l > 1) by lia. iMod (pc_drop _ 1 l with "PC_n1") as "PC_n1". auto. auto. iModIntro; done.
    }
    iMod "PC_n1".
    iMod (duty_add (v:=i) with "[DUTY_O PC_n1] []") as "DUTY_O". iFrame.
    { instantiate (1:=(s_shots_shot sr (o+1))). simpl. iModIntro. red_tl_all. iIntros "#SHOT". iModIntro. done. }
    
    iAssert (([∗ set] y ∈ (D ∖ {[o + 1]} ∖ {[o]}),
              ⌜y < o + 1⌝ ∗ (∃ tid obl, Ticket_issued r y tid obl)
              ∨ ⌜y > o + 1⌝
                ∗ (∃ tid obl ds, Duty(tid) ds
                  ∗ ShareDuty_white inlp tid ds
                  ∗ Ticket_wait r y tid obl
                  ∗ Shots_pending sr y
                  ∗ ◇[obl](S l, y - (o + 1))))
              ∗ [∗ set] y ∈ (D ∖ {[o + 1]} ∖ {[o]}),
                ⌜y > o + 1⌝ -∗ ∃ obl, #=( ObligationRA.edges_sat )=> obl_n -(0)-◇ obl)%I
                with "[HWAIT]" as "[HWAIT HPCS]".
    { assert (D ∖ {[o + 1]} = D ∖ {[o + 1]} ∖ {[o]} ∪ {[o]}).
      { assert (o ∈ D ∖ {[o + 1]}). set_unfold. split. apply HD; lia. lia.
        set_unfold. split; ii.
        { destruct (Nat.eq_dec x o); [right | left]; auto. } des; clarify.
      }
      iEval (setoid_rewrite H0) in "HWAIT". rewrite ! big_opS_union; cycle 1. set_solver.
      iDestruct "HWAIT" as "[HWAIT _]".
      iApply (big_sepS_sep). iApply (big_sepS_impl with "[HWAIT]"); iFrame. iModIntro. iIntros (x) "%XIN H".
      red_tl. iDestruct "H" as "[[%HLT HI] | [%HEQ | [%HGT HWAIT]]]".
      { iSplitL. iLeft. iSplit; auto. iPureIntro; lia. iDestruct "HI" as (?) "HI". red_tl.
        iDestruct "HI" as (?) "HI". red_tl_all. iExists x0, x1. done. iIntros "%HC". lia.
      }
      { subst. set_unfold in XIN. des; lia. }
      iDestruct "HWAIT" as (tid_w) "HWAIT". red_tl. iDestruct "HWAIT" as (obl_w) "HWAIT". red_tl.
      iDestruct "HWAIT" as (ds_w) "HWAIT". red_tl_all; simpl.
      iDestruct "HWAIT" as "(DUTY_W & SDUTY_W_W & WAIT_W & PENDING_W & PC_W & LINK_W)".
      iPoseProof (pc_split _ _ 1 _ with "[PC_W]") as "[PC_W1 PC_W2]".
      { replace (x - o) with (1 + (x - (o + 1))) by lia. done. }
      iSplitR "PC_W1".
      { iRight. iSplit; auto. iPureIntro. enough (x <> (o + 1)) by lia. set_solver.
        iExists tid_w. red_tl. iExists obl_w. red_tl. iExists ds_w. red_tl_all; simpl. iFrame. }
      { iIntros; iExists obl_w. iPoseProof (link_new with "[PC_W1]") as "[LINK _]".
        iSplit. iApply "OBL_n". instantiate (1:=0). simpl. iApply "PC_W1". done.
      }
    }
    
    induction D as [|x D Hx IH] using set_ind_L. { specialize (HD o). apply HD in HOIND. set_solver. }

    iAssert (#=> (prop (S i) (tklockInv i r sr lo' ln' P l)))%I
      with "[P LNPT TCK_B OTCK_BASE LOCKED_O HWAIT HPCS PC_n LOPT TISSUED DUTY_O SDUTY_W_O WAIT_O PENDING_O]" as "CLOSE".
    { simpl. iEval (unfold tklockInv; simpl; red_tl; simpl). iExists (o + 1).
      iEval (red_tl; simpl). iExists n. iEval (red_tl; simpl). iExists obl_n.
      iEval (red_tl; simpl). iExists D. iEval (red_tl_all; simpl).
      iFrame. iSplitR. iModIntro; auto. iSplitR "TISSUED HWAIT HPCS".
      { iModIntro. iLeft. iFrame. iRight. iSplit. iPureIntro; lia.
        iExists tid'''. red_tl. iExists obl'''. red_tl. iExists ds'''.
        red_tl; simpl; iFrame. red_tl_all. iFrame. done.
      }
      rewrite ! red_tl_big_sepS.
      assert (D = D ∖ {[o + 1]} ∖ {[o]} ∪ {[o + 1]} ∪ {[o]}).
      { assert (o + 1 ∈ D) by (apply HD; lia). assert (o ∈ D) by (apply HD; lia). set_unfold. split; ii.
        destruct (Nat.eq_dec x o); [right | left]; auto. destruct (Nat.eq_dec x (o + 1)); [right | left]; auto.
         des; clarify; auto.
      }
      iEval (setoid_rewrite H0). rewrite ! big_opS_union; cycle 1. set_solver. set_unfold. ii. clarify. des; lia.
      iSplitR "TISSUED"; cycle 1.
      { rewrite big_sepS_singleton. red_tl_all. iLeft. iModIntro. iSplit. iPureIntro; lia.
        iExists tid''. red_tl. iExists obl''. red_tl_all; auto.
      }
      iSplitL; cycle 1.
      { rewrite big_sepS_singleton. red_tl_all. iRight. iLeft. iPureIntro; lia. }
      iCombine "HWAIT" "HPCS" as "HWAIT".
      iPoseProof (big_sepS_sep with "HWAIT") as "HWAIT".
      (* assert (D ∖ {[o + 1]} = D ∖ {[o + 1]} ∖ {[o]} ∪ {[o]}).
      { assert (o ∈ D ∖ {[o + 1]}). set_unfold. split. apply HD; lia. lia.
        set_unfold. split; ii.
        { destruct (Nat.eq_dec x o); [right | left]; auto. } des; clarify. }
      iEval (setoid_rewrite H1) in "HWAIT". rewrite ! big_opS_union; cycle 1. set_solver.
      iDestruct "HWAIT" as "[HWAIT HO]". *)
      iApply (big_sepS_impl with "[HWAIT]"); iFrame.
      (* iMod "HPCS" as "#HPCS". *)
      do 2 iModIntro. iIntros (x) "%XIN PRE".
      red_tl_all. iDestruct "PRE" as "[[[%HLT HI] | [%HGT HWAIT]] LINKS]".
      { iLeft. iSplit; auto. iDestruct "HI" as (? ?) "HI". iExists tid0. red_tl. iExists obl. red_tl_all; iFrame. }
      (* { subst; set_solver. } *)
      iDestruct "HWAIT" as (tid_w) "HWAIT". red_tl. iDestruct "HWAIT" as (obl_w) "HWAIT". red_tl.
      iDestruct "HWAIT" as (ds_w) "HWAIT". red_tl_all; simpl.
      iDestruct "HWAIT" as "(DUTY_W & SDUTY_W_W & WAIT_W & PENDING_W & PC_W)".
      iPoseProof ("LINKS" with "[]") as "LINKS". iPureIntro; auto. iDestruct "LINKS" as (obl) "LINK".
      unfold ObligationRA.edges_sat, Region.sat.
      iRight. iRight. iSplit; auto.
      { iPureIntro. enough (x <> (o + 1)) by lia. set_solver. }
      iExists tid_w. red_tl. iExists obl_w. red_tl. iExists ds_w. red_tl_all; simpl. iFrame.

      admit.
    }
    iPoseProof (pcs_cons_unfold with "PCS") as "[PC PCS]". simpl.
    iApply (wpsim_yieldR2 with "[DUTY PCS]").
    instantiate (1:=i); auto. instantiate (1:=1); auto. iFrame.
    iIntros "DUTY CRED3 PCS". rred2r. iApply wpsim_tauR. rred2r.
    iApply ("POST" with "[DUTY]"). simpl. red_tl; simpl. done.
  Admitted.



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
      rewrite ! big_sepS_singleton. red_tl_all. iLeft. iSplitR "TISSUED". iPureIntro; lia.
      iExists tid''. red_tl. iExists obl''. red_tl_all. done.
    }



    


End SPEC.
Global Opaque TicketLock.lock TicketLock.unlock.