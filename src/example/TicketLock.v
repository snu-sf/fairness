From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Import pind Axioms ITreeLib Red TRed IRed2 WFLibLarge.
From Fairness Require Import FairBeh Mod Linking.
From Fairness Require Import PCM IProp IPM IPropAux.
From Fairness Require Import IndexedInvariants OpticsInterp SimWeakest.
From Fairness Require Import TemporalLogic TemporalLogicFull SCMemSpec.

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
  Context `{Σ : GRA.t}.
  Context {TLRAS : @TLRAs XAtom STT Σ}.
  Context {AUXRAS : AUXRAs Σ}.

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

  (* TODO *)

  (** Invariants. *)
  (* Ref: Lecture Notes on Iris. *)
  Definition tklockInv (i : nat) (r or : nat) (lo ln : SCMem.val) (P : Formula i) (l : nat)
    : Formula (1+i) :=
    (∃ (o n o_obl : τ{nat, 1+i}) (D : τ{gset nat, 1+i}),
        (lo ↦ o)
          ∗ (ln ↦ n)
          ∗ ➢(tk_b r o D)
          ∗ (⌜forall tk, (tk < n) <-> (tk ∈ D)⌝)
          ∗ ((➢(tk_locked r o) ∗ (⤉P) ∗
               ((⌜o = n⌝) ∨ (⌜o < n⌝ ∗ ∃ (tid obl: τ{nat}) (ds : τ{ listT (nat * nat * Φ)%ftype, 1+i}),
                                      (⤉Duty(tid) ((o_obl, 0, emp) :: ds))
                                      ∗ (⤉ ○Duty(tid) ds)
                                      ∗ ◇[o_obl](l, 1)
                                      ∗ ➢(otk_w or o tid obl))))
             ∨ (➢(tk_issued r o) ∗  (-[o_obl](0)-◇ emp))
            )
          ∗ ([∗ (1+i) set] tk ∈ D,
              (⌜tk <= o⌝) ∨ (∃ (tid obl : τ{nat}) (ds : τ{ listT (nat * nat * Φ)%ftype, 1+i}),
                               (⤉ Duty(tid) ds)
                                 ∗ (⤉ ○Duty(tid) ds)
                                 ∗ ➢(otk_w or tk tid obl)
                                 ∗ (◇[obl](1 + l, tk - o))
                                 ∗ (o_obl -(0)-◇ obl)
                           )
            )
    )%F.

  (* Namespace for TicketLock invariants. *)
  Definition N_TicketLock : namespace := (nroot .@ "TicketLock").

  Lemma mask_disjoint_ticketlock_state_tgt : ↑N_TicketLock ## (↑N_state_tgt : coPset).
  Proof. apply ndot_ne_disjoint. ss. Qed.

  Definition isTicketLock i (r or: nat) (v : SCMem.val * SCMem.val) (P : Formula i) (l : nat)
    : Formula (1+i) :=
    (∃ (lo ln : τ{SCMem.val}) (N : τ{namespace, 1+i}),
        (⌜(↑N ⊆ (↑N_TicketLock : coPset))⌝)
          ∗ (⌜0 < l⌝) ∗ (⌜v = (lo, ln)⌝) ∗ syn_inv (1+i) N (tklockInv i r or lo ln P l))%F.

  Global Instance isSpinlock_persistent i r or v P l : Persistent (⟦isTicketLock i r or v P l, 1+i⟧).
  Proof.
    unfold Persistent. iIntros "H". unfold isTicketLock.
    red_tl. iDestruct "H" as "[%lo H]". iExists lo.
    red_tl. iDestruct "H" as "[%ln H]". iExists ln.
    red_tl. iDestruct "H" as "[%N H]". iExists N.
    red_tl. rewrite red_syn_inv. iDestruct "H" as "#H". auto.
  Qed.

  Definition mask_has_TicketLock (Es : coPsets) n :=
    (match Es !! n with Some E => (↑N_TicketLock) ⊆ E | None => True end).

  Lemma make_isTicketLock
        i lo ln P l (LT : 0 < l)
        Es
    :
    ⊢
      ⟦((lo ↦ 0) ∗ (ln ↦ 0) ∗ (⤉⤉P) ∗ ➢(tk_auth) ∗ ➢(otk_auth))%F, 2+i⟧
        -∗
        ⟦(∃ (r or : τ{nat, 2+i}), =|2+i|={Es}=> (⤉(isTicketLock i r or (lo, ln) P l)))%F, 2+i⟧.
  Proof.
    red_tl; simpl. iIntros "(LO & LN & P & TAUTH & OTAUTH)".
    iPoseProof (TicketRA_alloc 0 ∅ with "TAUTH") as "(%r & ALLOC)". iExists r. red_tl; simpl.
    iPoseProof (OblTicket_alloc with "OTAUTH") as "(%or & OALLOC)". iExists or.

    rewrite red_syn_fupd; simpl. iMod "ALLOC" as "(TAUTH & TB & TL)". iMod "OALLOC".
    iMod ((FUpd_alloc _ _ _ (S i) (N_TicketLock)) (tklockInv i r or lo ln P l)
      with "[-]") as "#TINV". lia.
    { unfold tklockInv. simpl. red_tl. iExists 0. red_tl; simpl. iExists 0.
      red_tl; simpl. iExists 0. red_tl; simpl. iExists ∅.
      red_tl; simpl. iSplitL "LO"; [ iFrame | ].
      iSplitL "LN"; [ iFrame | ]. iSplitL "TB"; [ iFrame | ].
      iSplit. { iPureIntro. split; i; inv H. }
      iSplitL; cycle 1. auto.
      iLeft. iSplitL "TL"; auto. iSplitL "P"; auto. }
    iModIntro.
    unfold isTicketLock. red_tl; simpl. iExists lo. red_tl; simpl. iExists ln. red_tl; simpl.
    iExists N_TicketLock. red_tl.
    iSplitL ""; [ iPureIntro; set_solver | ].
    iSplitL ""; [ iPureIntro; auto | ].
    iSplitL ""; [ iPureIntro; auto | ].
    rewrite red_syn_inv. auto.
    Unshelve. all: auto.
  Qed.

  Lemma TicketLock_lock_spec
        tid i
        (Es : coPsets)
        (MASK_TOP : OwnEs_top Es)
    :
    ⊢ ∀ r or lo ln (P : Formula i) l (ds : list (nat * nat * Formula (1+i))),
        [@ tid, 1+i, Es @]
          ⧼⟦(((syn_tgt_interp_as (1+i) sndl (fun m => (➢ (scm_memory_black m))))
                ∗ (⤉ isTicketLock i r or (lo, ln) P l)
                ∗ (⤉ Duty(tid) ds)
                ∗ (⤉ ○Duty(tid) ds)
                ∗ (⤉ ●Duty(tid) ds)
                ∗ ◇{ds@1}(3 + l, 1))%F), 2+i⟧⧽
            (OMod.close_itree Client (SCMem.mod gvs) (TicketLock.lock (lo, ln)))
            ⧼rv, ⟦(∃ (o u : τ{nat, 2+i}),
                      (⤉ (⤉ P))
                        ∗ ➢(tk_locked r o)
                        ∗ (⤉ Duty(tid) ((u, 0, emp) :: ds))
                        ∗ (⤉ ○Duty(tid) ds)
                        ∗ (⤉ ●Duty(tid) ds)
                        ∗ ◇[u](l, 1))%F, 2+i⟧⧽
  .
  Proof.
    iIntros. iStartTriple. iIntros "PRE POST". unfold TicketLock.lock.
    iApply wpsim_free_all; auto.
    unfold isTicketLock. iEval (red_tl; simpl; rewrite red_syn_tgt_interp_as) in "PRE".
    iEval (red_tl; simpl) in "PRE".
    iDestruct "PRE" as "(#MEM & PRE & DUTY & WDUTY & BDUTY & PCS)".
    iDestruct "PRE" as (lo') "PRE". iEval (red_tl; simpl) in "PRE".
    iDestruct "PRE" as (ln') "PRE". iEval (red_tl; simpl) in "PRE".
    iDestruct "PRE" as (N) "PRE". iEval (red_tl; simpl; rewrite red_syn_inv) in "PRE".
    iDestruct "PRE" as "(%SUB & %GT & %EQ & #TINV)". symmetry in EQ. clarify.

    (* YIELD *)
    rred2r. iMod (pcs_drop _ _ 1 _ (2+l) 4 with "[PCS]") as "PCS". auto. iFrame.
    iMod (pcs_decr _ _ 1 _ with "PCS") as "[PCS1 PCS2]". auto.
    iMod (pcs_drop _ _ 1 _ 1 1 with "PCS1") as "PCS1". lia.
    iApply (wpsim_yieldR with "[DUTY PCS1]"). { instantiate (1:= 1+i). auto. }
    { iSplitL "DUTY"; iFrame. }
    iIntros "DUTY CRED". iModIntro.

    (* OPEN *)
    iInv "TINV" as "TI" "TI_CLOSE".
    iEval (unfold tklockInv; simpl; red_tl) in "TI".
    iDestruct "TI" as (o) "TI"; iEval (red_tl; simpl) in "TI".
    iDestruct "TI" as (n) "TI"; iEval (red_tl; simpl) in "TI".
    iDestruct "TI" as (u) "TI"; iEval (red_tl; simpl) in "TI".
    iDestruct "TI" as (D) "TI"; iEval (red_tl; simpl) in "TI".

    destruct (Nat.eq_dec o n).
    (* SUCCESS *)
    { subst. iClear "CRED".
      iDestruct "TI" as "(LOPT & LNPT & TB & %HD & HCOND & HWAIT)". rred2r.
      (* FAA *)
      iApply (SCMem_faa_fun_spec with "[LNPT MEM]"). auto.
      { rewrite lookup_insert. pose proof mask_disjoint_ticketlock_state_tgt. set_solver. }
      { iSplitR "LNPT"; done. }
      iIntros (rv) "(%EQ & LNPT)". subst. iEval (ss) in "LNPT". rred2r. iApply wpsim_tauR.
      (* ALLOCATE TICKETS AND OBLIGATIONS TO PUT IN *)
      rred2r. iMod (Ticket_alloc r n D n with "TB") as "[TB TISSUED]".
      { intros H; apply HD in H; lia. }
      iDestruct "HCOND" as "[TKL | [TCONT _]]"; cycle 1.
      (* NO ONE HOLDING THE LOCK *)
      { iExFalso. iApply (Ticket_issued_twice with "[TCONT TISSUED]"). iFrame. }
      iDestruct "TKL" as "(TKL & P & [_ | [%NEQ _]])"; cycle 1. lia.
      iMod (alloc_obligation (1+l) 4) as "(%o_obl & #OBL & PC)".
      iPoseProof (pc_split _ _ 1 _ with "[PC]") as "[PC3 PC2]". simpl. done.
      iMod (pc_drop _ 1 with "PC2") as "PC2". lia. lia.
      iPoseProof (pc_split _ _ 1 _ with "[PC2]") as "[PC1 PC2]". simpl. done.
      iMod (pc_drop _ l with "PC3") as "PC3". lia. lia.
      iPoseProof (duty_add with "[DUTY PC1] []") as "DUTY".
      { iSplitL "DUTY"; done. }
      { instantiate (1:=emp%F). simpl.  red_tl. iModIntro. iIntros. iModIntro. done. }
      iMod "DUTY".
      iPoseProof (duty_tpromise with "DUTY") as "#ULKPRM".
      { simpl. left; auto. }
      (* CLOSE *)
      iMod ("TI_CLOSE" with "[LOPT LNPT TB TISSUED HWAIT]") as "_".
      { iEval (unfold tklockInv; simpl; red_tl). iExists n.
        iEval (red_tl; simpl). iExists (n+1).
        iEval (red_tl; simpl). iExists o_obl.
        iEval (red_tl; simpl). iExists (D ∪ {[n]}).
        iEval (red_tl; simpl). iSplitL "LOPT"; auto. iSplitL "LNPT"; auto.
        iSplitL "TB"; auto. iSplit.
        { iPureIntro; auto. split; ii.
          { destruct (Nat.eq_dec tk n); [set_solver|].
            assert (HLT : tk < n) by lia; apply HD in HLT; set_solver. }
          { rewrite elem_of_union in H; destruct H.
            { apply HD in H; lia. } { rewrite elem_of_singleton in H; clarify; lia. } } }
        iSplitL "TISSUED".
        { iRight; iSplit; auto. }
        { repeat rewrite red_tl_big_sepS. rewrite big_opS_union. iSplitL; cycle 1.
          { rewrite big_sepS_singleton. red_tl. iLeft; done. }
          { iApply (big_sepS_impl with "HWAIT"). iModIntro. iIntros "%x %HXD PRE".
            red_tl. iLeft. iPureIntro. apply HD in HXD. lia. }
          set_unfold. ii. subst. apply HD in H; lia. } }
      iEval (rewrite unfold_iter_eq; rred2r).
      (* YIELD *)
      iPoseProof (pc_split _ _ 1 _ with "PC2") as "[PC1 PC2]".
      iMod (pcs_decr _ _ 1 _ with "PCS2") as "[PCS1 PCS2]". auto.
      iMod (pcs_drop _ _ 1 _ 1 1 with "PCS1") as "PCS1". lia.
      iApply (wpsim_yieldR with "[DUTY PCS1 PC1]"). auto.
      { iSplitL "DUTY". done.
        iApply (pcs_cons_fold with "[PCS1 PC1]").
        { iEval (rewrite Nat.add_comm). iSplitL "PC1"; done. } }
      iIntros "DUTY _". iModIntro. rred2r.
      (* LOAD - OPEN INVARIANT *)
      iInv "TINV" as "TI" "TI_CLOSE".
      iEval (unfold tklockInv; simpl; red_tl) in "TI".
      iDestruct "TI" as (o') "TI"; iEval (red_tl; simpl) in "TI".
      iDestruct "TI" as (n') "TI"; iEval (red_tl; simpl) in "TI".
      iDestruct "TI" as (o_obl') "TI"; iEval (red_tl; simpl) in "TI".
      iDestruct "TI" as (D') "TI"; iEval (red_tl; simpl) in "TI".
      iDestruct "TI" as "(LOPT & LNPT & TB & %HD' & [(TKL' & P' & _) | [TISSUED #ULKPRM']] & HWAIT)".
      { iExFalso; iApply (Ticket_locked_twice with "[TKL TKL']"). iSplitL "TKL"; done. }
      iPoseProof (Ticket_black_locked with "[TKL TB]") as "%EQ".
      iSplitL "TKL"; done. symmetry in EQ; subst.
      (* LOAD *)
      iApply (SCMem_load_fun_spec with "[LOPT]"). auto.
      { rewrite lookup_insert. pose proof mask_disjoint_ticketlock_state_tgt. set_solver. }
      { iSplitR "LOPT"; done. }
      iIntros (rv) "[%EQ LOPT]"; subst. rred2r. iApply (wpsim_tauR). rred2r.
      (* CLOSE *)
      iMod ("TI_CLOSE" with "[LOPT LNPT TB TISSUED HWAIT]") as "_".
      { iEval (unfold tklockInv; simpl; red_tl). iExists n.
        iEval (red_tl; simpl). iExists n'.
        iEval (red_tl; simpl). iExists o_obl'.
        iEval (red_tl; simpl). iExists D'.
        iEval (red_tl; simpl). iSplitL "LOPT"; auto. iSplitL "LNPT"; auto.
        iSplitL "TB"; auto. iSplit. auto.
        iSplitL "TISSUED".
        { iRight; iSplit; auto. }
        { done. } }
      iClear "ULKPRM'". clear n' HD' D' o_obl'.
      (* YIELD *)
      iMod (pcs_decr _ _ 1 _ with "PCS2") as "[PCS1 PCS2]". auto.
      iMod (pcs_drop _ _ 1 _ 1 1 with "PCS1") as "PCS1". lia.
      iPoseProof (pc_split _ _ 1 _ with "PC2") as "[PC1 PC2]".
      iApply (wpsim_yieldR with "[DUTY PCS1 PC1]"). auto.
      { iSplitL "DUTY". done.
        iApply (pcs_cons_fold with "[PCS1 PC1]").
        { iEval (rewrite Nat.add_comm). iSplitL "PC1"; done. } }
      iIntros "DUTY _". iModIntro. rred2r.
      (* COMPARE - OPEN INVARIANT *)
      iInv "TINV" as "TI" "TI_CLOSE".
      iEval (unfold tklockInv; simpl; red_tl) in "TI".
      iDestruct "TI" as (o') "TI"; iEval (red_tl; simpl) in "TI".
      iDestruct "TI" as (n') "TI"; iEval (red_tl; simpl) in "TI".
      iDestruct "TI" as (o_obl') "TI"; iEval (red_tl; simpl) in "TI".
      iDestruct "TI" as (D') "TI"; iEval (red_tl; simpl) in "TI".
      iDestruct "TI" as "(LOPT & LNPT & TB & %HD' & [(TKL' & P' & _) | [TISSUED #ULKPRM']] & HWAIT)".
      { iExFalso; iApply (Ticket_locked_twice with "[TKL TKL']"). iSplitL "TKL"; done. }
      iPoseProof (Ticket_black_locked with "[TKL TB]") as "%EQ".
      iSplitL "TKL"; done. symmetry in EQ; subst.
      (* COMPARE *)
      iApply (SCMem_compare_fun_spec with "[MEM]"). auto.
      { unfold mask_has_st_tgt. rewrite lookup_insert.
        pose proof mask_disjoint_ticketlock_state_tgt. set_solver. }
      { simpl. des_ifs. iApply (tgt_interp_as_equiv with "MEM"). iIntros. iSplit.
        { iIntros. simpl. red_tl; simpl. iSplit; [done | iPureIntro; auto]. }
        { simpl. red_tl; simpl. iIntros "[? _]". done. } }
      iIntros (rv) "[%EQ _]". exploit EQ. auto. i; subst. rred2r. iApply wpsim_tauR. rred2r.
      (* POST *)
      iMod ("TI_CLOSE" with "[LOPT LNPT TB TISSUED HWAIT]") as "_".
      { iEval (unfold tklockInv; simpl; red_tl). iExists n.
        iEval (red_tl; simpl). iExists n'.
        iEval (red_tl; simpl). iExists o_obl'.
        iEval (red_tl; simpl). iExists D'.
        iEval (red_tl; simpl). iSplitL "LOPT"; auto. iSplitL "LNPT"; auto.
        iSplitL "TB"; auto. iSplit. auto.
        iSplitL "TISSUED".
        { iRight; iSplit; auto. }
        { done. } }
      (* SYNC *)
      iMod (pcs_drop _ _ 1 _ 1 1 with "PCS2") as "PCS2". lia.
      iApply (wpsim_yieldR with "[DUTY PCS2 PC2]"). auto.
      { iSplitL "DUTY". done.
        iApply (pcs_cons_fold with "[PCS2 PC2]").
        { iEval (rewrite Nat.add_comm). iSplitL "PC2"; done. } }
      iIntros "DUTY _". iModIntro. rred2r. iApply wpsim_tauR. rred2r.
      (* POST *)
      iEval (red_tl) in "POST".
      iApply ("POST" with "[-]").
      { iExists n. red_tl. iExists o_obl. red_tl; simpl.
        iSplitL "P"; [ red_tl; done | ].
        iSplitL "TKL"; [ red_tl; done | ].
        iSplitL "DUTY"; [ red_tl; done | ].
        red_tl; simpl. iSplitL "WDUTY"; [done | iSplitL "BDUTY"; [done | done]]. } }

    (* FAILURE *)
    iDestruct "TI" as "(LOPT & LNPT & TB & %HD' & HCOND & HWAIT)". rred2r.
    iApply (SCMem_faa_fun_spec with "[MEM LNPT]"). auto.
    { rewrite lookup_insert. pose proof mask_disjoint_ticketlock_state_tgt. set_solver. }
    { iSplitR "LNPT"; done. }
    iIntros (rv) "[%EQ LNPT]". subst. iEval (simpl) in "LNPT".
    rred2r. iApply wpsim_tauR. rred2r.
    (* ISSUE A TICKET *)
    iMod (Ticket_alloc _ _ _ n with "TB") as "[TB TISSUED]".
    { intros H; apply HD' in H; lia. }
    (* ALLOCATE OBLIGATION - SOMEBODY GIVE ME THE LOCK *)
    (* iMod (alloc_obligation (1+l) 4) as "(%o_obl & #OBL & PC)". *)
    (* iMod () *)
    (* YIELD *)
    iEval (rewrite unfold_iter_eq; simpl). rred2r.
    iMod (pcs_decr _ _ 1 _ with "PCS2") as "[PCS1 PCS2]". auto.
    iMod (pcs_drop _ _ 1 _ 1 1 with "PCS1") as "PCS1". lia.
    iApply (wpsim_yieldR with "[DUTY PCS1]"). auto.
    { iSplitL "DUTY"; done. }
    iIntros "DUTY CRED2".
    iPoseProof ("TI_CLOSE" with "[LOPT LNPT TB HCOND HWAIT TISSUED DUTY WDUTY BDUTY]") as "CLOSED".
    { iEval (unfold tklockInv; simpl; red_tl). iExists o.
      iEval (red_tl; simpl). iExists (n + 1).
      iEval (red_tl; simpl). iExists u.
      iEval (red_tl; simpl). iExists (D ∪ {[n]}).
      iEval (red_tl; simpl). iSplitL "LOPT"; auto. iSplitL "LNPT"; auto.
      iSplitL "TB"; auto. iSplit.
      { iPureIntro. split; i.
        { destruct (Nat.eq_dec tk n); [set_solver|].
          assert (HLT : tk < n) by lia; apply HD' in HLT; set_solver.
        }
        { rewrite elem_of_union in H; destruct H.
          { apply HD' in H; lia. } { rewrite elem_of_singleton in H; clarify; lia. }
        }
      }
      iSplitR "HWAIT WDUTY BDUTY DUTY".
      { admit. }
      { repeat rewrite red_tl_big_sepS. rewrite big_opS_union. iSplitL "HWAIT"; cycle 1.
        { rewrite big_sepS_singleton. red_tl. iRight. iExists tid. red_tl; simpl. admit. }
          (* iExists o_obl. } *)
      { iApply (big_sepS_impl with "HWAIT"). iModIntro. iIntros "%x %HXD PRE".
        red_tl. iLeft. iPureIntro. admit. }
      set_unfold. ii. subst. admit. }
    }
    iApply elim_modal_FUpd_FUpd; cycle 1. iSplitL "CLOSED".  rewrite /ElimModal bi.intuitionistically_if_elim.
    iMod ("CLOSED") as "_".
    iModIntro. { apply map_Forall_lookup. ii. unfold OwnEs_top.  }

    iDestruct "HCOND" as "[(TKL & P & [%EQ | [%HGT DUTIES]]) | [TISSUED #ULKPRM]]".
    { clarify. }
    (* CASE 1 : NOT MY TURN, BUT LOCK NOT TAKEN *)
    { iDestruct "DUTIES" as (owner) "DUTIES". iEval (red_tl; simpl) in "DUTIES".
      iDestruct "DUTIES" as (o_obl) "DUTIES". iEval (red_tl; simpl) in "DUTIES".
      iDestruct "DUTIES" as (o_ds) "DUTIES". iEval (red_tl; simpl) in "DUTIES".
    }
      
        

      (* INDUCTION *)

  Admitted.

  Lemma TicketLock_unlock_spec
        tid i
        (Es : coPsets)
        (MASK_TOP : OwnEs_top Es)
    :
    ⊢ ∀ r lo ln (P : Formula i) l (ds : list (nat * nat * Formula i)) u o,
        [@ tid, 1+i, Es @]
          ⧼⟦((syn_tgt_interp_as (1+i) sndl (fun m => (➢ (scm_memory_black m))))
               ∗ (⤉ isTicketLock i r (lo, ln) P l)
               ∗ (⤉ (⤉ P))
               ∗ ➢(tkl_locked r o)
               ∗ (⤉ (⤉ Duty(tid) ((u, 0, emp) :: ds)))
               ∗ live[u] (1/2)
               ∗ ◇{((u, 0, emp) :: ds)@1}(1, 3))%F, 2+i⟧⧽
            (OMod.close_itree Client (SCMem.mod gvs) (TicketLock.unlock (lo, ln)))
            ⧼rv, ⟦((⤉ (⤉ Duty(tid) ds))
                     ∗ (⤉ (⤉ ○Duty(tid) ds))
                     ∗ (⤉ (⤉ ●Duty(tid) ds))
                  )%F, 2+i⟧⧽
  .
  Proof.
  Admitted.

End SPEC.
Global Opaque TicketLock.lock TicketLock.unlock.
