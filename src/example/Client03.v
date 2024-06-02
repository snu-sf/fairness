From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Import pind Axioms ITreeLib Red TRed IRed2 WFLibLarge.
From Fairness Require Import FairBeh Mod Concurrency Linking.
From Fairness Require Import PCM IProp IPM IPropAux.
From Fairness Require Import IndexedInvariants OpticsInterp SimWeakest.
From Fairness Require Import TemporalLogic TemporalLogicFull SCMemSpec Spinlock.

Module Client03.

  Definition gvs : list nat := [2].
  Definition L : SCMem.val := SCMem.val_ptr (0, 0).
  Definition C : SCMem.val := SCMem.val_ptr (1, 0).
  Definition D : SCMem.val := SCMem.val_ptr (2, 0).

  Section CODE.

    Definition state := unit.
    Definition ident := void.

    Definition incr (n : nat) :
      itree (threadE ident state) unit
      :=
      _ <- (trigger Yield;;; Spinlock.lock L);;
      c <- (OMod.call (R:=SCMem.val) "load" C);;
      _ <- (OMod.call (R:=unit) "store" (C, SCMem.val_add c n));;
      _ <- (trigger Yield;;; Spinlock.unlock L);; Ret tt.

    Definition read :
      itree (threadE ident state) SCMem.val
      :=
      _ <- (trigger Yield;;; Spinlock.lock L);;
      c <- (OMod.call (R:=SCMem.val) "load" C);;
      _ <- (trigger Yield;;; Spinlock.unlock L);;
      Ret c.

    Definition thread1 :
      ktree (threadE ident state) unit SCMem.val
      :=
      fun _ =>
        _ <- trigger Yield;;
        let a := (0 : nat) in
        _ <- (ITree.iter (fun (i : nat) =>
                           r <- (if (Nat.eq_dec i 100)
                                then Ret (inr tt)
                                else _ <- incr 2;; _ <- trigger Yield;; Ret (inl (i + 1)));;
                           Ret r) a);;
        r <- (ITree.iter (fun (_ : unit) =>
                           d <- (OMod.call (R:=SCMem.val) "load" D);;
                           b <- (OMod.call (R:=bool) "compare" (d, 0 : SCMem.val));;
                           r <- (if b
                                then Ret (inl tt)
                                else c <- read;; Ret (inr c));;
                           Ret r) tt);;
        _ <- trigger Yield;;
        Ret r.

    Definition thread2 :
      ktree (threadE ident state) unit SCMem.val
      :=
      fun _ =>
        _ <- trigger Yield;;
        let a := (0 : nat) in
        _ <- (ITree.iter (fun (i : nat) =>
                           r <- (if (Nat.eq_dec i 10)
                                then Ret (inr tt)
                                else _ <- incr 5;; _ <- trigger Yield;; Ret (inl (i + 1)));;
                           Ret r) a);;
        _ <- (OMod.call (R:=unit) "store" (D, 1 : SCMem.val));;
        r <- read;;
        _ <- trigger Yield;;
        Ret r.

    Definition omod : Mod.t :=
      Mod.mk
        tt
        (Mod.get_funs [("thread1", Mod.wrap_fun thread1);
                       ("thread2", Mod.wrap_fun thread2)])
    .

    Definition module : Mod.t :=
      OMod.close
        (omod)
        (SCMem.mod gvs)
    .

  End CODE.

End Client03.

Module Client03Spec.

  Section SPEC.

    Definition state := unit.
    Definition ident := void.

    Definition thread1 :
      ktree (threadE ident state) unit SCMem.val
      :=
      fun _ =>
        _ <- trigger Yield;; Ret (250 : SCMem.val).

    Definition thread2:
      ktree (threadE void unit) unit SCMem.val
      :=
      fun _ =>
        _ <- trigger Yield;;
        n <- trigger (Choose nat);;
        _ <- trigger Yield;; Ret ((2 * n) + 50 : SCMem.val).

    Definition module : Mod.t :=
      Mod.mk
        tt
        (Mod.get_funs [("thread1", Mod.wrap_fun thread1);
                       ("thread2", Mod.wrap_fun thread2)])
    .

  End SPEC.

End Client03Spec.

Section SPEC.

  Notation src_state := (Mod.state Client03Spec.module).
  Notation src_ident := (Mod.ident Client03Spec.module).
  Notation tgt_state := (Mod.state Client03.module).
  Notation tgt_ident := (Mod.ident Client03.module).

  Local Instance STT : StateTypes := Build_StateTypes src_state tgt_state src_ident tgt_ident.
  Context `{Σ : GRA.t}.
  Context {TLRAS : @TLRAs XAtom STT Σ}.
  Context {AUXRAS : AUXRAs Σ}.

  Import Client03.

  (** Invariants. *)

  (* Namespace for Client03 invariants. *)
  Definition N_Client03 : namespace := (nroot .@ "Client03").
  Definition N_t2_write_inv : namespace := (N_Client03 .@ "t2_write").
  Definition N_t2_promise_inv : namespace := (N_Client03 .@ "t2_promise").

  Definition counter n c1 c2 r1 r2 : Formula n :=
    (∃ (x y : τ{nat}), (C ↦ ((c1 * x) + (c2 * y))) ∗ ➢(auexa_b r1 (x : nat)) ∗ ➢(auexa_b r2 (y : nat)))%F.

  Definition t2_write n r : Formula n :=
    (➢(auexa_w r (10 : nat)) ∗ (D ↦ 1))%F.

  Definition t2_write_inv n r : Formula n :=
    (syn_inv n N_t2_write_inv (t2_write n r))%F.

  Definition t2_promise n w r : Formula n :=
    ((live[w] (1/2) ∗ (D ↦ 0)) -U-[w](0)-◇ (dead[w] ∗ (t2_write_inv n r)))%F.

  Definition t2_promise_inv n w r : Formula n :=
    (syn_inv n N_t2_promise_inv (t2_promise n w r))%F.

  (** Simulation proof. *)

  Lemma Client03_incr_spec
        tid N Es
        (TOP : OwnEs_top Es)
    :
    ⊢ ∀ (r k lft l r1 r2 a c1 c2 c0 r0 : τ{nat, 1+N}) (ds : list (nat * nat * Formula N))
      ,
        [@ tid, N, Es @]
          ⧼⟦((syn_tgt_interp_as N sndl (λ m : SCMem.t, ➢(scm_memory_black m)))
               ∗ (⤉ Duty(tid) ds) ∗ ◇{ds@1}(2+lft, 2)
               ∗ (⤉ isSpinlock N r L (counter N c1 c2 r1 r2) k lft l)
               ∗ (⌜2 <= l⌝) ∗ live[k] (1/2) ∗ ◇[k](1+l, 1)
               ∗ ➢(auexa_w r0 (a : nat))
               ∗ ⌜(r0 = r1 /\ c0 = c1) \/ (r0 = r2 /\ c0 = c2)⌝
            )%F, 1+N⟧⧽
            (OMod.close_itree omod (SCMem.mod gvs) (incr c0))
            ⧼rv, ⟦((⤉ Duty(tid) ds) ∗ live[k] (1/2) ∗  ➢(auexa_w r0 (a + 1)))%F, 1+N⟧⧽
  .
  Proof.
    iIntros. iStartTriple.
    red_tl. rewrite red_syn_tgt_interp_as.
    iIntros "(#MEM & DUTY & PCS & #ISL & %LE & LIVE_k & PC_k & CNTW_r0 & %CASES)".
    iMod (pcs_decr _ _ 1 1 with "PCS") as "[PCS PCS_SPIN]". lia.
    iMod (pcs_drop _ _ _ _ 1 100 with "PCS") as "PCS". lia.
    iIntros "POST".
    unfold incr. rred.
    iApply (wpsim_yieldR2 with "[DUTY PCS]").
    3:{ iFrame. }
    auto. lia.
    iIntros "DUTY _ PCS". iModIntro. rred2r. iApply wpsim_tauR. rred2r.
    iApply (Spinlock_lock_spec with "[LIVE_k DUTY PCS_SPIN] [-]").
    1,2: ss.
    { red_tl. rewrite red_syn_tgt_interp_as. iSplit. eauto. iSplitR. eauto. iFrame. }
    Unshelve. 2: lia.
    iEval (red_tl). iIntros (_) "[%u A]". iEval (unfold counter; red_tl; simpl) in "A".
    iDestruct "A" as "([%x A] & LOCKED & LIVE_k & DUTY & LIVE_u & PC_u)". iEval (red_tl) in "A".
    iDestruct "A" as "[%y A]". iEval (red_tl) in "A". iDestruct "A" as "(PT & CNTB_r1 & CNTB_r2)".
    rred2r. iMod (pc_drop _ 1 _ _ 99 with "PC_u") as "PC_u". lia.
    Unshelve. 2: lia.
    iPoseProof (pcs_cons_fold with "[PC_u PCS]") as "PCS".
    { simpl. iSplitR "PCS". 2: iFrame. instantiate (1:=0). iFrame. }
    iApply (wpsim_yieldR2 with "[DUTY PCS]").
    3:{ iSplitL "DUTY". iFrame. iFrame. }
    auto. lia.
    iIntros "DUTY _ PCS". iModIntro. rred2r.
    iApply (SCMem_load_fun_spec with "[PT]").
    3:{ iFrame. eauto. }
    auto. ss.
    iIntros (rv) "[%RV PT]". rred2r. iApply wpsim_tauR. rred2r.
    iApply (wpsim_yieldR2 with "[DUTY PCS]").
    3:{ iSplitL "DUTY"; iFrame. }
    auto. lia.
    iIntros "DUTY _ PCS". iModIntro. rred2r.
    iApply (SCMem_store_fun_spec with "[PT]").
    3:{ iFrame. eauto. }
    auto. ss.
    iIntros (rv0) "PT". rred2r. iApply wpsim_tauR. rred2r.
    iApply (wpsim_yieldR2 with "[DUTY PCS]").
    3:{ iSplitL "DUTY"; iFrame. }
    auto. lia.
    iIntros "DUTY _ PCS". iEval (simpl) in "PCS". iModIntro. rred2r. iApply wpsim_tauR. rred2r.
    destruct CASES as [CASE | CASE]; des; subst r0; subst c0.
    - replace (SCMem.val_add rv c1) with ((c1 * (1 + x) + c2 * y) : SCMem.val).
      2:{ subst rv. ss. f_equal. lia. }
      iPoseProof (auexa_b_w_eq with "CNTB_r1 CNTW_r0") as "%EQ". subst a.
      iMod (auexa_b_w_update _ _ _ _ nat (1 + x) with "CNTB_r1 CNTW_r0") as "[CNTB_r1 CNTW_r0]".
      iMod (pcs_decr _ _ 1 1 with "PCS") as "[PCS _]". lia.
      iApply (Spinlock_unlock_spec with "[CNTB_r1 CNTB_r2 PT LOCKED LIVE_k DUTY PCS LIVE_u PC_k]").
      3:{ repeat (try rewrite @red_tl_sepconj). simpl.
          iSplitR. rewrite red_syn_tgt_interp_as. eauto. iSplitR. eauto.
          unfold counter. red_tl. iSplitL "PT CNTB_r1 CNTB_r2".
          { iExists _. red_tl. iExists _. red_tl. iFrame. }
          simpl. iFrame.
      }
      1,2: ss.
      iEval red_tl. iIntros (_) "[DUTY LIVE_k]". rred2r.
      iApply "POST". replace (1+x) with (x+1). iFrame. lia.
    - replace (SCMem.val_add rv c2) with ((c1 * x + c2 * (1 + y)) : SCMem.val).
      2:{ subst rv. ss. f_equal. lia. }
      iPoseProof (auexa_b_w_eq with "CNTB_r2 CNTW_r0") as "%EQ". subst a.
      iMod (auexa_b_w_update _ _ _ _ nat (1 + y) with "CNTB_r2 CNTW_r0") as "[CNTB_r2 CNTW_r0]".
      iMod (pcs_decr _ _ 1 1 with "PCS") as "[PCS _]". lia.
      iApply (Spinlock_unlock_spec with "[CNTB_r1 CNTB_r2 PT LOCKED LIVE_k DUTY PCS LIVE_u PC_k]").
      3:{ repeat (try rewrite @red_tl_sepconj). simpl.
          iSplitR. rewrite red_syn_tgt_interp_as. eauto. iSplitR. eauto.
          unfold counter. red_tl. iSplitL "PT CNTB_r1 CNTB_r2".
          { iExists _. red_tl. iExists _. red_tl. iFrame. }
          simpl. iFrame.
      }
      1,2: ss.
      iEval red_tl. iIntros (_) "[DUTY LIVE_k]". rred2r.
      iApply "POST". replace (1+y) with (y+1). iFrame. lia.
  Qed.

  Local Opaque incr.

  Lemma Client03_thread1_spec
        tid N
    :
    ⊢ ⟦(∀ (r k w wl r1 r2 : τ{nat, 1+N}),
           ((syn_tgt_interp_as N sndl (fun m => (➢ (scm_memory_black m))))
               ∗ ○(tid)
               ∗ (⤉ Duty(tid) [])
               ∗ (⤉ isSpinlock N r L (counter N 2 5 r1 r2) k 4 2)
               ∗ live[k] (1/2)
               ∗ ◇[k](3, 101)
               ∗ ➢(auexa_w r1 0)
               ∗ ◆[w, wl]
               ∗ (⤉ t2_promise_inv N w r2)
            )
              -∗
              syn_wpsim (1+N) tid ∅
              (fun rs rt => (⤉(syn_term_cond N tid _ rs rt))%F)
              false false
              (fn2th Client03Spec.module "thread1" (tt ↑))
              (fn2th Client03.module "thread1" (tt ↑)))%F, 1+N⟧.
  Proof.
    iIntros. simpl.
    red_tl; iIntros (r). red_tl. iIntros (k). red_tl. iIntros (w). red_tl. iIntros (wl). red_tl. iIntros (r1). red_tl. iIntros (r2).
    red_tl. simpl.
    rewrite red_syn_tgt_interp_as. unfold t2_promise_inv. rewrite red_syn_inv. rewrite red_syn_wpsim.
    iIntros "(#MEM & TID & DUTY & #ISL & LIVE_k & PC_k & CNTW_r1 & #LO_w & #UNTILI)".
    unfold fn2th. simpl. lred2r. rred2r.
    iApply (wpsim_yieldR with "[DUTY]").
    2:{ iSplitL "DUTY". iApply "DUTY". simpl. ss. }
    auto.
    iIntros "DUTY _". iModIntro. rred2r. iApply wpsim_tauR. rred2r.
    assert (exists j, 0 = j). eauto. des.
    replace 
      (ITree.iter
         (λ i : nat,
             ` r0 : nat + () <- (if Nat.eq_dec i 100 then Ret (inr ()) else incr 2;;; trigger Yield;;; Ret (inl (i + 1)));; Ret r0)
         0)
      with
      (ITree.iter
         (λ i : nat,
             ` r0 : nat + () <- (if Nat.eq_dec i 100 then Ret (inr ()) else incr 2;;; trigger Yield;;; Ret (inl (i + 1)));; Ret r0)
         j).
    2:{ subst j. auto. }
    iEval (replace 250 with ((100 * 2) + 50)).
    remember (100 - j) as J.
    assert (100 = J). subst. ss.
    iEval (rewrite H0) in "PC_k". iEval (rewrite H) in "CNTW_r1".
    assert (LT : j <= 100). subst. lia.
    clear H0 H.
    iStopProof.
    revert j HeqJ LT. induction J; cycle 1.
    { i. iIntros "((#MEM & #ISL & #LO_w & #UNTILI) & TID & LIVE_k & PC_k & CNTW_r1 & DUTY)".
      iEval (rewrite unfold_iter_eq). rred2r.
      destruct (Nat.eq_dec j 100).
      { exfalso. lia. }
      rred2.
      iPoseProof (pc_split _ _ 1 (S J) with "PC_k") as "[PC_k1 PC_k]".
      iApply (Client03_incr_spec with "[DUTY LIVE_k PC_k1 CNTW_r1] [TID PC_k]").
      ss.
      { red_tl. simpl. iSplitR. rewrite red_syn_tgt_interp_as. eauto. iFrame.
        simpl. iSplitR; [iApply pcs_nil |]. iSplit. eauto. iSplit; eauto.
      }
      iEval red_tl. iIntros (_) "(DUTY & LIVE_k & CNTW_r1)". rred2r.
      iApply (wpsim_yieldR with "[DUTY]").
      2:{ iSplitL "DUTY". iApply "DUTY". simpl. ss. }
      auto.
      iIntros "DUTY _". iModIntro. rred2r. iApply wpsim_tauR. rred2r.
      iApply wpsim_tauR.
      specialize (IHJ (j+1)).
      iPoseProof (IHJ with "[TID LIVE_k PC_k CNTW_r1 DUTY]") as "IH".
      { lia. }
      { lia. }
      { iSplit. iModIntro. eauto. iFrame. }
      iApply "IH".
    }
    i. iIntros "((#MEM & #ISL & #LO_w & #UNTILI) & TID & LIVE_k & PC_k & CNTW_r1 & DUTY)".
    iEval (rewrite unfold_iter_eq). rred2r.
    destruct (Nat.eq_dec j 100).
    2:{ exfalso. lia. }
    rred2r.
    (* Set-up for induction. *)
    iEval (rewrite unfold_iter_eq). rred2r.
    iApply (wpsim_yieldR with "[DUTY]").
    2:{ iFrame. }
    auto.
    iIntros "DUTY _". iModIntro. rred2r.
    iInv "UNTILI" as "UNTIL" "UNTIL_CLOSE".
    iEval (unfold t2_promise; simpl; red_tl) in "UNTIL". iEval (rewrite red_syn_until_tpromise) in "UNTIL".
    iPoseProof (until_tpromise_get_tpromise with "UNTIL") as "#TPROM".
    iRevert "TID LIVE_k PC_k CNTW_r1 DUTY UNTIL_CLOSE".
    iMod (until_tpromise_ind with "[UNTIL] []") as "IH".
    { iSplitR. eauto. iFrame. }
    2:{ iApply "IH". }
    iSplit; iModIntro.
    { iIntros "IH". iModIntro. iIntros "CUR TID LIVE_k PC_k CNTW_r1 DUTY UNTIL_CLOSE".
      iEval (simpl; red_tl; simpl) in "CUR". iDestruct "CUR" as "[CUR0 CUR]".
      iApply (SCMem_load_fun_spec with "[CUR] [-]").
      3:{ iFrame. eauto. }
      auto.
      { rewrite lookup_insert. assert (↑N_state_tgt ## (↑N_t2_promise_inv : coPset)).
        { apply ndot_preserve_disjoint_r. apply ndot_ne_disjoint. ss. }
        set_solver.
      }
      iIntros (rv) "[%RVEQ PTD]". subst rv. rred2r. iApply wpsim_tauR. rred2r.
      iMod ("UNTIL_CLOSE" with "[CUR0 PTD]") as "_".
      { unfold t2_promise. simpl. rewrite red_syn_until_tpromise. iApply until_tpromise_make1. simpl. red_tl. iFrame. auto. }
      iApply (wpsim_yieldR with "[DUTY]").
      2:{ iFrame. }
      auto.
      iIntros "DUTY FC". iModIntro. rred2r. iApply (SCMem_compare_fun_spec with "[] [-]").
      3:{ iApply tgt_interp_as_equiv. 2: eauto. ss. iIntros. red_tl.
          ss. iSplit. iIntros "MEM"; iFrame. ss. iIntros "[MEM _]". iFrame.
      }
      auto. ss.
      iIntros (rv) "[%TRUE _]". specialize (TRUE eq_refl). subst rv. rred2r. iApply wpsim_tauR.
      rred2r. iApply wpsim_tauR.
      iEval (rewrite unfold_iter_eq). rred2r.
      iApply (wpsim_yieldR with "[DUTY]").
      2:{ iFrame. }
      auto.
      iIntros "DUTY _". iModIntro. rred2r.
      iInv "UNTILI" as "UNTIL" "UNTIL_CLOSE".
      iEval (unfold t2_promise; simpl; red_tl) in "UNTIL". iEval (rewrite red_syn_until_tpromise) in "UNTIL".
      iMod ("IH" with "[FC UNTIL]") as "IH".
      { iFrame. }
      iApply ("IH" with "TID LIVE_k PC_k CNTW_r1 DUTY UNTIL_CLOSE").
    }
    { iIntros "#PR". iIntros "TID LIVE_k PC_k CNTW_r1 DUTY UNTIL_CLOSE".
      iMod ("UNTIL_CLOSE" with "[]") as "_".
      { unfold t2_promise. simpl. rewrite red_syn_until_tpromise. iApply until_tpromise_make2. simpl. iSplit; eauto. }
      iEval (unfold t2_write_inv; simpl; red_tl) in "PR". iEval (rewrite red_syn_inv) in "PR".
      iDestruct "PR" as "[DEAD PR]".
      iInv "PR" as "PRO" "PR_CLOSE". iEval (unfold t2_write; simpl; red_tl) in "PRO".
      iDestruct "PRO" as "[RES PTD]".
      iApply (SCMem_load_fun_spec with "[PTD] [-]").
      3:{ iFrame. eauto. }
      auto.
      { rewrite lookup_insert. assert (↑N_state_tgt ## (↑N_t2_write_inv : coPset)).
        { apply ndot_preserve_disjoint_r. apply ndot_ne_disjoint. ss. }
        set_solver.
      }
      iIntros (rv) "[%RVEQ PTD]". subst rv. rred2r. iApply wpsim_tauR. rred2r.
      iMod ("PR_CLOSE" with "[PTD RES]") as "_".
      { unfold t2_write. simpl. red_tl. iFrame. }
      iApply (wpsim_yieldR with "[DUTY]").
      2:{ iFrame. }
      auto.
      iIntros "DUTY _". iModIntro. rred2r.
      iApply (SCMem_compare_fun_spec with "[] [-]").
      3:{ iApply tgt_interp_as_equiv. 2: eauto. ss. iIntros. red_tl.
          ss. iSplit. iIntros "MEM"; iFrame. ss. iIntros "[MEM _]". iFrame.
      }
      auto. ss.
      iIntros (rv) "[_ %FALSE]". exploit FALSE. ss. intros; subst. clear FALSE. rred2r.
      iApply wpsim_tauR. rred2r.
      iApply (wpsim_yieldR with "[DUTY]").
      2:{ iFrame. }
      auto.
      iIntros "DUTY _". iModIntro. rred2r. iApply wpsim_tauR. rred2r.
      iApply (Spinlock_lock_spec with "[LIVE_k DUTY] [-]").
      3:{ red_tl. iSplitR. rewrite red_syn_tgt_interp_as. eauto. iSplitR. eauto. iFrame. }
      ss. ss.
      iEval red_tl. iIntros (_) "[%u POST]". iEval (red_tl; simpl) in "POST".
      iDestruct "POST" as "(CNT & LOCK & LIVE_k & DUTY & LIVE_u & PC_u)".
      rred2r. iMod (pc_drop _ 1 _ _ 100 with "PC_u") as "PC_u".
      auto. Unshelve. 2: auto.
      iPoseProof (pcs_cons_fold u 0 [] 1 _ with "[PC_u]") as "PCS".
      { simpl. iFrame. }
      iApply (wpsim_yieldR2 with "[DUTY PCS]").
      3:{ iSplitL "DUTY"; iFrame. }
      auto. lia.
      iIntros "DUTY _ PCS". iModIntro. rred2r.
      iEval (unfold counter; red_tl) in "CNT". iDestruct "CNT" as "[%x CNT]".
      iEval (red_tl) in "CNT". iDestruct "CNT" as "[%y CNT]".
      iEval (red_tl) in "CNT". iDestruct "CNT" as "(PT & CNTB_r1 & CNTB_r2)".
      iApply (SCMem_load_fun_spec with "[PT] [-]").
      3:{ iFrame. eauto. }
      auto. ss.
      iIntros (rv) "[%RV PT]". rred2r. iApply wpsim_tauR. rred2r.
      iApply (wpsim_yieldR2 with "[DUTY PCS]").
      3:{ iSplitL "DUTY"; done. }
      auto. lia.
      iIntros "DUTY _ PCS". iModIntro. rred2r. iApply wpsim_tauR. rred2r.
      (* Get numbers. *)
      iInv "PR" as "PRO" "PR_CLOSE". iEval (unfold t2_write; simpl; red_tl) in "PRO".
      iDestruct "PRO" as "[RES PTD]".
      iPoseProof (auexa_b_w_eq with "CNTB_r1 CNTW_r1") as "%EQ1". subst x.
      iPoseProof (auexa_b_w_eq with "CNTB_r2 RES") as "%EQ2". subst y.
      iMod ("PR_CLOSE" with "[PTD RES]") as "_".
      { unfold t2_write. simpl. red_tl. iFrame. }
      iMod (pcs_decr _ _ 1 1 _ with "PCS") as "[PCS _]". lia.
      iApply (Spinlock_unlock_spec with "[CNTB_r1 CNTB_r2 PT LOCK LIVE_k DUTY LIVE_u PCS PC_k]").
      3:{ repeat (try rewrite @red_tl_sepconj). simpl.
          iSplitR. rewrite red_syn_tgt_interp_as. eauto. iSplitR. eauto.
          unfold counter. red_tl. iSplitL "PT CNTB_r1 CNTB_r2".
          { iExists 100. red_tl. iExists 10. red_tl. iFrame. }
          simpl. iFrame. simpl. done.
      }
      1,2: ss.
      iEval red_tl. iIntros (_) "[DUTY LIVE_k]". rred2r.
      iApply (wpsim_sync with "[DUTY]").
      2:{ iFrame. }
      auto.
      iIntros "DUTY _". iModIntro. rred2r. iApply wpsim_tauR. rred2r. lred2r.
      subst rv. simpl.
      iApply wpsim_ret.
      2:{ iModIntro. iFrame. auto. }
      reflexivity.
    }
  Qed.

  Lemma Client03_thread2_spec
        tid N
    :
    ⊢ ⟦(∀ (r k w r1 r2 : τ{nat, 1+N}),
           ((syn_tgt_interp_as N sndl (fun m => (➢ (scm_memory_black m))))
               ∗ ○(tid)
               ∗ (⤉ Duty(tid) [(w, 0, t2_write_inv N r2)])
               ∗ (⤉ isSpinlock N r L (counter N 2 5 r1 r2) k 4 2)
               ∗ live[k] (1/2)
               ∗ ◇[k](3, 11)
               ∗ ➢(auexa_w r2 0)
               ∗ ◇[w](6, 31)
               ∗ live[w] (1/2)
               ∗ (⤉ t2_promise_inv N w r2)
            )
              -∗
              syn_wpsim (1+N) tid ∅
              (fun rs rt => (⤉(syn_term_cond N tid _ rs rt))%F)
              false false
              (fn2th Client03Spec.module "thread2" (tt ↑))
              (fn2th Client03.module "thread2" (tt ↑)))%F, 1+N⟧.
  Proof.
    iIntros. red_tl; iIntros (r). red_tl. iIntros (k). red_tl. iIntros (w). red_tl. iIntros (r1). red_tl. iIntros (r2).
    red_tl. rewrite red_syn_tgt_interp_as. unfold t2_promise_inv. rewrite red_syn_inv. rewrite red_syn_wpsim.
    simpl.
    iIntros "(#MEM & TID & DUTY & #ISL & LIVE_k & PC_k & CNTW_r2 & PC_w & LIVE_w & #UNTILI)".
    unfold fn2th. simpl. lred2r. rred2r.
    iMod (pcs_decr [(w, 0)] _ 30 1 with "[PC_w]") as "[PCS_w1 PCS_w2]".
    2:{ iApply pcs_cons_fold. iSplitL "PC_w". iFrame. ss. }
    auto.
    iMod (pcs_drop _ _ _ _ 1 100 with "PCS_w2") as "PCS_w2".
    lia. Unshelve. 2: lia.
    iApply (wpsim_yieldR2 with "[DUTY PCS_w2]").
    3:{ iSplitL "DUTY". iApply "DUTY". iFrame. }
    auto. lia.
    iIntros "DUTY _ PCS_w2". iEval (simpl) in "PCS_w2". iModIntro. rred2r.
    iApply wpsim_tauR. rred2r.
    assert (exists j, 0 = j). eauto. des.
    replace 
      (ITree.iter
         (λ i : nat,
             ` r0 : nat + () <- (if Nat.eq_dec i 10 then Ret (inr ()) else incr 5;;; trigger Yield;;; Ret (inl (i + 1)));; Ret r0)
         0)
      with
      (ITree.iter
         (λ i : nat,
             ` r0 : nat + () <- (if Nat.eq_dec i 10 then Ret (inr ()) else incr 5;;; trigger Yield;;; Ret (inl (i + 1)));; Ret r0)
         j).
    2:{ subst j. auto. }
    iEval (replace 50 with (5 * 10)).
    remember (10 - j) as J.
    assert (10 = J). subst. ss.
    iPoseProof (pc_split_le _ _ J 1 with "PC_k") as "[PC_k PC_k2]". subst; lia.
    iMod (pcs_decr _ _ (3*J) 0 with "PCS_w1") as "[PCS_w1 _]". subst; lia.
    iEval (rewrite H) in "CNTW_r2".
    assert (LT : j <= 10). subst. lia.
    clear H0 H.
    iStopProof.
    revert j HeqJ LT. induction J; cycle 1.
    { i. iIntros "((#MEM & #ISL & #UNTILI) & TID & LIVE_k & CNTW_r2 & LIVE_w & DUTY & PCS_w1 & PC_k & PC_k1 & PCS_w)".
      iPoseProof (pc_split_le _ _ 1 J with "PC_k") as "[PC_k0 PC_k]". lia.
      iMod (pcs_decr _ _ 3 (3*J) with "PCS_w") as "[PCS_w0 PCS_w]". lia.
      iMod (pcs_decr _ _ 2 1 with "PCS_w0") as "[PCS_w0 PCS_w2]". lia.
      iEval (rewrite unfold_iter_eq). rred2r.
      destruct (Nat.eq_dec j 10).
      { exfalso. lia. }
      rred2.
      iApply (Client03_incr_spec with "[DUTY PCS_w0 LIVE_k PC_k0 CNTW_r2] [-]").
      ss.
      { red_tl. simpl. iSplitR. rewrite red_syn_tgt_interp_as. eauto.
        iSplitL "DUTY". iFrame. iSplitL "PCS_w0". iFrame. iSplitR. eauto. iFrame.
        iSplit; eauto.
      }
      iEval red_tl. iIntros (_) "(DUTY & LIVE_k & CNTW_r1)". rred2r.
      iMod (pcs_drop _ _ _ _ 1 1 with "PCS_w2") as "PCS_w2". lia. Unshelve. 2: auto.
      iApply (wpsim_yieldR with "[DUTY PCS_w2]").
      2:{ iSplitL "DUTY". iApply "DUTY". iFrame. }
      auto.
      iIntros "DUTY _". iModIntro. rred2r. iApply wpsim_tauR. rred2r. iApply wpsim_tauR.
      specialize (IHJ (j+1)).
      iPoseProof (IHJ with "[-]") as "IH".
      { lia. }
      { lia. }
      { iSplit. iModIntro. eauto. iFrame. }
      iApply "IH".
    }
    i. iIntros "((#MEM & #ISL & #UNTILI) & TID & LIVE_k & CNTW_r2 & LIVE_w & DUTY & PCS_w & _ & PC_k & _)".
    iEval (rewrite unfold_iter_eq). rred2r. destruct (Nat.eq_dec j 10).
    2:{ exfalso. lia. }
    rred2r. iApply (wpsim_yieldR2 with "[DUTY PCS_w]").
    3:{ iSplitL "DUTY". iFrame. iFrame. }
    1,2: lia.
    iIntros "DUTY _ PCS_w". iEval (simpl) in "PCS_w". iModIntro. rred2r.
    iInv "UNTILI" as "UNTIL" "UNTIL_CLOSE". iEval (unfold t2_promise; simpl; red_tl) in "UNTIL".
    iEval (rewrite red_syn_until_tpromise) in "UNTIL". iDestruct "UNTIL" as "[#PR [L | D]]".
    2:{ iEval (unfold t2_write_inv; simpl; red_tl; simpl) in "D". iPoseProof "D" as "#[D WI]".
        iExFalso. iPoseProof (not_dead with "[LIVE_w]") as "%F". iFrame. auto. inv F.
    }
    iEval (simpl; red_tl; simpl) in "L". iDestruct "L" as "[LIVE_w2 PTD]".
    iApply (SCMem_store_fun_spec with "[PTD] [-]").
    3:{ iSplitR. auto. iFrame. }
    auto.
    { rewrite lookup_insert. assert (↑N_state_tgt ## (↑N_t2_promise_inv : coPset)).
      { apply ndot_preserve_disjoint_r. apply ndot_ne_disjoint. ss. }
      set_solver.
    }
    iIntros (rv) "PTD". destruct rv. rred2r. iApply wpsim_tauR. rred2r.
    iMod (kill with "[LIVE_w LIVE_w2]") as "#DEAD_w".
    { iEval (rewrite <- (Qp.div_2 1)). iApply live_merge. iFrame. }
    subst j. clear LT HeqJ.
    iMod (FUpd_alloc _ _ _ _ N_t2_write_inv ((➢(auexa_w r2 (10:nat)) ∗ (D ↦ 1))%F : Formula N) with "[CNTW_r2 PTD]") as "#DONE".
    2:{ simpl. red_tl. iFrame. }
    auto.
    iMod ("UNTIL_CLOSE" with "[]") as "_".
    { simpl. unfold t2_promise. rewrite red_syn_until_tpromise. iSplitR. auto.
      simpl; red_tl. simpl. iRight. iModIntro. auto.
    }
    iMod (duty_fulfill with "[DUTY]") as "DUTY".
    { iSplitL. iFrame. simpl. auto. }
    iApply (wpsim_yieldR with "[DUTY]"). 2: iFrame. auto. iIntros "DUTY _". iModIntro. rred2r.
    iApply wpsim_tauR. rred2r. iApply (Spinlock_lock_spec with "[LIVE_k DUTY] [-]").
    3:{ red_tl. iSplitR. rewrite red_syn_tgt_interp_as. auto. iSplitR. eauto.  iFrame. }
    1,2: ss.
    iEval (red_tl). iIntros (_) "[%u Q]". iEval (red_tl; simpl) in "Q".
    iDestruct "Q" as "(CNT & LOCK & LIVE_k & DUTY & LIVE_u & PC_u)". rred2r.
    iMod (pc_drop _ 1 _ _ 100 with "PC_u") as "PC_u". auto. Unshelve. 2: lia.
    iPoseProof (pcs_cons_fold _ 0 [] 1 with "[PC_u]") as "PCS".
    { iFrame. }
    iApply (wpsim_yieldR2 with "[DUTY PCS]").
    3:{ iSplitL "DUTY"; iFrame. }
    1,2: lia.
    iIntros "DUTY _ PCS". iEval (simpl) in "PCS". iModIntro. rred2r.
    iEval (unfold counter; red_tl) in "CNT". iDestruct "CNT" as "[%x CNT]".
    iEval (red_tl) in "CNT". iDestruct "CNT" as "[%y CNT]".
    iEval (red_tl) in "CNT". iDestruct "CNT" as "(PTC & CB_r1 & CB_r2)".
    iApply (SCMem_load_fun_spec with "[PTC] [-]").
    3:{ iSplitR. auto. iFrame. }
    1,2: ss.
    iIntros (rv) "[%RV PTC]". rred2r. iApply wpsim_tauR. rred2r.
    iApply (wpsim_yieldR2 with "[DUTY PCS]").
    3:{ iSplitL "DUTY"; iFrame. }
    1,2: lia.
    iIntros "DUTY _ PCS". iEval (simpl) in "PCS". iModIntro. rred2r. iApply wpsim_tauR. rred2r.
    (* Get the value of y. *)
    iInv "DONE" as "D" "D_CLOSE". iEval (simpl; red_tl; simpl) in "D". iDestruct "D" as "[W PT]".
    iPoseProof (auexa_b_w_eq with "CB_r2 W") as "%EQ".
    iMod ("D_CLOSE" with "[W PT]") as "_".
    { simpl. red_tl. iFrame. }
    iMod (pcs_decr _ _ 1 0 _ with "PCS") as "[PCS _]". lia.
    iApply (Spinlock_unlock_spec with "[CB_r1 CB_r2 PTC LOCK LIVE_k DUTY PCS LIVE_u PC_k] [-]").
    3:{ repeat (try rewrite @red_tl_sepconj). simpl.
        iSplitR. rewrite red_syn_tgt_interp_as. eauto. iSplitR. eauto.
        unfold counter. red_tl. iSplitL "PTC CB_r1 CB_r2".
        { iExists _. red_tl. iExists _. red_tl. iFrame. }
        simpl. iFrame. iFrame.
    }
    1,2: ss.
    iEval red_tl. iIntros (_) "[DUTY LIVE_k]". rred2r.
    iApply wpsim_yieldL. lred2r. iApply wpsim_chooseL. iExists x. lred2r.
    iApply (wpsim_sync with "[DUTY]").
    2:{ iFrame. }
    auto.
    iIntros "DUTY _". iModIntro. rred2r. iApply wpsim_tauR. rred2r. lred2r.
    subst y rv. iApply wpsim_ret.
    2:{ iModIntro. iFrame. ss. }
    reflexivity.
  Qed.

End SPEC.
