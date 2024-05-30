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
        (* a <- Ret (0 : nat);; *)
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
        (* a <- Ret (0 : nat);; *)
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
  Definition N_counter_inv : namespace := (N_Client03 .@ "counter").
  Definition N_t2_write_inv : namespace := (N_Client03 .@ "t2_write").

  Definition counter n c1 c2 r1 r2 : Formula n :=
    (∃ (x y : τ{nat}), (C ↦ ((c1 * x) + (c2 * y))) ∗ ➢(auexa_b r1 (x : nat)) ∗ ➢(auexa_b r2 (y : nat)))%F.

  (* Definition counter_inv n r1 r2 : Formula n := *)
  (*   (syn_inv n N_counter_inv (counter n r1 r2)). *)

  Definition t2_write n r : Formula n :=
    (➢(auexa_w r (10 : nat)) ∗ (D ↦ 1))%F.

  Definition t2_write_inv n r : Formula n :=
    (syn_inv n N_t2_write_inv (t2_write n r))%F.

  (** Simulation proof. *)

  Lemma Client03_incr_spec
        tid N Es c1 c2
        (TOP : OwnEs_top Es)
    :
    ⊢ ∀ (r k lft l r1 r2 a : τ{nat, 1+N}) (ds : list (nat * nat * Formula N)),
        [@ tid, N, Es @]
          ⧼⟦((syn_tgt_interp_as N sndl (λ m : SCMem.t, ➢(scm_memory_black m)))
               ∗ (⤉ Duty(tid) ds) ∗ ◇{List.map fst ds}(lft, 1) ∗ ◇{List.map fst ds}(0, 1)
               ∗ ◇{List.map fst ds}(0, 5)
               ∗ (⤉ isSpinlock N r L (counter N c1 c2 r1 r2) k lft l)
               ∗ (⌜2 <= l⌝) ∗ live[k] (1/2) ∗ ◇[k](1+l, 1)
               ∗ ➢(auexa_w r1 (a : nat)))%F , 1+N⟧⧽
            (OMod.close_itree omod (SCMem.mod gvs) (incr c1))
            ⧼rv, ⟦((⤉ Duty(tid) ds) ∗ live[k] (1/2) ∗  ➢(auexa_w r1 (a + 1)))%F, 1+N⟧⧽
  .
  Proof.
    iIntros. simpl. iStartTriple.
    red_tl. simpl. rewrite red_syn_tgt_interp_as.
    iIntros "(#MEM & DUTY & PCS_SPIN1 & PCS_SPIN2 & PCS & #ISL & %LE & LIVE_k & PC_k & CNTW_r1)".
    iIntros "POST".
    unfold incr. rred.
    iMod (pcs_decr _ _ 4 1 with "PCS") as "[PCS PCS1]". auto.
    iApply (wpsim_yieldR with "[DUTY PCS1]").
    2:{ iFrame. }
    auto.
    iIntros "DUTY _". iModIntro. rred2r. iApply wpsim_tauR. rred2r.
    iApply (Spinlock_lock_spec with "[LIVE_k DUTY PCS_SPIN1 PCS_SPIN2] [PCS PC_k CNTW_r1 POST]").
    1,2: ss.
    { red_tl. simpl. rewrite red_syn_tgt_interp_as. iSplit. eauto. iSplitR. eauto. iFrame. }
    iEval (red_tl). iIntros (_) "[%u A]". iEval (unfold counter; red_tl) in "A".
    iDestruct "A" as "([%x A] & LOCKED & LIVE_k & DUTY & LIVE_u & PC_u)". iEval (red_tl) in "A".
    iDestruct "A" as "[%y A]". iEval (red_tl) in "A". iDestruct "A" as "(PT & CNTB_r1 & CNTB_r2)".
    rred2r. iMod (pc_drop _ 1 _ _ 100 with "PC_u") as "PC_u". lia.
    Unshelve. 2: lia.
    iPoseProof (pc_split with "[PC_u]") as "[PC_u PC_u_pay]".
    { iEval (replace 100 with (99 + 1)) in "PC_u". iFrame. }
    iMod (pcs_decr _ _ 3 1 with "PCS") as "[PCS PCS1]". auto.
    iApply (wpsim_yieldR with "[DUTY PC_u_pay PCS1]").
    2:{ iSplitL "DUTY". iFrame. simpl. iApply pcs_cons_fold. iFrame. }
    auto.
    iIntros "DUTY _". iModIntro. rred2r.
    iApply (SCMem_load_fun_spec with "[PT]").
    3:{ iFrame. eauto. }
    auto. ss.
    iIntros (rv) "[%RV PT]". rred2r. iApply wpsim_tauR. rred2r.
    iPoseProof (pc_split with "[PC_u]") as "[PC_u PC_u_pay]".
    { iEval (replace 99 with (98 + 1)) in "PC_u". iFrame. }
    iMod (pcs_decr _ _ 2 1 with "PCS") as "[PCS PCS1]". auto.
    iApply (wpsim_yieldR with "[DUTY PC_u_pay PCS1]").
    2:{ iSplitL "DUTY". iFrame. simpl. iApply pcs_cons_fold. iFrame. }
    auto.
    iIntros "DUTY _". iModIntro. rred2r.
    iApply (SCMem_store_fun_spec with "[PT]").
    3:{ iFrame. eauto. }
    auto. ss.
    iIntros (rv0) "PT". rred2r. iApply wpsim_tauR. rred2r.
    iPoseProof (pc_split with "[PC_u]") as "[PC_u PC_u_pay]".
    { iEval (replace 98 with (97 + 1)) in "PC_u". iFrame. }
    iMod (pcs_decr _ _ 1 1 with "PCS") as "[PCS PCS1]". auto.
    iApply (wpsim_yieldR with "[DUTY PC_u_pay PCS1]").
    2:{ iSplitL "DUTY". iFrame. simpl. iApply pcs_cons_fold. iFrame. }
    auto.
    iIntros "DUTY _". iModIntro. rred2r. iApply wpsim_tauR. rred2r.
    replace (SCMem.val_add rv c1) with ((c1 * (1 + x) + c2 * y) : SCMem.val).
    2:{ subst rv. ss. f_equal. lia. }
    iPoseProof (auexa_b_w_eq with "CNTB_r1 CNTW_r1") as "%EQ". subst a.
    iMod (auexa_b_w_update _ _ _ _ nat (1 + x) with "CNTB_r1 CNTW_r1") as "[CNTB_r1 CNTW_r1]".
    iApply (Spinlock_unlock_spec with "[CNTB_r1 CNTB_r2 PT LOCKED LIVE_k DUTY PCS LIVE_u PC_u PC_k]").
    3:{ repeat (try rewrite @red_tl_sepconj). simpl.
        iSplitR. rewrite red_syn_tgt_interp_as. eauto. iSplitR. eauto.
        unfold counter. red_tl. iSplitL "PT CNTB_r1 CNTB_r2".
        { iExists (1+x). red_tl. iExists y. red_tl. iFrame. }
        Local Opaque progress_credits.
        simpl. iEval (replace (l+1) with (S l) by lia). iFrame.
        iApply pcs_cons_fold.
        iPoseProof (pc_split with "[PC_u]") as "[PC1 PC2]". 2: iFrame.
        simpl. replace 97 with (96 + 1) by ss. iFrame.
        Local Transparent progress_credits.
    }
    ss. ss.
    iEval red_tl. iIntros (_) "[DUTY LIVE_k]". rred2r.
    iApply "POST". replace (1+x) with (x+1). iFrame. lia.
  Qed.

  Local Opaque incr.

  Lemma Client03_thread1_spec
        tid N
    :
    ⊢ ⟦(∀ (r k w r1 r2 : τ{nat, 1+N}),
           ((syn_tgt_interp_as N sndl (fun m => (➢ (scm_memory_black m))))
               ∗ ○(tid)
               ∗ (⤉ Duty(tid) [])
               ∗ (⤉ isSpinlock N r L (counter N 2 5 r1 r2) k 4 2)
               ∗ live[k] (1/2)
               ∗ ◇[k](3, 101)
               ∗ ➢(auexa_w r1 0)
               ∗ (⤉ ((D ↦ 0) -U-[w](0)-◇ (t2_write_inv N r2)))
            )
              -∗
              syn_wpsim (1+N) tid ∅
              (fun rs rt => (⤉(syn_term_cond N tid _ rs rt))%F)
              false false
              (fn2th Client03Spec.module "thread1" (tt ↑))
              (fn2th Client03.module "thread1" (tt ↑)))%F, 1+N⟧.
  Proof.
    iIntros. simpl. red_tl; iIntros (r). red_tl. iIntros (k). red_tl. iIntros (w). red_tl. iIntros (r1). red_tl. iIntros (r2).
    red_tl. simpl.
    rewrite red_syn_tgt_interp_as. rewrite red_syn_until_tpromise. rewrite red_syn_wpsim.
    iIntros "(#MEM & TID & DUTY & #ISL & LIVE_k & PC_k & CNTW_r1 & UNTIL)".
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
    iRevert "MEM ISL TID LIVE_k PC_k CNTW_r1 UNTIL DUTY". iStopProof.
    revert j HeqJ LT. induction J; cycle 1.
    { i. iIntros "_ #MEM #ISL TID LIVE_k PC_k CNTW_r1 UNTIL DUTY".
      iEval (rewrite unfold_iter_eq). rred2r.
      destruct (Nat.eq_dec j 100).
      { exfalso. lia. }
      rred2.
      iPoseProof (pc_split _ _ 1 (S J) with "PC_k") as "[PC_k1 PC_k]".
      iApply (Client03_incr_spec with "[DUTY LIVE_k PC_k1 CNTW_r1] [TID UNTIL PC_k]").
      ss.
      { red_tl. simpl. iSplitR. rewrite red_syn_tgt_interp_as. eauto. iFrame.
        simpl. do 3 (iSplitR; [iApply pcs_nil |]). iSplit. eauto. auto.
      }
      iEval red_tl. iIntros (_) "(DUTY & LIVE_k & CNTW_r1)". rred2r.
      iApply (wpsim_yieldR with "[DUTY]").
      2:{ iSplitL "DUTY". iApply "DUTY". simpl. ss. }
      auto.
      iIntros "DUTY _". iModIntro. rred2r. iApply wpsim_tauR. rred2r.
      iApply wpsim_tauR.
      specialize (IHJ (j+1)).
      iPoseProof (IHJ with "[] MEM ISL TID LIVE_k PC_k CNTW_r1 UNTIL DUTY") as "IH".
      { lia. }
      { lia. }
      { auto. }
      iApply "IH".
    }
    { i. iIntros "_ #MEM #ISL TID LIVE_k PC_k CNTW_r1 UNTIL DUTY".
      iEval (rewrite unfold_iter_eq). rred2r.
      destruct (Nat.eq_dec j 100).
      2:{ exfalso. lia. }
      rred2.

      TODO
      


    

  Admitted.

End SPEC.
