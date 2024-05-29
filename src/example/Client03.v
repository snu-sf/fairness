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

    Definition thread1 :
      ktree (threadE ident state) unit SCMem.val
      :=
      fun _ =>
        _ <- trigger Yield;;
        a <- Ret (0 : nat);;
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
                                else c <- (OMod.call (R:=SCMem.val) "load" C);; Ret (inr c));;
                           Ret r) tt);;
        _ <- trigger Yield;;
        Ret r.

    Definition thread2 :
      ktree (threadE ident state) unit SCMem.val
      :=
      fun _ =>
        _ <- trigger Yield;;
        a <- Ret (0 : nat);;
        _ <- (ITree.iter (fun (i : nat) =>
                           r <- (if (Nat.eq_dec i 10)
                                then Ret (inr tt)
                                else _ <- incr 5;; _ <- trigger Yield;; Ret (inl (i + 1)));;
                           Ret r) a);;
        _ <- (OMod.call (R:=unit) "store" (D, 1 : SCMem.val));;
        r <- (OMod.call (R:=SCMem.val) "load" C);;
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
  (* Notation tgt_ident := (void + SCMem.val)%type. *)

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

  Definition counter r1 r2 n : Formula n :=
    (∃ (x y : τ{nat}), (C ↦ ((2 * x) + (5 * y))) ∗ ➢(auexa_b r1 (x : nat)) ∗ ➢(auexa_b r2 (y : nat)))%F.

  Definition counter_inv r1 r2 n : Formula n :=
    (syn_inv n N_counter_inv (counter r1 r2 n)).

  Definition t2_write n : Formula n :=
    (D ↦ 1)%F.

  Definition t2_write_inv n : Formula n :=
    (syn_inv n N_t2_write_inv (t2_write n))%F.

  (** Simulation proof. *)

  Lemma Client03_thread1_spec
        tid
    :
    ⊢ ⟦(∀ (r k w r1 r2 : τ{nat, 2}),
           ((syn_tgt_interp_as 1 sndl (fun m => (➢ (scm_memory_black m))))
               ∗ ○(tid)
               ∗ (⤉ Duty(tid) [])
               ∗ (⤉ isSpinlock 1 r L emp%F k 4 2)
               ∗ live[k] (1/2)
               ∗ ◇[k](3, 100)
               ∗ (⤉ (counter_inv r1 r2 1))
               ∗ ➢(auexa_w r1 0)
               ∗ (⤉ ((D ↦ 0) -U-[w](0)-◇ (t2_write_inv 1)))
            )
              -∗
              syn_wpsim 2 tid ∅
              (fun rs rt => (⤉(syn_term_cond 1 tid _ rs rt))%F)
              false false
              (fn2th Client03Spec.module "thread1" (tt ↑))
              (fn2th Client03.module "thread1" (tt ↑)))%F, 2⟧.
  Proof.
    Local Opaque incr.
    iIntros. simpl. red_tl; iIntros (r). red_tl. iIntros (k). red_tl. iIntros (w). red_tl. iIntros (r1). red_tl. iIntros (r2).
    red_tl. simpl.
    rewrite red_syn_tgt_interp_as. rewrite red_syn_until_tpromise. rewrite red_syn_wpsim.
    unfold counter_inv. rewrite red_syn_inv.
    iIntros "(#MEM & TID & DUTY & #ISL & LIVE_k & PC_k & #CNT & CNTW_r1 & UNTIL)".
    unfold fn2th. simpl. lred2r. rred2r.
    iApply (wpsim_yieldR with "[DUTY]").
    2:{ iSplitL "DUTY". iApply "DUTY". simpl. ss. }
    auto.
    iIntros "DUTY FC". iModIntro. rred2r. iApply wpsim_tauR. rred2r.
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
    clear H0 H. iClear "FC".
    iRevert "MEM ISL CNT TID LIVE_k PC_k CNTW_r1 UNTIL DUTY". iStopProof.
    revert j HeqJ LT. induction J; cycle 1.
    { i. iIntros "_ #MEM #ISL #CNT TID LIVE_k PC_k CNTW_r1 UNTIL DUTY".
      iEval (rewrite unfold_iter_eq). rred2r.
      destruct (Nat.eq_dec j 100).
      { exfalso. lia. }
      rred2.

      TODO
      


    
    iEval (rewrite unfold_iter_eq). rred2r.
    iApply (SCMem_store_fun_spec _ _ tid n n with "[] [DUTY FC]").
    auto. admit. admit.
    iIntros (rv) "PT".
    rred2r. iApply wpsim_tauR. rred2r. iEval (rewrite unfold_iter_eq). rred2r.
    iApply (wpsim_yieldR with "[DUTY]"). 2: iFrame. auto.
    iIntros "DUTY _". iModIntro. rred2r. iApply wpsim_tauR. rred2r.
    iApply (Spinlock_lock_spec with "[DUTY PT FC] []").
    ss. ss.
    { red_tl. iFrame. instantiate (6:=⌜1 = 1⌝%F). admit. }
    iIntros (_). red_tl. iIntros "[%u S]". iEval (red_tl) in "S".

  Admitted.

End SPEC.
