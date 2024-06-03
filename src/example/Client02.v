From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Import pind Axioms ITreeLib Red TRed IRed2 WFLibLarge.
From Fairness Require Import FairBeh Mod Concurrency Linking.
From Fairness Require Import PCM IProp IPM IPropAux.
From Fairness Require Import IndexedInvariants OpticsInterp SimWeakest.
From Fairness Require Import TemporalLogic TemporalLogicFull SCMemSpec Spinlock.

Module Client02.

  Definition gvs : list nat := [2].
  Definition L : SCMem.val := SCMem.val_ptr (0, 0).
  Definition C : SCMem.val := SCMem.val_ptr (1, 0).

  Section CODE.

    Definition state := unit.
    Definition ident := void.

    Definition decr :
      itree (threadE ident state) SCMem.val
      :=
      a <- (ITree.iter (fun (_ : unit) =>
                         _ <- (trigger Yield;;; Spinlock.lock L);;
                         c <- (OMod.call (R:=SCMem.val) "load" C);;
                         b <- (OMod.call (R:=bool) "compare" (c, 0 : SCMem.val));;
                         _ <- (if (negb b)
                              then OMod.call "store" (C, SCMem.val_sub c 1)
                              else Ret tt);;
                         _ <- (trigger Yield;;; Spinlock.unlock L);;
                         if b then Ret (inr c) else Ret (inl tt))) tt;;
      Ret a.

    Definition thread1 :
      ktree (threadE ident state) unit SCMem.val
      :=
      fun _ =>
        _ <- (OMod.call (R:=unit) "store" (C, 100 : SCMem.val));;
        a <- decr;;
        _ <- trigger Yield;;
        Ret a.

    Definition thread2 :
      ktree (threadE ident state) unit SCMem.val
      :=
      fun _ =>
        a <- decr;;
        _ <- trigger Yield;;
        Ret a.

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

End Client02.

Module Client02Spec.

  Section SPEC.

    Definition state := unit.
    Definition ident := void.

    Definition thread1 :
      ktree (threadE ident state) unit SCMem.val
      :=
      fun _ =>
        _ <- trigger Yield;; Ret (0 : SCMem.val).

    Definition thread2:
      ktree (threadE void unit) unit SCMem.val
      :=
      fun _ =>
        _ <- trigger Yield;; Ret (0 : SCMem.val).

    Definition module : Mod.t :=
      Mod.mk
        tt
        (Mod.get_funs [("thread1", Mod.wrap_fun thread1);
                       ("thread2", Mod.wrap_fun thread2)])
    .

  End SPEC.

End Client02Spec.

Section SPEC.

  Import Client02.

  Notation src_state := (Mod.state Client02Spec.module).
  Notation src_ident := (Mod.ident Client02Spec.module).
  Notation tgt_state := (Mod.state Client02.module).
  Notation tgt_ident := (Mod.ident Client02.module).
  (* Notation tgt_ident := (void + SCMem.val)%type. *)

  Local Instance STT : StateTypes := Build_StateTypes src_state tgt_state src_ident tgt_ident.
  Context `{Σ : GRA.t}.
  Context {TLRAS : @TLRAs XAtom STT Σ}.
  Context {AUXRAS : AUXRAs Σ}.

  (** Invariants. *)

  (* Namespace for Client01 invariants. *)
  (* Definition N_Client02 : namespace := (nroot .@ "Client01"). *)
  (* Definition N_t1_write : namespace := (nroot .@ "t1_write"). *)

  (* Lemma mask_disjoint_client01 : ↑N_Client01 ## (↑N_t1_write : coPset). *)
  (* Proof. apply ndot_ne_disjoint. ss. Qed. *)

  (* Definition t1_write n : Formula n := *)
  (*   syn_inv n N_t1_write (X ↦ 1)%F. *)

  (* Global Instance t1_write_persistent n : Persistent (⟦t1_write n, n⟧). *)
  (* Proof. *)
  (*   unfold Persistent. iIntros "H". unfold t1_write. rewrite red_syn_inv. *)
  (*   iDestruct "H" as "#H". auto. *)
  (* Qed. *)

  (* Definition client01Inv k n : Formula n := *)
  (*   ((◆[k, 2] ∗ -[k](0)-◇ t1_write n) *)
  (*     ∗ *)
  (*     ((live[k] (1/2) ∗ (X ↦ 0)) *)
  (*      ∨ *)
  (*        (t1_write n)) *)
  (*   )%F. *)

  (** Simulation proof. *)

  Lemma Client02_thread1_spec
        tid n
    :
    ⊢ ⟦((TID(tid) ∗ (⤉ Duty(tid) []))
             -∗
             syn_wpsim (S n) tid ∅
             (fun rs rt => (⤉(syn_term_cond n tid _ rs rt))%F)
             false false
             (fn2th Client02Spec.module "thread1" (tt ↑))
             (fn2th Client02.module "thread1" (tt ↑)))%F, 1+n⟧.
  Proof.
    iIntros. red_tl. simpl. iEval (rewrite red_syn_wpsim).
    iIntros "(TID & DUTY)".
    unfold fn2th. simpl. lred2r. rred2r.
    iApply (wpsim_yieldR with "[DUTY]"). 2: iFrame. auto.
    iIntros "DUTY FC". iModIntro. rred2r.
    iApply (SCMem_store_fun_spec _ _ tid n n with "[] [DUTY FC]").
    auto. admit. admit.
    iIntros (rv) "PT".
    rred2r. iApply wpsim_tauR. rred2r. iEval (rewrite unfold_iter_eq). rred2r.
    iApply (wpsim_yieldR with "[DUTY]"). 2: iFrame. auto.
    iIntros "DUTY _". iModIntro. rred2r. iApply wpsim_tauR. rred2r.

  Admitted.

End SPEC.
