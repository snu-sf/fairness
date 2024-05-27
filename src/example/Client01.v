From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Import pind Axioms ITreeLib Red TRed IRed2 WFLibLarge.
From Fairness Require Import FairBeh Mod Concurrency Linking.
From Fairness Require Import PCM IProp IPM IPropAux.
From Fairness Require Import IndexedInvariants OpticsInterp SimWeakest.
From Fairness Require Import TemporalLogic TemporalLogicFull SCMemSpec.

Module Client01.

  Definition gvs : list nat := [1].
  Definition X := SCMem.val_ptr (0, 0).

  Section CODE.

    Notation state := unit.
    Notation ident := void.

    Definition thread1 :
      ktree (threadE ident state) unit SCMem.val
      :=
      fun _ =>
        `_ : unit <- (OMod.call "store" (X, 1));;
        _ <- trigger Yield;;
        Ret (0 : SCMem.val).

    Definition thread2 :
      ktree (threadE ident state) unit SCMem.val
      :=
      fun _ =>
        _ <- trigger Yield;;
        a <- (ITree.iter (fun (_ : unit) =>
                           `a : SCMem.val <- (OMod.call "load" X);;
                                `b : bool <- (OMod.call "compare" (a, 0));;
                                     if b then Ret (inl tt) else Ret (inr a))) tt;;
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

End Client01.

Module Client01Spec.

  Section SPEC.

    Notation state := unit.
    Notation ident := void.

    Definition thread1 :
      ktree (threadE ident state) unit SCMem.val
      :=
      fun _ =>
        _ <- trigger Yield;; Ret (0 : SCMem.val).

    Definition thread2:
      ktree (threadE void unit) unit SCMem.val
      :=
      fun _ =>
        _ <- trigger Yield;; Ret (1 : SCMem.val).

    Definition module : Mod.t :=
      Mod.mk
        tt
        (Mod.get_funs [("thread1", Mod.wrap_fun thread1);
                       ("thread2", Mod.wrap_fun thread2)])
    .

  End SPEC.

End Client01Spec.

Section SPEC.

  Import Client01.

  Notation src_state := (Mod.state Client01Spec.module).
  Notation src_ident := (Mod.ident Client01Spec.module).
  Notation tgt_state := (Mod.state Client01.module).
  Notation tgt_ident := (Mod.ident Client01.module).

  Local Instance STT : StateTypes := Build_StateTypes src_state tgt_state src_ident tgt_ident.
  Context `{Σ : GRA.t}.
  Context {TLRAS : @TLRAs XAtom STT Σ}.
  Context {AUXRAS : AUXRAs Σ}.

  (** Invariants. *)

  (* Namespace for Client01 invariants. *)
  Definition N_Client01 : namespace := (nroot .@ "Client01").
  Definition N_t1_write : namespace := (nroot .@ "t1_write").

  Lemma mask_disjoint_client01 : ↑N_Client01 ## (↑N_t1_write : coPset).
  Proof. apply ndot_ne_disjoint. ss. Qed.

  Definition t1_write n : Formula n :=
    syn_inv n N_t1_write (X ↦ 1)%F.

  Global Instance t1_write_persistent n : Persistent (⟦t1_write n, n⟧).
  Proof.
    unfold Persistent. iIntros "H". unfold t1_write. rewrite red_syn_inv.
    iDestruct "H" as "#H". auto.
  Qed.

  Definition client01Inv k n : Formula n :=
    ((◆[k, 2] ∗ -[k](0)-◇ t1_write n)
      ∗
      ((live[k] (1/2) ∗ (X ↦ 0))
       ∨
         (t1_write n))
    )%F.

  (* Simulation proof. *)

  Lemma Client01_thread1_spec
        tid n
    :
    ⊢ ⟦(∀ (k : τ{nat, 1+n}),
           ((⤉ syn_inv n N_Client01 (client01Inv k n))
              ∗ ○(tid) ∗ (⤉ Duty(tid) [(k, 0, t1_write n)]) ∗ ◇[k](1, 1) ∗ live[k] (1/2))
             -∗
             syn_wpsim (S n) tid ∅
             (fun rs rt => ((⤉ syn_term n tid rs rt))%F : Formula (S n))
             false false
             (fn2th Client01Spec.module "thread1" (tt ↑))
             (fn2th Client01.module "thread1" (tt ↑)))%F, 1+n⟧.
  Proof.
    iIntros. red_tl. iIntros (k). red_tl. simpl.
    iEval (rewrite red_syn_inv; rewrite red_syn_wpsim).
    iIntros "(#INV & THDW & DUTY & PCk)".

  Admitted.

End SPEC.
