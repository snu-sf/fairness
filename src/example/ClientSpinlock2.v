From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Import pind Axioms ITreeLib Red TRed IRed2 WFLibLarge.
From Fairness Require Import FairBeh Mod Linking.
From Fairness Require Import Spinlock.
From Fairness Require Import PCM IProp IPM IPropAux.
From Fairness Require Import IndexedInvariants OpticsInterp SimWeakest.
From Fairness Require Import TemporalLogic SCMemSpec SpinlockSpec.
From Fairness Require Import AuthExclsRA ExclsRA OneShotsRA.

Module ClientSpinlock2.

  Definition gvs : list nat := [2].
  Definition X : SCMem.val := SCMem.val_ptr (0, 0).
  Definition D : SCMem.val := SCMem.val_ptr (1, 0).

  Section CODE.

    Definition state := unit.
    Definition ident := void.

    Definition thread1 :
      ktree (threadE ident state) unit SCMem.val
      :=
      fun _ =>
        _ <- (trigger Yield;;; Spinlock.lock X);;
        _ <- (OMod.call (R:=unit) "store" (D, SCMem.val_nat 1));;
        _ <- trigger Yield;;
        Ret (SCMem.val_nat 0).

    Definition thread2 :
      ktree (threadE ident state) unit SCMem.val
      :=
      fun _ =>
        _ <- trigger Yield;;
        _ <- (ITree.iter (fun _ =>
                           d <- (OMod.call (R:=SCMem.val) "load" D);;
                           b <- (OMod.call (R:=bool) "compare" (d, 1 : SCMem.val));;
                           r <- (if b
                                then Ret (inr tt)
                                else Ret (inl tt));;
                           Ret r) tt);;
        _ <- (trigger Yield;;; Spinlock.unlock X);;
        Ret (SCMem.val_nat 0).

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

End ClientSpinlock2.

Module ClientSpinlock2Spec.

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

End ClientSpinlock2Spec.

Section SIM.

  Notation src_state := (Mod.state ClientSpinlock2Spec.module).
  Notation src_ident := (Mod.ident ClientSpinlock2Spec.module).
  Notation tgt_state := (Mod.state ClientSpinlock2.module).
  Notation tgt_ident := (Mod.ident ClientSpinlock2.module).

  Local Instance STT : StateTypes := Build_StateTypes src_state tgt_state src_ident tgt_ident.
  Context `{sub : @SRA.subG Γ Σ}.
  Context {TLRASs : TLRAs_small STT Γ}.
  Context {TLRAS : TLRAs STT Γ Σ}.

  Context {HasMEMRA: @GRA.inG memRA Γ}.
  Context {HasAuthExcls : @GRA.inG (AuthExcls.t nat) Γ}.
  Context {HasExcls : @GRA.inG (Excls.t unit) Γ}.

  Context {HasOneShots : @GRA.inG (OneShots.t nat) Γ}.
  Context {HasOneShots2 : @GRA.inG (OneShots.t unit) Γ}.

  Ltac red_tl_all := red_tl; red_tl_memra; red_tl_authexcls; red_tl_excls; red_tl_oneshots.

  Import ClientSpinlock2.

  (** Invariants. *)

  Definition N_ClientSpinlock2 : namespace := (nroot .@ "ClientSpinlock2").

  Lemma md_N_ClientSpinlock2_state_tgt : (↑N_ClientSpinlock2 : coPset) ## (↑N_state_tgt : coPset).
  Proof. apply ndot_ne_disjoint. ss. Qed.

  Lemma md_N_ClientSpinlock2_Spinlock : (↑N_ClientSpinlock2 : coPset) ## (↑N_Spinlock : coPset).
  Proof. apply ndot_ne_disjoint. ss. Qed.

  Definition ClientSpinlock2_inv n (tid2 : thread_id) (γX γe κs : nat) (κl γκl : nat) (γr : nat) : sProp n :=
    (
      ((○ γX 0) ∗ (D ↦ 0)
                ∗ (-[κl](0)-◇ (∃ (γκw : τ{nat}), ▿ γκl γκw)) ∗ (△ γκl (1/2))
                ∗ (Duty(tid2) [])
      )
      ∨
        ((○ γX 1) ∗ (D ↦ 0)
                  ∗ (∃ (κw γκw : τ{nat}),
                        (-[κw](0)-◇ (∃ (γκu : τ{nat}), ▿ γκw γκu))
                          ∗ (△ γκw (1/2)) ∗ (κw -(0)-◇ κs) ∗ (▿ γκl γκw)
                          ∗ (Duty(tid2) []))
        )
      ∨
        ((○ γX 1) ∗ (D ↦ 1)
                  ∗ (∃ (κw γκw κu γκu : τ{nat}),
                        (-[κu](0)-◇ (▿ γκu tt))
                          ∗ (△ γκu (1/2)) ∗ (κu -(0)-◇ κs) ∗ (▿ γκl γκw) ∗ (▿ γκw γκu)
                          ∗ ((Duty(tid2) [(κu, 0, (▿ γκu tt))] ∗ (EX γe tt)) ∨ (▿ γr tt)))
        )
      ∨
        ((○ γX 0) ∗ (D ↦ 1)
                  ∗ (∃ (κw γκw κu γκu : τ{nat}),
                        (▿ γκl γκw) ∗ (▿ γκw γκu) ∗ (▿ γr tt) ∗ (▿ γκu tt)))
    )%S.


  Lemma ClientSpinlock2_thread1_sim
        tid n
    :
    ⊢ ⟦(∀ (γk k : τ{nat, 1+n}),
           ((⤉ syn_inv n N_Client01 (client01Inv γk k n))
              ∗ (syn_tgt_interp_as n sndl (fun m => (s_memory_black m)))
              ∗ (isSpinlock n X γX γe κs L)
              ∗ TID(tid)
              ∗ (⤉ Duty(tid) [(κl, 0, (∃ κw, (▿ γκl κw)))])
              ∗ ◇[k](2, 1) ∗ ⤉(live γk (k : nat) (1/2)))
             -∗
             syn_wpsim (S n) tid ⊤
             (fun rs rt => (⤉(syn_term_cond n tid _ rs rt))%S)
             false false
             (fn2th ClientSpinlock2Spec.module "thread1" (tt ↑))
             (fn2th ClientSpinlock2.module "thread1" (tt ↑)))%S, 1+n⟧.
  Proof.
    iIntros. red_tl_all. iIntros (γk). red_tl_all. iIntros (k). red_tl_all. simpl.
    iEval (rewrite red_syn_inv; rewrite red_syn_wpsim; rewrite red_syn_tgt_interp_as).

    iIntros "(#INV & #MEM & THDW & DUTY & PCk & LIVE)".

    unfold fn2th. simpl. unfold thread1, Client01Spec.thread1.
    rred2r. lred2r.


End SIM.

