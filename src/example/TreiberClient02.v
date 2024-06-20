From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Import pind Axioms ITreeLib Red TRed IRed2 WFLibLarge.
From Fairness Require Import FairBeh Mod Concurrency Linking.
From Fairness Require Import PCM IProp IPM IPropAux.
From Fairness Require Import IndexedInvariants OpticsInterp SimWeakest.
From Fairness Require Import TemporalLogic SCMemSpec ExclsRA AuthExclsRA LifetimeRA ghost_map TreiberStack TreiberStackSpec.

Module TreiberClient2.

  Definition gvs : list nat := [1].
  Definition s : SCMem.val := SCMem.val_ptr (0, 0).

  Section CODE.

    Definition state := unit.
    Definition ident := void.

    Definition thread_push :
      ktree (threadE ident state) unit unit
      := fun _ =>
      _ <- (trigger Yield;;; TreiberStack.push (s,SCMem.val_nat 1));;
      _ <- trigger Yield;;
      Ret tt.

    Definition thread_pop :
      ktree (threadE ident state) unit (SCMem.val)
      := fun _ =>
      _ <- trigger Yield;;
      v <- ITree.iter
        (fun _ =>
          ov <- (trigger Yield;;; TreiberStack.pop s);;
          if ov is Some v then Ret (inr v) else Ret (inl tt)
        ) tt;;
        _ <- trigger Yield;;
        Ret v.

    Definition omod : Mod.t :=
      Mod.mk
        tt
        (Mod.get_funs [("thread_push", Mod.wrap_fun thread_push);
                       ("thread_pop", Mod.wrap_fun thread_pop)])
    .

    Definition module : Mod.t :=
      OMod.close
        (omod)
        (SCMem.mod gvs)
    .

  End CODE.

End TreiberClient2.

Module TreiberClient2Spec.

  Section SPEC.

    Notation state := unit.
    Notation ident := void.

    Definition thread_push :
      ktree (threadE ident state) unit unit
      :=
      fun _ =>
        _ <- trigger Yield;; Ret tt.

    Definition thread_pop:
      ktree (threadE void unit) unit SCMem.val
      :=
      fun _ =>
        _ <- trigger Yield;; Ret (1 : SCMem.val).

    Definition module : Mod.t :=
      Mod.mk
        tt
        (Mod.get_funs [("thread_push", Mod.wrap_fun thread_push);
                       ("thread_pop", Mod.wrap_fun thread_pop)])
    .

  End SPEC.

End TreiberClient2Spec.

Section SPEC.

  Notation src_state := (Mod.state TreiberClient2Spec.module).
  Notation src_ident := (Mod.ident TreiberClient2Spec.module).
  Notation tgt_state := (Mod.state TreiberClient2.module).
  Notation tgt_ident := (Mod.ident TreiberClient2.module).

  Local Instance STT : StateTypes := Build_StateTypes src_state tgt_state src_ident tgt_ident.
  Context `{sub : @SRA.subG Γ Σ}.
  Context {TLRASs : TLRAs_small STT Γ}.
  Context {TLRAS : TLRAs STT Γ Σ}.

  Context {HasMemRA: @GRA.inG memRA Γ}.
  Context {HasAuthExclsRAlist : @GRA.inG (AuthExcls.t (list SCMem.val)) Γ}.
  Context {HasAuthExclsRAunit : @GRA.inG (AuthExcls.t unit) Γ}.
  Context {HasGhostMap : @GRA.inG (ghost_mapURA nat maybe_null_ptr) Γ}.
  Context {HasExcl : @GRA.inG (Excls.t unit) Γ}.
  Context {HasLifetime : @GRA.inG Lifetime.t Γ}.

  Ltac red_tl_all := red_tl; red_tl_memra; red_tl_authexcls; red_tl_lifetime.

  Import TreiberClient2.

  (** Invariants. *)

  (* Namespace for TreiberClient2 invariants. *)
  Definition nTCli : namespace := (nroot .@"TCli").
  Definition nTpush : namespace := (nroot .@"Tpush").
  Definition nTMod : namespace := (nroot .@"TMod").

  Definition push_then_pop n γs γpop : sProp n :=
    (○ γs [(1 : SCMem.val)] ∨ ○ γpop tt)%S.

  Definition push_then_pop_inv n γs γpop : sProp n :=
    (syn_inv n nTpush (push_then_pop n γs γpop))%S.

  Definition Client2StackState n γk k γs γpop : sProp n :=
    (◆[k,2] ∗
    ((live γk k (1/2) ∗ ○ γs ([] : list SCMem.val)) -U-[k](0)-◇ (dead γk k ∗ push_then_pop_inv n γs γpop))
    )%S.

  Definition C2Inv n γk k γs γpop : sProp n :=
    (syn_inv n nTCli (Client2StackState n γk k γs γpop))%S.

  Global Instance C2Inv_persistent n γk k γs γpop : Persistent ⟦C2Inv n γk k γs γpop, n⟧.
  Proof.
    unfold Persistent. iIntros "H". unfold C2Inv. rewrite red_syn_inv.
    iDestruct "H" as "#H". auto.
  Qed.

  (** Simulation proof. *)

  Lemma TreiberClient2_push_spec tid n :
    ⊢ ⟦(∀ (γk k' k γs γpop : τ{nat, 1+n}),
      ((syn_tgt_interp_as n sndl (fun m => s_memory_black m)) ∗
      (⤉ IsT nTMod n s k' γs) ∗
      (⤉ C2Inv n γk k γs γpop) ∗
      TID(tid) ∗
      ◇[k'](1, 1) ∗
      (⤉ Duty(tid) [(k, 0, dead γk (k : nat) ∗ push_then_pop_inv n γs γpop)]) ∗
      ◇[k](3, 1) ∗ ⤉(live γk (k : nat) (1/2)))
      -∗
      syn_wpsim (1+n) tid ⊤
      (fun rs rt => (⤉(syn_term_cond n tid _ rs rt))%S)
      false false
      (fn2th TreiberClient2Spec.module "thread_push" (tt ↑))
      (fn2th TreiberClient2.module "thread_push" (tt ↑))
    )%S,1+n⟧.
  Proof.
    iIntros.
    red_tl_all; iIntros (γk); red_tl_all; iIntros (k'); red_tl_all; iIntros (k); red_tl_all; iIntros (γs); red_tl_all; iIntros (γpop).

    red_tl_all. unfold C2Inv. simpl.

    iEval (rewrite red_syn_inv; rewrite red_syn_wpsim; rewrite red_syn_tgt_interp_as).

    iIntros "(#Mem & #IsTreiber & #C2Inv & TID & Pck & Duty & Pc & Live)".

    unfold fn2th. simpl. unfold thread_push, TreiberClient2Spec.thread_push.
    rred2r. lred2r.

    iMod (pc_drop _ 2 _ _ 3 with "Pc") as "Pc"; [lia|].
    iDestruct (pc_split _ _ 1 2 with "Pc") as "[PcS Pc]".
    iMod (pc_drop _ 1 _ _ 3 with "Pc") as "Pc"; [lia|].
    iDestruct (pc_split _ _ 1 2 with "Pc") as "[PcY Pc]".
    iApply (wpsim_yieldR with "[$Duty PcY]"); [lia| |].
    { simpl. iDestruct (pcs_cons_fold with "[PcY]") as "$". iFrame. }
    Unshelve. 2,3:lia.

    iIntros "Duty C". rred2r. iApply wpsim_tauR. rred2r.
    iDestruct (pc_split _ _ 1 1 with "Pc") as "[Pc Pc']".

    iApply (Treiber_push_spec nTMod (λ v, (dead γk (k : nat)) ∗ syn_inv n nTpush (push_then_pop n γs γpop))%S with "[Duty Pck PcS Live] [-]"); [|].
    { red_tl_all. rewrite red_syn_tgt_interp_as. iSplit; [eauto|]. iSplitR; [iFrame "#"|]. simpl.
      iFrame. simpl.
      iDestruct (pcs_cons_fold with "[PcS]") as "$".
      { simpl. iFrame. }
      iIntros (s_st). red_tl_all. iIntros "[TStackInv _]".
      rewrite red_syn_fupd. red_tl_all.
      iInv "C2Inv" as "Client2" "CloseC2Inv".
      iEval (unfold Client2StackState; simpl; red_tl_all; simpl; rewrite red_syn_until_tpromise) in "Client2".
      iDestruct "Client2" as "[#OBL PushProm]".

      iEval (unfold until_thread_promise; red_tl_all; simpl) in "PushProm".

      iDestruct "PushProm" as "[#Prm [Bf | #Af]]"; simpl.
      - iEval (red_tl_all; simpl) in "Bf". iDestruct "Bf" as "[LiveInv TStackC]".
        iDestruct (AuthExcls.b_w_eq with "TStackInv TStackC") as "%EQ".
        subst s_st.
        iMod (AuthExcls.b_w_update with "TStackInv TStackC") as "[TStackInv TStackC]".
        iMod ((FUpd_alloc _ _ _ n (nTpush) (push_then_pop n γs γpop : sProp n)%S) with "[TStackC]") as "#Pushed"; [lia| |].
        { unfold push_then_pop. iEval (simpl; red_tl_all; simpl). auto. }
        iDestruct (Lifetime.pending_merge with "Live LiveInv") as "Live".
        iEval (rewrite Qp.half_half) in "Live".
        iMod (Lifetime.pending_shot with "Live") as "#Dead".
        iMod ("CloseC2Inv" with "[]") as "_".
        { iEval (unfold Client2StackState; simpl; red_tl_all; simpl).
          iFrame "#". iEval (rewrite red_syn_until_tpromise).
          iApply until_tpromise_make2. simpl. iSplit; auto.
          iEval (red_tl_all; simpl). iModIntro; iSplit; auto.
        }
        iModIntro. iFrame "∗#".
      - iEval (red_tl_all; simpl) in "Af". iDestruct "Af" as "[Dead TStackC]".
        by iDestruct (Lifetime.pending_not_shot with "Live Dead") as "%False".
    }
    Unshelve.
    2:{ apply ndot_ne_disjoint. ss. }

    iIntros (_). red_tl_all. iIntros "[[#Dead Pushed] Duty]".
    iEval (rewrite red_syn_inv) in "Pushed". iDestruct "Pushed" as "#Pushed".
    iMod (duty_fulfill with "[Dead Duty]") as "Duty".
    { iFrame. simpl. unfold push_then_pop_inv. red_tl_all. rewrite red_syn_inv. auto. }

    rred2r.
    iApply (wpsim_sync with "[$Duty Pc]"); [lia|].

    iIntros "Duty C'". lred2r. rred2r. iApply wpsim_tauR. rred2r.
    iApply wpsim_ret; [eauto|].
    iModIntro.
    iEval (unfold term_cond). iSplit; iFrame. iPureIntro; auto.
  Qed.

  Lemma TreiberClient2_pop_spec tid n :
    ⊢ ⟦(∀ (γk k k' γs γpop : τ{nat, 1+n}),
      ((syn_tgt_interp_as n sndl (fun m => s_memory_black m)) ∗
      (⤉ IsT nTMod n s k' γs) ∗
      (⤉ C2Inv n γk k γs γpop) ∗
      (⤉ ○ γpop tt) ∗
      ◇[k'](1,1) ∗
      TID(tid) ∗
      (⤉ Duty(tid) []))
      -∗
      syn_wpsim (1+n) tid ⊤
      (fun rs rt => (⤉(syn_term_cond n tid _ rs rt))%S)
      false false
      (fn2th TreiberClient2Spec.module "thread_pop" (tt ↑))
      (fn2th TreiberClient2.module "thread_pop" (tt ↑))
    )%S,1+n⟧.
  Proof.
    iIntros.
    red_tl_all; iIntros (γk); red_tl_all; iIntros (k);
    red_tl_all; iIntros (k');
    red_tl_all; iIntros (γs); red_tl_all; iIntros (γpop).

    red_tl_all. unfold C2Inv. simpl.

    iEval (rewrite red_syn_inv; rewrite red_syn_wpsim; rewrite red_syn_tgt_interp_as).

    iIntros "(#Mem & #IsTreiber & #C2Inv & Tok & Pck & TID & Duty)".

    unfold fn2th. simpl. unfold thread_pop, TreiberClient2Spec.thread_pop.
    rred2r. lred2r.

    iApply (wpsim_yieldR with "[$Duty]"); [lia|].
    iIntros "Duty _". rred2r. iApply wpsim_tauR. rred2r.
    iEval (rewrite unfold_iter_eq; rred2r).
    iApply (wpsim_yieldR with "[$Duty]"); [lia|].
    iIntros "Duty _". rred2r. iApply wpsim_tauR. rred2r.

    iInv "C2Inv" as "Client2" "CloseC2Inv".
    iEval (unfold Client2StackState; simpl; red_tl_all; simpl; rewrite red_syn_until_tpromise) in "Client2".

    iDestruct "Client2" as "[#Obl PushProm]".
    iPoseProof (until_tpromise_get_tpromise with "PushProm") as "#TProm".
    iRevert "Tok TID Duty CloseC2Inv Pck".
    iMod (until_tpromise_ind with "[Obl PushProm] [-]") as "Ind"; cycle 2.
    { iApply "Ind". }
    { iSplit; iFrame; auto. }
    iSplit.
    - simpl. red_tl_all. iIntros "!> IH !> [LiveInv TStackC] Tok TID Duty CloseC2Inv Pck".
      iMod ("CloseC2Inv" with "[LiveInv TStackC]") as "_".
      { iEval (unfold Client2StackState; simpl; red_tl_all; simpl).
        iFrame "#". iEval (rewrite red_syn_until_tpromise).
        unfold until_thread_promise. simpl. iSplit; auto.
        iLeft. red_tl_all. iFrame.
      }

      iApply (Treiber_pop_spec nTMod (λ ov, if ov is Some v then ⌜v = 1⌝ else (○ γpop (tt:unit)))%S with "[Duty Pck Tok] [-]"); [|].
      { red_tl_all. rewrite red_syn_tgt_interp_as. iSplit; [eauto|]. iSplit; [iFrame "#"|].
        iFrame. iSplit; [done|]. iSplitL; [|done]. iIntros (s_st). red_tl_all. iIntros "[TStackInv _]".
        rewrite red_syn_fupd. red_tl_all.
        iInv "C2Inv" as "Client2" "CloseC2Inv".
        iEval (unfold Client2StackState; simpl; red_tl_all; simpl; rewrite red_syn_until_tpromise) in "Client2".

        iDestruct "Client2" as "[#OBL PushProm]".

        iEval (unfold until_thread_promise; red_tl_all; simpl) in "PushProm".
        iDestruct "PushProm" as "[#Prm [Bf | #Af]]"; simpl.
        - iEval (red_tl_all; simpl) in "Bf". iDestruct "Bf" as "[LiveInv TStackC]".
          iDestruct (AuthExcls.b_w_eq with "TStackInv TStackC") as "%EQ".
          subst s_st.
          iMod ("CloseC2Inv" with "[LiveInv TStackC]") as "_".
          { iEval (unfold Client2StackState; simpl; red_tl_all; simpl).
            iFrame "#". iEval (rewrite red_syn_until_tpromise).
            unfold until_thread_promise. simpl. iSplit; auto.
            iLeft. red_tl_all. iFrame.
          }
          iModIntro. red_tl_all. iFrame "∗#".
        - iEval (red_tl_all; simpl) in "Af". iDestruct "Af" as "[Dead PushedInv]".
          unfold push_then_pop_inv. rewrite red_syn_inv.
          iInv "PushedInv" as "TStackC" "ClosePushedInv".
          unfold push_then_pop. simpl. red_tl_all.
          iDestruct "TStackC" as "[TStackC| Tok']"; last first.
          { by iDestruct (AuthExcls.w_w_false with "Tok Tok'") as "%False". }
          iDestruct (AuthExcls.b_w_eq with "TStackInv TStackC") as "%EQ".
          subst s_st.
          iMod (AuthExcls.b_w_update with "TStackInv TStackC") as "[TStackInv TStackC]".
          iMod ("ClosePushedInv" with "[$Tok]") as "_".
          iMod ("CloseC2Inv" with "[TStackC]") as "_".
          { iEval (unfold Client2StackState; simpl; red_tl_all; simpl).
            iFrame "#". iEval (rewrite red_syn_until_tpromise).
            unfold until_thread_promise. simpl. iSplit; auto.
            iRight. red_tl_all. iFrame "#".
          }
          iModIntro. red_tl_all. iFrame. done.
      }
      iIntros (rv) "PopPost".
      destruct rv as [v|]; simpl; red_tl_all; rred2r.
      + iDestruct "PopPost" as "[%EQ Duty]". subst v.
        iApply (wpsim_sync with "[$Duty]"); [lia|].
        iIntros "Duty C". lred2r. rred2r. iApply wpsim_tauR. rred2r.
        iApply wpsim_ret; [eauto|].
        iModIntro.
        iEval (unfold term_cond). iSplit; iFrame. iPureIntro; auto.
      + iDestruct "PopPost" as "[Tok Duty]".
        iApply wpsim_tauR. rred2r.
        iEval (rewrite unfold_iter_eq; rred2r).
        iApply (wpsim_yieldR with "[$Duty]"); [lia|].
        iIntros "Duty C". lred2r. rred2r. iApply wpsim_tauR. rred2r.
        iInv "C2Inv" as "Client2" "CloseC2Inv".
        iEval (unfold Client2StackState; simpl; red_tl_all; simpl; rewrite red_syn_until_tpromise) in "Client2".

        iDestruct "Client2" as "[_ PushProm]".
        iMod ("IH" with "[$C $PushProm] ") as "IH".
        iApply ("IH" with "Tok TID Duty CloseC2Inv").
        (* TODO: Uh... *)
        admit.
    - unfold push_then_pop_inv. simpl. red_tl_all. rewrite red_syn_inv.
      iIntros "!> #[Dead PushedInv] Tok TID Duty CloseC2Inv Pck".
      iMod ("CloseC2Inv" with "[]") as "_".
      { iEval (unfold Client2StackState; simpl; red_tl_all; simpl).
        iFrame "#". iEval (rewrite red_syn_until_tpromise).
        iApply until_tpromise_make2. simpl. iSplit; auto.
        iEval (red_tl_all; simpl). iModIntro; iSplit; auto.
      }
      iApply (Treiber_pop_spec nTMod (λ ov, ⌜ ov = Some (1 : SCMem.val) ⌝)%S with "[Duty Pck Tok] [-]"); [|].
      { red_tl_all. rewrite red_syn_tgt_interp_as. iSplit; [eauto|]. iSplitR; [iFrame "#"|].
      iFrame. iSplit; [done|]. iSplitL; [|done]. iIntros (s_st). red_tl_all. iIntros "[TStackInv _]".
      rewrite red_syn_fupd. red_tl_all.
      iInv "C2Inv" as "Client2" "CloseC2Inv".
      iEval (unfold Client2StackState; simpl; red_tl_all; simpl; rewrite red_syn_until_tpromise) in "Client2".

      iDestruct "Client2" as "[#OBL PushProm]".

      iEval (unfold until_thread_promise; red_tl_all; simpl) in "PushProm".
      iDestruct "PushProm" as "[#Prm [Bf | _]]"; simpl.
      - iEval (red_tl_all; simpl) in "Bf". iDestruct "Bf" as "[LiveInv TStackC]".
        iDestruct (Lifetime.pending_not_shot with "LiveInv Dead") as "%False".
        done.
      - (* Note: Slight proof repetition with above failed induction case. *)
        iInv "PushedInv" as "TStackC" "ClosePushedInv".
        unfold push_then_pop. simpl. red_tl_all.
        iDestruct "TStackC" as "[TStackC| Tok']"; last first.
        { by iDestruct (AuthExcls.w_w_false with "Tok Tok'") as "%False". }
        iDestruct (AuthExcls.b_w_eq with "TStackInv TStackC") as "%EQ".
        subst s_st.
        iMod (AuthExcls.b_w_update with "TStackInv TStackC") as "[TStackInv TStackC]".
        iMod ("ClosePushedInv" with "[$Tok]") as "_".
        iMod ("CloseC2Inv" with "[TStackC]") as "_".
        { iEval (unfold Client2StackState; simpl; red_tl_all; simpl).
          iFrame "#". iEval (rewrite red_syn_until_tpromise).
          unfold until_thread_promise. simpl. iSplit; auto.
          iRight. red_tl_all. iFrame "#".
        }
        iModIntro. red_tl_all. iFrame. done.
    }
    iIntros (rv) "PopPost". red_tl_all.
    iDestruct "PopPost" as "[%EQ Duty]". subst rv. rred2r.
    iApply (wpsim_sync with "[$Duty]"); [lia|].
    iIntros "Duty C". lred2r. rred2r. iApply wpsim_tauR. rred2r.
    iApply wpsim_ret; [eauto|].
    iModIntro.
    iEval (unfold term_cond). iSplit; iFrame. iPureIntro; auto.
    Unshelve. all: auto.
    all: apply ndot_ne_disjoint; ss.
  Admitted.

End SPEC.
