From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Import pind Axioms ITreeLib Red TRed IRed2 WFLibLarge.
From Fairness Require Import FairBeh Mod Concurrency Linking.
From Fairness Require Import PCM IProp IPM IPropAux.
From Fairness Require Import IndexedInvariants OpticsInterp SimWeakest SimWeakestAdequacy.
From Fairness Require Import TemporalLogic SCMemSpec ghost_excl LifetimeRA AuthExclsRA.
From Fairness.treiber Require Import SpecLat ClientCode.

Section SPEC.

  Notation src_state := (Mod.state TreiberClientSpec.module).
  Notation src_ident := (Mod.ident TreiberClientSpec.module).
  Notation tgt_state := (Mod.state TreiberClient.module).
  Notation tgt_ident := (Mod.ident TreiberClient.module).

  Local Instance STT : StateTypes := Build_StateTypes src_state tgt_state src_ident tgt_ident.
  Context `{sub : @SRA.subG Γ Σ}.
  Context {TLRASs : TLRAs_small STT Γ}.
  Context {TLRAS : TLRAs STT Γ Σ}.

  Context {HasMemRA: @GRA.inG memRA Γ}.
  Context {HasLifetime : @GRA.inG Lifetime.t Γ}.

  Context {HasGhostMap : @GRA.inG (ghost_mapURA nat maybe_null_ptr) Γ}.
  Context {HasGhostVar : @GRA.inG (ghost_varURA (list SCMem.val)) Γ}.

  Context `{HasGhostExcl : @GRA.inG (ghost_exclURA unit) Γ}.

  Ltac red_tl_all := red_tl; red_tl_memra; red_tl_ghost_excl_ura; red_tl_lifetime.

  Import TreiberClient.

  (** Invariants. *)

  (* Namespace for TreiberClient invariants. *)
  Definition nTCli : namespace := (nroot .@"TCli").
  Definition nTpush : namespace := (nroot .@"Tpush").
  Definition nTMod : namespace := (nroot .@"TMod").

  Definition push_then_pop n γs γpop : sProp n :=
    (TStack n γs [(1 : SCMem.val)] ∨ GEx γpop tt)%S.

  Definition push_then_pop_inv n γs γpop : sProp n :=
    (syn_inv n nTpush (push_then_pop n γs γpop))%S.

  Definition Client2StackState n γk k γs γpop : sProp n :=
    (◆[k,2] ∗
    ((live γk k (1/2) ∗ TStack n γs ([] : list SCMem.val)) -U-[k](0)-◇ (dead γk k ∗ push_then_pop_inv n γs γpop))
    )%S.

  Definition CInv n γk k γs γpop : sProp n :=
    (syn_inv n nTCli (Client2StackState n γk k γs γpop))%S.

  Global Instance CInv_persistent n γk k γs γpop : Persistent ⟦CInv n γk k γs γpop, n⟧.
  Proof.
    unfold Persistent. iIntros "H". unfold CInv. rewrite red_syn_inv.
    iDestruct "H" as "#H". auto.
  Qed.

  (** Simulation proof. *)

  Lemma TreiberClient_push_spec tid n :
    ⊢ ⟦(∀ (γk kt k γs γpop : τ{nat, 1+n}),
      ((syn_tgt_interp_as n sndl (fun m => s_memory_black m)) ∗
      (⤉ IsT nTMod n 1 2 s kt γs) ∗
      (⤉ CInv n γk k γs γpop) ∗
      TID(tid) ∗
      ◇[kt](1, 1) ∗
      (⤉ Duty(tid) [(k, 0, dead γk (k : nat) ∗ push_then_pop_inv n γs γpop)]) ∗
      ◇[k](3, 5) ∗ ⤉(live γk (k : nat) (1/2)) ∗
      ⋈[k])
      -∗
      syn_wpsim (1+n) tid ⊤
      (fun rs rt => (⤉(syn_term_cond n tid _ rs rt))%S)
      false false
      (fn2th TreiberClientSpec.module "thread_push" (tt ↑))
      (fn2th TreiberClient.module "thread_push" (tt ↑))
    )%S,1+n⟧.
  Proof.
    iIntros.
    red_tl_all; iIntros (γk); red_tl_all; iIntros (kt); red_tl_all; iIntros (k); red_tl_all; iIntros (γs); red_tl_all; iIntros (γpop).

    red_tl_all. unfold CInv. simpl.

    iEval (rewrite red_syn_inv; rewrite red_syn_wpsim; rewrite red_syn_tgt_interp_as).

    iIntros "(#Mem & #IsTreiber & #CInv & TID & Pck & Duty & Pc & Live & k_Act)".

    unfold fn2th. simpl. unfold thread_push, TreiberClientSpec.thread_push.
    rred2r. lred2r.

    iDestruct (pc_split _ _ 1 4 with "Pc") as "[Ys PcSt]".
    iMod (pc_drop _ 1 3 ltac:(auto) 100 with "Ys") as "Ys"; [lia|].
    iDestruct (pc_split _ _ 1 99 with "Ys") as "[Y Ys]".
    iApply (wpsim_yieldR with "[$Duty Y]"); [lia| |].
    { simpl. iDestruct (pcs_cons_fold with "[Y]") as "$". iFrame. }

    iIntros "Duty _". rred2r. iApply wpsim_tauR. rred2r.

    iApply (Treiber_push_spec nTMod with "[Duty Pck PcSt] [-]").
    { red_tl_all. rewrite red_syn_tgt_interp_as. simpl. iFrame "#".
      iFrame. iDestruct (pcs_cons_fold with "[PcSt]") as "$". iFrame.
    }
    Unshelve.
    2:{ apply ndot_ne_disjoint. ss. }

    unfold atomic_update.

    iInv "CInv" as "Client2" "CloseCInv". simpl.
    iApply FUpd_mask_keep; [set_solver|].
    iIntros "CloseTS !>".

    iEval (unfold Client2StackState; simpl; red_tl_all; simpl; rewrite red_syn_until_tpromise) in "Client2".
    iDestruct "Client2" as "[#OBL PushProm]".

    iEval (unfold until_thread_promise; red_tl_all; simpl) in "PushProm".

    iDestruct "PushProm" as "[#Prm [Bf | #Af]]"; simpl; last first.
    { iEval (red_tl_all; simpl) in "Af". iDestruct "Af" as "[Dead TStackC]".
      by iDestruct (Lifetime.pending_not_shot with "Live Dead") as "%False".
    }
    iEval (red_tl_all; simpl) in "Bf". iDestruct "Bf" as "[LiveInv TStackC]".
    iExists _. iFrame "TStackC". iIntros (_) "TStackC".
    iMod ((FUpd_alloc _ _ _ n (nTpush) (push_then_pop n γs γpop : sProp n)%S) with "[TStackC]") as "#Pushed"; [lia| |].
    { unfold push_then_pop. iEval (simpl; red_tl_all; simpl). auto. }
    iDestruct (Lifetime.pending_merge with "Live LiveInv") as "Live".
    iEval (rewrite Qp.half_half) in "Live".
    iMod (Lifetime.pending_shot with "Live") as "#Dead".
    iMod "CloseTS" as "_".
    iMod ("CloseCInv" with "[]") as "_".
    { iEval (unfold Client2StackState; simpl; red_tl_all; simpl).
      iFrame "#". iEval (rewrite red_syn_until_tpromise).
      iApply until_tpromise_make2. simpl. iSplit; auto.
      iEval (red_tl_all; simpl). iModIntro; iSplit; auto.
    }
    iIntros "!>" (_) "Duty".

    red_tl_all.
    iMod (duty_fulfill with "[Dead $Duty k_Act]") as "Duty".
    { simpl. unfold push_then_pop_inv. red_tl_all. rewrite red_syn_inv. auto. }

    rred2r.

    iApply (wpsim_sync with "[$Duty]"); [lia|].

    iIntros "Duty _". lred2r. rred2r. iApply wpsim_tauR. rred2r.
    iApply wpsim_ret; [eauto|].
    iModIntro.
    iEval (unfold term_cond). iSplit; iFrame. iPureIntro; auto.
  Qed.

  Lemma TreiberClient_pop_spec tid n :
    ⊢ ⟦(∀ (γk k kt γs γpop : τ{nat, 1+n}),
      ((syn_tgt_interp_as n sndl (fun m => s_memory_black m)) ∗
      (⤉ IsT nTMod n 1 2 s kt γs) ∗
      (⤉ CInv n γk k γs γpop) ∗
      (⤉ GEx γpop tt) ∗
      ◇[kt](1,1) ∗
      TID(tid) ∗
      (⤉ Duty(tid) []))
      -∗
      syn_wpsim (1+n) tid ⊤
      (fun rs rt => (⤉(syn_term_cond n tid _ rs rt))%S)
      false false
      (fn2th TreiberClientSpec.module "thread_pop" (tt ↑))
      (fn2th TreiberClient.module "thread_pop" (tt ↑))
    )%S,1+n⟧.
  Proof.
    iIntros.
    red_tl_all; iIntros (γk); red_tl_all; iIntros (k);
    red_tl_all; iIntros (kt);
    red_tl_all; iIntros (γs); red_tl_all; iIntros (γpop).

    red_tl_all. unfold CInv. simpl.

    iEval (rewrite red_syn_inv; rewrite red_syn_wpsim; rewrite red_syn_tgt_interp_as).

    iIntros "(#Mem & #IsTreiber & #CInv & Tok & Pck & TID & Duty)".

    unfold fn2th. simpl. unfold thread_pop, TreiberClientSpec.thread_pop.
    rred2r. lred2r.

    iApply (wpsim_yieldR with "[$Duty]"); [lia|].
    iIntros "Duty _". rred2r. iApply wpsim_tauR. rred2r.

    iInv "CInv" as "Client2" "CloseCInv".
    iEval (unfold Client2StackState; simpl; red_tl_all; simpl; rewrite red_syn_until_tpromise) in "Client2".

    iDestruct "Client2" as "[#Obl PushProm]".
    iPoseProof (until_tpromise_get_tpromise with "PushProm") as "#TProm".
    iRevert "Tok TID Duty CloseCInv Pck".
    iMod (until_tpromise_ind with "[Obl PushProm] [-]") as "Ind"; cycle 2.
    { iApply "Ind". }
    { iSplit; iFrame; auto. }
    iSplit.
    - simpl. red_tl_all. iIntros "!> IH !> [LiveInv TStackC] Tok TID Duty CloseCInv Pck".
      iMod ("CloseCInv" with "[LiveInv TStackC]") as "_".
      { iEval (unfold Client2StackState; simpl; red_tl_all; simpl).
        iFrame "#". iEval (rewrite red_syn_until_tpromise).
        unfold until_thread_promise. simpl. iSplit; auto.
        iLeft. red_tl_all. iFrame.
      }

      iEval (rewrite unfold_iter_eq; rred2r).
      iApply (wpsim_yieldR with "[$Duty]"); [lia|].
      iIntros "Duty C". rred2r. iApply wpsim_tauR. rred2r.

      iApply (Treiber_pop_spec nTMod with "[Duty Pck] [-]").
      { red_tl_all. rewrite red_syn_tgt_interp_as. simpl. iFrame "# ∗". }

      unfold atomic_update.

      iInv "CInv" as "Client2" "CloseCInv". simpl.

      iEval (unfold Client2StackState; simpl; red_tl_all; simpl; rewrite red_syn_until_tpromise) in "Client2".

      iDestruct "Client2" as "[#OBL PushProm]".
      iEval (unfold until_thread_promise; red_tl_all; simpl) in "PushProm".
      iDestruct "PushProm" as "[#Prm [Bf | #Af]]"; simpl.
      + iEval (red_tl_all; simpl) in "Bf". iDestruct "Bf" as "[LiveInv TStackC]".
        iApply FUpd_mask_keep; [set_solver|].
        iIntros "CloseTS !>".

        iExists _. iFrame. iIntros (s_st) "[TStackC %EQ]". subst s_st.
        iMod "CloseTS" as "_".
        iMod ("CloseCInv" with "[LiveInv TStackC]") as "_".
        { iEval (unfold Client2StackState; simpl; red_tl_all; simpl).
          iFrame "#". iEval (rewrite red_syn_until_tpromise).
          unfold until_thread_promise. simpl. iSplit; auto.
          iLeft. red_tl_all. iFrame.
        }
        iIntros "!>" (?) "[Duty Pck]".
        rred2r. iApply wpsim_tauR. rred2r.

        iInv "CInv" as "Client2" "CloseCInv".
        iEval (unfold Client2StackState; simpl; red_tl_all; simpl; rewrite red_syn_until_tpromise) in "Client2".

        iDestruct "Client2" as "[_ PushProm]".
        iMod ("IH" with "[$C $PushProm] ") as "IH".
        iApply ("IH" with "Tok TID Duty CloseCInv Pck").
      + iEval (red_tl_all; simpl) in "Af". iDestruct "Af" as "[Dead PushedInv]".
        unfold push_then_pop_inv. rewrite red_syn_inv.
        iInv "PushedInv" as "TStackC" "ClosePushedInv".
        unfold push_then_pop. simpl. red_tl_all.
        iDestruct "TStackC" as "[TStackC| Tokt]"; last first.
        { iDestruct (ghost_excl_exclusive with "Tok Tokt") as %[]. }
        iApply FUpd_mask_keep; [set_solver|].
        iIntros "CloseTS !>".
        iExists _. iFrame "TStackC". iIntros (s_st) "[TStackC %EQ]". subst s_st.

        iMod "CloseTS" as "_".
        iMod ("ClosePushedInv" with "[$Tok]") as "_".
        iMod ("CloseCInv" with "[TStackC]") as "_".
        { iEval (unfold Client2StackState; simpl; red_tl_all; simpl).
          iFrame "#". iEval (rewrite red_syn_until_tpromise).
          unfold until_thread_promise. simpl. iSplit; auto.
          iRight. red_tl_all. iFrame "#".
        }
        iIntros "!>" (_) "[Duty _]". red_tl_all. rred2r.
        iApply (wpsim_sync with "[$Duty]"); [lia|].
        iIntros "Duty _". lred2r. rred2r. iApply wpsim_tauR. rred2r.
        iApply wpsim_ret; [eauto|].
        iModIntro.
        iEval (unfold term_cond). iSplit; iFrame. iPureIntro; auto.
  - unfold push_then_pop_inv. simpl. red_tl_all. rewrite red_syn_inv.
    iIntros "!> #[Dead PushedInv] Tok TID Duty CloseCInv Pck".
    iMod ("CloseCInv" with "[]") as "_".
    { iEval (unfold Client2StackState; simpl; red_tl_all; simpl).
      iFrame "#". iEval (rewrite red_syn_until_tpromise).
      iApply until_tpromise_make2. simpl. iSplit; auto.
      iEval (red_tl_all; simpl). iModIntro; iSplit; auto.
    }

    iEval (rewrite unfold_iter_eq; rred2r).
    iApply (wpsim_yieldR with "[$Duty]"); [lia|].
    iIntros "Duty _". rred2r. iApply wpsim_tauR. rred2r.

    iApply (Treiber_pop_spec nTMod with "[Duty Pck] [-]").
    { red_tl_all. simpl. rewrite red_syn_tgt_interp_as. iFrame "# ∗". }

    unfold atomic_update.

    iInv "CInv" as "Client2" "CloseCInv". simpl.
    iEval (unfold Client2StackState; simpl; red_tl_all; simpl; rewrite red_syn_until_tpromise) in "Client2".
    iDestruct "Client2" as "[#OBL PushProm]".
    iEval (unfold until_thread_promise; red_tl_all; simpl) in "PushProm".
    iDestruct "PushProm" as "[#Prm [Bf | _]]"; simpl.
    { iEval (red_tl_all; simpl) in "Bf". iDestruct "Bf" as "[LiveInv TStackC]".
      iDestruct (Lifetime.pending_not_shot with "LiveInv Dead") as %[].
    }

    iInv "PushedInv" as "TStackC" "ClosePushedInv".
    unfold push_then_pop. simpl. red_tl_all.
    iDestruct "TStackC" as "[TStackC| Tokt]"; last first.
    { iDestruct (ghost_excl_exclusive with "Tok Tokt") as %[]. }
    iApply FUpd_mask_keep; [set_solver|].
    iIntros "CloseTS !>".

    iExists _. iFrame "TStackC". iIntros (s_st) "[TStackC %EQ]". subst s_st.

    iMod "CloseTS" as "_".
    iMod ("ClosePushedInv" with "[$Tok]") as "_".
    iMod ("CloseCInv" with "[TStackC]") as "_".
    { iEval (unfold Client2StackState; simpl; red_tl_all; simpl).
      iFrame "#". iEval (rewrite red_syn_until_tpromise).
      unfold until_thread_promise. simpl. iSplit; auto.
      iRight. red_tl_all. iFrame "#".
    }
    iIntros "!>" (_) "[Duty _]". rred2r.

    iApply (wpsim_sync with "[$Duty]"); [lia|].
    iIntros "Duty _". lred2r. rred2r. iApply wpsim_tauR. rred2r.
    iApply wpsim_ret; [eauto|].
    iModIntro.
    iEval (unfold term_cond). iSplit; iFrame. iPureIntro; auto.
    Unshelve.
    all: apply ndot_ne_disjoint; ss.
  Qed.

End SPEC.
