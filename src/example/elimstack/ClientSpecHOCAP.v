From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Import pind Axioms ITreeLib Red TRed IRed2 WFLibLarge.
From Fairness Require Import FairBeh Mod Concurrency Linking.
From Fairness Require Import PCM IPM IPropAux.
From Fairness Require Import IndexedInvariants OpticsInterp SimWeakest SimWeakestAdequacy.
From Fairness Require Import TemporalLogic SCMemSpec ghost_var ghost_map ghost_excl LifetimeRA.
From Fairness.elimstack Require Import ClientCode SpecHOCAP.

Section SPEC.

  Notation src_state := (Mod.state ElimStackClientSpec.module).
  Notation src_ident := (Mod.ident ElimStackClientSpec.module).
  Notation tgt_state := (Mod.state ElimStackClient.module).
  Notation tgt_ident := (Mod.ident ElimStackClient.module).

  Local Instance STT : StateTypes := Build_StateTypes src_state tgt_state src_ident tgt_ident.
  Context `{sub : @SRA.subG Γ Σ}.
  Context {TLRASs : TLRAs_small STT Γ}.
  Context {TLRAS : TLRAs STT Γ Σ}.

  Context {HasMemRA: @GRA.inG memRA Γ}.
  Context {HasLifetime : @GRA.inG Lifetime.t Γ}.

  Context {HasGhostVar : @GRA.inG (ghost_varURA (list SCMem.val)) Γ}.
  Context {HasGhostMap : @GRA.inG (ghost_mapURA nat maybe_null_ptr) Γ}.
  Context {HasGhostExcl : @GRA.inG (ghost_exclURA unit) Γ}.

  Ltac red_tl_all := red_tl; red_tl_memra; red_tl_lifetime; red_tl_ghost_excl.

  Import ElimStackClient.

  Local Opaque s.

  (** Invariants. *)

  (* Namespace for ElimStackClient invariants. *)
  Definition nESCli : namespace := (nroot .@"ESCli").
  Definition nESpush : namespace := (nroot .@"ESpush").
  Definition nESMod : namespace := (nroot .@"ESMod").

  Definition push_then_pop n γs γpop : sProp n :=
    (EStack n γs [(1 : SCMem.val)] ∨ GEx γpop tt)%S.

  Definition push_then_pop_inv n γs γpop : sProp n :=
    (syn_inv n nESpush (push_then_pop n γs γpop))%S.

  Definition CState (n γk k γs γpop : nat) : sProp n :=
    ((((live γk k (1/2)) ∗ (EStack n γs [])))
    -U-[k](0)-◇
    (((dead γk k) ∗ (push_then_pop_inv n γs γpop)))
    )%S.

  Definition CInv n γk k γs γpop : sProp n :=
    (◆[k,3,6] ∗ syn_inv n nESCli (CState n γk k γs γpop))%S.

  Global Instance CInv_persistent n γk k γs γpop : Persistent ⟦CInv n γk k γs γpop, n⟧.
  Proof. unfold Persistent,CInv. red_tl. rewrite red_syn_inv. iIntros "#$". Qed.

  (** Simulation proof. *)

  Lemma ElimStackClient_push_sim tid n γk k kt γs γpop :
    ⊢ ⟦(
      (syn_tgt_interp_as (2+n) sndl (fun m => s_memory_black m) ∗
      (⤉ IsES nESMod n 1 2 s kt γs) ∗
      (⤉⤉⤉ CInv n γk k γs γpop) ∗
      TID(tid) ∗
      ◇[kt](1, 1) ∗
      (⤉⤉⤉ Duty(tid) [(k, 0, dead γk k ∗ push_then_pop_inv n γs γpop)]) ∗
      ◇[k](3, 5) ∗ (⤉⤉⤉ live γk k (1/2)) ∗
      ⋈[k])
      -∗
      syn_wpsim (3+n) tid ⊤
      (fun rs rt => (⤉⤉⤉ (syn_term_cond n tid _ rs rt))%S)
      false false
      (fn2th ElimStackClientSpec.module "thread_push" (tt ↑))
      (fn2th ElimStackClient.module "thread_push" (tt ↑))
    )%S,3+n⟧.
  Proof.
    iIntros. unfold CInv. red_tl_all. simpl. red_tl_all.

    iEval (rewrite red_syn_inv; rewrite red_syn_wpsim; rewrite red_syn_tgt_interp_as).

    iIntros "(#Mem & #IsElimStack & #[Ob_kb CInv] & TID & Pck & Duty & Pc & Live & k_Act)".

    unfold fn2th. simpl. unfold thread_push, ElimStackClientSpec.thread_push.
    rred2r. lred2r.

    iDestruct (pc_split _ _ 1 4 with "Pc") as "[Ys PcSt]".
    iMod (pc_drop _ 1 3 ltac:(auto) 100 with "Ys") as "Ys"; [lia|].
    iDestruct (pc_split _ _ 1 99 with "Ys") as "[Y Ys]".
    iApply (wpsim_yieldR with "[$Duty Y]"); [lia| |].
    { simpl. iDestruct (pcs_cons_fold with "[Y]") as "$". iFrame. }

    iIntros "Duty _". rred2r. iApply wpsim_tauR. rred2r. red_tl_all.

    iApply (Elim_push_spec nESMod ltac:(solve_ndisj) (⤉ (dead γk k ∗ syn_inv n nESpush (push_then_pop n γs γpop)))%S with "[Duty Pck PcSt Live] [-]").
    { simpl. red_tl_all. rewrite red_syn_tgt_interp_as. iSplit; [eauto|]. iSplitR; [iFrame "#"|]. simpl.
      iFrame. simpl.
      iDestruct (pcs_cons_fold with "[PcSt]") as "$".
      { simpl. iFrame. }
      rewrite red_syn_atomic_update.
      iInv "CInv" as "Client" "CloseCInv".
      iApply fupd_mask_intro; [solve_ndisj|].
      iIntros "CloseES".

      iEval (unfold CState; simpl; red_tl_all; simpl; rewrite red_syn_until_tpromise) in "Client".
      iDestruct "Client" as "[#OBL PushProm]".

      iEval (unfold until_thread_promise; red_tl_all; simpl) in "PushProm".

      iDestruct "PushProm" as "[Bf | #Af]"; simpl.
      - iEval (red_tl_all; simpl) in "Bf". iDestruct "Bf" as "[LiveInv EStackC]".
      iExists _. red_tl. iFrame. iIntros (_) "EStackC".
      iMod ((FUpd_alloc _ _ _ n (nESpush) (push_then_pop n γs γpop : sProp n)%S) with "[EStackC]") as "#Pushed"; [lia| |].
        { unfold push_then_pop. iEval (simpl; red_tl_all; simpl). auto. }
        iDestruct (Lifetime.pending_merge with "Live LiveInv") as "Live".
        iEval (rewrite Qp.half_half) in "Live".
        iMod (Lifetime.pending_shot with "Live") as "#Dead".

        iMod "CloseES" as "_".
        iMod ("CloseCInv" with "[]") as "_".
        { iEval (unfold CState; simpl; red_tl_all; simpl).
          iFrame "#". iEval (rewrite red_syn_until_tpromise).
          iApply until_tpromise_make2. simpl. iSplit; auto.
          iEval (red_tl_all; simpl). iModIntro; iSplit; auto.
        }
        iModIntro. red_tl_all. iFrame "∗#".
      - iEval (red_tl_all; simpl) in "Af". iDestruct "Af" as "[Dead EStackC]".
        iDestruct (Lifetime.pending_not_shot with "Live Dead") as %[].
    }

    iIntros (_). simpl. red_tl_all. iIntros "[[#Dead Pushed] Duty]".
    iEval (rewrite red_syn_inv) in "Pushed". iDestruct "Pushed" as "#Pushed".
    iMod (duty_fulfill with "[$Duty $k_Act]") as "Duty".
    { iFrame. simpl. unfold push_then_pop_inv. red_tl_all. rewrite red_syn_inv. auto. }

    rred2r.
    iApply (wpsim_sync with "[$Duty]"); [lia|].

    iIntros "Duty _". lred2r. rred2r. iApply wpsim_tauR. rred2r.
    iApply wpsim_ret; [eauto|].
    iModIntro.
    iEval (unfold term_cond). iSplitL; iFrame; iPureIntro; auto.
  Qed.

  Lemma ElimStackClient_pop_sim tid n γk k kt γs γpop:
    ⊢ ⟦(
      (syn_tgt_interp_as (2+n) sndl (fun m => s_memory_black m) ∗
      (⤉ IsES nESMod n 1 2 s kt γs) ∗
      (⤉⤉⤉ CInv n γk k γs γpop) ∗
      (⤉⤉⤉ GEx γpop tt) ∗
      ◇[kt](1,1) ∗
      TID(tid) ∗
      (⤉⤉⤉ Duty(tid) []))
      -∗
      syn_wpsim (3+n) tid ⊤
      (fun rs rt => (⤉⤉⤉ (syn_term_cond n tid _ rs rt))%S)
      false false
      (fn2th ElimStackClientSpec.module "thread_pop" (tt ↑))
      (fn2th ElimStackClient.module "thread_pop" (tt ↑))
    )%S,3+n⟧.
  Proof.
    iIntros. unfold CInv. red_tl_all. simpl. red_tl_all.

    iEval (rewrite red_syn_inv; rewrite red_syn_wpsim; rewrite red_syn_tgt_interp_as).

    iIntros "(#Mem & #IsElimStack & #[Ob_kb CInv] & Tok & Pck & TID & Duty)".

    iMod (ccs_make_fine _ _ _ [] 0 with "[$Ob_kb]") as "CCS".

    unfold fn2th. simpl. unfold thread_pop, ElimStackClientSpec.thread_pop.
    rred2r. lred2r.

    iApply (wpsim_yieldR with "[$Duty]"); [lia|].
    iIntros "Duty _". rred2r. iApply wpsim_tauR. rred2r.
    iEval (rewrite unfold_iter_eq; rred2r).
    iApply (wpsim_yieldR with "[$Duty]"); [lia|].
    iIntros "Duty _". rred2r. iApply wpsim_tauR. rred2r.

    iInv "CInv" as "PushProm" "CloseCInv".
    iEval (unfold CState; simpl; red_tl_all; simpl; rewrite red_syn_until_tpromise) in "PushProm".

    iPoseProof (until_tpromise_get_tpromise with "PushProm") as "#TProm".
    iRevert "Tok TID Duty CloseCInv Pck".
    iMod (ccs_until_tpromise_ind with "[$CCS $PushProm] [-]") as "Ind"; [|by iApply "Ind"].
    iSplit.
    - simpl. red_tl_all. iIntros "!> IH !> _ [LiveInv EStackC] Tok TID Duty CloseCInv Pck".
      iMod ("CloseCInv" with "[LiveInv EStackC]") as "_".
      { iEval (unfold CState; simpl; red_tl_all; simpl).
        iFrame "#". iEval (rewrite red_syn_until_tpromise).
        unfold until_thread_promise. simpl. iSplit; auto.
        iLeft. red_tl_all. iFrame.
      }

      iApply (Elim_pop_spec nESMod ltac:(solve_ndisj) (λ ov, if ov is Some v then ⌜v = 1⌝ else GEx γpop tt)%S with "[Duty Pck Tok] [-]").
      { simpl. red_tl_all. rewrite red_syn_tgt_interp_as. iSplit; [eauto|]. iSplit; [iFrame "#"|].
        iFrame. simpl.  iSplitL; [|done].
        rewrite red_syn_atomic_update.
        iInv "CInv" as "Client" "CloseCInv".
        iEval (unfold CState; simpl; red_tl_all; simpl; rewrite red_syn_until_tpromise) in "Client".

        iDestruct "Client" as "[_ PushProm]".

        iEval (unfold until_thread_promise; red_tl_all; simpl) in "PushProm".
        iDestruct "PushProm" as "[Bf | #Af]"; simpl.
        - iEval (red_tl_all; simpl) in "Bf". iDestruct "Bf" as "[LiveInv EStackC]".
          iApply fupd_mask_intro; [solve_ndisj|].
          iIntros "CloseES".
          iExists _. red_tl. iFrame. iIntros (_) "EStackC".
          iMod "CloseES" as "_".
          iMod ("CloseCInv" with "[LiveInv EStackC]") as "_".
          { iEval (unfold CState; simpl; red_tl_all; simpl).
            iFrame "#". iEval (rewrite red_syn_until_tpromise).
            unfold until_thread_promise. simpl. iSplit; auto.
            iLeft. red_tl_all. iFrame.
          }
          iModIntro. simpl. red_tl_all. iFrame "∗#".
        - iEval (red_tl_all; simpl) in "Af". iDestruct "Af" as "[Dead PushedInv]".
          unfold push_then_pop_inv. rewrite red_syn_inv.
          iInv "PushedInv" as "EStackC" "ClosePushedInv".
          unfold push_then_pop. simpl. red_tl_all.
          iDestruct "EStackC" as "[EStackC| Tokt]"; last first.
          { iDestruct (ghost_excl_exclusive with "Tok Tokt") as %[]. }

          iApply fupd_mask_intro; [solve_ndisj|].
          iIntros "CloseES".
          iExists _. red_tl. iFrame. iIntros (_) "EStackC".
          iMod "CloseES" as "_".

          iMod ("ClosePushedInv" with "[$Tok]") as "_".
          iMod ("CloseCInv" with "[EStackC]") as "_".
          { iEval (unfold CState; simpl; red_tl_all; simpl).
            iFrame "#". iEval (rewrite red_syn_until_tpromise).
            unfold until_thread_promise. simpl. iSplit; auto.
            iRight. red_tl_all. iFrame "#".
          }
          iModIntro. simpl. red_tl_all. done.
      }
      iIntros (rv) "PopPost".
      destruct rv as [v|]; simpl; red_tl_all; rred2r.
      + iDestruct "PopPost" as "(%EQ & Duty & _)". subst v.
        iApply (wpsim_sync with "[$Duty]"); [lia|].
        iIntros "Duty C". lred2r. rred2r. iApply wpsim_tauR. rred2r.
        iApply wpsim_ret; [eauto|].
        iModIntro.
        iEval (unfold term_cond). iSplitL; iFrame. iPureIntro; auto.
      + iDestruct "PopPost" as "(Tok & Duty & Pck)".
        iApply wpsim_tauR. rred2r.
        iEval (rewrite unfold_iter_eq; rred2r).
        iApply (wpsim_yieldR with "[$Duty]"); [lia|].
        iIntros "Duty C". lred2r. rred2r. iApply wpsim_tauR. rred2r.
        iInv "CInv" as "Client" "CloseCInv".
        iEval (unfold CState; simpl; red_tl_all; simpl; rewrite red_syn_until_tpromise) in "Client".

        iDestruct "Client" as "[_ PushProm]".
        iMod ("IH" with "[$C $PushProm $TProm]") as "IH".
        iApply ("IH" with "Tok TID Duty CloseCInv Pck").
    - unfold push_then_pop_inv. simpl. red_tl_all. rewrite red_syn_inv.
      iIntros "!> #[Dead PushedInv] Tok TID Duty CloseCInv Pck".
      iMod ("CloseCInv" with "[]") as "_".
      { iEval (unfold CState; simpl; red_tl_all; simpl).
        iFrame "#". iEval (rewrite red_syn_until_tpromise).
        iApply until_tpromise_make2. simpl. iSplit; auto.
        iEval (red_tl_all; simpl). iModIntro; iSplit; auto.
      }
      iApply (Elim_pop_spec nESMod ltac:(solve_ndisj) (λ ov, ⌜ ov = Some (1 : SCMem.val) ⌝)%S with "[Duty Pck Tok] [-]").
      { simpl. red_tl_all. rewrite red_syn_tgt_interp_as. iSplit; [eauto|]. iSplitR; [iFrame "#"|].
      iFrame. iSplitL; [|done].
      rewrite red_syn_atomic_update.

      iInv "CInv" as "Client" "CloseCInv".
      iEval (unfold CState; simpl; red_tl_all; simpl; rewrite red_syn_until_tpromise) in "Client".

      iDestruct "Client" as "[#OBL PushProm]".

      iEval (unfold until_thread_promise; red_tl_all; simpl) in "PushProm".
      iDestruct "PushProm" as "[Bf | _]"; simpl.
      { iEval (red_tl_all; simpl) in "Bf". iDestruct "Bf" as "[LiveInv EStackC]".
        iDestruct (Lifetime.pending_not_shot with "LiveInv Dead") as %[].
      }
      (* Note: Slight proof repetition with above failed induction case. *)
      iInv "PushedInv" as "EStackC" "ClosePushedInv".
      unfold push_then_pop. simpl. red_tl_all.
      iDestruct "EStackC" as "[EStackC| Tokt]"; last first.
      { iDestruct (ghost_excl_exclusive with "Tok Tokt") as %[]. }

      iApply fupd_mask_intro; [solve_ndisj|].
      iIntros "CloseTS".
      iExists _. red_tl. iFrame. iIntros (_) "EStackC".
      iMod "CloseTS" as "_".

      iMod ("ClosePushedInv" with "[$Tok]") as "_".
      iMod ("CloseCInv" with "[EStackC]") as "_".
      { iEval (unfold CState; simpl; red_tl_all; simpl).
        iFrame "#". iEval (rewrite red_syn_until_tpromise).
        unfold until_thread_promise. simpl. iSplit; auto.
        iRight. red_tl_all. iFrame "#".
      }
      iModIntro. red_tl_all. iFrame. done.
    }
    iIntros (rv) "PopPost". simpl. red_tl_all.
    iDestruct "PopPost" as "(%EQ & Duty & _)". subst rv. rred2r.
    iApply (wpsim_sync with "[$Duty]"); [lia|].
    iIntros "Duty _". lred2r. rred2r. iApply wpsim_tauR. rred2r.
    iApply wpsim_ret; [eauto|].
    iModIntro.
    iEval (unfold term_cond). iSplitL; iFrame. iPureIntro; auto.
  Qed.

  Section INITIAL.

  Variable tid_push tid_pop : thread_id.
  Let init_ord := Ord.O.
  Let init_ths :=
        (NatStructsLarge.NatMap.add
            tid_push tt
            (NatStructsLarge.NatMap.add
              tid_pop tt
              (NatStructsLarge.NatMap.empty unit))).

  Let idx := 1.

  Lemma init_sat E (H_TID : tid_push ≠ tid_pop) :
    (OwnM (Σ:=Σ) (memory_init_resource ElimStackClient.gvs))
      ∗
      (WSim.initial_prop
        ElimStackClientSpec.module ElimStackClient.module
          (Vars:=@sProp STT Γ) (Σ:=Σ)
          (STATESRC:=@SRA.in_subG Γ Σ sub _ _STATESRC)
          (STATETGT:=@SRA.in_subG Γ Σ sub _ _STATETGT)
          (IDENTSRC:=@SRA.in_subG Γ Σ sub _ _IDENTSRC)
          (IDENTTGT:=@SRA.in_subG Γ Σ sub _ _IDENTTGT)
          (ARROWRA:=@_ARROWRA STT Γ Σ TLRAS)
          idx init_ths init_ord)
      ⊢
      =| 3+idx |=(⟦syn_fairI (3+idx), 3+idx⟧)={E}=>
        ∃ (γk k γpop γs kt : nat),
        ⟦syn_tgt_interp_as (2+idx) sndl (fun m => s_memory_black m),3+idx⟧ ∗
        ⟦IsES nESMod idx 1 2 s kt γs,2+idx⟧ ∗
        ⟦CInv idx γk k γs γpop,idx⟧ ∗
        (* thread_push *)
        own_thread tid_push ∗
        ⟦Duty(tid_push) [(k, 0, (dead γk k : sProp idx) ∗ push_then_pop_inv idx γs γpop)],idx⟧ ∗
        ◇[kt](1, 1) ∗
        ◇[k](3, 5) ∗
        live γk k (1/2) ∗
        ⋈[k] ∗
        (* thread_pop *)
        GEx γpop tt ∗
        ◇[kt](1,1) ∗
        own_thread tid_pop ∗
        ⟦Duty(tid_pop) [],idx⟧
  .
  Proof.
    iIntros "(Mem & Init)". rewrite red_syn_fairI.
    iDestruct (memory_init_iprop with "Mem") as "[Mem ↦s]".
    iDestruct "↦s" as "((s↦ & s.o↦ & _) & _)".
    Local Transparent s.
    assert ((((SCMem.next_block SCMem.empty,0) : SCMem.pointer): SCMem.val) = s) as -> by done.
    Local Opaque s.

    unfold WSim.initial_prop. simpl.
    iDestruct "Init" as "(_ & _ & Ds & Ts & _ & St_tgt)".

    assert (NatStructsLarge.NatMap.find tid_push init_ths = Some tt) as Htid_push.
    { unfold init_ths. apply NatStructsLarge.nm_find_add_eq. }
    iDestruct (natmap_prop_remove_find _ _ _ Htid_push with "Ds") as "[Dpush Ds]".
    iDestruct (natmap_prop_remove_find _ _ _ Htid_push with "Ts") as "[Tpush Ts]".
    clear Htid_push.

    assert (NatStructsLarge.NatMap.find tid_pop (NatStructsLarge.NatMap.remove tid_push init_ths) = Some tt) as Htid_pop.
    { unfold init_ths.
      rewrite NatStructsLarge.NatMapP.F.remove_neq_o; ss.
      rewrite NatStructsLarge.nm_find_add_neq; ss.
      rewrite NatStructsLarge.nm_find_add_eq. ss.
    }
    iDestruct (natmap_prop_remove_find _ _ _ Htid_pop with "Ds") as "[Dpop _]".
    iDestruct (natmap_prop_remove_find _ _ _ Htid_pop with "Ts") as "[Tpop _]".
    clear Htid_pop.

    iMod (tgt_interp_as_id _ _ (n:=S (S idx)) with "[St_tgt Mem]") as "St_tgt"; [auto|..].
    2:{ iExists _. iFrame. simpl.
        instantiate (1:=fun '(_, m) => s_memory_black m). simpl.
        red_tl_all. iFrame.
    }
    { simpl. instantiate (1:= (∃ (st : τ{st_tgt_type, S (S idx)}), ⟨Atom.ow_st_tgt st⟩ ∗ (let '(_, m) := st in s_memory_black (n:=S (S idx)) m))%S).
      red_tl. f_equal.
    }
    iDestruct (tgt_interp_as_compose (n:=S (S idx)) (la:=Lens.id) (lb:=sndl) with "St_tgt") as "#TGT_ST".
    { ss. econs. iIntros ([x m]) "MEM". unfold Lens.view. ss. iFrame.
      iIntros (m') "MEM". iFrame.
    }
    iEval (rewrite Lens.left_unit) in "TGT_ST".
    iClear "St_tgt". clear.

    iMod (alloc_obligation_fine 3 6) as (k) "(#Ob_kb & Pc_k & Po_k)".
    iEval (rewrite -Qp.half_half) in "Po_k".
    iDestruct (pending_split _ (1/2) (1/2) with "Po_k") as "(Po_d & Po_p)".
    iDestruct (pc_split _ _ 5 1 with "Pc_k") as "[Pc_k_push Pc_k]".
    iMod (pc_drop _ 1 3 ltac:(auto) 1 with "Pc_k") as "Pc_k"; [lia|].

    iMod (Lifetime.alloc k) as (γk) "live".
    iEval (rewrite -Qp.half_half) in "live".
    iDestruct (Lifetime.pending_split _ (1/2) (1/2) with "live") as "[live_i live_p]".

    iMod (ghost_excl_alloc tt) as (γpop) "Tok".
    iMod (alloc_ElimStack nESMod idx _ 1 2 with "s↦ s.o↦") as (kt γs) "(#IsES & EStack & Pc_kt)".
    iDestruct (pc_split _ _ 1 1 with "Pc_kt") as "[? ?]".

    iMod (duty_add _ _ [] _ 0 (((dead γk k : sProp idx) ∗ push_then_pop_inv idx γs γpop) : sProp idx)%S with "[$Dpush $Po_d $Pc_k] []") as "Dpush".
    { simpl. unfold push_then_pop_inv. red_tl_all.
      rewrite red_syn_inv. iModIntro. iIntros "#$".
    }

    iDestruct (duty_delayed_tpromise with "Dpush") as "#Prm'"; [ss;eauto|].
    iMod (activate_tpromise with "Prm' Po_p") as "[#Prm #Act_k]".
    iClear "Prm'".

    iDestruct (until_tpromise_make1 _ _ _ (((live γk k (1/2) : sProp idx) ∗ EStack idx γs []) : sProp idx)%S with "[live_i EStack]") as "uPrm".
    { simpl. red_tl_all. iFrame "∗". iFrame "Prm". }

    iMod (FUpd_alloc _ _ _ idx nESCli (CState idx γk k γs γpop) with "[uPrm]") as "#CInv"; [lia| |].
    { simpl. unfold CState. red_tl_all. rewrite red_syn_until_tpromise.
      unfold until_thread_promise. simpl. red_tl_all.
      iFrame.
    }

    iModIntro. iExists γk,k,γpop,γs,kt.

    rewrite red_syn_tgt_interp_as. unfold CInv. red_tl_all. iFrame "∗#".
  Qed.

End INITIAL.

End SPEC.
