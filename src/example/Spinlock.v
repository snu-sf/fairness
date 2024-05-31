From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Import pind Axioms ITreeLib Red TRed IRed2 WFLibLarge.
From Fairness Require Import FairBeh Mod Linking.
From Fairness Require Import PCM IProp IPM IPropAux.
From Fairness Require Import IndexedInvariants OpticsInterp SimWeakest.
From Fairness Require Import TemporalLogic TemporalLogicFull SCMemSpec.

Module Spinlock.

  Section SPINLOCK.

    Context {state : Type}.
    Context {ident : ID}.

    Notation unlocked := (SCMem.val_nat 0).
    Notation locked := (SCMem.val_nat 1).

    Definition lock :
      (* ktree (threadE void unit) SCMem.val unit *)
      ktree (threadE ident state) SCMem.val unit
      :=
      fun x =>
        ITree.iter
          (fun (_ : unit) =>
             b <- (OMod.call "cas" (x, unlocked, locked));;
             if (b : bool) then Ret (inr tt) else Ret (inl tt)) tt.

    Definition unlock :
      (* ktree (threadE void unit) SCMem.val unit *)
      ktree (threadE ident state) SCMem.val unit
      :=
      fun x => (OMod.call "store" (x, unlocked)).

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

  End SPINLOCK.

End Spinlock.

Section SPEC.

  Context {src_state : Type}.
  Context {src_ident : Type}.
  Context {Client : Mod.t}.
  Context {gvs : list nat}.
  Notation tgt_state := (OMod.closed_state Client (SCMem.mod gvs)).
  Notation tgt_ident := (OMod.closed_ident Client (SCMem.mod gvs)).

  Local Instance STT : StateTypes := Build_StateTypes src_state tgt_state src_ident tgt_ident.
  (* Notation Formula := (@Formula XAtom STT). *)
  Context `{Σ : GRA.t}.
  Context {TLRAS : @TLRAs XAtom STT Σ}.
  Context {AUXRAS : AUXRAs Σ}.

  (*
Liveness chain of a spinlock : 
(Holder needs one ◇ at l (> 0) = Holder will unlock @ l + 1)
<
(Spinlock will end @ L)
<
(Other duties of tid @ ? < L)
   *)

  (** Invariants. *)
  Definition spinlockInv (n : nat) (r : nat) (x : SCMem.val) (P : Formula n) (k l : nat)
    : Formula n :=
    ((∃ (q : τ{Qp}) (u : τ{nat}),
         ➢(@auexa_b r (Qp * nat)%type (q, u))
          ∗
          (((x ↦ 0) ∗ ◇[k](l + 1, 1) ∗ ➢(@auexa_w r (Qp * nat)%type (q, u)) ∗ P)
           ∨ ((x ↦ 1) ∗ live[k] q ∗ live[u] (1/2) ∗ (-[u](0)-◇ emp) ∗ (u -(0)-◇ k))))
     ∨ dead[k]
    )%F.

  (* Namespace for Spinlock invariants. *)
  Definition N_Spinlock : namespace := (nroot .@ "Spinlock").

  Definition isSpinlock n (r : nat) (x : SCMem.val) (P : Formula n) (k L l : nat)
    : Formula n :=
    (∃ (N : τ{namespace, n}),
        (⌜(↑N ⊆ (↑N_Spinlock : coPset))⌝)
          ∗ ◆[k, L] ∗ (⌜0 < l⌝) ∗ syn_inv n N (spinlockInv n r x P k l))%F.

  Global Instance isSpinlock_persistent n r x P k L l : Persistent (⟦isSpinlock n r x P k L l, n⟧).
  Proof.
    unfold Persistent. iIntros "H". unfold isSpinlock. red_tl.
    iDestruct "H" as "[%N H]". iExists N. red_tl. rewrite red_syn_inv.
    iDestruct "H" as "#H". auto.
  Qed.

  Definition mask_has_Spinlock (Es : coPsets) n :=
    (match Es !! n with Some E => (↑N_Spinlock) ⊆ E | None => True end).

  Lemma mask_disjoint_spinlock_state_tgt : ↑N_Spinlock ## (↑N_state_tgt : coPset).
  Proof. apply ndot_ne_disjoint. ss. Qed.

  Lemma make_isSpinlock
        n r x P k L l (LT : 0 < l)
        (q : Qp) (u : nat) Es
    :
    ⊢
      ⟦((x ↦ 0) ∗ ➢(auexa_b r (q, u)) ∗ ➢(auexa_w r (q, u)) ∗ (⤉P) ∗ ◆[k, L] ∗ ◇[k](l+1, 1))%F, 1+n⟧
        -∗
        ⟦( =|1+n|={Es}=> (⤉(isSpinlock n r x P k L l)))%F, 1+n⟧.
  Proof.
    red_tl. simpl. iIntros "(PT & BQ & WQ & P & #LO & PC)".
    rewrite red_syn_fupd. red_tl.
    iMod ((FUpd_alloc _ _ _ n (↑(N_Spinlock.@"a")) (spinlockInv n r x P k l))
           with "[PT BQ WQ P PC]") as "#SINV".
    auto.
    { simpl. unfold spinlockInv. red_tl. iLeft. iExists q. red_tl. iExists u. red_tl.
      iSplitL "BQ". iFrame. iLeft. iFrame.
    }
    iModIntro. unfold isSpinlock. red_tl.
    iExists (↑(N_Spinlock.@"a")). red_tl. iSplit.
    { iPureIntro. apply nclose_subseteq. }
    simpl. rewrite red_syn_inv. auto.
  Qed.

  Lemma init_isSpinlock
        n x P k L l (LT : 0 < l)
        Es
    :
    ⊢
      ⟦(➢(auexa) ∗ (x ↦ 0) ∗ (⤉P) ∗ ◆[k, L] ∗ ◇[k](l+1, 1))%F, 1+n⟧
        -∗
        ⟦( =|1+n|={Es}=> (➢(auexa) ∗ ∃ (r : τ{nat}), ⤉(isSpinlock n r x P k L l)))%F, 1+n⟧.
  Proof.
    red_tl. simpl. iIntros "(AEA & PT & P & #LO & PC)".
    rewrite red_syn_fupd. red_tl.
    iMod (auexa_alloc _ ((1%Qp, 0)) with "AEA") as "[AEA (%r & BQ & BW)]".
    iPoseProof (make_isSpinlock n r x P k L l with "[PT BQ BW P PC]") as "ISL".
    auto.
    { red_tl. iFrame. iApply "LO". }
    iEval (rewrite red_syn_fupd) in "ISL". iMod "ISL".
    iModIntro. iSplitL "AEA". iFrame.
    iExists r. iFrame.
  Qed.

  Lemma update_isSpinlock
        n r x P k L l
        Es
        (MASK_SL : mask_has_Spinlock Es n)
        k' L' l' (LT' : 0 < l')
    :
    ⊢⟦((⤉(isSpinlock n r x P k L l)) ∗ live[k] 1 ∗ ◆[k', L'] ∗ ◇[k'](l' + 1, 1))%F, 1+n⟧
       -∗
       ⟦( =|1+n|={Es}=>((⤉ isSpinlock n r x P k' L' l') ∗ dead[k]))%F, 1+n⟧.
  Proof.
    red_tl. simpl. iIntros "(ISL & LIVE & LO' & PC')". rewrite red_syn_fupd. red_tl.
    iEval (unfold isSpinlock) in "ISL". red_tl.
    iDestruct "ISL" as "[%N ISL]". iEval red_tl in "ISL".
    iDestruct "ISL" as "(%IN & _ & %LT & SI)". rewrite red_syn_inv.
    iInv "SI" as "SI" "K".
    { unfold mask_has_Spinlock in MASK_SL. des_ifs. set_solver. }
    simpl. iEval (unfold spinlockInv; red_tl) in "SI".
    iDestruct "SI" as "[[%q SI] | DEAD]".
    2:{ iExFalso. simpl. iPoseProof (not_dead with "[LIVE DEAD]") as "F". iFrame. auto. }
    red_tl. iDestruct "SI" as "[%u SI]".
    red_tl. iDestruct "SI" as "[BQ [(PT & _ & WQ & P) | (_ & LIVE2 & _)]]".
    2:{ iPoseProof (live_merge with "[LIVE2 LIVE]") as "LIVE". iFrame.
        iPoseProof (live_wf with "LIVE") as "%F". exfalso. eapply Qp_add_lt_one. eauto.
    }
    iMod (kill with "LIVE") as "#DEAD". iMod ("K" with "[DEAD]") as "_".
    { unfold spinlockInv. red_tl. iRight. eauto. }
    iPoseProof (make_isSpinlock n r x P k' L' l' LT' with "[PT BQ WQ P LO' PC']") as "ISL".
    { red_tl. iFrame. }
    rewrite red_syn_fupd. iMod "ISL".
    iModIntro. iFrame. auto.
  Qed.

  Lemma Spinlock_lock_spec
        tid n
        (Es : coPsets)
        (MASK_TOP : OwnEs_top Es)
        (MASK_STTGT : mask_has_st_tgt Es n)
    :
    ⊢ ∀ r x (P : Formula n) k L l q (ds : list (nat * nat * Formula n)),
        [@ tid, n, Es @]
          ⧼⟦(((syn_tgt_interp_as n sndl (fun m => (➢ (scm_memory_black m))))
                ∗ (⤉ isSpinlock n r x P k L l)
                ∗ live[k] q ∗ (⤉ Duty(tid) ds)
                ∗ ◇{List.map fst ds}(L, 1) ∗ ◇{List.map fst ds}(0, 1))%F), 1+n⟧⧽
            (OMod.close_itree Client (SCMem.mod gvs) (Spinlock.lock x))
            ⧼rv, ⟦(∃ (u : τ{nat, 1+n}),
                      (⤉ P) ∗ ➢(auexa_w r (((q/2)%Qp, u) : Qp * nat)) ∗ live[k] (q/2)
                       ∗ (⤉ Duty(tid) ((u, 0, emp) :: ds)) ∗ live[u] (1/2) ∗ ◇[u](l, 1))%F, 1+n⟧⧽
  .
  Proof.
    iIntros (? ? ? ? ? ? ? ?).
    iStartTriple. iIntros "PRE POST". unfold Spinlock.lock.
    (* Preprocess for induction. *)
    iApply wpsim_free_all. auto.
    unfold isSpinlock. ss.
    iEval (red_tl; simpl) in "PRE". iEval (rewrite red_syn_tgt_interp_as) in "PRE".
    iDestruct "PRE" as "(#STINTP & (%N & SL) & LIVE & DUTY & PCS2 & PCS)".
    iEval (red_tl; simpl) in "SL". iDestruct "SL" as "(%IN & #LO & %POS & INV)".
    iEval (rewrite red_syn_inv) in "INV". iPoseProof "INV" as "#INV".
    (* iMod ((pcs_decr _ _ 1 1 2) with "PCS") as "[PCS PCS2]". ss. *)
    iMod (ccs_make k L _ 0 with "[PCS2]") as "CCS". iFrame. auto.
    (* iMod (pcs_drop _ _ _ _ 0 with "PCS") as "PCS". lia. *)
    (* Set up induction hypothesis. *)
    iRevert "LIVE DUTY PCS POST". iMod (ccs_ind with "CCS []") as "IND".
    2:{ iApply "IND". }
    iModIntro. iExists 0. iIntros "IH". iModIntro. iIntros "LIVE DUTY PCS POST".
    (* Start an iteration. *)
    iEval (rewrite unfold_iter_eq). rred2r.
    (* iApply wpsim_free_all. auto. *)
    iApply (wpsim_yieldR with "[DUTY PCS]").
    2:{ iSplitL "DUTY". iApply "DUTY". iFrame. }
    auto.
    iIntros "DUTY FC". iModIntro. rred2r.
    (* Case analysis on lock variable. *)
    iInv "INV" as "SLI" "SLI_CLOSE". iEval (unfold spinlockInv; simpl; red_tl; simpl) in "SLI".
    iDestruct "SLI" as "[[%q0 SLI] | DEAD]".
    2:{ iExFalso. iPoseProof (not_dead with "[LIVE DEAD]") as "%F". iFrame. auto. }
    iEval (red_tl; simpl) in "SLI". iDestruct "SLI" as "[%u0 SLI]".
    iEval (red_tl; simpl) in "SLI". iDestruct "SLI" as "[qISB [ACQ|WAIT]]".

    (** Case 1. Acquire the lock. *)
    { iClear "IH". iDestruct "ACQ" as "(PT & PCk & qISW & PROP)".
      iApply (SCMem_cas_fun_spec _ _ _ n with "[PT]"). auto.
      { unfold mask_has_st_tgt. rewrite lookup_insert. pose mask_disjoint_spinlock_state_tgt. clear - d IN. set_solver. }
      { iFrame. iApply tgt_interp_as_equiv. 2: iApply "STINTP".
        iIntros. iEval (simpl; red_tl; simpl). iSplit; iIntros "P".
        - iFrame. ss.
        - iDestruct "P" as "[MB _]". iFrame.
      }
      iIntros (b) "(%u & %RES & PT)". destruct (SCMem.val_eq_dec 0 0).
      2:{ exfalso. ss. }
      clear e. des. subst. rred2r. iApply wpsim_tauR. rred2r.
      (* Close the invariant spinlockInv: *)
      (* 1. Allocate new obligation: I will release the lock. *)
      iMod (alloc_obligation (l + 1)) as "(%k1 & #LO1 & PC1 & LIVE1)".
      (* 2. Preprocess. *)
      iPoseProof (live_split _ (1/2)%Qp (1/2)%Qp with "[LIVE1]") as "[LIVE1 LIVE1']".
      { iEval (rewrite Qp.half_half). iFrame. }
      iMod (pc_drop _ l _ _ (1+1) _ with "PC1") as "PC1". auto. Unshelve. 2: lia.
      iPoseProof (pc_split with "PC1") as "[PC1 PC_POST]".
      iMod (pc_mon _ 1 _ (0+1) _ _ with "PC1") as "PC1". Unshelve.
      2:{ apply layer_drop_eq; auto. }
      iMod (duty_add _ _ _ _ 0 (emp%F : Formula n) with "[DUTY PC1] []") as "DUTY".
      { iFrame. }
      { iModIntro. iEval (ss; red_tl). auto. }
      iPoseProof (duty_tpromise with "DUTY") as "#PROM1".
      { simpl. left. auto. }
      iMod (link_new k1 k (l+1) 0 with "[PCk]") as "#LINK1".
      { iFrame. eauto. }
      iPoseProof ((live_split k (q/2)%Qp (q/2)%Qp) with "[LIVE]") as "[MYLIVE LIVE]".
      { rewrite Qp.div_2. iFrame. }
      iMod (auexa_b_w_update with "qISB qISW") as "[qISB qISW]".
      (* Now close with SLI_CLOSE. *)
      iMod ("SLI_CLOSE" with "[LIVE PT LIVE1' qISB]") as "_".
      { iEval (unfold spinlockInv; simpl; red_tl; simpl).
        iLeft. iExists (q/2)%Qp. iEval (red_tl; simpl). iExists k1. iEval (red_tl; simpl).
        iSplitL "qISB"; [iFrame|].
        iRight. iFrame. auto.
      }
      (* Finish with POST. *)
      iApply "POST". iEval (red_tl; simpl). iExists k1. iEval (red_tl; simpl).
      iFrame.
    }

    (** Case 2. Miss the lock and loops. *)
    { iDestruct "WAIT" as "(PT & LIVE_SL & LIVE_O & #OATH & #LINK)".
      iApply (SCMem_cas_fun_spec _ _ _ n with "[PT]"). auto.
      { unfold mask_has_st_tgt. rewrite lookup_insert. pose mask_disjoint_spinlock_state_tgt. clear - d IN. set_solver. }
      { iFrame. iApply tgt_interp_as_equiv. 2: iApply "STINTP".
        iIntros. iEval (simpl; red_tl; simpl). iSplit; iIntros "P".
        - iFrame. ss.
        - iDestruct "P" as "[MB _]". iFrame.
      }
      iIntros (b) "(%u & %RES & PT)". destruct (SCMem.val_eq_dec 1 0).
      { exfalso. ss. }
      clear n0. des. subst. rred2r. iApply wpsim_tauR. rred2r. iApply wpsim_tauR.
      (* Get credits from IH and the invariant. *)
      iMod (tpromise_progress with "[FC]") as "[PC | [DEAD _]]".
      { iFrame. iApply "OATH". }
      2:{ iExFalso. iPoseProof (not_dead with "[LIVE_O DEAD]") as "%FALSE". iFrame. auto. }
      iMod (link_amplify with "[PC]") as "PC".
      { iFrame. iApply "LINK". }
      iMod ("IH" with "PC") as "[PCS IH]". auto.
      (* Close the invariant spinlockInv. *)
      iMod ("SLI_CLOSE" with "[qISB LIVE_SL LIVE_O PT]") as "_".
      { iEval (unfold spinlockInv; simpl; red_tl; simpl).
        iLeft. iExists q0. iEval (red_tl; simpl). iExists u0. iEval (red_tl; simpl).
        iSplitL "qISB"; [iFrame|].
        iRight. iFrame. auto.
      }
      (* Finish with IH. *)
      iApply wpsim_stutter_mon. i; eauto. instantiate (1:=pt). i; auto.
      iApply ("IH" with "LIVE DUTY PCS POST").
    }
  Qed.

  Lemma red_syn_Spinlock_lock_spec
        tid n
        (Es : coPsets)
    :
    ⟦(∀ (r : τ{nat})
        (x : τ{SCMem.val})
        (P : τ{Φ, 1+n})
        (k L l : τ{nat})
        (q : τ{Qp})
        (ds : τ{ listT (nat * nat * Φ)%ftype, 1+n})
       ,
         [@ tid, n, Es @]
           ⧼((syn_tgt_interp_as n sndl (fun m => (➢ (scm_memory_black m))))
                ∗ (⤉ isSpinlock n r x P k L l)
                ∗ live[k] q ∗ (⤉ Duty(tid) ds)
                ∗ ◇{List.map fst ds}(L, 1) ∗ ◇{List.map fst ds}(0, 1))⧽
             (OMod.close_itree Client (SCMem.mod gvs) (Spinlock.lock x))
             ⧼rv, (∃ (u : τ{nat, 1+n}),
                      (⤉ P) ∗ ➢(auexa_w r (((q/2)%Qp, u) : Qp * nat)) ∗ live[k] (q/2)
                            ∗ (⤉ Duty(tid) ((u, 0, emp) :: ds)) ∗ live[u] (1/2) ∗ ◇[u](l, 1))⧽)%F, 1+n⟧
    =
      (∀ r x (P : Formula n) k L l q (ds : list (nat * nat * Formula n)),
          [@ tid, n, Es @]
            ⧼⟦((syn_tgt_interp_as n sndl (fun m => (➢ (scm_memory_black m))))
                  ∗ (⤉ isSpinlock n r x P k L l)
                  ∗ live[k] q ∗ (⤉ Duty(tid) ds)
                  ∗ ◇{List.map fst ds}(L, 1) ∗ ◇{List.map fst ds}(0, 1))%F, 1+n⟧⧽
              (OMod.close_itree Client (SCMem.mod gvs) (Spinlock.lock x))
              ⧼rv, ⟦(∃ (u : τ{nat, 1+n}),
                        (⤉ P) ∗ ➢(auexa_w r (((q/2)%Qp, u) : Qp * nat)) ∗ live[k] (q/2)
                              ∗ (⤉ Duty(tid) ((u, 0, emp) :: ds)) ∗ live[u] (1/2) ∗ ◇[u](l, 1))%F, 1+n⟧⧽)%I
  .
  Proof.
    simpl.
    red_tl. apply f_equal. extensionalities r.
    red_tl. apply f_equal. extensionalities x.
    red_tl. apply f_equal. extensionalities P.
    red_tl. apply f_equal. extensionalities k.
    red_tl. apply f_equal. extensionalities L.
    red_tl. apply f_equal. extensionalities l.
    red_tl. apply f_equal. extensionalities q.
    red_tl. apply f_equal. extensionalities ds.
    apply red_syn_non_atomic_triple.
  Qed.

  Lemma Spinlock_lock_syn_spec
        tid n
        (Es : coPsets)
        (MASK_TOP : OwnEs_top Es)
        (MASK_STTGT : mask_has_st_tgt Es n)
    :
    ⊢ ⟦(∀ (r : τ{nat})
          (x : τ{SCMem.val})
          (P : τ{Φ, 1+n})
          (k L l : τ{nat})
          (q : τ{Qp})
          (ds : τ{ listT (nat * nat * Φ)%ftype, 1+n})
         ,
           [@ tid, n, Es @]
             ⧼((syn_tgt_interp_as n sndl (fun m => (➢ (scm_memory_black m))))
                  ∗ (⤉ isSpinlock n r x P k L l)
                  ∗ live[k] q ∗ (⤉ Duty(tid) ds)
                  ∗ ◇{List.map fst ds}(L, 1) ∗ ◇{List.map fst ds}(0, 1))⧽
               (OMod.close_itree Client (SCMem.mod gvs) (Spinlock.lock x))
               ⧼rv, (∃ (u : τ{nat, 1+n}),
                        (⤉ P) ∗ ➢(auexa_w r (((q/2)%Qp, u) : Qp * nat)) ∗ live[k] (q/2)
                              ∗ (⤉ Duty(tid) ((u, 0, emp) :: ds)) ∗ live[u] (1/2) ∗ ◇[u](l, 1))⧽)%F, 1+n⟧
  .
  Proof.
    rewrite red_syn_Spinlock_lock_spec. iApply Spinlock_lock_spec. all: auto.
  Qed.

  Lemma Spinlock_unlock_spec
        tid n
        (Es : coPsets)
        (MASK_TOP : OwnEs_top Es)
        (MASK_STTGT : mask_has_st_tgt Es n)
    :
    ⊢ ∀ r x (P : Formula n) k L l q (ds : list (nat * nat * Formula n)) u,
        [@ tid, n, Es @]
          ⧼⟦(((syn_tgt_interp_as n sndl (fun m => (➢ (scm_memory_black m))))
                ∗ (⤉ isSpinlock n r x P k L l) ∗ (⤉ P)
                ∗ ➢(auexa_w r (((q/2)%Qp, u) : Qp * nat)) ∗ live[k] (q/2)
                ∗ (⤉ Duty(tid) ((u, 0, emp) :: ds)) ∗ live[u] (1/2)
                ∗ ◇{List.map fst ((u, 0, emp) :: ds)}(0, 1)
                ∗ ◇[k](l + 1, 1)))%F, 1+n⟧⧽
            (OMod.close_itree Client (SCMem.mod gvs) (Spinlock.unlock x))
            ⧼rv, ⟦((⤉ Duty(tid) ds) ∗ live[k] q)%F, 1+n⟧⧽
  .
  Proof.
    iIntros (? ? ? ? ? ? ? ? ?).
    iStartTriple. iIntros "PRE POST". unfold Spinlock.unlock.
    (* Preprocess. *)
    iApply wpsim_free_all. auto.
    unfold isSpinlock. ss.
    iEval (red_tl; simpl) in "PRE". iEval (rewrite red_syn_tgt_interp_as) in "PRE".
    iDestruct "PRE" as "(#STINTP & (%N & SL) & P & WQ & LIVE & DUTY & LIVEU & PCS & PCk)".
    iEval (red_tl; simpl) in "SL". iDestruct "SL" as "(%IN & #LO & %POS & INV)".
    iEval (rewrite red_syn_inv) in "INV". iPoseProof "INV" as "#INV".
    rred2r. iApply (wpsim_yieldR with "[DUTY PCS]").
    2:{ iSplitL "DUTY". iFrame. iFrame. }
    auto.
    iIntros "DUTY FC". iModIntro.
    (* Open invariant. *)
    iInv "INV" as "SLI" "SLI_CLOSE". iEval (unfold spinlockInv; simpl; red_tl; simpl) in "SLI".
    iDestruct "SLI" as "[[%q0 SLI] | DEAD]".
    2:{ iExFalso. iPoseProof (not_dead with "[LIVE DEAD]") as "%F". iFrame. auto. }
    iEval (red_tl; simpl) in "SLI". iDestruct "SLI" as "[%u0 SLI]".
    iEval (red_tl; simpl) in "SLI". iDestruct "SLI" as "[BQ [ACQ | WAIT]]".
    { iExFalso. iDestruct "ACQ" as "(_ & _ & WQ2 & _)".
      iPoseProof (auexa_w_w_false with "WQ WQ2") as "%F". inv F.
    }
    iDestruct "WAIT" as "(PT & LIVE2 & LIVEU2 & _)". rred2r.
    (* Proceed simulation. *)
    iApply (SCMem_store_fun_spec _ _ _ n with "[PT]"). auto.
    { rewrite lookup_insert. pose mask_disjoint_spinlock_state_tgt. clear - d IN. set_solver. }
    { iFrame. auto. }
    iIntros (rv) "PT". rred2r. destruct rv. iApply wpsim_tauR. rred2r.
    (* Close invariant. *)
    iPoseProof (auexa_b_w_eq with "BQ WQ") as "%EQ". clarify.
    iMod ("SLI_CLOSE" with "[P WQ PCk BQ PT]") as "_".
    { simpl. iEval (unfold spinlockInv). red_tl. iLeft.
      iExists (q/2)%Qp. red_tl. iExists u. red_tl. iSplitL "BQ". iFrame. iLeft. iFrame.
    }
    (* Postconditions. *)
    iMod (kill with "[LIVEU LIVEU2]") as "DEADU".
    { iEval (rewrite <- Qp.half_half). iApply live_merge. iFrame. }
    iMod (duty_fulfill with "[DUTY DEADU]") as "DUTY".
    { iFrame. }
    iPoseProof (live_merge with "[LIVE LIVE2]") as "LIVE". iFrame. iEval (rewrite Qp.div_2) in "LIVE".
    iApply "POST". red_tl. iFrame.
  Qed.

  Lemma red_syn_Spinlock_unlock_spec
        tid n
        (Es : coPsets)
    :
    ⟦(∀ (r : τ{nat})
        (x : τ{SCMem.val})
        (P : τ{Φ, 1+n})
        (k L l : τ{nat})
        (q : τ{Qp})
        (ds : τ{ listT (nat * nat * Φ)%ftype, 1+n})
        (u : τ{nat, 1+n})
       ,
         [@ tid, n, Es @]
           ⧼((syn_tgt_interp_as n sndl (fun m => (➢(scm_memory_black m))))
               ∗ (⤉ isSpinlock n r x P k L l) ∗ (⤉ P)
               ∗ ➢(auexa_w r (((q/2)%Qp, u) : Qp * nat)) ∗ live[k] (q/2)
               ∗ (⤉ Duty(tid) ((u, 0, emp) :: ds)) ∗ live[u] (1/2)
               ∗ ◇{List.map fst ((u, 0, emp) :: ds)}(0, 1)
               ∗ ◇[k](l + 1, 1))⧽
             (OMod.close_itree Client (SCMem.mod gvs) (Spinlock.unlock x))
             ⧼rv, ((⤉ Duty(tid) ds) ∗ live[k] q)⧽)%F, 1+n⟧
    =
      (∀ r x (P : Formula n) k L l q (ds : list (nat * nat * Formula n)) u,
          [@ tid, n, Es @]
            ⧼⟦(((syn_tgt_interp_as n sndl (fun m => (➢ (scm_memory_black m))))
                  ∗ (⤉ isSpinlock n r x P k L l) ∗ (⤉ P)
                  ∗ ➢(auexa_w r (((q/2)%Qp, u) : Qp * nat)) ∗ live[k] (q/2)
                  ∗ (⤉ Duty(tid) ((u, 0, emp) :: ds)) ∗ live[u] (1/2)
                  ∗ ◇{List.map fst ((u, 0, emp) :: ds)}(0, 1)
                  ∗ ◇[k](l + 1, 1)))%F, 1+n⟧⧽
              (OMod.close_itree Client (SCMem.mod gvs) (Spinlock.unlock x))
              ⧼rv, ⟦((⤉ Duty(tid) ds) ∗ live[k] q)%F, 1+n⟧⧽)%I
  .
  Proof.
    (* simpl. *)
    red_tl. apply f_equal. extensionalities r.
    red_tl. apply f_equal. extensionalities x.
    red_tl. apply f_equal. extensionalities P.
    red_tl. apply f_equal. extensionalities k.
    red_tl. apply f_equal. extensionalities L.
    red_tl. apply f_equal. extensionalities l.
    red_tl. apply f_equal. extensionalities q.
    red_tl. apply f_equal. extensionalities ds.
    rewrite @red_tl_univ. apply f_equal. extensionalities u.
    apply red_syn_non_atomic_triple.
  Qed.

  Lemma Spinlock_unlock_syn_spec
        tid n
        (Es : coPsets)
        (MASK_TOP : OwnEs_top Es)
        (MASK_STTGT : mask_has_st_tgt Es n)
    :
    ⊢ ⟦(∀ (r : τ{nat})
          (x : τ{SCMem.val})
          (P : τ{Φ, 1+n})
          (k L l : τ{nat})
          (q : τ{Qp})
          (ds : τ{ listT (nat * nat * Φ)%ftype, 1+n})
          (u : τ{nat, 1+n})
         ,
           [@ tid, n, Es @]
             ⧼((syn_tgt_interp_as n sndl (fun m => (➢(scm_memory_black m))))
                 ∗ (⤉ isSpinlock n r x P k L l) ∗ (⤉ P)
                 ∗ ➢(auexa_w r (((q/2)%Qp, u) : Qp * nat)) ∗ live[k] (q/2)
                 ∗ (⤉ Duty(tid) ((u, 0, emp) :: ds)) ∗ live[u] (1/2)
                 ∗ ◇{List.map fst ((u, 0, emp) :: ds)}(0, 1)
                 ∗ ◇[k](l + 1, 1))⧽
               (OMod.close_itree Client (SCMem.mod gvs) (Spinlock.unlock x))
               ⧼rv, ((⤉ Duty(tid) ds) ∗ live[k] q)⧽)%F, 1+n⟧
  .
  Proof.
    rewrite red_syn_Spinlock_unlock_spec. iApply Spinlock_unlock_spec. all: auto.
  Qed.

End SPEC.
Global Opaque Spinlock.lock Spinlock.unlock.
