From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Import pind Axioms ITreeLib Red TRed IRed2 WFLibLarge.
From Fairness Require Import FairBeh Mod Linking.
From Fairness Require Import PCM IProp IPM.
From Fairness Require Import IndexedInvariants OpticsInterp SimWeakest.
From Fairness Require Import TemporalLogic TemporalLogicFull SCMemSpec.

Module Spinlock.

  Section SPINLOCK.

    Variable Client : Mod.t.
    Notation state := (Mod.state Client).
    Notation ident := (Mod.ident Client).

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

Section SIM.

  Variable src_state : Type.
  Variable src_ident : Type.
  Variable Client : Mod.t.
  Variable gvs : list nat.
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
    ((∃ (q : τ{Qp, n}),
         (➢(auex_b_Qp q))
           ∗
           (((x ↦ 0) ∗ ◇[k](l + 1, 1) ∗ ➢(excls r) ∗ ➢(auex_w_Qp q) ∗ P)
            ∨ ((x ↦ 1) ∗ live[k] q ∗ ∃ (u : τ{nat, n}), live[u] (1/2) ∗ (-[u](0)-◇ emp) ∗ (u -(0)-◇ k))))
     ∨ dead[k]
    )%F.

  (* Namespace for Spinlock invariants. *)
  Definition N_Spinlock : namespace := (nroot .@ "Spinlock").

  Definition isSpinlock n (r : nat) (x : SCMem.val) (P : Formula n) (k L l : nat)
    : Formula n :=
    (∃ (N : τ{namespace, n}),
        (⌜(↑N ⊆ (↑N_Spinlock : coPset))⌝)
          ∗ ◆[k, L] ∗ (⌜0 < l⌝) ∗ syn_inv n N (spinlockInv n r x P k l))%F.

  Lemma init_isSpinlock
        n x P k L l (LT : 0 < l)
        q Es
    :
    ⊢
      ⟦(➢(excls_auth) ∗ (x ↦ 0) ∗ ➢(auex_b_Qp q) ∗ ➢(auex_w_Qp q) ∗ (⤉P)
         ∗ ◆[k, L] ∗ ◇[k](l+1, 1))%F, 1+n⟧
        -∗
        ⟦( =|1+n|={Es}=> (➢(excls_auth) ∗ ∃ (r : τ{nat}), ⤉(isSpinlock n r x P k L l)))%F, 1+n⟧.
  Proof.
    red_tl. simpl. iIntros "([% EXA] & PT & BQ & WQ & P & #LO & PC)".
    rewrite red_syn_fupd. red_tl.
    assert (URA.updatable
              ((λ k : nat, if lt_dec k U then ε else (Excl.just () : Excl.t unit)) : ExclUnitsRA)
              (((λ k : nat, if lt_dec k (1+U) then ε else Excl.just ()) : ExclUnitsRA)
                 ⋅
                 (maps_to_res U (Some tt : Excl.t unit) : ExclUnitsRA))).
    { unfold maps_to_res. setoid_rewrite unfold_pointwise_add. apply pointwise_updatable.
      i. ii. unfold URA.wf in *. unseal "ra". ss.
      des_ifs; try lia.
      - rewrite URA.unit_idl. auto.
      - rewrite URA.unit_idl. auto.
      - rewrite URA.unit_id. auto.
    }
    iMod (OwnM_Upd H with "EXA") as "[EXA EX]". clear H.
    iMod ((FUpd_alloc _ _ _ n (↑(N_Spinlock.@"a")) (spinlockInv n U x P k l))
           with "[PT BQ WQ P PC EX]") as "#SINV".
    auto.
    { simpl. unfold spinlockInv. red_tl. iLeft. iExists q. red_tl.
      iSplitL "BQ". iFrame. iLeft. iFrame.
    }
    iModIntro.
    iSplitL "EXA".
    { iExists (1+U). iFrame. }
    iExists U. unfold isSpinlock. red_tl.
    iExists (↑(N_Spinlock.@"a")). red_tl. iSplit.
    { iPureIntro. apply nclose_subseteq. }
    simpl. rewrite red_syn_inv. auto.
  Qed.

  Lemma Spinlock_lock_spec
        tid n
        (Es : coPsets)
        (MASK_TOP : OwnEs_top Es)
        (MASK_STTGT : mask_has_st_tgt Es (1+n))
        (MASK_DISJ : ↑N_Spinlock ## (↑N_state_tgt : coPset))
    :
    ⊢ ∀ r x (P : Formula n) k L l q (ds : list (nat * nat * Formula n)),
        [@ tid, n, Es @]
          ⧼⟦(((syn_tgt_interp_as n sndl (fun m => (➢ (scm_memory_black m))))
                ∗ (⤉ isSpinlock n r x P k L l)
                ∗ live[k] q ∗ (⤉ Duty(tid) ds) ∗ ◇{List.map fst ds}(L, 2))%F
              : Formula (1+n)), 1+n⟧⧽
            (OMod.close_itree Client (SCMem.mod gvs) (Spinlock.lock Client x))
            ⧼rv, ⟦(∃ (u : τ{nat, 1+n}),
                       ➢(excls r) ∗ (⤉ P) ∗ ➢(auex_w_Qp q) ∗
                        (⤉ Duty(tid) ((u, 0, emp) :: ds)) ∗ ◇[u](l, 1))%F, 1+n⟧⧽
  .
  Proof.
    (* simpl. *)
    (* red_tl. iIntros (r). *)
    (* red_tl. iIntros (x). *)
    (* red_tl. iIntros (P). *)
    (* red_tl. iIntros (k). *)
    (* red_tl. iIntros (L). *)
    (* red_tl. iIntros (l). *)
    (* red_tl. iIntros (q). *)
    (* red_tl. iIntros (ds). *)
    iIntros (? ? ? ? ? ? ? ?).
    (* rewrite red_syn_non_atomic_triple. simpl in *. *)
    iStartTriple. iIntros "PRE POST".
    unfold Spinlock.lock.
    (* Preprocess for induction. *)
    iApply wpsim_free_all. auto.
    unfold isSpinlock. ss.
    iEval (red_tl; simpl) in "PRE". iEval (rewrite red_syn_tgt_interp_as) in "PRE".
    iDestruct "PRE" as "(#STINTP & (%N & SL) & LIVE & DUTY & PCS)".
    iEval (red_tl; simpl) in "SL". iDestruct "SL" as "(%IN & #LO & %POS & INV)".
    iEval (rewrite red_syn_inv) in "INV". iPoseProof "INV" as "#INV".
    iMod ((pcs_decr _ _ 1 1 2) with "PCS") as "[PCS PCS2]". ss.
    iMod (ccs_make k L _ 0 with "[PCS2]") as "CCS". iFrame. auto.
    iMod (pcs_drop _ _ _ _ 0 with "PCS") as "PCS". lia.
    (* Set up induction hypothesis. *)
    iRevert "LIVE DUTY PCS POST". iMod (ccs_ind with "CCS []") as "IND".
    2:{ iApply "IND". }
    iModIntro. iExists 0. iIntros "IH". iModIntro. iIntros "LIVE DUTY PCS POST".
    (* Start an iteration. *)
    iEval (rewrite unfold_iter_eq). rred2r.
    iApply (wpsim_yieldR with "[DUTY PCS]").
    2:{ iSplitL "DUTY". iApply "DUTY". iFrame. }
    auto. Unshelve. 2: auto.
    iIntros "DUTY FC". iModIntro. rred2r.
    (* Case analysis on lock variable. *)
    iInv "INV" as "SLI" "SLI_CLOSE". iEval (unfold spinlockInv; simpl; red_tl; simpl) in "SLI".
    iDestruct "SLI" as "[[%q0 SLI] | DEAD]".
    2:{ iExFalso. iPoseProof (not_dead with "[LIVE DEAD]") as "%F". iFrame. auto. }
    iEval (red_tl; simpl) in "SLI". iDestruct "SLI" as "[qISB [ACQ|WAIT]]".

    (** Case 1. Acquire the lock. *)
    { iClear "IH". iDestruct "ACQ" as "(PT & PCk & EXCL & qISW & PROP)".
      iApply (SCMem_cas_fun_spec _ _ _ n with "[PT]"). auto.
      { unfold mask_has_st_tgt. rewrite lookup_insert. clear - MASK_DISJ IN. set_solver. }
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
      iMod (duty_add _ _ _ _ _ 0 (emp%F : Formula n) with "[DUTY PC1] []") as "DUTY".
      { iFrame. }
      { iModIntro. iEval (ss; red_tl). auto. }
      iPoseProof (duty_tpromise with "DUTY") as "#PROM1".
      { simpl. left. auto. }
      iMod (link_new k1 k (l+1) 0 with "[PCk]") as "#LINK1".
      { iFrame. eauto. }
      assert (AUTH: URA.updatable
                      (Auth.black ((Excl.just q0) : Excl.t Qp) ⋅ Auth.white ((Excl.just q0) : Excl.t Qp))
                      (Auth.black ((Some q) : Excl.t Qp) ⋅ Auth.white ((Some q) : Excl.t Qp))).
      { apply Auth.auth_update. ii. des. split.
        - ur. ss.
        - ur in FRAME. ur. des_ifs.
      }
      iCombine "qISB qISW" as "qIS". iMod (OwnM_Upd AUTH with "qIS") as "[qISB qISW]". clear AUTH.
      (* Now close with SLI_CLOSE. *)
      iMod ("SLI_CLOSE" with "[LIVE PT LIVE1' qISB]") as "_".
      { iEval (unfold spinlockInv; simpl; red_tl; simpl).
        iLeft. iExists q. iEval (red_tl; simpl). iSplitL "qISB"; [iFrame|].
        iRight. iFrame. iExists k1. iEval (red_tl; simpl). iFrame. auto.
      }
      (* Finish with POST. *)
      iApply "POST". iEval (red_tl; simpl). iExists k1. iEval (red_tl; simpl).
      iFrame.
    }

    (** Case 2. Miss the lock and loop. *)
    { iDestruct "WAIT" as "(PT & LIVE_SL & %k_other & WAIT)".
      iEval (simpl; red_tl; simpl) in "WAIT". iDestruct "WAIT" as "(LIVE_O & #OATH & #LINK)".
      iApply (SCMem_cas_fun_spec _ _ _ n with "[PT]"). auto.
      { unfold mask_has_st_tgt. rewrite lookup_insert. clear - MASK_DISJ IN. set_solver. }
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
        iLeft. iExists q0. iEval (red_tl; simpl). iSplitL "qISB"; [iFrame|].
        iRight. iFrame. iExists k_other. iEval (red_tl; simpl). iFrame. auto.
      }
      (* Finish with IH. *)
      iApply wpsim_stutter_mon. i; eauto. instantiate (1:=pt). i; auto.
      iApply ("IH" with "LIVE DUTY PCS POST").
    }
  Qed.

  Lemma Spinlock_lock_syn_spec
        tid n
        (Es : coPsets)
        (MASK_TOP : OwnEs_top Es)
        (MASK_STTGT : mask_has_st_tgt Es (1+n))
        (MASK_DISJ : ↑N_Spinlock ## (↑N_state_tgt : coPset))
    :
    ⊢ ⟦(∀ (r : τ{nat})
          (x : τ{SCMem.val})
          (P : τ{Φ, 1+n})
          (k L l : τ{nat})
          (q : τ{Qp})
          (ds : τ{ listT (nat * nat * Φ)%ftype, 1+n}),
        [@ tid, n, Es @]
          ⧼(((syn_tgt_interp_as n sndl (fun m => (➢ (scm_memory_black m))))
                ∗ (⤉ isSpinlock n r x P k L l)
                      ∗ live[k] q ∗ (⤉ Duty(tid) ds) ∗ ◇{List.map fst ds}(L, 2)) : Formula (1+n))⧽
            (OMod.close_itree Client (SCMem.mod gvs) (Spinlock.lock Client x))
            ⧼rv, (∃ (u : τ{nat, 1+n}),
                       ➢(excls r) ∗ (⤉ P) ∗ ➢(auex_w_Qp q) ∗
                        (⤉ Duty(tid) ((u, 0, emp) :: ds)) ∗ ◇[u](l, 1))⧽)%F, 1+n⟧
  .
  Proof.
    simpl.
    red_tl. iIntros (r).
    red_tl. iIntros (x).
    red_tl. iIntros (P).
    red_tl. iIntros (k).
    red_tl. iIntros (L).
    red_tl. iIntros (l).
    red_tl. iIntros (q).
    red_tl. iIntros (ds).
    rewrite red_syn_non_atomic_triple. simpl in *.
    iApply Spinlock_lock_spec. all: auto.
  Qed.


  (* Lemma spinlock_lock_spec2 *)
  (*       n *)
  (*       tid R_src R_tgt (Q : R_src -> R_tgt -> iProp) R G ps pt itr_src ktr_tgt *)
  (*       (* (TOP : OwnEs_top Es) *) *)
  (*       (Es : coPsets) E *)
  (*       (MASK : match Es !! n with Some E' => E ⊆ E' | None => True end) *)
  (*   : *)
  (*   ⊢ *)
  (*   (∀ r x (P : Formula n) k l q (ds : list (nat * nat * Formula n)), *)
  (*       (Duty(tid) ds =|S n|={Es, ∅}=∗ emp%I) *)
  (*       → *)
  (*         (⟦((isSpinlock n E r x P k l) ∗ live(k, q) ∗ Duty(tid) ds ∗ ◇[List.map fst ds @ l](2))%F, n⟧) *)
  (*           -∗ *)
  (*           ((⟦(∃ (u : τ{nat}), (➢(excls r)) ∗ (➢(agree_w_Qp q)) ∗ P ∗ Duty(tid) ((u, l, emp) :: ds) ∗ ◇(u @ l) 1)%F , n⟧) *)
  (*              -∗ *)
  (*              (wpsim (S n) tid ∅ R G Q ps true itr_src (ktr_tgt tt))) *)
  (*           -∗ *)
  (*           wpsim (S n) tid Es R G Q ps pt itr_src *)
  (*           (map_event emb_spinlock (Spinlock.lock x) >>= ktr_tgt)). *)
  (* Proof. *)
  (*   iIntros (? ? ? ? ? ? ?) "CLOSE PRE POST". *)

    (** Invariants. *)
  Definition spinlockInv (n : nat) (r : nat) (x : SCMem.val) (P : Formula n) (k l : nat) : Formula n :=
    ((∃ (q : τ{Qp}),
         (➢(auex_b_Qp q))
           ∗
           (((x ↦ 0) ∗ ◇[k](l + 1, 1) ∗ ➢(excls r) ∗ ➢(auex_w_Qp q) ∗ P)
            ∨ ((x ↦ 1) ∗ live[k] q ∗ ∃ (u : τ{nat}), live[u] (1/2) ∗ (-[u](0)-◇ emp) ∗ (u -(0)-◇ k))))
     ∨ dead[k]
    )%F.

  Definition isSpinlock n (E : coPset) (r : nat) (x : SCMem.val) (P : Formula n) (k L l : nat) : Formula n :=
    (∃ (N : τ{namespace}),
        ⌜(↑N ⊆ E)⌝ ∗ ◆[k, L] ∗ (⌜0 < l⌝) ∗ syn_inv _ N (spinlockInv n r x P k l))%F.


  Lemma Spinlock_lock_spec
        tid n
        (Es : coPsets) (E : coPset)
        (MASK_TOP : OwnEs_top Es)
        (MASK_STTGT : mask_has_st_tgt Es n)
        (MASK_DISJ : E ## ↑N_state_tgt)
    :
    ⊢
      ∀ r x (P : Formula n) k L l q (ds : list (nat * nat * Formula n)),
        [@ tid, (S n), Es @]
          ⧼(⟦((syn_tgt_interp_as n sndl (fun m => (➢ (scm_memory_black m))))
                ∗ ⤉((isSpinlock n E r x P k L l)
                      ∗ live[k] q ∗ Duty(tid) ds ∗ ◇{List.map fst ds}(L, 2)))%F, S n⟧)⧽
            (OMod.close_itree Client (SCMem.mod gvs) (Spinlock.lock Client x))
            ⧼rv, (⟦(∃ (u : τ{nat}),
                       ➢(excls r) ∗ P ∗ ➢(auex_w_Qp q) ∗
                        Duty(tid) ((u, 0, emp) :: ds) ∗ ◇[u](l, 1))%F , n⟧)⧽
  .
  Proof.
    iIntros (? ? ? ? ? ? ? ?). iStartTriple. iIntros "PRE POST".
    unfold Spinlock.lock.
    (* Preprocess for induction. *)
    iApply wpsim_free_all. auto.
    unfold isSpinlock. ss.
    iEval (red_tl; simpl) in "PRE". iEval (rewrite red_syn_tgt_interp_as) in "PRE".
    iDestruct "PRE" as "(#STINTP & (%N & SL) & LIVE & DUTY & PCS)".
    iEval (red_tl; simpl) in "SL". iDestruct "SL" as "(%IN & #LO & %POS & INV)".
    iEval (rewrite red_syn_inv) in "INV". iPoseProof "INV" as "#INV".
    iMod ((pcs_decr _ _ 1 1 2) with "PCS") as "[PCS PCS2]". ss.
    iMod (ccs_make k L _ 0 with "[PCS2]") as "CCS". iFrame. auto.
    iMod (pcs_drop _ _ _ _ 0 with "PCS") as "PCS". lia.
    (* Set up induction hypothesis. *)
    iRevert "LIVE DUTY PCS POST". iMod (ccs_ind with "CCS []") as "IND".
    2:{ iApply "IND". }
    iModIntro. iExists 0. iIntros "IH". iModIntro. iIntros "LIVE DUTY PCS POST".
    (* Start an iteration. *)
    iEval (rewrite unfold_iter_eq). rred2r.
    iApply (wpsim_yieldR with "[DUTY PCS]"). 2: iFrame. auto. Unshelve. 2: auto.
    iIntros "DUTY FC". iModIntro. rred2r.
    (* Case analysis on lock variable. *)
    iInv "INV" as "SLI" "SLI_CLOSE". iEval (unfold spinlockInv; simpl; red_tl; simpl) in "SLI".
    iDestruct "SLI" as "[[%q0 SLI] | DEAD]".
    2:{ iExFalso. iPoseProof (not_dead with "[LIVE DEAD]") as "%F". iFrame. auto. }
    iEval (red_tl; simpl) in "SLI". iDestruct "SLI" as "[qISB [ACQ|WAIT]]".

    (** Case 1. Acquire the lock. *)
    { iClear "IH". iDestruct "ACQ" as "(PT & PCk & EXCL & qISW & PROP)".
      iApply (SCMem_cas_fun_spec _ _ _ n with "[PT]"). auto.
      { unfold mask_has_st_tgt. rewrite lookup_insert. clear - MASK_DISJ IN. set_solver. }
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
      iMod (duty_add _ _ _ _ _ 0 (emp%F : Formula n) with "[DUTY PC1] []") as "DUTY".
      { iFrame. }
      { iModIntro. iEval (ss; red_tl). auto. }
      iPoseProof (duty_tpromise with "DUTY") as "#PROM1".
      { simpl. left. auto. }
      iMod (link_new k1 k (l+1) 0 with "[PCk]") as "#LINK1".
      { iFrame. eauto. }
      assert (AUTH: URA.updatable
                      (Auth.black ((Excl.just q0) : Excl.t Qp) ⋅ Auth.white ((Excl.just q0) : Excl.t Qp))
                      (Auth.black ((Some q) : Excl.t Qp) ⋅ Auth.white ((Some q) : Excl.t Qp))).
      { apply Auth.auth_update. ii. des. split.
        - ur. ss.
        - ur in FRAME. ur. des_ifs.
      }
      iCombine "qISB qISW" as "qIS". iMod (OwnM_Upd AUTH with "qIS") as "[qISB qISW]". clear AUTH.
      (* Now close with SLI_CLOSE. *)
      iMod ("SLI_CLOSE" with "[LIVE PT LIVE1' qISB]") as "_".
      { iEval (unfold spinlockInv; simpl; red_tl; simpl).
        iLeft. iExists q. iEval (red_tl; simpl). iSplitL "qISB"; [iFrame|].
        iRight. iFrame. iExists k1. iEval (red_tl; simpl). iFrame. auto.
      }
      (* Finish with POST. *)
      iApply "POST". iEval (red_tl; simpl). iExists k1. iEval (red_tl; simpl).
      iFrame.
    }

    (** Case 2. Miss the lock and loop. *)
    { iDestruct "WAIT" as "(PT & LIVE_SL & %k_other & WAIT)".
      iEval (simpl; red_tl; simpl) in "WAIT". iDestruct "WAIT" as "(LIVE_O & #OATH & #LINK)".
      iApply (SCMem_cas_fun_spec _ _ _ n with "[PT]"). auto.
      { unfold mask_has_st_tgt. rewrite lookup_insert. clear - MASK_DISJ IN. set_solver. }
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
        iLeft. iExists q0. iEval (red_tl; simpl). iSplitL "qISB"; [iFrame|].
        iRight. iFrame. iExists k_other. iEval (red_tl; simpl). iFrame. auto.
      }
      (* Finish with IH. *)
      iApply wpsim_stutter_mon. i; eauto. instantiate (1:=pt). i; auto.
      iApply ("IH" with "LIVE DUTY PCS POST").
    }
  Qed.

End SIM.
