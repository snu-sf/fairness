From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Import pind Axioms ITreeLib Red TRed IRed2 WFLibLarge.
From Fairness Require Import FairBeh Mod Linking.
From Fairness Require Import Spinlock.
From Fairness Require Import PCM IProp IPM IPropAux.
From Fairness Require Import IndexedInvariants OpticsInterp SimWeakest.
From Fairness Require Import TemporalLogic SCMemSpec.
From Fairness Require Import OneShotsRA AuthExclsRA ExclsRA.

Section SPEC.

  Context {src_state : Type}.
  Context {src_ident : Type}.
  Context {Client : Mod.t}.
  Context {gvs : list nat}.
  Notation tgt_state := (OMod.closed_state Client (SCMem.mod gvs)).
  Notation tgt_ident := (OMod.closed_ident Client (SCMem.mod gvs)).

  Local Instance STT : StateTypes := Build_StateTypes src_state tgt_state src_ident tgt_ident.

  Context `{sub : @SRA.subG Γ Σ}.
  Context {TLRASs : TLRAs_small STT Γ}.
  Context {TLRAS : TLRAs STT Γ Σ}.

  Context {HasMEMRA: @GRA.inG memRA Γ}.
  Context {HasOneShots : @GRA.inG (OneShots.t unit) Γ}.
  (* Context {HasAuthExcl : @GRA.inG (AuthExcls.t nat) Γ}. *)
  Context {HasAuthExcl2 : @GRA.inG (AuthExcls.t (nat * nat)) Γ}.
  Context {HasExcls : @GRA.inG (Excls.t unit) Γ}.

  Ltac red_tl_all := red_tl; red_tl_memra; red_tl_authexcls; red_tl_excls; red_tl_oneshots.

  Context (spinlockN : namespace) `{DISJ: (↑N_state_tgt :coPset) ## (↑spinlockN : coPset)}.

  (** Invariants. *)
  Definition spinlockInv (n : nat) κs (x : SCMem.val) (γx γl : nat) (P : sProp n)
    : sProp n :=
    (∃ (γκu κu : τ{nat}),
        (● γl (γκu, κu))
          ∗
          (((x ↦ 0) ∗ (○ γl (γκu, κu)) ∗ P)
           ∨ ((x ↦ 1) ∗ (△ γκu 1) ∗ (-[κu](0)-◇ (▿ γκu tt)) ∗ (κu -(0)-◇ κs)))
    )%S.
  (* Definition spinlockInv (n : nat) κs (x : SCMem.val) (γx γl : nat) (P : sProp n) *)
  (*   : sProp n := *)
  (*   (∃ (l γκu κu : τ{nat}), *)
  (*       ((x ↦ l) ∗ (● γx l) ∗ (● γl (γκu, κu))) *)
  (*         ∗ *)
  (*         ((⌜l = 0⌝ ∗ (○ γl (γκu, κu)) ∗ P) *)
  (*          ∨ (⌜l = 1⌝ ∗ (△ γκu 1) ∗ (-[κu](0)-◇ (▿ γκu tt)) ∗ (κu -(0)-◇ κs))) *)
  (*   )%S. *)

  Definition isSpinlock n κs (x : SCMem.val) (γx γl : nat) (P : sProp n) (ℓL μn : nat)
    : sProp n :=
    (◆[κs, ℓL, μn] ∗ syn_inv n spinlockN (spinlockInv n κs x γx γl P))%S.

  Global Instance isSpinlock_persistent n κs (x : SCMem.val) (γx γl : nat) (P : sProp n) ℓL μn :
    Persistent (⟦isSpinlock n κs x γx γl P ℓL μn, n⟧).
  Proof.
    unfold Persistent. iIntros "H". unfold isSpinlock. red_tl.
    rewrite red_syn_inv. iDestruct "H" as "#H". auto.
  Qed.

  Lemma isSpinlock_unfold
        n κs (x : SCMem.val) (γx γl : nat) (P : sProp n) (ℓL μn : nat)
    :
    ⟦(isSpinlock n κs x γx γl P ℓL μn), n⟧
      ⊢ (◆[κs, ℓL, μn] ∗ inv n spinlockN (spinlockInv n κs x γx γl P))%I.
  Proof.
    unfold isSpinlock. red_tl. rewrite red_syn_inv. iIntros "[A B]". iFrame.
  Qed.

  Lemma pass_lock
        n κs (x : SCMem.val) (γx γl : nat) (P : sProp n) (ℓL μn : nat)
        tid γκu κu ϕ
        ℓl μa γκu' κu'
        E
        (SUB : (↑spinlockN) ⊆ E)
    :
    ⊢
      (⟦((isSpinlock n κs x γx γl P ℓL μn)
           ∗ (○ γl (γκu, κu)) ∗ (Duty(tid) ((κu, 0, ▿ γκu tt) :: ϕ))
           ∗ ◇[κs](ℓl, μa)
           ∗ ◆[κu', ℓl, μa] ∗ ⧖[κu', (1/2)] ∗ (△ γκu' 1) ∗ (-[κu'](0)-⧖ (▿ γκu' tt))
        )%S, n⟧)
      =|1+n|=(⟦syn_fairI (1+n), 1+n⟧)={E}=∗ (⟦((○ γl (γκu', κu')) ∗ (Duty(tid) ϕ) ∗ (▿ γκu tt) ∗ (⋈[κu']))%S, n⟧).
  Proof.
    rewrite red_syn_fairI. red_tl_all. simpl.
    iIntros "(#ISL & LK & DUTY & PCs & #LOu' & POu' & PENDu' & DPu')".
    iPoseProof (isSpinlock_unfold with "ISL") as "[_ #INV_SL]".
    iInv "INV_SL" as "SL" "INV_SL_CL".
    iEval (simpl; unfold spinlockInv; red_tl_all) in "SL".
    iDestruct "SL" as "[%γκu0 SL]". iEval (red_tl) in "SL".
    iDestruct "SL" as "[%κu0 SL]". iEval (red_tl) in "SL".
    iEval (red_tl_all; simpl) in "SL".
    iDestruct "SL" as "(LKb & CASES)".
    iPoseProof (AuthExcls.b_w_eq with "LKb LK") as "%EQ". inv EQ.
    iDestruct "CASES" as "[(_ & LK2 & _) | (PTx & PENDu & PRu & LINKu)]".
    { iExFalso. iPoseProof (AuthExcls.w_w_false with "LK LK2") as "%F". inv F. }
    iMod (OneShots.pending_shot _ tt with "PENDu") as "#SHOTu".
    iPoseProof (unfold_tpromise with "PRu") as "[_ #ACTu]".
    iMod (duty_fulfill with "[DUTY]") as "DUTY".
    { iFrame. iEval (simpl; red_tl_all). auto. }
    iMod (activate_tpromise with "DPu' POu'") as "[#PRu' ACTu']".
    iMod (link_new_fine _ _ _ _ 0 with "[PCs]") as "#LINKu'".
    { iSplitR. iApply "LOu'". iFrame. }
    iMod (AuthExcls.b_w_update _ _ _ (γκu', κu') with "LKb LK") as "[LKb LK]".
    iMod ("INV_SL_CL" with "[PENDu' PTx LKb]") as "_".
    { iEval (unfold spinlockInv; simpl; red_tl_all).
      iExists γκu'. iEval (red_tl). iExists κu'.
      iEval (red_tl_all; simpl). iFrame. iRight. iFrame. auto.
    }
    iModIntro. iFrame. auto.
  Qed.


  Lemma Spinlock_lock_spec
        tid n
    :
    ⊢ ∀ κs x γx γl (P : sProp n) ℓL μn (ds : list (nat * nat * sProp n)) ℓu μu,
        [@ tid, n, ⊤ @]
          ⧼⟦((syn_tgt_interp_as n sndl (fun m => (s_memory_black m)))
               ∗ (⤉ isSpinlock n κs x γx γl P ℓL μn)
               ∗ ◇[κs](1 + ℓu, μu)
               ∗ (⤉ Duty(tid) ds)
               ∗ ◇{ds@1}(1 + ℓL, μn)
               ∗ ◇{ds@1}(1, 1)
            )%S, 1+n⟧⧽
            (OMod.close_itree Client (SCMem.mod gvs) (Spinlock.lock x))
            ⧼rv, ⟦(∃ (γκu κu : τ{nat, 1+n}),
                      (⤉ ○ γl (γκu, κu))
                        ∗ (⤉ P)
                        ∗ (⤉ Duty(tid) ((κu, 0, ▿ γκu tt) :: ds))
                        ∗ ◇[κu](ℓu, μu)
                  )%S, 1+n⟧⧽
  .
  Proof.
    iIntros (? ? ? ? ? ? ? ? ? ?).
    iStartTriple. iIntros "PRE POST". unfold Spinlock.lock.
    (* Preprocess for induction. *)
  Admitted.

  (* Lemma red_syn_Spinlock_lock_spec *)
  (*       tid n *)
  (*       (Es : coPsets) *)
  (*   : *)
  (*   ⟦(∀ (γ : τ{nat}) *)
  (*       (x : τ{SCMem.val}) *)
  (*       (P : τ{Φ, 1+n}) *)
  (*       (γk k L l : τ{nat}) *)
  (*       (q : τ{Qp}) *)
  (*       (ds : τ{ listT (nat * nat * Φ)%ftype, 1+n}) *)
  (*      , *)
  (*        [@ tid, n, Es @] *)
  (*          ⧼((syn_tgt_interp_as n sndl (fun m => (➢ (scm_memory_black m)))) *)
  (*               ∗ (⤉ isSpinlock n γ x P γk k L l) *)
  (*               ∗ ➢(@live γk nat k q) ∗ (⤉ Duty(tid) ds) *)
  (*               ∗ ◇{List.map fst ds}(2 + L, 1))⧽ *)
  (*            (OMod.close_itree Client (SCMem.mod gvs) (Spinlock.lock x)) *)
  (*            ⧼rv, (∃ (γu u : τ{nat, 1+n}), *)
  (*                     (⤉ P) ∗ ➢(auexa_w γ (((q/2)%Qp, γu, u) : Qp * nat * nat)) ∗ ➢(@live γk nat k (q/2)) *)
  (*                           ∗ (⤉ Duty(tid) ((u, 0, ➢(@dead γu nat u)) :: ds)) ∗ ➢(@live γu nat u (1/2)) ∗ ◇[u](l, 1))⧽)%F, 1+n⟧ *)
  (*   = *)
  (*     (∀ γ x (P : Formula n) γk k L l q (ds : list (nat * nat * Formula n)), *)
  (*         [@ tid, n, Es @] *)
  (*           ⧼⟦((syn_tgt_interp_as n sndl (fun m => (➢ (scm_memory_black m)))) *)
  (*                 ∗ (⤉ isSpinlock n γ x P γk k L l) *)
  (*                 ∗ ➢(live γk k q) ∗ (⤉ Duty(tid) ds) *)
  (*                 ∗ ◇{List.map fst ds}(2 + L, 1))%F, 1+n⟧⧽ *)
  (*             (OMod.close_itree Client (SCMem.mod gvs) (Spinlock.lock x)) *)
  (*             ⧼rv, ⟦(∃ (γu u : τ{nat, 1+n}), *)
  (*                       (⤉ P) ∗ ➢(auexa_w γ (((q/2)%Qp, γu, u) : Qp * nat * nat)) ∗ ➢(live γk k (q/2)) *)
  (*                             ∗ (⤉ Duty(tid) ((u, 0, ➢(@dead γu nat u)) :: ds)) ∗ ➢(@live γu nat u (1/2)) ∗ ◇[u](l, 1))%F, 1+n⟧⧽)%I *)
  (* . *)
  (* Proof. *)
  (*   simpl. *)
  (*   red_tl. apply f_equal. extensionalities γ. *)
  (*   red_tl. apply f_equal. extensionalities x. *)
  (*   red_tl. apply f_equal. extensionalities P. *)
  (*   red_tl. apply f_equal. extensionalities γk. *)
  (*   red_tl. apply f_equal. extensionalities k. *)
  (*   red_tl. apply f_equal. extensionalities L. *)
  (*   red_tl. apply f_equal. extensionalities l. *)
  (*   red_tl. apply f_equal. extensionalities q. *)
  (*   red_tl. apply f_equal. extensionalities ds. *)
  (*   apply red_syn_non_atomic_triple. *)
  (* Qed. *)

  (* Lemma Spinlock_lock_syn_spec *)
  (*       tid n *)
  (*       (Es : coPsets) *)
  (*       (MASK_TOP : OwnEs_top Es) *)
  (*       (MASK_STTGT : mask_has_st_tgt Es n) *)
  (*   : *)
  (*   ⊢ ⟦(∀ (γ : τ{nat}) *)
  (*         (x : τ{SCMem.val}) *)
  (*         (P : τ{Φ, 1+n}) *)
  (*         (γk k L l : τ{nat}) *)
  (*         (q : τ{Qp}) *)
  (*         (ds : τ{ listT (nat * nat * Φ)%ftype, 1+n}) *)
  (*        , *)
  (*          [@ tid, n, Es @] *)
  (*            ⧼((syn_tgt_interp_as n sndl (fun m => (➢ (scm_memory_black m)))) *)
  (*                 ∗ (⤉ isSpinlock n γ x P γk k L l) *)
  (*                 ∗ ➢(@live γk nat k q) ∗ (⤉ Duty(tid) ds) *)
  (*                 ∗ ◇{List.map fst ds}(2 + L, 1))⧽ *)
  (*              (OMod.close_itree Client (SCMem.mod gvs) (Spinlock.lock x)) *)
  (*              ⧼rv, (∃ (γu u : τ{nat, 1+n}), *)
  (*                       (⤉ P) ∗ ➢(auexa_w γ (((q/2)%Qp, γu, u) : Qp * nat * nat)) ∗ ➢(@live γk nat k (q/2)) *)
  (*                             ∗ (⤉ Duty(tid) ((u, 0, ➢(@dead γu nat u)) :: ds)) ∗ ➢(@live γu nat u (1/2)) ∗ ◇[u](l, 1))⧽)%F, 1+n⟧ *)
  (* . *)
  (* Proof. *)
  (*   rewrite red_syn_Spinlock_lock_spec. iApply Spinlock_lock_spec. all: auto. *)
  (* Qed. *)

  Lemma Spinlock_unlock_spec
        tid n
    :
    ⊢ ∀ κs x γx γl (P : sProp n) ℓL μn (ds : list (nat * nat * sProp n)) γκu κu,
        [@ tid, n, ⊤ @]
          ⧼⟦((syn_tgt_interp_as n sndl (fun m => (s_memory_black m)))
               ∗ (⤉ isSpinlock n κs x γx γl P ℓL μn)
               ∗ (⤉ ○ γl (γκu, κu))
               ∗ (⤉ P)
               ∗ (⤉ Duty(tid) ((κu, 0, ▿ γκu tt) :: ds))
               ∗ ◇{((κu, 0, ▿ κu tt) :: ds)@1}(1, 1)
            )%S, 1+n⟧⧽
            (OMod.close_itree Client (SCMem.mod gvs) (Spinlock.unlock x))
            ⧼rv, ⟦((⤉ Duty(tid) ds))%S, 1+n⟧⧽
  .
  Proof.
    iIntros (? ? ? ? ? ? ? ? ? ?).
    iStartTriple. iIntros "PRE POST". unfold Spinlock.unlock.
    (* Preprocess. *)
  Admitted.

  (* Lemma red_syn_Spinlock_unlock_spec *)
  (*       tid n *)
  (*       (Es : coPsets) *)
  (*   : *)
  (*   ⟦(∀ (γ : τ{nat}) *)
  (*       (x : τ{SCMem.val}) *)
  (*       (P : τ{Φ, 1+n}) *)
  (*       (γk k L l : τ{nat}) *)
  (*       (q : τ{Qp}) *)
  (*       (ds : τ{ listT (nat * nat * Φ)%ftype, 1+n}) *)
  (*       (γu u : τ{nat, 1+n}) *)
  (*      , *)
  (*        [@ tid, n, Es @] *)
  (*          ⧼((syn_tgt_interp_as n sndl (fun m => (➢(scm_memory_black m)))) *)
  (*              ∗ (⤉ isSpinlock n γ x P γk k L l) ∗ (⤉ P) *)
  (*              ∗ ➢(auexa_w γ (((q/2)%Qp, γu, u) : Qp * nat * nat)) ∗ ➢(@live γk nat k (q/2)) *)
  (*              ∗ (⤉ Duty(tid) ((u, 0, ➢(@dead γu nat u)) :: ds)) ∗ ➢(@live γu nat u (1/2)) *)
  (*              ∗ ◇{List.map fst ((u, 0, ➢(@dead γu nat u)) :: ds)}(1, 1) *)
  (*              ∗ ◇[k](1 + l, 1))⧽ *)
  (*            (OMod.close_itree Client (SCMem.mod gvs) (Spinlock.unlock x)) *)
  (*            ⧼rv, ((⤉ Duty(tid) ds) ∗ ➢(@live γk nat k q))⧽)%F, 1+n⟧ *)
  (*   = *)
  (*     (∀ γ x (P : Formula n) γk k L l q (ds : list (nat * nat * Formula n)) γu u, *)
  (*         [@ tid, n, Es @] *)
  (*           ⧼⟦(((syn_tgt_interp_as n sndl (fun m => (➢ (scm_memory_black m)))) *)
  (*                 ∗ (⤉ isSpinlock n γ x P γk k L l) ∗ (⤉ P) *)
  (*                 ∗ ➢(auexa_w γ (((q/2)%Qp, γu, u) : Qp * nat * nat)) ∗ ➢(live γk k (q/2)) *)
  (*                 ∗ (⤉ Duty(tid) ((u, 0, ➢(dead γu u)) :: ds)) ∗ ➢(live γu u (1/2)) *)
  (*                 ∗ ◇{List.map fst ((u, 0, ➢(dead γu u)) :: ds)}(1, 1) *)
  (*                 ∗ ◇[k](1 + l, 1)))%F, 1+n⟧⧽ *)
  (*             (OMod.close_itree Client (SCMem.mod gvs) (Spinlock.unlock x)) *)
  (*             ⧼rv, ⟦((⤉ Duty(tid) ds) ∗ ➢(live γk k q))%F, 1+n⟧⧽)%I *)
  (* . *)
  (* Proof. *)
  (*   red_tl. apply f_equal. extensionalities γ. *)
  (*   red_tl. apply f_equal. extensionalities x. *)
  (*   red_tl. apply f_equal. extensionalities P. *)
  (*   red_tl. apply f_equal. extensionalities γk. *)
  (*   red_tl. apply f_equal. extensionalities k. *)
  (*   red_tl. apply f_equal. extensionalities L. *)
  (*   red_tl. apply f_equal. extensionalities l. *)
  (*   red_tl. apply f_equal. extensionalities q. *)
  (*   red_tl. apply f_equal. extensionalities ds. *)
  (*   rewrite @red_tl_univ. apply f_equal. extensionalities γu. *)
  (*   rewrite @red_tl_univ. apply f_equal. extensionalities u. *)
  (*   apply red_syn_non_atomic_triple. *)
  (* Qed. *)

  (* Lemma Spinlock_unlock_syn_spec *)
  (*       tid n *)
  (*       (Es : coPsets) *)
  (*       (MASK_TOP : OwnEs_top Es) *)
  (*       (MASK_STTGT : mask_has_st_tgt Es n) *)
  (*   : *)
  (*   ⊢ ⟦(∀ (γ : τ{nat}) *)
  (*         (x : τ{SCMem.val}) *)
  (*         (P : τ{Φ, 1+n}) *)
  (*         (γk k L l : τ{nat}) *)
  (*         (q : τ{Qp}) *)
  (*         (ds : τ{ listT (nat * nat * Φ)%ftype, 1+n}) *)
  (*         (γu u : τ{nat, 1+n}) *)
  (*        , *)
  (*          [@ tid, n, Es @] *)
  (*            ⧼((syn_tgt_interp_as n sndl (fun m => (➢(scm_memory_black m)))) *)
  (*                ∗ (⤉ isSpinlock n γ x P γk k L l) ∗ (⤉ P) *)
  (*                ∗ ➢(auexa_w γ (((q/2)%Qp, γu, u) : Qp * nat * nat)) ∗ ➢(@live γk nat k (q/2)) *)
  (*                ∗ (⤉ Duty(tid) ((u, 0, ➢(@dead γu nat u)) :: ds)) ∗ ➢(@live γu nat u (1/2)) *)
  (*                ∗ ◇{List.map fst ((u, 0, ➢(@dead γu nat u )) :: ds)}(1, 1) *)
  (*                ∗ ◇[k](1 + l, 1))⧽ *)
  (*              (OMod.close_itree Client (SCMem.mod gvs) (Spinlock.unlock x)) *)
  (*              ⧼rv, ((⤉ Duty(tid) ds) ∗ ➢(@live γk nat k q))⧽)%F, 1+n⟧ *)
  (* . *)
  (* Proof. *)
  (*   rewrite red_syn_Spinlock_unlock_spec. iApply Spinlock_unlock_spec. all: auto. *)
  (* Qed. *)

End SPEC.
Global Opaque Spinlock.lock Spinlock.unlock.
