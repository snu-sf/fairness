From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Import ITreeLib Red TRed IRed2 LinkingRed.
From Fairness Require Import Mod Linking.
From Fairness Require Import PCM IPM.
From Fairness Require Import IndexedInvariants OpticsInterp SimWeakest.
From Fairness Require Import TemporalLogic.
From Fairness Require Export SCMem.


Section SPEC.

  Context {STT : StateTypes}.
  Context `{sub : @SRA.subG Γ Σ}.
  Context {TLRASs : TLRAs_small STT Γ}.
  Context {TLRAS : TLRAs STT Γ Σ}.

  Context {HasMEMRA: @GRA.inG memRA Γ}.

  Variable p_mem : Prism.t id_tgt_type SCMem.val.
  Variable l_mem : Lens.t st_tgt_type SCMem.t.
  Let emb_mem := plmap p_mem l_mem.

  Lemma SCMem_alloc_fun_spec_gen
        tid x y z (LT : x < S (z + y))
        E (IN : ↑N_state_tgt ⊆ E)
        sz
    :
    ⊢ [@ tid, y, z, E @]
      {(tgt_interp_as l_mem (fun m => ((s_memory_black m) : sProp x)%S))}
      (map_event emb_mem (SCMem.alloc_fun sz))
      {l, (l ↦∗ (repeat (SCMem.val_nat 0) sz))}.
  Proof.
    iStartTriple.
    unfold SCMem.alloc_fun. iIntros "#ST SIM".
    iInv "ST" as (st) "ST1" "V".
    iDestruct "ST1" as (vw) "[VW MEM]".
    rred2r. iApply wpsim_getR. iSplit. iFrame.
    destruct (SCMem.alloc ((id ∘ Lens.view l_mem) (Lens.set l_mem vw st)) sz) eqn: Hal.
    iEval (simpl; red_tl_memra) in "MEM".
    iPoseProof (memory_ra_alloc with "MEM") as "ALLOC".
    { ss. rewrite Lens.view_set in Hal. eauto. }
    rred2r. iApply (wpsim_modifyR with "VW"). iIntros "STTGT".
    rred2r.
    iMod "ALLOC" as "[MB PTS]". iMod ("V" with "[STTGT MB]") as "_".
    { iExists _. iEval (simpl; red_tl_memra). iFrame. unfold Vw_tgt. ss.
      replace (Lens.set l_mem t st) with (Lens.modify l_mem (λ _ : SCMem.t, t) (Lens.set l_mem vw st)).
      iFrame. unfold Lens.modify. rewrite Lens.set_set. ss.
    }
    iApply "SIM". iFrame.
  Qed.

  Lemma SCMem_alloc_fun_spec
        tid x y (LT : x < S y)
        E (IN : ↑N_state_tgt ⊆ E)
        sz
    :
    ⊢ [@ tid, y, E @]
      {(tgt_interp_as l_mem (fun m => ((s_memory_black m) : sProp x)%S))}
      (map_event emb_mem (SCMem.alloc_fun sz))
      {l, (l ↦∗ (repeat (SCMem.val_nat 0) sz))}.
  Proof.
    iStartTriple.
    iIntros "#ST SIM".
    iApply (SCMem_alloc_fun_spec_gen tid x y 0 with "[$ST]"); [lia|auto..].
  Qed.

  Lemma SCMem_alloc_fun_syn_spec
        tid n
        E (IN : ↑N_state_tgt ⊆ E)
        sz
    :
    ⊢ ⟦([@ tid, n, E @]
          {(syn_tgt_interp_as n l_mem (fun m => ((s_memory_black m) : sProp n)%S))}
          (map_event emb_mem (SCMem.alloc_fun sz))
          {l, (l ↦∗ (repeat (SCMem.val_nat 0) sz))} : sProp (1+n))%S, 1+n⟧.
  Proof.
    iIntros. iEval (setoid_rewrite red_syn_atomic_triple).
    iStartTriple. iIntros "P Q". iEval (rewrite red_syn_tgt_interp_as) in "P".
    iApply (SCMem_alloc_fun_spec with "P [Q]"). auto. auto.
    iIntros "% PTS". iSpecialize ("Q" $! rv with "[PTS]"). 2: iFrame.
    iEval red_tl_memra. iFrame.
  Qed.


  Lemma SCMem_free_fun_spec
        tid x y (LT : x < S y)
        E (IN : ↑N_state_tgt ⊆ E)
        p v
    :
    ⊢ [@ tid, y, E @]
      {(tgt_interp_as l_mem (fun m => ((s_memory_black m) : sProp x)%S)) ∗ (p ↦ v)}
      (map_event emb_mem (SCMem.free_fun p))
      {u, ⌜True⌝%I}.
  Proof.
    iStartTriple.
    iIntros "[#ST PT] SIM". iInv "ST" as (st) "ST1" "V".
    iDestruct "ST1" as (vw) "[VW MB]".
    rred2r. iApply wpsim_getR. iSplit; [iFrame | ].
    rred2r. rewrite Lens.view_set. iEval (simpl; red_tl_memra) in "MB".
    iPoseProof (memory_ra_free with "[MB PT]") as (m1) "[%FREE MB]".
    { iFrame. }
    rewrite FREE. rred2r.
    iApply (wpsim_modifyR with "VW"). iIntros "STTGT". rred2r. iMod "MB".
    iMod ("V" with "[STTGT MB]") as "_".
    { ss. iExists _. red_tl. unfold Lens.modify. rewrite Lens.set_set.
      iEval (red_tl_memra). iFrame.
    }
    iApply "SIM". auto.
  Qed.

  Lemma SCMem_free_fun_syn_spec
        tid n
        E (IN : ↑N_state_tgt ⊆ E)
        p v
    :
    ⊢ ⟦([@ tid, n, E @]
          {(syn_tgt_interp_as n l_mem (fun m => (s_memory_black m))) ∗ ⤉(p ↦ v)}
          (map_event emb_mem (SCMem.free_fun p))
          {u, ⌜True⌝})%S, 1+n⟧.
  Proof.
    iIntros. iEval (setoid_rewrite red_syn_atomic_triple).
    iStartTriple. iIntros "P Q".
    iApply (SCMem_free_fun_spec with "[P] Q"). 2: eauto. auto.
    red_tl. iDestruct "P" as "[A B]". rewrite red_syn_tgt_interp_as. red_tl_memra. iFrame.
  Qed.


  Lemma SCMem_store_fun_spec_gen
        tid x y z (LT : x < S (z + y))
        E (IN : ↑N_state_tgt ⊆ E)
        l v v0
    :
    ⊢ [@ tid, y, z, E @]
      {(tgt_interp_as l_mem (fun m => ((s_memory_black m) : sProp x)%S)) ∗ (l ↦ v0)}
      (map_event emb_mem (SCMem.store_fun (l, v)))
      {u, l ↦ v }.
  Proof.
    iStartTriple.
    iIntros "[#ST PT] SIM". iInv "ST" as (st) "ST1" "V".
    iDestruct "ST1" as (vs) "[VW MEM]". rred2.
    iApply wpsim_getR. iSplit. iFrame. rred2. rewrite Lens.view_set.
    iEval (simpl; red_tl_memra) in "MEM".
    iPoseProof (memory_ra_store with "MEM PT") as "STORE".
    iDestruct "STORE" as (m1) "[%STORE1 MB]". iMod ("MB") as "MB".
    erewrite STORE1. rred2. iApply (wpsim_modifyR with "VW"). iIntros "STTGT". rred2.
    iDestruct "MB" as "[MB PT]".
    iMod ("V" with "[STTGT MB]") as "_".
    { iExists _. ss. red_tl_memra. iFrame. unfold Lens.modify. rewrite Lens.set_set. iFrame. }
    iApply "SIM"; iFrame.
  Qed.
  Lemma SCMem_store_fun_spec
        tid x y (LT : x < S y)
        E (IN : ↑N_state_tgt ⊆ E)
        l v v0
    :
    ⊢ [@ tid, y, E @]
      {(tgt_interp_as l_mem (fun m => ((s_memory_black m) : sProp x)%S)) ∗ (l ↦ v0)}
      (map_event emb_mem (SCMem.store_fun (l, v)))
      {u, l ↦ v }.
  Proof.
    iStartTriple.
    iIntros "[#ST PT] SIM".
    iApply (SCMem_store_fun_spec_gen tid x y 0 with "[$ST $PT]"); [lia|auto..].
  Qed.

  Lemma SCMem_store_fun_syn_spec
        tid n
        E (IN : ↑N_state_tgt ⊆ E)
        l v v0
    :
    ⊢ ⟦([@ tid, n, E @]
          {(syn_tgt_interp_as _ l_mem (fun m => (s_memory_black m))) ∗ ⤉(l ↦ v0)}
          (map_event emb_mem (SCMem.store_fun (l, v)))
          {u, ⤉(l ↦ v) })%S, 1+n⟧.
  Proof.
    iIntros. iEval (setoid_rewrite red_syn_atomic_triple).
    iStartTriple. iIntros "P Q". iEval (red_tl; red_tl_memra) in "Q".
    iApply (SCMem_store_fun_spec with "[P] Q"). 2: eauto. auto.
    red_tl. iDestruct "P" as "[A B]". rewrite red_syn_tgt_interp_as. red_tl_memra. iFrame.
  Qed.


  Lemma SCMem_load_fun_spec_gen
        tid x y z (LT : x < S (y + z))
        E (IN : ↑N_state_tgt ⊆ E)
        l v dq
    :
    ⊢ [@ tid, y, z, E @]
      {(tgt_interp_as l_mem (fun m => (s_memory_black m) : sProp x)%S) ∗ (l ↦{dq} v)}
      (map_event emb_mem (SCMem.load_fun l))
      {rv, ⌜rv = v⌝ ∗ (l ↦{dq} v)}.
  Proof.
    iStartTriple.
    iIntros "[#ST PT] SIM". unfold SCMem.load_fun. rred2.
    iInv "ST" as (st) "ST1" "K"; [lia|].
    iDestruct "ST1" as (vw) "[VW MEM]". iEval (simpl; red_tl_memra) in "MEM".
    iApply wpsim_getR. iSplit. iFrame. rred2.
    iPoseProof (memory_ra_load with "MEM PT") as "[%LOAD %PERM]".
    rewrite Lens.view_set. rewrite LOAD. rred2.
    iMod ("K" with "[VW MEM]") as "_"; [|lia|]. iExists _. iFrame. iEval (simpl; red_tl_memra). iFrame.
    iApply "SIM". iFrame. auto.
  Qed.

  Lemma SCMem_load_fun_spec
        tid x y (LT : x < S y)
        E (IN : ↑N_state_tgt ⊆ E)
        l v dq
    :
    ⊢ [@ tid, y, E @]
      {(tgt_interp_as l_mem (fun m => (s_memory_black m) : sProp x)%S) ∗ (l ↦{dq} v)}
      (map_event emb_mem (SCMem.load_fun l))
      {rv, ⌜rv = v⌝ ∗ (l ↦{dq} v)}.
  Proof.
    iStartTriple.
    iIntros "[#ST PT] SIM".
    iApply (SCMem_load_fun_spec_gen tid x y 0 with "[$ST $PT]"); [lia|auto..].
  Qed.

  Lemma SCMem_load_fun_syn_spec
        tid n
        E (IN : ↑N_state_tgt ⊆ E)
        l v dq
    :
    ⊢ ⟦([@ tid, n, E @]
          {(syn_tgt_interp_as _ l_mem (fun m => (s_memory_black m))) ∗ ⤉(l ↦{dq} v)}
          (map_event emb_mem (SCMem.load_fun l))
          {rv, ⌜rv = v⌝ ∗ ⤉(l ↦{dq} v)})%S, 1+n⟧.
  Proof.
    iIntros. iEval (setoid_rewrite red_syn_atomic_triple).
    iStartTriple. iIntros "P Q".
    iApply (SCMem_load_fun_spec with "[P] [Q]"). 2: eauto. auto.
    red_tl. iDestruct "P" as "[A B]". rewrite red_syn_tgt_interp_as. red_tl_memra. iFrame.
    iIntros (rv) "[A B]". iApply "Q". red_tl. red_tl_memra. iFrame.
  Qed.


  Lemma SCMem_faa_fun_spec
        tid x y (LT : x < S y)
        E (IN : ↑N_state_tgt ⊆ E)
        l add v
    :
    ⊢ [@ tid, y, E @]
      {(tgt_interp_as l_mem (fun m => (s_memory_black m) : sProp x)%S) ∗ (l ↦ v)}
      (map_event emb_mem (SCMem.faa_fun (l, add)))
      {rv, ⌜rv = v⌝ ∗ (l ↦ (SCMem.val_add v add))}.
  Proof.
    iStartTriple.
    iIntros "[#ST PT] SIM". unfold SCMem.faa_fun. rred2.
    iInv "ST" as (st) "ST1" "K". iDestruct "ST1" as (vw) "[VW MB]".
    iApply wpsim_getR. iSplit. iFrame. rred2. iEval (simpl; red_tl_memra) in "MB".
    iPoseProof (memory_ra_faa with "MB PT") as (m1) "[%FAA MB]".
    rewrite Lens.view_set. erewrite FAA. rred2.
    iApply (wpsim_modifyR with "VW"). iIntros "STTGT". rred2.
    iMod "MB" as "[MB PT]".
    iMod ("K" with "[STTGT MB]") as "_".
    { ss. iExists _. red_tl_memra. iFrame. unfold Lens.modify. rewrite Lens.set_set. iFrame. }
    iApply "SIM". iFrame. auto.
  Qed.

  Lemma SCMem_faa_fun_syn_spec
        tid n
        E (IN : ↑N_state_tgt ⊆ E)
        l add v
    :
    ⊢ ⟦([@ tid, n, E @]
          {(syn_tgt_interp_as _ l_mem (fun m => (s_memory_black m))) ∗ ⤉(l ↦ v)}
          (map_event emb_mem (SCMem.faa_fun (l, add)))
          {rv, ⌜rv = v⌝ ∗ (⤉(l ↦ (SCMem.val_add rv add)))})%S, 1+n⟧.
  Proof.
    iIntros. iEval (setoid_rewrite red_syn_atomic_triple).
    iStartTriple. iIntros "P Q".
    iApply (SCMem_faa_fun_spec with "[P] [Q]"). 2: eauto. auto.
    red_tl. iDestruct "P" as "[A B]". rewrite red_syn_tgt_interp_as. red_tl_memra. iFrame.
    iIntros (rv) "[%A B]". iApply "Q". red_tl. red_tl_memra. subst. iFrame. auto.
  Qed.

  Lemma SCMem_cas_fun_spec_gen
        tid x y z (LT : x < S (z + y))
        E (IN : ↑N_state_tgt ⊆ E)
        l old new v
    :
    ⊢ [@ tid, y, z, E @]
      {(tgt_interp_as l_mem (fun m => (s_memory_black m) ∗ ⌜is_Some (SCMem.val_compare m v old)⌝ : sProp x)%S) ∗ (l ↦ v)}
      (map_event emb_mem (SCMem.cas_fun (l, old, new)))
      {b, ∃ u, ⌜(if (SCMem.val_eq_dec v old) then (b = true /\ u = new) else (b = false /\ u = v))⌝
                ∗ (l ↦ u)}.
  Proof.
    Local Transparent SCMem.cas.
    iStartTriple.
    iIntros "[#ST PT] CAS". iInv "ST" as (st) "ST1" "K".
    ss. iDestruct "ST1" as (mem) "[VW MM]". iEval (red_tl; simpl) in "MM".
    iDestruct "MM" as "[MB %MC]".
    rred2r. iApply wpsim_getR. iSplit; [iFrame | ].
    iEval (simpl; red_tl_memra) in "MB".
    rred2r. unfold SCMem.cas. iPoseProof (memory_ra_load with "MB PT") as "[%LOAD %PERM]".
    rewrite Lens.view_set. rewrite LOAD. destruct MC as [b MC]. rewrite MC.
    destruct b.
    - iPoseProof (memory_ra_store with "MB PT") as (m1) "[%STORE MEM]". erewrite STORE. rred2r.
      iApply (wpsim_modifyR with "VW"). iIntros "STTGT". rred2r.
      iEval (unfold Lens.modify; rewrite Lens.set_set) in "STTGT".
      iMod ("MEM") as "[MB PT]". iMod ("K" with "[STTGT MB]") as "_".
      { iExists _. iEval (red_tl; red_tl_memra). iFrame.
        iPureIntro. erewrite <- SCMem.val_compare_store; eauto.
      }
      iApply "CAS". iExists _. iFrame.
      iPureIntro. apply SCMem.val_compare_Some in MC. subst. des_ifs.
    - rred2r. iMod ("K" with "[VW MB]") as "_".
      { iExists _. iFrame. iEval red_tl; red_tl_memra. iFrame. iPureIntro. rewrite MC; auto. }
      iApply "CAS". iExists _. iFrame.
      iPureIntro. apply SCMem.val_compare_Some in MC. des_ifs.
  Qed.
  Lemma SCMem_cas_fun_spec
        tid x y (LT : x < S y)
        E (IN : ↑N_state_tgt ⊆ E)
        l old new v
    :
    ⊢ [@ tid, y, E @]
      {(tgt_interp_as l_mem (fun m => (s_memory_black m) ∗ ⌜is_Some (SCMem.val_compare m v old)⌝ : sProp x)%S) ∗ (l ↦ v)}
      (map_event emb_mem (SCMem.cas_fun (l, old, new)))
      {b, ∃ u, ⌜(if (SCMem.val_eq_dec v old) then (b = true /\ u = new) else (b = false /\ u = v))⌝
                ∗ (l ↦ u)}.
  Proof.
    iStartTriple.
    iIntros "[#ST PT] SIM".
    iApply (SCMem_cas_fun_spec_gen tid x y 0 with "[$ST $PT]"); [lia|auto..].
  Qed.

  (* Note: weak, can't guarnatee that the values the points-to point to doesn't change. *)
  Lemma SCMem_cas_loc_fun_spec_gen_gen
        tid x y z (LT : x < S (z + y))
        E (IN : ↑N_state_tgt ⊆ E)
        l old new v pv po
    :
    ⊢ [@ tid, y, z, E @]
      {(tgt_interp_as l_mem (fun m => (s_memory_black m) : sProp x)%S) ∗
        (l ↦ v) ∗
        (if (SCMem.val_eq_dec v SCMem.val_null) then emp else (∃ vv: τ{SCMem.val,y}, v ↦{ pv } vv)) ∗
        (if (SCMem.val_eq_dec old SCMem.val_null) then emp else (∃ vo: τ{SCMem.val,y}, old ↦{ po } vo))
      }
      (map_event emb_mem (SCMem.cas_fun (l, (old : SCMem.val), (new : SCMem.val))))
      {b, ∃ u, ⌜(if (SCMem.val_eq_dec v old) then (b = true /\ u = (new : SCMem.val)) else (b = false /\ u = (v : SCMem.val)))⌝
                ∗ (l ↦ u) ∗
                (if (SCMem.val_eq_dec v SCMem.val_null) then emp else (∃ vv: τ{SCMem.val,y}, v ↦{ pv } vv)) ∗
                (if (SCMem.val_eq_dec old SCMem.val_null) then emp else (∃ vo: τ{SCMem.val,y}, old ↦{ po } vo))
      }.
  Proof.
    Local Transparent SCMem.cas.
    iStartTriple.
    iIntros "[#ST (PT & v↦ & o↦)] CAS". iInv "ST" as (st) "ST1" "K".
    ss. iDestruct "ST1" as (mem) "[VW MB]". red_tl_memra.
    des_ifs.
    2,4,5: iDestruct "o↦" as (vo) "o↦".
    3,4,5: iDestruct "v↦" as (vv) "v↦".
    2: iDestruct (SCMem.memory_ra_compare_ptr_left _ 0 with "MB o↦") as %MC.
    5: iDestruct (SCMem.memory_ra_compare_ptr_right _ 0 with "MB v↦") as %MC.
    3: iDestruct (SCMem.memory_ra_compare_ptr_both_gen with "MB v↦ o↦") as %MC.
    4: iDestruct (SCMem.memory_ra_compare_ptr_both_gen with "MB v↦ o↦") as %MC.
    all: rred2r; iApply wpsim_getR; iSplit; [iFrame | ].
    all: iEval (simpl; red_tl_memra) in "MB".
    all: rred2r; unfold SCMem.cas.
    1: iDestruct (memory_ra_load with "MB PT") as "[%LOAD %PERM]".
    2: iDestruct (memory_ra_load with "MB PT") as "[%LOAD %PERM]".
    3: iDestruct (memory_ra_load with "MB PT") as "[%LOAD %PERM]".
    4: iDestruct (memory_ra_load with "MB PT") as "[%LOAD %PERM]".
    5: iDestruct (memory_ra_load with "MB PT") as "[%LOAD %PERM]".
    all: rewrite Lens.view_set; rewrite LOAD.
    1: simpl in *.
    all: try (unfold SCMem.compare in MC; unfold SCMem.val_null; rewrite MC).
    - iPoseProof (memory_ra_store with "MB PT") as (m1) "[%STORE MEM]". erewrite STORE. rred2r.
      iApply (wpsim_modifyR with "VW"). iIntros "STTGT". rred2r.
      iEval (unfold Lens.modify; rewrite Lens.set_set) in "STTGT".
      iMod ("MEM") as "[MB PT]". iMod ("K" with "[STTGT MB]") as "_".
      { iExists _. iEval (red_tl; red_tl_memra). iFrame. }
      iApply "CAS". iExists _. iFrame. done.
    - rred2r. iMod ("K" with "[VW MB]") as "_".
      { iExists _. iFrame. iEval red_tl; red_tl_memra. iFrame. }
      iApply "CAS". iExists 0. iFrame. iSplit; [done|].
      iExists _. iFrame.
    - case_bool_decide; [|done].
      subst. iPoseProof (memory_ra_store with "MB PT") as (m1) "[%STORE MEM]". erewrite STORE. rred2r.
      iApply (wpsim_modifyR with "VW"). iIntros "STTGT". rred2r.
      iEval (unfold Lens.modify; rewrite Lens.set_set) in "STTGT".
      iMod ("MEM") as "[MB PT]". iMod ("K" with "[STTGT MB]") as "_".
      { iExists _. iEval (red_tl; red_tl_memra). iFrame. }
      iApply "CAS". iExists _. iFrame. iSplit; [done|].
      iSplitL "v↦"; iExists _; iFrame.
    - case_bool_decide; [done|].
      rred2r. iMod ("K" with "[VW MB]") as "_".
      { iExists _. iFrame. iEval red_tl; red_tl_memra. iFrame. }
      iApply "CAS". iExists _. iFrame.
      iSplit; [done|].
      iSplitL "v↦"; iExists _; iFrame.
    - rred2r. iMod ("K" with "[VW MB]") as "_".
      { iExists _. iFrame. iEval red_tl; red_tl_memra. iFrame. }
      iApply "CAS". iExists _. iFrame. iSplit; [done|].
      iExists _. done.
  Qed.
  Lemma SCMem_cas_loc_fun_spec_gen
        tid x y (LT : x < S y)
        E (IN : ↑N_state_tgt ⊆ E)
        l old new v pv po
    :
    ⊢ [@ tid, y, E @]
      {(tgt_interp_as l_mem (fun m => (s_memory_black m) : sProp x)%S) ∗
        (l ↦ v) ∗
        (if (SCMem.val_eq_dec v SCMem.val_null) then emp else (∃ vv: τ{SCMem.val,y}, v ↦{ pv } vv)) ∗
        (if (SCMem.val_eq_dec old SCMem.val_null) then emp else (∃ vo: τ{SCMem.val,y}, old ↦{ po } vo))
      }
      (map_event emb_mem (SCMem.cas_fun (l, (old : SCMem.val), (new : SCMem.val))))
      {b, ∃ u, ⌜(if (SCMem.val_eq_dec v old) then (b = true /\ u = (new : SCMem.val)) else (b = false /\ u = (v : SCMem.val)))⌝
                ∗ (l ↦ u) ∗
                (if (SCMem.val_eq_dec v SCMem.val_null) then emp else (∃ vv: τ{SCMem.val,y}, v ↦{ pv } vv)) ∗
                (if (SCMem.val_eq_dec old SCMem.val_null) then emp else (∃ vo: τ{SCMem.val,y}, old ↦{ po } vo))
      }.
  Proof.
    iStartTriple.
    iIntros "[#ST (PT & v↦ & o↦)] CAS".
    iApply (SCMem_cas_loc_fun_spec_gen_gen tid x y 0 with "[$ST $PT $v↦ $o↦]"); [lia|auto..].
  Qed.

  Lemma SCMem_cas_fun_syn_spec
        tid n
        E (IN : ↑N_state_tgt ⊆ E)
        l old new v
    :
    ⊢ ⟦([@ tid, n, E @]
          {(syn_tgt_interp_as _ l_mem (fun m => (s_memory_black m) ∗ ⌜is_Some (SCMem.val_compare m v old)⌝)) ∗ ⤉(l ↦ v)}
          (map_event emb_mem (SCMem.cas_fun (l, old, new)))
          {b, ∃ (u : τ{SCMem.val, 1+n}),
              ⌜(if (SCMem.val_eq_dec v old) then (b = true /\ u = new) else (b = false /\ u = v))⌝ ∗ ⤉(l ↦ u)})%S, 1+n⟧.
  Proof.
    iIntros. iEval (setoid_rewrite red_syn_atomic_triple).
    iStartTriple. iIntros "P Q".
    iApply (SCMem_cas_fun_spec with "[P] [Q]"). 2: eauto. auto.
    red_tl. iDestruct "P" as "[A B]". rewrite red_syn_tgt_interp_as. red_tl_memra. iFrame.
    iIntros (rv) "[% A]". iApply "Q". red_tl. iExists _. red_tl. red_tl_memra. iFrame.
  Qed.


  Lemma SCMem_compare_fun_spec_gen
        tid x y z (LT : x < S (z + y))
        E (IN : ↑N_state_tgt ⊆ E)
        v1 v2
    :
    ⊢ [@ tid, y, z, E @]
      {(tgt_interp_as l_mem (fun m => (s_memory_black m) ∗ ⌜is_Some (SCMem.val_compare m v1 v2)⌝ : sProp x)%S)}
      (map_event emb_mem (SCMem.compare_fun (v1, v2)))
      {b, ⌜(v1 = v2 -> b = true) /\ (v1 <> v2 -> b = false)⌝}.
  Proof.
    iStartTriple.
    iIntros "#ST CASE". iInv "ST" as (st) "ST1" "K".
    iDestruct "ST1" as (vw) "[VW MM]". ss. iEval red_tl in "MM".
    iDestruct "MM" as "[MB %MC]". rred2r.
    iApply wpsim_getR. iSplit; iFrame. rred2r.
    rewrite Lens.view_set. unfold SCMem.compare.
    destruct (SCMem.val_compare vw v1 v2) eqn:COMPR.
    - destruct b.
      + rred2r. exploit SCMem.val_compare_Some; eauto. i. ss; clarify.
        iMod ("K" with "[VW MB]") as "_".
        { iExists _. iFrame. iEval red_tl. iFrame. iPureIntro. auto. }
        iApply "CASE". ss.
      + rred2r. exploit SCMem.val_compare_Some; eauto. i. ss; clarify.
        iMod ("K" with "[VW MB]") as "_".
        { iExists _. iFrame. iEval red_tl. iFrame. iPureIntro. auto. }
        iApply "CASE". ss.
    - exfalso. apply is_Some_None in MC. ss.
  Qed.
  Lemma SCMem_compare_fun_spec
        tid x y (LT : x < S y)
        E (IN : ↑N_state_tgt ⊆ E)
        v1 v2
    :
    ⊢ [@ tid, y, E @]
      {(tgt_interp_as l_mem (fun m => (s_memory_black m) ∗ ⌜is_Some (SCMem.val_compare m v1 v2)⌝ : sProp x)%S)}
      (map_event emb_mem (SCMem.compare_fun (v1, v2)))
      {b, ⌜(v1 = v2 -> b = true) /\ (v1 <> v2 -> b = false)⌝}.
  Proof.
    iStartTriple.
    iIntros "#ST CASE".
    iApply (SCMem_compare_fun_spec_gen tid x y 0 with "[$ST]"); [lia|auto..].
  Qed.

  Lemma SCMem_compare_loc_null_fun_spec_gen
        tid x y z (LT : x < S (z + y))
        E (IN : ↑N_state_tgt ⊆ E)
        p pp pv
    :
    ⊢ [@ tid, y, z, E @]
      {(tgt_interp_as l_mem (fun m => (s_memory_black m) : sProp x)%S)
      ∗ (p ↦{ pp} pv)
      }
      (map_event emb_mem (SCMem.compare_fun (p, SCMem.val_null)))
      {b, (p ↦{ pp} pv) ∗ ⌜b = false⌝ }.
  Proof.
    iStartTriple.
    iIntros "[#ST p↦] CASE".
    destruct p as [n|p]; [done|].
    iInv "ST" as (st) "ST1" "K".
    iDestruct "ST1" as (vw) "[VW MB]". ss. iEval red_tl in "MB".
    red_tl_memra.

    iDestruct (SCMem.memory_ra_compare_ptr_right _ 0 with "MB p↦") as %MC.

    rred2r. iApply wpsim_getR. iSplit; iFrame. rred2r.
    rewrite Lens.view_set. unfold SCMem.compare in MC.
    simpl in *. unfold SCMem.has_permission in MC.
    destruct p as [blk ofs]. simpl in *.
    des_ifs.
    iMod ("K" with "[VW MB]") as "_".
    { iExists _. red_tl_memra. iFrame. }
    rred2r. iApply "CASE". iFrame. done.
  Qed.
  Lemma SCMem_compare_loc_null_fun_spec
        tid x y (LT : x < S y)
        E (IN : ↑N_state_tgt ⊆ E)
        p pp pv
    :
    ⊢ [@ tid, y, E @]
      {(tgt_interp_as l_mem (fun m => (s_memory_black m) : sProp x)%S)
      ∗ (p ↦{ pp} pv)
      }
      (map_event emb_mem (SCMem.compare_fun (p, SCMem.val_null)))
      {b, (p ↦{ pp} pv) ∗ ⌜b = false⌝ }.
  Proof.
    iStartTriple.
    iIntros "[#ST p↦] CASE".
    iApply (SCMem_compare_loc_null_fun_spec_gen tid x y 0 with "[$ST $p↦]"); [lia|auto..].
  Qed.

  Lemma SCMem_compare_fun_syn_spec
        tid n
        E (IN : ↑N_state_tgt ⊆ E)
        v1 v2
    :
    ⊢ ⟦([@ tid, n, E @]
          {syn_tgt_interp_as _ l_mem (fun m => (s_memory_black m) ∗ ⌜is_Some (SCMem.val_compare m v1 v2)⌝)}
          (map_event emb_mem (SCMem.compare_fun (v1, v2)))
          {b, ⌜(v1 = v2 -> b = true) /\ (v1 <> v2 -> b = false)⌝})%S, 1+n⟧.
  Proof.
    iIntros. iEval (setoid_rewrite red_syn_atomic_triple).
    iStartTriple. iIntros "P Q".
    iApply (SCMem_compare_fun_spec with "[P] Q"). 2: eauto. auto.
    red_tl. rewrite red_syn_tgt_interp_as. iFrame.
  Qed.

End SPEC.
Global Opaque SCMem.alloc_fun SCMem.free_fun SCMem.load_fun SCMem.store_fun SCMem.faa_fun SCMem.cas_fun SCMem.compare_fun.
