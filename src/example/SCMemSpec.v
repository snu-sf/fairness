From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Import ITreeLib Red TRed IRed2 LinkingRed.
From Fairness Require Import Mod Linking.
From Fairness Require Import PCM IProp IPM.
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

  Lemma SCMem_alloc_fun_spec
        tid x y (LT : x < S y)
        E (IN : ↑N_state_tgt ⊆ E)
        sz
    :
    ⊢ [@ tid, y, E @]
      {(tgt_interp_as l_mem (fun m => ((s_memory_black m) : sProp x)%S))}
      (map_event emb_mem (SCMem.alloc_fun sz))
      {l, (points_tos l (repeat (SCMem.val_nat 0) sz))}.
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

  Lemma SCMem_alloc_fun_syn_spec
        tid n
        E (IN : ↑N_state_tgt ⊆ E)
        sz
    :
    ⊢ ⟦([@ tid, n, E @]
          {(syn_tgt_interp_as n l_mem (fun m => ((s_memory_black m) : sProp n)%S))}
          (map_event emb_mem (SCMem.alloc_fun sz))
          {l, (s_points_tos l (repeat (SCMem.val_nat 0) sz))} : sProp (1+n))%S, 1+n⟧.
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
      {(tgt_interp_as l_mem (fun m => ((s_memory_black m) : sProp x)%S)) ∗ (points_to p v)}
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
    { ss. iExists _. red_tl. iFrame. unfold Lens.modify. rewrite Lens.set_set.
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


  Lemma SCMem_store_fun_spec
        tid x y (LT : x < S y)
        E (IN : ↑N_state_tgt ⊆ E)
        l v v0
    :
    ⊢ [@ tid, y, E @]
      {(tgt_interp_as l_mem (fun m => ((s_memory_black m) : sProp x)%S)) ∗ (points_to l v0)}
      (map_event emb_mem (SCMem.store_fun (l, v)))
      {u, points_to l v }.
  Proof.
    iStartTriple.
    iIntros "[#ST PT] SIM". iInv "ST" as (st) "ST1" "V".
    iDestruct "ST1" as (vs) "[VW MEM]". rred2.
    iApply wpsim_getR. iSplit. iFrame. rred2. rewrite Lens.view_set.
    iEval (simpl; red_tl_memra) in "MEM".
    iPoseProof (memory_ra_store with "MEM PT") as "STORE".
    iDestruct "STORE" as (m1) "[%STORE1 MB]". iMod ("MB") as "MB".
    rewrite STORE1. rred2. iApply (wpsim_modifyR with "VW"). iIntros "STTGT". rred2.
    iDestruct "MB" as "[MB PT]".
    iMod ("V" with "[STTGT MB]") as "_".
    { iExists _. ss. red_tl_memra. iFrame. unfold Lens.modify. rewrite Lens.set_set. iFrame. }
    iApply "SIM"; iFrame.
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


  Lemma SCMem_load_fun_spec
        tid x y (LT : x < S y)
        E (IN : ↑N_state_tgt ⊆ E)
        l v
    :
    ⊢ [@ tid, y, E @]
      {(tgt_interp_as l_mem (fun m => (s_memory_black m) : sProp x)%S) ∗ (points_to l v)}
      (map_event emb_mem (SCMem.load_fun l))
      {rv, ⌜rv = v⌝ ∗ points_to l v}.
  Proof.
    iStartTriple.
    iIntros "[#ST PT] SIM". unfold SCMem.load_fun. rred2.
    iInv "ST" as (st) "ST1" "K".
    iDestruct "ST1" as (vw) "[VW MEM]". iEval (simpl; red_tl_memra) in "MEM".
    iApply wpsim_getR. iSplit. iFrame. rred2.
    iPoseProof (memory_ra_load with "MEM PT") as "[%LOAD %PERM]".
    rewrite Lens.view_set. rewrite LOAD. rred2.
    iMod ("K" with "[VW MEM]") as "_". iExists _. iFrame. iEval (simpl; red_tl_memra). iFrame.
    iApply "SIM". iFrame. auto.
  Qed.

  Lemma SCMem_load_fun_syn_spec
        tid n
        E (IN : ↑N_state_tgt ⊆ E)
        l v
    :
    ⊢ ⟦([@ tid, n, E @]
          {(syn_tgt_interp_as _ l_mem (fun m => (s_memory_black m))) ∗ ⤉(l ↦ v)}
          (map_event emb_mem (SCMem.load_fun l))
          {rv, ⌜rv = v⌝ ∗ ⤉(l ↦ v)})%S, 1+n⟧.
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
      {(tgt_interp_as l_mem (fun m => (s_memory_black m) : sProp x)%S) ∗ (points_to l v)}
      (map_event emb_mem (SCMem.faa_fun (l, add)))
      {v, points_to l (SCMem.val_add v add)}.
  Proof.
    iStartTriple.
    iIntros "[#ST PT] SIM". unfold SCMem.faa_fun. rred2.
    iInv "ST" as (st) "ST1" "K". iDestruct "ST1" as (vw) "[VW MB]".
    iApply wpsim_getR. iSplit. iFrame. rred2. iEval (simpl; red_tl_memra) in "MB".
    iPoseProof (memory_ra_faa with "MB PT") as (m1) "[%FAA MB]".
    rewrite Lens.view_set. rewrite FAA. rred2.
    iApply (wpsim_modifyR with "VW"). iIntros "STTGT". rred2.
    iMod "MB" as "[MB PT]".
    iMod ("K" with "[STTGT MB]") as "_".
    { ss. iExists _. red_tl_memra. iFrame. unfold Lens.modify. rewrite Lens.set_set. iFrame. }
    iApply "SIM". iFrame.
  Qed.

  Lemma SCMem_faa_fun_syn_spec
        tid n
        E (IN : ↑N_state_tgt ⊆ E)
        l add v
    :
    ⊢ ⟦([@ tid, n, E @]
          {(syn_tgt_interp_as _ l_mem (fun m => (s_memory_black m))) ∗ ⤉(l ↦ v)}
          (map_event emb_mem (SCMem.faa_fun (l, add)))
          {v, l ↦ (SCMem.val_add v add)})%S, 1+n⟧.
  Proof.
    iIntros. iEval (setoid_rewrite red_syn_atomic_triple).
    iStartTriple. iIntros "P Q".
    iApply (SCMem_faa_fun_spec with "[P] [Q]"). 2: eauto. auto.
    red_tl. iDestruct "P" as "[A B]". rewrite red_syn_tgt_interp_as. red_tl_memra. iFrame.
    iIntros (rv) "A". iApply "Q". red_tl_memra. iFrame.
  Qed.


  Lemma SCMem_cas_fun_spec
        tid x y (LT : x < S y)
        E (IN : ↑N_state_tgt ⊆ E)
        l old new v
    :
    ⊢ [@ tid, y, E @]
      {(tgt_interp_as l_mem (fun m => (s_memory_black m) ∗ ⌜is_Some (SCMem.val_compare m v old)⌝ : sProp x)%S) ∗ (points_to l v)}
      (map_event emb_mem (SCMem.cas_fun (l, old, new)))
      {b, ∃ u, ⌜(if (SCMem.val_eq_dec v old) then (b = true /\ u = new) else (b = false /\ u = v))⌝
                ∗ points_to l u}.
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
    - iPoseProof (memory_ra_store with "MB PT") as (m1) "[%STORE MEM]". rewrite STORE. rred2r.
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
