From sflib Require Import sflib.
From Paco Require Import paco.
From stdpp Require namespaces.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Export ITreeLib
     PCMFOS  IPMFOS
     Mod Linking SCM Red TRed IRed2 LinkingRed Weakest FancyUpdate.


Section SPEC.
  Variable ident_src: ID.
  Variable ident_tgt: ID.
  Variable state_src: Type.
  Variable state_tgt: Type.

  Context `{Σ: GRA.t}.
  Variable Invs : @InvSet Σ.

  Context `{MONORA: @GRA.inG monoRA Σ}.
  Context `{THDRA: @GRA.inG ThreadRA Σ}.
  Context `{STATESRC: @GRA.inG (stateSrcRA state_src) Σ}.
  Context `{STATETGT: @GRA.inG (stateTgtRA state_tgt) Σ}.
  Context `{IDENTSRC: @GRA.inG (identSrcRA ident_src) Σ}.
  Context `{IDENTTGT: @GRA.inG (identTgtRA ident_tgt) Σ}.
  Context `{OBLGRA: @GRA.inG ObligationRA.t Σ}.
  Context `{ARROWRA: @GRA.inG (ArrowRA ident_tgt) Σ}.
  Context `{EDGERA: @GRA.inG EdgeRA Σ}.
  Context `{ONESHOTRA: @GRA.inG (@FiniteMap.t (OneShot.t unit)) Σ}.
  Context `{COPSETRA : @GRA.inG CoPset.t Σ}.
  Context `{GSETRA : @GRA.inG Gset.t Σ}.
  Context `{INVSETRA : @GRA.inG (InvSetRA Var) Σ}.

  Context `{MEMRA: @GRA.inG memRA Σ}.


  Variable p_mem : Prism.t ident_tgt SCMem.val.
  Variable l_mem : Lens.t state_tgt SCMem.t.
  Let emb_mem := plmap p_mem l_mem.

  Ltac lred2 := repeat (prw ltac:(red_tac itree_class) 1 2 0).
  Ltac rred2 := repeat (prw ltac:(red_tac itree_class) 1 1 0).

  Lemma alloc_fun_spec
        tid E R_src R_tgt (Q : R_src -> R_tgt -> iProp)
        r g ps pt
        itr_src ktr_tgt
        (IN: ↑N_state_tgt ⊆ E)
        sz
    :
      (tgt_interp_as l_mem memory_black)
      -∗
      (∀ l, points_tos l (repeat (SCMem.val_nat 0) sz) -∗ stsim tid E r g Q ps true itr_src (ktr_tgt l))
      -∗
      (stsim tid E r g Q ps pt
            itr_src
            (map_event emb_mem (SCMem.alloc_fun sz) >>= ktr_tgt)).
  Proof.
    unfold SCMem.alloc_fun. i. iIntros "#ST SIM".
    iInv "ST" as (st) "ST1" "V".
    iDestruct "ST1" as (vw) "[VW MEM]". rred2.
    iApply stsim_getR. iSplit. iFrame.
    destruct (SCMem.alloc ((id ∘ Lens.view l_mem) (Lens.set l_mem vw st)) sz) eqn: Hal.
    iPoseProof (memory_ra_alloc with "MEM") as "ALLOC".
    { ss. rewrite Lens.view_set in Hal. eauto. }
    rred2.
    iApply (stsim_modifyR with "VW"). iIntros "STTGT". rred2.
    iMod "ALLOC" as "[MB PTS]".
    iMod ("V" with "[STTGT MB]") as "_". iExists _. iFrame. unfold Vw_tgt.
    { ss. replace (Lens.set l_mem t st) with (Lens.modify l_mem (λ _ : SCMem.t, t) (Lens.set l_mem vw st)).
      iFrame. unfold Lens.modify. rewrite Lens.set_set. ss. }
    iApply "SIM". iFrame.
  Qed.

  Lemma free_fun_spec
        tid E r R_src R_tgt (Q : R_src -> R_tgt -> iProp) g ps pt
        itr_src ktr_tgt
        (IN: ↑N_state_tgt ⊆ E)
        p v
        :
      (tgt_interp_as l_mem memory_black)
      -∗
      (points_to p v)
      -∗
      (stsim tid E r g Q ps true itr_src (ktr_tgt tt))
      -∗
      stsim tid E r g Q ps pt
            itr_src
            (map_event emb_mem (SCMem.free_fun p) >>= ktr_tgt).
  Proof.
    i. iIntros "#ST PT SIM". iInv "ST" as (st) "ST1" "V".
    iDestruct "ST1" as (vw) "[VW MB]". rred2.
    iApply stsim_getR. iSplit; [iFrame | ]. rred2.
    rewrite Lens.view_set.
    iPoseProof (memory_ra_free with "[MB PT]") as (m1) "[%FREE MB]"; [iFrame | ].
    rewrite FREE. rred2.
    iApply (stsim_modifyR with "VW"). iIntros "STTGT". rred2. iMod "MB".
    iMod ("V" with "[STTGT MB]") as "_".
    { iExists _. iFrame. unfold Lens.modify. rewrite Lens.set_set. iFrame. }
    iApply "SIM".
  Qed.

  Lemma store_fun_spec
        tid E R_src R_tgt r g (Q : R_src -> R_tgt -> iProp) ps pt
        itr_src ktr_tgt
        (IN: ↑N_state_tgt ⊆ E)
        l v v0
        :
      (tgt_interp_as l_mem memory_black)
      -∗
      (points_to l v0)
      -∗
      (points_to l v -∗ stsim tid E r g Q ps true itr_src (ktr_tgt tt))
      -∗
      stsim tid E r g Q ps pt
        itr_src
        (map_event emb_mem (SCMem.store_fun (l, v)) >>= ktr_tgt).
  Proof.
    i. iIntros "#ST PT SIM". iInv "ST" as (st) "ST1" "V".
    iDestruct "ST1" as (vs) "[VW MEM]". rred2.
    iApply stsim_getR. iSplit. iFrame. rred2. rewrite Lens.view_set.
    iPoseProof (memory_ra_store with "MEM PT") as "STORE".
    iDestruct "STORE" as (m1) "[%STORE1 MB]". iMod ("MB") as "MB".
    rewrite STORE1. rred2. iApply (stsim_modifyR with "VW"). iIntros "STTGT". rred2.
    iDestruct "MB" as "[MB PT]".
    iMod ("V" with "[STTGT MB]") as "_".
    { iExists _. iFrame. unfold Lens.modify. rewrite Lens.set_set. iFrame. }
    iApply "SIM"; iFrame.
  Qed.

  Lemma load_fun_spec
        tid E R_src R_tgt (Q : R_src -> R_tgt -> iProp)
        r g ps pt
        itr_src ktr_tgt
        (IN: ↑N_state_tgt ⊆ E)
        l v
    :
      (tgt_interp_as l_mem memory_black)
        -∗
        (points_to l v)
        -∗
        (points_to l v -∗ stsim tid E r g Q ps true itr_src (ktr_tgt v))
        -∗
        stsim tid E r g Q ps pt
        itr_src
        (map_event emb_mem (SCMem.load_fun l) >>= ktr_tgt).
  Proof.
    i. iIntros "#ST PT SIM". unfold SCMem.load_fun. rred2.
    iInv "ST" as (st) "ST1" "K".
    iDestruct "ST1" as (vw) "[VW MEM]".
    iApply stsim_getR. iSplit. iFrame. rred2.
    iPoseProof (memory_ra_load with "MEM PT") as "[%LOAD %PERM]".
    rewrite Lens.view_set. rewrite LOAD. rred2.
    iMod ("K" with "[VW MEM]") as "_". iExists _. iFrame.
    iApply "SIM". iFrame.
  Qed.

  Lemma faa_fun_spec
        tid E r g R_src R_tgt (Q : R_src -> R_tgt -> iProp) ps pt
        itr_src ktr_tgt
        (IN: ↑N_state_tgt ⊆ E)
        l add v
    :
      (tgt_interp_as l_mem memory_black)
      -∗
      (points_to l v)
      -∗
      (points_to l (SCMem.val_add v add) -∗ stsim tid E r g Q ps true itr_src (ktr_tgt v))
      -∗
      stsim tid E r g Q ps pt
        itr_src
        (map_event emb_mem (SCMem.faa_fun (l, add)) >>= ktr_tgt).
  Proof.
    i. iIntros "#ST PT SIM". unfold SCMem.faa_fun. rred2.
    iInv "ST" as (st) "ST1" "K". iDestruct "ST1" as (vw) "[VW MB]".
    iApply stsim_getR. iSplit. iFrame. rred2.
    iPoseProof (memory_ra_faa with "MB PT") as (m1) "[%FAA MB]".
    rewrite Lens.view_set. rewrite FAA. rred2.
    iApply (stsim_modifyR with "VW"). iIntros "STTGT". rred2.
    iMod "MB" as "[MB PT]".
    iMod ("K" with "[STTGT MB]") as "_".
    { iExists _. iFrame. unfold Lens.modify. rewrite Lens.set_set. iFrame. }
    iApply "SIM". iFrame.
  Qed.

  Definition memory_comparable (m : SCMem.t) (v : SCMem.val) : iProp :=
    match (SCMem.unwrap_ptr v) with
    | Some (vb, vo) =>
        match (SCMem.contents m) vb vo with
        | Some vv => True
        | None => False
        end
    | _ => True
    end.

  Lemma memory_comparable_store m m' l stv v :
    SCMem.store m l stv = Some m' ->
    memory_comparable m v ⊢ memory_comparable m' v.
  Proof.
    Local Transparent SCMem.store SCMem.mem_update. unfold SCMem.store, SCMem.mem_update, SCMem.unwrap_ptr.
    des_ifs.
    i; des_ifs; clarify. iIntros "MC". unfold memory_comparable. des_ifs. ss. des_ifs.
  Qed.

  Lemma val_compare_None m v1 v2 :
    SCMem.val_compare m v1 v2 = None ->
    (memory_comparable m v1 ∧ memory_comparable m v2) ⊢ False%I.
  Proof.
    i. iIntros "MC". unfold memory_comparable. unfold SCMem.val_compare, SCMem.has_permission in H.
    des_ifs; iDestruct "MC" as "[MC1 MC2]"; iFrame.
  Qed.

  Lemma val_compare_Some m v1 v2 b :
    SCMem.val_compare m v1 v2 = Some b ->
    if b then v1 = v2 else ~ v1 = v2.
  Proof.
    unfold SCMem.val_compare. i. des_ifs; ii; inv H0; congruence.
  Qed.

  Lemma cas_fun_spec
        tid E r g R_src R_tgt (Q : R_src -> R_tgt -> iProp) ps pt
        itr_src ktr_tgt
        (IN: ↑N_state_tgt ⊆ E)
        l old new v
        :
      (tgt_interp_as l_mem (fun m => memory_black m ** memory_comparable m v ** memory_comparable m old))
      -∗
      (points_to l v)
      -∗
      (points_to l v -∗ stsim tid E r g Q ps true itr_src (ktr_tgt false))
      -∗
      (points_to l new -∗ stsim tid E r g Q ps true itr_src (ktr_tgt true)) (* new = v ? *)
      -∗
      stsim tid E r g Q ps pt
        itr_src
        (map_event emb_mem (SCMem.cas_fun (l, old, new)) >>= ktr_tgt).
  Proof.
    i. iIntros "#ST PT CASF CAST". iInv "ST" as (st) "ST1" "K". iDestruct "ST1" as (vw) "[VW [[MB MC1] MC2]]".
    rred2. iApply stsim_getR. iSplit; [iFrame | ]. rred2.
    unfold SCMem.cas. iPoseProof (memory_ra_load with "MB PT") as "[%LOAD %PERM]".
    rewrite Lens.view_set. rewrite LOAD. des_ifs.
    - rred2. iApply (stsim_modifyR with "VW"). iIntros "STTGT". rred2.
      unfold Lens.modify. rewrite Lens.set_set.
      iPoseProof (memory_ra_store with "MB PT") as (m1) "[%STORE MEM]".
      rewrite STORE in Heq0; clarify. iMod ("MEM") as "[MB PT]".
      iMod ("K" with "[STTGT MB MC1 MC2]") as "_".
      { iPoseProof (memory_comparable_store with "MC1") as "COMP"; eauto.
        iPoseProof (memory_comparable_store with "MC2") as "COMP2"; eauto. iExists _. iFrame. }
      iApply "CAST". iFrame.
    - iPoseProof (memory_ra_store with "MB PT") as (m1) "[%STORE MEM]".
      rewrite STORE in Heq0; clarify.
    - rred2. iMod ("K" with "[VW MB MC1 MC2]") as "_".
      { iExists _. iFrame. }
      iApply "CASF". iFrame.
    - iPoseProof (val_compare_None with "[MC1 MC2]") as "CONT"; ss; eauto.
  Qed.

  Lemma cas_weak_fun_spec : True.
  Admitted.

  Lemma compare_fun_spec
        tid E r g R_src R_tgt (Q : R_src -> R_tgt -> iProp) ps pt
        itr_src ktr_tgt
        (IN: ↑N_state_tgt ⊆ E)
        v1 v2
        :
      (tgt_interp_as l_mem (fun m => memory_black m ** memory_comparable m v1 ** memory_comparable m v2))
      -∗
      (⌜~ (v1 = v2)⌝ -∗ stsim tid E r g Q ps true itr_src (ktr_tgt false))
      -∗
      (⌜v1 = v2⌝ -∗ stsim tid E r g Q ps true itr_src (ktr_tgt true))
      -∗
      stsim tid E r g Q ps pt
        itr_src
        (map_event emb_mem (SCMem.compare_fun (v1, v2)) >>= ktr_tgt).
  Proof.
    i. iIntros "#ST NEQ EQ". iInv "ST" as (st) "ST1" "K". iDestruct "ST1" as (vw) "[VW [[MB MC1] MC2]]".
    unfold SCMem.compare_fun. rred2.
    iApply stsim_getR. iSplit; iFrame. rred2.
    rewrite Lens.view_set. unfold SCMem.compare. destruct (SCMem.val_compare vw v1 v2) eqn:COMPR.
    - destruct b.
      + rred2. exploit val_compare_Some; eauto. i. ss; clarify.
        iMod ("K" with "[VW MB MC1 MC2]") as "_".
        { iExists _. iFrame. }
        iApply "EQ". ss.
      + rred2. exploit val_compare_Some; eauto. i. ss; clarify.
        iMod ("K" with "[VW MB MC1 MC2]") as "_".
        { iExists _. iFrame. }
        iApply "NEQ". ss.
    - exploit val_compare_None; eauto. i. iPoseProof x0 as "CONT". iExFalso.
      iApply "CONT"; iFrame.
  Qed.

End SPEC.
