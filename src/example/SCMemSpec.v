From sflib Require Import sflib.
From Paco Require Import paco.
From stdpp Require namespaces.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Import ITreeLib Red TRed IRed2 LinkingRed.
From Fairness Require Import Mod Linking.
From Fairness Require Import PCM IProp IPM.
From Fairness Require Import SCMem IndexedInvariants OpticsInterp SimWeakest.


Section SPEC.

  Variable ident_src: ID.
  Variable ident_tgt: ID.
  Variable state_src: Type.
  Variable state_tgt: Type.

  Context `{Vars : nat -> Type}.
  Context `{Σ : GRA.t}.
  Context `{Invs : @IInvSet Σ Vars}.

  (* Invariant related default RAs *)
  Context `{OWNESRA : @GRA.inG OwnEsRA Σ}.
  Context `{OWNDSRA : @GRA.inG OwnDsRA Σ}.
  Context `{IINVSETRA : @GRA.inG (IInvSetRA Vars) Σ}.

  (* State related default RAs *)
  Context `{THDRA: @GRA.inG ThreadRA Σ}.
  Context `{STATESRC: @GRA.inG (stateSrcRA state_src) Σ}.
  Context `{STATETGT: @GRA.inG (stateTgtRA state_tgt) Σ}.
  Context `{IDENTSRC: @GRA.inG (identSrcRA ident_src) Σ}.
  Context `{IDENTTGT: @GRA.inG (identTgtRA ident_tgt) Σ}.

  (* Liveness logic related default RAs *)
  Context `{OBLGRA: @GRA.inG ObligationRA.t Σ}.
  Context `{EDGERA: @GRA.inG EdgeRA Σ}.
  Context `{ONESHOTRA: @GRA.inG ArrowShotRA Σ}.
  Context `{ARROWRA: @GRA.inG (@ArrowRA ident_tgt Vars) Σ}.

  (* SCMem related RAs *)
  Context `{MEMRA: @GRA.inG memRA Σ}.


  Variable p_mem : Prism.t ident_tgt SCMem.val.
  Variable l_mem : Lens.t state_tgt SCMem.t.
  Let emb_mem := plmap p_mem l_mem.

  Lemma alloc_fun_spec
        x y (LT : x < y)
        tid Es R_src R_tgt (Q : R_src -> R_tgt -> iProp)
        r g ps pt
        itr_src ktr_tgt
        (IN: match Es !! x with | Some E => ↑N_state_tgt ⊆ E | _ => True end)
        sz
    :
    (tgt_interp_as x l_mem memory_black)
      -∗
      (∀ l, points_tos l (repeat (SCMem.val_nat 0) sz) -∗ wpsim y tid Es r g Q ps true itr_src (ktr_tgt l))
      -∗
      (wpsim y tid Es r g Q ps pt
             itr_src
             (map_event emb_mem (SCMem.alloc_fun sz) >>= ktr_tgt)).
  Proof.
    unfold SCMem.alloc_fun. iIntros "#ST SIM".
    iInv "ST" as (st) "ST1" "V".
    iDestruct "ST1" as (vw) "[VW MEM]".
    rred2r. iApply wpsim_getR. iSplit. iFrame.
    destruct (SCMem.alloc ((id ∘ Lens.view l_mem) (Lens.set l_mem vw st)) sz) eqn: Hal.
    iPoseProof (memory_ra_alloc with "MEM") as "ALLOC".
    { ss. rewrite Lens.view_set in Hal. eauto. }
    rred2r. iApply (wpsim_modifyR with "VW"). iIntros "STTGT".
    rred2r.
    iMod "ALLOC" as "[MB PTS]". iMod ("V" with "[STTGT MB]") as "_".
    { iExists _. iFrame. unfold Vw_tgt. ss.
      replace (Lens.set l_mem t st) with (Lens.modify l_mem (λ _ : SCMem.t, t) (Lens.set l_mem vw st)).
      iFrame. unfold Lens.modify. rewrite Lens.set_set. ss.
    }
    iApply "SIM". iFrame.
  Qed.

  Lemma free_fun_spec
        x y (LT : x < y)
        tid Es r R_src R_tgt (Q : R_src -> R_tgt -> iProp) g ps pt
        itr_src ktr_tgt
        (IN: match Es !! x with | Some E => ↑N_state_tgt ⊆ E | _ => True end)
        p v
    :
    (tgt_interp_as x l_mem memory_black)
      -∗
      (points_to p v)
      -∗
      (wpsim y tid Es r g Q ps true itr_src (ktr_tgt tt))
      -∗
      wpsim y tid Es r g Q ps pt
      itr_src
      (map_event emb_mem (SCMem.free_fun p) >>= ktr_tgt).
  Proof.
    iIntros "#ST PT SIM". iInv "ST" as (st) "ST1" "V".
    iDestruct "ST1" as (vw) "[VW MB]".
    rred2r. iApply wpsim_getR. iSplit; [iFrame | ].
    rred2r. rewrite Lens.view_set.
    iPoseProof (memory_ra_free with "[MB PT]") as (m1) "[%FREE MB]"; [iFrame | ].
    rewrite FREE. rred2.
    iApply (wpsim_modifyR with "VW"). iIntros "STTGT". rred2. iMod "MB".
    iMod ("V" with "[STTGT MB]") as "_".
    { iExists _. iFrame. unfold Lens.modify. rewrite Lens.set_set. iFrame. }
    iApply "SIM".
  Qed.

  Lemma store_fun_spec
        x y (LT : x < y)
        tid Es R_src R_tgt r g (Q : R_src -> R_tgt -> iProp) ps pt
        itr_src ktr_tgt
        (IN: match Es !! x with | Some E => ↑N_state_tgt ⊆ E | _ => True end)
        l v v0
    :
    (tgt_interp_as x l_mem memory_black)
      -∗
      (points_to l v0)
      -∗
      (points_to l v -∗ wpsim y tid Es r g Q ps true itr_src (ktr_tgt tt))
      -∗
      wpsim y tid Es r g Q ps pt
      itr_src
      (map_event emb_mem (SCMem.store_fun (l, v)) >>= ktr_tgt).
  Proof.
    i. iIntros "#ST PT SIM". iInv "ST" as (st) "ST1" "V".
    iDestruct "ST1" as (vs) "[VW MEM]". rred2.
    iApply wpsim_getR. iSplit. iFrame. rred2. rewrite Lens.view_set.
    iPoseProof (memory_ra_store with "MEM PT") as "STORE".
    iDestruct "STORE" as (m1) "[%STORE1 MB]". iMod ("MB") as "MB".
    rewrite STORE1. rred2. iApply (wpsim_modifyR with "VW"). iIntros "STTGT". rred2.
    iDestruct "MB" as "[MB PT]".
    iMod ("V" with "[STTGT MB]") as "_".
    { iExists _. iFrame. unfold Lens.modify. rewrite Lens.set_set. iFrame. }
    iApply "SIM"; iFrame.
  Qed.

  Lemma load_fun_spec
        x y (LT : x < y)
        tid Es R_src R_tgt (Q : R_src -> R_tgt -> iProp)
        r g ps pt
        itr_src ktr_tgt
        (IN: match Es !! x with | Some E => ↑N_state_tgt ⊆ E | _ => True end)
        l v
    :
    (tgt_interp_as x l_mem memory_black)
      -∗
      (points_to l v)
      -∗
      (points_to l v -∗ wpsim y tid Es r g Q ps true itr_src (ktr_tgt v))
      -∗
      wpsim y tid Es r g Q ps pt
      itr_src
      (map_event emb_mem (SCMem.load_fun l) >>= ktr_tgt).
  Proof.
    i. iIntros "#ST PT SIM". unfold SCMem.load_fun. rred2.
    iInv "ST" as (st) "ST1" "K".
    iDestruct "ST1" as (vw) "[VW MEM]".
    iApply wpsim_getR. iSplit. iFrame. rred2.
    iPoseProof (memory_ra_load with "MEM PT") as "[%LOAD %PERM]".
    rewrite Lens.view_set. rewrite LOAD. rred2.
    iMod ("K" with "[VW MEM]") as "_". iExists _. iFrame.
    iApply "SIM". iFrame.
  Qed.

  Lemma faa_fun_spec
        x y (LT : x < y)
        tid Es r g R_src R_tgt (Q : R_src -> R_tgt -> iProp) ps pt
        itr_src ktr_tgt
        (IN: match Es !! x with | Some E => ↑N_state_tgt ⊆ E | _ => True end)
        l add v
    :
    (tgt_interp_as x l_mem memory_black)
      -∗
      (points_to l v)
      -∗
      (points_to l (SCMem.val_add v add) -∗ wpsim y tid Es r g Q ps true itr_src (ktr_tgt v))
      -∗
      wpsim y tid Es r g Q ps pt
      itr_src
      (map_event emb_mem (SCMem.faa_fun (l, add)) >>= ktr_tgt).
  Proof.
    i. iIntros "#ST PT SIM". unfold SCMem.faa_fun. rred2.
    iInv "ST" as (st) "ST1" "K". iDestruct "ST1" as (vw) "[VW MB]".
    iApply wpsim_getR. iSplit. iFrame. rred2.
    iPoseProof (memory_ra_faa with "MB PT") as (m1) "[%FAA MB]".
    rewrite Lens.view_set. rewrite FAA. rred2.
    iApply (wpsim_modifyR with "VW"). iIntros "STTGT". rred2.
    iMod "MB" as "[MB PT]".
    iMod ("K" with "[STTGT MB]") as "_".
    { iExists _. iFrame. unfold Lens.modify. rewrite Lens.set_set. iFrame. }
    iApply "SIM". iFrame.
  Qed.

  Lemma cas_fun_spec
        x y (LT : x < y)
        tid Es r g R_src R_tgt (Q : R_src -> R_tgt -> iProp) ps pt
        itr_src ktr_tgt
        (IN: mask_has_st_tgt Es x)
        l old new v
    :
    (tgt_interp_as x l_mem (fun m => memory_black m ∗ ⌜SCMem.memory_comparable m v⌝ ∗ ⌜SCMem.memory_comparable m old⌝))
      -∗
      (points_to l v)
      -∗
      (points_to l v -∗ wpsim y tid Es r g Q ps true itr_src (ktr_tgt false))
      -∗
      (points_to l new -∗ wpsim y tid Es r g Q ps true itr_src (ktr_tgt true)) (* new = v ? *)
      -∗
      wpsim y tid Es r g Q ps pt
      itr_src
      (map_event emb_mem (SCMem.cas_fun (l, old, new)) >>= ktr_tgt).
  Proof.
    Local Transparent SCMem.cas.
    iIntros "#ST PT CASF CAST". iInv "ST" as (st) "ST1" "K". iDestruct "ST1" as (vw) "[VW [MB [%MC1 %MC2]]]".
    rred2r. iApply wpsim_getR. iSplit; [iFrame | ].
    rred2r. unfold SCMem.cas. iPoseProof (memory_ra_load with "MB PT") as "[%LOAD %PERM]".
    rewrite Lens.view_set. rewrite LOAD.  des_ifs.
    - rred2r. iApply (wpsim_modifyR with "VW"). iIntros "STTGT".
      rred2r. unfold Lens.modify. rewrite Lens.set_set.
      iPoseProof (memory_ra_store with "MB PT") as (m1) "[%STORE MEM]".
      rewrite STORE in Heq0; clarify. iMod ("MEM") as "[MB PT]".
      iMod ("K" with "[STTGT MB]") as "_".
      { exploit SCMem.memory_comparable_store. eauto. apply MC1. intros COMP.
        exploit SCMem.memory_comparable_store. eauto. apply MC2. intros COMP2.
        iExists _. iFrame. iPureIntro. split; auto.
      }
      iApply "CAST". iFrame.
    - iPoseProof (memory_ra_store with "MB PT") as (m1) "[%STORE MEM]".
      rewrite STORE in Heq0; clarify.
    - rred2r. iMod ("K" with "[VW MB]") as "_".
      { iExists _. iFrame. iPureIntro. split; auto. }
      iApply "CASF". iFrame.
    - exploit SCMem.val_compare_None; eauto. intro F. ss.
    Local Opaque SCMem.cas.
  Qed.

  Lemma compare_fun_spec
        x y (LT : x < y)
        tid Es r g R_src R_tgt (Q : R_src -> R_tgt -> iProp) ps pt
        itr_src ktr_tgt
        (IN: mask_has_st_tgt Es x)
        v1 v2
    :
    (tgt_interp_as x l_mem (fun m => memory_black m ∗ ⌜SCMem.memory_comparable m v1⌝ ∗ ⌜SCMem.memory_comparable m v2⌝))
      -∗
      (⌜(v1 <> v2)⌝ -∗ wpsim y tid Es r g Q ps true itr_src (ktr_tgt false))
      -∗
      (⌜v1 = v2⌝ -∗ wpsim y tid Es r g Q ps true itr_src (ktr_tgt true))
      -∗
      wpsim y tid Es r g Q ps pt
      itr_src
      (map_event emb_mem (SCMem.compare_fun (v1, v2)) >>= ktr_tgt).
  Proof.
    iIntros "#ST NEQ EQ". iInv "ST" as (st) "ST1" "K". iDestruct "ST1" as (vw) "[VW [MB [%MC1 %MC2]]]".
    unfold SCMem.compare_fun. rred2r. iApply wpsim_getR. iSplit; iFrame.
    rred2r. rewrite Lens.view_set. unfold SCMem.compare. destruct (SCMem.val_compare vw v1 v2) eqn:COMPR.
    - destruct b.
      + rred2r. exploit SCMem.val_compare_Some; eauto. i. ss; clarify.
        iMod ("K" with "[VW MB]") as "_".
        { iExists _. iFrame. iSplit; auto. }
        iApply "EQ". ss.
      + rred2r. exploit SCMem.val_compare_Some; eauto. i. ss; clarify.
        iMod ("K" with "[VW MB]") as "_".
        { iExists _. iFrame. iSplit; auto. }
        iApply "NEQ". ss.
    - exploit SCMem.val_compare_None; eauto. i. ss.
  Qed.

End SPEC.
