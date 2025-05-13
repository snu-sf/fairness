From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Import ITreeLib Red TRed IRed2 LinkingRed.
From Fairness Require Import Mod Linking.
From Fairness Require Import PCM IPM.
From Fairness Require Import IndexedInvariants OpticsInterp SimWeakest.
From Fairness Require Import TemporalLogic.
From PromisingLib Require Import Loc Event.
From PromisingSEQ Require Import Time View TView Cell Memory Local.
From Fairness Require Export WMM.

Section SPEC.

  Import WMem.

  Context {STT : StateTypes}.
  Context `{sub : @SRA.subG Γ Σ}.
  Context {TLRASs : TLRAs_small STT Γ}.
  Context {TLRAS : TLRAs STT Γ Σ}.

  Context {HasWMEMRA: @GRA.inG wmemRA Γ}.

  Variable p_mem : Prism.t id_tgt_type WMM.WMem.ident.
  Variable l_mem : Lens.t st_tgt_type WMM.WMem.t.
  Let emb_mem := plmap p_mem l_mem.

  Lemma WMem_faa_fun_spec
          tid x y (LT : x < S y)
          E (IN : ↑N_state_tgt ⊆ E)
          V loc add (DEF : add <> Const.undef) v
      :
      ⊢ [@ tid, y, E @]
        {(tgt_interp_as l_mem (fun m => ((s_wmemory_black_strong p_mem m) : sProp x)))
          ∗ (loc ↦{faa} v)}
        (map_event emb_mem (WMem.faa_fun (V, loc, add, Ordering.plain, Ordering.acqrel)))
        {r, ∃ (V' : View.t),
          ⌜r = (V', v)⌝
          ∗ (loc ↦{faa} (Const.add v add))
          ∗ ⌜View.le V V'⌝}.
  Proof.
    iStartTriple. iIntros "[#ST PT] Q".
    unfold faa_fun.
    iInv "ST" as (st) "ST1" "V".
    iDestruct "ST1" as (vw) "[VW MEM]". simpl. red_tl_memra.
    rred2r. iApply wpsim_getR. iSplit. iFrame.
    rred2r. iApply wpsim_chooseR. iIntros "%".
    destruct x0. destruct x0 as [[[[lc2 to] val] sc1] mem1]. des.
    rename y0 into READ, y1 into WRITE. rred.

    iPoseProof (wmemory_ra_faa_strong with "MEM PT") as "[%FAA >[MEM0 MEM2]]".
    { rewrite Lens.view_set in READ. eapply READ. }
    { rewrite Lens.view_set in WRITE. eapply WRITE. }
    auto. auto. auto.
    iApply wpsim_fairR. auto.
    { i. instantiate (1:=[]). ss. clear - IN0. unfold prism_fmap, WMem.missed in IN0. des_ifs. }
    { i. instantiate (1:=[]) in IN0. inv IN0. }
    { econs. }
    { auto. }
    iIntros "_ _". rred2r. rewrite <- map_lens_Modify.
    iApply (wpsim_lens_modifyR with "[VW]"). auto. iIntros "VW". rred.
    iMod ("V" with "[MEM0 VW]") as "_".
    { iExists _. iFrame. red_tl_memra. auto. }
    iApply ("Q" with "[MEM2]"). iFrame. des; clarify. iExists _. iSplit; auto.
  Qed.

  Lemma WMem_load_fun_spec
          tid x y (LT : x < S y)
          E (IN : ↑N_state_tgt ⊆ E)
          V V2 loc k P Q
      :
      ⊢ [@ tid, y, E @]
        {(tgt_interp_as l_mem (fun m => ((s_wmemory_black_strong p_mem m) : sProp x)))
          ∗ (loc ↦(y, p_mem){full} V k P Q)}
        (map_event emb_mem (WMem.load_fun (V2, loc, Ordering.acqrel)))
        {r, ∃ (V3: View.t) (v: Const.t),
          ⌜r = (V3, v) /\ View.le V2 V3⌝
          ∗ (loc ↦(y, p_mem){full} V k P Q)
          ∗ ((lift_wProp P v V3) ∗ ◇[k](0, 1)
            ∨ ((lift_wProp Q v V3) ∗ (⌜View.le V V3⌝)))}.
  Proof.
    iStartTriple. iIntros "[#ST PT] Q".
    unfold load_fun.
    iInv "ST" as (st) "ST1" "V".
    iDestruct "ST1" as (vw) "[VW MEM]". simpl. red_tl_memra.
    rred2r. iApply wpsim_getR. iSplit. iFrame.
    rred2r. iApply wpsim_chooseR. iIntros "%".
    destruct x0. destruct x0 as [[[[lc2 to] val] sc1] mem1]. des.
    rename y0 into READ. rred.

    rewrite ! Lens.view_set in READ. rewrite ! Lens.view_set.
    iPoseProof (wmemory_ra_load_acq with "[MEM] PT") as "[% (MEM & PT & [S | F])]". eauto. eauto. auto. eauto.
    { iDestruct "S" as "[P (% & #PRM & %)]".
      iApply wpsim_fairR_prism. auto.
      { i. instantiate (1:=[]). ss. clear - IN0. unfold prism_fmap, WMem.missed in IN0. des_ifs. }
      { i. instantiate (1:=[(loc, ts)]) in IN0. inv IN0. done. inv H1. }
      eauto using List.NoDup. ss.
      iIntros "_ [CRED _]". iPoseProof (promise_progress with "[PRM CRED]") as "PC". iFrame. done.
      iMod "PC". iDestruct "PC" as "[PC | #CONTRA]"; cycle 1. ss.
      iMod ("V" with "[MEM VW]") as "_".
      { iExists _. iFrame. red_tl_memra. auto. }
      rred2r.
      iApply ("Q" with "[-]"). iFrame. iExists _, _. iSplit.
      2:{ iLeft. iFrame. } eauto.
    }
    { iApply wpsim_fairR_prism. auto.
      { i. instantiate (1:=[]). ss. clear - IN0. unfold prism_fmap, WMem.missed in IN0. des_ifs. }
      { i. instantiate (1:=[]) in IN0. inv IN0. }
      eauto using List.NoDup. ss.
      iIntros "_ _". rred2r.
      iMod ("V" with "[MEM VW]") as "_".
      { iExists _. iFrame. red_tl_memra. auto. }
      iApply ("Q" with "[-]"). iFrame. iExists _, _. iSplit.
      2:{ iRight. iFrame. } eauto.
    }
  Qed.

  Lemma WMem_load_fun_spec_rlx
          tid x y (LT : x < S y)
          E (IN : ↑N_state_tgt ⊆ E)
          V V1 loc k P Q
      :
      ⊢ [@ tid, y, E @]
        {(tgt_interp_as l_mem (fun m => ((s_wmemory_black_strong p_mem m) : sProp x)))
          ∗ (loc ↦(y, p_mem){full} V k P Q)
          ∗ ⌜View.le V V1⌝}
        (map_event emb_mem (WMem.load_fun (V1, loc, Ordering.relaxed)))
        {r, ∃ (V2: View.t) (v: Const.t),
          ⌜r = (V2, v) /\ View.le V1 V2⌝
          ∗ (loc ↦(y, p_mem){full} V k P Q)
          ∗ (lift_wProp Q v V2)}.
  Proof.
    iStartTriple. iIntros "[#ST [PT %LE]] Q".
    unfold load_fun.
    iInv "ST" as (st) "ST1" "V".
    iDestruct "ST1" as (vw) "[VW MEM]". simpl. red_tl_memra.
    rred2r. iApply wpsim_getR. iSplit. iFrame.
    rred2r. iApply wpsim_chooseR. iIntros "%".
    destruct x0. destruct x0 as [[[[lc2 to] val] sc1] mem1]. des.
    rename y0 into READ. rred.

    rewrite ! Lens.view_set in READ.
    iPoseProof (wmemory_ra_load_rlx with "MEM PT []") as "(%LE2 & MEM & PT & POST)". eauto. eauto. auto. eauto.
    iApply wpsim_fairR_prism. auto.
    { i. instantiate (1:=[]). ss. clear - IN0. unfold prism_fmap, WMem.missed in IN0. des_ifs. }
    { i. instantiate (1:=[]) in IN0. inv IN0. }
    eauto using List.NoDup. ss.
    iIntros "_ _".
    iMod ("V" with "[MEM VW]") as "_".
    { iExists _. iFrame. red_tl_memra. auto. }
    rred2r.
    iApply ("Q" with "[-]"). iFrame. iExists _, _. iSplit; auto.
  Qed.

  Lemma WMem_store_fun_spec
        tid x y (LT : x < S y)
        E (IN : ↑N_state_tgt ⊆ E)
        V V1 loc k P Q R val
    :
    ⊢ [@ tid, y, E @]
      {(tgt_interp_as l_mem (fun m => ((s_wmemory_black_strong p_mem m) : sProp x)))
        ∗ (loc ↦(y, p_mem){full} V k P Q)
        ∗ ⌜R val View.bot /\ val <> Const.undef⌝
        ∗ ⌜View.le V V1⌝}
      (map_event emb_mem (WMem.store_fun (V1, loc, val, Ordering.acqrel)))
      {r, ∃ (V2 V': View.t) (k': nat),
        ⌜r = V2 /\ View.le V1 V2 /\ View.le V' V2 /\ View.le V1 V'⌝
        ∗ (loc ↦(y, p_mem){full} V' k' (wor P Q) R)
        ∗ (◆[k', 1])}.
  Proof.
    iStartTriple. iIntros "[#ST [PT [%HR %LE]]] Q". des.
    unfold store_fun.
    iInv "ST" as (st) "ST1" "V".
    iDestruct "ST1" as (vw) "[VW MEM]". simpl. red_tl_memra.
    rred2r. iApply wpsim_getR. iSplit. iFrame.
    rred2r. iApply wpsim_chooseR. iIntros "%".
    destruct x0. destruct x0 as [[[lc2 to] sc1] mem1]. des.
    rename y0 into STORE. rred.

    rewrite ! Lens.view_set in STORE. rewrite ! Lens.view_set.
    iPoseProof (wmemory_ra_store_rel with "MEM PT [] []")
      as "(%VLE & > (WMEM & %V' & %k' & %VLE2 & %VLE3 & > [POST LO]))"; eauto.

    iApply wpsim_fairR_prism. auto.
    { i. instantiate (1:=[]). ss. clear - IN0. unfold prism_fmap, WMem.missed in IN0. des_ifs. }
    { i. instantiate (1:=[]) in IN0. inv IN0. }
    eauto using List.NoDup. ss.
    iIntros "_ _". rred2r.
    rewrite <- map_lens_Modify.
    iApply (wpsim_lens_modifyR with "VW"). iIntros "VW".
    iMod ("V" with "[WMEM VW]") as "_".
    { iExists _. iFrame. red_tl_memra. auto. }
    rred2r.
    iApply ("Q" with "[-]"). iFrame. iExists _, _, _. iSplit; auto.
  Qed.

End SPEC.

Global Opaque WMem.faa_fun WMem.load_fun WMem.store_fun.