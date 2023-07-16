From stdpp Require Import coPset gmap namespaces.
From sflib Require Import sflib.
From Fairness Require Import PCM IProp IPM.
From iris Require Import bi.big_op.
From iris Require base_logic.lib.invariants.

Section INVARIANT_SET.

  Context `{Σ : GRA.t}.

  Class InvSet :=
    { Var : Type
    ; prop : Var -> iProp
    }.

  Class InvIn `{InvSet} (P : iProp) :=
    { inhabitant : Var
    ; inhabitant_eq : prop inhabitant = P
    }.

  Definition InvSetRA (Var : Type) : URA.t := (Auth.t (positive ==> URA.agree Var)%ra).

End INVARIANT_SET.

Section PCM_OWN.

  Context `{Σ : GRA.t}.

  Definition OwnE `{@GRA.inG CoPset.t Σ} (E : coPset) := OwnM (Some E).
  Definition OwnD `{@GRA.inG Gset.t Σ} (D : gset positive) := OwnM (Some D).
  Definition OwnI `{InvSet} `{@GRA.inG (InvSetRA Var) Σ} (i : positive) (p : Var) :=
    OwnM (Auth.white (@maps_to_res positive (URA.agree Var) i (Some (Some p)))).

  Lemma OwnE_exploit `{@GRA.inG CoPset.t Σ} (E1 E2 : coPset) :
    OwnE E1 ∗ OwnE E2 ⊢ ⌜E1 ## E2⌝.
  Proof.
    iIntros "[H1 H2]". iCombine "H1 H2" as "H". iPoseProof (OwnM_valid with "H") as "%WF".
    iPureIntro. rewrite /URA.wf /URA.add in WF. unseal "ra". ss; des_ifs.
  Qed.

  Lemma OwnE_union `{@GRA.inG CoPset.t Σ} (E1 E2 : coPset) :
    OwnE E1 ∗ OwnE E2 ⊢ OwnE (E1 ∪ E2).
  Proof.
    iIntros "H". iPoseProof (OwnE_exploit with "H") as "%D".
    iRevert "H". iApply from_sep. eapply from_sep_ownM.
    unfold IsOp, URA.add. unseal "ra". ss. des_ifs.
  Qed.

  Lemma OwnE_disjoint `{@GRA.inG CoPset.t Σ} (E1 E2 : coPset) :
    E1 ## E2 -> OwnE (E1 ∪ E2) ⊢ OwnE E1 ∗ OwnE E2.
  Proof.
    i. unfold OwnE.
    iApply into_sep. eapply into_sep_ownM.
    unfold IsOp, URA.add. unseal "ra". ss. des_ifs.
  Qed.

  Lemma OwnE_subset `{@GRA.inG CoPset.t Σ} (E1 E2 : coPset) :
    E1 ⊆ E2 -> OwnE E2 ⊢ OwnE E1 ∗ (OwnE E1 -∗ OwnE E2).
  Proof.
    iIntros (SUB) "E".
    assert (E2 = E1 ∪ E2 ∖ E1) as EQ.
    { eapply leibniz_equiv. eapply union_difference. ss. }
    rewrite EQ.
    iPoseProof (OwnE_disjoint with "E") as "[E1 E2]"; [set_solver|].
    iFrame. iIntros "E1".
    iApply OwnE_union. iFrame.
  Qed.

  Global Instance OwnI_persistent `{InvSet} `{@GRA.inG (Auth.t (positive ==> URA.agree Var)%ra) Σ}
    i p : Persistent (OwnI i p).
  Proof.
    unfold OwnI. remember (Auth.white
                            (@maps_to_res
                               positive
                               (URA.agree Var)
                               i (Some (Some p)))) as r.
    unfold Persistent. iIntros "H".
    iPoseProof (@OwnM_persistently _ _ H0 _ with "H") as "#HP".
    iModIntro. replace r with (URA.core r) at 2 by (subst; ss). iApply "HP".
  Qed.

End PCM_OWN.

Section WORLD_SATISFACTION.

  Context `{Σ : GRA.t}.
  Context `{@InvSet Σ}.
  Context `{@GRA.inG CoPset.t Σ}.
  Context `{@GRA.inG Gset.t Σ}.
  Context `{@GRA.inG (InvSetRA Var) Σ}.

  Definition inv_auth (I : gmap positive Var) :=
    OwnM (@Auth.black
            (positive ==> URA.agree Var)%ra
            (fun (i : positive) => Some <$> (I !! i))).

  Definition inv_satall (I : gmap positive Var) :=
    ([∗ map] i ↦ p ∈ I, prop p ∗ OwnD {[i]} ∨ OwnE {[i]})%I.

  Definition wsat : iProp := (∃ I, inv_auth I ∗ inv_satall I)%I.

  Lemma alloc_name φ
    (INF : forall (E : gset positive) , exists i, i ∉ E /\ φ i)
    : ⊢ |==> ∃ i, ⌜φ i⌝ ∧ OwnD {[i]}.
  Proof.
    assert (@URA.updatable_set Gset.t (Some ∅) (fun r => exists i, r = Some {[i]} /\ φ i)) as UPD.
    { clear - INF. ii. apply URA.wf_split in WF; des. destruct ctx as [D|].
      - specialize (INF D). des. esplits; eauto.
        unfold URA.wf, URA.add. unseal "ra". ss. des_ifs; set_solver.
      - rr in WF0. unseal "ra". ss.
    }
    iPoseProof (@OwnM_unit _ _ H1) as "-# H".
    iMod (OwnM_Upd_set UPD with "H") as "[% [% DIS]]".
    iModIntro. des. subst. iExists i. eauto.
  Qed.

  Lemma wsat_OwnI_alloc p φ
    (INF : forall (E : gset positive) , exists i, i ∉ E /\ φ i)
    : wsat ∗ prop p ⊢ |==> (∃ i, ⌜φ i⌝ ∧ OwnI i p) ∗ wsat.
  Proof.
    iIntros "[[% [AUTH SAT]] P]".
    unfold inv_auth, inv_satall.
    iMod (alloc_name (fun i => i ∉ dom I /\ φ i)) as "[% [[%iI %iφ] D]]".
    { i. specialize (INF (E ∪ dom I)). des. eapply not_elem_of_union in INF. des. esplits; eauto. }
    pose (<[i:=p]> I) as I'.

    assert (URA.updatable
              (@Auth.black (positive ==> URA.agree Var)%ra (fun i => Some <$> (I !! i)))
              (@Auth.black
                 (positive ==> URA.agree Var)%ra
                 (fun i => Some <$> (I' !! i))
                 ⋅
                 (@Auth.white
                    (positive ==> URA.agree Var)%ra
                    (@maps_to_res _ (URA.agree Var) i (Some (Some p)))))).
    { apply Auth.auth_alloc. ii. des. rewrite URA.unit_idl in FRAME. subst. split.
      { rr; unseal "ra". ss. intro. rr; unseal "ra". destruct (I' !! k); ss. }
      rr. subst I'.
      unfold URA.add. unseal "ra". ss.
      extensionalities j. unfold maps_to_res. des_ifs.
      - rewrite lookup_insert. rewrite not_elem_of_dom_1; ss.
        unfold URA.add. unseal "ra". ss.
      - rewrite URA.unit_idl. rewrite lookup_insert_ne; eauto.
    }
    iMod (OwnM_Upd H3 with "AUTH") as "[AUTH NEW]". iModIntro.

    iSplit.
    - iExists i. iFrame. ss.
    - unfold wsat. iExists I'. iFrame.
      unfold inv_satall. subst I'.
      iApply big_sepM_insert. { apply not_elem_of_dom_1; ss. }
      iSplitL "P D"; ss. iLeft. iFrame.
  Qed.

  Lemma wsat_OwnI_open i p :
    OwnI i p ∗ wsat ∗ OwnE {[i]} ⊢ |==> prop p ∗ wsat ∗ OwnD {[i]}.
  Proof.
    iIntros "(I & [% [AUTH SAT]] & EN)". iModIntro.
    unfold OwnI, inv_auth, inv_satall.
    iCombine "AUTH I" as "AUTH".
    iPoseProof (OwnM_valid with "AUTH") as "%WF".
    assert (Hip : I !! i = Some p).
    { apply Auth.auth_included in WF. rename WF into EXTENDS.
      apply pw_extends in EXTENDS. specialize (EXTENDS i).
      unfold maps_to_res in EXTENDS. des_ifs. clear e.
      rr in EXTENDS. des. unfold URA.add in EXTENDS; unseal "ra".
      destruct (I !! i) eqn: E.
      - destruct ctx; ss; des_ifs.
      - destruct ctx; ss; des_ifs.
    }
    clear WF.
    iDestruct "AUTH" as "[AUTH I]".
    iPoseProof (big_sepM_delete _ _ _ _ Hip with "SAT") as "[[[H1 H2]|H1] SAT]".
    2: { iCombine "EN H1" as "F". iPoseProof (OwnM_valid with "F") as "%WF".
         unfold URA.wf, URA.add in WF. unseal "ra". ss. des_ifs. set_solver.
    }
    iFrame. unfold wsat. iExists I. iFrame. unfold inv_satall.
    iApply (big_sepM_delete _ _ _ _ Hip). iFrame.
  Qed.

  Lemma wsat_OwnI_close i p :
    OwnI i p ∗ wsat ∗ prop p ∗ OwnD {[i]} ⊢ |==> wsat ∗ OwnE {[i]}.
  Proof.
    iIntros "(I & [% [AUTH SAT]] & P & DIS)". iModIntro.
    unfold OwnI, inv_auth, inv_satall.
    iCombine "AUTH I" as "AUTH".
    iPoseProof (OwnM_valid with "AUTH") as "%WF".
    assert (Hip : I !! i = Some p).
    { apply Auth.auth_included in WF. rename WF into EXTENDS.
      apply pw_extends in EXTENDS. specialize (EXTENDS i).
      unfold maps_to_res in EXTENDS. des_ifs. clear e.
      rr in EXTENDS. des. unfold URA.add in EXTENDS; unseal "ra".
      destruct (I !! i) eqn: E.
      - destruct ctx; ss; des_ifs.
      - destruct ctx; ss; des_ifs.
    }
    clear WF.
    iDestruct "AUTH" as "[AUTH I]".
    iPoseProof (big_sepM_delete _ _ _ _ Hip with "SAT") as "[[[H1 H2]|H1] SAT]".
    { iCombine "DIS H2" as "F". iPoseProof (OwnM_valid with "F") as "%WF".
      unfold URA.wf, URA.add in WF. unseal "ra". ss. des_ifs. set_solver.
    }
    iFrame. unfold wsat. iExists I. iFrame. unfold inv_satall.
    iApply (big_sepM_delete _ _ _ _ Hip). iFrame. iLeft. iFrame.
  Qed.

  Lemma wsat_init :
    OwnM (@Auth.black (positive ==> URA.agree Var)%ra (fun (i : positive) => None))
      ⊢ wsat.
  Proof.
    iIntros "H". iExists ∅. iFrame.
    unfold inv_satall. iApply big_sepM_empty. ss.
  Qed.

End WORLD_SATISFACTION.

Section FANCY_UPDATE.

  Context `{Σ : GRA.t}.
  Context `{Invs : @InvSet Σ}.
  Context `{@GRA.inG CoPset.t Σ}.
  Context `{@GRA.inG Gset.t Σ}.
  Context `{@GRA.inG (InvSetRA Var) Σ}.

  Definition inv (N : namespace) P :=
    (∃ p, ∃ i, ⌜prop p = P⌝ ∧ ⌜i ∈ (↑N : coPset)⌝ ∧ OwnI i p)%I.

  Definition FUpd (A : iProp) (E1 E2 : coPset) (P : iProp) : iProp :=
    A ∗ wsat ∗ OwnE E1 -∗ #=> (A ∗ wsat ∗ OwnE E2 ∗ P).

  Lemma FUpd_alloc A E N P `{hasP : @InvIn Σ Invs P} :
    P ⊢ FUpd A E E (inv N P).
  Proof.
    destruct hasP as [p HE]. subst. iIntros "P (A & WSAT & EN)".
    iMod (wsat_OwnI_alloc p (fun i => i ∈ ↑N) with "[WSAT P]") as "[I WSAT]".
    - i. apply iris.base_logic.lib.invariants.fresh_inv_name.
    - iFrame.
    - iModIntro. iFrame. iDestruct "I" as "[% I]". iExists p, i. iFrame. ss.
  Qed.

  Lemma FUpd_open A E N (IN : ↑N ⊆ E) P :
    inv N P ⊢ FUpd A E (E∖↑N) (P ∗ (P -∗ FUpd A (E∖↑N) E emp)).
  Proof.
    iIntros "[% [% (%HP & %iN & #HI)]] (A & WSAT & EN)". subst.
    iAssert (OwnE (E ∖ ↑N) ∗ OwnE (↑N ∖ {[i]}) ∗ OwnE {[i]})%I with "[EN]" as "(EN1 & EN2 & EN3)".
    {
      iApply bi.sep_mono_r. { apply OwnE_disjoint. set_solver. }
      iApply OwnE_disjoint. { set_solver. }
      replace (E ∖ ↑N ∪ (↑N ∖ {[i]} ∪ {[i]})) with E.
      - ss.
      - transitivity ({[i]} ∪ ↑N ∖ {[i]} ∪ E ∖ ↑N).
        + rewrite <- union_difference_singleton_L; ss. eapply union_difference_L; ss.
        + rewrite union_comm_L. f_equal. rewrite union_comm_L. ss.
    }
    iMod (wsat_OwnI_open i p with "[HI WSAT EN3]") as "(P & WSAT & DIS)". { iFrame. iApply "HI". }
    iModIntro. iFrame. iIntros "P (A & WSAT & EN1)".
    iMod (wsat_OwnI_close i p with "[HI WSAT P DIS]") as "(WSAT & EN3)". { iFrame. iApply "HI". }
    iModIntro. iFrame. iSplit; eauto.
    iPoseProof (OwnE_union with "[EN2 EN3]") as "EN2". iFrame.
    iPoseProof (OwnE_union with "[EN1 EN2]") as "EN". iFrame.
    rewrite <- union_difference_singleton_L; ss.
    rewrite <- union_difference_L; ss.
  Qed.

  Lemma FUpd_intro A E P :
    #=> P ⊢ FUpd A E E P.
  Proof. iIntros "P H". iMod "P". iModIntro. iFrame. iFrame. Qed.

  Lemma FUpd_mask_frame A E1 E2 E P :
    E1 ## E -> FUpd A E1 E2 P ⊢ FUpd A (E1 ∪ E) (E2 ∪ E) P.
  Proof.
    rewrite /FUpd. iIntros (D) "H (A & WSAT & EN)".
    iPoseProof (OwnE_disjoint _ _ D with "EN") as "[EN1 EN]".
    iPoseProof ("H" with "[A WSAT EN1]") as ">(A & WSAT & EN2 & P)". iFrame.
    iModIntro. iFrame. iApply OwnE_union. iFrame.
  Qed.

  Lemma FUpd_intro_mask A E1 E2 P :
    E2 ⊆ E1 -> FUpd A E1 E1 P ⊢ FUpd A E1 E2 (FUpd A E2 E1 P).
  Proof.
    rewrite /FUpd. iIntros (HE) "H (A & WSAT & EN)".
    iPoseProof ("H" with "[A WSAT EN]") as ">(A & WSAT & EN & P)". iFrame.
    iModIntro.
    rewrite (union_difference_L _ _ HE).
    iPoseProof (OwnE_disjoint _ _ with "EN") as "[EN1 EN]". { set_solver. }
    iFrame. iIntros "(A & WSAT & EN2)". iModIntro. iFrame.
    iApply OwnE_union. iFrame.
  Qed.

  Lemma FUpd_mask_mono A E1 E2 P :
    E1 ⊆ E2 -> FUpd A E1 E1 P ⊢ FUpd A E2 E2 P.
  Proof.
    i. replace E2 with (E1 ∪ E2 ∖ E1).
    - eapply FUpd_mask_frame; set_solver.
    - symmetry. eapply leibniz_equiv. eapply union_difference. ss.
  Qed.

  Global Instance from_modal_FUpd A E P :
    FromModal True modality_id (FUpd A E E P) (FUpd A E E P) P.
  Proof. rewrite /FromModal /= /FUpd. iIntros. iModIntro. iFrame. iFrame. Qed.

  Global Instance from_modal_FUpd_general A E1 E2 P :
    FromModal (E2 ⊆ E1) modality_id P (FUpd A E1 E2 P) P.
  Proof. rewrite /FromModal /FUpd. ss.
         iIntros (HE) "P (A & WSAT & EN)". iModIntro. iFrame.
         replace E1 with (E2 ∪ E1 ∖ E2).
         - iPoseProof (OwnE_disjoint with "EN") as "[EN1 EN2]". set_solver. ss.
         - symmetry. eapply union_difference_L. ss.
  Qed.

  Global Instance from_modal_FUpd_wrong_mask A E1 E2 P :
    FromModal (pm_error "Only non-mask-changing update modalities can be introduced directly.
Use [FUpd_mask_frame] and [FUpd_intro_mask]")
              modality_id (FUpd A E1 E2 P) (FUpd A E1 E2 P) P | 100.
  Proof. intros []. Qed.

  Global Instance elim_modal_bupd_FUpd p A E1 E2 P Q :
    ElimModal True p false (|==> P) P (FUpd A E1 E2 Q) (FUpd A E1 E2 Q) | 10.
  Proof. rewrite /ElimModal bi.intuitionistically_if_elim /FUpd.
         iIntros (_) "[P K] I". iMod "P". iApply ("K" with "P"). iFrame.
  Qed.

  Global Instance elim_modal_FUpd_FUpd p A E1 E2 E3 P Q :
    ElimModal True p false (FUpd A E1 E2 P) P (FUpd A E1 E3 Q) (FUpd A E2 E3 Q).
  Proof. rewrite /ElimModal bi.intuitionistically_if_elim /FUpd.
         iIntros (_) "[P K] I". iMod ("P" with "I") as "(A & WSAT & EN & P)".
         iApply ("K" with "P"). iFrame.
  Qed.

  Global Instance elim_modal_FUpd_FUpd_general p A E0 E1 E2 E3 P Q :
    ElimModal (E0 ⊆ E2) p false (FUpd A E0 E1 P) P (FUpd A E2 E3 Q) (FUpd A (E1 ∪ (E2 ∖ E0)) E3 Q) | 10.
  Proof. rewrite /ElimModal bi.intuitionistically_if_elim. ss.
         iIntros (HE) "[M K]".
         iPoseProof (FUpd_mask_frame _ _ _ (E2 ∖ E0) with "M") as "M".
         { set_solver. }
         replace (E0 ∪ E2 ∖ E0) with E2 by (eapply union_difference_L; ss).
         iMod "M". iPoseProof ("K" with "M") as "M". ss.
  Qed.

  Global Instance elim_acc_FUpd {X : Type} A E1 E2 E (α β : X -> iProp) (mγ : X -> option iProp) (Q : iProp) :
    ElimAcc True (FUpd A E1 E2) (FUpd A E2 E1) α β mγ (FUpd A E1 E Q) (fun x : X => ((FUpd A E2 E2 (β x)) ∗ (mγ x -∗? FUpd A E1 E Q))%I).
  Proof.
    iIntros (_) "Hinner >[% [Hα Hclose]]".
    iPoseProof ("Hinner" with "Hα") as "[>Hβ Hfin]".
    iPoseProof ("Hclose" with "Hβ") as ">Hγ".
    iApply "Hfin". iFrame.
  Qed.

  Global Instance into_acc_FUpd_inv A E N P :
    IntoAcc (inv N P) (↑N ⊆ E) True (FUpd A E (E ∖ ↑N)) (FUpd A (E ∖ ↑N) E) (fun _ : () => P) (fun _ : () => P) (fun _ : () => None).
  Proof.
    rewrite /IntoAcc. iIntros (iE) "INV _". rewrite /accessor.
    iPoseProof (FUpd_open _ _ _ iE with "INV") as ">[open close]".
    iModIntro. iExists tt. iFrame.
  Qed.

  Global Instance elim_modal_iupd_FUpd p A E1 E2 P Q :
    ElimModal True p false (#=(A)=> P) P (FUpd A E1 E2 Q) (FUpd A E1 E2 Q) | 10.
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim /FUpd.
    iIntros (_) "[P K] [A I]".
    iMod ("P" with "A") as "[A P]". iApply ("K" with "P"). iFrame.
  Qed.
End FANCY_UPDATE.

Global Opaque FUpd.
