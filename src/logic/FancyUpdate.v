From stdpp Require Import coPset gmap.
From sflib Require Import sflib.
From Fairness Require Import PCM IProp IPM.
From iris Require Import bi.big_op.

Section INTERPRETATION.

  Class Interp `(Σ : GRA.t) :=
    { Var : Type
    ; prop : Var -> iProp
    }.

  Definition interpRA `{Interp} : URA.t := (Auth.t (positive ==> URA.agree Var)%ra).

End INTERPRETATION.

Section PCM_OWN.

  Context `{Σ : GRA.t}.

  Definition OwnE `{@GRA.inG CoPset.t Σ} (E : coPset) := OwnM (Some E).
  Definition OwnD `{@GRA.inG Gset.t Σ} (D : gset positive) := OwnM (Some D).
  Definition inv `{Interp} `{@GRA.inG interpRA Σ}
    (i : positive) (x : Var) :=
    OwnM (Auth.white (@maps_to_res positive (URA.agree Var) i (Some (Some x)))).

  Lemma OwnE_disjoint `{@GRA.inG CoPset.t Σ} (E1 E2 : coPset) :
    E1 ## E2 -> OwnE (E1 ∪ E2) ⊣⊢ OwnE E1 ∗ OwnE E2.
  Proof.
    i. unfold OwnE. iSplit.
    - iApply into_sep. eapply into_sep_ownM.
      unfold IsOp, URA.add. unseal "ra". ss. des_ifs.
    - iApply from_sep. eapply from_sep_ownM.
      unfold IsOp, URA.add. unseal "ra". ss. des_ifs.
  Qed.

  Lemma OwnE_not_disjoint `{@GRA.inG CoPset.t Σ} (E1 E2 : coPset) :
    ¬ E1 ## E2 -> OwnE E1 ∗ OwnE E2 ⊢ False.
  Proof.
    i. iIntros "H". iAssert (OwnM (None : CoPset.t)) with "[H]" as "H".
    - iRevert "H". iApply from_sep. eapply from_sep_ownM.
      unfold IsOp. unfold URA.add. unseal "ra". ss. des_ifs.
    - iPoseProof (OwnM_valid with "H") as "H".
      iRevert "H". iPureIntro. unfold URA.wf. unseal "ra". ss.
  Qed.

  Global Instance inv_persistent `{Interp} `{@GRA.inG (Auth.t (positive ==> URA.agree Var)%ra) Σ}
    i p : Persistent (inv i p).
  Proof.
    unfold inv. remember (Auth.white
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
  Context `{@Interp Σ}.
  Context `{@GRA.inG CoPset.t Σ}.
  Context `{@GRA.inG Gset.t Σ}.
  Context `{@GRA.inG interpRA Σ}.

  Definition inv_auth (I : gmap positive Var) :=
    OwnM (@Auth.black
            (positive ==> URA.agree Var)%ra
            (fun (i : positive) => Some <$> (I !! i))).

  Definition inv_satall (I : gmap positive Var) :=
    ([∗ map] i ↦ p ∈ I, prop p ∗ OwnD {[i]} ∨ OwnE {[i]})%I.

  Definition wsat : iProp := (∃ I, inv_auth I ∗ inv_satall I)%I.

  Lemma alloc_name (X : gset positive) :
    ⊢ |==> ∃ i, OwnD {[i]} ∧ ⌜i ∉ X⌝.
  Proof.
    assert (@URA.updatable_set Gset.t (Some ∅) (fun r => exists i, r = Some {[i]} /\ i ∉ X)) as UPD.
    { clear. ii. apply URA.wf_split in WF; des. destruct ctx as [D|].
      - assert (exists i, i ∉ D /\ i ∉ X) as [i [iD iI]].
        { exists (fresh (D ∪ X)). pose proof (is_fresh (D ∪ X)). set_solver. }
        exists (Some {[i]}). split.
        + exists i. ss.
        + unfold URA.wf, URA.add. unseal "ra". ss. des_ifs; set_solver.
      - rr in WF0. unseal "ra". ss.
    }
    iPoseProof (@OwnM_unit _ _ H1) as "-# H".
    iMod (OwnM_Upd_set UPD with "H") as "[% [% DIS]]".
    iModIntro. des. subst. iExists i. eauto.
  Qed.

  Lemma wsat_inv_alloc p :
    wsat ∗ prop p ⊢ |==> ∃ i, inv i p ∗ wsat.
  Proof.
    iIntros "[[% [AUTH SAT]] P]".
    unfold inv_auth, inv_satall.
    iMod (alloc_name (dom I)) as "[% [D %iI]]".
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

    iExists i. iFrame. unfold wsat. iExists I'. iFrame.
    unfold inv_satall. subst I'.
    iApply big_sepM_insert. { apply not_elem_of_dom_1; ss. }
    iSplitL "P D"; ss. iLeft. iFrame.
  Qed.

  Lemma wsat_inv_open i p :
    inv i p ∗ wsat ∗ OwnE {[i]} ⊢ |==> prop p ∗ wsat ∗ OwnD {[i]}.
  Proof.
    iIntros "(I & [% [AUTH SAT]] & EN)". iModIntro.
    unfold inv, inv_auth, inv_satall.
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

  Lemma wsat_inv_close i p :
    inv i p ∗ wsat ∗ prop p ∗ OwnD {[i]} ⊢ |==> wsat ∗ OwnE {[i]}.
  Proof.
    iIntros "(I & [% [AUTH SAT]] & P & DIS)". iModIntro.
    unfold inv, inv_auth, inv_satall.
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

End WORLD_SATISFACTION.

Section FANCY_UPDATE.

  Context `{Σ : GRA.t}.
  Context `{@Interp Σ}.
  Context `{@GRA.inG CoPset.t Σ}.
  Context `{@GRA.inG Gset.t Σ}.
  Context `{@GRA.inG (Auth.t (positive ==> URA.agree Var)%ra) Σ}.

  Definition FUpd (E1 E2 : coPset) (P : iProp) : iProp :=
    wsat ∗ OwnE E1 -∗ #=> (wsat ∗ OwnE E2 ∗ P).

  Lemma FUpd_open E i p (IN : i ∈ E) :
    inv i p ⊢ FUpd E (E∖{[i]}) (prop p ∗ (prop p -∗ FUpd (E∖{[i]}) E True)).
  Proof.
    iIntros "#H [WSAT EN]".
    iAssert (OwnE (E ∖ {[i]}) ∗ OwnE {[i]})%I with "[EN]" as "[EN1 EN2]".
    { iApply OwnE_disjoint. { set_solver. }
      iRevert "EN". replace E with ((E ∖ {[i]}) ∪ {[i]}) at 1. eauto.
      eapply leibniz_equiv. symmetry. transitivity ({[i]} ∪ E ∖ {[i]}).
      - apply union_difference; set_solver.
      - eapply union_comm.
    }
    iMod (wsat_inv_open i p with "[H WSAT EN2]") as "(P & WSAT & DIS)". { iFrame. iApply "H". }
    iModIntro. iFrame. iIntros "P [WSAT EN1]".
    iMod (wsat_inv_close i p with "[H WSAT P  DIS]") as "(WSAT & EN2)". { iFrame. iApply "H". }
    iModIntro. iFrame. iSplit; eauto.
    iAssert (OwnE (E∖{[i]} ∪ {[i]}))%I with "[EN1 EN2]" as "EN".
    { iApply OwnE_disjoint. set_solver. iFrame. }
    replace (E ∖ {[i]} ∪ {[i]}) with E. eauto.
    eapply leibniz_equiv. transitivity ({[i]} ∪ E ∖ {[i]}).
    - apply union_difference; set_solver.
    - eapply union_comm.
  Qed.

End FANCY_UPDATE.
