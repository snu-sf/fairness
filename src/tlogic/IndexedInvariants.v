From stdpp Require Import coPset gmap namespaces.
From sflib Require Import sflib.
From Fairness Require Import Axioms PCM IProp IPM.
From iris Require Import bi.big_op.
From iris Require base_logic.lib.invariants.

Local Notation index := nat.

Section INDEXED_INVARIANT_SET.

  Context `{Σ : GRA.t}.

  Class IInvSet (Vars : index -> Type) :=
    { prop : forall (i : index), (Vars i) -> iProp }.

  Class IInvIn {Vars : index -> Type} `{IInvSet Vars} (n : index) (P : iProp) :=
    { inhabitant : Vars n
    ; inhabitant_eq : prop _ inhabitant = P
    }.

  Definition InvSetRA (Vars : index -> Type) (n : index) : URA.t :=
    (Auth.t (positive ==> URA.agree (Vars n)))%ra.

  Definition IInvSetRA (Vars : index -> Type) : URA.t :=
    @URA.pointwise_dep index (InvSetRA Vars).

End INDEXED_INVARIANT_SET.

Section PCM_OWN.

  Context `{Σ : GRA.t}.

  Definition OwnE `{@GRA.inG (index ==> CoPset.t)%ra Σ} (n : index) (E : coPset) :=
    OwnM (@maps_to_res index CoPset.t n (Some E)).

  Definition OwnD `{@GRA.inG (index ==> Gset.t)%ra Σ} (n : index) (D : gset positive) :=
    OwnM (@maps_to_res index Gset.t n (Some D)).

  Definition OwnI_white {Vars} (n : index) (i : positive) (p : Vars n) : IInvSetRA Vars :=
    @maps_to_res_dep index (@InvSetRA Vars)
                     n
                     (Auth.white (@maps_to_res positive (URA.agree (Vars n)) i (Some (Some p)))).

  Definition OwnI {Vars} `{@GRA.inG (IInvSetRA Vars) Σ} (n : index) (i : positive) (p : Vars n) :=
    OwnM (OwnI_white n i p).

  Lemma OwnE_index_diff `{@GRA.inG (index ==> CoPset.t)%ra Σ} n1 n2 (E : coPset) :
    (E <> ∅) -> OwnE n1 E ∗ OwnE n2 E ⊢ ⌜n1 <> n2⌝.
  Proof.
    intros NEMP.
    iIntros "[H1 H2]". iCombine "H1 H2" as "H". iPoseProof (OwnM_valid with "H") as "%WF".
    iPureIntro. unfold maps_to_res in WF. rewrite /URA.wf /URA.add in WF. unseal "ra".
    ss. intros EQ. subst n2. specialize (WF n1). des_ifs.
    rewrite /URA.wf /URA.add in WF. unseal "ra". ss. des_ifs. set_solver.
  Qed.

  Lemma OwnE_exploit `{@GRA.inG (index ==> CoPset.t)%ra Σ} n (E1 E2 : coPset) :
    OwnE n E1 ∗ OwnE n E2 ⊢ ⌜E1 ## E2⌝.
  Proof.
    iIntros "[H1 H2]". iCombine "H1 H2" as "H". iPoseProof (OwnM_valid with "H") as "%WF".
    iPureIntro. rewrite /URA.wf /URA.add in WF. unseal "ra". ss.
    specialize (WF n). unfold maps_to_res in WF. des_ifs.
    rewrite /URA.wf /URA.add in WF. unseal "ra". ss; des_ifs.
  Qed.

  Lemma OwnE_union `{@GRA.inG (index ==> CoPset.t)%ra Σ} n (E1 E2 : coPset) :
    OwnE n E1 ∗ OwnE n E2 ⊢ OwnE n (E1 ∪ E2).
  Proof.
    iIntros "H". iPoseProof (OwnE_exploit with "H") as "%D".
    iRevert "H". iApply from_sep. eapply from_sep_ownM.
    unfold IsOp, maps_to_res, URA.add. ss. extensionalities k. unseal "ra".
    des_ifs; ss.
    - unfold URA.add. unseal "ra". ss. des_ifs.
    - rewrite URA.unit_id. auto.
  Qed.

  Lemma OwnE_disjoint `{@GRA.inG (index ==> CoPset.t)%ra Σ} n (E1 E2 : coPset) :
    E1 ## E2 -> OwnE n (E1 ∪ E2) ⊢ OwnE n E1 ∗ OwnE n E2.
  Proof.
    i. unfold OwnE.
    iApply into_sep. eapply into_sep_ownM.
    unfold IsOp, maps_to_res, URA.add. unseal "ra". ss.
    extensionalities k. des_ifs.
    - unfold URA.add. unseal "ra". ss. des_ifs.
    - rewrite URA.unit_id. auto.
  Qed.

  Lemma OwnE_subset `{@GRA.inG (index ==> CoPset.t)%ra Σ} n (E1 E2 : coPset) :
    E1 ⊆ E2 -> OwnE n E2 ⊢ OwnE n E1 ∗ (OwnE n E1 -∗ OwnE n E2).
  Proof.
    iIntros (SUB) "E".
    assert (E2 = E1 ∪ E2 ∖ E1) as EQ.
    { eapply leibniz_equiv. eapply union_difference. ss. }
    rewrite EQ.
    iPoseProof (OwnE_disjoint with "E") as "[E1 E2]"; [set_solver|].
    iFrame. iIntros "E1".
    iApply OwnE_union. iFrame.
  Qed.

  Global Instance OwnI_persistent {Vars} `{@GRA.inG (IInvSetRA Vars) Σ}
    n i p : Persistent (OwnI n i p).
  Proof.
    unfold OwnI, OwnI_white.
    remember (@maps_to_res_dep index (InvSetRA Vars) n (Auth.white (@maps_to_res positive (URA.agree (Vars n)) i (Some (Some p))))) as r.
    unfold Persistent. iIntros "H".
    iPoseProof (@OwnM_persistently _ _ H _ with "H") as "#HP". iModIntro.
    replace r with (URA.core r) at 2. auto.
    subst. unfold maps_to_res_dep, maps_to_res. ss. extensionalities k. des_ifs.
  Qed.

End PCM_OWN.

Section WORLD_SATISFACTION.

  Context `{Σ : GRA.t}.
  Context `{Vars : index -> Type}.
  Context `{@IInvSet Σ Vars}.
  (* Context `{@InvSet Σ (Vars n)}. *)
  Context `{@GRA.inG (index ==> CoPset.t)%ra Σ}.
  Context `{@GRA.inG (index ==> Gset.t)%ra Σ}.
  Context `{@GRA.inG (IInvSetRA Vars) Σ}.

  Variable n : index.
  Local Notation Var := (Vars n).

  (* Context `{prop : Var -> iProp}. *)

  Definition inv_auth_black (I : gmap positive Var) : IInvSetRA Vars :=
    @maps_to_res_dep index _
                     n (@Auth.black (positive ==> URA.agree Var)%ra
                                    (fun (i : positive) => Some <$> (I !! i))).

  Definition inv_auth (I : gmap positive Var) := OwnM (inv_auth_black I).

  (* Definition inv_satall (I : gmap positive Var) := *)
  (*   ([∗ map] i ↦ p ∈ I, (prop p) ∗ OwnD n {[i]} ∨ OwnE n {[i]})%I. *)
  Definition inv_satall (I : gmap positive Var) :=
    ([∗ map] i ↦ p ∈ I, (prop n p) ∗ OwnD n {[i]} ∨ OwnE n {[i]})%I.

  Definition wsat : iProp := (∃ I, inv_auth I ∗ inv_satall I)%I.


  Lemma alloc_name φ
        (INF : forall (E : index -> option (gset positive)) n,
            match E n with
            | None => True
            | Some G => (exists i, i ∉ G /\ φ i)
            end)
    : ⊢ |==> ∃ i, ⌜φ i⌝ ∧ OwnD n {[i]}.
  Proof.
    assert (@URA.updatable_set
              (index ==> Gset.t)%ra
              (fun _ => (Some ∅ : Gset.t))
              (fun r => exists i, r = (maps_to_res n (Some {[i]} : Gset.t)) /\ φ i)) as UPD.
    { clear - INF. ii. apply URA.wf_split in WF; des. specialize (INF ctx n).
      des_ifs.
      - des. esplits; eauto.
        unfold maps_to_res, URA.wf, URA.add. unseal "ra". ss.
        i. des_ifs.
        + unfold URA.wf, URA.add in *. unseal "ra". ss.
          specialize (WF0 n). unfold URA.wf in WF0. unseal "ra". ss. des_ifs. set_solver.
        + rewrite URA.unit_idl. unfold URA.wf in WF0. unseal "ra". ss.
      - rr in WF0. unseal "ra". ss. specialize (WF0 n). rr in WF0. unseal "ra". ss.
        rewrite Heq in WF0. ss.
    }
    (* iPoseProof (@OwnM_unit _ _ H0) as "-# H". *)
    iPoseProof (@OwnM_unit _ _ H1) as "-# H".
    iMod (OwnM_Upd_set UPD with "H") as "[% [% DIS]]".
    iModIntro. des. subst. iExists i. eauto.
  Qed.

  Lemma wsat_OwnI_alloc p φ
        (INF : forall (E : index -> option (gset positive)) n,
            match E n with
            | None => True
            | Some G => (exists i, i ∉ G /\ φ i)
            end)
    (* : wsat ∗ prop p ⊢ |==> (∃ i, ⌜φ i⌝ ∧ OwnI n i p) ∗ wsat. *)
    : wsat ∗ prop n p ⊢ |==> (∃ i, ⌜φ i⌝ ∧ OwnI n i p) ∗ wsat.
  Proof.
    iIntros "[[% [AUTH SAT]] P]".
    iMod (alloc_name (fun i => i ∉ dom I /\ φ i)) as "[% [[%iI %iφ] D]]".
    { i.
      set (uni := fun n => match E n with
                        | None => None
                        | Some G => Some (G ∪ dom I)
                        end).
      specialize (INF uni n0). subst uni. ss. des_ifs.
      des. eapply not_elem_of_union in INF. des. esplits; eauto. }
    pose (<[i:=p]> I) as I'.

    assert (URA.updatable
              (maps_to_res_dep n (@Auth.black (positive ==> URA.agree Var)%ra (fun i => Some <$> (I !! i))) : IInvSetRA Vars)
              ((maps_to_res_dep n (@Auth.black (positive ==> URA.agree Var)%ra (fun i => Some <$> (I' !! i))) : IInvSetRA Vars)
                 ⋅
                 (maps_to_res_dep n (Auth.white (@maps_to_res _ (URA.agree Var) i (Some (Some p)))) : IInvSetRA Vars))).
    { setoid_rewrite maps_to_res_dep_add. apply maps_to_res_dep_updatable.
      apply Auth.auth_alloc. ii. des. rewrite URA.unit_idl in FRAME. subst. split.
      { rr; unseal "ra". ss. intro. rr; unseal "ra". destruct (I' !! k); ss. }
      rr. subst I'.
      unfold URA.add. unseal "ra". ss.
      extensionalities j. unfold maps_to_res. des_ifs.
      - rewrite lookup_insert. rewrite not_elem_of_dom_1; ss.
        unfold URA.add. unseal "ra". ss.
      - rewrite URA.unit_idl. rewrite lookup_insert_ne; eauto.
    }
    unfold inv_auth, inv_satall.
    (* iMod (OwnM_Upd H2 with "AUTH") as "[AUTH NEW]". iModIntro. *)
    iMod (OwnM_Upd H3 with "AUTH") as "[AUTH NEW]". iModIntro.

    iSplit.
    - iExists i. iFrame. ss.
    - unfold wsat. iExists I'. iFrame.
      unfold inv_satall. subst I'.
      iApply big_sepM_insert.
      { apply not_elem_of_dom_1; ss. }
      iSplitL "P D"; ss. iLeft. iFrame.
  Qed.

  Lemma wsat_OwnI_open i p :
    (* OwnI n i p ∗ wsat ∗ OwnE n {[i]} ⊢ |==> prop p ∗ wsat ∗ OwnD n {[i]}. *)
    OwnI n i p ∗ wsat ∗ OwnE n {[i]} ⊢ |==> prop n p ∗ wsat ∗ OwnD n {[i]}.
  Proof.
    iIntros "(I & [% [AUTH SAT]] & EN)". iModIntro.
    unfold OwnI, inv_auth, inv_satall.
    iCombine "AUTH I" as "AUTH".
    iPoseProof (OwnM_valid with "AUTH") as "%WF".
    assert (Hip : I !! i = Some p).
    { unfold inv_auth_black, OwnI_white in WF. setoid_rewrite maps_to_res_dep_add in WF.
      unfold maps_to_res_dep, maps_to_res in WF. apply (pwd_lookup_wf n) in WF. ss. des_ifs.
      unfold eq_rect_r in WF. rewrite <- Eqdep.EqdepTheory.eq_rect_eq in WF.
      apply Auth.auth_included in WF. rename WF into EXTENDS.
      apply pw_extends in EXTENDS. specialize (EXTENDS i).
      des_ifs. clear e e0. rr in EXTENDS. des. unfold URA.add in EXTENDS; unseal "ra".
      destruct (I !! i) eqn: E.
      - destruct ctx; ss; des_ifs.
      - destruct ctx; ss; des_ifs.
    }
    clear WF.
    iDestruct "AUTH" as "[AUTH I]".
    iPoseProof (big_sepM_delete _ _ _ _ Hip with "SAT") as "[[[H1 H2]|H1] SAT]".
    2: { iCombine "EN H1" as "F". iPoseProof (OwnM_valid with "F") as "%WF".
         exfalso. unfold maps_to_res, URA.wf, URA.add in WF. unseal "ra". ss.
         specialize (WF n). des_ifs. unfold URA.wf, URA.add in WF. unseal "ra".
         ss. des_ifs. set_solver.
    }
    iFrame. unfold wsat. iExists I. iFrame. unfold inv_satall.
    iApply (big_sepM_delete _ _ _ _ Hip). iFrame.
  Qed.

  Lemma wsat_OwnI_close i p :
    (* OwnI n i p ∗ wsat ∗ prop p ∗ OwnD n {[i]} ⊢ |==> wsat ∗ OwnE n {[i]}. *)
    OwnI n i p ∗ wsat ∗ prop n p ∗ OwnD n {[i]} ⊢ |==> wsat ∗ OwnE n {[i]}.
  Proof.
    iIntros "(I & [% [AUTH SAT]] & P & DIS)". iModIntro.
    unfold OwnI, inv_auth, inv_satall.
    iCombine "AUTH I" as "AUTH".
    iPoseProof (OwnM_valid with "AUTH") as "%WF".
    assert (Hip : I !! i = Some p).
    { unfold inv_auth_black, OwnI_white in WF. setoid_rewrite maps_to_res_dep_add in WF.
      unfold maps_to_res_dep, maps_to_res in WF. apply (pwd_lookup_wf n) in WF. ss. des_ifs.
      unfold eq_rect_r in WF. rewrite <- Eqdep.EqdepTheory.eq_rect_eq in WF.
      apply Auth.auth_included in WF. rename WF into EXTENDS.
      apply pw_extends in EXTENDS. specialize (EXTENDS i).
      des_ifs. clear e e0.
      rr in EXTENDS. des. unfold URA.add in EXTENDS; unseal "ra".
      destruct (I !! i) eqn: E.
      - destruct ctx; ss; des_ifs.
      - destruct ctx; ss; des_ifs.
    }
    clear WF.
    iDestruct "AUTH" as "[AUTH I]".
    iPoseProof (big_sepM_delete _ _ _ _ Hip with "SAT") as "[[[H1 H2]|H1] SAT]".
    { iCombine "DIS H2" as "F". iPoseProof (OwnM_valid with "F") as "%WF".
      exfalso. unfold maps_to_res, URA.wf, URA.add in WF. unseal "ra". ss.
      specialize (WF n). des_ifs.
      unfold URA.wf, URA.add in WF. unseal "ra". ss. des_ifs. set_solver.
    }
    iFrame. unfold wsat. iExists I. iFrame. unfold inv_satall.
    iApply (big_sepM_delete _ _ _ _ Hip). iFrame. iLeft. iFrame.
  Qed.

  Lemma wsat_init :
    OwnM (maps_to_res_dep n (@Auth.black (positive ==> URA.agree Var)%ra (fun (i : positive) => None)))
      ⊢ wsat.
  Proof.
    iIntros "H". iExists ∅. iFrame.
    unfold inv_satall. iApply big_sepM_empty. ss.
  Qed.

End WORLD_SATISFACTION.

Section WSATS.

  Context `{Σ : GRA.t}.
  Context `{Vars : index -> Type}.
  Context `{@IInvSet Σ Vars}.
  Context `{@GRA.inG (index ==> CoPset.t)%ra Σ}.
  Context `{@GRA.inG (index ==> Gset.t)%ra Σ}.
  Context `{@GRA.inG (IInvSetRA Vars) Σ}.

  Definition wsat_auth_black (X : gset index) : IInvSetRA Vars :=
    (fun n => if (gset_elem_of_dec n X)
           then ε
           else @Auth.black (positive ==> URA.agree (Vars n))%ra (fun _ => None)).

  Definition wsat_auth (X : gset index) := OwnM (wsat_auth_black X).

  Definition wsat_satall (X : gset index) := ([∗ set] n ∈ X, wsat n)%I.

  Definition wsats : iProp := (∃ X, wsat_auth X ∗ wsat_satall X)%I.


  Lemma wsat_auth_nin (X : gset index) (n : index) (NIN : n ∉ X)
    : wsat_auth X ⊢ |==> wsat_auth ({[n]} ∪ X) ∗ wsat n.
  Proof.
    iIntros "AUTH".
    remember ({[n]} ∪ X) as X'.
    assert (URA.updatable
              (wsat_auth_black X)
              ((wsat_auth_black X')
                 ⋅
                 (maps_to_res_dep n (@Auth.black (positive ==> URA.agree (Vars n))%ra (fun (i : positive) => None))))).
    { apply pointwise_dep_updatable. i.
      unfold wsat_auth_black, maps_to_res_dep. unfold URA.add. unseal "ra". ss.
      destruct (excluded_middle_informative (a = n)).
      - subst a. des_ifs.
        2:{ exfalso. set_solver + n1. }
        unfold eq_rect_r. ss. rewrite URA.unit_idl. reflexivity.
      - subst X'. destruct (gset_elem_of_dec a X).
        { des_ifs.
          - rewrite URA.unit_idl. reflexivity.
          - exfalso. set_solver + e n1.
        }
        { des_ifs.
          - set_solver + n0 n1 e.
          - rewrite URA.unit_id. reflexivity.
        }
    }
    unfold wsat_auth.
    iMod (OwnM_Upd H3 with "AUTH") as "[AUTH NEW]".
    iPoseProof (wsat_init with "NEW") as "NEW".
    iModIntro. iFrame.
  Qed.

  Lemma wsat_satall_nin (X : gset index) (n : index) (NIN : n ∉ X)
    : wsat_satall X ∗ wsat n ⊢ wsat_satall ({[n]} ∪ X).
  Proof.
    iIntros "[SALL WSAT]". unfold wsat_satall. iApply (big_sepS_insert); auto. iFrame.
  Qed.


  Lemma wsats_OwnI_alloc n p φ
        (INF : forall (E : index -> option (gset positive)) n,
            match E n with
            | None => True
            | Some G => (exists i, i ∉ G /\ φ i)
            end)
    : wsats ∗ prop n p ⊢ |==> (∃ i, ⌜φ i⌝ ∧ OwnI n i p) ∗ wsats.
  Proof.
    iIntros "[[% [AUTH SALL]] P]".
    destruct (gset_elem_of_dec n X).
    { iPoseProof (big_sepS_elem_of_acc with "SALL") as "[WSAT K]". apply e.
      iPoseProof (wsat_OwnI_alloc with "[WSAT P]") as ">[RES WSAT]". apply INF. iFrame.
      iPoseProof ("K" with "WSAT") as "SALL".
      iModIntro. iFrame. iExists _. iFrame.
    }
    { iMod (wsat_auth_nin with "AUTH") as "[AUTH WSAT]". apply n0.
      iPoseProof (wsat_OwnI_alloc with "[WSAT P]") as ">[RES WSAT]". apply INF. iFrame.
      iPoseProof (wsat_satall_nin with "[SALL WSAT]") as "SALL". apply n0. iFrame.
      iModIntro. iFrame. iExists _. iFrame.
    }
  Qed.

  Lemma wsats_OwnI_open n i p :
    OwnI n i p ∗ wsats ∗ OwnE n {[i]} ⊢ |==> prop n p ∗ wsats ∗ OwnD n {[i]}.
  Proof.
    iIntros "(I & [% [AUTH SAT]] & EN)".
    unfold OwnI, wsat_auth, wsat_satall.
    iCombine "AUTH I" as "AUTH".
    iPoseProof (OwnM_valid with "AUTH") as "%WF".
    assert (Hin : n ∈ X).
    { unfold wsat_auth_black, OwnI_white, maps_to_res_dep in WF. unfold URA.add in WF. unseal "ra". ss.
      apply (pwd_lookup_wf n) in WF. ss. des_ifs.
      exfalso. unfold eq_rect_r in WF. rewrite <- Eqdep.EqdepTheory.eq_rect_eq in WF.
      unfold maps_to_res in WF. apply Auth.auth_included in WF. rename WF into EXTENDS.
      apply pw_extends in EXTENDS. specialize (EXTENDS i). des_ifs.
      clear e e0. rr in EXTENDS. des. unfold URA.add in EXTENDS; unseal "ra".
      ss. des_ifs.
    }
    clear WF. iDestruct "AUTH" as "[AUTH I]".
    iPoseProof (big_sepS_elem_of_acc with "SAT") as "[WSAT K]". apply Hin.
    iMod (wsat_OwnI_open with "[I WSAT EN]") as "[P [WSAT DN]]". iFrame.
    iPoseProof ("K" with "WSAT") as "SAT".
    iModIntro. iFrame. iExists _. iFrame.
  Qed.

  Lemma wsats_OwnI_close n i p :
    OwnI n i p ∗ wsats ∗ prop n p ∗ OwnD n {[i]} ⊢ |==> wsats ∗ OwnE n {[i]}.
  Proof.
    iIntros "(I & [% [AUTH SAT]] & P & DIS)".
    unfold OwnI, wsat_auth, wsat_satall.
    iCombine "AUTH I" as "AUTH".
    iPoseProof (OwnM_valid with "AUTH") as "%WF".
    assert (Hin : n ∈ X).
    { unfold wsat_auth_black, OwnI_white, maps_to_res_dep in WF. unfold URA.add in WF. unseal "ra". ss.
      apply (pwd_lookup_wf n) in WF. ss. des_ifs.
      exfalso. unfold eq_rect_r in WF. rewrite <- Eqdep.EqdepTheory.eq_rect_eq in WF.
      unfold maps_to_res in WF. apply Auth.auth_included in WF. rename WF into EXTENDS.
      apply pw_extends in EXTENDS. specialize (EXTENDS i). des_ifs.
      clear e e0. rr in EXTENDS. des. unfold URA.add in EXTENDS; unseal "ra".
      ss. des_ifs.
    }
    clear WF. iDestruct "AUTH" as "[AUTH I]".
    iPoseProof (big_sepS_elem_of_acc with "SAT") as "[WSAT K]". apply Hin.
    iMod (wsat_OwnI_close with "[I WSAT P DIS]") as "[WSAT EN]". iFrame.
    iPoseProof ("K" with "WSAT") as "SAT".
    iModIntro. iFrame. iExists _. iFrame.
  Qed.

  Lemma wsats_init :
    OwnM ((fun n => @Auth.black (positive ==> URA.agree (Vars n))%ra (fun _ => None)) : IInvSetRA Vars)
         ⊢ wsats.
  Proof.
    iIntros "H". iExists ∅. iFrame.
    unfold wsat_satall. iApply big_sepS_empty. ss.
  Qed.

End WSATS.

Notation coPsets := (gmap index coPset).

Section OWNES.

  Context `{Σ : GRA.t}.
  Context `{@GRA.inG (index ==> CoPset.t)%ra Σ}.

  Definition OwnE_auth_black (Es : coPsets) : (index ==> CoPset.t)%ra :=
    fun n => match Es !! n with
          | Some _ => ε
          | None => (Some ⊤)
          end.

  Definition OwnE_auth (Es : coPsets) := OwnM (OwnE_auth_black Es).

  Definition OwnE_satall (Es : coPsets) := ([∗ map] n ↦ E ∈ Es, OwnE n E)%I.

  Definition OwnEs (Es : coPsets) := (OwnE_auth Es ∗ OwnE_satall Es)%I.

  Definition OwnEs_top (Es : coPsets) : Prop := map_Forall (fun _ E => E = ⊤) Es.

  Lemma OwnEs_alloc Es n (NIN : Es !! n = None) :
    OwnEs Es ⊢ |==> OwnEs (<[n := ⊤]>Es).
  Proof.
    iIntros "[AUTH SAT]". unfold OwnE_auth, OwnE_satall.
    remember (<[n := ⊤]> Es) as Es'.
    assert (URA.updatable
              (OwnE_auth_black Es)
              ((OwnE_auth_black Es')
                 ⋅
                 (maps_to_res n (Some ⊤)))).
    { apply pointwise_updatable. i.
      unfold OwnE_auth_black, maps_to_res. unfold URA.add. unseal "ra". ss. subst.
      destruct (excluded_middle_informative (a = n)).
      - subst a. des_ifs.
        2:{ exfalso. setoid_rewrite lookup_insert in Heq0. inv Heq0. }
        rewrite URA.unit_idl. reflexivity.
      - rewrite lookup_insert_ne; auto. rewrite URA.unit_id. reflexivity.
    }
    iMod (OwnM_Upd H0 with "AUTH") as "[AUTH NEW]". clear H0.
    iModIntro. iFrame. unfold OwnE_satall. subst. iApply big_sepM_insert; auto. iFrame.
  Qed.

  Lemma OwnEs_acc_in Es n E (IN : Es !! n = Some E) :
    OwnEs Es ⊢ OwnE n E ∗ OwnEs (<[n := ∅]>Es).
  Proof.
    iIntros "[AUTH SAT]". unfold OwnE_satall.
    iAssert (OwnE n E ∗ ([∗ map] n0↦E0 ∈ delete n Es, OwnE n0 E0))%I with "[SAT]" as "[EN SAT]".
    { iApply big_sepM_delete; auto. }
    iPoseProof (OwnM_persistently with "EN") as "#EN2". ss.
    iAssert ([∗ map] n0↦E0 ∈ <[n := ∅]>Es, OwnE n0 E0)%I with "[SAT]" as "SAT".
    { iApply big_sepM_insert_delete. iFrame. iApply (OwnM_extends with "EN2").
      unfold maps_to_res. clear. exists ε. rewrite URA.unit_id. extensionalities a. des_ifs.
    }
    iFrame. iClear "EN2".
    iApply (OwnM_extends with "AUTH"). exists ε. rewrite URA.unit_id. extensionalities a.
    unfold OwnE_auth_black. destruct (Nat.eqb_spec a n).
    - subst. rewrite lookup_insert. rewrite IN. auto.
    - rewrite lookup_insert_ne; auto.
  Qed.

  Lemma OwnEs_acc_new Es n (NIN : Es !! n = None) :
    OwnEs Es ⊢ |==> OwnE n ⊤ ∗ OwnEs (<[n := ∅]>Es).
  Proof.
    iIntros "ENS". iMod (OwnEs_alloc with "ENS") as "ENS". eauto.
    iModIntro.
    assert (<[n:=∅]> Es = <[n:=∅]> (<[n:=⊤]> Es)).
    { rewrite insert_insert. auto. }
    rewrite H0. iApply OwnEs_acc_in.
    - rewrite lookup_insert. auto.
    - iFrame.
  Qed.

  Lemma OwnEs_union Es n E1 E2 :
    OwnEs (<[n:=E1]> Es) ∗ OwnE n E2 ⊢ OwnEs (<[n:=E1 ∪ E2]> Es).
  Proof.
    iIntros "[[AUTH SAT] EN]". unfold OwnEs. iSplitL "AUTH".
    { iApply (OwnM_extends with "AUTH"). exists ε. rewrite URA.unit_id. extensionalities a.
      unfold OwnE_auth_black. destruct (Nat.eqb_spec a n).
      - subst. rewrite ! lookup_insert. auto.
      - rewrite ! lookup_insert_ne; auto.
    }
    iApply big_sepM_insert_delete.
    iAssert (OwnE n E1 ∗ (OwnE_satall (delete n (<[n:=E1]> Es))))%I with "[SAT]" as "[EN' SAT]".
    { iApply big_sepM_delete.
      - apply lookup_insert.
      - iFrame.
    }
    assert ((delete n (<[n:=E1]> Es)) = delete n Es).
    { rewrite delete_insert_delete. auto. }
    rewrite H0. iFrame. iApply OwnE_union. iFrame.
  Qed.


  Definition lookup_def (Es : coPsets) (n : nat) : coPset := default ⊤ (Es !! n).

  Definition subseteq_def (Es : coPsets) (n : nat) (E : coPset) : Prop :=
    match Es !! n with | Some E' => E ⊆ E' | None => True end.

  Definition insert_def (Es : coPsets) (n : nat) : coPsets :=
    match Es !! n with | Some E => Es | None => <[n:=⊤]> Es end.

  Lemma OwnEs_free Es n :
    Es !! n = None -> OwnEs (<[n:=⊤]>Es) ⊢ |==> OwnEs Es.
  Proof.
    iIntros (NIN) "ENS". iPoseProof (OwnEs_acc_in with "ENS") as "[EN ENS]". apply lookup_insert.
    rewrite insert_insert. unfold OwnEs. iDestruct "ENS" as "[AUTH SAT]".
    iSplitL "EN AUTH".
    - unfold OwnE_auth, OwnE. iCombine "EN AUTH" as "AUTH".
      assert (URA.updatable
                ((@maps_to_res index CoPset.t n (Some ⊤))
                   ⋅
                   OwnE_auth_black (<[n:=∅]> Es))
                (OwnE_auth_black Es)).
      { apply pointwise_updatable. i.
        unfold OwnE_auth_black, maps_to_res. unfold URA.add. unseal "ra". ss.
        destruct (excluded_middle_informative (a = n)).
        - subst a. rewrite lookup_insert. rewrite NIN.
          rewrite URA.unit_id. reflexivity.
        - rewrite lookup_insert_ne; auto. rewrite URA.unit_idl. reflexivity.
      }
      iMod (OwnM_Upd H0 with "AUTH") as "AUTH". iModIntro. iFrame.
    - unfold OwnE_satall. iModIntro.
      iPoseProof (big_sepM_insert with "SAT") as "[_ SAT]"; auto.
  Qed.

  Lemma OwnEs_lookup_def Es n :
    OwnEs Es ⊢ |==> OwnEs (<[n := lookup_def Es n]>Es).
  Proof.
    iIntros "ENS". unfold lookup_def, default. des_ifs; ss.
    - rewrite insert_id; auto.
    - iMod (OwnEs_alloc with "ENS") as "ENS"; eauto.
  Qed.

End OWNES.

Section FANCY_UPDATE.

  Context `{Σ : GRA.t}.
  Context `{Vars : index -> Type}.
  Context `{Invs : @IInvSet Σ Vars}.
  Context `{@GRA.inG (index ==> CoPset.t)%ra Σ}.
  Context `{@GRA.inG (index ==> Gset.t)%ra Σ}.
  Context `{@GRA.inG (IInvSetRA Vars) Σ}.

  Definition inv (n : index) (N : namespace) P :=
    (∃ p, ∃ i, ⌜prop n p = P⌝ ∧ ⌜i ∈ (↑N : coPset)⌝ ∧ OwnI n i p)%I.

  Definition FUpd (A : iProp) (Es1 Es2 : coPsets) (P : iProp) : iProp :=
    A ∗ wsats ∗ OwnEs Es1 -∗ #=> (A ∗ wsats ∗ OwnEs Es2 ∗ P).


  Lemma FUpd_alloc A Es n N P `{hasP : @IInvIn Σ Vars Invs n P} :
    P ⊢ FUpd A Es Es (inv n N P).
  Proof.
    destruct hasP as [p HE]. subst. iIntros "P (A & WSAT & EN)".
    iMod (wsats_OwnI_alloc n p (fun i => i ∈ ↑N) with "[WSAT P]") as "[I WSAT]".
    - i. des_ifs. apply iris.base_logic.lib.invariants.fresh_inv_name.
    - iFrame.
    - iModIntro. iFrame. iDestruct "I" as "[% I]". iExists p, i. iFrame. ss.
  Qed.

  Lemma FUpd_open_aux A Es n N E (INE : Es !! n = Some E) (IN : ↑N ⊆ E) P :
    inv n N P ⊢ FUpd A Es (<[n := E∖↑N]> Es) (P ∗ (P -∗ FUpd A (<[n := E∖↑N]> Es) Es emp)).
  Proof.
    iIntros "[% [% (%HP & %iN & #HI)]] (A & WSAT & ENS)". subst.
    iPoseProof ((OwnEs_acc_in _ _ _ INE) with "ENS") as "[EN ENS]".
    iAssert (OwnE n (E ∖ ↑N) ∗ OwnE n (↑N ∖ {[i]}) ∗ OwnE n {[i]})%I with "[EN]" as "(EN1 & EN2 & EN3)".
    { iApply bi.sep_mono_r.
      { apply OwnE_disjoint. set_solver. }
      iApply OwnE_disjoint.
      { set_solver. }
      replace (E ∖ ↑N ∪ (↑N ∖ {[i]} ∪ {[i]})) with E.
      - iFrame.
      - transitivity ({[i]} ∪ ↑N ∖ {[i]} ∪ E ∖ ↑N).
        + rewrite <- union_difference_singleton_L; ss. eapply union_difference_L; ss.
        + rewrite union_comm_L. f_equal. rewrite union_comm_L. ss.
    }
    iMod (wsats_OwnI_open n i p with "[HI WSAT EN3]") as "(P & WSAT & DIS)".
    { iFrame. auto. }
    iModIntro. iFrame. iPoseProof (OwnEs_union with "[ENS EN1]") as "ENS". iFrame.
    replace (∅ ∪ E ∖ ↑N) with (E ∖ ↑N). 2: set_solver.
    iFrame. iIntros "P (A & WSAT & EN1)".
    iMod (wsats_OwnI_close n i p with "[HI WSAT P DIS]") as "(WSAT & EN3)".
    { iFrame. auto. }
    iModIntro. iFrame. iSplit; auto.
    iPoseProof (OwnE_union with "[EN2 EN3]") as "EN2". iFrame.
    rewrite <- union_difference_singleton_L; ss.
    iPoseProof (OwnEs_union with "[EN1 EN2]") as "ENS". iFrame.
    rewrite insert_id. iFrame. rewrite INE. f_equal.
    rewrite difference_union_L. set_solver.
  Qed.

  Lemma FUpd_open A Es n N (IN : subseteq_def Es n (↑N)) P :
    inv n N P ⊢
        FUpd A Es (<[n := (lookup_def Es n)∖↑N]> Es) (P ∗ (P -∗ FUpd A (<[n := (lookup_def Es n)∖↑N]> Es) (insert_def Es n) emp)).
  Proof.
    iIntros "[% [% (%HP & %iN & #HI)]] (A & WSAT & ENS)". subst.
    unfold lookup_def, subseteq_def, insert_def in *. destruct (Es !! n) eqn:CASES; ss.
    - iApply FUpd_open_aux; auto. unfold inv; auto. iFrame.
    - iMod (OwnEs_alloc _ _ CASES with "ENS") as "ENS". remember (<[n:=⊤]> Es) as Es'.
      replace (<[n:=⊤ ∖ ↑N]> Es) with (<[n:=⊤ ∖ ↑N]> Es').
      2:{ subst. rewrite insert_insert. auto. }
      iApply FUpd_open_aux; auto.
      { subst. apply lookup_insert. }
      unfold inv; auto. iFrame.
  Qed.

  Lemma FUpd_intro A Es P :
    #=> P ⊢ FUpd A Es Es P.
  Proof.
    iIntros "P H". iMod "P". iModIntro. iFrame. iFrame.
  Qed.

  Lemma FUpd_mask_frame A Es1 Es2 E P n :
    (lookup_def Es1 n) ## E ->
    FUpd A Es1 Es2 P ⊢ FUpd A (<[n := (lookup_def Es1 n) ∪ E]>Es1) (<[n := (lookup_def Es2 n) ∪ E]>Es2) P.
  Proof.
    rewrite /FUpd. iIntros (D) "H (A & WSAT & ENS)".
    iPoseProof ((OwnEs_acc_in _ n) with "ENS") as "[EN ENS]". apply lookup_insert.
    iPoseProof (OwnE_disjoint _ _ _ D with "EN") as "[EN1 EN]".
    iPoseProof (OwnEs_union with "[ENS EN1]") as "ENS". iFrame.
    replace (∅ ∪ lookup_def Es1 n) with (lookup_def Es1 n) by set_solver.
    destruct (coPset_equiv_dec E ∅); cycle 1.
    { unfold lookup_def, default in D. des_ifs; ss.
      2:{ exfalso. set_solver. }
      rewrite insert_insert. rewrite (insert_id Es1).
      2:{ unfold lookup_def, default. rewrite Heq. ss. }
      iPoseProof ("H" with "[A WSAT ENS]") as ">(A & WSAT & ENS2 & P)". iFrame.
      destruct (Es2 !! n) eqn:CASES.
      2:{ iMod ((OwnEs_acc_new _ _ CASES) with "ENS2") as "[EN2 _]".
          iPoseProof (OwnE_exploit with "[EN EN2]") as "%DIS". iFrame.
          set_solver.
      }
      unfold lookup_def. rewrite CASES. ss.
      iPoseProof ((OwnEs_acc_in _ _ _ CASES) with "ENS2") as "[EN2 ENS]".
      iPoseProof (OwnE_union with "[EN EN2]") as "EN". iFrame.
      iPoseProof (OwnEs_union with "[ENS EN]") as "ENS". iFrame.
      replace (∅ ∪ (c0 ∪ E)) with (c0 ∪ E) by set_solver.
      iModIntro. iFrame.
    }
    { replace (lookup_def Es1 n ∪ E) with (lookup_def Es1 n) by set_solver.
      replace (lookup_def Es2 n ∪ E) with (lookup_def Es2 n) by set_solver.
      rewrite insert_insert.
      destruct (Es1 !! n) eqn:CASES.
      - rewrite (insert_id Es1).
        2:{ unfold lookup_def, default. rewrite CASES. ss. }
        iPoseProof ("H" with "[A WSAT ENS]") as ">(A & WSAT & ENS2 & P)". iFrame.
        iMod (OwnEs_lookup_def with "ENS2") as "ENS2". iModIntro. iFrame.
      - replace (lookup_def Es1 n) with (⊤ : coPset).
        2:{ unfold lookup_def, default. rewrite CASES. ss. }
        iMod ((OwnEs_free _ _ CASES) with "ENS") as "ENS".
        iPoseProof ("H" with "[A WSAT ENS]") as ">(A & WSAT & ENS2 & P)". iFrame.
        iMod (OwnEs_lookup_def with "ENS2") as "ENS2". iModIntro. iFrame.
    }
  Qed.

  TODO

  Lemma FUpd_intro_mask A E1 E2 P :
    E2 ⊆ E1 -> FUpd A E1 E1 P ⊢ FUpd A E1 E2 (FUpd A E2 E1 P).
  Proof.
    rewrite /FUpd. iIntros (HE) "H (A & WSAT & EN)".
    iPoseProof ("H" with "[A WSAT EN]") as ">(A & WSAT & EN & P)". iFrame.
    iModIntro.
    rewrite (union_difference_L _ _ HE).
    iPoseProof (OwnE_disjoint _ _ _ with "EN") as "[EN1 EN]".
    { set_solver. }
    iFrame. iIntros "(A & WSAT & EN2)". iModIntro. iFrame.
    iApply OwnE_union. iFrame.
  Qed.

  Lemma FUpd_mask_mono A E1 E2 P :
    E1 ⊆ E2 -> FUpd A E1 E1 P ⊢ FUpd A E2 E2 P.
  Proof.
    i. replace E2 with (E1 ∪ E2 ∖ E1).
    - eapply FUpd_mask_frame. set_solver.
    - symmetry. eapply leibniz_equiv. eapply union_difference. ss.
  Qed.

  Global Instance from_modal_FUpd A E P :
    FromModal True modality_id (FUpd A E E P) (FUpd A E E P) P.
  Proof.
    rewrite /FromModal /= /FUpd. iIntros. iModIntro. iFrame. iFrame.
  Qed.

  Global Instance from_modal_FUpd_general A E1 E2 P :
    FromModal (E2 ⊆ E1) modality_id P (FUpd A E1 E2 P) P.
  Proof.
    rewrite /FromModal /FUpd. ss.
    iIntros (HE) "P (A & WSAT & EN)". iModIntro. iFrame.
    iPoseProof ((OwnE_subset _ _ _ HE) with "EN") as "[EN1 _]". iFrame.
  Qed.

  Global Instance from_modal_FUpd_wrong_mask A E1 E2 P :
    FromModal (pm_error "Only non-mask-changing update modalities can be introduced directly.
Use [FUpd_mask_frame] and [FUpd_intro_mask]")
              modality_id (FUpd A E1 E2 P) (FUpd A E1 E2 P) P | 100.
  Proof.
    intros [].
  Qed.

  Global Instance elim_modal_bupd_FUpd p A E1 E2 P Q :
    ElimModal True p false (|==> P) P (FUpd A E1 E2 Q) (FUpd A E1 E2 Q) | 10.
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim /FUpd.
    iIntros (_) "[P K] I". iMod "P". iApply ("K" with "P"). iFrame.
  Qed.

  Global Instance elim_modal_FUpd_FUpd p A E1 E2 E3 P Q :
    ElimModal True p false (FUpd A E1 E2 P) P (FUpd A E1 E3 Q) (FUpd A E2 E3 Q).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim /FUpd.
    iIntros (_) "[P K] I". iMod ("P" with "I") as "(A & WSAT & EN & P)".
    iApply ("K" with "P"). iFrame.
  Qed.

  Global Instance elim_modal_FUpd_FUpd_general p A E0 E1 E2 E3 P Q :
    ElimModal (E0 ⊆ E2) p false (FUpd A E0 E1 P) P (FUpd A E2 E3 Q) (FUpd A (E1 ∪ (E2 ∖ E0)) E3 Q) | 10.
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim. ss.
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

Section FANCY_UPDATE.

  Context `{Σ : GRA.t}.
  Context `{Vars : index -> Type}.
  Context `{Invs : @IInvSet Σ Vars}.
  (* Context `{Invs : @InvSet Σ (Vars n)}. *)
  Context `{@GRA.inG (index ==> CoPset.t)%ra Σ}.
  Context `{@GRA.inG (index ==> Gset.t)%ra Σ}.
  Context `{@GRA.inG (IInvSetRA Vars) Σ}.

  Variable n : index.

  Local Notation Var := (Vars n).

  Definition inv (N : namespace) P :=
    (∃ p, ∃ i, ⌜prop n p = P⌝ ∧ ⌜i ∈ (↑N : coPset)⌝ ∧ OwnI n i p)%I.

  Definition FUpd (A : iProp) (E1 E2 : coPset) (P : iProp) : iProp :=
    (* A ∗ wsat (prop:=prop n) n ∗ OwnE n E1 -∗ #=> (A ∗ wsat (prop:=prop n) n ∗ OwnE n E2 ∗ P). *)
    A ∗ wsat n ∗ OwnE n E1 -∗ #=> (A ∗ wsat n ∗ OwnE n E2 ∗ P).

  Lemma FUpd_alloc A E N P `{hasP : @IInvIn Σ Vars Invs n P} :
    P ⊢ FUpd A E E (inv N P).
  Proof.
    destruct hasP as [p HE]. subst. iIntros "P (A & WSAT & EN)".
    (* iMod (wsat_OwnI_alloc (prop:=prop n) n p (fun i => i ∈ ↑N) with "[WSAT P]") as "[I WSAT]". *)
    iMod (wsat_OwnI_alloc n p (fun i => i ∈ ↑N) with "[WSAT P]") as "[I WSAT]".
    - i. des_ifs. apply iris.base_logic.lib.invariants.fresh_inv_name.
    - iFrame.
    - iModIntro. iFrame. iDestruct "I" as "[% I]". iExists p, i. iFrame. ss.
  Qed.

  Lemma FUpd_open A E N (IN : ↑N ⊆ E) P :
    inv N P ⊢ FUpd A E (E∖↑N) (P ∗ (P -∗ FUpd A (E∖↑N) E emp)).
  Proof.
    iIntros "[% [% (%HP & %iN & #HI)]] (A & WSAT & EN)". subst.
    iAssert (OwnE n (E ∖ ↑N) ∗ OwnE n (↑N ∖ {[i]}) ∗ OwnE n {[i]})%I with "[EN]" as "(EN1 & EN2 & EN3)".
    { iApply bi.sep_mono_r.
      { apply OwnE_disjoint. set_solver. }
      iApply OwnE_disjoint.
      { set_solver. }
      replace (E ∖ ↑N ∪ (↑N ∖ {[i]} ∪ {[i]})) with E.
      - iFrame.
      - transitivity ({[i]} ∪ ↑N ∖ {[i]} ∪ E ∖ ↑N).
        + rewrite <- union_difference_singleton_L; ss. eapply union_difference_L; ss.
        + rewrite union_comm_L. f_equal. rewrite union_comm_L. ss.
    }
    iMod (wsat_OwnI_open n i p with "[HI WSAT EN3]") as "(P & WSAT & DIS)".
    { iFrame. auto. }
    iModIntro. iFrame. iIntros "P (A & WSAT & EN1)".
    iMod (wsat_OwnI_close n i p with "[HI WSAT P DIS]") as "(WSAT & EN3)".
    { iFrame. auto. }
    iModIntro. iFrame. iSplit; auto.
    iPoseProof (OwnE_union with "[EN2 EN3]") as "EN2". iFrame.
    iPoseProof (OwnE_union with "[EN1 EN2]") as "EN". iFrame.
    rewrite <- union_difference_singleton_L; ss.
    rewrite <- union_difference_L; ss.
  Qed.

  Lemma FUpd_intro A E P :
    #=> P ⊢ FUpd A E E P.
  Proof.
    iIntros "P H". iMod "P". iModIntro. iFrame. iFrame.
  Qed.

  Lemma FUpd_mask_frame A E1 E2 E P :
    E1 ## E -> FUpd A E1 E2 P ⊢ FUpd A (E1 ∪ E) (E2 ∪ E) P.
  Proof.
    rewrite /FUpd. iIntros (D) "H (A & WSAT & EN)".
    iPoseProof (OwnE_disjoint _ _ _ D with "EN") as "[EN1 EN]".
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
    iPoseProof (OwnE_disjoint _ _ _ with "EN") as "[EN1 EN]".
    { set_solver. }
    iFrame. iIntros "(A & WSAT & EN2)". iModIntro. iFrame.
    iApply OwnE_union. iFrame.
  Qed.

  Lemma FUpd_mask_mono A E1 E2 P :
    E1 ⊆ E2 -> FUpd A E1 E1 P ⊢ FUpd A E2 E2 P.
  Proof.
    i. replace E2 with (E1 ∪ E2 ∖ E1).
    - eapply FUpd_mask_frame. set_solver.
    - symmetry. eapply leibniz_equiv. eapply union_difference. ss.
  Qed.

  Global Instance from_modal_FUpd A E P :
    FromModal True modality_id (FUpd A E E P) (FUpd A E E P) P.
  Proof.
    rewrite /FromModal /= /FUpd. iIntros. iModIntro. iFrame. iFrame.
  Qed.

  Global Instance from_modal_FUpd_general A E1 E2 P :
    FromModal (E2 ⊆ E1) modality_id P (FUpd A E1 E2 P) P.
  Proof.
    rewrite /FromModal /FUpd. ss.
    iIntros (HE) "P (A & WSAT & EN)". iModIntro. iFrame.
    iPoseProof ((OwnE_subset _ _ _ HE) with "EN") as "[EN1 _]". iFrame.
  Qed.

  Global Instance from_modal_FUpd_wrong_mask A E1 E2 P :
    FromModal (pm_error "Only non-mask-changing update modalities can be introduced directly.
Use [FUpd_mask_frame] and [FUpd_intro_mask]")
              modality_id (FUpd A E1 E2 P) (FUpd A E1 E2 P) P | 100.
  Proof.
    intros [].
  Qed.

  Global Instance elim_modal_bupd_FUpd p A E1 E2 P Q :
    ElimModal True p false (|==> P) P (FUpd A E1 E2 Q) (FUpd A E1 E2 Q) | 10.
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim /FUpd.
    iIntros (_) "[P K] I". iMod "P". iApply ("K" with "P"). iFrame.
  Qed.

  Global Instance elim_modal_FUpd_FUpd p A E1 E2 E3 P Q :
    ElimModal True p false (FUpd A E1 E2 P) P (FUpd A E1 E3 Q) (FUpd A E2 E3 Q).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim /FUpd.
    iIntros (_) "[P K] I". iMod ("P" with "I") as "(A & WSAT & EN & P)".
    iApply ("K" with "P"). iFrame.
  Qed.

  Global Instance elim_modal_FUpd_FUpd_general p A E0 E1 E2 E3 P Q :
    ElimModal (E0 ⊆ E2) p false (FUpd A E0 E1 P) P (FUpd A E2 E3 Q) (FUpd A (E1 ∪ (E2 ∖ E0)) E3 Q) | 10.
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim. ss.
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
