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

  Definition wsat_auth_black (N : gset index) : IInvSetRA Vars :=
    (fun n => if (gset_elem_of_dec n N)
           then ε
           else @Auth.black (positive ==> URA.agree (Vars n))%ra (fun _ => None)).

  Definition wsat_auth (N : gset index) := OwnM (wsat_auth_black N).

  Definition wsat_satall (N : gset index) := ([∗ set] n ∈ N, wsat n)%I.

  Definition wsats : iProp := (∃ N, wsat_auth N ∗ wsat_satall N)%I.

  Lemma wsat_auth_nin (N : gset index) (n : index) (NIN : n ∉ N)
    : wsat_auth N ⊢ |==> wsat_auth ({[n]} ∪ N) ∗ wsat n.
  Proof.
    iIntros "AUTH".
    remember ({[n]} ∪ N) as N'.
    assert (URA.updatable
              (wsat_auth_black N)
              ((wsat_auth_black N')
                 ⋅
                 (maps_to_res_dep n (@Auth.black (positive ==> URA.agree (Vars n))%ra (fun (i : positive) => None))))).
    { apply pointwise_dep_updatable. i.
      unfold wsat_auth_black, maps_to_res_dep. unfold URA.add. unseal "ra". ss.
      destruct (excluded_middle_informative (a = n)).
      - subst a. des_ifs.
        2:{ exfalso. set_solver + n1. }
        unfold eq_rect_r. ss. rewrite URA.unit_idl. reflexivity.
      - subst N'. destruct (gset_elem_of_dec a N).
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

  Lemma wsat_satall_nin (N : gset index) (n : index) (NIN : n ∉ N)
    : wsat_satall N ∗ wsat n ⊢ wsat_satall ({[n]} ∪ N).
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
    destruct (gset_elem_of_dec n N).
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
    assert (Hin : n ∈ N).
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


    TODO

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


  REF

  Definition inv_auth_black (I : gmap positive Var) : IInvSetRA Vars :=
    @maps_to_res_dep index _
                     n (@Auth.black (positive ==> URA.agree Var)%ra
                                    (fun (i : positive) => Some <$> (I !! i))).

  Definition inv_auth (I : gmap positive Var) :=
    OwnM (inv_auth_black I).

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

End WSATS.

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
