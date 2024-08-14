From stdpp Require Import coPset gmap namespaces.
From sflib Require Import sflib.
From Fairness Require Import Axioms PCM IPM.
From iris Require Import bi.big_op.
From iris Require base_logic.lib.invariants.
From iris.algebra Require Import auth agree coPset gset.

Local Notation index := nat.

Section INDEXED_INVARIANT_SET.

  Context `{Σ : GRA.t}.
  Notation iProp := (iProp Σ).

  Class IInvSet (Vars : index -> Type) :=
    { prop : forall (i : index), (Vars i) -> iProp }.

  Definition InvSetRA (Vars : index -> Type) (n : index) : ucmra :=
    (authUR (positive ==> optionUR (agreeR $ leibnizO (Vars n))))%ra.

  Definition IInvSetRA (Vars : index -> Type) : ucmra :=
    pointwise_dep (InvSetRA Vars).

  Definition OwnERA : ucmra := coPset_disjUR.
  Definition OwnDRA : ucmra := gset_disjUR positive.

End INDEXED_INVARIANT_SET.

Section PCM_OWN.

  Context `{Σ : GRA.t}.
  Notation iProp := (iProp Σ).
  Definition OwnE `{GRA.inG OwnERA Σ} (E : coPset) : iProp := OwnM (CoPset E).

  Definition OwnD `{GRA.inG OwnDRA Σ} (D : gset positive) := OwnM (GSet D).

  Definition OwnI_white {Vars} (n : index) (i : positive) (p : Vars n) : IInvSetRA Vars :=
    maps_to_res_dep n (◯ (maps_to_res i (Some $ to_agree (p : leibnizO (Vars n))))).

  Definition OwnI {Vars} `{GRA.inG (IInvSetRA Vars) Σ} (n : index) (i : positive) (p : Vars n) :=
    OwnM (OwnI_white n i p).

  Lemma OwnE_exploit `{GRA.inG OwnERA Σ} (E1 E2 : coPset) :
    OwnE E1 ∗ OwnE E2 ⊢ ⌜E1 ## E2⌝.
  Proof.
    iIntros "[H1 H2]". iCombine "H1 H2" as "H". iOwnWf "H" as WF.
    iPureIntro. by apply coPset_disj_valid_op.
  Qed.

  Lemma OwnE_union `{@GRA.inG OwnERA Σ} (E1 E2 : coPset) :
    OwnE E1 ∗ OwnE E2 ⊢ OwnE (E1 ∪ E2).
  Proof.
    iIntros "H". iDestruct (OwnE_exploit with "H") as %D.
    rewrite -OwnM_op coPset_disj_union //.
  Qed.

  Lemma OwnE_disjoint `{@GRA.inG OwnERA Σ} (E1 E2 : coPset) :
    E1 ## E2 -> OwnE (E1 ∪ E2) ⊢ OwnE E1 ∗ OwnE E2.
  Proof.
    iIntros (D) "H".
    rewrite /OwnE -OwnM_op coPset_disj_union //.
  Qed.

  Lemma OwnE_add `{@GRA.inG OwnERA Σ} (E1 E2 : coPset) :
    E1 ## E2 -> OwnE (E1 ∪ E2) ⊣⊢ OwnE E1 ∗ OwnE E2.
  Proof.
    i. iSplit.
    - iApply OwnE_disjoint. done.
    - iApply OwnE_union.
  Qed.
  Lemma OwnE_is_disjoint `{@GRA.inG OwnERA Σ} E1 E2 : OwnE E1 ∗ OwnE E2 ⊢ ⌜E1 ## E2⌝.
  Proof. apply OwnE_exploit. Qed.
  Lemma OwnE_add' `{@GRA.inG OwnERA Σ} E1 E2 : ⌜E1 ## E2⌝ ∧ OwnE (E1 ∪ E2) ⊣⊢ OwnE E1 ∗ OwnE E2.
  Proof.
    iSplit; [iIntros "[% ?]"; by iApply OwnE_add|].
    iIntros "HE". iDestruct (OwnE_is_disjoint with "HE") as %?.
    iSplit; first done. iApply OwnE_add; by try iFrame.
  Qed.
  Lemma OwnE_singleton_twice `{@GRA.inG OwnERA Σ} i : OwnE {[i]} ∗ OwnE {[i]} ⊢ False.
  Proof. rewrite OwnE_is_disjoint. iIntros (?); set_solver. Qed.

  Lemma OwnE_subset `{@GRA.inG OwnERA Σ} (E1 E2 : coPset) :
    E1 ⊆ E2 -> OwnE E2 ⊢ OwnE E1 ∗ (OwnE E1 -∗ OwnE E2).
  Proof.
    iIntros (SUB) "E".
    assert (E2 = E1 ∪ E2 ∖ E1) as EQ.
    { eapply union_difference_L. ss. }
    rewrite EQ.
    iPoseProof (OwnE_disjoint with "E") as "[E1 E2]"; [set_solver|].
    iFrame. iIntros "E1".
    iApply OwnE_union. iFrame.
  Qed.

  Global Instance OwnI_persistent {Vars} `{@GRA.inG (IInvSetRA Vars) Σ}
    n i p : Persistent (OwnI n i p).
  Proof.
    unfold OwnI, OwnI_white, Persistent. iIntros "H".
    iDestruct (OwnM_persistently with "H") as "#HP".
    iApply (OwnM_proper with "HP").
    intros k.
    rewrite /maps_to_res_dep /eq_rect_r discrete_fun_lookup_core.
    des_ifs. simpl.
    rewrite auth_frag_core. f_equiv. intros i'.
    rewrite /maps_to_res discrete_fun_lookup_core. des_ifs.
  Qed.

End PCM_OWN.

Section WORLD_SATISFACTION.

  Context `{Σ : GRA.t}.
  Context `{Vars : index -> Type}.
  Context `{@IInvSet Σ Vars}.
  Context `{@GRA.inG OwnERA Σ}.
  Context `{@GRA.inG OwnDRA Σ}.
  Context `{@GRA.inG (IInvSetRA Vars) Σ}.
  Notation iProp := (iProp Σ).

  Variable n : index.
  Local Notation Var := (Vars n).

  Definition inv_auth_black (I : gmap positive Var) : IInvSetRA Vars :=
    maps_to_res_dep n (@auth_auth (positive ==> (optionUR (agreeR $ leibnizO (Vars n))))%ra
                        (DfracOwn 1)
                        (fun (i : positive) => to_agree <$> (I !! i : option (leibnizO Var)))).

  Definition inv_auth (I : gmap positive Var) := OwnM (inv_auth_black I).

  Definition inv_satall (I : gmap positive Var) :=
    ([∗ map] i ↦ p ∈ I, (prop n p) ∗ OwnD {[i]} ∨ OwnE {[i]})%I.

  Definition wsat : iProp := (∃ I, inv_auth I ∗ inv_satall I)%I.


  Lemma alloc_name φ
    (INF : forall (E : gset positive), exists i, i ∉ E /\ φ i)
    : ⊢ |==> ∃ i, ⌜φ i⌝ ∧ OwnD {[i]}.
  Proof.
    assert ((GSet (∅ : gset positive)) ~~>: (fun r => exists i, r = GSet {[i]} /\ φ i)) as UPD.
    { clear - INF. apply gset_disj_alloc_empty_updateP_strong'. done. }
    iPoseProof (@OwnM_unit _ _ H1) as "-# H".
    iMod (OwnM_Upd_set _ _ UPD with "H") as "[% [% DIS]]".
    iModIntro. des. subst. iExists i. eauto.
  Qed.

  Lemma wsat_OwnI_alloc_gen p φ
        (INF : forall (E : gset positive), exists i, i ∉ E /\ φ i)
    : wsat ⊢ |==> (∃ i, ⌜φ i⌝ ∧ OwnI n i p) ∗ (prop n p -∗ wsat).
  Proof.
    iIntros "[% [AUTH SAT]]".
    iMod (alloc_name (fun i => i ∉ dom I /\ φ i)) as "[% [%Hi D]]".
    { i. specialize (INF (E ∪ dom I)). des. eapply not_elem_of_union in INF. des. esplits; eauto. }
    destruct Hi as [iI iφ].
    pose (<[i:=p]> I) as I'.

    assert (inv_auth_black I ~~> inv_auth_black I' ⋅ OwnI_white n i p).
    { rewrite maps_to_res_dep_add. apply maps_to_res_dep_updatable.
      apply auth_update_alloc. clear -iI. apply local_update_unital_discrete.
      intros mz WF FRAME; simpl in *. split.
      { intros i'. subst I'. destruct (decide (i' = i)) as [->|NE].
        - rewrite lookup_insert. done.
        - rewrite lookup_insert_ne; [|done]. apply (WF i').
      }
      intros i'. subst I'. specialize (FRAME i').
      rewrite discrete_fun_lookup_op left_id in FRAME.
      rewrite /maps_to_res discrete_fun_lookup_op. des_ifs; last first.
      - rewrite lookup_insert_ne; last done. by rewrite FRAME left_id.
      - apply not_elem_of_dom_1 in iI.
        rewrite iI in FRAME. simpl in *.
        rewrite -FRAME lookup_insert //.
    }
    unfold inv_auth, inv_satall.
    iMod (OwnM_Upd _ _ H3 with "AUTH") as "[AUTH NEW]". iModIntro.

    iSplit.
    - iExists i. iFrame. ss.
    - iIntros "P". unfold wsat. iExists I'. iFrame.
      unfold inv_satall. subst I'.
      iApply big_sepM_insert.
      { apply not_elem_of_dom_1; ss. }
      iSplitL "P D"; ss. iLeft. iFrame.
  Qed.

  Lemma wsat_OwnI_alloc p φ
        (INF : forall (E : gset positive), exists i, i ∉ E /\ φ i)
    : wsat ∗ prop n p ⊢ |==> (∃ i, ⌜φ i⌝ ∧ OwnI n i p) ∗ wsat.
  Proof.
    iIntros "[W P]".
    iMod (wsat_OwnI_alloc_gen with "W") as "[I W]". eauto.
    iFrame. iModIntro. iApply "W". iFrame.
  Qed.

  Lemma wsat_OwnI_open i p :
    OwnI n i p ∗ wsat ∗ OwnE {[i]} ⊢ |==> prop n p ∗ wsat ∗ OwnD {[i]}.
  Proof.
    iIntros "(I & [% [AUTH SAT]] & EN)". iModIntro.
    unfold OwnI, inv_auth, inv_satall.
    iCombine "AUTH I" as "AUTH".
    iDestruct (OwnM_valid with "AUTH") as %WF.
    assert (Hip : I !! i = Some p).
    { rewrite /inv_auth_black /OwnI_white maps_to_res_dep_add
          /maps_to_res_dep /maps_to_res in WF.
      specialize (WF n). ss. des_ifs.
      unfold eq_rect_r in WF. rewrite <- Eqdep.EqdepTheory.eq_rect_eq in WF.
      apply auth_both_valid_discrete in WF.
      destruct WF as [EXTENDS WF]. apply pw_extends in EXTENDS.
      specialize (EXTENDS i). specialize (WF i). simpl in *.
      des_ifs. clear e e0.
      destruct (I !! i) eqn: E.
      - f_equal. rewrite Some_included in EXTENDS. des.
        + apply (inj _) in EXTENDS. fold_leibniz. done.
        + apply to_agree_included in EXTENDS. fold_leibniz. done.
      - simpl in *. apply option_included_total in EXTENDS. des; ss.
    }
    clear WF.
    iDestruct "AUTH" as "[AUTH I]".
    iPoseProof (big_sepM_delete _ _ _ _ Hip with "SAT") as "[[[H1 H2]|H1] SAT]".
    2: { iCombine "EN H1" as "F". iDestruct (OwnM_valid with "F") as %WF.
         exfalso. apply coPset_disj_valid_op in WF. set_solver.
    }
    iFrame "H1 H2". unfold wsat. iExists I. iFrame. unfold inv_satall.
    iApply (big_sepM_delete _ _ _ _ Hip). iFrame.
  Qed.

  Lemma wsat_OwnI_close i p :
    OwnI n i p ∗ wsat ∗ prop n p ∗ OwnD {[i]} ⊢ |==> wsat ∗ OwnE {[i]}.
  Proof.
    iIntros "(I & [% [AUTH SAT]] & P & DIS)". iModIntro.
    unfold OwnI, inv_auth, inv_satall.
    iCombine "AUTH I" as "AUTH".
    iDestruct (OwnM_valid with "AUTH") as %WF.
    assert (Hip : I !! i = Some p).
    { unfold inv_auth_black, OwnI_white in WF. setoid_rewrite maps_to_res_dep_add in WF.
      unfold maps_to_res_dep, maps_to_res in WF. apply (pwd_lookup_wf n) in WF. ss. des_ifs.
      unfold eq_rect_r in WF. rewrite <- Eqdep.EqdepTheory.eq_rect_eq in WF.
      apply auth_both_valid_discrete in WF.
      destruct WF as [EXTENDS WF]. apply pw_extends in EXTENDS.
      specialize (EXTENDS i). specialize (WF i).
      des_ifs. clear e e0.
      destruct (I !! i) eqn: E.
      - f_equal. simpl in *. rewrite Some_included in EXTENDS. des.
        + apply (inj _) in EXTENDS. unfold_leibniz. done.
        + apply to_agree_included in EXTENDS. unfold_leibniz. done.
      - simpl in *. apply option_included_total in EXTENDS. des; ss.
    }
    clear WF.
    iDestruct "AUTH" as "[AUTH I]".
    iPoseProof (big_sepM_delete _ _ _ _ Hip with "SAT") as "[[[H1 H2]|H1] SAT]".
    { iCombine "DIS H2" as "F". iDestruct (OwnM_valid with "F") as %WF.
      exfalso. apply gset_disj_valid_op in WF. set_solver.
    }
    iFrame "H1". unfold wsat. iExists I. iFrame. unfold inv_satall.
    iApply (big_sepM_delete _ _ _ _ Hip). iFrame. iLeft. iFrame.
  Qed.

  Lemma wsat_init :
    OwnM (maps_to_res_dep n (@auth_auth (positive ==> (optionUR (agreeR $ leibnizO (Vars n))))%ra (DfracOwn 1) (fun (i : positive) => None)) : IInvSetRA _)
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
  Context `{@GRA.inG OwnERA Σ}.
  Context `{@GRA.inG OwnDRA Σ}.
  Context `{@GRA.inG (IInvSetRA Vars) Σ}.

  Notation iProp := (iProp Σ).

  Definition wsat_auth_black (x : index) : IInvSetRA Vars :=
    (fun n => if (lt_dec n x)
           then ε
           else @auth_auth (positive ==> (optionUR (agreeR $ leibnizO (Vars n))))%ra (DfracOwn 1) (fun _ => None)).

  Definition wsat_auth (x : index) := OwnM (wsat_auth_black x).

  (* wsat n for all n < x *)
  Definition wsats (x : index) := sep_conjs wsat x.

  Definition wsats_l (x : index) := ([∗ list] n ∈ (seq 0 x), wsat n)%I.

  Lemma unfold_wsats x :
    wsats (S x) = (wsats x ∗ wsat x)%I.
  Proof. ss. Qed.

  Lemma unfold_wsats_l x :
    wsats_l (S x) ⊢ (wsats_l x ∗ wsat x)%I.
  Proof.
    iIntros "A". unfold wsats_l. replace (seq 0 (S x)) with (seq 0 x ++ [x]).
    2:{ rewrite seq_S. ss. }
    iPoseProof (big_sepL_snoc with "A") as "[A B]". ss. iFrame.
  Qed.

  Lemma fold_wsats_l x :
    (wsats_l x ∗ wsat x)%I ⊢ wsats_l (S x).
  Proof.
    iIntros "A". unfold wsats_l. replace (seq 0 (S x)) with (seq 0 x ++ [x]).
    2:{ rewrite seq_S. ss. }
    iApply big_sepL_app. ss. iDestruct "A" as "[A B]". iFrame.
  Qed.

  Lemma wsats_equiv_l x :
    wsats x ⊣⊢ wsats_l x.
  Proof.
    iInduction x as [|x] "IH"; iSplit; iIntros "W"; ss.
    - iEval (rewrite unfold_wsats) in "W". iDestruct "W" as "[WS W]".
      iApply fold_wsats_l. iFrame. iApply "IH"; auto.
    - iEval (rewrite unfold_wsats_l) in "W". iDestruct "W" as "[WS W]".
      rewrite unfold_wsats. iFrame. iApply "IH"; auto.
  Qed.

  Lemma wsats_init_zero :
    OwnM ((fun n => @auth_auth (positive ==> (optionUR (agreeR $ leibnizO (Vars n))))%ra (DfracOwn 1) (fun _ => None)) : IInvSetRA Vars)
         ⊢ wsat_auth 0 ∗ wsats 0.
  Proof.
    iIntros "H". iFrame.
  Qed.

  Lemma wsat_auth_nin (x n : index) (NIN : x ≤ n)
    : wsat_auth x ⊢ wsat_auth n ∗ ([∗ list] m ∈ (seq x (n - x)), wsat m).
  Proof.
    induction NIN.
    - iIntros "AUTH". rename x into n. remember (S n) as x.
      assert ((wsat_auth_black n) =
                ((wsat_auth_black x)
                   ⋅
                   (maps_to_res_dep n (@auth_auth (positive ==> (optionUR (agreeR $ leibnizO (Vars n))))%ra (DfracOwn 1) (fun (i : positive) => None))))).
      { subst. extensionalities a. unfold wsat_auth_black, maps_to_res_dep.
        rewrite discrete_fun_lookup_op.
        destruct (excluded_middle_informative (a = n)).
        all: des_ifs; try lia.
      }
      rewrite Nat.sub_diag. simpl. iFrame.
    - iIntros "AUTH". iPoseProof (IHNIN with "AUTH") as "[AUTH SAT]".
      clear IHNIN. remember (S m) as y.
      assert ((wsat_auth_black m) =
                ((wsat_auth_black y)
                   ⋅
                   (maps_to_res_dep m (@auth_auth (positive ==> (optionUR (agreeR $ leibnizO (Vars m))))%ra (DfracOwn 1) (fun (i : positive) => None))))).
      { subst. extensionalities a. unfold wsat_auth_black, maps_to_res_dep.
        rewrite discrete_fun_lookup_op.
        destruct (excluded_middle_informative (a = m)).
        all: des_ifs; try lia.
      }
      unfold wsat_auth. rewrite H3. iDestruct "AUTH" as "[AUTH NEW]".
      iPoseProof (wsat_init with "NEW") as "NEW".
      subst y. iFrame.
      replace (S m - x) with ((m - x) + 1) by lia. rewrite seq_app.
      iApply big_sepL_app. iFrame.
      replace (x + (m - x)) with m by lia. ss. iFrame.
  Qed.

  Lemma wsats_nin (x n : index) (NIN : x ≤ n)
    : wsats x ∗ ([∗ list] m ∈ (seq x (n - x)), wsat m) ⊢ wsats n.
  Proof.
    rewrite ! wsats_equiv_l.
    iIntros "[SALL WSAT]". unfold wsats_l.
    replace n with (x + (n - x)) by lia. rewrite seq_app. iFrame.
    replace (x + (n - x) - x) with (n - x) by lia. iFrame.
  Qed.

  Lemma wsats_in (x0 x1 : index) :
    x0 ≤ x1 -> wsats x1 ⊢ wsats x0 ∗ ([∗ list] n ∈ (seq x0 (x1 - x0)), wsat n).
  Proof.
    rewrite ! wsats_equiv_l.
    iIntros (LE) "SAT". unfold wsats_l.
    replace x1 with (x0 + (x1 - x0)) by lia. rewrite (seq_app _ _ 0).
    iPoseProof (big_sepL_app with "SAT") as "[SAT K]". iFrame.
    ss. replace (x0 + (x1 - x0) - x0) with (x1 - x0) by lia. iFrame.
  Qed.

  Lemma wsats_drop_keep (x : index) :
    wsats (S x) ⊢ wsats x ∗ wsat x.
  Proof.
    iIntros "WS". iPoseProof (wsats_in x with "WS") as "[WS W]". auto.
    iFrame. replace (S x - x) with (S O) by lia. rewrite seq_S.
    simpl. replace (x + 0) with x by lia. iDestruct "W" as "[W _]". iFrame.
  Qed.

  Lemma wsats_allocs x1 x2 :
    x1 ≤ x2 -> wsat_auth x1 ∗ wsats x1 ⊢ (wsat_auth x2 ∗ wsats x2).
  Proof.
    iIntros (LE) "[AUTH SAT]". iPoseProof ((wsat_auth_nin _ _ LE) with "AUTH") as "[AUTH NEW]".
    iPoseProof ((wsats_nin _ _ LE) with "[SAT NEW]") as "SAT". iFrame. iFrame.
  Qed.


  Lemma wsats_OwnI_alloc_lt_gen x n (LT : n < x) p φ
        (INF : forall (E : gset positive), exists i, i ∉ E /\ φ i)
    : wsats x ⊢ |==> (∃ i, ⌜φ i⌝ ∧ OwnI n i p) ∗ (prop n p -∗ wsats x).
  Proof.
    rewrite ! wsats_equiv_l.
    iIntros "SALL".
    iPoseProof (big_sepL_lookup_acc with "SALL") as "[WSAT K]".
    apply lookup_seq_lt; eauto.
    iPoseProof (wsat_OwnI_alloc_gen with "WSAT") as ">[RES WSAT]". apply INF. iFrame.
    iModIntro. iIntros "P". iFrame. iPoseProof ("WSAT" with "P") as "WSAT".
    iPoseProof ("K" with "WSAT") as "SALL". iFrame.
  Qed.

  Lemma wsats_OwnI_alloc_lt x n (LT : n < x) p φ
        (INF : forall (E : gset positive), exists i, i ∉ E /\ φ i)
    : wsats x ∗ prop n p ⊢ |==> (∃ i, ⌜φ i⌝ ∧ OwnI n i p) ∗ wsats x.
  Proof.
    iIntros "[W P]". iMod (wsats_OwnI_alloc_lt_gen with "W") as "[I W]". 1,2: eauto.
    iModIntro. iFrame. iApply "W". iFrame.
  Qed.

  Lemma wsats_OwnI_alloc_ge_gen x n (GE : x <= n) p φ
        (INF : forall (E : gset positive), exists i, i ∉ E /\ φ i)
    : wsat_auth x ∗ wsats x ⊢
                |==> (∃ i, ⌜φ i⌝ ∧ OwnI n i p) ∗ wsat_auth (S n) ∗ (prop n p -∗ wsats (S n)).
  Proof.
    iIntros "(AUTH & WSAT)".
    iPoseProof ((wsats_allocs x (S n)) with "[AUTH WSAT]") as "[AUTH WSAT]". lia. iFrame.
    iMod ((wsats_OwnI_alloc_lt_gen (S n) n) with "WSAT") as "[RES WSAT]". auto. eauto. iFrame.
    auto.
  Qed.

  Lemma wsats_OwnI_alloc_ge x n (GE : x <= n) p φ
        (INF : forall (E : gset positive), exists i, i ∉ E /\ φ i)
    : wsat_auth x ∗ wsats x ∗ prop n p ⊢ |==> (∃ i, ⌜φ i⌝ ∧ OwnI n i p) ∗ wsat_auth (S n) ∗ wsats (S n).
  Proof.
    iIntros "(A & W & P)". iMod (wsats_OwnI_alloc_ge_gen with "[A W]") as "(I & A & W)".
    1,2: eauto.
    iFrame. iModIntro. iFrame. iApply "W". iFrame.
  Qed.

  Lemma wsat_auth_OwnI_le x n i p :
    OwnI n i p ∗ wsat_auth x ⊢ ⌜n < x⌝.
  Proof.
    iIntros "(I & AUTH)".
    unfold OwnI, wsat_auth.
    iCombine "AUTH I" as "AUTH".
    iDestruct (OwnM_valid with "AUTH") as %WF.
    unfold wsat_auth_black, OwnI_white, maps_to_res_dep in WF.
    apply (pwd_lookup_wf n) in WF.
    rewrite discrete_fun_lookup_op /= in WF.
    des_ifs. exfalso. unfold eq_rect_r in WF. rewrite <- Eqdep.EqdepTheory.eq_rect_eq in WF.
    unfold maps_to_res in WF.
    apply auth_both_valid_discrete in WF.
    destruct WF as [EXTENDS WF].
    apply pw_extends in EXTENDS. specialize (EXTENDS i).
    specialize (WF i). des_ifs.
    clear e e0.
    apply option_included_total in EXTENDS. des; ss.
  Qed.

  Lemma wsats_OwnI_open x n i p :
    n < x -> OwnI n i p ∗ wsats x ∗ OwnE {[i]} ⊢ |==> prop n p ∗ wsats x ∗ OwnD {[i]}.
  Proof.
    rewrite ! wsats_equiv_l.
    iIntros (LT) "(I & SAT & EN)".
    unfold OwnI, wsats.
    iPoseProof (big_sepL_lookup_acc with "SAT") as "[WSAT K]".
    apply lookup_seq_lt; eauto.
    ss. iMod (wsat_OwnI_open with "[$I $WSAT $EN]") as "[P [WSAT DN]]".
    iPoseProof ("K" with "WSAT") as "SAT".
    iModIntro. iFrame.
  Qed.

  Lemma wsats_OwnI_close x n i p :
    n < x -> OwnI n i p ∗ wsats x ∗ prop n p ∗ OwnD {[i]} ⊢ |==> wsats x ∗ OwnE {[i]}.
  Proof.
    rewrite ! wsats_equiv_l.
    iIntros (LT) "(I & SAT & P & DIS)".
    iPoseProof (big_sepL_lookup_acc with "SAT") as "[WSAT K]".
    apply lookup_seq_lt; eauto.
    iMod (wsat_OwnI_close with "[$I $WSAT $P $DIS]") as "[WSAT EN]".
    iPoseProof ("K" with "WSAT") as "SAT".
    iModIntro. iFrame.
  Qed.

End WSATS.

Section FANCY_UPDATE.

  Context `{Σ : GRA.t}.
  Context `{Vars : index -> Type}.
  Context `{Invs : @IInvSet Σ Vars}.
  Context `{@GRA.inG OwnERA Σ}.
  Context `{@GRA.inG OwnDRA Σ}.
  Context `{@GRA.inG (IInvSetRA Vars) Σ}.

  Notation iProp := (iProp Σ).

  Definition inv (n : index) (N : namespace) p :=
    (∃ i, ⌜i ∈ (↑N : coPset)⌝ ∧ OwnI n i p)%I.

  Local Definition FUpd_def x (A : iProp) (E1 E2 : coPset) (P : iProp) : iProp :=
    A ∗ wsats x ∗ OwnE E1 -∗ #=> (A ∗ wsats x ∗ OwnE E2 ∗ P).
  Local Definition FUpd_aux : seal (@FUpd_def). Proof. by eexists. Qed.
  Definition FUpd := FUpd_aux.(unseal).
  Lemma FUpd_unseal' x A: @fupd _ (FUpd x A) = (FUpd_def x A).
  Proof. rewrite -FUpd_aux.(seal_eq) //. Qed.

  Lemma wsats_inv_gen x A E n N p :
    n < x ->
    ⊢ A ∗ wsats x ∗ OwnE E -∗ #=> (A ∗ (prop n p -∗ wsats x) ∗ OwnE E ∗ (inv n N p)).
  Proof.
    iIntros (LT) "(A & WSAT & EN)".
    iMod (wsats_OwnI_alloc_lt_gen _ _ LT p (fun i => i ∈ ↑N) with "WSAT") as "[I WSAT]".
    - i. des_ifs. apply iris.base_logic.lib.invariants.fresh_inv_name.
    - iFrame. auto.
  Qed.

  (* BiFUpd instance. Due to it depending on x and A, this needs to be given explicitly.
     Most of the time, the `=|x|=(A)={E1,E2}=>` notation does it, but for some typeclasses instances explicit
     annotations may be required.

     The same goes for BiBUpd instance for IUpd, but that does not need to be typed out a lot.
  *)
  Lemma FUpd_fupd_mixin x A : BiFUpdMixin iProp (FUpd x A).
  Proof.
    split.
    - rewrite FUpd_unseal'. solve_proper.
    - intros E1 E2 (E1''&->&?)%subseteq_disjoint_union_L.
      rewrite FUpd_unseal' /FUpd_def OwnE_add //.
      by iIntros "($ & $ & $ & HE) !> ($ & $ & $) !>".
    - rewrite FUpd_unseal' /FUpd_def.
      iIntros (E1 E2 P) ">H [Hw HE]". iApply "H"; by iFrame.
    - rewrite FUpd_unseal' /FUpd_def.
      iIntros (E1 E2 P Q HPQ) "HP HwE". rewrite -HPQ. by iApply "HP".
    - rewrite FUpd_unseal' /FUpd_def. iIntros (E1 E2 E3 P) "HP HwE".
      iMod ("HP" with "HwE") as "(HA & Hw & HE & HP)". iApply "HP"; by iFrame.
    - intros E1 E2 Ef P HE1Ef. rewrite FUpd_unseal' /FUpd_def OwnE_add //.
      iIntros "Hvs (HA & Hw & HE1 &HEf)".
      iMod ("Hvs" with "[HA Hw HE1]") as "($ & $ & HE2 & HP)"; first by iFrame.
      iDestruct (OwnE_add' with "[HE2 HEf]") as "[? $]"; first by iFrame.
      iIntros "!>". by iApply "HP".
    - rewrite FUpd_unseal' /FUpd_def. by iIntros (????) "[HwP $]".
  Qed.
  Global Instance iProp_bi_fupd_FUpd x A : BiFUpd iProp :=
  {| bi_fupd_mixin := (FUpd_fupd_mixin x A) |}.
  Global Instance iProp_bi_BUpd_FUpd x A : @BiBUpdFUpd iProp iProp_bi_bupd (iProp_bi_fupd_FUpd x A).
  Proof. rewrite /BiBUpdFUpd FUpd_unseal'. by iIntros (??) ">$ $". Qed.
  Global Instance iProp_bi_IUpd_FUpd x A : @BiBUpdFUpd iProp (iProp_bi_bupd_IUpd A) (iProp_bi_fupd_FUpd x A).
  Proof.
    rewrite /BiBUpdFUpd FUpd_unseal'.
    iIntros (??) "P [A [$ $]]". rewrite IUpd_eq.
    by iMod ("P" with "A") as "[$ $]".
  Qed.

End FANCY_UPDATE.

(* Give explicit [BiFUpd] typeclass instance for [FUpd] since inference fails. *)
(* Explictly spelling out the coercion [bi_car iProp] ensures the below notations are used. Else it will be ``inserted'' ruining the notation. *)
Notation fupd_ex x A :=
  (@fupd (bi_car (iProp _)) (@bi_fupd_fupd _ (iProp_bi_fupd_FUpd x A))) (only parsing).

Notation "'=|' x '|=(' A ')={' E1 ',' E2 '}=>' P" := (fupd_ex x A E1 E2 P) (at level 90).
Notation "'=|' x '|={' E1 ',' E2 '}=>' P" := (=|x|=( ⌜True⌝%I )={ E1, E2}=> P) (at level 90).
Notation "P =| x |=( A )={ E1 , E2 }=∗ Q" := (P -∗ =|x|=(A)={E1,E2}=> Q)%I (at level 90).
Notation "P =| x |={ E1 , E2 }=∗ Q" := (P -∗ =|x|={E1,E2}=> Q)%I (at level 90).

Notation "'=|' x '|=(' A ')={' E '}=>' P" := (=|x|=( A )={E, E}=> P) (at level 90).
Notation "'=|' x '|={' E '}=>' P" := (=|x|=( ⌜True⌝%I )={ E }=> P) (at level 90).
Notation "P =| x |=( A )={ E }=∗ Q" := (P -∗ =|x|=(A)={E}=> Q)%I (at level 90).
Notation "P =| x |={ E }=∗ Q" := (P -∗ =|x|={E}=> Q)%I (at level 90).

Section LEMMAS.

Context `{Σ : GRA.t}.
Context `{Vars : index -> Type}.
Context `{Invs : @IInvSet Σ Vars}.
Context `{@GRA.inG OwnERA Σ}.
Context `{@GRA.inG OwnDRA Σ}.
Context `{@GRA.inG (IInvSetRA Vars) Σ}.
Local Transparent FUpd.
Notation iProp := (iProp Σ).

  Lemma FUpd_unseal x A E1 E2 P :
    (=|x|=(A)={E1,E2}=> P) ⊣⊢ (A ∗ wsats x ∗ OwnE E1 -∗ #=> (A ∗ wsats x ∗ OwnE E2 ∗ P)).
  Proof. rewrite FUpd_unseal' //. Qed.

  Lemma FUpd_mono x0 x1 A Es1 Es2 P :
    (x0 ≤ x1) -> =|x0|=(A)={Es1,Es2}=> P ⊢ =|x1|=(A)={Es1,Es2}=> P.
  Proof.
    rewrite !FUpd_unseal /FUpd_def.
    iIntros (LE) "FUPD (A & SAT & EN)".
    iPoseProof ((wsats_in _ _ LE) with "SAT") as "[SAT K]".
    iMod ("FUPD" with "[A SAT EN]") as "(A & SAT & EN & P)". iFrame.
    iModIntro. iFrame. iApply wsats_nin. apply LE. iFrame.
  Qed.

  Lemma FUpd_alloc_gen x A E n N p :
    n < x -> (inv n N p -∗ prop n p) ⊢ =|x|=(A)={E}=> (inv n N p).
  Proof.
    rewrite !FUpd_unseal /FUpd_def.
    iIntros (LT) "P (A & WSAT & EN)".
    iMod (wsats_inv_gen _ A with "[$A $WSAT $EN]") as "($ & W & $ & #$)"; [done|].
    iModIntro. iApply "W". iApply "P". done.
  Qed.

  Lemma FUpd_alloc x A E n N p :
    n < x -> prop n p ⊢ =|x|=(A)={E}=> (inv n N p).
  Proof.
    iIntros (LT) "P". iApply FUpd_alloc_gen. auto. iIntros. iFrame.
  Qed.

  Lemma FUpd_open x A E n N (LT : n < x) (IN : ↑N ⊆ E) p :
    inv n N p ⊢
        =|x|=(A)={E,(E∖↑N)}=>
        ((prop n p) ∗ ((prop n p) -∗ =|x|=(A)={(E∖↑N),E}=> emp)).
  Proof.
    rewrite !FUpd_unseal /FUpd_def.
    iIntros "[% (%iN & #HI)] (A & WSAT & EN)".
    iAssert (OwnE (E ∖ ↑N) ∗ OwnE (↑N ∖ {[i]}) ∗ OwnE {[i]})%I with "[EN]" as "(EN1 & EN2 & EN3)".
    { iApply bi.sep_mono_r. { apply OwnE_disjoint. set_solver. }
      iApply OwnE_disjoint. { set_solver. }
      replace (E ∖ ↑N ∪ (↑N ∖ {[i]} ∪ {[i]})) with E.
      - ss.
      - transitivity ({[i]} ∪ ↑N ∖ {[i]} ∪ E ∖ ↑N).
        + rewrite <- union_difference_singleton_L; ss. eapply union_difference_L; ss.
        + rewrite union_comm_L. f_equal. rewrite union_comm_L. ss.
    }
    iMod (wsats_OwnI_open x n i p LT with "[HI WSAT EN3]") as "(P & WSAT & DIS)".
    { iFrame. auto. }
    iModIntro. iFrame. iIntros "P (A & WSAT & EN1)".
    iMod (wsats_OwnI_close x n i p LT with "[HI WSAT P DIS]") as "(WSAT & EN3)".
    { iFrame. auto. }
    iModIntro. iFrame. iSplitL; [|done].
    iPoseProof (OwnE_union with "[EN2 EN3]") as "EN2". iFrame.
    rewrite <- union_difference_singleton_L; ss.
    iPoseProof (OwnE_union with "[EN1 EN2]") as "ENS". iFrame.
    rewrite <- union_difference_L; ss.
  Qed.

  Global Instance from_modal_FUpd_general x A E1 E2 P :
    FromModal (E2 ⊆ E1) modality_id P (=|x|=(A)={E1,E2}=> P) P.
  Proof.
    rewrite /FromModal !FUpd_unseal /FUpd_def. ss.
    iIntros (HE) "P (A & WSAT & EN)". iModIntro. iFrame.
    replace E1 with (E2 ∪ E1 ∖ E2).
    - iPoseProof (OwnE_disjoint with "EN") as "[EN1 EN2]". set_solver. ss.
    - symmetry. eapply union_difference_L. ss.
  Qed.

  Global Instance elim_modal_FUpd_FUpd_simple p n x A E1 E2 E3 P Q :
    ElimModal (n <= x) p false (=|n|={E1,E2}=> P) P (=|x|=(A)={E1,E3}=> Q) (=|x|=(A)={E2,E3}=> Q).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim.
    iIntros (LE) "[P K]".
    iPoseProof (FUpd_mono n x with "P") as "P"; [done|].
    rewrite !FUpd_unseal /FUpd_def.
    iIntros "[A I]".
    iMod ("P" with "[$I]") as "(_ & WSAT & EN & P)".
    iApply ("K" with "P"). iFrame.
  Qed.

  Global Instance into_acc_FUpd_inv x A E n N p :
    IntoAcc (inv n N p) (n < x /\ (↑N ⊆ E)) True
            (fupd_ex x A E (E ∖ ↑N))
            (fupd_ex x A (E ∖ ↑N) E)
            (fun _ : () => prop n p) (fun _ : () => prop n p) (fun _ : () => None).
  Proof.
    rewrite /IntoAcc /accessor bi.exist_unit.
    iIntros ((?&?)) "#INV _". by iApply FUpd_open.
  Qed.

  Global Instance elim_modal_FUpd_FUpd p n x A E1 E2 E3 P Q :
    ElimModal (n <= x) p false (=|n|=(A)={E1,E2}=> P) P (=|x|=(A)={E1,E3}=> Q) (=|x|=(A)={E2,E3}=> Q).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim.
    iIntros (LE) "[P K]".
    iDestruct (FUpd_mono n x with "P") as "P"; [done|].
    iMod "P". iApply ("K" with "P").
  Qed.

  Global Instance elim_modal_FUpd_FUpd_simple_general p x A E0 E1 E2 E3 P Q :
    ElimModal (E0 ⊆ E2) p false
              (=|x|={E0,E1}=> P)
              P
              (=|x|=(A)={E2,E3}=> Q)
              (=|x|=(A)={(E1 ∪ (E2 ∖ E0)),E3}=> Q) | 10.
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim. ss.
    iIntros (HE) "[M K]".
    iDestruct (fupd_mask_frame_r _ _ (E2 ∖ E0) with "M") as "M".
    { set_solver. }
    replace (E0 ∪ E2 ∖ E0) with E2 by (eapply union_difference_L; ss).
    iMod "M". iApply ("K" with "M").
  Qed.

  Global Instance elim_modal_FUpd_FUpd_general p x A E0 E1 E2 E3 P Q :
    ElimModal (E0 ⊆ E2) p false
              (=|x|=(A)={E0,E1}=> P)
              P
              (=|x|=(A)={E2,E3}=> Q)
              (=|x|=(A)={(E1 ∪ (E2 ∖ E0)),E3}=> Q) | 10.
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim. ss.
    iIntros (HE) "[M K]".
    iDestruct (fupd_mask_frame_r _ _ (E2 ∖ E0) with "M") as "M".
    { set_solver. }
    replace (E0 ∪ E2 ∖ E0) with E2 by (eapply union_difference_L; ss).
    iMod "M". iApply ("K" with "M").
  Qed.

End LEMMAS.
