From stdpp Require Import coPset gmap namespaces.
From sflib Require Import sflib.
From Fairness Require Import PCM IProp IPM.
From iris Require Import bi.big_op.
From iris Require base_logic.lib.invariants.

Local Notation index := nat.

Section INVARIANT_SET.

  Context `{Σ : GRA.t}.

  Class InvSet (Var : Type) :=
    { prop : Var -> iProp }.

  Class InvIn {Var : Type} `{InvSet Var} (P : iProp) :=
    { inhabitant : Var
    ; inhabitant_eq : prop inhabitant = P
    }.

  Definition InvSetRA (Vars : index -> Type) (n : index) : URA.t :=
    (Auth.t (positive ==> URA.agree (Vars n)))%ra.

  (* Definition IInvSetRA (Vars : index -> Type) : URA.t := (@URA.pointwise_dep index (fun n => InvSetRA (Vars n)))%ra. *)
  (* Polymorphic Definition IInvSetRA (Vars : index -> Type) : URA.t := (@URA.pointwise_dep index (fun n => InvSetRA (Vars n)))%ra. *)
  (* Polymorphic Definition IInvSetRA (Var : Type) : URA.t := (index ==> InvSetRA Var)%ra. *)
  (* Definition IInvSetRA (Var : Type) : URA.t := (index ==> InvSetRA Var)%ra. *)

  Definition IInvSetRA (Vars : index -> Type) : URA.t :=
    @URA.pointwise_dep index (InvSetRA Vars).

  Global Instance InvSet_top (Var : Type) : InvSet Var :=
    {| prop := fun (_ : Var) => (⌜True⌝)%I |}.

  Global Instance InvSet_bot (Var : Type) : InvSet Var :=
    {| prop := fun (_ : Var) => (⌜False⌝)%I |}.

End INVARIANT_SET.

Section PWDEP.

  Lemma pointwise_dep_updatable
        A (Ms : A -> URA.t)
        (f0 f1 : @URA.pointwise_dep A Ms)
        (UPD : forall a, URA.updatable (f0 a) (f1 a))
    :
    URA.updatable f0 f1.
  Proof.
    ii. ur. i. ur in H. specialize (H k).
    eapply (UPD k); eauto.
  Qed.

  Lemma pointwise_dep_updatable_set
        A (Ms : A -> URA.t)
        (f : @URA.pointwise_dep A Ms)
        (P : forall (a : A), (Ms a) -> Prop)
        (UPD: forall a, URA.updatable_set (f a) (P a))
    :
    URA.updatable_set f (fun f' => forall a, P a (f' a)).
  Proof.
    ii. hexploit (Axioms.choice (fun a m => P a m /\ URA.wf (m ⋅ ctx a))).
    { i. eapply (UPD x). ur in WF. auto. }
    i. des. exists f0. splits; auto.
    { i. specialize (H a). des. auto. }
    { ur. i. specialize (H k). des. auto. }
  Qed.

  Program Definition maps_to_res_dep {A : Type} {Ms : A -> URA.t} (a : A) (m : Ms a)
    : @URA.pointwise_dep A Ms.
  Proof.
    ii. destruct (Axioms.excluded_middle_informative (k = a)).
    - subst k. exact m.
    - exact ε.
  Defined.

  Lemma maps_to_res_dep_eq
        A (Ms : A -> URA.t)
        (a : A)
        (m : Ms a)
    :
    (@maps_to_res_dep A Ms a m) a = m.
  Proof.
    unfold maps_to_res_dep. des_ifs. unfold eq_rect_r.
    rewrite <- Eqdep.EqdepTheory.eq_rect_eq. auto.
  Qed.

  Lemma maps_to_res_dep_neq
        A (Ms : A -> URA.t)
        (a b : A)
        (m : Ms a)
    :
    a <> b -> (@maps_to_res_dep A Ms a m) b = ε.
  Proof.
    i. unfold maps_to_res_dep. des_ifs.
  Qed.

  Lemma maps_to_res_dep_add
        A (Ms : A -> URA.t)
        (a : A)
        (m0 m1 : Ms a)
    :
    @maps_to_res_dep _ Ms a m0 ⋅ @maps_to_res_dep _ Ms a m1 = @maps_to_res_dep _ Ms a (m0 ⋅ m1).
  Proof.
    extensionalities a'. unfold URA.add at 1. unseal "ra". ss.
    destruct (Axioms.excluded_middle_informative (a' = a)).
    - subst a'. rewrite ! @maps_to_res_dep_eq. auto.
    - rewrite ! @maps_to_res_dep_neq; auto. apply URA.unit_id.
  Qed.

  Lemma maps_to_res_dep_updatable
        A (Ms : A -> URA.t)
        (a : A)
        (m0 m1 : Ms a)
        (UPD: URA.updatable m0 m1)
    :
    URA.updatable (@maps_to_res_dep A Ms a m0) (@maps_to_res_dep A Ms a m1).
  Proof.
    
        

  Lemma maps_to_updatable A (M: URA.t)
        (a: A) (m0 m1: M)
        (UPD: URA.updatable m0 m1)
    :
    URA.updatable (maps_to_res a m0) (maps_to_res a m1).
  Proof.
    eapply pointwise_updatable. i.
    unfold maps_to_res. des_ifs.
  Qed.

  Lemma maps_to_updatable_set A (M: URA.t)
        (a: A) (m: M) (P: M -> Prop)
        (UPD: URA.updatable_set m P)
    :
    URA.updatable_set
      (maps_to_res a m)
      (fun f => exists (m1: M), f = maps_to_res a m1 /\ P m1).
  Proof.
    eapply updatable_set_impl; cycle 1.
    { eapply pointwise_updatable_set.
      instantiate (1:= fun a' m' => (a' = a -> P m') /\ (a' <> a -> m' = URA.unit)).
      ii. unfold maps_to_res in WF. des_ifs.
      { exploit UPD; eauto. i. des. esplits; eauto. ss. }
      { exists URA.unit. splits; ss. }
    }
    { i. ss. exists (r a). splits; auto.
      { extensionality a'. unfold maps_to_res. des_ifs.
        specialize (H0 a'). des. auto.
      }
      { specialize (H0 a). des. auto. }
    }
  Qed.

  Definition map_update {A} {M: URA.t}
             (f: (A ==> M)%ra) a m :=
    fun a' => if excluded_middle_informative (a' = a)
              then m
              else f a'.

(* maps_to_res =  *)
(* λ (A : Type) (M : URA.t) (a : A) (m : M) (a' : A), *)
(*   if Axioms.excluded_middle_informative (a' = a) then m else ε *)
(*      : ∀ (A : Type) (M : URA.t), A → M → (A ==> M)%ra *)

End PWDEP.

Section PCM_OWN.

  Context `{Σ : GRA.t}.

  Definition OwnE `{@GRA.inG (index ==> CoPset.t)%ra Σ} (n : index) (E : coPset) :=
    OwnM (@maps_to_res index CoPset.t n (Some E)).

  Definition OwnD `{@GRA.inG (index ==> Gset.t)%ra Σ} (n : index) (D : gset positive) :=
    OwnM (@maps_to_res index Gset.t n (Some D)).

  Definition OwnI_white {Vars} (n : index) (i : positive) (p : Var) : IInvSetRA Vars :=
    @maps_to_res index (Auth.t (positive ==> URA.agree Var))%ra
                 n (Auth.white (@maps_to_res positive (URA.agree Var) i (Some (Some p)))).

  Definition OwnI {Var} `{@GRA.inG (IInvSetRA Var) Σ} (n : index) (i : positive) (p : Var) :=
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

  Global Instance OwnI_persistent {Var} `{@GRA.inG (IInvSetRA Var) Σ}
    n i p : Persistent (OwnI n i p).
  Proof.
    unfold OwnI, OwnI_white.
    remember (@maps_to_res index (Auth.t (positive ==> URA.agree Var))%ra n (Auth.white (@maps_to_res positive (URA.agree Var) i (Some (Some p))))) as r.
    unfold Persistent. iIntros "H".
    iPoseProof (@OwnM_persistently _ _ H _ with "H") as "#HP". iModIntro.
    replace r with (URA.core r) at 2. auto.
    subst. unfold maps_to_res. ss. extensionalities k. des_ifs.
  Qed.

End PCM_OWN.

Section WORLD_SATISFACTION.

  Context `{Σ : GRA.t}.
  Variable n : index.
  Context `{Var : Type}.
  Context `{@InvSet Σ Var}.
  Context `{@GRA.inG (index ==> CoPset.t)%ra Σ}.
  Context `{@GRA.inG (index ==> Gset.t)%ra Σ}.
  Context `{@GRA.inG (IInvSetRA Var) Σ}.

  Definition inv_auth_black (I : gmap positive Var) : IInvSetRA Var :=
    @maps_to_res index _
                 n (@Auth.black (positive ==> URA.agree Var)%ra
                                (fun (i : positive) => Some <$> (I !! i))).

  Definition inv_auth (I : gmap positive Var) :=
    OwnM (inv_auth_black I).

  Definition inv_satall (I : gmap positive Var) :=
    ([∗ map] i ↦ p ∈ I, (prop p) ∗ OwnD n {[i]} ∨ OwnE n {[i]})%I.

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
    : wsat ∗ prop p ⊢ |==> (∃ i, ⌜φ i⌝ ∧ OwnI n i p) ∗ wsat.
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
              (maps_to_res n (@Auth.black (positive ==> URA.agree Var)%ra (fun i => Some <$> (I !! i))) : IInvSetRA Var)
              ((maps_to_res n (@Auth.black (positive ==> URA.agree Var)%ra (fun i => Some <$> (I' !! i))) : IInvSetRA Var)
                 ⋅
                 (maps_to_res n (Auth.white (@maps_to_res _ (URA.agree Var) i (Some (Some p)))) : IInvSetRA Var))).
    { setoid_rewrite maps_to_res_add. apply maps_to_updatable.
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
    OwnI n i p ∗ wsat ∗ OwnE n {[i]} ⊢ |==> prop p ∗ wsat ∗ OwnD n {[i]}.
  Proof.
    iIntros "(I & [% [AUTH SAT]] & EN)". iModIntro.
    unfold OwnI, inv_auth, inv_satall.
    iCombine "AUTH I" as "AUTH".
    iPoseProof (OwnM_valid with "AUTH") as "%WF".
    assert (Hip : I !! i = Some p).
    { unfold inv_auth_black, OwnI_white in WF. setoid_rewrite maps_to_res_add in WF.
      unfold maps_to_res in WF. apply (lookup_wf n) in WF. ss. des_ifs.
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
    OwnI n i p ∗ wsat ∗ prop p ∗ OwnD n {[i]} ⊢ |==> wsat ∗ OwnE n {[i]}.
  Proof.
    iIntros "(I & [% [AUTH SAT]] & P & DIS)". iModIntro.
    unfold OwnI, inv_auth, inv_satall.
    iCombine "AUTH I" as "AUTH".
    iPoseProof (OwnM_valid with "AUTH") as "%WF".
    assert (Hip : I !! i = Some p).
    { unfold inv_auth_black, OwnI_white in WF. setoid_rewrite maps_to_res_add in WF.
      unfold maps_to_res in WF. apply (lookup_wf n) in WF. ss. des_ifs.
      apply Auth.auth_included in WF. rename WF into EXTENDS.
      apply pw_extends in EXTENDS. specialize (EXTENDS i).
      unfold maps_to_res in EXTENDS. des_ifs. clear e e0.
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
    OwnM (maps_to_res n (@Auth.black (positive ==> URA.agree Var)%ra (fun (i : positive) => None)))
      ⊢ wsat.
  Proof.
    iIntros "H". iExists ∅. iFrame.
    unfold inv_satall. iApply big_sepM_empty. ss.
  Qed.

End WORLD_SATISFACTION.

Section FANCY_UPDATE.

  Context `{Σ : GRA.t}.
  Variable n : index.
  Context `{Var : Type}.
  Context `{Invs : @InvSet Σ Var}.
  Context `{@GRA.inG (index ==> CoPset.t)%ra Σ}.
  Context `{@GRA.inG (index ==> Gset.t)%ra Σ}.
  Context `{@GRA.inG (IInvSetRA Var) Σ}.


  Definition inv (N : namespace) P :=
    (∃ p, ∃ i, ⌜prop p = P⌝ ∧ ⌜i ∈ (↑N : coPset)⌝ ∧ OwnI n i p)%I.

  Definition FUpd (A : iProp) (E1 E2 : coPset) (P : iProp) : iProp :=
    A ∗ wsat n ∗ OwnE n E1 -∗ #=> (A ∗ wsat n ∗ OwnE n E2 ∗ P).

  Lemma FUpd_alloc A E N P `{hasP : @InvIn Σ Var Invs P} :
    P ⊢ FUpd A E E (inv N P).
  Proof.
    destruct hasP as [p HE]. subst. iIntros "P (A & WSAT & EN)".
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
