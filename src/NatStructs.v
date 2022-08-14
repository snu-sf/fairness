From sflib Require Import sflib.

From Fairness Require Import Axioms.

From Coq Require Import
  Permutation
  SetoidList
  SetoidPermutation
  Lists.List
  Lia.

Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FMaps.
Module NatMap := FMapList.Make(Nat_as_OT).
Module NatMapP := WProperties_fun Nat_as_OT NatMap.

Set Implicit Arguments.



Section NATMAP.

  Definition nm_proj1 elt (m: NatMap.t elt): list NatMap.key := List.map fst (NatMap.elements m).
  Definition nm_proj2 elt (m: NatMap.t elt): list elt := List.map snd (NatMap.elements m).

  Definition nm_proj_v1 V1 V2 (m: NatMap.t (prod V1 V2)): NatMap.t V1 := NatMap.map fst m.
  Definition nm_proj_v2 V1 V2 (m: NatMap.t (prod V1 V2)): NatMap.t V2 := NatMap.map snd m.

  Definition nm_pop (elt: Type) : NatMap.key -> NatMap.t elt -> option (prod elt (NatMap.t elt)) :=
    fun k m => match NatMap.find k m with
            | None => None
            | Some e => Some (e, NatMap.remove k m)
            end.

  Definition nm_pop_l elt: NatMap.key -> list (NatMap.key * elt)%type -> option (prod elt (list (NatMap.key * elt)%type)) :=
    fun k l => match findA (NatMapP.F.eqb k) l with
            | None => None
            | Some e => Some (e, NatMap.Raw.remove k l)
            end.

  Variant nm_add_new {elt}: NatMap.key -> elt -> (NatMap.t elt) -> (NatMap.t elt) -> Prop :=
    | nm_add_new_intro
        k e m1 m2
        (NEW: NatMap.find k m1 = None)
        (ADD: m2 = NatMap.add k e m1)
      :
      nm_add_new k e m1 m2.

  Definition tfind elt (def: elt) (k: NatMap.key) (m: NatMap.t elt): elt :=
    match NatMap.find k m with
    | Some e => e
    | None => def
    end.

  Definition tfind_l elt (def: elt) (k: NatMap.key) (l: list (NatMap.key * elt)%type): elt :=
    match findA (NatMapP.F.eqb k) l with
    | Some e => e
    | None => def
    end.


  Definition KeySetLE {elt} (x y : NatMap.t elt) : Prop := forall k, NatMap.In k x -> NatMap.In k y.

  (* prefers x over y *)
  Definition union {elt} (x y : NatMap.t elt) : NatMap.t elt := NatMap.fold (@NatMap.add elt) x y.

  Definition disjoint {elt} (x y : NatMap.t elt) : bool := NatMap.is_empty (NatMapP.restrict x y).

  Import FMapFacts.
  Import NatMap.

  Lemma Disjoint_empty elt (x : NatMap.t elt) : NatMapP.Disjoint x (NatMap.empty elt).
  Proof. ii. des. inv H0. inv H1. Qed.

  Lemma KeySetLE_empty elt (x : NatMap.t elt) : KeySetLE (NatMap.empty elt) x.
  Proof. ii. inv H. inv H0. Qed.

  Lemma union_assoc elt (x y z : NatMap.t elt) : union (union x y) z = union x (union y z).
  Admitted.

  Lemma union_KeySetLE elt (x y : NatMap.t elt) : KeySetLE x (union x y).
  Admitted.

  Lemma inv_add_new elt k e (m1 m2 : NatMap.t elt) : nm_add_new k e m1 m2 <-> ~ NatMap.In k m1 /\ m2 = NatMap.add k e m1.
  Proof.
    split.
    - i. destruct H. eapply NatMapP.F.not_find_in_iff in NEW. eauto.
    - i. des. econs; ss. eapply NatMapP.F.not_find_in_iff. ss.
  Qed.

  Lemma union_empty elt (x : NatMap.t elt) : union (NatMap.empty elt) x = x.
  Proof. ss. Qed.

  Lemma is_empty_false elt (m : NatMap.t elt) : NatMap.is_empty m = false <-> exists k, NatMap.In k m.
  Proof.
    split.
    - i. unfold NatMap.is_empty, NatMap.Raw.is_empty in H.
      destruct m as [[] SORTED]; ss. destruct p as [k x].
      exists k. exists x. ss. econs; ss.
    - i. destruct m as [[] SORTED]; ss. des. inv H. inv H0.
  Qed.

  Lemma Empty_iff_not_In elt (x : NatMap.t elt) : NatMap.Empty x <-> ~ exists k, NatMap.In k x.
  Proof.
    split.
    - ii. destruct H0 as [k [e H0]]. specialize (H k e). ss.
    - ii. eapply H. exists a, e. ss.
  Qed.

  Lemma disjoint_false_iff' elt (x y : NatMap.t elt) : disjoint x y = false <-> exists k, NatMap.In k x /\ NatMap.In k y.
  Proof.
    unfold disjoint. split.
    - i. eapply is_empty_false in H. des. eapply NatMapP.restrict_in_iff in H. eauto.
    - i. eapply is_empty_false. des. exists k. eapply NatMapP.restrict_in_iff. eauto.
  Qed.

  Lemma disjoint_true_iff elt (x y : NatMap.t elt) : disjoint x y = true <-> NatMapP.Disjoint x y.
  Proof.
    pose proof (disjoint_false_iff' x y). rewrite <- Bool.not_false_iff_true. firstorder.
  Qed.

  Lemma disjoint_false_iff elt (x y : NatMap.t elt) : disjoint x y = false <-> ~ NatMapP.Disjoint x y.
  Proof.
    pose proof (disjoint_true_iff x y). rewrite <- Bool.not_true_iff_false. tauto.
  Qed.

  Lemma disjoint_comm elt (x y : NatMap.t elt) : disjoint x y = disjoint y x.
  Proof.
    destruct (disjoint x y) eqn: H1, (disjoint y x) eqn: H2; ss.
    - apply disjoint_true_iff in H1. apply disjoint_false_iff in H2. eapply NatMapP.Disjoint_sym in H1. tauto.
    - apply disjoint_false_iff in H1. apply disjoint_true_iff in H2. eapply NatMapP.Disjoint_sym in H2. tauto.
  Qed.

  Lemma union_in_iff elt k (x y : NatMap.t elt) : NatMap.In k (union x y) <-> NatMap.In k x \/ NatMap.In k y.
  Admitted.

  Lemma Disjoint_add elt k e (x y : NatMap.t elt)
    : NatMapP.Disjoint x (NatMap.add k e y) <-> ~ NatMap.In k x /\ NatMapP.Disjoint x y.
  Proof.
    unfold NatMapP.Disjoint. setoid_rewrite NatMapP.F.add_in_iff. split.
    - firstorder.
    - ii. des; subst; firstorder.
  Qed.

  Lemma Disjoint_remove elt k (x y : NatMap.t elt) :
    NatMapP.Disjoint x y ->
    NatMapP.Disjoint x (NatMap.remove k y).
  Proof.
    unfold NatMapP.Disjoint. setoid_rewrite NatMapP.F.remove_in_iff. firstorder.
  Qed.

  Lemma Disjoint_union elt (x y z : NatMap.t elt)
    : NatMapP.Disjoint x (union y z) <-> NatMapP.Disjoint x y /\ NatMapP.Disjoint x z.
  Proof.
    unfold NatMapP.Disjoint. setoid_rewrite union_in_iff. firstorder.
  Qed.

  Lemma not_Disjoint_sym elt (x y : NatMap.t elt) : ~ NatMapP.Disjoint x y -> ~ NatMapP.Disjoint y x.
  Proof. eauto using NatMapP.Disjoint_sym. Qed.

  Lemma Partition_In_left elt (x y z : NatMap.t elt) : NatMapP.Partition x y z -> KeySetLE y x.
  Proof.
    ii. destruct H. destruct H0. specialize (H1 k x0). des. firstorder.
  Qed.

  Lemma Partition_In_right elt (x y z : NatMap.t elt) : NatMapP.Partition x y z -> KeySetLE z x.
  Proof.
    ii. destruct H. destruct H0. specialize (H1 k x0). des. firstorder.
  Qed.

  Lemma Partition_empty elt (x : NatMap.t elt) : NatMapP.Partition x x (NatMap.empty elt).
  Proof. split; [ eapply Disjoint_empty | firstorder; inv H ]. Qed.

  Lemma In_MapsTo A k e (m : NatMap.t A) : List.In (k, e) (elements m) -> MapsTo k e m.
  Proof.
    unfold MapsTo, Raw.PX.MapsTo, elements, Raw.elements.
    remember (this m) as l. clear m Heql. intros.
    induction l; ss. destruct H.
    - eapply InA_cons_hd. subst. ss.
    - eapply InA_cons_tl. eauto.
  Qed.

  Lemma In_nm_proj1 A k (m : NatMap.t A) : List.In k (nm_proj1 m) -> exists e, MapsTo k e m.
  Proof.
    unfold nm_proj1, MapsTo, Raw.PX.MapsTo, elements, Raw.elements.
    remember (this m) as l. clear m Heql. intros.
    induction l; ss. destruct H.
    - eexists. eapply InA_cons_hd. subst. ss.
    - eapply IHl in H. destruct H. eexists. eapply InA_cons_tl. eauto.
  Qed.

  Lemma Permutation_remove A k e (m : NatMap.t A) l :
    Permutation (elements m) ((k, e) :: l) -> Permutation (elements (NatMap.remove k m)) l.
  Proof.
    unfold elements, Raw.elements, remove.
    destruct m as [m SORTED]. ss.
    revert l. induction m; i.
    - eapply Permutation_length in H. ss.
    - assert (List.In a ((k, e) :: l)) by (rewrite <- H; econs; ss).
      destruct H0.
      + inv H0. eapply Permutation_cons_inv in H. ss.
        Raw.MX.elim_comp_eq k k. eauto.
    + eapply Add_inv in H0. destruct H0. eapply Permutation_Add in H0.
      rewrite <- H0 in *. clear l H0.
      rewrite perm_swap in H. eapply Permutation_cons_inv in H.
      assert (List.In (k, e) m).
      { eapply Permutation_in.
        - symmetry; eauto.
        - econs; ss.
      }
      epose proof (Sorted_extends _ SORTED).
      eapply Forall_forall in H1; eauto.
      destruct a. ss. Raw.MX.elim_comp_gt k n.
      inv SORTED.
      econs. eapply IHm; eauto.
    Unshelve. compute. lia.
  Qed.

  Lemma Permutation_add A k e (m : NatMap.t A) l :
    ~ NatMap.In k m -> Permutation (elements m) l -> Permutation (elements (add k e m)) ((k, e) :: l).
  Proof.
    unfold elements, Raw.elements, add, In.
    destruct m as [m SORTED]. ss. revert l. induction m; intros l H1 H2.
    - rewrite <- H2. ss.
    - destruct a. ss.
      assert (k = n \/ k < n \/ k > n) by lia.
      destruct H as [|[]].
      + exfalso. eapply H1. exists a. left. ss.
      + Raw.MX.elim_comp_lt k n. econs; eauto.
      + Raw.MX.elim_comp_gt k n.
        rewrite <- H2. rewrite perm_swap. econs.
        inv SORTED. eapply IHm; eauto.
        intro. eapply H1. unfold Raw.PX.In in *.
        destruct H0. eexists. right. eauto.
  Qed.

  Lemma InA_In A x (l : list A) : InA (@eq A) x l -> List.In x l.
  Proof. i. induction H.
         - left; eauto.
         - right; eauto.
  Qed.

  Lemma InA_In' A k (e : A) l :
    SetoidList.InA (@eq_key_elt A) (k, e) l -> List.In (k, e) l.
  Proof.
    i. induction H.
    - left. destruct H; ss. subst. destruct y; ss.
    - right. eauto.
  Qed.

  Lemma Permutation_NoDupA A l1 l2 :
    Permutation l1 l2 ->
    SetoidList.NoDupA (eq_key (elt:=A)) l1 ->
    SetoidList.NoDupA (eq_key (elt:=A)) l2.
  Proof.
    i.
    eapply PermutationA_preserves_NoDupA; eauto.
    eapply Permutation_PermutationA; eauto.
  Qed.



  Import NatMapP.

  Lemma eqlistA_eq_key_elt_eq
        elt (this0 this1 : Raw.t elt)
        (EQLA: eqlistA (eq_key_elt (elt:=elt)) this0 this1)
    :
    this0 = this1.
  Proof.
    induction EQLA; ss.
    destruct x, x'. unfold eq_key_elt, Raw.PX.eqke in *. des; ss; clarify.
  Qed.

  Lemma nm_eq_is_equal
        elt (m1 m2: t elt)
        (EQ: Equal m1 m2)
    :
    m1 = m2.
  Proof.
    destruct m1, m2.
    assert (EQ1: this0 = this1).
    { match goal with
      | EQ: Equal ?lhs ?rhs |- _ => cut (forall k e, (MapsTo k e lhs) <-> (MapsTo k e rhs))
      end.
      2:{ i. rewrite EQ. auto. }
      intro MT.
      cut (eqlistA (@eq_key_elt elt) this0 this1).
      2:{ eapply SortA_equivlistA_eqlistA; eauto.
          eapply eqke_equiv. eapply Raw.PX.ltk_strorder.
          { ii. unfold eq_key_elt, Raw.PX.eqke in *. des. destruct x, y, x0, y0; ss; clarify. }
          match goal with
          | EQ: Equal ?_lhs ?_rhs |- _ => remember _lhs as lhs; remember _rhs as rhs
          end.
          replace this0 with (elements lhs). replace this1 with (elements rhs).
          2,3: clarify; ss.
          split; i.
          - destruct x. eapply elements_1. eapply MT. eapply elements_2; auto.
          - destruct x. eapply elements_1. eapply MT. eapply elements_2; auto.
      }
      eapply eqlistA_eq_key_elt_eq; eauto.
    }
    revert sorted0 sorted1 EQ. rewrite EQ1. i.
    rewrite (proof_irrelevance sorted0 sorted1). auto.
  Qed.

  Variable elt: Type.

  Lemma nm_find_add_eq
        (m: t elt) k e
    :
    find k (add k e m) = Some e.
  Proof.
    eapply find_1. eapply add_1. auto.
  Qed.

  Lemma nm_find_add_neq
        (m: t elt) k1 k2 e
        (NEQ: k2 <> k1)
    :
    find k1 (add k2 e m) = find k1 m.
  Proof.
    match goal with | |- ?lhs = _ => destruct lhs eqn:FA end.
    - pose (find_2 FA) as MT. pose (add_3 NEQ MT) as MT0. pose (find_1 MT0) as FA1. auto.
    - match goal with | |- _ = ?rhs => destruct rhs eqn:FA1 end; auto.
      pose (find_2 FA1) as MT. pose (add_2 e NEQ MT) as MT1. pose (find_1 MT1) as FA2. clarify.
  Qed.

  Lemma nm_find_rm_eq
        (m: t elt) k
    :
    find k (remove k m) = None.
  Proof.
    eapply F.remove_eq_o; auto.
  Qed.

  Lemma nm_find_rm_neq
        (m: t elt) k1 k2
        (NEQ: k2 <> k1)
    :
    find k1 (remove k2 m) = find k1 m.
  Proof.
    eapply F.remove_neq_o; auto.
  Qed.

  Lemma nm_add_add_equal
        (m: t elt) k e1 e2
    :
    Equal (add k e2 (add k e1 m)) (add k e2 m).
  Proof.
    eapply F.Equal_mapsto_iff. i. split; i.
    - eapply F.add_mapsto_iff in H. des; clarify. eapply add_1; auto.
      eapply add_2; eauto. eapply add_3 in H0; auto.
    - eapply F.add_mapsto_iff in H. des; clarify. eapply add_1; auto.
      eapply add_2; eauto. eapply add_2; eauto.
  Qed.
  Lemma nm_add_add_eq
        (m: t elt) k e1 e2
    :
    (add k e2 (add k e1 m)) = (add k e2 m).
  Proof. eapply nm_eq_is_equal. eapply nm_add_add_equal. Qed.

  Lemma nm_rm_add_equal
        (m: t elt) k e1 e2
    :
    Equal (remove k (add k e1 m)) (remove k (add k e2 m)).
  Proof.
    eapply F.Equal_mapsto_iff. i. split; i.
    - eapply F.remove_mapsto_iff in H. des; clarify.
      eapply remove_2; eauto. eapply add_2; eauto. hexploit add_3; eauto.
    - eapply F.remove_mapsto_iff in H. des; clarify.
      eapply remove_2; eauto. eapply add_2; eauto. hexploit add_3; eauto.
  Qed.
  Lemma nm_rm_add_eq
        (m: t elt) k e1 e2
    :
    (remove k (add k e1 m)) = (remove k (add k e2 m)).
  Proof. eapply nm_eq_is_equal. eapply nm_rm_add_equal. Qed.

  Lemma nm_find_none_rm_add_equal
        (m: t elt) k e
        (FIND: find k m = None)
    :
    Equal (remove k (add k e m)) m.
  Proof.
    eapply F.Equal_mapsto_iff. i. split; i.
    - eapply F.remove_mapsto_iff in H. des; clarify.
      erewrite F.add_neq_mapsto_iff in H0; eauto.
    - destruct (F.eq_dec k0 k); clarify.
      + eapply find_1 in H. clarify.
      + eapply remove_2; auto. eapply add_2; auto.
  Qed.
  Lemma nm_find_none_rm_add_eq
        (m: t elt) k e
        (FIND: find k m = None)
    :
    (remove k (add k e m)) = m.
  Proof. eapply nm_eq_is_equal, nm_find_none_rm_add_equal; auto. Qed.

  Lemma nm_find_none_rm_equal
        (m: t elt) k
        (FIND: find k m = None)
    :
    Equal (remove k m) m.
  Proof.
    eapply F.Equal_mapsto_iff. i. split; i.
    - eapply F.remove_mapsto_iff in H. des; clarify.
    - destruct (F.eq_dec k0 k); clarify.
      + eapply find_1 in H. clarify.
      + eapply remove_2; auto.
  Qed.
  Lemma nm_find_none_rm_eq
        (m: t elt) k
        (FIND: find k m = None)
    :
    (remove k m) = m.
  Proof. eapply nm_eq_is_equal, nm_find_none_rm_equal; auto. Qed.

  Lemma nm_find_some_add_equal
        (m: t elt) k e
        (FIND: find k m = Some e)
    :
    Equal (add k e m) m.
  Proof.
    eapply F.Equal_mapsto_iff. i. split; i.
    - eapply F.add_mapsto_iff in H. des; clarify. eapply find_2; eauto.
    - destruct (F.eq_dec k0 k); clarify.
      + eapply find_1 in H. clarify. eapply add_1; auto.
      + eapply add_2; auto.
  Qed.
  Lemma nm_find_some_add_eq
        (m: t elt) k e
        (FIND: find k m = Some e)
    :
    (add k e m) = m.
  Proof. eapply nm_eq_is_equal, nm_find_some_add_equal; auto. Qed.

  Lemma nm_rm_add_rm_equal
        (m: t elt) k e
    :
    Equal (remove k (add k e m)) (remove k m).
  Proof.
    eapply F.Equal_mapsto_iff. i. split; i.
    - eapply F.remove_mapsto_iff in H. des; clarify.
      erewrite F.add_neq_mapsto_iff in H0; eauto. eapply remove_2; eauto.
    - eapply F.remove_mapsto_iff in H. des; clarify.
      eapply remove_2; eauto. eapply add_2; eauto.
  Qed.
  Lemma nm_rm_add_rm_eq
        (m: t elt) k e
    :
    (remove k (add k e m)) = remove k m.
  Proof. eapply nm_eq_is_equal, nm_rm_add_rm_equal; auto. Qed.

  Lemma nm_rm_rm_equal
        (m: t elt) k
    :
    Equal (remove k (remove k m)) (remove k m).
  Proof.
    eapply nm_find_none_rm_equal. eapply nm_find_rm_eq.
  Qed.
  Lemma nm_rm_rm_eq
        (m: t elt) k
    :
    (remove k (remove k m)) = (remove k m).
  Proof. eapply nm_eq_is_equal. eapply nm_rm_rm_equal. Qed.

  Lemma nm_add_rm_equal
        (m: t elt) k e
    :
    Equal (add k e (remove k m)) (add k e m).
  Proof.
    eapply F.Equal_mapsto_iff. i. split; i.
    - eapply F.add_mapsto_iff in H. des; clarify.
      + eapply add_1; auto.
      + eapply F.remove_mapsto_iff in H0. des; clarify. eapply add_2; eauto.
    - eapply F.add_mapsto_iff in H. des; clarify.
      + eapply add_1; eauto.
      + eapply add_2; auto. eapply remove_2; auto.
  Qed.
  Lemma nm_add_rm_eq
        (m: t elt) k e
    :
    (add k e (remove k m)) = add k e m.
  Proof. eapply nm_eq_is_equal, nm_add_rm_equal; auto. Qed.

  Lemma nm_find_none_add_rm_is_equal
        (m1 m2: t elt) k e
        (FIND: find k m1 = None)
        (ADD: Equal (add k e m1) m2)
    :
    Equal m1 (remove k m2).
  Proof.
    rewrite <- ADD. rewrite nm_find_none_rm_add_equal; auto. reflexivity.
  Qed.
  Lemma nm_find_none_add_rm_is_eq
        (m1 m2: t elt) k e
        (FIND: find k m1 = None)
        (ADD: (add k e m1) = m2)
    :
    m1 = (remove k m2).
  Proof. eapply nm_eq_is_equal, nm_find_none_add_rm_is_equal; eauto. rewrite ADD. reflexivity. Qed.


  Lemma nm_pop_find_some
        (m1 m2: t elt) k e
        (POP: nm_pop k m1 = Some (e, m2))
    :
    find k m1 = Some e.
  Proof.
    unfold nm_pop in *. des_ifs.
  Qed.

  Lemma nm_pop_find_none
        (m: t elt) k
        (POP: nm_pop k m = None)
    :
    find k m = None.
  Proof.
    unfold nm_pop in *. des_ifs.
  Qed.

  Lemma nm_pop_res_find_none
        (m1 m2: t elt) k e
        (POP: nm_pop k m1 = Some (e, m2))
    :
    find k m2 = None.
  Proof.
    unfold nm_pop in *. des_ifs. eapply nm_find_rm_eq.
  Qed.

  Lemma nm_pop_res_is_rm_equal
        (m1 m2: t elt) k e
        (POP: nm_pop k m1 = Some (e, m2))
    :
    Equal (remove k m1) m2.
  Proof.
    unfold nm_pop in *. des_ifs.
  Qed.
  Lemma nm_pop_res_is_rm_eq
        (m1 m2: t elt) k e
        (POP: nm_pop k m1 = Some (e, m2))
    :
    (remove k m1) = m2.
  Proof. eapply nm_eq_is_equal. eapply nm_pop_res_is_rm_equal; eauto. Qed.

  Lemma nm_pop_res_is_add_equal
        (m1 m2: t elt) k e
        (POP: nm_pop k m1 = Some (e, m2))
    :
    Equal m1 (add k e m2).
  Proof.
    unfold nm_pop in *. des_ifs. rewrite nm_add_rm_equal. rewrite nm_find_some_add_equal; eauto. reflexivity.
  Qed.
  Lemma nm_pop_res_is_add_eq
        (m1 m2: t elt) k e
        (POP: nm_pop k m1 = Some (e, m2))
    :
    m1 = (add k e m2).
  Proof. eapply nm_eq_is_equal, nm_pop_res_is_add_equal; eauto. Qed.

  Lemma nm_pop_find_none_add_same_equal
        (m1 m2: t elt) k e1 e2
        (FIND: find k m1 = None)
        (POP: nm_pop k (add k e1 m1) = Some (e2, m2))
    :
    e1 = e2 /\ (Equal m1 m2).
  Proof.
    hexploit nm_pop_res_is_rm_equal; eauto. intro RM.
    hexploit nm_pop_find_some; eauto. intro FIND2.
    rewrite nm_find_add_eq in FIND2. inv FIND2. split; auto.
    rewrite <- RM. rewrite nm_find_none_rm_add_equal; auto. reflexivity.
  Qed.
  Lemma nm_pop_find_none_add_same_eq
        (m1 m2: t elt) k e1 e2
        (FIND: find k m1 = None)
        (POP: nm_pop k (add k e1 m1) = Some (e2, m2))
    :
    e1 = e2 /\ (m1 = m2).
  Proof. hexploit nm_pop_find_none_add_same_equal; eauto. i; des. split; auto. eapply nm_eq_is_equal; auto. Qed.

  Lemma nm_pop_neq_find_some
        (m1 m2: t elt) k1 k2 e e0
        (POP : nm_pop k2 (add k1 e m1) = Some (e0, m2))
        (NEQ: k1 <> k2)
    :
    find k1 m2 = Some e.
  Proof.
    hexploit nm_pop_res_is_rm_equal; eauto. i. rewrite <- H. rewrite F.remove_neq_o; auto. apply nm_find_add_eq.
  Qed.

  Lemma nm_pop_neq_find_some_eq
        (m1 m2: t elt) k1 k2 e e0 e1
        (POP : nm_pop k2 (add k1 e m1) = Some (e0, m2))
        (NEQ: k1 <> k2)
        (FIND: find k1 m2 = Some e1)
    :
    e1 = e.
  Proof.
    hexploit nm_pop_neq_find_some; eauto. i. clarify.
  Qed.

  Lemma nm_pop_add_eq
        (m: t elt) k e
    :
    nm_pop k (add k e m) = Some (e, remove k m).
  Proof.
    unfold nm_pop. rewrite nm_find_add_eq. rewrite nm_rm_add_rm_eq. auto.
  Qed.


  Lemma nm_find_some_tfind
        (m: t elt) k e
        (SOME: find k m = Some e)
    :
    forall d, tfind d k m = e.
  Proof.
    i. unfold tfind. rewrite SOME. auto.
  Qed.

  Lemma nm_find_none_tfind
        (m: t elt) k
        (NONE: find k m = None)
    :
    forall d, tfind d k m = d.
  Proof.
    i. unfold tfind. rewrite NONE. auto.
  Qed.


  Lemma tfind_to_tfind_l
        (m: t elt) d
    :
    forall k, tfind d k m = tfind_l d k (elements m).
  Proof.
    i. unfold tfind, tfind_l. rewrite F.elements_o. auto.
  Qed.


  Lemma nm_pop_l_eq_none
        (m: t elt)
        k
        (POP: nm_pop k m = None)
    :
    nm_pop_l k (elements m) = None.
  Proof.
    unfold nm_pop, nm_pop_l in *. rewrite <- F.elements_o. des_ifs.
  Qed.

  Lemma nm_pop_l_eq_some
        (m: t elt)
        k e m'
        (POP: nm_pop k m = Some (e, m'))
    :
    nm_pop_l k (elements m) = Some (e, elements m').
  Proof.
    unfold nm_pop, nm_pop_l in *. rewrite <- F.elements_o. des_ifs.
  Qed.

End NATMAP.

Ltac solve_andb := 
  repeat match goal with
    | [ H : andb _ _ = true |- _ ] => eapply Bool.andb_true_iff in H; destruct H
    | [ H : andb _ _ = false |- _ ] => eapply Bool.andb_false_iff in H; destruct H
    end.

Ltac solve_disjoint :=
  repeat match goal with
    | [ H : disjoint _ _ = true |- _ ] => eapply disjoint_true_iff in H
    | [ H : disjoint _ _ = false |- _ ] => eapply disjoint_false_iff in H
    end;
  repeat match goal with
    | [ H :   NatMapP.Disjoint _ (NatMap.empty _)   |- _ ] => clear H
    | [ H : ~ NatMapP.Disjoint _ (NatMap.empty _)   |- _ ] => exfalso; eapply H, Disjoint_empty
    | [ H :   NatMapP.Disjoint _ (NatMap.add _ _ _) |- _ ] => eapply Disjoint_add in H; destruct H
    | [ H :   NatMapP.Disjoint _ (union _ _)        |- _ ] => eapply Disjoint_union in H
    | [ H : ~ NatMapP.Disjoint _ (union _ _)        |- _ ] => rewrite Disjoint_union in H
    (* symmetricity *)
    | [ H :   NatMapP.Disjoint (NatMap.empty _) _   |- _ ] => clear H
    | [ H : ~ NatMapP.Disjoint (NatMap.empty _) _   |- _ ] => eapply not_Disjoint_sym in H
    | [ H :   NatMapP.Disjoint (NatMap.add _ _ _) _ |- _ ] => eapply NatMapP.Disjoint_sym in H
    | [ H :   NatMapP.Disjoint (union _ _) _        |- _ ] => eapply NatMapP.Disjoint_sym in H
    | [ H : ~ NatMapP.Disjoint (union _ _) _        |- _ ] => eapply not_Disjoint_sym in H
    end.

Tactic Notation "solve_disjoint!" :=
  solve_andb;
  solve_disjoint;
  firstorder using NatMapP.Disjoint_sym;
  fail.

Module NatSet.
  Definition t := NatMap.t unit.
  Definition empty: t := @NatMap.empty unit.
  Definition add x m := @NatMap.add unit x tt m.
  Definition remove := @NatMap.remove unit.
  Definition elements := @nm_proj1 unit.
  Definition Empty := @NatMap.Empty unit.
  Definition In := @NatMap.In unit.
  Definition add_new k m1 m2 := @nm_add_new unit k tt m1 m2.
End NatSet.

Section NATSET.

  Lemma union_comm (x y : NatSet.t) : union x y = union y x.
  Admitted.

  Lemma Empty_nil s : NatSet.Empty s -> NatSet.elements s = [].
  Proof.
    i. destruct s as [s SORTED]; ss. destruct s; ss.
    exfalso. eapply H. econs. ss.
  Qed.

  Lemma Empty_nil_neg s : ~ NatSet.Empty s -> NatSet.elements s <> [].
  Proof.
    destruct s as [s SORTED]. ii.
    eapply map_eq_nil in H0. ss. subst.
    eapply H. ii. eapply InA_nil; eauto.
  Qed.

  Lemma In_NatSetIn x s : In x (NatSet.elements s) -> NatSet.In x s.
  Proof.
    i. exists tt. unfold NatSet.elements, nm_proj1 in *. destruct s as [s SORTED]; ss. clear SORTED.
    induction s; ss. destruct H.
    - destruct a as [a []]; ss; subst. econs 1. econs; ss.
    - econs 2. eapply IHs. ss.
  Qed.

  Lemma NatSetIn_In x s : NatSet.In x s -> In x (NatSet.elements s).
  Proof.
    i. destruct s as [s SORTED]. destruct H. unfold NatSet.elements, nm_proj1. ss. clear SORTED.
    induction H.
    - econs 1. inv H. ss.
    - econs 2. eapply IHInA.
  Qed.

  Lemma NatSet_In_MapsTo x s : NatSet.In x s <-> NatMap.MapsTo x tt s.
  Proof.
    (* unfold NatSet.In, NatMap.In, NatMap.Raw.PX.In. i. des. destruct e. ss. *)
    split.
    - i. destruct H. destruct x0. ss.
    - firstorder.
  Qed.

  Lemma NatSet_Permutation_remove x s l :
    Permutation (NatSet.elements s) (x :: l) -> Permutation (NatSet.elements (NatSet.remove x s)) l.
  Proof.
    unfold NatSet.elements, nm_proj1. intro H.
    eapply Permutation_map with (f := fun x => (x, tt)) in H.
    rewrite map_map in H. replace (fun x => (fst x, tt)) with (fun x : NatMap.key * unit => x) in H; cycle 1.
    { extensionalities. destruct H0 as [a []]. ss. }
    rewrite map_id in H. simpl in H.
    eapply Permutation_remove in H.
    eapply Permutation_map with (f := fst) in H.
    rewrite map_map in H. simpl in H. rewrite map_id in H. ss.
  Qed.

  Lemma NatSet_Permutation_add x s l :
    ~ NatSet.In x s -> Permutation (NatSet.elements s) l -> Permutation (NatSet.elements (NatSet.add x s)) (x :: l).
  Proof.
    unfold NatSet.elements, nm_proj1. intros H0 H.
    eapply Permutation_map with (f := fun x => (x, tt)) in H.
    rewrite map_map in H. replace (fun x => (fst x, tt)) with (fun x : NatMap.key * unit => x) in H; cycle 1.
    { extensionalities. destruct H1 as [a []]. ss. }
    rewrite map_id in H. simpl in H.
    eapply Permutation_add in H; [| eapply H0 ].
    eapply Permutation_map with (f := fst) in H. simpl in H.
    rewrite map_map in H. rewrite map_id in H. eapply H.
  Qed.

  Lemma unfold_Partition (x y z : NatSet.t) : NatMapP.Partition x y z <-> NatMapP.Disjoint y z /\ (forall k, NatSet.In k x <-> NatSet.In k y \/ NatSet.In k z).
  Proof.
    split; [firstorder |].
    i. des. split; ss. i. destruct e. rewrite <- ! NatSet_In_MapsTo. ss.
  Qed.

  Lemma Partition_add k e (x x' y z : NatSet.t) :
    NatMapP.Partition x y z ->
    nm_add_new k e x x' ->
    NatMapP.Partition x' y (NatMap.add k e z).
  Proof.
    i. eapply inv_add_new in H0. des; subst. eapply unfold_Partition.
    split.
    - eapply Disjoint_add. firstorder using Partition_In_left.
    - setoid_rewrite NatMapP.F.add_in_iff. firstorder.
  Qed.

  Lemma Partition_remove k (x y z : NatSet.t) :
    NatMapP.Partition x y z ->
    NatMap.In k z ->
    NatMapP.Partition (NatSet.remove k x) y (NatSet.remove k z).
  Proof.
    rewrite 2 unfold_Partition. i. des. split.
    - eapply Disjoint_remove. ss.
    - i. setoid_rewrite NatMapP.F.remove_in_iff.
      firstorder. intro. subst. firstorder.
  Qed.

End NATSET.



Section AUX.

  Definition unit1 {E} : E -> unit := fun _ => tt.
  Definition key_set {elt} : NatMap.t elt -> NatSet.t :=
    fun m => NatMap.map unit1 m.

  Definition nm_wf_pair_equal {elt1 elt2} (m1: NatMap.t elt1) (m2: NatMap.t elt2) := NatMap.Equal (key_set m1) (key_set m2).
  Definition nm_wf_pair {elt1 elt2} (m1: NatMap.t elt1) (m2: NatMap.t elt2) := (key_set m1) = (key_set m2).

  Import NatMap.
  Import NatMapP.

  Lemma nm_wf_pair_implies
        elt1 elt2 (m1: t elt1) (m2: t elt2)
        (WF: nm_wf_pair m1 m2)
    :
    nm_wf_pair_equal m1 m2.
  Proof.
    unfold nm_wf_pair , nm_wf_pair_equal in *. rewrite WF. reflexivity.
  Qed.

  Lemma nm_wf_pair_equal_sym
        elt1 elt2 (m1: t elt1) (m2: t elt2)
        (WF: nm_wf_pair_equal m1 m2)
    :
    nm_wf_pair_equal m2 m1.
  Proof.
    unfold nm_wf_pair_equal in *. rewrite WF. reflexivity.
  Qed.
  Lemma nm_wf_pair_sym
        elt1 elt2 (m1: t elt1) (m2: t elt2)
        (WF: nm_wf_pair m1 m2)
    :
    nm_wf_pair m2 m1.
  Proof.
    unfold nm_wf_pair in *. rewrite WF. reflexivity.
  Qed.


  Lemma key_set_find_none1
        elt (m: NatMap.t elt) k
        (FIND: find k m = None)
    :
    find k (key_set m) = None.
  Proof.
    unfold key_set. rewrite F.map_o. rewrite FIND. ss.
  Qed.

  Lemma key_set_find_none2
        elt (m: NatMap.t elt) k
        (FIND: find k (key_set m) = None)
    :
    find k m = None.
  Proof.
    unfold key_set in *. rewrite F.map_o in *. destruct (find k m); ss.
  Qed.

  Lemma key_set_find_some1
        elt (m: NatMap.t elt) k e
        (FIND: find k m = Some e)
    :
    find k (key_set m) = Some tt.
  Proof.
    unfold key_set. rewrite F.map_o. rewrite FIND. ss.
  Qed.

  Lemma key_set_find_some2
        elt (m: NatMap.t elt) k
        (FIND: find k (key_set m) = Some tt)
    :
    exists e, find k m = Some e.
  Proof.
    unfold key_set in *. rewrite F.map_o in *. destruct (find k m); ss. eauto.
  Qed.

  Lemma nm_map_equal_equal
        elt (m1 m2: t elt) elt' (f: elt -> elt')
        (RM: Equal m1 m2)
    :
    Equal (map f m1) (map f m2).
  Proof. rewrite RM. reflexivity. Qed.
  Lemma nm_map_equal_eq
        elt (m1 m2: t elt) elt' (f: elt -> elt')
        (RM: Equal m1 m2)
    :
    (map f m1) = (map f m2).
  Proof. eapply nm_eq_is_equal, nm_map_equal_equal. auto. Qed.

  Lemma nm_map_rm_comm_equal
        elt (m: t elt) elt' (f: elt -> elt') k
    :
    Equal (remove k (map f m)) (map f (remove k m)).
  Proof.
    eapply F.Equal_mapsto_iff. i. split; i.
    - eapply F.remove_mapsto_iff in H. des. eapply F.map_mapsto_iff in H0. des; clarify.
      eapply map_1. eapply remove_2; eauto.
    - eapply F.map_mapsto_iff in H. des; clarify. eapply F.remove_mapsto_iff in H0. des.
      eapply remove_2; auto. eapply map_1; auto.
  Qed.
  Lemma nm_map_rm_comm_eq
        elt (m: t elt) elt' (f: elt -> elt') k
    :
    (remove k (map f m)) = (map f (remove k m)).
  Proof. eapply nm_eq_is_equal, nm_map_rm_comm_equal. Qed.

  Lemma key_set_pull_rm_equal
        elt (m: NatMap.t elt) k
    :
    Equal (key_set (remove k m)) (remove k (key_set m)).
  Proof. unfold key_set. rewrite <- nm_map_rm_comm_equal. ss. Qed.
  Lemma key_set_pull_rm_eq
        elt (m: NatMap.t elt) k
    :
    (key_set (remove k m)) = (remove k (key_set m)).
  Proof. eapply nm_eq_is_equal. eapply key_set_pull_rm_equal. Qed.

  Lemma nm_map_add_comm_equal
        elt (m: t elt) elt' (f: elt -> elt') k e
    :
    Equal (add k (f e) (map f m)) (map f (add k e m)).
  Proof.
    eapply F.Equal_mapsto_iff. i. split; i.
    - eapply F.add_mapsto_iff in H. des; clarify.
      + eapply map_1. eapply add_1; auto.
      + eapply F.map_mapsto_iff in H0. des; clarify. eapply map_1. eapply add_2; eauto.
    - eapply F.map_mapsto_iff in H. des; clarify. eapply F.add_mapsto_iff in H0. des; clarify.
      + eapply add_1; auto.
      + eapply add_2; auto. eapply map_1; auto.
  Qed.
  Lemma nm_map_add_comm_eq
        elt (m: t elt) elt' (f: elt -> elt') k e
    :
    (add k (f e) (map f m)) = (map f (add k e m)).
  Proof. eapply nm_eq_is_equal, nm_map_add_comm_equal. Qed.

  Lemma key_set_pull_add_equal
        elt (m: NatMap.t elt) e k
    :
    Equal (key_set (add k e m)) (add k tt (key_set m)).
  Proof. unfold key_set. rewrite <- nm_map_add_comm_equal. ss. Qed.
  Lemma key_set_pull_add_eq
        elt (m: NatMap.t elt) e k
    :
    (key_set (add k e m)) = (add k tt (key_set m)).
  Proof. eapply nm_eq_is_equal. eapply key_set_pull_add_equal. Qed.


  Lemma nm_map_rm_equal
        elt (m1 m2: t elt) elt' (f: elt -> elt')
        k
        (RM: Equal (remove k m1) m2)
    :
    Equal (remove k (map f m1)) (map f m2).
  Proof. rewrite nm_map_rm_comm_equal. eapply nm_map_equal_equal. auto. Qed.
  Lemma nm_map_rm_eq
        elt (m1 m2: t elt) elt' (f: elt -> elt')
        k
        (RM: Equal (remove k m1) m2)
    :
    (remove k (map f m1)) = (map f m2).
  Proof. eapply nm_eq_is_equal. eapply nm_map_rm_equal. auto. Qed.

  Lemma nm_map_add_equal
        elt (m1 m2: t elt) elt' (f: elt -> elt')
        k e
        (RM: Equal (add k e m1) m2)
    :
    Equal (add k (f e) (map f m1)) (map f m2).
  Proof. rewrite nm_map_add_comm_equal. eapply nm_map_equal_equal. auto. Qed.
  Lemma nm_map_add_eq
        elt (m1 m2: t elt) elt' (f: elt -> elt')
        k e
        (RM: Equal (add k e m1) m2)
    :
    (add k (f e) (map f m1)) = (map f m2).
  Proof. eapply nm_eq_is_equal. eapply nm_map_add_equal. auto. Qed.

  Lemma nm_wf_pair_equal_find_cases
        elt1 elt2 (m1: NatMap.t elt1) (m2: NatMap.t elt2)
        (WF: nm_wf_pair_equal m1 m2)
    :
    forall k, (find k m1 = None -> find k m2 = None) /\ (~ (find k m1 = None) -> ~ (find k m2 = None)).
  Proof.
    unfold nm_wf_pair_equal in *. i. split; i.
    - eapply key_set_find_none1 in H. eapply key_set_find_none2. rewrite <- WF. auto.
    - ii; apply H; clear H.
      eapply key_set_find_none1 in H0. eapply key_set_find_none2. rewrite WF. auto.
  Qed.
  Lemma nm_wf_pair_find_cases
        elt1 elt2 (m1: NatMap.t elt1) (m2: NatMap.t elt2)
        (WF: nm_wf_pair m1 m2)
    :
    forall k, (find k m1 = None -> find k m2 = None) /\ (~ (find k m1 = None) -> ~ (find k m2 = None)).
  Proof. eapply nm_wf_pair_equal_find_cases. eapply nm_wf_pair_implies. auto. Qed.

  Lemma nm_wf_pair_equal_pop_cases
        elt1 elt2 (m1: NatMap.t elt1) (m2: NatMap.t elt2)
        (WF: nm_wf_pair_equal m1 m2)
    :
    forall k, ((nm_pop k m1 = None) /\ (nm_pop k m2 = None)) \/
           (exists e1 e2 m3 m4,
               (nm_pop k m1 = Some (e1, m3)) /\
                 (nm_pop k m2 = Some (e2, m4)) /\
                 (nm_wf_pair_equal m3 m4)).
  Proof.
    i. hexploit nm_wf_pair_equal_find_cases. eapply nm_wf_pair_equal_sym in WF. eauto.
    hexploit nm_wf_pair_equal_find_cases; eauto. do 2 instantiate (1:=k). i. des.
    unfold nm_wf_pair_equal in *. unfold key_set in *. destruct (nm_pop k m1) eqn:POP1.
    { destruct (nm_pop k m2) eqn:POP2.
      { right. destruct p, p0. esplits; eauto. eapply nm_pop_res_is_rm_equal in POP1, POP2.
        rewrite <- POP1, <- POP2. rewrite <- ! nm_map_rm_comm_equal. rewrite WF. reflexivity. }
      eapply nm_pop_find_none in POP2. destruct p. eapply nm_pop_find_some in POP1.
      apply H0 in POP2. clarify.
    }
    { destruct (nm_pop k m2) eqn:POP2.
      { eapply nm_pop_find_none in POP1. destruct p. eapply nm_pop_find_some in POP2.
        apply H in POP1. clarify. }
      left; auto.
    }
  Qed.
  Lemma nm_wf_pair_pop_cases
        elt1 elt2 (m1: NatMap.t elt1) (m2: NatMap.t elt2)
        (WF: nm_wf_pair m1 m2)
    :
    forall k, ((nm_pop k m1 = None) /\ (nm_pop k m2 = None)) \/
           (exists e1 e2 m3 m4,
               (nm_pop k m1 = Some (e1, m3)) /\
                 (nm_pop k m2 = Some (e2, m4)) /\
                 (nm_wf_pair m3 m4)).
  Proof.
    i. hexploit nm_wf_pair_equal_pop_cases. eapply nm_wf_pair_implies. eauto. i; des; eauto.
    right. esplits; eauto. unfold nm_wf_pair, nm_wf_pair_equal in *. eapply nm_eq_is_equal. auto.
  Qed.


  Lemma nm_map_empty1
        elt1 (m: NatMap.t elt1) elt2 (f: elt1 -> elt2)
        (EMP: Empty m)
    :
    Empty (map f m).
  Proof.
    rewrite elements_Empty in *. ss. unfold elements, Raw.elements in *. rewrite EMP. ss.
  Qed.

  Lemma nm_map_empty2
        elt1 (m: NatMap.t elt1) elt2 (f: elt1 -> elt2)
        (EMP: Empty (map f m))
    :
    Empty m.
  Proof.
    rewrite elements_Empty in *. ss. revert EMP. destruct m. induction this0; i; ss.
    des_ifs.
  Qed.

  Lemma nm_pop_none_map1
        elt1 (m: NatMap.t elt1) elt2 (f: elt1 -> elt2)
        k
        (POP: nm_pop k m = None)
    :
    nm_pop k (map f m) = None.
  Proof.
    unfold nm_pop in *. rewrite F.map_o. des_ifs.
  Qed.

  Lemma nm_pop_none_map2
        elt1 (m: NatMap.t elt1) elt2 (f: elt1 -> elt2)
        k
        (POP: nm_pop k (map f m) = None)
    :
    nm_pop k m = None.
  Proof.
    unfold nm_pop in *. rewrite F.map_o in POP. des_ifs.
  Qed.

  Lemma nm_pop_some_map1
        elt1 (m1 m2: NatMap.t elt1) elt2 (f: elt1 -> elt2)
        k e
        (POP: nm_pop k m1 = Some (e, m2))
    :
    nm_pop k (map f m1) = Some (f e, map f m2).
  Proof.
    unfold nm_pop in *. rewrite F.map_o. des_ifs. ss. inv Heq. do 2 f_equal.
    rewrite nm_map_rm_comm_eq. reflexivity.
  Qed.

  Lemma key_set_empty1
        elt (m: NatMap.t elt)
        (EMP: Empty m)
    :
    Empty (key_set m).
  Proof. eapply nm_map_empty1; eauto. Qed.

  Lemma key_set_empty2
        elt (m: NatMap.t elt)
        (EMP: Empty (key_set m))
    :
    Empty m.
  Proof. eapply nm_map_empty2; eauto. Qed.


  Lemma nm_wf_pair_equal_empty
        elt1 elt2 (m1: NatMap.t elt1) (m2: NatMap.t elt2)
        (WF: nm_wf_pair_equal m1 m2)
    :
    Empty m1 <-> Empty m2.
  Proof.
    unfold nm_wf_pair_equal in *.
    split; i.
    - eapply key_set_empty2. rewrite <- WF. eapply key_set_empty1. auto.
    - eapply key_set_empty2. rewrite WF. eapply key_set_empty1. auto.
  Qed.
  Lemma nm_wf_pair_empty
        elt1 elt2 (m1: NatMap.t elt1) (m2: NatMap.t elt2)
        (WF: nm_wf_pair m1 m2)
    :
    Empty m1 <-> Empty m2.
  Proof. eapply nm_wf_pair_equal_empty. eapply nm_wf_pair_implies. auto. Qed.

  Lemma nm_wf_pair_equal_is_empty
        elt1 elt2 (m1: NatMap.t elt1) (m2: NatMap.t elt2)
        (WF: nm_wf_pair_equal m1 m2)
    :
    is_empty m1 = is_empty m2.
  Proof.
    hexploit nm_wf_pair_equal_empty; eauto. i; des.
    destruct (is_empty m1) eqn:EMP1.
    - destruct (is_empty m2) eqn:EMP2; auto.
      apply is_empty_2 in EMP1. apply H in EMP1. apply is_empty_1 in EMP1. clarify.
    - destruct (is_empty m2) eqn:EMP2; auto.
      apply is_empty_2 in EMP2. apply H0 in EMP2. apply is_empty_1 in EMP2. clarify.
  Qed.
  Lemma nm_wf_pair_is_empty
        elt1 elt2 (m1: NatMap.t elt1) (m2: NatMap.t elt2)
        (WF: nm_wf_pair m1 m2)
    :
    is_empty m1 = is_empty m2.
  Proof. eapply nm_wf_pair_equal_is_empty. eapply nm_wf_pair_implies. auto. Qed.


  Lemma nm_map_map_equal
        elt (m: t elt) elt1 (f: elt -> elt1) elt2 (g: elt1 -> elt2)
    :
    Equal (map g (map f m)) (map (fun e => (g (f e))) m).
  Proof.
    eapply F.Equal_mapsto_iff. i. split; i.
    - rewrite F.map_mapsto_iff in H. des; clarify.
      rewrite F.map_mapsto_iff in H0. des; clarify.
      eapply map_1 in H1. instantiate (1:= (fun e => g (f e))) in H1. ss.
    - rewrite F.map_mapsto_iff in H. des; clarify.
      do 2 eapply map_1. auto.
  Qed.
  Lemma nm_map_map_eq
        elt (m: t elt) elt1 (f: elt -> elt1) elt2 (g: elt1 -> elt2)
    :
    (map g (map f m)) = (map (fun e => (g (f e))) m).
  Proof. eapply nm_eq_is_equal, nm_map_map_equal. Qed.

  Lemma nm_map_unit1_map_equal
        elt (m: t elt) elt' (f: elt -> elt')
    :
    Equal (map unit1 (map f m)) (map unit1 m).
  Proof. rewrite nm_map_map_equal. ss. Qed.
  Lemma nm_map_unit1_map_eq
        elt (m: t elt) elt' (f: elt -> elt')
    :
    (map unit1 (map f m)) = (map unit1 m).
  Proof. eapply nm_eq_is_equal, nm_map_unit1_map_equal. Qed.

  Lemma nm_map_self_equal
        elt (m: t elt)
    :
    Equal (map (fun e => e) m) m.
  Proof.
    eapply F.Equal_mapsto_iff. i. split; i.
    - rewrite F.map_mapsto_iff in H. des; clarify.
    - rewrite F.map_mapsto_iff. eauto.
  Qed.
  Lemma nm_map_self_eq
        elt (m: t elt)
    :
    (map (fun e => e) m) = m.
  Proof. eapply nm_eq_is_equal, nm_map_self_equal. Qed.

  Lemma nm_wf_pair_add
        elt1 elt2 (m1: NatMap.t elt1) (m2: NatMap.t elt2)
        (WF: nm_wf_pair m1 m2)
        k e1 e2
    :
    nm_wf_pair (add k e1 m1) (add k e2 m2).
  Proof.
    unfold nm_wf_pair in *. rewrite !key_set_pull_add_eq. rewrite WF. auto.
  Qed.


  Lemma nm_wf_pair_rm
        elt1 elt2 (m1: NatMap.t elt1) (m2: NatMap.t elt2)
        (WF: nm_wf_pair m1 m2)
        k
    :
    nm_wf_pair (remove k m1) (remove k m2).
  Proof.
    unfold nm_wf_pair in *. rewrite !key_set_pull_rm_eq. rewrite WF. auto.
  Qed.

  Lemma nm_rm_add_mapsto_equal
        elt (m: NatMap.t elt)
        k e
        (MT: MapsTo k e m)
    :
    Equal m (add k e (remove k m)).
  Proof.
    eapply F.Equal_mapsto_iff. i. split; i.
    - destruct (F.eq_dec k0 k); clarify.
      + pose (F.MapsTo_fun MT H). rewrite e1. apply add_1; auto.
      + apply add_2; auto. apply remove_2; auto.
    - apply F.add_mapsto_iff in H. des; clarify. apply F.remove_mapsto_iff in H0. des; auto.
  Qed.
  Lemma nm_rm_add_mapsto_eq
        elt (m: NatMap.t elt)
        k e
        (MT: MapsTo k e m)
    :
    m = (add k e (remove k m)).
  Proof. apply nm_eq_is_equal. apply nm_rm_add_mapsto_equal; auto. Qed.

  Lemma nm_wf_pair_rm_inv
        elt1 elt2 (m1: NatMap.t elt1) (m2: NatMap.t elt2)
        k
        (IN1: In k m1)
        (IN2: In k m2)
        (WF: nm_wf_pair (remove k m1) (remove k m2))
    :
    nm_wf_pair m1 m2.
  Proof.
    assert (MT1: MapsTo k tt (key_set m1)).
    { rewrite <- F.map_in_iff in IN1. instantiate (1:=unit1) in IN1. unfold In, Raw.PX.In in IN1. des. destruct e.
      unfold MapsTo. unfold key_set. eapply IN1.
    }
    assert (MT2: MapsTo k tt (key_set m2)).
    { rewrite <- F.map_in_iff in IN2. instantiate (1:=unit1) in IN2. unfold In, Raw.PX.In in IN2. des. destruct e.
      unfold MapsTo. unfold key_set. eapply IN2.
    }
    unfold nm_wf_pair. rewrite (nm_rm_add_mapsto_eq MT1). rewrite (nm_rm_add_mapsto_eq MT2).
    rewrite <- !key_set_pull_rm_eq. rewrite WF. auto.
  Qed.


  Lemma nm_empty_equal
        elt (m: NatMap.t elt)
        (EMP: Empty m)
    :
    Equal m (@empty elt).
  Proof.
    eapply F.Equal_mapsto_iff. i. split; i.
    - unfold Empty, MapsTo in *. unfold Raw.Empty in *. exfalso. eapply EMP; eauto.
    - exfalso. eapply F.empty_mapsto_iff in H. auto.
  Qed.
  Lemma nm_empty_eq
        elt (m: NatMap.t elt)
        (EMP: Empty m)
    :
    m = (@empty elt).
  Proof. eapply nm_eq_is_equal, nm_empty_equal; auto. Qed.

  Lemma nm_wf_pair_empty_empty_equal
        elt1 elt2
    :
    nm_wf_pair_equal (@empty elt1) (@empty elt2).
  Proof.
    eapply nm_empty_equal. eapply key_set_empty1. eapply empty_1.
  Qed.
  Lemma nm_wf_pair_empty_empty_eq
        elt1 elt2
    :
    nm_wf_pair (@empty elt1) (@empty elt2).
  Proof. eapply nm_eq_is_equal, nm_wf_pair_empty_empty_equal. Qed.

  Lemma nm_elements_cons_rm
        elt (m: NatMap.t elt)
        k e l
        (ELEM: (k, e) :: l = elements m)
    :
    l = elements (remove k m).
  Proof.
    destruct m. unfold elements in *. ss. unfold Raw.elements in *.
    destruct this0 as [| [k0 e0] l0]; ss.
    inv ELEM. Raw.MX.elim_comp_eq k0 k0. auto.
  Qed.

  Lemma nm_elements_cons_find_some
        elt (m: NatMap.t elt)
        k e l
        (ELEM: (k, e) :: l = elements m)
    :
    find k m = Some e.
  Proof.
    rewrite F.elements_o. rewrite <- ELEM. ss. unfold F.eqb. des_ifs.
  Qed.

  Lemma nm_find_some_rm_add_equal
        elt (m: NatMap.t elt)
        k e
        (FIND: find k m = Some e)
    :
    Equal m (add k e (remove k m)).
  Proof.
    eapply F.Equal_mapsto_iff. i. split; i.
    - apply find_2 in FIND. destruct (F.eq_dec k0 k); clarify.
      + pose F.MapsTo_fun. specialize (e1 _ _ _ _ _ FIND H). clarify. eapply add_1; auto.
      + eapply add_2; auto. eapply remove_2; auto.
    - apply find_2 in FIND. eapply F.add_mapsto_iff in H. des; clarify.
      eapply F.remove_mapsto_iff in H0. des; auto.
  Qed.
  Lemma nm_find_some_rm_add_eq
        elt (m: NatMap.t elt)
        k e
        (FIND: find k m = Some e)
    :
    m = (add k e (remove k m)).
  Proof. eapply nm_eq_is_equal, nm_find_some_rm_add_equal; eauto. Qed.

  Lemma nm_forall2_wf_pair_equal
        elt1 elt2 (m1: NatMap.t elt1) (m2: NatMap.t elt2)
        (FA: List.Forall2 (fun '(k1, e1) '(k2, e2) => k1 = k2) (elements m1) (elements m2))
    :
    nm_wf_pair_equal m1 m2.
  Proof.
    match goal with
    | FA: Forall2 _ ?_ml1 ?_ml2 |- _ => remember _ml1 as ml1; remember _ml2 as ml2
    end.
    move FA before elt2. revert_until FA. induction FA; i.
    { symmetry in Heqml1; apply elements_Empty in Heqml1.
      symmetry in Heqml2; apply elements_Empty in Heqml2.
      rewrite nm_empty_eq; auto. rewrite nm_empty_eq at 1; auto.
      apply nm_wf_pair_empty_empty_equal.
    }
    des_ifs.
    unfold nm_wf_pair_equal in *. dup Heqml1. dup Heqml2.
    eapply nm_elements_cons_rm in Heqml1, Heqml2.
    eapply nm_elements_cons_find_some in Heqml0, Heqml3.
    eapply nm_find_some_rm_add_eq in Heqml0, Heqml3.
    hexploit IHFA; clear IHFA; eauto. i.
    rewrite Heqml0, Heqml3. rewrite !key_set_pull_add_equal. rewrite H. reflexivity.
  Qed.
  Lemma nm_forall2_wf_pair
        elt1 elt2 (m1: NatMap.t elt1) (m2: NatMap.t elt2)
        (FA: List.Forall2 (fun '(k1, e1) '(k2, e2) => k1 = k2) (elements m1) (elements m2))
    :
    nm_wf_pair m1 m2.
  Proof. eapply nm_eq_is_equal. eapply nm_forall2_wf_pair_equal; auto. Qed.

  Lemma nm_forall2_implies_find_some
        elt1 elt2 (m1: NatMap.t elt1) (m2: NatMap.t elt2)
        P
        (FA: List.Forall2 (fun '(k1, e1) '(k2, e2) => (k1 = k2) /\ (P e1 e2 k1)) (elements m1) (elements m2))
    :
    forall k e1 e2 (FIND1: find k m1 = Some e1) (FIND2: find k m2 = Some e2),
      P e1 e2 k.
  Proof.
    match goal with
    | FA: Forall2 _ ?_ml1 ?_ml2 |- _ => remember _ml1 as ml1; remember _ml2 as ml2
    end.
    move FA before elt2. revert_until FA. induction FA; i.
    { symmetry in Heqml1; apply elements_Empty in Heqml1.
      symmetry in Heqml2; apply elements_Empty in Heqml2.
      apply nm_empty_eq in Heqml1, Heqml2. subst. rewrite F.empty_o in FIND1; ss.
    }
    des_ifs. des; clarify. destruct (F.eq_dec k k1); clarify.
    { eapply nm_elements_cons_find_some in Heqml1, Heqml2. clarify. }
    hexploit nm_elements_cons_rm. eapply Heqml1. intro RM1.
    hexploit nm_elements_cons_rm. eapply Heqml2. intro RM2.
    eapply IHFA; eauto. rewrite nm_find_rm_neq; auto. rewrite nm_find_rm_neq; auto.
  Qed.


  Lemma key_set_empty_empty_equal
        elt
    :
    Equal (key_set (@empty elt)) (@empty unit).
  Proof.
    eapply nm_empty_equal. eapply key_set_empty1. apply empty_1.
  Qed.
  Lemma key_set_empty_empty_eq
        elt
    :
    (key_set (@empty elt)) = (@empty unit).
  Proof. eapply nm_eq_is_equal. eapply key_set_empty_empty_equal. Qed.


  Lemma elements_inj_equal
        elt (m1 m2: t elt)
        (EQ: elements m1 = elements m2)
    :
    Equal m1 m2.
  Proof.
    eapply F.Equal_mapsto_iff. i. split; i.
    - eapply elements_2. rewrite <- EQ. apply elements_1. auto.
    - eapply elements_2. rewrite EQ. apply elements_1. auto.
  Qed.
  Lemma elements_inj_eq
        elt (m1 m2: t elt)
        (EQ: elements m1 = elements m2)
    :
    m1 = m2.
  Proof. eapply nm_eq_is_equal. apply elements_inj_equal; auto. Qed.


  Lemma list_map_elements_nm_map
        elt (m: t elt) elt1 (f: elt -> elt1)
    :
    List.map (fun '(k, e) => (k, f e)) (elements m) = elements (map f m).
  Proof.
    ss. unfold elements. unfold Raw.elements. destruct m. ss. clear sorted0.
    rename this0 into l. induction l; ss. des_ifs. f_equal; auto.
  Qed.

  Lemma nm_wf_pair_elements_forall2
        elt1 elt2 (m1: t elt1) (m2: t elt2)
        (WFP: nm_wf_pair m1 m2)
    :
    Forall2 (fun '(k1, e1) '(k2, e2) => k1 = k2) (elements m1) (elements m2).
  Proof.
    cut (Forall2 (fun '(k1, e1) '(k2, e2) => k1 = k2) (elements (key_set m1)) (elements (key_set m2))).
    { intro FA. clear WFP. unfold key_set in FA. rewrite <- !list_map_elements_nm_map in FA.
      remember (elements m1) as l1. remember (elements m2) as l2.
      clear m1 Heql1 m2 Heql2.
      match goal with
      | FA: Forall2 _ ?_l1 ?_l2 |- _ => remember _l1 as kl1; remember _l2 as kl2
      end.
      move FA before elt2. revert_until FA. induction FA; i.
      { symmetry in Heqkl1, Heqkl2. apply map_eq_nil in Heqkl1, Heqkl2. subst. econs. }
      destruct x, y. clarify. rename k0 into k. destruct u, u0.
      symmetry in Heqkl1, Heqkl2. apply map_eq_cons in Heqkl1, Heqkl2. des.
      des_ifs. econs; auto.
    }
    rewrite WFP. remember (elements (key_set m2)) as l. clear m1 m2 WFP Heql.
    induction l; ss. econs; auto. des_ifs.
  Qed.

  Lemma nm_wf_pair_tfind_elements_eq
        elt1 elt2 (m1: t elt1) (m2: t elt2)
        (WFP: nm_wf_pair m1 m2)
    :
    forall d, List.map (fun '(k, _) => (k, tfind d k m2)) (elements m1) = elements m2.
  Proof.
    hexploit nm_wf_pair_elements_forall2. eauto. intro FA. i.
    match goal with
    | |- List.map ?_f _ = _ => assert (EQF: _f = (fun '(k, _) => (k, tfind_l d k (elements m2))))
    end.
    { extensionalities x. des_ifs. rewrite tfind_to_tfind_l. auto. }
    rewrite EQF; clear EQF. clear WFP.
    hexploit (elements_3w m1). intro ND1. hexploit (elements_3w m2). intro ND2.
    remember (elements m1) as l1; remember (elements m2) as l2.
    clear m1 m2 Heql1 Heql2.
    revert_until FA. induction FA; i; ss. des_ifs. f_equal.
    { f_equal. unfold tfind_l. ss. unfold F.eqb. unfold F.eq_dec. des_ifs. }
    hexploit (IHFA d); clear IHFA.
    { inv ND1. auto. }
    { inv ND2. auto. }
    intro LM. symmetry. rewrite <- LM at 1.
    clear LM ND2 FA.
    revert_until l. induction l; i; ss. des_ifs. f_equal.
    { f_equal. inv ND1. destruct (F.eqb k0 k) eqn:EQ.
      { unfold F.eqb in EQ. des_ifs. exfalso. apply H1. econs. ss. }
      unfold tfind_l. ss. unfold F.eqb in *. des_ifs.
    }
    inv ND1. inv H2.
    eapply IHl. econs. instantiate (1:=e).
    { ii. apply H1. econs 2. auto. }
    auto.
  Qed.

  Lemma nm_wf_pair_tfind_elements_cons_eq
        elt1 elt2 (m1: t elt1) (m2: t elt2)
        (WFP: nm_wf_pair m1 m2)
        k e1
    :
    forall d, List.map (fun '(k, _) => (k, tfind d k m2)) ((k, e1) :: elements m1) =
           (k, tfind d k m2) :: elements m2.
  Proof.
    i. ss. rewrite nm_wf_pair_tfind_elements_eq; auto.
  Qed.

  Lemma tfind_l_remove_not_in
        elt1 (l: list (key * elt1)%type) elt2 (m: t elt2)
        k
        (NOTIN: ~ Raw.PX.In k l)
        e
    :
    List.map (fun '(k0, _) => (k0, tfind_l e k0 (elements (remove k m)))) l =
      List.map (fun '(k0, _) => (k0, tfind_l e k0 (elements m))) l.
  Proof.
    revert_until l. induction l; i. ss. Local Opaque remove. ss. Local Transparent remove.
    des_ifs. hexploit IHl; clear IHl.
    { instantiate (1:=k). ii. apply NOTIN. apply Raw.PX.In_alt in H. apply Raw.PX.In_alt. des.
      destruct (F.eqb k k0) eqn:EQ; clarify.
      - unfold F.eqb in EQ. des_ifs. eexists. econs. unfold Raw.PX.eqk. eauto.
      - eexists. econs 2. eauto.
    }
    i. f_equal.
    { f_equal. rewrite <- !tfind_to_tfind_l. unfold tfind. rewrite nm_find_rm_neq; auto. ii.
      apply NOTIN. clarify. econs. econs. econs; eauto.
    }
    eauto.
  Qed.

  Lemma key_set_idempotent
        elt (m: t elt)
    :
    (key_set (key_set m)) = key_set m.
  Proof.
    unfold key_set. rewrite nm_map_map_eq. f_equal.
  Qed.

  Lemma nm_wf_pair_key_set
        elt (m: t elt)
    :
    nm_wf_pair (key_set m) m.
  Proof.
    unfold nm_wf_pair. rewrite key_set_idempotent. auto.
  Qed.

  Lemma key_set_elements_cons_rm
        elt (m: NatMap.t elt)
        k e
        (REF: (k, tt) :: (elements (remove k (key_set m))) = elements (key_set m))
        (FIND: find k m = Some e)
    :
    (k, e) :: (elements (remove k m)) = elements m.
  Proof.
    assert (EQ: List.map (fun '(k0, _) => (k0, tfind e k0 (remove k m))) ((k, tt) :: elements (remove k (key_set m))) = List.map (fun '(k0, _) => (k0, tfind e k0 m)) (elements (key_set m))).
    { rewrite <- REF. ss. f_equal. f_equal. unfold tfind. rewrite nm_find_rm_eq. rewrite FIND. auto.
      match goal with
      | |- List.map ?_f _ = _ => assert (EQF: _f = (fun '(k0, _) => (k0, tfind_l e k0 (elements (remove k m)))))
      end.
      { extensionalities x. des_ifs. rewrite tfind_to_tfind_l. auto. }
      rewrite EQF; clear EQF.
      match goal with
      | |- _ = List.map ?_f _ => assert (EQF: _f = (fun '(k0, _) => (k0, tfind_l e k0 (elements m))))
      end.
      { extensionalities x. des_ifs. rewrite tfind_to_tfind_l. auto. }
      rewrite EQF; clear EQF.
      eapply tfind_l_remove_not_in. apply Raw.remove_1; auto. apply Raw.map_sorted. apply sorted.
    }
    clear REF.
    rewrite nm_wf_pair_tfind_elements_cons_eq in EQ.
    2:{ apply nm_wf_pair_rm. apply nm_wf_pair_key_set. }
    rewrite nm_wf_pair_tfind_elements_eq in EQ.
    2:{ apply nm_wf_pair_key_set. }
    rewrite <- EQ. f_equal. f_equal. unfold tfind. rewrite nm_find_rm_eq. auto.
  Qed.

  Lemma elements_key_set_cons_rm
        elt (m: NatMap.t elt)
        k e
        (REF: (k, e) :: (elements (remove k m)) = elements m)
        (FIND: find k (key_set m) = Some tt)
    :
    (k, tt) :: (elements (remove k (key_set m))) = elements (key_set m).
  Proof.
    assert (EQ: List.map (fun '(k0, _) => (k0, tfind tt k0 (remove k (key_set m)))) ((k, e) :: elements (remove k m)) = List.map (fun '(k0, _) => (k0, tfind tt k0 (key_set m))) (elements m)).
    { rewrite <- REF. ss. f_equal. f_equal. unfold tfind. rewrite nm_find_rm_eq. rewrite FIND. auto.
      match goal with
      | |- List.map ?_f _ = _ => assert (EQF: _f = (fun '(k0, _) => (k0, tfind_l tt k0 (elements (remove k (key_set m))))))
      end.
      { extensionalities x. des_ifs. rewrite tfind_to_tfind_l. auto. }
      rewrite EQF; clear EQF.
      match goal with
      | |- _ = List.map ?_f _ => assert (EQF: _f = (fun '(k0, _) => (k0, tfind_l tt k0 (elements (key_set m)))))
      end.
      { extensionalities x. des_ifs. rewrite tfind_to_tfind_l. auto. }
      rewrite EQF; clear EQF.
      eapply tfind_l_remove_not_in. apply Raw.remove_1; auto. apply sorted.
    }
    clear REF.
    rewrite nm_wf_pair_tfind_elements_cons_eq in EQ.
    2:{ apply nm_wf_pair_rm. apply nm_wf_pair_sym. apply nm_wf_pair_key_set. }
    rewrite nm_wf_pair_tfind_elements_eq in EQ.
    2:{ apply nm_wf_pair_sym. apply nm_wf_pair_key_set. }
    rewrite <- EQ. f_equal. f_equal. unfold tfind. rewrite nm_find_rm_eq. auto.
  Qed.

  Lemma wf_pair_elements_cons_rm
        elt1 elt2 (m1: NatMap.t elt1) (m2: NatMap.t elt2)
        k e1 e2
        (WFP: nm_wf_pair m1 m2)
        (REF: (k, e1) :: (elements (remove k m1)) = elements m1)
        (FIND: find k m2 = Some e2)
    :
    (k, e2) :: (elements (remove k m2)) = elements m2.
  Proof.
    eapply key_set_elements_cons_rm; auto. rewrite <- WFP. eapply elements_key_set_cons_rm; eauto.
    rewrite WFP. unfold key_set. rewrite F.map_o. rewrite FIND. ss.
  Qed.


  Lemma nm_find_some_implies_forall2
        elt1 elt2 (m1: NatMap.t elt1) (m2: NatMap.t elt2)
        (P: elt1 -> elt2 -> key -> Prop)
        (WFP: nm_wf_pair m1 m2)
        (PROP: forall k e1 e2 (FIND1: find k m1 = Some e1) (FIND2: find k m2 = Some e2), P e1 e2 k)
    :
    List.Forall2 (fun '(k1, e1) '(k2, e2) => (k1 = k2) /\ (P e1 e2 k1)) (elements m1) (elements m2).
  Proof.
    remember (elements m1) as l1. move l1 before elt2. revert_until l1. induction l1; i; ss.
    { symmetry in Heql1. apply elements_Empty in Heql1. hexploit nm_wf_pair_empty; eauto. i. apply H in Heql1.
      apply nm_empty_eq in Heql1. subst. rewrite elements_empty. ss. }
    destruct a as [k e1]. hexploit nm_elements_cons_rm. eauto. intros ELEM1. rewrite ELEM1 in Heql1.
    destruct (elements m2) eqn:Heql2.
    { apply elements_Empty in Heql2. hexploit nm_wf_pair_empty; eauto. i. apply H in Heql2.
      apply nm_empty_eq in Heql2. subst. rewrite elements_empty in Heql1. inv Heql1. }
    destruct p as [k0 e2]. rename l into l2. symmetry in Heql2.
    hexploit nm_elements_cons_rm. eapply Heql2. intro ELEM2. rewrite ELEM2 in Heql2.
    assert (k = k0).
    { hexploit nm_wf_pair_elements_forall2. eauto. rewrite <- Heql1, <- Heql2. i. inv H. auto. }
    replace k0 with k in *. clear H. econs.
    2:{ rewrite ELEM2. eapply IHl1; eauto. apply nm_wf_pair_rm; auto.
        i. eapply PROP. rewrite F.remove_o in FIND1. des_ifs. rewrite F.remove_o in FIND2. des_ifs.
    }
    split; auto. eapply PROP. eapply nm_elements_cons_find_some; eauto. eapply nm_elements_cons_find_some; eauto.
  Qed.

End AUX.


From Fairness Require Import WFLib.
Section NMWF.

  Import NatMap.
  Import NatMapP.

  Variant nm_lt A (R: A -> A -> Prop): NatMap.t A -> NatMap.t A -> Prop :=
    | nm_lt_intro
        nm0 nm1 k e0 e1
        (FIND1: find k nm0 = Some e0)
        (FIND2: find k nm1 = Some e1)
        (LT: R e0 e1)
        (EQ: forall k0 (NEQ: k <> k0), find k0 nm0 = find k0 nm1)
      :
      nm_lt R nm0 nm1.

  Lemma cardinal_remove A k (m: NatMap.t A)
        (IN: NatMap.In k m)
    :
    S (cardinal (remove k m)) = cardinal m.
  Proof.
    eapply F.in_find_iff in IN.
    destruct (find k m) eqn:EQ; ss.
    symmetry. eapply cardinal_2.
    { eapply remove_1; eauto. }
    instantiate (1:=a). unfold Add.
    i. rewrite F.add_o. rewrite F.remove_o. des_ifs.
  Qed.

  Lemma nm_lt_same_cardinal A (R: A -> A -> Prop) m0 m1
        (LT: nm_lt R m0 m1)
    :
    cardinal m0 = cardinal m1.
  Proof.
    inv LT.
    transitivity (S (cardinal (remove k m0))).
    { symmetry. eapply cardinal_remove.
      eapply F.in_find_iff. rewrite FIND1. ss. }
    { transitivity (S (cardinal (remove k m1))).
      { f_equal. eapply Equal_cardinal. ii.
        rewrite F.remove_o. rewrite F.remove_o.
        des_ifs. eauto.
      }
      eapply cardinal_remove.
      eapply F.in_find_iff. rewrite FIND2. ss. }
  Qed.

  Lemma nm_lt_inv A (R: A -> A-> Prop)
        m k a
        (FIND: NatMap.find k m = Some a)
    :
    forall m' (LT: nm_lt R m' m),
      (exists a',
          (<<FIND: NatMap.find k m' = Some a'>>) /\
            (<<REMOVE: NatMap.remove k m = NatMap.remove k m'>>) /\
            (<<REL: R a' a>>)) \/
        ((<<FIND: NatMap.find k m' = Some a>>) /\
           (<<REL: nm_lt R (NatMap.remove k m') (NatMap.remove k m)>>)).
  Proof.
    i. inv LT.
    destruct (PeanoNat.Nat.eq_dec k k0).
    { clarify. left. esplits; eauto.
      eapply nm_eq_is_equal. ii.
      rewrite F.remove_o. rewrite F.remove_o.
      des_ifs. symmetry. eapply EQ; eauto.
    }
    { subst. right. splits; auto.
      { rewrite EQ; eauto. }
      { econs.
        { rewrite nm_find_rm_neq; eauto. }
        { rewrite nm_find_rm_neq; eauto. }
        { eauto. }
        { i. rewrite F.remove_o. rewrite F.remove_o.
          des_ifs. eapply EQ; eauto.
        }
      }
    }
  Qed.

  Lemma nm_lt_well_founded A (R: A -> A -> Prop)
        (WF: well_founded R)
    :
    well_founded (nm_lt R).
  Proof.
    cut (forall n m (CARDINAL: cardinal m = n), Acc (nm_lt R) m).
    { ii. eapply H; eauto. }
    induction n.
    { ii. econs. i. inv H.
      eapply cardinal_inv_1 in CARDINAL.
      eapply nm_empty_equal in CARDINAL.
      rewrite CARDINAL in FIND2. rewrite F.empty_o in FIND2. ss.
    }
    i.
    assert (FIND: exists k a, NatMap.find k m = Some a).
    { destruct (cardinal_inv_2 CARDINAL) as [[k a] p]. ss.
      exists k, a. eapply find_1. eauto.
    }
    des. revert m CARDINAL FIND.
    pattern a. revert a.
    eapply (well_founded_induction WF). intros a IHL.
    i. hexploit (IHn (NatMap.remove k m)).
    { erewrite <- cardinal_remove in CARDINAL; eauto.
      eapply F.in_find_iff. ii. clarify.
    }
    intros ACC. remember (NatMap.remove k m) as m0 eqn:REMOVE.
    revert m REMOVE CARDINAL FIND.
    pattern m0. revert m0 ACC.
    eapply Acc_ind. intros m0 _ IHR.
    i. subst. econs. i.
    hexploit nm_lt_inv; eauto. i. des.
    { eapply IHL; eauto. eapply nm_lt_same_cardinal in H. rewrite H. auto. }
    { eapply IHR; eauto. eapply nm_lt_same_cardinal in H. rewrite H. auto. }
  Qed.
End NMWF.
