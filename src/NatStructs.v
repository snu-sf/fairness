From sflib Require Import sflib.

From Coq Require Import
  Permutation
  SetoidList
  SetoidPermutation
  Lists.List
  Lia.

Require Import Coq.FSets.FSets Coq.FSets.FMaps Coq.Structures.OrderedTypeEx.
Module NatSet := FSetList.Make(Nat_as_OT).
Module NatMap := FMapList.Make(Nat_as_OT).

Set Implicit Arguments.

Section NATSET.

  Lemma ns_in_dec: forall n s, {NatSet.In n s} + {~ NatSet.In n s}.
  Proof.
    i. eapply InA_dec. eapply NatSet.MSet.E.eq_dec.
  Qed.

  Definition set_pop : NatSet.elt -> NatSet.t -> option NatSet.t :=
    fun x s => if NatSet.mem x s
            then Some (NatSet.remove x s)
            else None.

  Lemma Empty_nil s : NatSet.Empty s -> NatSet.elements s = [].
  Proof.
    i. destruct s as [s OK]; ss. destruct s; ss.
    exfalso. eapply H. econs. ss.
  Qed.

  Lemma Empty_nil_neg s : ~ NatSet.Empty s -> NatSet.elements s <> [].
  Proof.
    destruct s as [s SORTED]; ss.
    ii. subst. eapply H. ii. eapply InA_nil; eauto.
  Qed.

  Lemma NatSet_Permutation_remove x s l :
    Permutation (NatSet.elements s) (x :: l) -> Permutation (NatSet.elements (NatSet.remove x s)) l.
  Proof.
    destruct s as [s SORTED]. ss.
    revert l. induction s; i.
    - eapply Permutation_length in H. ss.
    - assert (List.In a (x :: l)) by (rewrite <- H; econs; ss).
      destruct H0.
      + subst. eapply Permutation_cons_inv in H. ss. rewrite NatSet.MSet.Raw.MX.compare_refl. auto.
      + eapply Add_inv in H0. des. eapply Permutation_Add in H0.
        rewrite <- H0 in *. clear l H0.
        rewrite perm_swap in H. eapply Permutation_cons_inv in H.
        assert (List.In x s).
        { eapply Permutation_in.
          - symmetry. eapply H.
          - econs; ss.
        }
        eapply NatSet.MSet.Raw.isok_iff in SORTED.
        epose proof (Sorted_extends _ SORTED).
        eapply Forall_forall in H1; eauto.
        ss. pose (NatSet.MSet.Raw.MX.compare_gt_iff x a) as GT. ss. des. rewrite (GT0 H1).
        econs. eapply IHs; eauto.
        eapply NatSet.MSet.Raw.isok_iff.
        inv SORTED; ss.
        Unshelve. compute. lia.
  Qed.

  Lemma NatSet_Permutation_add x s l :
    ~ NatSet.In x s -> Permutation (NatSet.elements s) l -> Permutation (NatSet.elements (NatSet.add x s)) (x :: l).
  Proof.
    destruct s as [s SORTED]. ss. revert l. induction s; intros l H1 H2.
    - rewrite <- H2. ss.
    - ss. assert (x = a \/ x < a \/ x > a) by lia. des.
      + exfalso. eapply H1. econs. ss.
      + pose (NatSet.MSet.Raw.MX.compare_lt_iff x a). ss. des. rewrite (i0 H). econs. ss.
      + pose (NatSet.MSet.Raw.MX.compare_gt_iff x a). ss. des. rewrite (i0 H).
        rewrite <- H2. rewrite perm_swap. econs.
        eapply IHs; eauto.
        unfold NatSet.In, NatSet.MSet.In in *. ss.
        intro. eapply H1. econs 2. eapply H0.
        Unshelve. clear H1. eapply NatSet.MSet.Raw.isok_iff in SORTED. inv SORTED.
        eapply NatSet.MSet.Raw.isok_iff. ss.
  Qed.

End NATSET.



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



  Import NatMap.

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

End NATMAP.



Section AUX.

  Definition key_set {elt} : NatMap.t elt -> NatSet.t.
  Proof.
    Import NatMap.
    intros [l SORTED]. unfold Raw.t in *.
    set (l' := List.map fst l).
    econs. instantiate (1 := l').
    unfold Raw.PX.ltk in *.

    assert (Sorted (fun x y => x < y) l').
    { induction SORTED.
      - subst l'. ss.
      - subst l'. ss. econs 2; ss.
        inv H; ss. econs; ss.
    }

    eapply NatSet.MSet.Raw.isok_iff. ss.
  Defined.

End AUX.
