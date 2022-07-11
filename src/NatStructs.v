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



  Import FMapFacts.
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



  Import NatMapP.
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

  Lemma eqlistA_eq_key_elt_eq
        (this0 this1 : Raw.t elt)
        (EQLA: eqlistA (eq_key_elt (elt:=elt)) this0 this1)
    :
    this0 = this1.
  Proof.
    induction EQLA; ss.
    destruct x, x'. unfold eq_key_elt, Raw.PX.eqke in *. des; ss; clarify.
  Qed.

  Lemma nm_equal_is_eq
        (m1 m2: t elt)
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
    rewrite (proof_irrelevance _ sorted0 sorted1). auto.
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
  Proof. eapply nm_equal_is_eq. eapply nm_add_add_equal. Qed.

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
  Proof. eapply nm_equal_is_eq. eapply nm_rm_add_equal. Qed.

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
  Proof. eapply nm_equal_is_eq, nm_find_none_rm_add_equal; auto. Qed.

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
  Proof. eapply nm_equal_is_eq, nm_find_none_rm_equal; auto. Qed.

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
  Proof. eapply nm_equal_is_eq, nm_rm_add_rm_equal; auto. Qed.




End NATMAP.



Module NatSet.
  Definition t := NatMap.t unit.
  Definition add x m := @NatMap.add unit x tt m.
  Definition remove := @NatMap.remove unit.
End NatSet.

(* Section NATSET. *)

  (* Lemma ns_in_dec: forall n s, {NatSet.In n s} + {~ NatSet.In n s}. *)
  (* Proof. *)
  (*   i. eapply InA_dec. eapply NatSet.MSet.E.eq_dec. *)
  (* Qed. *)

  (* Definition set_pop : NatSet.elt -> NatSet.t -> option NatSet.t := *)
  (*   fun x s => if NatSet.mem x s *)
  (*           then Some (NatSet.remove x s) *)
  (*           else None. *)

  (* Lemma Empty_nil s : NatSet.Empty s -> NatSet.elements s = []. *)
  (* Proof. *)
  (*   i. destruct s as [s OK]; ss. destruct s; ss. *)
  (*   exfalso. eapply H. econs. ss. *)
  (* Qed. *)

  (* Lemma Empty_nil_neg s : ~ NatSet.Empty s -> NatSet.elements s <> []. *)
  (* Proof. *)
  (*   destruct s as [s SORTED]; ss. *)
  (*   ii. subst. eapply H. ii. eapply InA_nil; eauto. *)
  (* Qed. *)

  (* Lemma NatSet_Permutation_remove x s l : *)
  (*   Permutation (NatSet.elements s) (x :: l) -> Permutation (NatSet.elements (NatSet.remove x s)) l. *)
  (* Proof. *)
  (*   destruct s as [s SORTED]. ss. *)
  (*   revert l. induction s; i. *)
  (*   - eapply Permutation_length in H. ss. *)
  (*   - assert (List.In a (x :: l)) by (rewrite <- H; econs; ss). *)
  (*     destruct H0. *)
  (*     + subst. eapply Permutation_cons_inv in H. ss. rewrite NatSet.MSet.Raw.MX.compare_refl. auto. *)
  (*     + eapply Add_inv in H0. des. eapply Permutation_Add in H0. *)
  (*       rewrite <- H0 in *. clear l H0. *)
  (*       rewrite perm_swap in H. eapply Permutation_cons_inv in H. *)
  (*       assert (List.In x s). *)
  (*       { eapply Permutation_in. *)
  (*         - symmetry. eapply H. *)
  (*         - econs; ss. *)
  (*       } *)
  (*       eapply NatSet.MSet.Raw.isok_iff in SORTED. *)
  (*       epose proof (Sorted_extends _ SORTED). *)
  (*       eapply Forall_forall in H1; eauto. *)
  (*       ss. pose (NatSet.MSet.Raw.MX.compare_gt_iff x a) as GT. ss. des. rewrite (GT0 H1). *)
  (*       econs. eapply IHs; eauto. *)
  (*       eapply NatSet.MSet.Raw.isok_iff. *)
  (*       inv SORTED; ss. *)
  (*       Unshelve. compute. lia. *)
  (* Qed. *)

  (* Lemma NatSet_Permutation_add x s l : *)
  (*   ~ NatSet.In x s -> Permutation (NatSet.elements s) l -> Permutation (NatSet.elements (NatSet.add x s)) (x :: l). *)
  (* Proof. *)
  (*   destruct s as [s SORTED]. ss. revert l. induction s; intros l H1 H2. *)
  (*   - rewrite <- H2. ss. *)
  (*   - ss. assert (x = a \/ x < a \/ x > a) by lia. des. *)
  (*     + exfalso. eapply H1. econs. ss. *)
  (*     + pose (NatSet.MSet.Raw.MX.compare_lt_iff x a). ss. des. rewrite (i0 H). econs. ss. *)
  (*     + pose (NatSet.MSet.Raw.MX.compare_gt_iff x a). ss. des. rewrite (i0 H). *)
  (*       rewrite <- H2. rewrite perm_swap. econs. *)
  (*       eapply IHs; eauto. *)
  (*       unfold NatSet.In, NatSet.MSet.In in *. ss. *)
  (*       intro. eapply H1. econs 2. eapply H0. *)
  (*       Unshelve. clear H1. eapply NatSet.MSet.Raw.isok_iff in SORTED. inv SORTED. *)
  (*       eapply NatSet.MSet.Raw.isok_iff. ss. *)
  (* Qed. *)

(* End NATSET. *)



Section AUX.

  Definition unit1 {E} : E -> unit := fun _ => tt.
  Definition key_set {elt} : NatMap.t elt -> NatSet.t :=
    fun m => NatMap.map unit1 m.

  Definition nm_wf_pair {elt1 elt2} (m1: NatMap.t elt1) (m2: NatMap.t elt2) := key_set m1 = key_set m2.

  Import NatMap.
  Import NatMapP.

  (* Definition key_set {elt} : NatMap.t elt -> NatSet.t. *)
  (* Proof. *)
  (*   intros [l SORTED]. unfold Raw.t in *. *)
  (*   set (l' := List.map fst l). *)
  (*   econs. instantiate (1 := l'). *)
  (*   unfold Raw.PX.ltk in *. *)
  (*   assert (Sorted (fun x y => x < y) l'). *)
  (*   { induction SORTED. *)
  (*     - subst l'. ss. *)
  (*     - subst l'. ss. econs 2; ss. *)
  (*       inv H; ss. econs; ss. *)
  (*   } *)
  (*   eapply NatSet.MSet.Raw.isok_iff. ss. *)
  (* Defined. *)

  Lemma key_set_pull_add_equal
        elt (m: NatMap.t elt) e k
    :
    Equal (key_set (add k e m)) (add k tt (key_set m)).
  Proof.
    unfold key_set. eapply F.Equal_mapsto_iff. i. split; i.
    - eapply F.map_mapsto_iff in H. des. clarify. eapply F.add_mapsto_iff in H0. des; clarify.
      + eapply add_1; auto.
      + eapply add_2; eauto. eapply map_1 in H1. eapply H1.
    - eapply F.add_mapsto_iff in H. des; clarify.
      + eapply (map_1 (m:=add k0 e m) (e:=e) (x:=k0) unit1). eapply add_1; auto.
      + eapply F.map_mapsto_iff in H0. des; clarify. eapply map_1. eapply add_2; auto.
  Qed.
  Lemma key_set_pull_add_eq
        elt (m: NatMap.t elt) e k
    :
    (key_set (add k e m)) = (add k tt (key_set m)).
  Proof. eapply nm_equal_is_eq. eapply key_set_pull_add_equal. Qed.


  Lemma th_wf_pair_pop_cases
        R0 R1
        (ths_src: threads_src2 R0)
        (ths_tgt: threads_tgt R1)
        (WF: th_wf_pair ths_src ths_tgt)
    :
    forall x, ((nm_pop x ths_src = None) /\ (nm_pop x ths_tgt = None)) \/
           (exists th_src th_tgt ths_src0 ths_tgt0,
               (nm_pop x ths_src = Some (th_src, ths_src0)) /\
                 (nm_pop x ths_tgt = Some (th_tgt, ths_tgt0)) /\
                 (th_wf_pair ths_src0 ths_tgt0)).
  Proof.

  Admitted.

End AUX.
