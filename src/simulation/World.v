From sflib Require Import sflib.
Require Import Coq.Classes.RelationClasses.
From iris.algebra Require Import cmra updates.
From Fairness Require Import Axioms NatStructsLarge.
From Fairness Require Import PCM.
From Fairness Require Import Mod.
Require Import String.

Set Implicit Arguments.


Section INVARIANT.
  Context `{M: ucmra}.

  Definition local_resources := NatMap.t (cmra_car M).

  Definition unwrap_opt_resource (r: option (cmra_car M)): (cmra_car M) :=
    match r with
    | Some r => r
    | None => ε
    end.

  Definition sum_of_resources (rs: local_resources): (cmra_car M) :=
    NatMap.fold (fun _ r s => r ⋅ s) rs ε.

  (* TODO: place somewhere else. Bikesheed namess  *)
  Local Instance fold_left_proper `{Equiv A} B (f : A → B → A) (l : list B) :
  Proper ((≡)==>(=)==>(≡)) f →
  Proper ((≡)==>(≡)) (fold_left f l).
  Proof.
    intros Hf x y EQ. revert x y EQ.
    induction l; i; ss.
    apply (IHl (f x a) (f y a)).
    apply Hf; done.
  Qed.

  Lemma permutation_same_sum l0 l1 r
        (PERM: Permutation.Permutation l0 l1)
    :
    List.fold_left (fun a (p : NatMap.key * M) => snd p ⋅ a) l0 r
    ≡ List.fold_left (fun a (p : NatMap.key * M) => snd p ⋅ a) l1 r.
  Proof.
    revert r. induction PERM; i; ss.
    { apply fold_left_proper; last first.
      { by rewrite !(assoc cmra.op) (comm cmra.op x.2). }
      intros a b Hab p1 p2 ->.
      rewrite Hab. done.
    }
    { rewrite IHPERM1. rewrite IHPERM2. auto. }
  Qed.

  Lemma resources_fold_left_base r l
    :
    List.fold_left (fun a (p : NatMap.key * M) => snd p ⋅ a) l r
    ≡
    List.fold_left (fun a (p : NatMap.key * M) => snd p ⋅ a) l ε ⋅ r.
  Proof.
    revert r. induction l; i; ss.
    { rewrite left_id. auto. }
    { rewrite (IHl (snd a ⋅ r)). rewrite (IHl (snd a ⋅ ε)). r_solve. }
  Qed.

  Lemma setoid_list_findA_in A B (f: A -> bool) l (b: B)
        (FIND: SetoidList.findA f l = Some b)
    :
    exists a, List.In (a, b) l /\ f a.
  Proof.
    revert b FIND. induction l; ss; i. des_ifs.
    { eauto. }
    { hexploit IHl; eauto. i. des. esplits; eauto. }
  Qed.

  Lemma sum_of_resources_remove rs tid r
        (FIND: NatMap.find tid rs = Some r)
    :
    sum_of_resources rs ≡ (sum_of_resources (NatMap.remove tid rs)) ⋅ r.
  Proof.
    unfold sum_of_resources. rewrite ! NatMap.fold_1.
    assert (exists l, Permutation.Permutation (NatMap.elements (elt:=M) rs) ((tid, r) :: l)).
    { rewrite NatMapP.F.elements_o in FIND.
      eapply setoid_list_findA_in in FIND. des.
      eapply List.in_split in FIND. des. rewrite FIND.
      unfold NatMapP.F.eqb in FIND0. des_ifs.
      exists (l1 ++ l2).
      rewrite Permutation.Permutation_app_comm. ss.
      eapply Permutation.perm_skip. eapply Permutation.Permutation_app_comm.
    }
    des. hexploit Permutation_remove; eauto.
    i. eapply permutation_same_sum in H.
    eapply permutation_same_sum in H0. rewrite H0. rewrite H.
    ss. rewrite resources_fold_left_base. r_solve.
  Qed.

  Lemma sum_of_resources_add rs tid r
        (FIND: NatMap.find tid rs = None)
    :
    sum_of_resources (NatMap.add tid r rs) ≡ (sum_of_resources rs) ⋅ r.
  Proof.
    unfold sum_of_resources. rewrite ! NatMap.fold_1.
    hexploit Permutation_add.
    { eapply NatMapP.F.not_find_in_iff. eauto. }
    { reflexivity. }
    i. eapply permutation_same_sum in H.
    rewrite H. ss. rewrite resources_fold_left_base. r_solve.
  Qed.

  Definition resources_wf (g: (cmra_car M)) (rs: local_resources): Prop :=
    ✓ (g ⋅ sum_of_resources rs)
  .

  Definition get_resource
             (tid: thread_id)
             (rs: local_resources)
    : ((cmra_car M) * local_resources) :=
    match nm_pop tid rs with
    | Some (r, rs) => (r, rs)
    | _ => (ε, rs)
    end.

  Lemma resources_wf_get_wf g0 tid rs0 r0 rs1
        (WF: resources_wf g0 rs0)
        (GET: get_resource tid rs0 = (r0, rs1))
    :
    (<<WF: ✓ (g0 ⋅ r0 ⋅ sum_of_resources rs1)>>) /\
      (<<UPDATE: forall g1 r1
                        (WF: ✓ (g1 ⋅ r1 ⋅ sum_of_resources rs1)),
          resources_wf g1 (NatMap.add tid r1 rs1)>>).
  Proof.
    unfold resources_wf, get_resource in *. des_ifs.
    { hexploit nm_pop_find_some; eauto. i.
      hexploit nm_pop_res_is_rm_eq; eauto. i.
      hexploit sum_of_resources_remove; eauto. i. subst.
      rewrite H1 in WF. split.
      { r. rewrite (comm cmra.op _ r0) (assoc cmra.op) in WF. done. }
      { ii. rewrite sum_of_resources_add.
        { rewrite (comm cmra.op _ r1) (assoc cmra.op). done. }
        { eapply nm_find_rm_eq. }
      }
    }
    { hexploit nm_pop_find_none; eauto. i. split.
      { r. rewrite right_id. done. }
      { ii. rewrite sum_of_resources_add; eauto. rewrite (comm cmra.op _ r1) (assoc cmra.op). done. }
    }
  Qed.
End INVARIANT.

Section AUX.

  Context `{M: ucmra}.

  Lemma get_resource_find_some
        (rs: (@local_resources M))
        tid
        r
        (SOME: NatMap.find tid rs = Some r)
    :
    ((@get_resource M) tid rs).1 = r ∧ ((@get_resource M) tid rs).2 = NatMap.remove tid rs.
  Proof.
    unfold get_resource, nm_pop. rewrite SOME. ss.
  Qed.

  Lemma get_resource_find_some_fst
        (rs: local_resources)
        tid
        r
        (SOME: NatMap.find tid rs = Some r)
    :
    fst (@get_resource M tid rs) = r.
  Proof. hexploit get_resource_find_some; eauto. i. des. ss. Qed.

  Lemma get_resource_find_some_snd
        (rs: local_resources)
        tid
        r
        (SOME: NatMap.find tid rs = Some r)
    :
    snd (@get_resource M tid rs) = NatMap.remove tid rs.
  Proof. hexploit get_resource_find_some; eauto. i. des. ss. Qed.

  Lemma get_resource_find_none
        (rs: local_resources)
        tid
        (NONE: NatMap.find tid rs = None)
    :
    @get_resource M tid rs = (ε,rs).
  Proof.
    unfold get_resource. unfold nm_pop. rewrite NONE. ss.
  Qed.

  Lemma get_resource_find_none_fst
        (rs: local_resources)
        tid
        (NONE: NatMap.find tid rs = None)
    :
    fst (@get_resource M tid rs) = ε.
  Proof. hexploit get_resource_find_none; eauto. intros ->. ss. Qed.

  Lemma get_resource_find_none_snd
        (rs: local_resources)
        tid
        (NONE: NatMap.find tid rs = None)
    :
    snd (@get_resource M tid rs) = rs.
  Proof. hexploit get_resource_find_none; eauto. intros ->. ss. Qed.

  Lemma get_resource_remove_eq
        (rs: local_resources)
        tid
    :
    @get_resource M tid (NatMap.remove tid rs) = (ε,NatMap.remove tid rs).
  Proof.
    unfold get_resource. unfold nm_pop. rewrite nm_find_rm_eq. ss.
  Qed.

  Lemma get_resource_remove_neq_fst
        (rs: local_resources)
        tid0 tid1
        (NEQ: tid0 <> tid1)
    :
    fst (@get_resource M tid1 (NatMap.remove tid0 rs)) = fst (@get_resource M tid1 rs).
  Proof.
    unfold get_resource. unfold nm_pop. rewrite nm_find_rm_neq; auto. des_ifs.
  Qed.

  Lemma get_resource_remove_neq_find_some
        (rs: local_resources)
        tid0 tid1 r
        (NEQ: tid0 <> tid1)
        (SOME: NatMap.find tid1 rs = Some r)
    :
    @get_resource M tid1 (NatMap.remove tid0 rs) = (r,NatMap.remove tid1 (NatMap.remove tid0 rs)).
  Proof.
    unfold get_resource. unfold nm_pop. rewrite nm_find_rm_neq; auto. rewrite SOME. ss.
  Qed.

  Lemma get_resource_remove_neq_find_none
        (rs: local_resources)
        tid0 tid1
        (NEQ: tid0 <> tid1)
        (NONE: NatMap.find tid1 rs = None)
    :
    @get_resource M tid1 (NatMap.remove tid0 rs) = (ε,NatMap.remove tid0 rs).
  Proof.
    unfold get_resource. unfold nm_pop. rewrite nm_find_rm_neq; auto. rewrite NONE. ss.
  Qed.

  Lemma get_resource_add_eq
        (rs: local_resources)
        tid r
    :
    @get_resource M tid (NatMap.add tid r rs) = (r,NatMap.remove tid rs).
  Proof.
    unfold get_resource. rewrite nm_pop_add_eq. ss.
  Qed.

  Lemma get_resource_add_neq_fst
        (rs: local_resources)
        tid0 tid1 r
        (NEQ: tid0 <> tid1)
    :
    fst (@get_resource M tid1 (NatMap.add tid0 r rs)) = fst (@get_resource M tid1 rs).
  Proof.
    unfold get_resource. unfold nm_pop. rewrite nm_find_add_neq; auto. des_ifs.
  Qed.

  Lemma get_resource_add_neq_find_some
        (rs: local_resources)
        tid0 tid1 r r0
        (NEQ: tid0 <> tid1)
        (SOME: NatMap.find tid1 rs = Some r0)
    :
    @get_resource M tid1 (NatMap.add tid0 r rs) = (r0,NatMap.remove tid1 (NatMap.add tid0 r rs)).
  Proof.
    unfold get_resource. unfold nm_pop. rewrite nm_find_add_neq; auto. rewrite SOME. ss.
  Qed.

  Lemma get_resource_add_neq_find_some_fst
        (rs: local_resources)
        tid0 tid1 r r0
        (NEQ: tid0 <> tid1)
        (SOME: NatMap.find tid1 rs = Some r0)
    :
    (@get_resource M tid1 (NatMap.add tid0 r rs)).1 = r0.
  Proof.
    unfold get_resource. unfold nm_pop. rewrite nm_find_add_neq; auto. rewrite SOME. ss.
  Qed.

  Lemma get_resource_add_neq_find_some_snd
        (rs: local_resources)
        tid0 tid1 r r0
        (NEQ: tid0 <> tid1)
        (SOME: NatMap.find tid1 rs = Some r0)
    :
    (@get_resource M tid1 (NatMap.add tid0 r rs)).2 = NatMap.remove tid1 (NatMap.add tid0 r rs).
  Proof.
    unfold get_resource. unfold nm_pop. rewrite nm_find_add_neq; auto. rewrite SOME. ss.
  Qed.

  Lemma get_resource_add_neq_find_none
        (rs: local_resources)
        tid0 tid1 r
        (NEQ: tid0 <> tid1)
        (NONE: NatMap.find tid1 rs = None)
    :
    @get_resource M tid1 (NatMap.add tid0 r rs) = (ε,NatMap.add tid0 r rs).
  Proof.
    unfold get_resource. unfold nm_pop. rewrite nm_find_add_neq; auto. rewrite NONE. ss.
  Qed.

  Lemma get_resource_add_neq_find_none_fst
        (rs: local_resources)
        tid0 tid1 r
        (NEQ: tid0 <> tid1)
        (NONE: NatMap.find tid1 rs = None)
    :
    (@get_resource M tid1 (NatMap.add tid0 r rs)).1 = ε.
  Proof.
    unfold get_resource. unfold nm_pop. rewrite nm_find_add_neq; auto. rewrite NONE. ss.
  Qed.

  Lemma get_resource_add_neq_find_none_snd
        (rs: local_resources)
        tid0 tid1 r
        (NEQ: tid0 <> tid1)
        (NONE: NatMap.find tid1 rs = None)
    :
    (@get_resource M tid1 (NatMap.add tid0 r rs)).2 = NatMap.add tid0 r rs.
  Proof.
    unfold get_resource. unfold nm_pop. rewrite nm_find_add_neq; auto. rewrite NONE. ss.
  Qed.

  Lemma get_resource_rs_neq
        rs
        tid0 tid1
        (NEQ: tid0 <> tid1)
    :
    fst (@get_resource M tid1 (snd (@get_resource M tid0 rs))) = fst (@get_resource M tid1 rs).
  Proof.
    destruct (NatMap.find tid0 rs) eqn:FIND.
    { erewrite get_resource_find_some_snd; eauto. rewrite get_resource_remove_neq_fst; auto. }
    { erewrite get_resource_find_none_snd; eauto. }
  Qed.

  Lemma ura_wf_get_resource_neq
        g r_own rs_ctx
        tid tid0
        (NEQ: tid <> tid0)
        (RSWF: NatMap.find tid rs_ctx = None)
        (URAWF: ✓ (g ⋅ r_own ⋅ sum_of_resources rs_ctx))
    :
    ✓ (g ⋅ fst (@get_resource M tid0 rs_ctx)
              ⋅ sum_of_resources (snd (@get_resource M tid0 (NatMap.add tid r_own rs_ctx)))).
  Proof.
    destruct (NatMap.find tid0 rs_ctx) eqn:FIND.
    { erewrite get_resource_add_neq_find_some_snd; eauto. ss.
      erewrite get_resource_find_some_fst; eauto.
      assert (FIND2: NatMap.find tid0 (NatMap.add tid r_own rs_ctx) = Some c).
      { rewrite nm_find_add_neq; auto. }
      hexploit (@sum_of_resources_remove M). eapply FIND2. i.
      rewrite (comm cmra.op) in H.
      assert (g ⋅ c ⋅ sum_of_resources (NatMap.remove (elt:=M) tid0 (NatMap.add tid r_own rs_ctx)) ≡ g ⋅ sum_of_resources (NatMap.add tid r_own rs_ctx)) as EQ.
      { rewrite H. r_solve. }
      rewrite EQ.
      hexploit (@sum_of_resources_add M); eauto. instantiate (1:=r_own). i.
      rewrite H0. clear -URAWF.
      by rewrite (comm cmra.op _ r_own) (assoc cmra.op).
    }
    { erewrite get_resource_add_neq_find_none_snd; eauto. ss.
      erewrite get_resource_find_none_fst; eauto.
      hexploit (@sum_of_resources_add M). eapply RSWF. instantiate (1:=r_own). i.
      rewrite H. clear -URAWF.
      by rewrite right_id (comm cmra.op _ r_own) (assoc cmra.op).
    }
  Qed.

  Lemma sum_of_resources_empty
    :
    sum_of_resources (NatMap.empty M) = ε.
  Proof.
    eapply NatMapP.fold_Empty; auto. apply NatMap.empty_1.
  Qed.

  Lemma get_resource_snd_find_eq_none
        tid rs
    :
    NatMap.find (elt:=M) tid (snd (@get_resource M tid rs)) = None.
  Proof.
    unfold get_resource. des_ifs; ss.
    - eapply nm_pop_res_find_none; eauto.
    - eapply nm_pop_find_none; eauto.
  Qed.

  Definition get_resource_l
             (tid: thread_id)
             (rs: list (thread_id * M)%type)
    : ((cmra_car M) * (list (thread_id * M)%type)) :=
    match nm_pop_l tid rs with
    | Some (r, rs) => (r, rs)
    | _ => (ε, rs)
    end.

  Lemma get_resource_l_eq
        tid rs
        r rs'
        (GET: @get_resource M tid rs = (r, rs'))
    :
    get_resource_l tid (NatMap.elements rs) = (r, NatMap.elements rs').
  Proof.
    unfold get_resource, get_resource_l in *. destruct (nm_pop tid rs) eqn:POP.
    - destruct p as [r0 rs0]. inv GET. apply nm_pop_l_eq_some in POP. rewrite POP. ss.
    - inv GET. apply nm_pop_l_eq_none in POP. rewrite POP. ss.
  Qed.

  Lemma get_resource_l_eq_fst
        tid rs
    :
    fst (@get_resource M tid rs) = fst (get_resource_l tid (NatMap.elements rs)).
  Proof.
    destruct (@get_resource M tid rs) eqn:GET. apply get_resource_l_eq in GET. rewrite GET. ss.
  Qed.

  Lemma get_resource_l_eq_snd
        tid rs
    :
    NatMap.elements (snd (@get_resource M tid rs)) = snd (get_resource_l tid (NatMap.elements rs)).
  Proof.
    destruct (@get_resource M tid rs) eqn:GET. apply get_resource_l_eq in GET. rewrite GET. ss.
  Qed.

End AUX.
