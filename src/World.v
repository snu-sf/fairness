From sflib Require Import sflib.
Require Import Coq.Classes.RelationClasses.
From Fairness Require Import Axioms NatStructs.
From Fairness Require Import PCM.
From Fairness Require Import Mod.
Require Import String.

Set Implicit Arguments.


Section INVARIANT.
  Context `{M: URA.t}.

  Definition local_resources := NatMap.t URA.car.

  Definition unwrap_opt_resource (r: option URA.car): URA.car :=
    match r with
    | Some r => r
    | None => ε
    end.

  Definition sum_of_resources (rs: local_resources): URA.car :=
    NatMap.fold (fun _ r s => r ⋅ s) rs ε.

  Lemma permutation_same_sum l0 l1 r
        (PERM: Permutation.Permutation l0 l1)
    :
    List.fold_left (fun a (p : NatMap.key * M) => snd p ⋅ a) l0 r
    = List.fold_left (fun a (p : NatMap.key * M) => snd p ⋅ a) l1 r.
  Proof.
    revert r. induction PERM; i; ss.
    { f_equal. r_solve. }
    { rewrite IHPERM1. rewrite IHPERM2. auto. }
  Qed.

  Lemma resources_fold_left_base r l
    :
    List.fold_left (fun a (p : NatMap.key * M) => snd p ⋅ a) l r
    =
    List.fold_left (fun a (p : NatMap.key * M) => snd p ⋅ a) l ε ⋅ r.
  Proof.
    revert r. induction l; i; ss.
    { rewrite URA.unit_idl. auto. }
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
    sum_of_resources rs = (sum_of_resources (NatMap.remove tid rs)) ⋅ r.
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
    sum_of_resources (NatMap.add tid r rs) = (sum_of_resources rs) ⋅ r.
  Proof.
    unfold sum_of_resources. rewrite ! NatMap.fold_1.
    hexploit Permutation_add.
    { eapply NatMapP.F.not_find_in_iff. eauto. }
    { reflexivity. }
    i. eapply permutation_same_sum in H.
    rewrite H. ss. rewrite resources_fold_left_base. r_solve.
  Qed.

  Definition resources_wf (g: URA.car) (rs: local_resources): Prop :=
    URA.wf (g ⋅ sum_of_resources rs)
  .

  Definition get_resource
             (tid: thread_id)
             (rs: local_resources)
    : (URA.car * local_resources) :=
    match nm_pop tid rs with
    | Some (r, rs) => (r, rs)
    | _ => (ε, rs)
    end.

  Lemma resources_wf_get_wf g0 tid rs0 r0 rs1
        (WF: resources_wf g0 rs0)
        (GET: get_resource tid rs0 = (r0, rs1))
    :
    (<<WF: URA.wf (g0 ⋅ r0 ⋅ sum_of_resources rs1)>>) /\
      (<<UPDATE: forall g1 r1
                        (WF: URA.wf (g1 ⋅ r1 ⋅ sum_of_resources rs1)),
          resources_wf g1 (NatMap.add tid r1 rs1)>>).
  Proof.
    unfold resources_wf, get_resource in *. des_ifs.
    { hexploit nm_pop_find_some; eauto. i.
      hexploit nm_pop_res_is_rm_eq; eauto. i.
      hexploit sum_of_resources_remove; eauto. i. subst.
      rewrite H1 in WF. split.
      { r. r_wf WF. }
      { ii. rewrite sum_of_resources_add.
        { r_wf WF0. }
        { eapply nm_find_rm_eq. }
      }
    }
    { hexploit nm_pop_find_none; eauto. i. split.
      { r. r_wf WF. }
      { ii. rewrite sum_of_resources_add; eauto. r_wf WF0. }
    }
  Qed.
End INVARIANT.

Section AUX.

  Context `{M: URA.t}.

  Lemma get_resource_find_some
        (rs: local_resources)
        tid
        r
        (SOME: NatMap.find tid rs = Some r)
    :
    get_resource tid rs = (r, NatMap.remove tid rs).
  Proof.
    unfold get_resource, nm_pop. rewrite SOME. ss.
  Qed.

  Lemma get_resource_find_some_fst
        (rs: local_resources)
        tid
        r
        (SOME: NatMap.find tid rs = Some r)
    :
    fst (get_resource tid rs) = r.
  Proof. hexploit get_resource_find_some; eauto. i. rewrite H. ss. Qed.

  Lemma get_resource_find_some_snd
        (rs: local_resources)
        tid
        r
        (SOME: NatMap.find tid rs = Some r)
    :
    snd (get_resource tid rs) = NatMap.remove tid rs.
  Proof. hexploit get_resource_find_some; eauto. i. rewrite H. ss. Qed.

  Lemma get_resource_find_none
        (rs: local_resources)
        tid
        (NONE: NatMap.find tid rs = None)
    :
    get_resource tid rs = (ε, rs).
  Proof.
    unfold get_resource. unfold nm_pop. rewrite NONE. ss.
  Qed.

  Lemma get_resource_find_none_fst
        (rs: local_resources)
        tid
        (NONE: NatMap.find tid rs = None)
    :
    fst (get_resource tid rs) = ε.
  Proof. hexploit get_resource_find_none; eauto. i. rewrite H. ss. Qed.

  Lemma get_resource_find_none_snd
        (rs: local_resources)
        tid
        (NONE: NatMap.find tid rs = None)
    :
    snd (get_resource tid rs) = rs.
  Proof. hexploit get_resource_find_none; eauto. i. rewrite H. ss. Qed.

  Lemma get_resource_remove_eq
        (rs: local_resources)
        tid
    :
    get_resource tid (NatMap.remove tid rs) = (ε, NatMap.remove tid rs).
  Proof.
    unfold get_resource. unfold nm_pop. rewrite nm_find_rm_eq. ss.
  Qed.

  Lemma get_resource_remove_neq_fst
        (rs: local_resources)
        tid0 tid1
        (NEQ: tid0 <> tid1)
    :
    fst (get_resource tid1 (NatMap.remove tid0 rs)) = fst (get_resource tid1 rs).
  Proof.
    unfold get_resource. unfold nm_pop. rewrite nm_find_rm_neq; auto. des_ifs.
  Qed.

  Lemma get_resource_remove_neq_find_some
        (rs: local_resources)
        tid0 tid1 r
        (NEQ: tid0 <> tid1)
        (SOME: NatMap.find tid1 rs = Some r)
    :
    get_resource tid1 (NatMap.remove tid0 rs) = (r, NatMap.remove tid1 (NatMap.remove tid0 rs)).
  Proof.
    unfold get_resource. unfold nm_pop. rewrite nm_find_rm_neq; auto. rewrite SOME. ss.
  Qed.

  Lemma get_resource_remove_neq_find_none
        (rs: local_resources)
        tid0 tid1
        (NEQ: tid0 <> tid1)
        (NONE: NatMap.find tid1 rs = None)
    :
    get_resource tid1 (NatMap.remove tid0 rs) = (ε, NatMap.remove tid0 rs).
  Proof.
    unfold get_resource. unfold nm_pop. rewrite nm_find_rm_neq; auto. rewrite NONE. ss.
  Qed.

  Lemma get_resource_add_eq
        (rs: local_resources)
        tid r
    :
    get_resource tid (NatMap.add tid r rs) = (r, NatMap.remove tid rs).
  Proof.
    unfold get_resource. rewrite nm_pop_add_eq. ss.
  Qed.

  Lemma get_resource_add_neq_fst
        (rs: local_resources)
        tid0 tid1 r
        (NEQ: tid0 <> tid1)
    :
    fst (get_resource tid1 (NatMap.add tid0 r rs)) = fst (get_resource tid1 rs).
  Proof.
    unfold get_resource. unfold nm_pop. rewrite nm_find_add_neq; auto. des_ifs.
  Qed.

  Lemma get_resource_add_neq_find_some
        (rs: local_resources)
        tid0 tid1 r r0
        (NEQ: tid0 <> tid1)
        (SOME: NatMap.find tid1 rs = Some r0)
    :
    get_resource tid1 (NatMap.add tid0 r rs) = (r0, NatMap.remove tid1 (NatMap.add tid0 r rs)).
  Proof.
    unfold get_resource. unfold nm_pop. rewrite nm_find_add_neq; auto. rewrite SOME. ss.
  Qed.

  Lemma get_resource_add_neq_find_none
        (rs: local_resources)
        tid0 tid1 r
        (NEQ: tid0 <> tid1)
        (NONE: NatMap.find tid1 rs = None)
    :
    get_resource tid1 (NatMap.add tid0 r rs) = (ε, (NatMap.add tid0 r rs)).
  Proof.
    unfold get_resource. unfold nm_pop. rewrite nm_find_add_neq; auto. rewrite NONE. ss.
  Qed.

  Lemma get_resource_rs_neq
        rs
        tid0 tid1
        (NEQ: tid0 <> tid1)
    :
    fst (get_resource tid1 (snd (get_resource tid0 rs))) = fst (get_resource tid1 rs).
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
        (URAWF: URA.wf (g ⋅ r_own ⋅ sum_of_resources rs_ctx))
    :
    URA.wf (g ⋅ fst (get_resource tid0 rs_ctx)
              ⋅ sum_of_resources (snd (get_resource tid0 (NatMap.add tid r_own rs_ctx)))).
  Proof.
    destruct (NatMap.find tid0 rs_ctx) eqn:FIND.
    { erewrite get_resource_add_neq_find_some; eauto. ss.
      erewrite get_resource_find_some_fst; eauto.
      assert (FIND2: NatMap.find tid0 (NatMap.add tid r_own rs_ctx) = Some c).
      { rewrite nm_find_add_neq; auto. }
      hexploit sum_of_resources_remove. eapply FIND2. i.
      rewrite URA.add_comm in H.
      replace (g ⋅ c ⋅ sum_of_resources (NatMap.remove (elt:=M) tid0 (NatMap.add tid r_own rs_ctx))) with (g ⋅ sum_of_resources (NatMap.add tid r_own rs_ctx)).
      2:{ rewrite H. r_solve. }
      hexploit sum_of_resources_add; eauto. instantiate (1:=r_own). i.
      rewrite H0. r_wf URAWF.
    }
    { erewrite get_resource_add_neq_find_none; eauto. ss.
      erewrite get_resource_find_none_fst; eauto.
      hexploit sum_of_resources_add. eapply RSWF. instantiate (1:=r_own). i.
      rewrite H. r_wf URAWF.
    }
  Qed.

End AUX.
