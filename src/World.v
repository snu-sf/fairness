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