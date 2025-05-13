From sflib Require Import sflib.
Require Import Coq.Classes.RelationClasses.
From iris.algebra Require Import cmra updates local_updates auth gmap.
From iris.proofmode Require Import tactics.

From Fairness Require Import Axioms NatStructsLarge.
From Fairness Require Import PCM.
Require Import String Lia Program.

Set Implicit Arguments.

Module NatMapRALarge.
  Section MAP.
    Context {A: Type}.

    Inductive car :=
    | Map : (NatMap.t A) → car
    | Bot : car.

    Definition unit: car := Map (NatMap.empty A).

    Definition add (m0 m1: car): car :=
      match m0, m1 with
      | Map m0, Map m1 =>
          if (NatStructsLarge.disjoint m0 m1) then Map (NatMapP.update m0 m1) else Bot
      | _, _ => Bot
      end.

    Definition wf (m: car): Prop :=
      match m with
      | Bot => False
      | _ => True
      end.

    Definition core (m: car): option car := (Some unit).

    Canonical Structure NatMapRALargeO := leibnizO car.

    Local Instance NatMapRALarge_valid_instance : Valid car := wf.
    Local Instance NatMapRALarge_pcore_instance : PCore car := core.
    Local Instance NatMapRALarge_op_instance : Op car := add.
    Local Instance NatMapRALarge_unit_instance : Unit car := unit.

    Lemma valid_unfold om : ✓ om ↔ wf om.
    Proof. done. Qed.
    Lemma valid_some m : ✓ (Map m).
    Proof. done. Qed.
    Lemma op_unfold p q : p ⋅ q = add p q.
    Proof. done. Qed.
    Lemma pcore_unfold p : pcore p = (core p).
    Proof. done. Qed.
    Lemma unit_unfold : ε = unit.
    Proof. done. Qed.

    Definition mixin : RAMixin car.
    Proof.
      apply ra_total_mixin; try apply _; try done.
      all: fold_leibniz.
      - intros ???. fold_leibniz.
        rewrite !op_unfold /add. des_ifs.
        { f_equal. rewrite union_assoc. auto. }
        { rewrite disjoint_true_iff in Heq0.
          rewrite disjoint_true_iff in Heq1.
          apply Disjoint_union in Heq0. des.
          hexploit (proj2 (Disjoint_union t2 t t3)).
          { split.
            { apply NatMapP.Disjoint_sym. auto. }
            { apply NatMapP.Disjoint_sym. auto. }
          }
          i. apply NatMapP.Disjoint_sym in H.
          apply disjoint_true_iff in H. clarify.
        }
        { rewrite disjoint_true_iff in Heq0.
          rewrite disjoint_true_iff in Heq3.
          apply Disjoint_union in Heq0. des.
          apply disjoint_true_iff in Heq0. clarify.
        }
        { rewrite disjoint_true_iff in Heq1.
          rewrite disjoint_true_iff in Heq3.
          rewrite disjoint_true_iff in Heq2.
          apply NatMapP.Disjoint_sym in Heq2.
          apply Disjoint_union in Heq2. des.
          hexploit (proj2 (Disjoint_union t t3 t2)).
          { split; auto. apply NatMapP.Disjoint_sym. auto. }
          i. apply disjoint_true_iff in H. clarify.
        }
        { rewrite disjoint_true_iff in Heq2.
          rewrite disjoint_true_iff in Heq1.
          apply NatMapP.Disjoint_sym in Heq1.
          apply Disjoint_union in Heq1. des.
          apply NatMapP.Disjoint_sym in Heq3.
          apply disjoint_true_iff in Heq3. clarify.
        }
      - intros ??. fold_leibniz.
        rewrite !op_unfold /add. des_ifs.
        { f_equal. apply disjoint_union_comm. apply disjoint_true_iff; auto. }
        { rewrite disjoint_comm in Heq. clarify. }
        { rewrite disjoint_comm in Heq. clarify. }
      - intros x. rewrite /cmra.core pcore_unfold op_unfold /core /add.
        simpl. des_ifs. f_equal. rewrite union_empty. auto.
      - intros x y [z EQ]. fold_leibniz. subst.
        rewrite /cmra.core pcore_unfold op_unfold /core /add /=.
        exists unit. split; eauto.
      - intros x y. rewrite !valid_unfold /wf op_unfold /add.
        des_ifs.
    Qed.
    Canonical Structure NatMapR := discreteR car mixin.

    Global Instance discrete : CmraDiscrete NatMapR.
    Proof. apply discrete_cmra_discrete. Qed.

    Lemma ucmra_mixin : UcmraMixin car.
    Proof.
      split; try apply _; try done.
      intros m.
      fold_leibniz.
      rewrite op_unfold /add unit_unfold /unit.
      des_ifs. rewrite union_empty. ss.
    Qed.
    Canonical Structure t := Ucmra car ucmra_mixin.

    Definition to_Map (map : NatMap.t A) : t := Map map.

    Definition singleton (k: nat) (a: A): t := Map (NatMap.add k a (NatMap.empty A)).

    Lemma singleton_unique k0 a0 k1 a1
          (WF: ✓ (singleton k0 a0 ⋅ singleton k1 a1))
      :
      k0 ≠ k1.
    Proof.
      ii. rewrite valid_unfold op_unfold /wf /add /singleton in WF. des_ifs.
      rewrite disjoint_true_iff in Heq0.
      eapply Heq0. split.
      { apply NatMapP.F.add_in_iff. eauto. }
      { apply NatMapP.F.add_in_iff. eauto. }
    Qed.

    Lemma extends_iff m0 m1
      :
      (Map m0) ≼ (Map m1)
      ↔
        (forall k a (FIND: NatMap.find k m0 = Some a), NatMap.find k m1 = Some a).
    Proof.
      split.
      { ii. rr in H. des. fold_leibniz. rewrite op_unfold /add in H. des_ifs.
        apply NatMap.find_1. apply NatMapP.update_mapsto_iff.
        apply NatMap.find_2 in FIND. right. split; auto.
        apply disjoint_true_iff in Heq.
        ii. eapply Heq; eauto. split; eauto.
        apply NatMapP.F.in_find_iff. apply NatMap.find_1 in FIND. ii. clarify.
      }
      { i. exists (Map (NatMapP.diff m1 m0)). fold_leibniz.
        rewrite op_unfold /add. des_ifs.
        { f_equal. apply nm_eq_is_equal.
          apply NatMapP.F.Equal_mapsto_iff. i.
          rewrite NatMapP.update_mapsto_iff.
          rewrite NatMapP.diff_mapsto_iff. split; i; des; auto; last first.
          { apply NatMap.find_2. eapply H.
            apply NatMap.find_1. auto.
          }
          { destruct (NatMap.find k m0) eqn:FIND.
            { apply NatMap.find_1 in H0.
              hexploit H; eauto. i. clarify.
              right. split; auto.
              { apply NatMap.find_2; auto. }
              { ii. apply NatMapP.diff_in_iff in H0. des.
                eapply H2. apply NatMapP.F.in_find_iff. ii. clarify.
              }
            }
            { left. split; auto. ii.
              apply NatMapP.F.in_find_iff in H1. ss.
            }
          }
        }
        { apply disjoint_false_iff in Heq.
          exfalso. eapply Heq. ii. des.
          apply NatMapP.diff_in_iff in H1. des. ss.
        }
      }
    Qed.

    Lemma extends_singleton_iff m k a
      :
      (singleton k a) ≼ (Map m)
      <->
        (NatMap.find k m = Some a).
    Proof.
      unfold singleton. rewrite extends_iff. split; i.
      { eapply H. apply nm_find_add_eq. }
      { rewrite NatMapP.F.add_o in FIND. des_ifs. }
    Qed.

    Lemma add_local_update m k a
          (NONE: NatMap.find k m = None)
      :
      ((Map m),ε) ~l~> ((Map (NatMap.add k a m)),(singleton k a)).
    Proof.
      rewrite local_update_unital_discrete.
      intros ctx _ FRAME. fold_leibniz.
      rewrite left_id in FRAME. subst.
      split; ss.
      rewrite op_unfold /add /singleton.
      des_ifs.
      { apply disjoint_true_iff, NatMapP.Disjoint_sym, Disjoint_add in Heq.
        des.
        f_equal. eapply eq_ext_is_eq. ii.
        rewrite ! NatMapP.F.add_mapsto_iff
          ! NatMapP.update_mapsto_iff
          ! NatMapP.F.add_mapsto_iff
          NatMapP.F.empty_mapsto_iff.
        split; i; des; subst; auto.
        - right. split; auto. ii. subst.
          apply NatMapP.F.find_mapsto_iff in H. clarify.
        - right. split; auto. ii. clarify.
      }
      { exfalso. apply disjoint_false_iff in Heq. apply Heq.
        apply NatMapP.Disjoint_sym.
        eapply Disjoint_add. split.
        { by apply NatMapP.F.not_find_in_iff in NONE. }
        { apply Disjoint_empty. }
      }
    Qed.

    Lemma remove_local_update m k a
      :
      ((Map m), (singleton k a)) ~l~> ((Map (NatMap.remove k m)),ε).
    Proof.
      rewrite local_update_unital_discrete.
      intros ctx _ FRAME. fold_leibniz.
      rewrite op_unfold /add /singleton in FRAME.

      des_ifs. split; ss.
      rewrite left_id. f_equal.
      apply disjoint_true_iff in Heq.
      apply NatMapP.Disjoint_sym in Heq.
      apply Disjoint_add in Heq. des.
      eapply eq_ext_is_eq. ii.
      rewrite ! NatMapP.F.remove_mapsto_iff
        ! NatMapP.update_mapsto_iff
        ! NatMapP.F.add_mapsto_iff
        NatMapP.F.empty_mapsto_iff.
      split; i; des; subst; auto; try done.
      splits; auto. ii. subst. eapply Heq.
      apply NatMapP.F.in_find_iff.
      apply NatMap.find_1 in H. ii. clarify.
    Qed.
  End MAP.
End NatMapRALarge.
Global Arguments NatMapRALarge.t _ : clear implicits.

From Fairness Require Import IPM IUpd ListIProp.
From iris.bi Require Import derived_laws.
Import bi.

Section SUM.
  Context `{Σ: GRA.t}.
  Notation iProp := (iProp Σ) (only parsing).

  Definition natmap_prop_sum A (f: NatMap.t A) (P: nat -> A -> iProp) :=
    list_prop_sum (fun '(k, v) => P k v) (NatMap.elements f).

  Lemma natmap_prop_sum_empty A P
    :
    ⊢ natmap_prop_sum (NatMap.empty A) P.
  Proof.
    unfold natmap_prop_sum. ss.
  Qed.

  Lemma natmap_prop_remove_find A (f: NatMap.t A) P k v
        (FIND: NatMap.find k f = Some v)
    :
    (natmap_prop_sum f P)
      -∗
      (P k v ∗ natmap_prop_sum (NatMap.remove k f) P).
  Proof.
    hexploit NatMap.elements_1.
    { eapply NatMap.find_2; eauto. }
    i. eapply SetoidList.InA_split in H. des.
    destruct y. inv H. ss. subst.
    unfold natmap_prop_sum. rewrite H0.
    iIntros "H".
    iPoseProof (list_prop_sum_perm with "H") as "H".
    { instantiate (1:=(k0,a)::(l1 ++ l2)).
      symmetry. apply Permutation_middle.
    }
    iEval (ss) in "H". iDestruct "H" as "[H0 H1]". iFrame.
    iApply (list_prop_sum_perm with "H1").
    symmetry. eapply Permutation_remove.
    rewrite H0. symmetry. apply Permutation_middle.
  Qed.

  Lemma natmap_prop_remove A (f: NatMap.t A) P k
    :
    (natmap_prop_sum f P)
      -∗
      (natmap_prop_sum (NatMap.remove k f) P).
  Proof.
    destruct (NatMap.find k f) eqn:EQ.
    { iIntros "H". iPoseProof (natmap_prop_remove_find with "H") as "[_ H]"; eauto. }
    replace (NatMap.remove k f) with f; auto.
    eapply eq_ext_is_eq. ii.
    rewrite NatMapP.F.remove_mapsto_iff. split.
    { i. split; auto. ii.
      eapply NatMap.find_1 in H. clarify.
    }
    { i. des. auto. }
  Qed.

  Lemma natmap_prop_sum_add A P k v (f: NatMap.t A)
    :
    (natmap_prop_sum f P)
      -∗
      (P k v)
      -∗
      (natmap_prop_sum (NatMap.add k v f) P).
  Proof.
    destruct (NatMapP.F.In_dec f k).
    { rewrite <- nm_add_rm_eq. iIntros "H0 H1".
      unfold natmap_prop_sum.
      iApply list_prop_sum_perm.
      { symmetry. eapply Permutation_add; eauto. apply NatMap.remove_1; auto. }
      iPoseProof (natmap_prop_remove with "H0") as "H0".
      ss. iFrame.
    }
    { unfold natmap_prop_sum. iIntros "H0 H1".
      iApply list_prop_sum_perm.
      { symmetry. eapply Permutation_add; eauto. }
      ss. iFrame.
    }
  Qed.

  Lemma natmap_prop_sum_persistent A (P: nat -> A -> iProp) m
        (PERSIST: forall n a, Persistent (P n a))
    :
    (natmap_prop_sum m P) -∗ (□ natmap_prop_sum m P).
  Proof.
    unfold natmap_prop_sum. apply list_prop_sum_persistent. i. des_ifs.
  Qed.

  Global Program Instance Persistent_natmap_prop_sum
         A (P: nat -> A -> iProp) m
         (PERSIST: forall n a, Persistent (P n a)) : Persistent (natmap_prop_sum m P).
  Next Obligation.
  Proof.
    intros. iIntros "Ps". iPoseProof (natmap_prop_sum_persistent with "Ps") as "Ps". auto.
  Qed.

  Lemma natmap_prop_sum_in A P k a (m: NatMap.t A)
        (FIND: NatMap.find k m = Some a)
    :
    (natmap_prop_sum m P)
      -∗
      (P k a).
  Proof.
    iIntros "MAP". iPoseProof (natmap_prop_remove_find with "MAP") as "[H0 H1]".
    { eauto. }
    eauto.
  Qed.

  Lemma natmap_prop_sum_impl A P0 P1 (m: NatMap.t A)
        (IMPL: forall k a (IN: NatMap.find k m = Some a), P0 k a ⊢ P1 k a)
    :
    (natmap_prop_sum m P0)
      -∗
      (natmap_prop_sum m P1).
  Proof.
    revert IMPL. pattern m. eapply nm_ind.
    { iIntros. iApply natmap_prop_sum_empty. }
    i. iIntros "MAP".
    iPoseProof (natmap_prop_remove_find with "MAP") as "[H0 H1]".
    { eapply nm_find_add_eq. }
    iPoseProof (IMPL with "H0") as "H0".
    { rewrite nm_find_add_eq. auto. }
    iApply (natmap_prop_sum_add with "[H1] H0").
    iApply IH.
    { i. eapply IMPL. rewrite NatMapP.F.add_o; eauto. des_ifs. }
    { rewrite nm_find_none_rm_add_eq; auto. }
  Qed.

  Lemma natmap_prop_sum_impl_ctx A HCTX P0 P1 (m: NatMap.t A)
        (IMPL: forall k a (IN: NatMap.find k m = Some a), HCTX ∗ P0 k a ⊢ P1 k a)
    :
    □ HCTX
    -∗
    (natmap_prop_sum m P0)
      -∗
      (natmap_prop_sum m P1).
  Proof.
    revert IMPL. pattern m. eapply nm_ind.
    { iIntros. iApply natmap_prop_sum_empty. }
    i. iIntros "#CTX MAP".
    iPoseProof (natmap_prop_remove_find with "MAP") as "[H0 H1]".
    { eapply nm_find_add_eq. }
    iPoseProof (IMPL with "[CTX H0]") as "H0".
    { erewrite nm_find_add_eq. auto. } iFrame. done.
    iApply (natmap_prop_sum_add with "[H1] H0").
    iApply IH.
    { i. eapply IMPL. rewrite NatMapP.F.add_o; eauto. des_ifs. }
    { iModIntro. done. }
    { rewrite nm_find_none_rm_add_eq; auto. }
  Qed.

  Lemma natmap_prop_sum_wand (A: Type) P0 P1 (m: NatMap.t A)
    :
    (natmap_prop_sum m P0)
      -∗
      (natmap_prop_sum m (fun k v => P0 k v -∗ P1 k v))
      -∗
      (natmap_prop_sum m P1).
  Proof.
    pattern m. eapply nm_ind.
    { iIntros. iApply natmap_prop_sum_empty. }
    i. iIntros "MAP IMPL".
    iPoseProof (natmap_prop_remove_find with "MAP") as "[H0 H1]".
    { eapply nm_find_add_eq. }
    iPoseProof (natmap_prop_remove_find with "IMPL") as "[G0 G1]".
    { eapply nm_find_add_eq. }
    iApply (natmap_prop_sum_add with "[H1 G1] [H0 G0]").
    { rewrite nm_find_none_rm_add_eq; auto. iApply (IH with "H1 G1"). }
    { iApply ("G0" with "H0"). }
  Qed.

  Lemma natmap_prop_sum_impl_strong (A: Type) P0 P1 Q (m: NatMap.t A)
        (IMPL: forall k v, P0 k v ∗ Q ⊢ P1 k v ∗ Q)
    :
    (natmap_prop_sum m P0 ∗ Q)
      -∗
      (natmap_prop_sum m P1 ∗ Q).
  Proof.
    pattern m. eapply nm_ind.
    { iIntros "[SUM H]". iFrame. }
    i. iIntros "[MAP H]".
    iPoseProof (natmap_prop_remove_find with "MAP") as "[H0 H1]".
    { eapply nm_find_add_eq. }
    rewrite nm_find_none_rm_add_eq; [|auto].
    iPoseProof (IH with "[H1 H]") as "[H1 H]".
    { iFrame. }
    iPoseProof (IMPL with "[H0 H]") as "[H0 H]".
    { iFrame. }
    iFrame. iApply (natmap_prop_sum_add with "H1 H0").
  Qed.

  Lemma natmap_prop_sum_or_cases_l
        A (P0 P1: nat -> A -> iProp) m
    :
    (natmap_prop_sum m (fun k a => (P0 k a ∨ P1 k a)))
      -∗
      ((natmap_prop_sum m P0) ∨ (∃ k a, (⌜NatMap.find k m = Some a⌝) ∗ (P1 k a))).
  Proof.
    unfold natmap_prop_sum. iIntros "SUM".
    iPoseProof (list_prop_sum_or_cases_l with "[SUM]") as "SUM".
    { iApply list_prop_sum_impl. 2: iFrame. i. ss. des_ifs. iIntros "[P0|P1]".
      - iLeft. instantiate (1:=fun '(k, a) => P0 k a). ss.
      - iRight. instantiate (1:=fun '(k, a) => P1 k a). ss.
    }
    iDestruct "SUM" as "[SUM|ELSE]".
    { iFrame. }
    iRight. iDestruct "ELSE" as "[% [IN P]]". des_ifs. do 2 iExists _. iFrame.
    iPure "IN" as IN. iPureIntro. remember (NatMap.elements m) as ml.
    assert (ND: SetoidList.NoDupA (NatMap.eq_key (elt:=_)) ml).
    { subst. apply NatMap.elements_3w. }
    rewrite NatMapP.F.elements_o. rewrite <- Heqml. clear m Heqml.
    eapply SetoidList.In_InA in IN.
    { eapply SetoidList.findA_NoDupA; eauto. }
    econs; ss.
    - econs; des; clarify.
    - econs; des; clarify; auto. rewrite <- H0. auto. rewrite <- H1; auto.
  Qed.

  Lemma natmap_prop_sum_or_cases_r
        A (P0 P1: nat -> A -> iProp) m
    :
    (natmap_prop_sum m (fun k a => (P0 k a ∨ P1 k a)))
      -∗
      ((natmap_prop_sum m P1) ∨ (∃ k a, (⌜NatMap.find k m = Some a⌝) ∗ (P0 k a))).
  Proof.
    iIntros "SUM". iApply natmap_prop_sum_or_cases_l. iApply natmap_prop_sum_impl. 2: iFrame.
    i. iIntros "[C0|C1]"; iFrame.
  Qed.

  Lemma natmap_prop_sum_pull_bupd
        Q
        A (P: nat -> A -> iProp) m
    :
    (natmap_prop_sum m (fun k a => #=( Q )=> P k a))
      -∗
      #=( Q )=>(natmap_prop_sum m P).
  Proof.
    unfold natmap_prop_sum. iIntros "SUM".
    iPoseProof (list_prop_sum_pull_bupd with "[SUM]") as "SUM".
    { iApply list_prop_sum_impl. 2: iFrame. i. ss. des_ifs.
      instantiate (1:=fun '(k, a) => P k a). ss.
    }
    iFrame.
  Qed.

  Lemma natmap_prop_sum_pull_bupd_default
        A (P: nat -> A -> iProp) m
    :
    (natmap_prop_sum m (fun k a => #=> P k a))
      -∗
      #=>(natmap_prop_sum m P).
  Proof.
    unfold natmap_prop_sum. iIntros "SUM".
    iPoseProof (list_prop_sum_pull_bupd_default with "[SUM]") as "SUM".
    { iApply list_prop_sum_impl. 2: iFrame. i. ss. des_ifs.
      instantiate (1:=fun '(k, a) => P k a). ss.
    }
    iFrame.
  Qed.

  Lemma natmap_prop_sum_sepconj A (P0 P1: nat -> A -> iProp) m
    :
    ((natmap_prop_sum m P0) ∗ (natmap_prop_sum m P1))
      -∗
      natmap_prop_sum m (fun k a => (P0 k a) ∗ (P1 k a)).
  Proof.
    unfold natmap_prop_sum . iIntros "SUM".
    iPoseProof (list_prop_sum_sepconj with "SUM") as "SUM". iApply list_prop_sum_impl. 2: iFrame.
    i. ss. des_ifs; ss.
  Qed.

  Lemma natmap_prop_sepconj_sum A (P0 P1: nat -> A -> iProp) m
    :
    (natmap_prop_sum m (fun k a => (P0 k a) ∗ (P1 k a)))
      -∗
      ((natmap_prop_sum m P0) ∗ (natmap_prop_sum m P1)).
  Proof.
    unfold natmap_prop_sum. iIntros "SUM".
    iPoseProof (list_prop_sepconj_sum with "[SUM]") as "SUM".
    { iApply list_prop_sum_impl. 2: iFrame. i. destruct a.
      instantiate (1:=fun '(k, a) => P1 k a). instantiate (1:=fun '(k, a) => P0 k a). ss.
    }
    iFrame.
  Qed.

  Lemma natmap_prop_sum_impl2 A (P0 P1 Q: nat -> A -> iProp) m
        (IMPL: forall k a, (P0 k a ∗ P1 k a) -∗ Q k a)
    :
    ((natmap_prop_sum m P0) ∗ (natmap_prop_sum m P1))
      -∗
      natmap_prop_sum m Q.
  Proof.
    iIntros "SUMs". iApply natmap_prop_sum_impl. 2: iApply natmap_prop_sum_sepconj; iFrame.
    i. ss. iApply IMPL.
  Qed.

  Lemma natmap_prop_sum_find_remove
        A (P: nat -> A -> iProp) m k a
        (FIND: NatMap.find k m = Some a)
    :
    (natmap_prop_sum m (fun k a => P k a))
      -∗ ((P k a) ∗ ((P k a) -∗ (natmap_prop_sum m (fun k a => P k a)))).
  Proof.
    unfold natmap_prop_sum. set (P' := fun x => P (fst x) (snd x)). remember (k, a) as x.
    cut
  (list_prop_sum (λ x, P' x) (NatMap.elements (elt:=A) m) -∗
                 P' x ∗ (P' x -∗ list_prop_sum (λ x, P' x) (NatMap.elements (elt:=A) m))).
    { subst. subst P'. ss. i. replace (λ '(k0, v), P k0 v) with (λ x : nat * A, P x.1 x.2). auto.
      extensionality x. destruct x. ss.
    }
    iIntros "SUMs". iApply (list_prop_sum_in_split with "SUMs").
    subst. apply InA_In'. rewrite NatMapP.F.elements_o in FIND.
    apply SetoidList.findA_NoDupA in FIND; eauto.
    apply NatMap.elements_3w.
  Qed.

End SUM.

Section UPDNATMAP.
  Context {A: Type}.
  Import NatMapRALarge.
  Context `{NATMAPRA: @GRA.inG (authUR (t A)) Σ}.

  Lemma NatMapRALarge_find_some m k a
    :
    (OwnM (● (Map m)))
      -∗
      (OwnM (◯ (singleton k a)))
      -∗
      (⌜NatMap.find k m = Some a⌝).
  Proof.
    iIntros "B W". iCombine "B W" gives %(_&Ha&_)%auth_both_dfrac_valid_discrete.
    by apply NatMapRALarge.extends_singleton_iff in Ha.
  Qed.

  Lemma NatMapRALarge_singleton_unique k0 k1 a0 a1
    :
    (OwnM (◯ singleton k0 a0))
      -∗
      (OwnM (◯ (singleton k1 a1)))
      -∗
      (⌜k0 <> k1⌝).
  Proof.
    iIntros "W0 W1". iCombine "W0 W1" gives %?%auth_frag_valid%singleton_unique.
    auto.
  Qed.

  Lemma NatMapRALarge_remove m k a
    :
    (OwnM (● (Map m)))
      -∗
      (OwnM (◯ (singleton k a)))
      -∗
      #=>(OwnM (● (Map (NatMap.remove k m)))).
  Proof.
    rewrite bi.wand_curry -OwnM_op.
    apply bi.entails_wand, OwnM_Upd, auth_update_dealloc, remove_local_update.
  Qed.

  Lemma NatMapRALarge_add m k a
        (NONE: NatMap.find k m = None)
    :
    (OwnM (● (Map m)))
      -∗
      #=>((OwnM (● (Map (NatMap.add k a m))
                            ⋅ ◯ (singleton k a)))
         ).
  Proof.
    by apply bi.entails_wand, OwnM_Upd, auth_update_alloc, add_local_update.
  Qed.

End UPDNATMAP.
