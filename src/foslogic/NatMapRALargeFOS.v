From sflib Require Import sflib.
Require Import Coq.Classes.RelationClasses.
From Fairness Require Import Axioms NatStructs.
From Fairness Require Import PCMFOS.
Require Import String Lia Program.

Set Implicit Arguments.

Module NatMapRAFOS.
  Section MAP.
    Variable A: Type.

    Definition car := option (NatMap.t A).

    Definition unit: car := Some (NatMap.empty A).

    Definition add (m0 m1: car): car :=
      match m0, m1 with
      | Some m0, Some m1 =>
          if (NatStructs.disjoint m0 m1) then Some (NatMapP.update m0 m1) else None
      | _, _ => None
      end.

    Definition wf (m: car): Prop :=
      match m with
      | None => False
      | _ => True
      end.

    Definition core (m: car): car := unit.

    Global Program Instance t: URA.t := {
        car := car;
        unit := unit;
        _add := add;
        _wf := wf;
        core := core;
      }
    .
    Next Obligation.
      unfold add. des_ifs.
      { f_equal. apply disjoint_union_comm. apply disjoint_true_iff; auto. }
      { rewrite disjoint_comm in Heq. clarify. }
      { rewrite disjoint_comm in Heq. clarify. }
    Qed.
    Next Obligation.
      unfold add. des_ifs.
      { f_equal. rewrite union_assoc. auto. }
      { rewrite disjoint_true_iff in *.
        apply Disjoint_union in Heq0. des.
        hexploit (proj2 (Disjoint_union t2 t t3)).
        { split.
          { apply NatMapP.Disjoint_sym. auto. }
          { apply NatMapP.Disjoint_sym. auto. }
        }
        i. apply NatMapP.Disjoint_sym in H.
        apply disjoint_true_iff in H. clarify.
      }
      { rewrite disjoint_true_iff in *.
        apply Disjoint_union in Heq0. des.
        apply disjoint_true_iff in Heq0. clarify.
      }
      { rewrite disjoint_true_iff in *.
        apply NatMapP.Disjoint_sym in Heq2.
        apply Disjoint_union in Heq2. des.
        hexploit (proj2 (Disjoint_union t t3 t2)).
        { split; auto. apply NatMapP.Disjoint_sym. auto. }
        i. apply disjoint_true_iff in H. clarify.
      }
      { rewrite disjoint_true_iff in *.
        apply NatMapP.Disjoint_sym in Heq1.
        apply Disjoint_union in Heq1. des.
        apply NatMapP.Disjoint_sym in Heq3.
        apply disjoint_true_iff in Heq3. clarify.
      }
    Qed.
    Next Obligation.
      unseal "ra". unfold add, unit. des_ifs.
      hexploit Disjoint_empty. i.
      apply disjoint_true_iff in H. rewrite H in *. clarify.
    Qed.
    Next Obligation.
      unseal "ra". ss.
    Qed.
    Next Obligation.
      unseal "ra". unfold add in *. des_ifs.
    Qed.
    Next Obligation.
      unseal "ra". ss. des_ifs. f_equal.
      rewrite union_empty. auto.
    Qed.
    Next Obligation.
      exists unit. unseal "ra". unfold add, core, unit. des_ifs.
    Qed.

    Definition singleton (k: nat) (a: A): car := Some (NatMap.add k a (NatMap.empty A)).

    Lemma singleton_unique k0 a0 k1 a1
          (WF: URA.wf (singleton k0 a0 ⋅ singleton k1 a1))
      :
      k0 <> k1.
    Proof.
      ii. ur in WF. des_ifs.
      rewrite disjoint_true_iff in *.
      eapply Heq. split.
      { apply NatMapP.F.add_in_iff. eauto. }
      { apply NatMapP.F.add_in_iff. eauto. }
    Qed.

    Lemma extends_iff m0 m1
      :
      URA.extends (Some m0) (Some m1)
      <->
        (forall k a (FIND: NatMap.find k m0 = Some a), NatMap.find k m1 = Some a).
    Proof.
      split.
      { ii. rr in H. des. ur in H. des_ifs.
        apply NatMap.find_1. apply NatMapP.update_mapsto_iff.
        apply NatMap.find_2 in FIND. right. split; auto.
        apply disjoint_true_iff in Heq.
        ii. eapply Heq; eauto. split; eauto.
        apply NatMapP.F.in_find_iff. apply NatMap.find_1 in FIND. ii. clarify.
      }
      { i. exists (Some (NatMapP.diff m1 m0)).
        ur. des_ifs.
        { f_equal. apply nm_eq_is_equal.
          apply NatMapP.F.Equal_mapsto_iff. i.
          rewrite NatMapP.update_mapsto_iff.
          rewrite NatMapP.diff_mapsto_iff. split; i; des; auto.
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
      URA.extends (singleton k a) (Some m)
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
      Auth.local_update (Some m) unit (Some (NatMap.add k a m)) (singleton k a).
    Proof.
      ii. des. ur in FRAME. des_ifs. split; ss.
      { ur. ss. }
      rr. ur. des_ifs.
      { apply disjoint_true_iff in Heq.
        apply NatMapP.Disjoint_sym in Heq.
        apply Disjoint_add in Heq. des.
        f_equal. eapply eq_ext_is_eq. ii.
        rewrite ! NatMapP.F.add_mapsto_iff.
        rewrite ! NatMapP.update_mapsto_iff.
        rewrite ! NatMapP.F.add_mapsto_iff.
        rewrite NatMapP.F.empty_mapsto_iff.
        rewrite <- NatMapP.F.not_find_in_iff in NONE.
        rewrite NatMapP.update_in_iff in NONE.
        split; i; des; subst; auto.
        right. split; auto. ii. subst.
        eapply Heq. apply NatMapP.F.in_find_iff.
        apply NatMap.find_1 in H. ii. clarify.
      }
      { exfalso. apply disjoint_false_iff in Heq. apply Heq.
        apply NatMapP.Disjoint_sym.
        eapply Disjoint_add. split.
        { apply NatMapP.F.not_find_in_iff in NONE.
          rewrite NatMapP.update_in_iff in NONE.
          ii. eapply NONE; eauto.
        }
        { apply Disjoint_empty. }
      }
    Qed.

    Lemma remove_local_update m k a
      :
      Auth.local_update (Some m) (singleton k a) (Some (NatMap.remove k m)) unit.
    Proof.
      ii. des. ur in FRAME. des_ifs. split; ss.
      { ur. ss. }
      rr. unfold unit. ur. f_equal.
      apply disjoint_true_iff in Heq.
      apply NatMapP.Disjoint_sym in Heq.
      apply Disjoint_add in Heq. des.
      eapply eq_ext_is_eq. ii.
      rewrite ! NatMapP.F.remove_mapsto_iff.
      rewrite ! NatMapP.update_mapsto_iff.
      rewrite ! NatMapP.F.add_mapsto_iff.
      rewrite NatMapP.F.empty_mapsto_iff.
      split; i; des; subst; auto.
      { splits; auto. ii. subst. eapply Heq.
        apply NatMapP.F.in_find_iff.
        apply NatMap.find_1 in H. ii. clarify.
      }
      { split; auto. right; auto. }
    Qed.
  End MAP.
End NatMapRAFOS.

From Fairness Require Import IPropFOS IPMFOS.
From iris.bi Require Import derived_laws. Import bi.

Section SUM.
  Context `{Σ: GRA.t}.

  Fixpoint list_prop_sum A (P: A -> iProp) (l: list A): iProp :=
    match l with
    | [] => True
    | hd::tl => P hd ** list_prop_sum P tl
    end.

  Lemma list_prop_sum_wand (A: Type) (P0 P1 : A → iProp)
        (l: list A)
    :
    (list_prop_sum P0 l)
      -∗
      (list_prop_sum (fun a => P0 a -* P1 a) l)
      -∗
      (list_prop_sum P1 l).
  Proof.
    induction l; ss.
    { iIntros. auto. }
    iIntros "[HD0 TL0] [HD1 TL1]". iSplitL "HD0 HD1".
    { iApply ("HD1" with "HD0"). }
    { iApply (IHl with "TL0 TL1"). }
  Qed.

  Lemma list_prop_sum_perm A P (l0 l1: list A)
        (PERM: Permutation l0 l1)
    :
    list_prop_sum P l0 ⊢ list_prop_sum P l1.
  Proof.
    induction PERM; ss.
    { iIntros "[H0 H1]". iFrame. iApply IHPERM. auto. }
    { iIntros "[H0 [H1 H2]]". iFrame. }
    { etrans; eauto. }
  Qed.

  Lemma list_prop_sum_nil A (P: A -> iProp)
    :
    ⊢ list_prop_sum P [].
  Proof.
    ss. auto.
  Qed.

  Lemma list_prop_sum_cons_fold A (P: A -> iProp) hd tl
    :
    (P hd ** list_prop_sum P tl)
      -∗
      (list_prop_sum P (hd::tl)).
  Proof.
    ss.
  Qed.

  Lemma list_prop_sum_cons_unfold A (P: A -> iProp) hd tl
    :
    (list_prop_sum P (hd::tl))
      -∗
      (P hd ** list_prop_sum P tl).
  Proof.
    ss.
  Qed.

  Lemma list_prop_sum_split A (P: A -> iProp) l0 l1
    :
    (list_prop_sum P (l0 ++ l1))
      -∗
      (list_prop_sum P l0 ** list_prop_sum P l1).
  Proof.
    induction l0; ss.
    { iIntros "SAT". iFrame. }
    { iIntros "[INTERP SAT]". iFrame. iApply IHl0; auto. }
  Qed.

  Lemma list_prop_sum_combine A (P: A -> iProp) l0 l1
    :
    (list_prop_sum P l0 ** list_prop_sum P l1)
      -∗
      (list_prop_sum P (l0 ++ l1)).
  Proof.
    induction l0; ss.
    { iIntros "[_ SAT]". auto. }
    { iIntros "[[INTERP SAT0] SAT1]". iFrame.
      iApply IHl0. iFrame.
    }
  Qed.

  Lemma list_prop_sum_add A (P: A -> iProp) l a
    :
    (P a ** list_prop_sum P l)
      -∗
      (list_prop_sum P (l++[a])).
  Proof.
    iIntros "[NEW SAT]". iApply list_prop_sum_combine. iFrame.
  Qed.

  Lemma list_prop_sum_impl A (P0 P1: A -> iProp) l
        (IMPL: forall a, P0 a ⊢ P1 a)
    :
    (list_prop_sum P0 l)
      -∗
      (list_prop_sum P1 l).
  Proof.
    induction l; ss.
    iIntros "[HD TL]". iSplitL "HD".
    { iApply (IMPL with "HD"). }
    { iApply (IHl with "TL"). }
  Qed.

  Lemma list_prop_sum_sepconj A (P0 P1: A -> iProp) l
    :
    ((list_prop_sum P0 l) ∗ (list_prop_sum P1 l))
      -∗
      list_prop_sum (fun a => (P0 a) ∗ (P1 a)) l.
  Proof.
    induction l; ss; auto.
    iIntros "[[HD1 TL1] [HD2 TL2]]". iFrame. iApply IHl. iFrame.
  Qed.

  Lemma list_prop_sepconj_sum A (P0 P1: A -> iProp) l
    :
    (list_prop_sum (fun a => (P0 a) ∗ (P1 a)) l)
      -∗
      ((list_prop_sum P0 l) ∗ (list_prop_sum P1 l)).
  Proof.
    induction l; ss; auto.
    iIntros "[[HD1 HD2] TL]". iFrame. iApply IHl. iFrame.
  Qed.

  Lemma list_prop_sum_impl2 A (P0 P1 Q: A -> iProp) l
        (IMPL: forall a, (P0 a ∗ P1 a) -∗ Q a)
    :
    ((list_prop_sum P0 l) ∗ (list_prop_sum P1 l))
      -∗
      list_prop_sum Q l.
  Proof.
    iIntros "SUMs". iApply list_prop_sum_impl. 2: iApply list_prop_sum_sepconj; iFrame.
    i. ss.
  Qed.

  Lemma list_prop_sum_persistent A (P: A -> iProp) l
        (PERSIST: forall a, Persistent (P a))
    :
    (list_prop_sum P l) -∗ (□ list_prop_sum P l).
  Proof.
    induction l.
    { iIntros "_". ss. }
    ss. iIntros "[#P Ps]".
    iApply intuitionistically_sep_2. iSplitL "P".
    - iModIntro. auto.
    - iApply IHl; iFrame.
  Qed.

  Global Program Instance Persistent_list_prop_sum
         A (P: A -> iProp) l (PERSIST: forall a, Persistent (P a)) : Persistent (list_prop_sum P l).
  Next Obligation.
  Proof.
    intros. iIntros "Ps". iPoseProof (list_prop_sum_persistent with "Ps") as "Ps". auto.
  Qed.

  Lemma list_map_forall2 A B (f: A -> B)
        l
    :
    List.Forall2 (fun a b => b = f a) l (List.map f l).
  Proof.
    induction l; ss. econs; eauto.
  Qed.

  Lemma list_prop_sum_forall2 A B
        (R: A -> B -> Prop)
        (P: A -> iProp) (Q: B -> iProp)
        la lb
        (FORALL: List.Forall2 R la lb)
        (IMPL: forall a b (INA: List.In a la) (INB: List.In b lb),
            R a b -> P a ⊢ Q b)
    :
    (list_prop_sum P la)
      -∗
      (list_prop_sum Q lb).
  Proof.
    revert IMPL. induction FORALL; i; ss.
    iIntros "[HD TL]". iSplitL "HD".
    { iApply (IMPL with "HD"); auto. }
    { iApply (IHFORALL with "TL"). auto. }
  Qed.

  Lemma list_prop_sum_or_cases_l
        A (P0 P1: A -> iProp) l
    :
    (list_prop_sum (fun a => (P0 a ∨ P1 a)) l)
      -∗
      ((list_prop_sum P0 l) ∨ (∃ a, (⌜List.In a l⌝) ∗ (P1 a))).
  Proof.
    induction l.
    { iIntros "_". iLeft. ss. }
    ss. iIntros "[[C0|C1] SUM]".
    - iPoseProof (IHl with "SUM") as "[S0|S1]". iLeft; iFrame.
      iRight. iDestruct "S1" as "[% [%IN P1]]". iExists a0. iFrame. iPureIntro. auto.
    - iRight. iExists a. iFrame. iPureIntro. auto.
  Qed.

  Lemma list_prop_sum_or_cases_r
        A (P0 P1: A -> iProp) l
    :
    (list_prop_sum (fun a => (P0 a ∨ P1 a)) l)
      -∗
      ((list_prop_sum P1 l) ∨ (∃ a, (⌜List.In a l⌝) ∗ (P0 a))).
  Proof.
    iIntros "SUM". iApply list_prop_sum_or_cases_l. iApply list_prop_sum_impl. 2: iFrame.
    i. iIntros "[C0|C1]"; iFrame.
  Qed.

  Lemma list_prop_sum_pull_bupd
        Q
        A (P: A -> iProp) l
    :
    (list_prop_sum (fun a => #=( Q )=> P a) l)
      -∗
      #=( Q )=>(list_prop_sum P l).
  Proof.
    induction l.
    { iIntros "_". ss. }
    ss. iIntros "[PA SUM]". iSplitL "PA"; iFrame. iApply IHl. iFrame.
  Qed.

  Lemma list_prop_sum_pull_bupd_default
        A (P: A -> iProp) l
    :
    (list_prop_sum (fun a => #=> P a) l)
      -∗
      #=>(list_prop_sum P l).
  Proof.
    induction l.
    { iIntros "_". ss. }
    ss. iIntros "[PA SUM]". iSplitL "PA"; iFrame. iApply IHl. iFrame.
  Qed.

  Lemma list_prop_sum_in_split
        A (P: A -> iProp) l a
        (IN: In a l)
    :
    (list_prop_sum (fun a => P a) l)
      -∗ ((P a) ∗ ((P a) -∗ (list_prop_sum (fun a => P a) l))).
  Proof.
    iIntros "SUM". apply in_split in IN. des. rewrite cons_middle in IN. clarify.
    iPoseProof (list_prop_sum_split with "SUM") as "[SL SR]".
    iPoseProof (list_prop_sum_split with "SR") as "[SM SR]".
    iSplitL "SM". ss. iDestruct "SM" as "[PA _]". iFrame.
    iIntros "PA".
    iAssert (list_prop_sum (fun a0 => P a0) (a :: (l1 ++ l2)))%I with "[SL SR PA]" as "SP".
    { ss. iFrame. iApply list_prop_sum_combine. iFrame. }
    iApply (list_prop_sum_perm with "SP"). rewrite app_assoc. rewrite app_comm_cons.
    apply Permutation_app_tail. apply Permutation_cons_append.
  Qed.

  Lemma list_prop_sum_map
        A (P0: A -> iProp)
        B (P1: B -> iProp)
        l (f: A -> B)
        (MAP: forall a, (P0 a) -∗ (P1 (f a)))
    :
    (list_prop_sum P0 l)
      -∗
      (list_prop_sum P1 (List.map f l)).
  Proof.
    induction l; ss.
    iIntros "[HD TL]". iSplitL "HD".
    { iApply (MAP with "HD"). }
    { iApply (IHl with "TL"). }
  Qed.

  Lemma list_prop_sum_map_inv
        A (P0: A -> iProp)
        B (P1: B -> iProp)
        l (f: A -> B)
        (MAP: forall a, (P1 (f a)) -∗ (P0 a))
    :
    (list_prop_sum P1 (List.map f l))
      -∗
    (list_prop_sum P0 l).
  Proof.
    induction l; ss.
    iIntros "[HD TL]". iSplitL "HD".
    { iApply (MAP with "HD"). }
    { iApply (IHl with "TL"). }
  Qed.

  Definition natmap_prop_sum A (f: NatMap.t A) (P: nat -> A -> iProp) :=
    list_prop_sum (fun '(k, v) => P k v) (NatMap.elements f).

  Lemma natmap_prop_sum_empty A P
    :
    ⊢ natmap_prop_sum (NatMap.empty A) P.
  Proof.
    unfold natmap_prop_sum. ss. auto.
  Qed.

  Lemma natmap_prop_remove_find A (f: NatMap.t A) P k v
        (FIND: NatMap.find k f = Some v)
    :
    (natmap_prop_sum f P)
      -∗
      (P k v ** natmap_prop_sum (NatMap.remove k f) P).
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

  Lemma natmap_prop_sum_wand (A: Type) P0 P1 (m: NatMap.t A)
    :
    (natmap_prop_sum m P0)
      -∗
      (natmap_prop_sum m (fun k v => P0 k v -* P1 k v))
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
        (IMPL: forall k v, P0 k v ** Q ⊢ P1 k v ** Q)
    :
    (natmap_prop_sum m P0 ** Q)
      -∗
      (natmap_prop_sum m P1 ** Q).
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
    i. ss.
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
  Variable A: Type.
  Context `{NATMAPRA: @GRA.inG (Auth.t (NatMapRAFOS.t A)) Σ}.

  Lemma NatMapRA_find_some m k a
    :
    (OwnM (Auth.black (Some m: NatMapRAFOS.t A)))
      -∗
      (OwnM (Auth.white (NatMapRAFOS.singleton k a: NatMapRAFOS.t A)))
      -∗
      (⌜NatMap.find k m = Some a⌝).
  Proof.
    iIntros "B W". iCombine "B W" as "BW". iOwnWf "BW".
    eapply Auth.auth_included in H. eapply NatMapRAFOS.extends_singleton_iff in H. auto.
  Qed.

  Lemma NatMapRA_singleton_unique k0 k1 a0 a1
    :
    (OwnM (Auth.white (NatMapRAFOS.singleton k0 a0: NatMapRAFOS.t A)))
      -∗
      (OwnM (Auth.white (NatMapRAFOS.singleton k1 a1: NatMapRAFOS.t A)))
      -∗
      (⌜k0 <> k1⌝).
  Proof.
    iIntros "W0 W1". iCombine "W0 W1" as "W". iOwnWf "W".
    ur in H. eapply NatMapRAFOS.singleton_unique in H. auto.
  Qed.

  Lemma NatMapRA_remove m k a
    :
    (OwnM (Auth.black (Some m: NatMapRAFOS.t A)))
      -∗
      (OwnM (Auth.white (NatMapRAFOS.singleton k a: NatMapRAFOS.t A)))
      -∗
      #=>(OwnM (Auth.black (Some (NatMap.remove k m): NatMapRAFOS.t A))).
  Proof.
    iIntros "B W". iCombine "B W" as "BW". iApply OwnM_Upd. 2: iFrame.
    eapply Auth.auth_dealloc. eapply NatMapRAFOS.remove_local_update.
  Qed.

  Lemma NatMapRA_add m k a
        (NONE: NatMap.find k m = None)
    :
    (OwnM (Auth.black (Some m: NatMapRAFOS.t A)))
      -∗
      #=>((OwnM (Auth.black (Some (NatMap.add k a m): NatMapRAFOS.t A)
                            ⋅ Auth.white (NatMapRAFOS.singleton k a: NatMapRAFOS.t A)))
         ).
  Proof.
    iIntros "B". iApply OwnM_Upd. 2: iFrame.
    eapply Auth.auth_alloc. eapply NatMapRAFOS.add_local_update. auto.
  Qed.

End UPDNATMAP.
