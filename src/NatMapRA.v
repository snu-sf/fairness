From sflib Require Import sflib.
Require Import Coq.Classes.RelationClasses.
From Fairness Require Import Axioms NatStructs.
From Fairness Require Import PCM.
Require Import String Lia Program.

Set Implicit Arguments.

Module NatMapRA.
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
End NatMapRA.
