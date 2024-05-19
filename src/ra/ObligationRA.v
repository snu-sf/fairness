From sflib Require Import sflib.
From Fairness Require Import WFLibLarge Mod Optics.
From Fairness Require Import PCM IProp IPM IPropAux.
From Fairness Require Import NatMapRALarge MonotoneRA RegionRA.
Require Import Coq.Classes.RelationClasses.
(* Require Import Coq.Logic.PropExtensionality. *)
From Fairness Require Import Axioms.
Require Import Program.
From Fairness Require Import FairnessRA IndexedInvariants.
From Ordinal Require Export Ordinal Arithmetic Hessenberg ClassicalHessenberg.

Set Implicit Arguments.

Module CounterRA.
  Section MONOID.
    Variable (A: Type).
    Context `{OrderedCM.t A}.

    Record partition :=
      mk {
          collection:> A -> Prop;
          closed: forall a0 a1 (LE: OrderedCM.le a0 a1),
            collection a1 -> collection a0;
        }.

    Lemma partition_ext (p0 p1: partition)
          (EXT: forall a, p0 a <-> p1 a)
      :
      p0 = p1.
    Proof.
      destruct p0, p1. assert (collection0 = collection1).
      { extensionality a. eapply propositional_extensionality. ss. }
      { subst. f_equal. apply proof_irrelevance. }
    Qed.

    Program Definition partition_join (p0 p1: partition): partition :=
      mk (fun a => p0 a /\ p1 a) _.
    Next Obligation.
      split.
      { eapply closed; eauto. }
      { eapply closed; eauto. }
    Qed.

    Program Definition partition_top: partition :=
      mk (fun _ => True) _.

    Program Definition partition_from_monoid (a: A): partition :=
      mk (fun a' => OrderedCM.le a' a) _.
    Next Obligation.
      etrans; eauto.
    Qed.

    Definition car: Type :=
      partition * (@Fuel.quotient A _).

    Definition add: car -> car -> car :=
      fun '(s0, q0) '(s1, q1) =>
        (partition_join s0 s1, Fuel.quotient_add q0 q1).

    Definition wf: car -> Prop :=
      fun '(s, q) =>
        exists a, Fuel.collection q a /\ s a.

    Definition core: car -> car :=
      fun '(s, q) => (s, Fuel.from_monoid OrderedCM.unit).

    Definition unit: car :=
      (partition_top, Fuel.from_monoid OrderedCM.unit).

    Global Program Instance t: URA.t := {
        car := car;
        unit := unit;
        _add := add;
        _wf := wf;
        core := core;
      }
    .
    Next Obligation.
    Proof.
      unfold add. des_ifs. f_equal.
      { apply partition_ext. i. ss. split; i; des; auto. }
      { apply Fuel.quotient_add_comm. }
    Qed.
    Next Obligation.
    Proof.
      unfold add. des_ifs. f_equal.
      { apply partition_ext. i. ss. split; i; des; auto. }
      { apply Fuel.quotient_add_assoc. }
    Qed.
    Next Obligation.
    Proof.
      unseal "ra". unfold add, unit. des_ifs. f_equal.
      { apply partition_ext. i. ss. split; i; des; auto. }
      { hexploit (Fuel.from_monoid_exist q). i. des. subst.
        rewrite Fuel.from_monoid_add.
        apply Fuel.from_monoid_eq. eapply OrderedCM.add_unit_eq_l.
      }
    Qed.
    Next Obligation.
    Proof.
      unseal "ra". ss. splits; auto. exists OrderedCM.unit.
      rewrite Fuel.from_monoid_le. splits; auto. reflexivity.
    Qed.
    Next Obligation.
    Proof.
      unseal "ra". unfold add, wf in *. des_ifs. des.
      hexploit (Fuel.from_monoid_exist q). i. des. subst.
      hexploit (Fuel.from_monoid_exist q1). i. des. subst.
      rewrite Fuel.from_monoid_add in H0.
      rewrite Fuel.from_monoid_le in H0. esplits; eauto.
      { rewrite Fuel.from_monoid_le. etrans; eauto.
        apply OrderedCM.add_base_l.
      }
      { ss. des. auto. }
    Qed.
    Next Obligation.
    Proof.
      unseal "ra". unfold add. des_ifs. ss. clarify. f_equal.
      { apply partition_ext. i. ss. split; i; des; auto. }
      { hexploit (Fuel.from_monoid_exist q0). i. des. subst.
        rewrite Fuel.from_monoid_add.
        apply Fuel.from_monoid_eq. apply OrderedCM.add_unit_eq_r.
      }
    Qed.
    Next Obligation.
    Proof.
      unfold core. des_ifs.
    Qed.
    Next Obligation.
    Proof.
      unseal "ra". unfold add. des_ifs. ss. clarify.
      eexists (_, _). f_equal.
      rewrite Fuel.from_monoid_add.
      apply Fuel.from_monoid_eq. symmetry. apply OrderedCM.add_unit_eq_r.
    Qed.

    Definition black (a: A): car :=
      (partition_from_monoid a, Fuel.from_monoid OrderedCM.unit).

    Definition white (a: A): car :=
      (partition_top, Fuel.from_monoid a).

    Lemma black_persistent a
      :
      URA.core (black a) = black a.
    Proof.
      ss.
    Qed.

    Lemma black_mon a0 a1
          (LE: OrderedCM.le a0 a1)
      :
      URA.extends (black a1) (black a0).
    Proof.
      exists (black a0).
      ur. unfold black. f_equal.
      { apply partition_ext. i. ss. split; i; des; auto.
        split; auto. etrans; eauto.
      }
      { rewrite Fuel.from_monoid_add.
        apply Fuel.from_monoid_eq. apply OrderedCM.add_unit_eq_r.
      }
    Qed.

    Lemma white_mon a0 a1
          (LE: OrderedCM.le a0 a1)
      :
      URA.updatable (white a1) (white a0).
    Proof.
      ii. ur in H0. ur. des_ifs.
      hexploit (Fuel.from_monoid_exist q). i. des. subst.
      rewrite Fuel.from_monoid_add in *. ss. des.
      esplits; eauto.
      rewrite Fuel.from_monoid_le in H0.
      rewrite Fuel.from_monoid_le. etrans; eauto.
      apply OrderedCM.le_add_r; auto.
    Qed.

    Lemma white_eq a0 a1
          (LE: OrderedCM.eq a0 a1)
      :
      white a0 = white a1.
    Proof.
      unfold white. f_equal. apply Fuel.from_monoid_eq; auto.
    Qed.

    Lemma white_split a0 a1
      :
      white (OrderedCM.add a0 a1) = white a0 ⋅ white a1.
    Proof.
      ur. unfold white. f_equal.
      { apply partition_ext. i. ss. }
      { rewrite Fuel.from_monoid_add. auto. }
    Qed.

    Lemma black_white_wf a
      :
      URA.wf (black a ⋅ white a).
    Proof.
      ur. exists a. rewrite Fuel.from_monoid_add. splits; auto.
      { rewrite Fuel.from_monoid_le. apply OrderedCM.add_unit_le_r. }
      { reflexivity. }
    Qed.

    Lemma black_white_decr a0 a1
      :
      URA.updatable_set (black a0 ⋅ white a1) (fun r => exists a2, r = black a2 /\ OrderedCM.le (OrderedCM.add a2 a1) a0).
    Proof.
      ii. ur in WF. ss. des_ifs.
      hexploit (Fuel.from_monoid_exist q). i. des. subst. ss. des.
      rewrite ! Fuel.from_monoid_add in *.
      rewrite Fuel.from_monoid_le in WF.
      eexists (_, _). esplits.
      { reflexivity. }
      { instantiate (1:=a). etrans; eauto.
        etrans; eauto. etrans.
        { eapply OrderedCM.add_comm_le. }
        { apply OrderedCM.le_add_r. apply OrderedCM.add_base_r. }
      }
      { ur. esplits.
        { rewrite Fuel.from_monoid_add. rewrite Fuel.from_monoid_le.
          eapply OrderedCM.add_unit_le_r.
        }
        { reflexivity. }
        { eapply closed; eauto. etrans; eauto.
          eapply OrderedCM.add_base_r.
        }
      }
    Qed.

    Lemma black_white_compare a0 a1
          (WF: URA.wf (black a0 ⋅ white a1))
      :
      OrderedCM.le a1 a0.
    Proof.
      exploit black_white_decr.
      { rewrite URA.unit_id. eauto. }
      i. des. etrans; eauto. apply OrderedCM.add_base_r.
    Qed.
  End MONOID.
End CounterRA.



Lemma ord_mult_split (n: nat)
  :
  ((Ord.omega ⊕ Ord.large × n) <= (Ord.large × (S n)))%ord.
Proof.
  rewrite Ord.from_nat_S.
  rewrite Jacobsthal.mult_S.
  apply Hessenberg.le_add_l.
  apply Ord.lt_le.
  rewrite Ord.omega_from_peano_lt_set.
  apply Ord.large_lt_from_wf_set.
Qed.

Module ObligationRA.
  Definition t: URA.t := @FiniteMap.t (URA.prod (@CounterRA.t Ord.t _) (OneShot.t unit)).
  Section RA.
    Context `{@GRA.inG t Σ}.

    Definition black (k: nat) (o: Ord.t): iProp :=
      OwnM (FiniteMap.singleton k ((CounterRA.black o: @CounterRA.t Ord.t _, ε: OneShot.t unit): URA.prod (@CounterRA.t Ord.t _) (OneShot.t unit))).

    Definition white (k: nat) (o: Ord.t): iProp :=
      OwnM (FiniteMap.singleton k ((CounterRA.white o: @CounterRA.t Ord.t _, ε: OneShot.t unit): URA.prod (@CounterRA.t Ord.t _) (OneShot.t unit))).

    Definition pending (k: nat) (q: Qp): iProp :=
      OwnM (FiniteMap.singleton k ((ε: @CounterRA.t Ord.t _, OneShot.pending unit q: OneShot.t unit): URA.prod (@CounterRA.t Ord.t _) (OneShot.t unit))).

    Definition shot (k: nat): iProp :=
      OwnM (FiniteMap.singleton k ((ε: @CounterRA.t Ord.t _, OneShot.shot tt: OneShot.t unit): URA.prod (@CounterRA.t Ord.t _) (OneShot.t unit))).

    Definition white_one k: iProp :=
      white k (Ord.S Ord.O).

    Lemma black_persistent k o
      :
      black k o -∗ □ black k o.
    Proof.
      iIntros "H".
      unfold black.
      iPoseProof (own_persistent with "H") as "H".
      rewrite FiniteMap.singleton_core. auto.
    Qed.

    Global Program Instance Persistent_black k o: Persistent (black k o).
    Next Obligation.
    Proof.
      i. iIntros "POS". iPoseProof (black_persistent with "POS") as "POS". auto.
    Qed.

    Lemma shot_persistent k
      :
      shot k -∗ □ shot k.
    Proof.
      iIntros "H".
      unfold black.
      iPoseProof (own_persistent with "H") as "H".
      rewrite FiniteMap.singleton_core. auto.
    Qed.

    Global Program Instance Persistent_shot k: Persistent (shot k).
    Next Obligation.
    Proof.
      i. iIntros "POS". ss. iPoseProof (shot_persistent with "POS") as "POS". auto.
    Qed.

    Lemma pending_shot k
      :
      (pending k 1)
        -∗
        #=> (shot k).
    Proof.
      iApply OwnM_Upd. eapply FiniteMap.singleton_updatable.
      apply URA.prod_updatable.
      { reflexivity. }
      { apply OneShot.pending_shot. }
    Qed.

    Lemma pending_not_shot k q
      :
      (pending k q)
        -∗
        (shot k)
        -∗
        False.
    Proof.
      iIntros "H0 H1". iCombine "H0 H1" as "H".
      iOwnWf "H". rewrite FiniteMap.singleton_add in H0.
      rewrite FiniteMap.singleton_wf in H0.
      ur in H0. des. exfalso. eapply OneShot.pending_not_shot; eauto.
    Qed.

    Lemma pending_sum k q0 q1
      :
      (pending k q0)
        -∗
        (pending k q1)
        -∗
        (pending k (q0 + q1)%Qp).
    Proof.
      iIntros "H0 H1". iCombine "H0 H1" as "H".
      rewrite FiniteMap.singleton_add.
      ur. rewrite URA.unit_id. ur. auto.
    Qed.

    Lemma pending_wf k q
      :
      (pending k q)
        -∗
        (⌜(q ≤ 1)%Qp⌝).
    Proof.
      iIntros "H". iOwnWf "H".
      rewrite FiniteMap.singleton_wf in H0. ur in H0. des.
      apply OneShot.pending_wf in H1. auto.
    Qed.

    Lemma pending_split k q0 q1
      :
      (pending k (q0 + q1)%Qp)
        -∗
        (pending k q0 ∗ pending k q1).
    Proof.
      iIntros "H".
      iPoseProof (OwnM_extends with "H") as "[H0 H1]"; [|iSplitL "H0"; [iApply "H0"|iApply "H1"]].
      { rewrite FiniteMap.singleton_add.
        rewrite OneShot.pending_sum. ur.
        rewrite URA.unit_id. ur. reflexivity.
      }
    Qed.

    Lemma alloc o
      :
      ⊢ #=> (∃ k, black k o ∗ white k o ∗ pending k 1).
    Proof.
      iPoseProof (@OwnM_unit _ _ H) as "H".
      iPoseProof (OwnM_Upd_set with "H") as "> H0".
      { eapply FiniteMap.singleton_alloc.
        instantiate (1:=((CounterRA.black o, ε): URA.prod (@CounterRA.t Ord.t _) (OneShot.t unit)) ⋅ ((CounterRA.white o, ε): URA.prod (@CounterRA.t Ord.t _) (OneShot.t unit)) ⋅ (ε, OneShot.pending unit 1)).
        repeat rewrite unfold_prod_add. repeat rewrite URA.unit_idl. repeat rewrite URA.unit_id.
        rewrite unfold_prod_wf. ss. split.
        { eapply CounterRA.black_white_wf. }
        { apply OneShot.pending_one_wf. }
      }
      iDestruct "H0" as "[% [% H0]]".
      des. subst. erewrite <- FiniteMap.singleton_add. erewrite <- FiniteMap.singleton_add.
      iDestruct "H0" as "[[H0 H1] H2]".
      iModIntro. iExists _. iFrame.
    Qed.

    Lemma black_mon o1 k o0
          (LE: Ord.le o0 o1)
      :
      black k o0 -∗ black k o1.
    Proof.
      iApply OwnM_extends. apply FiniteMap.singleton_extends.
      apply URA.prod_extends. split; [|reflexivity].
      apply CounterRA.black_mon. auto.
    Qed.

    Lemma white_mon o1 k o0
          (LE: Ord.le o0 o1)
      :
      white k o1 -∗ #=> white k o0.
    Proof.
      iApply OwnM_Upd. apply FiniteMap.singleton_updatable.
      apply URA.prod_updatable; [|reflexivity].
      apply CounterRA.white_mon. auto.
    Qed.

    Lemma white_eq o1 k o0
          (LE: Ord.eq o0 o1)
      :
      white k o0 -∗ white k o1.
    Proof.
      unfold white. erewrite CounterRA.white_eq; auto.
    Qed.

    Lemma white_merge k o0 o1
      :
      (white k o0)
        -∗
        (white k o1)
        -∗
        (white k (Hessenberg.add o0 o1)).
    Proof.
      iIntros "H0 H1". unfold white.
      replace (CounterRA.white (Hessenberg.add o0 o1): @CounterRA.t Ord.t ord_OrderedCM) with
        ((CounterRA.white o0: @CounterRA.t Ord.t _) ⋅ (CounterRA.white o1: @CounterRA.t Ord.t _)).
      { iCombine "H0 H1" as "H". rewrite FiniteMap.singleton_add.
        rewrite unfold_prod_add. rewrite URA.unit_id. auto.
      }
      { symmetry. eapply (@CounterRA.white_split Ord.t ord_OrderedCM o0 o1). }
    Qed.

    Lemma white_split_eq k o0 o1
      :
      (white k (Hessenberg.add o0 o1))
        -∗
        (white k o0 ∗ white k o1).
    Proof.
      iIntros "H". unfold white.
      replace (CounterRA.white (Hessenberg.add o0 o1): @CounterRA.t Ord.t ord_OrderedCM, ε: @OneShot.t unit) with
        (((CounterRA.white o0, ε): URA.prod (@CounterRA.t Ord.t _) (OneShot.t unit)) ⋅ ((CounterRA.white o1, ε): URA.prod (@CounterRA.t Ord.t _) (OneShot.t unit))).
      { rewrite <- FiniteMap.singleton_add. iDestruct "H" as "[H0 H1]". iFrame. }
      { rewrite unfold_prod_add. rewrite URA.unit_id. f_equal.
        symmetry. eapply (@CounterRA.white_split Ord.t ord_OrderedCM o0 o1).
      }
    Qed.

    Lemma white_split o0 o1 k o
          (LE: Ord.le (Hessenberg.add o0 o1) o)
      :
      (white k o)
        -∗
        (#=> (white k o0 ∗ white k o1)).
    Proof.
      iIntros "H". iPoseProof (white_mon with "H") as "> H"; eauto.
      iModIntro. iApply white_split_eq; auto.
    Qed.

    Lemma white_split_one o0 k o1
          (LT: Ord.lt o0 o1)
      :
      (white k o1)
        -∗
        (#=> (white k o0 ∗ white_one k)).
    Proof.
      iIntros "H". iApply white_split; eauto.
      rewrite Hessenberg.add_S_r. rewrite Hessenberg.add_O_r.
      apply Ord.S_supremum; auto.
    Qed.

    Lemma cut_white k n o
      :
      (white k (o × (S n))%ord)
        -∗
        (white k (o × n)%ord ∗ white k o).
    Proof.
      iIntros "WHITE".
      iApply (white_split_eq with "[WHITE]").
      iApply (white_eq with "WHITE").
      rewrite Ord.from_nat_S. rewrite Jacobsthal.mult_S.
      rewrite Hessenberg.add_comm. reflexivity.
    Qed.

    Lemma black_white_compare k o0 o1
      :
      (black k o0)
        -∗
        (white k o1)
        -∗
        ⌜Ord.le o1 o0⌝.
    Proof.
      iIntros "H0 H1".
      iCombine "H0 H1" as "H". rewrite FiniteMap.singleton_add.
      iOwnWf "H". iPureIntro.
      apply FiniteMap.singleton_wf in H0.
      rewrite ! unfold_prod_add in H0.
      rewrite unfold_prod_wf in H0. des. ss.
      apply CounterRA.black_white_compare in H0. auto.
    Qed.

    Lemma black_white_decr k o0 o1
      :
      (black k o0)
        -∗
        (white k o1)
        -∗
        (#=> ∃ o2, black k o2 ∗ ⌜Ord.le (Hessenberg.add o2 o1) o0⌝).
    Proof.
      iIntros "H0 H1".
      iCombine "H0 H1" as "H". rewrite FiniteMap.singleton_add.
      iPoseProof (OwnM_Upd_set with "H") as "> [% [% H]]".
      { eapply FiniteMap.singleton_updatable_set.
        rewrite unfold_prod_add. eapply URA.prod_updatable_set.
        { eapply CounterRA.black_white_decr. }
        { instantiate (1:=eq (ε ⋅ ε: OneShot.t unit)). ii. esplits; eauto. }
      }
      { ss. des. destruct m1. des; subst.
        rewrite URA.unit_id. iModIntro. iExists _. iFrame. eauto. }
    Qed.

    Lemma black_white_decr_one k o1
      :
      (black k o1)
        -∗
        (white_one k)
        -∗
        (#=> ∃ o0, black k o0 ∗ ⌜Ord.lt o0 o1⌝).
    Proof.
      iIntros "H0 H1".
      iPoseProof (black_white_decr with "H0 H1") as "> [% [H %]]".
      iModIntro. iExists _. iFrame. iPureIntro.
      eapply Ord.lt_le_lt; eauto.
      rewrite Hessenberg.add_S_r. rewrite Hessenberg.add_O_r.
      apply Ord.S_lt; auto.
    Qed.

    Lemma black_white_annihilate o_w0 k o_b1 o_w1
          (LT: Ord.lt o_w0 o_w1)
      :
      (black k o_b1)
        -∗
        (white k o_w1)
        -∗
        (#=> ∃ o_b0, black k o_b0 ∗ white k o_w0 ∗ ⌜Ord.lt o_b0 o_b1⌝).
    Proof.
      iIntros "H0 H1".
      iPoseProof (white_split_one with "H1") as "> [H1 H2]"; [eauto|].
      iPoseProof (black_white_decr_one with "H0 H2") as "> [% [H0 %]]".
      iModIntro. iExists _. iFrame. auto.
    Qed.
  End RA.

  Section EDGE.
    Context `{Σ: GRA.t}.
    Context `{@GRA.inG t Σ}.
    Context `{@GRA.inG (Region.t (nat * nat * Ord.t)) Σ}.


    Definition edge: (nat * nat * Ord.t) -> iProp :=
      fun '(k0, k1, c) => (∃ o, black k0 o ∗ white k1 (Jacobsthal.mult c o))%I.

    Definition edges_sat: iProp := Region.sat edge.

    Definition amplifier (k0 k1: nat) (c: Ord.t): iProp :=
      □ (∀ o, white k0 o -∗ #=(edges_sat)=> white k1 (Jacobsthal.mult c o)).

    Lemma amplifier_persistent k0 k1 c
      :
      amplifier k0 k1 c ⊢ □ amplifier k0 k1 c.
    Proof.
      iIntros "# H". auto.
    Qed.

    Global Program Instance Persistent_amplifier k0 k1 c: Persistent (amplifier k0 k1 c).

    Local Opaque IUpd.
    Lemma amplifier_mon k0 k1 c0 c1
          (LE: Ord.le c0 c1)
      :
      amplifier k0 k1 c1 ⊢ amplifier k0 k1 c0.
    Proof.
      iIntros "# H". iModIntro. iIntros "% WHITE".
      iPoseProof ("H" with "WHITE") as "> WHITE".
      iPoseProof (white_mon with "WHITE") as "> WHITE".
      {  eapply Jacobsthal.le_mult_l. eauto. }
      iModIntro. auto.
    Qed.

    Lemma amplifier_trans k0 k1 k2 c0 c1
      :
      (amplifier k0 k1 c0)
        -∗
        (amplifier k1 k2 c1)
        -∗
        (amplifier k0 k2 (Jacobsthal.mult c1 c0)).
    Proof.
      iIntros "# H0 # H1". iModIntro. iIntros "% WHITE".
      iPoseProof ("H0" with "WHITE") as "> WHITE".
      iPoseProof ("H1" with "WHITE") as "> WHITE".
      iPoseProof (white_mon with "WHITE") as "> WHITE".
      { rewrite <- ClassicJacobsthal.mult_assoc. reflexivity. }
      iModIntro. auto.
    Qed.

    Lemma amplifier_amplify k0 k1 c o
      :
      (amplifier k0 k1 c)
        -∗
        (white k0 o)
        -∗
        (#=(edges_sat)=> white k1 (Jacobsthal.mult c o)).
    Proof.
      iIntros "H0 H1".
      iPoseProof ("H0" with "H1") as "> H". iModIntro. auto.
    Qed.

    Local Transparent IUpd.
    Lemma amplifier_intro k0 k1 c o
      :
      (black k0 o)
        -∗
        (white k1 (Jacobsthal.mult c o))
        -∗
        (#=(edges_sat)=> amplifier k0 k1 c).
    Proof.
      iIntros "BLACK WHITE".
      iPoseProof (Region.alloc with "[BLACK WHITE]") as "H".
      { instantiate (1:=(k0, k1, c)). instantiate (1:=edge).
        ss. iExists _. iFrame.
      }
      iMod "H" as "[% # H]". iModIntro.
      unfold amplifier. iModIntro. iIntros "% WHITE".
      iApply (Region.update with "H [WHITE]").
      iIntros "[% [H0 H1]]".
      iPoseProof (black_white_decr with "H0 WHITE") as "> [% [H0 %]]".
      iPoseProof (white_mon with "H1") as "> H1".
      { rewrite <- Jacobsthal.le_mult_r; [|eauto].
        rewrite ClassicJacobsthal.mult_dist. reflexivity.
      }
      iPoseProof (white_split_eq with "H1") as "[H1 H2]".
      iFrame. iModIntro. iExists _. iFrame.
    Qed.

  End EDGE.


  Section ARROW.
    Variable (S: Type).
    Context `{@GRA.inG t Σ}.
    Context `{@GRA.inG (@FairRA.t S nat _) Σ}.
    Context `{@GRA.inG (@FiniteMap.t (OneShot.t unit)) Σ}.

    Local Notation index := nat.
    Context `{Vars : index -> Type}.
    Context `{Invs : @IInvSet Σ Vars}.
    Context `{@GRA.inG (@Regions.t _ (fun l => (S * nat * Ord.t * Qp * nat * (Vars l))%type)) Σ}.

    Section PRISM.

    Variable (Id: Type).
    Variable (v: index).
    Local Notation Var := (Vars v).
    Variable (p: Prism.t S Id).

    Definition arrow: (S * nat * Ord.t * Qp * nat * Var) -> iProp :=
      fun '(i, k, c, q, x, f) =>
        ((□ (prop _ f -∗ □ (prop _ f)))
           ∗
           ((OwnM (FiniteMap.singleton x (OneShot.shot tt)) ∗ shot k ∗ (prop _ f))
            ∨
              (∃ n, (FairRA.black Prism.id i n q)
                      ∗ white k (Jacobsthal.mult c (Ord.from_nat n)))))%I.

    Definition arrows_sat: iProp := Regions.sat _ arrow.

    Definition correl (i: Id) (k: nat) (c: Ord.t) (f : Var): iProp :=
      (∃ r q x, Regions.white _ r (Prism.review p i, k, c, q, x, f))%I.

    (* Definition correl (i: Id) (k: nat) (c: Ord.t) (F : iProp): iProp := *)
    (*   (∃ (f : Var), (⌜prop _ f = F⌝) ∗ _correl i k c f)%I. *)

    Lemma correl_persistent i k c F
      :
      correl i k c F ⊢ □ correl i k c F.
    Proof.
      iIntros "# H". auto.
    Qed.

    Global Program Instance Persistent_correl i k c F: Persistent (correl i k c F).

    Local Transparent IUpd.
    Lemma correl_correlate_gen i k c f n
      :
      (correl i k c f)
        -∗
        (FairRA.white p i n)
        -∗
        (#=(arrows_sat)=>
           ((□ (prop _ f -∗ □ (prop _ f)))
              ∗
              ((white k (Jacobsthal.mult c (Ord.from_nat n)))
            ∨
              (shot k ∗ (□ prop _ f))))).
    Proof.
      iIntros "[% [% [% WHITE]]] H".
      iApply (Regions.update with "WHITE [H]").
      iIntros "[#PERS [[OWN [#SHOT PROP]]|[% [BLACK WHITE]]]]".
      { iModIntro. iPoseProof ("PERS" with "PROP") as "#F". iSplitL.
        { iSplitR. auto. iLeft. iFrame. auto. }
        { iSplit. auto. iRight. subst. auto. }
      }
      { iPoseProof (FairRA.decr_update with "BLACK H") as "> [% [H %]]".
        iPoseProof (white_split with "WHITE") as "> [WHITE0 WHITE1]".
        { ss. apply OrdArith.le_from_nat in H3.
          rewrite Hessenberg.add_from_nat in H3. rewrite <- H3.
          rewrite ClassicJacobsthal.mult_dist. reflexivity.
        }
        iModIntro. iSplitR "WHITE0".
        { iSplitR. auto. iRight. iExists _. iFrame. }
        { iSplit. auto. iLeft. auto. }
      }
    Qed.

    Lemma correl_correlate i k c f
      :
      (correl i k c f)
        -∗
        (FairRA.white p i 1)
        -∗
        (#=(arrows_sat)=> white k c ∨ (shot k ∗ □ prop _ f)).
    Proof.
      iIntros "CORR WHITE".
      iPoseProof (correl_correlate_gen with "CORR WHITE") as "> [_ [H|H]]"; auto.
      iModIntro. iLeft. iApply white_eq; eauto.
      apply Jacobsthal.mult_1_r.
    Qed.


    Definition duty_list (i: Id) (rs: list (nat * (nat * Ord.t * Qp * nat * Var))) (q: Qp): iProp :=
      (list_prop_sum (fun '(r, (k, c, q, x, f)) =>
                        ((Regions.white _ r (Prism.review p i, k, c, q, x, f))
                           ∗
                           (OwnM ((FiniteMap.singleton x (OneShot.pending unit 1%Qp)))))%I) rs)
        ∗
        (⌜(fold_right (fun '(r, (k, c, q0, x, f)) q1 => (q0 + q1)%Qp) q rs = 1%Qp)⌝)
    .

    Lemma duty_list_nil i
      :
      ⊢ duty_list i [] 1%Qp.
    Proof.
      unfold duty_list. iSplit; ss.
    Qed.

    Lemma duty_list_fold i tl (q0: Qp) r k c (q1: Qp) x f
      :
      (duty_list i tl (q0 + q1)%Qp)
        -∗
        (Regions.white _ r (Prism.review p i, k, c, q1, x, f))
        -∗
        (OwnM ((FiniteMap.singleton x (OneShot.pending unit 1))))
        -∗
        (duty_list i ((r, (k, c, q1, x, f))::tl) q0).
    Proof.
      iIntros "[DUTY %] WHITE OWN". des. iSplit.
      { ss. iFrame. }
      iPureIntro. ss. rewrite <- H3.
      clear H3. revert q0 q1. induction tl.
      { i. ss. rewrite Qp.add_comm. auto. }
      { i. ss. destruct a as [? [[[[? ?] ?] ?] ?]]. rewrite <- IHtl.
        rewrite Qp.add_assoc. rewrite Qp.add_assoc. f_equal.
        apply Qp.add_comm.
      }
    Qed.

    Lemma duty_list_unfold i tl (q0: Qp) r k c (q1: Qp) x f
      :
      (duty_list i ((r, (k, c, q1, x, f))::tl) q0)
        -∗
        (Regions.white _ r (Prism.review p i, k, c, q1, x, f) ∗ OwnM ((FiniteMap.singleton x (OneShot.pending unit 1))) ∗ duty_list i tl (q0 + q1)%Qp).
    Proof.
      iIntros "[DUTY %]". ss.
      iPoseProof "DUTY" as "[[WHITE OWN] DUTY]". iFrame.
      iPureIntro. rewrite <- H3.
      clear H3. revert q0 q1. induction tl.
      { i. ss. apply Qp.add_comm. }
      { i. ss. destruct a as [? [[[[? ?] ?] ?] ?]]. rewrite IHtl.
        rewrite Qp.add_assoc. rewrite Qp.add_assoc. f_equal.
        apply Qp.add_comm.
      }
    Qed.

    Lemma duty_list_permutation i rs0 rs1 q
          (PERM: Permutation rs0 rs1)
      :
      (duty_list i rs0 q)
        -∗
        (duty_list i rs1 q).
    Proof.
      revert q. rr in PERM.
      pattern rs0, rs1. revert rs0 rs1 PERM. eapply Permutation_ind_bis.
      { iIntros. ss. }
      { i. iIntros "DUTY". destruct x as [? [[[[? ?] ?] ?] ?]].
        iPoseProof (duty_list_unfold with "DUTY") as "[WHITE [OWN DUTY]]".
        iPoseProof (H4 with "DUTY") as "DUTY".
        iApply (duty_list_fold with "DUTY WHITE OWN").
      }
      { i. iIntros "DUTY".
        destruct x as [? [[[[? ?] ?] ?] ?]]. destruct y as [? [[[[? ?] ?] ?] ?]].
        iPoseProof (duty_list_unfold with "DUTY") as "[WHITE0 [OWN0 DUTY]]".
        iPoseProof (duty_list_unfold with "DUTY") as "[WHITE1 [OWN1 DUTY]]".
        iPoseProof (H4 with "DUTY") as "DUTY".
        iApply (duty_list_fold with "[DUTY WHITE0 OWN0] WHITE1 OWN1").
        replace (q + q1 + q0)%Qp with ((q + q0) + q1)%Qp.
        2:{ rewrite <- Qp.add_assoc. rewrite <- Qp.add_assoc. f_equal. apply Qp.add_comm. }
        iApply (duty_list_fold with "DUTY WHITE0 OWN0").
      }
      { i. iIntros "DUTY". iApply H6. iApply H4. auto. }
    Qed.

    Definition duty (i: Id) (l: list (nat * Ord.t * Var)): iProp :=
      ∃ (rs: list (nat * (nat * Ord.t * Qp * nat * Var))) (q: Qp),
        (FairRA.black_ex p i q)
          ∗
          (duty_list i rs q)
          ∗
          (⌜List.map (fun '(r, (k, c, q, x, f)) => (k, c, f)) rs = l⌝)
    .

    Lemma duty_permutation i l0 l1
          (PERM: Permutation l0 l1)
      :
      (duty i l0)
        -∗
        (duty i l1).
    Proof.
      iIntros "[% [% [BLACK [DUTY %]]]]".
      assert (exists rs1, List.map (fun '(r, (k, c, q, x, f)) => (k, c, f)) rs1 = l1 /\ Permutation rs rs1).
      { revert rs H3. pattern l0, l1. revert l0 l1 PERM.
        eapply Permutation_ind_bis; i; ss.
        { destruct rs; ss. exists []. ss. }
        { destruct rs; ss. des_ifs. hexploit H4; eauto. i. des.
          rewrite <- H5. eexists ((_, (_, _, _, _, _))::_). ss. esplits; eauto.
        }
        { destruct rs; ss. destruct rs; ss. des_ifs. hexploit H4; eauto. i. des.
          rewrite <- H5. eexists ((_, (_, _, _, _, _))::(_, (_, _, _, _, _))::_).
          ss. esplits; eauto. rewrite H6. eapply perm_swap.
        }
        { hexploit H4; eauto. i. des.
          hexploit H6; eauto. i. des. esplits; eauto. etrans; eauto.
        }
      }
      des. subst.
      iPoseProof (duty_list_permutation with "DUTY") as "DUTY"; [eauto|].
      iExists _, _. iFrame. eauto.
    Qed.

    Lemma duty_list_white_list i rs q
      :
      (duty_list i rs q)
        -∗
        □ (list_prop_sum (fun '(r, (k, c, q, x, f)) =>
                            (Regions.white _ r (Prism.review p i, k, c, q, x, f))) rs).
    Proof.
      revert q. induction rs.
      { i. iIntros. iModIntro. ss. }
      i. iIntros "DUTY". destruct a as [? [[[[? ?] ?] ?] ?]].
      iPoseProof (duty_list_unfold with "DUTY") as "[#WHITE [OWN DUTY]]".
      iPoseProof (IHrs with "DUTY") as "# WHITES". iClear "OWN DUTY".
      iModIntro. ss. iFrame. iSplit; auto.
    Qed.

    Lemma duty_list_whites i rs q
      :
      (duty_list i rs q)
        -∗
        □ (∀ r k c q x f (IN: List.In (r, (k, c, q, x, f)) rs),
              Regions.white _ r (Prism.review p i, k, c, q, x, f)).
    Proof.
      iIntros "H".
      iPoseProof (duty_list_white_list with "H") as "# WHITES".
      iClear "H". iModIntro. iStopProof. induction rs.
      { iIntros "# WHITES" (? ? ? ? ? ? ?). ss. }
      iIntros "# WHITES" (? ? ? ? ? ? ?). ss.
      destruct a as [? [[[[? ?] ?] ?] ?]]. iPoseProof "WHITES" as "[WHITE WHITES0]".
      des; clarify. iApply IHrs; auto.
    Qed.

    Lemma duty_correl i l k c f
          (IN: List.In (k, c, f) l)
      :
      (duty i l)
        -∗
        (correl i k c f).
    Proof.
      iIntros "[% [% [BLACK [DUTY %]]]]".
      subst. eapply in_map_iff in IN. des. des_ifs.
      iPoseProof (duty_list_whites with "DUTY") as "# WHITES".
      iExists _, _, _. iApply "WHITES". iPureIntro. eauto.
    Qed.

    Lemma duty_done i l k c f
      :
      (duty i ((k, c, f)::l))
        -∗
        (shot k)
        -∗
        (prop _ f)
        -∗
        #=(arrows_sat)=> (duty i l).
    Proof.
      iIntros "[% [% [BLACK [DUTY %]]]] SHOT PROP".
      destruct rs; ss. des_ifs.
      iPoseProof (duty_list_unfold with "DUTY") as "[WHITE [OWN DUTY]]".
      iPoseProof (Regions.update with "WHITE [SHOT OWN PROP]") as "> BLACKF".
      { iIntros "[#PERS [[DONE [_ _]]|[% [BLACK WHITE]]]]".
        { iCombine "OWN DONE" as "FALSE".
          rewrite FiniteMap.singleton_add. iOwnWf "FALSE".
          rewrite FiniteMap.singleton_wf in H3.
          apply OneShot.pending_not_shot in H3. ss.
        }
        iPoseProof (OwnM_Upd with "OWN") as "> OWN".
        { apply FiniteMap.singleton_updatable. apply OneShot.pending_shot. }
        iModIntro. iSplitR "BLACK".
        { iSplitR. auto. iLeft. iFrame. }
        { instantiate (1:=FairRA.black_ex p i q0).
          iExists _. iApply "BLACK".
        }
      }
      iModIntro. iExists _, _. iSplitR "DUTY".
      { iApply (FairRA.black_ex_sum with "BLACK BLACKF"). }
      iSplit; [|auto]. iFrame.
    Qed.

    Lemma duty_alloc k c f i l
      :
      (duty i l)
        -∗
        (white k (Jacobsthal.mult c Ord.omega))
        -∗
        (□ (prop _ f -∗ □ prop _ f))
        -∗
        #=(arrows_sat)=> (duty i ((k, c, f)::l)).
    Proof.
      iIntros "[% [% [BLACK [DUTY %]]]] SHOT #PERS".
      iPoseProof (FairRA.black_ex_split with "[BLACK]") as "[BLACK0 [% BLACK1]]".
      { rewrite Qp.div_2. iFrame. }
      iPoseProof (@OwnM_ura_unit (@FiniteMap.t (OneShot.t unit))) as "H".
      iPoseProof (OwnM_Upd_set with "H") as "> [% [% OWN]]".
      { eapply FiniteMap.singleton_alloc. eapply OneShot.pending_one_wf. }
      ss. des. subst.
      iPoseProof (white_mon with "SHOT") as "> SHOT".
      { eapply Jacobsthal.le_mult_r.
        eapply Ord.lt_le. apply Ord.omega_upperbound.
      }
      iPoseProof (Regions.alloc with "[SHOT BLACK1]") as "> [% WHITE]".
      { instantiate (1:=(Prism.review p i, k, c, (q / 2)%Qp, k0, f)). iSplit. auto.
        iRight. iExists _. iFrame.
      }
      { iModIntro. iExists _, _. iFrame. iSplit.
        { iApply (duty_list_fold with "[DUTY] WHITE OWN"). rewrite Qp.div_2. eauto. }
        iPureIntro. ss.
      }
    Qed.

    Lemma duty_to_black i
      :
      (duty i [])
        -∗
        FairRA.black_ex p i 1%Qp.
    Proof.
      iIntros "[% [% [H0 [[H1 %] %]]]]". destruct rs; ss. subst. auto.
    Qed.

    Lemma black_to_duty i
      :
      (FairRA.black_ex p i 1%Qp)
        -∗
        (duty i []).
    Proof.
      iIntros "H". iExists _, _. iFrame. iSplit.
      { iSplit.
        { iApply list_prop_sum_nil. }
        { auto. }
      }
      { auto. }
    Qed.


    Definition tax (l: list (nat * Ord.t)): iProp :=
      list_prop_sum (fun '(k, c) => white k (Jacobsthal.mult c Ord.omega)) l.

    Definition taxes (l: list (nat * Ord.t)) (o: Ord.t): iProp :=
      list_prop_sum (fun '(k, c) => white k ((Jacobsthal.mult c Ord.omega) × o)%ord) l.

    Lemma tax_perm l0 l1
          (PERM: Permutation l0 l1)
      :
      tax l0 ⊢ tax l1.
    Proof.
      apply list_prop_sum_perm; auto.
    Qed.

    Lemma tax_nil
      :
      ⊢ tax [].
    Proof.
      apply list_prop_sum_nil.
    Qed.

    Lemma tax_cons_fold k c tl
      :
      (white k (Jacobsthal.mult c Ord.omega) ∗ tax tl)
        -∗
        (tax ((k, c)::tl)).
    Proof.
      ss.
    Qed.

    Lemma tax_cons_unfold k c tl
      :
      (tax ((k, c)::tl))
        -∗
        (white k (Jacobsthal.mult c Ord.omega) ∗ tax tl).
    Proof.
      ss.
    Qed.

    Lemma tax_split l0 l1
      :
      (tax (l0 ++ l1))
        -∗
        (tax l0 ∗ tax l1).
    Proof.
      apply list_prop_sum_split.
    Qed.

    Lemma tax_combine l0 l1
      :
      (tax l0 ∗ tax l1)
        -∗
        (tax (l0 ++ l1)).
    Proof.
      apply list_prop_sum_combine.
    Qed.

    Lemma taxes_perm l0 l1 o
          (PERM: Permutation l0 l1)
      :
      taxes l0 o ⊢ taxes l1 o.
    Proof.
      apply list_prop_sum_perm; auto.
    Qed.

    Lemma taxes_nil o
      :
      ⊢ taxes [] o.
    Proof.
      apply list_prop_sum_nil.
    Qed.

    Lemma taxes_cons_fold k c tl o
      :
      (white k ((c × Ord.omega) × o)%ord ∗ (taxes tl o))
        -∗
        (taxes ((k, c)::tl) o).
    Proof.
      ss.
    Qed.

    Lemma taxes_cons_unfold k c tl o
      :
      (taxes ((k, c)::tl) o)
        -∗
        (white k ((c × Ord.omega) × o)%ord ∗ taxes tl o).
    Proof.
      ss.
    Qed.

    Lemma taxes_split l0 l1 o
      :
      (taxes (l0 ++ l1) o)
        -∗
        (taxes l0 o ∗ taxes l1 o).
    Proof.
      apply list_prop_sum_split.
    Qed.

    Lemma taxes_combine l0 l1 o
      :
      (taxes l0 o ∗ taxes l1 o)
        -∗
        (taxes (l0 ++ l1) o).
    Proof.
      apply list_prop_sum_combine.
    Qed.

    Lemma taxes_ord_mon l o0 o1
          (LE: Ord.le o0 o1)
      :
      taxes l o1 ⊢ #=> taxes l o0.
    Proof.
      revert_until l. induction l; i.
      { iIntros "H". iModIntro. iApply taxes_nil. }
      iIntros "H". destruct a as [k o].
      iPoseProof (taxes_cons_unfold with "H") as "[W TX]".
      iPoseProof (IHl with "TX") as "IH".
      { eauto. }
      iPoseProof (white_mon with "W") as "W".
      { instantiate (1:=((o × Ord.omega) × o0)%ord).
        apply Jacobsthal.le_mult_r. auto.
      }
      iMod "W". iMod "IH".
      iPoseProof (taxes_cons_fold with "[W IH]") as "A".
      { iFrame. }
      iModIntro. iFrame.
    Qed.

    Lemma taxes_ord_split_eq l o0 o1
      :
      taxes l (o0 ⊕ o1)%ord ⊢ taxes l o0 ∗ taxes l o1.
    Proof.
      revert_until l. induction l; i.
      { iIntros "H". iPoseProof taxes_nil as "TN". iFrame. }
      iIntros "H". destruct a as [k o].
      iPoseProof (taxes_cons_unfold with "H") as "[W TX]".
      iPoseProof (IHl with "TX") as "[IH1 IH2]".
      iPoseProof (white_eq with "W") as "W".
      { rewrite ClassicJacobsthal.mult_dist. reflexivity. }
      iPoseProof (white_split_eq with "W") as "[W1 W2]".
      iSplitL "IH1 W1".
      { iApply taxes_cons_fold. iFrame. }
      { iApply taxes_cons_fold. iFrame. }
      Unshelve. exact o0.
    Qed.

    Lemma taxes_ord_split l o o0 o1
          (LE: ((o0 ⊕ o1) <= o)%ord)
      :
      taxes l o ⊢ #=> (taxes l o0 ∗ taxes l o1).
    Proof.
      iIntros "T". iPoseProof (taxes_ord_mon with "T") as "T". eauto.
      iMod "T". iModIntro. iApply taxes_ord_split_eq. auto.
    Qed.

    Lemma tax_is_single_taxes l
      :
      tax l ⊢ taxes l (Ord.S Ord.O).
    Proof.
      induction l.
      { iIntros. iApply taxes_nil. }
      iIntros "T". destruct a as [k o].
      iPoseProof (tax_cons_unfold with "T") as "[W T]".
      iApply taxes_cons_fold.
      iPoseProof (white_eq with "W") as "W".
      { rewrite <- Jacobsthal.mult_1_r. reflexivity. }
      iFrame. iApply IHl. auto.
    Qed.

    Lemma taxes_single_is_tax l
      :
      taxes l (Ord.S Ord.O) ⊢ tax l.
    Proof.
      induction l.
      { iIntros. iApply tax_nil. }
      iIntros "T". destruct a as [k o].
      iPoseProof (taxes_cons_unfold with "T") as "[W T]".
      iApply tax_cons_fold.
      iPoseProof (white_eq with "W") as "W".
      { rewrite Jacobsthal.mult_1_r. reflexivity. }
      iFrame. iApply IHl. auto.
    Qed.

    Lemma taxes_ord_split_one l o0 o1
          (LT: (o0 < o1)%ord)
      :
      taxes l o1 ⊢ #=> (taxes l o0 ∗ tax l).
    Proof.
      iIntros "T". iPoseProof (taxes_ord_split with "T") as "T".
      { dup LT. eapply Ord.S_supremum in LT0.
        assert (REP: (o0 == (Ord.O ⊕ o0))%ord).
        { symmetry. apply Hessenberg.add_O_l. }
        etrans. 2: eapply LT0. rewrite REP.
        rewrite <- Hessenberg.add_S_l. reflexivity.
      }
      iMod "T". iDestruct "T" as "[T1 T2]".
      iModIntro. iFrame. iApply taxes_single_is_tax. auto.
    Qed.

    Lemma taxes_ord_merge l o0 o1
      :
      taxes l o0 ∗ taxes l o1 ⊢ taxes l (o0 ⊕ o1)%ord.
    Proof.
      revert_until l. induction l; i.
      { iIntros "H". iPoseProof taxes_nil as "TN". eauto. }
      iIntros "[H1 H2]". destruct a as [k o].
      iPoseProof (taxes_cons_unfold with "H1") as "[W1 TX1]".
      iPoseProof (taxes_cons_unfold with "H2") as "[W2 TX2]".
      iApply taxes_cons_fold. iSplitR "TX1 TX2"; cycle 1.
      { iApply IHl. iFrame. }
      iApply white_eq.
      { rewrite ClassicJacobsthal.mult_dist. reflexivity. }
      iApply (white_merge with "W1 W2").
    Qed.



    Lemma duty_list_pending P i rs q
          (IMPL: P ⊢ duty_list i rs q)
      :
      (P)
        -∗
        (P ∧ (∀ r k c q x f (IN: List.In (r, (k, c, q, x, f)) rs), OwnM ((FiniteMap.singleton x (OneShot.pending unit 1))))).
    Proof.
      revert P q IMPL. induction rs.
      { i. iIntros "H". iSplit; ss. iIntros. ss. }
      i. destruct a as [? [[[[? ?] ?] ?] ?]].
      ss. iIntros "DUTY".
      iPoseProof (IHrs with "DUTY") as "DUTY".
      { etrans; eauto. iIntros "DUTY".
        iPoseProof (duty_list_unfold with "DUTY") as "[#WHITE [OWN DUTY]]". eauto.
      }
      iSplit.
      { iDestruct "DUTY" as "[DUTY _]". auto. }
      iIntros. des; clarify.
      { iDestruct "DUTY" as "[DUTY _]". iPoseProof (IMPL with "DUTY") as "DUTY".
        iPoseProof (duty_list_unfold with "DUTY") as "[#WHITE [OWN DUTY]]". eauto.
      }
      { iDestruct "DUTY" as "[_ DUTY]". iApply "DUTY". eauto. }
    Qed.

    Lemma duty_list_disjoint P i0 rs0 q0 i1 rs1 q1
          (IMPL: P ⊢ (duty_list i0 rs0 q0 ∗ duty_list i1 rs1 q1))
      :
      (P)
        -∗
        #=(arrows_sat)=> (P ∗ ⌜forall r (IN0: List.In r (List.map fst rs0)) (IN1: List.In r (List.map fst rs1)), False⌝).
    Proof.
      iIntros "DUTY".
      iPoseProof (duty_list_whites with "[DUTY]") as "# WHITES0".
      { iPoseProof (IMPL with "DUTY") as "[DUTY0 DUTY1]". iApply "DUTY0". }
      iPoseProof (duty_list_whites with "[DUTY]") as "# WHITES1".
      { iPoseProof (IMPL with "DUTY") as "[DUTY0 DUTY1]". iApply "DUTY1". }
      iIntros "H".
      iAssert (⌜forall r v0 v1 (IN0: In (r, v0) rs0) (IN1: In (r, v1) rs1), v0 = v1⌝)%I as "%".
      { iIntros (? ? ? ? ?).
        destruct a0 as [[[[? ?] ?] ?] ?]. destruct a1 as [[[[? ?] ?] ?] ?].
        iDestruct "H" as "[% [H SAT]]".
        iPoseProof (Regions.white_agree with "[] []") as "%".
        { iApply "WHITES0". eauto. }
        { iApply "WHITES1". eauto. }
        clarify.
      }
      iAssert (P ∧ ((∀ r k c q x f (IN0: List.In (r, (k, c, q, x, f)) rs0), OwnM ((FiniteMap.singleton x (OneShot.pending unit 1)))) ∗ (∀ r k c q x f (IN: List.In (r, (k, c, q, x, f)) rs1), OwnM ((FiniteMap.singleton x (OneShot.pending unit 1))))))%I with "[DUTY]" as "DUTY".
      { iSplit; [auto|]. iPoseProof (IMPL with "DUTY") as "[DUTY0 DUTY1]".
        iSplitL "DUTY0".
        { iPoseProof (duty_list_pending with "DUTY0") as "[_ DUTY0]"; eauto. }
        { iPoseProof (duty_list_pending with "DUTY1") as "[_ DUTY1]"; eauto. }
      }
      iModIntro. iFrame. iSplit.
      { iPoseProof "DUTY" as "[DUTY _]"; auto. }
      { iPoseProof "DUTY" as "[_ [OWN0 OWN1]]".
        iIntros (? ? ?).
        apply in_map_iff in a0. des. destruct x as [? [[[[? ?] ?] ?] ?]].
        apply in_map_iff in a1. des. destruct x as [? [[[[? ?] ?] ?] ?]].
        ss. subst.
        hexploit H3; eauto. i. clarify.
        iPoseProof ("OWN0" $! _ _ _ _ _ _ a2) as "OWN0".
        iPoseProof ("OWN1" $! _ _ _ _ _ _ a3) as "OWN1".
        iCombine "OWN0 OWN1" as "OWN". iOwnWf "OWN".
        rewrite FiniteMap.singleton_add in H4.
        apply FiniteMap.singleton_wf in H4.
        rewrite <- OneShot.pending_sum in H4.
        apply OneShot.pending_wf in H4. apply Qp.not_add_le_r in H4. ss.
      }
    Qed.

    Lemma duty_list_nodup P i rs q
          (IMPL: P ⊢ (duty_list i rs q))
      :
      (P)
        -∗
        #=(arrows_sat)=> ((P) ∗ ⌜List.NoDup (List.map fst rs)⌝).
    Proof.
      revert q P IMPL. induction rs.
      { i. iIntros "H". iModIntro. iSplit; ss. iPureIntro. econs; ss. }
      i. destruct a as [? [[[[? ?] ?] ?] ?]].
      ss. iIntros "DUTY".
      iPoseProof (IHrs with "DUTY") as "> [DUTY %]".
      { etrans; eauto. iIntros "DUTY".
        iPoseProof (duty_list_unfold with "DUTY") as "[#WHITE [OWN DUTY]]". eauto.
      }
      iPoseProof (duty_list_whites with "[DUTY]") as "# WHITES".
      { iApply IMPL. auto. }
      iIntros "H".
      iAssert (⌜forall r k c q x f (IN: List.In (r, (k, c, q, x, f)) rs), n <> r⌝)%I as "%".
      { iIntros (? ? ? ? ? ? IN ?). subst.
        iPoseProof (IMPL with "DUTY") as "DUTY".
        iPoseProof (duty_list_unfold with "DUTY") as "[WHITE [PENDING DUTY]]". eauto.
        iPoseProof "H" as "[% [H _]]".
        iPoseProof (Regions.white_agree with "[] WHITE") as "%".
        { iApply "WHITES". iPureIntro. ss. eauto. }
        clarify. iPoseProof ("WHITES" $! _ _ _ _ _ _ (or_intror IN)) as "# WHITE1".
        iAssert (OwnM (FiniteMap.singleton n1 (OneShot.pending unit 1))) with "[DUTY]" as "OWN1".
        { iClear "WHITE1 WHITES". clear IHrs H3 IMPL.
          iStopProof. generalize (q + q0)%Qp. revert IN. induction rs; ss.
          { i. destruct a0 as [? [[[[? ?] ?] ?] ?]].
            iIntros "H". iPoseProof (duty_list_unfold with "H") as "[_ [OWN DUTY]]".
            des; clarify. iApply IHrs; eauto.
          }
        }
        iCombine "PENDING OWN1" as "OWN". iOwnWf "OWN".
        rewrite FiniteMap.singleton_add in H4.
        rewrite FiniteMap.singleton_wf in H4.
        rewrite <- OneShot.pending_sum in H4.
        apply OneShot.pending_wf in H4. apply Qp.not_add_le_r in H4. ss.
      }
      iSplitL "H".
      { eauto. }
      iModIntro. iSplit; auto.
      iPureIntro. econs; ss. ii. eapply in_map_iff in H5.
      des. destruct x as [? [[[[? ?] ?] ?] ?]]. ss. subst. eapply H4; eauto.
    Qed.

    Lemma duty_update n i l
      :
      (duty i l)
        -∗
        (tax (map fst l))
        -∗
        #=(arrows_sat)=> (duty i l ∗ FairRA.white p i n).
    Proof.
      iIntros "[% [% [BLACK [DUTY %]]]] TAX". subst.
      iPoseProof (duty_list_nodup with "DUTY") as "> [DUTY %]".
      { reflexivity. }
      iPoseProof (duty_list_whites with "DUTY") as "# WHITES".
      iApply (Regions.updates with "[]").
      { instantiate (1:=List.map (fun '(r, (k, c, q, x, f)) => (r, (Prism.review p i, k, c, q, x, f))) rs).
        rewrite List.map_map. erewrite List.map_ext; [eauto|]. i. des_ifs.
      }
      { iIntros. apply in_map_iff in IN. des. des_ifs. iApply "WHITES". auto. }
      iIntros "SAT".
      iAssert (duty_list i rs q ∗ FairRA.black_ex p i 1%Qp ∗ (foldr (fun '(_, (_, _, _, _, f)) P => (□ (prop _ f -∗ □ prop _ f)) ∗ P) True%I rs))%I with "[DUTY BLACK SAT]" as "[DUTY [BLACK PERSS]]".
      { iClear "WHITES". iStopProof. clear H3. revert q. induction rs.
        { ss. i. iIntros "[[DUTY %] [BLACK _]]". ss. subst. iFrame. auto. }
        i. destruct a as [? [[[[? ?] ?] ?] ?]].
        iIntros "[DUTY [BLACK SAT]]". ss.
        iPoseProof (duty_list_unfold with "DUTY") as "[WHITE [OWN DUTY]]".
        iDestruct "SAT" as "[[#PERS [[SHOT _]|[% [BLACK1 SAT]]]] SATS]".
        { iExFalso. iCombine "OWN SHOT" as "OWN". iOwnWf "OWN".
          rewrite FiniteMap.singleton_add in H3.
          rewrite FiniteMap.singleton_wf in H3.
          apply OneShot.pending_not_shot in H3. ss.
        }
        iPoseProof (IHrs with "[DUTY BLACK BLACK1 SATS]") as "[DUTY [BLACK PERSS]]".
        { iSplitL "DUTY"; [eauto|]. iSplitL "BLACK BLACK1"; [|auto].
          iApply (FairRA.black_ex_sum with "BLACK"). iExists _. iFrame.
        }
        iSplitR "BLACK PERSS".
        { iApply (duty_list_fold with "DUTY WHITE OWN"). }
        { iFrame. auto. }
      }
      iPoseProof (FairRA.success_ex_update with "BLACK") as "> [[% BLACK] WHITE]".
      iFrame.
      iAssert (⌜(fold_right (fun '(r, (k, c, q0, x, f)) q1 => (q0 + q1)%Qp) q rs = 1%Qp)⌝)%I as "%".
      { iPoseProof "DUTY" as "[DUTY %]". auto. }
      iAssert (#=> (Region.sat_list
                      arrow
                      (List.map snd (List.map (fun '(r, (k, c, q0, x, f)) => (r, (Prism.review p i, k, c, q0, x, f))) rs)) ∗ FairRA.black p i a q)) with "[TAX BLACK PERSS]" as "> [REGION BLACK]".
      2:{ iModIntro. iFrame. iExists _, _. iFrame. iSplit; eauto. iExists _. iFrame. }
      rewrite <- H4. iStopProof. clear H3 H4. revert q. induction rs.
      { i. iIntros "[# WHITES [TAX [BLACK PERSS]]]". iModIntro. ss. iFrame. }
      { i. iIntros "[# WHITES [TAX [BLACK PERSS]]]". ss.
        destruct a0 as [? [[[[? ?] ?] ?] ?]]. ss.
        iPoseProof "TAX" as "[WHITE TAX]".
        replace (q0 + foldr (fun '(_, (_, _, q1, _, _)) q2 => (q1 + q2)%Qp) q rs)%Qp with (q + foldr (fun '(_, (_, _, q1, _, _)) q2 => (q1 + q2)%Qp) q0 rs)%Qp; cycle 1.
        { clear IHrs. revert q q0. induction rs; ss; i.
          { apply Qp.add_comm. }
          { destruct a0 as [? [[[[? ?] ?] ?] ?]].
            rewrite (IHrs q1 q0). rewrite (IHrs q1 q).
            rewrite Qp.add_assoc. rewrite Qp.add_assoc.
            f_equal. apply Qp.add_comm.
          }
        }
        iPoseProof (FairRA.black_split with "BLACK") as "[BLACK0 BLACK1]".
        iDestruct "PERSS" as "[#PERS PERSS]".
        iPoseProof (IHrs with "[TAX BLACK1 PERSS]") as "> [REGION BLACK1]".
        { iSplit.
          { iClear "TAX BLACK1". iModIntro. iIntros.
            iApply "WHITES". eauto.
          }
          iFrame.
        }
        iFrame. iSplitR; [auto|]. iRight. iExists _. iFrame. iApply (white_mon with "WHITE").
        apply Jacobsthal.le_mult_r. eapply Ord.lt_le. eapply Ord.omega_upperbound.
      }
    Qed.

    Lemma duty_list_updating i rs q
      :
      (duty_list i rs q)
        -∗
        (FairRA.black_ex p i q)
        -∗
        (list_prop_sum (fun '(r, (k, c, q, x, f)) => white k (c × Ord.omega)%ord) rs)
        -∗
        #=(arrows_sat)=>
            (updating
               (@Regions.sat_list _ (fun l => (S * nat * Ord.t * Qp * nat * (Vars l))%type) _ _ arrow (List.map snd (List.map (fun '(r, (k, c, q, x, f)) => (r, (Prism.review p i, k, c, q, x, f))) rs)))
               (FairRA.black_ex p i 1)
               (FairRA.black_ex p i 1)
               (duty_list i rs q ∗ FairRA.black_ex p i q)).
    Proof.
      iIntros "DUTY BLACK TAX".
      iPoseProof (duty_list_nodup with "DUTY") as "> [DUTY %]".
      { reflexivity. }
      iPoseProof (duty_list_whites with "DUTY") as "# WHITES".
      iIntros "SAT". iModIntro.
      iSplitL "SAT"; [auto|]. iIntros "SAT".
      iAssert (duty_list i rs q ∗ FairRA.black_ex p i 1%Qp ∗ (foldr (fun '(_, (_, _, _, _, f)) P => (□ (prop _ f -∗ □ prop _ f)) ∗ P) True%I rs))%I with "[DUTY BLACK SAT]" as "[DUTY [BLACK PERSS]]".
      { iClear "WHITES". iStopProof. clear H3. revert q. induction rs.
        { ss. i. iIntros "[[DUTY %] [BLACK _]]". ss. subst. iFrame. auto. }
        i. destruct a as [? [[[[? ?] ?] ?] ?]].
        iIntros "[DUTY [BLACK SAT]]". ss.
        iPoseProof (duty_list_unfold with "DUTY") as "[WHITE [OWN DUTY]]".
        iDestruct "SAT" as "[[#PERS [[SHOT _]|[% [BLACK1 SAT]]]] SATS]".
        { iExFalso. iCombine "OWN SHOT" as "OWN". iOwnWf "OWN".
          rewrite FiniteMap.singleton_add in H3.
          rewrite FiniteMap.singleton_wf in H3.
          apply OneShot.pending_not_shot in H3. ss.
        }
        iPoseProof (IHrs with "[DUTY BLACK BLACK1 SATS]") as "[DUTY [BLACK PERSS]]".
        { iSplitL "DUTY"; [eauto|]. iSplitL "BLACK BLACK1"; [|auto].
          iApply (FairRA.black_ex_sum with "BLACK"). iExists _. iFrame.
        }
        iSplitR "BLACK PERSS".
        { iApply (duty_list_fold with "DUTY WHITE OWN"). }
        { iFrame. auto. }
      }
      iModIntro. iSplitL "BLACK"; [auto|].
      iAssert (⌜(fold_right (fun '(r, (k, c, q0, x, f)) q1 => (q0 + q1)%Qp) q rs = 1%Qp)⌝)%I as "%".
      { iPoseProof "DUTY" as "[DUTY %]". auto. }
      iIntros "[% BLACK]".
      iAssert (#=> (Region.sat_list
                      arrow
                      (List.map snd (List.map (fun '(r, (k, c, q0, x, f)) => (r, (Prism.review p i, k, c, q0, x, f))) rs)) ∗ FairRA.black p i a q)) with "[TAX BLACK PERSS]" as "> [REGION BLACK]".
      2:{ iModIntro. iFrame. iExists _. eauto. }
      rewrite <- H4. iStopProof. clear H3 H4. revert q. induction rs.
      { i. iIntros "[# WHITES [TAX [BLACK PERSS]]]". iModIntro. ss. iFrame. }
      { i. iIntros "[# WHITES [TAX [BLACK PERSS]]]". ss.
        destruct a0 as [? [[[[? ?] ?] ?] ?]]. ss.
        iPoseProof "TAX" as "[WHITE TAX]".
        replace (q0 + foldr (fun '(_, (_, _, q1, _, _)) q2 => (q1 + q2)%Qp) q rs)%Qp with (q + foldr (fun '(_, (_, _, q1, _, _)) q2 => (q1 + q2)%Qp) q0 rs)%Qp; cycle 1.
        { clear IHrs. revert q q0. induction rs; ss; i.
          { apply Qp.add_comm. }
          { destruct a0 as [? [[[[? ?] ?] ?] ?]].
            rewrite (IHrs q1 q0). rewrite (IHrs q1 q).
            rewrite Qp.add_assoc. rewrite Qp.add_assoc.
            f_equal. apply Qp.add_comm.
          }
        }
        iPoseProof (FairRA.black_split with "BLACK") as "[BLACK0 BLACK1]".
        iDestruct "PERSS" as "[#PERS PERSS]".
        iPoseProof (IHrs with "[TAX BLACK1 PERSS]") as "> [REGION BLACK1]".
        { iSplit.
          { iClear "TAX BLACK1". iModIntro. iIntros.
            iApply "WHITES". eauto.
          }
          iFrame.
        }
        iFrame. iSplitR. auto. iRight. iExists _. iFrame. iApply (white_mon with "WHITE").
        apply Jacobsthal.le_mult_r. eapply Ord.lt_le. eapply Ord.omega_upperbound.
      }
    Qed.

    Lemma list_app_disjoint_nodup A (l0 l1: list A)
          (NODUP0: List.NoDup l0)
          (NODUP1: List.NoDup l1)
          (DISJOINT: forall a (IN0: List.In a l0) (IN1: List.In a l1), False)
      :
      List.NoDup (l0 ++ l1).
    Proof.
      revert NODUP0 DISJOINT. induction l0; ss; i. inv NODUP0. econs; eauto.
      ii. apply in_app_iff in H3. des; ss. eapply DISJOINT; eauto.
    Qed.

    Lemma duty_list_pers_props i rs q :
      duty_list i rs q ⊢
                #=(arrows_sat)=> (duty_list i rs q) ∗ □(foldr (λ '(_, (_, _, _, _, f)) P, (□(prop v f -∗ □ prop v f) ∗ P)%I) True%I rs).
    Proof.
      revert q. induction rs.
      { ss. i. iIntros "A". iModIntro. auto. }
      i. destruct a as [? [[[[? ?] ?] ?] ?]].
      iIntros "DUTY". iPoseProof (duty_list_unfold with "DUTY") as "[#WHITE [OWN DUTY]]".
      iMod (IHrs with "DUTY") as "[DUTY #TL]". clear IHrs.
      ss. iSplitL.
      { iModIntro. iApply (duty_list_fold with "DUTY [] [OWN]"). auto. iFrame. }
      iApply (Regions.update with "WHITE").
      iIntros "[#PERS SAT]". iModIntro. iFrame. auto.
    Qed.

    Lemma duties_updating os
      :
      (list_prop_sum (fun '(i, l) => duty i l ∗ tax (map fst l)) os)
        -∗
        #=(arrows_sat)=>
            (updating
               arrows_sat
               (FairRA.blacks_of p (List.map fst os))
               (FairRA.blacks_of p (List.map fst os))
               (list_prop_sum (fun '(i, l) => duty i l) os)).
    Proof.
      iIntros "DUTY".
      iAssert (∃ (xs: list (Id * list (nat * (nat * Ord.t * Qp * nat * Var)) * Qp)),
                  (⌜os = List.map (fun '(i, rs, q) => (i, List.map (fun '(r, (k, c, q, x, f)) => (k, c, f)) rs)) xs⌝)
                    ∗
                    (#=(arrows_sat)=> list_prop_sum (fun '(i, rs, q) =>
                                      (duty_list i rs q)
                                        ∗
                                        (list_prop_sum (fun '(r, (k, c, q, x, f)) => white k (c × Ord.omega)%ord) rs)
                                        ∗
                                        (FairRA.black_ex p i q)
                                        ∗
                                        (foldr (fun '(_, (_, _, _, _, f)) P => (□ (prop _ f -∗ □ prop _ f)) ∗ P) True%I rs)) xs))%I with "[DUTY]" as "[% [% >ALL]]".
      { iStopProof. induction os; ss; i.
        { iIntros. iExists []. ss. }
        { destruct a as [i l].
          iIntros "[[[% [% [BLACK [DUTY %]]]] TAX] OS]".
          iPoseProof (IHos with "OS") as "[% [% OS]]". subst.
          iExists ((_, _, _)::_). ss. iSplit.
          { iPureIntro. eauto. }
          iMod "OS".
          iPoseProof (duty_list_pers_props with "DUTY") as ">[DUTY #PERSS]".
          iFrame. iSplitL. 2: auto. clear IHos. iClear "PERSS". iStopProof. induction rs; ss.
          { auto. }
          destruct a as [? [[[[? ?] ?] ?] ?]].
          iIntros "TAX". iPoseProof (tax_cons_unfold with "TAX") as "[HD TL]".
          iPoseProof (IHrs with "TL") as "TL". iFrame. iFrame.
        }
      }
      subst.
      set (l := List.concat (List.map (fun '(i, rs, q) => List.map (fun '(r, (k, c, q, x, f)) => (r, (Prism.review p i, k, c, q, x, f))) rs) xs)).

      iAssert (#=(arrows_sat)=>
                 ((list_prop_sum (fun '(i, rs, q) =>
                                    (duty_list i rs q)
                                      ∗
                                      (list_prop_sum (fun '(r, (k, c, q, x, f)) => white k (c × Ord.omega)%ord) rs)
                                      ∗
                                      (FairRA.black_ex p i q)
                                      ∗
                                      (foldr (fun '(_, (_, _, _, _, f)) P => (□ (prop _ f -∗ □ prop _ f)) ∗ P) True%I rs)) xs)
                    ∗
                    (⌜List.NoDup (List.map fst l)⌝))%I) with "[ALL]" as "> [ALL %]".
      { subst l. iStopProof. induction xs; ss.
        { iIntros. iModIntro. iSplit; ss. iPureIntro. econs; ss. }
        destruct a as [[i rs] q]. iIntros "[[DUTY [HD BLACK]] TL]".
        iPoseProof (IHxs with "TL") as "> [TL %]".
        iPoseProof (duty_list_nodup with "DUTY") as "> [DUTY %]".
        { reflexivity. }
        iAssert (#=(arrows_sat)=>
                   (((duty_list i rs q)
                       ∗
                       (* (foldr (fun '(_, (_, _, _, _, f)) P => (□ (prop _ f -∗ □ prop _ f)) ∗ P) True%I rs) *)
                       (* ∗ *)
                       (list_prop_sum (fun '(i, rs, q) =>
                                         (duty_list i rs q)
                                           ∗
                                           (list_prop_sum (fun '(r, (k, c, q, x, f)) => white k (c × Ord.omega)%ord) rs)
                                           ∗
                                           (FairRA.black_ex p i q)
                                           ∗
                                           (foldr (fun '(_, (_, _, _, _, f)) P => (□ (prop _ f -∗ □ prop _ f)) ∗ P) True%I rs)) xs))
                      ∗
                      (⌜forall i0 rs0 q0 (IN: List.In (i0, rs0, q0) xs),
                            (forall r (IN0: List.In r (List.map fst rs)) (IN1: List.In r (List.map fst rs0)), False)⌝)))%I with "[DUTY TL]" as "> [[DUTY TL] %]".
        { clear IHxs H3 H4. iStopProof. induction xs; ss.
          { iIntros "[DUTY TL]". iModIntro. iSplit; auto. }
          destruct a as [[i0 rs0] q0].
          iIntros "[DUTY [HD TL]]".
          iPoseProof (IHxs with "[DUTY TL]") as "> [[DUTY TL] %]".
          { iFrame. }
          iCombine "HD DUTY" as "H".
          iPoseProof (duty_list_disjoint with "H") as "> [[HD DUTY] %]".
          { iIntros "[[[H0 X0] X1] H1]". iFrame. }
          iModIntro. iFrame. iPureIntro. i. des; clarify; eauto.
        }
        { iModIntro. iFrame. iPureIntro.
          rewrite List.map_app. apply list_app_disjoint_nodup; auto.
          { rewrite List.map_map. erewrite List.map_ext; eauto. i. des_ifs. }
          { i. rewrite List.concat_map in IN1.
            apply in_concat in IN1. des.
            rewrite List.map_map in IN1. rewrite List.in_map_iff in IN1. des. subst.
            rewrite List.in_map_iff in IN2. des. subst.
            destruct x0 as [[? ?] ?].
            rewrite List.in_map_iff in IN1. des. subst.
            destruct x0 as [? [[[[? ?] ?] ?] ?]]. ss.
            rewrite List.map_map in IN0.
            rewrite List.in_map_iff in IN0. des. subst.
            destruct x as [? [[[[? ?] ?] ?] ?]]. ss.
            eapply H5.
            { eauto. }
            { eapply in_map_iff. esplits; eauto. }
            { ss. eapply in_map_iff. esplits; eauto. ss. }
          }
        }
      }
      iAssert (#=(arrows_sat)=>
                 (((list_prop_sum (fun '(i, rs, q) =>
                                     (updating
                                        (@Regions.sat_list _ (fun l => (S * nat * Ord.t * Qp * nat * (Vars l))%type) _ _ arrow (List.map snd (List.map (fun '(r, (k, c, q, x, f)) => (r, (Prism.review p i, k, c, q, x, f))) rs)))
                                        (FairRA.black_ex p i 1)
                                        (FairRA.black_ex p i 1)
                                        (duty_list i rs q ∗ FairRA.black_ex p i q))%I)) xs)
                    ∗ (∀ i rs q0 r k c q1 x f
                         (IN0: List.In (i, rs, q0) xs)
                         (IN1: List.In (r, (k, c, q1, x, f)) rs),
                          @Regions.white _ (fun l => (S * nat * Ord.t * Qp * nat * (Vars l))%type) _ _ _ r (Prism.review p i, k, c, q1, x, f)))) with "[ALL]" as "> [ALL WHITES]".
      { subst l. iStopProof. clear H3. induction xs.
        { iIntros. iModIntro. ss. iSplit; auto. iIntros. ss. }
        destruct a as [[i rs] q]. iIntros "[[DUTY [TAX [BLACK PERSS]]] DUTIES]".
        iPoseProof (IHxs with "DUTIES") as "> [DUTIES WHITES]".
        iPoseProof (duty_list_whites with "DUTY") as "# WHITE".
        iPoseProof (duty_list_updating with "DUTY BLACK TAX") as "> UPD".
        iModIntro. iSplitL "DUTIES UPD".
        { ss. iFrame. }
        { iIntros. ss. des; clarify.
          { iApply "WHITE"; auto. }
          { iApply "WHITES"; auto. }
        }
      }
      iModIntro.
      iApply (Regions.sat_updating with "[WHITES] [ALL]").
      { instantiate (1:=l). subst l. auto. }
      { iIntros. subst l. apply List.in_concat in IN. des.
        apply in_map_iff in IN. des. destruct x0 as [[i rs] q]. subst.
        apply in_map_iff in IN0. des.
        destruct x as [? [[[[? ?] ?] ?] ?]]. clarify.
        iApply "WHITES"; eauto.
      }
      subst l. clear H3. iStopProof. induction xs.
      { ss. iIntros "_ SAT". iModIntro. ss. }
      destruct a as [[i rs] q]. ss.
      iIntros "[UPD UPDS]".
      iPoseProof (IHxs with "UPDS") as "UPDS".
      iIntros "SAT". repeat rewrite List.map_app.
      iPoseProof (Regions.sat_list_split with "SAT") as "[SAT SATS]".
      iPoseProof ("UPD" with "SAT") as "> [BLACK K]".
      iPoseProof ("UPDS" with "SATS") as "> [BLACKS KS]".
      iModIntro. iSplitL "BLACK BLACKS".
      { iApply list_prop_sum_cons_fold. iFrame. }
      iIntros "BLACKS".
      iPoseProof (list_prop_sum_cons_unfold with "BLACKS") as "[BLACK BLACKS]".
      iPoseProof ("K" with "BLACK") as "> [SAT [BLACK DUTY]]".
      iPoseProof ("KS" with "BLACKS") as "> [SATS DUTIES]".
      iModIntro. iSplitL "SAT SATS".
      { iCombine "SAT SATS" as "SATS".
        iPoseProof (Regions.sat_list_combine with "SATS") as "SATS". iFrame.
      }
      { iFrame. iExists _, _. iFrame. eauto. }
    Qed.

    End PRISM.

    Lemma duty_prism_id Id (p: Prism.t S Id) v i l
      :
      (duty p (v:=v) i l)
        -∗
        (duty Prism.id (v:=v) (Prism.review p i) l).
    Proof. auto. Qed.

    Lemma duty_prism_id_rev Id (p: Prism.t S Id) v i l
      :
      (duty Prism.id (v:=v) (Prism.review p i) l)
        -∗
        (duty p (v:=v) i l).
    Proof. auto. Qed.

    Section SATS.

      Definition arrows : forall i, (S * nat * Ord.t * Qp * nat * Vars i) -> iProp :=
        fun i => (fun x => @arrow i x).

      Definition arrows_sats j : iProp := @Regions.nsats _ Σ _ arrows j.

      Global Instance arrows_sats_elim_upd P Q b i j :
        ElimModal (i < j) b false (#=(arrows_sat i)=> P) P (#=(arrows_sats j)=> Q) (#=(arrows_sats j)=> Q).
      Proof.
        rewrite /ElimModal bi.intuitionistically_if_elim.
        iIntros (LT) "[P K]".
        iPoseProof (@Regions.nsats_sat_sub _ _ _ arrows _ _ LT) as "SUB".
        iCombine "SUB P" as "P". iMod "P".
        iApply "K". iFrame.
      Qed.

      Definition arrows_auth j : iProp :=
        OwnM (@Regions.nauth_ra (fun i => (S * nat * Ord.t * Qp * nat * Vars i)%type) j).

    End SATS.

    Section COLLECT.

      (* Variable (v: index). *)
      (* Local Notation Var := (Vars v). *)

      Definition collect_tax o : (nat * Ord.t) -> iProp :=
        fun '(k, c) => white k ((c × Ord.omega) × o)%ord.

      Definition collection_tax k o (l : list (nat * Ord.t)) :=
        (black k o ∗ Region.sat_list (collect_tax o) l)%I.

      Lemma collect_tax_split o k c :
        forall o0, (o0 < o)%ord ->
              collect_tax o (k, c) ⊢ #=> collect_tax o0 (k, c) ∗ white k (c × Ord.omega)%ord.
      Proof.
        iIntros (o0 LT) "C". unfold collect_tax.
        iMod (white_split ((c × Ord.omega) × o0)%ord ((c × Ord.omega) × (Ord.S Ord.O))%ord with "C") as "[C0 C1]".
        { rewrite <- ClassicJacobsthal.mult_dist. apply Jacobsthal.le_mult_r.
          rewrite Hessenberg.add_S_r. rewrite Hessenberg.add_O_r. apply Ord.S_supremum; auto.
        }
        iModIntro. iFrame. iApply white_eq. 2: iFrame.
        apply Jacobsthal.mult_1_r.
      Qed.

      Lemma collect_taxes_split o l :
        forall o0, (o0 < o)%ord ->
              Region.sat_list (collect_tax o) l ⊢ #=> Region.sat_list (collect_tax o0) l ∗ tax l.
      Proof.
        induction l; iIntros (o0 LT) "C".
        { ss. }
        ss. iDestruct "C" as "[T C]". iMod (IHl o0 LT with "C") as "[C T2]". iFrame.
        destruct a as [k c]. iApply collect_tax_split; eauto.
      Qed.

      Lemma collection_tax_decr k o l :
        (collection_tax k o l)
          -∗
          (white_one k)
          -∗
          (#=> ∃ o', collection_tax k o' l ∗ ⌜(o' < o)%ord⌝ ∗ tax l).
      Proof.
        iIntros "[B C] W". iMod (black_white_decr_one with "B W") as "[% [B2 %]]".
        iExists o0. iFrame. iMod (collect_taxes_split with "C") as "[C T]". eauto.
        iFrame. iPureIntro. auto.
      Qed.

    End COLLECT.

  End ARROW.

  Section ARROWTHREAD.
    Variable (S: Type).
    Context `{@GRA.inG t Σ}.
    Context `{@GRA.inG (FairRA.tgtt S) Σ}.
    Context `{@GRA.inG (@FiniteMap.t (OneShot.t unit)) Σ}.
    (* Context `{@GRA.inG (Region.t ((sum_tid S) * nat * Ord.t * Qp * nat)) Σ}. *)

    Local Notation index := nat.
    Context `{Vars : index -> Type}.
    Context `{Invs : @IInvSet Σ Vars}.
    Context `{@GRA.inG (@Regions.t _ (fun l => ((sum_tid S) * nat * Ord.t * Qp * nat * (Vars l))%type)) Σ}.

    Definition correl_thread v (k: nat) (c: Ord.t) (f : Vars v): iProp :=
      ∃ i, correl v inlp i k c f.

    Lemma correl_thread_persistent v k c f
      :
      @correl_thread v k c f ⊢ □ @correl_thread v k c f.
    Proof.
      iIntros "# H". auto.
    Qed.

    Global Program Instance Persistent_correl_thread v k c f: Persistent (@correl_thread v k c f).

    Lemma correl_thread_correlate v k c f
      :
      (@correl_thread v k c f)
        -∗
        (FairRA.white_thread (S := S))
        -∗
        (#=(arrows_sat (S := sum_tid S) v)=> (white k c ∨ (shot k ∗ □ prop _ f))).
    Proof.
      iIntros "[% CORR] WHITE". iApply (correl_correlate with "CORR WHITE").
    Qed.

    Lemma duty_correl_thread v i l k c f
          (IN: List.In (k, c, f) l)
      :
      (duty v inlp i l)
        -∗
        (@correl_thread v k c f).
    Proof.
      iIntros "DUTY".
      iPoseProof (duty_correl with "DUTY") as "# CORR"; [eauto|].
      iExists _. eauto.
    Qed.
  End ARROWTHREAD.


  Section TARGET.

    Variable (S: Type).
    Let Id := id_sum thread_id S.

    Context `{Σ: GRA.t}.
    Context `{@GRA.inG t Σ}.
    Context `{@GRA.inG (@FairRA.tgtt S) Σ}.
    Context `{@GRA.inG (@FiniteMap.t (OneShot.t unit)) Σ}.
    (* Context `{@GRA.inG (Region.t (Id * nat * Ord.t * Qp * nat)) Σ}. *)

    Local Notation index := nat.
    Context `{Vars : index -> Type}.
    Context `{Invs : @IInvSet Σ Vars}.
    Context `{@GRA.inG (@Regions.t _ (fun l => (Id * nat * Ord.t * Qp * nat * (Vars l))%type)) Σ}.

    Lemma IUpd_open I P
      :
      (#=(I)=> P)
        -∗
        I
        -∗
        (#=> (I ∗ P)).
    Proof.
      iIntros "H0 H1". iPoseProof ("H0" with "H1") as "H". auto.
    Qed.

    Lemma target_update_thread
          (tid: thread_id) v l
          ths
          (f0 f1: FairBeh.imap Id nat_wf)
          (UPD: fair_update f0 f1 (prism_fmap inlp (tids_fmap tid ths)))
      :
      (FairRA.sat_target f0 ths)
        -∗
        (duty v inlp tid l ∗ tax (map fst l))
        -∗
        (#=(arrows_sat (S := Id) v)=>
           ((FairRA.sat_target f1 ths)
              ∗
              (duty v inlp tid l)
              ∗
              FairRA.white_thread (S := S))).
    Proof.
      iIntros "SAT DUTY ARROWS".
      iPoseProof (duties_updating with "[DUTY]") as "UPD".
      { instantiate (1:=[(tid, l)]). ss. iFrame. }
      iPoseProof (IUpd_open with "UPD ARROWS") as "> [ARROWS UPD]".
      iPoseProof ("UPD" with "ARROWS") as "> [[BLACK _] K]".
      iPoseProof (FairRA.target_update_thread with "SAT BLACK") as "> [SAT [BLACK WHITE]]".
      { eauto. }
      iPoseProof ("K" with "[BLACK]") as "> [ARROWS [DUTY _]]".
      { iFrame. }
      iModIntro. iFrame.
    Qed.

    Lemma target_update A
          v lf ls ths
          (p: Prism.t S A)
          (f0 f1: FairBeh.imap Id nat_wf)
          (fm: Event.fmap A)
          (UPD: fair_update f0 f1 (prism_fmap (Prism.compose inrp p) fm))
          (SUCCESS: forall i (IN: fm i = Flag.success), List.In i (List.map fst ls))
          (FAIL: forall i (IN: List.In i lf), fm i = Flag.fail)
          (NODUP: List.NoDup lf)
      :
      (FairRA.sat_target f0 ths)
        -∗
        (list_prop_sum (fun '(i, l) => duty v (Prism.compose inrp p) i l ∗ tax (map fst l)) ls)
        -∗
        (#=(arrows_sat (S := Id) v)=>
           ((FairRA.sat_target f1 ths)
              ∗
              (list_prop_sum (fun '(i, l) => duty v (Prism.compose inrp p) i l) ls)
              ∗
              (list_prop_sum (fun i => FairRA.white (Prism.compose inrp p) i 1) lf))).
    Proof.
      iIntros "SAT DUTY ARROWS".
      iPoseProof (duties_updating with "[DUTY]") as "UPD".
      { instantiate (1:=ls).
        clear SUCCESS. iStopProof.
        induction ls; ss.
      }
      iPoseProof (IUpd_open with "UPD ARROWS") as "> [ARROWS K]".
      iPoseProof ("K" with "ARROWS") as "> [BLACKS K]".
      iPoseProof (FairRA.target_update with "SAT [BLACKS]") as "> [SAT [BLACKS WHITES]]".
      { rewrite prism_fmap_compose in UPD. eauto. }
      { instantiate (1:=List.map (Prism.review p) (List.map fst ls)).
        i. unfold prism_fmap in IN. des_ifs.
        hexploit SUCCESS; eauto. i.
        eapply Prism.review_preview in Heq. subst.
        eapply in_map in H3. eauto.
      }
      { instantiate (1:=List.map (Prism.review p) lf).
        i. eapply in_map_iff in IN. des. subst.
        unfold prism_fmap. rewrite Prism.preview_review. eauto.
      }
      { eapply FinFun.Injective_map_NoDup; eauto.
        ii. eapply f_equal with (f:=Prism.preview p) in H3.
        rewrite ! Prism.preview_review in H3. clarify.
      }
      { clear SUCCESS. iStopProof.
        induction ls; ss. destruct a. ss. unfold FairRA.blacks_of. ss.
        iIntros "[HD TL]". iFrame. iApply IHls. auto.
      }
      iPoseProof ("K" with "[BLACKS]") as "> [ARROWS DUTY]".
      { clear SUCCESS. iStopProof.
        induction ls; ss. destruct a. iIntros "[HD TL]".
        iFrame. iApply IHls. auto.
      }
      iModIntro. iFrame.
      iApply (list_prop_sum_map_inv with "WHITES").
      i. iIntros "WHITE". iApply FairRA.white_prism_id_rev. auto.
    Qed.
  End TARGET.

End ObligationRA.
