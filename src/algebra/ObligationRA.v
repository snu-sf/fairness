From iris.algebra Require Import cmra updates.
From sflib Require Import sflib.
From Fairness Require Import WFLibLarge Mod Optics.
From Fairness Require Import PCM IPM IPropAux.
From Fairness Require Import RegionRA.
Require Import Coq.Classes.RelationClasses.
(* Require Import Coq.Logic.PropExtensionality. *)
From Fairness Require Import Axioms.
Require Import Program.
From Fairness Require Import FairnessRA IndexedInvariants.
From Ordinal Require Export Ordinal Arithmetic Hessenberg ClassicalHessenberg.

Set Implicit Arguments.

Local Instance frame_exist_instantiate_disabled :
FrameInstantiateExistDisabled := {}.

Module CounterRA.
  Section MONOID.
    Context {A: Type}.
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

    Record car: Type := mk_car {
      elem :> partition * (@Fuel.quotient A _);
    }.

    Definition add: car -> car -> car :=
      fun '{| elem := (s0, q0) |} '{| elem := (s1, q1) |} =>
        mk_car (partition_join s0 s1, Fuel.quotient_add q0 q1).

    Definition wf: car -> Prop :=
      fun '{| elem := (s, q) |} =>
        exists a, Fuel.collection q a /\ s a.

    Definition core: car -> option car :=
      fun '{| elem := (s, q) |} => Some (mk_car (s, Fuel.from_monoid OrderedCM.unit)).

    Definition unit: car :=
      mk_car (partition_top, Fuel.from_monoid OrderedCM.unit).

    Canonical Structure CounterO := leibnizO car.

    Local Instance counter_valid_instance : Valid car := wf.
    Local Instance counter_pcore_instance : PCore car := core.
    Local Instance counter_op_instance : Op car := add.
    Local Instance counter_unit_instance : Unit car := unit.

    Lemma valid_unfold om : ✓ om ↔ wf om.
    Proof. done. Qed.
    Lemma op_unfold p q : p ⋅ q = add p q.
    Proof. done. Qed.
    Lemma pcore_unfold p : pcore p = (core p).
    Proof. done. Qed.
    Lemma unit_unfold : ε = unit.
    Proof. done. Qed.

    Definition mixin : RAMixin car.
    Proof.
      split; try apply _; try done.
      all: fold_leibniz.
      all: try apply _; try done.
      - intros ??? -> ->. eauto.
      - intros a b c. fold_leibniz.
        rewrite !op_unfold /add.
        des_ifs. do 2 f_equal.
        { apply partition_ext. i. ss. split; i; des; auto. }
        { apply Fuel.quotient_add_assoc. }
      - intros a b. fold_leibniz.
        rewrite !op_unfold /add.
        des_ifs. do 2 f_equal.
        { apply partition_ext. i. ss. split; i; des; auto. }
        { apply Fuel.quotient_add_comm. }
      - intros [[]] [[]].
        rewrite !pcore_unfold /core /unit.
        injection 1. intros <- <-.
        rewrite !op_unfold /add. do 2 f_equal.
        { apply partition_ext. i. ss. split; i; des; auto. }
        { hexploit (Fuel.from_monoid_exist q). i. des. subst.
          rewrite Fuel.from_monoid_add.
          apply Fuel.from_monoid_eq. eapply OrderedCM.add_unit_eq_r.
        }
      - intros [[]] [[]].
        rewrite !pcore_unfold /core /unit.
        injection 1. intros <- <-. done.
      - intros [[]] [[]] [[]] LE.
        destruct LE as [[[]] EQ].
        rewrite op_unfold /add in EQ.
        injection EQ. intros -> ->.
        rewrite pcore_unfold /core.
        injection 1. intros <- <-.
        eexists {| elem := (_,_) |}.
        rewrite pcore_unfold /core.
        split; [done|].
        eexists {| elem := (_,_) |}.
        rewrite op_unfold /add.
        do 2 f_equal.
        hexploit (Fuel.from_monoid_exist q). i. des. subst.
        erewrite Fuel.from_monoid_add.
        apply Fuel.from_monoid_eq.
        symmetry. eapply OrderedCM.add_unit_eq_l.
      - intros [[]] [[]].
        rewrite valid_unfold /wf op_unfold /add.
        intros WF.
        rewrite valid_unfold /wf. des.
        hexploit (Fuel.from_monoid_exist q). i. des. subst.
        hexploit (Fuel.from_monoid_exist q0). i. des. subst.
        rewrite Fuel.from_monoid_add in WF.
        rewrite Fuel.from_monoid_le in WF. esplits; eauto.
        { rewrite Fuel.from_monoid_le. etrans; eauto.
          apply OrderedCM.add_base_l.
        }
        { ss. des. auto. }
    Qed.

    Canonical Structure CounterR := discreteR car mixin.

    Global Instance discrete : CmraDiscrete CounterR.
    Proof. apply discrete_cmra_discrete. Qed.

    Lemma ucmra_mixin : UcmraMixin car.
    Proof.
      split; try apply _; try done.
      - rewrite valid_unfold /wf unit_unfold /unit. exists OrderedCM.unit.
        ss. splits; auto.
        rewrite Fuel.from_monoid_le. splits; auto. reflexivity.
      - intros [[]].
        rewrite op_unfold /add unit_unfold /unit. do 2 f_equal.
        { apply partition_ext. i. ss. split; i; des; auto. }
        { hexploit (Fuel.from_monoid_exist q). i. des. subst.
          rewrite Fuel.from_monoid_add.
          apply Fuel.from_monoid_eq. eapply OrderedCM.add_unit_eq_r.
        }
    Qed.
    Canonical Structure t := Ucmra car ucmra_mixin.

    Definition black (a: A): t :=
      mk_car (partition_from_monoid a, Fuel.from_monoid OrderedCM.unit).

    Definition white (a: A): t :=
      mk_car (partition_top, Fuel.from_monoid a).

    Global Instance black_core_id a : CoreId (black a).
    Proof. rewrite core_id_total_L. ss. Qed.

    Lemma black_persistent a
      :
      cmra.core (black a) = black a.
    Proof. ss. Qed.

    Lemma black_mon a0 a1
          (LE: OrderedCM.le a0 a1)
      :
      (black a1) ≼ (black a0).
    Proof.
      exists (black a0).
      rewrite op_unfold /add /black. do 2 f_equal.
      { apply partition_ext. i. ss. split; i; des; auto.
        split; auto. etrans; eauto.
      }
      { rewrite Fuel.from_monoid_add.
        apply Fuel.from_monoid_eq. symmetry. apply OrderedCM.add_unit_eq_r.
      }
    Qed.

    Lemma white_mon a0 a1
          (LE: OrderedCM.le a0 a1)
      :
      (white a1) ~~> (white a0).
    Proof.
      rewrite cmra_discrete_total_update. intros [[]] H0.
      rewrite op_unfold /add valid_unfold /wf in H0.
      rewrite op_unfold /add valid_unfold /wf. simpl in *.
      des. des_ifs.
      hexploit (Fuel.from_monoid_exist q). i. des. subst.
      rewrite Fuel.from_monoid_add.
      rewrite Fuel.from_monoid_add in H0.
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
      unfold white. do 2 f_equal. apply Fuel.from_monoid_eq; auto.
    Qed.

    Lemma white_split a0 a1
      :
      white (OrderedCM.add a0 a1) = white a0 ⋅ white a1.
    Proof.
      rewrite op_unfold /add. unfold white. do 2 f_equal.
      { apply partition_ext. i. ss. }
      { rewrite Fuel.from_monoid_add. auto. }
    Qed.

    Lemma black_white_wf a
      :
      ✓ (black a ⋅ white a).
    Proof.
      rewrite op_unfold /add valid_unfold /wf.
      exists a. rewrite Fuel.from_monoid_add. splits; auto.
      { rewrite Fuel.from_monoid_le. apply OrderedCM.add_unit_le_r. }
      { simpl in *. split; [|done]. reflexivity. }
    Qed.

    Lemma black_white_decr a0 a1
      :
      (black a0 ⋅ white a1) ~~>: (fun r => exists a2, r = black a2 /\ OrderedCM.le (OrderedCM.add a2 a1) a0).
    Proof.
      apply cmra_discrete_total_updateP. intros [[]] WF.
      rewrite /black /white op_unfold /add valid_unfold /wf in WF. ss.
      des. ss. des_ifs.
      hexploit (Fuel.from_monoid_exist q). i. des. subst. ss. des.
      rewrite !Fuel.from_monoid_add Fuel.from_monoid_le in WF.
      eexists {| elem := (_, _) |}. esplits.
      { reflexivity. }
      { instantiate (1:=a2). etrans; eauto.
        etrans; eauto. etrans.
        { eapply OrderedCM.add_comm_le. }
        { apply OrderedCM.le_add_r. apply OrderedCM.add_base_r. }
      }
      { rewrite op_unfold /add valid_unfold /wf /=. esplits.
        { rewrite Fuel.from_monoid_add. rewrite Fuel.from_monoid_le.
          eapply OrderedCM.add_unit_le_r.
        }
        { reflexivity. }
        { eapply closed; eauto. etrans; eauto.
          eapply OrderedCM.add_base_r.
        }
      }
    Qed.
    Lemma black_white_decr' a0 a1
      :
      ∀ z : t,
        ✓ (black a0 ⋅ white a1 ⋅ z)
        → ∃ y : t,
            (∃ a2 : A,
               y = black a2 ∧ OrderedCM.le (OrderedCM.add a2 a1) a0)
            ∧ ✓ (y ⋅ z).
    Proof. apply cmra_discrete_total_updateP,black_white_decr. Qed.

    Lemma black_white_compare a0 a1
          (WF: ✓ (black a0 ⋅ white a1))
      :
      OrderedCM.le a1 a0.
    Proof.
      exploit black_white_decr'.
      { instantiate (1:=ε). rewrite right_id. eauto. }
      i. des. etrans; eauto. apply OrderedCM.add_base_r.
    Qed.
  End MONOID.
End CounterRA.
Global Arguments CounterRA.t _ : clear implicits.

Local Lemma ord_mult_split (n: nat)
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

From Fairness Require Export FiniteMapRA OneShotRA IUpd ListIProp.

Module ObligationRA.

  Variant _unit : Type := _tt.

  Definition t: ucmra := @FiniteMap.t (prodUR (@CounterRA.t Ord.t _) (OneShot.t _unit)).

  Global Instance discrete : CmraDiscrete t.
  Proof. apply _. Qed.

  Section RA.
    Context `{@GRA.inG t Σ}.
    Notation iProp := (iProp Σ) (only parsing).

    Definition black (k: nat) (o: Ord.t): iProp :=
      OwnM (FiniteMap.singleton k ((CounterRA.black o: @CounterRA.t Ord.t _, ε: OneShot.t _unit): prodUR (@CounterRA.t Ord.t _) (OneShot.t _unit))).

    Definition white (k: nat) (o: Ord.t): iProp :=
      OwnM (FiniteMap.singleton k ((CounterRA.white o: @CounterRA.t Ord.t _, ε: OneShot.t _unit): prodUR (@CounterRA.t Ord.t _) (OneShot.t _unit))).

    Definition pending (k: nat) (q: Qp): iProp :=
      OwnM (FiniteMap.singleton k ((ε: @CounterRA.t Ord.t _, OneShot.pending _unit q: OneShot.t _unit): prodUR (@CounterRA.t Ord.t _) (OneShot.t _unit))).

    Definition shot (k: nat): iProp :=
      OwnM (FiniteMap.singleton k ((ε: @CounterRA.t Ord.t _, OneShot.shot _tt: OneShot.t _unit): prodUR (@CounterRA.t Ord.t _) (OneShot.t _unit))).


    Definition white_one k: iProp :=
      white k (Ord.S Ord.O).

    Global Instance Persistent_black k o: Persistent (black k o).
    Proof. apply _. Qed.

    Global Instance Persistent_shot k: Persistent (shot k).
    Proof. apply _. Qed.

    Lemma pending_shot k
      :
      (pending k 1)
        -∗
        #=> (shot k).
    Proof.
      iApply OwnM_Upd. eapply FiniteMap.singleton_updatable.
      apply prod_update.
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
      iIntros "H0 H1". iCombine "H0 H1" gives %WF.
      rewrite FiniteMap.singleton_add FiniteMap.singleton_wf pair_valid Some_valid in WF.
      des. exfalso. apply OneShot.pending_not_shot in WF0. eauto.
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
      rewrite -(OneShot.pending_sum).
      iFrame "H".
    Qed.

    Lemma pending_wf k q
      :
      (pending k q)
        -∗
        (⌜(q ≤ 1)%Qp⌝).
    Proof.
      iIntros "H".
      iDestruct (OwnM_valid with "H") as %?.
      rewrite FiniteMap.singleton_wf pair_valid in H0.
      des. apply OneShot.pending_wf in H1. auto.
    Qed.

    Lemma pending_split k q0 q1
      :
      (pending k (q0 + q1)%Qp)
        -∗
        (pending k q0 ∗ pending k q1).
    Proof.
      iIntros "H".
      iDestruct (OwnM_extends with "H") as "[$ $]".
      rewrite FiniteMap.singleton_add OneShot.pending_sum -pair_op right_id.
      reflexivity.
    Qed.

    Lemma alloc o
      :
      ⊢ #=> (∃ k, black k o ∗ white k o ∗ pending k 1).
    Proof.
      iDestruct (OwnM_unit (M:=t) emp with "[//]") as "H".
      iMod (OwnM_Upd_set with "H") as "H0".
      { eapply FiniteMap.singleton_alloc.
        instantiate (1:=(CounterRA.black o, ε) ⋅ (CounterRA.white o, ε) ⋅ (ε, OneShot.pending _unit 1)).
        rewrite -!pair_op /= left_id right_id.
        rewrite pair_valid. split.
        { eapply CounterRA.black_white_wf. }
        { apply OneShot.pending_one_wf. }
      }
      iDestruct "H0" as "[% [% H0]]".
      des. rewrite H0. subst. rewrite -!FiniteMap.singleton_add. iDestruct "H0" as "[[H0 H1] H2]".
      iModIntro. iExists _. iFrame "H0 H1 H2".
    Qed.

    Lemma black_mon o1 k o0
          (LE: Ord.le o0 o1)
      :
      black k o0 -∗ black k o1.
    Proof.
      iApply OwnM_extends. apply FiniteMap.singleton_extends.
      rewrite pair_included. split; [|reflexivity].
      apply CounterRA.black_mon. auto.
    Qed.

    Lemma white_mon o1 k o0
          (LE: Ord.le o0 o1)
      :
      white k o1 -∗ #=> white k o0.
    Proof.
      iApply OwnM_Upd. apply FiniteMap.singleton_updatable.
      apply prod_update; [|reflexivity].
      apply CounterRA.white_mon. auto.
    Qed.

    Lemma white_eq o1 k o0
          (LE: Ord.eq o0 o1)
      :
      white k o0 -∗ white k o1.
    Proof.
      unfold white. erewrite CounterRA.white_eq.
      { iIntros "H". iFrame "H". }
      auto.
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
      { iCombine "H0 H1" as "$". }
      { symmetry. eapply (@CounterRA.white_split Ord.t ord_OrderedCM o0 o1). }
    Qed.

    Lemma white_split_eq k o0 o1
      :
      (white k (Hessenberg.add o0 o1))
        -∗
        (white k o0 ∗ white k o1).
    Proof.
      iIntros "H". unfold white.
      replace (CounterRA.white (Hessenberg.add o0 o1): @CounterRA.t Ord.t ord_OrderedCM, ε: @OneShot.t _unit) with
        (((CounterRA.white o0, ε): prodUR (@CounterRA.t Ord.t _) (OneShot.t _unit)) ⋅ ((CounterRA.white o1, ε): prodUR (@CounterRA.t Ord.t _) (OneShot.t _unit))).
      { rewrite <- FiniteMap.singleton_add. iDestruct "H" as "[H0 H1]". iFrame. }
      { rewrite -pair_op right_id. f_equal.
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
      iIntros "H". iPoseProof (white_mon with "H") as "> H".
      { eauto. }
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
      iCombine "H0 H1" gives %H0.
      iPureIntro.
      rewrite FiniteMap.singleton_add in H0.
      apply FiniteMap.singleton_wf in H0.
      rewrite pair_valid in H0. des. ss.
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
      iCombine "H0 H1" as "H".
      iMod (OwnM_Upd_set with "H") as (?) "[Hb H]".
      { eapply singleton_updateP', prod_updateP'.
        { eapply CounterRA.black_white_decr. }
        { eapply cmra_update_updateP. simpl. reflexivity. }
      }
      { ss. iDestruct "Hb" as ([]) "%". des. simpl in *. des; subst.
        iModIntro. iExists _. simpl in *. iFrame "H". eauto. }
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
      iMod (black_white_decr with "H0 H1") as (?) "[H %]".
      iModIntro. iExists _. iFrame. iPureIntro.
      eapply Ord.lt_le_lt; eauto.
      rewrite Hessenberg.add_S_r Hessenberg.add_O_r.
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
      iMod (white_split_one with "H1") as "[H1 H2]"; [eauto|].
      iMod (black_white_decr_one with "H0 H2") as (?) "[H0 %]".
      iModIntro. iExists _. iFrame. auto.
    Qed.

  End RA.

  Section EDGE.

    Context `{Σ: GRA.t}.
    Context `{@GRA.inG t Σ}.
    Context `{@GRA.inG (Region.t (nat * nat * Ord.t)) Σ}.
    Notation iProp := (iProp Σ) (only parsing).

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

    Global Instance Persistent_amplifier k0 k1 c: Persistent (amplifier k0 k1 c).
    Proof. apply _. Qed.

    Lemma amplifier_mon k0 k1 c0 c1
          (LE: Ord.le c0 c1)
      :
      amplifier k0 k1 c1 ⊢ amplifier k0 k1 c0.
    Proof.
      iIntros "# H". iModIntro. iIntros "% WHITE".
      iMod ("H" with "WHITE") as "WHITE".
      iMod (white_mon with "WHITE") as "$".
      { by apply Jacobsthal.le_mult_l. }
      done.
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
      iMod ("H0" with "WHITE") as "WHITE".
      iMod ("H1" with "WHITE") as "WHITE".
      iMod (white_mon with "WHITE") as "$".
      { rewrite -ClassicJacobsthal.mult_assoc. reflexivity. }
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
      iIntros "H0 H1". iMod ("H0" with "H1") as "$". done.
    Qed.

    Lemma amplifier_intro k0 k1 c o
      :
      (black k0 o)
        -∗
        (white k1 (Jacobsthal.mult c o))
        -∗
        (#=(edges_sat)=> amplifier k0 k1 c).
    Proof.
      iIntros "BLACK WHITE".
      iMod (Region.alloc edge (_,_,_) with "[BLACK WHITE]") as "[% # H]".
      { iExists _. iFrame. }
      iModIntro.
      unfold amplifier. iModIntro. iIntros "% WHITE".
      iApply (Region.update with "H [WHITE]").
      rewrite IUpd_eq. iIntros "[% [H0 H1]]".
      iPoseProof (black_white_decr with "H0 WHITE") as "> [% [H0 %]]".
      iPoseProof (white_mon with "H1") as "> H1".
      { (* FIXME: ssreflect rewrite doesn't work. *)
        rewrite <-Jacobsthal.le_mult_r; [|eauto].
        rewrite ClassicJacobsthal.mult_dist. reflexivity.
      }
      iPoseProof (white_split_eq with "H1") as "[H1 H2]".
      iFrame "H2". iModIntro. iExists _. iFrame "H0 H1".
    Qed.

  End EDGE.

  Section ARROW.
    Variable (S: Type).
    Context `{@GRA.inG t Σ}.
    Context `{@GRA.inG (@FairRA.t S nat _) Σ}.
    Context `{@GRA.inG (@FiniteMap.t (OneShot.t _unit)) Σ}.

    Local Notation index := nat.
    Context `{Vars : index -> Type}.
    Context `{Invs : @IInvSet Σ Vars}.
    Context `{GRA.inG (Regions.t (fun l => (S * nat * Ord.t * Qp * nat * (Vars l))%type)) Σ}.
    Notation iProp := (iProp Σ) (only parsing).

    Section PRISM.

    Variable (Id: Type).
    Variable (v: index).
    Local Notation Var := (Vars v).
    Variable (p: Prism.t S Id).

    Definition arrow: (S * nat * Ord.t * Qp * nat * Var) -> iProp :=
      fun '(i, k, c, q, x, f) =>
        ((□ (prop _ f -∗ □ (prop _ f)))
           ∗
           (((pending k (1/2)) ∗ (∃ n, FairRA.black Prism.id i n q) ∗ (white k (Jacobsthal.mult c Ord.omega)))
            ∨
              ((shot k)
                 ∗
                 ((OwnM (FiniteMap.singleton x (OneShot.shot _tt)) ∗ (prop _ f))
                  ∨
                    (∃ n, (FairRA.black Prism.id i n q)
                            ∗ (white k (Jacobsthal.mult c (Ord.from_nat n)))))))
        )%I.

    Definition arrows_sat: iProp := Regions.sat _ arrow.

    Definition delay (i: Id) (k: nat) (c: Ord.t) (f : Var): iProp :=
      (∃ r q x, Regions.white _ r (Prism.review p i, k, c, q, x, f))%I.

    Lemma delay_persistent i k c F
      :
      delay i k c F ⊢ □ delay i k c F.
    Proof.
      iIntros "H".
      unfold delay. iDestruct "H" as (???) "#H".
      auto.
    Qed.

    Global Instance Persistent_delay i k c F: Persistent (delay i k c F).
    Proof. apply _. Qed.


    Lemma delay_shot i k c F
      :
      (delay i k c F)
        -∗
        (pending k (1/2))
        -∗
        (#=(arrows_sat)=> (delay i k c F) ∗ (shot k)).
    Proof.
      iIntros "(% & % & % & #WHITE) P".
      iApply (Regions.update with "WHITE [P]").
      rewrite IUpd_eq. iIntros "[#PERS [(PEND & BL & WH) | (#SHOT & _)]]".
      { iMod (pending_shot with "[P PEND]") as "#SHOT".
        { iEval (rewrite <- (Qp.div_2 1)). iApply (pending_sum with "P PEND"). }
        iDestruct "BL" as "(% & BL)". iMod (white_mon _ _ (o0:=(c × (Ord.from_nat n))%ord) with "WH") as "WH".
        Unshelve.
        2:{ apply Jacobsthal.le_mult_r. apply Ord.lt_le. apply Ord.omega_upperbound. }
        iModIntro. iSplitL.
        { iEval (unfold arrow). iSplitR. auto. iRight. iSplitR. auto. iRight. iExists _. iFrame "BL WH". }
        { iSplitL. 2: auto. unfold delay. iExists _, _, _. iFrame "WHITE". }
      }
      { iPoseProof (pending_not_shot with "P SHOT") as "%FAL". inv FAL. }
    Qed.


    Definition correl (i: Id) (k: nat) (c: Ord.t) (f : Var): iProp :=
      (shot k ∗ ∃ r q x, Regions.white _ r (Prism.review p i, k, c, q, x, f))%I.

    Lemma correl_persistent i k c F
      :
      correl i k c F ⊢ □ correl i k c F.
    Proof.
      iIntros "# H". auto.
    Qed.

    Global Instance Persistent_correl i k c F: Persistent (correl i k c F).
    Proof. apply _. Qed.

    Lemma delay_to_correl i k c F
      :
      (delay i k c F)
        -∗
        (shot k)
        -∗
        (correl i k c F).
    Proof.
      iIntros "D S". iFrame.
    Qed.

    Lemma unfold_correl i k c F
      :
      (correl i k c F)
        -∗
        (delay i k c F) ∗ (shot k).
    Proof.
      iIntros "[D S]". iFrame.
    Qed.

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
                 (□ prop _ f)))).
    Proof.
      iIntros "(#SHOT & [% [% [% WHITE]]]) H".
      iApply (Regions.update with "WHITE [H]").
      rewrite IUpd_eq. iIntros "[#PERS [[PEND _] | (_ & [[OWN PROP] | [% [BLACK WHITE]]])]]".
      { iPoseProof (pending_not_shot with "PEND SHOT") as "%FAL". inv FAL. }
      { iModIntro. iPoseProof ("PERS" with "PROP") as "#F". iSplitL.
        { iSplitR. auto. iRight. iSplitR. auto. iLeft. iFrame. }
        { iSplit. auto. iRight. auto. }
      }
      { iPoseProof (FairRA.decr_update with "BLACK H") as "> [% [H %]]".
        iPoseProof (white_split with "WHITE") as "> [WHITE0 WHITE1]".
        { ss. apply OrdArith.le_from_nat in H3.
          rewrite Hessenberg.add_from_nat in H3.
          etransitivity; last first.
          { apply Jacobsthal.le_mult_r,H3. }
          { rewrite ClassicJacobsthal.mult_dist. reflexivity. }
        }
        iModIntro. iSplitR "WHITE0".
        { iSplitR. auto. iRight. iSplitR. auto. iRight. iExists _. iFrame "H WHITE1". }
        { iSplit. auto. iLeft. auto. }
      }
    Qed.

    Lemma correl_correlate i k c f
      :
      (correl i k c f)
        -∗
        (FairRA.white p i 1)
        -∗
        (#=(arrows_sat)=> white k c ∨ (□ prop _ f)).
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
                           (OwnM ((FiniteMap.singleton x (OneShot.pending _unit 1%Qp)))))%I) rs)
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
        (OwnM ((FiniteMap.singleton x (OneShot.pending _unit 1))))
        -∗
        (duty_list i ((r, (k, c, q1, x, f))::tl) q0).
    Proof.
      iIntros "[DUTY %] WHITE OWN". des. unfold duty_list. simpl. iSplitL.
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
        (Regions.white _ r (Prism.review p i, k, c, q1, x, f) ∗ OwnM ((FiniteMap.singleton x (OneShot.pending _unit 1))) ∗ duty_list i tl (q0 + q1)%Qp).
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
      iClear "H". iIntros "!>" (???????).
      iInduction (rs) as [|a rs] "IHrs"; ss.
      destruct a as [? [[[[? ?] ?] ?] ?]]. iPoseProof "WHITES" as "[WHITE WHITES0]".
      des; clarify. iApply "IHrs"; auto.
    Qed.

    Lemma duty_delay i l k c f
          (IN: List.In (k, c, f) l)
      :
      (duty i l)
        -∗
        (delay i k c f).
    Proof.
      iIntros "[% [% [BLACK [DUTY %]]]]".
      subst. eapply in_map_iff in IN. des. des_ifs.
      iPoseProof (duty_list_whites with "DUTY") as "# WHITES".
      iExists _, _, _. iApply "WHITES". iPureIntro. eauto.
    Qed.

    Lemma duty_correl i l k c f
          (IN: List.In (k, c, f) l)
      :
      (duty i l)
        -∗
        (shot k)
        -∗
        (correl i k c f).
    Proof.
      iIntros "[% [% [BLACK [DUTY %]]]] #SHOT".
      subst. eapply in_map_iff in IN. des. des_ifs.
      iPoseProof (duty_list_whites with "DUTY") as "# WHITES".
      iSplitR. auto. iExists _, _, _. iApply "WHITES". iPureIntro. eauto.
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
      iIntros "[% [% [BLACK [DUTY %]]]] #SHOT PROP".
      destruct rs; ss. des_ifs.
      iPoseProof (duty_list_unfold with "DUTY") as "[WHITE [OWN DUTY]]".
      iPoseProof (Regions.update with "WHITE [OWN PROP]") as "> BLACKF".
      { rewrite IUpd_eq. iIntros "[#PERS [(PEND & _) | (_ & [[DONE _]|[% [BLACK WHITE]]])]]".
        { iPoseProof (pending_not_shot with "PEND SHOT") as "%FAL". inv FAL. }
        { iCombine "OWN DONE" as "FALSE".
          iDestruct (OwnM_valid with "FALSE") as %F.
          rewrite FiniteMap.singleton_wf in F.
          apply OneShot.pending_not_shot in F. ss.
        }
        iPoseProof (OwnM_Upd with "OWN") as "> OWN".
        { apply FiniteMap.singleton_updatable. apply OneShot.pending_shot. }
        iModIntro. iSplitR "BLACK".
        { iSplitR. auto. iRight. iSplit. auto. iLeft. iFrame. }
        { instantiate (1:=FairRA.black_ex p i q0). iExists _. iApply "BLACK". }
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
        (pending k (1/2))
        -∗
        (□ (prop _ f -∗ □ prop _ f))
        -∗
        #=(arrows_sat)=> (duty i ((k, c, f)::l)).
    Proof.
      iIntros "[% [% [BLACK [DUTY %]]]] SHOT PEND #PERS".
      iPoseProof (FairRA.black_ex_split with "[BLACK]") as "[BLACK0 [% BLACK1]]".
      { erewrite Qp.div_2. iFrame. }
      iPoseProof (OwnM_unit (M:=FiniteMap.t (OneShot.t _unit)) emp with "[//]") as "H".
      iMod (OwnM_Upd_set with "H") as (?) "[Hb OWN]".
      { eapply FiniteMap.singleton_alloc. eapply OneShot.pending_one_wf. }
      ss. iDestruct "Hb" as %?. des. rewrite H4.
      iPoseProof (Regions.alloc with "[SHOT PEND BLACK1]") as "> [% WHITE]".
      { instantiate (1:=(Prism.review p i, k, c, (q / 2)%Qp, k0, f)). iSplit. auto.
        iLeft. iFrame. iExists _. iFrame.
      }
      { iModIntro. iExists _, _. iFrame "BLACK0". iSplitL.
        { iApply (duty_list_fold with "[DUTY] WHITE OWN"). erewrite Qp.div_2. eauto. }
        iPureIntro. ss.
        f_equal. ss.
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



    Definition taxes (l: list (nat * Ord.t)) (o: Ord.t): iProp :=
      list_prop_sum (fun '(k, c) => white k (c × o)%ord) l.

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
      (white k (c × o)%ord ∗ (taxes tl o))
        ⊢
        (taxes ((k, c)::tl) o).
    Proof.
      ss.
    Qed.

    Lemma taxes_cons_unfold k c tl o
      :
      (taxes ((k, c)::tl) o)
        ⊢
        (white k (c × o)%ord ∗ taxes tl o).
    Proof.
      ss.
    Qed.

    Lemma taxes_split l0 l1 o
      :
      (taxes (l0 ++ l1) o)
        ⊢
        (taxes l0 o ∗ taxes l1 o).
    Proof.
      apply list_prop_sum_split.
    Qed.

    Lemma taxes_combine l0 l1 o
      :
      (taxes l0 o ∗ taxes l1 o)
        ⊢
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
      { instantiate (1:=(o × o0)%ord).
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

    Lemma taxes_ord_split_one l o0 o1
          (LT: (o0 < o1)%ord)
      :
      taxes l o1 ⊢ #=> (taxes l o0 ∗ taxes l Ord.one).
    Proof.
      iIntros "T". iPoseProof (taxes_ord_split with "T") as "T".
      { dup LT. eapply Ord.S_supremum in LT0.
        assert (REP: (o0 == (Ord.O ⊕ o0))%ord).
        { symmetry. apply Hessenberg.add_O_l. }
        etrans. 2: eapply LT0.
        (* Just doing [rewrite REP] rewrites too many terms *)
        assert ((Ord.S o0 == Ord.S (Ord.O ⊕ o0))%ord) as ->.
        { rewrite -REP. reflexivity. }
        rewrite -Hessenberg.add_S_l //.
      }
      by iMod "T" as "[$ $]".
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

    Definition ptaxes (l: list (nat * Ord.t * option Qp)) (o: Ord.t): iProp :=
      list_prop_sum (fun '(k, c, oq) => match oq with
                                 | None => white k (c × o)%ord
                                 | Some q => pending k q
                                 end
                    ) l.

    Lemma ptaxes_perm l0 l1 o
          (PERM: Permutation l0 l1)
      :
      ptaxes l0 o ⊢ ptaxes l1 o.
    Proof.
      apply list_prop_sum_perm; auto.
    Qed.

    Lemma ptaxes_nil o
      :
      ⊢ ptaxes [] o.
    Proof.
      apply list_prop_sum_nil.
    Qed.

    Lemma ptaxes_cons_fold k c oq tl o
      :
      ((match oq with | None => white k (c × o)%ord | Some q => pending k q end)
         ∗ (ptaxes tl o))
        ⊢
        (ptaxes ((k, c, oq)::tl) o).
    Proof.
      ss.
    Qed.

    Lemma ptaxes_cons_unfold k c oq tl o
      :
      (ptaxes ((k, c, oq)::tl) o)
        ⊢
        ((match oq with | None => white k (c × o)%ord | Some z => pending k z end)
           ∗ (ptaxes tl o)).
    Proof.
      ss.
    Qed.

    Lemma ptaxes_split l0 l1 o
      :
      (ptaxes (l0 ++ l1) o)
        ⊢
        (ptaxes l0 o ∗ ptaxes l1 o).
    Proof.
      apply list_prop_sum_split.
    Qed.

    Lemma ptaxes_combine l0 l1 o
      :
      (ptaxes l0 o ∗ ptaxes l1 o)
        ⊢
        (ptaxes (l0 ++ l1) o).
    Proof.
      apply list_prop_sum_combine.
    Qed.

    Lemma ptaxes_ord_mon l o0 o1
          (LE: Ord.le o0 o1)
      :
      ptaxes l o1 ⊢ #=> ptaxes l o0.
    Proof.
      revert_until l. induction l; i.
      { iIntros "H". iModIntro. iApply ptaxes_nil. }
      iIntros "H". destruct a as [[k o] oq].
      iPoseProof (ptaxes_cons_unfold with "H") as "[W TX]".
      iPoseProof (IHl with "TX") as "IH".
      { eauto. }
      des_ifs.
      { iMod "IH". iApply (ptaxes_cons_fold with "[W IH]"). iFrame. }
      iPoseProof (white_mon with "W") as "W".
      { instantiate (1:=(o × o0)%ord).
        apply Jacobsthal.le_mult_r. auto.
      }
      iMod "W". iMod "IH".
      iPoseProof (ptaxes_cons_fold with "[W IH]") as "A".
      2: iModIntro; iFrame.
      { iFrame. }
    Qed.

    Definition opends (l: list (nat * Ord.t * option Qp)) : iProp :=
      list_prop_sum (fun '(k, c, oq) => match oq with
                                     | None => emp%I
                                     | Some q => pending k q
                                     end
                    ) l.

    Lemma opends_perm l0 l1
          (PERM: Permutation l0 l1)
      :
      opends l0 ⊢ opends l1.
    Proof.
      apply list_prop_sum_perm; auto.
    Qed.

    Lemma opends_nil
      :
      ⊢ opends [].
    Proof.
      apply list_prop_sum_nil.
    Qed.

    Lemma opends_cons_fold k c oq tl
      :
      ((match oq with | None => emp%I | Some q => pending k q end)
         ∗ (opends tl))
        ⊢
        (opends ((k, c, oq)::tl)).
    Proof.
      ss.
    Qed.

    Lemma opends_cons_unfold k c oq tl
      :
      (opends ((k, c, oq)::tl))
        ⊢
        ((match oq with | None => emp%I | Some q => pending k q end)
           ∗ (opends tl)).
    Proof.
      ss.
    Qed.

    Lemma opends_split l0 l1
      :
      (opends (l0 ++ l1))
        ⊢
        (opends l0 ∗ opends l1).
    Proof.
      apply list_prop_sum_split.
    Qed.

    Lemma opends_combine l0 l1
      :
      (opends l0 ∗ opends l1)
        ⊢
        (opends (l0 ++ l1)).
    Proof.
      apply list_prop_sum_combine.
    Qed.

    Definition pends (l: list (nat * Qp)) : iProp :=
      list_prop_sum (fun '(k, q) => pending k q) l.

    Lemma pends_perm l0 l1
          (PERM: Permutation l0 l1)
      :
      pends l0 ⊢ pends l1.
    Proof.
      apply list_prop_sum_perm; auto.
    Qed.

    Lemma pends_nil
      :
      ⊢ pends [].
    Proof.
      apply list_prop_sum_nil.
    Qed.

    Lemma pends_cons_fold k q tl
      :
      ((pending k q) ∗ (pends tl))
        ⊢
        (pends ((k, q) :: tl)).
    Proof.
      ss.
    Qed.

    Lemma pends_cons_unfold k q tl
      :
      (pends ((k, q) :: tl))
        ⊢
        ((pending k q) ∗ (pends tl)).
    Proof.
      ss.
    Qed.

    Lemma pends_split l0 l1
      :
      (pends (l0 ++ l1))
        ⊢
        (pends l0 ∗ pends l1).
    Proof.
      apply list_prop_sum_split.
    Qed.

    Lemma pends_combine l0 l1
      :
      (pends l0 ∗ pends l1)
        ⊢
        (pends (l0 ++ l1)).
    Proof.
      apply list_prop_sum_combine.
    Qed.


    Notation in_dec_nat := (in_dec PeanoNat.Nat.eq_dec).

    Lemma pends_to_opends l :
      (pends l)
        -∗
        (opends (map (fun '(k, q) => (k, Ord.O, Some q)) l)).
    Proof.
      iIntros "P". unfold pends, opends. iApply (list_prop_sum_map). 2: iFrame.
      i. simpl. des_ifs. iIntros "$".
    Qed.

    Lemma opends_to_pends l :
      (opends (map (fun '(k, q) => (k, Ord.O, Some q)) l))
        -∗
        (pends l).
    Proof.
      iIntros "P". unfold pends, opends. iApply (list_prop_sum_map_inv). 2: iFrame.
      i. simpl. des_ifs. iIntros "$".
    Qed.

    Lemma pends_taxes_to_ptaxes l1 l2 c :
      (pends l1)
        -∗
        (taxes l2 c)
        -∗
        (ptaxes
           ((map (fun '(k, q) => (k, Ord.O, Some q)) l1) ++ (map (fun '(k, o) => (k, o, None)) l2))
           c).
    Proof.
      iIntros "P T". iApply ptaxes_combine. iSplitL "P".
      { unfold pends, ptaxes. iApply (list_prop_sum_map). 2: iFrame.
        i. destruct a. eauto.
      }
      { unfold taxes, ptaxes. iApply (list_prop_sum_map). 2: iFrame.
        i. destruct a. eauto.
      }
    Qed.

    Lemma opends_to_pends2 (l1 : list (index * Qp)) (l2 : list (index * Ord.t)) :
      (opends ((map (fun '(k, q) => (k, Ord.O, Some q)) l1) ++ (map (fun '(k, o) => (k, o, None)) l2)))
        -∗
        (pends l1).
    Proof.
      iIntros "OP". iPoseProof (opends_split with "OP") as "[O _]".
      iApply opends_to_pends. iFrame.
    Qed.


    Lemma duty_list_pending P i rs q
          (IMPL: P ⊢ duty_list i rs q)
      :
      (P)
        -∗
        (P ∧ (∀ r k c q x f (IN: List.In (r, (k, c, q, x, f)) rs), OwnM ((FiniteMap.singleton x (OneShot.pending _unit 1))))).
    Proof.
      revert P q IMPL. induction rs.
      { i. iIntros "H". iSplit; ss. iIntros. ss. }
      i. destruct a as [? [[[[? ?] ?] ?] ?]].
      ss. iIntros "DUTY".
      iPoseProof (IHrs with "DUTY") as "DUTY".
      { iIntros "P". iDestruct (IMPL with "P") as "DUTY".
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
      rewrite IUpd_eq. iIntros "H".
      iAssert (⌜forall r v0 v1 (IN0: In (r, v0) rs0) (IN1: In (r, v1) rs1), v0 = v1⌝)%I as "%".
      { iIntros (? ? ? ? ?).
        destruct a0 as [[[[? ?] ?] ?] ?]. destruct a1 as [[[[? ?] ?] ?] ?].
        iDestruct "H" as "[% [H SAT]]".
        iPoseProof (Regions.white_agree with "[] []") as "%".
        { iApply "WHITES0". eauto. }
        { iApply "WHITES1". eauto. }
        clarify.
      }
      iAssert (P ∧ ((∀ r k c q x f (IN0: List.In (r, (k, c, q, x, f)) rs0), OwnM ((FiniteMap.singleton x (OneShot.pending _unit 1)))) ∗ (∀ r k c q x f (IN: List.In (r, (k, c, q, x, f)) rs1), OwnM ((FiniteMap.singleton x (OneShot.pending _unit 1))))))%I with "[DUTY]" as "DUTY".
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
        iCombine "OWN0 OWN1" gives %H4.
        rewrite FiniteMap.singleton_add in H4.
        apply FiniteMap.singleton_wf in H4.
        rewrite -OneShot.pending_sum in H4.
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
      { iIntros "P". iDestruct (IMPL with "P") as "DUTY".
        iPoseProof (duty_list_unfold with "DUTY") as "[#WHITE [OWN DUTY]]". eauto.
      }
      iPoseProof (duty_list_whites with "[DUTY]") as "# WHITES".
      { iApply IMPL. auto. }
      rewrite IUpd_eq. iIntros "H".
      iAssert (⌜forall r k c q x f (IN: List.In (r, (k, c, q, x, f)) rs), n <> r⌝)%I as "%".
      { iIntros (? ? ? ? ? ? IN ?). subst.
        iPoseProof (IMPL with "DUTY") as "DUTY".
        iPoseProof (duty_list_unfold with "DUTY") as "[WHITE [PENDING DUTY]]". eauto.
        iPoseProof "H" as "[% [H _]]".
        iPoseProof (Regions.white_agree with "[] WHITE") as "%".
        { iApply "WHITES". iPureIntro. ss. eauto. }
        clarify. iPoseProof ("WHITES" $! _ _ _ _ _ _ (or_intror IN)) as "# WHITE1".
        iAssert (OwnM (FiniteMap.singleton n1 (OneShot.pending _unit 1))) with "[DUTY]" as "OWN1".
        { iClear "WHITE1 WHITES". clear IHrs H3 IMPL.
          move: (q + q0)%Qp => q'.
          iInduction (rs) as [|a0 rs] "IHrs" forall (q'); ss.
          { destruct a0 as [? [[[[? ?] ?] ?] ?]].
            iPoseProof (duty_list_unfold with "DUTY") as "[_ [OWN DUTY]]".
            des; clarify. iApply "IHrs"; eauto.
          }
        }
        iCombine "PENDING OWN1" gives %WF.
        exfalso. clear -WF.
        rewrite singleton_op -OneShot.pending_sum in WF.
        apply singleton_valid, OneShot.pending_wf in WF.
        apply Qp.not_add_le_r in WF. ss.
      }
      iSplitL "H".
      { eauto. }
      iModIntro. iSplit; auto.
      iPureIntro. econs; ss. ii. eapply in_map_iff in H5.
      des. destruct x as [? [[[[? ?] ?] ?] ?]]. ss. subst. eapply H4; eauto.
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
      rewrite IUpd_eq. iIntros "SAT". iModIntro.
      iSplitL "SAT"; [auto|]. iIntros "SAT".
      iAssert (duty_list i rs q ∗ FairRA.black_ex p i 1%Qp ∗ (foldr (fun '(_, (k, _, _, _, f)) P => ((□(prop _ f -∗ □ prop _ f)) ∗ (pending k (1/2) ∨ shot k)) ∗ P) emp rs))%I with "[DUTY BLACK SAT]" as "[DUTY [BLACK PERSS]]".
      { iClear "WHITES". iStopProof. clear H3. revert q. induction rs.
        { ss. i. iIntros "[[DUTY %] [BLACK _]]". ss. subst. iFrame. auto. }
        i. destruct a as [? [[[[? ?] ?] ?] ?]].
        iIntros "[DUTY [BLACK SAT]]". ss.
        iPoseProof (duty_list_unfold with "DUTY") as "[WHITE [OWN DUTY]]".
        iDestruct "SAT" as "[[#PERS [(PEND & [% BLACK1] & WH) | [#SHOTk [[SHOT _]|[% [BLACK1 SAT]]]]]] SATS]".
        - iPoseProof (IHrs with "[DUTY BLACK BLACK1 SATS]") as "[DUTY [BLACK PERSS]]".
          { iSplitL "DUTY"; [eauto|]. iSplitL "BLACK BLACK1"; [|auto].
            iApply (FairRA.black_ex_sum with "BLACK"). iExists _. iFrame.
          }
          iSplitR "BLACK PEND PERSS".
          { iApply (duty_list_fold with "DUTY WHITE OWN"). }
          { iFrame. auto. }
        - iExFalso. iCombine "OWN SHOT" gives %WF.
          exfalso.
          rewrite singleton_op in WF.
          apply singleton_valid, OneShot.pending_not_shot in WF. ss.
        - iPoseProof (IHrs with "[DUTY BLACK BLACK1 SATS]") as "[DUTY [BLACK PERSS]]".
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
      iEval (rewrite <- H4) in "BLACK". iStopProof. clear H3 H4. revert q. induction rs.
      { i. iIntros "[# WHITES [TAX [BLACK PERSS]]]". iModIntro. ss. iFrame. }
      { i. iIntros "[# WHITES [TAX [BLACK PERSS]]]". ss.
        destruct a0 as [? [[[[? ?] ?] ?] ?]]. ss.
        iPoseProof "TAX" as "[WHITE TAX]".
        replace (q0 + foldr (fun '(_, (_, _, q1, _, _)) q2 => (q1 + q2)%Qp) q rs)%Qp with (q + foldr (fun '(_, (_, _, q1, _, _)) q2 => (q1 + q2)%Qp) q0 rs)%Qp; cycle 1.
        { clear IHrs. revert q q0. induction rs; ss; i.
          { apply Qp.add_comm. }
          { destruct a0 as [? [[[[? ?] ?] ?] ?]].
            rewrite (IHrs q1 q0) (IHrs q1 q).
            rewrite !Qp.add_assoc.
            f_equal. apply Qp.add_comm.
          }
        }
        iPoseProof (FairRA.black_split with "BLACK") as "[BLACK0 BLACK1]".
        iDestruct "PERSS" as "[(#PERS & CASE) PERSS]".
        iPoseProof (IHrs with "[TAX BLACK1 PERSS]") as "> [REGION BLACK1]".
        { iSplit.
          { iClear "TAX BLACK1". iModIntro. iIntros.
            iApply "WHITES". eauto.
          }
          iFrame.
        }
        iFrame. iSplitR. auto. iDestruct "CASE" as "[PEND | #SHOTk]".
        - iLeft. iFrame. iModIntro. iExists _. iFrame.
        - iRight. iSplitR. iModIntro; auto. iRight. iExists _. iFrame. iApply (white_mon with "WHITE").
          apply Jacobsthal.le_mult_r, Ord.lt_le, Ord.omega_upperbound.
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
      rewrite IUpd_eq. iIntros "[#PERS SAT]". iModIntro. iFrame. auto.
    Qed.

    Lemma duties_updating os
      :
      (list_prop_sum (fun '(i, l) => duty i l ∗ taxes (map fst l) Ord.omega) os)
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
          iIntros "TAX". iPoseProof (taxes_cons_unfold with "TAX") as "[HD TL]".
          iPoseProof (IHrs with "TL") as "TL". iPoseProof (white_eq with "HD") as "HD".
          2: iFrame. reflexivity.
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

    Lemma duty_list_updating_pending i rs q ps
          (PENDS : Forall2 (fun '(_, (k1, c1, _, _, _)) '(k2, c2, oq) => k1 = k2 /\ (match oq with None => c1 = c2 | Some _ => True end)) rs ps)
      :
      (duty_list i rs q)
        -∗
        (FairRA.black_ex p i q)
        -∗
        (ptaxes ps Ord.omega)
        -∗
        #=(arrows_sat)=>
            (updating
               (@Regions.sat_list _ (fun l => (S * nat * Ord.t * Qp * nat * (Vars l))%type) _ _ arrow (List.map snd (List.map (fun '(r, (k, c, q, x, f)) => (r, (Prism.review p i, k, c, q, x, f))) rs)))
               (FairRA.black_ex p i 1)
               (FairRA.black_ex p i 1)
               ((duty_list i rs q)
                  ∗ (FairRA.black_ex p i q)
                  ∗ (opends ps)
            )).
    Proof.
      iIntros "DUTY BLACK TAX".
      iPoseProof (duty_list_nodup with "DUTY") as "> [DUTY %]".
      { reflexivity. }
      iPoseProof (duty_list_whites with "DUTY") as "# WHITES".
      rewrite IUpd_eq. iIntros "SAT". iModIntro.
      iSplitL "SAT"; [auto|]. iIntros "SAT".
      iAssert (duty_list i rs q ∗ FairRA.black_ex p i 1%Qp ∗ (foldr (fun '(_, (k, c, _, _, f)) P => ((□(prop _ f -∗ □ prop _ f)) ∗ ((pending k (1/2) ∗ white k (c × Ord.omega)%ord) ∨ shot k)) ∗ P) emp rs))%I with "[DUTY BLACK SAT]" as "[DUTY [BLACK PERSS]]".
      { iClear "WHITES". iStopProof. clear H3 PENDS ps. revert q. induction rs.
        { ss. i. iIntros "[[DUTY %] [BLACK _]]". ss. subst. iFrame. auto. }
        i. destruct a as [? [[[[? ?] ?] ?] ?]].
        iIntros "[DUTY [BLACK SAT]]". ss.
        iPoseProof (duty_list_unfold with "DUTY") as "[WHITE [OWN DUTY]]".
        iDestruct "SAT" as "[[#PERS [(PEND & [% BLACK1] & WH) | [#SHOTk [[SHOT _]|[% [BLACK1 SAT]]]]]] SATS]".
        - iPoseProof (IHrs with "[DUTY BLACK BLACK1 SATS]") as "[DUTY [BLACK PERSS]]".
          { iSplitL "DUTY"; [eauto|]. iSplitL "BLACK BLACK1"; [|auto].
            iApply (FairRA.black_ex_sum with "BLACK"). iExists _. iFrame.
          }
          iSplitR "BLACK PEND WH PERSS".
          { iApply (duty_list_fold with "DUTY WHITE OWN"). }
          { iFrame. iSplitR. auto. iLeft. iFrame. }
        - iExFalso. iCombine "OWN SHOT" as "OWN".
          iDestruct (OwnM_valid with "OWN") as
            %[]%FiniteMap.singleton_wf%OneShot.pending_not_shot.
        - iPoseProof (IHrs with "[DUTY BLACK BLACK1 SATS]") as "[DUTY [BLACK PERSS]]".
          { iFrame "DUTY SATS".
            iDestruct (FairRA.black_ex_sum with "BLACK [BLACK1]") as "$".
            iExists _. iFrame.
          }
          iSplitR "BLACK PERSS".
          { iApply (duty_list_fold with "DUTY WHITE OWN"). }
          { iFrame. auto. }
      }
      iModIntro. iFrame "BLACK".
      iAssert (⌜(fold_right (fun '(r, (k, c, q0, x, f)) q1 => (q0 + q1)%Qp) q rs = 1%Qp)⌝)%I as %?.
      { iDestruct "DUTY" as "[_ $]". }
      iIntros "[% BLACK]".
      iAssert (#=> ((Region.sat_list
                       arrow
                       (List.map snd (List.map (fun '(r, (k, c, q0, x, f)) => (r, (Prism.review p i, k, c, q0, x, f))) rs)))
                      ∗ (FairRA.black p i a q)
                      ∗ (opends ps)
              )) with "[TAX BLACK PERSS]" as "> (REGION & BLACK & PENDS)".
      2:{ iModIntro. iFrame. iExists _. eauto. }
      iEval (rewrite <- H4) in "BLACK". iStopProof. clear H3 H4. revert q ps PENDS. induction rs.
      { i. iIntros "[# WHITES [TAX [BLACK PERSS]]]". iModIntro. ss. iFrame. inv PENDS. ss. }
      { i. iIntros "[# WHITES [TAX [BLACK PERSS]]]". ss.
        destruct a0 as [? [[[[? ?] ?] ?] ?]]. ss.
        inv PENDS. destruct y. destruct p0. des; subst. rename H7 into PENDS.
        iPoseProof "TAX" as "[WHITE TAX]".
        replace (q0 + foldr (fun '(_, (_, _, q1, _, _)) q2 => (q1 + q2)%Qp) q rs)%Qp with (q + foldr (fun '(_, (_, _, q1, _, _)) q2 => (q1 + q2)%Qp) q0 rs)%Qp; cycle 1.
        { clear IHrs. revert q q0 l' PENDS. induction rs; ss; i.
          { apply Qp.add_comm. }
          { destruct a0 as [? [[[[? ?] ?] ?] ?]].
            inv PENDS. rewrite (IHrs q1 q0 _ H8). rewrite (IHrs q1 q _ H8).
            rewrite Qp.add_assoc. rewrite Qp.add_assoc. f_equal. apply Qp.add_comm.
          }
        }
        iPoseProof (FairRA.black_split with "BLACK") as "[BLACK0 BLACK1]".
        iDestruct "PERSS" as "[(#PERS & CASE) PERSS]".
        iPoseProof (IHrs with "[TAX BLACK1 PERSS]") as "> (REGION & BLACK1 & PENDS)".
        { eauto. }
        { iSplit.
          { iClear "TAX BLACK1". iModIntro. iIntros.
            iApply "WHITES". eauto.
          }
          iFrame.
        }
        iFrame. destruct o.
        - iDestruct "CASE" as "[(PEND & WHI) | #SHOTk]".
          + iFrame. iSplitR. iModIntro; auto. iLeft. iFrame. iModIntro. iExists _. iFrame.
          + iPoseProof (pending_not_shot with "WHITE SHOTk") as "%FAL". inv FAL.
        - iDestruct "CASE" as "[(PEND & WHI) | #SHOTk]".
          + iSplitL; [|auto]. iSplitR; [auto|]. iLeft. iFrame. iModIntro. iExists _. iFrame.
          + iSplitL; [|auto]. iSplitR; [auto|].
            iRight. iSplitR. { iModIntro; auto. } subst.
            iRight. iExists _. iFrame. iApply (white_mon with "WHITE").
            apply Jacobsthal.le_mult_r, Ord.lt_le, Ord.omega_upperbound.
      }
    Qed.

    Lemma duties_updating_pending
          (os : list (Id * (list (nat * Ord.t * Var)))) (ps : list (list (nat * Ord.t * option Qp)))
          (PENDS: Forall2 (fun '(_, l1) l2 => Forall2 (fun '(k1, c1, _) '(k2, c2, oq) => k1 = k2 /\ (match oq with | None => c1 = c2 | Some _ => True end)) l1 l2) os ps)
      :
      (list_prop_sum (fun '(i, l) => duty i l) os)
        -∗
        (list_prop_sum (fun l => ptaxes l Ord.omega) ps)
        -∗
        #=(arrows_sat)=>
            (updating
               arrows_sat
               (FairRA.blacks_of p (List.map fst os))
               (FairRA.blacks_of p (List.map fst os))
               ((list_prop_sum (fun '(i, l) => duty i l) os) ∗ (list_prop_sum (fun l => opends l) ps))
            ).
    Proof.
      iIntros "DUTY PTAX".
      iAssert (∃ (xs: list ((Id * list (nat * (nat * Ord.t * Qp * nat * Var)) * Qp) * (list (nat * Ord.t * option Qp)))),
                  (⌜os = List.map (fun '((i, rs, q), _) => (i, List.map (fun '(r, (k, c, q, x, f)) => (k, c, f)) rs)) xs⌝)
                    ∗
                    (⌜ps = List.map (fun '(_, pps) => pps) xs⌝)
                    ∗
                    (#=(arrows_sat)=> list_prop_sum (fun '((i, rs, q), pps) =>
                                                      (duty_list i rs q)
                                                        ∗
                                                        (ptaxes pps Ord.omega)
                                                        ∗
                                                        (FairRA.black_ex p i q)
                                                        ∗
                                                        (foldr (fun '(_, (_, _, _, _, f)) P => (□ (prop _ f -∗ □ prop _ f)) ∗ P) True%I rs)
                                                   ) xs))%I
        with "[DUTY PTAX]" as "[% [% [% >ALL]]]".
      { iStopProof. induction PENDS; ss; i.
        { iIntros. iExists []. ss. }
        { destruct x as [i l1].
          iIntros "([[% [% [BLACK [DUTY %]]]] OS] & PTAX & PS)".
          iPoseProof (IHPENDS with "[OS PS]") as "[% [% [% OS]]]".
          { iFrame. }
          subst. iExists ((_, _, _, _)::_). ss. iSplit.
          { iPureIntro. eauto. }
          iSplit.
          { iPureIntro. eauto. }
          iMod "OS".
          iPoseProof (duty_list_pers_props with "DUTY") as ">[DUTY #PERSS]".
          iFrame. iModIntro. auto.
        }
      }
      subst.
      set (l := List.concat (List.map (fun '(i, rs, q, _) => List.map (fun '(r, (k, c, q, x, f)) => (r, (Prism.review p i, k, c, q, x, f))) rs) xs)).

      iAssert (#=(arrows_sat)=>
                 ((list_prop_sum (fun '(i, rs, q, ps) =>
                                    (duty_list i rs q)
                                      ∗
                                      (ptaxes ps Ord.omega)
                                      ∗
                                      (FairRA.black_ex p i q)
                                      ∗
                                      (foldr (fun '(_, (_, _, _, _, f)) P => (□ (prop _ f -∗ □ prop _ f)) ∗ P) True%I rs)) xs)
                    ∗
                    (⌜List.NoDup (List.map fst l)⌝))%I) with "[ALL]" as "> [ALL %]".
      { subst l. iStopProof. revert PENDS. induction xs; ss.
        { iIntros. iModIntro. iSplit; ss. iPureIntro. econs; ss. }
        destruct a as [[[i rs] q] ps]. iIntros (FA) "[[DUTY [HD BLACK]] TL]".
        inv FA. rename H6 into PENDS. rename H8 into FA.
        iPoseProof (IHxs FA with "TL") as "> [TL %]".
        iPoseProof (duty_list_nodup with "DUTY") as "> [DUTY %]".
        { reflexivity. }
        iAssert (#=(arrows_sat)=>
                   (((duty_list i rs q)
                       ∗
                       (list_prop_sum (fun '(i, rs, q, ps) =>
                                         (duty_list i rs q)
                                           ∗
                                           (ptaxes ps Ord.omega)
                                           ∗
                                           (FairRA.black_ex p i q)
                                           ∗
                                           (foldr (fun '(_, (_, _, _, _, f)) P => (□ (prop _ f -∗ □ prop _ f)) ∗ P) True%I rs)) xs))
                      ∗
                      (⌜forall i0 rs0 q0 ps0 (IN: List.In (i0, rs0, q0, ps0) xs),
                            (forall r (IN0: List.In r (List.map fst rs)) (IN1: List.In r (List.map fst rs0)), False)⌝)))%I with "[DUTY TL]" as "> [[DUTY TL] %]".
        { clear IHxs H3 H4. clear ps PENDS FA. iStopProof. induction xs; ss.
          { iIntros "[DUTY TL]". iModIntro. iSplit; auto. }
          destruct a as [[[i0 rs0] q0] ps0].
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
            destruct x0 as [[[? ?] ?] ?].
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
                 (((list_prop_sum (fun '(i, rs, q, ps) =>
                                     (updating
                                        (@Regions.sat_list _ (fun l => (S * nat * Ord.t * Qp * nat * (Vars l))%type) _ _ arrow (List.map snd (List.map (fun '(r, (k, c, q, x, f)) => (r, (Prism.review p i, k, c, q, x, f))) rs)))
                                        (FairRA.black_ex p i 1)
                                        (FairRA.black_ex p i 1)
                                        (duty_list i rs q ∗ FairRA.black_ex p i q
                                                   ∗ (opends ps)
                                     ))%I)) xs)
                    ∗ (∀ i rs q0 ps r k c q1 x f
                         (IN0: List.In (i, rs, q0, ps) xs)
                         (IN1: List.In (r, (k, c, q1, x, f)) rs),
                          @Regions.white _ (fun l => (S * nat * Ord.t * Qp * nat * (Vars l))%type) _ _ _ r (Prism.review p i, k, c, q1, x, f)))) with "[ALL]" as "> [ALL WHITES]".
      { subst l. iStopProof. clear H3. revert PENDS. induction xs.
        { intros. iIntros. iModIntro. ss. iSplit; auto. iIntros. ss. }
        destruct a as [[[i rs] q] ps]. iIntros (FA) "[[DUTY [TAX [BLACK PERSS]]] DUTIES]".
        inv FA. rename H6 into PENDS, H8 into FA.
        iPoseProof (IHxs FA with "DUTIES") as "> [DUTIES WHITES]".
        iPoseProof (duty_list_whites with "DUTY") as "# WHITE".
        iPoseProof (duty_list_updating_pending with "DUTY BLACK TAX") as "> UPD".
        { clear - PENDS. eapply Forall2_impl. eapply Forall2_fmap_l. apply PENDS.
          i. des_ifs.
        }
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
        apply in_map_iff in IN. des. destruct x0 as [[[i rs] q] ps]. subst.
        apply in_map_iff in IN0. des.
        destruct x as [? [[[[? ?] ?] ?] ?]]. clarify.
        iApply "WHITES"; eauto.
      }
      subst l. clear H3. iStopProof. revert PENDS. induction xs.
      { ss. intros. iIntros "_ SAT". iModIntro. ss. }
      destruct a as [[[i rs] q] ps]. intros. inv PENDS. rename H6 into PENDS, H8 into FA. ss.
      iIntros "[UPD UPDS]".
      iPoseProof (IHxs FA with "UPDS") as "UPDS".
      iIntros "SAT". repeat rewrite List.map_app.
      iPoseProof (Regions.sat_list_split with "SAT") as "[SAT SATS]".
      iPoseProof ("UPD" with "SAT") as "> [BLACK K]".
      iPoseProof ("UPDS" with "SATS") as "> [BLACKS KS]".
      iModIntro. iSplitL "BLACK BLACKS".
      { iApply list_prop_sum_cons_fold. iFrame. }
      iIntros "BLACKS".
      iPoseProof (list_prop_sum_cons_unfold with "BLACKS") as "[BLACK BLACKS]".
      iPoseProof ("K" with "BLACK") as "> [SAT [BLACK [DUTY PENDS]]]".
      iPoseProof ("KS" with "BLACKS") as "> [SATS [DUTIES OPS]]".
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
    Proof. iIntros "Duty". iFrame "Duty". Qed.

    Lemma duty_prism_id_rev Id (p: Prism.t S Id) v i l
      :
      (duty Prism.id (v:=v) (Prism.review p i) l)
        -∗
        (duty p (v:=v) i l).
    Proof. iIntros "Duty". iFrame "Duty". Qed.

    Section SATS.

    (* arrows arrows_sats *)
      Definition arrows : forall i, (S * nat * Ord.t * Qp * nat * Vars i) -> iProp :=
        fun i => (fun x => @arrow i x).

      Definition arrows_sats j : iProp := @Regions.nsats _ Σ _ arrows j.

      Global Instance arrows_sats_elim_upd P Q b i j :
        ElimModal (i < j) b false (#=(arrows_sat i)=> P) P (#=(arrows_sats j)=> Q) (#=(arrows_sats j)=> Q).
      Proof.
        rewrite /ElimModal bi.intuitionistically_if_elim.
        iIntros (LT) "[P K]".
        iPoseProof (@Regions.nsats_sat_sub _ _ _ arrows _ _ LT) as "SUB".
        unfold SubIProp.
        iCombine "SUB P" as "P". iMod "P".
        iApply "K". iFrame.
      Qed.

      Definition arrows_auth j : iProp :=
        OwnM (@Regions.nauth_ra (fun i => (S * nat * Ord.t * Qp * nat * Vars i)%type) j).
    End SATS.

    Section COLLECT.

      Definition collection_taxes k o (l : list (nat * Ord.t)) ot :=
        (black k o ∗ taxes l (ot × o)%ord)%I.

      Lemma collection_taxes_decr k o0 l ot o1 :
        (collection_taxes k o0 l ot)
          -∗
          (white k o1)
          -∗
          (#=> ∃ o2, collection_taxes k o2 l ot ∗ ⌜((o2 ⊕ o1) <= o0)%ord⌝ ∗ taxes l (ot × o1)%ord).
      Proof.
        iIntros "[B C] W". iMod (black_white_decr with "B W") as "[% [B2 %]]".
        iExists o2. iFrame. iMod (taxes_ord_split with "C") as "[TS T]".
        { rewrite <- ClassicJacobsthal.mult_dist. apply Jacobsthal.le_mult_r. eauto. }
        iFrame. iPureIntro. auto.
      Qed.

      Lemma collection_taxes_decr_one k o l ot :
        (collection_taxes k o l ot)
          -∗
          (white_one k)
          -∗
          (#=> ∃ o', collection_taxes k o' l ot ∗ ⌜(o' < o)%ord⌝ ∗ taxes l ot).
      Proof.
        iIntros "[B C] W". iMod (collection_taxes_decr with "[B C] W") as "[% (CT & % & TS)]".
        { iFrame. }
        iExists o2. iFrame. iMod (taxes_ord_mon with "TS") as "TS". 2: iFrame.
        { rewrite Jacobsthal.mult_1_r. reflexivity. }
        iPureIntro. eapply Ord.lt_le_lt. 2: eauto.
        apply Hessenberg.add_lt_l. apply Ord.S_lt.
      Qed.

      Lemma collection_taxes_make k o l ot :
        (black k o ∗ taxes l (ot × o)%ord) ⊢ collection_taxes k o l ot.
      Proof.
        iIntros "[B T]". iFrame.
      Qed.

    End COLLECT.

  End ARROW.

  Section ARROWTHREAD.
    Variable (S: Type).
    Context `{@GRA.inG t Σ}.
    Context `{@GRA.inG (FairRA.tgtt S) Σ}.
    Context `{@GRA.inG (@FiniteMap.t (OneShot.t _unit)) Σ}.

    Local Notation index := nat.
    Context `{Vars : index -> Type}.
    Context `{Invs : @IInvSet Σ Vars}.
    Context `{@GRA.inG (@Regions.t _ (fun l => ((sum_tid S) * nat * Ord.t * Qp * nat * (Vars l))%type)) Σ}.
    Notation iProp := (iProp Σ) (only parsing).

    Definition delay_thread v (k: nat) (c: Ord.t) (f : Vars v): iProp :=
      ∃ i, delay v inlp i k c f.

    Lemma delay_thread_persistent v k c f
      :
      @delay_thread v k c f ⊢ □ @delay_thread v k c f.
    Proof.
      iIntros "# H". auto.
    Qed.

    Global Instance Persistent_delay_thread v k c f: Persistent (@delay_thread v k c f).
    Proof. apply _. Qed.

    Definition correl_thread v (k: nat) (c: Ord.t) (f : Vars v): iProp :=
      ∃ i, correl v inlp i k c f.

    Lemma correl_thread_persistent v k c f
      :
      @correl_thread v k c f ⊢ □ @correl_thread v k c f.
    Proof.
      iIntros "# H". auto.
    Qed.

    Global Instance Persistent_correl_thread v k c f: Persistent (@correl_thread v k c f).
    Proof. apply _. Qed.

    Lemma delay_thread_shot v k c F
      :
      (@delay_thread v k c F)
        -∗
        (pending k (1/2))
        -∗
        (#=(arrows_sat v)=> (@delay_thread v k c F) ∗ (shot k)).
    Proof.
      iIntros "[% DEL] WHITE". iMod (delay_shot with "DEL WHITE") as "[A S]".
      iModIntro. iFrame. iExists _. iFrame.
    Qed.

    Local Transparent delay.
    Local Typeclasses Transparent delay.
    Lemma delay_to_correl_thread v k c F
      :
      (@delay_thread v k c F)
        -∗
        (shot k)
        -∗
        (@correl_thread v k c F).
    Proof.
      iIntros "D S". iFrame.
    Qed.

    Lemma unfold_correl_thread v k c F
      :
      (@correl_thread v k c F)
        -∗
        (@delay_thread v k c F) ∗ (shot k).
    Proof.
      iIntros "[% [D S]]". iFrame. iExists _. iFrame.
    Qed.

    Lemma delay_thread_shot_correl v k c F
      :
      (@delay_thread v k c F)
        -∗
        (pending k (1/2))
        -∗
        (#=(arrows_sat v)=> (@correl_thread v k c F)).
    Proof.
      iIntros "D P". iMod (delay_thread_shot with "D P") as "[D' S]". iModIntro. iFrame.
    Qed.

    Lemma correl_thread_correlate v k c f
      :
      (@correl_thread v k c f)
        -∗
        (FairRA.white_thread (S := S))
        -∗
        (#=(arrows_sat (S := sum_tid S) v)=> (white k c ∨ (□ prop _ f))).
    Proof.
      iIntros "[% CORR] WHITE". iApply (correl_correlate with "CORR WHITE").
    Qed.

    Lemma duty_delay_thread v i l k c f
          (IN: List.In (k, c, f) l)
      :
      (duty v inlp i l)
        -∗
        (@delay_thread v k c f).
    Proof.
      iIntros "DUTY".
      iPoseProof (duty_delay with "DUTY") as "# CORR"; [eauto|].
      iExists _. eauto.
    Qed.

    Lemma duty_correl_thread v i l k c f
          (IN: List.In (k, c, f) l)
      :
      (duty v inlp i l)
        -∗
        (shot k)
        -∗
        (@correl_thread v k c f).
    Proof.
      iIntros "DUTY SHOT".
      iPoseProof (duty_correl with "DUTY SHOT") as "# CORR"; [eauto|].
      iExists _. eauto.
    Qed.
  End ARROWTHREAD.


  Section TARGET.

    Variable (S: Type).
    Let Id := id_sum thread_id S.

    Context `{Σ: GRA.t}.
    Context `{@GRA.inG t Σ}.
    Context `{@GRA.inG (@FairRA.tgtt S) Σ}.
    Context `{@GRA.inG (@FiniteMap.t (OneShot.t _unit)) Σ}.

    Local Notation index := nat.
    Context `{Vars : index -> Type}.
    Context `{Invs : @IInvSet Σ Vars}.
    Context `{@GRA.inG (@Regions.t _ (fun l => (Id * nat * Ord.t * Qp * nat * (Vars l))%type)) Σ}.
    Notation iProp := (iProp Σ) (only parsing).

    Lemma IUpd_open (I P : iProp)
      :
      (#=(I)=> P)
        -∗
        I
        -∗
        (#=> (I ∗ P)).
    Proof.
      iIntros "H0 H1". rewrite IUpd_eq. iPoseProof ("H0" with "H1") as "H". auto.
    Qed.

    Lemma target_update_thread
          (tid: thread_id) v l
          ths
          (f0 f1: FairBeh.imap Id nat_wf)
          (UPD: fair_update f0 f1 (prism_fmap inlp (tids_fmap tid ths)))
      :
      (FairRA.sat_target f0 ths)
        -∗
        (duty v inlp tid l ∗ taxes (map fst l) Ord.omega)
        -∗
        (#=(arrows_sat (S := Id) v)=>
           ((FairRA.sat_target f1 ths)
              ∗
              (duty v inlp tid l)
              ∗
              FairRA.white_thread (S := S))).
    Proof.
      rewrite IUpd_eq. iIntros "SAT DUTY ARROWS".
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

    Lemma target_update_thread_pending
          (tid: thread_id) v l
          ths
          (f0 f1: FairBeh.imap Id nat_wf)
          (UPD: fair_update f0 f1 (prism_fmap inlp (tids_fmap tid ths)))
          ps
          (PENDS : Forall2 (fun '(k1, c1, _) '(k2, c2, oq) => k1 = k2 /\ (match oq with None => c1 = c2 | Some _ => True end)) l ps)
      :
      (FairRA.sat_target f0 ths)
        -∗
        (duty v inlp tid l ∗ ptaxes ps Ord.omega)
        -∗
        (#=(arrows_sat (S := Id) v)=>
           ((FairRA.sat_target f1 ths)
              ∗
              (duty v inlp tid l)
              ∗
              FairRA.white_thread (S := S)
              ∗
              opends ps
        )).
    Proof.
      rewrite IUpd_eq. iIntros "SAT [DUTY PT] ARROWS".
      iPoseProof (duties_updating_pending with "[DUTY] [PT]") as "UPD".
      2:{ instantiate (1:=[(tid, l)]). ss. iFrame. }
      2:{ instantiate (1:=[ps]). ss. iFrame. }
      { auto. }
      iPoseProof (IUpd_open with "UPD ARROWS") as "> [ARROWS UPD]".
      iPoseProof ("UPD" with "ARROWS") as "> [[BLACK _] K]".
      iPoseProof (FairRA.target_update_thread with "SAT BLACK") as "> [SAT [BLACK WHITE]]".
      { eauto. }
      iPoseProof ("K" with "[BLACK]") as "> [ARROWS [[DUTY _] [PS _]]]".
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
        (list_prop_sum (fun '(i, l) => duty v (Prism.compose inrp p) i l ∗ taxes (map fst l) Ord.omega) ls)
        -∗
        (#=(arrows_sat (S := Id) v)=>
           ((FairRA.sat_target f1 ths)
              ∗
              (list_prop_sum (fun '(i, l) => duty v (Prism.compose inrp p) i l) ls)
              ∗
              (list_prop_sum (fun i => FairRA.white (Prism.compose inrp p) i 1) lf))).
    Proof.
      rewrite IUpd_eq. iIntros "SAT DUTY ARROWS".
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

    Lemma target_update_pending A
          v lf ls ths
          (p: Prism.t S A)
          (f0 f1: FairBeh.imap Id nat_wf)
          (fm: Event.fmap A)
          (UPD: fair_update f0 f1 (prism_fmap (Prism.compose inrp p) fm))
          (SUCCESS: forall i (IN: fm i = Flag.success), List.In i (List.map fst ls))
          (FAIL: forall i (IN: List.In i lf), fm i = Flag.fail)
          (NODUP: List.NoDup lf)
          ps
          (PENDS: Forall2 (fun '(_, l1) l2 => Forall2 (fun '(k1, c1, _) '(k2, c2, oq) => k1 = k2 /\ (match oq with | None => c1 = c2 | Some _ => True end)) l1 l2) ls ps)
      :
      (FairRA.sat_target f0 ths)
        -∗
        (list_prop_sum (fun '(i, l) => duty v (Prism.compose inrp p) i l) ls)
        -∗
        (list_prop_sum (fun l => ptaxes l Ord.omega) ps)
        -∗
        (#=(arrows_sat (S := Id) v)=>
           ((FairRA.sat_target f1 ths)
              ∗
              (list_prop_sum (fun '(i, l) => duty v (Prism.compose inrp p) i l) ls)
              ∗
              (list_prop_sum (fun i => FairRA.white (Prism.compose inrp p) i 1) lf)
              ∗
              (list_prop_sum (fun l => opends l) ps)
        )).
    Proof.
      rewrite IUpd_eq. iIntros "SAT DUTY PTX ARROWS".
      iPoseProof (duties_updating_pending with "[DUTY] [PTX]") as "UPD".
      2:{ instantiate (1:=ls). clear SUCCESS. iStopProof. induction ls; ss. }
      2:{ instantiate (1:=ps). done. }
      { auto. }
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
      { clear SUCCESS ps PENDS. iStopProof.
        induction ls; ss. destruct a. ss. unfold FairRA.blacks_of. ss.
        iIntros "[HD TL]". iFrame. iApply IHls. auto.
      }
      iPoseProof ("K" with "[BLACKS]") as "> [ARROWS [DUTY PTX]]".
      { clear SUCCESS ps PENDS. iStopProof.
        induction ls; ss. destruct a. iIntros "[HD TL]".
        iFrame. iApply IHls. auto.
      }
      iModIntro. iFrame.
      iApply (list_prop_sum_map_inv with "WHITES").
      i. iIntros "WHITE". iApply FairRA.white_prism_id_rev. auto.
    Qed.

  End TARGET.

End ObligationRA.
