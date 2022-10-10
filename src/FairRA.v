From sflib Require Import sflib.
From Fairness Require Import PCM IProp IPM.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.PropExtensionality.
From Fairness Require Import Axioms MonotonePCM.
Require Import Program.

Set Implicit Arguments.

Module AddLattice.
  Section LATTICE.
    Variable car: Type.
    Class t := mk {
        le: car -> car -> Prop;
        unit: car;
        add: car -> car -> car;

        le_PreOrder:> PreOrder le;
        add_assoc_le: forall a0 a1 a2, le (add a0 (add a1 a2)) (add (add a0 a1) a2);
        add_comm_le: forall a0 a1, le (add a0 a1) (add a1 a0);
        add_unit_le_l: forall a, le (add a unit) a;
        add_base_l: forall a0 a1, le a0 (add a0 a1);
        le_add_l: forall a0 a1 a2 (LE: le a1 a2), le (add a0 a1) (add a0 a2);
      }.

    Context `{t}.

    Definition eq (a0 a1: car): Prop := le a0 a1 /\ le a1 a0.

    Global Program Instance eq_Equivalence: Equivalence eq.
    Next Obligation.
    Proof.
      unfold eq. ii. split.
      { reflexivity. }
      { reflexivity. }
    Qed.
    Next Obligation.
    Proof.
      unfold eq. ii. des. split; auto.
    Qed.
    Next Obligation.
    Proof.
      unfold eq. ii. des. split.
      { etrans; eauto. }
      { etrans; eauto. }
    Qed.

    Lemma add_assoc_eq a0 a1 a2
      :
      eq (add a0 (add a1 a2)) (add (add a0 a1) a2).
    Proof.
      split.
      { eapply add_assoc_le. }
      { etrans.
        { eapply add_comm_le. }
        etrans.
        { eapply add_assoc_le. }
        etrans.
        { eapply add_comm_le. }
        etrans.
        { eapply add_assoc_le. }
        { eapply add_comm_le. }
      }
    Qed.

    Lemma add_comm_eq a0 a1
      :
      eq (add a0 a1) (add a1 a0).
    Proof.
      split.
      { eapply add_comm_le. }
      { eapply add_comm_le. }
    Qed.

    Lemma add_unit_le_r a
      :
      le (add unit a) a.
    Proof.
      etrans.
      { eapply add_comm_le. }
      { eapply add_unit_le_l. }
    Qed.

    Lemma add_unit_eq_l a
      :
      eq (add a unit) a.
    Proof.
      split.
      { apply add_unit_le_l. }
      { apply add_base_l. }
    Qed.

    Lemma add_unit_eq_r a
      :
      eq (add unit a) a.
    Proof.
      etrans.
      { eapply add_comm_eq. }
      { eapply add_unit_eq_l. }
    Qed.

    Lemma add_base_r a0 a1
      :
      le a1 (add a0 a1).
    Proof.
      etrans.
      { eapply add_base_l. }
      { eapply add_comm_le. }
    Qed.

    Lemma le_add_r a0 a1 a2
          (LE: le a0 a1)
      :
      le (add a0 a2) (add a1 a2).
    Proof.
      i. etrans.
      { eapply add_comm_le. }
      etrans.
      { eapply le_add_l; eauto. }
      { eapply add_comm_le. }
    Qed.

    Lemma le_unit a
      :
      le unit a.
    Proof.
      etrans.
      { eapply add_base_r. }
      { eapply add_unit_le_l. }
    Qed.

    Lemma eq_add_l a0 a1 a2
          (EQ: eq a1 a2)
      :
      eq (add a0 a1) (add a0 a2).
    Proof.
      unfold eq in *. des. split.
      { eapply le_add_l; eauto. }
      { eapply le_add_l; eauto. }
    Qed.

    Lemma eq_add_r a0 a1 a2
          (EQ: eq a0 a1)
      :
      eq (add a0 a2) (add a1 a2).
    Proof.
      unfold eq in *. des. split.
      { eapply le_add_r; eauto. }
      { eapply le_add_r; eauto. }
    Qed.
  End LATTICE.
End AddLattice.


Global Program Instance nat_AddLattice: AddLattice.t nat :=
  @AddLattice.mk _ le 0 Nat.add _ _ _ _ _ _ .
Next Obligation. Proof. lia. Qed.
Next Obligation. Proof. lia. Qed.
Next Obligation. Proof. lia. Qed.
Next Obligation. Proof. lia. Qed.
Next Obligation. Proof. lia. Qed.

From Ordinal Require Import Ordinal Hessenberg.

Global Program Instance ord_AddLattice: AddLattice.t Ord.t :=
  @AddLattice.mk _ Ord.le Ord.O Hessenberg.add _ _ _ _ _ _ .
Next Obligation.
Proof.
  eapply Hessenberg.add_assoc.
Qed.
Next Obligation.
Proof.
  eapply Hessenberg.add_comm.
Qed.
Next Obligation.
Proof.
  eapply Hessenberg.add_O_r.
Qed.
Next Obligation.
Proof.
  eapply Hessenberg.add_base_l.
Qed.
Next Obligation.
Proof.
  eapply Hessenberg.le_add_r; eauto.
Qed.

Lemma ord_AddLattice_eq (a0 a1: Ord.t):
  AddLattice.eq a0 a1 <-> Ord.eq a0 a1.
Proof.
  auto.
Qed.

Lemma nat_AddLattice_eq (a0 a1: nat):
  AddLattice.eq a0 a1 <-> a0 = a1.
Proof.
  split.
  { i. red in H. des. ss. lia. }
  { i. subst. reflexivity. }
Qed.


Module Fuel.
  Section LATTICE.
    Variable (A: Type).
    Context `{AddLattice.t A}.

    Record quotient :=
      mk {
          collection:> A -> Prop;
          generated: exists a0, forall a1,
            collection a1 <-> AddLattice.le a0 a1;
        }.

    Global Program Definition from_lattice (a: A): quotient :=
      mk (AddLattice.le a) _.
    Next Obligation.
    Proof.
      exists a. i. auto.
    Qed.

    Definition le (s0 s1: quotient): Prop :=
      forall a, s1 a -> s0 a.

    Global Program Instance le_PreOrder: PreOrder le.
    Next Obligation.
    Proof.
      ii. auto.
    Qed.
    Next Obligation.
    Proof.
      ii. eauto.
    Qed.

    Lemma le_anstisymmetric s0 s1
          (LE0: le s0 s1)
          (LE1: le s1 s0)
      :
      s0 = s1.
    Proof.
      destruct s0, s1.
      assert (collection0 = collection1).
      { extensionality a. eapply propositional_extensionality.
        red in LE0. red in LE1. ss. split; auto.
      }
      subst. f_equal. eapply proof_irrelevance.
    Qed.

    Lemma ext (s0 s1: quotient)
          (EXT: forall a, s0 a <-> s1 a)
      :
      s0 = s1.
    Proof.
      eapply le_anstisymmetric.
      { ii. eapply EXT; auto. }
      { ii. eapply EXT; auto. }
    Qed.

    Lemma from_lattice_exist (s: quotient)
      :
      exists a, s = from_lattice a.
    Proof.
      hexploit generated. i. des. exists a0.
      eapply ext. i. rewrite H0. ss.
    Qed.

    Lemma from_lattice_le a0 a1
      :
      from_lattice a0 a1 <-> AddLattice.le a0 a1.
    Proof.
      ss.
    Qed.

    Lemma le_iff a0 a1
      :
      le (from_lattice a0) (from_lattice a1) <-> AddLattice.le a0 a1.
    Proof.
      split.
      { i. exploit H0.
        { s. reflexivity. }
        i. rewrite <- from_lattice_le. ss.
      }
      { ii. ss. etrans; eauto. }
    Qed.

    Lemma from_lattice_eq a0 a1
      :
      from_lattice a0 = from_lattice a1 <-> AddLattice.eq a0 a1.
    Proof.
      split.
      { i. split.
        { rewrite <- from_lattice_le. rewrite H0. ss. reflexivity. }
        { rewrite <- from_lattice_le. rewrite <- H0. ss. reflexivity. }
      }
      { i. red in H0. des. eapply ext. i. etrans.
        { eapply from_lattice_le. }
        etrans.
        2:{ symmetry. eapply from_lattice_le. }
        split. i.
        { etransitivity; eauto. }
        { etransitivity; eauto. }
      }
    Qed.

    Global Program Definition quotient_add (s0 s1: quotient): quotient :=
      mk (fun a => exists a0 a1 (IN0: s0 a0) (IN1: s1 a1),
              AddLattice.le (AddLattice.add a0 a1) a) _.
    Next Obligation.
      hexploit (from_lattice_exist s0).
      hexploit (from_lattice_exist s1). i. des. subst.
      exists (AddLattice.add a a0). i. split.
      { i. des. etrans.
        { eapply AddLattice.le_add_r. erewrite <- from_lattice_le. eauto. }
        etrans.
        { eapply AddLattice.le_add_l. erewrite <- from_lattice_le. eauto. }
        { eauto. }
      }
      i. esplits.
      { erewrite from_lattice_le. reflexivity. }
      { erewrite from_lattice_le. reflexivity. }
      { eauto. }
    Qed.

    Lemma from_lattice_add a0 a1
      :
      quotient_add (from_lattice a0) (from_lattice a1)
      =
        from_lattice (AddLattice.add a0 a1).
    Proof.
      eapply ext. i. split.
      { i. ss. des. etrans.
        { eapply AddLattice.le_add_r. eauto. }
        etrans.
        { eapply AddLattice.le_add_l. eauto. }
        { eauto. }
      }
      { i. ss. esplits.
        { reflexivity. }
        { reflexivity. }
        { eauto. }
      }
    Qed.

    Lemma quotient_add_comm s0 s1
      :
      quotient_add s0 s1
      =
        quotient_add s1 s0.
    Proof.
      hexploit (from_lattice_exist s0).
      hexploit (from_lattice_exist s1). i. des. subst.
      rewrite ! from_lattice_add.
      eapply from_lattice_eq. eapply AddLattice.add_comm_eq.
    Qed.

    Lemma quotient_add_assoc s0 s1 s2
      :
      quotient_add s0 (quotient_add s1 s2)
      =
        quotient_add (quotient_add s0 s1) s2.
    Proof.
      hexploit (from_lattice_exist s0).
      hexploit (from_lattice_exist s1).
      hexploit (from_lattice_exist s2). i. des. subst.
      rewrite ! from_lattice_add.
      eapply from_lattice_eq. eapply AddLattice.add_assoc_eq.
    Qed.

    Variant car: Type :=
      | frag (s: quotient)
      | excl (e: quotient) (s: quotient)
      | boom
    .

    Definition black (a: A): car :=
      excl (from_lattice a) (from_lattice (@AddLattice.unit _ _)).

    Definition white (a: A): car :=
      frag (from_lattice a).

    Definition unit: car :=
      white (@AddLattice.unit _ _).

    Let add := fun (a0 a1: car) =>
                 match a0, a1 with
                 | frag f0, frag f1 => frag (quotient_add f0 f1)
                 | frag f0, excl e1 f1 => excl e1 (quotient_add f0 f1)
                 | excl e0 f0, frag f1 => excl e0 (quotient_add f0 f1)
                 | _, _ => boom
                 end.

    Let wf := fun (a: car) =>
                match a with
                | frag f => True
                | excl e f => le f e
                | boom => False
                end.

    Let core := fun (a: car) => unit.

    Global Program Instance t: URA.t := {
        car := car;
        unit := unit;
        _add := add;
        _wf := wf;
        core := core;
      }
    .
    Next Obligation.
      destruct a, b; ss.
      { f_equal. eapply quotient_add_comm. }
      { f_equal. eapply quotient_add_comm. }
      { f_equal. eapply quotient_add_comm. }
    Qed.
    Next Obligation.
      destruct a, b, c; ss.
      { f_equal. eapply quotient_add_assoc. }
      { f_equal. eapply quotient_add_assoc. }
      { f_equal. eapply quotient_add_assoc. }
      { f_equal. eapply quotient_add_assoc. }
    Qed.
    Next Obligation.
      unseal "ra". destruct a; ss.
      { f_equal.
        hexploit (from_lattice_exist s). i. des. subst.
        rewrite from_lattice_add.
        eapply from_lattice_eq. eapply AddLattice.add_unit_eq_l.
      }
      { f_equal.
        hexploit (from_lattice_exist s). i. des. subst.
        rewrite from_lattice_add.
        eapply from_lattice_eq. eapply AddLattice.add_unit_eq_l.
      }
    Qed.
    Next Obligation.
      unseal "ra". ss.
    Qed.
    Next Obligation.
      unseal "ra". destruct a, b; ss.
      hexploit (from_lattice_exist s).
      hexploit (from_lattice_exist s0).
      hexploit (from_lattice_exist e). i. des. subst.
      rewrite from_lattice_add in H0.
      rewrite le_iff in H0. rewrite le_iff.
      etrans; eauto. eapply AddLattice.add_base_l.
    Qed.
    Next Obligation.
      unseal "ra". destruct a; ss.
      { f_equal.
        hexploit (from_lattice_exist s). i. des. subst.
        rewrite from_lattice_add.
        eapply from_lattice_eq.
        eapply AddLattice.add_unit_eq_r.
      }
      { f_equal.
        hexploit (from_lattice_exist s). i. des. subst.
        rewrite from_lattice_add.
        eapply from_lattice_eq.
        eapply AddLattice.add_unit_eq_r.
      }
    Qed.
    Next Obligation.
      unseal "ra". exists unit. unfold core, unit, white. ss.
      f_equal.
      rewrite from_lattice_add.
      eapply from_lattice_eq. symmetry.
      eapply AddLattice.add_unit_eq_r.
    Qed.

    Lemma white_sum (a0 a1: A)
      :
      white a0 ⋅ white a1
      =
        white (AddLattice.add a0 a1).
    Proof.
      ur. unfold white. f_equal.
      rewrite from_lattice_add. auto.
    Qed.

    Lemma white_eq (a0 a1: A)
          (EQ: AddLattice.eq a0 a1)
      :
      white a0 = white a1.
    Proof.
      unfold white. f_equal.
      eapply from_lattice_eq; eauto.
    Qed.

    Lemma black_eq (a0 a1: A)
          (EQ: AddLattice.eq a0 a1)
      :
      black a0 = black a1.
    Proof.
      unfold black. f_equal.
      eapply from_lattice_eq; eauto.
    Qed.

    Lemma white_mon (a0 a1: A)
          (LE: AddLattice.le a0 a1)
      :
      URA.updatable (white a1) (white a0).
    Proof.
      ii. ur in H0. ur. unfold wf in *. des_ifs.
      etrans; eauto.
      hexploit (from_lattice_exist s0). i. des. subst.
      rewrite ! from_lattice_add. eapply le_iff.
      eapply AddLattice.le_add_r. auto.
    Qed.

    Lemma black_mon (a0 a1: A)
          (LE: AddLattice.le a0 a1)
      :
      URA.updatable (black a0) (black a1).
    Proof.
      ii. ur in H0. ur. unfold wf in *. des_ifs.
      hexploit (from_lattice_exist s0). i. des. subst.
      rewrite from_lattice_add in *. etrans; eauto.
      eapply le_iff. auto.
    Qed.

    Lemma success_update a0 a1
      :
      URA.updatable
        (black a0)
        (black (AddLattice.add a0 a1) ⋅ white a1).
    Proof.
      ii. ur in H0. ur. unfold wf in *. des_ifs.
      hexploit (from_lattice_exist s0). i. des. subst.
      rewrite ! from_lattice_add in H0.
      rewrite ! from_lattice_add.
      erewrite le_iff in H0. erewrite le_iff.
      etrans.
      { eapply AddLattice.le_add_l. etrans.
        { eapply AddLattice.add_base_r. }
        { eapply H0. }
      }
      etrans.
      { eapply AddLattice.add_comm_le. }
      { eapply AddLattice.le_add_l.
        eapply AddLattice.add_unit_le_r.
      }
    Qed.

    Lemma decr_update a0 a1
      :
      URA.updatable_set
        (black a0 ⋅ white a1)
        (fun r => exists a2, r = black a2 /\ AddLattice.le (AddLattice.add a1 a2) a0).
    Proof.
      ii. ur in WF. unfold wf in WF. des_ifs.
      hexploit (from_lattice_exist s0). i. des. subst.
      rewrite ! from_lattice_add in WF. rewrite le_iff in WF.
      eexists. esplits.
      { reflexivity. }
      { instantiate (1:=a). etrans; eauto.
        eapply AddLattice.le_add_r. eapply AddLattice.add_base_r.
      }
      ur. rewrite ! from_lattice_add. rewrite le_iff.
      eapply AddLattice.add_unit_le_r.
    Qed.
  End LATTICE.
End Fuel.


From Paco Require Import paco.

Section INFSUM.
  Variable M: URA.t.

  Variant _infsum (infsum: forall (X: Type) (P: X -> M -> Prop) (r: M), Prop)
          (X: Type) (P: X -> M -> Prop) (r: M): Prop :=
    | infsum_intro
        (INF: forall Y (Q: Y -> M -> Prop) x
                     (f: Y -> X)
                     (PRED: forall y r, P (f y) r -> Q y r)
                     (INJ: forall y0 y1, f y0 = f y1 -> y0 = y1)
                     (MINUS: forall y, f y <> x),
          exists r0 r1,
            r = r0 ⋅ r1 /\ P x r0 /\ infsum Y Q r1)
  .

  Lemma infsum_monotone: monotone3 _infsum.
  Proof.
    ii. inv IN. econs; eauto.
    i. hexploit INF; eauto. i. des. esplits; eauto.
  Qed.
  Hint Resolve infsum_monotone: paco.
  Hint Resolve cpn3_wcompat: paco.

  Definition infsum := paco3 _infsum bot3.

  Lemma infsum_void
        (X: Type) (EMPTY: forall (x: X), False)
        (P: X -> M -> Prop)
        (r: M)
    :
    infsum P r.
  Proof.
    pfold. econs. i. exfalso. eapply EMPTY; eauto.
  Qed.

  Lemma singleton_to_infsum (r: M) (P: M -> Prop)
        (SAT: P r)
    :
    infsum (fun _: unit => P) r.
  Proof.
    pfold. econs. i.
    exists r, URA.unit. rewrite URA.unit_id. splits; auto.
    left. eapply infsum_void; eauto.
    i. eapply (MINUS x0). destruct (f x0), x; ss.
  Qed.

  Variant infsum_extendC (R: forall (X: Type) (P: X -> M -> Prop) (r: M), Prop)
          X (P: X -> M -> Prop) (r: M): Prop :=
    | infsum_extendC_intro
        r0 r1
        (SAT: R X P r0)
        (EQ: r = r0 ⋅ r1)
  .

  Lemma infsum_extendC_spec
    :
    infsum_extendC <4= gupaco3 _infsum (cpn3 _infsum).
  Proof.
    eapply wrespect3_uclo; eauto with paco. econs.
    { ii. inv IN. econs; eauto. }
    i. inv PR. eapply GF in SAT. inv SAT.
    econs. i. hexploit INF; eauto. i. des. subst.
    exists r2, (r3 ⋅ r1). splits; auto.
    { r_solve. }
    eapply rclo3_clo_base. econs; eauto.
  Qed.

  Variant infsum_monoC (R: forall (X: Type) (P: X -> M -> Prop) (r: M), Prop)
          Y (Q: Y -> M -> Prop) (r: M): Prop :=
    | infsum_monoC_intro
        X (f: Y -> X) (P: X -> M -> Prop)
        (PRED: forall y r, P (f y) r -> Q y r)
        (INJ: forall y0 y1, f y0 = f y1 -> y0 = y1)
        (SAT: R X P r)
  .

  Lemma infsum_monoC_spec
    :
    infsum_monoC <4= gupaco3 _infsum (cpn3 _infsum).
  Proof.
    eapply wrespect3_uclo; eauto with paco. econs.
    { ii. inv IN. econs; eauto. }
    i. inv PR. eapply GF in SAT. inv SAT.
    econs. i.
    hexploit (INF Y Q (f x) (fun x => f (f0 x))); auto.
    { ii. eapply INJ in H. eapply MINUS; eauto. }
    i. des. exists r0, r1. splits; auto.
    eapply rclo3_base. auto.
  Qed.

  Lemma infsum_unfold
        (X: Type) (P: X -> M -> Prop) (r: M)
        (INF: infsum P r)
        Y (Q: Y -> M -> Prop) x
        (f: Y -> X)
        (PRED: forall y r, P (f y) r -> Q y r)
        (INJ: forall y0 y1, f y0 = f y1 -> y0 = y1)
        (MINUS: forall y, f y <> x)
    :
    exists r0 r1,
      r = r0 ⋅ r1 /\ P x r0 /\ infsum Q r1.
  Proof.
    punfold INF. inv INF. hexploit INF0; eauto.
    i. des. subst. pclearbot. esplits; eauto.
  Qed.

  Let partial_fun_to_total X Y (f: X -> option Y)
      (TOTAL: forall x, f x <> None)
    :
    X -> Y.
  Proof.
    intros x. destruct (f x) eqn:EQ.
    { exact y. }
    { destruct (TOTAL _ EQ). }
  Defined.

  Lemma partial_fun_to_total_eq
        X Y (f: X -> option Y)
        (TOTAL: forall x, f x <> None)
        x y
        (EQ: f x = Some y)
    :
    partial_fun_to_total f TOTAL x = y.
  Proof.
  Admitted.

  Lemma infsum_fold_aux
    :
    forall
      (X: Type) (P0: X -> M -> Prop) (r0: M)
      (INF: infsum P0 r0)
      (P1: M -> Prop) (r1: M)
      (SAT: P1 r1),
      infsum (option_rect _ P0 P1) (r0 ⋅ r1).
  Proof.
    ginit. gcofix CIH. i. gstep. econs. i.
    destruct x.
    { admit. }
    { exists r1, r0. splits.
      { eapply URA.add_comm. }
      { ss. }
      { guclo infsum_monoC_spec.
        econs.
        3:{ gfinal. right. eapply paco3_mon; eauto. ss. }
        { instantiate (1:=partial_fun_to_total f MINUS).
          intros y. destruct (f y) eqn:EQ.
          2:{ destruct (MINUS _ EQ). }
          i. hexploit partial_fun_to_total_eq; eauto. i.
          erewrite H0 in H. eapply PRED. rewrite EQ. ss.
        }
        {
  Admitted.

  Lemma infsum_fold
    :
    forall
      (X: Type) (P0: X -> M -> Prop) (r0: M)
      (INF: infsum P0 r0)
      (P1: M -> Prop) (r1: M)
      (SAT: P1 r1)
      Y (Q: Y -> M -> Prop)
      (f: Y -> option X)
      (PRED0: forall y x r (EQ: f y = Some x), P0 x r -> Q y r)
      (PRED1: forall y r (EQ: f y = None), P1 r -> Q y r)
      (INJ: forall y0 y1, f y0 = f y1 -> y0 = y1),
      infsum Q (r0 ⋅ r1).
  Proof.
  Admitted.

  Lemma infsum_to_singleton
        (X: Type) (P: X -> M -> Prop)
        (r: M)
        (INF: infsum P r)
        x
    :
    exists r0 r1, r = r0 ⋅ r1 /\ P x r0.
  Proof.
    punfold INF. inv INF.
    hexploit (INF0 (sig (fun y => y <> x)) (fun y => P (proj1_sig y)) x proj1_sig).
    { i. auto. }
    { i. destruct y0, y1. ss. subst. f_equal. eapply proof_irrelevance. }
    { i. eapply (proj2_sig y). }
    i. des. esplits; eauto.
  Qed.
End INFSUM.

Module FairRA.
  Section FAIR.
    Variable (Id: Type).
    Variable (O: Type).
    Context `{AddLattice.t O}.

    Definition t: URA.t :=
      (Id ==> @Fuel.t O _)%ra.

    Set Printing All.

    Definition black (i:


    Variable (M: URA.t).
    Definition t: URA.t := Auth.t M.

    Context `{ING: @GRA.inG t Σ}.

    Definition curr (n: M): iProp :=
      OwnM (Auth.black n).

    Definition decr (n: M): iProp :=
      OwnM (Auth.white n).

    Lemma decr_sum (n0 n1: M)
      :
      (decr n0)
        -∗
        (decr n1)
        -∗
        (decr (n0 ⋅ n1)).
    Proof.
      iIntros "H0 H1". iCombine "H0 H1" as "H".
      ur. ur. auto.
    Qed.

    Lemma decr_split (n0 n1: M)
      :
      (decr (n0 ⋅ n1))
        -∗
        (decr n0 ** decr n1).
    Proof.
      iIntros "H". unfold decr.
      replace (Auth.white (n0 ⋅ n1)) with (Auth.white n0 ⋅ Auth.white n1).
      { iDestruct "H" as "[H0 H1]". iFrame. }
      repeat ur. auto.
    Qed.

    Lemma decr_0 (n0 n1: M)
      :
      ⊢
        (decr URA.unit).
    Proof.
      iIntros "". iApply (@OwnM_unit _ _ ING).
    Qed.

    Lemma decr_mon (n0 n1: M)
          (LE: URA.extends n0 n1)
      :
      (decr n1)
        -∗
        (decr n0).
    Proof.
      rr in LE. des. subst.
      iIntros "H". iPoseProof (decr_split with "H") as "[H0 H1]". iFrame.
    Qed.

    Lemma curr_mon (n0 n1: M)
          (LE: URA.extends n0 n1)
          (WF: URA.wf n1)
      :
      (curr n0)
        -∗
        (#=> curr n1).
    Proof.
      iIntros "H". iPoseProof (OwnM_Upd with "H") as "> H".
      { instantiate (1:=Auth.black n1).
        ii. ur in H. des_ifs. des.
        ur. split; auto. etrans; eauto.
      }
      iModIntro. eauto.
    Qed.

    Lemma success_update n2 n0 n1
          (WF: URA.wf (n1 ⋅ n2))
      :
      (decr n0)
        -∗
        (curr n1)
        -∗
        (#=> (decr n2 ** ∃ n, curr n)).
    Proof.
      iIntros "H0 H1".
      iCombine "H1 H0" as "H".
      iOwnWf "H".
      iPoseProof (OwnM_Upd_set with "H") as "> H".
      { instantiate (1:= fun r => exists ctx, r = Auth.black (n2 ⋅ ctx) ⋅ Auth.white (n2)).
        ii. ur in WF0. des_ifs. des.
        exists (Auth.black (n2 ⋅ f0) ⋅ Auth.white n2).
        esplits; eauto. rewrite URA.unfold_add. ss.
        rewrite URA.unfold_wf. ss. split.
        { rewrite URA.unit_idl. reflexivity. }
        { r in WF0. des. subst.
          eapply URA.wf_mon.
          instantiate (1:=ctx ⋅ n0). r_wf WF.
        }
      }
      iDestruct "H" as "[% [% H]]". des. subst.
      iDestruct "H" as "[H0 H1]". iModIntro.
      iFrame. iExists _. eauto.
    Qed.

    Lemma fail_update n0 n1 n2
          (LE: URA.extends (n0 ⋅ n1) n2)
      :
      (decr n2)
        -∗
        (decr n0 ** decr n1).
    Proof.
      iIntros "H". iApply decr_split.
      iApply (decr_mon with "H"); eauto.
    Qed.

    Lemma decr_update_gen n0 n1
      :
      (curr n0)
        -∗
        (decr n1)
        -∗
        (#=> (∃ n, ⌜(n0 = n ⋅ n1)%nat⌝ ** curr n)).
    Proof.
      iIntros "H0 H1".
      iCombine "H1 H0" as "H".
      iOwnWf "H". rewrite URA.unfold_add in H. ss.
      rewrite URA.unfold_wf in H. ss. des.
      r in H. des. subst.
      iPoseProof (OwnM_Upd with "H") as "> H".
      { instantiate (1:=Auth.black (n1)). ii.
        rewrite URA.unfold_add in H. ss.
        rewrite URA.unfold_wf in H. ss. des_ifs. des.
        rewrite URA.unfold_add. rewrite URA.unfold_wf. ss.
        split.
        { admit. }
        { admit. }
      }
      iModIntro. iExists _. iSplit; eauto.
      iPureIntro. r_solve. change (@URA.unit NatRA.t) with 0 in *. lia.



in H. ss. des_ifs. des.


des.
        r in H. des.

repeat ur in H1. des_ifs. des.
        rr in H1. des. repeat ur in H1.
        repeat ur. splits; auto. exists ctx0.
        repeat ur. change (@URA.unit NatRA.t) with 0 in *. lia.
      }
      iModIntro. iExists _. iSplit; eauto.
      iPureIntro. change (@URA.unit NatRA.t) with 0 in *. lia.
    Qed.

    Lemma decr_update n1
      :
      (curr n1)
        -∗
        (decr 1)
        -∗
        (#=> (∃ n0, ⌜n0 < n1⌝ ** curr n0)).
    Proof.
      iIntros "H0 H1".
      iPoseProof (decr_update_gen with "H0 H1") as "> [% [% H]]".
      iModIntro. iExists _. iSplit; eauto. iPureIntro. lia.
    Qed.
  End FAIRTGT.
End FairTgtRA.


Module FairTgtRA.
  Section FAIRTGT.
    Variable (M: URA.t).
    Definition t: URA.t := Auth.t M.

    Context `{ING: @GRA.inG t Σ}.

    Definition curr (n: M): iProp :=
      OwnM (Auth.black n).

    Definition decr (n: M): iProp :=
      OwnM (Auth.white n).

    Lemma decr_sum (n0 n1: M)
      :
      (decr n0)
        -∗
        (decr n1)
        -∗
        (decr (n0 ⋅ n1)).
    Proof.
      iIntros "H0 H1". iCombine "H0 H1" as "H".
      ur. ur. auto.
    Qed.

    Lemma decr_split (n0 n1: M)
      :
      (decr (n0 ⋅ n1))
        -∗
        (decr n0 ** decr n1).
    Proof.
      iIntros "H". unfold decr.
      replace (Auth.white (n0 ⋅ n1)) with (Auth.white n0 ⋅ Auth.white n1).
      { iDestruct "H" as "[H0 H1]". iFrame. }
      repeat ur. auto.
    Qed.

    Lemma decr_0 (n0 n1: M)
      :
      ⊢
        (decr URA.unit).
    Proof.
      iIntros "". iApply (@OwnM_unit _ _ ING).
    Qed.

    Lemma decr_mon (n0 n1: M)
          (LE: URA.extends n0 n1)
      :
      (decr n1)
        -∗
        (decr n0).
    Proof.
      rr in LE. des. subst.
      iIntros "H". iPoseProof (decr_split with "H") as "[H0 H1]". iFrame.
    Qed.

    Lemma curr_mon (n0 n1: M)
          (LE: URA.extends n0 n1)
          (WF: URA.wf n1)
      :
      (curr n0)
        -∗
        (#=> curr n1).
    Proof.
      iIntros "H". iPoseProof (OwnM_Upd with "H") as "> H".
      { instantiate (1:=Auth.black n1).
        ii. ur in H. des_ifs. des.
        ur. split; auto. etrans; eauto.
      }
      iModIntro. eauto.
    Qed.

    Lemma success_update n2 n0 n1
          (WF: URA.wf (n1 ⋅ n2))
      :
      (decr n0)
        -∗
        (curr n1)
        -∗
        (#=> (decr n2 ** ∃ n, curr n)).
    Proof.
      iIntros "H0 H1".
      iCombine "H1 H0" as "H".
      iOwnWf "H".
      iPoseProof (OwnM_Upd_set with "H") as "> H".
      { instantiate (1:= fun r => exists ctx, r = Auth.black (n2 ⋅ ctx) ⋅ Auth.white (n2)).
        ii. ur in WF0. des_ifs. des.
        exists (Auth.black (n2 ⋅ f0) ⋅ Auth.white n2).
        esplits; eauto. rewrite URA.unfold_add. ss.
        rewrite URA.unfold_wf. ss. split.
        { rewrite URA.unit_idl. reflexivity. }
        { r in WF0. des. subst.
          eapply URA.wf_mon.
          instantiate (1:=ctx ⋅ n0). r_wf WF.
        }
      }
      iDestruct "H" as "[% [% H]]". des. subst.
      iDestruct "H" as "[H0 H1]". iModIntro.
      iFrame. iExists _. eauto.
    Qed.

    Lemma fail_update n0 n1 n2
          (LE: URA.extends (n0 ⋅ n1) n2)
      :
      (decr n2)
        -∗
        (decr n0 ** decr n1).
    Proof.
      iIntros "H". iApply decr_split.
      iApply (decr_mon with "H"); eauto.
    Qed.

    Lemma decr_update_gen n0 n1
      :
      (curr n0)
        -∗
        (decr n1)
        -∗
        (#=> (∃ n, ⌜(n0 = n ⋅ n1)%nat⌝ ** curr n)).
    Proof.
      iIntros "H0 H1".
      iCombine "H1 H0" as "H".
      iOwnWf "H". rewrite URA.unfold_add in H. ss.
      rewrite URA.unfold_wf in H. ss. des.
      r in H. des. subst.
      iPoseProof (OwnM_Upd with "H") as "> H".
      { instantiate (1:=Auth.black (n1)). ii.
        rewrite URA.unfold_add in H. ss.
        rewrite URA.unfold_wf in H. ss. des_ifs. des.
        rewrite URA.unfold_add. rewrite URA.unfold_wf. ss.
        split.
        { admit. }
        { admit. }
      }
      iModIntro. iExists _. iSplit; eauto.
      iPureIntro. r_solve. change (@URA.unit NatRA.t) with 0 in *. lia.



in H. ss. des_ifs. des.


des.
        r in H. des.

repeat ur in H1. des_ifs. des.
        rr in H1. des. repeat ur in H1.
        repeat ur. splits; auto. exists ctx0.
        repeat ur. change (@URA.unit NatRA.t) with 0 in *. lia.
      }
      iModIntro. iExists _. iSplit; eauto.
      iPureIntro. change (@URA.unit NatRA.t) with 0 in *. lia.
    Qed.

    Lemma decr_update n1
      :
      (curr n1)
        -∗
        (decr 1)
        -∗
        (#=> (∃ n0, ⌜n0 < n1⌝ ** curr n0)).
    Proof.
      iIntros "H0 H1".
      iPoseProof (decr_update_gen with "H0 H1") as "> [% [% H]]".
      iModIntro. iExists _. iSplit; eauto. iPureIntro. lia.
    Qed.
  End FAIRTGT.
End FairTgtRA.


Module FairTgtRA.
  Section FAIRTGT.
    Definition t: URA.t := Auth.t NatRA.t.

    Context `{ING: @GRA.inG t Σ}.

    Definition curr (n: nat): iProp :=
      OwnM (Auth.black (n: NatRA.t)).

    Definition decr (n: nat): iProp :=
      OwnM (Auth.white (n: NatRA.t)).

    Lemma decr_sum (n0 n1: nat)
      :
      (decr n0)
        -∗
        (decr n1)
        -∗
        (decr (n0 + n1)).
    Proof.
      iIntros "H0 H1". iCombine "H0 H1" as "H".
      ur. ur. auto.
    Qed.

    Lemma decr_split (n0 n1: nat)
      :
      (decr (n0 + n1))
        -∗
        (decr n0 ** decr n1).
    Proof.
      iIntros "H". unfold decr.
      replace (Auth.white (n0 + n1: NatRA.t)) with (Auth.white (n0: NatRA.t) ⋅ Auth.white (n1: NatRA.t)).
      { iDestruct "H" as "[H0 H1]". iFrame. }
      repeat ur. auto.
    Qed.

    Lemma decr_0 (n0 n1: nat)
      :
      ⊢
        (decr 0).
    Proof.
      iIntros "". iApply (@OwnM_unit _ _ ING).
    Qed.

    Lemma decr_mon (n0 n1: nat)
          (LE: n0 <= n1)
      :
      (decr n1)
        -∗
        (decr n0).
    Proof.
      assert (exists n, n0 + n = n1).
      { exists (n1 - n0). lia. }
      des. subst. iIntros "H".
      iPoseProof (decr_split with "H") as "[H0 H1]". iFrame.
    Qed.

    Lemma curr_mon (n0 n1: nat)
          (LE: n0 <= n1)
      :
      (curr n0)
        -∗
        (#=> curr n1).
    Proof.
      iIntros "H". iPoseProof (OwnM_Upd with "H") as "> H".
      { instantiate (1:=Auth.black (n1: NatRA.t)).
        ii. repeat ur in H. des_ifs. des.
        rr in H. des. repeat ur in H.
        repeat ur. splits; auto. exists (n1 - e + ctx).
        repeat ur. lia.
      }
      iModIntro. eauto.
    Qed.

    Lemma success_update n2 n0 n1
      :
      (decr n0)
        -∗
        (curr n1)
        -∗
        (#=> (decr n2 ** ∃ n, curr n)).
    Proof.
      iIntros "H0 H1".
      iCombine "H1 H0" as "H".
      iPoseProof (OwnM_Upd_set with "H") as "> H".
      { instantiate (1:= fun r => exists ctx, r = Auth.black (n2 + ctx: NatRA.t) ⋅ Auth.white (n2: NatRA.t)).
        ii. ur in WF. des_ifs. des.
        exists (Auth.black (n2 + f0: NatRA.t) ⋅ Auth.white (n2: NatRA.t)).
        esplits; eauto. repeat ur. split; auto.
        exists 0. repeat ur. auto.
      }
      iDestruct "H" as "[% [% H]]". des. subst.
      iDestruct "H" as "[H0 H1]". iModIntro.
      iFrame. iExists _. eauto.
    Qed.

    Lemma fail_update n0 n1
          (LT: n0 < n1)
      :
      (decr n1)
        -∗
        (decr n0 ** decr 1).
    Proof.
      assert (exists n, n1 = n + n0 + 1).
      { exists (n1 - n0 - 1). lia. }
      des. subst.
      iIntros "H".
      iPoseProof (decr_split with "H") as "[H0 H1]".
      iPoseProof (decr_split with "H0") as "[H0 H2]".
      iFrame.
    Qed.

    Lemma decr_update_gen n0 n1
      :
      (curr n0)
        -∗
        (decr n1)
        -∗
        (#=> (∃ n, ⌜(n0 = n + n1)%nat⌝ ** curr n)).
    Proof.
      iIntros "H0 H1".
      iCombine "H1 H0" as "H".
      iOwnWf "H". repeat ur in H. des. rr in H. des.
      ur in H. ss.
      iPoseProof (OwnM_Upd with "H") as "> H".
      { instantiate (1:=Auth.black ctx). ii.
        repeat ur in H1. des_ifs. des.
        rr in H1. des. repeat ur in H1.
        repeat ur. splits; auto. exists ctx0.
        repeat ur. change (@URA.unit NatRA.t) with 0 in *. lia.
      }
      iModIntro. iExists _. iSplit; eauto.
      iPureIntro. change (@URA.unit NatRA.t) with 0 in *. lia.
    Qed.

    Lemma decr_update n1
      :
      (curr n1)
        -∗
        (decr 1)
        -∗
        (#=> (∃ n0, ⌜n0 < n1⌝ ** curr n0)).
    Proof.
      iIntros "H0 H1".
      iPoseProof (decr_update_gen with "H0 H1") as "> [% [% H]]".
      iModIntro. iExists _. iSplit; eauto. iPureIntro. lia.
    Qed.
  End FAIRTGT.
End FairTgtRA.
