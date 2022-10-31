From sflib Require Import sflib.
From Fairness Require Import PCM IProp IPM.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.PropExtensionality.
From Fairness Require Import Axioms.
Require Import Program.

Set Implicit Arguments.

Module OrderedCM.
  Class t (car: Type) :=
    mk { le: car -> car -> Prop;
         unit: car;
         add: car -> car -> car;

         le_PreOrder:> PreOrder le;
         add_assoc_le: forall a0 a1 a2, le (add a0 (add a1 a2)) (add (add a0 a1) a2);
         add_comm_le: forall a0 a1, le (add a0 a1) (add a1 a0);
         add_unit_le_l: forall a, le (add a unit) a;
         add_base_l: forall a0 a1, le a0 (add a0 a1);
         le_add_l: forall a0 a1 a2 (LE: le a1 a2), le (add a0 a1) (add a0 a2);
      }.

  Section MONOID.
    Variable car: Type.
    Context `{t car}.

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
  End MONOID.
End OrderedCM.


Global Program Instance nat_OrderedCM: OrderedCM.t nat :=
  @OrderedCM.mk _ le 0 Nat.add _ _ _ _ _ _ .
Next Obligation. Proof. lia. Qed.
Next Obligation. Proof. lia. Qed.
Next Obligation. Proof. lia. Qed.
Next Obligation. Proof. lia. Qed.
Next Obligation. Proof. lia. Qed.

From Ordinal Require Import Ordinal Hessenberg.

Global Program Instance ord_OrderedCM: OrderedCM.t Ord.t :=
  @OrderedCM.mk _ Ord.le Ord.O Hessenberg.add _ _ _ _ _ _ .
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

Lemma ord_OrderedCM_eq (a0 a1: Ord.t):
  OrderedCM.eq a0 a1 <-> Ord.eq a0 a1.
Proof.
  auto.
Qed.

Lemma nat_OrderedCM_eq (a0 a1: nat):
  OrderedCM.eq a0 a1 <-> a0 = a1.
Proof.
  split.
  { i. red in H. des. ss. lia. }
  { i. subst. reflexivity. }
Qed.

Module SOrderedCM.
  Class t (car: Type) `{OrderedCM.t car} :=
    mk { lt: car -> car -> Prop;
         one: car;
         lt_iff: forall a0 a1,
           lt a0 a1 <-> OrderedCM.le (OrderedCM.add a0 one) a1;
      }.
End SOrderedCM.

Global Program Instance ord_SOrderedCM: @SOrderedCM.t Ord.t _ :=
  @SOrderedCM.mk _ _ Ord.lt (Ord.S Ord.O) _.
Next Obligation.
Proof.
  rewrite Hessenberg.add_S_r. rewrite Hessenberg.add_O_r.
  split; i.
  { eapply Ord.S_supremum; auto. }
  { eapply Ord.lt_le_lt; eauto. eapply Ord.S_lt. }
Qed.

Global Program Instance nat_SOrderedCM: @SOrderedCM.t nat _ :=
  @SOrderedCM.mk _ _ lt 1 _.
Next Obligation.
Proof.
  lia.
Qed.

Definition prod_add A0 B0 C0 A1 B1 C1
           (f0: A0 -> B0 -> C0)
           (f1: A1 -> B1 -> C1)
  :
  (A0 * A1) -> (B0 * B1) -> (C0 * C1) :=
  fun '(a0, a1) '(b0, b1) => (f0 a0 b0, f1 a1 b1).

Global Program Instance prod_OrderedCM A B `{OrderedCM.t A} `{OrderedCM.t B}
  : OrderedCM.t (A * B)%type :=
  @OrderedCM.mk
    _ (prod_relation OrderedCM.le OrderedCM.le)
    (OrderedCM.unit, OrderedCM.unit)
    (prod_add OrderedCM.add OrderedCM.add)
    _ _ _ _ _ _.
Next Obligation.
Proof.
  econs.
  { ii. destruct x; ss. econs; ss; reflexivity. }
  { ii. inv H1. inv H2. econs; etrans; eauto. }
Qed.
Next Obligation.
Proof.
  econs; ss.
  { eapply OrderedCM.add_assoc_le. }
  { eapply OrderedCM.add_assoc_le. }
Qed.
Next Obligation.
Proof.
  econs; ss.
  { eapply OrderedCM.add_comm_le. }
  { eapply OrderedCM.add_comm_le. }
Qed.
Next Obligation.
Proof.
  econs; ss.
  { eapply OrderedCM.add_unit_le_l. }
  { eapply OrderedCM.add_unit_le_l. }
Qed.
Next Obligation.
Proof.
  econs; ss.
  { eapply OrderedCM.add_base_l. }
  { eapply OrderedCM.add_base_l. }
Qed.
Next Obligation.
Proof.
  inv LE. econs; ss.
  { eapply OrderedCM.le_add_l; auto. }
  { eapply OrderedCM.le_add_l; auto. }
Qed.

Global Program Instance bool_OrderedCM
  : OrderedCM.t bool :=
  @OrderedCM.mk
    _ implb
    false
    orb
    _ _ _ _ _ _.
Next Obligation.
Proof.
  econs.
  { ii. destruct x; auto. }
  { ii. destruct x, y; ss. }
Qed.
Next Obligation.
Proof.
  destruct a0, a1, a2; ss.
Qed.
Next Obligation.
Proof.
  destruct a0, a1; ss.
Qed.
Next Obligation.
Proof.
  destruct a; ss.
Qed.
Next Obligation.
Proof.
  destruct a0, a1; ss.
Qed.
Next Obligation.
Proof.
  destruct a0, a1, a2; ss.
Qed.

Module Fuel.
  Section MONOID.
    Variable (A: Type).

    Record quotient `{OrderedCM.t A} :=
      mk {
          collection:> A -> Prop;
          generated: exists a0, forall a1,
            collection a1 <-> OrderedCM.le a0 a1;
        }.

    Global Program Definition from_monoid `{OrderedCM.t A} (a: A): quotient :=
      mk _ (OrderedCM.le a) _.
    Next Obligation.
    Proof.
      exists a. i. auto.
    Qed.

    Definition le `{OrderedCM.t A} (s0 s1: quotient): Prop :=
      forall a, s1 a -> s0 a.

    Global Program Instance le_PreOrder `{OrderedCM.t A}: PreOrder le.
    Next Obligation.
    Proof.
      ii. auto.
    Qed.
    Next Obligation.
    Proof.
      ii. eauto.
    Qed.

    Lemma le_anstisymmetric`{OrderedCM.t A} s0 s1
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

    Lemma ext `{OrderedCM.t A} (s0 s1: quotient)
          (EXT: forall a, s0 a <-> s1 a)
      :
      s0 = s1.
    Proof.
      eapply le_anstisymmetric.
      { ii. eapply EXT; auto. }
      { ii. eapply EXT; auto. }
    Qed.

    Lemma from_monoid_exist `{OrderedCM.t A} (s: quotient)
      :
      exists a, s = from_monoid a.
    Proof.
      hexploit generated. i. des. exists a0.
      eapply ext. i. rewrite H0. ss.
    Qed.

    Lemma from_monoid_le `{OrderedCM.t A} a0 a1
      :
      from_monoid a0 a1 <-> OrderedCM.le a0 a1.
    Proof.
      ss.
    Qed.

    Lemma le_iff `{OrderedCM.t A} a0 a1
      :
      le (from_monoid a0) (from_monoid a1) <-> OrderedCM.le a0 a1.
    Proof.
      split.
      { i. exploit H0.
        { s. reflexivity. }
        i. rewrite <- from_monoid_le. ss.
      }
      { ii. ss. etrans; eauto. }
    Qed.

    Lemma from_monoid_eq `{OrderedCM.t A} a0 a1
      :
      from_monoid a0 = from_monoid a1 <-> OrderedCM.eq a0 a1.
    Proof.
      split.
      { i. split.
        { rewrite <- from_monoid_le. rewrite H0. ss. reflexivity. }
        { rewrite <- from_monoid_le. rewrite <- H0. ss. reflexivity. }
      }
      { i. red in H0. des. eapply ext. i. etrans.
        { eapply from_monoid_le. }
        etrans.
        2:{ symmetry. eapply from_monoid_le. }
        split. i.
        { etransitivity; eauto. }
        { etransitivity; eauto. }
      }
    Qed.

    Global Program Definition quotient_add `{OrderedCM.t A}
           (s0 s1: quotient): quotient :=
      mk _ (fun a => exists a0 a1 (IN0: s0 a0) (IN1: s1 a1),
                OrderedCM.le (OrderedCM.add a0 a1) a) _.
    Next Obligation.
      hexploit (from_monoid_exist s0).
      hexploit (from_monoid_exist s1). i. des. subst.
      exists (OrderedCM.add a a0). i. split.
      { i. des. etrans.
        { eapply OrderedCM.le_add_r. erewrite <- from_monoid_le. eauto. }
        etrans.
        { eapply OrderedCM.le_add_l. erewrite <- from_monoid_le. eauto. }
        { eauto. }
      }
      i. esplits.
      { erewrite from_monoid_le. reflexivity. }
      { erewrite from_monoid_le. reflexivity. }
      { eauto. }
    Qed.

    Lemma from_monoid_add `{OrderedCM.t A} a0 a1
      :
      quotient_add (from_monoid a0) (from_monoid a1)
      =
        from_monoid (OrderedCM.add a0 a1).
    Proof.
      eapply ext. i. split.
      { i. ss. des. etrans.
        { eapply OrderedCM.le_add_r. eauto. }
        etrans.
        { eapply OrderedCM.le_add_l. eauto. }
        { eauto. }
      }
      { i. ss. esplits.
        { reflexivity. }
        { reflexivity. }
        { eauto. }
      }
    Qed.

    Lemma quotient_add_comm `{OrderedCM.t A} s0 s1
      :
      quotient_add s0 s1
      =
        quotient_add s1 s0.
    Proof.
      hexploit (from_monoid_exist s0).
      hexploit (from_monoid_exist s1). i. des. subst.
      rewrite ! from_monoid_add.
      eapply from_monoid_eq. eapply OrderedCM.add_comm_eq.
    Qed.

    Lemma quotient_add_assoc `{OrderedCM.t A} s0 s1 s2
      :
      quotient_add s0 (quotient_add s1 s2)
      =
        quotient_add (quotient_add s0 s1) s2.
    Proof.
      hexploit (from_monoid_exist s0).
      hexploit (from_monoid_exist s1).
      hexploit (from_monoid_exist s2). i. des. subst.
      rewrite ! from_monoid_add.
      eapply from_monoid_eq. eapply OrderedCM.add_assoc_eq.
    Qed.

    Variant car `{OrderedCM.t A}: Type :=
      | frag (s: quotient)
      | excl (e: quotient) (s: quotient)
      | boom
    .

    Definition black `{OrderedCM.t A} (a: A): car :=
      excl (from_monoid a) (from_monoid (@OrderedCM.unit _ _)).

    Definition white `{OrderedCM.t A} (a: A): car :=
      frag (from_monoid a).

    Definition unit `{OrderedCM.t A}: car :=
      white (@OrderedCM.unit _ _).

    Let add `{OrderedCM.t A} :=
          fun (a0 a1: car) =>
            match a0, a1 with
            | frag f0, frag f1 => frag (quotient_add f0 f1)
            | frag f0, excl e1 f1 => excl e1 (quotient_add f0 f1)
            | excl e0 f0, frag f1 => excl e0 (quotient_add f0 f1)
            | _, _ => boom
            end.

    Let wf `{OrderedCM.t A} :=
          fun (a: car) =>
            match a with
            | frag f => True
            | excl e f => le f e
            | boom => False
            end.

    Let core `{OrderedCM.t A} :=
          fun (a: car) => unit.

    Global Program Instance t `{OrderedCM.t A}: URA.t := {
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
        hexploit (from_monoid_exist s). i. des. subst.
        rewrite from_monoid_add.
        eapply from_monoid_eq. eapply OrderedCM.add_unit_eq_l.
      }
      { f_equal.
        hexploit (from_monoid_exist s). i. des. subst.
        rewrite from_monoid_add.
        eapply from_monoid_eq. eapply OrderedCM.add_unit_eq_l.
      }
    Qed.
    Next Obligation.
      unseal "ra". ss.
    Qed.
    Next Obligation.
      unseal "ra". destruct a, b; ss.
      hexploit (from_monoid_exist s).
      hexploit (from_monoid_exist s0).
      hexploit (from_monoid_exist e). i. des. subst.
      rewrite from_monoid_add in H0.
      rewrite le_iff in H0. rewrite le_iff.
      etrans; eauto. eapply OrderedCM.add_base_l.
    Qed.
    Next Obligation.
      unseal "ra". destruct a; ss.
      { f_equal.
        hexploit (from_monoid_exist s). i. des. subst.
        rewrite from_monoid_add.
        eapply from_monoid_eq.
        eapply OrderedCM.add_unit_eq_r.
      }
      { f_equal.
        hexploit (from_monoid_exist s). i. des. subst.
        rewrite from_monoid_add.
        eapply from_monoid_eq.
        eapply OrderedCM.add_unit_eq_r.
      }
    Qed.
    Next Obligation.
      unseal "ra". exists unit. unfold core, unit, white. ss.
      f_equal.
      rewrite from_monoid_add.
      eapply from_monoid_eq. symmetry.
      eapply OrderedCM.add_unit_eq_r.
    Qed.

    Lemma white_sum `{OrderedCM.t A} (a0 a1: A)
      :
      white a0 ⋅ white a1
      =
        white (OrderedCM.add a0 a1).
    Proof.
      ur. unfold white. f_equal.
      rewrite from_monoid_add. auto.
    Qed.

    Lemma white_eq `{OrderedCM.t A} (a0 a1: A)
          (EQ: OrderedCM.eq a0 a1)
      :
      white a0 = white a1.
    Proof.
      unfold white. f_equal.
      eapply from_monoid_eq; eauto.
    Qed.

    Lemma black_eq `{OrderedCM.t A} (a0 a1: A)
          (EQ: OrderedCM.eq a0 a1)
      :
      black a0 = black a1.
    Proof.
      unfold black. f_equal.
      eapply from_monoid_eq; eauto.
    Qed.

    Lemma white_mon `{OrderedCM.t A} (a0 a1: A)
          (LE: OrderedCM.le a0 a1)
      :
      URA.updatable (white a1) (white a0).
    Proof.
      ii. ur in H0. ur. unfold wf in *. des_ifs.
      etrans; eauto.
      hexploit (from_monoid_exist s0). i. des. subst.
      rewrite ! from_monoid_add. eapply le_iff.
      eapply OrderedCM.le_add_r. auto.
    Qed.

    Lemma black_mon `{OrderedCM.t A} (a0 a1: A)
          (LE: OrderedCM.le a0 a1)
      :
      URA.updatable (black a0) (black a1).
    Proof.
      ii. ur in H0. ur. unfold wf in *. des_ifs.
      hexploit (from_monoid_exist s0). i. des. subst.
      rewrite from_monoid_add in *. etrans; eauto.
      eapply le_iff. auto.
    Qed.

    Lemma success_update `{OrderedCM.t A} a0 a1
      :
      URA.updatable
        (black a0)
        (black (OrderedCM.add a0 a1) ⋅ white a1).
    Proof.
      ii. ur in H0. ur. unfold wf in *. des_ifs.
      hexploit (from_monoid_exist s0). i. des. subst.
      rewrite ! from_monoid_add in H0.
      rewrite ! from_monoid_add.
      erewrite le_iff in H0. erewrite le_iff.
      etrans.
      { eapply OrderedCM.le_add_l. etrans.
        { eapply OrderedCM.add_base_r. }
        { eapply H0. }
      }
      etrans.
      { eapply OrderedCM.add_comm_le. }
      { eapply OrderedCM.le_add_l.
        eapply OrderedCM.add_unit_le_r.
      }
    Qed.

    Lemma decr_update `{OrderedCM.t A} a0 a1
      :
      URA.updatable_set
        (black a0 ⋅ white a1)
        (fun r => exists a2, r = black a2 /\ OrderedCM.le (OrderedCM.add a1 a2) a0).
    Proof.
      ii. ur in WF. unfold wf in WF. des_ifs.
      hexploit (from_monoid_exist s0). i. des. subst.
      rewrite ! from_monoid_add in WF. rewrite le_iff in WF.
      eexists. esplits.
      { reflexivity. }
      { instantiate (1:=a). etrans; eauto.
        eapply OrderedCM.le_add_r. eapply OrderedCM.add_base_r.
      }
      ur. rewrite ! from_monoid_add. rewrite le_iff.
      eapply OrderedCM.add_unit_le_r.
    Qed.
  End MONOID.
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
        X Y (Q: Y -> M -> Prop) (f: Y -> X)
        (P: X -> M -> Prop) (r: M)
        (INF: infsum P r)
        (PRED: forall y r, P (f y) r -> Q y r)
        (INJ: forall y0 y1, f y0 = f y1 -> y0 = y1)
        x
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
    compute.
    replace (fun (EQ0 : f x = None) => match TOTAL x EQ0 return Y with
                                       end) with
      (fun (EQ0 : f x = None) => y).
    2:{ extensionality a. clarify. }
    rewrite EQ. auto.
  Qed.

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
    { assert (exists (f': sig (fun y => f y <> None) -> X),
               forall y, f (proj1_sig y) = Some (f' y)).
      { eapply (choice (fun (y: sig (fun y => f y <> None)) x => f (proj1_sig y) = Some x)).
        i. destruct x0. ss. destruct (f x0); ss. eauto.
      }
      des. hexploit (@infsum_unfold X _ (fun y => Q (proj1_sig y)) f').
      { eauto. }
      { i. eapply PRED. rewrite H. ss. }
      { i. assert (proj1_sig y0 = proj1_sig y1).
        { eapply INJ. rewrite ! H. f_equal. auto. }
        { destruct y0, y1. ss. subst. f_equal. apply proof_irrelevance. }
      }
      { instantiate (1:=x). ii. eapply MINUS. rewrite H. rewrite H0. auto. }
      i. des. subst. exists r2, (r3 ⋅ r1). splits.
      { r_solve. }
      { ss. }
      assert (exists (wrap: Y -> option (sig (fun y => f y <> None))),
               forall y,
                 match (wrap y) with
                 | None => f y = None
                 | Some (exist _ y' _) => y = y' /\ exists x, f y = Some x
                 end).
      { eapply (choice (fun y (y': option (sig (fun y => f y <> None))) =>
                          match y' with
                          | Some (exist _ y' _) => y = y' /\ exists x, f y = Some x
                          | None => f y = None
                          end)).
        i. destruct (f x0) eqn:EQ.
        { refine (ex_intro _ (Some (exist _ x0 _)) _).
          { ii. clarify. }
          { splits; eauto. }
        }
        { exists None. auto. }
      }
      des. guclo infsum_monoC_spec. econs.
      3:{ gbase. eapply CIH; eauto. }
      { instantiate (1:=wrap). i. specialize (H0 y). des_ifs; ss.
        { des. subst. auto. }
        { eapply PRED. rewrite H0. ss. }
      }
      { i. eapply INJ. pose proof (H0 y0). pose proof (H0 y1). des_ifs.
        { des. subst. auto. }
        { rewrite H4. rewrite H5. auto. }
      }
    }
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
        { i. destruct (f y0) eqn:EQ0.
          2:{ destruct (MINUS _ EQ0). }
          destruct (f y1) eqn:EQ1.
          2:{ destruct (MINUS _ EQ1). }
          eapply INJ; eauto.
          erewrite partial_fun_to_total_eq in H; eauto.
          erewrite partial_fun_to_total_eq in H; eauto.
          rewrite EQ0. rewrite EQ1. subst. auto.
        }
      }
    }
  Qed.

  Lemma infsum_fold
        (X: Type) (P0: X -> M -> Prop) (r0: M)
        (INF: infsum P0 r0)
        (P1: M -> Prop) (r1: M)
        (SAT: P1 r1)
        Y (Q: Y -> M -> Prop)
        (f: Y -> option X)
        (PRED0: forall y x r (EQ: f y = Some x), P0 x r -> Q y r)
        (PRED1: forall y r (EQ: f y = None), P1 r -> Q y r)
        (INJ: forall y0 y1, f y0 = f y1 -> y0 = y1)
    :
    infsum Q (r0 ⋅ r1).
  Proof.
    ginit. guclo infsum_monoC_spec. econs.
    3:{ gfinal. right. eapply infsum_fold_aux; eauto. }
    { instantiate (1:=f). i. destruct (f y) eqn:EQ; ss; eauto. }
    { auto. }
  Qed.

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
#[export] Hint Resolve infsum_monotone: paco.
#[export] Hint Resolve cpn3_wcompat: paco.

Lemma updatable_set_impl (M: URA.t)
      (P0 P1: M -> Prop)
      (IMPL: forall r, URA.wf r -> P0 r -> P1 r)
      (m: M)
      (UPD: URA.updatable_set m P0)
  :
  URA.updatable_set m P1.
Proof.
  ii. eapply UPD in WF; eauto. des.
  esplits; eauto. eapply IMPL; auto.
  eapply URA.wf_mon. eauto.
Qed.

Lemma pointwise_updatable A (M: URA.t)
      (f0 f1: (A ==> M)%ra)
      (UPD: forall a, URA.updatable (f0 a) (f1 a))
  :
  URA.updatable f0 f1.
Proof.
  ii. ur. i. ur in H. specialize (H k).
  eapply (UPD k); eauto.
Qed.

Lemma pointwise_updatable_set A (M: URA.t)
      (f: (A ==> M)%ra)
      (P: A -> M -> Prop)
      (UPD: forall a, URA.updatable_set (f a) (P a))
  :
  URA.updatable_set f (fun f' => forall a, P a (f' a)).
Proof.
  ii. hexploit (choice (fun a m => P a m /\ URA.wf (m ⋅ ctx a))).
  { i. eapply (UPD x). ur in WF. auto. }
  i. des. exists f0. splits; auto.
  { i. specialize (H a). des. auto. }
  { ur. i. specialize (H k). des. auto. }
Qed.

Definition maps_to_res {A} {M: URA.t}
           a m: (A ==> M)%ra :=
  fun a' => if excluded_middle_informative (a' = a)
            then m
            else URA.unit.

Lemma maps_to_res_add A (M: URA.t)
      (a: A) (m0 m1: M)
  :
  maps_to_res a m0 ⋅ maps_to_res a m1
  =
    maps_to_res a (m0 ⋅ m1).
Proof.
  extensionality a'. unfold maps_to_res. ur. des_ifs.
  { ur. auto. }
  { r_solve. }
Qed.

Lemma maps_to_updatable A (M: URA.t)
      (a: A) (m0 m1: M)
      (UPD: URA.updatable m0 m1)
  :
  URA.updatable (maps_to_res a m0) (maps_to_res a m1).
Proof.
  eapply pointwise_updatable. i.
  unfold maps_to_res. des_ifs.
Qed.

Lemma maps_to_updatable_set A (M: URA.t)
      (a: A) (m: M) (P: M -> Prop)
      (UPD: URA.updatable_set m P)
  :
  URA.updatable_set
    (maps_to_res a m)
    (fun f => exists (m1: M), f = maps_to_res a m1 /\ P m1).
Proof.
  eapply updatable_set_impl; cycle 1.
  { eapply pointwise_updatable_set.
    instantiate (1:= fun a' m' => (a' = a -> P m') /\ (a' <> a -> m' = URA.unit)).
    ii. unfold maps_to_res in WF. des_ifs.
    { exploit UPD; eauto. i. des. esplits; eauto. ss. }
    { exists URA.unit. splits; ss. }
  }
  { i. ss. exists (r a). splits; auto.
    { extensionality a'. unfold maps_to_res. des_ifs.
      specialize (H0 a'). des. auto.
    }
    { specialize (H0 a). des. auto. }
  }
Qed.

Definition map_update {A} {M: URA.t}
           (f: (A ==> M)%ra) a m :=
  fun a' => if excluded_middle_informative (a' = a)
            then m
            else f a'.

Definition maps_to {Σ} {A: Type} {M: URA.t} `{ING: @GRA.inG (A ==> M)%ra Σ}
           (a: A) (m: M): iProp :=
  OwnM (maps_to_res a m).

Program Definition Infsum {Σ: GRA.t} (X: Type) (P: X -> iProp): iProp :=
  iProp_intro (infsum Σ P) _.
Next Obligation.
Proof.
  rr in LE. des. subst.
  ginit. guclo infsum_extendC_spec. econs; eauto. gfinal. right. auto.
Qed.

Lemma pointwise_own_infsum A (M: URA.t)
      {Σ: GRA.t} `{ING: @GRA.inG (A ==> M)%ra Σ}
      (f: (A ==> M)%ra)
  :
  (OwnM f)
    -∗
    Infsum (fun a => OwnM (maps_to_res a (f a))).
Proof.
  uipropall. i. rr in H. uipropall. rr in H. des. subst.
  ginit. guclo infsum_extendC_spec. econs; eauto.
  clear WF ctx. revert f. gcofix CIH. i. gstep. econs. i.
  exists (GRA.embed (maps_to_res x (f x))), (GRA.embed (map_update f x URA.unit: (A ==> M)%ra)).
  splits.
  { rewrite GRA.embed_add. f_equal.
    extensionality a. ur.
    unfold maps_to_res, map_update. des_ifs.
    { r_solve. }
    { r_solve. }
  }
  { rr. uipropall. reflexivity. }
  guclo infsum_monoC_spec. econs.
  3:{ gbase. eapply CIH. }
  { instantiate (1:=f0). i. ss.
    unfold map_update in H. des_ifs.
    { exfalso. eapply MINUS; eauto. }
    { eapply PRED; eauto. }
  }
  { auto. }
Qed.

Arguments Fuel.t A {_}.

Module FairRA.
  Section FAIR.
    Variable (Id: Type).
    Variable (A: Type).
    Context `{L: OrderedCM.t A}.

    Definition t: URA.t :=
      (Id ==> @Fuel.t A _)%ra.

    Context `{ING: @GRA.inG t Σ}.

    Definition black (i: Id) (a: A): iProp :=
      maps_to i (Fuel.black a: Fuel.t A).

    Definition white (i: Id) (a: A): iProp :=
      maps_to i (Fuel.white a: Fuel.t A).

    Lemma white_sum i a0 a1
      :
      (white i a0)
        -∗
        (white i a1)
        -∗
        (white i (OrderedCM.add a0 a1)).
    Proof.
      unfold white, maps_to. iIntros "H0 H1".
      iCombine "H0 H1" as "H".
      rewrite maps_to_res_add. rewrite (@Fuel.white_sum A L). auto.
    Qed.

    Lemma white_split i a0 a1
      :
      (white i (OrderedCM.add a0 a1))
        -∗
        (white i a0 ** white i a1).
    Proof.
      unfold white, maps_to. iIntros "H".
      rewrite <- (@Fuel.white_sum A L).
      rewrite <- maps_to_res_add.
      iDestruct "H" as "[H0 H1]". iFrame.
    Qed.

    Lemma white_eq a1 i a0
          (EQ: OrderedCM.eq a0 a1)
      :
      white i a0 = white i a1.
    Proof.
      unfold white. erewrite Fuel.white_eq; eauto.
    Qed.

    Lemma black_eq a1 i a0
          (EQ: OrderedCM.eq a0 a1)
      :
      black i a0 = black i a1.
    Proof.
      unfold black. erewrite Fuel.black_eq; eauto.
    Qed.

    Lemma white_mon a0 i a1
          (LE: OrderedCM.le a0 a1)
      :
      (white i a1)
        -∗
        (#=> white i a0).
    Proof.
      eapply OwnM_Upd. eapply maps_to_updatable.
      eapply Fuel.white_mon. auto.
    Qed.

    Lemma black_mon a1 i a0
          (LE: OrderedCM.le a0 a1)
      :
      (black i a0)
        -∗
        (#=> black i a1).
    Proof.
      eapply OwnM_Upd. eapply maps_to_updatable.
      eapply Fuel.black_mon. auto.
    Qed.

    Lemma success_update a1 i a0
      :
      (black i a0)
        -∗
        (#=> ((∃ a, black i a) ** (white i a1))).
    Proof.
      iIntros "H".
      iPoseProof (OwnM_Upd with "H") as "> H".
      { eapply maps_to_updatable.
        eapply Fuel.success_update. }
      rewrite <- maps_to_res_add. iDestruct "H" as "[H0 H1]".
      iModIntro. iFrame. iExists _. iFrame.
    Qed.

    Lemma decr_update i a0 a1
      :
      (black i a0)
        -∗
        (white i a1)
        -∗
        (#=> (∃ a2, black i a2 ** ⌜OrderedCM.le (OrderedCM.add a1 a2) a0⌝)).
    Proof.
      iIntros "H0 H1". iCombine "H0 H1" as "H".
      rewrite maps_to_res_add.
      iPoseProof (OwnM_Upd_set with "H") as "> H".
      { eapply maps_to_updatable_set. eapply Fuel.decr_update. }
      iModIntro. ss. iDestruct "H" as "[% [% H]]".
      des. subst. iExists _. iFrame. auto.
    Qed.

    (* Target *)
    Definition whites (f: Id -> A): iProp :=
      OwnM ((fun i => Fuel.white (f i)): (Id ==> Fuel.t A)%ra).

    Definition whites_update
               (f0 f1: Id -> A)
               (u: A)
               (S F: Id -> Prop)
               (EMPTY: forall i (FAIL: ~ F i) (SUCC: ~ S i), f1 i = f0 i)
               (FAIL: forall i (FAIL: F i) (SUCC: ~ S i), OrderedCM.le (OrderedCM.add u (f1 i)) (f0 i))
      :
      (whites f0)
        -∗
        (Infsum (fun i: sig S => (∃ a, black (proj1_sig i) a)%I))
        -∗
        (#=>
           ((whites f1)
              **
              (Infsum (fun i: sig S => (∃ a, black (proj1_sig i) a)%I))
              **
              (Infsum (fun i: sig F => white (proj1_sig i) u)))).
    Proof.
    Admitted.

    (* Source *)
    Definition blacks (f: Id -> A): iProp :=
      OwnM ((fun i => Fuel.black (f i)): (Id ==> Fuel.t A)%ra).

    Definition blacks_update
               (f0: Id -> A)
               (u: A) (n: A)
               (S F: Id -> Prop)
      :
      (blacks f0)
        -∗
        (Infsum (fun i: sig F => white (proj1_sig i) u))
        -∗
        (#=>
           (∃ (f1: Id -> A),
               ((blacks f1)
                  **
                  (Infsum (fun i: sig S => white (proj1_sig i) n))
                  **
                  ⌜((forall i (FAIL: ~ F i) (SUCC: ~ S i), f1 i = f0 i) /\
                      (forall i (FAIL: F i) (SUCC: ~ S i), OrderedCM.le (OrderedCM.add u (f1 i)) (f0 i)))⌝))).
    Proof.
    Admitted.
  End FAIR.
End FairRA.

Global Opaque Fuel.from_monoid Fuel.quotient_add.

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


From Fairness Require Import Axioms MonotonePCM.
From Ordinal Require Export Ordinal Arithmetic Hessenberg ClassicalHessenberg.

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

    Definition pending (k: nat): iProp :=
      OwnM (FiniteMap.singleton k ((ε: @CounterRA.t Ord.t _, OneShot.pending unit: OneShot.t unit): URA.prod (@CounterRA.t Ord.t _) (OneShot.t unit))).

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

    Lemma pending_unique k
      :
      (pending k)
        -∗
        (pending k)
        -∗
        False.
    Proof.
      iIntros "H0 H1". iCombine "H0 H1" as "H".
      iOwnWf "H". rewrite FiniteMap.singleton_add in H0.
      rewrite FiniteMap.singleton_wf in H0.
      ur in H0. des. exfalso. eapply OneShot.pending_unique; eauto.
    Qed.

    Lemma pending_not_shot k
      :
      (pending k)
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

    Lemma pending_shot k
      :
      (pending k)
        -∗
        #=> (shot k).
    Proof.
      iApply OwnM_Upd. eapply FiniteMap.singleton_updatable.
      apply URA.prod_updatable.
      { reflexivity. }
      { apply OneShot.pending_shot. }
    Qed.

    Lemma alloc o
      :
      ⊢ #=> (∃ k, black k o ** white k o ** pending k).
    Proof.
      iPoseProof (@OwnM_unit _ _ H) as "H".
      iPoseProof (OwnM_Upd_set with "H") as "> H0".
      { eapply FiniteMap.singleton_alloc.
        instantiate (1:=((CounterRA.black o, ε): URA.prod (@CounterRA.t Ord.t _) (OneShot.t unit)) ⋅ ((CounterRA.white o, ε): URA.prod (@CounterRA.t Ord.t _) (OneShot.t unit)) ⋅ (ε, OneShot.pending unit)).
        repeat rewrite unfold_prod_add. repeat rewrite URA.unit_idl. repeat rewrite URA.unit_id.
        rewrite unfold_prod_wf. ss. split.
        { eapply CounterRA.black_white_wf. }
        { apply OneShot.pending_wf. }
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
        (white k o0 ** white k o1).
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
        (#=> (white k o0 ** white k o1)).
    Proof.
      iIntros "H". iPoseProof (white_mon with "H") as "> H"; eauto.
      iModIntro. iApply white_split_eq; auto.
    Qed.

    Lemma white_split_one o0 k o1
          (LT: Ord.lt o0 o1)
      :
      (white k o1)
        -∗
        (#=> (white k o0 ** white_one k)).
    Proof.
      iIntros "H". iApply white_split; eauto.
      rewrite Hessenberg.add_S_r. rewrite Hessenberg.add_O_r.
      apply Ord.S_supremum; auto.
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
        (#=> ∃ o2, black k o2 ** ⌜Ord.le (Hessenberg.add o2 o1) o0⌝).
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
        (#=> ∃ o0, black k o0 ** ⌜Ord.lt o0 o1⌝).
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
        (#=> ∃ o_b0, black k o_b0 ** white k o_w0 ** ⌜Ord.lt o_b0 o_b1⌝).
    Proof.
      iIntros "H0 H1".
      iPoseProof (white_split_one with "H1") as "> [H1 H2]"; [eauto|].
      iPoseProof (black_white_decr_one with "H0 H2") as "> [% [H0 %]]".
      iModIntro. iExists _. iFrame. auto.
    Qed.
  End RA.

  Section REGION.
    Context `{Σ: GRA.t}.
    Context `{@GRA.inG t Σ}.
    Context `{@GRA.inG (Region.t (nat * nat * Ord.t)) Σ}.

    Definition edge: (nat * nat * Ord.t) -> iProp :=
      fun '(k0, k1, c) => (∃ o, black k0 o ** white k1 (Jacobsthal.mult c o))%I.

    Definition region_sat: iProp := Region.sat edge.

    Definition amplifier (k0 k1: nat) (c: Ord.t): iProp :=
      □ (∀ o, white k0 o -* #=(region_sat)=> white k1 (Jacobsthal.mult c o)).

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
        (#=(region_sat)=> white k1 (Jacobsthal.mult c o)).
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
        (#=(region_sat)=> amplifier k0 k1 c).
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
  End REGION.
End ObligationRA.
