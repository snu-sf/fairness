From sflib Require Import sflib.
From Fairness Require Import PCM IProp IPM.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.PropExtensionality.
From Fairness Require Import Axioms MonotonePCM.
Require Import Program.

Set Implicit Arguments.

Module CommMonoid.
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

  Section LATTICE.
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
  End LATTICE.
End CommMonoid.


Global Program Instance nat_CommMonoid: CommMonoid.t nat :=
  @CommMonoid.mk _ le 0 Nat.add _ _ _ _ _ _ .
Next Obligation. Proof. lia. Qed.
Next Obligation. Proof. lia. Qed.
Next Obligation. Proof. lia. Qed.
Next Obligation. Proof. lia. Qed.
Next Obligation. Proof. lia. Qed.

From Ordinal Require Import Ordinal Hessenberg.

Global Program Instance ord_CommMonoid: CommMonoid.t Ord.t :=
  @CommMonoid.mk _ Ord.le Ord.O Hessenberg.add _ _ _ _ _ _ .
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

Lemma ord_CommMonoid_eq (a0 a1: Ord.t):
  CommMonoid.eq a0 a1 <-> Ord.eq a0 a1.
Proof.
  auto.
Qed.

Lemma nat_CommMonoid_eq (a0 a1: nat):
  CommMonoid.eq a0 a1 <-> a0 = a1.
Proof.
  split.
  { i. red in H. des. ss. lia. }
  { i. subst. reflexivity. }
Qed.

Module LtMonoid.
  Class t (car: Type) `{CommMonoid.t car} :=
    mk { lt: car -> car -> Prop;
         one: car;
         lt_iff: forall a0 a1,
           lt a0 a1 <-> CommMonoid.le (CommMonoid.add a0 one) a1;
      }.
End LtMonoid.

Global Program Instance ord_LtMonoid: @LtMonoid.t Ord.t _ :=
  @LtMonoid.mk _ _ Ord.lt (Ord.S Ord.O) _.
Next Obligation.
Proof.
  rewrite Hessenberg.add_S_r. rewrite Hessenberg.add_O_r.
  split; i.
  { eapply Ord.S_supremum; auto. }
  { eapply Ord.lt_le_lt; eauto. eapply Ord.S_lt. }
Qed.

Global Program Instance nat_LtMonoid: @LtMonoid.t nat _ :=
  @LtMonoid.mk _ _ lt 1 _.
Next Obligation.
Proof.
  lia.
Qed.

Module Fuel.
  Section LATTICE.
    Variable (A: Type).

    Record quotient `{CommMonoid.t A} :=
      mk {
          collection:> A -> Prop;
          generated: exists a0, forall a1,
            collection a1 <-> CommMonoid.le a0 a1;
        }.

    Global Program Definition from_lattice `{CommMonoid.t A} (a: A): quotient :=
      mk _ (CommMonoid.le a) _.
    Next Obligation.
    Proof.
      exists a. i. auto.
    Qed.

    Definition le `{CommMonoid.t A} (s0 s1: quotient): Prop :=
      forall a, s1 a -> s0 a.

    Global Program Instance le_PreOrder `{CommMonoid.t A}: PreOrder le.
    Next Obligation.
    Proof.
      ii. auto.
    Qed.
    Next Obligation.
    Proof.
      ii. eauto.
    Qed.

    Lemma le_anstisymmetric`{CommMonoid.t A} s0 s1
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

    Lemma ext `{CommMonoid.t A} (s0 s1: quotient)
          (EXT: forall a, s0 a <-> s1 a)
      :
      s0 = s1.
    Proof.
      eapply le_anstisymmetric.
      { ii. eapply EXT; auto. }
      { ii. eapply EXT; auto. }
    Qed.

    Lemma from_lattice_exist `{CommMonoid.t A} (s: quotient)
      :
      exists a, s = from_lattice a.
    Proof.
      hexploit generated. i. des. exists a0.
      eapply ext. i. rewrite H0. ss.
    Qed.

    Lemma from_lattice_le `{CommMonoid.t A} a0 a1
      :
      from_lattice a0 a1 <-> CommMonoid.le a0 a1.
    Proof.
      ss.
    Qed.

    Lemma le_iff `{CommMonoid.t A} a0 a1
      :
      le (from_lattice a0) (from_lattice a1) <-> CommMonoid.le a0 a1.
    Proof.
      split.
      { i. exploit H0.
        { s. reflexivity. }
        i. rewrite <- from_lattice_le. ss.
      }
      { ii. ss. etrans; eauto. }
    Qed.

    Lemma from_lattice_eq `{CommMonoid.t A} a0 a1
      :
      from_lattice a0 = from_lattice a1 <-> CommMonoid.eq a0 a1.
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

    Global Program Definition quotient_add `{CommMonoid.t A}
           (s0 s1: quotient): quotient :=
      mk _ (fun a => exists a0 a1 (IN0: s0 a0) (IN1: s1 a1),
                CommMonoid.le (CommMonoid.add a0 a1) a) _.
    Next Obligation.
      hexploit (from_lattice_exist s0).
      hexploit (from_lattice_exist s1). i. des. subst.
      exists (CommMonoid.add a a0). i. split.
      { i. des. etrans.
        { eapply CommMonoid.le_add_r. erewrite <- from_lattice_le. eauto. }
        etrans.
        { eapply CommMonoid.le_add_l. erewrite <- from_lattice_le. eauto. }
        { eauto. }
      }
      i. esplits.
      { erewrite from_lattice_le. reflexivity. }
      { erewrite from_lattice_le. reflexivity. }
      { eauto. }
    Qed.

    Lemma from_lattice_add `{CommMonoid.t A} a0 a1
      :
      quotient_add (from_lattice a0) (from_lattice a1)
      =
        from_lattice (CommMonoid.add a0 a1).
    Proof.
      eapply ext. i. split.
      { i. ss. des. etrans.
        { eapply CommMonoid.le_add_r. eauto. }
        etrans.
        { eapply CommMonoid.le_add_l. eauto. }
        { eauto. }
      }
      { i. ss. esplits.
        { reflexivity. }
        { reflexivity. }
        { eauto. }
      }
    Qed.

    Lemma quotient_add_comm `{CommMonoid.t A} s0 s1
      :
      quotient_add s0 s1
      =
        quotient_add s1 s0.
    Proof.
      hexploit (from_lattice_exist s0).
      hexploit (from_lattice_exist s1). i. des. subst.
      rewrite ! from_lattice_add.
      eapply from_lattice_eq. eapply CommMonoid.add_comm_eq.
    Qed.

    Lemma quotient_add_assoc `{CommMonoid.t A} s0 s1 s2
      :
      quotient_add s0 (quotient_add s1 s2)
      =
        quotient_add (quotient_add s0 s1) s2.
    Proof.
      hexploit (from_lattice_exist s0).
      hexploit (from_lattice_exist s1).
      hexploit (from_lattice_exist s2). i. des. subst.
      rewrite ! from_lattice_add.
      eapply from_lattice_eq. eapply CommMonoid.add_assoc_eq.
    Qed.

    Variant car `{CommMonoid.t A}: Type :=
      | frag (s: quotient)
      | excl (e: quotient) (s: quotient)
      | boom
    .

    Definition black `{CommMonoid.t A} (a: A): car :=
      excl (from_lattice a) (from_lattice (@CommMonoid.unit _ _)).

    Definition white `{CommMonoid.t A} (a: A): car :=
      frag (from_lattice a).

    Definition unit `{CommMonoid.t A}: car :=
      white (@CommMonoid.unit _ _).

    Let add `{CommMonoid.t A} :=
          fun (a0 a1: car) =>
            match a0, a1 with
            | frag f0, frag f1 => frag (quotient_add f0 f1)
            | frag f0, excl e1 f1 => excl e1 (quotient_add f0 f1)
            | excl e0 f0, frag f1 => excl e0 (quotient_add f0 f1)
            | _, _ => boom
            end.

    Let wf `{CommMonoid.t A} :=
          fun (a: car) =>
            match a with
            | frag f => True
            | excl e f => le f e
            | boom => False
            end.

    Let core `{CommMonoid.t A} :=
          fun (a: car) => unit.

    Global Program Instance t `{CommMonoid.t A}: URA.t := {
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
        eapply from_lattice_eq. eapply CommMonoid.add_unit_eq_l.
      }
      { f_equal.
        hexploit (from_lattice_exist s). i. des. subst.
        rewrite from_lattice_add.
        eapply from_lattice_eq. eapply CommMonoid.add_unit_eq_l.
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
      etrans; eauto. eapply CommMonoid.add_base_l.
    Qed.
    Next Obligation.
      unseal "ra". destruct a; ss.
      { f_equal.
        hexploit (from_lattice_exist s). i. des. subst.
        rewrite from_lattice_add.
        eapply from_lattice_eq.
        eapply CommMonoid.add_unit_eq_r.
      }
      { f_equal.
        hexploit (from_lattice_exist s). i. des. subst.
        rewrite from_lattice_add.
        eapply from_lattice_eq.
        eapply CommMonoid.add_unit_eq_r.
      }
    Qed.
    Next Obligation.
      unseal "ra". exists unit. unfold core, unit, white. ss.
      f_equal.
      rewrite from_lattice_add.
      eapply from_lattice_eq. symmetry.
      eapply CommMonoid.add_unit_eq_r.
    Qed.

    Lemma white_sum `{CommMonoid.t A} (a0 a1: A)
      :
      white a0 ⋅ white a1
      =
        white (CommMonoid.add a0 a1).
    Proof.
      ur. unfold white. f_equal.
      rewrite from_lattice_add. auto.
    Qed.

    Lemma white_eq `{CommMonoid.t A} (a0 a1: A)
          (EQ: CommMonoid.eq a0 a1)
      :
      white a0 = white a1.
    Proof.
      unfold white. f_equal.
      eapply from_lattice_eq; eauto.
    Qed.

    Lemma black_eq `{CommMonoid.t A} (a0 a1: A)
          (EQ: CommMonoid.eq a0 a1)
      :
      black a0 = black a1.
    Proof.
      unfold black. f_equal.
      eapply from_lattice_eq; eauto.
    Qed.

    Lemma white_mon `{CommMonoid.t A} (a0 a1: A)
          (LE: CommMonoid.le a0 a1)
      :
      URA.updatable (white a1) (white a0).
    Proof.
      ii. ur in H0. ur. unfold wf in *. des_ifs.
      etrans; eauto.
      hexploit (from_lattice_exist s0). i. des. subst.
      rewrite ! from_lattice_add. eapply le_iff.
      eapply CommMonoid.le_add_r. auto.
    Qed.

    Lemma black_mon `{CommMonoid.t A} (a0 a1: A)
          (LE: CommMonoid.le a0 a1)
      :
      URA.updatable (black a0) (black a1).
    Proof.
      ii. ur in H0. ur. unfold wf in *. des_ifs.
      hexploit (from_lattice_exist s0). i. des. subst.
      rewrite from_lattice_add in *. etrans; eauto.
      eapply le_iff. auto.
    Qed.

    Lemma success_update `{CommMonoid.t A} a0 a1
      :
      URA.updatable
        (black a0)
        (black (CommMonoid.add a0 a1) ⋅ white a1).
    Proof.
      ii. ur in H0. ur. unfold wf in *. des_ifs.
      hexploit (from_lattice_exist s0). i. des. subst.
      rewrite ! from_lattice_add in H0.
      rewrite ! from_lattice_add.
      erewrite le_iff in H0. erewrite le_iff.
      etrans.
      { eapply CommMonoid.le_add_l. etrans.
        { eapply CommMonoid.add_base_r. }
        { eapply H0. }
      }
      etrans.
      { eapply CommMonoid.add_comm_le. }
      { eapply CommMonoid.le_add_l.
        eapply CommMonoid.add_unit_le_r.
      }
    Qed.

    Lemma decr_update `{CommMonoid.t A} a0 a1
      :
      URA.updatable_set
        (black a0 ⋅ white a1)
        (fun r => exists a2, r = black a2 /\ CommMonoid.le (CommMonoid.add a1 a2) a0).
    Proof.
      ii. ur in WF. unfold wf in WF. des_ifs.
      hexploit (from_lattice_exist s0). i. des. subst.
      rewrite ! from_lattice_add in WF. rewrite le_iff in WF.
      eexists. esplits.
      { reflexivity. }
      { instantiate (1:=a). etrans; eauto.
        eapply CommMonoid.le_add_r. eapply CommMonoid.add_base_r.
      }
      ur. rewrite ! from_lattice_add. rewrite le_iff.
      eapply CommMonoid.add_unit_le_r.
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
    Context `{L: CommMonoid.t A}.

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
        (white i (CommMonoid.add a0 a1)).
    Proof.
      unfold white, maps_to. iIntros "H0 H1".
      iCombine "H0 H1" as "H".
      rewrite maps_to_res_add. rewrite (@Fuel.white_sum A L). auto.
    Qed.

    Lemma white_eq a1 i a0
          (EQ: CommMonoid.eq a0 a1)
      :
      white i a0 = white i a1.
    Proof.
      unfold white. erewrite Fuel.white_eq; eauto.
    Qed.

    Lemma black_eq a1 i a0
          (EQ: CommMonoid.eq a0 a1)
      :
      black i a0 = black i a1.
    Proof.
      unfold black. erewrite Fuel.black_eq; eauto.
    Qed.

    Lemma white_mon a0 i a1
          (LE: CommMonoid.le a0 a1)
      :
      (white i a1)
        -∗
        (#=> white i a0).
    Proof.
      eapply OwnM_Upd. eapply maps_to_updatable.
      eapply Fuel.white_mon. auto.
    Qed.

    Lemma black_mon a1 i a0
          (LE: CommMonoid.le a0 a1)
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
        (#=> (∃ a2, black i a2 ** ⌜CommMonoid.le (CommMonoid.add a1 a2) a0⌝)).
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
               (FAIL: forall i (FAIL: F i) (SUCC: ~ S i), CommMonoid.le (CommMonoid.add u (f1 i)) (f0 i))
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
                      (forall i (FAIL: F i) (SUCC: ~ S i), CommMonoid.le (CommMonoid.add u (f1 i)) (f0 i)))⌝))).
    Proof.
    Admitted.
  End FAIR.
End FairRA.
