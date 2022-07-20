From sflib Require Import sflib.
Require Import Coq.Classes.RelationClasses.
From Fairness Require Import Axioms NatStructs.
From Fairness Require Import PCM.
Require Import String.

Set Implicit Arguments.


Module World.
  Class t : Type :=
    mk {
        G: Type;
        L: Type;
        unit: L;
        compatible: G -> L -> Prop;
        disjoint: L -> L -> Prop;
        unit_compatible: forall g, compatible g unit;
        unit_disjoint_l: forall l, disjoint unit l;
        disjoint_comm: forall l0 l1 (DISJ: disjoint l0 l1), disjoint l1 l0;
      }.

  Section WORLD.
    Context `{W: t}.

    Lemma unit_disjoint_r: forall l, disjoint l unit.
    Proof.
      i. eapply disjoint_comm. eapply unit_disjoint_l.
    Qed.

    Variant update: G * L -> G * L -> Prop :=
      | update_intro
          (g0: G) (l0: L) (g1: G) (l1: L)
          (UPDATE: forall
              (COMPAT0: compatible g0 l0),
              (<<COMPAT1: compatible g1 l1>>) /\
                (<<CTX: forall l (COMPAT: compatible g0 l) (DISJ: disjoint l0 l),
                    (<<COMPAT: compatible g1 l>>) /\ (<<DISJ: disjoint l1 l>>)>>))
        :
        update (g0, l0) (g1, l1)
    .

    Global Program Instance update_PreOrder: PreOrder update.
    Next Obligation.
      ii. destruct x. econs; eauto.
    Qed.
    Next Obligation.
      ii. inv H; inv H0. econs. ii.
      hexploit UPDATE; eauto. i. des.
      hexploit UPDATE0; eauto. i. des. splits; eauto.
      i. hexploit CTX; eauto. i. des.
      hexploit CTX0; eauto.
    Qed.

    Lemma update_compatible g0 l0 g1 l1
          (UPDATE: update (g0, l0) (g1, l1))
          (COMPAT: compatible g0 l0)
      :
      compatible g1 l1.
    Proof.
      inv UPDATE. hexploit UPDATE0; eauto. i. des. auto.
    Qed.
  End WORLD.

  Section PRODUCT.
    Context `{W0: t}.
    Context `{W1: t}.

    Definition prod_G: Type := W0.(G) * W1.(G).
    Definition prod_L: Type := W0.(L) * W1.(L).
    Definition prod_unit: prod_L := (W0.(unit), W1.(unit)).
    Definition prod_compatible: prod_G -> prod_L -> Prop :=
      fun '(g0, g1) '(l0, l1) =>
        (<<COMPAT0: W0.(compatible) g0 l0>>) /\ (<<COMPAT1: W1.(compatible) g1 l1>>).
    Definition prod_disjoint: prod_L -> prod_L -> Prop :=
      fun '(ll0, lr0) '(ll1, lr1) =>
        (<<DISJ0: W0.(disjoint) ll0 ll1>>) /\ (<<DISJ1: W1.(disjoint) lr0 lr1>>).

    Global Program Instance prod: t :=
      @mk prod_G prod_L prod_unit prod_compatible prod_disjoint _ _ _.
    Next Obligation.
      destruct g; ss. split; eapply unit_compatible.
    Qed.
    Next Obligation.
      destruct l as [l0 l1]. split; eapply unit_disjoint_l.
    Qed.
    Next Obligation.
      destruct l0 as [ll0 lr0]. destruct l1 as [ll1 lr1].
      ss. des. split; eapply disjoint_comm; eauto.
    Qed.

    Lemma prod_update gl0 gr0 ll0 lr0 gl1 gr1 ll1 lr1
          (UPDATE0: @update W0 (gl0, ll0) (gl1, ll1))
          (UPDATE1: @update W1 (gr0, lr0) (gr1, lr1))
      :
      update ((gl0, gr0), (ll0, lr0)) ((gl1, gr1), (ll1, lr1)).
    Proof.
      inv UPDATE0. inv UPDATE1. econs. i. ss. des.
      hexploit UPDATE; eauto. hexploit UPDATE0; eauto. i. des.
      splits; eauto. i. destruct l. des.
      hexploit CTX; eauto. hexploit CTX0; eauto. i. des. splits; auto.
    Qed.
  End PRODUCT.
End World.


Section INVARIANT.
  Context `{W: World.t}.

  Definition local_worlds := NatMap.t World.L.

  Variant worlds_wf (g: World.G) (ls: local_worlds): Prop :=
    | worlds_wf_intro
        (COMPATIBLE: forall tid l (GET: NatMap.find tid ls = Some l),
            World.compatible g l)
        (DISJOINT: forall tid0 tid1 l0 l1
                          (NEQ: tid0 <> tid1)
                          (GET0: NatMap.find tid0 ls = Some l0)
                          (GET1: NatMap.find tid1 ls = Some l1),
            World.disjoint l0 l1)
  .

  Lemma initial_worlds_wf g: worlds_wf g (NatMap.empty World.L).
  Proof.
    econs.
    { i. rewrite NatMapP.F.empty_o in GET. ss. }
    { i. rewrite NatMapP.F.empty_o in GET0. ss. }
  Qed.

  Lemma worlds_add_unit_wf g ls tid
        (WF: worlds_wf g ls)
    :
    worlds_wf g (NatMap.add tid World.unit ls).
  Proof.
    inv WF. econs.
    { i. rewrite NatMapP.F.add_o in GET. des_ifs.
      { eapply World.unit_compatible. }
      { eapply COMPATIBLE; eauto. }
    }
    { i. rewrite NatMapP.F.add_o in GET0. rewrite NatMapP.F.add_o in GET1. des_ifs.
      { eapply World.unit_disjoint_r. }
      { eapply World.unit_disjoint_l. }
      { eapply (DISJOINT tid0 tid1); eauto. }
    }
  Qed.

  Lemma worlds_update_wf g0 ls tid l0 g1 l1
        (UPDATE: World.update (g0, l0) (g1, l1))
        (GET: NatMap.find tid ls = Some l0)
        (WF: worlds_wf g0 ls)
    :
    worlds_wf g1 (NatMap.add tid l1 ls).
  Proof.
    inv WF. inv UPDATE. hexploit UPDATE0; eauto. i. des.
    econs.
    { i. rewrite NatMapP.F.add_o in GET0. des_ifs.
      eapply CTX; eauto.
    }
    { i. rewrite NatMapP.F.add_o in GET0. rewrite NatMapP.F.add_o in GET1. des_ifs.
      { eapply World.disjoint_comm. eapply UPDATE0; eauto. }
      { eapply UPDATE0; eauto. }
      { eapply (DISJOINT tid0 tid1); eauto. }
    }
  Qed.
End INVARIANT.

Section PCM.
  Context `{M: URA.t}.

  Definition pcm_disjoint: URA.car -> URA.car -> Prop :=
    fun r0 r1 => forall (WF0: URA.wf r0) (WF1: URA.wf r1), URA.wf (r0 ⋅ r1).

  (* Definition pcm_disjoint: URA.car -> URA.car -> Prop := *)
  (*   fun r0 r1 => URA.wf (r0 ⋅ r1). *)

  (* Definition pcm_compatible: URA.car -> URA.car -> Prop := *)
  (*   fun g r => forall (WF: URA.wf g), URA.wf (g ⋅ r). *)

  Global Program Instance pcm_world: World.t :=
    @World.mk URA.car URA.car URA.unit pcm_disjoint pcm_disjoint _ _ _.
  Next Obligation.
    ii. rewrite URA.unit_id. auto.
  Qed.
  Next Obligation.
    ii. rewrite URA.unit_idl. auto.
  Qed.
  Next Obligation.
    ii. rewrite URA.add_comm. eapply DISJ; eauto.
  Qed.

  Lemma updatable_update g0 r0 g1 r1
        (COMPAT: World.compatible g0 r0)
        (UPDATABLE: URA.updatable (g0 ⋅ r0) (g1 ⋅ r1))
        (WF0: URA.wf g0)
        (WF1: URA.wf r0)
    :
    (<<UPDATE: World.update (g0, r0) (g1, r1)>>) /\ (<<WF0: URA.wf g1>>) /\ (<<WF1: URA.wf r1>>).
  Proof.
    pose proof (UPDATABLE URA.unit) as UNIT.
    hexploit UNIT.
    { rewrite URA.unit_id. eapply COMPAT; eauto. }
    i. rewrite URA.unit_id in H. splits.
    { econs. i. splits.
      { ii. eauto. }
      { i. split.
  Abort.
End PCM.
