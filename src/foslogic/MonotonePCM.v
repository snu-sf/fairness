From sflib Require Import sflib.
From Fairness Require Import PCM IPropFOS IPMFOS.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.PropExtensionality.
From Fairness Require Import Axioms.
Require Import Program.

Set Implicit Arguments.


Module FiniteMap.
  Section FiniteMap.
    Context `{M: URA.t}.

    Definition car := nat -> option M.(URA.car).

    Definition unit: car := fun _ => None.

    Definition add (f0 f1: car): car :=
      fun n =>
        match (f0 n), (f1 n) with
        | None, _ => f1 n
        | _, None => f0 n
        | Some m0, Some m1 => Some (URA.add m0 m1)
        end.

    Definition wf (f: car): Prop :=
      (<<POINTWISE: forall n m (EQ: f n = Some m), URA.wf m>>) /\ (<<FIN: exists k, forall n (LE: k < n), f n = None>>).

    Definition core (f: car): car := fun n =>
                                       match (f n) with
                                       | Some m => Some (URA.core m)
                                       | None => None
                                       end.

    Global Program Instance t: URA.t := {
        car := car;
        unit := unit;
        _add := add;
        _wf := wf;
        core := core;
      }
    .
    Next Obligation.
      unfold add. apply func_ext.
      ii. des_ifs. f_equal.
      rewrite URA.add_comm. ss.
    Qed.
    Next Obligation.
      unfold add. apply func_ext.
      ii. des_ifs. f_equal.
      rewrite URA.add_assoc. ss.
    Qed.
    Next Obligation.
      unfold add. unseal "ra". apply func_ext.
      ii. des_ifs.
    Qed.
    Next Obligation.
      unfold unit, wf. unseal "ra". splits; auto.
      { i. ss. }
      { exists 0. auto. }
    Qed.
    Next Obligation.
      unseal "ra". unfold wf, add in *.
      des. splits; auto.
      { i. hexploit POINTWISE.
        { rewrite EQ.
          instantiate (1:= match b n with
                           | Some m1 => m ⋅ m1
                           | None => m
                           end). des_ifs.
        }
        { des_ifs. i. eapply URA.wf_mon; eauto. }
      }
      { exists k. i. hexploit FIN; eauto. i. des_ifs. }
    Qed.
    Next Obligation.
      unseal "ra". unfold add, core. apply func_ext.
      ii. des_ifs. f_equal.
      rewrite URA.core_id. ss.
    Qed.
    Next Obligation.
      unfold core. apply func_ext.
      ii. des_ifs. f_equal.
      rewrite URA.core_idem. ss.
    Qed.
    Next Obligation.
      unseal "ra".
      hexploit (choice (fun (n: nat) (m: option URA.car) =>
                          core (add a b) n = match (core a n), m with
                                             | None, _ => m
                                             | _, None => core a n
                                             | Some m0, Some m1 => Some (URA.add m0 m1)
                                             end)).
      { i. unfold core, add. des_ifs.
        { hexploit URA.core_mono. i. des.
          rewrite H. exists (Some c). auto.
        }
        { exists None. auto. }
        { eauto. }
        { eauto. }
      }
      i. des. exists f. apply func_ext.
      i. rewrite H. unfold add, core. des_ifs.
    Qed.

    Definition singleton (k: nat) (m: @URA.car M):
      @URA.car t :=
      fun n => if Nat.eq_dec n k then Some m else None.

    Lemma singleton_wf k m
      :
      URA.wf (singleton k m) <-> URA.wf m.
    Proof.
      split; i.
      { rewrite URA.unfold_wf in H. rr in H.
        des. eapply POINTWISE. unfold singleton. des_ifs.
      }
      { rewrite URA.unfold_wf. rr. splits.
        { i. unfold singleton in *. des_ifs. }
        { exists k. i. unfold singleton. des_ifs. lia. }
      }
    Qed.

    Lemma singleton_add k m0 m1
      :
      URA.add (singleton k m0) (singleton k m1)
      =
        singleton k (URA.add m0 m1).
    Proof.
      rewrite URA.unfold_add. ss.
      unfold singleton, add. apply func_ext. i. des_ifs.
    Qed.

    Lemma singleton_core_total k m
      :
      URA.core (singleton k m) = singleton k (URA.core m).
    Proof.
      unfold URA.car. ss.
      apply func_ext. i. unfold core, singleton. des_ifs.
    Qed.

    Lemma singleton_updatable k m0 m1
          (UPD: @URA.updatable M m0 m1)
      :
      URA.updatable (singleton k m0) (singleton k m1).
    Proof.
      ii. rewrite URA.unfold_wf in H. rr in H. des.
      hexploit (UPD (match ctx k with
                     | Some a => a
                     | None => URA.unit
                     end)).
      { rewrite URA.unfold_add in POINTWISE. ss.
        eapply (POINTWISE k).
        unfold add, singleton. des_ifs. rewrite URA.unit_id. auto.
      }
      i.
      assert (OTHER: forall n m (NEQ: n <> k) (EQ: ctx n = Some m), URA.wf m).
      { i. eapply (POINTWISE n).
        rewrite URA.unfold_add. ss. unfold add, singleton. des_ifs.
      }
      rewrite URA.unfold_wf. ss. rr. splits.
      { i. rewrite URA.unfold_add in EQ. ss. unfold add, singleton in EQ.
        des_ifs; eauto. r_wf H.
      }
      { exists k0. i. hexploit FIN; eauto.
        rewrite URA.unfold_add. i. ss.
        unfold add, singleton in *. des_ifs.
      }
    Qed.

    Lemma singleton_extends k m0 m1
          (UPD: @URA.extends M m0 m1)
      :
      URA.extends (singleton k m0) (singleton k m1).
    Proof.
      r in UPD. des. exists (singleton k ctx).
      rewrite singleton_add. subst. auto.
    Qed.

    Lemma singleton_updatable_set k m s
          (UPD: @URA.updatable_set M m s)
      :
      URA.updatable_set (singleton k m) (fun a => exists m1, s m1 /\ a = singleton k m1).
    Proof.
      ii. rewrite URA.unfold_wf in WF. rr in WF. des.
      hexploit (UPD (match ctx k with
                     | Some a => a
                     | None => URA.unit
                     end)).
      { rewrite URA.unfold_add in POINTWISE. ss.
        eapply (POINTWISE k).
        unfold add, singleton. des_ifs. rewrite URA.unit_id. auto.
      }
      i. destruct H as [m1 [SAT H]]. des.
      assert (OTHER: forall n m (NEQ: n <> k) (EQ: ctx n = Some m), URA.wf m).
      { i. eapply (POINTWISE n).
        rewrite URA.unfold_add. ss. unfold add, singleton. des_ifs.
      }
      exists (singleton k m1). splits.
      { splits; eauto. }
      rewrite URA.unfold_wf. ss. rr. splits.
      { i. rewrite URA.unfold_add in EQ. ss. unfold add, singleton in EQ.
        des_ifs; eauto. r_wf H.
      }
      { exists k0. i. hexploit FIN; eauto.
        rewrite URA.unfold_add. i. ss.
        unfold add, singleton in *. des_ifs.
      }
    Qed.

    Lemma singleton_alloc (m: @URA.car M) (f: @URA.car t)
          (WF: URA.wf m)
      :
      URA.updatable_set f (fun f1 => exists k, f1 = singleton k m).
    Proof.
      ii. rewrite URA.unfold_wf in WF0. rr in WF0. des.
      exists (singleton (S k) m). splits.
      { eauto. }
      hexploit (FIN (S k)).
      { lia. }
      i. rewrite URA.unfold_add in H. ss. unfold add in H. des_ifs.
      rewrite URA.unfold_wf. ss. rr. split.
      { ii. rewrite URA.unfold_add in EQ. ss.
        unfold add, singleton in EQ. des_ifs.
        hexploit (POINTWISE n (m0 ⋅ match f n with
                                    | Some a => a
                                    | None => URA.unit
                                    end)).
        { rewrite URA.unfold_add. ss. unfold add. des_ifs.
          { rewrite URA.add_comm. auto. }
          { rewrite URA.unit_id. auto. }
        }
        i. eapply URA.wf_mon; eauto.
      }
      { exists (S k). i. hexploit (FIN n).
        { lia. }
        i. rewrite URA.unfold_add. rewrite URA.unfold_add in H0.
        ss. unfold add, singleton in *. des_ifs. lia.
      }
    Qed.
  End FiniteMap.
End FiniteMap.


Module Collection.
  Section Collection.
    Variable A: Type.

    Definition car: Type := A -> Prop.

    Definition unit: car := fun _ => True.

    Definition add: car -> car -> car :=
      fun s0 s1 a => s0 a /\ s1 a.

    Definition wf: car -> Prop :=
      fun _ => True.

    Definition core: car -> car :=
      fun s => s.

    Program Instance t: URA.t := {
        car := car;
        unit := unit;
        _add := add;
        _wf := wf;
        core := core;
      }
    .
    Next Obligation.
    Proof.
      unfold add. extensionality a0.
      eapply propositional_extensionality. split; i; des; ss.
    Qed.
    Next Obligation.
    Proof.
      unfold add. extensionality a0.
      eapply propositional_extensionality. split; i; des; ss.
    Qed.
    Next Obligation.
    Proof.
      unseal "ra". unfold add. extensionality a0.
      eapply propositional_extensionality. split; i; des; ss.
    Qed.
    Next Obligation.
    Proof.
      unseal "ra". ss.
    Qed.
    Next Obligation.
    Proof.
      unseal "ra". ss.
    Qed.
    Next Obligation.
    Proof.
      unseal "ra". unfold add, core. extensionality a0.
      eapply propositional_extensionality. split; i; des; ss.
    Qed.
    Next Obligation.
    Proof.
      unseal "ra".
      unfold add, core. esplits; eauto.
    Qed.
  End Collection.
End Collection.


Variant gmon: Type :=
  | mk_gmon
      (A: Type)
      (le: A -> A -> Prop)
      (ORDER: PreOrder le)
      (a: A)
.

Variant gmon_le: gmon -> gmon -> Prop :=
  | mk_gmon_intro
      A (le: A -> A -> Prop) ORDER a0 a1 (LE: le a0 a1)
    :
    gmon_le (@mk_gmon A le ORDER a0) (@mk_gmon A le ORDER a1)
.

Program Instance gmon_le_PreOrder: PreOrder gmon_le.
Next Obligation.
  ii. destruct x. econs. reflexivity.
Qed.
Next Obligation.
  ii. dependent destruction H. dependent destruction H0.
  replace ORDER0 with ORDER.
  { econs; eauto. etrans; eauto. }
  eapply proof_irrelevance.
Qed.



Lemma embed_core_commute `{@GRA.inG M Σ}
      (r: M)
  :
  GRA.embed (URA.core r) = URA.core (GRA.embed r).
Proof.
  Local Transparent GRA.to_URA URA.unit.
  dependent destruction H. subst.
  extensionality n. ss. unfold URA.core at 2. ss.
  unfold GRA.embed. destruct (PeanoNat.Nat.eq_dec GRA.inG_id n) eqn:EQ; ss.
  { subst. ss. }
  { des_ifs. ss. transitivity (add (core unit) unit); auto. }
Qed.

Lemma own_persistent `{@GRA.inG M Σ}
      (r: M)
  :
  (OwnM r) -∗ (□ OwnM (URA.core r)).
Proof.
  rr. autorewrite with iprop. i.
  rr. autorewrite with iprop. split.
  { rr. autorewrite with iprop. auto. }
  { rr. autorewrite with iprop.
    rr in H0. autorewrite with iprop in H0.
    rr. autorewrite with iprop.
    eapply URA.extends_core in H0.
    rewrite embed_core_commute. auto.
  }
Qed.

Lemma OwnM_unit `{@GRA.inG M Σ}
  :
  ⊢ OwnM (@URA.unit M).
Proof.
  rr. autorewrite with iprop. i.
  rr. autorewrite with iprop.
  exists r.
  Local Transparent GRA.to_URA URA.unit.
  replace (GRA.embed ε) with (@URA.unit Σ).
  { rewrite URA.unit_idl. auto. }
  unfold GRA.embed. extensionality n. des_ifs. ss.
  destruct H. ss. destruct inG_prf. ss.
Qed.

Section Monotone.
  Definition monoRA: URA.t := @FiniteMap.t (Auth.t (Collection.t gmon)).
  Context `{@GRA.inG monoRA Σ}.

  Section LE.
    Variable k: nat.

    Variable W: Type.
    Variable le: W -> W -> Prop.
    Hypothesis le_PreOrder: PreOrder le.

    Let leR (w: W): Collection.t gmon := gmon_le (@mk_gmon W le le_PreOrder w).

    Definition monoBlack (w: W): iProp :=
      OwnM (FiniteMap.singleton k (Auth.black (leR w) ⋅ Auth.white (leR w))).

    Definition monoWhiteExact (w: W): iProp :=
      OwnM (FiniteMap.singleton k (Auth.white (leR w))).

    Definition monoWhite (w0: W): iProp :=
      ∃ w1, monoWhiteExact w1 ∧ ⌜le w0 w1⌝.

    Lemma white_idempotent w0 w1
          (LE: le w0 w1)
      :
      Auth.white (leR w0) ⋅ Auth.white (leR w1) = Auth.white (leR w1).
    Proof.
      unfold Auth.white.
      unfold URA.add. unseal "ra". ss.
      unfold URA.add. unseal "ra". ss.
      unfold Collection.add. f_equal. extensionality a.
      eapply propositional_extensionality. split; i; des; ss.
      split; auto. rr. etrans; eauto. econs; eauto.
    Qed.

    Lemma white_exact_persistent w
      :
      (monoWhiteExact w) -∗ (□ monoWhiteExact w).
    Proof.
      unfold monoBlack, monoWhiteExact.
      iIntros "H". iPoseProof (own_persistent with "H") as "H".
      rewrite FiniteMap.singleton_core_total. auto.
    Qed.

    Global Program Instance Persistent_white_exact w: Persistent (monoWhiteExact w).
    Next Obligation.
    Proof.
      i. iIntros "WHITE". iPoseProof (white_exact_persistent with "WHITE") as "WHITE". auto.
    Qed.

    Lemma white_persistent w
      :
      (monoWhite w) -∗ (□ monoWhite w).
    Proof.
      unfold monoWhite. iIntros "H".
      iDestruct "H" as (w1) "[H %]".
      iPoseProof (white_exact_persistent with "H") as "# H0".
      iClear "∗". iModIntro.
      iExists _. iSplit; eauto.
    Qed.

    Global Program Instance Persistent_white w: Persistent (monoWhite w).

    Lemma black_persistent_white_exact w
      :
      (monoBlack w) -∗ (monoWhiteExact w).
    Proof.
      unfold monoBlack, monoWhiteExact.
      rewrite <- FiniteMap.singleton_add.
      iIntros "[_ H]". auto.
    Qed.

    Lemma black_white w
      :
      (monoBlack w) -∗ (monoWhite w).
    Proof.
      unfold monoWhite. iIntros "H".
      iPoseProof (black_persistent_white_exact with "H") as "H".
      iExists _. iSplit; eauto.
    Qed.

    Lemma white_mon w0 w1
          (LE: le w0 w1)
      :
      (monoWhite w1) -∗ (monoWhite w0).
    Proof.
      unfold monoWhite. iIntros "H".
      iDestruct "H" as (w) "[H %]".
      iExists _. iSplit; eauto. iPureIntro. etrans; eauto.
    Qed.

    Lemma black_updatable w0 w1
          (LE: le w0 w1)
      :
      (monoBlack w0) -∗ (#=> monoBlack w1).
    Proof.
      iIntros "H". iApply (OwnM_Upd with "H").
      eapply FiniteMap.singleton_updatable.
      eapply Auth.auth_update.
      rr. i. des. splits; auto.
      { rr. unseal "ra". ss. }
      { unfold URA.add in *. unseal "ra". ss.
        unfold Collection.add in *.
        extensionality w. eapply equal_f with (x:=w) in FRAME.
        eapply prop_ext_rev in FRAME. des.
        eapply propositional_extensionality. split; i; des; ss.
        split; eauto. eapply FRAME.
        rr. etrans; eauto. econs; eauto.
      }
    Qed.

    Lemma black_white_exact_compare w0 w1
      :
      (monoWhiteExact w0) -∗ (monoBlack w1) -∗ ⌜le w0 w1⌝.
    Proof.
      unfold monoWhiteExact, monoBlack.
      rewrite <- FiniteMap.singleton_add.
      iIntros "H0 [H1 H2]".
      iCombine "H1 H0" as "H".
      rewrite FiniteMap.singleton_add.
      iOwnWf "H". iPureIntro.
      rewrite FiniteMap.singleton_wf in H0.
      eapply Auth.auth_included in H0.
      rr in H0. des. unfold URA.add in H0. unseal "ra".
      ss. unfold Collection.add in H0.
      eapply equal_f in H0. eapply prop_ext_rev in H0. des.
      hexploit H1.
      { rr. econs. reflexivity. }
      i. des. rr in H2. dependent destruction H2. auto.
    Qed.

    Lemma black_white_compare w0 w1
      :
      (monoWhite w0) -∗ (monoBlack w1) -∗ ⌜le w0 w1⌝.
    Proof.
      unfold monoWhite.
      iIntros "H0 H1". iDestruct "H0" as (w) "[H0 %]".
      iPoseProof (black_white_exact_compare with "H0 H1") as "%".
      iPureIntro. etrans; eauto.
    Qed.
  End LE.

  Lemma monoBlack_alloc
        (W: Type)
        (le: W -> W -> Prop)
        (le_PreOrder: PreOrder le)
        (w: W)
    :
    ⊢ #=> (∃ k, monoBlack k le_PreOrder w).
  Proof.
    iPoseProof (@OwnM_unit _ _ H) as "H".
    iPoseProof (OwnM_Upd_set with "H") as "> H0".
    { eapply FiniteMap.singleton_alloc.
      instantiate (1:=@Auth.black (Collection.t gmon) (gmon_le (mk_gmon le_PreOrder w)) ⋅ @Auth.white (Collection.t gmon) (gmon_le (mk_gmon le_PreOrder w))).
      rewrite URA.unfold_wf. rewrite URA.unfold_add. ss. split.
      { exists (URA.unit). rewrite URA.unit_id.
        rewrite URA.unfold_add. ss. extensionality a.
        eapply propositional_extensionality. split; i; des; ss.
        rr in H0. des; auto.
      }
      { rewrite URA.unfold_wf. ss. }
    }
    iDestruct "H0" as (b) "[% H0]". des. subst.
    iModIntro. iExists k. auto.
  Qed.
End Monotone.


Section Monotone.
  Variable W: Type.
  Variable le: W -> W -> Prop.
  Hypothesis le_PreOrder: PreOrder le.

  Let leR (w: W): Collection.t W := le w.

  Definition monoRA2: URA.t := Auth.t (Collection.t W).

  Context `{@GRA.inG monoRA2 Σ}.

  Definition monoBlack2 (w: W): iProp :=
    OwnM (Auth.black (leR w) ⋅ Auth.white (leR w)).

  Definition monoWhiteExact2 (w: W): iProp :=
    OwnM (Auth.white (leR w)).

  Definition monoWhite2 (w0: W): iProp :=
    ∃ w1, monoWhiteExact2 w1 ∧ ⌜le w0 w1⌝.

  Lemma white_exact_persistent2 w
    :
    (monoWhiteExact2 w) -∗ (□ monoWhiteExact2 w).
  Proof.
    unfold monoBlack2, monoWhiteExact2.
    iIntros "H". iPoseProof (own_persistent with "H") as "H". ss.
  Qed.

  Global Program Instance Persistent_white_exact2 w: Persistent (monoWhiteExact2 w).
  Next Obligation.
  Proof.
    i. iIntros "WHITE". iPoseProof (white_exact_persistent2 with "WHITE") as "WHITE". auto.
  Qed.

  Lemma white_persistent2 w
    :
    (monoWhite2 w) -∗ (□ monoWhite2 w).
  Proof.
    unfold monoWhite2. iIntros "H".
    iDestruct "H" as (w1) "[H %]".
    iPoseProof (white_exact_persistent2 with "H") as "# H0".
    iClear "∗". iModIntro.
    iExists _. iSplit; eauto.
  Qed.

  Global Program Instance Persistent_white2 w: Persistent (monoWhite2 w).

  Lemma black_white_exact2 w
    :
    (monoBlack2 w) -∗ (monoWhiteExact2 w).
  Proof.
    unfold monoBlack2, monoWhiteExact2.
    iIntros "[_ H]". ss.
  Qed.

  Lemma black_white2 w
    :
    (monoBlack2 w) -∗ (monoWhite2 w).
  Proof.
    unfold monoWhite2. iIntros "H".
    iPoseProof (black_white_exact2 with "H") as "H".
    iExists _. iSplit; eauto.
  Qed.

  Lemma white_mon2 w0 w1
    :
    (monoWhite2 w1) -∗ ⌜le w0 w1⌝ -∗ (monoWhite2 w0).
  Proof.
    unfold monoWhite2. iIntros "H %".
    iDestruct "H" as (w) "[H %]".
    iExists _. iSplit; eauto. iPureIntro. etrans; eauto.
  Qed.

  Lemma black_updatable2 w0 w1
        (LE: le w0 w1)
    :
    (monoBlack2 w0) -∗ (#=> monoBlack2 w1).
  Proof.
    iIntros "H". iApply (OwnM_Upd with "H").
    eapply Auth.auth_update.
    rr. i. des. splits; auto.
    { rr. unseal "ra". ss. }
    { unfold URA.add in *. unseal "ra". ss.
      unfold Collection.add in *.
      extensionality w. eapply equal_f with (x:=w) in FRAME.
      eapply prop_ext_rev in FRAME. des.
      eapply propositional_extensionality. split; i; des; ss.
      split; eauto. eapply FRAME. etrans; eauto.
    }
  Qed.

  Lemma black_white_exact_compare2 w0 w1
    :
    (monoWhiteExact2 w0) -∗ (monoBlack2 w1) -∗ ⌜le w0 w1⌝.
  Proof.
    iIntros "H0 [H1 H2]".
    iCombine "H1 H0" as "H". iOwnWf "H".
    iPureIntro. eapply Auth.auth_included in H0.
    rr in H0. des. unfold URA.add in H0. unseal "ra".
    ss. unfold Collection.add in H0.
    eapply equal_f in H0. eapply prop_ext_rev in H0. des.
    eapply H1. reflexivity.
  Qed.

  Lemma black_white_compare2 w0 w1
    :
    (monoWhite2 w0) -∗ (monoBlack2 w1) -∗ ⌜le w0 w1⌝.
  Proof.
    unfold monoWhite2.
    iIntros "H0 H1". iDestruct "H0" as (w) "[H0 %]".
    iPoseProof (black_white_exact_compare2 with "H0 H1") as "%".
    iPureIntro. etrans; eauto.
  Qed.
End Monotone.


Section MAP.
  Definition partial_map_le A B (f0 f1: A -> option B): Prop :=
    forall a b (SOME: f0 a = Some b), f1 a = Some b.

  Global Program Instance partial_map_PreOrder A B: PreOrder (@partial_map_le A B).
  Next Obligation.
  Proof.
    ii. auto.
  Qed.
  Next Obligation.
  Proof.
    ii. eapply H0. eapply H. auto.
  Qed.

  Definition partial_map_empty A B: A -> option B :=
    fun _ => None.

  Definition partial_map_update A B (a: A) (b: B) (f: A -> option B):
    A -> option B :=
    fun a' => if (excluded_middle_informative (a' = a)) then Some b else (f a').

  Definition partial_map_singleton A B (a: A) (b: B): A -> option B :=
    partial_map_update a b (@partial_map_empty A B).

  Definition partial_map_update_le A B (a: A) (b: B) (f: A -> option B)
             (NONE: f a = None)
    :
    partial_map_le f (partial_map_update a b f).
  Proof.
    ii. unfold partial_map_update. des_ifs.
  Qed.

  Definition partial_map_update_le_singleton A B (a: A) (b: B) (f: A -> option B)
             (NONE: f a = None)
    :
    partial_map_le (partial_map_singleton a b) (partial_map_update a b f).
  Proof.
    ii. unfold partial_map_singleton, partial_map_update in *. des_ifs.
  Qed.

  Lemma partial_map_singleton_le_iff A B (a: A) (b: B) f
    :
    partial_map_le (partial_map_singleton a b) f <-> (f a = Some b).
  Proof.
    split.
    { i. eapply H. unfold partial_map_singleton, partial_map_update. des_ifs. }
    { ii. unfold partial_map_singleton, partial_map_update in *. des_ifs. }
  Qed.
End MAP.


From iris.bi Require Import derived_laws. Import bi.
Require Export Coq.Sorting.Mergesort. Import NatSort.


Create HintDb mset.
Section MUPD.
  Definition mset := list nat.
  Definition mset_disjoint (s0 s1: mset): Prop :=
    forall n (IN0: List.In n s0) (IN1: List.In n s1), False.

  Fixpoint mset_disjoint_b (s0 s1: mset): bool :=
    match s0 with
    | [] => true
    | hd::tl =>
        match find (Nat.eqb hd) s1 with
        | Some _ => false
        | None => mset_disjoint_b tl s1
        end
    end.

  Lemma mset_disjoint_b_reflect s0 s1
    :
    mset_disjoint s0 s1 <-> mset_disjoint_b s0 s1 = true.
  Proof.
    induction s0; ss.
    { split; i; auto. ii. inv IN0. }
    des_ifs.
    { split; i.
      { eapply find_some in Heq. des.
        rewrite Nat.eqb_eq in Heq0. subst.
        exfalso. eapply H; eauto. econs; ss.
      }
      { ii. inv IN0; eauto. }
    }
    { rewrite <- IHs0. split; i.
      { ii. eapply H; eauto. econs 2; ss. }
      { ii. inv IN0.
        { eapply find_none in Heq; eauto. rewrite Nat.eqb_refl in Heq. ss. }
        { eapply H; eauto. }
      }
    }
  Qed.

  Definition list_sub A (s0 s1: list A): Prop :=
    exists s, Permutation (s ++ s0) s1.

  Global Program Instance list_sub_PreOrder A: PreOrder (@list_sub A).
  Next Obligation.
  Proof.
    ii. exists []. ss.
  Qed.
  Next Obligation.
  Proof.
    ii. unfold list_sub in *. des.
    rewrite <- H in H0. exists (s ++ s0).
    rewrite <- app_assoc. auto.
  Qed.

  Global Instance permutation_list_sub_proper A:
    Proper (Permutation ==> Permutation ==> iff) (@list_sub A).
  Proof.
    ii. unfold list_sub. split.
    { i. des. exists s. rewrite <- H. rewrite H1. auto. }
    { i. des. exists s. rewrite H0. rewrite H. auto. }
  Qed.

  Definition mset_sub (s0 s1: mset): Prop := list_sub s0 s1.

  Global Program Instance mset_sub_PreOrder: PreOrder mset_sub.

  Global Instance permutation_mset_sub_proper:
    Proper (Permutation ==> Permutation ==> iff) mset_sub.
  Proof.
    unfold mset_sub. typeclasses eauto.
  Qed.

  Global Instance permutation_mset_disjoint_proper:
    Proper (Permutation ==> Permutation ==> iff) mset_disjoint.
  Proof.
    ii. split.
    { ii. eapply H1.
      { symmetry in H. eapply Permutation_in; eauto. }
      { symmetry in H0. eapply Permutation_in; eauto. }
    }
    { ii. eapply H1.
      { eapply Permutation_in; eauto. }
      { eapply Permutation_in; eauto. }
    }
  Qed.

  Definition mset_minus (s0 s1: mset): mset :=
    match list_remove_list s1 s0 with
    | Some s => s
    | None => []
    end.

  Definition mset_sub_b (s0 s1: mset): bool :=
    match list_remove_list s0 s1 with
    | Some _ => true
    | None => false
    end.

  Lemma list_remove_none A `{EqDecision A} (a: A) (l: list A)
        (NONE: list_remove a l = None)
    :
    ~ List.In a l.
  Proof.
    revert NONE. induction l; ss.
    des_ifs. i. unfold fmap, option_fmap, option_map in NONE.
    des_ifs. ii. des; clarify. eapply IHl; auto.
  Qed.

  Lemma mset_sub_b_reflect s0 s1
    :
    mset_sub s0 s1 <-> mset_sub_b s0 s1 = true.
  Proof.
    revert s1. induction s0; ss; i.
    { split; i; auto. exists s1. rewrite app_nil_r. auto. }
    { unfold mset_sub_b in *. ss.
      destruct (list_remove a s1) eqn:EQ; ss.
      { eapply list_remove_Some in EQ.
        rewrite <- IHs0. unfold mset_sub, list_sub. split.
        { i. des. rewrite EQ in H.
          rewrite <- Permutation_middle in H.
          apply Permutation_cons_inv in H.
          exists s. auto.
        }
        { i. des. rewrite <- H in EQ.
          eexists s. rewrite EQ. rewrite <- Permutation_middle. auto.
        }
      }
      { eapply list_remove_none in EQ. split; i; ss.
        exfalso. unfold mset_sub, list_sub in H. des.
        rewrite <- Permutation_middle in H.
        eapply EQ. eapply Permutation_in; eauto.
        econs; ss.
      }
    }
  Qed.

  Context `{Σ: GRA.t}.
  Variable I: nat -> iProp.
  Variable IA: iProp.
  Definition mset_all (l: mset) := fold_right (fun n P => I n ** P) True%I l.

  Lemma mset_all_nil
    :
    ⊢ mset_all [].
  Proof.
    unfold mset_all. ss. auto.
  Qed.

  Lemma mset_all_cons_fold hd tl
    :
    (I hd ** mset_all tl)
      -∗
      (mset_all (hd::tl)).
  Proof.
    unfold mset_all. ss.
  Qed.

  Lemma mset_all_cons_unfold hd tl
    :
    (mset_all (hd::tl))
      -∗
      (I hd ** mset_all tl).
  Proof.
    unfold mset_all. ss.
  Qed.

  Lemma mset_all_split l0 l1
    :
    (mset_all (l0 ++ l1))
      -∗
      (mset_all l0 ** mset_all l1).
  Proof.
    induction l0; ss.
    { iIntros "SAT". iFrame. }
    { iIntros "[INTERP SAT]". iFrame. iApply IHl0; auto. }
  Qed.

  Lemma mset_all_combine l0 l1
    :
    (mset_all l0 ** mset_all l1)
      -∗
      (mset_all (l0 ++ l1)).
  Proof.
    induction l0; ss.
    { iIntros "[_ SAT]". auto. }
    { iIntros "[[INTERP SAT0] SAT1]". iFrame.
      iApply IHl0. iFrame.
    }
  Qed.

  Lemma mset_all_add l a
    :
    (I a ** mset_all l)
      -∗
      (mset_all (l++[a])).
  Proof.
    iIntros "[NEW SAT]". iApply mset_all_combine. iFrame.
  Qed.

  Lemma mset_all_permutation l0 l1
        (PERM: Permutation l0 l1)
    :
    mset_all l0 ⊢ mset_all l1.
  Proof.
    induction PERM.
    { auto. }
    { iIntros "H". iApply mset_all_cons_fold.
      iPoseProof (mset_all_cons_unfold with "H") as "[HD TL]".
      iFrame. iApply IHPERM; auto.
    }
    { iIntros "H". iApply mset_all_cons_fold.
      iPoseProof (mset_all_cons_unfold with "H") as "[HD0 TL]".
      iPoseProof (mset_all_cons_unfold with "TL") as "[HD1 TL]".
      iSplitL "HD1"; auto. iApply mset_all_cons_fold. iFrame.
    }
    { etrans; eauto. }
  Qed.

  Lemma mset_all_sub l0 l1
        (SUB: mset_sub l0 l1)
    :
    mset_all l1 ⊢ mset_all l0 ** (mset_all l0 -* mset_all l1).
  Proof.
    rr in SUB. des. iIntros "H".
    iPoseProof (mset_all_permutation with "H") as "H".
    { symmetry. eauto. }
    iPoseProof (mset_all_split with "H") as "[H0 H1]". iFrame.
    iIntros "H1". iApply mset_all_permutation; eauto.
    iApply mset_all_combine. iFrame.
  Qed.

  Lemma mset_all_discard l0 l1
        (SUB: mset_sub l0 l1)
    :
    mset_all l1 ⊢ mset_all l0.
  Proof.
    rewrite mset_all_sub; eauto. iIntros "[H0 H1]". iFrame.
  Qed.

  Lemma mset_all_update l k a
        (FIND: nth_error l k = Some a)
    :
    mset_all l ⊢ I a ** (I a -* mset_all l).
  Proof.
    hexploit nth_error_split; eauto. i. des. subst.
    iIntros "SAT". iPoseProof (mset_all_split with "SAT") as "[SAT0 SAT1]".
    iPoseProof (mset_all_cons_unfold with "SAT1") as "[OLD SAT1]".
    iFrame. iIntros "NEW". iApply mset_all_combine. iFrame.
  Qed.

  Lemma mset_all_nth_sub l k a
        (FIND: nth_error l k = Some a)
    :
    ⊢ SubIProp (I a) (mset_all l).
  Proof.
    iIntros "H". iPoseProof (mset_all_update with "H") as "[H0 H1]"; eauto.
    iFrame. iModIntro. iIntros "H". iModIntro. iApply ("H1" with "H").
  Qed.

  Lemma list_remove_permutation A `{EqDecision A} a (l0 l1: list A)
        (PERM: Permutation l0 l1)
    :
    option_Forall2 Permutation (list_remove a l0) (list_remove a l1).
  Proof.
    induction PERM; ss.
    { econs. }
    { des_ifs.
      { econs. auto. }
      { unfold fmap, option_fmap, option_map. inv IHPERM; econs.
        econs. auto.
      }
    }
    { des_ifs.
      { econs. auto. }
      { unfold fmap, option_fmap, option_map. reflexivity. }
      { unfold fmap, option_fmap, option_map. reflexivity. }
      { unfold fmap, option_fmap, option_map. des_ifs; econs. econs. }
    }
    { etrans; eauto. }
  Qed.

  Lemma list_remove_list_permutation_l A `{EqDecision A} (l l0 l1: list A)
        (PERM: Permutation l0 l1)
    :
    option_Forall2 Permutation (list_remove_list l l0) (list_remove_list l l1).
  Proof.
    revert l0 l1 PERM. induction l; i.
    { ss. econs; eauto. }
    ss. unfold mbind, option_bind.
    hexploit list_remove_permutation.
    { eapply PERM. }
    instantiate (1:=a). i. inv H.
    { rewrite <- H0. rewrite <- H1. auto. }
    { rewrite <- H1. rewrite <- H2. econs. }
  Qed.

  Lemma list_remove_add_permutation A `{EqDecision A} a (l0 l1: list A)
        (REMOVE: list_remove a l0 = Some l1)
    :
    Permutation l0 (a :: l1).
  Proof.
    revert l1 REMOVE. induction l0; i; ss. des_ifs.
    unfold fmap, option_fmap, option_map in REMOVE. des_ifs.
    rewrite IHl0; eauto. econs.
  Qed.

  Lemma list_remove_list_add_permutation A `{EqDecision A} (l l0 l1: list A)
        (REMOVE: list_remove_list l l0 = Some l1)
    :
    Permutation l0 (l ++ l1).
  Proof.
    revert l0 l1 REMOVE. induction l; i; ss.
    { clarify. }
    unfold mbind, option_bind in REMOVE. des_ifs.
    hexploit IHl; eauto. i. rewrite <- H.
    eapply list_remove_add_permutation; eauto.
  Qed.

  Lemma list_remove_list_permutation_r A `{EqDecision A} (l l0 l1: list A)
        (PERM: Permutation l0 l1)
    :
    option_Forall2 Permutation (list_remove_list l0 l) (list_remove_list l1 l).
  Proof.
    destruct (list_remove_list l0 l) eqn:EQ0, (list_remove_list l1 l) eqn:EQ1.
    { econs.
      eapply list_remove_list_add_permutation in EQ0.
      eapply list_remove_list_add_permutation in EQ1.
      rewrite EQ0 in EQ1. rewrite PERM in EQ1.
      eapply Permutation_app_inv_l; eauto.
    }
    { assert (submseteq l0 l).
      { eapply list_remove_list_submseteq. rewrite EQ0. ss. }
      rewrite PERM in H. eapply list_remove_list_submseteq in H.
      rewrite EQ1 in H. inv H. ss.
    }
    { assert (submseteq l1 l).
      { eapply list_remove_list_submseteq. rewrite EQ1. ss. }
      rewrite <- PERM in H. eapply list_remove_list_submseteq in H.
      rewrite EQ0 in H. inv H. ss.
    }
    { econs. }
  Qed.

  Global Instance permutation_mset_minus_proper:
    Proper (Permutation ==> Permutation ==> Permutation) mset_minus.
  Proof.
    ii. unfold mset_minus.
    cut (option_Forall2 Permutation (list_remove_list x0 x) (list_remove_list y0 y)).
    { i. inv H1; ss. }
    rewrite list_remove_list_permutation_r; [|eauto].
    eapply list_remove_list_permutation_l; auto.
  Qed.

  Lemma mset_minus_add_eq E1 E
        (SUB: mset_sub E1 E)
    :
    Permutation E (E1 ++ mset_minus E E1).
  Proof.
    rr in SUB. des. rewrite <- SUB.
    unfold mset_minus.
    assert (is_Some (list_remove_list E1 (s ++ E1))).
    { eapply list_remove_list_submseteq.
      eapply submseteq_inserts_l. reflexivity.
    }
    inv H. rewrite H0.
    eapply list_remove_list_add_permutation; auto.
  Qed.

  Definition MUpd (l0 l1: mset) (P: iProp): iProp :=
    (IA ** mset_all l0) -* #=> ((IA ** mset_all l1) ** P).

  Lemma MUpd_open i:
    ⊢ MUpd [i] [] (I i ** (I i -* (MUpd [] [i] True))).
  Proof.
    i. iIntros "[X [H0 H1]]". ss. iModIntro. iFrame.
    iIntros "H0 [X H1]". iModIntro. ss. iFrame.
  Qed.

  Lemma MUpd_mask_subseteq E1 E2 :
    mset_sub E2 E1 -> ⊢ MUpd E1 E2 (MUpd E2 E1 emp).
  Proof.
    i. iIntros "[X H]".
    iPoseProof (mset_all_sub with "H") as "[H0 H1]"; eauto.
    iModIntro. iFrame. iIntros "[X H0]". iModIntro. iSplit; auto. iFrame.
    iApply "H1"; auto.
  Qed.

  Lemma MUpd_mono E1 E2 P Q
    :
    (P ⊢ Q) -> (MUpd E1 E2 P ⊢ MUpd E1 E2 Q).
  Proof.
    i. iIntros "H0 H1". iPoseProof ("H0" with "H1") as "> [H0 H1]".
    iModIntro. iFrame. iApply H. auto.
  Qed.

  Lemma MUpd_trans E1 E2 E3 P
    :
    MUpd E1 E2 (MUpd E2 E3 P) ⊢ MUpd E1 E3 P.
  Proof.
    iIntros "H0 H1". iPoseProof ("H0" with "H1") as "> [H0 H1]".
    iPoseProof ("H1" with "H0") as "> [H0 H1]".
    iModIntro. iFrame.
  Qed.

  Lemma MUpd_frame_r E1 E2 P R
    :
    MUpd E1 E2 P ** R ⊢ MUpd E1 E2 (P ** R).
  Proof.
    iIntros "[H0 H1] H2". iPoseProof ("H0" with "H2") as "> [H0 H2]".
    iModIntro. iFrame.
  Qed.

  Lemma MUpd_mask_frame_r E1 E2 Ef P
    :
    (MUpd E1 E2 P ⊢ MUpd (E1 ++ Ef) (E2 ++ Ef) P).
  Proof.
    i. iIntros "H0 [X H1]".
    iPoseProof (mset_all_split with "H1") as "[H1 H2]".
    iPoseProof ("H0" with "[X H1]") as "> [[X H0] H1]".
    { iFrame. }
    iModIntro. iFrame. iApply (mset_all_combine with "[H2 H0]"). iFrame.
  Qed.

  Global Instance MUpd_ne E1 E2 : NonExpansive (MUpd E1 E2).
  Proof.
    ii. unfold MUpd. rewrite H. auto.
  Qed.

  Global Instance MUpd_proper E1 E2 :
    Proper ((≡) ==> (≡)) (MUpd E1 E2) := ne_proper _.

  Global Instance MUpd_mono' E1 E2 : Proper ((⊢) ==> (⊢)) (MUpd E1 E2).
  Proof. intros P Q; apply MUpd_mono. Qed.
  Global Instance MUpd_flip_mono' E1 E2 :
    Proper (flip (⊢) ==> flip (⊢)) (MUpd E1 E2).
  Proof. intros P Q; apply MUpd_mono. Qed.

  Lemma MUpd_mask_intro_subseteq E1 E2 P :
    mset_sub E2 E1 -> P ⊢ MUpd E1 E2 (MUpd E2 E1 P).
  Proof.
    intros HE. iIntros "H0". iApply MUpd_mono.
    { eapply MUpd_mono. instantiate (1:=emp ** P).
      iIntros "[H0 H1]". auto.
    }
    { iApply MUpd_mono.
      { iApply MUpd_frame_r. }
      iApply MUpd_frame_r. iFrame.
      iApply MUpd_mask_subseteq. auto.
    }
  Qed.

  Lemma MUpd_intro E P : P ⊢ MUpd E E P.
  Proof.
    etrans.
    { eapply MUpd_mask_intro_subseteq. reflexivity. }
    { eapply MUpd_trans. }
  Qed.

  Lemma MUpd_idemp E P : (MUpd E E (MUpd E E P)) ⊣⊢ MUpd E E P.
  Proof.
    apply: anti_symm.
    - apply MUpd_trans.
    - apply MUpd_intro.
  Qed.

  Lemma MUpd_mask_weaken {E1} E2 {E3 P} :
    mset_sub E2 E1 ->
    (MUpd E2 E1 emp -* MUpd E2 E3 P) -∗ MUpd E1 E3 P.
  Proof.
    intros HE.
    iIntros "H1".
    iPoseProof MUpd_mask_subseteq as "H0"; eauto.
    iPoseProof (MUpd_frame_r with "[H0 H1]") as "H".
    { iSplitR "H1".
      { iExact "H0". }
      { iExact "H1". }
    }
    iApply MUpd_trans. iClear "H0".
    iStopProof. eapply MUpd_mono.
    eapply wand_elim_r.
  Qed.

  Lemma MUpd_mask_intro E1 E2 P :
    mset_sub E2 E1 ->
    ((MUpd E2 E1 emp) -∗ P) -∗ MUpd E1 E2 P.
  Proof.
    intros. etrans; [|by apply MUpd_mask_weaken].
    rewrite <- MUpd_intro. auto.
  Qed.

  Lemma MUpd_mask_intro_discard E1 E2 P:
    mset_sub E2 E1 -> P ⊢ MUpd E1 E2 P.
  Proof.
    intros. etrans; [|by apply MUpd_mask_intro].
    apply Wand_intro_r. rewrite sep_elim_l; try done.
    econs 2. typeclasses eauto.
  Qed.

  Lemma MUpd_frame_l E1 E2 R Q : (R ∗ MUpd E1 E2 Q) ⊢ MUpd E1 E2 (R ∗ Q).
  Proof. rewrite !(comm _ R); apply MUpd_frame_r. Qed.
  Lemma MUpd_wand_l E1 E2 P Q : (P -∗ Q) ∗ (MUpd E1 E2 P) ⊢ MUpd E1 E2 Q.
  Proof. rewrite MUpd_frame_l. rewrite wand_elim_l. auto. Qed.
  Lemma MUpd_wand_r E1 E2 P Q : (MUpd E1 E2 P) ∗ (P -∗ Q) ⊢ MUpd E1 E2 Q.
  Proof. rewrite MUpd_frame_r. rewrite wand_elim_r. auto. Qed.

  Lemma MUpd_trans_frame E1 E2 E3 P Q :
    ((Q -* MUpd E2 E3 emp) ∗ MUpd E1 E2 (Q ∗ P)) ⊢ MUpd E1 E3 P.
  Proof.
    rewrite MUpd_frame_l.
    iIntros "H0". iApply MUpd_trans.
    iApply (MUpd_mono with "H0").
    iIntros "[H0 [H1 H2]]".
    iPoseProof ("H0" with "H1") as "H0".
    iApply MUpd_mono.
    { instantiate (1:=emp ** P). iIntros "[H0 H1]". auto. }
    iApply MUpd_frame_r. iFrame.
  Qed.

  Lemma MUpd_elim E1 E2 E3 P Q :
    (Q -∗ MUpd E2 E3 P) -> (MUpd E1 E2 Q) -∗ (MUpd E1 E3 P).
  Proof.
    i. rewrite H. rewrite MUpd_trans. auto.
  Qed.

  Lemma MUpd_permutation E1 E2 E1' E2' P
        (PERM0: Permutation E1 E1')
        (PERM1: Permutation E2 E2')
    :
    MUpd E1' E2' P ⊢ MUpd E1 E2 P.
  Proof.
    iIntros "H".
    iApply MUpd_trans.
    iApply MUpd_mask_intro_discard.
    { rewrite PERM0. reflexivity. }
    iApply MUpd_trans. iApply (MUpd_mono with "H").
    iApply MUpd_mask_intro_discard. rewrite PERM1. reflexivity.
  Qed.

  Lemma MUpd_sort E1 E2 P
    :
    MUpd (NatSort.sort E1) (NatSort.sort E2) P ⊢ MUpd E1 E2 P.
  Proof.
    apply MUpd_permutation.
    { apply Permuted_sort. }
    { apply Permuted_sort. }
  Qed.

  Lemma MUpd_mask_mono E1 E2 P : mset_sub E1 E2 -> MUpd E1 E1 P ⊢ MUpd E2 E2 P.
  Proof.
    i. rr in H. des.
    symmetry in H. rewrite Permutation_app_comm in H.
    iIntros "H". iPoseProof (MUpd_mask_frame_r with "H") as "H".
    iApply (MUpd_permutation with "H"); eauto.
  Qed.

  Lemma MUpd_mask_frame E E' E1 E2 P :
    mset_sub E1 E →
    (MUpd E1 E2 (MUpd (E2 ++ (mset_minus E E1)) E' P)) -∗ (MUpd E E' P).
  Proof.
    i. rewrite (MUpd_mask_frame_r _ _ (mset_minus E E1)).
    rewrite MUpd_trans. eapply MUpd_permutation; eauto.
    eapply mset_minus_add_eq. auto.
  Qed.

  Lemma MUpd_or E1 E2 P Q :
    (MUpd E1 E2 P ∨ MUpd E1 E2 Q)
      ⊢
      (MUpd E1 E2 (P ∨ Q)).
  Proof. apply Or_elim; apply MUpd_mono; [ apply Or_intro_l | apply Or_intro_r ]. Qed.

  Global Instance MUpd_or_homomorphism E :
    MonoidHomomorphism bi_or bi_or (flip (⊢)) (MUpd E E).
  Proof. split; [split|]; try apply _; [apply MUpd_or | apply MUpd_intro]. Qed.

  Lemma MUpd_and E1 E2 P Q :
    (MUpd E1 E2 (P ∧ Q)) ⊢ (MUpd E1 E2 P) ∧ (MUpd E1 E2 Q).
  Proof. apply And_intro; apply MUpd_mono; [apply And_elim_l | apply And_elim_r]. Qed.

  Lemma MUpd_exist E1 E2 A (Φ : A → iProp) : (∃ x : A, MUpd E1 E2 (Φ x)) ⊢ MUpd E1 E2 (∃ x : A, Φ x).
  Proof.
    iIntros "[% H]". iApply (MUpd_mono with "H"). apply Ex_intro.
  Qed.

  Lemma MUpd_forall E1 E2 A (Φ : A → iProp) : (MUpd E1 E2 (∀ x : A, Φ x)) ⊢ ∀ x : A, MUpd E1 E2 (Φ x).
  Proof.
    iIntros "H %". iApply (MUpd_mono with "H"). apply Univ_elim.
  Qed.

  Lemma MUpd_sep E P Q : (MUpd E E P) ∗ (MUpd E E Q) ⊢ MUpd E E (P ∗ Q).
  Proof. rewrite MUpd_frame_r. rewrite MUpd_frame_l. rewrite MUpd_trans. auto. Qed.

  Global Instance MUpd_sep_homomorphism E :
    MonoidHomomorphism bi_sep bi_sep (flip (⊢)) (MUpd E E).
  Proof. split; [split|]; try apply _; [apply MUpd_sep | apply MUpd_intro]. Qed.

  Lemma MUpd_mask_subseteq_emptyset_difference E1 E2 :
    mset_sub E2 E1 ->
    ⊢ MUpd E1 E2 (MUpd [] (mset_minus E1 E2) emp).
  Proof.
    i. iStartProof. iStopProof. etrans.
    { eapply MUpd_mask_intro_subseteq.
      instantiate (1:=mset_minus E1 E2). instantiate (1:=[]).
      rr in H. rr. des.
      exists s. rewrite app_nil_r. rewrite <- H.
      eapply Permutation_app_inv_l. rewrite <- mset_minus_add_eq.
      { apply Permutation_app_comm. }
      { exists s. auto. }
    }
    etrans.
    { eapply MUpd_mask_frame_r. }
    eapply MUpd_permutation.
    { instantiate (1:=E2). rewrite Permutation_app_comm. eapply mset_minus_add_eq. auto. }
    { ss. }
  Qed.

  (* Lemma MUpd_mask_frame_acc E E' E1 E2 P Q : *)
  (*   mset_sub E1 E -> *)
  (*   (MUpd E1 (mset_minus E1 E2) Q) *)
  (*     -∗ *)
  (*     (Q -∗ MUpd (mset_minus E E2) E' (∀ R, MUpd (mset_minus E1 E2) E1 R -∗ MUpd (mset_minus E E2) E R) -∗ P) *)
  (*     -∗ *)
  (*     (MUpd E E' P). *)
  (* Proof. *)
  (*   intros HE. apply Wand_intro_r. rewrite MUpd_frame_r. *)
  (*   rewrite wand_elim_r. clear Q. *)
  (*   iIntros "H0". *)
  (*   rewrite - (MUpd_mask_frame E E'). *)
  (*   ; first apply fupd_mono; last done. *)
  (*   (* The most horrible way to apply fupd_intro_mask *) *)
  (*   rewrite -[X in (X -∗ _)](right_id emp%I). *)
  (*   rewrite (fupd_mask_intro_subseteq (E1 ∖ E2 ∪ E ∖ E1) (E ∖ E2) emp%I); last first. *)
  (*   { rewrite {1}(union_difference_L _ _ HE). set_solver. } *)
  (*   rewrite fupd_frame_l fupd_frame_r. apply fupd_elim. *)
  (*   apply fupd_mono. *)
  (*   eapply wand_apply; *)
  (*     last (apply sep_mono; first reflexivity); first reflexivity. *)
  (*   apply forall_intro=>R. apply wand_intro_r. *)
  (*   rewrite fupd_frame_r. apply fupd_elim. rewrite left_id. *)
  (*   rewrite (fupd_mask_frame_r _ _ (E ∖ E1)); last set_solver+. *)
  (*   rewrite {4}(union_difference_L _ _ HE). done. *)
  (* Qed. *)

  Lemma BUpd_MUpd E P:
    #=> P ⊢ MUpd E E P.
  Proof.
    iIntros "H0 H1". iMod "H0". iModIntro. iFrame.
  Qed.

  Global Instance from_assumption_MUpd
         E p P Q :
    FromAssumption p P (#=> Q) → KnownRFromAssumption p P (MUpd E E Q).
  Proof. rewrite /KnownRFromAssumption /FromAssumption=>->. apply BUpd_MUpd. Qed.

  Global Instance from_pure_MUpd a E P φ :
    FromPure a P φ → FromPure a (MUpd E E P) φ.
  Proof. rewrite /FromPure=> <-. apply MUpd_intro. Qed.

  Global Instance into_wand_MUpd E p q R P Q :
    IntoWand false false R P Q →
    IntoWand p q (MUpd E E R) (MUpd E E P) (MUpd E E Q).
  Proof.
    rewrite /IntoWand /= => HR. rewrite ! intuitionistically_if_elim.
    rewrite ! HR. apply wand_intro_l. rewrite MUpd_sep. rewrite wand_elim_r. auto.
  Qed.

  Global Instance into_wand_MUpd_persistent E1 E2 p q R P Q :
    IntoWand false q R P Q → IntoWand p q (MUpd E1 E2 R) P (MUpd E1 E2 Q).
  Proof.
    rewrite /IntoWand /= => HR. rewrite intuitionistically_if_elim. rewrite HR.
    apply wand_intro_l. rewrite MUpd_frame_l. rewrite wand_elim_r. auto.
  Qed.

  Global Instance into_wand_MUpd_args E1 E2 p q R P Q :
    IntoWand p false R P Q → IntoWand' p q R (MUpd E1 E2 P) (MUpd E1 E2 Q).
  Proof.
    rewrite /IntoWand' /IntoWand /= => ->.
    apply wand_intro_l. rewrite intuitionistically_if_elim. rewrite MUpd_wand_r. auto.
  Qed.

  Global Instance from_sep_MUpd E P Q1 Q2 :
    FromSep P Q1 Q2 → FromSep (MUpd E E P) (MUpd E E Q1) (MUpd E E Q2).
  Proof. rewrite /FromSep =><-. apply MUpd_sep. Qed.

  Global Instance from_or_MUpd E1 E2 P Q1 Q2 :
    FromOr P Q1 Q2 → FromOr (MUpd E1 E2 P) (MUpd E1 E2 Q1) (MUpd E1 E2 Q2).
  Proof. rewrite /FromOr=><-. apply MUpd_or. Qed.

  Global Instance into_and_MUpd E1 E2 P Q1 Q2 :
    IntoAnd false P Q1 Q2 → IntoAnd false (MUpd E1 E2 P) (MUpd E1 E2 Q1) (MUpd E1 E2 Q2).
  Proof. rewrite /IntoAnd/==>->. apply MUpd_and. Qed.

  Global Instance from_exist_MUpd {A} E1 E2 P (Φ : A → iProp) :
    FromExist P Φ → FromExist (MUpd E1 E2 P) (λ a, MUpd E1 E2 (Φ a))%I.
  Proof. rewrite /FromExist=><-. apply MUpd_exist. Qed.

  Global Instance into_forall_MUpd {A} E1 E2 P (Φ : A → iProp) :
    IntoForall P Φ → IntoForall (MUpd E1 E2 P) (λ a, MUpd E1 E2 (Φ a))%I.
  Proof. rewrite /IntoForall=>->. apply MUpd_forall. Qed.

  Global Instance from_modal_MUpd E P :
    FromModal True modality_id (MUpd E E P) (MUpd E E P) P.
  Proof. by rewrite /FromModal /= -MUpd_intro. Qed.

  Global Instance from_modal_MUpd_wrong_mask E1 E2 P :
    FromModal
      (pm_error "Only non-mask-changing update modalities can be introduced directly.
Use [iApply MUpd_mask_intro] to introduce mask-changing update modalities")
      modality_id (MUpd E1 E2 P) (MUpd E1 E2 P) P | 100.
  Proof. by intros []. Qed.

  Global Instance elim_modal_bupd_MUpd
         p E1 E2 P Q :
    ElimModal True p false (|==> P) P (MUpd E1 E2 Q) (MUpd E1 E2 Q) | 10.
  Proof.
    unfold ElimModal. rewrite intuitionistically_if_elim.
    rewrite (BUpd_MUpd E1). rewrite MUpd_frame_r. rewrite wand_elim_r. rewrite MUpd_trans. auto.
  Qed.

  Global Instance elim_modal_MUpd_MUpd_gen p E0 E1 E2 E3 P Q :
    ElimModal (mset_sub E0 E2) p false (MUpd E0 E1 P) P (MUpd E2 E3 Q) (MUpd (E1 ++ mset_minus E2 E0) E3 Q).
  Proof.
    unfold ElimModal. i. rewrite intuitionistically_if_elim.
    rewrite MUpd_frame_r. rewrite wand_elim_r. rewrite MUpd_mask_frame; eauto.
  Qed.

  Global Instance elim_modal_MUpd_MUpd p E1 E2 E3 P Q :
    ElimModal True p false (MUpd E1 E2 P) P (MUpd E1 E3 Q) (MUpd E2 E3 Q).
  Proof.
    unfold ElimModal. rewrite intuitionistically_if_elim.
    rewrite MUpd_frame_r. rewrite wand_elim_r. rewrite MUpd_trans. auto.
  Qed.

  Global Instance elim_modal_MUpd_MUpd_wrong_mask p E0 E1 E2 E3 P Q :
    ElimModal
      (pm_error "Goal and eliminated modality must have the same mask.
Use [iMod (MUpd_mask_subseteq E2)] to adjust the mask of your goal to [E2]")
      p false
      (MUpd E1 E2 P) False (MUpd E0 E3 Q) False | 100.
  Proof. intros []. Qed.

  Global Instance add_modal_MUpd E1 E2 P Q :
    AddModal (MUpd E1 E1 P) P (MUpd E1 E2 Q).
  Proof.
    unfold AddModal. rewrite MUpd_frame_r. rewrite wand_elim_r. rewrite MUpd_trans. auto.
  Qed.

  Global Instance elim_acc_MUpd {X} E1 E2 E α β mγ Q :
    ElimAcc (X:=X) True (MUpd E1 E2) (MUpd E2 E1) α β mγ
            (MUpd E1 E Q)
            (λ x, MUpd E2 E2 (β x) ∗ (mγ x -∗? MUpd E1 E Q))%I.
  Proof.
    iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iPoseProof ("Hinner" with "Hα") as "[> Hβ Hfin]".
    iMod ("Hclose" with "Hβ") as "Hγ". by iApply "Hfin".
  Qed.

  Global Instance elim_modal_iupd_MUpd
         p E1 E2 P Q :
    ElimModal True p false (IUpd IA P) P (MUpd E1 E2 Q) (MUpd E1 E2 Q) | 10.
  Proof.
    unfold ElimModal. rewrite intuitionistically_if_elim.
    i. iIntros "[H0 H1] [H2 H3]".
    iPoseProof ("H0" with "H2") as "> [H2 H0]".
    iApply ("H1" with "H0 [H2 H3]"). iFrame.
  Qed.
End MUPD.

Ltac msubtac :=
  try by (ss; apply mset_sub_b_reflect; ss).

#[export] Hint Unfold NatSort.sort: mset.
Ltac msimpl := autounfold with mset; simpl.

Lemma injective_map_NoDup_strong A B (f: A -> B) (l: list A)
      (INJ: forall a0 a1 (IN0: List.In a0 l) (IN1: List.In a1 l)
                   (EQ: f a0 = f a1), a0 = a1)
      (ND: List.NoDup l)
  :
  List.NoDup (List.map f l).
Proof.
  revert INJ ND. induction l.
  { i. s. econs. }
  i. inv ND. ss. econs; eauto.
  ii. rewrite in_map_iff in H. des.
  hexploit (INJ x a); eauto. i. subst. ss.
Qed.

Ltac iopen i H K :=
  let str := constr:(String.append "[" (String.append H (String.append " " (String.append K "]")))) in
  let Inv := fresh "I" in
  evar (Inv: nat -> iProp);
  ((iPoseProof (@MUpd_open _ Inv _ i) as "> _H";
    [msubtac|
      let x := (eval cbn in (Inv i)) in
      change (Inv i) with x;
      subst Inv;
      msimpl;
      iDestruct "_H" as str])
   +
     (iPoseProof (@MUpd_open _ Inv _ i) as "> _H";
      [let x := (eval cbn in (Inv i)) in
       change (Inv i) with x;
       subst Inv;
       msimpl;
       iDestruct "_H" as str])).


Section UPDATING.
  Context `{Σ: @GRA.t}.

  Definition updating (I: iProp) (P Q R: iProp): iProp :=
    I -* (#=> (P ** (Q -* #=> (I ** R)))).

  Lemma updating_sub_mon (I0 I1: iProp) (P Q R: iProp)
    :
    (SubIProp I0 I1)
      -∗
      (updating I0 P Q R)
      -∗
      (updating I1 P Q R).
  Proof.
    iIntros "SUB UPD INV".
    iPoseProof ("SUB" with "INV") as "> [INV K]".
    iPoseProof ("UPD" with "INV") as "> [INV FIN]".
    iFrame. iModIntro. iIntros "H".
    iPoseProof ("FIN" with "H") as "> [INV H]".
    iPoseProof ("K" with "INV") as "> INV".
    iModIntro. iFrame.
  Qed.
End UPDATING.



Require Import Program.

Module OneShot.
  Section ONESHOT.
    Variable A: Type.

    Definition oneshot_add (a0 a1: bool + (Qp + A)): bool + (Qp + A) :=
      match a0, a1 with
      | inl false, a
      | a, inl false => a
      | inr (inr a0), inr (inr a1) => if (excluded_middle_informative (a0 = a1)) then inr (inr a0) else inl true
      | inr (inl q0), inr (inl q1) => inr (inl (q0 + q1)%Qp)
      | _, _ => inl true
      end.

    Definition oneshot_core (a: bool + (Qp + A)): bool + (Qp + A) :=
      match a with
      | inr (inl _) => inl false
      | _ => a
      end.

    Program Instance t: URA.t := {
        car := bool + (Qp + A);
        unit := inl false;
        _add := oneshot_add;
        _wf := fun a =>
                 match a with
                 | inl true => False
                 | inr (inl q) => (q ≤ 1)%Qp
                 | _ => True
                 end;
        core := oneshot_core;
      }
    .
    Next Obligation.
      unfold oneshot_add. des_ifs. f_equal. f_equal. eapply Qp.add_comm.
    Qed.
    Next Obligation.
      unfold oneshot_add. des_ifs. f_equal. f_equal. eapply Qp.add_assoc.
    Qed.
    Next Obligation.
      unseal "ra". unfold oneshot_add. des_ifs.
    Qed.
    Next Obligation.
      unseal "ra". ss.
    Qed.
    Next Obligation.
      unseal "ra". unfold oneshot_add in *. des_ifs.
      etrans; [|eauto]. apply Qp.le_add_l.
    Qed.
    Next Obligation.
      unseal "ra". unfold oneshot_add, oneshot_core. des_ifs.
    Qed.
    Next Obligation.
      unfold oneshot_add, oneshot_core. des_ifs.
    Qed.
    Next Obligation.
      unseal "ra".
      pose (c := oneshot_core b).
      unfold oneshot_core, oneshot_add. des_ifs; subst; try by (exists c; ss).
      { exists (inl true). ss. }
      { exists (inl true). ss. }
      { exists (inl true). ss. }
      { exists (inl true). ss. }
      { exists (inr (inr a0)). des_ifs. }
    Qed.

    Definition pending (q: Qp): t := inr (inl q).
    Definition shot (a: A): t := inr (inr a).

    Lemma pending_one_wf: URA.wf (pending 1).
    Proof.
      ur. ss.
    Qed.

    Lemma shot_wf a: URA.wf (shot a).
    Proof.
      ur. ss.
    Qed.

    Lemma shot_agree a0 a1
          (WF: URA.wf (shot a0 ⋅ shot a1))
      :
      a0 = a1.
    Proof.
      ur in WF. des_ifs.
    Qed.

    Lemma pending_not_shot a q
          (WF: URA.wf (pending q ⋅ shot a))
      :
      False.
    Proof.
      ur in WF. ss.
    Qed.

    Lemma pending_wf q
          (WF: URA.wf (pending q))
      :
      (q ≤ 1)%Qp.
    Proof.
      ur in WF. ss.
    Qed.

    Lemma pending_sum q0 q1
      :
      pending (q0 + q1)%Qp = pending q0 ⋅ pending q1.
    Proof.
      ur. ss.
    Qed.

    Lemma pending_shot a
      :
      URA.updatable (pending 1) (shot a).
    Proof.
      ii. ur in H. ur. des_ifs.
      apply Qp.not_add_le_l in H; auto.
    Qed.
  End ONESHOT.
End OneShot.

Module OneShotP.
  Global Program Instance shot_persistent (A: Type)
         `{@GRA.inG (OneShot.t A) Σ}
         (a: A)
    :
    Persistent (OwnM (OneShot.shot a)).
  Next Obligation.
    i. iIntros "H". iPoseProof (own_persistent with "H") as "# G". ss.
  Qed.

  Lemma shot_agree (A: Type)
        `{@GRA.inG (OneShot.t A) Σ}
        (a0 a1: A)
    :
    (OwnM (OneShot.shot a0) ∧ (OwnM (OneShot.shot a1)))
      -∗
      (⌜a0 = a1⌝).
  Proof.
    iIntros "[# H0 # H1]".
    iCombine "H0 H1" as "H". iOwnWf "H". apply OneShot.shot_agree in H0. auto.
  Qed.

  Lemma pending_not_shot (A: Type)
        `{@GRA.inG (OneShot.t A) Σ}
        (a: A) q
    :
    (OwnM (OneShot.pending A q) ∧ (OwnM (OneShot.shot a)))
      -∗
      False.
  Proof.
    iIntros "[H0 # H1]".
    iCombine "H0 H1" as "H". iOwnWf "H". apply OneShot.pending_not_shot in H0. auto.
  Qed.

  Global Program Instance shot_persistent_singleton (A: Type)
         `{@GRA.inG (@FiniteMap.t (OneShot.t A)) Σ}
         k (a: A)
    :
    Persistent (OwnM (FiniteMap.singleton k (OneShot.shot a))).
  Next Obligation.
    i. iIntros "H". iPoseProof (own_persistent with "H") as "# G".
    rewrite FiniteMap.singleton_core_total. ss.
  Qed.

  Lemma shot_agree_singleton (A: Type)
        `{@GRA.inG (@FiniteMap.t (OneShot.t A)) Σ}
        k (a0 a1: A)
    :
    (OwnM (FiniteMap.singleton k (OneShot.shot a0)) ∧ (OwnM (FiniteMap.singleton k (OneShot.shot a1))))
      -∗
      (⌜a0 = a1⌝).
  Proof.
    iIntros "[# H0 # H1]".
    iCombine "H0 H1" as "H". iOwnWf "H".
    rewrite FiniteMap.singleton_add in H0. apply FiniteMap.singleton_wf in H0.
    apply OneShot.shot_agree in H0. auto.
  Qed.

  Lemma pending_not_shot_singleton (A: Type)
        `{@GRA.inG (@FiniteMap.t (OneShot.t A)) Σ}
        k (a: A) q
    :
    (OwnM (FiniteMap.singleton k (OneShot.pending A q)) ∧ (OwnM (FiniteMap.singleton k (OneShot.shot a))))
      -∗
      False.
  Proof.
    iIntros "[H0 # H1]".
    iCombine "H0 H1" as "H". iOwnWf "H".
    rewrite FiniteMap.singleton_add in H0. apply FiniteMap.singleton_wf in H0.
    apply OneShot.pending_not_shot in H0. auto.
  Qed.
End OneShotP.



Module Frac.
  Program Instance t: URA.t := {
      car := option Qp;
      unit := None;
      _add := fun q0 q1 =>
                match q0, q1 with
                | Some q0, Some q1 => Some (q0 + q1)%Qp
                | None, _ => q1
                | _, None => q0
                end;
      _wf := fun q =>
               match q with
               | None => True
               | Some q => (q ≤ 1)%Qp
               end;
      core := fun _ => None;
    }
  .
  Next Obligation.
    des_ifs. f_equal. eapply Qp.add_comm.
  Qed.
  Next Obligation.
    des_ifs. f_equal. eapply Qp.add_assoc.
  Qed.
  Next Obligation.
    unseal "ra". des_ifs.
  Qed.
  Next Obligation.
    unseal "ra". ss.
  Qed.
  Next Obligation.
    unseal "ra". des_ifs.
    etrans; [|eauto]. apply Qp.le_add_l.
  Qed.
  Next Obligation.
    unseal "ra". auto.
  Qed.
  Next Obligation.
    exists None. unseal "ra". auto.
  Qed.
End Frac.


Module Consent.
  Section CONSENT.
    Variable A: Type.
    Definition car: Type := bool + (Qp * A).

    Definition consent_add (a0 a1: car): car :=
      match a0, a1 with
      | inl false, a
      | a, inl false => a
      | inr (q0, a0), inr (q1, a1) =>
          if (excluded_middle_informative (a0 = a1)) then inr ((q0 + q1)%Qp, a0) else inl true
      | _, _ => inl true
      end.

    Program Instance t: URA.t := {
        car := car;
        unit := inl false;
        _add := consent_add;
        _wf := fun a =>
                 match a with
                 | inl true => False
                 | inr (q, a) => (q ≤ 1)%Qp
                 | _ => True
                 end;
        core := fun _ => inl false;
      }
    .
    Next Obligation.
      unfold consent_add. des_ifs. f_equal. f_equal. eapply Qp.add_comm.
    Qed.
    Next Obligation.
      unfold consent_add. des_ifs. f_equal. f_equal. eapply Qp.add_assoc.
    Qed.
    Next Obligation.
      unseal "ra". unfold consent_add. des_ifs.
    Qed.
    Next Obligation.
      unseal "ra". ss.
    Qed.
    Next Obligation.
      unseal "ra". unfold consent_add in *. des_ifs.
      etrans; [|eauto]. apply Qp.le_add_l.
    Qed.
    Next Obligation.
      unseal "ra". unfold consent_add. auto.
    Qed.
    Next Obligation.
      unseal "ra". unfold consent_add. exists (inl false). auto.
    Qed.

    Definition vote (a: A) (q: Qp): t := inr (q, a).

    Lemma vote_one_wf a: URA.wf (vote a 1%Qp).
    Proof.
      ur. ss.
    Qed.

    Lemma vote_agree a0 q0 a1 q1
          (WF: URA.wf (vote a0 q0 ⋅ vote a1 q1))
      :
      a0 = a1 /\ (q0 + q1 ≤ 1)%Qp.
    Proof.
      ur in WF. des_ifs.
    Qed.

    Lemma vote_wf a q
          (WF: URA.wf (vote a q))
      :
      (q ≤ 1)%Qp.
    Proof.
      ur in WF. ss.
    Qed.

    Lemma vote_sum a q0 q1
      :
      vote a (q0 + q1)%Qp = vote a q0 ⋅ vote a q1.
    Proof.
      ur. des_ifs.
    Qed.

    Lemma vote_revolution a0 a1
      :
      URA.updatable (vote a0 1%Qp) (vote a1 1%Qp).
    Proof.
      unfold vote. ii. ur in H. ur. des_ifs.
      apply Qp.not_add_le_l in H; auto.
    Qed.
  End CONSENT.
End Consent.

Module ConsentP.
  Lemma vote_agree (A: Type)
        `{@GRA.inG (Consent.t A) Σ}
        (a0 a1: A) q0 q1
    :
    (OwnM (Consent.vote a0 q0) ** (OwnM (Consent.vote a1 q1)))
      -∗
      (⌜a0 = a1⌝).
  Proof.
    iIntros "[H0 H1]".
    iCombine "H0 H1" as "H". iOwnWf "H". apply Consent.vote_agree in H0. des. auto.
  Qed.

  Definition voted (A: Type)
             `{@GRA.inG (Consent.t A) Σ}
             (a: A): iProp :=
    ∃ q, OwnM (Consent.vote a q).

  Lemma voted_agree (A: Type)
        `{@GRA.inG (Consent.t A) Σ}
        (a0 a1: A)
    :
    (voted a0 ** voted a1)
      -∗
      (⌜a0 = a1⌝).
  Proof.
    iIntros "[[% H0] [% H1]]". iApply vote_agree. iFrame.
  Qed.

  Lemma voted_duplicable (A: Type)
        `{@GRA.inG (Consent.t A) Σ}
        (a: A)
    :
    (voted a)
      -∗
      (voted a ** voted a).
  Proof.
    iIntros "[% H]". erewrite <- (Qp.div_2 q).
    rewrite Consent.vote_sum.
    iDestruct "H" as "[H0 H1]". iSplitL "H0".
    { iExists _. iFrame. }
    { iExists _. iFrame. }
  Qed.

  Definition voted_singleton (A: Type)
             `{@GRA.inG (@FiniteMap.t (Consent.t A)) Σ}
             k (a: A): iProp :=
    ∃ q, OwnM (FiniteMap.singleton k (Consent.vote a q)).

  Lemma voted_agree_singleton (A: Type)
        `{@GRA.inG (@FiniteMap.t (Consent.t A)) Σ}
        k (a0 a1: A)
    :
    (voted_singleton k a0 ** voted_singleton k a1)
      -∗
      (⌜a0 = a1⌝).
  Proof.
    iIntros "[[% H0] [% H1]]".
    iCombine "H0 H1" as "H". iOwnWf "H".
    rewrite FiniteMap.singleton_add in H0. apply FiniteMap.singleton_wf in H0.
    apply Consent.vote_agree in H0. des. auto.
  Qed.

  Lemma voted_duplicable_singleton (A: Type)
        `{@GRA.inG (@FiniteMap.t (Consent.t A)) Σ}
        k (a: A)
    :
    (voted_singleton k a)
      -∗
      (voted_singleton k a ** voted_singleton k a).
  Proof.
    iIntros "[% H]". erewrite <- (Qp.div_2 q).
    rewrite Consent.vote_sum.
    rewrite <- FiniteMap.singleton_add.
    iDestruct "H" as "[H0 H1]". iSplitL "H0".
    { iExists _. iFrame. }
    { iExists _. iFrame. }
  Qed.
End ConsentP.


Module Region.
  Section REGION.
    Variable A: Type.
    Definition t: URA.t := URA.pointwise nat (OneShot.t A).

    Context `{@GRA.inG t Σ}.

    Definition black (l: list A): iProp :=
      OwnM ((fun n =>
               match nth_error l n with
               | Some a => OneShot.shot a
               | _ => OneShot.pending A 1%Qp
               end): (nat ==> OneShot.t A)%ra).

    Definition white (k: nat) (a: A): iProp :=
      OwnM ((fun n =>
               if Nat.eq_dec n k then OneShot.shot a else ε): (nat ==> OneShot.t A)%ra).

    Global Program Instance Persistent_white k a: Persistent (white k a).
    Next Obligation.
      iIntros "H". iPoseProof (own_persistent with "H") as "# X".
      replace (URA.core
                 ((fun n =>
                     if Nat.eq_dec n k then OneShot.shot a else ε): (nat ==> OneShot.t A)%ra)) with
        ((fun n =>
            if Nat.eq_dec n k then OneShot.shot a else ε): (nat ==> OneShot.t A)%ra).
      2:{ ur. f_equal. extensionality n. des_ifs. }
      auto.
    Qed.

    Lemma black_white_in k a l
      :
      (black l)
        -∗
        (white k a)
        -∗
        ⌜nth_error l k = Some a⌝.
    Proof.
      iIntros "BLACK WHITE".
      iCombine "BLACK WHITE" as "OWN". iOwnWf "OWN". iPureIntro.
      ur in H0. specialize (H0 k). ur in H0. des_ifs; ss.
      { des_ifs. }
      { des_ifs. }
      { des_ifs. }
    Qed.

    Lemma white_agree k a0 a1
      :
        (white k a0)
        -∗
        (white k a1)
        -∗
        ⌜a0 = a1⌝.
    Proof.
      iIntros "WHITE0 WHITE1".
      iCombine "WHITE0 WHITE1" as "OWN". iOwnWf "OWN". iPureIntro.
      ur in H0. specialize (H0 k). des_ifs.
      apply OneShot.shot_agree in H0. auto.
    Qed.

    Lemma black_alloc l a
      :
      (black l)
        -∗
        #=> (black (l++[a]) ** white (length l) a).
    Proof.
      iIntros "H". iPoseProof (OwnM_Upd with "H") as "> [BLACK WHITE]".
      2:{ iModIntro. iSplitL "BLACK"; [iApply "BLACK"|iApply "WHITE"]. }
      eapply pointwise_updatable. i.
      rewrite ! (@unfold_pointwise_add nat (OneShot.t A)).
      destruct (nth_error l a0) eqn:EQ.
      { rewrite nth_error_app1.
        2:{ apply nth_error_Some; auto. rewrite EQ; auto. }
        rewrite EQ. des_ifs; ss.
        { exploit nth_error_Some.
          rewrite EQ. i. des. hexploit x0; auto. i. lia.
        }
        { ur. reflexivity. }
      }
      { dup EQ. eapply nth_error_None in EQ. rewrite nth_error_app2; auto.
        destruct (Nat.eq_dec a0 (length l)).
        { subst. replace (length l - length l) with 0 by lia. ss. etrans.
          { eapply OneShot.pending_shot. }
          { instantiate (1:=a). ur. des_ifs. }
        }
        { hexploit nth_error_None. i. des.
          hexploit H1.
          2:{ i. rewrite H2. rewrite URA.unit_id. reflexivity. }
          { ss. lia. }
        }
      }
    Qed.

    Variable interp: A -> iProp.

    Definition sat_list (l: list A) := fold_right (fun a P => interp a ** P) True%I l.

    Lemma sat_list_nil
      :
      ⊢ sat_list [].
    Proof.
      unfold sat_list. ss. auto.
    Qed.

    Lemma sat_list_cons_fold hd tl
      :
      (interp hd ** sat_list tl)
        -∗
        (sat_list (hd::tl)).
    Proof.
      unfold sat_list. ss.
    Qed.

    Lemma sat_list_cons_unfold hd tl
      :
      (sat_list (hd::tl))
        -∗
        (interp hd ** sat_list tl).
    Proof.
      unfold sat_list. ss.
    Qed.

    Lemma sat_list_split l0 l1
      :
      (sat_list (l0 ++ l1))
        -∗
        (sat_list l0 ** sat_list l1).
    Proof.
      induction l0; ss.
      { iIntros "SAT". iFrame. }
      { iIntros "[INTERP SAT]". iFrame. iApply IHl0; auto. }
    Qed.

    Lemma sat_list_combine l0 l1
      :
      (sat_list l0 ** sat_list l1)
        -∗
        (sat_list (l0 ++ l1)).
    Proof.
      induction l0; ss.
      { iIntros "[_ SAT]". auto. }
      { iIntros "[[INTERP SAT0] SAT1]". iFrame.
        iApply IHl0. iFrame.
      }
    Qed.

    Lemma sat_list_add l a
      :
      (interp a ** sat_list l)
        -∗
        (sat_list (l++[a])).
    Proof.
      iIntros "[NEW SAT]". iApply sat_list_combine. iFrame.
    Qed.

    Lemma sat_list_permutation l0 l1
          (PERM: Permutation l0 l1)
      :
      sat_list l0 ⊢ sat_list l1.
    Proof.
      induction PERM.
      { auto. }
      { iIntros "H". iApply sat_list_cons_fold.
        iPoseProof (sat_list_cons_unfold with "H") as "[HD TL]".
        iFrame. iApply IHPERM; auto.
      }
      { iIntros "H". iApply sat_list_cons_fold.
        iPoseProof (sat_list_cons_unfold with "H") as "[HD0 TL]".
        iPoseProof (sat_list_cons_unfold with "TL") as "[HD1 TL]".
        iSplitL "HD1"; auto. iApply sat_list_cons_fold. iFrame.
      }
      { etrans; eauto. }
    Qed.

    Lemma sat_list_update l k a
          (FIND: nth_error l k = Some a)
      :
      sat_list l ⊢ interp a ** (interp a -* sat_list l).
    Proof.
      hexploit nth_error_split; eauto. i. des. subst.
      iIntros "SAT". iPoseProof (sat_list_split with "SAT") as "[SAT0 SAT1]".
      iPoseProof (sat_list_cons_unfold with "SAT1") as "[OLD SAT1]".
      iFrame. iIntros "NEW". iApply sat_list_combine. iFrame.
    Qed.

    Lemma sat_list_nth_sub l k a
          (FIND: nth_error l k = Some a)
      :
      ⊢ SubIProp (interp a) (sat_list l).
    Proof.
      iIntros "H". iPoseProof (sat_list_update with "H") as "[H0 H1]"; eauto.
      iFrame. iModIntro. iIntros "H". iModIntro. iApply ("H1" with "H").
    Qed.

    Lemma sat_list_sub_update l0 l1
          (SUB: list_sub l0 l1)
      :
      sat_list l1 ⊢ sat_list l0 ** (sat_list l0 -* sat_list l1).
    Proof.
      rr in SUB. des.
      iIntros "H". iPoseProof (sat_list_permutation with "H") as "H".
      { symmetry. eassumption. }
      iPoseProof (sat_list_split with "H") as "[H0 H1]". iFrame.
      iIntros "H1". iPoseProof (sat_list_combine with "[H0 H1]") as "H".
      { iSplitL "H0"; eauto. }
      iApply (sat_list_permutation with "H"). auto.
    Qed.

    Lemma sat_list_sub_sub l0 l1
          (SUB: list_sub l0 l1)
      :
      ⊢ SubIProp (sat_list l0) (sat_list l1).
    Proof.
      iIntros "H". iPoseProof (sat_list_sub_update with "H") as "[H0 H1]"; eauto.
      iFrame. iModIntro. iIntros "H". iModIntro. iApply ("H1" with "H").
    Qed.

    Definition sat: iProp := ∃ l, black l ** sat_list l.

    Lemma white_agree_sat k a0 a1
      :
      (white k a0)
        -∗
        (white k a1)
        -∗
        (⌜a0 = a1⌝).
    Proof.
      iIntros "WHITE0 WHITE1".
      iPoseProof (white_agree with "WHITE0 WHITE1") as "%".
      subst. auto.
    Qed.

    Lemma sat_update k a
      :
      (white k a)
        -∗
        (sat)
        -∗
        (interp a ** (interp a -* sat)).
    Proof.
      iIntros "WHITE [% [BLACK SAT]]".
      iPoseProof (black_white_in with "BLACK WHITE") as "%".
      iPoseProof (sat_list_update with "SAT") as "[INTERP H0]"; eauto.
      iFrame. iIntros "H1". iExists _. iFrame. iApply ("H0" with "H1").
    Qed.

    Lemma sat_white_sub k a
      :
      white k a ⊢ SubIProp (interp a) sat.
    Proof.
      iIntros "H0 H1". iPoseProof (sat_update with "H0 H1") as "[H0 H1]".
      iFrame. iModIntro. iIntros "H". iModIntro. iApply ("H1" with "H").
    Qed.

    Lemma black_whites_in l ks
          (ND: List.NoDup (List.map fst ks))
      :
      (black l)
        -∗
        (∀ k a (IN: List.In (k, a) ks), white k a)
        -∗
        ⌜list_sub (List.map snd ks) l⌝.
    Proof.
      iIntros "BLACK WHITES".
      iAssert (⌜forall k a (IN: List.In (k, a) ks), nth_error l k = Some a⌝)%I as "%INS".
      { iStopProof. clear ND. induction ks; ss.
        { iIntros. ss. }
        { destruct a as [k a]. iIntros "[BLACK ALL] % % %".
          des; clarify.
          { iApply (black_white_in with "BLACK [ALL]"); eauto. iApply "ALL". auto. }
          { iPoseProof (IHks with "[BLACK ALL]") as "%".
            { iFrame. iIntros. iApply "ALL". auto. }
            iPureIntro. eauto.
          }
        }
      }
      iPureIntro.
      remember (length ks) as n. revert ks l Heqn ND INS.
      induction n; ss.
      { i. destruct ks; ss. exists l. rewrite app_nil_r. ss. }
      i. destruct ks as [|[k0 a0] tl]; ss. inv Heqn. inv ND.
      hexploit (INS k0 a0); eauto. i.
      hexploit nth_error_split; eauto. i. des. subst.
      hexploit (IHn (List.map (fun ka => (if le_lt_dec (fst ka) (length l1) then (fst ka) else (fst ka - 1), snd ka)) tl) (l1++l2)).
      { rewrite map_length. auto. }
      { rewrite map_map. ss.
        match goal with
        | |- _ (map ?f tl) => replace (map f tl) with (map (fun k => (if le_lt_dec k (length l1) then k else (k - 1))) (map fst tl))
        end.
        { eapply injective_map_NoDup_strong; auto. i. des_ifs.
          { exfalso. eapply H2. replace (length l1) with (a2 - 1) by lia; ss. }
          { exfalso. eapply H2. replace (length l1) with (a1 - 1) by lia; ss. }
          { lia. }
        }
        rewrite map_map. auto.
      }
      { i. apply in_map_iff in IN. des.
        destruct x as [k1 a1]. ss. clarify. des_ifs.
        { assert (k1 = length l1 \/ k1 < length l1) by lia. des.
          { subst. eapply in_map with (f:=fst)in IN0. ss. }
          rewrite nth_error_app1; auto.
          hexploit (INS k1 a); auto. i. rewrite nth_error_app1 in H4; auto.
        }
        rewrite nth_error_app2; [|lia].
        hexploit (INS k1 a); auto. i.
        rewrite nth_error_app2 in H1; [|lia].
        replace (k1 - length l1) with (S (k1 - 1 - length l1)) in H1 by lia. ss.
      }
      i. rewrite map_map in H1. ss.
      r in H1. des. exists s.
      rewrite <- Permutation_middle. rewrite <- Permutation_middle.
      econs. auto.
    Qed.

    Lemma sat_sub_update (l: list (nat * A))
          (ND: List.NoDup (List.map fst l))
      :
      (∀ k a (IN: List.In (k, a) l), white k a)
        -∗
        (sat)
        -∗
        (sat_list (List.map snd l)) ** ((sat_list (List.map snd l)) -* sat).
    Proof.
      iIntros "H0 [% [H1 H2]]".
      iPoseProof (black_whites_in with "H1 H0") as "%"; auto.
      iPoseProof (sat_list_sub_update with "H2") as "[H2 H3]".
      { eauto. }
      iFrame. iIntros "H". iPoseProof ("H3" with "H") as "H".
      iExists _. iFrame.
    Qed.

    Lemma sat_whites_sub (l: list (nat * A))
          (ND: List.NoDup (List.map fst l))
      :
      (∀ k a (IN: List.In (k, a) l), white k a)
        ⊢ SubIProp (sat_list (List.map snd l)) sat.
    Proof.
      iIntros "H0 H1". iPoseProof (sat_sub_update with "H0 H1") as "[H0 H1]".
      { auto. }
      iFrame. iModIntro. iIntros "H". iModIntro. iApply ("H1" with "H").
    Qed.

    Lemma sat_alloc a
      :
      sat
        -∗
        (interp a)
        -∗
        ∃ k, (#=> (sat ** white k a)).
    Proof.
      iIntros "[% [BLACK SAT]] INTERP".
      iPoseProof (sat_list_add with "[SAT INTERP]") as "SAT".
      { iFrame. }
      iExists _.
      iPoseProof (black_alloc with "BLACK") as "> [BLACK WHITE]".
      iModIntro. iSplitR "WHITE"; auto.
      iExists _. iFrame.
    Qed.

    Lemma update k a P
      :
      (white k a)
        -∗
        (#=(interp a)=> P)
        -∗
        (#=(sat)=> P).
    Proof.
      iIntros "H0 H1".
      iPoseProof (sat_white_sub with "H0") as "H0".
      iApply (IUpd_sub_mon with "H0 H1").
    Qed.

    Lemma updates (l: list (nat * A)) P
          (ND: List.NoDup (List.map fst l))
      :
      (∀ k a (IN: List.In (k, a) l), white k a)
        -∗
        (#=(sat_list (List.map snd l))=> P)
        -∗
        (#=(sat)=> P).
    Proof.
      iIntros "H0 H1".
      iPoseProof (sat_whites_sub with "H0") as "H0"; auto.
      iApply (IUpd_sub_mon with "H0 H1").
    Qed.

    Lemma sat_updating (l: list (nat * A)) P Q R
          (ND: List.NoDup (List.map fst l))
      :
      (∀ k a (IN: List.In (k, a) l), white k a)
        -∗
        (updating (sat_list (List.map snd l)) P Q R)
        -∗
        (updating sat P Q R).
    Proof.
      iIntros "H0 H1".
      iPoseProof (sat_whites_sub with "H0") as "H0"; auto.
      iApply (updating_sub_mon with "H0 H1").
    Qed.

    Lemma alloc a
      :
      (interp a)
        -∗
        (#=(sat)=> ∃ k, white k a).
    Proof.
      iIntros "H0 H1".
      iPoseProof (sat_alloc with "H1 H0") as "[% > [H0 H1]]".
      iModIntro. iFrame. iExists _. iFrame.
    Qed.
  End REGION.
End Region.

Definition maps_to {Σ} {A: Type} {M: URA.t} `{ING: @GRA.inG (A ==> M)%ra Σ}
           (a: A) (m: M): iProp :=
  OwnM (maps_to_res a m).

From Fairness Require Import NatStructsLarge.

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
    iIntros "Ps". iPoseProof (list_prop_sum_persistent with "Ps") as "Ps". auto.
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
    iIntros "Ps". iPoseProof (natmap_prop_sum_persistent with "Ps") as "Ps". auto.
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
