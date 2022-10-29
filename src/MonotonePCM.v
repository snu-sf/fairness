From sflib Require Import sflib.
From Fairness Require Import PCM IProp IPM.
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

    Lemma singleton_core k m
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
      rewrite FiniteMap.singleton_core. auto.
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


Module Region.
  Section REGION.
    Variable A: Type.
    Definition t: URA.t := monoRA2 (nat -> option A).

    Context `{@GRA.inG t Σ}.

    Definition black (l: list A): iProp :=
      monoBlack2 (@partial_map_le _ _) (nth_error l).

    Definition white (k: nat) (a: A): iProp :=
      monoWhite2 (@partial_map_le _ _) (partial_map_singleton k a).

    Global Program Instance Persistent_white k a: Persistent (white k a).

    Lemma black_white_in k a l
      :
      (black l)
        -∗
        (white k a)
        -∗
        ⌜nth_error l k = Some a⌝.
    Proof.
      iIntros "BLACK WHITE".
      iPoseProof (black_white_compare2 with "WHITE BLACK") as "%".
      apply partial_map_singleton_le_iff in H0. auto.
    Qed.

    Lemma white_agree k a0 a1 l
      :
      (black l)
        -∗
        (white k a0)
        -∗
        (white k a1)
        -∗
        ⌜a0 = a1⌝.
    Proof.
      iIntros "BLACK WHITE0 WHITE1".
      iPoseProof (black_white_in with "BLACK WHITE0") as "%".
      iPoseProof (black_white_in with "BLACK WHITE1") as "%".
      clarify.
    Qed.

    Lemma black_alloc l a
      :
      (black l)
        -∗
        #=> (black (l++[a]) ** white (length l) a).
    Proof.
      iIntros "H". iPoseProof (black_updatable2 with "H") as "> H".
      { instantiate (1:=nth_error (l++[a])). ii.
        rewrite nth_error_app1; eauto.
        apply nth_error_Some; auto. rewrite SOME; auto.
      }
      iModIntro. iSplit; auto.
      iPoseProof (black_white2 with "H") as "H".
      iApply (white_mon2 with "H"); auto. iPureIntro.
      apply partial_map_singleton_le_iff.
      rewrite nth_error_app2; auto.
      replace (length l - length l) with 0 by lia. ss.
    Qed.

    Variable interp: A -> iProp.

    Definition sat_list (l: list A): iProp :=
      fold_right (fun a P => interp a ** P) True%I l.

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

    Definition sat: iProp := ∃ l, black l ** sat_list l.

    Lemma white_agree_sat k a0 a1
      :
      (white k a0)
        -∗
        (white k a1)
        -∗
        (#=(sat)=> (⌜a0 = a1⌝)).
    Proof.
      iIntros "WHITE0 WHITE1 [% [BLACK SAT]]".
      iPoseProof (white_agree with "BLACK WHITE0 WHITE1") as "%".
      subst. iModIntro. iSplit; auto. iExists _. iFrame.
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
