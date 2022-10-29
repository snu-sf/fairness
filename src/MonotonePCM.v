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


From iris.bi Require Import derived_laws. Import bi.

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

  Definition mset_sub (s0 s1: mset): Prop :=
    exists s, Permutation (s ++ s0) s1.

  Global Program Instance mset_sub_PreOrder: PreOrder mset_sub.
  Next Obligation.
  Proof.
    ii. exists []. ss.
  Qed.
  Next Obligation.
  Proof.
    ii. unfold mset_sub in *. des.
    rewrite <- H in H0. exists (s ++ s0).
    rewrite <- app_assoc. auto.
  Qed.

  Definition mset_minus (s0 s1: mset): mset :=
    match list_remove_list s0 s1 with
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
        rewrite <- IHs0. unfold mset_sub. split.
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
        exfalso. unfold mset_sub in H. des.
        rewrite <- Permutation_middle in H.
        eapply EQ. eapply Permutation_in; eauto.
        econs; ss.
      }
    }
  Qed.

  Context `{Σ: GRA.t}.
  Variable I: nat -> iProp.
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
    red in SUB. des. iIntros "H".
    iPoseProof (mset_all_permutation with "H") as "H".
    { symmetry. eauto. }
    iPoseProof (mset_all_split with "H") as "[H0 H1]". iFrame.
    iIntros "H1". iApply mset_all_permutation; eauto.
    iApply mset_all_combine. iFrame.
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

  Definition MUpd (l0 l1: mset) (P: iProp): iProp :=
    mset_all l0 -* #=> (mset_all l1 ** P).

  Lemma MUpd_mask_subseteq E1 E2 :
    mset_sub E2 E1 -> ⊢ MUpd E1 E2 (MUpd E2 E1 emp).
  Proof.
    i. iIntros "H".
    iPoseProof (mset_all_sub with "H") as "[H0 H1]"; eauto.
    iModIntro. iFrame. iIntros "H0". iModIntro. iSplit; auto.
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

  Lemma MUpd_mask_frame_r' E1 E2 Ef P
    :
    (MUpd E1 E2 P ⊢ MUpd (E1 ++ Ef) (E2 ++ Ef) P).
  Proof.
    i. iIntros "H0 H1".
    iPoseProof (mset_all_split with "H1") as "[H1 H2]".
    iPoseProof ("H0" with "H1") as "> [H0 H1]".
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
    rewrite MUpd_frame_r.

assoc -(comm _ Q) wand_elim_r.
    by rewrite fupd_frame_r left_id fupd_trans.
  Qed.

  Lemma fupd_elim E1 E2 E3 P Q :
    (Q -∗ (|={E2,E3}=> P)) → (|={E1,E2}=> Q) -∗ (|={E1,E3}=> P).
  Proof. intros ->. rewrite fupd_trans //. Qed.

  Lemma fupd_mask_frame_r E1 E2 Ef P :
    E1 ## Ef → (|={E1,E2}=> P) ={E1 ∪ Ef,E2 ∪ Ef}=∗ P.
  Proof.
    intros ?. rewrite -fupd_mask_frame_r' //. f_equiv.
    apply impl_intro_l, and_elim_r.
  Qed.
  Lemma fupd_mask_mono E1 E2 P : E1 ⊆ E2 → (|={E1}=> P) ={E2}=∗ P.
  Proof.
    intros (Ef&->&?)%subseteq_disjoint_union_L. by apply fupd_mask_frame_r.
  Qed.
  (** How to apply an arbitrary mask-changing view shift when having
      an arbitrary mask. *)
  Lemma fupd_mask_frame E E' E1 E2 P :
    E1 ⊆ E →
    (|={E1,E2}=> |={E2 ∪ (E ∖ E1),E'}=> P) -∗ (|={E,E'}=> P).
  Proof.
    intros ?. rewrite (fupd_mask_frame_r _ _ (E ∖ E1)); last set_solver.
    rewrite fupd_trans.
    by replace (E1 ∪ E ∖ E1) with E by (by apply union_difference_L).
  Qed.
  (* A variant of [fupd_mask_frame] that works well for accessors: Tailored to
     eliminate updates of the form [|={E1,E1∖E2}=> Q] and provides a way to
     transform the closing view shift instead of letting you prove the same
     side-conditions twice. *)
  Lemma fupd_mask_frame_acc E E' E1(*Eo*) E2(*Em*) P Q :
    E1 ⊆ E →
    (|={E1,E1∖E2}=> Q) -∗
    (Q -∗ |={E∖E2,E'}=> (∀ R, (|={E1∖E2,E1}=> R) -∗ |={E∖E2,E}=> R) -∗  P) -∗
    (|={E,E'}=> P).
  Proof.
    intros HE. apply wand_intro_r. rewrite fupd_frame_r.
    rewrite wand_elim_r. clear Q.
    rewrite -(fupd_mask_frame E E'); first apply fupd_mono; last done.
    (* The most horrible way to apply fupd_intro_mask *)
    rewrite -[X in (X -∗ _)](right_id emp%I).
    rewrite (fupd_mask_intro_subseteq (E1 ∖ E2 ∪ E ∖ E1) (E ∖ E2) emp); last first.
    { rewrite {1}(union_difference_L _ _ HE). set_solver. }
    rewrite fupd_frame_l fupd_frame_r. apply fupd_elim.
    apply fupd_mono.
    eapply wand_apply;
      last (apply sep_mono; first reflexivity); first reflexivity.
    apply forall_intro=>R. apply wand_intro_r.
    rewrite fupd_frame_r. apply fupd_elim. rewrite left_id.
    rewrite (fupd_mask_frame_r _ _ (E ∖ E1)); last set_solver+.
    rewrite {4}(union_difference_L _ _ HE). done.
  Qed.

  Lemma fupd_mask_subseteq_emptyset_difference E1 E2 :
    E2 ⊆ E1 →
    ⊢@{PROP} |={E1, E2}=> |={∅, E1∖E2}=> emp.
  Proof.
    intros ?. rewrite [in fupd E1](union_difference_L E2 E1); [|done].
    rewrite (comm_L (∪))
      -[X in fupd _ X](left_id_L ∅ (∪) E2) -fupd_mask_frame_r; [|set_solver+].
    apply fupd_mask_intro_subseteq; set_solver.
  Qed.

  Lemma fupd_or E1 E2 P Q :
    (|={E1,E2}=> P) ∨ (|={E1,E2}=> Q) ⊢@{PROP}
    (|={E1,E2}=> (P ∨ Q)).
  Proof. apply or_elim; apply fupd_mono; [ apply or_intro_l | apply or_intro_r ]. Qed.

  Global Instance fupd_or_homomorphism E :
    MonoidHomomorphism bi_or bi_or (flip (⊢)) (fupd (PROP:=PROP) E E).
  Proof. split; [split|]; try apply _; [apply fupd_or | apply fupd_intro]. Qed.

  Lemma fupd_and E1 E2 P Q :
    (|={E1,E2}=> (P ∧ Q)) ⊢@{PROP} (|={E1,E2}=> P) ∧ (|={E1,E2}=> Q).
  Proof. apply and_intro; apply fupd_mono; [apply and_elim_l | apply and_elim_r]. Qed.

  Lemma fupd_exist E1 E2 A (Φ : A → PROP) : (∃ x : A, |={E1, E2}=> Φ x) ⊢ |={E1, E2}=> ∃ x : A, Φ x.
  Proof. apply exist_elim=> a. by rewrite -(exist_intro a). Qed.

  Lemma fupd_forall E1 E2 A (Φ : A → PROP) : (|={E1, E2}=> ∀ x : A, Φ x) ⊢ ∀ x : A, |={E1, E2}=> Φ x.
  Proof. apply forall_intro=> a. by rewrite -(forall_elim a). Qed.

  Lemma fupd_sep E P Q : (|={E}=> P) ∗ (|={E}=> Q) ={E}=∗ P ∗ Q.
  Proof. by rewrite fupd_frame_r fupd_frame_l fupd_trans. Qed.

  Global Instance fupd_sep_homomorphism E :
    MonoidHomomorphism bi_sep bi_sep (flip (⊢)) (fupd (PROP:=PROP) E E).
  Proof. split; [split|]; try apply _; [apply fupd_sep | apply fupd_intro]. Qed.








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




Section class_instances_updates.
Context {PROP : bi}.
Implicit Types P Q R : PROP.

Global Instance from_assumption_bupd `{!BiBUpd PROP} p P Q :
  FromAssumption p P Q → KnownRFromAssumption p P (|==> Q).
Proof. rewrite /KnownRFromAssumption /FromAssumption=>->. apply bupd_intro. Qed.
Global Instance from_assumption_fupd
    `{!BiBUpd PROP, !BiFUpd PROP, !BiBUpdFUpd PROP} E p P Q :
  FromAssumption p P (|==> Q) → KnownRFromAssumption p P (|={E}=> Q).
Proof. rewrite /KnownRFromAssumption /FromAssumption=>->. apply bupd_fupd. Qed.

Global Instance from_pure_bupd `{!BiBUpd PROP} a P φ :
  FromPure a P φ → FromPure a (|==> P) φ.
Proof. rewrite /FromPure=> <-. apply bupd_intro. Qed.
Global Instance from_pure_fupd `{!BiFUpd PROP} a E P φ :
  FromPure a P φ → FromPure a (|={E}=> P) φ.
Proof. rewrite /FromPure=> <-. apply fupd_intro. Qed.

Global Instance into_wand_bupd `{!BiBUpd PROP} p q R P Q :
  IntoWand false false R P Q → IntoWand p q (|==> R) (|==> P) (|==> Q).
Proof.
  rewrite /IntoWand /= => HR. rewrite !intuitionistically_if_elim HR.
  apply wand_intro_l. by rewrite bupd_sep wand_elim_r.
Qed.
Global Instance into_wand_fupd `{!BiFUpd PROP} E p q R P Q :
  IntoWand false false R P Q →
  IntoWand p q (|={E}=> R) (|={E}=> P) (|={E}=> Q).
Proof.
  rewrite /IntoWand /= => HR. rewrite !intuitionistically_if_elim HR.
  apply wand_intro_l. by rewrite fupd_sep wand_elim_r.
Qed.

Global Instance into_wand_bupd_persistent `{!BiBUpd PROP} p q R P Q :
  IntoWand false q R P Q → IntoWand p q (|==> R) P (|==> Q).
Proof.
  rewrite /IntoWand /= => HR. rewrite intuitionistically_if_elim HR.
  apply wand_intro_l. by rewrite bupd_frame_l wand_elim_r.
Qed.
Global Instance into_wand_fupd_persistent `{!BiFUpd PROP} E1 E2 p q R P Q :
  IntoWand false q R P Q → IntoWand p q (|={E1,E2}=> R) P (|={E1,E2}=> Q).
Proof.
  rewrite /IntoWand /= => HR. rewrite intuitionistically_if_elim HR.
  apply wand_intro_l. by rewrite fupd_frame_l wand_elim_r.
Qed.

Global Instance into_wand_bupd_args `{!BiBUpd PROP} p q R P Q :
  IntoWand p false R P Q → IntoWand' p q R (|==> P) (|==> Q).
Proof.
  rewrite /IntoWand' /IntoWand /= => ->.
  apply wand_intro_l. by rewrite intuitionistically_if_elim bupd_wand_r.
Qed.
Global Instance into_wand_fupd_args `{!BiFUpd PROP} E1 E2 p q R P Q :
  IntoWand p false R P Q → IntoWand' p q R (|={E1,E2}=> P) (|={E1,E2}=> Q).
Proof.
  rewrite /IntoWand' /IntoWand /= => ->.
  apply wand_intro_l. by rewrite intuitionistically_if_elim fupd_wand_r.
Qed.

Global Instance from_sep_bupd `{!BiBUpd PROP} P Q1 Q2 :
  FromSep P Q1 Q2 → FromSep (|==> P) (|==> Q1) (|==> Q2).
Proof. rewrite /FromSep=><-. apply bupd_sep. Qed.
Global Instance from_sep_fupd `{!BiFUpd PROP} E P Q1 Q2 :
  FromSep P Q1 Q2 → FromSep (|={E}=> P) (|={E}=> Q1) (|={E}=> Q2).
Proof. rewrite /FromSep =><-. apply fupd_sep. Qed.

Global Instance from_or_bupd `{!BiBUpd PROP} P Q1 Q2 :
  FromOr P Q1 Q2 → FromOr (|==> P) (|==> Q1) (|==> Q2).
Proof. rewrite /FromOr=><-. apply bupd_or. Qed.
Global Instance from_or_fupd `{!BiFUpd PROP} E1 E2 P Q1 Q2 :
  FromOr P Q1 Q2 → FromOr (|={E1,E2}=> P) (|={E1,E2}=> Q1) (|={E1,E2}=> Q2).
Proof. rewrite /FromOr=><-. apply fupd_or. Qed.

Global Instance into_and_bupd `{!BiBUpd PROP} P Q1 Q2 :
  IntoAnd false P Q1 Q2 → IntoAnd false (|==> P) (|==> Q1) (|==> Q2).
Proof. rewrite /IntoAnd/==>->. apply bupd_and. Qed.
Global Instance into_and_fupd `{!BiFUpd PROP} E1 E2 P Q1 Q2 :
  IntoAnd false P Q1 Q2 → IntoAnd false (|={E1,E2}=> P) (|={E1,E2}=> Q1) (|={E1,E2}=> Q2).
Proof. rewrite /IntoAnd/==>->. apply fupd_and. Qed.

Global Instance from_exist_bupd `{!BiBUpd PROP} {A} P (Φ : A → PROP) :
  FromExist P Φ → FromExist (|==> P) (λ a, |==> Φ a)%I.
Proof. rewrite /FromExist=><-. apply bupd_exist. Qed.
Global Instance from_exist_fupd `{!BiFUpd PROP} {A} E1 E2 P (Φ : A → PROP) :
  FromExist P Φ → FromExist (|={E1,E2}=> P) (λ a, |={E1,E2}=> Φ a)%I.
Proof. rewrite /FromExist=><-. apply fupd_exist. Qed.

Global Instance into_forall_bupd `{!BiBUpd PROP} {A} P (Φ : A → PROP) :
  IntoForall P Φ → IntoForall (|==> P) (λ a, |==> Φ a)%I.
Proof. rewrite /IntoForall=>->. apply bupd_forall. Qed.
Global Instance into_forall_fupd `{!BiFUpd PROP} {A} E1 E2 P (Φ : A → PROP) :
  IntoForall P Φ → IntoForall (|={E1,E2}=> P) (λ a, |={E1,E2}=> Φ a)%I.
Proof. rewrite /IntoForall=>->. apply fupd_forall. Qed.

Global Instance from_forall_fupd
    `{!BiFUpd PROP, !BiPlainly PROP, !BiFUpdPlainly PROP} E1 E2 {A} P (Φ : A → PROP) name :
  (* Some cases in which [E2 ⊆ E1] holds *)
  TCOr (TCEq E1 E2) (TCOr (TCEq E1 ⊤) (TCEq E2 ∅)) →
  FromForall P Φ name → (∀ x, Plain (Φ x)) →
  FromForall (|={E1,E2}=> P) (λ a, |={E1,E2}=> (Φ a))%I name.
Proof.
  rewrite /FromForall=> -[->|[->|->]] <- ?; rewrite fupd_plain_forall; set_solver.
Qed.
Global Instance from_forall_step_fupd
    `{!BiFUpd PROP, !BiPlainly PROP, !BiFUpdPlainly PROP} E1 E2 {A} P (Φ : A → PROP) name :
  (* Some cases in which [E2 ⊆ E1] holds *)
  TCOr (TCEq E1 E2) (TCOr (TCEq E1 ⊤) (TCEq E2 ∅)) →
  FromForall P Φ name → (∀ x, Plain (Φ x)) →
  FromForall (|={E1}[E2]▷=> P) (λ a, |={E1}[E2]▷=> (Φ a))%I name.
Proof.
  rewrite /FromForall=> -[->|[->|->]] <- ?; rewrite step_fupd_plain_forall; set_solver.
Qed.

Global Instance is_except_0_bupd `{!BiBUpd PROP} P : IsExcept0 P → IsExcept0 (|==> P).
Proof.
  rewrite /IsExcept0=> HP.
  by rewrite -{2}HP -(except_0_idemp P) -except_0_bupd -(except_0_intro P).
Qed.
Global Instance is_except_0_fupd `{!BiFUpd PROP} E1 E2 P :
  IsExcept0 (|={E1,E2}=> P).
Proof. by rewrite /IsExcept0 except_0_fupd. Qed.

Global Instance from_modal_bupd `{!BiBUpd PROP} P :
  FromModal True modality_id (|==> P) (|==> P) P.
Proof. by rewrite /FromModal /= -bupd_intro. Qed.
Global Instance from_modal_fupd E P `{!BiFUpd PROP} :
  FromModal True modality_id (|={E}=> P) (|={E}=> P) P.
Proof. by rewrite /FromModal /= -fupd_intro. Qed.
Global Instance from_modal_fupd_wrong_mask E1 E2 P `{!BiFUpd PROP} :
  FromModal
        (pm_error "Only non-mask-changing update modalities can be introduced directly.
Use [iApply fupd_mask_intro] to introduce mask-changing update modalities")
    modality_id (|={E1,E2}=> P) (|={E1,E2}=> P) P | 100.
Proof. by intros []. Qed.

Global Instance elim_modal_bupd `{!BiBUpd PROP} p P Q :
  ElimModal True p false (|==> P) P (|==> Q) (|==> Q).
Proof.
  by rewrite /ElimModal
    intuitionistically_if_elim bupd_frame_r wand_elim_r bupd_trans.
Qed.

Global Instance elim_modal_bupd_plain_goal
    `{!BiBUpd PROP, !BiPlainly PROP, !BiBUpdPlainly PROP} p P Q :
  Plain Q → ElimModal True p false (|==> P) P Q Q.
Proof.
  intros. by rewrite /ElimModal intuitionistically_if_elim
    bupd_frame_r wand_elim_r bupd_plain.
Qed.
Global Instance elim_modal_bupd_plain
    `{!BiBUpd PROP, !BiPlainly PROP, !BiBUpdPlainly PROP} p P Q :
  Plain P → ElimModal True p p (|==> P) P Q Q.
Proof. intros. by rewrite /ElimModal bupd_plain wand_elim_r. Qed.
Global Instance elim_modal_bupd_fupd
    `{!BiBUpd PROP, !BiFUpd PROP, !BiBUpdFUpd PROP} p E1 E2 P Q :
  ElimModal True p false (|==> P) P (|={E1,E2}=> Q) (|={E1,E2}=> Q) | 10.
Proof.
  by rewrite /ElimModal intuitionistically_if_elim
    (bupd_fupd E1) fupd_frame_r wand_elim_r fupd_trans.
Qed.
Global Instance elim_modal_fupd_fupd `{!BiFUpd PROP} p E1 E2 E3 P Q :
  ElimModal True p false (|={E1,E2}=> P) P (|={E1,E3}=> Q) (|={E2,E3}=> Q).
Proof.
  by rewrite /ElimModal intuitionistically_if_elim
    fupd_frame_r wand_elim_r fupd_trans.
Qed.
Global Instance elim_modal_fupd_fupd_wrong_mask `{!BiFUpd PROP} p E0 E1 E2 E3 P Q :
  ElimModal
    (pm_error "Goal and eliminated modality must have the same mask.
Use [iMod (fupd_mask_subseteq E2)] to adjust the mask of your goal to [E2]")
    p false
    (|={E1,E2}=> P) False (|={E0,E3}=> Q) False | 100.
Proof. intros []. Qed.

Global Instance add_modal_bupd `{!BiBUpd PROP} P Q : AddModal (|==> P) P (|==> Q).
Proof. by rewrite /AddModal bupd_frame_r wand_elim_r bupd_trans. Qed.

Global Instance add_modal_fupd `{!BiFUpd PROP} E1 E2 P Q :
  AddModal (|={E1}=> P) P (|={E1,E2}=> Q).
Proof. by rewrite /AddModal fupd_frame_r wand_elim_r fupd_trans. Qed.

Global Instance elim_acc_fupd `{!BiFUpd PROP} {X} E1 E2 E α β mγ Q :
  ElimAcc (X:=X) True (fupd E1 E2) (fupd E2 E1) α β mγ
          (|={E1,E}=> Q)
          (λ x, |={E2}=> β x ∗ (mγ x -∗? |={E1,E}=> Q))%I.
Proof.
  iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
  iMod ("Hinner" with "Hα") as "[Hβ Hfin]".
  iMod ("Hclose" with "Hβ") as "Hγ". by iApply "Hfin".
Qed.
End class_instances_updates.
