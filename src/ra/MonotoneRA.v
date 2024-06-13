From sflib Require Import sflib.
From Fairness Require Import PCM IProp IPM IPropAux.
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


Section UPDATING.
  Context `{Σ: @GRA.t}.

  Definition updating (I: iProp) (P Q R: iProp): iProp :=
    I -∗ (#=> (P ∗ (Q -∗ #=> (I ∗ R)))).

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

Section LISTSUB.

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

End LISTSUB.


Require Import Program.

Lemma Qp_add_lt_one : forall (q : Qp), (1 + q ≤ 1)%Qp -> False.
Proof. intros. eapply Qp.not_add_le_l. eauto. Qed.

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
    rewrite FiniteMap.singleton_core. ss.
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


Module OneShotWithVal.
  Section ONESHOTWITHVAL.
    Variable A: Type.

    Definition oneshot_add (a0 a1: bool + ((Qp * A) + A)): bool + ((Qp * A) + A) :=
      match a0, a1 with
      | inl false, a
      | a, inl false => a
      | inr (inr a0), inr (inr a1) => if (excluded_middle_informative (a0 = a1)) then inr (inr a0) else inl true
      | inr (inl (q0,a0)), inr (inl (q1,a1)) => if (excluded_middle_informative (a0 = a1)) then inr (inl ((q0 + q1)%Qp,a0)) else inl true
      | _, _ => inl true
      end.

    Definition oneshot_core (a: bool + ((Qp * A) + A)): bool + ((Qp * A) + A) :=
      match a with
      | inr (inl _) => inl false
      | _ => a
      end.

    Program Instance t: URA.t := {
        car := bool + ((Qp * A) + A);
        unit := inl false;
        _add := oneshot_add;
        _wf := fun a =>
                 match a with
                 | inl true => False
                 | inr (inl (q,a)) => (q ≤ 1)%Qp
                 | _ => True
                 end;
        core := oneshot_core;
      }
    .
    Next Obligation.
      unfold oneshot_add. des_ifs. f_equal. f_equal. f_equal. eapply Qp.add_comm.
    Qed.
    Next Obligation.
      unfold oneshot_add. des_ifs. f_equal. f_equal. f_equal. eapply Qp.add_assoc.
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
      { exists (inl true). ss. }
      { exists (inr (inr a0)). des_ifs. }
    Qed.

    Definition pending (q: Qp) (a : A) : t := inr (inl (q,a)).
    Definition shot (a: A): t := inr (inr a).

    Lemma pending_one_wf a: URA.wf (pending 1%Qp a).
    Proof.
      ur. ss.
    Qed.

    Lemma shot_wf a: URA.wf (shot a).
    Proof.
      ur. ss.
    Qed.

    Lemma pending_agree q0 q1 a0 a1 (WF: URA.wf (pending q0%Qp a0 ⋅ pending q1%Qp a1))
      :
      (q0 + q1 ≤ 1)%Qp /\ a0 = a1.
    Proof.
      ur in WF. des_ifs.
    Qed.

    Lemma shot_agree a0 a1
          (WF: URA.wf (shot a0 ⋅ shot a1))
      :
      a0 = a1.
    Proof.
      ur in WF. des_ifs.
    Qed.

    Lemma pending_not_shot a' a q
          (WF: URA.wf (pending q a' ⋅ shot a))
      :
      False.
    Proof.
      ur in WF. ss.
    Qed.

    Lemma pending_wf q a
          (WF: URA.wf (pending q a))
      :
      (q ≤ 1)%Qp.
    Proof.
      ur in WF. ss.
    Qed.

    Lemma pending_sum q0 q1 a
      :
      pending (q0 + q1)%Qp a = pending q0 a ⋅ pending q1 a.
    Proof.
      ur. des_ifs.
    Qed.

    Lemma pending_update a a'
      :
      URA.updatable (pending 1 a) (pending 1 a').
    Proof.
      ii. ur in H. ur. des_ifs.
      - apply Qp.not_add_le_l in H; auto.
      - unfold pending in *. inversion Heq. auto.
    Qed.

    Lemma pending_update_half a1 a2 a
      :
      URA.updatable (pending (1/2) a1 ⋅ pending (1/2) a2) (pending 1 a).
    Proof.
      ii. specialize (URA.wf_mon H) as H'. apply pending_agree in H'. destruct H' as [_ H']. subst.
      rewrite -pending_sum in H. rewrite Qp.half_half in H.
      ur in H. ur. des_ifs.
      - apply Qp.not_add_le_l in H; auto.
      - unfold oneshot_add in *. inversion Heq. auto.
    Qed.

    Lemma pending_update_half_half a1 a2 a
      :
      URA.updatable (pending (1/2) a1 ⋅ pending (1/2) a2) (pending (1/2) a ⋅ pending (1/2) a).
    Proof.
      ii. specialize (URA.wf_mon H) as H'. apply pending_agree in H'. destruct H' as [_ H']. subst.
      rewrite -pending_sum in H. rewrite Qp.half_half in H.
      ur in H. ur. des_ifs.
      - apply Qp.not_add_le_l in H; auto.
      - unfold oneshot_add in *. inversion Heq. rewrite Qp.half_half. auto.
      - apply Qp.not_add_le_l in H; done.
    Qed.

    Lemma pending_shot a a'
      :
      URA.updatable (pending 1 a') (shot a).
    Proof.
      ii. ur in H. ur. des_ifs.
      apply Qp.not_add_le_l in H; auto.
    Qed.
  End ONESHOTWITHVAL.
End OneShotWithVal.

Module OneShotWithValP.
  Global Program Instance shot_persistent (A: Type)
         `{@GRA.inG (OneShotWithVal.t A) Σ}
         (a: A)
    :
    Persistent (OwnM (OneShotWithVal.shot a)).
  Next Obligation.
    i. iIntros "H". iPoseProof (own_persistent with "H") as "# G". ss.
  Qed.

  Lemma pending_agree (A: Type)
        `{@GRA.inG (OneShotWithVal.t A) Σ}
        (a0 a1: A) (q0 q1 : Qp)
    :
    (OwnM (OneShotWithVal.pending q0 a0) ∗ (OwnM (OneShotWithVal.pending q1 a1)))
      -∗
      (⌜(q0 + q1 ≤ 1)%Qp ∧ a0 = a1⌝).
  Proof.
    iIntros "[H0 H1]".
    iCombine "H0 H1" as "H". iOwnWf "H". apply OneShotWithVal.pending_agree in H0. auto.
  Qed.

  Lemma shot_agree (A: Type)
        `{@GRA.inG (OneShotWithVal.t A) Σ}
        (a0 a1: A)
    :
    (OwnM (OneShotWithVal.shot a0) ∧ (OwnM (OneShotWithVal.shot a1)))
      -∗
      (⌜a0 = a1⌝).
  Proof.
    iIntros "[# H0 # H1]".
    iCombine "H0 H1" as "H". iOwnWf "H". apply OneShotWithVal.shot_agree in H0. auto.
  Qed.

  Lemma pending_not_shot (A: Type)
        `{@GRA.inG (OneShotWithVal.t A) Σ}
        (a a': A) q
    :
    (OwnM (OneShotWithVal.pending q a') ∧ (OwnM (OneShotWithVal.shot a)))
      -∗
      False.
  Proof.
    iIntros "[H0 # H1]".
    iCombine "H0 H1" as "H". iOwnWf "H". apply OneShotWithVal.pending_not_shot in H0. auto.
  Qed.

  Global Program Instance shot_persistent_singleton (A: Type)
         `{@GRA.inG (@FiniteMap.t (OneShotWithVal.t A)) Σ}
         k (a: A)
    :
    Persistent (OwnM (FiniteMap.singleton k (OneShotWithVal.shot a))).
  Next Obligation.
    i. iIntros "H". iPoseProof (own_persistent with "H") as "# G".
    rewrite FiniteMap.singleton_core. ss.
  Qed.

  Lemma shot_agree_singleton (A: Type)
        `{@GRA.inG (@FiniteMap.t (OneShotWithVal.t A)) Σ}
        k (a0 a1: A)
    :
    (OwnM (FiniteMap.singleton k (OneShotWithVal.shot a0)) ∧ (OwnM (FiniteMap.singleton k (OneShotWithVal.shot a1))))
      -∗
      (⌜a0 = a1⌝).
  Proof.
    iIntros "[# H0 # H1]".
    iCombine "H0 H1" as "H". iOwnWf "H".
    rewrite FiniteMap.singleton_add in H0. apply FiniteMap.singleton_wf in H0.
    apply OneShotWithVal.shot_agree in H0. auto.
  Qed.

  Lemma pending_not_shot_singleton (A: Type)
        `{@GRA.inG (@FiniteMap.t (OneShotWithVal.t A)) Σ}
        k (a a': A) q
    :
    (OwnM (FiniteMap.singleton k (OneShotWithVal.pending q a')) ∧ (OwnM (FiniteMap.singleton k (OneShotWithVal.shot a))))
      -∗
      False.
  Proof.
    iIntros "[H0 # H1]".
    iCombine "H0 H1" as "H". iOwnWf "H".
    rewrite FiniteMap.singleton_add in H0. apply FiniteMap.singleton_wf in H0.
    apply OneShotWithVal.pending_not_shot in H0. auto.
  Qed.
End OneShotWithValP.

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
    (OwnM (Consent.vote a0 q0) ∗ (OwnM (Consent.vote a1 q1)))
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
    (voted a0 ∗ voted a1)
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
      (voted a ∗ voted a).
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
    (voted_singleton k a0 ∗ voted_singleton k a1)
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
      (voted_singleton k a ∗ voted_singleton k a).
  Proof.
    iIntros "[% H]". erewrite <- (Qp.div_2 q).
    rewrite Consent.vote_sum.
    rewrite <- FiniteMap.singleton_add.
    iDestruct "H" as "[H0 H1]". iSplitL "H0".
    { iExists _. iFrame. }
    { iExists _. iFrame. }
  Qed.
End ConsentP.
