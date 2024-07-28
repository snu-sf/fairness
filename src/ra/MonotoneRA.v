From sflib Require Import sflib.
From iris.algebra Require Import cmra updates gmap auth.
From Fairness Require Import PCM IProp IPM IPropAux.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.PropExtensionality.
From Fairness Require Import Axioms.
Require Import Program.

Module FiniteMap.
  Section FiniteMap.
    Context `{M: cmra}.

    Definition t : ucmra := (gmapUR nat M).

    Definition singleton (k : nat) (m : M) : t := {[ k := m ]}.

    (* TODO: upstream to iris *)
    Global Instance singleton_proper k :
      Proper ((≡)==>(≡)) (singleton k).
    Proof.
      intros x y EQ. unfold singleton.
      intros k'. destruct (decide (k' = k)) as [->|NE].
      - rewrite !lookup_singleton. f_equiv. done.
      - rewrite !lookup_singleton_ne; done.
    Qed.

    Lemma singleton_wf k m
      :
      ✓ (singleton k m) <-> ✓ m.
    Proof. apply singleton_valid. Qed.

    Lemma singleton_add k m0 m1
      :
      (singleton k m0) ⋅ (singleton k m1)
      ≡
        singleton k (m0 ⋅ m1).
    Proof. by rewrite singleton_op /singleton. Qed.

    Lemma singleton_core k x cx
      :
      pcore x ≡ Some cx → core (singleton k x) ≡ singleton k cx.
    Proof. by apply singleton_core'. Qed.

    Lemma singleton_core_total k m `{CmraTotal M}
      :
      core (singleton k m) ≡ singleton k (core m).
    Proof. by rewrite singleton_core_total. Qed.

    Lemma singleton_updatable k m0 m1
          (UPD: m0 ~~> m1)
      :
      (singleton k m0) ~~> (singleton k m1).
    Proof. by apply singleton_update. Qed.

    Lemma singleton_extends k m0 m1
          (UPD: m0 ≼ m1)
      :
      (singleton k m0) ≼ (singleton k m1).
    Proof. apply singleton_included. by right. Qed.

    Lemma singleton_updatable_set k m s
          (UPD: m ~~>: s)
      :
      (singleton k m) ~~>: (fun a => exists m1, s m1 /\ a = singleton k m1).
    Proof.
      eapply cmra_updateP_weaken.
      { eapply singleton_updateP',UPD. }
      ii. simpl in *. des. eauto.
    Qed.

    Lemma singleton_alloc (m: M)
          (WF: ✓ m)
      :
      ε ~~>: (fun f => exists k, f ≡ singleton k m).
    Proof.
      eapply alloc_updateP.
      { exact WF. }
      intros k _. exists k. unfold singleton. set_solver.
    Qed.
  End FiniteMap.
  Global Arguments t : clear implicits.
End FiniteMap.


Module Collection.
  Section Collection.
    Context {A: Type}.

    Record car : Type := mk {
      elem :> A -> Prop
    }.

    Definition unit: car := mk (fun _ => True).

    Definition add: car -> car -> car :=
      fun s0 s1 => mk (fun a => s0 a /\ s1 a).

    Definition wf: car -> Prop :=
      fun _ => True.

    Definition core: car -> option car :=
      fun s => Some s.

    Canonical Structure CollectionO := leibnizO car.

    Global Instance collection_equiv : Equiv car := (=).
    Local Instance collection_valid_instance : Valid car := wf.
    Local Instance collection_pcore_instance : PCore car := core.
    Local Instance collection_op_instance : Op car := add.
    Local Instance collection_unit_instance : Unit car := unit.

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
      - intros ???. fold_leibniz.
        rewrite !op_unfold /add. f_equal.
        extensionality a0.
        eapply propositional_extensionality. split; i; des; ss; des; ss.
      - intros ??. fold_leibniz.
        rewrite !op_unfold /add. f_equal.
        extensionality a0.
        eapply propositional_extensionality. split; i; des; ss; des; ss.
      - intros ??. fold_leibniz.
        rewrite !pcore_unfold /core op_unfold /add. injection 1. intros ->. destruct cx. f_equal.
        extensionality a0.
        eapply propositional_extensionality. split; i; des; ss; des; ss.
      - intros ???.
        rewrite !pcore_unfold /core. intros [? EQ]. injection 1. intros ->. fold_leibniz. subst. eexists. split; ss.
        exists x0. fold_leibniz. done.
    Qed.

    Canonical Structure CollectionR := discreteR car mixin.

    Global Instance discrete : CmraDiscrete CollectionR.
    Proof. apply discrete_cmra_discrete. Qed.

    Lemma ucmra_mixin : UcmraMixin car.
    Proof.
      split; try apply _; try done.
      intros m.
      fold_leibniz.
      rewrite op_unfold /add unit_unfold /unit. destruct m. f_equal.
      extensionality a0.
      eapply propositional_extensionality. split; i; des; ss; des; ss.
    Qed.
    Canonical Structure t := Ucmra car ucmra_mixin.

    Definition into_t (a : A -> Prop) : t := mk a.
  End Collection.
End Collection.
Global Arguments Collection.t _ : clear implicits.

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
  Definition monoRA: ucmra := @FiniteMap.t (authUR (Collection.t gmon)).
  Context `{@GRA.inG monoRA Σ}.
  Notation iProp := (iProp Σ).

  Section LE.
    Variable k: nat.

    Variable W: Type.
    Variable le: W -> W -> Prop.
    Hypothesis le_PreOrder: PreOrder le.

    Let leR (w: W): Collection.t gmon := Collection.into_t (gmon_le (@mk_gmon W le le_PreOrder w)).

    Definition monoBlack (w: W): iProp :=
      OwnM (FiniteMap.singleton k (● (leR w) ⋅ ◯ (leR w))).

    Definition monoWhiteExact (w: W): iProp :=
      OwnM (FiniteMap.singleton k (◯ (leR w))).

    Definition monoWhite (w0: W): iProp :=
      ∃ w1, monoWhiteExact w1 ∧ ⌜le w0 w1⌝.

    Lemma white_idempotent w0 w1
          (LE: le w0 w1)
      :
      ◯ (leR w0) ⋅ ◯ (leR w1) ≡ ◯ (leR w1).
    Proof.
      rewrite -auth_frag_op. f_equiv.
      rewrite Collection.op_unfold /Collection.add /leR /Collection.into_t.
      fold_leibniz. f_equal. extensionality a.
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

    Local Lemma prop_ext_rev
          A B
          (EQ: A = B)
      :
        A <-> B
    .
    Proof. clarify. Qed.

    Lemma black_updatable w0 w1
          (LE: le w0 w1)
      :
      (monoBlack w0) -∗ (#=> monoBlack w1).
    Proof.
      iIntros "H". iApply (OwnM_Upd with "H").
      eapply FiniteMap.singleton_updatable.
      apply auth_update,local_update_discrete.
      fold_leibniz. intros w' _.
      rewrite Collection.valid_unfold /Collection.wf /leR /Collection.into_t.
      destruct w' as [[w']|]; ss.
      rewrite Collection.op_unfold /Collection.add.
      injection 1. intros FRAME.
      rewrite Collection.op_unfold /Collection.add. split; ss.
      f_equal.
      extensionality w. eapply equal_f with (x:=w) in FRAME.
      eapply prop_ext_rev in FRAME. des.
      eapply propositional_extensionality. split; i; des; ss.
      split; eauto. eapply FRAME.
      rr. etrans; eauto. econs; eauto.
    Qed.

    Lemma black_white_exact_compare w0 w1
      :
      (monoWhiteExact w0) -∗ (monoBlack w1) -∗ ⌜le w0 w1⌝.
    Proof.
      unfold monoWhiteExact, monoBlack.
      rewrite <- FiniteMap.singleton_add.
      iIntros "H0 [H1 H2]".
      iCombine "H1 H0" as "H".
      iOwnWf "H" as WF. iPureIntro.
      rewrite FiniteMap.singleton_wf in WF.
      apply auth_both_valid_discrete in WF as [WF _].
      rr in WF. destruct WF as [[z] EQ]. fold_leibniz.
      rewrite Collection.op_unfold /Collection.add /leR /Collection.into_t in EQ.
      injection EQ. intros LE. ss.
      eapply equal_f in LE. eapply prop_ext_rev in LE. des.
      hexploit LE.
      { rr. econs. reflexivity. }
      i. des. rr in H0. dependent destruction H0. auto.
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
    ⊢ #=> (∃ k, monoBlack k W le le_PreOrder w).
  Proof.
    iPoseProof (@OwnM_unit _ _ H) as "H".
    iPoseProof (OwnM_Upd_set with "H") as "> H0".
    { eapply FiniteMap.singleton_alloc.
      instantiate (1:= (● (Collection.into_t (gmon_le (@mk_gmon W le le_PreOrder w))) ⋅ ◯ (Collection.into_t (gmon_le (@mk_gmon W le le_PreOrder w))))).
      apply auth_both_valid_discrete. split; [|done].
      exists ε. rewrite right_id. fold_leibniz. done.
    }
    iDestruct "H0" as (b) "[% H0]". des. rewrite H0.
    iModIntro. iExists k. auto.
  Qed.
End Monotone.


Section MAP.
  Definition partial_map_le {A B} (f0 f1: A -> option B): Prop :=
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

  Definition partial_map_empty {A B} : A -> option B :=
    fun _ => None.

  Definition partial_map_update {A B} (a: A) (b: B) (f: A -> option B):
    A -> option B :=
    fun a' => if (excluded_middle_informative (a' = a)) then Some b else (f a').

  Definition partial_map_singleton {A B} (a: A) (b: B): A -> option B :=
    partial_map_update a b (@partial_map_empty A B).

  Definition partial_map_update_le {A B} (a: A) (b: B) (f: A -> option B)
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
  Notation iProp := (iProp Σ).

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

  Definition list_sub {A} (s0 s1: list A): Prop :=
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

From iris.algebra Require Import excl agree csum.

Module OneShot.
  Section ONESHOT.
    Variable A: Type.

    Definition t : ucmra := optionUR (csumR fracR (agreeR (leibnizO A))).

    Definition to_pending (q : Qp) : t := Some (Cinl q).
    Definition pending (q : Qp) : t := to_pending q.
    Definition to_shot (a : A) : t := Some (Cinr (to_agree (a : leibnizO A))).
    Definition shot (a : A) : t := to_shot a.

    Global Instance shot_core_id a: CoreId (shot a).
    Proof. apply _. Qed.

    Lemma pending_one_wf: ✓ (pending 1).
    Proof. done. Qed.

    Lemma shot_wf a: ✓ (shot a).
    Proof. done. Qed.

    Lemma shot_agree a0 a1
          (WF: ✓ (shot a0 ⋅ shot a1))
      :
      a0 = a1.
    Proof. apply (@to_agree_op_inv_L (leibnizO A)); [apply _|done]. Qed.

    Lemma pending_not_shot a q
          (WF: ✓ (pending q ⋅ shot a))
      :
      False.
    Proof. done. Qed.

    Lemma pending_wf q
          (WF: ✓ (pending q))
      :
      (q ≤ 1)%Qp.
    Proof. done. Qed.

    Lemma pending_sum q0 q1
      :
      pending (q0 + q1)%Qp = pending q0 ⋅ pending q1.
    Proof. done. Qed.

    Lemma pending_shot a
      :
      (pending 1) ~~> (shot a).
    Proof.
      rewrite /pending /shot /t.
      rewrite cmra_discrete_update. intros mz WF.
      apply exclusive_Some_l in WF; [|apply _].
      subst. done.
    Qed.

    Lemma shot_dup a
      :
      (shot a) ≡ (shot a) ⋅ (shot a).
    Proof.
      rewrite /shot -Some_op -Cinr_op.
      rewrite <- core_id_dup; [done|apply _].
    Qed.

  End ONESHOT.
  Global Typeclasses Opaque to_shot shot to_pending pending.
  Global Opaque to_shot shot to_pending pending.
End OneShot.
Global Arguments OneShot.shot {_} _.

Module OneShotP.

  Definition pending A `{@GRA.inG (OneShot.t A) Σ} (q : Qp) : iProp Σ :=
    OwnM (OneShot.pending A q).

  Definition shot `{@GRA.inG (OneShot.t A) Σ} a : iProp Σ := OwnM (OneShot.shot a).

  Global Program Instance shot_persistent (A: Type)
         `{@GRA.inG (OneShot.t A) Σ}
         (a: A)
    :
    Persistent (shot a).
  Next Obligation.
    i. iIntros "H". iPoseProof (own_persistent with "H") as "# G". ss.
  Qed.

  Lemma shot_agree (A: Type)
        `{@GRA.inG (OneShot.t A) Σ}
        (a0 a1: A)
    :
    (shot a0 ∧ (shot a1))
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
    (pending A q ∧ (shot a))
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
    apply FiniteMap.singleton_wf in H0.
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
    apply FiniteMap.singleton_wf in H0.
    apply OneShot.pending_not_shot in H0. auto.
  Qed.

Global Typeclasses Opaque shot pending.
Global Opaque shot pending.
End OneShotP.

From iris.algebra Require Import lib.dfrac_agree.
Module Consent.
  Section CONSENT.
    Variable A: Type.

    Definition t : ucmra := optionUR (dfrac_agreeR (leibnizO A)).

    Definition vote (a: A) (q: Qp): t := Some (to_frac_agree q (a : leibnizO A)).

    Lemma vote_one_wf a: ✓ (vote a 1%Qp).
    Proof. done. Qed.

    Lemma vote_agree a0 q0 a1 q1
          (WF: ✓ (vote a0 q0 ⋅ vote a1 q1))
      :
      a0 = a1 /\ (q0 + q1 ≤ 1)%Qp.
    Proof.
      rewrite /vote -Some_op Some_valid frac_agree_op_valid_L in WF.
      des. done.
    Qed.

    Lemma vote_wf a q
          (WF: ✓ (vote a q))
      :
      (q ≤ 1)%Qp.
    Proof. rewrite /vote Some_valid pair_valid in WF. des. done. Qed.

    Lemma vote_sum a q0 q1
      :
      vote a (q0 + q1)%Qp ≡ vote a q0 ⋅ vote a q1.
    Proof. rewrite /vote -Some_op frac_agree_op //. Qed.

    Lemma vote_revolution a0 a1
      :
      (vote a0 1%Qp) ~~> (vote a1 1%Qp).
    Proof.
      rewrite /vote cmra_discrete_update. intros mz WF.
      apply exclusive_Some_l in WF; [|apply _].
      subst. done.
    Qed.
  End CONSENT.
  Global Typeclasses Opaque vote.
  Global Opaque vote.
End Consent.
Global Arguments Consent.vote {_} _ _.

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

  Definition voted
             `{@GRA.inG (Consent.t A) Σ}
             (a: A): iProp Σ :=
    ∃ q, OwnM (Consent.vote a q).

  Lemma voted_agree (A: Type)
        `{@GRA.inG (Consent.t A) Σ}
        (a0 a1: A)
    :
    (voted a0 ∗ voted a1)
      -∗
      (⌜a0 = a1⌝).
  Proof.
    iIntros "[[% H0] [% H1]]". iApply vote_agree. iFrame "H0 H1".
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

  Definition voted_singleton
             `{@GRA.inG (@FiniteMap.t (Consent.t A)) Σ}
             k (a: A): iProp Σ :=
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
    apply FiniteMap.singleton_wf in H0.
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
  Global Typeclasses Opaque voted voted_singleton.
  Global Opaque voted voted_singleton.
End ConsentP.
