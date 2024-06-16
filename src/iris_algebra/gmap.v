From sflib Require Import sflib.
From stdpp Require Export list gmap.
From Fairness Require Import list cmra.
From Fairness Require Import gset.
From Fairness Require Import updates local_updates proofmode_classes big_op.
From iris.prelude Require Import prelude options.

Local Open Scope iris_algebra_scope.

(* Global Instance map_seq_ne {A : Type} start :
  NonExpansive (map_seq (M:=gmap nat A) start).
Proof.
  intros n l1 l2 Hl. revert start.
  induction Hl; intros; simpl; repeat (done || f_equiv).
Qed. *)

(* Global Arguments gmapO _ {_ _} _. *)

Section ofe.
Context `{Countable K} {A : Type}.
Implicit Types m : gmap K A.
Implicit Types i : K.

Global Instance lookup_ne k :
  Proper ((=) ==> (=)) (lookup k : gmap K A → option A).
Proof. by intros m1 m2 ->. Qed.
End ofe.

(** Non-expansiveness of higher-order map functions and big-ops *)
Global Instance merge_ne `{Countable K} {A B C : Type} :
  Proper ((eq (A:=option A) ==> eq (A:=option B) ==> eq (A:=option C)) ==>
           eq ==> eq ==> eq) (merge (M:=gmap K)).
Proof.
  intros ?? Hf ?? Hm1 ?? Hm2. apply map_eq. intros i. rewrite !lookup_merge.
  apply (f_equal (fun m => m !! i)) in Hm1.
  apply (f_equal (fun m => m !! i)) in Hm2.
  destruct Hm1, Hm2. destruct (x0 !! i),(x1 !! i); simpl; [..|done].
  all: apply Hf; done.
Qed.
Global Instance union_with_ne `{Countable K} {A : Type} :
  Proper ((eq ==> eq ==> eq) ==>
          eq ==> eq ==> eq) (union_with (M:=gmap K A)).
Proof.
  intros ?? Hf ?? Hm1 ?? Hm2; apply (merge_ne _ _); auto.
  do 2 destruct 1. unfold union_with,option_union_with.
  destruct x2,x3; try done. apply Hf; done.
Qed.
Global Instance map_fmap_ne `{Countable K} {A B : Type} (f : A → B) :
  Proper (eq ==> eq) f → Proper (eq ==> eq) (fmap (M:=gmap K) f).
Proof. intros ? m m' ?. apply map_eq. intros k. rewrite !lookup_fmap. by repeat f_equiv. Qed.
Global Instance map_zip_with_ne `{Countable K} {A B C : Type} (f : A → B → C) :
  Proper (eq ==> eq ==> eq) f →
  Proper (eq ==> eq ==> eq) (map_zip_with (M:=gmap K) f).
Proof.
  intros Hf m1 m1' Hm1 m2 m2' Hm2. apply merge_ne; try done.
Qed.

(* Global Instance gmap_union_ne `{Countable K} {A : Type} :
  NonExpansive2 (union (A:=gmap K A)).
Proof. intros n. apply union_with_ne. by constructor. Qed. *)
Global Instance gmap_disjoint_ne `{Countable K} {A : Type} :
  Proper (eq ==> eq ==> iff) (map_disjoint (M:=gmap K) (A:=A)).
Proof.
  intros m1 m1' Hm1 m2 m2' Hm2; split;
    intros Hm i; specialize (Hm i).
  all: apply (f_equal (fun m => m !! i)) in Hm1.
  all: apply (f_equal (fun m => m !! i)) in Hm2.
  all: by destruct Hm1, Hm2.
Qed.

Lemma gmap_union_dist_eq `{Countable K} {A : Type} (m m1 m2 : gmap K A) :
  m = m1 ∪ m2 ↔ ∃ m1' m2', m = m1' ∪ m2' ∧ m1' = m1 ∧ m2' = m2.
Proof.
  split; last first.
  { by intros (m1'&m2'&->&<-&<-). }
  intros Hm.
  exists m1,m2. done.
Qed.

Lemma big_opM_ne_2 `{Monoid M o} `{Countable K} {A : Type} (f g : K → A → M) m1 m2 :
  m1 = m2 →
  (∀ k y1 y2,
    m1 !! k = Some y1 → m2 !! k = Some y2 → y1 = y2 → f k y1 = g k y2) →
  ([^o map] k ↦ y ∈ m1, f k y) = ([^o map] k ↦ y ∈ m2, g k y).
Proof.
  intros Hl Hf. apply big_opM_gen_proper_2; try (apply _ || done).
  intros k. assert (m1 !! k = m2 !! k) as Hlk by (by f_equiv).
  destruct (m1 !! k) eqn:?, (m2 !! k) eqn:?; inversion Hlk; naive_solver.
Qed.

(* CMRA *)
Section cmra.
Context `{Countable K} {A : cmra}.
Implicit Types m : gmap K A.

Local Instance gmap_unit_instance : Unit (gmap K A) := (∅ : gmap K A).
Local Instance gmap_op_instance : Op (gmap K A) := merge op.
Local Instance gmap_pcore_instance : PCore (gmap K A) := λ m, Some (omap pcore m).
Local Instance gmap_valid_instance : Valid (gmap K A) := λ m, ∀ i, ✓ (m !! i).

Lemma gmap_op m1 m2 : m1 ⋅ m2 = merge op m1 m2.
Proof. done. Qed.
Lemma lookup_op m1 m2 i : (m1 ⋅ m2) !! i = m1 !! i ⋅ m2 !! i.
Proof. rewrite lookup_merge. by destruct (m1 !! i), (m2 !! i). Qed.
Lemma lookup_core m i : core m !! i = core (m !! i).
Proof. by apply lookup_omap. Qed.

(* [m1 ≼ m2] is not equivalent to [∀, m1 ≼ m2],
so there is no good way to reuse the above proof. *)
Lemma lookup_included (m1 m2 : gmap K A) : m1 ≼ m2 ↔ ∀ i, m1 !! i ≼ m2 !! i.
Proof.
  split; [by intros [m Hm] i; exists (m !! i); rewrite -lookup_op Hm|].
  revert m2. induction m1 as [|i x m Hi IH] using map_ind=> m2 Hm.
  { exists m2. by rewrite left_id. }
  destruct (IH (delete i m2)) as [m2' Hm2'].
  { intros j. move: (Hm j); destruct (decide (i = j)) as [->|].
    - intros _. rewrite Hi. apply: ucmra_unit_least.
    - rewrite lookup_insert_ne // lookup_delete_ne //. }
  destruct (Hm i) as [my Hi']; simplify_map_eq.
  exists (partial_alter (λ _, my) i m2'). apply map_eq. intros j; destruct (decide (i = j)) as [->|].
  - by rewrite Hi' lookup_op lookup_insert lookup_partial_alter.
  - apply (f_equal (fun m => m !! j)) in Hm2'. move: Hm2'. by rewrite !lookup_op lookup_delete_ne //
      lookup_insert_ne // lookup_partial_alter_ne.
Qed.

Lemma gmap_cmra_mixin : CmraMixin (gmap K A).
Proof.
  apply cmra_total_mixin.
  - eauto.
  - by intros m1 m2 m3; apply map_eq; intros i; rewrite !lookup_op assoc.
  - by intros m1 m2;  apply map_eq; intros i; rewrite !lookup_op (comm op).
  - intros m; apply map_eq; intros i. by rewrite lookup_op lookup_core cmra_core_l.
  - intros m; apply map_eq; intros i. by rewrite !lookup_core cmra_core_idemp.
  - intros m1 m2; rewrite !lookup_included=> Hm i.
    rewrite !lookup_core. by apply cmra_core_mono.
  - intros m1 m2 Hm i; apply cmra_valid_op_l with (m2 !! i).
    by rewrite -lookup_op.
  - intros m y1 y2 Hm Heq.
    refine ((λ FUN, _) (λ i, cmra_extend (m !! i) (y1 !! i) (y2 !! i) (Hm i) _)); last by rewrite -lookup_op Heq.
    exists (map_imap (λ i _, projT1 (FUN i)) y1).
    exists (map_imap (λ i _, proj1_sig (projT2 (FUN i))) y2).
    split_and!; apply map_eq=>i;
    rewrite ?lookup_op !map_lookup_imap;
    destruct (FUN i) as (z1i&z2i&Hmi&Hz1i&Hz2i)=>/=.
    + destruct (y1 !! i), (y2 !! i); inversion Hz1i; inversion Hz2i; subst=>//.
    + revert Hz1i. case: (y1!!i)=>[?|] //.
    + revert Hz2i. case: (y2!!i)=>[?|] //.
Qed.
Canonical Structure gmapR := Cmra (gmap K A) gmap_cmra_mixin.

(* Global Instance gmap_cmra_discrete : CmraDiscrete A → CmraDiscrete gmapR.
Proof. split; [apply _|]. intros m ? i. by apply: cmra_discrete_valid. Qed. *)

Lemma gmap_ucmra_mixin : UcmraMixin (gmap K A).
Proof.
  split.
  - by intros i; rewrite lookup_empty.
  - by intros m; apply map_eq=>i; rewrite /= lookup_op lookup_empty (left_id_L None _).
  - unfold pcore,gmap_pcore_instance. f_equal. apply map_eq=>i. by rewrite lookup_omap lookup_empty.
Qed.
Canonical Structure gmapUR := Ucmra (gmap K A) gmap_ucmra_mixin.

End cmra.

Global Arguments gmapR _ {_ _} _.
Global Arguments gmapUR _ {_ _} _.

Section properties.
Context `{Countable K} {A : cmra}.
Implicit Types m : gmap K A.
Implicit Types i : K.
Implicit Types x y : A.

Global Instance lookup_op_homomorphism i :
  MonoidHomomorphism op op (=) (lookup i : gmap K A → option A).
Proof.
  split; [split|]; try apply _.
  - intros m1 m2; by rewrite lookup_op.
  - done.
Qed.

Lemma lookup_opM m1 mm2 i : (m1 ⋅? mm2) !! i = m1 !! i ⋅ (mm2 ≫= (.!! i)).
Proof. destruct mm2; by rewrite /= ?lookup_op ?right_id_L. Qed.

Lemma lookup_valid_Some m i x : ✓ m → m !! i = Some x → ✓ x.
Proof. move=> Hm Hi. move:(Hm i). by rewrite Hi. Qed.

Lemma insert_valid m i x : ✓ x → ✓ m → ✓ <[i:=x]>m.
Proof. by intros ?? j; destruct (decide (i = j)); simplify_map_eq. Qed.
Lemma singleton_valid i x : ✓ ({[ i := x ]} : gmap K A) ↔ ✓ x.
Proof.
  split.
  - move=>/(_ i); by simplify_map_eq.
  - intros. apply insert_valid; first done. apply: ucmra_unit_valid.
Qed.

Lemma delete_valid m i : ✓ m → ✓ (delete i m).
Proof. intros Hm j; destruct (decide (i = j)); by simplify_map_eq. Qed.

Lemma insert_singleton_op m i x : m !! i = None → <[i:=x]> m = {[ i := x ]} ⋅ m.
Proof.
  intros Hi; apply map_eq=> j; destruct (decide (i = j)) as [->|].
  - by rewrite lookup_op lookup_insert lookup_singleton Hi right_id_L.
  - by rewrite lookup_op lookup_insert_ne // lookup_singleton_ne // left_id_L.
Qed.

Lemma singleton_core (i : K) (x : A) cx :
  pcore x = Some cx → core {[ i := x ]} =@{gmap K A} {[ i := cx ]}.
Proof. apply omap_singleton_Some. Qed.
Lemma singleton_core' (i : K) (x : A) cx :
  pcore x = Some cx → core {[ i := x ]} =@{gmap K A} {[ i := cx ]}.
Proof. apply omap_singleton_Some. Qed.
Lemma singleton_core_total `{!CmraTotal A} (i : K) (x : A) :
  core {[ i := x ]} =@{gmap K A} {[ i := core x ]}.
Proof. apply singleton_core. rewrite cmra_pcore_core //. Qed.
Lemma singleton_op (i : K) (x y : A) :
  {[ i := x ]} ⋅ {[ i := y ]} =@{gmap K A} {[ i := x ⋅ y ]}.
Proof. by apply (merge_singleton _ _ _ x y). Qed.
Global Instance singleton_is_op i a a1 a2 :
  IsOp a a1 a2 → IsOp' ({[ i := a ]} : gmap K A) {[ i := a1 ]} {[ i := a2 ]}.
Proof. rewrite /IsOp' /IsOp=> ->. by rewrite -singleton_op. Qed.

Lemma gmap_core_id m : (∀ i x, m !! i = Some x → CoreId x) → CoreId m.
Proof.
  intros Hcore; apply core_id_total. simpl.
  refine (map_eq _ _ _)=>i.
  rewrite lookup_core. destruct (m !! i) as [x|] eqn:Hix; [|done].
  by eapply Hcore.
Qed.
Global Instance gmap_core_id' m : (∀ x : A, CoreId x) → CoreId m.
Proof. auto using gmap_core_id. Qed.

Global Instance gmap_singleton_core_id i (x : A) :
  CoreId x → CoreId {[ i := x ]}.
Proof. intros. by apply core_id_total, singleton_core'. Qed.

Lemma singleton_included_l m i x :
  {[ i := x ]} ≼ m ↔ ∃ y, m !! i = Some y ∧ Some x ≼ Some y.
Proof.
  split.
  - intros [m' Hm']. apply (f_equal (fun m => m !! i)) in Hm'. revert Hm'. rewrite lookup_op lookup_singleton=> Hi.
    exists (x ⋅? m' !! i). rewrite -Some_op_opM.
    split; first done. apply cmra_included_l.
  - intros (y&Hi&[mz Hy]). exists (partial_alter (λ _, mz) i m).
    apply map_eq. intros j; destruct (decide (i = j)) as [->|].
    + by rewrite lookup_op lookup_singleton lookup_partial_alter Hi.
    + by rewrite lookup_op lookup_singleton_ne// lookup_partial_alter_ne// left_id.
Qed.
Lemma singleton_included_exclusive_l m i x :
  Exclusive x → ✓ m →
  {[ i := x ]} ≼ m ↔ m !! i = Some x.
Proof.
  intros ? Hm. rewrite singleton_included_l. split; last by eauto.
  intros (y&?&->%(Some_included_exclusive _)); eauto using lookup_valid_Some.
Qed.
Lemma singleton_included i x y :
  {[ i := x ]} ≼ ({[ i := y ]} : gmap K A) ↔ Some x ≼ Some y.
Proof.
  rewrite singleton_included_l. split.
  - intros (y'&Hi&?). rewrite lookup_insert in Hi. by rewrite Hi.
  - intros ?. exists y. by rewrite lookup_insert.
Qed.
Lemma singleton_included_total `{!CmraTotal A}  i x y :
  {[ i := x ]} ≼ ({[ i := y ]} : gmap K A) ↔ x ≼ y.
Proof. rewrite singleton_included Some_included_total. done. Qed.
Lemma singleton_included_mono i x y :
  x ≼ y → {[ i := x ]} ≼ ({[ i := y ]} : gmap K A).
Proof. intros Hincl. apply singleton_included, Some_included_mono. done. Qed.

Global Instance singleton_cancelable i x :
  Cancelable (Some x) → Cancelable {[ i := x ]}.
Proof.
  intros ? m1 m2 Hv EQ. refine (map_eq _ _ _)=>j. apply (f_equal (fun m => (m !! j))) in EQ. move: (Hv j) (EQ). rewrite !lookup_op.
  destruct (decide (i = j)) as [->|].
  - rewrite lookup_singleton. by apply cancelable.
  - rewrite lookup_singleton_ne //. repeat rewrite (left_id _). done.
Qed.

Global Instance gmap_cancelable (m : gmap K A) :
  (∀ x : A, IdFree x) → (∀ x : A, Cancelable x) → Cancelable m.
Proof.
  intros Id C m1 m2 ? EQ. refine (map_eq _ _ _)=>i. apply (cancelable (m !! i)); try rewrite -!lookup_op; try (done || apply _).
  by rewrite EQ.
Qed.

Lemma insert_op m1 m2 i x y :
  <[i:=x ⋅ y]>(m1 ⋅ m2) =  <[i:=x]>m1 ⋅ <[i:=y]>m2.
Proof. by rewrite (insert_merge (⋅) m1 m2 i (x ⋅ y) x y). Qed.

Lemma insert_updateP (P : A → Prop) (Q : gmap K A → Prop) m i x :
  x ~~>: P →
  (∀ y, P y → Q (<[i:=y]>m)) →
  <[i:=x]>m ~~>: Q.
Proof.
  intros Hx%option_updateP' HP; apply cmra_total_updateP=> mf Hm.
  destruct (Hx (Some (mf !! i))) as ([y|]&?&?); try done.
  { by generalize (Hm i); rewrite lookup_op; simplify_map_eq. }
  exists (<[i:=y]> m); split; first by auto.
  intros j; move: (Hm j)=>{Hm}; rewrite !lookup_op=>Hm.
  destruct (decide (i = j)); simplify_map_eq/=; auto.
Qed.
Lemma insert_updateP' (P : A → Prop) m i x :
  x ~~>: P → <[i:=x]>m ~~>: λ m', ∃ y, m' = <[i:=y]>m ∧ P y.
Proof. eauto using insert_updateP. Qed.
Lemma insert_update m i x y : x ~~> y → <[i:=x]>m ~~> <[i:=y]>m.
Proof. rewrite !cmra_update_updateP; eauto using insert_updateP with subst. Qed.

Lemma singleton_updateP (P : A → Prop) (Q : gmap K A → Prop) i x :
  x ~~>: P → (∀ y, P y → Q {[ i := y ]}) → {[ i := x ]} ~~>: Q.
Proof. apply insert_updateP. Qed.
Lemma singleton_updateP' (P : A → Prop) i x :
  x ~~>: P → {[ i := x ]} ~~>: λ m, ∃ y, m = {[ i := y ]} ∧ P y.
Proof. apply insert_updateP'. Qed.
Lemma singleton_update i (x y : A) : x ~~> y → {[ i := x ]} ~~> {[ i := y ]}.
Proof. apply insert_update. Qed.

Lemma delete_update m i : m ~~> delete i m.
Proof.
  apply cmra_total_update=> mf Hm j; destruct (decide (i = j)); subst.
  - move: (Hm j). rewrite !lookup_op lookup_delete left_id.
    apply cmra_valid_op_r.
  - move: (Hm j). by rewrite !lookup_op lookup_delete_ne.
Qed.

Lemma gmap_op_union m1 m2 : m1 ##ₘ m2 → m1 ⋅ m2 = m1 ∪ m2.
Proof.
  intros Hm. apply map_eq=> k. specialize (Hm k).
  rewrite lookup_op lookup_union. by destruct (m1 !! k), (m2 !! k).
Qed.

Lemma gmap_op_valid_disjoint m1 m2 :
  ✓ (m1 ⋅ m2) → (∀ k x, m1 !! k = Some x → Exclusive x) → m1 ##ₘ m2.
Proof.
  unfold Exclusive. intros Hvalid Hexcl k.
  specialize (Hvalid k). rewrite lookup_op in Hvalid. specialize (Hexcl k).
  destruct (m1 !! k), (m2 !! k); [|done..].
  rewrite -Some_op Some_valid in Hvalid. naive_solver.
Qed.

Lemma dom_op m1 m2 : dom (m1 ⋅ m2) = dom m1 ∪ dom m2.
Proof.
  apply set_eq=> i; rewrite elem_of_union !elem_of_dom.
  unfold is_Some; setoid_rewrite lookup_op.
  destruct (m1 !! i), (m2 !! i); naive_solver.
Qed.
Lemma dom_included m1 m2 : m1 ≼ m2 → dom m1 ⊆ dom m2.
Proof.
  rewrite lookup_included=>? i; rewrite !elem_of_dom. by apply is_Some_included.
Qed.

Section freshness.
  Local Set Default Proof Using "Type*".
  Context `{!Infinite K}.
  Lemma alloc_updateP_strong_dep (Q : gmap K A → Prop) (I : K → Prop) m (f : K → A) :
    pred_infinite I →
    (∀ i, m !! i = None → I i → ✓ (f i)) →
    (∀ i, m !! i = None → I i → Q (<[i:=f i]>m)) → m ~~>: Q.
  Proof.
    move=> /(pred_infinite_set I (C:=gset K)) HP ? HQ.
    apply cmra_total_updateP. intros mf Hm.
    destruct (HP (dom (m ⋅ mf))) as [i [Hi1 Hi2]].
    assert (m !! i = None).
    { eapply not_elem_of_dom. revert Hi2.
      rewrite dom_op not_elem_of_union. naive_solver. }
    exists (<[i:=f i]>m); split.
    - by apply HQ.
    - rewrite insert_singleton_op //.
      rewrite -assoc -insert_singleton_op; last by eapply not_elem_of_dom.
    apply insert_valid; auto.
  Qed.
  Lemma alloc_updateP_strong (Q : gmap K A → Prop) (I : K → Prop) m x :
    pred_infinite I →
    ✓ x → (∀ i, m !! i = None → I i → Q (<[i:=x]>m)) → m ~~>: Q.
  Proof.
    move=> HP ? HQ. eapply (alloc_updateP_strong_dep _ _ _ (λ _, x)); eauto.
  Qed.
  Lemma alloc_updateP (Q : gmap K A → Prop) m x :
    ✓ x → (∀ i, m !! i = None → Q (<[i:=x]>m)) → m ~~>: Q.
  Proof.
    move=>??.
    eapply (alloc_updateP_strong _ (λ _, True));
    eauto using pred_infinite_True.
  Qed.
  Lemma alloc_updateP_cofinite (Q : gmap K A → Prop) (J : gset K) m x :
    ✓ x → (∀ i, m !! i = None → i ∉ J → Q (<[i:=x]>m)) → m ~~>: Q.
  Proof.
    eapply alloc_updateP_strong.
    apply (pred_infinite_set (C:=gset K)).
    intros E. exists (fresh (J ∪ E)).
    apply not_elem_of_union, is_fresh.
  Qed.

  (* Variants without the universally quantified Q, for use in case that is an evar. *)
  Lemma alloc_updateP_strong_dep' m (f : K → A) (I : K → Prop) :
    pred_infinite I →
    (∀ i, m !! i = None → I i → ✓ (f i)) →
    m ~~>: λ m', ∃ i, I i ∧ m' = <[i:=f i]>m ∧ m !! i = None.
  Proof. eauto using alloc_updateP_strong_dep. Qed.
  Lemma alloc_updateP_strong' m x (I : K → Prop) :
    pred_infinite I →
    ✓ x → m ~~>: λ m', ∃ i, I i ∧ m' = <[i:=x]>m ∧ m !! i = None.
  Proof. eauto using alloc_updateP_strong. Qed.
  Lemma alloc_updateP' m x :
    ✓ x → m ~~>: λ m', ∃ i, m' = <[i:=x]>m ∧ m !! i = None.
  Proof. eauto using alloc_updateP. Qed.
  Lemma alloc_updateP_cofinite' m x (J : gset K) :
    ✓ x → m ~~>: λ m', ∃ i, i ∉ J ∧ m' = <[i:=x]>m ∧ m !! i = None.
  Proof. eauto using alloc_updateP_cofinite. Qed.
End freshness.

Lemma alloc_unit_singleton_updateP (P : A → Prop) (Q : gmap K A → Prop) u i :
  ✓ u → LeftId (=) u (⋅) →
  u ~~>: P → (∀ y, P y → Q {[ i := y ]}) → ∅ ~~>: Q.
Proof.
  intros ?? Hx HQ. apply cmra_total_updateP=> gf Hg.
  destruct (Hx (gf !! i)) as (y&?&Hy).
  { move:(Hg i). rewrite !left_id.
    case: (gf !! i)=>[x|]; rewrite /= ?left_id //.
  }
  exists {[ i := y ]}; split; first by auto.
  intros i'; destruct (decide (i' = i)) as [->|].
  - rewrite lookup_op lookup_singleton.
    move:Hy; case: (gf !! i)=>[x|]; rewrite /= ?right_id //.
  - move:(Hg i'). by rewrite !lookup_op lookup_singleton_ne // !left_id.
Qed.
Lemma alloc_unit_singleton_updateP' (P: A → Prop) u i :
  ✓ u → LeftId (=) u (⋅) →
  u ~~>: P → ∅ ~~>: λ m, ∃ y, m = {[ i := y ]} ∧ P y.
Proof. eauto using alloc_unit_singleton_updateP. Qed.
Lemma alloc_unit_singleton_update (u : A) i (y : A) :
  ✓ u → LeftId (=) u (⋅) → u ~~> y → (∅:gmap K A) ~~> {[ i := y ]}.
Proof.
  rewrite !cmra_update_updateP;
    eauto using alloc_unit_singleton_updateP with subst.
Qed.

Lemma gmap_local_update m1 m2 m1' m2' :
  (∀ i, (m1 !! i, m2 !! i) ~l~> (m1' !! i, m2' !! i)) →
  (m1, m2) ~l~> (m1', m2').
Proof.
  intros Hupd. apply local_update_unital=> mf Hmv Hm.
  unfold valid,cmra_valid,ucmra_cmraR,ucmra_valid. simpl.
  unfold gmap_valid_instance.
  assert (∀ i, ✓ (m1' !! i) ∧ m1' !! i = (m2' ⋅ mf) !! i) as PF.
  { intros i. rewrite lookup_op -cmra_opM_fmap_Some.
    apply Hupd; simpl; first done. by rewrite Hm lookup_op cmra_opM_fmap_Some.
  }
  split.
  - intros i. specialize (PF i) as [? _]. done.
  - refine (map_eq _ _ _). intros i. specialize (PF i) as [_ ?]. done.
Qed.

Lemma alloc_local_update m1 m2 i x :
  m1 !! i = None → ✓ x → (m1,m2) ~l~> (<[i:=x]>m1, <[i:=x]>m2).
Proof.
  intros Hi ?. apply gmap_local_update=> j.
  destruct (decide (i = j)) as [->|]; last by rewrite !lookup_insert_ne.
  rewrite !lookup_insert Hi. by apply alloc_option_local_update.
Qed.

Lemma alloc_singleton_local_update m i x :
  m !! i = None → ✓ x → (m,∅) ~l~> (<[i:=x]>m, {[ i:=x ]}).
Proof. apply alloc_local_update. Qed.

Lemma insert_local_update m1 m2 i x y x' y' :
  m1 !! i = Some x → m2 !! i = Some y →
  (x, y) ~l~> (x', y') →
  (m1, m2) ~l~> (<[i:=x']>m1, <[i:=y']>m2).
Proof.
  intros Hi1 Hi2 Hup. apply gmap_local_update=> j.
  destruct (decide (i = j)) as [->|]; last by rewrite !lookup_insert_ne.
  rewrite !lookup_insert Hi1 Hi2. by apply option_local_update.
Qed.

Lemma singleton_local_update_any m i y x' y' :
  (∀ x, m !! i = Some x → (x, y) ~l~> (x', y')) →
  (m, {[ i := y ]}) ~l~> (<[i:=x']>m, {[ i := y' ]}).
Proof.
  intros. apply gmap_local_update=> j.
  destruct (decide (i = j)) as [->|]; last by rewrite !lookup_insert_ne.
  rewrite !lookup_singleton lookup_insert.
  destruct (m !! j); first by eauto using option_local_update.
  apply local_update_total_valid=> _ _ /option_included; naive_solver.
Qed.

Lemma singleton_local_update m i x y x' y' :
  m !! i = Some x →
  (x, y) ~l~> (x', y') →
  (m, {[ i := y ]}) ~l~> (<[i:=x']>m, {[ i := y' ]}).
Proof.
  intros Hmi ?. apply singleton_local_update_any.
  intros x2. rewrite Hmi=>[=<-]. done.
Qed.

Lemma delete_local_update m1 m2 i x `{!Exclusive x} :
  m2 !! i = Some x → (m1, m2) ~l~> (delete i m1, delete i m2).
Proof.
  intros Hi. apply gmap_local_update=> j.
  destruct (decide (i = j)) as [->|]; last by rewrite !lookup_delete_ne.
  rewrite !lookup_delete Hi. by apply delete_option_local_update.
Qed.

Lemma delete_singleton_local_update m i x `{!Exclusive x} :
  (m, {[ i := x ]}) ~l~> (delete i m, ∅).
Proof.
  rewrite -(delete_singleton i x).
  by eapply delete_local_update, lookup_singleton.
Qed.

Lemma delete_local_update_cancelable m1 m2 i mx `{!Cancelable mx} :
  m1 !! i = mx → m2 !! i = mx →
  (m1, m2) ~l~> (delete i m1, delete i m2).
Proof.
  intros Hi1 Hi2. apply gmap_local_update=> j.
  destruct (decide (i = j)) as [->|]; last by rewrite !lookup_delete_ne.
  rewrite !lookup_delete Hi1 Hi2. by apply delete_option_local_update_cancelable.
Qed.

Lemma delete_singleton_local_update_cancelable m i x `{!Cancelable (Some x)} :
  m !! i = Some x → (m, {[ i := x ]}) ~l~> (delete i m, ∅).
Proof.
  intros. rewrite -(delete_singleton i x).
  apply (delete_local_update_cancelable m _ i (Some x));
    [done|by rewrite lookup_singleton].
Qed.

Lemma gmap_fmap_mono {B : cmra} (f : A → B) m1 m2 :
  Proper ((=) ==> (=)) f →
  (∀ x y, x ≼ y → f x ≼ f y) → m1 ≼ m2 → fmap f m1 ≼ fmap f m2.
Proof.
  intros ??. rewrite !lookup_included=> Hm i.
  rewrite !lookup_fmap. by apply option_fmap_mono.
Qed.

Lemma big_opM_singletons m :
  ([^op map] k ↦ x ∈ m, {[ k := x ]}) = m.
Proof.
  (* We are breaking the big_opM abstraction here. The reason is that [map_ind]
     is too weak: we need an induction principle that visits all the keys in the
     right order, namely the order in which they appear in map_to_list.  Here,
     we achieve this by unfolding [big_opM] and doing induction over that list
     instead. *)
  rewrite big_op.big_opM_unseal /big_op.big_opM_def -{2}(list_to_map_to_list m).
  assert (NoDup (map_to_list m).*1) as Hnodup by apply NoDup_fst_map_to_list.
  revert Hnodup. induction (map_to_list m) as [|[k x] l IH]; csimpl; first done.
  intros [??]%NoDup_cons. rewrite IH //.
  rewrite insert_singleton_op ?not_elem_of_list_to_map_1 //.
Qed.

End properties.

Section unital_properties.
Context `{Countable K} {A : ucmra}.
Implicit Types m : gmap K A.
Implicit Types i : K.
Implicit Types x y : A.

Lemma insert_alloc_local_update m1 m2 i x x' y' :
  m1 !! i = Some x → m2 !! i = None →
  (x, ε) ~l~> (x', y') →
  (m1, m2) ~l~> (<[i:=x']>m1, <[i:=y']>m2).
Proof.
  intros Hi1 Hi2 Hup. apply local_update_unital=> mf Hm1v Hm.
  assert (mf !! i = Some x) as Hif.
  { apply (f_equal (fun m => m !! i)) in Hm. revert Hm. by rewrite lookup_op Hi1 Hi2 left_id. }
  destruct (Hup (mf !! i)) as [Hx'v Hx'eq].
  { move: (Hm1v i). by rewrite Hi1. }
  { by rewrite Hif -(inj_iff Some) -Some_op_opM -Some_op left_id. }
  split.
  - by apply insert_valid.
  - simpl in Hx'eq. by rewrite -(insert_id mf i x) // -insert_op -Hm Hx'eq Hif.
Qed.
End unital_properties.

(** Functor *)
Global Instance gmap_fmap_ne `{Countable K} {A B : Type} (f : A → B) :
  Proper (eq ==> eq) f → Proper (eq ==> eq) (fmap (M:=gmap K) f).
Proof. by intros ? m m' Hm; apply map_eq=>k; rewrite !lookup_fmap Hm. Qed.
Lemma gmap_fmap_ne_ext `{Countable K}
  {A : Type} {B : Type} (f1 f2 : A → B) (m : gmap K A) :
  (∀ i x, m !! i = Some x → f1 x = f2 x) →
  f1 <$> m = f2 <$> m.
Proof.
  move => Hf. apply map_eq=>i.
  rewrite !lookup_fmap.
  destruct (m !! i) eqn:?; eauto. simpl. f_equal. by eapply Hf.
Qed.
(* Global Instance gmap_fmap_cmra_morphism `{Countable K} {A B : cmra} (f : A → B)
  `{!CmraMorphism f} : CmraMorphism (fmap f : gmap K A → gmap K B).
Proof.
  split; try apply _.
  - by intros m ? i; rewrite lookup_fmap; apply (cmra_morphism_valid _).
  - intros m. Print omap. apply (@Some_proper _ (=)). rewrite lookup_fmap !lookup_omap lookup_fmap.
    case: (m!!i)=>//= ?. apply cmra_morphism_pcore, _.
  - intros m1 m2 i. by rewrite lookup_op !lookup_fmap lookup_op cmra_morphism_op.
Qed.
Definition gmapO_map `{Countable K} {A B} (f: A -n> B) :
  gmapO K A -n> gmapO K B := OfeMor (fmap f : gmapO K A → gmapO K B).
Global Instance gmapO_map_ne `{Countable K} {A B} :
  NonExpansive (@gmapO_map K _ _ A B).
Proof.
  intros n f g Hf m k; rewrite /= !lookup_fmap.
  destruct (_ !! k) eqn:?; simpl; constructor; apply Hf.
Qed.

Program Definition gmapOF K `{Countable K} (F : oFunctor) : oFunctor := {|
  oFunctor_car A _ B _ := gmapO K (oFunctor_car F A B);
  oFunctor_map A1 _ A2 _ B1 _ B2 _ fg := gmapO_map (oFunctor_map F fg)
|}.
Next Obligation.
  by intros K ?? F A1 ? A2 ? B1 ? B2 ? n f g Hfg; apply gmapO_map_ne, oFunctor_map_ne.
Qed.
Next Obligation.
  intros K ?? F A ? B ? x. rewrite /= -{2}(map_fmap_id x).
  apply map_fmap_equiv_ext=>y ??; apply oFunctor_map_id.
Qed.
Next Obligation.
  intros K ?? F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x. rewrite /= -map_fmap_compose.
  apply map_fmap_equiv_ext=>y ??; apply oFunctor_map_compose.
Qed.
Global Instance gmapOF_contractive K `{Countable K} F :
  oFunctorContractive F → oFunctorContractive (gmapOF K F).
Proof.
  by intros ? A1 ? A2 ? B1 ? B2 ? n f g Hfg; apply gmapO_map_ne, oFunctor_map_contractive.
Qed.

Program Definition gmapURF K `{Countable K} (F : rFunctor) : urFunctor := {|
  urFunctor_car A _ B _ := gmapUR K (rFunctor_car F A B);
  urFunctor_map A1 _ A2 _ B1 _ B2 _ fg := gmapO_map (rFunctor_map F fg)
|}.
Next Obligation.
  by intros K ?? F A1 ? A2 ? B1 ? B2 ? n f g Hfg; apply gmapO_map_ne, rFunctor_map_ne.
Qed.
Next Obligation.
  intros K ?? F A ? B ? x. rewrite /= -{2}(map_fmap_id x).
  apply map_fmap_equiv_ext=>y ??; apply rFunctor_map_id.
Qed.
Next Obligation.
  intros K ?? F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x. rewrite /= -map_fmap_compose.
  apply map_fmap_equiv_ext=>y ??; apply rFunctor_map_compose.
Qed.
Global Instance gmapURF_contractive K `{Countable K} F :
  rFunctorContractive F → urFunctorContractive (gmapURF K F).
Proof.
  by intros ? A1 ? A2 ? B1 ? B2 ? n f g Hfg; apply gmapO_map_ne, rFunctor_map_contractive.
Qed.

Program Definition gmapRF K `{Countable K} (F : rFunctor) : rFunctor := {|
  rFunctor_car A _ B _ := gmapR K (rFunctor_car F A B);
  rFunctor_map A1 _ A2 _ B1 _ B2 _ fg := gmapO_map (rFunctor_map F fg)
|}.
Solve Obligations with apply gmapURF.

Global Instance gmapRF_contractive K `{Countable K} F :
  rFunctorContractive F → rFunctorContractive (gmapRF K F).
Proof. apply gmapURF_contractive. Qed. *)
