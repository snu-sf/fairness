From iris.algebra Require Export cmra updates.
From iris.bi Require Import notation.
From iris.prelude Require Import options.

Local Hint Extern 1 (_ ≼ _) => etrans; [eassumption|] : core.
Local Hint Extern 1 (_ ≼ _) => etrans; [|eassumption] : core.
Local Hint Extern 10 (_ ≤ _) => lia : core.

(** The basic definition of the uPred type, its metric and functor laws.
    You probably do not want to import this file. Instead, import
    base_logic.base_logic; that will also give you all the primitive
    and many derived laws for the logic. *)

(** A good way of understanding this definition of the uPred OFE is to
   consider the OFE uPred0 of monotonous SProp predicates. That is,
   uPred0 is the OFE of non-expansive functions from M to SProp that
   are monotonous with respect to CMRA inclusion. This notion of
   monotonicity has to be stated in the SProp logic. Together with the
   usual closedness property of SProp, this gives exactly uPred_mono.

   Then, we quotient uPred0 *in the siProp logic* with respect to
   equivalence on valid elements of M. That is, we quotient with
   respect to the following *siProp* equivalence relation:
     P1 ≡ P2 := ∀ x, ✓ x → (P1(x) ↔ P2(x))       (1)
   When seen from the ambiant logic, obtaining this quotient requires
   definig both a custom Equiv and Dist.


   It is worth noting that this equivalence relation admits canonical
   representatives. More precisely, one can show that every
   equivalence class contains exactly one element P0 such that:
     ∀ x, (✓ x → P0(x)) → P0(x)                 (2)
   (Again, this assertion has to be understood in siProp). Intuitively,
   this says that P0 trivially holds whenever the resource is invalid.
   Starting from any element P, one can find this canonical
   representative by choosing:
     P0(x) := ✓ x → P(x)                        (3)

   Hence, as an alternative definition of uPred, we could use the set
   of canonical representatives (i.e., the subtype of monotonous
   siProp predicates that verify (2)). This alternative definition would
   save us from using a quotient. However, the definitions of the various
   connectives would get more complicated, because we have to make sure
   they all verify (2), which sometimes requires some adjustments. We
   would moreover need to prove one more property for every logical
   connective.
 *)

(** Note that, somewhat curiously, [uPred M] is *not* in general a Camera,
   at least not if all propositions are considered "valid" Camera elements.
   It fails to satisfy the extension axiom. Here is the counterexample:

We use [M := (option Ex {A,B})^2] -- so we have pairs
whose components are ε, A or B.

Let
[[
  P r n := (ownM (A,A) ∧ ▷ False) ∨ ownM (A,B) ∨ ownM (B,A) ∨ ownM (B,B)
         ↔ r = (A,A) ∧ n = 0 ∨
           r = (A,B) ∨
           r = (B,A) ∨
           r = (B,B)
 Q1 r n := ownM (A, ε) ∨ ownM (B, ε)
         ↔ (A, ε) ≼ r ∨ (B, ε) ≼ r
           ("Left component is not ε")
 Q2 r n := ownM (ε, A) ∨ ownM (ε, B)
         ↔ (ε, A) ≼ r ∨ (ε, B) ≼ r
           ("Right component is not ε")
]]
These are all sufficiently closed and non-expansive and whatnot.
We have [P ≡{0}≡ Q1 * Q2]. So assume extension holds, then we get Q1', Q2'
such that
[[
  P ≡ Q1' ∗ Q2'
 Q1 ≡{0}≡ Q1'
 Q2 ≡{0}≡ Q2'
]]
Now comes the contradiction:
We know that [P (A,A) 1] does *not* hold, but I am going to show that
[(Q1' ∗ Q2') (A,A) 1] holds, which would be a contraction.
To this end, I will show (a) [Q1' (A,ε) 1] and (b) [Q2' (ε,A) 1].
The result [(Q1' ∗ Q2') (A,A)] follows from [(A,ε) ⋅ (ε,A) = (A,A)].

(a) Proof of [Q1' (A,ε) 1].
    We have [P (A,B) 1], and thus [Q1' r1 1] and [Q2' r2 1] for some
    [r1 ⋅ r2 = (A,B)]. There are four possible decompositions [r1 ⋅ r2]:
    - [(ε,ε) ⋅ (A,B)]: This would give us [Q1' (ε,ε) 1], from which we
      obtain (through down-closure and the equality [Q1 ≡{0}≡ Q1'] above) that
      [Q1 (ε,ε) 0]. However, we know that's false.
    - [(A,B) ⋅ (ε,ε)]: Can be excluded for similar reasons
      (the second resource must not be ε in the 2nd component).
    - [(ε,B) ⋅ (A,ε)]: Can be excluded for similar reasons
      (the first resource must not be ε in the 1st component).
    - [(A,ε) ⋅ (ε,B)]: This gives us the desired [Q1' (A,ε) 1].

(b) Proof of [Q2' (ε,A) 1].
    We have [P (B,A) 1], and thus [Q1' r1 1] and [Q2' r2 1] for some
    [r1 ⋅ r2 = (B,A)]. There are again four possible decompositions,
    and like above we can exclude three of them. This leaves us with
    [(B,ε) ⋅ (ε,A)] and thus [Q2' (ε,A) 1].

This completes the proof.

*)

Record uPred (M : ucmra) : Type := UPred {
  uPred_holds : M → Prop;

  uPred_mono x1 x2 :
    uPred_holds x1 → x1 ≼ x2 → uPred_holds x2
}.
(** When working in the model, it is convenient to be able to treat [uPred] as
[M → Prop].  But we only want to locally break the [uPred] abstraction
this way. *)
Local Coercion uPred_holds : uPred >-> Funclass.
Bind Scope bi_scope with uPred.
Global Arguments uPred_holds {_} _ _ : simpl never.
Add Printing Constructor uPred.
Global Instance: Params (@uPred_holds) 2 := {}.

Section cofe.
  Context {M : ucmra}.

  Inductive uPred_equiv' (P Q : uPred M) : Prop :=
    { uPred_in_equiv : ∀ x, ✓ x → P x ↔ Q x }.
  Local Instance uPred_equiv : Equiv (uPred M) := uPred_equiv'.
  Inductive uPred_dist' (P Q : uPred M) : Prop :=
    { uPred_in_dist : ∀ x, ✓ x → P x ↔ Q x }.
  Local Instance uPred_dist : Dist (uPred M) :=λ n, uPred_dist'.
  Definition uPred_ofe_mixin : OfeMixin (uPred M).
  Proof.
    split.
    - intros P Q; split.
      + by intros HPQ n; split=> x ?; apply HPQ.
      + intros HPQ; split=> x ?; apply (HPQ 0); auto.
    - intros; split.
      + by intros P; split=> x i.
      + by intros P Q HPQ; split=> x ?; symmetry; apply HPQ.
      + intros P Q Q' HP HQ; split=> x ?.
        by trans (Q x);[apply HP|apply HQ].
    - intros n m P Q HPQ. split=> x ?; apply HPQ. eauto with lia.
  Qed.
  Canonical Structure uPredO : ofe := Ofe (uPred M) uPred_ofe_mixin.

  Program Definition uPred_compl : Compl uPredO := λ c,
    {| uPred_holds x := ✓ x → c 0 x |}.
  Next Obligation.
    move=> /= c x1 x2 HP Hx12 Hv. eapply uPred_mono.
    - eapply HP, cmra_valid_included=>//.
    - done.
  Qed.
  Global Program Instance uPred_cofe : Cofe uPredO := {| compl := uPred_compl |}.
  Next Obligation.
    intros n c.
    etrans; [|by symmetry; apply (chain_cauchy c 0 n); lia]. split=> x H. split=>H'; [by apply H'|].
    repeat intro. done.
  Qed.
End cofe.
Global Arguments uPredO : clear implicits.

(* Global Instance uPred_ne {M} (P : uPred M) n : Proper (dist n ==> iff) (P n).
Proof.
  intros x1 x2 Hx; split=> ?; eapply uPred_mono; eauto; by rewrite Hx.
Qed. *)
Global Instance uPred_proper {M} (P : uPred M) : Proper ((≡) ==> iff) P.
Proof. intros x1 x2 Hx; split => ?; eapply uPred_mono; eauto; by rewrite Hx. Qed.

Lemma uPred_holds_ne {M} (P Q : uPred M) x :
  P ≡ Q → ✓ x → Q x → P x.
Proof.
  intros [Hne] ??. eapply Hne; try done.
Qed.

(* Equivalence to the definition of uPred in the appendix. *)
(* Lemma uPred_alt {M : ucmra} (P: nat → M → Prop) :
  (∀ n1 n2 x1 x2, P n1 x1 → x1 ≼{n1} x2 → n2 ≤ n1 → P n2 x2) ↔
  ( (∀ x n1 n2, n2 ≤ n1 → P n1 x → P n2 x) (* Pointwise down-closed *)
  ∧ (∀ n x1 x2, x1 ≡{n}≡ x2 → ∀ m, m ≤ n → P m x1 ↔ P m x2) (* Non-expansive *)
  ∧ (∀ n x1 x2, x1 ≼{n} x2 → ∀ m, m ≤ n → P m x1 → P m x2) (* Monotonicity *)
  ).
Proof.
  (* Provide this lemma to eauto. *)
  assert (∀ n1 n2 (x1 x2 : M), n2 ≤ n1 → x1 ≡{n1}≡ x2 → x1 ≼{n2} x2).
  { intros ????? H. eapply cmra_includedN_le; last done. by rewrite H. }
  (* Now go ahead. *)
  split.
  - intros Hupred. repeat split; eauto using cmra_includedN_le.
  - intros (Hdown & _ & Hmono) **. eapply Hmono; [done..|]. eapply Hdown; done.
Qed. *)

(** functor *)
(* Program Definition uPred_map {M1 M2 : ucmra} (f : M2 -n> M1)
  `{!CmraMorphism f} (P : uPred M1) :
  uPred M2 := {| uPred_holds n x := P n (f x) |}.
Next Obligation. naive_solver eauto using uPred_mono, cmra_morphism_monotoneN. Qed. *)

(* Global Instance uPred_map_ne {M1 M2 : ucmra} (f : M2 -n> M1)
  `{!CmraMorphism f} n : Proper (dist n ==> dist n) (uPred_map f).
Proof.
  intros x1 x2 Hx; split=> n' y ??.
  split; apply Hx; auto using cmra_morphism_validN.
Qed. *)
(* Lemma uPred_map_id {M : ucmra} (P : uPred M): uPred_map cid P ≡ P.
Proof. by split=> n x ?. Qed. *)
(* Lemma uPred_map_compose {M1 M2 M3 : ucmra} (f : M1 -n> M2) (g : M2 -n> M3)
    `{!CmraMorphism f, !CmraMorphism g} (P : uPred M3):
  uPred_map (g ◎ f) P ≡ uPred_map f (uPred_map g P).
Proof. by split=> n x Hx. Qed. *)
(* Lemma uPred_map_ext {M1 M2 : ucmra} (f g : M1 -n> M2)
      `{!CmraMorphism f} `{!CmraMorphism g}:
  (∀ x, f x ≡ g x) → ∀ x, uPred_map f x ≡ uPred_map g x.
Proof. intros Hf P; split=> n x Hx /=; by rewrite /uPred_holds /= Hf. Qed. *)
(* Definition uPredO_map {M1 M2 : ucmra} (f : M2 -n> M1) `{!CmraMorphism f} :
  uPredO M1 -n> uPredO M2 := OfeMor (uPred_map f : uPredO M1 → uPredO M2). *)
(* Lemma uPredO_map_ne {M1 M2 : ucmra} (f g : M2 -n> M1)
    `{!CmraMorphism f, !CmraMorphism g} n :
  f ≡{n}≡ g → uPredO_map f ≡{n}≡ uPredO_map g.
Proof.
  by intros Hfg P; split=> n' y ??;
    rewrite /uPred_holds /= (dist_le _ _ _ _(Hfg y)); last lia.
Qed. *)

(* Program Definition uPredOF (F : urFunctor) : oFunctor := {|
  oFunctor_car A _ B _ := uPredO (urFunctor_car F B A);
  oFunctor_map A1 _ A2 _ B1 _ B2 _ fg := uPredO_map (urFunctor_map F (fg.2, fg.1))
|}.
Next Obligation.
  intros F A1 ? A2 ? B1 ? B2 ? n P Q HPQ.
  apply uPredO_map_ne, urFunctor_map_ne; split; by apply HPQ.
Qed.
Next Obligation.
  intros F A ? B ? P; simpl. rewrite -{2}(uPred_map_id P).
  apply uPred_map_ext=>y. by rewrite urFunctor_map_id.
Qed.
Next Obligation.
  intros F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' P; simpl. rewrite -uPred_map_compose.
  apply uPred_map_ext=>y; apply urFunctor_map_compose.
Qed. *)

(* Global Instance uPredOF_contractive F :
  urFunctorContractive F → oFunctorContractive (uPredOF F).
Proof.
  intros ? A1 ? A2 ? B1 ? B2 ? n P Q HPQ.
  apply uPredO_map_ne, urFunctor_map_contractive.
  destruct HPQ as [HPQ]. constructor. intros ??.
  split; by eapply HPQ.
Qed. *)

(** logical entailement *)
Inductive uPred_entails {M} (P Q : uPred M) : Prop :=
  { uPred_in_entails : ∀ x, ✓ x → P x → Q x }.
Global Hint Resolve uPred_mono : uPred_def.

(** logical connectives *)
Local Program Definition uPred_pure_def {M} (φ : Prop) : uPred M :=
  {| uPred_holds x := φ |}.
Solve Obligations with done.
Local Definition uPred_pure_aux : seal (@uPred_pure_def). Proof. by eexists. Qed.
Definition uPred_pure := uPred_pure_aux.(unseal).
Global Arguments uPred_pure {M}.
Local Definition uPred_pure_unseal :
  @uPred_pure = @uPred_pure_def := uPred_pure_aux.(seal_eq).

Local Program Definition uPred_and_def {M} (P Q : uPred M) : uPred M :=
  {| uPred_holds x := P x ∧ Q x |}.
Solve Obligations with naive_solver eauto 2 with uPred_def.
Local Definition uPred_and_aux : seal (@uPred_and_def). Proof. by eexists. Qed.
Definition uPred_and := uPred_and_aux.(unseal).
Global Arguments uPred_and {M}.
Local Definition uPred_and_unseal :
  @uPred_and = @uPred_and_def := uPred_and_aux.(seal_eq).

Local Program Definition uPred_or_def {M} (P Q : uPred M) : uPred M :=
  {| uPred_holds x := P x ∨ Q x |}.
Solve Obligations with naive_solver eauto 2 with uPred_def.
Local Definition uPred_or_aux : seal (@uPred_or_def). Proof. by eexists. Qed.
Definition uPred_or := uPred_or_aux.(unseal).
Global Arguments uPred_or {M}.
Local Definition uPred_or_unseal :
  @uPred_or = @uPred_or_def := uPred_or_aux.(seal_eq).

Local Program Definition uPred_impl_def {M} (P Q : uPred M) : uPred M :=
  {| uPred_holds x := ∀ x',
       x ≼ x' → ✓ x' → P x' → Q x' |}.
Next Obligation.
  intros M P Q x1 x1' HPQ [x2 Hx1'] x3 [x4 Hx3]; simpl in *.
  rewrite Hx3 Hx1'; auto. intros ??.
  eapply HPQ; auto. exists (x2 ⋅ x4); by rewrite assoc.
Qed.
Local Definition uPred_impl_aux : seal (@uPred_impl_def). Proof. by eexists. Qed.
Definition uPred_impl := uPred_impl_aux.(unseal).
Global Arguments uPred_impl {M}.
Local Definition uPred_impl_unseal :
  @uPred_impl = @uPred_impl_def := uPred_impl_aux.(seal_eq).

Local Program Definition uPred_forall_def {M A} (Ψ : A → uPred M) : uPred M :=
  {| uPred_holds x := ∀ a, Ψ a x |}.
Solve Obligations with naive_solver eauto 2 with uPred_def.
Local Definition uPred_forall_aux : seal (@uPred_forall_def). Proof. by eexists. Qed.
Definition uPred_forall := uPred_forall_aux.(unseal).
Global Arguments uPred_forall {M A}.
Local Definition uPred_forall_unseal :
  @uPred_forall = @uPred_forall_def := uPred_forall_aux.(seal_eq).

Local Program Definition uPred_exist_def {M A} (Ψ : A → uPred M) : uPred M :=
  {| uPred_holds x := ∃ a, Ψ a x |}.
Solve Obligations with naive_solver eauto 2 with uPred_def.
Local Definition uPred_exist_aux : seal (@uPred_exist_def). Proof. by eexists. Qed.
Definition uPred_exist := uPred_exist_aux.(unseal).
Global Arguments uPred_exist {M A}.
Local Definition uPred_exist_unseal :
  @uPred_exist = @uPred_exist_def := uPred_exist_aux.(seal_eq).

Local Program Definition uPred_internal_eq_def {M} {A : ofe} (a1 a2 : A) : uPred M :=
  {| uPred_holds x := a1 ≡ a2 |}.
Solve Obligations with naive_solver eauto 2 using dist_le.
Local Definition uPred_internal_eq_aux : seal (@uPred_internal_eq_def).
Proof. by eexists. Qed.
Definition uPred_internal_eq := uPred_internal_eq_aux.(unseal).
Global Arguments uPred_internal_eq {M A}.
Local Definition uPred_internal_eq_unseal :
  @uPred_internal_eq = @uPred_internal_eq_def := uPred_internal_eq_aux.(seal_eq).

Local Program Definition uPred_sep_def {M} (P Q : uPred M) : uPred M :=
  {| uPred_holds x := ∃ x1 x2, x ≡ x1 ⋅ x2 ∧ P x1 ∧ Q x2 |}.
Next Obligation.
  intros M P Q x y (x1&x2&Hx&?&?) [z Hy].
  exists x1, (x2 ⋅ z); split_and?; eauto using uPred_mono, cmra_included_l.
  rewrite Hy. by rewrite Hx assoc.
Qed.
Local Definition uPred_sep_aux : seal (@uPred_sep_def). Proof. by eexists. Qed.
Definition uPred_sep := uPred_sep_aux.(unseal).
Global Arguments uPred_sep {M}.
Local Definition uPred_sep_unseal :
  @uPred_sep = @uPred_sep_def := uPred_sep_aux.(seal_eq).

Local Program Definition uPred_wand_def {M} (P Q : uPred M) : uPred M :=
  {| uPred_holds x := ∀ x',
       ✓ (x ⋅ x') → P x' → Q (x ⋅ x') |}.
Next Obligation.
  intros M P Q x1 x1' HPQ ? x3 ??; simpl in *.
  eapply uPred_mono with (x1 ⋅ x3);
    eauto using cmra_valid_included, cmra_mono_r.
Qed.
Local Definition uPred_wand_aux : seal (@uPred_wand_def). Proof. by eexists. Qed.
Definition uPred_wand := uPred_wand_aux.(unseal).
Global Arguments uPred_wand {M}.
Local Definition uPred_wand_unseal :
  @uPred_wand = @uPred_wand_def := uPred_wand_aux.(seal_eq).

(* Equivalently, this could be `∀ y, P y`.  That's closer to the intuition
   of "embedding the step-indexed logic in Iris", but the two are equivalent
   because Iris is afine.  The following is easier to work with. *)
Local Program Definition uPred_plainly_def {M} (P : uPred M) : uPred M :=
  {| uPred_holds x := P ε |}.
Solve Obligations with naive_solver eauto using uPred_mono, ucmra_unit_valid.
Local Definition uPred_plainly_aux : seal (@uPred_plainly_def). Proof. by eexists. Qed.
Definition uPred_plainly := uPred_plainly_aux.(unseal).
Global Arguments uPred_plainly {M}.
Local Definition uPred_plainly_unseal :
  @uPred_plainly = @uPred_plainly_def := uPred_plainly_aux.(seal_eq).

Local Program Definition uPred_persistently_def {M} (P : uPred M) : uPred M :=
  {| uPred_holds x := P (core x) |}.
Solve Obligations with naive_solver eauto using uPred_mono, cmra_core_mono.
Local Definition uPred_persistently_aux : seal (@uPred_persistently_def).
Proof. by eexists. Qed.
Definition uPred_persistently := uPred_persistently_aux.(unseal).
Global Arguments uPred_persistently {M}.
Local Definition uPred_persistently_unseal :
  @uPred_persistently = @uPred_persistently_def := uPred_persistently_aux.(seal_eq).

Local Program Definition uPred_later_def {M} (P : uPred M) : uPred M := P.
Local Definition uPred_later_aux : seal (@uPred_later_def). Proof. by eexists. Qed.
Definition uPred_later := uPred_later_aux.(unseal).
Global Arguments uPred_later {M}.
Local Definition uPred_later_unseal :
  @uPred_later = @uPred_later_def := uPred_later_aux.(seal_eq).

Local Program Definition uPred_ownM_def {M : ucmra} (a : M) : uPred M :=
  {| uPred_holds x := a ≼ x |}.
Next Obligation.
  intros M a x1 x [a' Hx1] [x2 Hx].
  exists (a' ⋅ x2). rewrite Hx (assoc op) -Hx1 //.
Qed.
Local Definition uPred_ownM_aux : seal (@uPred_ownM_def). Proof. by eexists. Qed.
Definition uPred_ownM := uPred_ownM_aux.(unseal).
Global Arguments uPred_ownM {M}.
Local Definition uPred_ownM_unseal :
  @uPred_ownM = @uPred_ownM_def := uPred_ownM_aux.(seal_eq).

Local Program Definition uPred_cmra_valid_def {M} {A : cmra} (a : A) : uPred M :=
  {| uPred_holds x := ✓ a |}.
Solve Obligations with naive_solver eauto 2.
Local Definition uPred_cmra_valid_aux : seal (@uPred_cmra_valid_def).
Proof. by eexists. Qed.
Definition uPred_cmra_valid := uPred_cmra_valid_aux.(unseal).
Global Arguments uPred_cmra_valid {M A}.
Local Definition uPred_cmra_valid_unseal :
  @uPred_cmra_valid = @uPred_cmra_valid_def := uPred_cmra_valid_aux.(seal_eq).

Local Program Definition uPred_bupd_def {M} (Q : uPred M) : uPred M :=
  {| uPred_holds x := ∀ yf,
      ✓ (x ⋅ yf) → ∃ x', ✓ (x' ⋅ yf) ∧ Q x' |}.
Next Obligation.
  intros M Q x1 x2 HQ [x3 Hx] yf.
  rewrite Hx. intros Hxy.
  destruct (HQ (x3 ⋅ yf)) as (x'&?&?); [by rewrite assoc|].
  exists (x' ⋅ x3); split; first by rewrite -assoc.
  eauto using uPred_mono, cmra_included_l.
Qed.
Local Definition uPred_bupd_aux : seal (@uPred_bupd_def). Proof. by eexists. Qed.
Definition uPred_bupd := uPred_bupd_aux.(unseal).
Global Arguments uPred_bupd {M}.
Local Definition uPred_bupd_unseal :
  @uPred_bupd = @uPred_bupd_def := uPred_bupd_aux.(seal_eq).

(** Global uPred-specific Notation *)
Notation "✓ x" := (uPred_cmra_valid x) (at level 20) : bi_scope.

(** Primitive logical rules.
    These are not directly usable later because they do not refer to the BI
    connectives. *)
Module uPred_primitive.
Local Definition uPred_unseal :=
  (uPred_pure_unseal, uPred_and_unseal, uPred_or_unseal, uPred_impl_unseal,
  uPred_forall_unseal, uPred_exist_unseal, uPred_internal_eq_unseal,
  uPred_sep_unseal, uPred_wand_unseal, uPred_plainly_unseal,
  uPred_persistently_unseal, uPred_later_unseal, uPred_ownM_unseal,
  uPred_cmra_valid_unseal, @uPred_bupd_unseal).
Ltac unseal :=
  rewrite !uPred_unseal /=.

Section primitive.
  Context {M : ucmra}.
  Implicit Types φ : Prop.
  Implicit Types P Q : uPred M.
  Implicit Types A : Type.
  Local Arguments uPred_holds {_} _ _ /.
  Local Hint Immediate uPred_in_entails : core.

  (** The notations below are implicitly local due to the section, so we do not
  mind the overlap with the general BI notations. *)
  Notation "P ⊢ Q" := (@uPred_entails M P%I Q%I) : stdpp_scope.
  Notation "(⊢)" := (@uPred_entails M) (only parsing) : stdpp_scope.
  Notation "P ⊣⊢ Q" := (@uPred_equiv M P%I Q%I) : stdpp_scope.
  Notation "(⊣⊢)" := (@uPred_equiv M) (only parsing) : stdpp_scope.

  Notation "'True'" := (uPred_pure True) : bi_scope.
  Notation "'False'" := (uPred_pure False) : bi_scope.
  Notation "'⌜' φ '⌝'" := (uPred_pure φ%type%stdpp) : bi_scope.
  Infix "∧" := uPred_and : bi_scope.
  Infix "∨" := uPred_or : bi_scope.
  Infix "→" := uPred_impl : bi_scope.
  Notation "∀ x .. y , P" :=
    (uPred_forall (λ x, .. (uPred_forall (λ y, P)) ..)) : bi_scope.
  Notation "∃ x .. y , P" :=
    (uPred_exist (λ x, .. (uPred_exist (λ y, P)) ..)) : bi_scope.
  Infix "∗" := uPred_sep : bi_scope.
  Infix "-∗" := uPred_wand : bi_scope.
  Notation "□ P" := (uPred_persistently P) : bi_scope.
  Notation "■ P" := (uPred_plainly P) : bi_scope.
  Notation "x ≡ y" := (uPred_internal_eq x y) : bi_scope.
  Notation "▷ P" := (uPred_later P) : bi_scope.
  Notation "|==> P" := (uPred_bupd P) : bi_scope.

  (** Entailment *)
  Lemma entails_po : PreOrder (⊢).
  Proof.
    split.
    - by intros P; split=> x.
    - by intros P Q Q' HP HQ; split=> x ??; apply HQ, HP.
  Qed.
  Lemma entails_anti_sym : AntiSymm (⊣⊢) (⊢).
  Proof. intros P Q HPQ HQP; split=> x; by split; [apply HPQ|apply HQP]. Qed.
  Lemma equiv_entails P Q : (P ⊣⊢ Q) ↔ (P ⊢ Q) ∧ (Q ⊢ P).
  Proof.
    split.
    - intros HPQ; split; split=> x; apply HPQ.
    - intros [??]. exact: entails_anti_sym.
  Qed.
  Lemma entails_lim (cP cQ : chain (uPredO M)) :
    (∀ n, cP n ⊢ cQ n) → compl cP ⊢ compl cQ.
  Proof.
    intros Hlim; split=> n m Hyp HP.
    eapply uPred_holds_ne, Hlim, Hyp, HP; eauto.
  Qed.

  (** Non-expansiveness and setoid morphisms *)
  Lemma pure_ne n : Proper (iff ==> dist n) (@uPred_pure M).
  Proof. intros φ1 φ2 Hφ. by unseal; split=> ? ?; try apply Hφ. Qed.

  Lemma and_ne : NonExpansive2 (@uPred_and M).
  Proof.
    intros n P P' HP Q Q' HQ; unseal; split=> x ?.
    split; (intros [??]; split; [by apply HP|by apply HQ]).
  Qed.

  Lemma or_ne : NonExpansive2 (@uPred_or M).
  Proof.
    intros n P P' HP Q Q' HQ; split=> x ?.
    unseal; split; (intros [?|?]; [left; by apply HP|right; by apply HQ]).
  Qed.

  Lemma impl_ne :
    NonExpansive2 (@uPred_impl M).
  Proof.
    intros n P P' HP Q Q' HQ; split=> x ?.
    unseal; split; intros HPQ x' ???; apply HQ, HPQ, HP; auto.
  Qed.

  Lemma sep_ne : NonExpansive2 (@uPred_sep M).
  Proof.
    intros n P P' HP Q Q' HQ; split=> x Hx.
    unseal; split; intros (x1&x2&EQ&?&?); ofe_subst x;
      exists x1, x2; split_and!; try (apply HP || apply HQ);
      rewrite EQ in Hx;
      eauto using cmra_valid_op_l, cmra_valid_op_r.
  Qed.

  Lemma wand_ne :
    NonExpansive2 (@uPred_wand M).
  Proof.
    intros n P P' HP Q Q' HQ; split=> x ?; unseal; split; intros HPQ x' ??;
      apply HQ, HPQ, HP; eauto using cmra_valid_op_r.
  Qed.

  Lemma internal_eq_ne (A : ofe) :
    Proper ((≡)==>(≡)==>(≡)) (@uPred_internal_eq M A).
  Proof.
    intros x x' Hx y y' Hy; split=> z; unseal; split; intros; simpl in *.
    - by rewrite -Hx -?Hy; auto.
    - by rewrite Hx ?Hy; auto.
  Qed.

  Lemma forall_ne A n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (@uPred_forall M A).
  Proof.
    by intros Ψ1 Ψ2 HΨ; unseal; split=> x; split; intros HP a; apply HΨ.
  Qed.

  Lemma exist_ne A n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (@uPred_exist M A).
  Proof.
    intros Ψ1 Ψ2 HΨ.
    unseal; split=>x ?; split; intros [a ?]; exists a; by apply HΨ.
  Qed.

  (* Lemma later_contractive : Contractive (@uPred_later M).
  Proof.
    unseal; intros [|n] P Q HPQ; split=> -[|n'] x ?? //=; try lia.
    eapply HPQ; eauto using cmra_validN_S.
  Qed. *)

  Lemma later_ne : NonExpansive (@uPred_later M).
  Proof.
    intros n P1 P2 HP.
    unseal; done.
  Qed.

  Lemma plainly_ne : NonExpansive (@uPred_plainly M).
  Proof.
    intros n P1 P2 HP.
    unseal; split=> x; split; apply HP; eauto using ucmra_unit_valid.
  Qed.

  Lemma persistently_ne : NonExpansive (@uPred_persistently M).
  Proof.
    intros n P1 P2 HP.
    unseal; split=> x; split; apply HP; eauto using cmra_core_valid.
  Qed.

  Lemma ownM_ne `{CmraDiscrete M} : NonExpansive (@uPred_ownM M).
  Proof.
    intros n a b Ha%discrete_iff; try apply _;
    unseal; split=> x ? /=. by rewrite Ha.
  Qed.

  Lemma ownM_proper : Proper ((≡)==>(≡)) (@uPred_ownM M).
  Proof.
    intros a b Ha.
    unseal; split=> x ? /=. by rewrite Ha.
  Qed.

  Lemma cmra_valid_ne {A : cmra} `{CmraDiscrete A} :
    NonExpansive (@uPred_cmra_valid M A).
  Proof.
    intros n a b Ha%discrete_iff; try apply _; unseal; split=> x ? /=.
    by rewrite Ha.
  Qed.

  Lemma cmra_valid_proper {A : cmra} :
    Proper ((≡)==>(≡)) (@uPred_cmra_valid M A).
  Proof.
    intros a b Ha; unseal; split=> x ? /=.
    by rewrite Ha.
  Qed.

  Lemma bupd_ne : NonExpansive (@uPred_bupd M).
  Proof.
    intros n P Q HPQ.
    unseal; split=> x; split; intros HP yf ?;
      destruct (HP yf) as (x'&?&?); auto;
      exists x'; split; auto; apply HPQ; eauto using cmra_valid_op_l.
  Qed.

  (** Introduction and elimination rules *)
  Lemma pure_intro φ P : φ → P ⊢ ⌜φ⌝.
  Proof. by intros ?; unseal; split. Qed.
  Lemma pure_elim' φ P : (φ → True ⊢ P) → ⌜φ⌝ ⊢ P.
  Proof. unseal; intros HP; split=> x ??. by apply HP. Qed.
  Lemma pure_forall_2 {A} (φ : A → Prop) : (∀ x : A, ⌜φ x⌝) ⊢ ⌜∀ x : A, φ x⌝.
  Proof. by unseal. Qed.

  Lemma and_elim_l P Q : P ∧ Q ⊢ P.
  Proof. by unseal; split=> x ? [??]. Qed.
  Lemma and_elim_r P Q : P ∧ Q ⊢ Q.
  Proof. by unseal; split=> x ? [??]. Qed.
  Lemma and_intro P Q R : (P ⊢ Q) → (P ⊢ R) → P ⊢ Q ∧ R.
  Proof. intros HQ HR; unseal; split=> x ??; by split; [apply HQ|apply HR]. Qed.

  Lemma or_intro_l P Q : P ⊢ P ∨ Q.
  Proof. unseal; split=> x ??; left; auto. Qed.
  Lemma or_intro_r P Q : Q ⊢ P ∨ Q.
  Proof. unseal; split=> x ??; right; auto. Qed.
  Lemma or_elim P Q R : (P ⊢ R) → (Q ⊢ R) → P ∨ Q ⊢ R.
  Proof.
    intros HP HQ; unseal; split=> x ? [?|?].
    - by apply HP.
    - by apply HQ.
  Qed.

  Lemma impl_intro_r P Q R : (P ∧ Q ⊢ R) → P ⊢ Q → R.
  Proof.
    unseal; intros HQ; split=> x ? x' ????. apply HQ; [done|].
    split; [|done]. eapply uPred_mono; eauto.
  Qed.
  Lemma impl_elim_l' P Q R : (P ⊢ Q → R) → P ∧ Q ⊢ R.
  Proof. unseal; intros HP ; split=> x ? [??]; apply HP with x; auto. Qed.

  Lemma forall_intro {A} P (Ψ : A → uPred M): (∀ a, P ⊢ Ψ a) → P ⊢ ∀ a, Ψ a.
  Proof. unseal; intros HPΨ; split=> x ?? a; by apply HPΨ. Qed.
  Lemma forall_elim {A} {Ψ : A → uPred M} a : (∀ a, Ψ a) ⊢ Ψ a.
  Proof. unseal; split=> x ? HP; apply HP. Qed.

  Lemma exist_intro {A} {Ψ : A → uPred M} a : Ψ a ⊢ ∃ a, Ψ a.
  Proof. unseal; split=> x ??; by exists a. Qed.
  Lemma exist_elim {A} (Φ : A → uPred M) Q : (∀ a, Φ a ⊢ Q) → (∃ a, Φ a) ⊢ Q.
  Proof. unseal; intros HΦΨ; split=> x ? [a ?]; by apply HΦΨ with a. Qed.

  (** BI connectives *)
  Lemma sep_mono P P' Q Q' : (P ⊢ Q) → (P' ⊢ Q') → P ∗ P' ⊢ Q ∗ Q'.
  Proof.
    intros HQ HQ'; unseal.
    split; intros x Hx (x1&x2&EQ&?&?); exists x1,x2; ofe_subst x.
    rewrite EQ in Hx. rewrite EQ.
    split_and!; [done|eapply uPred_in_entails;eauto..];
    eauto using cmra_valid_op_l,cmra_valid_op_r.
  Qed.
  Lemma True_sep_1 P : P ⊢ True ∗ P.
  Proof.
    unseal; split; intros x ??. exists (core x), x. by rewrite cmra_core_l.
  Qed.
  Lemma True_sep_2 P : True ∗ P ⊢ P.
  Proof.
    unseal; split; intros x Hx (x1&x2&EQ&_&?).
    rewrite EQ. rewrite EQ in Hx.
    eauto using uPred_mono, cmra_included_r.
  Qed.
  Lemma sep_comm' P Q : P ∗ Q ⊢ Q ∗ P.
  Proof.
    unseal; split; intros x ? (x1&x2&?&?&?); exists x2, x1; by rewrite (comm op).
  Qed.
  Lemma sep_assoc' P Q R : (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R).
  Proof.
    unseal; split; intros x ? (x1&x2&Hx&(y1&y2&Hy&?&?)&?).
    exists y1, (y2 ⋅ x2); split_and?; auto.
    + by rewrite (assoc op) -Hy -Hx.
    + by exists y2, x2.
  Qed.
  Lemma wand_intro_r P Q R : (P ∗ Q ⊢ R) → P ⊢ Q -∗ R.
  Proof.
    unseal=> HPQR; split=> x ?? x' ??; apply HPQR; auto.
    exists x, x'; split_and?; auto.
  Qed.
  Lemma wand_elim_l' P Q R : (P ⊢ Q -∗ R) → P ∗ Q ⊢ R.
  Proof.
    unseal =>HPQR. split; intros x Hx (?&?&EQ&?&?). ofe_subst.
    rewrite EQ in Hx. rewrite EQ.
    eapply HPQR; eauto using cmra_valid_op_l.
  Qed.

  (** Persistently *)
  Lemma persistently_mono P Q : (P ⊢ Q) → □ P ⊢ □ Q.
  Proof. intros HP; unseal; split=> x ? /=. by apply HP, cmra_core_valid. Qed.
  Lemma persistently_elim P : □ P ⊢ P.
  Proof.
    unseal; split=> x ? Hx.
    eapply uPred_mono; [exact Hx|apply cmra_included_core].
  Qed.
  Lemma persistently_idemp_2 P : □ P ⊢ □ □ P.
  Proof. unseal; split=> x ?? /=. by rewrite cmra_core_idemp. Qed.

  Lemma persistently_forall_2 {A} (Ψ : A → uPred M) : (∀ a, □ Ψ a) ⊢ (□ ∀ a, Ψ a).
  Proof. by unseal. Qed.
  Lemma persistently_exist_1 {A} (Ψ : A → uPred M) : (□ ∃ a, Ψ a) ⊢ (∃ a, □ Ψ a).
  Proof. by unseal. Qed.

  Lemma persistently_and_sep_l_1 P Q : □ P ∧ Q ⊢ P ∗ Q.
  Proof.
    unseal; split=> x ? [??]; exists (core x), x; simpl in *.
    by rewrite cmra_core_l.
  Qed.

  (** Plainly *)
  Lemma plainly_mono P Q : (P ⊢ Q) → ■ P ⊢ ■ Q.
  Proof. intros HP; unseal; split=> x ? /=. apply HP, ucmra_unit_valid. Qed.
  Lemma plainly_elim_persistently P : ■ P ⊢ □ P.
  Proof. unseal; split; simpl; intros. by eapply uPred_mono; [|eapply ucmra_unit_least]. Qed.
  Lemma plainly_idemp_2 P : ■ P ⊢ ■ ■ P.
  Proof. unseal; split=> x ?? //. Qed.

  Lemma plainly_forall_2 {A} (Ψ : A → uPred M) : (∀ a, ■ Ψ a) ⊢ (■ ∀ a, Ψ a).
  Proof. by unseal. Qed.
  Lemma plainly_exist_1 {A} (Ψ : A → uPred M) : (■ ∃ a, Ψ a) ⊢ (∃ a, ■ Ψ a).
  Proof. by unseal. Qed.

  Lemma prop_ext_2 P Q : ■ ((P -∗ Q) ∧ (Q -∗ P)) ⊢ P ≡ Q.
  Proof.
    unseal; split=> x ? /=. setoid_rewrite (left_id ε op). split; naive_solver.
  Qed.

  (* The following two laws are very similar, and indeed they hold not just for □
     and ■, but for any modality defined as `M P x := ∀ y, R x y → P y`. *)
  Lemma persistently_impl_plainly P Q : (■ P → □ Q) ⊢ □ (■ P → Q).
  Proof.
    unseal; split=> /= x ? HPQ x' ???.
    eapply uPred_mono with (core x)=>//.
    apply (HPQ x); eauto.
  Qed.

  Lemma plainly_impl_plainly P Q : (■ P → ■ Q) ⊢ ■ (■ P → Q).
  Proof.
    unseal; split=> /= x ? HPQ x' ???.
    eapply uPred_mono with ε=>//.
    apply (HPQ x); eauto.
  Qed.

  (** Later *)
  Lemma later_mono P Q : (P ⊢ Q) → ▷ P ⊢ ▷ Q.
  Proof.
    unseal=> HP; split=>- x ??; apply HP; eauto.
  Qed.
  Lemma later_intro P : P ⊢ ▷ P.
  Proof.
    unseal; split=> - /= x ? HP; first done.
  Qed.
  Lemma later_forall_2 {A} (Φ : A → uPred M) : (∀ a, ▷ Φ a) ⊢ ▷ ∀ a, Φ a.
  Proof. unseal; by split=> - x. Qed.
  Lemma later_exist_false {A} (Φ : A → uPred M) :
    (▷ ∃ a, Φ a) ⊢ ▷ False ∨ (∃ a, ▷ Φ a).
  Proof. unseal; split=> - x /=; eauto. Qed.
  Lemma later_sep_1 P Q : ▷ (P ∗ Q) ⊢ ▷ P ∗ ▷ Q.
  Proof. unseal; split=> x ?. done. Qed.
  Lemma later_sep_2 P Q : ▷ P ∗ ▷ Q ⊢ ▷ (P ∗ Q).
  Proof. unseal; split=> x ?. done. Qed.

  Lemma later_false_em P : ▷ P ⊢ ▷ False ∨ (▷ False → P).
  Proof.
    unseal; split=> - x ? /= HP; right.
    intros x' ???; eauto. done.
  Qed.

  Lemma later_persistently_1 P : ▷ □ P ⊢ □ ▷ P.
  Proof. by unseal. Qed.
  Lemma later_persistently_2 P : □ ▷ P ⊢ ▷ □ P.
  Proof. by unseal. Qed.
  Lemma later_plainly_1 P : ▷ ■ P ⊢ ■ ▷ P.
  Proof. by unseal. Qed.
  Lemma later_plainly_2 P : ■ ▷ P ⊢ ▷ ■ P.
  Proof. by unseal. Qed.

  (** Internal equality *)
  Lemma internal_eq_refl {A : ofe} P (a : A) : P ⊢ (a ≡ a).
  Proof. unseal; by split=> x ??; simpl. Qed.
  Lemma internal_eq_rewrite {A : ofe} a b (Ψ : A → uPred M) :
    Proper ((≡)==>(≡)) Ψ → a ≡ b ⊢ Ψ a → Ψ b.
  Proof. intros HΨ. unseal; split=> x ? EQ x' ?? Ha. by apply HΨ with a. Qed.

  Lemma fun_ext {A} {B : A → ofe} (g1 g2 : discrete_fun B) :
    (∀ i, g1 i ≡ g2 i) ⊢ g1 ≡ g2.
  Proof. by unseal. Qed.
  Lemma sig_eq {A : ofe} (P : A → Prop) (x y : sigO P) :
    proj1_sig x ≡ proj1_sig y ⊢ x ≡ y.
  Proof. by unseal. Qed.

  Lemma later_eq_1 {A : ofe} (x y : A) : Next x ≡ Next y ⊢ ▷ (x ≡ y).
  Proof.
    unseal. split. intros; simpl; done.
  Qed.
  Lemma later_eq_2 {A : ofe} (x y : A) : ▷ (x ≡ y) ⊢ Next x ≡ Next y.
  Proof.
    unseal. split. intros ? ? Hn; simpl in *.
    rewrite Hn. done.
  Qed.

  Lemma discrete_eq_1 {A : ofe} (a b : A) : a ≡ b ⊢ ⌜a ≡ b⌝.
  Proof.
    unseal. split=> x ? ?. done.
  Qed.

  (** This is really just a special case of an entailment
  between two [siProp], but we do not have the infrastructure
  to express the more general case. This temporary proof rule will
  be replaced by the proper one eventually. *)
  Lemma internal_eq_entails {A B : ofe} (a1 a2 : A) (b1 b2 : B) :
    (a1 ≡ a2 ⊢ b1 ≡ b2) ↔ (a1 ≡ a2 → b1 ≡ b2).
  Proof.
    split.
    - unseal=> -[Hsi]. apply (Hsi ε), ucmra_unit_valid.
    - unseal=> Hsi. split=> x ?. apply Hsi.
  Qed.

  (** Basic update modality *)
  Lemma bupd_intro P : P ⊢ |==> P.
  Proof.
    unseal. split=> x ? HP yf ?; exists x; split; done.
  Qed.
  Lemma bupd_mono P Q : (P ⊢ Q) → (|==> P) ⊢ |==> Q.
  Proof.
    unseal. intros HPQ; split=> x ? HP yf ?.
    destruct (HP yf) as (x'&?&?); eauto.
    exists x'; split; eauto using uPred_in_entails, cmra_valid_op_l.
  Qed.
  Lemma bupd_trans P : (|==> |==> P) ⊢ |==> P.
  Proof. unseal; split; naive_solver. Qed.
  Lemma bupd_frame_r P R : (|==> P) ∗ R ⊢ |==> P ∗ R.
  Proof.
    unseal; split; intros x ? (x1&x2&Hx&HP&?) yf ?.
    destruct (HP (x2 ⋅ yf)) as (x'&?&?); eauto.
    { by rewrite assoc -Hx. }
    exists (x' ⋅ x2); split; first by rewrite -assoc.
    exists x', x2. done.
  Qed.
  Lemma bupd_plainly P : (|==> ■ P) ⊢ P.
  Proof.
    unseal; split => x Hnx /= Hng.
    destruct (Hng ε) as [? [_ Hng']]; try rewrite right_id; auto.
    eapply uPred_mono; eauto using ucmra_unit_least.
  Qed.

  (** Own *)
  Lemma ownM_op (a1 a2 : M) :
    uPred_ownM (a1 ⋅ a2) ⊣⊢ uPred_ownM a1 ∗ uPred_ownM a2.
  Proof.
    unseal; split=> x ?; split.
    - intros [z ?]; exists a1, (a2 ⋅ z); split; [by rewrite (assoc op)|].
      split.
      + by exists (core a1); rewrite cmra_core_r.
      + by exists z.
    - intros (y1&y2&Hx&[z1 Hy1]&[z2 Hy2]); exists (z1 ⋅ z2).
      by rewrite (assoc op _ z1) -(comm op z1) (assoc op z1)
        -(assoc op _ a2) (comm op z1) -Hy1 -Hy2.
  Qed.
  Lemma persistently_ownM_core (a : M) : uPred_ownM a ⊢ □ uPred_ownM (core a).
  Proof.
    split=> x /=; unseal; intros Hx. simpl. by apply cmra_core_mono.
  Qed.
  Lemma ownM_unit P : P ⊢ (uPred_ownM ε).
  Proof. unseal; split=> x ??; by  exists x; rewrite left_id. Qed.
  Lemma later_ownM a : ▷ uPred_ownM a ⊢ ∃ b, uPred_ownM b ∧ ▷ (a ≡ b).
  Proof. unseal; split=> - x /= ? Hax; eauto. Qed.

  Lemma bupd_ownM_updateP `{!CmraDiscrete M} x (Φ : M → Prop) :
    x ~~>: Φ → uPred_ownM x ⊢ |==> ∃ y, ⌜Φ y⌝ ∧ uPred_ownM y.
  Proof.
    unseal=> Hup. split=> x2 ? [x3 Hx] yf ?.
    rewrite cmra_discrete_total_updateP in Hup.
    destruct (Hup (x3 ⋅ yf)) as (y&?&?); simpl in *.
    { rewrite /= assoc -Hx; auto. }
    exists (y ⋅ x3); split; first by rewrite -assoc.
    exists y; eauto using cmra_included_l.
  Qed.

  (** Valid *)
  Lemma ownM_valid (a : M) : uPred_ownM a ⊢ ✓ a.
  Proof.
    unseal; split=> x Hv [a' EQ]; rewrite EQ in Hv. eapply cmra_valid_op_l; eauto.
  Qed.
  Lemma cmra_valid_intro {A : cmra} P (a : A) : ✓ a → P ⊢ (✓ a).
  Proof. unseal=> ?; split=> x ? _ //=. Qed.
  Lemma cmra_valid_elim {A : cmra} (a : A) : ✓ a ⊢ ⌜ ✓{0} a ⌝.
  Proof. unseal; split=> x ??. apply cmra_valid_validN; auto. Qed.
  Lemma plainly_cmra_valid_1 {A : cmra} (a : A) : ✓ a ⊢ ■ ✓ a.
  Proof. by unseal. Qed.
  Lemma cmra_valid_weaken {A : cmra} (a b : A) : ✓ (a ⋅ b) ⊢ ✓ a.
  Proof. unseal; split=> x _; apply cmra_valid_op_l. Qed.

  Lemma discrete_valid {A : cmra} (a : A) : ✓ a ⊣⊢ ⌜✓ a⌝.
  Proof. unseal; split=> x _. done. Qed.

  (** This is really just a special case of an entailment
  between two [siProp], but we do not have the infrastructure
  to express the more general case. This temporary proof rule will
  be replaced by the proper one eventually. *)
  Lemma valid_entails {A B : cmra} (a : A) (b : B) :
    (✓ a → ✓ b) → ✓ a ⊢ ✓ b.
  Proof. unseal=> Hval. split=> x ?. apply Hval. Qed.

  (** Consistency/soundness statement *)
  (** The lemmas [pure_soundness] and [internal_eq_soundness] should become an
  instance of [siProp] soundness in the future. *)
  Lemma pure_soundness φ : (True ⊢ ⌜ φ ⌝) → φ.
  Proof. unseal=> -[H]. by apply (H ε); eauto using ucmra_unit_valid. Qed.

  Lemma internal_eq_soundness {A : ofe} (x y : A) : (True ⊢ x ≡ y) → x ≡ y.
  Proof.
    unseal=> -[H].
    by apply (H ε); eauto using ucmra_unit_valid.
  Qed.

  Lemma later_soundness P : (True ⊢ ▷ P) → (True ⊢ P).
  Proof.
    unseal=> -[HP]; split=> x Hx _.
    apply uPred_mono with ε; eauto using ucmra_unit_least.
    by apply HP; eauto using ucmra_unit_valid.
  Qed.

  Lemma later_eq P : (▷ P ⊢ P).
  Proof. unseal. done. Qed.
End primitive.
End uPred_primitive.
