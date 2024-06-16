From stdpp Require Import tactics.
From Fairness Require Import cmra.
From Fairness Require Import updates local_updates.
From iris.prelude Require Import prelude options.

Local Open Scope iris_algebra_scope.

Local Arguments pcore _ _ !_ /.
Local Arguments cmra_pcore _ !_ /.

Local Arguments valid _ _  !_ /.
Local Arguments cmra_valid _  !_ /.

Inductive csum (A B : Type) :=
  | Cinl : A → csum A B
  | Cinr : B → csum A B
  | CsumBot : csum A B.
Global Arguments Cinl {_ _} _.
Global Arguments Cinr {_ _} _.
Global Arguments CsumBot {_ _}.

Global Instance: Params (@Cinl) 2 := {}.
Global Instance: Params (@Cinr) 2 := {}.
Global Instance: Params (@CsumBot) 2 := {}.

Global Instance maybe_Cinl {A B} : Maybe (@Cinl A B) := λ x,
  match x with Cinl a => Some a | _ => None end.
Global Instance maybe_Cinr {A B} : Maybe (@Cinr A B) := λ x,
  match x with Cinr b => Some b | _ => None end.



(* Functor on COFEs *)
Definition csum_map {A A' B B'} (fA : A → A') (fB : B → B')
                    (x : csum A B) : csum A' B' :=
  match x with
  | Cinl a => Cinl (fA a)
  | Cinr b => Cinr (fB b)
  | CsumBot => CsumBot
  end.
Global Instance: Params (@csum_map) 4 := {}.

Lemma csum_map_id {A B} (x : csum A B) : csum_map id id x = x.
Proof. by destruct x. Qed.
Lemma csum_map_compose {A A' A'' B B' B''} (f : A → A') (f' : A' → A'')
                       (g : B → B') (g' : B' → B'') (x : csum A B) :
  csum_map (f' ∘ f) (g' ∘ g) x = csum_map f' g' (csum_map f g x).
Proof. by destruct x. Qed.
Lemma csum_map_ext {A A' B B' : Type} (f f' : A → A') (g g' : B → B') x :
  (∀ x, f x = f' x) → (∀ x, g x = g' x) → csum_map f g x = csum_map f' g' x.
Proof.
  destruct x; simpl; [intros H1 H2;f_equal..|done].
  - apply H1.
  - apply H2.
Qed.
(* Global Instance csum_map_cmra_ne {A A' B B' : Type} n :
  Proper ((dist n ==> dist n) ==> (dist n ==> dist n) ==> dist n ==> dist n)
         (@csum_map A A' B B').
Proof. intros f f' Hf g g' Hg []; destruct 1; constructor; by apply Hf || apply Hg. Qed.
Definition csumO_map {A A' B B'} (f : A -n> A') (g : B -n> B') :
  csumO A B -n> csumO A' B' :=
  OfeMor (csum_map f g).
Global Instance csumO_map_ne A A' B B' :
  NonExpansive2 (@csumO_map A A' B B').
Proof. by intros n f f' Hf g g' Hg []; constructor. Qed. *)

Section cmra.
Context {A B : cmra}.
Implicit Types a : A.
Implicit Types b : B.

(* CMRA *)
Local Instance csum_valid_instance : Valid (csum A B) := λ x,
  match x with
  | Cinl a => ✓ a
  | Cinr b => ✓ b
  | CsumBot => False
  end.
Local Instance csum_pcore_instance : PCore (csum A B) := λ x,
  match x with
  | Cinl a => Cinl <$> pcore a
  | Cinr b => Cinr <$> pcore b
  | CsumBot => Some CsumBot
  end.
Local Instance csum_op_instance : Op (csum A B) := λ x y,
  match x, y with
  | Cinl a, Cinl a' => Cinl (a ⋅ a')
  | Cinr b, Cinr b' => Cinr (b ⋅ b')
  | _, _ => CsumBot
  end.

Lemma Cinl_op a a' : Cinl (a ⋅ a') = Cinl a ⋅ Cinl a'.
Proof. done. Qed.
Lemma Cinr_op b b' : Cinr (b ⋅ b') = Cinr b ⋅ Cinr b'.
Proof. done. Qed.

Lemma Cinl_valid a : ✓ (Cinl a) ↔ ✓ a.
Proof. done. Qed.
Lemma Cinr_valid b : ✓ (Cinr b) ↔ ✓ b.
Proof. done. Qed.

Lemma csum_included x y :
  x ≼ y ↔ y = CsumBot ∨ (∃ a a', x = Cinl a ∧ y = Cinl a' ∧ a ≼ a')
                      ∨ (∃ b b', x = Cinr b ∧ y = Cinr b' ∧ b ≼ b').
Proof.
  split.
  - unfold included. intros [[a'|b'|] Hy]; destruct x as [a|b|];
      inversion_clear Hy; eauto 10.
  - intros [->|[(a&a'&->&->&c&EQ)|(b&b'&->&->&c&EQ)]].
    + destruct x; exists CsumBot; constructor.
    + exists (Cinl c); by rewrite -Cinl_op EQ.
    + exists (Cinr c); by rewrite -Cinr_op EQ.
Qed.
Lemma Cinl_included a a' : Cinl a ≼ Cinl a' ↔ a ≼ a'.
Proof. rewrite csum_included. naive_solver. Qed.
Lemma Cinr_included b b' : Cinr b ≼ Cinr b' ↔ b ≼ b'.
Proof. rewrite csum_included. naive_solver. Qed.
Lemma CsumBot_included x : x ≼ CsumBot.
Proof. exists CsumBot. by destruct x. Qed.
(** We register a hint for [CsumBot_included] below. *)

Lemma csum_cmra_mixin : CmraMixin (csum A B).
Proof.
  split.
  - intros ??? -> ?. eauto.
  - intros [a1|b1|] [a2|b2|] [a3|b3|]; try rewrite -!Cinl_op; try rewrite -!Cinr_op; by rewrite ?assoc.
  - intros [a1|b1|] [a2|b2|]; try rewrite -!Cinl_op; try rewrite -!Cinr_op; by rewrite 1?(comm op).
  - intros [a|b|] ? [=]; subst; auto.
    + destruct (pcore a) as [ca|] eqn:?; simplify_option_eq.
      rewrite -Cinl_op; f_equal; eauto using cmra_pcore_l.
    + destruct (pcore b) as [cb|] eqn:?; simplify_option_eq.
      rewrite -Cinr_op; f_equal; eauto using cmra_pcore_l.
  - intros [a|b|] ? [=]; subst; auto.
    + destruct (pcore a) as [ca|] eqn:?; simplify_option_eq.
      apply cmra_pcore_idemp in Heqo. rewrite Heqo. done.
    + destruct (pcore b) as [cb|] eqn:?; simplify_option_eq.
      apply cmra_pcore_idemp in Heqo. rewrite Heqo. done.
  - intros x y ? [->|[(a&a'&->&->&?)|(b&b'&->&->&?)]]%csum_included [=].
    + exists CsumBot. rewrite csum_included; eauto.
    + destruct (pcore a) as [ca|] eqn:?; simplify_option_eq.
      destruct (cmra_pcore_mono a a' ca) as (ca'&->&?); auto.
      exists (Cinl ca'). rewrite csum_included; eauto 10.
    + destruct (pcore b) as [cb|] eqn:?; simplify_option_eq.
      destruct (cmra_pcore_mono b b' cb) as (cb'&->&?); auto.
      exists (Cinr cb'). rewrite csum_included; eauto 10.
  - intros [a1|b1|] [a2|b2|]; simpl; eauto using cmra_valid_op_l; done.
  - intros [a|b|] y1 y2 Hx Hx'.
    + destruct y1 as [a1|b1|], y2 as [a2|b2|]; try by exfalso; inversion Hx'.
      destruct (cmra_extend a a1 a2) as (z1&z2&?&?&?); [done| |].
      { rewrite -Cinl_op in Hx'. injection Hx' as ->. done. }
      exists (Cinl z1), (Cinl z2). subst. rewrite !Cinl_op. done.
      + destruct y1 as [a1|b1|], y2 as [a2|b2|]; try by exfalso; inversion Hx'.
      destruct (cmra_extend b b1 b2) as (z1&z2&?&?&?); [done| |].
      { rewrite -Cinr_op in Hx'. injection Hx' as ->. done. }
      exists (Cinr z1), (Cinr z2). subst. rewrite !Cinr_op. done.
    + by exists CsumBot, CsumBot; destruct y1, y2; inversion_clear Hx'.
Qed.
Canonical Structure csumR := Cmra (csum A B) csum_cmra_mixin.

(* Global Instance csum_cmra_discrete :
  CmraDiscrete A → CmraDiscrete B → CmraDiscrete csumR.
Proof.
  split; first apply _.
  by move=>[a|b|] HH /=; try apply cmra_discrete_valid.
Qed. *)

Global Instance Cinl_core_id a : CoreId a → CoreId (Cinl a).
Proof. rewrite /CoreId /=. intros ->. done. Qed.
Global Instance Cinr_core_id b : CoreId b → CoreId (Cinr b).
Proof. rewrite /CoreId /=. intros ->. done. Qed.

Global Instance Cinl_exclusive a : Exclusive a → Exclusive (Cinl a).
Proof. by move=> H[]? =>[/H||]. Qed.
Global Instance Cinr_exclusive b : Exclusive b → Exclusive (Cinr b).
Proof. by move=> H[]? =>[|/H|]. Qed.

Global Instance Cinl_cancelable a : Cancelable a → Cancelable (Cinl a).
Proof.
  move=> ? [y|y|] [z|z|] ? EQ //; inversion EQ.
  f_equal. by eapply (cancelable a).
Qed.
Global Instance Cinr_cancelable b : Cancelable b → Cancelable (Cinr b).
Proof.
  move=> ? [y|y|] [z|z|] ? EQ //; inversion EQ.
  f_equal. by eapply (cancelable b).
Qed.

Global Instance Cinl_id_free a : IdFree a → IdFree (Cinl a).
Proof. intros ? [] ? EQ; inversion EQ. by eapply id_free_r. Qed.
Global Instance Cinr_id_free b : IdFree b → IdFree (Cinr b).
Proof. intros ? [] ? EQ; inversion EQ. by eapply id_free_r. Qed.

(** Interaction with [option] *)
Lemma Some_csum_included x y :
  Some x ≼ Some y ↔
    y = CsumBot ∨
    (∃ a a', x = Cinl a ∧ y = Cinl a' ∧ Some a ≼ Some a') ∨
    (∃ b b', x = Cinr b ∧ y = Cinr b' ∧ Some b ≼ Some b').
Proof.
  repeat setoid_rewrite Some_included. rewrite csum_included. split.
  - intros [->|EQ].
    + destruct y; naive_solver.
    + destruct EQ as [?|?]; naive_solver.
  - naive_solver by f_equal.
Qed.

(** Updates *)
Lemma csum_update_l (a1 a2 : A) : a1 ~~> a2 → Cinl a1 ~~> Cinl a2.
Proof.
  intros Ha [[a|b|]|] ?; simpl in *; auto.
  - by apply (Ha (Some a)).
  - by apply (Ha None).
Qed.
Lemma csum_update_r (b1 b2 : B) : b1 ~~> b2 → Cinr b1 ~~> Cinr b2.
Proof.
  intros Hb [[a|b|]|] ?; simpl in *; auto.
  - by apply (Hb (Some b)).
  - by apply (Hb None).
Qed.
Lemma csum_updateP_l (P : A → Prop) (Q : csum A B → Prop) a :
  a ~~>: P → (∀ a', P a' → Q (Cinl a')) → Cinl a ~~>: Q.
Proof.
  intros Hx HP mf Hm. destruct mf as [[a'|b'|]|]; try by destruct Hm.
  - destruct (Hx (Some a')) as (c&?&?); naive_solver.
  - destruct (Hx None) as (c&?&?); naive_solver eauto using cmra_valid_op_l.
Qed.
Lemma csum_updateP_r (P : B → Prop) (Q : csum A B → Prop) b :
  b ~~>: P → (∀ b', P b' → Q (Cinr b')) → Cinr b  ~~>: Q.
Proof.
  intros Hx HP mf Hm. destruct mf as [[a'|b'|]|]; try by destruct Hm.
  - destruct (Hx (Some b')) as (c&?&?); naive_solver.
  - destruct (Hx None) as (c&?&?); naive_solver eauto using cmra_valid_op_l.
Qed.
Lemma csum_updateP'_l (P : A → Prop) a :
  a ~~>: P → Cinl a ~~>: λ m', ∃ a', m' = Cinl a' ∧ P a'.
Proof. eauto using csum_updateP_l. Qed.
Lemma csum_updateP'_r (P : B → Prop) b :
  b ~~>: P → Cinr b ~~>: λ m', ∃ b', m' = Cinr b' ∧ P b'.
Proof. eauto using csum_updateP_r. Qed.

Lemma csum_local_update_l (a1 a2 a1' a2' : A) :
  (a1,a2) ~l~> (a1',a2') → (Cinl a1,Cinl a2) ~l~> (Cinl a1',Cinl a2').
Proof.
  intros Hup mf ? Ha1; simpl in *.
  destruct (Hup (mf ≫= maybe Cinl)); auto.
  { by destruct mf as [[]|]; inversion_clear Ha1. }
  split; first done. destruct mf as [[]|]; inversion Ha1; subst.
  - simpl in *. rewrite -Cinl_op. f_equal. done.
  - simpl in *. f_equal. done.
Qed.
Lemma csum_local_update_r (b1 b2 b1' b2' : B) :
  (b1,b2) ~l~> (b1',b2') → (Cinr b1,Cinr b2) ~l~> (Cinr b1',Cinr b2').
Proof.
  intros Hup mf ? Ha1; simpl in *.
  destruct (Hup (mf ≫= maybe Cinr)); auto.
  { by destruct mf as [[]|]; inversion_clear Ha1. }
  split; first done. destruct mf as [[]|]; inversion Ha1; subst.
  - simpl in *. rewrite -Cinr_op. f_equal. done.
  - simpl in *. f_equal. done.
Qed.
End cmra.

(* We use a [Hint Extern] with [apply:], instead of [Hint Immediate], to invoke
  the new unification algorithm. The old unification algorithm sometimes gets
  confused by going from [ucmra]'s to [cmra]'s and back. *)
Global Hint Extern 0 (_ ≼ CsumBot) => apply: CsumBot_included : core.
Global Arguments csumR : clear implicits.

(* Functor *)
Global Instance csum_map_cmra_morphism {A A' B B' : cmra} (f : A → A') (g : B → B') :
  CmraMorphism f → CmraMorphism g → CmraMorphism (csum_map f g).
Proof.
  split; try apply _.
  - intros [a|b|]; simpl; auto using cmra_morphism_valid.
  - move=> [a|b|]=>//=; rewrite -cmra_morphism_pcore; by destruct pcore.
  - intros [xa|ya|] [xb|yb|]=>//=; by rewrite cmra_morphism_op.
Qed.

(* Program Definition csumRF (Fa Fb : rFunctor) : rFunctor := {|
  rFunctor_car A _ B _ := csumR (rFunctor_car Fa A B) (rFunctor_car Fb A B);
  rFunctor_map A1 _ A2 _ B1 _ B2 _ fg := csumO_map (rFunctor_map Fa fg) (rFunctor_map Fb fg)
|}.
Next Obligation.
  by intros Fa Fb A1 ? A2 ? B1 ? B2 ? n f g Hfg; apply csumO_map_ne; try apply rFunctor_map_ne.
Qed.
Next Obligation.
  intros Fa Fb A ? B ? x. rewrite /= -{2}(csum_map_id x).
  apply csum_map_ext=>y; apply rFunctor_map_id.
Qed.
Next Obligation.
  intros Fa Fb A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x. rewrite /= -csum_map_compose.
  apply csum_map_ext=>y; apply rFunctor_map_compose.
Qed.

Global Instance csumRF_contractive Fa Fb :
  rFunctorContractive Fa → rFunctorContractive Fb →
  rFunctorContractive (csumRF Fa Fb).
Proof.
  intros ?? A1 ? A2 ? B1 ? B2 ? n f g Hfg.
  by apply csumO_map_ne; try apply rFunctor_map_contractive.
Qed. *)
