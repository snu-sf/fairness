From sflib Require Import sflib.
Require Export ZArith.
From Fairness Require Import Axioms.
From Fairness Require Import ucmra_list.
From iris.algebra Require Import cmra updates functions.

From iris.prelude Require Import options.

Set Implicit Arguments.

(* TODO: Auxillary discrete_fun lemmas. Move to somewhere else. *)
Section discrete_fun.
  (** Depends on axiom of dependent choice.  *)

  Lemma discrete_fun_included_spec_2 A (Ms : A → ucmra)
      (f0 f1 : discrete_fun Ms)
      (EXT : ∀ a, (f0 a) ≼ (f1 a)) :
    f0 ≼ f1.
  Proof.
    hexploit (dependent_functional_choice _ (λ a z, f1 a ≡ (f0 a) ⋅ z)).
    { i. specialize (EXT x). r in EXT. des. eauto. }
    intros H. des. exists f. naive_solver.
  Qed.

  Lemma discrete_fun_updateP
      A (Ms : A → ucmra)
      (f : discrete_fun Ms)
      (P : ∀ (a : A), (Ms a) → Prop)
      (UPD: ∀ a, (f a) ~~>: (P a))
    :
    f ~~>: λ f', ∀ a, P a (f' a).
  Proof.
    setoid_rewrite cmra_total_updateP in UPD.
    apply cmra_total_updateP => n z Hfy.
    hexploit (dependent_functional_choice _ (λ a y, P a y ∧ ✓{n} (y ⋅ z a))).
    { naive_solver. }
    ii. naive_solver.
  Qed.

  (** Axiom-free, can be upstreamed. *)

  Lemma discrete_fun_op {A} {B : A → ucmra} (f g : discrete_fun B) :
    f ⋅ g = λ a, f a ⋅ g a.
  Proof. done. Qed.

  (* TODO: Upstreamed. Remove after Iris bump *)
  Lemma discrete_fun_update
      A (Ms : A → ucmra)
      (f0 f1 : discrete_fun Ms)
      (UPD: ∀ a, (f0 a) ~~> (f1 a))
    :
    f0 ~~> f1.
  Proof.
    setoid_rewrite cmra_total_update in UPD.
    apply cmra_total_update => n z Hf0z k.
    naive_solver.
  Qed.

  (* TODO: Upstreamed. Remove after Iris bump *)
  Lemma discrete_fun_singleton_valid
    {A : Type} `{Heqdec : !EqDecision A} {B : A → ucmra}
    x (y : B x) :
    ✓ discrete_fun_singleton x y ↔ ✓ y.
  Proof.
    rewrite !cmra_valid_validN.
    by setoid_rewrite discrete_fun_singleton_validN.
  Qed.

  (* TODO: Upstreamed. Remove after Iris bump *)
  Lemma discrete_fun_singleton_unit
    {A : Type} `{Heqdec : !EqDecision A} {B : A → ucmra}
    x :
    (discrete_fun_singleton x ε : discrete_fun B) ≡ ε.
  Proof.
    intros y. destruct (decide (x = y)) as [->|];
    by rewrite ?discrete_fun_lookup_singleton
      ?discrete_fun_lookup_singleton_ne.
  Qed.

End discrete_fun.


(** [discrete_fun_singleton] with excluded middle built-in *)
(*  It may be tempting to just create a [Global Instance A_eq_decision : EqDecision A] using
    excluded middle. However that would create two instance of
    [EqDecision] for decidable types causing all kinds of
    weird inference failures.
*)
Local Lemma A_eq_decision {A} : EqDecision A.
Proof. intros ??. apply excluded_middle_informative. Qed.
Notation maps_to_res := (@discrete_fun_singleton _ (@A_eq_decision _) _).


Lemma maps_to_res_eq {A} {B : A → ucmra} :
  maps_to_res =
    λ a (m : B a) a',
      match excluded_middle_informative (a = a') with
      | left H => eq_rect a B m a' H
      | _ => ε
      end.
Proof.
  extensionalities a m a'; des_ifs;
  rewrite ?discrete_fun_lookup_singleton ?discrete_fun_lookup_singleton_ne //.
Qed.

Module GRA.
  Record t: Type := GRA__INTERNAL {
    gra_map :> nat → ucmra;
    gra_discrete : ∀ i, CmraDiscrete (gra_map i);
  }.
  Local Existing Instance gra_discrete.

  Class inG (RA: ucmra) (Σ: t) := InG {
    inG_id: nat;
    inG_prf: RA = Σ inG_id;
  }
  .

  Program Definition of_list (RAs: ucmra_list) : t :=
    {| gra_map := λ n, (UList.nth n RAs (optionUR Empty_setR)) |}.
  Next Obligation. induction RAs; destruct i; apply _. Qed.

  Definition to_URA (Σ: t) : ucmra := discrete_funUR Σ.

  Coercion to_URA : t >-> ucmra.

  Global Instance GRA_discrete `{Σ : t} : CmraDiscrete Σ.
  Proof. apply _. Qed.

  Global Instance inG_cmra_discrete `{!inG A Σ} : CmraDiscrete A.
  Proof. erewrite inG_prf. apply _. Qed.

  (* a: cmra_car =ty= RAs inG_id =ty= RAs n *)
  Definition embed `{!inG A Σ} (a: A) : Σ :=
    discrete_fun_singleton inG_id (cmra_transport (f_equal _ inG_prf) a).
  Local Instance: Params (@embed) 3 := {}.

Section lemmas.
  Context `{!inG A Σ}.
  Implicit Types a : A.

  Global Instance embed_ne : NonExpansive (@embed A Σ _).
  Proof. by intros ????; apply discrete_fun_singleton_ne, cmra_transport_ne. Qed.
  Global Instance embed_proper : Proper ((≡) ==> (≡)) (@embed A Σ _) := ne_proper _.

  Lemma embed_valid a :
    ✓ embed a ↔ ✓ a.
  Proof. by rewrite /embed discrete_fun_singleton_valid cmra_transport_valid. Qed.

  Lemma embed_wf
    a
    (WF: ✓ embed a)
  :
  <<WF: ✓ a>>
  .
  Proof. by rewrite embed_valid in WF. Qed.

  Lemma wf_embed
    a
    (WF: ✓ a)
  :
  <<WF: ✓ embed a >>
  .
  Proof. by rewrite /NW embed_valid. Qed.

  Lemma embed_add
        a0 a1
    :
      embed a0 ⋅ embed a1 ≡ embed (a0 ⋅ a1)
    .
  Proof. by rewrite /embed discrete_fun_singleton_op cmra_transport_op. Qed.

  Lemma embed_updatable_set
        a P
        (UPD: a ~~>: P)
    :
      <<UPD: embed a ~~>: λ b, ∃ a', b = embed a' ∧ P a' >>
  .
  Proof.
    eapply discrete_fun_singleton_updateP.
    { eapply cmra_transport_updateP', UPD. }
    ii. ss. des. subst. eauto.
  Qed.

  Lemma embed_updatable
        a0 a1
        (UPD: a0 ~~> a1)
    :
      <<UPD: embed a0 ~~> embed a1 >>
  .
  Proof.
    eapply cmra_update_updateP, cmra_updateP_weaken.
    - apply embed_updatable_set, cmra_update_updateP, UPD.
    - ii. ss. des. subst. done.
  Qed.

  Lemma embed_core a : core (embed a) ≡ embed (core a).
  Proof. by rewrite /embed discrete_fun_singleton_core cmra_transport_core. Qed.

  Global Instance core_id a :
    CoreId a → CoreId (embed a).
  Proof. rewrite !core_id_total embed_core. by intros ->. Qed.


  (* Note: NOT a general lemma for [cmra_transport]. Tailed for the proof pattern
    of [GRA]. I.e., upstreaming this to iris doesn't make sense. *)
  Local Lemma cmra_transport_unit {B C : ucmra} (H : B = C) : cmra_transport (f_equal _ H) ε = ε.
  Proof. by destruct H. Qed.
  Lemma embed_unit : embed ε ≡ ε.
  Proof. by rewrite /embed cmra_transport_unit discrete_fun_singleton_unit. Qed.

End lemmas.
End GRA.
Coercion GRA.to_URA: GRA.t >-> ucmra.

Global Opaque GRA.to_URA.

From iris.algebra Require Import proofmode_classes.

Section proofmode_instance.

  Global Instance gra_is_op `{!GRA.inG M Σ} (a b c : M):
    IsOp a b c → IsOp (GRA.embed a) (GRA.embed b) (GRA.embed c).
  Proof. rewrite /IsOp. intros ->. rewrite GRA.embed_add //. Qed.

End proofmode_instance.

(* Find the left-most element in a chain of [op]s. *)
Ltac r_first rs :=
  match rs with
  | (?rs0 ⋅ ?rs1) =>
    let tmp0 := r_first rs0 in
    constr:(tmp0)
  | ?r => constr:(r)
  end
.

(* Solve permuation of cmra [op]s. *)
Ltac r_solve :=
  rewrite ?(assoc (⋅)) ?(right_id ε (⋅)) ?(left_id ε (⋅));
  match goal with
  | [|- ?lhs ≡ (_ ⋅ _) ] =>
    let a := r_first lhs in
    rewrite -?(comm (⋅) a) -?(assoc (⋅));
    try (f_equiv; r_solve)
  | _ => try reflexivity
  end
.

(* Solve inclusion of cmra [op]s, with permuation. *)
Ltac r_solve_included :=
  rewrite ?(assoc (⋅)) ?(right_id ε (⋅)) ?(left_id ε (⋅));
  match goal with
  | [|- (?lhs ⋅ _) ≼ (_ ⋅ _) ] =>
    let a := r_first lhs in
    rewrite -?(comm (⋅) a) -?(assoc (⋅));
    apply cmra_mono_l;
    try r_solve_included
  | [|- ?lhs ≼ (_ ⋅ _) ] =>
    rewrite -?(comm (⋅) lhs) -?(assoc (⋅));
    try apply cmra_included_l
  | _ => try (reflexivity || apply ucmra_unit_least)
  end
.

(* [✓ a], [H : ✓ b] where [a ≼ b] syntactically. *)
Ltac r_wf H := eapply cmra_valid_included; [exact H|]; r_solve_included.

Tactic Notation "unfold_prod" :=
  rewrite -?pair_op ?pair_valid /=.

Tactic Notation "unfold_prod" hyp(H) :=
  rewrite -?pair_op ?pair_valid /= in H;
  let H1 := fresh H in
  try destruct H as [H H1].
