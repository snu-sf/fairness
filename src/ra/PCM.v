From sflib Require Import sflib.
Require Export ZArith.
(* Require Export Znumtheory. *)
Require Import String.
Require Import ClassicalChoice ChoiceFacts.
Require Import Coq.Classes.RelationClasses.
Require Import Lia.
Require Import Program.
From stdpp Require coPset gmap.
From Fairness Require Import Axioms.
From Fairness Require Import ucmra_list.
From iris.algebra Require Import cmra updates functions.

From iris.prelude Require Import prelude options.

Set Implicit Arguments.




Require Export String.
Module Type SEAL.
  Parameter sealing: string -> forall X: Type, X -> X.
  Parameter sealing_eq: forall key X (x: X), sealing key x = x.
End SEAL.
Module Seal: SEAL.
  Definition sealing (_: string) X (x: X) := x.
  Lemma sealing_eq key X (x: X): sealing key x = x.
  Proof. reflexivity. Qed.
End Seal.

Ltac seal_with key x :=
  replace x with (Seal.sealing key x); [|eapply Seal.sealing_eq].
Ltac seal x :=
  let key := fresh "key" in
  assert (key:= "_deafult_");
  seal_with key x.
Ltac unseal x :=
  match (type of x) with
  | string => repeat rewrite (@Seal.sealing_eq x) in *; try clear x
  | _ => repeat rewrite (@Seal.sealing_eq _ _ x) in *;
         repeat match goal with
                | [ H: string |- _ ] => try clear H
                end
  end
.

(* TODO: Auxillary discrete_fun lemmas. Move to somewhere else. *)
Section discrete_fun.
  (** Depends on axiom of dependent choice.  *)

  Lemma discrete_fun_included_spec_2
      A (Ms : A -> ucmra)
      (f0 f1 : discrete_fun Ms)
      (EXT : ∀ a, (f0 a) ≼ (f1 a))
    :
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
    excluded middle. However that would create two instance of [EqDecision] for all types [A],
    which will make two instances of [EqDecision] for decidable types causing all kinds of
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
      | in_right => ε
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

  Lemma embed_wf
        a
        (WF: ✓ embed a)
    :
      <<WF: ✓ a>>
  .
  Proof. by rewrite /embed discrete_fun_singleton_valid cmra_transport_valid in WF. Qed.

  Lemma wf_embed
        a
        (WF: ✓ a)
    :
      <<WF: ✓ embed a >>
  .
  Proof. by rewrite /NW /embed discrete_fun_singleton_valid cmra_transport_valid. Qed.

  Global Instance embed_ne : NonExpansive (@embed A Σ _).
  Proof. by intros ????; apply discrete_fun_singleton_ne, cmra_transport_ne. Qed.
  Global Instance embed_proper : Proper ((≡) ==> (≡)) (@embed A Σ _) := ne_proper _.

  Lemma embed_add
        a0 a1
    :
      <<EQ: embed a0 ⋅ embed a1 ≡ embed (a0 ⋅ a1) >>
    .
  Proof. by rewrite /NW /embed discrete_fun_singleton_op cmra_transport_op. Qed.

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

  Lemma embed_core a : embed (core a) ≡ core (embed a).
  Proof. by rewrite /embed discrete_fun_singleton_core cmra_transport_core. Qed.

  (* Note: NOT a general lemma for [cmra_transport]. Tailed for the proof pattern
    of [GRA]. I.e., upstreaming this to iris doesn't make sense. *)
  Local Lemma cmra_transport_unit {B C : ucmra} (H : B = C) : cmra_transport (f_equal _ H) ε = ε.
  Proof. by destruct H. Qed.
  Lemma embed_unit : embed ε ≡ ε.
  Proof. by rewrite /embed cmra_transport_unit discrete_fun_singleton_unit. Qed.

End lemmas.

  Section GETSET.
    Variable ra: ucmra.
    Variable gra: t.
    Context `{!inG ra gra}.

    Section GETSET.
    Variable get: cmra_car ra.
    Variable set: (cmra_car ra) -> unit.

    (* own & update can be lifted *)
    (* can we write spec in terms of own & update, not get & set? *)
    (* how about add / sub? *)
    Program Definition get_lifted: cmra_car gra :=
      discrete_fun_singleton inG_id _.
    Next Obligation.
      apply (cmra_transport (f_equal _ inG_prf) get).
    Defined.

    (* Program Definition set_lifted: cmra_car construction gra -> unit := *)
    (*   fun n => if Nat.eq_dec n inG_id then _ else URA.unit. *)
    (* Next Obligation. *)
    (*   apply (ra_transport inG_prf get). *)
    (* Defined. *)
    End GETSET.

    Section HANDLER.
    Variable handler: cmra_car ra -> cmra_car ra.
    Local Obligation Tactic := idtac.
    Program Definition handler_lifted: cmra_car gra -> cmra_car gra :=
      fun st0 => fun n => if Nat.eq_dec n inG_id then _ else st0 n
    .
    Next Obligation.
      i. subst. simpl in st0. specialize (st0 inG_id).
      rewrite /= -inG_prf in st0. specialize (handler st0). rewrite <- inG_prf. apply handler.
    Defined.

    End HANDLER.

  End GETSET.

  Fixpoint point_wise_wf (Ml: ucmra_list) (x: of_list Ml) (n: nat) :=
  match n with
  | O => True
  | S n' => ✓ (x n') ∧ point_wise_wf x n'
  end.

  Definition point_wise_wf_lift (Ml: ucmra_list) (x: of_list Ml)
             (POINT: point_wise_wf x (UList.length Ml))
    :
      ✓ x.
  Proof.
    intro i. unfold of_list in *.
    assert (WF: ∀ (n m: nat)
                       (POINT: point_wise_wf x n)
                       (LT: (m < n)%nat),
               ✓ (x m)).
    { induction n.
      { i. inv LT. }
      { i. ss. des. inv LT; auto. }
    }
    destruct (le_lt_dec (UList.length Ml) i).
    { generalize (x i). simpl. rewrite UList.nth_overflow; auto. intros []; done. }
    { eapply WF; eauto. }
  Qed.
End GRA.
Coercion GRA.to_URA: GRA.t >-> ucmra.

Global Opaque GRA.to_URA.
(* Definition ε `{Σ: GRA.t}: Σ := URA.unit. *)

(***
Choose: non-det
Take: angelic non-det
(*** empty choose : NB ***)
(*** empty take : UB ***)
x <- Choose X ;; guarantee (P x) ;; k x   (~=) x <- Choose { X | P x } ;; k x
x <- Take X   ;; assume (P x)    ;; k x   (~=) x <- Take { X | P x }   ;; k x
guarantee P ;; assume P ;; k              (~=) guarantee P ;; k
x <- Take X ;; pure ;; k x                (>=) pure ;; x <- Take X ;; k x
pure ;; x <- Choose X ;; k x              (>=) x <- Choose X ;; pure ;; k x
______________caller______________    _________________callee_________________   _caller_
x0 <- Choose X ;; guarantee (P x0) ;; (x1 <- Take X ;; assume (P x1) ;; k1 x1) ;; k0 x0
(<=)
x0 <- Choose X ;; x1 <- Take X ;; guarantee (P x0) ;; assume (P x1) ;; k1 x1 ;; k0 x0
(<=)
x <- Choose X ;; guarantee (P x) ;; assume (P x) ;; k1 x ;; k0 x
(<=)
x <- Choose X ;; guarantee (P x) ;; k1 x ;; k0 x
Goal forall X Y (k: X -> Y),
    x <- trigger (EChoose X) ;; Ret (k x) =
    y <- trigger (EChoose {y | exists x, y = k x}) ;; Ret (proj1_sig y)
.
Abort.
***)


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
  try rewrite !(assoc op);
  repeat (try rewrite !right_id; try rewrite !left_id);
  match goal with
  | [|- ?lhs ≡ (_ ⋅ _) ] =>
    let a := r_first lhs in
    try rewrite -!(comm op a);
    try rewrite -!(assoc op);
    try (f_equiv; r_solve)
  | _ => try reflexivity
  end
.

(* Solve inclusion of cmra [op]s, with permuation. *)
Ltac r_solve_included :=
  try rewrite !(assoc op);
  repeat (try rewrite !right_id; try rewrite !left_id);
  match goal with
  | [|- (?lhs ⋅ _) ≼ (_ ⋅ _) ] =>
    let a := r_first lhs in
    try rewrite -!(comm op a);
    repeat rewrite -!(assoc op);
    apply cmra_mono_l;
    try (r_solve_included)
  | [|- ?lhs ≼ (_ ⋅ _) ] =>
    try rewrite -!(comm op lhs);
    repeat rewrite -!(assoc op);
    try (apply cmra_included_l)
  | _ => try (reflexivity || apply ucmra_unit_least)
  end
.

(* [✓ a], [H : ✓ b] where [a ≼ b] syntactically. *)
Ltac r_wf H := eapply cmra_valid_included; [exact H|]; r_solve_included.

Ltac g_wf_tac :=
  cbn; rewrite !right_id !left_id;
  apply GRA.point_wise_wf_lift; ss; splits; repeat rewrite !discrete_fun_lookup_op; unfold GRA.embed; ss;
  repeat rewrite !right_id; repeat rewrite !left_id; try apply ucmra_unit_valid.

Tactic Notation "unfold_prod" :=
  try rewrite -!pair_op;
  rewrite pair_valid;
  simpl.

Tactic Notation "unfold_prod" hyp(H) :=
  try rewrite -!pair_op in H;
  rewrite pair_valid in H;
  simpl in H;
  let H1 := fresh H in
  destruct H as [H H1].
