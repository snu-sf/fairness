From Fairness Require Export Red.
Require Import String.

Variant red_class: Type := | red_class_cons: string -> red_class.

Class commute_db (c: red_class)
      (A: Type)
      (a: A) :=
  mk_commute_db {
      commute_lemma_type: Type;
      commute_lemma: commute_lemma_type;
    }
.
Arguments commute_db _ [_] _.
Arguments mk_commute_db _ [_] _ [_] _.
Arguments commute_lemma [_ _ _] _.

Class unfold_db (c: red_class)
      (A: Type)
      (a: A) :=
  mk_unfold_db {
      unfold_lemma_type: Type;
      unfold_lemma: unfold_lemma_type;
    }
.
Arguments unfold_db _ [_] _.
Arguments mk_unfold_db _ [_] _ [_] _.
Arguments unfold_lemma [_ _ _] _.

Class focus_db (c: red_class)
      (A: Type)
      (a: A) :=
  mk_focus_db {
      focus_lemma_type: Type;
      focus_lemma: focus_lemma_type;
      focus_next_type: Type;
      focus_next: focus_next_type;
    }
.
Arguments focus_db _ [_] _.
Arguments mk_focus_db _ [_] _ [_] _ [_] _.
Arguments focus_lemma [_ _ _] _.
Arguments focus_next [_ _ _] _.

#[export] Instance focus_id c A (a: A): focus_db c a :=
  mk_focus_db _ _ (@id) a.

Ltac _commute_tac c f term :=
  (let tc := fresh "_TC_" in
   unshelve evar (tc: @commute_db c _ term);
   [typeclasses eauto; instantiate (f:=_fail); fail|];
   let lem := constr:(commute_lemma tc) in
   instantiate (f:=_continue);
   eapply lem).

Ltac _unfold_tac c f term k :=
  (let tc := fresh "_TC_" in
   unshelve evar (tc: @unfold_db c _ term);
   [typeclasses eauto; instantiate (f:=_fail); fail|];
   let lem := constr:(unfold_lemma tc) in
   instantiate (f:=_break);
   k; eapply lem).

Ltac _red_tac c f term k :=
  (let tc := fresh "_TC_" in
   unshelve evar (tc: @focus_db c _ term);
   [typeclasses eauto; instantiate (f:=_fail); fail|];
   let lem := constr:(focus_lemma tc) in
   let _next := constr:(focus_next tc) in
   let next := (eval simpl in _next) in
   _unfold_tac c f next ltac:(k; eapply lem)).

Ltac red_tac c f :=
  match goal with
  | [ |- ?term = _ ] =>
      (_commute_tac c f term)
      ||
      (_red_tac c f term ltac:(idtac))
  end
.

Module TUTORIAL.
  Section FOO.
    (* Variables *)
    Variable A B C: Type.
    Variable a b c d: A.
    Variable x y z: B.
    Variable p q: C.
    Variable f: B -> B.

    Variable cl: red_class.

    Variable sim: A -> (nat * B) * C -> nat -> Prop.

    (* First Step: Prove Reduction Lemmas *)
    Hypothesis foo_red0: a = b.
    Hypothesis foo_red1: b = c.
    Hypothesis foo_red2: c = d.
    Hypothesis foo_red3: x = y.
    Hypothesis foo_red4: y = z.
    Hypothesis foo_red5: p = q.

    Instance foo_red1_hint: commute_db cl a :=
      mk_commute_db _ _ foo_red0.
    Instance foo_red2_hint: commute_db cl b :=
      mk_commute_db _ _ foo_red1.
    Instance foo_red3_hint: unfold_db cl x :=
      mk_unfold_db _ _ foo_red3.
    Instance foo_red4_hint: unfold_db cl y :=
      mk_unfold_db _ _ foo_red4.
    Instance foo_red5_hint: unfold_db cl p :=
      mk_unfold_db _ _ foo_red5.
    Instance foo_red_f_hint a: focus_db cl (f a) :=
      mk_focus_db _ _ (@f_equal _ _ f) a.

    Lemma foo: forall (n: nat) (H: sim c ((n, z), q) n),
        sim a ((n, x), p) n.
    Proof.
      intros n H.
      (prw ltac:(red_tac cl) 2 2 1 0).
      (prw ltac:(red_tac cl) 2 2 1 0).
      (prw ltac:(red_tac cl) 2 1 0).
      (prw ltac:(red_tac cl) 3 0).
      exact H.
    Qed.
  End FOO.
End TUTORIAL.
