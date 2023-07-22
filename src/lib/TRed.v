From Fairness Require Export Red.
Require Import String.

Variant red_class: Type := | red_class_cons: string -> red_class.

Class red_db (c: red_class)
      (A: Type)
      (a: A) :=
  mk_red_db {
      red_lemma_type: Type;
      red_lemma: red_lemma_type;
      red_focused_type: Type;
      red_focused: red_focused_type;
      red_next: (_flag + red_class)%type;
    }.
Arguments red_db _ [_] _.
Arguments mk_red_db _ [_] _ [_] _ [_] _ _.
Arguments red_lemma [_ _ _] _.
Arguments red_focused [_ _ _] _.
Arguments red_next [_ _ _] _.

Class red_db_incl (c0 c1: red_class) :=
  mk_red_db_incl { }.
Arguments mk_red_db_incl {_ _}.

#[export] Instance red_db_incl_focus c0 c1 `{red_db_incl c0 c1}
 A (a: A)
  : red_db c1 a :=
  mk_red_db _ _ (@id) a (inr c0).

Ltac _red_tac c f term k :=
  match c with
  | inr ?c =>
      (let tc := fresh "_TC_" in
       unshelve evar (tc: @red_db c _ term);
       [typeclasses eauto; instantiate (f:=_fail); fail|];
       let lem := constr:(red_lemma tc) in
       let _focused := constr:(red_focused tc) in
       let focused := (eval simpl in _focused) in
       let _next := constr:(red_next tc) in
       let next := (eval simpl in _next) in
       _red_tac next f focused ltac:(k; eapply lem))
  | inl ?fl =>
      instantiate (f:=fl); k
  end.

Ltac red_tac c f :=
  match goal with
  | [ |- ?term = _ ] =>
      (_red_tac constr:(inr c: (_flag + red_class)%type) f term ltac:(idtac))
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

    Variable cl_C: red_class.
    Variable cl_B: red_class.
    Variable cl_B_unfold: red_class.
    Variable cl_A: red_class.

    Variable sim: A -> (nat * B) * C -> nat -> Prop.

    (* First Step: Prove Reduction Lemmas *)
    Hypothesis foo_red0: a = b.
    Hypothesis foo_red1: b = c.
    Hypothesis foo_red2: c = d.
    Hypothesis foo_red3: x = y.
    Hypothesis foo_red4: y = z.
    Hypothesis foo_red5: p = q.


    Instance foo_red1_hint: red_db cl_A a :=
      mk_red_db _ _ foo_red0 b (inl _continue).
    Instance foo_red2_hint: red_db cl_A b :=
      mk_red_db _ _ foo_red1 c (inl _continue).
    Instance foo_red3_hint: red_db cl_B_unfold x :=
      mk_red_db _ _ foo_red3 y (inl _continue).
    Instance foo_red4_hint: red_db cl_B_unfold y :=
      mk_red_db _ _ foo_red4 y (inl _continue).
    Instance foo_red5_hint: red_db cl_C p :=
      mk_red_db _ _ foo_red5 q (inl _break).
    Instance cl_B_unfold_cl_B: red_db_incl cl_B_unfold cl_B := mk_red_db_incl.

    Instance foo_red_f_hint a: red_db cl_B (f a) :=
      mk_red_db _ _ (@f_equal _ _ f) a (inr cl_B).

    Lemma foo: forall (n: nat) (H: sim c ((n, f z), q) n),
        sim a ((n, f x), p) n.
    Proof.
      intros n H.
      (prw ltac:(red_tac cl_A) 3 0).
      (prw ltac:(red_tac cl_C) 2 1 0).
      (prw ltac:(red_tac cl_B) 2 2 1 0).
      exact H.
    Qed.
  End FOO.
End TUTORIAL.
