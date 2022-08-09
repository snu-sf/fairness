Tactic Notation "mrewrite" uconstr(EQ) "in" "*" :=
  rewrite EQ in *.
Tactic Notation "mrewrite" uconstr(EQ) "in" "*" :=
  rewrite EQ in *.
Tactic Notation "mrewrite" uconstr(EQ) "in" ident(H) :=
  rewrite EQ in H.
Tactic Notation "mrewrite" uconstr(EQ) :=
  rewrite EQ.
Tactic Notation "mrewrite" "<-" uconstr(EQ) "in" "*" :=
  rewrite <- EQ in *.
Tactic Notation "mrewrite" "<-" uconstr(EQ) "in" ident(H) :=
  rewrite <- EQ in H.
Tactic Notation "mrewrite" "<-" uconstr(EQ) :=
  rewrite <- EQ.

Tactic Notation "mrewrite" "!" uconstr(EQ) "in" "*" :=
  rewrite ! EQ in *.
Tactic Notation "mrewrite" "!" uconstr(EQ) "in" ident(H) :=
  rewrite ! EQ in H.
Tactic Notation "mrewrite" "!" uconstr(EQ) :=
  rewrite ! EQ.
Tactic Notation "mrewrite" "<-" "!" uconstr(EQ) "in" "*" :=
  rewrite <- ! EQ in *.
Tactic Notation "mrewrite" "<-" "!" uconstr(EQ) "in" ident(H) :=
  rewrite <- ! EQ in H.
Tactic Notation "mrewrite" "<-" "!" uconstr(EQ) :=
  rewrite <- ! EQ.

Tactic Notation "rewrite" uconstr(EQ) "in" "*" :=
  mrewrite EQ in *.
Tactic Notation "rewrite" uconstr(EQ) "in" ident(H) :=
  mrewrite EQ in H.
Tactic Notation "rewrite" uconstr(EQ) :=
  mrewrite EQ.
Tactic Notation "rewrite" "<-" uconstr(EQ) "in" "*" :=
  mrewrite <- EQ in *.
Tactic Notation "rewrite" "<-" uconstr(EQ) "in" ident(H) :=
  mrewrite <- EQ in H.
Tactic Notation "rewrite" "<-" uconstr(EQ) :=
  mrewrite <- EQ.

Tactic Notation "rewrite" "!" uconstr(EQ) "in" "*" :=
  mrewrite ! EQ in *.
Tactic Notation "rewrite" "!" uconstr(EQ) "in" ident(H) :=
  mrewrite ! EQ in H.
Tactic Notation "rewrite" "!" uconstr(EQ) :=
  mrewrite ! EQ.
Tactic Notation "rewrite" "<-" "!" uconstr(EQ) "in" "*" :=
  mrewrite <- ! EQ in *.
Tactic Notation "rewrite" "<-" "!" uconstr(EQ) "in" ident(H) :=
  mrewrite <- ! EQ in H.
Tactic Notation "rewrite" "<-" "!" uconstr(EQ) :=
  mrewrite <- ! EQ.

Ltac mf_equal := f_equal.
Ltac f_equal := mf_equal.

Module REWRITETEST.
  Section TEST.
    Variable x y: nat.
    Hypothesis XY: x = y.

    Goal forall (a b c: nat) (EQ0: a = b) (EQ1: a = c) (EQ2: c = b) (EQ3: x = y),
        a + b + y = c + c + x.
    Proof.
      (* intros. *)
      (* rewrite EQ0 in *. Undo. *)
      (* rewrite EQ1 in EQ0. Undo. *)
      (* rewrite EQ0. Undo. *)
      (* rewrite <- EQ0 in *. Undo. *)
      (* rewrite <- EQ2 in EQ0. Undo. *)
      (* rewrite <- EQ2. Undo. *)
      (* rewrite ! EQ0 in *. Undo. *)
      (* rewrite ! EQ1 in EQ0. Undo. *)
      (* rewrite ! EQ0. Undo. *)
      (* rewrite <- ! EQ0 in *. Undo. *)
      (* rewrite <- ! EQ2 in EQ0. Undo. *)
      (* rewrite <- ! EQ2. Undo. *)
      (* rewrite XY in *. Undo. *)
      (* rewrite XY in EQ3. Undo. *)
      (* rewrite XY. Undo. *)
      (* rewrite <- XY in *. Undo. *)
      (* rewrite <- XY in EQ3. Undo. *)
      (* rewrite <- XY. Undo. *)
      (* rewrite ! XY in *. Undo. *)
      (* rewrite ! XY in EQ3. Undo. *)
      (* rewrite ! XY. Undo. *)
      (* rewrite <- ! XY in *. Undo. *)
      (* rewrite <- ! XY in EQ3. Undo. *)
      (* rewrite <- ! XY. Undo. *)
    Abort.
  End TEST.
End REWRITETEST.

Require Import Basics.
Notation "f ∘ g" := (fun x => (f (g x))).

Typeclasses Opaque flip.

Require Export List.
