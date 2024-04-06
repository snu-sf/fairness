(* Adam's HOAS *)

(* Set Printing Universes. *)

Inductive type : Type :=
| Nat : type
| Arrow : type -> type -> type.

Infix "-->" := Arrow (right associativity, at level 60).

Section exp.
  Variable var : type -> Type.

  Inductive exp : type -> Type :=
  | Const' : nat -> exp Nat
  | Plus' : exp Nat -> exp Nat -> exp Nat

  | Var : forall t, var t -> exp t
  | App' : forall dom ran, exp (dom --> ran) -> exp dom -> exp ran
  | Abs' : forall dom ran, (var dom -> exp ran) -> exp (dom --> ran).
End exp.

Definition Exp t := forall var, exp var t.

Fixpoint countVars t (e : exp (fun _ => unit) t) : nat :=
  match e with
    | Const' _ _ => 0
    | Plus' _ e1 e2 => countVars _ e1 + countVars _ e2
    | Var _ _ _ => 1
    | App' _ _ _ e1 e2 => countVars _ e1 + countVars _ e2
    | Abs' _ _ _ e' => countVars _ (e' tt)
  end.

(* Definition exp2 := exp (exp var) *)

Definition CountVars t (E : Exp t) : nat := countVars (E _).

Section flatten.
  Variable var : type -> Type.

  Fixpoint flatten t (e : exp (exp var) t) : exp var t :=
    match e with
      | Const' n => Const' n
      | Plus' e1 e2 => Plus' (flatten e1) (flatten e2)
      | Var _ e' => e'
      | App' _ _ e1 e2 => App' (flatten e1) (flatten e2)
      | Abs' _ _ e' => Abs' (fun x => flatten (e' (Var x)))
    end.
End flatten.

Definition Subst t1 t2 (E1 : Exp t1) (E2 : Exp1 t1 t2) : Exp t2 := fun _ =>
  flatten (E2 _ (E1 _)).
