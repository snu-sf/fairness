(** list of discrete [ucmra]s. Exists to avoid universal inconsistency of iris and
  list with relations. See https://gitlab.mpi-sws.org/iris/stdpp/-/merge_requests/555
  for why this is needed. *)
From iris.algebra Require Import cmra.
Inductive ucmra_list : Type :=
 | nil : ucmra_list
 | cons (a : ucmra) (l : ucmra_list) `{CmraDiscrete a} : ucmra_list.

Declare Scope ulist_scope.
Delimit Scope ulist_scope with ucmra_list.
Bind Scope ulist_scope with ucmra_list.

Infix "::" := cons (at level 60, right associativity) : ulist_scope.

Local Open Scope ulist_scope.

Module UList.
Definition length : ucmra_list -> nat :=
  fix length l :=
  match l with
   | nil => O
   | _ :: l' => S (length l')
  end.

(** Concatenation of two lists *)

Definition app : ucmra_list -> ucmra_list -> ucmra_list :=
  fix app l m :=
  match l with
   | nil => m
   | a :: l1 => a :: app l1 m
  end.

Infix "++" := app (right associativity, at level 60) : ulist_scope.

#[local] Open Scope bool_scope.
Open Scope ulist_scope.

(** Standard notations for lists.
In a special module to avoid conflicts. *)
Module UListNotations.
Notation "[ ]" := nil (format "[ ]") : ulist_scope.
Notation "[ x ]" := (cons x nil) : ulist_scope.
Notation "[ x ; y ; .. ; z ]" :=  (cons x (cons y .. (cons z nil) ..))
  (format "[ '[' x ;  '/' y ;  '/' .. ;  '/' z ']' ]") : ulist_scope.
End UListNotations.

Import UListNotations.



Section Elts.


  (*****************************)
  (** ** Nth element of a list *)
  (*****************************)

  Fixpoint nth (n:nat) (l:ucmra_list) (default:ucmra) {struct l} : ucmra :=
    match n, l with
      | O, x :: l' => x
      | O, [] => default
      | S m, [] => default
      | S m, x :: t => nth m t default
    end.

  Lemma nth_overflow : forall l n d, length l <= n -> nth n l d = d.
  Proof.
    intro l; induction l as [|? ? IHl DISC]; intro n; destruct n;
     simpl; intros d H; auto.
    - inversion H.
    - apply IHl. now apply Nat.succ_le_mono.
  Qed.

  (* Fixpoint nth_ok (n:nat) (l:ucmra_list) (default:ucmra) {struct l} : bool :=
    match n, l with
      | O, x :: l' => true
      | O, [] => false
      | S m, [] => false
      | S m, x :: t => nth_ok m t default
    end. *)

  (* Fixpoint nth_error (l:ucmra_list) (n:nat) {struct n} : option ucmra :=
    match n, l with
      | O, x :: _ => Some x
      | S n, _ :: l => nth_error l n
      | _, _ => None
    end. *)

  (* Definition nth_default (default:ucmra) (l:ucmra_list) (n:nat) : ucmra :=
    match nth_error l n with
      | Some x => x
      | None => default
    end. *)

End Elts.
End UList.

Export UList.UListNotations.
