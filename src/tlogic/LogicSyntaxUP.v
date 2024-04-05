From stdpp Require Import coPset gmap namespaces.
From sflib Require Import sflib.
From Fairness Require Import PCM IProp IPM IndexedInvariants.
From iris Require Import bi.big_op.
From iris Require base_logic.lib.invariants.

Module Syntax.

  Local Set Printing Universes.

  Local Notation index := nat.

  Section SYNTAX.

    Context `{A : Type}.

    Polymorphic Inductive t : Type :=
      atomic (a : A)
    | sepconj (p q : t)
    | pure (P : Prop)
    | univ {X : Type} (p : X -> t)
    | ex {X : Type} (p : X -> t)
    (* | own (* Need indexed RA? *) *)
    | and (p q : t)
    | or (p q : t)
    | impl (p q : t)
    | wand (p q : t)
    | empty
    | persistently (p : t)
    | plainly (p : t)
    (* | later (p : Syntax) *)
    | upd (p : t)
    (* | entails (p q : t) *)
    .

    Definition test1 : t :=
      ex (fun (n : nat) => if (n =? 1) then pure (n = 1) else pure (n <> 1)).

    Polymorphic Fixpoint embedT@{i j k | i < k, j < k} (s : t@{i j}) : t@{k k} :=
      match s with
      | atomic a => atomic a
      | sepconj p q => sepconj (embedT p) (embedT q)
      | pure P => pure P
      | @univ X p => univ (fun (x : X) => embedT (p x))
      | @ex X p => ex (fun (x : X) => embedT (p x))
      (* | own (* Need indexed RA? *) *)
      | and p q => and (embedT p) (embedT q)
      | or p q => or (embedT p) (embedT q)
      | impl p q => impl (embedT p) (embedT q)
      | wand p q => wand (embedT p) (embedT q)
      | empty => empty
      | persistently p => persistently (embedT p)
      | plainly p => plainly (embedT p)
      (* | later (p : Syntax) *)
      | upd p => upd (embedT p)
      (* | entails p q => Entails (to_semantics p) (to_semantics q) *)
      end.

    About t.
    About embedT.

    Definition test2 : t :=
      @ex t (fun (s : t) => embedT s).
    About test2.

    Fail Definition test3 : t :=
      @ex t (fun (s : t) => s).

    (* Definition it := fun (_ : index) => t. *)
    Polymorphic Definition it := fun (_ : index) => t.

    Definition test4 n : it (S n) :=
      @ex (it n) (fun (s : (it n)) => embedT s).
    About test4.

    Definition test5 n : it (S n) :=
      @ex (it n) (fun (s : (it n)) => pure (s = (test4 n))).
    About test5.

  End SYNTAX.

  (* Print Universes. *)

  Section INTERP.

    Context `{Σ : GRA.t}.
    Context `{A : Type}.
    Context `{Atomics : @InvSet Σ A}.

    Polymorphic Fixpoint to_semantics (syn : t) : iProp :=
      match syn with
      | atomic a => prop a
      | sepconj p q => Sepconj (to_semantics p) (to_semantics q)
      | pure P => Pure P
      | @univ _ X p => Univ (fun (x : X) => to_semantics (p x))
      | @ex _ X p => Ex (fun (x : X) => to_semantics (p x))
      (* | own (* Need indexed RA? *) *)
      | and p q => And (to_semantics p) (to_semantics q)
      | or p q => Or (to_semantics p) (to_semantics q)
      | impl p q => Impl (to_semantics p) (to_semantics q)
      | wand p q => Wand (to_semantics p) (to_semantics q)
      | empty => Emp
      | persistently p => Persistently (to_semantics p)
      | plainly p => IProp.Plainly (to_semantics p)
      (* | later (p : Syntax) *)
      | upd p => Upd (to_semantics p)
      (* | entails p q => Entails (to_semantics p) (to_semantics q) *)
      end.

  End INTERP.

  Section INVSET.

    Context `{Σ : GRA.t}.
    Context `{A : Type}.
    Context `{Atomics : @InvSet Σ A}.

    Polymorphic Global Instance I {n : index} : @InvSet Σ (@it A n) :=
      {| prop := @to_semantics Σ A Atomics |}.

  End INVSET.

End Syntax.

(* Print Universes. *)

Section INDEXED.

  Local Notation index := nat.

  Context `{Σ : GRA.t}.
  Context `{A : Type}.
  Context `{Atomics : @InvSet Σ A}.

  Definition form1 : @Syntax.it A 3 :=
    @Syntax.ex _ (@Syntax.it A 2) (fun s => Syntax.pure (@prop _ _ (@Syntax.I _ _ Atomics 2) s = (⌜True⌝ ∗ ⌜False⌝)%I)).

  (* Compute @prop _ _ (@Syntax.I _ _ Atomics 3) form1. *)

  Lemma test1 :
    @prop _ _ (@Syntax.I _ _ Atomics 3) form1 =
      (∃ (s : @Syntax.it A 2), ⌜(@prop _ _ (@Syntax.I _ _ Atomics 2) s = (⌜True⌝ ∗ ⌜False⌝)%I)⌝)%I.
  Proof.
    ss.
  Qed.

  Definition form1' : @Syntax.it A 3 :=
    Syntax.ex (fun (s : @Syntax.it A 2) => Syntax.pure (prop (InvSet:=Syntax.I) s = (⌜True⌝ ∗ ⌜False⌝)%I)).

  Set Printing All.
  Print form1'.
  Unset Printing All.

  (* Local Notation it n := (@Syntax.it A n). *)

  (* Definition form1'' : it 3 := *)
  (*   Syntax.ex (fun (s : it 2) => Syntax.pure (prop (InvSet:=Syntax.I) s = (⌜True⌝ ∗ ⌜False⌝)%I)). *)

  Local Set Printing Universes.

  Goal @Syntax.it A 2 = @Syntax.it A 3.
  Proof.
    ss.
  Qed.

  Lemma test_up_type : forall n m, @Syntax.it A n = @Syntax.it A m.
  Proof.
    ss.
  Qed.

  (* Print Universes. *)
(* test_up_type.u0 < test_up_type.u2 *)
(* test_up_type.u1 < test_up_type.u2 *)
(* test_up_type.u2 < Coq.Relations.Relation_Definitions.1 *)
(* test_up_type.u3 = test_up_type.u0 *)
(* test_up_type.u4 = test_up_type.u1 *)

  (* Goal @Syntax.it (@Syntax.it A 1) 2 = @Syntax.it A 3. *)
  (* Proof. *)
  (*   ss. *)
  (* Abort. *)

  (* Goal @Syntax.it nat 2 = @Syntax.it unit 2. *)
  (* Proof. *)
  (*   ss. *)
  (* Abort. *)

  TODO

  Definition inv (N : namespace) P :=
    (∃ p, ∃ i, ⌜prop p = P⌝ ∧ ⌜i ∈ (↑N : coPset)⌝ ∧ OwnI n i p)%I.

  (* Fixpoint IndexedSyntax (n : nat) : Type := *)
  (*   match n with *)
  (*   | O => (@Syntax.t A) *)
  (*   | S n' => (@Syntax.t (IndexedSyntax n')) *)
  (*   end. *)

  (* Fixpoint indexed (n : index) : InvSet (IndexedSyntax n) := *)
  (*   match n with *)
  (*   | O => {| prop := @Syntax.to_semantics _ A Atomics |} *)
  (*   | S n' => {| prop := @Syntax.to_semantics _ (IndexedSyntax n') (indexed n') |} *)
  (*   end. *)

End INDEXED.

Section TEST.

  Local Instance Σ: GRA.t:=
    GRA.of_list [].

  Local Instance Atomics : InvSet unit :=
    {| prop := fun _ => emp%I |}.


  Lemma test0 :
    forall (n : nat),
      @prop _ _ (Syntax.InvSet) (Syntax.pure (@prop _ _ Syntax.InvSet (Syntax.sepconj (Syntax.pure True) (Syntax.atomic tt)) = (⌜True⌝ ∗ emp)%I))
      =
        (⌜(@prop _ _ (Syntax.InvSet) (Syntax.sepconj (Syntax.pure True) (Syntax.atomic tt)) = (⌜True⌝ ∗ emp)%I)⌝)%I.
  Proof.
    i. ss.
  Qed.

  Definition inv (N : namespace) P :=
    (∃ p, ∃ i, ⌜prop p = P⌝ ∧ ⌜i ∈ (↑N : coPset)⌝ ∧ OwnI n i p)%I.

  Lemma test1 :
    forall (n : nat),
      @prop _ _ (SynInvs (S n)) (Syntax.pure (@prop _ _ (SynInvs n) (Syntax.sepconj (Syntax.pure True) (Syntax.pure False)) = (⌜True⌝ ∗ ⌜False⌝)%I))
      =
        (⌜(@prop _ _ (SynInvs n) (Syntax.sepconj (Syntax.pure True) (Syntax.pure False)) = (⌜True⌝ ∗ ⌜False⌝)%I)⌝)%I.
  Proof.
    i. ss.
  Qed.

  Lemma test2 :
    forall (n : nat),
      @prop _ _ (SynInvs (n)) (Syntax.pure (@prop _ _ (SynInvs n) (Syntax.sepconj (Syntax.pure True) (Syntax.pure False)) = (⌜True⌝ ∗ ⌜False⌝)%I))
      =
        (⌜(@prop _ _ (SynInvs n) (Syntax.sepconj (Syntax.pure True) (Syntax.pure False)) = (⌜True⌝ ∗ ⌜False⌝)%I)⌝)%I.
  Proof.
    i. ss.
  Qed.

End TEST.
