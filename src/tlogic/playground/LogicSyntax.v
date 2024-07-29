From stdpp Require Import coPset gmap namespaces.
From sflib Require Import sflib.
From Fairness Require Import PCM IPM IndexedInvariants.
From iris Require Import bi.big_op.
From iris Require base_logic.lib.invariants.

Module Syntax.

  Section CONST.

    (* Variant con0 : Type := *)
    (*   | atomic *)
    (*   | pure *)
    (*   | empty. *)

    (* Variant con1 : Type := *)
    (*   | persistently *)
    (*   | plainly *)
    (*   | upd. *)

    (* Variant con2 : Type := *)
    (*   | sepconj *)
    (*   | and *)
    (*   | or *)
    (*   | impl *)
    (*   | wand. *)

    (* Variant conq {n : nat} : Type := *)
    (*   | univ (X : Type) *)
    (*   | ex (X : Type). *)

    (* Definition conq_dom {n : nat} (c : @conq n) : Type := *)
    (*   match c with *)
    (*   | univ X | ex X => X *)
    (*   end. *)

    (* Print Universes. *)

    (* Definition conq_embed (n : nat) : @conq n -> @conq (S n) := *)
    (*   fun cq => match cq with | univ X => univ X | ex X => ex X end. *)

  End CONST.

  Section SYNTAX.

    Set Printing Universes.

    (* Definition iType (T : Type) := Type. *)
    (* Definition iType0 (T : Type) := iType (iType T). *)
    (* Inductive iType : Type := | itype_base (t : Type) | itype_cons (t : iType). *)
    (* Definition iType0 := itype_base Type. *)
    (* Definition iType2 := itype_cons iType0. *)

    (* Definition iType0 := Type. *)
    (* (* Definition iType0 (T : Type) := Type. *) *)
    (* Definition iType1_ (T : Type) := Type. *)
    (* Definition iType1 := iType1_ iType0. *)
    (* Definition iType2_ (T : Type) := Type. *)
    (* Definition iType2 := iType2_ iType1. *)

    (* Definition iType1' := iType1_ iType0. *)
    (* Definition iType2' := iType1_ iType1'. *)

    (* Record Index (n : nat) : Type := Index_intro { index := n }. *)
    (* Definition iType__ (n : nat) := Type -> Type. *)

    (* Fixpoint iType_ (n : nat) (T : Type) := *)
    (*   match n with *)
    (*   | O => T *)
    (*   | S n' => let f := (fun (T' : Type) => Type) in f (iType_ n' T) *)
    (*   end. *)

    (* Record iType_ := iType_intro { iType_fun : Type -> Type }. *)

    (* Fixpoint iType (n : nat) : Type := *)
    (*   match n with *)
    (*   | O => iType_fun {| iType_fun := fun (T : Type) => Type |} Type *)
    (*   | S n' => iType_fun {| iType_fun := fun (T : Type) => Type |} (iType n') *)
    (*   end. *)

    (* Definition iType0 := iType 0. *)
    (* Definition iType1 := iType 1. *)

    (* Definition iType0 : iType 0 := {| iType_fun := fun (T : Type) => Type |}. *)

    (* Print Universes. *)

    (* Definition iType_ : Type := Type -> Type. *)
    (* Definition iType : Type := Type. *)

    (* Print Universes. *)

    (* Definition iType0 := iType_ Type. *)
    (* Definition iType := iType_ (iType_). *)


(* iType1_ =  *)
(* λ _ : Type@{iType1_.u0}, Type@{iType1_.u1} *)
(*      : Type@{iType1_.u0} → Type@{iType1_.u1+1} *)
(* iType1 = iType1_ iType0 *)
(*      : Type@{iType1_.u1+1} *)
(* iType2_ =  *)
(* λ _ : Type@{iType2_.u0}, Type@{iType2_.u1} *)
(*      : Type@{iType2_.u0} → Type@{iType2_.u1+1} *)
(* iType2 = iType2_ iType1 *)
(*      : Type@{iType2_.u1+1} *)
(* iType1_.u1 < iType2_.u0 *)


    Context `{A : Type}.

    (* Inductive t {n : nat} : iType n := *)
    (* | c0 (c : con0) *)
    (* | c1 (c : con1) (p : t) *)
    (* | c2 (c : con2) (p q : t) *)
    (* | cq {m : nat} (c : @conq m) (p : conq_dom c -> t) *)
    (* . *)

    (* Fixpoint embed (n : nat) (s : @t n) : @t (S n) := *)
    (*   match s with *)
    (*   | c0 c => c0 c *)
    (*   | c1 c p => c1 c (embed n p) *)
    (*   | c2 c p q => c2 c (embed n p) (embed n q) *)
    (*   | @cq _ m c p => @cq _ m c (fun x => embed n (p x)) *)
    (*   end. *)

    (* Definition test2 n : @t (S n) := *)
    (*   @cq _ _ (@ex n (@t n)) (fun (s : t) => embed n s). *)
    (* About test2. *)

    Inductive t {X : Type} : Type :=
      atomic (a : A)
    | sepconj (p q : t)
    | pure (P : Prop)
    | univ {Y : Type} (p : X -> @t Y)
    | ex {Y : Type} (p : X -> @t Y)
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

    Definition test1 : @t nat :=
      @ex _ bool (fun n => @ex _ unit (fun b => pure (n = 1 /\ b = true))).

    Definition test1' : @t nat :=
      ex (fun n => @ex _ unit (fun b => pure (n = 1 /\ b = true))).

    Definition test2 : @t (@t nat) :=
      @ex _ (bool) (fun (s : @t nat) => pure (s = @ex _ bool (fun (n : nat) => pure (n = 1)))).

    Fail Definition test2' : @t nat :=
      @ex _ (@t bool) (fun (s : @t nat) => pure (s = pure (1 = 1))).

    (* Fixpoint ind (n : nat) (X : Type) : Type := *)
    (*   match n with *)
    (*   | O => X *)
    (*   | S n' => @t (list (ind n' X)) *)
    (*   end. *)
    Fixpoint ind (n : nat) (X : Type) : Type :=
      match n with
      | O => X
      | S n' => @t (ind n' X)
      end.

    Set Printing All.
    Compute ind 3 nat.

    (* Definition test3 : ind 2 nat := *)
    (*   @ex _ (bool) (fun (s : ind 1 nat) => pure (s = @ex _ bool (fun (n : list nat) => pure (n = [1])))). *)
    Definition test3 : ind 2 nat :=
      @ex _ (bool) (fun (s : ind 1 nat) => pure (s = @ex _ bool (fun (n : nat) => pure (n = 1)))).

    Definition test3' {X : Type} : @t X -> nat := fun _ => 0.
    Goal test3' test3 = 0. ss. Qed.

    Lemma test3 :
      @ex _ (bool) (fun (s : @t nat) => pure (s = @ex _ bool (fun (n : nat) => pure (n = 1)))) : ind 2 nat.

    (* Fixpoint indexed (n : nat) (X : Type) : Type := *)
    (*   match n with *)
    (*   | O => @t X *)
    (*   | S n' => @t (indexed n' X) *)
    (*   end. *)

    (* Compute indexed 3 unit. *)

    (* Definition  *)

    (* Definition test2 n : t := *)
    (*   ex (fun (s : t) => pure True). *)

    Definition test2 n : t :=
      @ex (indexed n unit) (unit) (fun (s : indexed n unit) => pure True).
    About test2.

    (* Fixpoint embed {n m : nat} (s : @t n) : @t m := *)
    (*   match s with *)
    (*   | atomic a => atomic a *)
    (*   | sepconj p q => sepconj (embed p) (embed q) *)
    (*   | pure P => pure P *)
    (*   | univ p => univ (fun x => embed (p x)) *)
    (*   | ex p => ex (fun x => embed (p x)) *)
    (*   | and p q => and (embed p) (embed q) *)
    (*   | or p q => or (embed p) (embed q) *)
    (*   | impl p q => impl (embed p) (embed q) *)
    (*   | wand p q => wand (embed p) (embed q) *)
    (*   | empty => empty *)
    (*   | persistently p => persistently (embed p) *)
    (*   | plainly p => plainly (embed p) *)
    (*   | upd p => upd (embed p) *)
    (*   end. *)

    (* Definition test2 n : @t (S n) := *)
    (*   @ex (S n) (@t n) (fun (s : t) => @embed n (S n) s). *)
    (* About test2. *)


    (* Inductive t : Type := *)
    (*   atomic (a : A) *)
    (* | sepconj (p q : t) *)
    (* | pure (P : Prop) *)
    (* | univ {X : Type} (p : X -> t) *)
    (* | ex {X : Type} (p : X -> t) *)
    (* (* | own (* Need indexed RA? *) *) *)
    (* | and (p q : t) *)
    (* | or (p q : t) *)
    (* | impl (p q : t) *)
    (* | wand (p q : t) *)
    (* | empty *)
    (* | persistently (p : t) *)
    (* | plainly (p : t) *)
    (* (* | later (p : Syntax) *) *)
    (* | upd (p : t) *)
    (* (* | entails (p q : t) *) *)
    (* . *)

    Definition test1 : t :=
      extest (fun (n : nat) => if (n =? 1) then pure (n = 1) else pure (n <> 1)).

  End SYNTAX.

  Section FORMULA.

    Context `{A : Type}.

    Record formula {n : nat} :=
      formula_intro {
          formula_index := n;
          formula_syntax :> @t A;
        }.

    Program Definition atomicf {n : nat} (a : A) : formula :=
      formula_intro n (atomic a).

    Program Definition sepconjf {a n : nat} (p q : @formula a) : formula :=
      formula_intro n (sepconj p q).

    Program Definition puref {n : nat} (P : Prop) : formula :=
      formula_intro n (pure P).

    Program Definition extestf {a n : nat} {X : Type} (p : X -> (@formula a)) : formula :=
      formula_intro n (@extest A X (fun (x : X) => (p x))).

    Definition test2 (n : nat) : formula :=
      @extestf _ (S n) (@formula n) (fun (s : formula) => @sepconjf (S n) s s).
    About test2.


  End FORMULA.

  Section INTERP.

    Context `{Σ : GRA.t}.
    Context `{A : Type}.
    Context `{Atomics : @InvSet Σ A}.

    Fixpoint to_semantics (syn : t) : iProp :=
      match syn with
      | atomic a => prop a
      | sepconj p q => Sepconj (to_semantics p) (to_semantics q)
      | pure P => Pure P
      | ex (* FIXME *) => Emp
      | univ (* FIXME *) => Emp
      (* | own (* Need indexed RA? *) *)
      | and p q => And (to_semantics p) (to_semantics q)
      | or p q => Or (to_semantics p) (to_semantics q)
      | impl p q => Impl (to_semantics p) (to_semantics q)
      | wand p q => Wand (to_semantics p) (to_semantics q)
      | Syntax.emp => Emp
      | persistently p => Persistently (to_semantics p)
      | plainly p => .Plainly (to_semantics p)
      (* | later (p : Syntax) *)
      | upd p => Upd (to_semantics p)
      (* | entails p q => Entails (to_semantics p) (to_semantics q) *)
      | extest x p => Ex
      end.

  End INTERP.

  Section INVSET.

    Context `{Σ : GRA.t}.
    Context `{A : Type}.
    Context `{Atomics : @InvSet Σ A}.

    Global Instance InvSet : @IndexedInvariants.InvSet Σ (@t A) :=
      {| prop := @to_semantics Σ A Atomics |}.

  End INVSET.

End Syntax.

Section INDEXED.

  Notation index := nat.

  Context `{Σ : GRA.t}.
  Context `{A : Type}.
  Context `{Atomics : @InvSet Σ A}.

  Definition SynInvs : nat -> (InvSet (@Syntax.t A)) :=
    fun (n : index) => (@Syntax.InvSet _ _ Atomics).

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
