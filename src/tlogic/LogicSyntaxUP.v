From stdpp Require Import coPset gmap namespaces.
From sflib Require Import sflib.
From Fairness Require Import PCM IProp IPM IndexedInvariants.
From iris Require Import bi.big_op.
From iris Require base_logic.lib.invariants.

Module Syntax.

  Section SYNTAX.

    Set Printing Universes.

    Context `{A : Type}.

    Polymorphic Inductive t : Type :=
      atomic (a : A)
    | sepconj (p q : t)
    | pure (P : Prop)
    | ex (* FIXME *)
    | univ (* FIXME *)
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
    | extest {X : Type} (p : X -> t)
    .

    Definition test1 : t :=
      extest (fun (n : nat) => if (n =? 1) then pure (n = 1) else pure (n <> 1)).

    Polymorphic Fixpoint embed@{i j | i < j} (s : t@{i}) : t@{j} :=
      match s with
      | atomic a => atomic a
      | sepconj p q => sepconj (embed p) (embed q)
      | pure P => pure P
      | ex (* FIXME *) => ex
      | univ (* FIXME *) => univ
      (* | own (* Need indexed RA? *) *)
      | and p q => and (embed p) (embed q)
      | or p q => or (embed p) (embed q)
      | impl p q => impl (embed p) (embed q)
      | wand p q => wand (embed p) (embed q)
      | empty => empty
      | persistently p => persistently (embed p)
      | plainly p => plainly (embed p)
      (* | later (p : Syntax) *)
      | upd p => upd (embed p)
      (* | entails p q => Entails (to_semantics p) (to_semantics q) *)
      | @extest X p => extest (fun (x : X) => embed (p x))
      end.
    (* Fixpoint embed {n : nat} (s : @t n) : @t (S n) := *)
    (*   match s with *)
    (*   | atomic a => @atomic (S n) a *)
    (*   | sepconj p q => @sepconj (S n) (embed p) (embed q) *)
    (*   | pure P => @pure (S n) P *)
    (*   | ex (* FIXME *) => @ex (S n) *)
    (*   | univ (* FIXME *) => @univ (S n) *)
    (*   (* | own (* Need indexed RA? *) *) *)
    (*   | and p q => @and (S n) (embed p) (embed q) *)
    (*   | or p q => @or (S n) (embed p) (embed q) *)
    (*   | impl p q => @impl (S n) (embed p) (embed q) *)
    (*   | wand p q => @wand (S n) (embed p) (embed q) *)
    (*   | empty => @empty (S n) *)
    (*   | persistently p => @persistently (S n) (embed p) *)
    (*   | plainly p => @plainly (S n) (embed p) *)
    (*   (* | later (p : Syntax) *) *)
    (*   | upd p => @upd (S n) (embed p) *)
    (*   (* | entails p q => Entails (to_semantics p) (to_semantics q) *) *)
    (*   | @extest _ X p => @extest (S n) X (fun (x : X) => embed (p x)) *)
    (*   end. *)
    About t.
    About embed.

    (* Definition test2 n : @t (S n) := *)
    (*   @extest (S n) (@t n) (fun (s : @t n) => embed s). *)
    Definition test2 : t :=
      @extest t (fun (s : t) => embed s).
    About test2.

    Fail Definition test3 : t :=
      @extest t (fun (s : t) => s).


    (* Definition iType := nat -> Type. *)
    Polymorphic Definition it := fun (_ : nat) => t.

    (* Polymorphic Fixpoint it2 (n : nat) := *)
    (*   match n with *)
    (*   | O => t *)
    (*   | S n' => embed (it2 n') *)
    (*   end. *)

    Definition test4 n : it (S n) :=
      @extest (it n) (fun (s : (it n)) => embed s).
    About test4.

    Definition test5 n : it (S n) :=
      @extest (it n) (fun (s : (it n)) => pure (s = (test4 n))).
    About test5.

test4 = λ n : nat, extest@{test4.u0} (λ s : it@{test4.u1} n, embed@{test4.u1 test4.u0} s)
     : ∀ n : nat, it@{test4.u0} (S n)
test5 = λ n : nat, extest@{test5.u0} (λ s : it@{test4.u0} n, pure@{test5.u0} (s = test4 n))
     : ∀ n : nat, it@{test5.u0} (S n)
test4.u0 < Coq.Relations.Relation_Definitions.1
         < test5.u0
test4.u1 < test4.u0

    Print Universes.
    (* Program Definition Ex {X: Type} (P: X -> iProp'): iProp' := *)
    (*   Seal.sealing *)
    (*     "iProp" *)
    (*     (iProp_intro (fun r => exists x, P x r) _). *)
    (* Next Obligation. *)
    (*   esplits. eapply iProp_mono; eauto. *)
    (* Qed. *)

    (* Program Definition Univ {X: Type} (P: X -> iProp'): iProp' := *)
    (*   Seal.sealing *)
    (*     "iProp" *)
    (*     (iProp_intro (fun r => forall x, P x r) _). *)
    (* Next Obligation. *)
    (*   eapply iProp_mono; eauto. *)
    (* Qed. *)

  End SYNTAX.

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
      | plainly p => IProp.Plainly (to_semantics p)
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
