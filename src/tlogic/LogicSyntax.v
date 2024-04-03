From stdpp Require Import coPset gmap namespaces.
From sflib Require Import sflib.
From Fairness Require Import PCM IProp IPM IndexedInvariants.
From iris Require Import bi.big_op.
From iris Require base_logic.lib.invariants.

Module Syntax.

  Section SYNTAX.

    Context `{A : Type}.

    Inductive t : Type :=
      atomic (a : A)
    | sepconj (p q : t)
    | pure (p : Prop)
    | ex (* FIXME *)
    | univ (* FIXME *)
    (* | own (* Need indexed RA? *) *)
    | and (p q : t)
    | or (p q : t)
    | impl (p q : t)
    | wand (p q : t)
    | emp
    | persistently (p : t)
    | plainly (p : t)
    (* | later (p : Syntax) *)
    | upd (p : t)
    (* | entails (p q : t) *)
    .

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
      | pure p => Pure p
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
      end.

  End INTERP.

End Syntax.

Section INDEXED.

  Notation index := nat.

  Context `{Σ : GRA.t}.
  Context `{A : Type}.
  Context `{Atomics : @InvSet Σ A}.

  Fixpoint IndexedSyntax (n : nat) : Type :=
    match n with
    | O => (@Syntax.t A)
    | S n' => (@Syntax.t (IndexedSyntax n'))
    end.

  Fixpoint indexed (n : index) : InvSet (IndexedSyntax n) :=
    match n with
    | O => {| prop := @Syntax.to_semantics _ A Atomics |}
    | S n' => {| prop := @Syntax.to_semantics _ (IndexedSyntax n') (indexed n') |}
    end.

End INDEXED.
