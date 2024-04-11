From stdpp Require Import coPset gmap namespaces.
From sflib Require Import sflib.
From Fairness Require Import PCM IProp IPM IndexedInvariants.
From iris Require Import bi.big_op.
From iris Require base_logic.lib.invariants.

Module Syntax.

  Local Notation index := nat.

  Section TYPE.

    Context `{T : Type}.

    Inductive type : Type :=
    | baseT (t : T) : type
    | formulaT : type
    | prodT : type -> type -> type
    | sumT : type -> type -> type
    | listT : type -> type
    | funT : type -> type -> type
    | gmapTpos : type -> type.
    (* | gmapT (K : Type) {EqDec : EqDecision K} {Cnt : Countable K} : type -> type. *)

  (* If we define for a general gmapT with EqDec and Countable,
      universe inconsistency when checking (in TemporalLogic.Atoms)
      ==========
      Context `{Σ : GRA.t}.
      Context `{T : Type}.
      Context `{TSem : T -> Type}.
      Local Notation typing := (@Syntax.Typ T TSem (@t T)).
      Local Notation As := (fun (i : index) => @t T (typing i)).

      Context `{@GRA.inG (IInvSetRA As) Σ}.
      ==========
      with an error message
      ==========
      The term "t" has type
      "Type@{max(Set+1,Fairness.LogicSyntaxHOAS.59,Syntax.type.u0+1,Fairness.LogicSyntaxHOAS.64,Fairness.LogicSyntaxHOAS.65,RelDecision.u0,RelDecision.u1)}"
      while it is expected to have type "Type@{IInvSetRA.u0}" (universe inconsistency: Cannot enforce
      Fairness.LogicSyntaxHOAS.64 <= IInvSetRA.u0 because IInvSetRA.u0 <= InvSetRA.u0
      <= URA.agree_obligation_4.u0 <= URA.t.u0 < MRet.u0 = Fairness.LogicSyntaxHOAS.64).
      ==========
      Seems like there is a strict order between URA.t and MRet,
      and either EqDec or Countable uses MRet.
      ==========
      Found out that PCM.GRA.of_list introduces URA.t.u0 = RA.t.u0 < MRet.u0.
   *)

  End TYPE.

  Section SYNTAX.

    Context `{T : Type}.
    Context `{Typ : @type T -> Type}.
    Context `{A : Type}.

    Inductive t : Type :=
      atom (a : A) : t
    | lift : (Typ formulaT) -> t
    | sepconj (p q : t) : t
    | pure (P : Prop) : t
    | univ : forall ty, (Typ ty -> t) -> t
    | ex : forall ty, (Typ ty -> t) -> t
    | and (p q : t) : t
    | or (p q : t) : t
    | impl (p q : t) : t
    | wand (p q : t) : t
    | empty : t
    | persistently (p : t) : t
    | plainly (p : t) : t
    | upd (p : t) : t
    .

  End SYNTAX.

  Section INTERP_TYPE.

    Context `{T : Type}.
    Context `{TSem : T -> Type}.
    Context `{As : (@type T -> Type) -> Type}.

    Fixpoint Typ_0 (ty : @type T) : Type :=
      match ty with
      | baseT b => TSem b
      | formulaT => unit
      | prodT ty1 ty2 => prod (Typ_0 ty1) (Typ_0 ty2)
      | sumT ty1 ty2 => sum (Typ_0 ty1) (Typ_0 ty2)
      | listT ty' => list (Typ_0 ty')
      | funT ty1 ty2 => (Typ_0 ty1 -> Typ_0 ty2)
      | gmapTpos ty' => gmap positive (Typ_0 ty')
      (* | @gmapT _ K EqDec Cnt ty' => @gmap K EqDec Cnt (Typ_0 ty') *)
      end.

    Fixpoint Typ (i : index) : @type T -> Type :=
      match i with
      | O => Typ_0
      | S j =>
          fix Typ_aux (ty : @type T) : Type :=
        match ty with
        | baseT b => TSem b
        | formulaT => @t T (Typ j) (As (Typ j))
        | prodT ty1 ty2 => prod (Typ_aux ty1) (Typ_aux ty2)
        | sumT ty1 ty2 => sum (Typ_aux ty1) (Typ_aux ty2)
        | listT ty' => list (Typ_aux ty')
        | funT ty1 ty2 => (Typ_aux ty1 -> Typ_aux ty2)
        | gmapTpos ty' => gmap positive (Typ_aux ty')
        (* | @gmapT _ K EqDec Cnt ty' => @gmap K EqDec Cnt (Typ_aux ty') *)
        end
      end.

  End INTERP_TYPE.

  Section INTERP.

    Context `{Σ : GRA.t}.
    Context `{T : Type}.
    Context `{TSem : T -> Type}.
    Context `{As : (@type T -> Type) -> Type}.

    Local Notation typing := (@Typ T TSem As).

    Context `{interp_atoms : forall (n : index), As (typing n) -> iProp}.
    (* Context `{Atoms : @IInvSet Σ (fun (n : index) => As (typing n))}. *)

    Fixpoint to_semantics_0 (syn : @t T (typing O) (As (typing O))) : iProp :=
      match syn with
      | atom a => interp_atoms O a
      (* | atom a => prop O a *)
      | lift u => ⌜False⌝%I
      (* | lower u => (fun (x : unit) => ⌜False⌝%I) u *)
      | sepconj p q => Sepconj (to_semantics_0 p) (to_semantics_0 q)
      | pure P => Pure P
      | univ ty p => Univ (fun (x : typing O ty) => to_semantics_0 (p x))
      | ex ty p => Ex (fun (x : typing O ty) => to_semantics_0 (p x))
      | and p q => And (to_semantics_0 p) (to_semantics_0 q)
      | or p q => Or (to_semantics_0 p) (to_semantics_0 q)
      | impl p q => Impl (to_semantics_0 p) (to_semantics_0 q)
      | wand p q => Wand (to_semantics_0 p) (to_semantics_0 q)
      | empty => Emp
      | persistently p => Persistently (to_semantics_0 p)
      | plainly p => IProp.Plainly (to_semantics_0 p)
      | upd p => Upd (to_semantics_0 p)
      end.

    Fixpoint to_semantics (i : index) : @t T (typing i) (As (typing i)) -> iProp :=
      match i with
      | O => to_semantics_0
      | S j =>
          fix to_semantics_aux (syn : @t T (typing (S j)) (As (typing (S j)))) : iProp :=
        match syn with
        | atom a => interp_atoms (S j) a
        (* | atom a => prop (S j) a *)
        | lift syn' => to_semantics j syn'
        | sepconj p q => Sepconj (to_semantics_aux p) (to_semantics_aux q)
        | pure P => Pure P
        | univ ty p => Univ (fun (x : typing (S j) ty) => to_semantics_aux (p x))
        | ex ty p => Ex (fun (x : typing (S j) ty) => to_semantics_aux (p x))
        | and p q => And (to_semantics_aux p) (to_semantics_aux q)
        | or p q => Or (to_semantics_aux p) (to_semantics_aux q)
        | impl p q => Impl (to_semantics_aux p) (to_semantics_aux q)
        | wand p q => Wand (to_semantics_aux p) (to_semantics_aux q)
        | empty => Emp
        | persistently p => Persistently (to_semantics_aux p)
        | plainly p => IProp.Plainly (to_semantics_aux p)
        | upd p => Upd (to_semantics_aux p)
        end
      end.

  End INTERP.

  Section INDEXED_INVSET.

    Context `{Σ : GRA.t}.
    Context `{T : Type}.
    Context `{TSem : T -> Type}.
    Context `{As : (@type T -> Type) -> Type}.

    Local Notation typing := (@Typ T TSem As).
    Local Notation Formulas := (fun (i : index) => @t T (typing i) (As (typing i))).

    Context `{interp_atoms : forall (n : index), As (typing n) -> iProp}.
    (* Context `{Atoms : @IInvSet Σ (fun (n : index) => As (typing n))}. *)

    Global Instance IISet : @IInvSet Σ Formulas :=
      {| prop := @to_semantics Σ T TSem As interp_atoms |}.
      (* {| prop := @to_semantics Σ T TSem As Atoms |}. *)

  End INDEXED_INVSET.

  Section INV_IN.

    Context `{Σ : GRA.t}.
    Context `{T : Type}.
    Context `{TSem : T -> Type}.
    Context `{As : (@type T -> Type) -> Type}.

    Local Notation typing := (@Typ T TSem As).
    Local Notation Formulas := (fun (i : index) => @t T (typing i) (As (typing i))).

    Context `{interp_atoms : forall (n : index), As (typing n) -> iProp}.
    (* Context `{Atoms : @IInvSet Σ (fun (n : index) => As (typing n))}. *)

    Global Program Instance IIIn (i : index) (p : Formulas i)
      : @IInvIn Σ Formulas (IISet (interp_atoms:=interp_atoms)) i (@to_semantics Σ T TSem As interp_atoms i p) :=
      (* : @IInvIn Σ Formulas IISet i (@to_semantics Σ T TSem As Atoms i p) := *)
      { inhabitant := p }.
    Next Obligation.
      intros. simpl in *. done.
    Qed.

  End INV_IN.

End Syntax.
