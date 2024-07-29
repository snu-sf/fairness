From stdpp Require Import coPset gmap namespaces.
From sflib Require Import sflib.
From Fairness Require Import PCM IPM IndexedInvariants.
From iris Require Import bi.big_op.
From iris Require base_logic.lib.invariants.
From Coq Require Import Program Arith.

Module Syntax.

  Local Notation index := nat.

  Section SYNTAX.

    Context `{type : Type}.
    Context `{Typ : forall formula : Type, type -> Type}.
    Context `{A : Type}.

    Inductive t {form : Type} : Type :=
      atom (a : A) : t
    | lift (p : form) : t
    | sepconj (p q : t) : t
    | pure (P : Prop) : t
    | univ : forall (ty : type), (Typ form ty -> t) -> t
    | ex : forall (ty : type), (Typ form ty -> t) -> t
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

  Section FORMULA.

    Context `{type : Type}.
    Context `{Typ : forall formula : Type, type -> Type}.
    Context `{As : forall formula : Type, Type}.

    Fixpoint _formula (n : index) : Type :=
      match n with
      | O => Empty_set
      | S m => @t type Typ (As (_formula m)) (_formula m)
      end.

    Definition formula (n : index) : Type := _formula (S n).

  End FORMULA.

  Section INTERP.

    Context `{type : Type}.
    Context `{Typ : forall formula : Type, type -> Type}.
    Context `{As : forall formula : Type, Type}.

    Local Notation _formulas := (@_formula type Typ As).
    Local Notation formulas := (@formula type Typ As).

    Context `{Σ : GRA.t}.

    Context `{interp_atoms : forall (n : index), As (_formulas n) -> iProp}.

    Fixpoint _to_semantics n : _formulas n -> iProp :=
      match n with
      | O => fun _ => ⌜False⌝%I
      | S m =>
          fix _to_semantics_aux (syn : _formulas (S m)) : iProp :=
        match syn with
        | atom a => interp_atoms m a
        | lift p => _to_semantics m p
        | sepconj p q => Sepconj (_to_semantics_aux p) (_to_semantics_aux q)
        | pure P => Pure P
        | univ ty p => Univ (fun (x : Typ (_formulas m) ty) => _to_semantics_aux (p x))
        | ex ty p => Ex (fun (x : Typ (_formulas m) ty) => _to_semantics_aux (p x))
        | and p q => And (_to_semantics_aux p) (_to_semantics_aux q)
        | or p q => Or (_to_semantics_aux p) (_to_semantics_aux q)
        | impl p q => Impl (_to_semantics_aux p) (_to_semantics_aux q)
        | wand p q => Wand (_to_semantics_aux p) (_to_semantics_aux q)
        | empty => Emp
        | persistently p => Persistently (_to_semantics_aux p)
        | plainly p => .Plainly (_to_semantics_aux p)
        | upd p => Upd (_to_semantics_aux p)
        end
      end.

    Definition to_semantics n : formulas n -> iProp := _to_semantics (S n).

  End INTERP.

  Section INDEXED_INVSET.

    Context `{type : Type}.
    Context `{Typ : forall formula : Type, type -> Type}.
    Context `{As : forall formula : Type, Type}.

    Local Notation formulas := (@formula type Typ As).

    Context `{Σ : GRA.t}.

    Local Notation _formulas := (@_formula type Typ As).
    Context `{interp_atoms : forall (n : index), As (_formulas n) -> iProp}.

    Global Instance IISet : @IInvSet Σ formulas :=
      {| prop := @to_semantics type Typ As Σ interp_atoms |}.

  End INDEXED_INVSET.

  (* Section INV_IN. *)

  (*   Context `{type : Type}. *)
  (*   Context `{Typ : forall formula : Type, type -> Type}. *)
  (*   Context `{As : forall formula : Type, Type}. *)

  (*   Local Notation formulas := (@formula type Typ As). *)

  (*   Context `{Σ : GRA.t}. *)

  (*   Context `{interp_atoms_0 : As Empty_set -> iProp}. *)
  (*   Context `{interp_atoms : forall (n : index), As (formulas n) -> iProp}. *)

  (*   Global Program Instance IIIn (i : index) (p : formulas i) *)
  (*     : @IInvIn Σ formulas (IISet (interp_atoms_0:=interp_atoms_0) (interp_atoms:=interp_atoms)) i (@to_semantics type Typ As Σ interp_atoms_0 interp_atoms i p) := *)
  (*     { inhabitant := p }. *)
  (*   Next Obligation. *)
  (*     intros. simpl. done. *)
  (*   Qed. *)

  (* End INV_IN. *)

End Syntax.

Section RED.

  Local Notation index := nat.

  Context `{type : Type}.
  Context `{Typ : forall formula : Type, type -> Type}.
  Context `{As : forall formula : Type, Type}.

  Local Notation _formulas := (@Syntax._formula type Typ As).
  Local Notation formulas := (@Syntax.formula type Typ As).

  Context `{Σ : GRA.t}.
  Context `{interp_atoms : forall (n : index), As (_formulas n) -> iProp}.

  Local Notation Sem := (@Syntax.to_semantics _ Typ As _ interp_atoms).

  Lemma red_sem_atom n a :
    Sem n (Syntax.atom a : formulas n) = interp_atoms n a.
  Proof. ss. Qed.

  Lemma red_sem_lift_0 p :
    Sem 0 (Syntax.lift p) = ⌜False⌝%I.
  Proof. ss. Qed.

  Lemma red_sem_lift n p :
    Sem (S n) (Syntax.lift p) = Sem n p.
  Proof. ss. Qed.

  Lemma red_sem_sepconj n p q :
    Sem n (Syntax.sepconj p q) = (Sem n p ∗ Sem n q)%I.
  Proof. ss. Qed.

  Lemma red_sem_pure n P :
    Sem n (Syntax.pure P) = ⌜P⌝%I.
  Proof. ss. Qed.

  Lemma red_sem_univ n ty p :
    Sem n (Syntax.univ ty p) = (∀ (x : Typ (_formulas n) ty), Sem n (p x))%I.
  Proof. ss. Qed.

  Lemma red_sem_ex n ty p :
    Sem n (Syntax.ex ty p) = (∃ (x : Typ (_formulas n) ty), Sem n (p x))%I.
  Proof. ss. Qed.

  Lemma red_sem_and n p q :
    Sem n (Syntax.and p q) = (Sem n p ∧ Sem n q)%I.
  Proof. ss. Qed.

  Lemma red_sem_or n p q :
    Sem n (Syntax.or p q) = (Sem n p ∨ Sem n q)%I.
  Proof. ss. Qed.

  Lemma red_sem_impl n p q :
    Sem n (Syntax.impl p q) = (Sem n p → Sem n q)%I.
  Proof. ss. Qed.

  Lemma red_sem_wand n p q :
    Sem n (Syntax.wand p q) = (Sem n p -∗ Sem n q)%I.
  Proof. ss. Qed.

  Lemma red_sem_empty n :
    Sem n Syntax.empty = emp%I.
  Proof. ss. Qed.

  Lemma red_sem_persistently n p :
    Sem n (Syntax.persistently p) = (<pers> Sem n p)%I.
  Proof. ss. Qed.

  Lemma red_sem_plainly n p :
    Sem n (Syntax.plainly p) = (.Plainly (Sem n p))%I.
  Proof. ss. Qed.

  Lemma red_sem_upd n p :
    Sem n (Syntax.upd p) = (#=> Sem n p)%I.
  Proof. ss. Qed.

  Definition syn_affinely {n} (p : formulas n) : formulas n :=
    Syntax.and Syntax.empty p.

  Lemma red_sem_affinely n p :
    Sem n (syn_affinely p) = (<affine> Sem n p)%I.
  Proof. ss. Qed.

  Lemma red_sem_intuitionistically n p :
    Sem n (syn_affinely (Syntax.persistently p)) = (□ Sem n p)%I.
  Proof. ss. Qed.

End RED.

Global Opaque Syntax.to_semantics.

(** Notations *)

Declare Scope formula_scope.
Delimit Scope formula_scope with F.
Bind Scope formula_scope with Syntax.formula.

Local Open Scope formula_scope.

Notation "'⌜' P '⌝'" := (Syntax.pure P) : formula_scope.
Notation "'⊤'" := ⌜True⌝ : formula_scope.
Notation "'⊥'" := ⌜False⌝ : formula_scope.

Notation "'⟨' A '⟩'" := (Syntax.atom A) : formula_scope.
Notation "↑ P" := (Syntax.lift P) : formula_scope.

Notation "'<pers>' P" := (Syntax.persistently P) : formula_scope.
Notation "'<affine>' P" := (syn_affinely P) : formula_scope.
Notation "□ P" := (<affine> <pers> P) : formula_scope.
Notation "■ P" := (Syntax.plainly P) : formula_scope.
Notation "|==> P" := (Syntax.upd P) : formula_scope.
Infix "∧" := (Syntax.and) : formula_scope.
Infix "∨" := (Syntax.or) : formula_scope.
Infix "→" := (Syntax.impl) : formula_scope.
Notation "¬ P" := (P → False) : formula_scope.
Infix "∗" := (Syntax.sepconj) : formula_scope.
Infix "-∗" := (Syntax.wand) : formula_scope.
Notation "P ==∗ Q" := (P -∗ |==> Q) : formula_scope.
Notation f_forall A := (Syntax.univ A).
Notation "∀'" := (f_forall _) (only parsing) : formula_scope.
Notation "∀ a .. z , P" := (f_forall _ (λ a, .. (f_forall _ (λ z, P%F)) ..)) : formula_scope.
Notation f_exist A := (Syntax.ex A).
Notation "∃'" := (f_exist _) (only parsing) : formula_scope.
Notation "∃ a .. z , P" := (f_exist _ (λ a, .. (f_exist _ (λ z, P%F)) ..)) : formula_scope.
Notation "'emp'" := (Syntax.empty) : formula_scope.



(* (* Old version *) *)
(* Module Syntax. *)

(*   Local Notation index := nat. *)

(*   Section TYPE. *)

(*     (* Context `{T : Type}. *) *)

(*     Inductive type : Type := *)
(*     | baseT (t : Type) : type *)
(*     (* | baseT (t : T) : type *) *)
(*     | formulaT : type *)
(*     (* | prodT : type -> type -> type *) *)
(*     (* | sumT : type -> type -> type *) *)
(*     (* | listT : type -> type *) *)
(*     | funT : type -> type -> type *)
(*     (* | positiveT : type *) *)
(*     | pgmapT : type -> type. *)
(*     (* | gmapT (K : Type) {EqDec : EqDecision K} {Cnt : Countable K} : type -> type. *) *)

(*   (* If we define for a general gmapT with EqDec and Countable, *)
(*       universe inconsistency when checking (in TemporalLogic.Atoms) *)
(*       ========== *)
(*       Context `{Σ : GRA.t}. *)
(*       Context `{T : Type}. *)
(*       Context `{TSem : T -> Type}. *)
(*       Local Notation typing := (@Syntax.Typ T TSem (@t T)). *)
(*       Local Notation As := (fun (i : index) => @t T (typing i)). *)

(*       Context `{@GRA.inG (IInvSetRA As) Σ}. *)
(*       ========== *)
(*       with an error message *)
(*       ========== *)
(*       The term "t" has type *)
(*       "Type@{max(Set+1,Fairness.LogicSyntaxHOAS.59,Syntax.type.u0+1,Fairness.LogicSyntaxHOAS.64,Fairness.LogicSyntaxHOAS.65,RelDecision.u0,RelDecision.u1)}" *)
(*       while it is expected to have type "Type@{IInvSetRA.u0}" (universe inconsistency: Cannot enforce *)
(*       Fairness.LogicSyntaxHOAS.64 <= IInvSetRA.u0 because IInvSetRA.u0 <= InvSetRA.u0 *)
(*       <= URA.agree_obligation_4.u0 <= ucmra.u0 < MRet.u0 = Fairness.LogicSyntaxHOAS.64). *)
(*       ========== *)
(*       Seems like there is a strict order between ucmra and MRet, *)
(*       and either EqDec or Countable uses MRet. *)
(*       ========== *)
(*       Found out that PCM.GRA.of_list introduces ucmra.u0 = RA.t.u0 < MRet.u0. *)
(*    *) *)

(*   End TYPE. *)

(*   Section SYNTAX. *)

(*     (* Context `{T : Type}. *) *)
(*     Context `{Typ : type -> Type}. *)
(*     (* Context `{Typ : @type T -> Type}. *) *)
(*     Context `{A : Type}. *)

(*     Inductive t : Type := *)
(*       atom (a : A) : t *)
(*     | lift : (Typ formulaT) -> t *)
(*     | sepconj (p q : t) : t *)
(*     | pure (P : Prop) : t *)
(*     | univ : forall ty, (Typ ty -> t) -> t *)
(*     | ex : forall ty, (Typ ty -> t) -> t *)
(*     | and (p q : t) : t *)
(*     | or (p q : t) : t *)
(*     | impl (p q : t) : t *)
(*     | wand (p q : t) : t *)
(*     | empty : t *)
(*     | persistently (p : t) : t *)
(*     | plainly (p : t) : t *)
(*     | upd (p : t) : t *)
(*     . *)

(*   End SYNTAX. *)

(*   Section INTERP_TYPE. *)

(*     (* Context `{T : Type}. *) *)
(*     (* Context `{TSem : T -> Type}. *) *)
(*     Context `{As : (type -> Type) -> Type}. *)
(*     (* Context `{As : (@type T -> Type) -> Type}. *) *)

(*     Fixpoint Typ_0 (form : Type) (ty : type) : Type := *)
(*     (* Fixpoint Typ_0 (ty : @type T) : Type := *) *)
(*       match ty with *)
(*       | baseT b => b *)
(*       | formulaT => form *)
(*       (* | prodT ty1 ty2 => prod (Typ_0 ty1) (Typ_0 ty2) *) *)
(*       (* | sumT ty1 ty2 => sum (Typ_0 ty1) (Typ_0 ty2) *) *)
(*       (* | listT ty' => list (Typ_0 ty') *) *)
(*       | funT ty1 ty2 => (Typ_0 form ty1 -> Typ_0 form ty2) *)
(*       (* | positiveT => positive *) *)
(*       | pgmapT ty' => gmap positive (Typ_0 form ty') *)
(*       (* | gmapTpos ty' => gmap positive (Typ_0 ty') *) *)
(*       (* | @gmapT _ K EqDec Cnt ty' => @gmap K EqDec Cnt (Typ_0 ty') *) *)
(*       end. *)

(*     Fixpoint Typ (i : index) : @type -> Type := *)
(*       Typ_0 (match i with *)
(*              | O => Empty_set *)
(*              | S j => @t (Typ j) (As (Typ j)) *)
(*              end). *)

(*     (* Fixpoint Typ_0 (ty : @type T) : Type := *) *)
(*     (* (* Fixpoint Typ_0 (ty : @type T) : Type := *) *) *)
(*     (*   match ty with *) *)
(*     (*   | baseT b => TSem b *) *)
(*     (*   | formulaT => unit *) *)
(*     (*   | prodT ty1 ty2 => prod (Typ_0 ty1) (Typ_0 ty2) *) *)
(*     (*   | sumT ty1 ty2 => sum (Typ_0 ty1) (Typ_0 ty2) *) *)
(*     (*   | listT ty' => list (Typ_0 ty') *) *)
(*     (*   | funT ty1 ty2 => (Typ_0 ty1 -> Typ_0 ty2) *) *)
(*     (*   | positiveT => positive *) *)
(*     (*   | gmapTpos ty' => gmap positive (Typ_0 ty') *) *)
(*     (*   (* | @gmapT _ K EqDec Cnt ty' => @gmap K EqDec Cnt (Typ_0 ty') *) *) *)
(*     (*   end. *) *)

(*     (* Fixpoint Typ (i : index) : @type T -> Type := *) *)
(*     (*   match i with *) *)
(*     (*   | O => Typ_0 *) *)
(*     (*   | S j => *) *)
(*     (*       fix Typ_aux (ty : @type T) : Type := *) *)
(*     (*     match ty with *) *)
(*     (*     | baseT b => TSem b *) *)
(*     (*     | formulaT => @t T (Typ j) (As (Typ j)) *) *)
(*     (*     | prodT ty1 ty2 => prod (Typ_aux ty1) (Typ_aux ty2) *) *)
(*     (*     | sumT ty1 ty2 => sum (Typ_aux ty1) (Typ_aux ty2) *) *)
(*     (*     | listT ty' => list (Typ_aux ty') *) *)
(*     (*     | funT ty1 ty2 => (Typ_aux ty1 -> Typ_aux ty2) *) *)
(*     (*     | positiveT => positive *) *)
(*     (*     | gmapTpos ty' => gmap positive (Typ_aux ty') *) *)
(*     (*     (* | @gmapT _ K EqDec Cnt ty' => @gmap K EqDec Cnt (Typ_aux ty') *) *) *)
(*     (*     end *) *)
(*     (*   end. *) *)

(*   End INTERP_TYPE. *)

(*   Section INTERP. *)

(*     Context `{Σ : GRA.t}. *)
(*     (* Context `{T : Type}. *) *)
(*     (* Context `{TSem : T -> Type}. *) *)
(*     Context `{As : (type -> Type) -> Type}. *)
(*     (* Context `{As : (@type T -> Type) -> Type}. *) *)

(*     Local Notation typing := (@Typ As). *)
(*     (* Local Notation typing := (@Typ T TSem As). *) *)

(*     Context `{interp_atoms : forall (n : index), As (typing n) -> iProp}. *)
(*     (* Context `{Atoms : @IInvSet Σ (fun (n : index) => As (typing n))}. *) *)

(*     Fixpoint to_semantics_0 *)
(*              n (sem : (typing n formulaT) -> iProp) (syn : @t (typing n) (As (typing n))) *)
(*       : iProp := *)
(*       match syn with *)
(*       | atom a => interp_atoms n a *)
(*       | lift u => sem u *)
(*       | sepconj p q => Sepconj (to_semantics_0 n sem p) (to_semantics_0 n sem q) *)
(*       | pure P => Pure P *)
(*       | univ ty p => Univ (fun (x : typing n ty) => to_semantics_0 n sem (p x)) *)
(*       | ex ty p => Ex (fun (x : typing n ty) => to_semantics_0 n sem (p x)) *)
(*       | and p q => And (to_semantics_0 n sem p) (to_semantics_0 n sem q) *)
(*       | or p q => Or (to_semantics_0 n sem p) (to_semantics_0 n sem q) *)
(*       | impl p q => Impl (to_semantics_0 n sem p) (to_semantics_0 n sem q) *)
(*       | wand p q => Wand (to_semantics_0 n sem p) (to_semantics_0 n sem q) *)
(*       | empty => Emp *)
(*       | persistently p => Persistently (to_semantics_0 n sem p) *)
(*       | plainly p => .Plainly (to_semantics_0 n sem p) *)
(*       | upd p => Upd (to_semantics_0 n sem p) *)
(*       end. *)

(*     Let cast_typing n : typing (S n) formulaT -> @t (typing n) (As (typing n)) := *)
(*       fun p => p. *)

(*     Fixpoint to_semantics n : @t (typing n) (As (typing n)) -> iProp := *)
(*       to_semantics_0 n (match n with *)
(*                         | O => fun _ => ⌜False⌝%I *)
(*                         | S m => fun (p : typing (S m) formulaT) => to_semantics m (cast_typing m p) *)
(*                         end). *)

(*     (* Fixpoint to_semantics_0 (syn : @t T (typing O) (As (typing O))) : iProp := *) *)
(*     (*   match syn with *) *)
(*     (*   | atom a => interp_atoms O a *) *)
(*     (*   (* | atom a => prop O a *) *) *)
(*     (*   | lift u => ⌜False⌝%I *) *)
(*     (*   (* | lower u => (fun (x : unit) => ⌜False⌝%I) u *) *) *)
(*     (*   | sepconj p q => Sepconj (to_semantics_0 p) (to_semantics_0 q) *) *)
(*     (*   | pure P => Pure P *) *)
(*     (*   | univ ty p => Univ (fun (x : typing O ty) => to_semantics_0 (p x)) *) *)
(*     (*   | ex ty p => Ex (fun (x : typing O ty) => to_semantics_0 (p x)) *) *)
(*     (*   | and p q => And (to_semantics_0 p) (to_semantics_0 q) *) *)
(*     (*   | or p q => Or (to_semantics_0 p) (to_semantics_0 q) *) *)
(*     (*   | impl p q => Impl (to_semantics_0 p) (to_semantics_0 q) *) *)
(*     (*   | wand p q => Wand (to_semantics_0 p) (to_semantics_0 q) *) *)
(*     (*   | empty => Emp *) *)
(*     (*   | persistently p => Persistently (to_semantics_0 p) *) *)
(*     (*   | plainly p => .Plainly (to_semantics_0 p) *) *)
(*     (*   | upd p => Upd (to_semantics_0 p) *) *)
(*     (*   end. *) *)

(*     (* Fixpoint to_semantics (i : index) : @t T (typing i) (As (typing i)) -> iProp := *) *)
(*     (*   match i with *) *)
(*     (*   | O => to_semantics_0 *) *)
(*     (*   | S j => *) *)
(*     (*       fix to_semantics_aux (syn : @t T (typing (S j)) (As (typing (S j)))) : iProp := *) *)
(*     (*     match syn with *) *)
(*     (*     | atom a => interp_atoms (S j) a *) *)
(*     (*     (* | atom a => prop (S j) a *) *) *)
(*     (*     | lift syn' => to_semantics j syn' *) *)
(*     (*     | sepconj p q => Sepconj (to_semantics_aux p) (to_semantics_aux q) *) *)
(*     (*     | pure P => Pure P *) *)
(*     (*     | univ ty p => Univ (fun (x : typing (S j) ty) => to_semantics_aux (p x)) *) *)
(*     (*     | ex ty p => Ex (fun (x : typing (S j) ty) => to_semantics_aux (p x)) *) *)
(*     (*     | and p q => And (to_semantics_aux p) (to_semantics_aux q) *) *)
(*     (*     | or p q => Or (to_semantics_aux p) (to_semantics_aux q) *) *)
(*     (*     | impl p q => Impl (to_semantics_aux p) (to_semantics_aux q) *) *)
(*     (*     | wand p q => Wand (to_semantics_aux p) (to_semantics_aux q) *) *)
(*     (*     | empty => Emp *) *)
(*     (*     | persistently p => Persistently (to_semantics_aux p) *) *)
(*     (*     | plainly p => .Plainly (to_semantics_aux p) *) *)
(*     (*     | upd p => Upd (to_semantics_aux p) *) *)
(*     (*     end *) *)
(*     (*   end. *) *)

(*   End INTERP. *)

(*   Section INDEXED_INVSET. *)

(*     Context `{Σ : GRA.t}. *)
(*     (* Context `{T : Type}. *) *)
(*     (* Context `{TSem : T -> Type}. *) *)
(*     Context `{As : (type -> Type) -> Type}. *)
(*     (* Context `{As : (@type T -> Type) -> Type}. *) *)

(*     Local Notation typing := (@Typ As). *)
(*     Local Notation Formulas := (fun (i : index) => @t (typing i) (As (typing i))). *)
(*     (* Local Notation typing := (@Typ T TSem As). *) *)
(*     (* Local Notation Formulas := (fun (i : index) => @t T (typing i) (As (typing i))). *) *)

(*     Context `{interp_atoms : forall (n : index), As (typing n) -> iProp}. *)
(*     (* Context `{Atoms : @IInvSet Σ (fun (n : index) => As (typing n))}. *) *)

(*     Global Instance IISet : @IInvSet Σ Formulas := *)
(*       {| prop := @to_semantics Σ As interp_atoms |}. *)
(*       (* {| prop := @to_semantics Σ T TSem As interp_atoms |}. *) *)
(*       (* {| prop := @to_semantics Σ T TSem As Atoms |}. *) *)

(*   End INDEXED_INVSET. *)

(*   Section INV_IN. *)

(*     Context `{Σ : GRA.t}. *)
(*     Context `{As : (type -> Type) -> Type}. *)
(*     (* Context `{T : Type}. *) *)
(*     (* Context `{TSem : T -> Type}. *) *)
(*     (* Context `{As : (@type T -> Type) -> Type}. *) *)

(*     Local Notation typing := (@Typ As). *)
(*     Local Notation Formulas := (fun (i : index) => @t (typing i) (As (typing i))). *)
(*     (* Local Notation typing := (@Typ T TSem As). *) *)
(*     (* Local Notation Formulas := (fun (i : index) => @t T (typing i) (As (typing i))). *) *)

(*     Context `{interp_atoms : forall (n : index), As (typing n) -> iProp}. *)
(*     (* Context `{Atoms : @IInvSet Σ (fun (n : index) => As (typing n))}. *) *)

(*     Global Program Instance IIIn (i : index) (p : Formulas i) *)
(*       : @IInvIn Σ Formulas (IISet (interp_atoms:=interp_atoms)) i (@to_semantics Σ As interp_atoms i p) := *)
(*       (* : @IInvIn Σ Formulas IISet i (@to_semantics Σ T TSem As Atoms i p) := *) *)
(*       { inhabitant := p }. *)
(*     Next Obligation. *)
(*       intros. simpl in *. done. *)
(*     Qed. *)

(*     (* Global Program Instance IIIn (i : index) (p : Formulas i) *) *)
(*     (*   : @IInvIn Σ Formulas (IISet (interp_atoms:=interp_atoms)) i (@to_semantics Σ T TSem As interp_atoms i p) := *) *)
(*     (*   (* : @IInvIn Σ Formulas IISet i (@to_semantics Σ T TSem As Atoms i p) := *) *) *)
(*     (*   { inhabitant := p }. *) *)
(*     (* Next Obligation. *) *)
(*     (*   intros. simpl in *. done. *) *)
(*     (* Qed. *) *)

(*   End INV_IN. *)

(*   Section RED. *)

(*     Context `{Σ : GRA.t}. *)
(*     Context `{As : (type -> Type) -> Type}. *)
(*     (* Context `{T : Type}. *) *)
(*     (* Context `{TSem : T -> Type}. *) *)
(*     (* Context `{As : (@type T -> Type) -> Type}. *) *)

(*     Local Notation typing := (@Typ As). *)
(*     Local Notation Formulas := (fun (i : index) => @t (typing i) (As (typing i))). *)
(*     (* Local Notation typing := (@Typ T TSem As). *) *)
(*     (* Local Notation Formulas := (fun (i : index) => @t T (typing i) (As (typing i))). *) *)

(*     Context `{interp_atoms : forall (n : index), As (typing n) -> iProp}. *)

(*     Local Notation Sem := (fun i p => @to_semantics Σ As interp_atoms i p). *)
(*     (* Local Notation Sem := (fun i p => @to_semantics Σ T TSem As interp_atoms i p). *) *)

(*     Lemma to_semantics_empty *)
(*           n *)
(*       : *)
(*       Sem n empty = emp%I. *)
(*     Proof. *)
(*       induction n; ss. *)
(*     Qed. *)

(*     Lemma to_semantics_red_sepconj *)
(*           n p q *)
(*       : *)
(*       Sem n (sepconj p q) = ((Sem n p) ∗ (Sem n q))%I. *)
(*     Proof. *)
(*       induction n; ss. *)
(*     Qed. *)

(*     Lemma to_semantics_red_or *)
(*           n p q *)
(*       : *)
(*       Sem n (or p q) = ((Sem n p) ∨ (Sem n q))%I. *)
(*     Proof. *)
(*       induction n; ss. *)
(*     Qed. *)

(*     Lemma to_semantics_red_atom *)
(*           n a *)
(*       : *)
(*       Sem n (atom a) = interp_atoms n a. *)
(*     Proof. *)
(*       induction n; ss. *)
(*     Qed. *)

(*     Lemma to_semantics_red_ex *)
(*           n ty f *)
(*       : *)
(*       Sem n (ex ty f) = (∃ (x : typing n ty), Sem n (f x))%I. *)
(*     Proof. *)
(*       induction n; ss. *)
(*     Qed. *)

(*     Lemma to_semantics_red_lift *)
(*           n p *)
(*       : *)
(*       Sem (S n) (lift p) = Sem n p. *)
(*     Proof. *)
(*       ss. *)
(*     Qed. *)

(*   End RED. *)

(*   Section GMAP. *)

(*     Context `{Σ : GRA.t}. *)
(*     Context `{As : (type -> Type) -> Type}. *)

(*     Local Notation typing := (@Typ As). *)
(*     Local Notation Formulas := (fun (i : index) => @t (typing i) (As (typing i))). *)

(*     Context `{interp_atoms : forall (n : index), As (typing n) -> iProp}. *)

(*     (* Maybe we can make Syntax as an instance of bi. *) *)
(*     Definition star_gmap *)
(*                (n : index) (I : typing (S n) (pgmapT formulaT)) *)
(*                (f : positive -> Formulas n -> Formulas n) *)
(*       : Formulas n := *)
(*       fold_right (fun hd tl => @sepconj (typing n) (As (typing n)) (uncurry f hd) tl) empty (map_to_list I). *)


(*     Local Notation Sem := (fun i p => @to_semantics Σ As interp_atoms i p). *)

(*     Lemma star_gmap_iProp *)
(*           n I f *)
(*       : *)
(*       Sem n (star_gmap n I f) = *)
(*         ([∗ map] i ↦ p ∈ I, Sem n (f i p))%I. *)
(*     Proof. *)
(*       ss. unfold big_opM. rewrite seal_eq. unfold big_op.big_opM_def. *)
(*       unfold star_gmap. ss. remember (map_to_list I) as L. *)
(*       clear HeqL I. induction L. *)
(*       { ss. apply to_semantics_empty. } *)
(*       ss. rewrite to_semantics_red_sepconj. rewrite IHL. f_equal. *)
(*       destruct a. ss. *)
(*     Qed. *)

(*   End GMAP. *)

(* End Syntax. *)
