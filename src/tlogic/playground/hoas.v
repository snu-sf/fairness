
Module Syntax.

  Local Notation index := nat.

  Section TYPE.

    Inductive type : Type :=
    | baseT (t : Type) : type
    | formulaT : type
    | prodT : type -> type -> type
    | sumT : type -> type -> type
    | listT : type -> type
    | funT : type -> type -> type
    .
    (* | positiveT : type *)
    (* | gmapTpos : type -> type. *)
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
      <= URA.agree_obligation_4.u0 <= ucmra.u0 < MRet.u0 = Fairness.LogicSyntaxHOAS.64).
      ==========
      Seems like there is a strict order between ucmra and MRet,
      and either EqDec or Countable uses MRet.
      ==========
      Found out that PCM.GRA.of_list introduces ucmra.u0 = RA.t.u0 < MRet.u0.
   *)

  End TYPE.

Section SYNTAX.

    Context `{Typ : @type -> Type}.
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

    Context `{As : (@type -> Type) -> Type}.

    Fixpoint Typ_0 (ty : @type) : Type :=
      match ty with
      | baseT b => b
      | formulaT => unit
      | prodT ty1 ty2 => prod (Typ_0 ty1) (Typ_0 ty2)
      | sumT ty1 ty2 => sum (Typ_0 ty1) (Typ_0 ty2)
      | listT ty' => list (Typ_0 ty')
      | funT ty1 ty2 => (Typ_0 ty1 -> Typ_0 ty2)
      (* | positiveT => positive *)
      (* | gmapTpos ty' => gmap positive (Typ_0 ty') *)
      (* | @gmapT _ K EqDec Cnt ty' => @gmap K EqDec Cnt (Typ_0 ty') *)
      end.

    Fixpoint Typ (i : index) : @type -> Type :=
      match i with
      | O => Typ_0
      | S j =>
          fix Typ_aux (ty : @type ) : Type :=
        match ty with
        | baseT b => b
        | formulaT => @t (Typ j) (As (Typ j))
        | prodT ty1 ty2 => prod (Typ_aux ty1) (Typ_aux ty2)
        | sumT ty1 ty2 => sum (Typ_aux ty1) (Typ_aux ty2)
        | listT ty' => list (Typ_aux ty')
        | funT ty1 ty2 => (Typ_aux ty1 -> Typ_aux ty2)
        (* | positiveT => positive *)
        (* | gmapTpos ty' => gmap positive (Typ_aux *) (* ty') *)
        (* | @gmapT _ K EqDec Cnt ty' => @gmap K EqDec Cnt (Typ_aux ty') *)
        end
      end.
End INTERP_TYPE.


Module Syntax.

  Local Notation index := nat.

  (* Section TYPE. *)

  (*   Context `{T : Type}. *)

  (*   Inductive type : Type := *)
  (*   | baseT (t : T) : type *)
  (*   | formulaT : type *)
  (*   | prodT : type -> type -> type *)
  (*   | sumT : type -> type -> type *)
  (*   | listT : type -> type *)
  (*   | funT : type -> type -> type *)
  (*   (* | positiveT : type *) *)
  (*   (* | gmapTpos : type -> type. *) *)
  (*   (* | gmapT (K : Type) {EqDec : EqDecision K} {Cnt : Countable K} : type -> type. *) *)
  (*   . *)

  (* End TYPE. *)

  Section SYNTAX.

    (* Context `{T : Type}. *)
    (* Context `{Typ : @type T -> Type}. *)
    (* Context `{As : Type -> Type}. *)
    (* Context `{iprop: Type}. *)
    Variable iprop: Type.

    (* Inductive t : Type := *)
    (*   atom (a : As iprop) : t *)
    (* | lift (p: iprop) : t *)
    (* | sepconj (p q : t) : t *)
    (* | pure (P : Prop) : t *)
    (* | univ (X: Type -> Type) (f: X iprop -> t) : t *)
    (* | ex (X: Type -> Type) (f: X iprop -> t) : t *)
    (* | and (p q : t) : t *)
    (* | or (p q : t) : t *)
    (* | impl (p q : t) : t *)
    (* | wand (p q : t) : t *)
    (* | empty : t *)
    (* | persistently (p : t) : t *)
    (* | plainly (p : t) : t *)
    (* | upd (p : t) : t *)
    (* . *)

    Inductive t : Type :=
    (* atom (a : As iprop) : t *)
    | even
    | odd
    | lift (p: iprop) : t
    (* | sepconj (p q : t) : t *)
    (* | pure (P : Prop) : t *)
    | univ (X: Type -> Type) (f: forall V (emb: V -> iprop), X V -> t) : t
    | ex   (X: Type -> Type) (f: forall {V} (emb: V -> iprop), X V -> t) : t
    (* | and (p q : t) : t *)
    (* | or (p q : t) : t *)
    (* | impl (p q : t) : t *)
    (* | wand (p q : t) : t *)
    (* | empty : t *)
    (* | persistently (p : t) : t *)
    (* | plainly (p : t) : t *)
    (* | upd (p : t) : t *)
    .

  End SYNTAX.

  Section INTERP_TYPE.

    (* Context `{As : Type -> Type}. *)

    (* Inductive Typ : @type T -> Type := *)
    (* | Typ_formula ( )  (e: @t T Typ (As Typ)) : Typ formulaT *)
    (* . *)

    Fixpoint iprop (i : index) : Type :=
      match i with
      | 0 => @t Empty_set
      | S j => @t (iprop j)
      end.

    Check (
        univ _ (fun iprop => (nat * iprop)%type)
        (fun _ emb x => lift _ (emb (snd x))) : iprop 2).

    Fixpoint semT0 (p: iprop 0) : nat -> Prop :=
      match p with
      | even _ => fun n => n = 2
      | odd _ => fun n => n = 1
      | lift _ p' => fun n => match p' with end
      | univ _ X f => fun n =>
          forall V (emb: V -> Empty_set) (x: X V), semT0 (f V emb x) n
      | ex _ X f => fun n =>
          exists V (emb: V -> Empty_set) (x: X V), semT0 (f V emb x) n
      end.

    Fixpoint semT i : iprop i -> nat -> Prop :=
      match i with
      | 0 => fun p => semT0 p
      | S j => (fix self (p: iprop (S j)) :=
        match p with
        | even _ => fun n => n = 2
        | odd _ => fun n => n = 1
        | lift _ p' => semT j p'
        | univ _ X f => fun n =>
          forall V (emb: V -> iprop j) (x: X V), self (f V emb x) n
        | ex _ X f => fun n =>
          exists V (emb: V -> iprop j) (x: X V), self (f V emb x) n
        end)
      end.

    (* Definition exprop : iprop 0 := *)
    (*     ex _ (fun iprop => nat) *)
    (*     (fun _ emb (x:nat) => )). *)

    Axiom p : iprop 1.

    Definition exprop : iprop 2 :=
        ex _ (fun iprop => list iprop)
        (fun V emb (f: list V) =>  lift _ (f p)).

    Print exprop.


    V, emb: V -> iprop 2, (n,v): nat * V,    sem (lift _ (emb (snd (n,v)))) n



    (fun iprop => nat * iprop)




    Fixpoint sem {i} : iprop i -> nat -> Prop :=
      match i with
      | 0 => fun p n =>

               match p with
                        | even => n%2 = 0
                        | odd => n%2 = 1
                        | lift p' => match p' with end
                        | inv X f => forall (x: X Empty_set), f id x
                        end



    | univ (X: Type -> Type) (f: forall {V} (emb: V -> iprop), X V -> t) : t






    Fixpoint Typ0 (form: Type) (ty : @type T) : Type :=
      match ty with
      | baseT b => TSem b
      | formulaT => form
      | prodT ty1 ty2 => prod (Typ0 form ty1) (Typ0 form ty2)
      | sumT ty1 ty2 => sum (Typ0 form ty1) (Typ0 form ty2)
      | listT ty' => list (Typ0 form ty')
      | funT ty1 ty2 => (Typ0 form ty1 -> Typ0 form ty2)
      (* | positiveT => positive *)
      (* | gmapTpos ty' => gmap positive (Typ_0 ty') *)
      (* | @gmapT _ K EqDec Cnt ty' => @gmap K EqDec Cnt (Typ_0 ty') *)
      end.

    Fixpoint Typ (i : index) : @type T -> Type :=
      Typ0 (match i with 0 => unit | S j => (@t T (Typ j) (As (Typ j))) end).
      (* match i with *)
      (* | O => Typ0 unit *)
      (* | S j => Typ0 (@t T (Typ j) (As (Typ j))) *)
      (* end. *)

  End INTERP_TYPE.


Section TYPE.

Polymorphic Record PCM : Type := {
    car: Type;
    add: car -> car -> car;
}.

(* Polymorphic Fixpoint Res (n: nat) : Type := *)
(*   match n with   *)
(*   | 0 => PCM unit *)
(*   | S m => PCM (Res m) *)
(*   end. *)

Polymorphic Inductive Res : Type :=
| res (p: PCM)
.

Definition iProp := Res -> Prop.

Definition r1 :=
  res {|car := nat;
    add := plus;
  |}.

Definition r2 :=
  res {|car := iProp);
    add := fun _ _ _ => True;
  |}.





Inductive Res : Type :=
| lift (iProp: Res -> Prop): Res
|



End TYPE.
