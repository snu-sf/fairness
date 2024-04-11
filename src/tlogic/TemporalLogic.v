From stdpp Require Import coPset gmap namespaces.
From sflib Require Import sflib.
From Fairness Require Import PCM IProp IPM.
From Fairness Require Import IndexedInvariants LogicSyntaxHOAS.
From iris Require Import bi.big_op.
From iris Require base_logic.lib.invariants.

Local Notation index := nat.

Module Base.

  Variant meta : Type :=
    | src_stateT
    | tgt_stateT
    | src_identT
    | tgt_identT.

  Inductive t : Type :=
  | unitT
  | natT
  | boolT
  | positiveT
  | QpT
  | coPsetT
  | gsetTpos
  | metaT (ty : meta)
  .
  (* | gsetT (K : Type) {EqDec : EqDecision K} {Cnt : Countable K}. *)

  Definition sem {config_meta : meta -> Type} (ty : t) : Type :=
    match ty with
    | unitT => unit
    | natT => nat
    | boolT => bool
    | positiveT => positive
    | QpT => Qp
    | coPsetT => coPset
    | gsetTpos => gset positive
    | metaT ty => config_meta ty
    end.

End Base.

Module Atoms.

  Section ATOMS.

    Context `{T : Type}.

    (* TODO: more atoms *)

    (* Atoms do not interpret arguments. *)
    Inductive t {Typ : @Syntax.type T -> Type} : Type :=
    | owne (E : coPset)
    | ownd (D : gset positive)
    | owni (i : positive) (p : @Syntax.t T Typ (@t Typ))
    | wsat
    (* | inv_auth_meta (ps : gmap positive (Typ Syntax.formulaT)) *)
    (* | inv_satall_meta (ps : gmap positive (Typ Syntax.formulaT)) *)
    .
    (* Inductive t {Typ : @Syntax.type T -> Type} : Type := *)
    (* | owne (n : index) (E : coPset) *)
    (* | ownd (n : index) (D : gset positive) *)
    (* | owni (n : index) (i : positive) (p : @Syntax.t T Typ (@t Typ)) *)
    (* | inv_auth_meta (n : index) (I : gmap positive (Typ Syntax.formulaT)) *)
    (* | inv_satall_meta (n : index) (I : gmap positive (Typ Syntax.formulaT)) *)
    (* . *)

  (* Definition wsat : iProp := (∃ I, inv_auth I ∗ inv_satall I)%I. *)
  (* Definition inv_auth (I : gmap positive Var) := *)
  (*   OwnM (inv_auth_black I). *)


  (* Definition inv_satall (I : gmap positive Var) := *)
  (*   ([∗ map] i ↦ p ∈ I, (prop n p) ∗ OwnD n {[i]} ∨ OwnE n {[i]})%I. *)
(* Notation "'[∗' 'map]' k ↦ x ∈ m , P" := (big_opM bi_sep (fun k x => P) m) : bi_scope *)

  End ATOMS.

  Section INTERP.

    Context `{Σ : GRA.t}.
    Context `{T : Type}.
    Context `{TSem : T -> Type}.

    Local Notation typing := (@Syntax.Typ T TSem (@t T)).
    (* Local Notation As := (fun (i : index) => @t T (typing i)). *)
    Local Notation Formulas := (fun (i : index) => @Syntax.t T (typing i) (@t T (typing i))).

    Context `{@GRA.inG (IInvSetRA Formulas) Σ}.
    Context `{@GRA.inG (index ==> CoPset.t)%ra Σ}.
    Context `{@GRA.inG (index ==> Gset.t)%ra Σ}.

    (* Local Notation prop := (prop (IInvSet:=@Syntax.IISet _ _ TSem (@t T))). *)
    (* Set Printing All. *)

    Fixpoint to_semantics_0 (a : @t T (typing O)) : iProp :=
      match a with
      | owne E => OwnE O E
      | ownd D => OwnD O D
      | owni i p => @OwnI Σ Formulas _ O i p
      | wsat => ⌜True⌝%I
      end.

    Fixpoint to_semantics (n : index) : @t T (typing n) -> iProp :=
      match n with
      | O => to_semantics_0
      | S m =>
          fix to_semantics_aux (a : @t T (typing (S m))) : iProp :=
        match a with
        | owne E => OwnE (S m) E
        | ownd D => OwnD (S m) D
        | owni i p => @OwnI Σ Formulas _ (S m) i p
        | wsat => @IndexedInvariants.wsat
                   Σ Formulas _ _ _ m
                   (@Syntax.to_semantics _ _ TSem (@t T) to_semantics m)
        end
      end.
    (* Definition to_semantics (n : index) (a : @t T (typing n)) : iProp := *)
    (*   match a with *)
    (*   | owne m E => indexed_iProp n (OwnE n E) m *)
    (*   | ownd m D => indexed_iProp n (OwnD n D) m *)
    (*   | owni m i p => indexed_iProp n (@OwnI Σ Formulas _ n i p) m *)
    (*   end. *)
IndexedInvariants.wsat = 
λ (Σ : GRA.t) (Vars : index → Type) (H : IInvSet Vars) (H0 : GRA.inG (index ==> CoPset.t)%ra Σ) 
  (H1 : GRA.inG (index ==> Gset.t)%ra Σ) (H2 : GRA.inG (IInvSetRA Vars) Σ) 
  (n : index), (∃ I : gmap positive (Vars n), inv_auth n I ** inv_satall n I)%I
     : ∀ (Σ : GRA.t) (Vars : index → Type),
         IInvSet Vars
         → GRA.inG (index ==> CoPset.t)%ra Σ
           → GRA.inG (index ==> Gset.t)%ra Σ → GRA.inG (IInvSetRA Vars) Σ → index → iProp

    (*   Definition OwnE `{@GRA.inG (index ==> CoPset.t)%ra Σ} (n : index) (E : coPset) := *)
  (*   OwnM (@maps_to_res index CoPset.t n (Some E)). *)

  (* Definition OwnD `{@GRA.inG (index ==> Gset.t)%ra Σ} (n : index) (D : gset positive) := *)
  (*   OwnM (@maps_to_res index Gset.t n (Some D)). *)

  (* Definition OwnI_white {Vars} (n : index) (i : positive) (p : Vars n) : IInvSetRA Vars := *)
  (*   @maps_to_res_dep index (@InvSetRA Vars) *)
  (*                    n *)
  (*                    (Auth.white (@maps_to_res positive (URA.agree (Vars n)) i (Some (Some p)))). *)

  (* Definition OwnI {Vars} `{@GRA.inG (IInvSetRA Vars) Σ} (n : index) (i : positive) (p : Vars n) := *)
  (*   OwnM (OwnI_white n i p). *)

  (* Definition inv_auth_black (I : gmap positive Var) : IInvSetRA Vars := *)
  (*   @maps_to_res_dep index _ *)
  (*                    n (@Auth.black (positive ==> URA.agree Var)%ra *)
  (*                                   (fun (i : positive) => Some <$> (I !! i))). *)

  (* Definition inv_auth (I : gmap positive Var) := *)
  (*   OwnM (inv_auth_black I). *)

  (* Definition inv_satall (I : gmap positive Var) := *)
  (*   ([∗ map] i ↦ p ∈ I, (prop n p) ∗ OwnD n {[i]} ∨ OwnE n {[i]})%I. *)

  (* Definition wsat : iProp := (∃ I, inv_auth I ∗ inv_satall I)%I. *)

  (* Definition inv (N : namespace) P := *)
  (*   (∃ p, ∃ i, ⌜prop n p = P⌝ ∧ ⌜i ∈ (↑N : coPset)⌝ ∧ OwnI n i p)%I. *)

  (* Definition FUpd (A : iProp) (E1 E2 : coPset) (P : iProp) : iProp := *)
  (*   A ∗ wsat n ∗ OwnE n E1 -∗ #=> (A ∗ wsat n ∗ OwnE n E2 ∗ P). *)

  End INTERP.

  Section INDEXED_INVSET.

    Context `{Σ : GRA.t}.
    Context `{T : Type}.
    Context `{TSem : T -> Type}.

    Local Notation typing := (@Syntax.Typ T TSem (@t T)).
    Local Notation As := (fun (i : index) => @t T (typing i)).
    Local Notation Formulas := (fun (i : index) => @Syntax.t T (typing i) (As i)).

    Context `{@GRA.inG (IInvSetRA Formulas) Σ}.

    Global Instance IISet : @IInvSet Σ As :=
      {| prop := @to_semantics Σ T TSem _ |}.

  End INDEXED_INVSET.

  Section TEST.

    Context `{Σ : GRA.t}.

    Local Notation T := Base.t.
    Local Notation TSem := Base.sem.

    Local Notation typing := (@Syntax.Typ T TSem (@t T)).
    Local Notation Formulas := (fun (i : index) => @Syntax.t T (typing i) (@t T (typing i))).

    Context `{@GRA.inG (IInvSetRA Formulas) Σ}.

    Global Instance testIISet : IInvSet Formulas :=
      @Syntax.IISet Σ T TSem (@t T) IISet.

    Import Base.
    Import Syntax.

    Definition wsat n : Formulas (S n) :=
      ex formulaT (fun p => ex (baseT positiveT) (fun i => sepconj (lift p) (lift (atom (owni n i p))))).

    Lemma wsat_test1 :
      prop 3 (wsat 2) =
        (∃ (p : Formulas 2) (i : positive), (prop 2 p) ∗ (OwnI 2 i p))%I.
    Proof.
      ss.
    Qed.

  End TEST.


  Section TEST.

    Import Syntax.

    Context `{TSem : T -> Type}.

    Local Notation t := Atoms.t.


    Local Notation typing := (@Syntax.Typ T TSem t).
    Local Notation Formulas := (fun (i : index) => @Syntax.t T (typing i) (t (typing i))).

    Definition test1 : Formulas 3 :=
      atom (owni 4 xH (atom (owni 2 xH empty))).

    Definition test_OwnI (n : index) (i : positive) (p : Formulas n) : t (typing n) :=
      @owni (typing n) n i p.

    (* Set Printing All. *)

  End TEST.

End Atoms.



(*   Context `{T : Type}. *)
(*     Context `{TSem : T -> Type}. *)

(*     (* Atoms should not interpret arguments. *) *)
(*     Inductive As (V : @type T -> Type) : Type := *)
(*       | owni (p : V formulaT) *)
(*     . *)
(*     (* Inductive As (V : @type T -> Type) : Type := *) *)
(*     (*   | owni (i : index) (p : @t T V (As V)) *) *)
(*     (* . *) *)

(*     Definition typing (i : index) : @type T -> Type := *)
(*       @Typ T TSem As i. *)

(*     (* Definition ttt1 : As (typing 2) := owni (typing 2) 0 (ex formulaT (fun s => pure (s = empty))). *) *)
(*     (* Compute ttt1. *) *)
(*     Definition ttt1 : As (typing 2) := owni (typing 2) (ex formulaT (fun s => pure (s = empty))). *)
(*     Compute ttt1. *)
(*     Goal typing 2 formulaT = @t T (typing 1) (As (typing 1)). *)
(*     Proof. *)
(*       ss. *)
(*     Qed. *)

(*     Definition inv (i : index) (p : typing i formulaT) : *)
(*       @t T (typing i) (As (typing i)) := *)
(*       atom (owni _ p). *)
(*     (* Definition inv (n i : index) (p : @t T (typing i) (As (typing i))) : *) *)
(*     (*   @t T (typing i) (As (typing i)) := *) *)
(*     (*   atom (owni _ n p). *) *)
(*     Definition wsat (i : index) : *)
(*       @t T (typing i) (As (typing i)) := *)
(*       ex formulaT (fun (p : typing i formulaT) => sepconj (lift p) (inv i p)). *)

(*     (* Definition inv0 (n i : index) (p : @t T (typing 2) (As (typing 2))) : *) *)
(*     (*   @t T (typing 3) (As (typing 2)) := *) *)
(*     (*   atom (owni _ n p). *) *)

(*     (* (* Definition of As enforces that  *) *)
(*     (*    p should have the same typing level for itself and its atom  *) *)
(*     (*  *) *) *)
(*     (* Fail Definition inv1 (n : index) (p : @t T (typing 2) (As (typing 3))) : *) *)
(*     (*   @t T (typing 2) (As (typing 3)) := *) *)
(*     (*   atom (owni _ n p). *) *)

(*     (* Definition inv2 q := *) *)
(*     (*   inv 0 3 (atom (owni _ 1 (atom (owni _ 2 q)))). *) *)

(*     (* Fail Definition inv2' q := *) *)
(*     (*   inv 0 3 (atom (owni _ 1 (atom (owni (typing 2) 2 q)))). *) *)

(*     (* Set Printing All. *) *)

(*     (* Definition inv (N : namespace) P := *) *)
(*     (*   (∃ p, ∃ i, ⌜prop p = P⌝ ∧ ⌜i ∈ (↑N : coPset)⌝ ∧ OwnI n i p)%I. *) *)





(*   Section TEST. *)

(*     Context `{A : Type}. *)

(*     Variant tBase := | tBool | tNat. *)
(*     Definition tBase_sem (b : tBase) : Type := *)
(*       match b with | tBool => bool | tNat => nat end. *)

(*     Let Var := @Var tBase tBase_sem A. *)

(*     Compute Var 3 formulaT. *)

(*     (* Goal Var 3 formulaT = @t _ (Var 2) A formulaT. *) *)
(*     Goal Var 3 formulaT = @t _ (Var 2) A. *)
(*     Proof. ss. Qed. *)

(*     Definition syn_bad i := @t tBase (@Var i) A. *)
(*     Notation syn i := (@t tBase (@Var i) A). *)

(*     (* Definition form1 : @syn 2 formulaT := *) *)
(*     Definition form1 : @syn 2 := *)
(*       @ex _ _ _ (baseT tBool) (fun b => empty). *)

(*     (* Goal (syn 1 formulaT) = (Var 2 formulaT). *) *)
(*     Goal (syn 1) = (Var 2 formulaT). *)
(*     Proof. ss. Qed. *)

(*     (* Definition form2 : @syn 2 formulaT := *) *)
(*       (* @ex _ _ _ formulaT (fun (s : Var 2 formulaT) => and (var _ s) (var _ s)). *) *)
(*     Definition form2 : @syn 2 := *)
(*       @ex _ _ _ formulaT (fun (s : Var 2 formulaT) => pure (s = impl empty empty)). *)

(*     (* Definition form3 : @syn 2 formulaT := *) *)
(*     (*   @ex _ _ _ formulaT (fun (s : @t tBase (Var 1) A formulaT) => and (var _ s) (var _ s)). *) *)
(*     Definition form3 : @syn 2 := *)
(*       @ex _ _ _ formulaT (fun (s : @t tBase (Var 1) A) => pure (s = impl empty empty)). *)

(*     (* Definition form4 : @syn 2 formulaT := *) *)
(*     (*   @ex _ _ _ formulaT (fun (s : @syn 1 formulaT) => and (var _ s) (var _ s)). *) *)
(*     Definition form4 : @syn 2 := *)
(*       @ex _ _ _ formulaT (fun (s : @syn 1) => pure (s = impl empty empty)). *)

(*     (* Definition form5 : @syn 2 formulaT := *) *)
(*     (*   @ex _ _ _ formulaT (fun (s : @syn 1 formulaT) => pure (s = wand empty empty)). *) *)
(*     Definition form5 : @syn 2 := *)
(*       @ex _ _ _ formulaT (fun (s : @syn 1) => pure (s = wand empty empty)). *)

(*   End TEST. *)

(* Section TEST. *)

(*     Context `{T : Type}. *)
(*     Context `{TSem : T -> Type}. *)

(*     (* Atoms should not interpret arguments. *) *)
(*     Inductive As (V : @type T -> Type) : Type := *)
(*       | owni (p : V formulaT) *)
(*     . *)
(*     (* Inductive As (V : @type T -> Type) : Type := *) *)
(*     (*   | owni (i : index) (p : @t T V (As V)) *) *)
(*     (* . *) *)

(*     Definition typing (i : index) : @type T -> Type := *)
(*       @Typ T TSem As i. *)

(*     (* Definition ttt1 : As (typing 2) := owni (typing 2) 0 (ex formulaT (fun s => pure (s = empty))). *) *)
(*     (* Compute ttt1. *) *)
(*     Definition ttt1 : As (typing 2) := owni (typing 2) (ex formulaT (fun s => pure (s = empty))). *)
(*     Compute ttt1. *)
(*     Goal typing 2 formulaT = @t T (typing 1) (As (typing 1)). *)
(*     Proof. *)
(*       ss. *)
(*     Qed. *)

(*     Definition inv (i : index) (p : typing i formulaT) : *)
(*       @t T (typing i) (As (typing i)) := *)
(*       atom (owni _ p). *)
(*     (* Definition inv (n i : index) (p : @t T (typing i) (As (typing i))) : *) *)
(*     (*   @t T (typing i) (As (typing i)) := *) *)
(*     (*   atom (owni _ n p). *) *)
(*     Definition wsat (i : index) : *)
(*       @t T (typing i) (As (typing i)) := *)
(*       ex formulaT (fun (p : typing i formulaT) => sepconj (lift p) (inv i p)). *)

(*     (* Definition inv0 (n i : index) (p : @t T (typing 2) (As (typing 2))) : *) *)
(*     (*   @t T (typing 3) (As (typing 2)) := *) *)
(*     (*   atom (owni _ n p). *) *)

(*     (* (* Definition of As enforces that  *) *)
(*     (*    p should have the same typing level for itself and its atom  *) *)
(*     (*  *) *) *)
(*     (* Fail Definition inv1 (n : index) (p : @t T (typing 2) (As (typing 3))) : *) *)
(*     (*   @t T (typing 2) (As (typing 3)) := *) *)
(*     (*   atom (owni _ n p). *) *)

(*     (* Definition inv2 q := *) *)
(*     (*   inv 0 3 (atom (owni _ 1 (atom (owni _ 2 q)))). *) *)

(*     (* Fail Definition inv2' q := *) *)
(*     (*   inv 0 3 (atom (owni _ 1 (atom (owni (typing 2) 2 q)))). *) *)

(*     (* Set Printing All. *) *)

(*     (* Definition inv (N : namespace) P := *) *)
(*     (*   (∃ p, ∃ i, ⌜prop p = P⌝ ∧ ⌜i ∈ (↑N : coPset)⌝ ∧ OwnI n i p)%I. *) *)

(* End TEST. *)
