From stdpp Require Import coPset gmap namespaces.
From sflib Require Import sflib.
From Fairness Require Import PCM IProp IPM IndexedInvariants.
From iris Require Import bi.big_op.
From iris Require base_logic.lib.invariants.
Require Import Program.

(* Section AUX. *)

(*   Variant prod_lt *)
(*           A B (RA: A -> A -> Prop) (RB: B -> B -> Prop): *)
(*     A * B -> A * B -> Prop := *)
(*     | prod_lt_left *)
(*         a0 a1 b0 b1 *)
(*         (ALT: RA a0 a1) *)
(*       : *)
(*       prod_lt RA RB (a0, b0) (a1, b1) *)
(*     | prod_lt_right *)
(*         a0 a1 b0 b1 *)
(*         (ALE: a0 = a1 \/ RA a0 a1) *)
(*         (BLT: RB b0 b1) *)
(*       : *)
(*       prod_lt RA RB (a0, b0) (a1, b1) *)
(*   . *)

(*   Lemma prod_lt_well_founded *)
(*         A B (RA: A -> A -> Prop) (RB: B -> B -> Prop) *)
(*         (WFA: well_founded RA) *)
(*         (WFB: well_founded RB) *)
(*     : *)
(*     well_founded (prod_lt RA RB). *)
(*   Proof. *)
(*     ii. destruct a as [a b]. revert b. *)
(*     induction (WFA a). rename x into a. clear H. rename H0 into IHA. *)
(*     intros b. induction (WFB b). rename x into b. clear H. rename H0 into IHB. *)
(*     econs. i. inv H; eauto. des; subst; eauto. *)
(*   Qed. *)

(* End AUX. *)

Module Syntax.

  Local Notation index := nat.

  Section TYPE.

    Context `{T : Type}.

    (* Inductive type_0 : Type := *)
    (* | baseT_0 (t : T) : type_0 *)
    (* | arrowT_0 : type_0 -> type_0 -> type_0. *)

    Inductive type : Type :=
    | baseT (t : T) : type
    | formulaT : type
    (* | formulaT (i : index) : type *)
    | arrowT : type -> type -> type.

    (* Fixpoint type_size i (ty : type i) : nat := *)
    (*   match ty with *)
    (*   | baseT _ _ => 1 *)
    (*   | formulaT _ => 1 *)
    (*   | arrowT ty1 ty2 => (type_size ty1) + (type_size ty2) + 1 *)
    (*   end. *)

  End TYPE.

  Section SYNTAX.

    Context `{T : Type}.
    Context `{Var : @type T -> Type}.
    Context `{A : Type}.

    Inductive t : Type :=
      atom (a : A) : t
    | lower : (Var formulaT) -> t
    | sepconj (p q : t) : t
    | pure (P : Prop) : t
    | univ : forall ty, (Var ty -> t) -> t
    | ex : forall ty, (Var ty -> t) -> t
    | and (p q : t) : t
    | or (p q : t) : t
    | impl (p q : t) : t
    | wand (p q : t) : t
    | empty : t
    | persistently (p : t) : t
    | plainly (p : t) : t
    | upd (p : t) : t
    .

    (* Inductive t : type -> Type := *)
    (*   atom (a : A) : t formulaT *)
    (* | var : forall ty, Var ty -> t ty *)
    (* (* | app : forall D R, t (arrowT D R) -> t D -> t R *) *)
    (* (* | lam : forall D R, (Var D -> t R) -> t (arrowT D R) *) *)
    (* | sepconj (p q : t formulaT) : t formulaT *)
    (* | pure (P : Prop) : t formulaT *)
    (* | univ : forall ty, (Var ty -> t formulaT) -> t formulaT *)
    (* (* | univ {X : Type} (p : X -> t) *) *)
    (* | ex : forall ty, (Var ty -> t formulaT) -> t formulaT *)
    (* (* | ex {X : Type} (p : X -> t) *) *)
    (* | and (p q : t formulaT) : t formulaT *)
    (* | or (p q : t formulaT) : t formulaT *)
    (* | impl (p q : t formulaT) : t formulaT *)
    (* | wand (p q : t formulaT) : t formulaT *)
    (* | empty : t formulaT *)
    (* | persistently (p : t formulaT) : t formulaT *)
    (* | plainly (p : t formulaT) : t formulaT *)
    (* | upd (p : t formulaT) : t formulaT *)
    (* (* | owni (n : index) (i : positive) (p : t) *) *)
    (* (* | own (r : URA.t) : needs indexed RA *) *)
    (* . *)

  End SYNTAX.

  Section INTERP_TYPE.

    Context `{T : Type}.
    Context `{TSem : T -> Type}.
    (* Context `{Var : @type T -> Type}. *)
    Context `{As : (@type T -> Type) -> Type}.

    Fixpoint Var_0 (ty : @type T) : Type :=
      match ty with
      | baseT b => TSem b
      | formulaT => unit
      | arrowT t1 t2 => (Var_0 t1 -> Var_0 t2)
      end.

    Fixpoint Var (i : index) : @type T -> Type :=
      match i with
      | O => Var_0
      | S j =>
          fix Var_aux (ty : @type T) : Type :=
        match ty with
        | baseT b => TSem b
        | formulaT => @t T (Var j) (As (Var j))
            (* match j with *)
            (* | O => @t T Var_0 (As Var_0) *)
            (* | S k => @t T (Var j) (As (Var k)) *)
            (* end *)
        | arrowT t1 t2 => (Var_aux t1 -> Var_aux t2)
        end
      end.

  End INTERP_TYPE.

  Section TEST.

    Context `{T : Type}.
    Context `{TSem : T -> Type}.

    (* Atoms should not interpret arguments. *)
    Inductive As (V : @type T -> Type) : Type :=
      | owni (i : index) (p : @t T V (As V))
    .

    Definition typing (i : index) : @type T -> Type :=
      @Var T TSem As i.

    Definition ttt1 : As (typing 2) := owni (typing 2) 0 (ex formulaT (fun s => pure (s = empty))).
    Compute ttt1.
    Goal typing 2 formulaT = @t T (typing 1) (As (typing 1)).
    Proof.
      ss.
    Qed.

    Definition inv (n i : index) (p : @t T (typing i) (As (typing i))) :
      @t T (typing i) (As (typing i)) :=
      atom (owni _ n p).

    Definition inv0 (n i : index) (p : @t T (typing 2) (As (typing 2))) :
      @t T (typing 3) (As (typing 2)) :=
      atom (owni _ n p).

    (* Definition of As enforces that 
       p should have the same typing level for itself and its atom 
     *)
    Fail Definition inv1 (n : index) (p : @t T (typing 2) (As (typing 3))) :
      @t T (typing 2) (As (typing 3)) :=
      atom (owni _ n p).

    Definition inv2 q :=
      inv 0 3 (atom (owni _ 1 (atom (owni _ 2 q)))).

    Fail Definition inv2' q :=
      inv 0 3 (atom (owni _ 1 (atom (owni (typing 2) 2 q)))).

    (* Set Printing All. *)

    (* Definition inv (N : namespace) P := *)
    (*   (∃ p, ∃ i, ⌜prop p = P⌝ ∧ ⌜i ∈ (↑N : coPset)⌝ ∧ OwnI n i p)%I. *)

  End TEST.

  (* Section INTERP_TYPE. *)

  (*   Context `{T : Type}. *)
  (*   Context `{TSem : T -> Type}. *)
  (*   Context `{A : Type}. *)

  (*   Fixpoint Var_0 (ty : @type T) : Type := *)
  (*     match ty with *)
  (*     | baseT b => TSem b *)
  (*     | formulaT => unit *)
  (*     | arrowT t1 t2 => (Var_0 t1 -> Var_0 t2) *)
  (*     end. *)

  (*   Fixpoint Var (i : index) : @type T -> Type := *)
  (*     match i with *)
  (*     | O => Var_0 *)
  (*     | S j => *)
  (*         fix Var_aux (ty : @type T) : Type := *)
  (*       match ty with *)
  (*       | baseT b => TSem b *)
  (*       | formulaT => @t T (Var j) A *)
  (*       (* | formulaT => @t T (Var j) A formulaT *) *)
  (*       | arrowT t1 t2 => (Var_aux t1 -> Var_aux t2) *)
  (*       end *)
  (*     end. *)

  (* End INTERP_TYPE. *)

  Section INTERP.

    Context `{Σ : GRA.t}.
    Context `{T : Type}.
    Context `{TSem : T -> Type}.
    Context `{As : (@type T -> Type) -> Type}.

    Local Notation Vars := (@Var T TSem As).

    Context `{Atoms : @IInvSet Σ (fun (n : index) => As (Vars n))}.

    Fixpoint to_semantics_0 (syn : @t T (Vars O) (As (Vars O))) : iProp :=
      match syn with
      | atom a => prop O a
      | lower u => ⌜False⌝%I
      (* | lower u => (fun (x : unit) => ⌜False⌝%I) u *)
      | sepconj p q => Sepconj (to_semantics_0 p) (to_semantics_0 q)
      | pure P => Pure P
      | univ ty p => Univ (fun (x : Vars O ty) => to_semantics_0 (p x))
      | ex ty p => Ex (fun (x : Vars O ty) => to_semantics_0 (p x))
      | and p q => And (to_semantics_0 p) (to_semantics_0 q)
      | or p q => Or (to_semantics_0 p) (to_semantics_0 q)
      | impl p q => Impl (to_semantics_0 p) (to_semantics_0 q)
      | wand p q => Wand (to_semantics_0 p) (to_semantics_0 q)
      | empty => Emp
      | persistently p => Persistently (to_semantics_0 p)
      | plainly p => IProp.Plainly (to_semantics_0 p)
      | upd p => Upd (to_semantics_0 p)
      end.

    Fixpoint to_semantics (i : index) : @t T (Vars i) (As (Vars i)) -> iProp :=
      match i with
      | O => to_semantics_0
      | S j =>
          fix to_semantics_aux (syn : @t T (Vars (S j)) (As (Vars (S j)))) : iProp :=
        match syn with
        | atom a => prop (S j) a
        | lower syn' => to_semantics j syn'
        | sepconj p q => Sepconj (to_semantics_aux p) (to_semantics_aux q)
        | pure P => Pure P
        | univ ty p => Univ (fun (x : Vars (S j) ty) => to_semantics_aux (p x))
        | ex ty p => Ex (fun (x : Vars (S j) ty) => to_semantics_aux (p x))
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

  TODO

  Section INVSET.

    Context `{Σ : GRA.t}.
    Context `{T : Type}.
    Context `{Var : @type T -> Type}.
    Context `{A : Type}.
    Context `{Atoms : @InvSet Σ A}.

    Global Instance I : @InvSet Σ (@t T Var A) :=
      {| prop := @to_semantics Σ T Var A Atoms |}.

  End INVSET.

  Section INDEXED_INVSET.

    Context `{Σ : GRA.t}.
    Context `{T : Type}.
    Context `{TSem : T -> Type}.
    TODO
    Notation Vars := (@Var T TSem
    Context `{As : index -> Type}.
    Context `{iAtoms : forall (i : index), @InvSet Σ (As i)}.

    

  End INDEXED_INVSET.

  Section TEST.

    Context `{A : Type}.

    Variant tBase := | tBool | tNat.
    Definition tBase_sem (b : tBase) : Type :=
      match b with | tBool => bool | tNat => nat end.

    Let Var := @Var tBase tBase_sem A.

    Compute Var 3 formulaT.

    (* Goal Var 3 formulaT = @t _ (Var 2) A formulaT. *)
    Goal Var 3 formulaT = @t _ (Var 2) A.
    Proof. ss. Qed.

    Definition syn_bad i := @t tBase (@Var i) A.
    Notation syn i := (@t tBase (@Var i) A).

    (* Definition form1 : @syn 2 formulaT := *)
    Definition form1 : @syn 2 :=
      @ex _ _ _ (baseT tBool) (fun b => empty).

    (* Goal (syn 1 formulaT) = (Var 2 formulaT). *)
    Goal (syn 1) = (Var 2 formulaT).
    Proof. ss. Qed.

    (* Definition form2 : @syn 2 formulaT := *)
      (* @ex _ _ _ formulaT (fun (s : Var 2 formulaT) => and (var _ s) (var _ s)). *)
    Definition form2 : @syn 2 :=
      @ex _ _ _ formulaT (fun (s : Var 2 formulaT) => pure (s = impl empty empty)).

    (* Definition form3 : @syn 2 formulaT := *)
    (*   @ex _ _ _ formulaT (fun (s : @t tBase (Var 1) A formulaT) => and (var _ s) (var _ s)). *)
    Definition form3 : @syn 2 :=
      @ex _ _ _ formulaT (fun (s : @t tBase (Var 1) A) => pure (s = impl empty empty)).

    (* Definition form4 : @syn 2 formulaT := *)
    (*   @ex _ _ _ formulaT (fun (s : @syn 1 formulaT) => and (var _ s) (var _ s)). *)
    Definition form4 : @syn 2 :=
      @ex _ _ _ formulaT (fun (s : @syn 1) => pure (s = impl empty empty)).

    (* Definition form5 : @syn 2 formulaT := *)
    (*   @ex _ _ _ formulaT (fun (s : @syn 1 formulaT) => pure (s = wand empty empty)). *)
    Definition form5 : @syn 2 :=
      @ex _ _ _ formulaT (fun (s : @syn 1) => pure (s = wand empty empty)).

  End TEST.

End Syntax.

Module Atoms.

  Local Set Printing Universes.

  Local Notation index := nat.

  Section ATOMS.

    Polymorphic Inductive t :=
      | own_unit (x : unit)
      | owni (n : index) (i : positive) (p : @Syntax.t t)
    .

    Definition test1 n i :=
      owni n i (Syntax.atom (owni n i (Syntax.empty))).
    Definition test2 n i :=
      owni n i (Syntax.and (Syntax.empty) (Syntax.pure (1 = 1))).
    Fail Definition test3 n i :=
      @Syntax.ex t _ (fun (s : @Syntax.t t) => Syntax.pure (s = Syntax.atom (owni n i (@Syntax.ex t _ (fun (s' : Syntax.t) => Syntax.pure (s' = Syntax.atom (owni n i Syntax.empty))))))).
    TODO
    Definition test4 n i :=
      @Syntax.ex t _ (fun (s : Syntax.t) => Syntax.pure (s = Syntax.atom (owni n i (@Syntax.ex t _ (fun m => Syntax.and Syntax.empty (Syntax.pure (m = 1))))))).
    Definition test3 n i :=
      owni n i (Syntax.ex (fun (s : Syntax.t) => Syntax.empty)).
    Definition test2 n i :=
      owni n i (Syntax.ex (fun (s : Syntax.t) => Syntax.pure (s = Syntax.empty))).

    (* Polymorphic Inductive t@{i j k} : Type@{k} := *)
    (*   | own_unit (x : unit) *)
    (*   | owni (n : index) (i : positive) (p : @Syntax.t@{i j} t) *)
    (* . *)

    (* Polymorphic Fixpoint embedT@{i j k l | k < l} (a : t@{i j k}) : t@{i j l} := *)
    (*   match a with *)
    (*   | owni n i (p : Syntax.t) => owni n i (Syntax.castA@{k l i j} embedT p) *)
    (*   end. *)


  (* Definition OwnE `{@GRA.inG (index ==> CoPset.t)%ra Σ} (n : index) (E : coPset) := *)
  (*   OwnM (@maps_to_res index CoPset.t n (Some E)). *)

  (* Definition OwnD `{@GRA.inG (index ==> Gset.t)%ra Σ} (n : index) (D : gset positive) := *)
  (*   OwnM (@maps_to_res index Gset.t n (Some D)). *)

  (* Definition OwnI_white {Var} (n : index) (i : positive) (p : Var) : IInvSetRA Var := *)
  (*   @maps_to_res index (Auth.t (positive ==> URA.agree Var))%ra *)
  (*                n (Auth.white (@maps_to_res positive (URA.agree Var) i (Some (Some p)))). *)

  (* Definition OwnI {Var} `{@GRA.inG (IInvSetRA Var) Σ} (n : index) (i : positive) (p : Var) := *)
  (*   OwnM (OwnI_white n i p). *)

  (* Definition inv_auth_black (I : gmap positive Var) : IInvSetRA Var := *)
  (*   @maps_to_res index _ *)
  (*                n (@Auth.black (positive ==> URA.agree Var)%ra *)
  (*                               (fun (i : positive) => Some <$> (I !! i))). *)

  (* Definition inv_auth (I : gmap positive Var) := *)
  (*   OwnM (inv_auth_black I). *)

  (* Definition inv_satall (I : gmap positive Var) := *)
  (*   ([∗ map] i ↦ p ∈ I, (prop p) ∗ OwnD n {[i]} ∨ OwnE n {[i]})%I. *)

  (* Definition wsat : iProp := (∃ I, inv_auth I ∗ inv_satall I)%I. *)

  (* Definition inv (N : namespace) P := *)
  (*   (∃ p, ∃ i, ⌜prop p = P⌝ ∧ ⌜i ∈ (↑N : coPset)⌝ ∧ OwnI n i p)%I. *)

  (* Definition FUpd (A : iProp) (E1 E2 : coPset) (P : iProp) : iProp := *)
  (*   A ∗ wsat n ∗ OwnE n E1 -∗ #=> (A ∗ wsat n ∗ OwnE n E2 ∗ P). *)

  End ATOMS.

  Section INTERP.

    Context `{Σ : GRA.t}.
    Context `{@GRA.inG Unit Σ}.

    Definition to_semantics (a : t) : iProp :=
      match a with
      | own_unit x => OwnM (x : Unit)
      end.

  End INTERP.

  Section INVSET.

    Context `{Σ : GRA.t}.
    Context `{@GRA.inG Unit Σ}.

    Global Instance I : @InvSet Σ t :=
      {| prop := to_semantics |}.

  End INVSET.

End Atoms.

Section TEST.

  Local Notation index := nat.

  Local Set Printing Universes.

  Context `{Σ : GRA.t}.
  Context `{A : Type}.
  Context `{Atomics : @InvSet Σ A}.
  Context `{@GRA.inG (IInvSetRA (@t A)) Σ}.

  Print Universes.

  Definition inv_test (n : nat) (i : positive) (P : iProp) : Syntax.t :=
    Syntax.ex (fun (p : Syntax.t) =>
                 (Syntax.and
                   (Syntax.pure (@prop _ _ (@Syntax.I _ _ Atomics _) p = P))
                   (Syntax.owni n i p))).
Syntax.I@{} = 
λ (Σ : GRA.t) (A : Type@{Fairness.LogicSyntaxUP.597}) (Atomics : InvSet A) 
  (H : GRA.inG (IInvSetRA Syntax.t@{Fairness.LogicSyntaxUP.598 Fairness.LogicSyntaxUP.599}) Σ),
  {| prop := Syntax.to_semantics |}
     : ∀ (Σ : GRA.t) (A : Type@{Fairness.LogicSyntaxUP.597}),
         InvSet A
         → GRA.inG (IInvSetRA Syntax.t@{Fairness.LogicSyntaxUP.598 Fairness.LogicSyntaxUP.599}) Σ
           → InvSet Syntax.t@{Fairness.LogicSyntaxUP.589 Fairness.LogicSyntaxUP.590}
(*  |= Set < InvSet.u0
       Set < OwnI.u0
       Fairness.LogicSyntaxUP.589 < InvSet.u0
       Fairness.LogicSyntaxUP.589 < OwnI.u0
       Fairness.LogicSyntaxUP.590 < InvSet.u0
       Fairness.LogicSyntaxUP.590 < OwnI.u0
       Fairness.LogicSyntaxUP.396 <= InvSet.u0
       Fairness.LogicSyntaxUP.396 <= OwnI.u0
       Fairness.LogicSyntaxUP.588 <= InvSet.u0
       Fairness.LogicSyntaxUP.588 <= Fairness.LogicSyntaxUP.396
       Fairness.LogicSyntaxUP.589 <= Univ_obligation_1.u0
       Fairness.LogicSyntaxUP.590 <= Ex_obligation_1.u0
       Fairness.LogicSyntaxUP.597 <= Fairness.LogicSyntaxUP.396
       Fairness.LogicSyntaxUP.597 <= Fairness.LogicSyntaxUP.588
       Fairness.LogicSyntaxUP.589 = Fairness.LogicSyntaxUP.598
       Fairness.LogicSyntaxUP.590 = Fairness.LogicSyntaxUP.599 *)
  Definition inv (N : namespace) P :=
    (∃ p, ∃ i, ⌜prop p = P⌝ ∧ ⌜i ∈ (↑N : coPset)⌝ ∧ OwnI n i p)%I.

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

End TEST.

Section INDEXEDINV.

  Context `{Σ : GRA.t}.
  Context `{A : Type}.
  Context `{Atomics : @InvSet Σ A}.

  Fixpoint indexed (n : nat) (BaseI : @InvSet Σ (@Syntax.t A)) : @InvSet Σ (@Syntax.t A) :=
    match n with
      | O => @Syntax.I Σ A Atomics 


End INDEXEDINV.



Section TEST.

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

  Definition iisra0 := IInvSetRA (@Syntax.it A 0).
  Definition iisra1 := IInvSetRA (@Syntax.it A 1).
  (* Definition iisra n := IInvSetRA (@Syntax.it A n). *)
  Definition iisra := IInvSetRA (@Syntax.t A).

  Definition OwnI_white_test (i : positive) (p : @Syntax.t A) : IInvSetRA (@Syntax.t A) :=
    @maps_to_res index (Auth.t (positive ==> URA.agree (@Syntax.t A)))%ra
                 2
                 (Auth.white (@maps_to_res positive (URA.agree (@Syntax.t A))
                                           i (Some (Some (Syntax.ex (fun s => Syntax.pure (s = p))))))).

  Definition OwnI_test `{Σ0 : GRA.t} `{@GRA.inG (IInvSetRA (@Syntax.t A)) Σ0}
             (i : positive) (p : @Syntax.t A) :=
    OwnM (OwnI_white_test i p).

  Definition OwnI_white_test2 (i : positive) (p : @Syntax.t A) : IInvSetRA (@Syntax.t A) :=
    @maps_to_res index (Auth.t (positive ==> URA.agree (@Syntax.t A)))%ra
                 2
                 (Auth.white (@maps_to_res positive (URA.agree (@Syntax.t A))
                                           i (Some (Some (Syntax.ex (fun s => Syntax.pure (s = p))))))).

  Definition OwnI_test2 `{Σ0 : GRA.t} `{@GRA.inG (IInvSetRA (@Syntax.t A)) Σ0}
             (i : positive) (p : @Syntax.t A) :=
    OwnM (OwnI_white_test2 i p).

  Definition OwnI_test3 `{Σ0 : GRA.t} `{@GRA.inG (IInvSetRA (@Syntax.t A)) Σ0}
             (i : positive) (p : @Syntax.t A) (q : @Syntax.t A) :=
    ((OwnI_test i p) ∗ (OwnI_test2 i q))%I.

  Print Universes.
OwnI_test3 = 
λ (Σ0 : GRA.t) (H : GRA.inG (IInvSetRA Syntax.t@{OwnI_white_test.u2 OwnI_white_test.u3}) Σ0) 
  (i : positive) (p : Syntax.t@{OwnI_white_test.u0 OwnI_white_test.u1}) 
  (q : Syntax.t@{OwnI_white_test2.u0 OwnI_white_test2.u1}), OwnI_test i p ** OwnI_test2 i q
     : ∀ Σ0 : GRA.t,
         GRA.inG (IInvSetRA Syntax.t@{OwnI_white_test.u2 OwnI_white_test.u3}) Σ0
         → positive
           → Syntax.t@{OwnI_white_test.u0 OwnI_white_test.u1}
             → Syntax.t@{OwnI_white_test2.u0 OwnI_white_test2.u1} → iProp
(* iisra.u0 < IInvSetRA.u0 *)
(* iisra.u1 < IInvSetRA.u0 *)
OwnI_white_test = 
λ (i : positive) (p : Syntax.t@{OwnI_white_test.u0 OwnI_white_test.u1}),
  maps_to_res 2
    (Auth.white
       (maps_to_res i
          (Some
             (Some
                (Syntax.ex@{OwnI_white_test.u2 OwnI_white_test.u3}
                   (λ s : Syntax.t@{OwnI_white_test.u0 OwnI_white_test.u1},
                      Syntax.pure@{OwnI_white_test.u2 OwnI_white_test.u3} (s = p)))))))
     : positive
       → Syntax.t@{OwnI_white_test.u0 OwnI_white_test.u1}
         → IInvSetRA Syntax.t@{OwnI_white_test.u2 OwnI_white_test.u3}
OwnI_white_test.u0 < Coq.Relations.Relation_Definitions.1
                   < OwnI_white_test.u3
OwnI_white_test.u1 < Coq.Relations.Relation_Definitions.1
                   < OwnI_white_test.u3
OwnI_white_test.u2 < IInvSetRA.u0
                   < MRet.u0
                   < URA.agree_obligation_4.u0
OwnI_white_test.u3 < IInvSetRA.u0
                   < MRet.u0
                   < URA.agree_obligation_4.u0

OwnI_test = 
λ (Σ0 : GRA.t) (H : GRA.inG (IInvSetRA Syntax.t@{OwnI_white_test.u2 OwnI_white_test.u3}) Σ0) 
  (i : positive) (p : Syntax.t@{OwnI_white_test.u0 OwnI_white_test.u1}),
  OwnM (OwnI_white_test i p)
     : ∀ Σ0 : GRA.t,
         GRA.inG (IInvSetRA Syntax.t@{OwnI_white_test.u2 OwnI_white_test.u3}) Σ0
         → positive → Syntax.t@{OwnI_white_test.u0 OwnI_white_test.u1} → iProp

  Definition cast (A : Type) : nat -> A

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


  Local Instance Σ: GRA.t:=
    GRA.of_list [].

  Local Instance Atomics : InvSet unit :=
    {| prop := fun _ => emp%I |}.


  Lemma test0 :
    forall (n : nat),
      @prop _ _ (Syntax.InvSet) (Syntax.pure (@prop _ _ Syntax.InvSet (Syntax.sepconj (Syntax.pure True) (Syntax.atom tt)) = (⌜True⌝ ∗ emp)%I))
      =
        (⌜(@prop _ _ (Syntax.InvSet) (Syntax.sepconj (Syntax.pure True) (Syntax.atom tt)) = (⌜True⌝ ∗ emp)%I)⌝)%I.
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
