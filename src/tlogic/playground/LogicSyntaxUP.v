From stdpp Require Import coPset gmap namespaces.
From sflib Require Import sflib.
From Fairness Require Import PCM IPM IndexedInvariants.
From iris Require Import bi.big_op.
From iris Require base_logic.lib.invariants.

Module Syntax.

  Local Set Printing Universes.

  Local Notation index := nat.

  Section SYNTAX.

    Context `{A : Type}.

    Polymorphic Inductive t : Type :=
      atom (a : A)
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
    (* | owni (n : index) (i : positive) (p : t) *)
    .
    (* Polymorphic Inductive t@{i j k} : Type@{k} := *)
    (*   | owni (n : index) (i : positive) (p : @Syntax.t@{i j} t) *)
    (* . *)

    Definition test1 : t :=
      ex (fun (n : nat) => if (n =? 1) then pure (n = 1) else pure (n <> 1)).

    Polymorphic Fixpoint embedT@{i j k | i < k, j < k} (s : t@{i j}) : t@{k k} :=
      match s with
      | atom a => atom a
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
      (* | owni n i p => owni n i (embedT p) *)
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

  Section CAST.

    Polymorphic Fixpoint castA{A : Type} {B : Type} (cast : A -> B) (s : @t A) : @t B :=
      match s with
      | atom a => atom (cast a)
      | sepconj p q => sepconj (castA cast p) (castA cast q)
      | pure P => pure P
      | univ p => univ (fun x => castA cast (p x))
      | ex p => ex (fun x => castA cast (p x))
      (* | own (* Need indexed RA? *) *)
      | and p q => and (castA cast p) (castA cast q)
      | or p q => or (castA cast p) (castA cast q)
      | impl p q => impl (castA cast p) (castA cast q)
      | wand p q => wand (castA cast p) (castA cast q)
      | empty => empty
      | persistently p => persistently (castA cast p)
      | plainly p => plainly (castA cast p)
      (* | later (p : Syntax) *)
      | upd p => upd (castA cast p)
      (* | entails p q => Entails (to_semantics p) (to_semantics q) *)
      (* | owni n i p => owni n i (castA cast p) *)
      end.

  End CAST.

  (* Print Universes. *)

  Section INTERP.

    (* Universes i j x y. *)
    (* Constraint i < x, j < y. *)

    Context `{Σ : GRA.t}.
    Context `{A : Type}.
    Context `{Atomics : @InvSet Σ A}.
    (* Context `{@GRA.inG (IInvSetRA (@t@{i j} A)) Σ}. *)

    (* Polymorphic Fixpoint to_semantics {BaseI : @InvSet Σ (@t A)} (syn : t) : iProp := *)
    (* Polymorphic Fixpoint to_semantics (syn : t@{x y}) : iProp := *)
    Polymorphic Fixpoint to_semantics (syn : t) : iProp :=
      match syn with
      | atom a => prop a
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
      | plainly p => .Plainly (to_semantics p)
      (* | later (p : Syntax) *)
      | upd p => Upd (to_semantics p)
      (* | entails p q => Entails (to_semantics p) (to_semantics q) *)
      (* | owni n i p => @OwnI Σ (@t@{i j} A) _ n i p *)
      end.

  End INTERP.

  Section INVSET.

    Context `{Σ : GRA.t}.
    Context `{A : Type}.
    Context `{Atomics : @InvSet Σ A}.
    (* Context `{@GRA.inG (IInvSetRA (@t A)) Σ}. *)

    Polymorphic Global Instance I : @InvSet Σ (@t A) :=
      {| prop := @to_semantics Σ A Atomics |}.
      (* {| prop := @to_semantics Σ A Atomics _ |}. *)
    (* Polymorphic Global Instance I {n : index} : @InvSet Σ (@it A n) := *)
    (*   {| prop := @to_semantics Σ A Atomics |}. *)

  End INVSET.

End Syntax.

(* Print Universes. *)

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
  (q : Syntax.t@{OwnI_white_test2.u0 OwnI_white_test2.u1}), OwnI_test i p ∗ OwnI_test2 i q
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
