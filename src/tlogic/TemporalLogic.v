From stdpp Require Import coPset gmap namespaces.
From sflib Require Import sflib.
From Fairness Require Import PCM IProp IPM.
From Fairness Require Import IndexedInvariants LogicSyntaxHOAS.
(* From Fairness Require Import ISim. *)
From iris Require Import bi.big_op.
From iris Require base_logic.lib.invariants.

Local Notation index := nat.

Section TLOGIC.

  Section TYPE.

    Inductive type : Type :=
    | baseT (t : Type) : type
    | formulaT : type
    | funT : type -> type -> type
    | pgmapT : type -> type.

  End TYPE.

  Section INTERP_TYPE.

    Fixpoint Typ {form : Type} (ty : type) : Type :=
      match ty with
      | baseT b => b
      | formulaT => form
      | funT ty1 ty2 => (@Typ form ty1 -> @Typ form ty2)
      | pgmapT ty1 => gmap positive (@Typ form ty1)
      end.

  End INTERP_TYPE.

  Section FORMULA.

    Context `{As : forall formula : Type, Type}.

    Definition _formula : index -> Type :=
      @Syntax._formula type (@Typ) As.

    Definition formula : index -> Type :=
      @Syntax.formula type (@Typ) As.

  End FORMULA.

  Section INTERP.

    Context `{As : forall formula : Type, Type}.

    Context `{Σ : GRA.t}.
    Context `{interp_atoms : forall (n : index), As (@_formula As n) -> iProp}.

    Definition formula_sem : forall n, formula n -> iProp :=
      @Syntax.to_semantics type (@Typ) As Σ interp_atoms.

  End INTERP.

End TLOGIC.

Module Atoms.

  Section ATOMS.

    Inductive t {form : Type} : Type :=
    (* | own {A : Atom} (a : A.(T)) *)
    | owni (i : positive) (p : @Syntax.t _ (@Typ) (@t form) form)
    (* | syn_inv_auth_l (ps : list (prod positive form)) *)
    (* (* for invariant system *) *)
    (* | owni (i : positive) (p : t) *)
    (* | syn_inv_auth_l (ps : list (prod positive t)) *)
    (* | syn_inv_auth (ps : gmap positive form) *)
    | syn_inv_auth_l (ps : list (prod positive (@Syntax.t _ (@Typ) (@t form) form)))
    (* | syn_wsat_auth (X : gset index) *)
    (* Non strictly positive occurrence *)
    (* | syn_inv_auth (ps : gmap positive (@Syntax.t _ (@Typ) (@t form) form)) *)
    | ownd (D : gset positive)
    | owne (E : coPset)
    .

  End ATOMS.

  Section INTERP.

    Local Notation _Formula := (@_formula (@t)).
    Local Notation Formula := (@formula (@t)).

    Context `{Σ : PCM.GRA.t}.

    (* Local Notation Formula := (@formula (@t Σ)). *)

    Context `{@PCM.GRA.inG (IInvSetRA Formula) Σ}.
    Context `{@PCM.GRA.inG (URA.pointwise index CoPset.t) Σ}.
    Context `{@PCM.GRA.inG (URA.pointwise index Gset.t) Σ}.

    Definition to_semantics n (a : @t (_Formula n)) : iProp :=
      match a with
      | owni i p => @OwnI Σ Formula _ n i p
      | syn_inv_auth_l ps => @inv_auth Σ Formula _ n (list_to_map ps)
      (* | syn_inv_auth ps => @inv_auth Σ Formula _ n ps *)
      | ownd D => OwnD n D
      | owne E => OwnE n E
      end.

    (* Definition to_semantics n (a : @t (Formula n)) : iProp := *)
    (*   match a with *)
    (*   | owni i p => @OwnI Σ Formula _ (S n) i p *)
    (*   (* | syn_inv_auth_l ps => @inv_auth Σ Formulas _ n (list_to_map ps) *) *)
    (*   end. *)


    (* (* Definition to_semantics_0 (a : @t Σ Empty_set) : iProp := *) *)
    (* Definition to_semantics_0 (a : @t Empty_set) : iProp := *)
    (*   match a with *)
    (*   (* | @own _ _ A r => A.(interp) r *) *)
    (*   | owni i p => @OwnI Σ Formula _ O i p *)
    (*   (* | syn_inv_auth_l ps => @inv_auth Σ Formulas _ n (list_to_map ps) *) *)
    (*   end. *)

    (* (* Definition to_semantics n (a : @t Σ (Formula n)) : iProp := *) *)
    (* Definition to_semantics n (a : @t (Formula n)) : iProp := *)
    (*   match a with *)
    (*   (* | @own _ _ A r => A.(interp) r *) *)
    (*   | owni i p => @OwnI Σ Formula _ (S n) i p *)
    (*   (* | syn_inv_auth_l ps => @inv_auth Σ Formulas _ n (list_to_map ps) *) *)
    (*   end. *)

  End INTERP.

End Atoms.

Section TL.

  Local Notation index := nat.

  Definition Formula := (@formula (@Atoms.t)).

  Context `{Σ : PCM.GRA.t}.

  (* Definition Formula := (@formula (@Atoms.t Σ)). *)

  Context `{@GRA.inG (IInvSetRA Formula) Σ}.
  Context `{@GRA.inG (URA.pointwise index CoPset.t) Σ}.
  Context `{@GRA.inG (URA.pointwise index Gset.t) Σ}.

  (* Local Notation AtomSem0 := (@Atoms.to_semantics_0 Σ _). *)
  Definition AtomSem := (@Atoms.to_semantics Σ _ _ _).
  Definition SynSem n : Formula n -> iProp := (@formula_sem (@Atoms.t) Σ AtomSem n).
  (* Local Notation SynSem := (@formula_sem (@Atoms.t) Σ AtomSem0 AtomSem). *)
  (* Local Notation SynSem := (@formula_sem (@Atoms.t Σ) Σ AtomSem0 AtomSem). *)

  Global Instance SynIISet : @IInvSet Σ Formula :=
    (@Syntax.IISet _ _ _ Σ AtomSem).
  (* Global Instance SynIISet : @IInvSet Σ Formula := *)
  (*   (@Syntax.IISet _ _ _ Σ AtomSem0 AtomSem). *)

  (* Global Instance IIIn (i : index) (p : Formula i) : @IInvIn Σ Formula SynIISet i (SynSem i p) := *)
  (*   @Syntax.IIIn _ _ _ Σ AtomSem0 AtomSem i p. *)

End TL.

Notation "'τ{' t ',' n '}'" := (@Typ (Formula n) t).
Notation "'⟦' F ',' n '⟧'" := (SynSem n F).

Section TEST.

  Context `{Σ : GRA.t}.
  Context `{@PCM.GRA.inG (IInvSetRA Formula) Σ}.
  Context `{@GRA.inG (URA.pointwise index CoPset.t) Σ}.
  Context `{@GRA.inG (URA.pointwise index Gset.t) Σ}.

  Definition test : Formula 3 :=
    ⟨Atoms.owni xH (∃ (p : τ{formulaT, 2}), ⌜p = emp⌝)⟩%F.

  Lemma testp n :
    ⟦(⟨Atoms.owni xH ⟨(Atoms.owni xH emp)⟩⟩
         ∗ (∃ (p : τ{formulaT, n}), ↑(p -∗ ⌜p = emp⌝)))%F, (S n)⟧
    =
      ((OwnI (S n) xH ⟨Atoms.owni xH emp⟩%F) ∗ (∃ p, ⟦p, n⟧ -∗ ⌜p = emp%F⌝))%I.
  Proof.
    ss.
  Qed.

End TEST.

Section TEST.

  Import Syntax.

  Context `{Σ : GRA.t}.
  Context `{@PCM.GRA.inG (IInvSetRA Formula) Σ}.
  Context `{@GRA.inG (URA.pointwise index CoPset.t) Σ}.
  Context `{@GRA.inG (URA.pointwise index Gset.t) Σ}.

  Definition test0 := ((Syntax.atom (Atoms.owni xH (Syntax.ex formulaT (fun (p : Formula 2) => Syntax.pure (p = Syntax.empty)) : Formula 3))) : Formula 3).
  Let test1 := (Syntax.atom (Atoms.owni xH (Syntax.ex formulaT (fun (p : Formula 2) => Syntax.pure (p = Syntax.empty)) : Formula 3))) : Formula 3.
  Let test2 := (Syntax.atom (Atoms.owni xH (Syntax.ex formulaT (fun p => Syntax.pure (p = Syntax.empty))))) : Formula 3.

  Fail Check (Syntax.atom (Atoms.owni xH (Syntax.ex formulaT (fun (p : Formula 2) => Syntax.pure (p = Syntax.empty)) : Formula 2))) : Formula 3.
  Fail Check (Syntax.atom (Atoms.owni xH (Syntax.ex formulaT (fun (p : Formula 1) => Syntax.pure (p = Syntax.empty))))) : Formula 3.
  Fail Check (Syntax.atom (Atoms.owni xH (Syntax.ex formulaT (fun (p : Formula 0) => Syntax.pure (p = Syntax.empty))))) : Formula 3.

  Goal (SynSem _ test1) = OwnI 3 xH (Syntax.ex formulaT (fun (p : Formula 2) => Syntax.pure (p = Syntax.empty))).
  Proof.
    ss.
  Qed.

  Goal (SynSem 3 (Syntax.sepconj test1 test2)) =
         ((OwnI 3 xH (Syntax.ex formulaT (fun (p : Formula 2) => Syntax.pure (p = Syntax.empty)))) ∗ (OwnI 3 xH (Syntax.ex formulaT (fun (p : Formula 2) => Syntax.pure (p = Syntax.empty)))))%I.
  Proof.
    subst test1 test2. setoid_rewrite red_sem_sepconj. ss.
  Qed.

  Lemma testp0 n :
    SynSem (S n) (sepconj (atom (Atoms.owni xH (atom (Atoms.owni xH empty))))
                      (ex formulaT (fun (p : Formula n) => lift (wand p (pure (p = empty))))))
    =
      ((OwnI (S n) xH (atom (Atoms.owni xH empty))) ∗ (∃ p, (SynSem n p) -∗ ⌜p = empty⌝))%I.
  Proof.
    ss.
  Qed.

End TEST.


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


(* Old *)

(* Section Atom. *)

(*   Context `{Σ : GRA.t}. *)

(*   Class Atom := *)
(*     { T : Type *)
(*     ; interp : T -> iProp *)
(*     }. *)

(* End Atom. *)

(* Module Atoms. *)

(*   Section ATOMS. *)

(*     Context `{Σ : GRA.t}. *)

(*     Inductive t {Typ : Syntax.type -> Type} : Type := *)
(*     | own {A : Atom} (a : A.(T)) *)
(*     (* | ownes (Es : coPsets) *) *)
(*     (* | inv (N : namespace) (p : @Syntax.t Typ (@t Typ)) *) *)
(*     (* | wsats *) *)
(*     (* | owne (E : coPset) *) *)
(*     (* | ownd (D : gset positive) *) *)
(*     | owni (i : positive) (p : @Syntax.t Typ (@t Typ)) *)
(*     | syn_inv_auth_l (ps : list (prod positive (@Syntax.t Typ (@t Typ)))) *)
(*     (* | syn_wsat_auth (X : gset index) *) *)
(*     (* Non strictly positive occurrence *) *)
(*     (* | own_inv_auth (ps : gmap positive (@Syntax.t Typ (@t Typ))) *) *)
(*     . *)

(*   End ATOMS. *)

(*   Section INTERP. *)

(*     Context `{Σ : PCM.GRA.t}. *)

(*     Local Notation typing := (@Syntax.Typ (@t Σ)). *)
(*     Local Notation Formulas := (fun (i : index) => @Syntax.t (typing i) (@t Σ (typing i))). *)

(*     Context `{@PCM.GRA.inG (IInvSetRA Formulas) Σ}. *)
(*     (* Context `{@PCM.GRA.inG (PCM.URA.pointwise index PCM.CoPset.t) Σ}. *) *)
(*     (* Context `{@PCM.GRA.inG (PCM.URA.pointwise index PCM.Gset.t) Σ}. *) *)

(*     Definition to_semantics (n : index) (a : @t Σ (typing n)) : iProp := *)
(*       match a with *)
(*       | @own _ _ A r => A.(interp) r *)
(*       (* | ownes Es => OwnEs Es *) *)
(*       (* | inv N p => @IndexedInvariants.inv Σ Formulas  *) *)
(*       (* | owne E => OwnE n E *) *)
(*       (* | ownd D => OwnD n D *) *)
(*       | owni i p => @OwnI Σ Formulas _ n i p *)
(*       | syn_inv_auth_l ps => @inv_auth Σ Formulas _ n (list_to_map ps) *)
(*       (* | syn_wsat_auth X => wsat_auth X *) *)
(*       end. *)

(*   End INTERP. *)

(* End Atoms. *)

(* Section WSAT. *)

(*   Context `{Σ : PCM.GRA.t}. *)

(*   Local Notation typing := (@Syntax.Typ (@Atoms.t Σ)). *)
(*   Local Notation Formulas := (fun (n : index) => @Syntax.t (typing n) (@Atoms.t Σ (typing n))). *)

(*   Context `{@PCM.GRA.inG (IInvSetRA Formulas) Σ}. *)
(*   (* Context `{@PCM.GRA.inG (PCM.URA.pointwise index PCM.CoPset.t) Σ}. *) *)
(*   (* Context `{@PCM.GRA.inG (PCM.URA.pointwise index PCM.Gset.t) Σ}. *) *)

(*   Local Notation AtomSem := (@Atoms.to_semantics Σ _). *)
(*   (* Local Notation AtomSem := (@Atoms.to_semantics Σ _ _ _). *) *)
(*   Local Notation SynSem := (@Syntax.to_semantics Σ (@Atoms.t Σ) AtomSem). *)

(*   Global Instance SynIISet : @IInvSet Σ Formulas := (@Syntax.IISet Σ (@Atoms.t Σ) AtomSem). *)


(*   Definition syn_inv_auth n (ps : gmap positive (Formulas n)) : @Atoms.t Σ (typing n) := *)
(*     Atoms.syn_inv_auth_l (map_to_list ps). *)

(*   Lemma syn_inv_auth_iProp *)
(*         n ps *)
(*     : *)
(*     Atoms.to_semantics n (syn_inv_auth n ps) = inv_auth n ps. *)
(*   Proof. *)
(*     ss. rewrite list_to_map_to_list. ss. *)
(*   Qed. *)

(*   Import Atoms Syntax. *)

(*   Definition syn_inv_satall_fun n : positive -> (Formulas n) -> (Formulas n) := *)
(*     fun i p => or (sepconj p (atom (ownd {[i]}))) (atom (owne {[i]})). *)

(*   Definition syn_inv_satall n (ps : gmap positive (Formulas n)) : Formulas n := *)
(*     @star_gmap (@Atoms.t Σ) n ps (syn_inv_satall_fun n). *)

(*   Lemma syn_inv_satall_fun_iProp *)
(*         n i p *)
(*     : *)
(*     SynSem n (syn_inv_satall_fun n i p) = (((SynSem n p) ∗ (OwnD n {[i]})) ∨ (OwnE n {[i]}))%I. *)
(*   Proof. *)
(*     unfold syn_inv_satall_fun. rewrite to_semantics_red_or. rewrite to_semantics_red_sepconj. do 2 f_equal. *)
(*     all: rewrite to_semantics_red_atom; ss. *)
(*   Qed. *)

(*   Lemma syn_inv_satall_iProp *)
(*         n ps *)
(*     : *)
(*     SynSem n (syn_inv_satall n ps) = inv_satall n ps. *)
(*   Proof. *)
(*     ss. unfold syn_inv_satall. rewrite star_gmap_iProp. unfold inv_satall. *)
(*     f_equal. extensionalities i p. unfold syn_inv_satall_fun. *)
(*     rewrite to_semantics_red_or. rewrite to_semantics_red_sepconj. rewrite ! to_semantics_red_atom. *)
(*     ss. *)
(*   Qed. *)

(*   Definition syn_wsat n : Formulas (S n) := *)
(*     ex (pgmapT formulaT) (fun I => lift (sepconj (atom (syn_inv_auth n I)) (syn_inv_satall n I))). *)

(*   Lemma syn_wsat_iProp *)
(*         n *)
(*     : *)
(*     SynSem (S n) (syn_wsat n) = wsat n. *)
(*   Proof. *)
(*     unfold syn_wsat, wsat. rewrite to_semantics_red_ex. f_equal. extensionalities I. *)
(*     rewrite to_semantics_red_lift. rewrite to_semantics_red_sepconj. *)
(*     rewrite to_semantics_red_atom. rewrite syn_inv_auth_iProp. rewrite syn_inv_satall_iProp. *)
(*     ss. *)
(*   Qed. *)

(* End WSAT. *)
