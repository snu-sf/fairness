From stdpp Require Import coPset gmap namespaces.
From sflib Require Import sflib.
From Fairness Require Import PCM IProp IPM.
From Fairness Require Import IndexedInvariants.
(* From Fairness Require Import IndexedInvariants LogicSyntaxHOAS PCMForSyntax. *)
From iris Require Import bi.big_op.
From iris Require base_logic.lib.invariants.

Local Notation index := nat.

Module Atom.

  Section ATOMS.

    (* Context `{T : Type}. *)
    Context `{Σ : PCM.GRA.t}.

    (* TODO: more atoms *)

    (* Atom do not interpret arguments. *)
    Inductive t {Typ : Syntax.type -> Type} : Type :=
    | own {M : PCMForSyntax.URA.t} {IN : In M σ} (r : M)
    (* | own {M : PCMForSyntax.URA.t} {IN : PCMForSyntax.GRA.inG M σ} (r : M) *)
    | owne (E : coPset)
    | ownd (D : gset positive)
    | owni (i : positive) (p : @Syntax.t Typ (@t Typ))
    | syn_inv_auth_l (ps : list (prod positive (@Syntax.t Typ (@t Typ))))
    (* Non strictly positive occurrence *)
    (* | own_inv_auth (ps : gmap positive (@Syntax.t Typ (@t Typ))) *)
    .

    (* Inductive t {Typ : @Syntax.type T -> Type} : Type := *)
    (* | owne (E : coPset) *)
    (* | ownd (D : gset positive) *)
    (* | owni (i : positive) (p : @Syntax.t T Typ (@t Typ)) *)
    (* | syn_inv_auth_l (ps : list (prod positive (@Syntax.t T Typ (@t Typ)))) *)
    (* (* Non strictly positive occurrence *) *)
    (* (* | own_inv_auth (ps : gmap positive (@Syntax.t T Typ (@t Typ))) *) *)
    (* . *)

  End ATOMS.

  Section INTERP.

    Context `{σ : list PCMForSyntax.URA.t}.
    (* Local Notation σ := (PCMForSyntax.GRA.of_list _σ). *)
    (* Context `{σ : PCMForSyntax.GRA.t}. *)
    Context `{Σ : PCM.GRA.t}.
    (* Context `{T : Type}. *)
    (* Context `{TSem : T -> Type}. *)
    Context `{SUB : forall M, In M σ -> PCM.GRA.inG (to_LURA M) Σ}.

    (* This is too strong. *)
    (* Context `{SUB : forall (M : URA.t), PCMForSyntax.GRA.inG M σ -> PCM.GRA.inG (to_LURA M) Σ}. *)

    Local Notation typing := (@Syntax.Typ (@t σ)).
    Local Notation Formulas := (fun (i : index) => @Syntax.t (typing i) (@t σ (typing i))).
    (* Local Notation typing := (@Syntax.Typ T TSem (@t T)). *)
    (* Local Notation Formulas := (fun (i : index) => @Syntax.t T (typing i) (@t T (typing i))). *)

    Context `{@PCM.GRA.inG (IInvSetRA Formulas) Σ}.
    Context `{@PCM.GRA.inG (PCM.URA.pointwise index PCM.CoPset.t) Σ}.
    Context `{@PCM.GRA.inG (PCM.URA.pointwise index PCM.Gset.t) Σ}.

    Definition to_semantics (n : index) (a : @t σ (typing n)) : iProp :=
      match a with
      | @own _ _ M IN r => @OwnM Σ (to_LURA M) (SUB M IN) r
      | owne E => OwnE n E
      | ownd D => OwnD n D
      | owni i p => @OwnI Σ Formulas _ n i p
      | syn_inv_auth_l ps => @inv_auth Σ Formulas _ n (list_to_map ps)
      end.

    (* Definition to_semantics (n : index) (a : @t T (typing n)) : iProp := *)
    (*   match a with *)
    (*   | owne E => OwnE n E *)
    (*   | ownd D => OwnD n D *)
    (*   | owni i p => @OwnI Σ Formulas _ n i p *)
    (*   | syn_inv_auth_l ps => @inv_auth Σ Formulas _ n (list_to_map ps) *)
    (*   end. *)

  End INTERP.

End Atom.

Section WSAT.

  Context `{σ : list PCMForSyntax.URA.t}.
  Context `{Σ : PCM.GRA.t}.
  Context `{SUB : forall M, In M σ -> PCM.GRA.inG (to_LURA M) Σ}.
  (* Context `{Interp : Base.InterpMeta}. *)

  (* Local Notation T := Base.t. *)
  (* Local Notation TSem := (@Base.sem Base.interp). *)
  (* Local Notation TSem := (Base.sem). *)

  Local Notation typing := (@Syntax.Typ (@Atom.t σ)).
  Local Notation Formulas := (fun (n : index) => @Syntax.t (typing n) (@Atom.t σ (typing n))).
  (* Local Notation typing := (@Syntax.Typ T TSem (@Atom.t T)). *)
  (* Local Notation Formulas := (fun (n : index) => @Syntax.t T (typing n) (@Atom.t T (typing n))). *)

  Context `{@PCM.GRA.inG (IInvSetRA Formulas) Σ}.
  Context `{@PCM.GRA.inG (PCM.URA.pointwise index PCM.CoPset.t) Σ}.
  Context `{@PCM.GRA.inG (PCM.URA.pointwise index PCM.Gset.t) Σ}.

  Local Notation AtomSem := (@Atom.to_semantics σ Σ SUB _).
  Local Notation SynSem := (@Syntax.to_semantics Σ (@Atom.t σ) AtomSem).
  (* Local Notation AtomSem := (@Atom.to_semantics Σ _ TSem _ _ _). *)
  (* Local Notation SynSem := (@Syntax.to_semantics Σ _ TSem (@Atom.t T) AtomSem). *)

  Global Instance SynIISet : @IInvSet Σ Formulas := (@Syntax.IISet Σ (@Atom.t σ) AtomSem).
  (* Global Instance SynIISet : @IInvSet Σ Formulas := (@Syntax.IISet Σ _ TSem (@Atom.t T) AtomSem). *)


  Definition syn_inv_auth n (ps : gmap positive (Formulas n)) : @Atom.t σ (typing n) :=
    Atom.syn_inv_auth_l (map_to_list ps).
  (* Definition syn_inv_auth n (ps : gmap positive (Formulas n)) : @Atom.t T (typing n) := *)
  (*   Atom.syn_inv_auth_l (map_to_list ps). *)

  Lemma syn_inv_auth_iProp
        n ps
    :
    Atom.to_semantics n (syn_inv_auth n ps) = inv_auth n ps.
  Proof.
    ss. rewrite list_to_map_to_list. ss.
  Qed.

  Import Atom Syntax.

  Definition syn_inv_satall_fun n : positive -> (Formulas n) -> (Formulas n) :=
    fun i p => or (sepconj p (atom (ownd {[i]}))) (atom (owne {[i]})).
  (* fun i p => Syntax.or (Syntax.sepconj p (Syntax.atom (ownd {[i]}))) (Syntax.atom (owne {[i]})). *)

  Definition syn_inv_satall n (ps : gmap positive (Formulas n)) : Formulas n :=
    @star_gmap (@Atom.t σ) n ps (syn_inv_satall_fun n).
    (* @star_gmap _ TSem (@Atom.t T) n ps (syn_inv_satall_fun n). *)
  (* @Syntax.star_gmap _ TSem (@t T) n ps (inv_satall_fun n). *)


  Lemma syn_inv_satall_fun_iProp
        n i p
    :
    SynSem n (syn_inv_satall_fun n i p) = (((SynSem n p) ∗ (OwnD n {[i]})) ∨ (OwnE n {[i]}))%I.
  Proof.
    unfold syn_inv_satall_fun. rewrite to_semantics_red_or. rewrite to_semantics_red_sepconj. do 2 f_equal.
    all: rewrite to_semantics_red_atom; ss.
  Qed.

  Lemma syn_inv_satall_iProp
        n ps
    :
    SynSem n (syn_inv_satall n ps) = inv_satall n ps.
  Proof.
    ss. unfold syn_inv_satall. rewrite star_gmap_iProp. unfold inv_satall.
    f_equal. extensionalities i p. unfold syn_inv_satall_fun.
    rewrite to_semantics_red_or. rewrite to_semantics_red_sepconj. rewrite ! to_semantics_red_atom.
    ss.
  Qed.

  Definition syn_wsat n : Formulas (S n) :=
    ex (pgmapT formulaT) (fun I => lift (sepconj (atom (syn_inv_auth n I)) (syn_inv_satall n I))).
    (* ex (gmapTpos formulaT) (fun I => lift (sepconj (atom (syn_inv_auth n I)) (syn_inv_satall n I))). *)

  Lemma syn_wsat_iProp
        n
    :
    SynSem (S n) (syn_wsat n) = wsat n.
  Proof.
    unfold syn_wsat, wsat. rewrite to_semantics_red_ex. f_equal. extensionalities I.
    rewrite to_semantics_red_lift. rewrite to_semantics_red_sepconj.
    rewrite to_semantics_red_atom. rewrite syn_inv_auth_iProp. rewrite syn_inv_satall_iProp.
    ss.
  Qed.

End WSAT.
