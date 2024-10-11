From stdpp Require Import coPset gmap namespaces.
From sflib Require Import sflib.
From Fairness Require Import PCM IPM IndexedInvariants.
From Fairness Require Import ISim SimDefaultRA SimWeakest.
From Fairness Require Import LogicSyntaxHOAS.
From iris Require Import bi.big_op.
From iris Require base_logic.lib.invariants.
Require Import Program.

Local Notation index := nat.

Section STATETYPES.

  Class StateTypes :=
    { st_src_type : Type ;
      st_tgt_type : Type ;
      id_src_type : ID ;
      id_tgt_type : ID
    }.

End STATETYPES.

Section TYPES.

  Section TYPE.

    Inductive type : Type :=
    | baseT (t : Type) : type
    | formulaT : type
    | funT : type -> type -> type
    | prodT : type -> type -> type
    | sumT : type -> type -> type
    | listT : type -> type
    | pgmapT : type -> type.

  End TYPE.

  Section INTERP_TYPE.

    Fixpoint Typ (form : Type) (ty : type) : Type :=
      match ty with
      | baseT b => b
      | formulaT => form
      | funT ty1 ty2 => (Typ form ty1 -> Typ form ty2)
      | prodT ty1 ty2 => prod (Typ form ty1) (Typ form ty2)
      | sumT ty1 ty2 => sum (Typ form ty1) (Typ form ty2)
      | listT ty1 => list (Typ form ty1)
      | pgmapT ty1 => gmap positive (Typ form ty1)
      end.

  End INTERP_TYPE.

  Section FORMULA.

    Context `{As : forall formula : Type, Type}.

    Definition _formula : index -> Type :=
      @Syntax._formula type Typ As.

    Definition formula : index -> Type :=
      @Syntax.formula type Typ As.

  End FORMULA.

  Section INTERP.

    Context `{As : forall formula : Type, Type}.

    Context `{Σ : GRA.t}.
    Context `{interp_atoms : forall (n : index), As (@_formula As n) -> iProp}.

    Definition formula_sem : forall n, formula n -> iProp :=
      @Syntax.to_semantics type (@Typ) As Σ interp_atoms.

  End INTERP.

End TYPES.

(** Notations and Coercions. *)
Coercion baseT : Sortclass >-> type.

Declare Scope formula_type_scope.
Delimit Scope formula_type_scope with ftype.
Bind Scope formula_type_scope with type.

Notation "⇣ T" := (baseT T) (at level 90) : formula_type_scope.
Notation "'Φ'" := (formulaT) : formula_type_scope.
Infix "->" := (funT) : formula_type_scope.
Infix "*" := (prodT) : formula_type_scope.
Infix "+" := (sumT) : formula_type_scope.


Section BIGOP.

  Context `{As : forall formula : Type, Type}.

  Context `{Σ : GRA.t}.
  Variable interp_atoms : forall (n : index), As (@_formula As n) -> iProp.

  Local Notation _Formula := (@_formula As).
  Local Notation Formula := (@formula As).

  Import Syntax.
  Local Notation Sem := (@to_semantics _ Typ As Σ interp_atoms).

  (* Maybe we can make Syntax as an instance for big_opMs. *)
  Definition syn_big_sepM
             (n : index) {K} {H1 : EqDecision K} {H2 : Countable K}
             {A} (I : @gmap K H1 H2 (Typ (Formula n) A))
             (f : K -> (Typ (Formula n) A) -> Formula n)
    : Formula n :=
    fold_right (fun hd tl => @sepconj _ Typ (As (_Formula n)) (_Formula n) (uncurry f hd) tl) empty (map_to_list I).

  Lemma red_syn_big_sepM n K {H1 : EqDecision K} {H2 : Countable K} A I f :
    Sem n (@syn_big_sepM n K _ _ A I f) = ([∗ map] i ↦ a ∈ I, Sem n (f i a))%I.
  Proof.
    ss. unfold big_opM. rewrite seal_eq. unfold big_op.big_opM_def.
    unfold syn_big_sepM. simpl. remember (map_to_list I) as L.
    clear HeqL I. induction L.
    { ss. }
    ss. rewrite @red_sem_sepconj. rewrite IHL. f_equal.
    destruct a. ss.
  Qed.

  Definition syn_big_sepL1
             (n : index) {A} (I : Typ (Formula n) (listT A))
             (f : (Typ (Formula n) A) -> Formula n)
    : Formula n :=
    fold_right (fun hd tl => @sepconj _ Typ (As (_Formula n)) (_Formula n) (f hd) tl) empty I.

  Lemma red_syn_big_sepL1 n A I f :
    Sem n (@syn_big_sepL1 n A I f) = ([∗ list] a ∈ I, Sem n (f a))%I.
  Proof.
    ss. induction I; ss.
    rewrite @red_sem_sepconj. rewrite IHI. f_equal.
  Qed.

  (* Additional definitions. *)

  Definition syn_sat_list
             n X (Ts : X -> Type) (x : X) (intp : Ts x -> Formula n) (l : list (Ts x))
    : Formula n :=
    foldr (fun t (p : Formula n) => (intp t ∗ p)%F) ⊤%F l.

  Lemma red_syn_sat_list n X Ts x intp l :
    Sem n (syn_sat_list n X Ts x intp l) =
      @Regions.sat_list X Ts Σ x (fun (t : Ts x) => Sem n (intp t)) l.
  Proof.
    induction l; ss.
    rewrite @red_sem_sepconj. rewrite IHl. f_equal.
  Qed.

End BIGOP.

(* Notations. *)
Notation "'[∗' n 'map]' k ↦ x ∈ m , P" :=
  (syn_big_sepM n m (fun k x => P))
    (at level 200, n at level 1, m at level 10, k, x at level 1, right associativity,
      format "[∗ n map] k ↦ x ∈ m , P") : formula_scope.
Notation "'[∗' n , A 'map]' k ↦ x ∈ m , P" :=
  (syn_big_sepM n (A:=A) m (fun k x => P))
    (at level 200, n at level 1, m at level 10, k, x, A at level 1, right associativity,
      format "[∗ n , A map] k ↦ x ∈ m , P") : formula_scope.
Notation "'[∗' n 'list]' x ∈ l , P" :=
  (syn_big_sepL1 n l (fun k x => P))
    (at level 200, n at level 1, l at level 10, x at level 1, right associativity,
      format "[∗ n list] x ∈ l , P") : formula_scope.
Notation "'[∗' n , A 'list]' x ∈ l , P" :=
  (syn_big_sepL1 n (A:=A) l (fun k x => P))
    (at level 200, n at level 1, l at level 10, x, A at level 1, right associativity,
      format "[∗ n , A list] x ∈ l , P") : formula_scope.


Section AUXATOM.

  Class AuxAtom := { aAtom : Type }.

  Context `{Σ : GRA.t}.

  Class AAInterp {AA : AuxAtom} := { aaintp : @aAtom AA -> iProp }.

End AUXATOM.

Module Atom.

  Section ATOM.

    Context {AA : AuxAtom}.
    Context {STT : StateTypes}.

    Local Notation state_src := (@st_src_type STT).
    Local Notation state_tgt := (@st_tgt_type STT).
    Local Notation ident_src := (@id_src_type STT).
    Local Notation ident_tgt := (@id_tgt_type STT).

    Inductive t {form : Type} : Type :=
    (** Simple atoms. *)
    | satom (s : aAtom)
    (** Atoms to express the invariant system. *)
    | owni (i : positive) (p : @Syntax.t _ (@Typ) (@t form) form)
    | syn_inv_auth_l (ps : list (prod positive (@Syntax.t _ (@Typ) (@t form) form)))
    | ownd (x : index) (D : gset positive)
    | owne (x : index) (E : coPset)
    | syn_wsat_auth (x : index)
    | syn_owne_auth (Es : coPsets)
    (** Atoms to express state invariants of wpsim. *)
    | ob_ths (ths : TIdSet.t)
    | ob_st_src (st_src : state_src)
    | ow_st_src (st_src : state_src)
    | ob_st_tgt (st_tgt : state_tgt)
    | ow_st_tgt (st_tgt : state_tgt)
    | fair_src (im_src : @FairBeh.imap ident_src owf)
    | fair_tgt (im_tgt : @FairBeh.imap (sum_tid ident_tgt) nat_wf) (ths : TIdSet.t)
    (** Atoms to express liveness logic. *)
    | obl_edges_sat
    | obl_arrows_auth (x : index)
    | obl_arrows_regions_black (l : list ((sum_tid ident_tgt) * nat * Ord.t * Qp * nat * (@Syntax.t _ (@Typ) (@t form) form)))
    | obl_arrow_done1 (x : nat)
    | obl_arrow_done2 (k : nat)
    | obl_arrow_pend (i : sum_tid ident_tgt) (k : nat) (c : Ord.t) (q : Qp)
    .

  End ATOM.

  Section INTERP.

    Context {AA : AuxAtom}.
    Context {STT : StateTypes}.

    Local Notation att := (@t AA STT).
    Local Notation _Formula := (@_formula (@att)).
    Local Notation Formula := (@formula (@att)).

    Context `{Σ : GRA.t}.
    Context `{AAI : @AAInterp Σ AA}.
    (* Invariant related default RAs *)
    Context `{OWNESRA : @GRA.inG OwnEsRA Σ}.
    Context `{OWNDSRA : @GRA.inG OwnDsRA Σ}.
    Context `{IINVSETRA : @GRA.inG (IInvSetRA Formula) Σ}.
    (* State related default RAs *)
    Context `{THDRA: @GRA.inG ThreadRA Σ}.
    Context `{STATESRC: @GRA.inG (stateSrcRA st_src_type) Σ}.
    Context `{STATETGT: @GRA.inG (stateTgtRA st_tgt_type) Σ}.
    Context `{IDENTSRC: @GRA.inG (identSrcRA id_src_type) Σ}.
    Context `{IDENTTGT: @GRA.inG (identTgtRA id_tgt_type) Σ}.
    (* Liveness logic related default RAs *)
    Context `{OBLGRA: @GRA.inG ObligationRA.t Σ}.
    Context `{EDGERA: @GRA.inG EdgeRA Σ}.
    Context `{ONESHOTRA: @GRA.inG ArrowShotRA Σ}.
    Context `{ARROWRA: @GRA.inG (@ArrowRA id_tgt_type Formula) Σ}.

    Definition to_semantics n (a : @t AA STT (_Formula n)) : iProp :=
      match a with
      (** Simple atoms. *)
      | satom s => aaintp s
      (** Atom to express the invariant system. *)
      | owni i p => @OwnI Σ Formula _ n i p
      | syn_inv_auth_l ps => @inv_auth Σ Formula _ n (list_to_map ps)
      | ownd x D => OwnD x D
      | owne x E => OwnE x E
      | syn_wsat_auth x => wsat_auth x
      | syn_owne_auth Es => OwnE_auth Es
      (** Atoms to express state invariants of wpsim. *)
      | ob_ths ths =>
          OwnM (Auth.black (Some ths: (NatMapRA.t unit)): ThreadRA)
      | ob_st_src st_src =>
          OwnM (Auth.black (Excl.just (Some st_src): @Excl.t (option st_src_type)): stateSrcRA _)
      | ow_st_src st_src =>
          St_src st_src
      | ob_st_tgt st_tgt =>
          OwnM (Auth.black (Excl.just (Some st_tgt): @Excl.t (option st_tgt_type)): stateTgtRA _)
      | ow_st_tgt st_tgt =>
          St_tgt st_tgt
      | fair_src im_src =>
          FairRA.sat_source im_src
      | fair_tgt im_tgt ths =>
          FairRA.sat_target im_tgt ths
      (** Atoms to express liveness logic. *)
      | obl_edges_sat => ObligationRA.edges_sat
      | obl_arrows_auth x => ObligationRA.arrows_auth x
      | obl_arrows_regions_black l =>
          Regions.black n l
      | obl_arrow_done1 x =>
          OwnM (FiniteMap.singleton x (OneShot.shot ()): ArrowShotRA)
      | obl_arrow_done2 k =>
          ObligationRA.shot k
      | obl_arrow_pend i k c q =>
          (∃ (n : nat), FairRA.black Prism.id i n q ∗ ObligationRA.white k (c × n)%ord)%I
      end.

  End INTERP.

End Atom.

Section TL.

  Context {AA : AuxAtom}.
  Context {STT : StateTypes}.

  Definition _Formula := (@_formula (@Atom.t AA STT)).
  Definition Formula := (@formula (@Atom.t AA STT)).

  Context `{Σ : GRA.t}.
  Context `{AAI : @AAInterp Σ AA}.
  (* Invariant related default RAs *)
  Context `{OWNESRA : @GRA.inG OwnEsRA Σ}.
  Context `{OWNDSRA : @GRA.inG OwnDsRA Σ}.
  Context `{IINVSETRA : @GRA.inG (IInvSetRA Formula) Σ}.
  (* State related default RAs *)
  Context `{THDRA: @GRA.inG ThreadRA Σ}.
  Context `{STATESRC: @GRA.inG (stateSrcRA st_src_type) Σ}.
  Context `{STATETGT: @GRA.inG (stateTgtRA st_tgt_type) Σ}.
  Context `{IDENTSRC: @GRA.inG (identSrcRA id_src_type) Σ}.
  Context `{IDENTTGT: @GRA.inG (identTgtRA id_tgt_type) Σ}.
  (* Liveness logic related default RAs *)
  Context `{OBLGRA: @GRA.inG ObligationRA.t Σ}.
  Context `{EDGERA: @GRA.inG EdgeRA Σ}.
  Context `{ONESHOTRA: @GRA.inG ArrowShotRA Σ}.
  Context `{ARROWRA: @GRA.inG (@ArrowRA id_tgt_type Formula) Σ}.

  Definition AtomSem := (@Atom.to_semantics AA STT Σ AAI _ _ _ _ _ _ _ _ _ _ _ _).
  Definition SynSem n := (@formula_sem (@Atom.t AA STT) Σ (@AtomSem) n).

  Global Instance SynIISet : @IInvSet Σ Formula :=
    (@Syntax.IISet _ _ _ Σ AtomSem).

  (* Global Instance IIIn (i : index) (p : Formula i) : @IInvIn Σ Formula SynIISet i (SynSem i p) := *)
  (*   @Syntax.IIIn _ _ _ Σ AtomSem0 AtomSem i p. *)

End TL.

(** Notations and coercions. *)
Notation "'τ{' t ',' n '}'" := (@Typ (@_Formula _ _ n) t).
Notation "'τ{' t '}'" := (@Typ (@_Formula _ _ _) t).
Notation "'⟪' A ',' n '⟫'" := (AtomSem n A).
Notation "'⟦' F ',' n '⟧'" := (SynSem n F).


Section RED.

  Context {AA : AuxAtom}.
  Context {STT : StateTypes}.

  Context `{Σ : GRA.t}.
  Context `{AAI : @AAInterp Σ AA}.
  (* Invariant related default RAs *)
  Context `{OWNESRA : @GRA.inG OwnEsRA Σ}.
  Context `{OWNDSRA : @GRA.inG OwnDsRA Σ}.
  Context `{IINVSETRA : @GRA.inG (IInvSetRA Formula) Σ}.
  (* State related default RAs *)
  Context `{THDRA: @GRA.inG ThreadRA Σ}.
  Context `{STATESRC: @GRA.inG (stateSrcRA st_src_type) Σ}.
  Context `{STATETGT: @GRA.inG (stateTgtRA st_tgt_type) Σ}.
  Context `{IDENTSRC: @GRA.inG (identSrcRA id_src_type) Σ}.
  Context `{IDENTTGT: @GRA.inG (identTgtRA id_tgt_type) Σ}.
  (* Liveness logic related default RAs *)
  Context `{OBLGRA: @GRA.inG ObligationRA.t Σ}.
  Context `{EDGERA: @GRA.inG EdgeRA Σ}.
  Context `{ONESHOTRA: @GRA.inG ArrowShotRA Σ}.
  Context `{ARROWRA: @GRA.inG (@ArrowRA id_tgt_type Formula) Σ}.

  Lemma red_tl_atom n a :
    ⟦⟨a⟩%F, n⟧ = ⟪a, n⟫.
  Proof. apply red_sem_atom. Qed.

  Lemma red_tl_lift_0 p :
    ⟦(↑p)%F, 0⟧ = ⌜False⌝%I.
  Proof. apply red_sem_lift_0. Qed.

  Lemma red_tl_lift n p :
    ⟦(↑p)%F, S n⟧ = ⟦p, n⟧ .
  Proof. apply red_sem_lift. Qed.

  Lemma red_tl_sepconj n p q :
    ⟦(p ∗ q)%F, n⟧ = (⟦p, n⟧ ∗ ⟦q, n⟧)%I.
  Proof. apply red_sem_sepconj. Qed.

  Lemma red_tl_pure n P :
    ⟦⌜P⌝%F, n⟧ = ⌜P⌝%I.
  Proof. apply red_sem_pure. Qed.

  Lemma red_tl_univ n ty p :
    ⟦(∀ x, p x)%F, n⟧ = (∀ (x : τ{ty}), ⟦p x, n⟧)%I.
  Proof. apply red_sem_univ. Qed.

  Lemma red_tl_ex n ty p :
    ⟦(∃ x, p x)%F, n⟧ = (∃ (x : τ{ty}), ⟦p x, n⟧)%I.
  Proof. apply red_sem_ex. Qed.

  Lemma red_tl_and n p q :
    ⟦(p ∧ q)%F, n⟧ = (⟦p, n⟧ ∧ ⟦q, n⟧)%I.
  Proof. apply red_sem_and. Qed.

  Lemma red_tl_or n p q :
    ⟦(p ∨ q)%F, n⟧ = (⟦p, n⟧ ∨ ⟦q, n⟧)%I.
  Proof. apply red_sem_or. Qed.

  Lemma red_tl_impl n p q :
    ⟦(p → q)%F, n⟧ = (⟦p, n⟧ → ⟦q, n⟧)%I.
  Proof. apply red_sem_impl. Qed.

  Lemma red_tl_wand n p q :
    ⟦(p -∗ q)%F, n⟧ = (⟦p, n⟧ -∗ ⟦q, n⟧)%I.
  Proof. apply red_sem_wand. Qed.

  Lemma red_tl_empty n :
    ⟦emp%F, n⟧ = emp%I.
  Proof. apply red_sem_empty. Qed.

  Lemma red_tl_persistently n p :
    ⟦(<pers> p)%F, n⟧ = (<pers> ⟦p, n⟧)%I.
  Proof. apply red_sem_persistently. Qed.

  Lemma red_tl_plainly n p :
    ⟦(■ p)%F, n⟧ = (.Plainly ⟦p, n⟧)%I.
  Proof. apply red_sem_plainly. Qed.

  Lemma red_tl_upd n p :
    ⟦( |==> p)%F, n⟧ = ( |==> ⟦p, n⟧)%I.
  Proof. apply red_sem_upd. Qed.

  (** Derived ones. *)

  Lemma red_tl_affinely n p :
    ⟦(<affine> p)%F, n⟧ = (<affine> ⟦p, n⟧)%I.
  Proof. apply red_sem_affinely. Qed.

  Lemma red_tl_intuitionistically n p :
    ⟦(□ p)%F, n⟧ = (□ ⟦p, n⟧)%I.
  Proof. apply red_sem_intuitionistically. Qed.

  Lemma red_tl_big_sepM n A K {EQ : EqDecision K} {CNT : Countable K} I f :
    ⟦@syn_big_sepM (@Atom.t _ _) n K _ _ A I f, n⟧ = ([∗ map] i ↦ p ∈ I, ⟦f i p, n⟧)%I.
  Proof. apply red_syn_big_sepM. Qed.

  Lemma red_tl_big_sepL1 n A I f :
    ⟦@syn_big_sepL1 (@Atom.t _ _) n A I f, n⟧ = ([∗ list] a ∈ I, ⟦f a, n⟧)%I.
  Proof. apply red_syn_big_sepL1. Qed.

  Lemma red_tl_sat_list n X Ts x intp l :
    ⟦@syn_sat_list (@Atom.t _ _) n X Ts x intp l, n⟧
    = Regions.sat_list Ts x (fun t => ⟦intp t, n⟧) l.
  Proof. apply red_syn_sat_list. Qed.

End RED.
Global Opaque SynSem.

(** Simple formula reduction tactics. *)
Ltac red_tl_binary_once := (try rewrite ! @red_tl_sepconj;
                            try rewrite ! @red_tl_and;
                            try rewrite ! @red_tl_or;
                            try rewrite ! @red_tl_impl;
                            try rewrite ! @red_tl_wand
                           ).

Ltac red_tl_unary_once := (try rewrite ! @red_tl_atom;
                           try rewrite ! @red_tl_lift;
                           try rewrite ! @red_tl_pure;
                           try rewrite ! @red_tl_univ;
                           try rewrite ! @red_tl_ex;
                           try rewrite ! @red_tl_empty;
                           try rewrite ! @red_tl_persistently;
                           try rewrite ! @red_tl_plainly;
                           try rewrite ! @red_tl_upd;
                           try rewrite ! @red_tl_affinely;
                           try rewrite ! @red_tl_intuitionistically
                          ).

Ltac red_tl_binary := repeat red_tl_binary_once.
Ltac red_tl_unary := repeat red_tl_unary_once.
Ltac red_tl := repeat (red_tl_binary; red_tl_unary).


Section WSATS.

  Context {AA : AuxAtom}.
  Context {STT : StateTypes}.

  Context `{Σ : GRA.t}.
  Context `{AAI : @AAInterp Σ AA}.
  (* Invariant related default RAs *)
  Context `{OWNESRA : @GRA.inG OwnEsRA Σ}.
  Context `{OWNDSRA : @GRA.inG OwnDsRA Σ}.
  Context `{IINVSETRA : @GRA.inG (IInvSetRA Formula) Σ}.
  (* State related default RAs *)
  Context `{THDRA: @GRA.inG ThreadRA Σ}.
  Context `{STATESRC: @GRA.inG (stateSrcRA st_src_type) Σ}.
  Context `{STATETGT: @GRA.inG (stateTgtRA st_tgt_type) Σ}.
  Context `{IDENTSRC: @GRA.inG (identSrcRA id_src_type) Σ}.
  Context `{IDENTTGT: @GRA.inG (identTgtRA id_tgt_type) Σ}.
  (* Liveness logic related default RAs *)
  Context `{OBLGRA: @GRA.inG ObligationRA.t Σ}.
  Context `{EDGERA: @GRA.inG EdgeRA Σ}.
  Context `{ONESHOTRA: @GRA.inG ArrowShotRA Σ}.
  Context `{ARROWRA: @GRA.inG (@ArrowRA id_tgt_type Formula) Σ}.


  Import Atom.

  (** Definitions for wsat. *)

  Definition syn_inv_auth n (ps : gmap positive (Formula n)) : Atom.t :=
    syn_inv_auth_l (map_to_list ps).

  Lemma red_syn_inv_auth n ps :
    ⟪syn_inv_auth n ps, n⟫ = inv_auth n ps.
  Proof.
    ss. rewrite list_to_map_to_list. ss.
  Qed.

  Definition syn_inv_satall_fun n : positive -> Formula n -> Formula n :=
    fun i p => ((p ∗ ⟨ownd n {[i]}⟩) ∨ ⟨owne n {[i]}⟩)%F.

  Definition syn_inv_satall n (ps : gmap positive (Formula n)) : Formula n :=
    ([∗ n , formulaT map] k ↦ p ∈ ps, syn_inv_satall_fun n k p)%F.
  (* Definition syn_inv_satall n (ps : gmap positive (Formula n)) : Formula n := *)
  (*   syn_big_sepM n (A:=formulaT) ps (syn_inv_satall_fun n). *)

  Lemma red_syn_inv_satall_fun n i p :
    ⟦syn_inv_satall_fun n i p, n⟧ = ((⟦p, n⟧ ∗ (OwnD n {[i]})) ∨ (OwnE n {[i]}))%I.
  Proof.
    unfold syn_inv_satall_fun. red_tl. auto.
  Qed.

  Lemma red_syn_inv_satall n ps :
    ⟦syn_inv_satall n ps, n⟧ = inv_satall n ps.
  Proof.
    ss. unfold syn_inv_satall. rewrite red_tl_big_sepM. ss.
  Qed.

  Definition syn_wsat n : Formula (S n) :=
    (∃ (I : τ{pgmapT Φ, S n}), ↑(⟨syn_inv_auth n I⟩ ∗ (syn_inv_satall n I)))%F.

  Lemma red_syn_wsat n :
    ⟦syn_wsat n, S n⟧ = wsat n.
  Proof.
    unfold syn_wsat, wsat. red_tl. f_equal. extensionalities I.
    red_tl. rewrite red_syn_inv_auth. rewrite red_syn_inv_satall. auto.
  Qed.

  (** Definitions for wsats. *)

  Fixpoint lifts {n} (p : Formula n) m {struct m} : Formula (m + n) :=
    match m with
    | O => p
    | S m' => (↑(@lifts n p m'))%F
    end.

  (* Definition syn_wsats n : Formula (S n) := *)
  (*   syn_big_sepL1 n (baseT nat) (seq 0 n) (fun m => lifts (syn_wsat m) (n - (S m))). *)

  Fixpoint lifts_seps (p : forall n, Formula (S n)) n : Formula n :=
    match n with
    | O => emp%F
    | S m => ((↑(lifts_seps p m)) ∗ (p m))%F
    end.

  Lemma unfold_lifts_seps p n :
    lifts_seps p (S n) = (↑(lifts_seps p n) ∗ (p n))%F.
  Proof. ss. Qed.

  Definition syn_wsats n : Formula n := lifts_seps syn_wsat n.

  Lemma unfold_syn_wsats n :
    syn_wsats (S n) = (↑(syn_wsats n) ∗ (syn_wsat n))%F.
  Proof. apply unfold_lifts_seps. Qed.

  Lemma syn_wsats_to_wsats n :
    ⟦syn_wsats n, n⟧ ⊢ wsats n.
  Proof.
    induction n; ss. rewrite unfold_syn_wsats. red_tl. iIntros "[A B]".
    iApply fold_wsats. rewrite red_syn_wsat. iFrame. iApply IHn. iFrame.
  Qed.

  Lemma wsats_to_syn_wsats n :
    wsats n ⊢ ⟦syn_wsats n, n⟧.
  Proof.
    induction n; ss. rewrite unfold_syn_wsats. red_tl. iIntros "A".
    iPoseProof (unfold_wsats with "A") as "[A B]". rewrite red_syn_wsat. iFrame.
    iApply IHn. iFrame.
  Qed.

  (** Definitions for OwnEs. *)

  Definition syn_owne_satall_fun x : index -> coPset -> (Formula x) :=
    fun n E => ⟨owne n E⟩%F.

  Definition syn_owne_satall x (Es : coPsets) : Formula x :=
    ([∗ x , coPset map] k ↦ E ∈ Es, syn_owne_satall_fun x k E)%F.
  (* Definition syn_owne_satall x (Es : coPsets) : Formula x := *)
  (*   syn_big_sepM x index coPset Es (syn_owne_satall_fun x). *)

  Lemma red_syn_owne_satall x Es :
    ⟦syn_owne_satall x Es, x⟧ = OwnE_satall Es.
  Proof.
    unfold syn_owne_satall. rewrite red_tl_big_sepM. ss.
  Qed.

  Definition syn_ownes x (Es : coPsets) : Formula x :=
    (⟨syn_owne_auth Es⟩ ∗ (syn_owne_satall x Es))%F.

  Lemma red_syn_ownes x Es :
    ⟦syn_ownes x Es, x⟧ = OwnEs Es.
  Proof.
    unfold syn_ownes, OwnEs. red_tl. f_equal. apply red_syn_owne_satall.
  Qed.

  (** Definitions for inv and FUpd. *)

  Definition syn_inv (n : index) (N : namespace) (p : Formula n) : Formula n :=
    (∃ (i : τ{positive}), ⌜i ∈ (nclose N : coPset)⌝ ∧ ⟨owni i p⟩)%F.

  Lemma red_syn_inv n N p :
    ⟦syn_inv n N p, n⟧ = inv n N p.
  Proof.
    done.
  Qed.

  Definition syn_fupd (n : index) (A : Formula n) (Es1 Es2 : coPsets) (p : Formula n) : Formula n :=
    (A ∗ syn_wsats n ∗ syn_ownes _ Es1 -∗ |==> (A ∗ syn_wsats n ∗ syn_ownes _ Es2 ∗ p))%F.

  Lemma syn_fupd_to_fupd n A Es1 Es2 p :
    ⟦syn_fupd n A Es1 Es2 p, n⟧ ⊢ FUpd n ⟦A, n⟧ Es1 Es2 ⟦p, n⟧.
  Proof.
    unfold syn_fupd. red_tl. rewrite ! red_syn_ownes.
    Local Transparent FUpd.
    iIntros "F [A [W E]]". iPoseProof (wsats_to_syn_wsats with "W") as "W".
    iMod ("F" with "[A E W]") as "(A & W & E & P)". iFrame.
    iPoseProof (syn_wsats_to_wsats with "W") as "W".
    iModIntro. iFrame.
    Local Opaque FUpd.
  Qed.

  Lemma fupd_to_syn_fupd n A Es1 Es2 p :
    FUpd n ⟦A, n⟧ Es1 Es2 ⟦p, n⟧ ⊢ ⟦syn_fupd n A Es1 Es2 p, n⟧.
  Proof.
    unfold syn_fupd. red_tl. rewrite ! red_syn_ownes.
    Local Transparent FUpd.
    iIntros "F [A [W E]]". iPoseProof (syn_wsats_to_wsats with "W") as "W".
    iMod ("F" with "[A E W]") as "(A & W & E & P)". iFrame.
    iPoseProof (wsats_to_syn_wsats with "W") as "W".
    iModIntro. iFrame.
    Local Opaque FUpd.
  Qed.

End WSATS.
Global Opaque syn_wsat.
Global Opaque syn_wsats.
Global Opaque syn_ownes.
Global Opaque syn_inv.
Global Opaque syn_fupd.

Section OBLIG.

  Context {AA : AuxAtom}.
  Context {STT : StateTypes}.

  Context `{Σ : GRA.t}.
  Context `{AAI : @AAInterp Σ AA}.
  (* Invariant related default RAs *)
  Context `{OWNESRA : @GRA.inG OwnEsRA Σ}.
  Context `{OWNDSRA : @GRA.inG OwnDsRA Σ}.
  Context `{IINVSETRA : @GRA.inG (IInvSetRA Formula) Σ}.
  (* State related default RAs *)
  Context `{THDRA: @GRA.inG ThreadRA Σ}.
  Context `{STATESRC: @GRA.inG (stateSrcRA st_src_type) Σ}.
  Context `{STATETGT: @GRA.inG (stateTgtRA st_tgt_type) Σ}.
  Context `{IDENTSRC: @GRA.inG (identSrcRA id_src_type) Σ}.
  Context `{IDENTTGT: @GRA.inG (identTgtRA id_tgt_type) Σ}.
  (* Liveness logic related default RAs *)
  Context `{OBLGRA: @GRA.inG ObligationRA.t Σ}.
  Context `{EDGERA: @GRA.inG EdgeRA Σ}.
  Context `{ONESHOTRA: @GRA.inG ArrowShotRA Σ}.
  Context `{ARROWRA: @GRA.inG (@ArrowRA id_tgt_type Formula) Σ}.


  Local Notation _dataT := ((sum_tid id_tgt_type) * nat * Ord.t * Qp * nat)%type.
  Local Notation dataT := (fun (n : index) => (_dataT * Formula n)%type).

  Import Atom.

  Definition syn_obl_arrow n : dataT n -> Formula n :=
    fun '(i, k, c, q, x, f) =>
      ((□ (f -∗ □ f))
         ∗
         ((⟨obl_arrow_done1 x⟩ ∗ ⟨obl_arrow_done2 k⟩ ∗ f)
          ∨
            ⟨obl_arrow_pend i k c q⟩))%F.

  Lemma red_syn_obl_arrow n d :
    ⟦syn_obl_arrow n d, n⟧ = ObligationRA.arrow n d.
  Proof.
    unfold syn_obl_arrow. des_ifs.
  Qed.

  Definition syn_arrows_sat_list n (l : list (dataT n)) : Formula n :=
    syn_sat_list n _ dataT n (syn_obl_arrow n) l.

  Lemma red_syn_arrows_sat_list n l :
    ⟦syn_arrows_sat_list n l, n⟧ = Regions.sat_list _ _ (ObligationRA.arrow n) l.
  Proof.
    unfold syn_arrows_sat_list. rewrite red_tl_sat_list. f_equal.
    extensionalities t. apply red_syn_obl_arrow.
  Qed.

  Check (⇣ Ord.t)%ftype.
  Check (⇣ (nat + nat)%type)%ftype.
  (* Check (⇣ (sum_tid id_tgt_type))%ftype. *)

  Definition syn_arrows_sat n : Formula (S n) :=
    (∃ (l : τ{ listT ((⇣(nat + id_tgt_type)) * (⇣nat) * (⇣Ord.t) * (⇣Qp) * (⇣nat) * Φ)%ftype, S n }),
        ↑(⟨obl_arrows_regions_black l⟩ ∗ syn_arrows_sat_list n l))%F.

  Lemma red_syn_arrows_sat n :
    ⟦syn_arrows_sat n, S n⟧ = ObligationRA.arrows_sat n.
  Proof.
    unfold syn_arrows_sat. red_tl. unfold ObligationRA.arrows_sat, Regions.sat.
    f_equal. extensionality l. red_tl. ss.
    rewrite red_syn_arrows_sat_list. f_equal.
  Qed.

  Definition syn_arrows_sats n : Formula n := lifts_seps syn_arrows_sat n.

  Lemma unfold_syn_arrows_sats n :
    syn_arrows_sats (S n) = (↑(syn_arrows_sats n) ∗ (syn_arrows_sat n))%F.
  Proof. apply unfold_lifts_seps. Qed.

  Lemma syn_arrows_sats_to_arrows_sats n :
    ⟦syn_arrows_sats n, n⟧ ⊢ ObligationRA.arrows_sats n.
  Proof.
    induction n; ss. rewrite unfold_syn_arrows_sats. red_tl. iIntros "[A B]".
    iApply Regions.fold_nsats. rewrite red_syn_arrows_sat. iFrame. iApply IHn. iFrame.
  Qed.

  Lemma arrows_sats_to_syn_arrows_sats n :
    ObligationRA.arrows_sats n ⊢ ⟦syn_arrows_sats n, n⟧.
  Proof.
    induction n; ss. rewrite unfold_syn_arrows_sats. red_tl. iIntros "A".
    iPoseProof (Regions.unfold_nsats with "A") as "[A B]". rewrite red_syn_arrows_sat. iFrame.
    iApply IHn. iFrame.
  Qed.

  Definition syn_fairI n : Formula n := (⟨obl_edges_sat⟩ ∗ syn_arrows_sats n)%F.

  Lemma syn_fairI_to_fairI n :
    ⟦syn_fairI n, n⟧ ⊢ fairI n.
  Proof.
    unfold syn_fairI. red_tl. rewrite syn_arrows_sats_to_arrows_sats. unfold fairI. ss.
  Qed.

  Lemma fairI_to_syn_fairI n :
    fairI n ⊢ ⟦syn_fairI n, n⟧.
  Proof.
    unfold syn_fairI. red_tl. unfold fairI. rewrite arrows_sats_to_syn_arrows_sats. ss.
  Qed.

End OBLIG.
Global Opaque syn_obl_arrow.
Global Opaque syn_arrows_sat_list.
Global Opaque syn_arrows_sat.
Global Opaque syn_arrows_sats.



Section TEST.

  Context {AA : AuxAtom}.
  Context {STT : StateTypes}.
  Local Notation state_src := (@st_src_type STT).
  Local Notation state_tgt := (@st_tgt_type STT).
  Local Notation ident_src := (@id_src_type STT).
  Local Notation ident_tgt := (@id_tgt_type STT).

  Context `{Σ : GRA.t}.
  Context `{AAI : @AAInterp Σ AA}.
  (* Invariant related default RAs *)
  Context `{OWNESRA : @GRA.inG OwnEsRA Σ}.
  Context `{OWNDSRA : @GRA.inG OwnDsRA Σ}.
  Context `{IINVSETRA : @GRA.inG (IInvSetRA Formula) Σ}.
  (* State related default RAs *)
  Context `{THDRA: @GRA.inG ThreadRA Σ}.
  Context `{STATESRC: @GRA.inG (stateSrcRA state_src) Σ}.
  Context `{STATETGT: @GRA.inG (stateTgtRA state_tgt) Σ}.
  Context `{IDENTSRC: @GRA.inG (identSrcRA ident_src) Σ}.
  Context `{IDENTTGT: @GRA.inG (identTgtRA ident_tgt) Σ}.
  (* Liveness logic related default RAs *)
  Context `{OBLGRA: @GRA.inG ObligationRA.t Σ}.
  Context `{EDGERA: @GRA.inG EdgeRA Σ}.
  Context `{ONESHOTRA: @GRA.inG ArrowShotRA Σ}.
  Context `{ARROWRA: @GRA.inG (@ArrowRA ident_tgt Formula) Σ}.

  Definition test : Formula 3 :=
    ⟨Atom.owni xH (∃ (p : τ{formulaT, 3}), ⌜p = emp⌝)⟩%F.

  Definition test1 : Formula 3 :=
    ⟨Atom.owni xH (∃ (p : τ{baseT nat, 3}), ⌜p = 2⌝)⟩%F.
  Definition test1' : Formula 3 :=
    ⟨Atom.owni xH (∃ (p : τ{nat, 3}), ⌜p = 2⌝)⟩%F.
  Goal test1 = test1'. Proof. ss. Qed.

  Definition test2 : Formula 3 :=
    ⟨Atom.owni xH (∃ (p : τ{formulaT, 3}), ↑p)⟩%F.
  Fail Definition test3 : Formula 3 :=
    ⟨Atom.owni xH (∃ (p : τ{formulaT, 3}), p)⟩%F.

  Lemma testp n :
    ⟦(⟨Atom.owni xH ⟨(Atom.owni xH emp)⟩⟩ ∗ (∃ (p : τ{formulaT, S n}), ↑(p -∗ ⌜p = emp⌝)))%F, S n⟧
    =
      ((OwnI (S n) xH ⟨Atom.owni xH emp⟩%F) ∗ (∃ (p : τ{formulaT, S n}), ⟦p, n⟧ -∗ ⌜p = emp%F⌝))%I.
  Proof.
    ss.
  Qed.

  Lemma pers_test n (p q r : Formula n) :
    ⊢ ⟦(((□ (p -∗ □ q)) ∗ ((q ∗ q) -∗ r)) → p -∗ r)%F , n⟧.
  Proof.
    red_tl. iIntros "[#A B] C". iPoseProof ("A" with "C") as "#D".
    iPoseProof ("B" with "[D]") as "E". iSplitR; auto.
    iFrame.
  Qed.

  Lemma pers_test1 n (p : Formula n) :
    ⟦(□p)%F, n⟧ ⊢ □⟦p, n⟧.
  Proof.
    red_tl. iIntros "#P". auto.
  Qed.

  Lemma pers_test2 n (p : Formula n) :
    □⟦p, n⟧ ⊢ ⟦(□p)%F, n⟧.
  Proof.
    red_tl. iIntros "#P". auto.
  Qed.

  Lemma test_infix n (p q r : Formula n) :
    (p ∗ q ∗ r)%F = (p ∗ (q ∗ r))%F.
  Proof. ss. Qed.

  Lemma test_infix2 (P Q R : iProp) :
    (P ∗ Q ∗ R)%I = (P ∗ (Q ∗ R))%I.
  Proof. ss. Qed.

  (* Lemma test_infix3 (P Q R : iProp) : *)
  (*   (P ∗ Q ∗ R)%I = (P ∗ (Q ∗ R))%I. *)
  (* Proof. ss.  *)

End TEST.


(* (* Section OWN. *) *)

(* (*   Class SRA := { car : Type }. *) *)

(* (* End OWN. *) *)

(* Module Atom. *)

(*   Section ATOMS. *)

(*     (* Context `{σ : list SRA}. *) *)

(*     Inductive t {form : Type} : Type := *)
(*     (* | own {M : SRA} {IN : In M σ} (m : @car M) *) *)
(*     (** Atom to express the invariant system. *) *)
(*     | owni (i : positive) (p : @Syntax.t _ (@Typ) (@t form) form) *)
(*     | syn_inv_auth_l (ps : list (prod positive (@Syntax.t _ (@Typ) (@t form) form))) *)
(*     | ownd (x : index) (D : gset positive) *)
(*     | owne (x : index) (E : coPset) *)
(*     | syn_wsat_auth (x : index) *)
(*     | syn_owne_auth (Es : coPsets) *)
(*     . *)

(*   End ATOMS. *)

(*   Section INTERP. *)

(*     (* Context `{σ : list SRA}. *) *)

(*     Local Notation _Formula := (@_formula (@t)). *)
(*     Local Notation Formula := (@formula (@t)). *)

(*     Context `{Σ : GRA.t}. *)
(*     (* Context `{SUB : *) *)
(*     (*       forall M, In M σ -> *) *)
(*     (*            { to_URA : SRA -> ucmra & *) *)
(*     (*                               ((GRA.inG (to_URA M) Σ) * ((@car M) -> (to_URA M)))%type }}. *) *)

(*     Context `{@GRA.inG (IInvSetRA Formula) Σ}. *)
(*     Context `{@GRA.inG (URA.pointwise index CoPset.t) Σ}. *)
(*     Context `{@GRA.inG (URA.pointwise index Gset.t) Σ}. *)

(*     (* Definition to_semantics n (a : @t σ (_Formula n)) : iProp := *) *)
(*     Definition to_semantics n (a : @t (_Formula n)) : iProp := *)
(*       match a with *)
(*       (* | @own _ _ M IN m => *) *)
(*       (*     @OwnM Σ (projT1 (SUB M IN) M) (fst (projT2 (SUB M IN))) ((snd (projT2 (SUB M IN)) m)) *) *)
(*       (** Atom to express the invariant system. *) *)
(*       | owni i p => @OwnI Σ Formula _ n i p *)
(*       | syn_inv_auth_l ps => @inv_auth Σ Formula _ n (list_to_map ps) *)
(*       | ownd x D => OwnD x D *)
(*       | owne x E => OwnE x E *)
(*       | syn_wsat_auth x => wsat_auth x *)
(*       | syn_owne_auth Es => OwnE_auth Es *)
(*       end. *)

(*   End INTERP. *)

(* End Atom. *)
