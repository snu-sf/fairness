From stdpp Require Import coPset gmap namespaces.
From sflib Require Import sflib.
From Fairness Require Import Axioms.
From Fairness Require Import PCM IProp IPM IndexedInvariants.
From Fairness Require Import ISim SimDefaultRA LiveObligations SimWeakest.
From Fairness Require Export LogicSyntaxHOAS.
From iris Require Import bi.big_op.
From iris Require base_logic.lib.invariants.
Require Import Program.

Local Notation index := nat.

(** Types of TL. *)

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
    | pgmapT : type -> type
    | nat_wfT : type
    | owfT : type
    | tidsetT : type
    .

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
      | nat_wfT => T nat_wf
      | owfT => T owf
      | tidsetT => TIdSet.t
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

(** Define TL. *)

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
    | aux (s : aAtom)
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
    | fair_tgt (im_tgt : @FairBeh.imap (nat + ident_tgt) nat_wf) (ths : TIdSet.t)
    (** Atoms to express liveness logic invariants. *)
    | obl_edges_sat
    | obl_arrows_auth (x : index)
    | obl_arrows_regions_black (l : list ((nat + ident_tgt) * nat * Ord.t * Qp * nat * (@Syntax.t _ (@Typ) (@t form) form)))
    | obl_arrow_done1 (x : nat)
    | obl_arrow_done2 (k : nat)
    | obl_arrow_pend (i : nat + ident_tgt) (k : nat) (c : Ord.t) (q : Qp)
    (** Atoms to express liveness logic definitions. *)
    | obl_lo (k i : nat)
    | obl_pc (k l a : nat)
    | obl_live (k : nat) (q : Qp)
    | obl_dead (k : nat)
    | obl_link (k0 k1 l : nat)
    | obl_duty {Id : Type} (p : Prism.t (nat + ident_tgt) Id) (i : Id) (ds : list (nat * nat * (@Syntax.t _ (@Typ) (@t form) form)))
    | obl_fc {Id : Type} (p : Prism.t (nat + ident_tgt) Id) (i : Id)
    | obl_promise {Id : Type} (p : Prism.t (nat + ident_tgt) Id) (i : Id) (k l : nat) (f : @Syntax.t _ (@Typ) (@t form) form)
    | obl_tc
    | obl_tpromise (k l : nat) (f : @Syntax.t _ (@Typ) (@t form) form)
    | obl_pcs (ps : list (nat * nat)) (m a : nat)
    | obl_ccs (k : nat) (ps : list (nat * nat)) (l : nat)
    .

  End ATOM.

End Atom.

Section TL_FORMULA.

  Context {AA : AuxAtom}.
  Context {STT : StateTypes}.

  Definition _Formula := (@_formula (@Atom.t AA STT)).
  Definition Formula := (@formula (@Atom.t AA STT)).

End TL_FORMULA.

Section TLRAS.

  Context {AA : AuxAtom}.

  Class TLRAs (STT : StateTypes) (Σ : GRA.t) :=
    {
      (* Invariant related default RAs *)
      _OWNESRA : @GRA.inG OwnEsRA Σ;
      _OWNDSRA : @GRA.inG OwnDsRA Σ;
      _IINVSETRA : @GRA.inG (IInvSetRA Formula) Σ;
      (* State related default RAs *)
      _THDRA: @GRA.inG ThreadRA Σ;
      _STATESRC: @GRA.inG (stateSrcRA st_src_type) Σ;
      _STATETGT: @GRA.inG (stateTgtRA st_tgt_type) Σ;
      _IDENTSRC: @GRA.inG (identSrcRA id_src_type) Σ;
      _IDENTTGT: @GRA.inG (identTgtRA id_tgt_type) Σ;
      (* Liveness logic related default RAs *)
      _OBLGRA: @GRA.inG ObligationRA.t Σ;
      _EDGERA: @GRA.inG EdgeRA Σ;
      _ARROWSHOTRA: @GRA.inG ArrowShotRA Σ;
      _ARROWRA: @GRA.inG (@ArrowRA id_tgt_type Formula) Σ;
    }.

End TLRAS.

Section EXPORT.

  Context {AA : AuxAtom}.
  Context {STT : StateTypes}.
  Context `{Σ : GRA.t}.
  Context {TLRAS : TLRAs STT Σ}.

  (* Invariant related default RAs *)
  #[export] Instance OWNESRA : @GRA.inG OwnEsRA Σ := _OWNESRA.
  #[export] Instance OWNDSRA : @GRA.inG OwnDsRA Σ:= _OWNDSRA.
  #[export] Instance IINVSETRA : @GRA.inG (IInvSetRA Formula) Σ:= _IINVSETRA.
  (* State related default RAs *)
  #[export] Instance THDRA: @GRA.inG ThreadRA Σ:= _THDRA.
  #[export] Instance STATESRC: @GRA.inG (stateSrcRA st_src_type) Σ:= _STATESRC.
  #[export] Instance STATETGT: @GRA.inG (stateTgtRA st_tgt_type) Σ:= _STATETGT.
  #[export] Instance IDENTSRC: @GRA.inG (identSrcRA id_src_type) Σ:= _IDENTSRC.
  #[export] Instance IDENTTGT: @GRA.inG (identTgtRA id_tgt_type) Σ:= _IDENTTGT.
  (* Liveness logic related default RAs *)
  #[export] Instance OBLGRA: @GRA.inG ObligationRA.t Σ:= _OBLGRA.
  #[export] Instance EDGERA: @GRA.inG EdgeRA Σ:= _EDGERA.
  #[export] Instance ARROWSHOTRA: @GRA.inG ArrowShotRA Σ:= _ARROWSHOTRA.
  #[export] Instance ARROWRA: @GRA.inG (@ArrowRA id_tgt_type Formula) Σ:= _ARROWRA.

End EXPORT.

Section ATOMINTERP.

  Context {AA : AuxAtom}.
  Context {STT : StateTypes}.

  Import Atom.

  Local Notation att := (@t AA STT).

  Context `{Σ : GRA.t}.
  Context `{AAI : @AAInterp Σ AA}.
  Context {TLRAS : @TLRAs AA STT Σ}.

  Definition Atom_to_semantics n (a : @t AA STT (_Formula n)) : iProp :=
    match a with
    (** Simple atoms. *)
    | aux s => aaintp s
    (** Atom to express the invariant system. *)
    | owni i p => @OwnI Σ Formula _ n i p
    | syn_inv_auth_l ps => @inv_auth Σ Formula _ n (list_to_map ps)
    | ownd x D => OwnD x D
    | owne x E => OwnE x E
    | syn_wsat_auth x => wsat_auth x
    | syn_owne_auth Es => OwnE_auth Es
    (** Atoms to express state invariants of wpsim. *)
    | ob_ths ths =>
        OwnM (Auth.black (Some ths: (NatMapRALarge.t unit)): ThreadRA)
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
    (** Atoms to express liveness logic definitions. *)
    | obl_lo k l => liveness_obligation k l
    | obl_pc k l a => progress_credit k l a
    | obl_live k q => live k q
    | obl_dead k => dead k
    | obl_link k0 k1 l => link k0 k1 l
    | obl_duty p i ds => duty _ p i ds
    | obl_fc p i => fairness_credit _ p i
    | obl_promise p i k l f => promise _ p i k l f
    | obl_tc => thread_credit _
    | obl_tpromise k l f => thread_promise _ k l f
    | obl_pcs ps m a => progress_credits ps m a
    | obl_ccs k ps l => collection_credits k ps l
    end.

End ATOMINTERP.

Section TL_INTERP.

  Context {AA : AuxAtom}.
  Context {STT : StateTypes}.
  Context `{Σ : GRA.t}.
  Context `{AAI : @AAInterp Σ AA}.
  Context {TLRAS : @TLRAs AA STT Σ}.

  Definition AtomSem := (@Atom_to_semantics AA STT Σ AAI TLRAS).
  Definition SynSem := (@formula_sem (@Atom.t AA STT) Σ (@AtomSem)).

  Global Instance SynIISet : @IInvSet Σ Formula :=
    {| prop := SynSem |}.

End TL_INTERP.

(** Notations and coercions. *)
Notation "'τ{' t ',' n '}'" := (@Typ (@_Formula _ _ n) t).
Notation "'τ{' t '}'" := (@Typ (@_Formula _ _ _) t).
Notation "'⟪' A ',' n '⟫'" := (@AtomSem _ _ _ _ _ n A).
Notation "'⟦' F ',' n '⟧'" := (@SynSem _ _ _ _ _ n F).

Section RED.

  Context {AA : AuxAtom}.
  Context {STT : StateTypes}.

  Context `{Σ : GRA.t}.
  Context `{AAI : @AAInterp Σ AA}.
  Context {TLRAS : @TLRAs AA STT Σ}.

  Lemma red_tl_atom_aux n (a : aAtom) :
    ⟦⟨Atom.aux a⟩%F, n⟧ = aaintp a.
  Proof. setoid_rewrite red_sem_atom. ss. Qed.

  Lemma red_tl_atom n a :
    ⟦⟨a⟩%F, n⟧ = ⟪a, n⟫.
  Proof. apply red_sem_atom. Qed.

  Lemma red_tl_lift_0 p :
    ⟦(⤉p)%F, 0⟧ = ⌜False⌝%I.
  Proof. apply red_sem_lift_0. Qed.

  Lemma red_tl_lift n p :
    ⟦(⤉p)%F, S n⟧ = ⟦p, n⟧ .
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
    ⟦(■ p)%F, n⟧ = (IProp.Plainly ⟦p, n⟧)%I.
  Proof. apply red_sem_plainly. Qed.

  Lemma red_tl_upd n (p : Formula n) :
    ⟦( |==> p)%F, n⟧ = ( |==> ⟦p, n⟧)%I.
  Proof. apply red_sem_upd. Qed.

  Lemma red_tl_sisim n
        {state_src state_tgt ident_src ident_tgt : Type}
        (tid : thread_id)
        (I0 : TIdSet.t -> (@FairBeh.imap ident_src owf) -> (@FairBeh.imap (nat + ident_tgt) nat_wf) -> state_src -> state_tgt -> Formula n)
        (I1 : TIdSet.t -> (@FairBeh.imap ident_src owf) -> (@FairBeh.imap (nat + ident_tgt) nat_wf) -> state_src -> state_tgt -> Formula n)
        {R_src R_tgt : Type}
        (Q : R_src -> R_tgt -> Formula n)
        (ps pt : bool)
        (itr_src : itree (threadE ident_src state_src) R_src)
        (itr_tgt : itree (threadE ident_tgt state_tgt) R_tgt)
        (ths : TIdSet.t)
        (ims : @FairBeh.imap ident_src owf)
        (imt : @FairBeh.imap (nat + ident_tgt) nat_wf)
        (sts : state_src)
        (stt : state_tgt)
    :
    ⟦Syntax.sisim tid I0 I1 Q ps pt itr_src itr_tgt ths ims imt sts stt, n⟧
    = (isim_simple tid (intpF:=SynSem n) I0 I1 Q ps pt itr_src itr_tgt ths ims imt sts stt)%I.
  Proof. apply red_sem_sisim. Qed.

  Lemma red_tl_striple_format n
        {state_src state_tgt ident_src ident_tgt : Type}
        (tid : thread_id)
        (I0 : TIdSet.t -> (@FairBeh.imap ident_src owf) -> (@FairBeh.imap (nat + ident_tgt) nat_wf) -> state_src -> state_tgt -> Formula n)
        (I1 : TIdSet.t -> (@FairBeh.imap ident_src owf) -> (@FairBeh.imap (nat + ident_tgt) nat_wf) -> state_src -> state_tgt -> Formula n)
        (I2 : TIdSet.t -> (@FairBeh.imap ident_src owf) -> (@FairBeh.imap (nat + ident_tgt) nat_wf) -> state_src -> state_tgt -> coPsets -> Formula n)
        (P : Formula n)
        {RV : Type}
        (Q : RV -> Formula n)
        (Es1 Es2 : coPsets)
        {R_src R_tgt : Type}
        (TERM : R_src -> R_tgt -> Formula n)
        (ps pt : bool)
        (itr_src : itree (threadE ident_src state_src) R_src)
        (code : itree (threadE ident_tgt state_tgt) RV)
        (ktr_tgt : ktree (threadE ident_tgt state_tgt) RV R_tgt)
    :
    ⟦(Syntax.striple_format tid I0 I1 I2 P Q Es1 Es2 TERM ps pt itr_src code ktr_tgt), n⟧
    =
      (triple_format (intpF:=SynSem n) tid
                     I0 I1 I2 P Q Es1 Es2 TERM
                     ps pt itr_src code ktr_tgt)%I.
  Proof. apply red_sem_striple_format. Qed.

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

Ltac red_tl_unary_once := (try rewrite ! @red_tl_atom_aux;
                           try rewrite ! @red_tl_atom;
                           try rewrite ! @red_tl_lift;
                           try rewrite ! @red_tl_pure;
                           try rewrite ! @red_tl_univ;
                           try rewrite ! @red_tl_ex;
                           try rewrite ! @red_tl_empty;
                           try rewrite ! @red_tl_persistently;
                           try rewrite ! @red_tl_plainly;
                           try rewrite ! @red_tl_upd;
                           try rewrite ! @red_tl_affinely;
                           try rewrite ! @red_tl_intuitionistically;
                           try rewrite ! @red_tl_sisim;
                           try rewrite ! @red_tl_striple_format
                          ).

Ltac red_tl_binary := repeat red_tl_binary_once.
Ltac red_tl_unary := repeat red_tl_unary_once.
Ltac red_tl := repeat (red_tl_binary; red_tl_unary).


Ltac red_tl_binary_once_every := (try rewrite ! @red_tl_sepconj in *;
                                  try rewrite ! @red_tl_and in *;
                                  try rewrite ! @red_tl_or in *;
                                  try rewrite ! @red_tl_impl in *;
                                  try rewrite ! @red_tl_wand in *
                                 ).

Ltac red_tl_unary_once_every := (try rewrite ! @red_tl_atom_aux in *;
                                 try rewrite ! @red_tl_atom in *;
                                 try rewrite ! @red_tl_lift in *;
                                 try rewrite ! @red_tl_pure in *;
                                 try rewrite ! @red_tl_univ in *;
                                 try rewrite ! @red_tl_ex in *;
                                 try rewrite ! @red_tl_empty in *;
                                 try rewrite ! @red_tl_persistently in *;
                                 try rewrite ! @red_tl_plainly in *;
                                 try rewrite ! @red_tl_upd in *;
                                 try rewrite ! @red_tl_affinely in *;
                                 try rewrite ! @red_tl_intuitionistically in *;
                                 try rewrite ! @red_tl_sisim in *;
                                 try rewrite ! @red_tl_striple_format
                                ).

Ltac red_tl_binary_every := repeat red_tl_binary_once.
Ltac red_tl_unary_every := repeat red_tl_unary_once.
Ltac red_tl_every := repeat (red_tl_binary_every; red_tl_unary_every).


Section WSATS.

  Context {AA : AuxAtom}.
  Context {STT : StateTypes}.

  Context `{Σ : GRA.t}.
  Context `{AAI : @AAInterp Σ AA}.
  Context {TLRAS : @TLRAs AA STT Σ}.


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
    (∃ (I : τ{pgmapT Φ, S n}), ⤉(⟨syn_inv_auth n I⟩ ∗ (syn_inv_satall n I)))%F.

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
    | S m' => (⤉(@lifts n p m'))%F
    end.

  (* Definition syn_wsats n : Formula (S n) := *)
  (*   syn_big_sepL1 n (baseT nat) (seq 0 n) (fun m => lifts (syn_wsat m) (n - (S m))). *)

  Fixpoint lifts_seps (p : forall n, Formula (S n)) n : Formula n :=
    match n with
    | O => emp%F
    | S m => ((⤉(lifts_seps p m)) ∗ (p m))%F
    end.

  Lemma unfold_lifts_seps p n :
    lifts_seps p (S n) = (⤉(lifts_seps p n) ∗ (p n))%F.
  Proof. ss. Qed.

  Definition syn_wsats n : Formula n := lifts_seps syn_wsat n.

  Lemma unfold_syn_wsats n :
    syn_wsats (S n) = (⤉(syn_wsats n) ∗ (syn_wsat n))%F.
  Proof. apply unfold_lifts_seps. Qed.

  Lemma red_syn_wsats1 n :
    ⟦syn_wsats n, n⟧ ⊢ wsats n.
  Proof.
    induction n; ss. rewrite unfold_syn_wsats. red_tl. iIntros "[A B]".
    iApply fold_wsats. rewrite red_syn_wsat. iFrame. iApply IHn. iFrame.
  Qed.

  Lemma red_syn_wsats2 n :
    wsats n ⊢ ⟦syn_wsats n, n⟧.
  Proof.
    induction n; ss. rewrite unfold_syn_wsats. red_tl. iIntros "A".
    iPoseProof (unfold_wsats with "A") as "[A B]". rewrite red_syn_wsat. iFrame.
    iApply IHn. iFrame.
  Qed.

  Lemma red_syn_wsats n :
    ⟦syn_wsats n, n⟧ ⊣⊢ wsats n.
  Proof.
    iSplit. iApply red_syn_wsats1. iApply red_syn_wsats2.
  Qed.

  (** Definitions for OwnEs. *)

  Definition syn_owne_satall_fun x : index -> coPset -> (Formula x) :=
    fun n E => ⟨owne n E⟩%F.

  Definition syn_owne_satall x (Es : coPsets) : Formula x :=
    ([∗ x , coPset map] k ↦ E ∈ Es, syn_owne_satall_fun x k E)%F.

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

  Lemma red_syn_fupd1 n A Es1 Es2 p :
    ⟦syn_fupd n A Es1 Es2 p, n⟧ ⊢ FUpd n ⟦A, n⟧ Es1 Es2 ⟦p, n⟧.
  Proof.
    unfold syn_fupd. red_tl. rewrite ! red_syn_ownes.
    Local Transparent FUpd.
    iIntros "F [A [W E]]". iPoseProof (red_syn_wsats with "W") as "W".
    iMod ("F" with "[A E W]") as "(A & W & E & P)". iFrame.
    iPoseProof (red_syn_wsats with "W") as "W".
    iModIntro. iFrame.
    Local Opaque FUpd.
  Qed.

  Lemma red_syn_fupd2 n A Es1 Es2 p :
    FUpd n ⟦A, n⟧ Es1 Es2 ⟦p, n⟧ ⊢ ⟦syn_fupd n A Es1 Es2 p, n⟧.
  Proof.
    unfold syn_fupd. red_tl. rewrite ! red_syn_ownes.
    Local Transparent FUpd.
    iIntros "F [A [W E]]". iPoseProof (red_syn_wsats with "W") as "W".
    iMod ("F" with "[A E W]") as "(A & W & E & P)". iFrame.
    iPoseProof (red_syn_wsats with "W") as "W".
    iModIntro. iFrame.
    Local Opaque FUpd.
  Qed.

  Lemma red_syn_fupd n A Es1 Es2 p :
    ⟦syn_fupd n A Es1 Es2 p, n⟧ ⊣⊢ FUpd n ⟦A, n⟧ Es1 Es2 ⟦p, n⟧.
  Proof.
    iSplit. iApply red_syn_fupd1. iApply red_syn_fupd2.
  Qed.

End WSATS.
Global Opaque syn_wsat syn_wsats syn_ownes syn_inv syn_fupd.

Section OBLIG.

  Context {AA : AuxAtom}.
  Context {STT : StateTypes}.

  Context `{Σ : GRA.t}.
  Context `{AAI : @AAInterp Σ AA}.
  Context {TLRAS : @TLRAs AA STT Σ}.

  Local Notation _dataT := ((nat + id_tgt_type) * nat * Ord.t * Qp * nat)%type.
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

  (* Check (⇣ Ord.t)%ftype. *)
  (* Check (⇣ (nat + nat)%type)%ftype. *)
  (* Fail Check (⇣ (sum_tid id_tgt_type))%ftype. *)

  Definition syn_arrows_sat n : Formula (S n) :=
    (∃ (l : τ{ listT ((⇣(nat + id_tgt_type)) * (⇣nat) * (⇣Ord.t) * (⇣Qp) * (⇣nat) * Φ)%ftype, S n }),
        ⤉(⟨obl_arrows_regions_black l⟩ ∗ syn_arrows_sat_list n l))%F.

  Lemma red_syn_arrows_sat n :
    ⟦syn_arrows_sat n, S n⟧ = ObligationRA.arrows_sat n.
  Proof.
    unfold syn_arrows_sat. red_tl. unfold ObligationRA.arrows_sat, Regions.sat.
    f_equal. extensionality l. red_tl. ss.
    rewrite red_syn_arrows_sat_list. f_equal.
  Qed.

  Definition syn_arrows_sats n : Formula n := lifts_seps syn_arrows_sat n.

  Lemma unfold_syn_arrows_sats n :
    syn_arrows_sats (S n) = (⤉(syn_arrows_sats n) ∗ (syn_arrows_sat n))%F.
  Proof. apply unfold_lifts_seps. Qed.

  Lemma red_syn_arrows_sats1 n :
    ⟦syn_arrows_sats n, n⟧ ⊢ ObligationRA.arrows_sats n.
  Proof.
    induction n; ss. rewrite unfold_syn_arrows_sats. red_tl. iIntros "[A B]".
    iApply Regions.fold_nsats. rewrite red_syn_arrows_sat. iFrame. iApply IHn. iFrame.
  Qed.

  Lemma red_syn_arrows_sats2 n :
    ObligationRA.arrows_sats n ⊢ ⟦syn_arrows_sats n, n⟧.
  Proof.
    induction n; ss. rewrite unfold_syn_arrows_sats. red_tl. iIntros "A".
    iPoseProof (Regions.unfold_nsats with "A") as "[A B]". rewrite red_syn_arrows_sat. iFrame.
    iApply IHn. iFrame.
  Qed.

  Lemma red_syn_arrows_sats n :
    ⟦syn_arrows_sats n, n⟧ ⊣⊢ ObligationRA.arrows_sats n.
  Proof.
    iSplit. iApply red_syn_arrows_sats1. iApply red_syn_arrows_sats2.
  Qed.

  Definition syn_fairI n : Formula n := (⟨obl_edges_sat⟩ ∗ syn_arrows_sats n)%F.

  Lemma red_syn_fairI1 n :
    ⟦syn_fairI n, n⟧ ⊢ fairI n.
  Proof.
    unfold syn_fairI. red_tl. rewrite red_syn_arrows_sats. unfold fairI. ss.
  Qed.

  Lemma red_syn_fairI2 n :
    fairI n ⊢ ⟦syn_fairI n, n⟧.
  Proof.
    unfold syn_fairI. red_tl. unfold fairI. rewrite red_syn_arrows_sats. ss.
  Qed.

  Lemma red_syn_fairI n :
    ⟦syn_fairI n, n⟧ ⊣⊢ fairI n.
  Proof.
    iSplit. iApply red_syn_fairI1. iApply red_syn_fairI2.
  Qed.

End OBLIG.
Global Opaque syn_obl_arrow syn_arrows_sat_list syn_arrows_sat syn_arrows_sats.

Section SIMI.

  Context {AA : AuxAtom}.
  Context {STT : StateTypes}.

  Context `{Σ : GRA.t}.
  Context `{AAI : @AAInterp Σ AA}.
  Context {TLRAS : @TLRAs AA STT Σ}.

  Let srcE := threadE id_src_type st_src_type.
  Let tgtE := threadE id_tgt_type st_tgt_type.

  Import Atom.

  Definition syn_default_I n
    : TIdSet.t -> (@FairBeh.imap id_src_type owf) -> (@FairBeh.imap (nat + id_tgt_type) nat_wf) -> st_src_type -> st_tgt_type -> Formula n :=
    fun ths im_src im_tgt st_src st_tgt =>
      (⟨ob_ths ths⟩ ∗ ⟨ob_st_src st_src⟩ ∗ ⟨ob_st_tgt st_tgt⟩ ∗ ⟨fair_src im_src⟩ ∗ ⟨fair_tgt im_tgt ths⟩ ∗ ⟨obl_edges_sat⟩ ∗ syn_arrows_sats n ∗ ⟨obl_arrows_auth n⟩)%F.

  Lemma red_syn_default_I1 n ths ims imt sts stt :
    ⟦syn_default_I n ths ims imt sts stt, n⟧ ⊢ default_I n ths ims imt sts stt.
  Proof.
    unfold syn_default_I, default_I. red_tl. iIntros "[A [B [C [D [E [F [G H]]]]]]]". iFrame.
    iApply red_syn_arrows_sats. iFrame.
  Qed.

  Lemma red_syn_default_I2 n ths ims imt sts stt :
    default_I n ths ims imt sts stt ⊢ ⟦syn_default_I n ths ims imt sts stt, n⟧.
  Proof.
    unfold syn_default_I, default_I. red_tl. iIntros "[A [B [C [D [E [F [G H]]]]]]]". iFrame.
    iApply red_syn_arrows_sats. iFrame.
  Qed.

  Lemma red_syn_default_I n ths ims imt sts stt :
    ⟦syn_default_I n ths ims imt sts stt, n⟧ ⊣⊢ default_I n ths ims imt sts stt.
  Proof.
    iSplit. iApply red_syn_default_I1. iApply red_syn_default_I2.
  Qed.

  Definition syn_default_I_past tid n
    : TIdSet.t -> (@FairBeh.imap id_src_type owf) -> (@FairBeh.imap (nat + id_tgt_type) nat_wf) -> st_src_type -> st_tgt_type -> Formula n :=
    fun ths im_src im_tgt st_src st_tgt =>
      (∃ (im_tgt0 : τ{ ((nat + id_tgt_type)%type -> nat_wfT) }),
          (⌜fair_update im_tgt0 im_tgt (prism_fmap inlp (tids_fmap tid ths))⌝)
            ∗ (syn_default_I n ths im_src im_tgt0 st_src st_tgt))%F.

  Lemma red_syn_default_I_past1 tid n ths ims imt sts stt :
    ⟦syn_default_I_past tid n ths ims imt sts stt, n⟧ ⊢ default_I_past tid n ths ims imt sts stt.
  Proof.
    unfold syn_default_I_past, default_I_past. red_tl.
    iIntros "[% D]". red_tl. iDestruct "D" as "[% D]".
    iExists _. rewrite red_syn_default_I. iFrame. auto.
  Qed.

  Lemma red_syn_default_I_past2 tid n ths ims imt sts stt :
    default_I_past tid n ths ims imt sts stt ⊢ ⟦syn_default_I_past tid n ths ims imt sts stt, n⟧.
  Proof.
    unfold syn_default_I_past, default_I_past. red_tl.
    iIntros "[% [% D]]". iExists _. red_tl. iSplit. auto.
    iApply red_syn_default_I. iFrame.
  Qed.

  Lemma red_syn_default_I_past tid n ths ims imt sts stt :
    ⟦syn_default_I_past tid n ths ims imt sts stt, n⟧ ⊣⊢ default_I_past tid n ths ims imt sts stt.
  Proof.
    iSplit. iApply red_syn_default_I_past1. iApply red_syn_default_I_past2.
  Qed.

  Definition syn_wpsim n tid Es
    : forall {R_src R_tgt : Type}, (R_src -> R_tgt -> Formula n) -> bool -> bool -> itree srcE R_src -> itree tgtE R_tgt -> Formula n
    :=
    fun R_src R_tgt Q ps pt itr_src itr_tgt =>
      (∀ (ths : τ{ tidsetT })
         (im_src : τ{ id_src_type -> owfT })
         (im_tgt : τ{ ((nat + id_tgt_type)%type -> nat_wfT) })
         (st_src : τ{ st_src_type })
         (st_tgt : τ{ st_tgt_type }),
          (syn_default_I_past tid n ths im_src im_tgt st_src st_tgt ∗ (⟨syn_wsat_auth n⟩ ∗ syn_wsats n ∗ syn_ownes n Es))
            -∗
            (Syntax.sisim tid
                          (fun ths ims imt sts stt =>
                             ((syn_default_I n ths ims imt sts stt)
                                ∗ (⟨syn_wsat_auth n⟩ ∗ syn_wsats n ∗ syn_ownes n ∅))%F)
                          (fun ths ims imt sts stt =>
                             ((syn_default_I_past tid n ths ims imt sts stt)
                                ∗ (⟨syn_wsat_auth n⟩ ∗ syn_wsats n ∗ syn_ownes n ∅))%F)
                          Q ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
      )%F.

  Lemma red_syn_wpsim1
        n tid Es RS RT (Q : RS -> RT -> Formula n) ps pt itr_src itr_tgt :
    ⟦syn_wpsim n tid Es Q ps pt itr_src itr_tgt, n⟧
      ⊢
      wpsim n tid Es ibot7 ibot7 (fun rs rt => ⟦Q rs rt, n⟧) ps pt itr_src itr_tgt.
  Proof.
    iIntros "SWP". unfold syn_wpsim. red_tl.
    iIntros (? ? ? ? ?) "[D (W1 & W2 & W3)]".
    iSpecialize ("SWP" $! ths). red_tl.
    iSpecialize ("SWP" $! im_src). red_tl.
    iSpecialize ("SWP" $! im_tgt). red_tl.
    iSpecialize ("SWP" $! st_src). red_tl.
    iSpecialize ("SWP" $! st_tgt). red_tl.
    iPoseProof ("SWP" with "[D W1 W2 W3]") as "SWP".
    { ss. iFrame.
      rewrite red_syn_default_I_past. rewrite red_syn_wsats. rewrite red_syn_ownes.
      iFrame.
    }
    unfold isim_simple.
    iApply isim_mono_knowledge; cycle 2.
    iApply isim_mono; cycle 1.
    { iApply isim_equivI. 2: iFrame.
      iIntros. red_tl. ss. iSplit; iIntros "(A & B & C & D)"; iFrame.
      - rewrite red_syn_default_I. rewrite red_syn_wsats. rewrite red_syn_ownes. iFrame.
      - rewrite red_syn_default_I. rewrite red_syn_wsats. rewrite red_syn_ownes. iFrame.
    }
    { ss. iIntros (? ? ? ? ? ? ?). red_tl. iIntros "[(A & B & C & D) Q]". ss. iFrame.
      iModIntro. rewrite red_syn_default_I_past. rewrite red_syn_wsats. rewrite red_syn_ownes. iFrame.
    }
    { iIntros. inv H. }
    { iIntros. inv H. }
  Qed.

  Lemma red_syn_wpsim2
        n tid Es RS RT (Q : RS -> RT -> Formula n) ps pt itr_src itr_tgt :
    wpsim n tid Es ibot7 ibot7 (fun rs rt => ⟦Q rs rt, n⟧) ps pt itr_src itr_tgt
          ⊢
          ⟦syn_wpsim n tid Es Q ps pt itr_src itr_tgt, n⟧.
  Proof.
    iIntros "SWP". unfold syn_wpsim. red_tl.
    iIntros (ths). red_tl.
    iIntros (im_src). red_tl.
    iIntros (im_tgt). red_tl.
    iIntros (st_src). red_tl.
    iIntros (st_tgt). red_tl.
    simpl in *. unfold wpsim. iSpecialize ("SWP" $! ths im_src im_tgt st_src st_tgt).
    iIntros "[D (W1 & W2 & W3)]".
    iPoseProof ("SWP" with "[D W1 W2 W3]") as "SWP".
    { ss. iFrame.
      rewrite red_syn_default_I_past. rewrite red_syn_wsats. rewrite red_syn_ownes.
      iFrame.
    }
    unfold isim_simple.
    iPoseProof (isim_mono_knowledge with "SWP") as "SWP"; cycle 2.
    iPoseProof (isim_mono with "SWP") as "SWP"; cycle 1.
    { iPoseProof (isim_equivI with "SWP") as "SWP". 2: iFrame.
      iIntros. red_tl. ss. iSplit; iIntros "(A & B & C & D)"; iFrame.
      - rewrite red_syn_default_I. rewrite red_syn_wsats. rewrite red_syn_ownes. iFrame.
      - rewrite red_syn_default_I. rewrite red_syn_wsats. rewrite red_syn_ownes. iFrame.
    }
    { ss. iIntros (? ? ? ? ? ? ?). red_tl. iIntros "[(A & B & C & D) Q]". ss. iFrame.
      iModIntro.
      rewrite red_syn_default_I_past. rewrite red_syn_wsats. rewrite red_syn_ownes. iFrame.
    }
    { ss. iIntros (? ? ? ? ? ? ? ? ? ? ? ?). iIntros "(% & % & %H & _)". inv H. }
    { ss. iIntros (? ? ? ? ? ? ? ? ? ? ? ?). iIntros "(% & % & %H & _)". inv H. }
  Qed.

  Lemma red_syn_wpsim
        n tid Es RS RT (Q : RS -> RT -> Formula n) ps pt itr_src itr_tgt :
    ⟦syn_wpsim n tid Es Q ps pt itr_src itr_tgt, n⟧
      ⊣⊢
      wpsim n tid Es ibot7 ibot7 (fun rs rt => ⟦Q rs rt, n⟧) ps pt itr_src itr_tgt.
  Proof.
    iSplit. iApply red_syn_wpsim1. iApply red_syn_wpsim2.
  Qed.

  (* State interp with lens. *)
  Definition syn_view_interp n {S V} (l : Lens.t S V) (SI : S -> Formula n) (VI : V -> Formula n) : Prop :=
    forall s, ⟦SI s , n⟧ ⊢ ( ⟦VI (Lens.view l s), n⟧ ∗ ∀ x, ⟦VI x, n⟧ -∗ ⟦SI (Lens.set l x s), n⟧ ).

  Definition syn_src_interp_as n {V} (l: Lens.t st_src_type V) (VI: V -> Formula n) : Formula (S n) :=
    (∃ (SI : τ{(st_src_type -> Φ)%ftype, S n}) (p : τ{Φ, S n}),
        (⌜⟦p, n⟧ = (∃ st, St_src st ∗ ⟦(SI st), n⟧)%I⌝)
          ∗ (⤉(syn_inv n N_state_src p)) ∗ ⌜syn_view_interp n l SI VI⌝)%F.

  Lemma red_syn_src_interp_as n {V} (l: Lens.t st_src_type V) (VI: V -> Formula n) :
    ⟦syn_src_interp_as n l VI, S n⟧ = (src_interp_as l VI).
  Proof.
    unfold syn_src_interp_as. unfold src_interp_as.
    red_tl. ss. f_equal. extensionalities SI.
    red_tl. ss. f_equal. extensionalities p.
    red_tl. ss. repeat f_equal. unfold syn_view_interp.
    apply propositional_extensionality. split; i.
    - econs. auto.
    - inv H. auto.
  Qed.

  Definition syn_tgt_interp_as n {V} (l: Lens.t st_tgt_type V) (VI: V -> Formula n) : Formula (S n) :=
    (∃ (SI : τ{(st_tgt_type -> Φ)%ftype, S n}) (p : τ{Φ, S n}),
        (⌜⟦p, n⟧ = (∃ st, St_tgt st ∗ ⟦(SI st), n⟧)%I⌝)
          ∗ (⤉(syn_inv n N_state_tgt p)) ∗ ⌜syn_view_interp n l SI VI⌝)%F.

  Lemma red_syn_tgt_interp_as n {V} (l: Lens.t st_tgt_type V) (VI: V -> Formula n) :
    ⟦syn_tgt_interp_as n l VI, S n⟧ = (tgt_interp_as l VI).
  Proof.
    unfold syn_tgt_interp_as. unfold tgt_interp_as.
    red_tl. ss. f_equal. extensionalities SI.
    red_tl. ss. f_equal. extensionalities p.
    red_tl. ss. repeat f_equal. unfold syn_view_interp.
    apply propositional_extensionality. split; i.
    - econs. auto.
    - inv H. auto.
  Qed.

End SIMI.
Global Opaque
       syn_default_I syn_default_I_past syn_wpsim
       syn_src_interp_as syn_tgt_interp_as.

Section TRIPLE.

  Context {AA : AuxAtom}.
  Context {STT : StateTypes}.

  Context `{Σ : GRA.t}.
  Context `{AAI : @AAInterp Σ AA}.
  Context {TLRAS : @TLRAs AA STT Σ}.

  Let srcE := threadE id_src_type st_src_type.
  Let tgtE := threadE id_tgt_type st_tgt_type.

  Import Atom.

  Definition syn_triple_gen n tid (P : Formula n) {RV} (Q : RV -> Formula n) (Es1 Es2 : coPsets)
    : forall {R_src R_tgt : Type} (TERM : R_src -> R_tgt -> Formula n), bool -> bool -> itree srcE R_src -> itree tgtE RV -> ktree tgtE RV R_tgt -> Formula n
    :=
    fun R_src R_tgt TERM ps pt itr_src code ktr_tgt =>
      (
        (* ∀ (ths : τ{ tidsetT }) *)
        (*  (im_src : τ{ id_src_type -> owfT }) *)
        (*  (im_tgt : τ{ ((nat + id_tgt_type)%type -> nat_wfT) }) *)
        (*  (st_src : τ{ st_src_type }) *)
        (*  (st_tgt : τ{ st_tgt_type }), *)
          let I0 := (fun ths ims imt sts stt => ((syn_default_I n ths ims imt sts stt) ∗ (⟨syn_wsat_auth n⟩ ∗ syn_wsats n ∗ syn_ownes n ∅))%F)
          in
          let I1 := (fun ths ims imt sts stt => ((syn_default_I_past tid n ths ims imt sts stt) ∗ (⟨syn_wsat_auth n⟩ ∗ syn_wsats n ∗ syn_ownes n ∅))%F)
          in
          let I2 := (fun ths im_src im_tgt st_src st_tgt Es => (syn_default_I_past tid n ths im_src im_tgt st_src st_tgt ∗ (⟨syn_wsat_auth n⟩ ∗ syn_wsats n ∗ syn_ownes n Es)))
          in
          Syntax.striple_format tid I0 I1 I2 P Q Es1 Es2 TERM ps pt itr_src code ktr_tgt)%F.

  (* Let big_rel := *)
  (*       ∀ R_src R_tgt : Type, *)
  (*         (R_src → R_tgt *)
  (*          → TIdSet.t *)
  (*          → FairBeh.imap id_src_type owf *)
  (*          → FairBeh.imap (sum_tid id_tgt_type) nat_wf *)
  (*          → st_src_type → st_tgt_type → iProp) *)
  (*         → bool *)
  (*         → bool *)
  (*         → itree (threadE id_src_type st_src_type) R_src *)
  (*         → itree (threadE id_tgt_type st_tgt_type) R_tgt *)
  (*         → TIdSet.t *)
  (*         → FairBeh.imap id_src_type owf *)
  (*         → FairBeh.imap (sum_tid id_tgt_type) nat_wf *)
  (*         → st_src_type → st_tgt_type → iProp. *)

  (* Let small_rel := *)
  (*       ∀ R_src R_tgt : Type, *)
  (*         (R_src → R_tgt → iProp) *)
  (*         → bool *)
  (*         → bool *)
  (*         → itree (threadE id_src_type st_src_type) R_src *)
  (*         → itree (threadE id_tgt_type st_tgt_type) R_tgt → iProp. *)

  (* Let lift_rel tid x *)
  (*     (rr: small_rel) *)
  (*   : *)
  (*   big_rel *)
  (*     := *)
  (*       fun R_src R_tgt QQ ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt => *)
  (*         (∃ (Q: R_src -> R_tgt -> iProp) *)
  (*            (EQ: QQ = (fun r_src r_tgt ths im_src im_tgt st_src st_tgt => *)
  (*                         (default_I_past tid x ths im_src im_tgt st_src st_tgt ∗ (wsat_auth x ∗ wsats x ∗ OwnEs ∅)) ∗ Q r_src r_tgt)), *)
  (*             rr R_src R_tgt Q ps pt itr_src itr_tgt ∗ *)
  (*                (default_I_past tid x ths im_src im_tgt st_src st_tgt ∗ (wsat_auth x ∗ wsats x ∗ OwnEs ∅)))%I. *)

  Lemma red_syn_triple_gen1
        n tid P RV (Q : RV -> Formula n) Es1 Es2
        RS RT (TERM : RS -> RT -> Formula n) ps pt itr_src code (ktr_tgt : ktree tgtE RV RT)
    :
    ⟦syn_triple_gen n tid P Q Es1 Es2 TERM ps pt itr_src code ktr_tgt, n⟧
      ⊢
      (∀ rr gr,
          (⟦P, n⟧)
            -∗
            (∀ (rv : RV),
                (⟦Q rv, n⟧)
                  -∗
                  (wpsim n tid Es2 rr gr (fun rs rt => ⟦TERM rs rt, n⟧) ps pt itr_src (ktr_tgt rv)))
            -∗
            (wpsim n tid Es1 rr gr (fun rs rt => ⟦TERM rs rt, n⟧) ps pt itr_src (code >>= ktr_tgt))
      )%I.
  Proof.
    iIntros "ST % %". iEval (unfold syn_triple_gen; red_tl; simpl) in "ST".
    iEval (unfold triple_format) in "ST".
    iSpecialize ("ST" $! rr gr).
    (* iSpecialize ("ST" $! (lift_rel tid n rr) (lift_rel tid n gr)). *)
    iIntros "PRE POST". iSpecialize ("ST" with "PRE").
    iPoseProof ("ST" with "[POST]") as "ST".
    - iIntros "% Q" (? ? ? ? ?) "WP". iEval (red_tl; simpl) in "WP".
      iSpecialize ("POST" $! rv with "Q"). iEval (unfold wpsim) in "POST".
      iSpecialize ("POST" $! ths im_src im_tgt st_src st_tgt).
      iPoseProof ("POST" with "[WP]") as "SIM".
      { iDestruct "WP" as "(A & B & C & D)".
        iEval (rewrite red_syn_default_I_past) in "A".
        iEval (rewrite red_syn_wsats) in "C". iEval (rewrite red_syn_ownes) in "D".
        iSplitL "A". iFrame. iSplitL "B". iFrame. iSplitL "C"; iFrame.
      }
      iApply isim_mono_knowledge; cycle 2.
      iApply isim_mono; cycle 1.
      { iApply isim_equivI. 2: iFrame.
        iIntros. red_tl. ss. iSplit; iIntros "(A & B & C & D)"; iFrame.
        - rewrite red_syn_default_I. rewrite red_syn_wsats. rewrite red_syn_ownes. iFrame.
        - rewrite red_syn_default_I. rewrite red_syn_wsats. rewrite red_syn_ownes. iFrame.
      }
      { ss. iIntros (? ? ? ? ? ? ?). red_tl. iIntros "[(A & B & C & D) Q]". ss. iFrame.
        iModIntro. rewrite red_syn_default_I_past. rewrite red_syn_wsats. rewrite red_syn_ownes.
        iFrame.
      }
      { ss. iIntros (? ? ? ? ? ? ? ? ? ? ? ?) "(% & %EQ & A & B & C & D & E)".
        iModIntro. iExists Q1.

        TODO

        iFrame. }
      { unfold lift_rel. iIntros. iModIntro. iFrame. }
    - iIntros (? ? ? ? ?) "WP".
      iSpecialize ("ST" $! ths im_src im_tgt st_src st_tgt).
      iPoseProof ("ST" with "[WP]") as "SIM".
      { iDestruct "WP" as "(A & B & C & D)". red_tl. ss.
        rewrite red_syn_default_I_past. rewrite red_syn_wsats. rewrite red_syn_ownes.
        iFrame.
      }
      iApply isim_mono_knowledge; cycle 2.
      iApply isim_mono; cycle 1.
      { iApply isim_equivI. 2: iFrame.
        iIntros. red_tl. ss. iSplit; iIntros "(A & B & C & D)"; iFrame.
        - rewrite red_syn_default_I. rewrite red_syn_wsats. rewrite red_syn_ownes. iFrame.
        - rewrite red_syn_default_I. rewrite red_syn_wsats. rewrite red_syn_ownes. iFrame.
      }
      { ss. iIntros (? ? ? ? ? ? ?). red_tl. iIntros "[(A & B & C & D) Q]". ss. iFrame.
        iModIntro. rewrite red_syn_default_I_past. rewrite red_syn_wsats. rewrite red_syn_ownes.
        iFrame.
      }
      { unfold lift_rel. iIntros. iModIntro. iFrame. }
      { unfold lift_rel. iIntros. iModIntro. iFrame. }
  Qed.

  Let unlift_rel tid x
      (r: big_rel)
    :
    small_rel
      :=
        fun R_src R_tgt Q ps pt itr_src itr_tgt =>
          (∀ ths im_src im_tgt st_src st_tgt,
              (default_I_past tid x ths im_src im_tgt st_src st_tgt ∗ (wsat_auth x ∗ wsats x ∗ OwnEs ∅))
                -∗
                (@r R_src R_tgt (fun r_src r_tgt ths im_src im_tgt st_src st_tgt => (default_I_past tid x ths im_src im_tgt st_src st_tgt ∗ (wsat_auth x ∗ wsats x ∗ OwnEs ∅)) ∗ Q r_src r_tgt) ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt))%I.

  Lemma red_syn_triple_gen2
        n tid P RV (Q : RV -> Formula n) Es1 Es2
        RS RT (TERM : RS -> RT -> Formula n) ps pt itr_src code (ktr_tgt : ktree tgtE RV RT)
    :
    (∀ rr gr,
        (⟦P, n⟧)
          -∗
          (∀ (rv : RV),
              (⟦Q rv, n⟧)
                -∗
                (wpsim n tid Es2 rr gr (fun rs rt => ⟦TERM rs rt, n⟧) ps pt itr_src (ktr_tgt rv)))
          -∗
          (wpsim n tid Es1 rr gr (fun rs rt => ⟦TERM rs rt, n⟧) ps pt itr_src (code >>= ktr_tgt))
    )%I
     ⊢
     ⟦syn_triple_gen n tid P Q Es1 Es2 TERM ps pt itr_src code ktr_tgt, n⟧.
  Proof.
    iIntros "ST". iEval (unfold syn_triple_gen; red_tl; simpl).
    iEval (unfold triple_format). iIntros (? ?) "PRE POST". iIntros (? ? ? ? ?).
    iSpecialize ("ST" $! (unlift_rel tid n rr) (unlift_rel tid n gr) with "PRE").
    iPoseProof ("ST" with "[POST]") as "ST".
    - iIntros "% Q" (? ? ? ? ?) "WP".
      iSpecialize ("POST" $! rv with "Q").
      iSpecialize ("POST" $! ths0 im_src0 im_tgt0 st_src0 st_tgt0).
      iPoseProof ("POST" with "[WP]") as "SIM".
      { iDestruct "WP" as "(A & B & C & D)". iEval red_tl.
        rewrite red_syn_default_I_past. rewrite red_syn_wsats. rewrite red_syn_ownes. iFrame.
      }
      iApply isim_mono_knowledge; cycle 2.
      iApply isim_mono; cycle 1.
      { iApply isim_equivI. 2: iFrame.
        iIntros. red_tl. ss. iSplit; iIntros "(A & B & C & D)"; iFrame.
        - rewrite red_syn_default_I. rewrite red_syn_wsats. rewrite red_syn_ownes. iFrame.
        - rewrite red_syn_default_I. rewrite red_syn_wsats. rewrite red_syn_ownes. iFrame.
      }
      { ss. iIntros (? ? ? ? ? ? ?). red_tl. iIntros "[(A & B & C & D) Q]". ss. iFrame.
        iModIntro. rewrite red_syn_default_I_past. rewrite red_syn_wsats. rewrite red_syn_ownes.
        iFrame.
      }
      { unfold unlift_rel. iIntros. iModIntro. iExists  iFrame. }
      { unfold lift_rel. iIntros. iModIntro. iFrame. }
    - iIntros (? ? ? ? ?) "WP".
      iSpecialize ("ST" $! ths im_src im_tgt st_src st_tgt).
      iPoseProof ("ST" with "[WP]") as "SIM".
      { iDestruct "WP" as "(A & B & C & D)". red_tl. ss.
        rewrite red_syn_default_I_past. rewrite red_syn_wsats. rewrite red_syn_ownes.
        iFrame.
      }
      iApply isim_mono_knowledge; cycle 2.
      iApply isim_mono; cycle 1.
      { iApply isim_equivI. 2: iFrame.
        iIntros. red_tl. ss. iSplit; iIntros "(A & B & C & D)"; iFrame.
        - rewrite red_syn_default_I. rewrite red_syn_wsats. rewrite red_syn_ownes. iFrame.
        - rewrite red_syn_default_I. rewrite red_syn_wsats. rewrite red_syn_ownes. iFrame.
      }
      { ss. iIntros (? ? ? ? ? ? ?). red_tl. iIntros "[(A & B & C & D) Q]". ss. iFrame.
        iModIntro. rewrite red_syn_default_I_past. rewrite red_syn_wsats. rewrite red_syn_ownes.
        iFrame.
      }
      { unfold lift_rel. iIntros. iModIntro. iFrame. }
      { unfold lift_rel. iIntros. iModIntro. iFrame. }
  Qed.
  
      

    






End TRIPLE.

(** Notations. *)

Notation "'=|' x '|=(' A ')={' Es1 ',' Es2 '}=>' P" := (syn_fupd x A Es1 Es2 P) (at level 90) : formula_scope.
Notation "'=|' x '|={' Es1 ',' Es2 '}=>' P" := (=|x|=( ⌜True⌝%I )={ Es1, Es2}=> P)%F (at level 90) : formula_scope.
Notation "P =| x |=( A )={ Es1 , Es2 }=∗ Q" := (P -∗ =|x|=(A)={Es1,Es2}=> Q)%F (at level 90) : formula_scope.
Notation "P =| x |={ Es1 , Es2 }=∗ Q" := (P -∗ =|x|={Es1,Es2}=> Q)%F (at level 90) : formula_scope.

Notation "'=|' x '|=(' A ')={' Es '}=>' P" := (syn_fupd x A Es Es P) (at level 90) : formula_scope.
Notation "'=|' x '|={' Es '}=>' P" := (=|x|=( ⌜True⌝%I )={ Es }=> P)%F (at level 90) : formula_scope.
Notation "P =| x |=( A )={ Es }=∗ Q" := (P -∗ =|x|=(A)={Es}=> Q)%F (at level 90) : formula_scope.
Notation "P =| x |={ Es }=∗ Q" := (P -∗ =|x|={Es}=> Q)%F (at level 90) : formula_scope.

Notation "'◆' [ k , l ]" :=
  (⟨Atom.obl_lo k l⟩)%F (at level 50, k, l at level 1, format "◆ [ k ,  l ]") : formula_scope.
Notation "'◇' [ k ]( l , a )" :=
  (⟨Atom.obl_pc k l a⟩)%F (at level 50, k, l, a at level 1, format "◇ [ k ]( l ,  a )") : formula_scope.
Notation "'live[' k ']' q " :=
  (⟨Atom.obl_live k q⟩)%F (at level 50, k, q at level 1, format "live[ k ] q") : formula_scope.
Notation "'dead[' k ']'" :=
  (⟨Atom.obl_dead k⟩)%F (at level 50, k at level 1, format "dead[ k ]") : formula_scope.
Notation "s '-(' l ')-' '◇' t" :=
  (⟨Atom.obl_link s t l⟩)%F (at level 50, l, t at level 1, format "s  -( l )- ◇  t") : formula_scope.
Notation "'Duty' ( p ◬ i ) ds" :=
  (⟨Atom.obl_duty p i ds⟩)%F (at level 50, p, i, ds at level 1, format "Duty ( p  ◬  i )  ds") : formula_scope.
Notation "'Duty' ( tid ) ds" :=
  (⟨Atom.obl_duty inlp tid ds⟩)%F (at level 50, tid, ds at level 1, format "Duty ( tid )  ds") : formula_scope.
Notation "'€' ( p ◬ i )" :=
  (⟨Atom.obl_fc p i⟩)%F (format "€ ( p  ◬  i )") : formula_scope.
Notation "'-(' p ◬ i ')-[' k '](' l ')-' '◇' f" :=
  (⟨Atom.obl_promise p i k l f⟩)%F (at level 50, k, l, p, i at level 1, format "-( p  ◬  i )-[ k ]( l )- ◇  f") : formula_scope.
Notation "'€'" :=
  (⟨Atom.obl_tc⟩)%F : formula_scope.
Notation "'-[' k '](' l ')-' '◇' f" :=
  (⟨Atom.obl_tpromise k l f⟩)%F (at level 50, k, l at level 1, format "-[ k ]( l )- ◇  f") : formula_scope.
Notation "'◇' { ps }( m , a )" :=
  (⟨Atom.obl_pcs ps m a⟩)%F (at level 50, ps, m, a at level 1, format "◇ { ps }( m ,  a )") : formula_scope.
Notation "⦃ '◆' [ k ] & '◇' { ps }( l )⦄" :=
  (⟨Atom.obl_ccs k ps l⟩)%F (at level 50, k, ps, l at level 1, format "⦃ ◆ [ k ]  &  ◇ { ps }( l )⦄") : formula_scope.



Section TEST.

  Context {AA : AuxAtom}.
  Context {STT : StateTypes}.
  Local Notation state_src := (@st_src_type STT).
  Local Notation state_tgt := (@st_tgt_type STT).
  Local Notation ident_src := (@id_src_type STT).
  Local Notation ident_tgt := (@id_tgt_type STT).

  Context `{Σ : GRA.t}.
  Context `{AAI : @AAInterp Σ AA}.
  Context {TLRAS : @TLRAs AA STT Σ}.

  Definition test : Formula 3 :=
    ⟨Atom.owni xH (∃ (p : τ{formulaT, 3}), ⌜p = emp⌝)⟩%F.

  Definition test1 : Formula 3 :=
    ⟨Atom.owni xH (∃ (p : τ{baseT nat, 3}), ⌜p = 2⌝)⟩%F.
  Definition test1' : Formula 3 :=
    ⟨Atom.owni xH (∃ (p : τ{nat, 3}), ⌜p = 2⌝)⟩%F.
  Goal test1 = test1'. Proof. ss. Qed.

  Definition test2 : Formula 3 :=
    ⟨Atom.owni xH (∃ (p : τ{formulaT, 3}), ⤉p)⟩%F.
  Fail Definition test3 : Formula 3 :=
    ⟨Atom.owni xH (∃ (p : τ{formulaT, 3}), p)⟩%F.

  Lemma testp n :
    ⟦(⟨Atom.owni xH ⟨(Atom.owni xH emp)⟩⟩ ∗ (∃ (p : τ{formulaT, S n}), ⤉(p -∗ ⌜p = emp⌝)))%F, S n⟧
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
(*     (*            { to_URA : SRA -> URA.t & *) *)
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
