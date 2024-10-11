From iris.algebra Require Import cmra excl_auth auth.
From stdpp Require Export coPset gmap namespaces.
From sflib Require Import sflib.
From Fairness Require Import Axioms.
From Fairness Require Import PCM IPM IndexedInvariants IPropAux.
From Fairness Require Export ISim SimDefaultRA LiveObligations SimWeakest.
From Fairness Require Export LogicSyntaxHOAS.
From iris Require Import bi.big_op.
From Fairness Require Import DisableSsreflect.
Require Import Program.

Local Notation index := nat.

(** Types of TL. *)
Section TYPES.

  Section TYPE.

    Inductive type : Type :=
    | baseT (t : Type) : type
    | sPropT : type
    | funT : type -> type -> type
    | prodT : type -> type -> type
    | sumT : type -> type -> type
    | listT : type -> type
    | pgmapT : type -> type
    | nat_wfT : type
    | owfT : type
    | tidsetT : type
    | metaT : type
    | codeT (idT stT R : Type) : type
    .

  End TYPE.

  Section INTERP_TYPE.

    Fixpoint type_interp (ty : type) (form : Type) : Type :=
      match ty with
      | baseT b => b
      | sPropT => form
      | funT ty1 ty2 => (type_interp ty1 form -> type_interp ty2 form)
      | prodT ty1 ty2 => prod (type_interp ty1 form) (type_interp ty2 form)
      | sumT ty1 ty2 => sum (type_interp ty1 form) (type_interp ty2 form)
      | listT ty1 => list (type_interp ty1 form)
      | pgmapT ty1 => gmap positive (type_interp ty1 form)
      | nat_wfT => T nat_wf
      | owfT => T owf
      | tidsetT => TIdSet.t
      | metaT => Type
      | codeT idT stT R => itree (threadE idT stT) R
      end.

  End INTERP_TYPE.

  Global Instance TL_type : sType.t := {
      car := type;
      interp := type_interp;
    }.

End TYPES.

(** Notations and Coercions. *)
Coercion baseT : Sortclass >-> type.

Declare Scope sProp_type_scope.
Delimit Scope sProp_type_scope with stype.
Bind Scope sProp_type_scope with type.

Notation "⇣ T" := (baseT T) (at level 90) : sProp_type_scope.
Notation "'Φ'" := (sPropT) : sProp_type_scope.
Infix "->" := (funT) : sProp_type_scope.
Infix "*" := (prodT) : sProp_type_scope.
Infix "+" := (sumT) : sProp_type_scope.


Section BIGOP.

  Context `{α : sAtomI.t (τ := TL_type)}.
  Context {sub : @SRA.subG Γ Σ}.

  Import Syntax SyntaxI.

  (* Maybe we can make Syntax as an instance for big_opMs. *)
  Definition syn_big_sepM
             (n : index) {K} {H1 : EqDecision K} {H2 : Countable K}
             {A} (I : @gmap K H1 H2 (sType.interp A (sProp n)))
             (f : K -> (sType.interp A (sProp n)) -> sProp n)
    : sProp n :=
    fold_right (fun hd tl => sepconj (uncurry f hd) tl) empty (map_to_list I).

  Lemma red_syn_big_sepM n K {H1 : EqDecision K} {H2 : Countable K} A I f :
    interp n (@syn_big_sepM n K _ _ A I f) = ([∗ map] i ↦ a ∈ I, interp n (f i a))%I.
  Proof.
    ss. rewrite big_op.big_opM_unseal. unfold big_op.big_opM_def.
    unfold syn_big_sepM. simpl. remember (map_to_list I) as L.
    clear HeqL I. induction L.
    { ss. }
    ss. rewrite @red_sem_sepconj. rewrite IHL. f_equal.
    destruct a. ss.
  Qed.

  Definition syn_big_sepS
             (n : index) {K} {H1 : EqDecision K} {H2 : Countable K}
             (I : @gset K H1 H2)
             (f : K -> sProp n)
    : sProp n :=
    fold_right (fun hd tl => sepconj (f hd) tl) empty (elements I).

  Lemma red_syn_big_sepS n K {H1 : EqDecision K} {H2 : Countable K} I f :
    interp n (@syn_big_sepS n K _ _ I f) = ([∗ set] i ∈ I, interp n (f i))%I.
  Proof.
    ss. unfold big_opS. rewrite seal_eq. unfold big_op.big_opS_def.
    unfold syn_big_sepS. remember (elements I) as L.
    clear HeqL I. induction L.
    { ss. }
    ss. rewrite @red_sem_sepconj. rewrite IHL. f_equal.
  Qed.


  Definition syn_big_sepL1
             (n : index) {A} (I : sType.interp (listT A) (sProp n))
             (f : (sType.interp A (sProp n)) -> sProp n)
    : sProp n :=
    fold_right (fun hd tl => sepconj (f hd) tl) empty I.

  Lemma red_syn_big_sepL1 n A I f :
    interp n (@syn_big_sepL1 n A I f) = ([∗ list] a ∈ I, interp n (f a))%I.
  Proof.
    ss. induction I; ss.
    rewrite @red_sem_sepconj. rewrite IHI. f_equal.
  Qed.

  (* Additional definitions. *)

  Definition syn_sat_list
             n X (Ts : X -> Type) (x : X) (intp : Ts x -> sProp n) (l : list (Ts x))
    : sProp n :=
    foldr (fun t (p : sProp n) => (intp t ∗ p)%S) ⌜True⌝%S l.

  Lemma red_syn_sat_list n X Ts x intp l :
    interp n (syn_sat_list n X Ts x intp l) =
      @Regions.sat_list X Ts Σ x (fun (t : Ts x) => interp n (intp t)) l.
  Proof.
    induction l; ss. rewrite @red_sem_sepconj. rewrite IHl. f_equal.
  Qed.

End BIGOP.

(* Notations. *)
Notation "'[∗' n 'map]' k ↦ x ∈ m , P" :=
  (syn_big_sepM n m (fun k x => P))
    (at level 200, n at level 1, m at level 10, k, x at level 1, right associativity,
      format "[∗  n  map]  k  ↦  x  ∈  m ,  P") : sProp_scope.
Notation "'[∗' n , A 'map]' k ↦ x ∈ m , P" :=
  (syn_big_sepM n (A:=A) m (fun k x => P))
    (at level 200, n at level 1, m at level 10, k, x, A at level 1, right associativity,
      format "[∗  n  ,  A  map]  k  ↦  x  ∈  m ,  P") : sProp_scope.
Notation "'[∗' n 'set]' x ∈ X , P" :=
  (syn_big_sepS n X (fun x => P))
    (at level 200, n at level 1, X at level 10, x at level 1, right associativity,
      format "[∗  n  set]  x  ∈  X ,  P") : sProp_scope.
Notation "'[∗' n 'list]' x ∈ l , P" :=
  (syn_big_sepL1 n l (fun x => P))
    (at level 200, n at level 1, l at level 10, x at level 1, right associativity,
      format "[∗  n  list]  x  ∈  l ,  P") : sProp_scope.
Notation "'[∗' n , A 'list]' x ∈ l , P" :=
  (syn_big_sepL1 n (A:=A) l (fun x => P))
    (at level 200, n at level 1, l at level 10, x, A at level 1, right associativity,
      format "[∗  n ,  A  list]  x  ∈  l ,  P") : sProp_scope.

(** Define TL. *)
Module Atom.

  Section ATOM.

    Context {STT : StateTypes}.
    Context {Γ: SRA.t}.

    Inductive t {form : Type} : Type :=
    (** Atoms for the invariant system. *)
    | owni (i : positive) (p : @Syntax.t _ _ (@t form) form)
    | syn_inv_auth_l (ps : list (prod positive (@Syntax.t _ _ (@t form) form)))
    | ownd (D : gset positive)
    | owne (E : coPset)
    | syn_wsat_auth (x : index)
    (** Atoms for state invariants of wpsim. *)
    | ob_ths (ths : TIdSet.t)
    | ow_ths (tid : thread_id)
    | ob_st_src (st_src : st_src_type)
    | ow_st_src (st_src : st_src_type)
    | ob_st_tgt (st_tgt : st_tgt_type)
    | ow_st_tgt (st_tgt : st_tgt_type)
    | fair_src (im_src : @FairBeh.imap id_src_type owf)
    | fair_tgt (im_tgt : @FairBeh.imap (nat + id_tgt_type) nat_wf) (ths : TIdSet.t)
    (** Atoms for liveness logic invariants. *)
    | obl_edges_sat
    | obl_arrows_auth (x : index)
    | obl_arrows_regions_black (l : list ((nat + id_tgt_type) * nat * Ord.t * Qp * nat * (@Syntax.t _ _ (@t form) form)))
    | obl_arrow_delay (i : nat + id_tgt_type) (k : nat) (c : Ord.t) (q : Qp)
    | obl_arrow_done (x : nat)
    | obl_arrow_pend (i : nat + id_tgt_type) (k : nat) (c : Ord.t) (q : Qp)
    (** Atoms for liveness logic definitions. *)
    | obl_lof (k i n : nat)
    | obl_lo (k i : nat)
    | obl_pc (k l a : nat)
    | obl_pend (k : nat) (q : Qp)
    | obl_act (k : nat)
    | obl_link (k0 k1 l : nat)
    | obl_duty
        {Id : Type} (p : Prism.t (nat + id_tgt_type) Id) (i : Id) (ds : list (nat * nat * (@Syntax.t _ _ (@t form) form)))
    | obl_share_duty_b
        {Id : Type} (p : Prism.t (nat + id_tgt_type) Id) (i : Id) (ds : list (nat * nat * (@Syntax.t _ _ (@t form) form)))
    | obl_share_duty_w
        {Id : Type} (p : Prism.t (nat + id_tgt_type) Id) (i : Id) (ds : list (nat * nat * (@Syntax.t _ _ (@t form) form)))
    | obl_fc {Id : Type} (p : Prism.t (nat + id_tgt_type) Id) (i : Id)
    | obl_dpromise
        {Id : Type} (p : Prism.t (nat + id_tgt_type) Id) (i : Id) (k l : nat) (f : @Syntax.t _ _ (@t form) form)
    | obl_promise {Id : Type} (p : Prism.t (nat + id_tgt_type) Id) (i : Id) (k l : nat) (f : @Syntax.t _ _ (@t form) form)
    | obl_tc
    | obl_tdpromise (k l : nat) (f : @Syntax.t _ _ (@t form) form)
    | obl_tpromise (k l : nat) (f : @Syntax.t _ _ (@t form) form)
    | obl_pcs (ps : list (nat * nat)) (m a : nat)
    | obl_pps (ps : list (nat * Qp))
    | obl_ccs (k : nat) (ps : list (nat * nat)) (l : nat)
    (** Atoms for fairness logic *)
    | fair_white_src {Id : Type} (p : Prism.t id_src_type Id) (i : Id) (o : Ord.t)
    | fair_whites_src {Id : Type} (p : Prism.t id_src_type Id) (pred : Id -> Prop) (o : Ord.t)
    | fair_blacks_tgt {Id : Type} (p : Prism.t (nat + id_tgt_type) Id) (pred : Id -> Prop)
    .

  End ATOM.

End Atom.

Section TL_ATOM.

  Context {STT : StateTypes}.
  Context {Γ : SRA.t}.

  Global Instance TL_atom : sAtom.t := @Atom.t STT Γ.

End TL_ATOM.

Section TL_PROP.

  Context {STT : StateTypes}.
  Context {Γ : SRA.t}.

  Definition _sProp := (@Syntax._sProp TL_type _ TL_atom).
  Definition sProp := (@Syntax.sProp TL_type _ TL_atom).

End TL_PROP.

Section TLRAS.

  Class TLRAs_small (STT : StateTypes) (Γ : SRA.t) :=
    {
      (* Invariant related default RAs *)
      _OWNERA : @GRA.inG OwnERA Γ;
      _OWNDRA : @GRA.inG OwnDRA Γ;
      (* State related default RAs *)
      _THDRA: @GRA.inG ThreadRA Γ;
      _STATESRC: @GRA.inG (stateSrcRA st_src_type) Γ;
      _STATETGT: @GRA.inG (stateTgtRA st_tgt_type) Γ;
      _IDENTSRC: @GRA.inG (identSrcRA id_src_type) Γ;
      _IDENTTGT: @GRA.inG (identTgtRA id_tgt_type) Γ;
      (* Liveness logic related default RAs *)
      _OBLGRA: @GRA.inG ObligationRA.t Γ;
      _EDGERA: @GRA.inG EdgeRA Γ;
      _ARROWSHOTRA: @GRA.inG ArrowShotRA Γ;
    }.

  Class TLRAs (STT : StateTypes) (Γ : SRA.t) (Σ : GRA.t) :=
    {
      (* Invariant related default RAs *)
      _IINVSETRA : @GRA.inG (IInvSetRA sProp) Σ;
      (* Liveness logic related default RAs *)
      _ARROWRA: @GRA.inG (@ArrowRA id_tgt_type sProp) Σ;
      _SHAREDUTY: @GRA.inG (@ShareDutyRA id_tgt_type sProp) Σ;
    }.

End TLRAS.

Section EXPORT.

  Context {STT : StateTypes}.
  Context `{sub : @SRA.subG Γ Σ}.
  Context {TLRASs : TLRAs_small STT Γ}.
  Context {TLRAS : TLRAs STT Γ Σ}.

  (* Invariant related default RAs *)
  #[export] Instance OWNERA : @GRA.inG OwnERA Γ := _OWNERA.
  #[export] Instance OWNDRA : @GRA.inG OwnDRA Γ := _OWNDRA.
  #[export] Instance IINVSETRA : @GRA.inG (IInvSetRA sProp) Σ := _IINVSETRA.
  (* State related default RAs *)
  #[export] Instance THDRA: @GRA.inG ThreadRA Γ := _THDRA.
  #[export] Instance STATESRC: @GRA.inG (stateSrcRA st_src_type) Γ := _STATESRC.
  #[export] Instance STATETGT: @GRA.inG (stateTgtRA st_tgt_type) Γ := _STATETGT.
  #[export] Instance IDENTSRC: @GRA.inG (identSrcRA id_src_type) Γ := _IDENTSRC.
  #[export] Instance IDENTTGT: @GRA.inG (identTgtRA id_tgt_type) Γ := _IDENTTGT.
  (* Liveness logic related default RAs *)
  #[export] Instance OBLGRA: @GRA.inG ObligationRA.t Γ := _OBLGRA.
  #[export] Instance EDGERA: @GRA.inG EdgeRA Γ := _EDGERA.
  #[export] Instance ARROWSHOTRA: @GRA.inG ArrowShotRA Γ := _ARROWSHOTRA.
  #[export] Instance ARROWRA: @GRA.inG (@ArrowRA id_tgt_type sProp) Σ := _ARROWRA.
  #[export] Instance SHAREDUTY: @GRA.inG (@ShareDutyRA id_tgt_type sProp) Σ := _SHAREDUTY.

End EXPORT.

Section ATOMINTERP.

  Context {STT : StateTypes}.
  Context `{sub : @SRA.subG Γ Σ}.
  Context {TLRASs : TLRAs_small STT Γ}.
  Context {TLRAS : TLRAs STT Γ Σ}.
  Notation iProp := (iProp _).

  Import Atom.

  Definition Atom_interp n (a : @Atom.t STT Γ (_sProp n)) : iProp :=
    match a with
    (** Atom for the invariant system. *)
    | owni i p => @OwnI Σ sProp _ n i p
    | syn_inv_auth_l ps => @inv_auth Σ sProp _ n (list_to_map ps)
    | ownd D => OwnD D
    | owne E => OwnE E
    | syn_wsat_auth x => wsat_auth x
    (** Atoms for state invariants of wpsim. *)
    | ob_ths ths =>
        OwnM (● (NatMapRALarge.to_Map ths: (NatMapRALarge.t unit)): ThreadRA)
    | ow_ths tid =>
        own_thread tid
    | ob_st_src st_src =>
        OwnM (●E (Some st_src : leibnizO (option st_src_type)): stateSrcRA _)
    | ow_st_src st_src =>
        St_src st_src
    | ob_st_tgt st_tgt =>
        OwnM (●E (Some st_tgt : leibnizO (option st_tgt_type)): stateTgtRA _)
    | ow_st_tgt st_tgt =>
        St_tgt st_tgt
    | fair_src im_src =>
        FairRA.sat_source im_src
    | fair_tgt im_tgt ths =>
        FairRA.sat_target im_tgt ths
    (** Atoms for liveness logic. *)
    | obl_edges_sat => ObligationRA.edges_sat
    | obl_arrows_auth x => ObligationRA.arrows_auth x
    | obl_arrows_regions_black l => Regions.black n l
    | obl_arrow_delay i k c q =>
        ((∃ n, FairRA.black Prism.id i n q) ∗ (ObligationRA.white k (c × Ord.omega)%ord))%I
    | obl_arrow_done x =>
        OwnM (FiniteMap.singleton x (OneShot.shot ObligationRA._tt): ArrowShotRA)
    | obl_arrow_pend i k c q =>
        (∃ (n : nat), FairRA.black Prism.id i n q ∗ ObligationRA.white k (c × n)%ord)%I
    (** Atoms for liveness logic definitions. *)
    | obl_lof k l n => liveness_obligation_fine k l n
    | obl_lo k l => liveness_obligation k l
    | obl_pc k l a => progress_credit k l a
    | obl_pend k q => pending_obligation k q
    | obl_act k => active_obligation k
    | obl_link k0 k1 l => link k0 k1 l
    | obl_duty p i ds => duty p i ds
    | obl_share_duty_b p i ds => ShareDuty_black p i ds
    | obl_share_duty_w p i ds => ShareDuty_white p i ds
    | obl_fc p i => fairness_credit p i
    | obl_dpromise p i k l f => delayed_promise p i k l f
    | obl_promise p i k l f => promise p i k l f
    | obl_tc => thread_credit
    | obl_tdpromise k l f => thread_delayed_promise k l f
    | obl_tpromise k l f => thread_promise k l f
    | obl_pcs ps m a => progress_credits ps m a
    | obl_pps ps => progress_pendings ps
    | obl_ccs k ps l => collection_credits k ps l
    (** Atoms for fairness logic *)
    | fair_white_src p i o => FairRA.white p i o
    | fair_whites_src p pred o => FairRA.whites p pred o
    | fair_blacks_tgt p pred => FairRA.blacks p pred
    end.

  Global Instance TL_atom_interp : sAtomI.t := Atom_interp.

End ATOMINTERP.

Section TL_INTERP.

  Context {STT : StateTypes}.
  Context `{sub : @SRA.subG Γ Σ}.
  Context {TLRASs : TLRAs_small STT Γ}.
  Context {TLRAS : TLRAs STT Γ Σ}.

  Global Instance TL_interp : @IInvSet Σ sProp :=
    {| prop := @SyntaxI.interp _ _ sub TL_type TL_atom TL_atom_interp |}.

End TL_INTERP.

(** Notations and coercions. *)
Notation "'τ{' t ',' n '}'" := (sType.interp (t:=TL_type) t (_sProp n)).
Notation "'τ{' t '}'" := (sType.interp (t:=TL_type) t (_sProp _)).
Notation "'⟪' A ',' n '⟫'" := (TL_atom_interp n A).
Notation "'⟦' F ',' n '⟧'" := (SyntaxI.interp (α:=TL_atom_interp) n F).

Section RED.

  Context {STT : StateTypes}.
  Context `{sub : @SRA.subG Γ Σ}.
  Context {TLRASs : TLRAs_small STT Γ}.
  Context {TLRAS : TLRAs STT Γ Σ}.

  Lemma red_tl_atom n a :
    ⟦⟨a⟩%S, n⟧ = ⟪a, n⟫.
  Proof. apply red_sem_atom. Qed.

  Lemma red_tl_ownm n i r :
    ⟦Syntax.ownm i r, n⟧ = OwnM r.
  Proof. apply red_sem_ownm. Qed.

  Lemma red_tl_ownM `{@GRA.inG M Γ} n (r: M) :
    ⟦(➢ r)%S, n⟧ = OwnM r.
  Proof. apply red_sem_ownM. Qed.

  Lemma red_tl_lift_0 p :
    ⟦(⤉p)%S, 0⟧ = ⌜False⌝%I.
  Proof. apply red_sem_lift_0. Qed.

  Lemma red_tl_lift n p :
    ⟦(⤉p)%S, S n⟧ = ⟦p, n⟧ .
  Proof. apply red_sem_lift. Qed.

  Lemma red_tl_sepconj n p q :
    ⟦(p ∗ q)%S, n⟧ = (⟦p, n⟧ ∗ ⟦q, n⟧)%I.
  Proof. apply red_sem_sepconj. Qed.

  Lemma red_tl_pure n P :
    ⟦⌜P⌝%S, n⟧ = ⌜P⌝%I.
  Proof. apply red_sem_pure. Qed.

  Lemma red_tl_univ n ty p :
    ⟦(∀ (x : τ{ty}), p x)%S, n⟧ = (∀ (x : τ{ty}), ⟦p x, n⟧)%I.
  Proof. apply red_sem_univ. Qed.

  Lemma red_tl_ex n ty p :
    ⟦(∃ (x : τ{ty}), p x)%S, n⟧ = (∃ (x : τ{ty}), ⟦p x, n⟧)%I.
  Proof. apply red_sem_ex. Qed.

  Lemma red_tl_and n p q :
    ⟦(p ∧ q)%S, n⟧ = (⟦p, n⟧ ∧ ⟦q, n⟧)%I.
  Proof. apply red_sem_and. Qed.

  Lemma red_tl_or n p q :
    ⟦(p ∨ q)%S, n⟧ = (⟦p, n⟧ ∨ ⟦q, n⟧)%I.
  Proof. apply red_sem_or. Qed.

  Lemma red_tl_impl n p q :
    ⟦(p → q)%S, n⟧ = (⟦p, n⟧ → ⟦q, n⟧)%I.
  Proof. apply red_sem_impl. Qed.

  Lemma red_tl_wand n p q :
    ⟦(p -∗ q)%S, n⟧ = (⟦p, n⟧ -∗ ⟦q, n⟧)%I.
  Proof. apply red_sem_wand. Qed.

  Lemma red_tl_empty n :
    ⟦emp%S, n⟧ = emp%I.
  Proof. apply red_sem_empty. Qed.

  Lemma red_tl_persistently n p :
    ⟦(<pers> p)%S, n⟧ = (<pers> ⟦p, n⟧)%I.
  Proof. apply red_sem_persistently. Qed.

  Lemma red_tl_plainly n p :
    ⟦(■ p)%S, n⟧ = (■ ⟦p, n⟧)%I.
  Proof. apply red_sem_plainly. Qed.

  Lemma red_tl_upd n (p : sProp n) :
    ⟦( |==> p)%S, n⟧ = ( |==> ⟦p, n⟧ )%I.
  Proof. apply red_sem_upd. Qed.

  Lemma red_tl_sisim n
        {state_src state_tgt ident_src ident_tgt : Type}
        (tid : thread_id)
        (I0 : TIdSet.t -> (@FairBeh.imap ident_src owf) -> (@FairBeh.imap (nat + ident_tgt) nat_wf) -> state_src -> state_tgt -> sProp n)
        (I1 : TIdSet.t -> (@FairBeh.imap ident_src owf) -> (@FairBeh.imap (nat + ident_tgt) nat_wf) -> state_src -> state_tgt -> sProp n)
        {R_src R_tgt : Type}
        (Q : R_src -> R_tgt -> sProp n)
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
    = (isim_simple tid (intpF:=prop n) I0 I1 Q ps pt itr_src itr_tgt ths ims imt sts stt)%I.
  Proof. apply red_sem_sisim. Qed.

  Lemma red_tl_striple_format n
        (tid : thread_id)
        (I0 : TIdSet.t -> (@FairBeh.imap id_src_type owf) -> (@FairBeh.imap (nat + id_tgt_type) nat_wf) -> st_src_type -> st_tgt_type -> sProp n)
        (I1 : TIdSet.t -> (@FairBeh.imap id_src_type owf) -> (@FairBeh.imap (nat + id_tgt_type) nat_wf) -> st_src_type -> st_tgt_type -> sProp n)
        (I2 : TIdSet.t -> (@FairBeh.imap id_src_type owf) -> (@FairBeh.imap (nat + id_tgt_type) nat_wf) -> st_src_type -> st_tgt_type -> coPset -> sProp n)
        (P : sProp n)
        {RV : Type}
        (Q : RV -> sProp n)
        (E1 E2 : coPset)
        {R_src R_tgt : Type}
        (TERM : R_src -> R_tgt -> sProp n)
        (ps pt : bool)
        (itr_src : itree (threadE id_src_type st_src_type) R_src)
        (code : itree (threadE id_tgt_type st_tgt_type) RV)
        (ktr_tgt : ktree (threadE id_tgt_type st_tgt_type) RV R_tgt)
    :
    ⟦(Syntax.striple_format tid I0 I1 I2 P Q E1 E2 TERM ps pt itr_src code ktr_tgt), n⟧
    =
      (triple_format (intpF:=prop n) tid
                     I0 I1 I2 P Q E1 E2 TERM
                     ps pt itr_src code ktr_tgt)%I.
  Proof. apply red_sem_striple_format. Qed.

  (** Derived ones. *)

  Lemma red_tl_affinely n p :
    ⟦(<affine> p)%S, n⟧ = (<affine> ⟦p, n⟧)%I.
  Proof. apply red_sem_affinely. Qed.

  Lemma red_tl_intuitionistically n p :
    ⟦(□ p)%S, n⟧ = (□ ⟦p, n⟧)%I.
  Proof. apply red_sem_intuitionistically. Qed.

  Lemma red_tl_big_sepM n A K {EQ : EqDecision K} {CNT : Countable K} I f :
    ⟦@syn_big_sepM _ _ n K _ _ A I f, n⟧ = ([∗ map] i ↦ p ∈ I, ⟦f i p, n⟧)%I.
  Proof. apply red_syn_big_sepM. Qed.

  Lemma red_tl_big_sepS n K {EQ : EqDecision K} {CNT : Countable K} I f :
    ⟦@syn_big_sepS _ _ n K _ _ I f, n⟧ = ([∗ set] i ∈ I, ⟦f i, n⟧)%I.
  Proof. apply red_syn_big_sepS. Qed.

  Lemma red_tl_big_sepL1 n A I f :
    ⟦@syn_big_sepL1 _ _ n A I f, n⟧ = ([∗ list] a ∈ I, ⟦f a, n⟧)%I.
  Proof. apply red_syn_big_sepL1. Qed.

  Lemma red_tl_sat_list n X Ts x intp l :
    ⟦@syn_sat_list _ _ n X Ts x intp l, n⟧
    = @Regions.sat_list _ Ts _ x (fun t => ⟦intp t, n⟧) l.
  Proof. apply red_syn_sat_list. Qed.

End RED.

(** Simple sProp reduction tactics. *)
Ltac red_tl_binary_once := (try rewrite ! @red_tl_sepconj;
                            try rewrite ! @red_tl_and;
                            try rewrite ! @red_tl_or;
                            try rewrite ! @red_tl_impl;
                            try rewrite ! @red_tl_wand
                           ).

Ltac red_tl_unary_once := (
                           try rewrite ! @red_tl_atom;
                           try rewrite ! @red_tl_ownm;
                           try rewrite ! @red_tl_ownM;
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

Ltac red_tl_unary_once_every := (
                                 try rewrite ! @red_tl_atom in *;
                                 try rewrite ! @red_tl_ownm in *;
                                 try rewrite ! @red_tl_ownM in *;
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

(** Develop full definitions. *)
Section WSATS.

  Context {STT : StateTypes}.
  Context `{sub : @SRA.subG Γ Σ}.
  Context {TLRASs : TLRAs_small STT Γ}.
  Context {TLRAS : TLRAs STT Γ Σ}.

  Import Atom.

  (** Definitions for wsat. *)

  Definition syn_inv_auth n (ps : gmap positive (sProp n)) : Atom.t :=
    syn_inv_auth_l (map_to_list ps).

  Lemma red_syn_inv_auth n ps :
    ⟪syn_inv_auth n ps, n⟫ = inv_auth n ps.
  Proof.
    ss. rewrite list_to_map_to_list. ss.
  Qed.

  Definition syn_inv_satall_fun n : positive -> sProp n -> sProp n :=
    fun i p => ((p ∗ ⟨ownd {[i]}⟩) ∨ (⟨owne {[i]}⟩))%S.

  Definition syn_inv_satall n (ps : gmap positive (sProp n)) : sProp n :=
    ([∗ n, sPropT map] k ↦ p ∈ ps, syn_inv_satall_fun n k p)%S.

  Lemma red_syn_inv_satall_fun n i p :
    ⟦syn_inv_satall_fun n i p, n⟧ = ((⟦p, n⟧ ∗ (OwnD {[i]})) ∨ (OwnE {[i]}))%I.
  Proof.
    unfold syn_inv_satall_fun. red_tl. auto.
  Qed.

  Lemma red_syn_inv_satall n ps :
    ⟦syn_inv_satall n ps, n⟧ = inv_satall n ps.
  Proof.
    unfold syn_inv_satall. rewrite red_tl_big_sepM. ss.
  Qed.

  Definition syn_wsat n : sProp (S n) :=
    (∃ (I : τ{pgmapT Φ, S n}), ⤉(⟨syn_inv_auth n I⟩ ∗ (syn_inv_satall n I)))%S.

  Lemma red_syn_wsat n :
    ⟦syn_wsat n, S n⟧ = wsat n.
  Proof.
    unfold syn_wsat, wsat. red_tl. f_equal. extensionalities I.
    red_tl. rewrite red_syn_inv_auth. rewrite red_syn_inv_satall. auto.
  Qed.

  (** Definitions for wsats. *)

  Fixpoint lifts {n} (p : sProp n) m {struct m} : sProp (m + n) :=
    match m with
    | O => p
    | S m' => (⤉(@lifts n p m'))%S
    end.

  Lemma red_lifts n (p : sProp n) m :
    ⟦lifts p m, m + n⟧ = ⟦p, n⟧.
  Proof.
    induction m; ss.
  Qed.

  (* Definition syn_wsats n : sProp (S n) := *)
  (*   syn_big_sepL1 n (baseT nat) (seq 0 n) (fun m => lifts (syn_wsat m) (n - (S m))). *)

  Fixpoint lifts_seps (p : forall n, sProp (S n)) n : sProp n :=
    match n with
    | O => emp%S
    | S m => ((⤉(lifts_seps p m)) ∗ (p m))%S
    end.

  Lemma unfold_lifts_seps p n :
    lifts_seps p (S n) = (⤉(lifts_seps p n) ∗ (p n))%S.
  Proof. ss. Qed.

  Lemma red_lifts_seps (p : forall n, sProp (S n)) n :
    ⟦lifts_seps p n, n⟧ = sep_conjs (fun i => ⟦p i, S i⟧) n.
  Proof.
    induction n; ss.
    red_tl. rewrite IHn. auto.
  Qed.

  Definition syn_wsats n : sProp n := lifts_seps syn_wsat n.

  Lemma unfold_syn_wsats n :
    syn_wsats (S n) = (⤉(syn_wsats n) ∗ (syn_wsat n))%S.
  Proof. apply unfold_lifts_seps. Qed.

  Lemma red_syn_wsats n :
    ⟦syn_wsats n, n⟧ = wsats n.
  Proof.
    unfold syn_wsats, wsats. replace wsat with (fun i => ⟦syn_wsat i, S i⟧).
    apply red_lifts_seps.
    extensionalities i. apply red_syn_wsat.
  Qed.

  (** Definitions for inv and FUpd. *)

  Definition syn_inv (n : index) (N : namespace) (p : sProp n) : sProp n :=
    (∃ (i : τ{positive}), ⌜i ∈ (nclose N : coPset)⌝ ∧ ⟨owni i p⟩)%S.

  Lemma red_syn_inv n N p :
    ⟦syn_inv n N p, n⟧ = inv n N p.
  Proof.
    done.
  Qed.

  Definition syn_fupd (n : index) (A : sProp n) (E1 E2 : coPset) (p : sProp n) : sProp n :=
    (A ∗ syn_wsats n ∗ ⟨owne E1⟩ -∗ |==> (A ∗ syn_wsats n ∗ ⟨owne E2⟩ ∗ p))%S.

  Lemma red_syn_fupd n A E1 E2 p :
    ⟦syn_fupd n A E1 E2 p, n⟧ = =|n|=(⟦A, n⟧)={E1,E2}=> ⟦p, n⟧.
  Proof.
    rewrite /syn_fupd IndexedInvariants.FUpd_unseal'.
    red_tl. rewrite ! red_syn_wsats. auto.
  Qed.

End WSATS.
Global Opaque syn_wsat syn_wsats syn_inv syn_fupd.

Section OBLIG.

  Context {STT : StateTypes}.
  Context `{sub : @SRA.subG Γ Σ}.
  Context {TLRASs : TLRAs_small STT Γ}.
  Context {TLRAS : TLRAs STT Γ Σ}.

  Local Notation _dataT := ((nat + id_tgt_type) * nat * Ord.t * Qp * nat)%type.
  Local Notation dataT := (fun (n : index) => (_dataT * sProp n)%type).

  Import Atom.

  Definition syn_obl_arrow n : dataT n -> sProp n :=
    fun '(i, k, c, q, x, f) =>
      ((□ (f -∗ □ f))
         ∗
         ((⟨obl_pend k (1/2)⟩ ∗ ⟨obl_arrow_delay i k c q⟩)
          ∨
            (⟨obl_act k⟩
               ∗
               ((⟨obl_arrow_done x⟩ ∗ f)
                ∨
                  ⟨obl_arrow_pend i k c q⟩))
      ))%S.

  Lemma red_syn_obl_arrow n d :
    ⟦syn_obl_arrow n d, n⟧ = ObligationRA.arrow n d.
  Proof.
    unfold syn_obl_arrow. des_ifs.
  Qed.

  Definition syn_arrows_sat_list n (l : list (dataT n)) : sProp n :=
    syn_sat_list n _ dataT n (syn_obl_arrow n) l.

  Lemma red_syn_arrows_sat_list n l :
    ⟦syn_arrows_sat_list n l, n⟧ = Regions.sat_list _ (ObligationRA.arrow n) l.
  Proof.
    unfold syn_arrows_sat_list. rewrite red_tl_sat_list. f_equal.
    extensionalities t. apply red_syn_obl_arrow.
  Qed.

  (* Check (⇣ Ord.t)%stype. *)
  (* Check (⇣ (nat + nat)%type)%stype. *)
  (* Fail Check (⇣ (sum_tid id_tgt_type))%stype. *)

  Definition syn_arrows_sat n : sProp (S n) :=
    (∃ (l : τ{ listT ((⇣(nat + id_tgt_type)) * (⇣nat) * (⇣Ord.t) * (⇣Qp) * (⇣nat) * Φ)%stype, S n }),
        ⤉(⟨obl_arrows_regions_black l⟩ ∗ syn_arrows_sat_list n l))%S.

  Lemma red_syn_arrows_sat n :
    ⟦syn_arrows_sat n, S n⟧ = ObligationRA.arrows_sat n.
  Proof.
    unfold syn_arrows_sat. red_tl.
    unfold ObligationRA.arrows_sat, Regions.sat.
    f_equal. extensionality l. red_tl. ss.
    rewrite red_syn_arrows_sat_list. f_equal.
  Qed.

  Definition syn_arrows_sats n : sProp n := lifts_seps syn_arrows_sat n.

  Lemma unfold_syn_arrows_sats n :
    syn_arrows_sats (S n) = (⤉(syn_arrows_sats n) ∗ (syn_arrows_sat n))%S.
  Proof. apply unfold_lifts_seps. Qed.

  Lemma red_syn_arrows_sats n :
    ⟦syn_arrows_sats n, n⟧ = ObligationRA.arrows_sats n.
  Proof.
    unfold syn_arrows_sats, ObligationRA.arrows_sats. unfold Regions.nsats.
    replace (λ i : index, Regions.sat i (ObligationRA.arrows i))
            with (fun i => ⟦syn_arrows_sat i, S i⟧).
    apply red_lifts_seps.
    extensionalities i. apply red_syn_arrows_sat.
  Qed.

  Definition syn_fairI n : sProp n := (⟨obl_edges_sat⟩ ∗ syn_arrows_sats n)%S.

  Lemma red_syn_fairI n :
    ⟦syn_fairI n, n⟧ = fairI n.
  Proof.
    unfold syn_fairI, fairI. red_tl. rewrite red_syn_arrows_sats. ss.
  Qed.

End OBLIG.
Global Opaque syn_obl_arrow syn_arrows_sat_list syn_arrows_sat syn_arrows_sats.

Section SIMI.

  Context {STT : StateTypes}.
  Context `{sub : @SRA.subG Γ Σ}.
  Context {TLRASs : TLRAs_small STT Γ}.
  Context {TLRAS : TLRAs STT Γ Σ}.
  Notation iProp := (iProp _).

  Let srcE := threadE id_src_type st_src_type.
  Let tgtE := threadE id_tgt_type st_tgt_type.

  Import Atom.

  Definition syn_default_I n
    : TIdSet.t -> (@FairBeh.imap id_src_type owf) -> (@FairBeh.imap (nat + id_tgt_type) nat_wf) -> st_src_type -> st_tgt_type -> sProp n :=
    fun ths im_src im_tgt st_src st_tgt =>
      (⟨ob_ths ths⟩ ∗ ⟨ob_st_src st_src⟩ ∗ ⟨ob_st_tgt st_tgt⟩ ∗ ⟨fair_src im_src⟩ ∗ ⟨fair_tgt im_tgt ths⟩ ∗ ⟨obl_edges_sat⟩ ∗ syn_arrows_sats n ∗ ⟨obl_arrows_auth n⟩)%S.

  Lemma red_syn_default_I n ths ims imt sts stt :
    ⟦syn_default_I n ths ims imt sts stt, n⟧ = default_I n ths ims imt sts stt.
  Proof.
    unfold syn_default_I, default_I. red_tl. ss.
    rewrite red_syn_arrows_sats. auto.
  Qed.

  Definition syn_default_I_past tid n
    : TIdSet.t -> (@FairBeh.imap id_src_type owf) -> (@FairBeh.imap (nat + id_tgt_type) nat_wf) -> st_src_type -> st_tgt_type -> sProp n :=
    fun ths im_src im_tgt st_src st_tgt =>
      (∃ (im_tgt0 : τ{ ((nat + id_tgt_type) -> nat_wfT)%stype }),
          (⌜fair_update im_tgt0 im_tgt (prism_fmap inlp (tids_fmap tid ths))⌝)
            ∗ (syn_default_I n ths im_src im_tgt0 st_src st_tgt))%S.

  Lemma red_syn_default_I_past tid n ths ims imt sts stt :
    ⟦syn_default_I_past tid n ths ims imt sts stt, n⟧ = default_I_past tid n ths ims imt sts stt.
  Proof.
    unfold syn_default_I_past, default_I_past. red_tl. ss.
    f_equal. extensionalities im_tgt0.
    rewrite -red_syn_default_I.
    red_tl. auto.
  Qed.

  Definition syn_wpsim n tid E
    : forall {R_src R_tgt : Type}, (R_src -> R_tgt -> sProp n) -> bool -> bool -> itree srcE R_src -> itree tgtE R_tgt -> sProp n
    :=
    fun R_src R_tgt Q ps pt itr_src itr_tgt =>
      (∀ (ths : τ{ tidsetT })
         (im_src : τ{ (id_src_type -> owfT)%stype })
         (im_tgt : τ{ ((nat + id_tgt_type) -> nat_wfT)%stype })
         (st_src : τ{ st_src_type })
         (st_tgt : τ{ st_tgt_type }),
          (syn_default_I_past tid n ths im_src im_tgt st_src st_tgt ∗ (⟨syn_wsat_auth n⟩ ∗ syn_wsats n ∗ ⟨owne E⟩))
            -∗
            (Syntax.sisim tid
                          (fun ths ims imt sts stt =>
                             ((syn_default_I n ths ims imt sts stt)
                                ∗ (⟨syn_wsat_auth n⟩ ∗ syn_wsats n ∗ ⟨owne ⊤⟩))%S)
                          (fun ths ims imt sts stt =>
                             ((syn_default_I_past tid n ths ims imt sts stt)
                                ∗ (⟨syn_wsat_auth n⟩ ∗ syn_wsats n ∗ ⟨owne ⊤⟩))%S)
                          Q ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
      )%S.

  Lemma red_isim_eq_1 n :
    (λ (ths0 : TIdSet.t) (ims : FairBeh.imap id_src_type owf) (imt : FairBeh.imap (sum_tid id_tgt_type) nat_wf) (sts : st_src_type) (stt : st_tgt_type),
      ⟦ (syn_default_I n ths0 ims imt sts stt ∗ ⟨ syn_wsat_auth n ⟩ ∗ syn_wsats n ∗ ⟨owne ⊤⟩)%S, n ⟧) =
      (λ (ths0 : TIdSet.t) (im_src0 : FairBeh.imap id_src_type owf) (im_tgt0 : FairBeh.imap (sum_tid id_tgt_type) nat_wf) (st_src0 : st_src_type) (st_tgt0 : st_tgt_type),
        (default_I n ths0 im_src0 im_tgt0 st_src0 st_tgt0 ∗ wsat_auth n ∗ wsats n ∗ OwnE ⊤)%I).
  Proof.
    extensionalities ths0 ims imt sts stt. red_tl.
    rewrite -red_syn_default_I. rewrite red_syn_wsats. ss.
  Qed.

  Lemma red_isim_eq_2 tid n rr :
  (λ (R_src R_tgt : Type) (QQ : R_src
                                → R_tgt
                                  → TIdSet.t
                                    → FairBeh.imap id_src_type owf
                                      → FairBeh.imap (sum_tid id_tgt_type) nat_wf
                                        → st_src_type → st_tgt_type → iProp)
     (ps0 pt0 : bool) (itr_src0 : itree (threadE id_src_type st_src_type) R_src)
     (itr_tgt : itree (threadE id_tgt_type st_tgt_type) R_tgt) (ths0 : TIdSet.t)
     (im_src0 : FairBeh.imap id_src_type owf) (im_tgt0 : FairBeh.imap
                                                           (sum_tid id_tgt_type) nat_wf)
     (st_src0 : st_src_type) (st_tgt0 : st_tgt_type),
     (∃ (Q0 : R_src → R_tgt → iProp) (_ : QQ =
                                          (λ (r_src : R_src) (r_tgt : R_tgt)
                                             (ths1 : TIdSet.t) (im_src1 :
                                                                FairBeh.imap id_src_type owf)
                                             (im_tgt1 : FairBeh.imap (sum_tid id_tgt_type) nat_wf)
                                             (st_src1 : st_src_type)
                                             (st_tgt1 : st_tgt_type),
                                             (default_I_past tid n ths1 im_src1 im_tgt1 st_src1
                                                st_tgt1 ∗ wsat_auth n ∗
                                              wsats n ∗ OwnE ⊤) ∗ Q0 r_src r_tgt)),
        rr R_src R_tgt Q0 ps0 pt0 itr_src0 itr_tgt ∗
        default_I_past tid n ths0 im_src0 im_tgt0 st_src0 st_tgt0 ∗ wsat_auth n ∗
        wsats n ∗ OwnE ⊤)%I) =
  (λ (R_src R_tgt : Type) (QQ : R_src
                                → R_tgt
                                  → TIdSet.t
                                    → FairBeh.imap id_src_type owf
                                      → FairBeh.imap (sum_tid id_tgt_type) nat_wf
                                        → st_src_type → st_tgt_type → iProp)
     (ps0 pt0 : bool) (itr_src0 : itree (threadE id_src_type st_src_type) R_src)
     (itr_tgt : itree (threadE id_tgt_type st_tgt_type) R_tgt) (ths0 : TIdSet.t)
     (im_src0 : FairBeh.imap id_src_type owf) (im_tgt0 : FairBeh.imap
                                                           (sum_tid id_tgt_type) nat_wf)
     (st_src0 : st_src_type) (st_tgt0 : st_tgt_type),
     (∃ (Q0 : R_src → R_tgt → iProp) (_ : QQ =
                                          (λ (r_src : R_src) (r_tgt : R_tgt)
                                             (ths1 : TIdSet.t) (im_src1 :
                                                                FairBeh.imap id_src_type owf)
                                             (im_tgt1 : FairBeh.imap (sum_tid id_tgt_type) nat_wf)
                                             (st_src1 : st_src_type)
                                             (st_tgt1 : st_tgt_type),
                                             ⟦ (syn_default_I_past tid n ths1 im_src1 im_tgt1
                                                  st_src1 st_tgt1 ∗ ⟨ syn_wsat_auth n ⟩ ∗
                                                syn_wsats n ∗ ⟨owne ⊤⟩)%S, n ⟧ ∗
                                             Q0 r_src r_tgt)),
        rr R_src R_tgt Q0 ps0 pt0 itr_src0 itr_tgt ∗
        ⟦ (syn_default_I_past tid n ths0 im_src0 im_tgt0 st_src0 st_tgt0 ∗
                              ⟨ syn_wsat_auth n ⟩ ∗ syn_wsats n ∗ ⟨owne ⊤⟩)%S, n ⟧)%I).
  Proof.
    extensionalities R_src R_tgt QQ ps0 pt0 itr_src0.
    extensionalities itr_tgt0 ths0 im_src0 im_tgt0 st_src0 st_tgt0.
    f_equal. extensionalities Q0. red_tl.
    rewrite -red_syn_default_I_past. rewrite red_syn_wsats. ss.
    replace
      (λ (r_src : R_src) (r_tgt : R_tgt) (ths1 : TIdSet.t) (im_src1 :
                                                             FairBeh.imap id_src_type owf)
         (im_tgt1 : FairBeh.imap (sum_tid id_tgt_type) nat_wf) (st_src1 : st_src_type)
         (st_tgt1 : st_tgt_type),
        (⟦ (syn_default_I_past tid n ths1 im_src1 im_tgt1 st_src1 st_tgt1 ∗
                               ⟨ syn_wsat_auth n ⟩ ∗ syn_wsats n ∗ ⟨owne ⊤⟩)%S, n ⟧ ∗ Q0 r_src r_tgt)%I)
      with
      (λ (r_src : R_src) (r_tgt : R_tgt) (ths1 : TIdSet.t) (im_src1 :
                                                             FairBeh.imap id_src_type owf)
         (im_tgt1 : FairBeh.imap (sum_tid id_tgt_type) nat_wf) (st_src1 : st_src_type)
         (st_tgt1 : st_tgt_type),
        ((default_I_past tid n ths1 im_src1 im_tgt1 st_src1 st_tgt1 ∗
                         wsat_auth n ∗ wsats n ∗ OwnE ⊤) ∗ Q0 r_src r_tgt)%I).
    auto.
    extensionalities r_src r_tgt ths1 im_src1 im_tgt1.
    extensionalities st_src1 st_tgt1.
    red_tl. rewrite -red_syn_default_I_past. rewrite red_syn_wsats. ss.
  Qed.

  Lemma red_isim_eq_3 RS RT tid n Q :
  (λ (r_src : RS) (r_tgt : RT) (ths0 : TIdSet.t) (ims : FairBeh.imap id_src_type owf)
     (imt : FairBeh.imap (sum_tid id_tgt_type) nat_wf) (sts : st_src_type)
     (stt : st_tgt_type),
     (⟦ (syn_default_I_past tid n ths0 ims imt sts stt ∗ ⟨ syn_wsat_auth n ⟩ ∗
         syn_wsats n ∗ ⟨owne ⊤⟩)%S, n ⟧ ∗ ⟦ Q r_src r_tgt, n ⟧)%I) =
  (λ (r_src : RS) (r_tgt : RT) (ths0 : TIdSet.t) (im_src0 : FairBeh.imap id_src_type owf)
     (im_tgt0 : FairBeh.imap (sum_tid id_tgt_type) nat_wf) (st_src0 : st_src_type)
     (st_tgt0 : st_tgt_type),
     ((default_I_past tid n ths0 im_src0 im_tgt0 st_src0 st_tgt0 ∗ wsat_auth n ∗
                      wsats n ∗ OwnE ⊤) ∗ ⟦ Q r_src r_tgt, n ⟧)%I).
  Proof.
    extensionalities r_src r_tgt ths1 im_src1 im_tgt1.
    extensionalities st_src1 st_tgt1.
    red_tl. rewrite -red_syn_default_I_past. rewrite red_syn_wsats. ss.
  Qed.

  Lemma red_syn_wpsim
        n tid E RS RT (Q : RS -> RT -> sProp n) ps pt itr_src itr_tgt :
    ⟦syn_wpsim n tid E Q ps pt itr_src itr_tgt, n⟧
      =
      wpsim n tid E ibot7 ibot7 (fun rs rt => ⟦Q rs rt, n⟧) ps pt itr_src itr_tgt.
  Proof.
    unfold syn_wpsim, wpsim. red_tl. simpl.
    f_equal. extensionalities ths. red_tl.
    f_equal. extensionalities im_src. red_tl.
    f_equal. extensionalities im_tgt. red_tl.
    f_equal. extensionalities st_src. red_tl.
    f_equal. extensionalities st_tgt. red_tl.
    rewrite -red_syn_default_I_past. rewrite red_syn_wsats.
    f_equal. unfold isim_simple.
    f_equal; ss.
    - apply red_isim_eq_1.
    - unfold ibot7. symmetry. apply red_isim_eq_2.
    - unfold ibot7. symmetry. apply red_isim_eq_2.
    - apply red_isim_eq_3.
  Qed.



  (* State interp with lens. *)
  Definition syn_view_interp n {S V} (l : Lens.t S V) (SI : S -> sProp n) (VI : V -> sProp n) : Prop :=
    forall s, ⟦SI s , n⟧ ⊢ ( ⟦VI (Lens.view l s), n⟧ ∗ ∀ x, ⟦VI x, n⟧ -∗ ⟦SI (Lens.set l x s), n⟧ ).

  Definition syn_src_interp_as n {V} (l: Lens.t st_src_type V) (VI: V -> sProp n) : sProp (S n) :=
    (∃ (SI : τ{(st_src_type -> Φ)%stype, S n}) (p : τ{Φ%stype, S n}),
        (⌜⟦p, n⟧ = (∃ st, St_src st ∗ ⟦(SI st), n⟧)%I⌝)
          ∗ (⤉(syn_inv n N_state_src p)) ∗ ⌜syn_view_interp n l SI VI⌝)%S.

  Lemma red_syn_src_interp_as n {V} (l: Lens.t st_src_type V) (VI: V -> sProp n) :
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

  Definition syn_tgt_interp_as n {V} (l: Lens.t st_tgt_type V) (VI: V -> sProp n) : sProp (S n) :=
    (∃ (SI : τ{(st_tgt_type -> Φ)%stype, S n}) (p : τ{Φ%stype, S n}),
        (⌜⟦p, n⟧ = (∃ st, St_tgt st ∗ ⟦(SI st), n⟧)%I⌝)
          ∗ (⤉(syn_inv n N_state_tgt p)) ∗ ⌜syn_view_interp n l SI VI⌝)%S.

  Lemma red_syn_tgt_interp_as n {V} (l: Lens.t st_tgt_type V) (VI: V -> sProp n) :
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

Section DERIV.

  Context {STT : StateTypes}.
  Context `{sub : @SRA.subG Γ Σ}.
  Context {TLRASs : TLRAs_small STT Γ}.
  Context {TLRAS : TLRAs STT Γ Σ}.

  Import Atom.

  Definition syn_until_promise {Id} {n} (p : Prism.t _ Id) (i : Id) k l (f P : sProp n) :=
    (⟨obl_promise p i k l f⟩ ∗ (P ∨ (□ f)))%S.

  Definition syn_until_tpromise {n} k l (f P : sProp n) :=
    (⟨obl_tpromise k l f⟩ ∗ (P ∨ (□ f)))%S.

  Lemma red_syn_until_promise
        {Id} n (p : Prism.t _ Id) (i : Id) k l (f P : sProp n) :
    ⟦syn_until_promise p i k l f P, n⟧ = until_promise p i k l f P.
  Proof.
    unfold syn_until_promise. red_tl. unfold until_promise. f_equal.
  Qed.

  Lemma red_syn_until_tpromise
        n k l (f P : sProp n) :
    ⟦syn_until_tpromise k l f P, n⟧ = until_thread_promise k l f P.
  Proof.
    unfold syn_until_tpromise. red_tl. unfold until_thread_promise. f_equal.
  Qed.

End DERIV.

(** Notations. *)

(* Fancy update. *)
Notation "'=|' x '|=(' A ')={' E1 ',' E2 '}=>' P" := (syn_fupd x A E1 E2 P) (at level 90) : sProp_scope.
Notation "'=|' x '|={' E1 ',' E2 '}=>' P" := (=|x|=( ⌜True⌝%S )={ E1, E2}=> P)%S (at level 90) : sProp_scope.
Notation "P =| x |=( A )={ E1 , E2 }=∗ Q" := (P -∗ =|x|=(A)={E1,E2}=> Q)%S (at level 90) : sProp_scope.
Notation "P =| x |={ E1 , E2 }=∗ Q" := (P -∗ =|x|={E1,E2}=> Q)%S (at level 90) : sProp_scope.

Notation "'=|' x '|=(' A ')={' E '}=>' P" := (syn_fupd x A E E P) (at level 90) : sProp_scope.
Notation "'=|' x '|={' E '}=>' P" := (=|x|=( ⌜True⌝%S )={ E }=> P)%S (at level 90) : sProp_scope.
Notation "P =| x |=( A )={ E }=∗ Q" := (P -∗ =|x|=(A)={E}=> Q)%S (at level 90) : sProp_scope.
Notation "P =| x |={ E }=∗ Q" := (P -∗ =|x|={E}=> Q)%S (at level 90) : sProp_scope.

(* State. *)
Notation "'TID' ( tid )" :=
  (⟨Atom.ow_ths tid⟩)%S (at level 50, tid at level 1, format "TID ( tid )") : sProp_scope.
Notation "'STSRC' { s }" :=
  (⟨Atom.ow_st_src s⟩)%S (at level 50, s at level 1, format "STSRC { s }") : sProp_scope.
Notation "'STTGT' { s }" :=
  (⟨Atom.ow_st_tgt s⟩)%S (at level 50, s at level 1, format "STTGT { s }") : sProp_scope.

(* Liveness logic. *)
Notation "'◆' [ k , l ]" :=
  (⟨Atom.obl_lo k l⟩)%S (at level 50, k, l at level 1, format "◆ [ k ,  l ]") : sProp_scope.
Notation "'◆' [ k , l , n ]" :=
  (⟨Atom.obl_lof k l n⟩)%S (at level 50, k, l, n at level 1, format "◆ [ k ,  l ,  n ]") : sProp_scope.
Notation "'◇' [ k ]( l , a )" :=
  (⟨Atom.obl_pc k l a⟩)%S (at level 50, k, l, a at level 1, format "◇ [ k ]( l ,  a )") : sProp_scope.
Notation "'⧖' [ k , q ]" :=
  (⟨Atom.obl_pend k q⟩)%S (at level 50, k, q at level 1, format "⧖ [ k ,  q ]") : sProp_scope.
Notation "'⋈' [ k ]" :=
  (⟨Atom.obl_act k⟩)%S (at level 50, k at level 1, format "⋈ [ k ]") : sProp_scope.
Notation "s '-(' l ')-' '◇' t" :=
  (⟨Atom.obl_link s t l⟩)%S (at level 50, l, t at level 1, format "s  -( l )- ◇  t") : sProp_scope.
Notation "'Duty' ( p ◬ i ) ds" :=
  (⟨Atom.obl_duty p i ds⟩)%S (at level 50, p, i, ds at level 1, format "Duty ( p  ◬  i )  ds") : sProp_scope.
Notation "'Duty' ( tid ) ds" :=
  (⟨Atom.obl_duty inlp tid ds⟩)%S (at level 50, tid, ds at level 1, format "Duty ( tid )  ds") : sProp_scope.
Notation "'€' ( p ◬ i )" :=
  (⟨Atom.obl_fc p i⟩)%S (format "€ ( p  ◬  i )") : sProp_scope.
Notation "'-(' p ◬ i ')-[' k '](' l ')-' '⧖' f" :=
  (⟨Atom.obl_dpromise p i k l f⟩)%S (at level 50, k, l, p, i at level 1, format "-( p  ◬  i )-[ k ]( l )- ⧖  f") : sProp_scope.
Notation "'-(' p ◬ i ')-[' k '](' l ')-' '◇' f" :=
  (⟨Atom.obl_promise p i k l f⟩)%S (at level 50, k, l, p, i at level 1, format "-( p  ◬  i )-[ k ]( l )- ◇  f") : sProp_scope.
Notation "'€'" :=
  (⟨Atom.obl_tc⟩)%S : sProp_scope.
Notation "'-[' k '](' l ')-' '⧖' f" :=
  (⟨Atom.obl_tdpromise k l f⟩)%S (at level 50, k, l at level 1, format "-[ k ]( l )- ⧖  f") : sProp_scope.
Notation "'-[' k '](' l ')-' '◇' f" :=
  (⟨Atom.obl_tpromise k l f⟩)%S (at level 50, k, l at level 1, format "-[ k ]( l )- ◇  f") : sProp_scope.
Notation "'◇' { ps }( m , a )" :=
  (⟨Atom.obl_pcs ps m a⟩)%S (at level 50, ps, m, a at level 1, format "◇ { ps }( m ,  a )") : sProp_scope.
Notation "'⧖' { ps }" :=
  (⟨Atom.obl_pps ps⟩)%S (at level 50, ps at level 1, format "⧖ { ps }") : sProp_scope.
Notation "⦃ '◆' [ k ] & '◇' { ps }( l )⦄" :=
  (⟨Atom.obl_ccs k ps l⟩)%S (at level 50, k, ps, l at level 1, format "⦃ ◆ [ k ]  &  ◇ { ps }( l )⦄") : sProp_scope.
Notation "P '-U-(' p ◬ i ')-[' k '](' l ')-' '◇' f" :=
  (syn_until_promise p i k l f P)%S (at level 50, k, l, p, i at level 1, format "P  -U-( p  ◬  i )-[ k ]( l )- ◇  f") : sProp_scope.
Notation "P '-U-[' k '](' l ')-' '◇' f" :=
  (syn_until_tpromise k l f P) (at level 50, k, l at level 1, format "P  -U-[ k ]( l )- ◇  f") : sProp_scope.

Notation "'●Duty' ( p ◬ i ) ds" :=
  (⟨Atom.obl_share_duty_b p i ds⟩)%S (at level 50, p, i, ds at level 1, format "●Duty ( p  ◬  i )  ds") : sProp_scope.
Notation "'○Duty' ( p ◬ i ) ds" :=
  (⟨Atom.obl_share_duty_w p i ds⟩)%S (at level 50, p, i, ds at level 1, format "○Duty ( p  ◬  i )  ds") : sProp_scope.
Notation "'●Duty' ( tid ) ds" :=
  (⟨Atom.obl_share_duty_b inlp tid ds⟩)%S (at level 50, tid, ds at level 1, format "●Duty ( tid )  ds") : sProp_scope.
Notation "'○Duty' ( tid ) ds" :=
  (⟨Atom.obl_share_duty_w inlp tid ds⟩)%S (at level 50, tid, ds at level 1, format "○Duty ( tid )  ds") : sProp_scope.

(* Auxiliary. *)
Notation "l '@1'" := (List.map fst l) (at level 50, format "l @1") : sProp_scope.


Section TRIPLE.

  Context {STT : StateTypes}.
  Context `{sub : @SRA.subG Γ Σ}.
  Context {TLRASs : TLRAs_small STT Γ}.
  Context {TLRAS : TLRAs STT Γ Σ}.

  Let srcE := threadE id_src_type st_src_type.
  Let tgtE := threadE id_tgt_type st_tgt_type.

  Import Atom.

  (* Definition syn_triple_gen *)
  (*            n tid (P : sProp n) {RV} (Q : RV -> sProp n) (E1 E2 : coPset) *)
  (*   : forall {R_src R_tgt : Type} (TERM : R_src -> R_tgt -> sProp n), bool -> bool -> itree srcE R_src -> itree tgtE RV -> ktree tgtE RV R_tgt -> sProp n *)
  (*   := *)
  (*   fun R_src R_tgt TERM ps pt itr_src code ktr_tgt => *)
  (*     ( *)
  (*       (* let N := (S n) in *) *)
  (*       let I0 := (fun ths ims imt sts stt => ((syn_default_I n ths ims imt sts stt) ∗ (⟨syn_wsat_auth n⟩ ∗ syn_wsats n ∗ syn_ownes n ∅))%S) *)
  (*      in *)
  (*      let I1 := (fun ths ims imt sts stt => ((syn_default_I_past tid n ths ims imt sts stt) ∗ (⟨syn_wsat_auth n⟩ ∗ syn_wsats n ∗ syn_ownes n ∅))%S) *)
  (*      in *)
  (*      let I2 := (fun ths im_src im_tgt st_src st_tgt E => (syn_default_I_past tid n ths im_src im_tgt st_src st_tgt ∗ (⟨syn_wsat_auth n⟩ ∗ syn_wsats n ∗ syn_ownes n E))) *)
  (*      in *)
  (*      Syntax.striple_format tid I0 I1 I2 P Q E1 E2 TERM ps pt itr_src code ktr_tgt)%S. *)

  Definition syn_term_cond n (tid : thread_id) (R_term : Type) : R_term -> R_term -> sProp n :=
    fun rs rt => ((⟨ow_ths tid⟩ ∗ ⟨obl_duty inlp tid []⟩) ∗ (⌜rs = rt⌝))%S.

  Lemma red_syn_term_cond n tid R_term :
    (fun (rs rt : R_term) => ⟦syn_term_cond n tid R_term rs rt, n⟧)
    =
      (term_cond n tid (R_term:=R_term)).
  Proof.
    extensionalities rs rt. unfold syn_term_cond. red_tl. unfold term_cond. f_equal.
  Qed.

  (* Definition syn_triple_gen *)
  (*            n tid (P : sProp (S n)) {RV} (Q : RV -> sProp (S n)) (E1 E2 : coPset) *)
  (*   : forall {R_term : Type}, bool -> bool -> itree srcE R_term -> itree tgtE RV -> ktree tgtE RV R_term -> sProp (S n) *)
  (*   := *)
  (*   fun R_term ps pt itr_src code ktr_tgt => *)
  (*     (let N := (S n) in *)
  (*       let I0 := (fun ths ims imt sts stt => ((syn_default_I N ths ims imt sts stt) ∗ (⟨syn_wsat_auth N⟩ ∗ syn_wsats N ∗ ⟨owne ⊤⟩))%S) *)
  (*      in *)
  (*      let I1 := (fun ths ims imt sts stt => ((syn_default_I_past tid N ths ims imt sts stt) ∗ (⟨syn_wsat_auth N⟩ ∗ syn_wsats N ∗ ⟨owne ⊤⟩))%S) *)
  (*      in *)
  (*      let I2 := (fun ths im_src im_tgt st_src st_tgt E => (syn_default_I_past tid N ths im_src im_tgt st_src st_tgt ∗ (⟨syn_wsat_auth N⟩ ∗ syn_wsats N ∗ ⟨owne E⟩))) *)
  (*      in *)
  (*      Syntax.striple_format tid I0 I1 I2 P Q E1 E2 (fun rs rt => ⤉ (syn_term_cond n tid R_term rs rt)) ps pt itr_src code ktr_tgt)%S. *)

  Definition syn_triple_gen
             n δ tid (P : sProp (S (δ + n))) {RV} (Q : RV -> sProp (S (δ + n))) (E1 E2 : coPset)
    : forall {R_term : Type}, bool -> bool -> itree srcE R_term -> itree tgtE RV -> ktree tgtE RV R_term -> sProp (S (δ + n))
    :=
    fun R_term ps pt itr_src code ktr_tgt =>
      (let N := (S (δ + n)) in
        let I0 := (fun ths ims imt sts stt => ((syn_default_I N ths ims imt sts stt) ∗ (⟨syn_wsat_auth N⟩ ∗ syn_wsats N ∗ ⟨owne ⊤⟩))%S)
       in
       let I1 := (fun ths ims imt sts stt => ((syn_default_I_past tid N ths ims imt sts stt) ∗ (⟨syn_wsat_auth N⟩ ∗ syn_wsats N ∗ ⟨owne ⊤⟩))%S)
       in
       let I2 := (fun ths im_src im_tgt st_src st_tgt E => (syn_default_I_past tid N ths im_src im_tgt st_src st_tgt ∗ (⟨syn_wsat_auth N⟩ ∗ syn_wsats N ∗ ⟨owne E⟩)))
       in
       Syntax.striple_format tid I0 I1 I2 P Q E1 E2 (fun rs rt => lifts (syn_term_cond n tid R_term rs rt) (S δ)) ps pt itr_src code ktr_tgt)%S.


  Lemma red_syn_triple_gen
        n δ tid (P : sProp (S (δ + n))) RV (Q : RV -> sProp (S (δ + n))) E1 E2
        R_term ps pt itr_src code (ktr_tgt : ktree tgtE RV R_term)
    :
    ⟦syn_triple_gen n δ tid P Q E1 E2 ps pt itr_src code ktr_tgt, S (δ + n)⟧
    =
      triple_gen (S (δ + n)) n tid ⟦P, S (δ + n)⟧ (fun rv => ⟦Q rv, S (δ + n)⟧) E1 E2 ps pt itr_src code ktr_tgt.
  Proof.
    unfold syn_triple_gen, triple_gen. red_tl. unfold triple_format.
    apply f_equal. extensionalities rr. apply f_equal. extensionalities gr.
    apply f_equal.
    match goal with
    | [ |- (?A -∗ _)%I = (?B -∗ _)%I] => replace A with B
    end.
    match goal with
    | [ |- (_ -∗ ?C)%I = (_ -∗ ?D)%I] => replace C with D
    end.
    auto.
    - unfold wpsim.
      apply f_equal. extensionalities ths.
      apply f_equal. extensionalities im_src. apply f_equal. extensionalities im_tgt.
      apply f_equal. extensionalities st_src. apply f_equal. extensionalities st_tgt.
      red_tl. simpl. red_tl. rewrite red_syn_default_I_past. rewrite red_syn_wsats.
      f_equal. f_equal.
      + symmetry. apply (red_isim_eq_1 (S (δ + n))).
      + apply (red_isim_eq_2 _ (S (δ + n))).
      + apply (red_isim_eq_2 _ (S (δ + n))).
      + symmetry.
        extensionalities r_src r_tgt ths1 im_src1 im_tgt1.
        extensionalities st_src1 st_tgt1.
        red_tl. rewrite red_syn_default_I_past. rewrite red_syn_wsats. rewrite red_lifts. ss.
    - apply f_equal. extensionalities rv. apply f_equal.
      unfold wpsim.
      apply f_equal. extensionalities ths.
      apply f_equal. extensionalities im_src. apply f_equal. extensionalities im_tgt.
      apply f_equal. extensionalities st_src. apply f_equal. extensionalities st_tgt.
      red_tl. simpl. red_tl. rewrite red_syn_default_I_past. rewrite red_syn_wsats.
      f_equal. f_equal.
      + symmetry. apply (red_isim_eq_1 (S (δ + n))).
      + apply (red_isim_eq_2 _ (S (δ + n))).
      + apply (red_isim_eq_2 _ (S (δ + n))).
      + symmetry.
        extensionalities r_src r_tgt ths1 im_src1 im_tgt1.
        extensionalities st_src1 st_tgt1.
        red_tl. rewrite red_syn_default_I_past. rewrite red_syn_wsats. rewrite red_lifts. ss.
  Qed.

  Definition syn_atomic_triple
             tid n δ (E : coPset)
             (P : sProp (S (δ + n))) {RV} (code : itree tgtE RV) (Q : RV -> sProp (S (δ + n)))
    : sProp (S (δ + n))
    :=
    (∀ (R_term : τ{metaT})
       (ps pt : τ{bool})
       (itr_src : τ{codeT id_src_type st_src_type R_term, S (δ + n)})
       (ktr_tgt : τ{(RV -> codeT id_tgt_type st_tgt_type R_term)%stype, S (δ + n)}),
        (syn_triple_gen n δ tid P Q E E ps pt itr_src code ktr_tgt))%S.

  Lemma red_syn_atomic_triple
        tid n δ (E : coPset)
        (P : sProp (S (δ + n))) RV (code : itree tgtE RV) (Q : RV -> sProp (S (δ + n)))
    :
    ⟦syn_atomic_triple tid n δ E P code Q, S (δ + n)⟧
    =
      atomic_triple tid (S (δ + n)) n E ⟦P, S (δ + n)⟧ code (fun v => ⟦Q v, S (δ + n)⟧).
  Proof.
    unfold syn_atomic_triple, atomic_triple. red_tl.
    apply f_equal. extensionalities R_term. red_tl.
    apply f_equal. extensionalities ps. red_tl.
    apply f_equal. extensionalities pt. red_tl.
    apply f_equal. extensionalities itr_src. red_tl.
    apply f_equal. extensionalities itr_tgt. red_tl.
    apply red_syn_triple_gen.
  Qed.

  Definition syn_non_atomic_triple
             tid n δ (E : coPset)
             (P : sProp (S (δ + n))) {RV} (code : itree tgtE RV) (Q : RV -> sProp (S (δ + n)))
    : sProp (S (δ + n))
    :=
    (∀ (R_term : τ{metaT})
       (ps pt : τ{bool})
       (itr_src : τ{codeT id_src_type st_src_type R_term})
       (ktr_tgt : τ{(RV -> codeT id_tgt_type st_tgt_type R_term)%stype, S (δ + n)}),
        (syn_triple_gen n δ tid P Q E ⊤ ps pt (trigger Yield;;; itr_src) code ktr_tgt))%S.

  Lemma red_syn_non_atomic_triple
        tid n δ (E : coPset)
        (P : sProp (S (δ + n))) RV (code : itree tgtE RV) (Q : RV -> sProp (S (δ + n)))
    :
    ⟦syn_non_atomic_triple tid n δ E P code Q, S (δ + n)⟧
    =
      non_atomic_triple tid (S (δ + n)) n E ⟦P, S (δ + n)⟧ code (fun v => ⟦Q v, S (δ + n)⟧).
  Proof.
    unfold syn_non_atomic_triple, non_atomic_triple. red_tl.
    apply f_equal. extensionalities R_term. red_tl.
    apply f_equal. extensionalities ps. red_tl.
    apply f_equal. extensionalities pt. red_tl.
    apply f_equal. extensionalities itr_src. red_tl.
    apply f_equal. extensionalities itr_tgt. red_tl.
    apply red_syn_triple_gen.
  Qed.

  (* Lemma red_syn_triple_gen *)
  (*       n tid (P : sProp (S n)) RV (Q : RV -> sProp (S n)) E1 E2 *)
  (*       R_term ps pt itr_src code (ktr_tgt : ktree tgtE RV R_term) *)
  (*   : *)
  (*   ⟦syn_triple_gen n tid P Q E1 E2 ps pt itr_src code ktr_tgt, S n⟧ *)
  (*   = *)
  (*     triple_gen (S n) n tid ⟦P, S n⟧ (fun rv => ⟦Q rv, S n⟧) E1 E2 ps pt itr_src code ktr_tgt. *)
  (* Proof. *)
  (*   unfold syn_triple_gen, triple_gen. red_tl. unfold triple_format. *)
  (*   apply f_equal. extensionalities rr. apply f_equal. extensionalities gr. *)
  (*   apply f_equal. *)
  (*   match goal with *)
  (*   | [ |- (?A -∗ _)%I = (?B -∗ _)%I] => replace A with B *)
  (*   end. *)
  (*   match goal with *)
  (*   | [ |- (_ -∗ ?C)%I = (_ -∗ ?D)%I] => replace C with D *)
  (*   end. *)
  (*   auto. *)
  (*   - unfold wpsim. *)
  (*     apply f_equal. extensionalities ths. *)
  (*     apply f_equal. extensionalities im_src. apply f_equal. extensionalities im_tgt. *)
  (*     apply f_equal. extensionalities st_src. apply f_equal. extensionalities st_tgt. *)
  (*     red_tl. simpl. red_tl. rewrite red_syn_default_I_past. rewrite red_syn_wsats. *)
  (*     f_equal. f_equal. *)
  (*     + symmetry. apply (red_isim_eq_1 (S n)). *)
  (*     + apply (red_isim_eq_2 _ (S n)). *)
  (*     + apply (red_isim_eq_2 _ (S n)). *)
  (*     + symmetry. *)
  (*       extensionalities r_src r_tgt ths1 im_src1 im_tgt1. *)
  (*       extensionalities st_src1 st_tgt1. *)
  (*       red_tl. rewrite red_syn_default_I_past. rewrite red_syn_wsats. ss. *)
  (*   - apply f_equal. extensionalities rv. apply f_equal. *)
  (*     unfold wpsim. *)
  (*     apply f_equal. extensionalities ths. *)
  (*     apply f_equal. extensionalities im_src. apply f_equal. extensionalities im_tgt. *)
  (*     apply f_equal. extensionalities st_src. apply f_equal. extensionalities st_tgt. *)
  (*     red_tl. simpl. red_tl. rewrite red_syn_default_I_past. rewrite red_syn_wsats. *)
  (*     f_equal. f_equal. *)
  (*     + symmetry. apply (red_isim_eq_1 (S n)). *)
  (*     + apply (red_isim_eq_2 _ (S n)). *)
  (*     + apply (red_isim_eq_2 _ (S n)). *)
  (*     + symmetry. *)
  (*       extensionalities r_src r_tgt ths1 im_src1 im_tgt1. *)
  (*       extensionalities st_src1 st_tgt1. *)
  (*       red_tl. rewrite red_syn_default_I_past. rewrite red_syn_wsats. ss. *)
  (* Qed. *)

  (* Definition syn_atomic_triple *)
  (*            tid n (E : coPset) *)
  (*            (P : sProp (S n)) {RV} (code : itree tgtE RV) (Q : RV -> sProp (S n)) *)
  (*   : sProp (S n) *)
  (*   := *)
  (*   (∀ (R_term : τ{metaT}) *)
  (*      (* (TERM : τ{(R_src -> R_tgt -> Φ)%stype, n}) *) *)
  (*      (ps pt : τ{bool}) *)
  (*      (itr_src : τ{codeT id_src_type st_src_type R_term, S n}) *)
  (*      (ktr_tgt : τ{(RV -> codeT id_tgt_type st_tgt_type R_term)%stype, S n}), *)
  (*       (syn_triple_gen n tid P Q E E ps pt itr_src code ktr_tgt))%S. *)

  (* Lemma red_syn_atomic_triple *)
  (*       tid n (E : coPset) *)
  (*       (P : sProp (S n)) RV (code : itree tgtE RV) (Q : RV -> sProp (S n)) *)
  (*   : *)
  (*   ⟦syn_atomic_triple tid n E P code Q, S n⟧ *)
  (*   = *)
  (*     atomic_triple tid n E ⟦P, S n⟧ code (fun v => ⟦Q v, S n⟧). *)
  (* Proof. *)
  (*   unfold syn_atomic_triple, atomic_triple. red_tl. *)
  (*   apply f_equal. extensionalities R_term. red_tl. *)
  (*   apply f_equal. extensionalities ps. red_tl. *)
  (*   apply f_equal. extensionalities pt. red_tl. *)
  (*   apply f_equal. extensionalities itr_src. red_tl. *)
  (*   apply f_equal. extensionalities itr_tgt. red_tl. *)
  (*   apply red_syn_triple_gen. *)
  (* Qed. *)

  (* Definition syn_non_atomic_triple *)
  (*            tid n (E : coPset) *)
  (*            (P : sProp (S n)) {RV} (code : itree tgtE RV) (Q : RV -> sProp (S n)) *)
  (*   : sProp (S n) *)
  (*   := *)
  (*   (∀ (R_term : τ{metaT}) *)
  (*      (ps pt : τ{bool}) *)
  (*      (itr_src : τ{codeT id_src_type st_src_type R_term}) *)
  (*      (ktr_tgt : τ{(RV -> codeT id_tgt_type st_tgt_type R_term)%stype, S n}), *)
  (*       (syn_triple_gen n tid P Q E ⊤ ps pt (trigger Yield;;; itr_src) code ktr_tgt))%S. *)

  (* Lemma red_syn_non_atomic_triple *)
  (*       tid n (E : coPset) *)
  (*       (P : sProp (S n)) RV (code : itree tgtE RV) (Q : RV -> sProp (S n)) *)
  (*   : *)
  (*   ⟦syn_non_atomic_triple tid n E P code Q, S n⟧ *)
  (*   = *)
  (*     non_atomic_triple tid n E ⟦P, S n⟧ code (fun v => ⟦Q v, S n⟧). *)
  (* Proof. *)
  (*   unfold syn_non_atomic_triple, non_atomic_triple. red_tl. *)
  (*   apply f_equal. extensionalities R_term. red_tl. *)
  (*   apply f_equal. extensionalities ps. red_tl. *)
  (*   apply f_equal. extensionalities pt. red_tl. *)
  (*   apply f_equal. extensionalities itr_src. red_tl. *)
  (*   apply f_equal. extensionalities itr_tgt. red_tl. *)
  (*   apply red_syn_triple_gen. *)
  (* Qed. *)

  (** LAT *)
  Section syn_atomic_update_def.

  (* TODO: ideally should be Tele *)
  Context {TA TB : Type}.
  Context (n : nat).
  Implicit Types
    (Eo Ei : coPset) (* outer/inner masks *)
    (α : TA → sProp (S n)) (* atomic pre-condition *)
    (β : TA → TB → sProp (S n)) (* atomic post-condition *)
    (POST : TA → TB → sProp (S n)) (* post-condition *)
  .

  (** atomic_update without abort, so no need for fixpoint *)
  Definition syn_atomic_update Eo Ei α β POST : sProp (S n) :=
    (=|S n|={Eo, Ei}=> ∃ x : τ{TA,S n}, α x ∗
          (∀ y : τ{TB,S n}, β x y =|S n|={Ei, Eo}=∗ POST x y))%S.
  (* TODO: Seal? *)
  End syn_atomic_update_def.

  Definition syn_LAT_ind {TA TB TP: Type}
             tid n (E : coPset)
             {RV : Type}
             (α: TA → sProp (S n)) (* atomic pre-condition *)
             (β: TA → TB → sProp (S n)) (* atomic post-condition *)
             (POST: TA → TB → TP → sProp (S n)) (* post-condition *)
             (f: TA → TB → TP → RV) (* Turn the return data into the return value *)
             (code : itree tgtE RV)
    : sProp (S n)
    :=
    (∀ (R_term : τ{metaT})
       (ps pt : τ{bool})
       (itr_src : τ{codeT id_src_type st_src_type R_term})
       (ktr_tgt : τ{(RV -> codeT id_tgt_type st_tgt_type R_term)%stype, S n}),
       syn_atomic_update n (⊤∖E) ∅ α β
       (λ (x : τ{TA,S n}) (y : τ{TB,S n}), ∀ (z : τ{TP,S n}), POST x y z -∗
       syn_wpsim (S n) tid ⊤ (fun rs rt => ⤉ (syn_term_cond n tid R_term rs rt)) ps true (trigger Yield;;; itr_src) (ktr_tgt (f x y z))
       )
       -∗
       syn_wpsim (S n) tid ⊤ (fun rs rt => ⤉ (syn_term_cond n tid R_term rs rt)) ps pt (trigger Yield;;; itr_src) (code >>= ktr_tgt))%S.

  Lemma red_syn_atomic_update TA TB
        n (Eo Ei : coPset)
        (α: TA → sProp (S n)) (* atomic pre-condition *)
        (β: TA → TB → sProp (S n)) (* atomic post-condition *)
        (POST: TA → TB → sProp (S n)) (* post-condition *)
    :
    ⟦syn_atomic_update n Eo Ei α β POST, S n⟧
    =
      (AU <{ ∃∃ x, ⟦α x, S n⟧ }> @ n, Eo, Ei <{ ∀∀ y, ⟦β x y, S n⟧, COMM ⟦POST x y, S n⟧}>)%I.
  Proof.
    unfold syn_atomic_update, atomic_update. red_tl.
    rewrite red_syn_fupd. red_tl.
    apply f_equal. f_equal. extensionalities x. red_tl.
    apply f_equal. f_equal. extensionalities y. red_tl.
    apply f_equal. rewrite red_syn_fupd. red_tl.
    done.
  Qed.

  Lemma red_syn_LAT_ind TA TB TP
        tid n (E : coPset)
        RV
        (α: TA → sProp (S n)) (* atomic pre-condition *)
        (β: TA → TB → sProp (S n)) (* atomic post-condition *)
        (POST: TA → TB → TP → sProp (S n)) (* post-condition *)
        (f: TA → TB → TP → RV) (* Turn the return data into the return value *)
        (code : itree tgtE RV)
    :
    ⟦syn_LAT_ind tid n E α β POST f code, S n⟧
    = (<<{ ∀∀ x, ⟦α x, S n⟧ }>>
        code @ tid,n,E
      <<{ ∃∃ y, ⟦β x y, S n⟧ | z, RET f x y z; ⟦POST x y z, S n⟧ }>>)%I.
  Proof.
    unfold syn_LAT_ind, LAT_ind. red_tl.
    apply f_equal. extensionalities R_term. red_tl.
    apply f_equal. extensionalities ps. red_tl.
    apply f_equal. extensionalities pt. red_tl.
    apply f_equal. extensionalities itr_src. red_tl.
    apply f_equal. extensionalities itr_tgt. red_tl.
    f_equal; last first.
    { rewrite red_syn_wpsim. done. }
    rewrite red_syn_atomic_update.
    apply f_equal. extensionalities x y. red_tl.
    apply f_equal. extensionalities z. red_tl.
    apply f_equal. rewrite red_syn_wpsim. done.
  Qed.

End TRIPLE.

(* Triples. *)
Notation "'[@' tid , n , E '@]' { P } code { v , Q }" :=
  (syn_atomic_triple tid n 0 E P code (fun v => Q))
    (at level 200, tid, n, E, P, code, v, Q at level 1,
      format "[@  tid ,  n ,  E  @] { P }  code  { v ,  Q }") : sProp_scope.

Notation "'[@' tid , n , δ , E '@]' { P } code { v , Q }" :=
  (syn_atomic_triple tid n δ E P code (fun v => Q))
    (at level 200, tid, n, δ, E, P, code, v, Q at level 1,
      format "[@  tid ,  n ,  δ ,  E  @] { P }  code  { v ,  Q }") : sProp_scope.

Notation "'[@' tid , n , E '@]' ⧼ P ⧽ code ⧼ v , Q ⧽" :=
  (syn_non_atomic_triple tid n 0 E P code (fun v => Q))
    (at level 200, tid, n, E, P, code, v, Q at level 1,
      format "[@  tid ,  n ,  E  @] ⧼ P ⧽  code  ⧼ v ,  Q ⧽") : sProp_scope.

Notation "'[@' tid , n , δ , E '@]' ⧼ P ⧽ code ⧼ v , Q ⧽" :=
  (syn_non_atomic_triple tid n δ E P code (fun v => Q))
    (at level 200, tid, n, δ, E, P, code, v, Q at level 1,
      format "[@  tid ,  n ,  δ ,  E  @] ⧼ P ⧽  code  ⧼ v ,  Q ⧽") : sProp_scope.

Notation "'<<{' ∀∀ x , α '}>>' e @ tid , n , E '<<{' ∃∃ y , β '|' z , 'RET' v ; POST '}>>'" :=
  (syn_LAT_ind tid n E
            (λ x, α%S)
            (λ x y, β%S)
            (λ x y z, POST%S)
            (λ x y z, v)
            e
  )
  (at level 20, E, β, α, v, POST at level 200, x binder, y binder, z binder,
   format "'[hv' '<<{'  '[' ∀∀  x ,  '/' α  ']' '}>>'  '/  ' e  @  tid , n , E  '/' '<<{'  '[' ∃∃  y ,  '/' β  '|'  '/' z ,  RET  v ;  '/' POST  ']' '}>>' ']'")
  : sProp_scope.

(** Notation: Atomic updates *)
(** We avoid '<<'/'>>' since those can also reasonably be infix operators
(and in fact Autosubst uses the latter). *)
Notation "'AU' '<{' ∃∃ x , α '}>' @ n , Eo , Ei '<{' ∀∀ y , β , 'COMM' POST '}>'" :=
  (* The way to read the [tele_app foo] here is that they convert the n-ary
  function [foo] into a unary function taking a telescope as the argument. *)
    (syn_atomic_update n Eo Ei
                   (λ x, α%S)
                   (λ x y, β%S)
                   (λ x y, POST%S)
    )
    (at level 20, Eo, Ei, α, β, POST at level 200, x binder, y binder,
     format "'[hv   ' 'AU'  '<{'  '[' ∃∃  x ,  '/' α  ']' '}>'  '/' @  '[' n ,  '/' Eo ,  '/' Ei ']'  '/' '<{'  '[' ∀∀  y ,  '/' β ,  '/' COMM  POST  ']' '}>' ']'") : sProp_scope.
