From stdpp Require Import coPset gmap namespaces.
From sflib Require Import sflib.
From Fairness Require Import PCM IProp IPM IndexedInvariants.
From Fairness Require Import ISim SimDefaultRA SimWeakest.
From Fairness Require Import LogicSyntaxHOAS.
From iris Require Import bi.big_op.
From iris Require base_logic.lib.invariants.
Require Import Program.

Local Notation index := nat.

Section TYPES.

  Section TYPE.

    Inductive type : Type :=
    | baseT (t : Type) : type
    | formulaT : type
    | funT : type -> type -> type
    | listT : type -> type
    | pgmapT : type -> type.

  End TYPE.

  Section INTERP_TYPE.

    Fixpoint Typ (form : Type) (ty : type) : Type :=
      match ty with
      | baseT b => b
      | formulaT => form
      | funT ty1 ty2 => (Typ form ty1 -> Typ form ty2)
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
             (n : index) K {H1 : EqDecision K} {H2 : Countable K}
             A (I : @gmap K H1 H2 (Typ (Formula n) A))
             (f : K -> (Typ (Formula n) A) -> Formula n)
    : Formula n :=
    fold_right (fun hd tl => @sepconj _ Typ (As (_Formula n)) (_Formula n) (uncurry f hd) tl) empty (map_to_list I).

  Lemma red_syn_big_sepM n K {H1 : EqDecision K} {H2 : Countable K} A I f :
    Sem n (syn_big_sepM n K A I f) = ([∗ map] i ↦ a ∈ I, Sem n (f i a))%I.
  Proof.
    ss. unfold big_opM. rewrite seal_eq. unfold big_op.big_opM_def.
    unfold syn_big_sepM. simpl. remember (map_to_list I) as L.
    clear HeqL I. induction L.
    { ss. }
    ss. rewrite @red_sem_sepconj. rewrite IHL. f_equal.
    destruct a. ss.
  Qed.

  Definition syn_big_sepL1
             (n : index) A (I : Typ (Formula n) (listT A))
             (f : (Typ (Formula n) A) -> Formula n)
    : Formula n :=
    fold_right (fun hd tl => @sepconj _ Typ (As (_Formula n)) (_Formula n) (f hd) tl) empty I.

  Lemma red_syn_big_sepL1 n A I f :
    Sem n (syn_big_sepL1 n A I f) = ([∗ list] a ∈ I, Sem n (f a))%I.
  Proof.
    ss. induction I; ss.
    rewrite @red_sem_sepconj. rewrite IHI. f_equal.
  Qed.

End BIGOP.

Section SIMPLEATOM.

  Class SimpleAtom := { sAtom : Type }.

  Context `{Σ : GRA.t}.

  Class SAInterp {SA : SimpleAtom} := { saintp : @sAtom SA -> iProp }.

End SIMPLEATOM.

Section STATE.

  Class StateTypes :=
    { state_src_type : Type
    ; state_tgt_type : Type
    ; ident_src_type : ID
    ; ident_tgt_type : ID}.

End STATE.

Module Atom.

  Section ATOM.

    Context {SA : SimpleAtom}.
    Context {STT : StateTypes}.

    Local Notation state_src := (@state_src_type STT).
    Local Notation state_tgt := (@state_tgt_type STT).
    Local Notation ident_src := (@ident_src_type STT).
    Local Notation ident_tgt := (@ident_tgt_type STT).

    Inductive t {form : Type} : Type :=
    (** Simple atoms. *)
    | satom (s : @sAtom SA)
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
    .

  End ATOM.

  Section INTERP.

    Context {SA : SimpleAtom}.
    Context {STT : StateTypes}.

    Local Notation state_src := (@state_src_type STT).
    Local Notation state_tgt := (@state_tgt_type STT).
    Local Notation ident_src := (@ident_src_type STT).
    Local Notation ident_tgt := (@ident_tgt_type STT).

    Local Notation att := (@t SA STT).
    Local Notation _Formula := (@_formula (@att)).
    Local Notation Formula := (@formula (@att)).

    Context `{Σ : GRA.t}.
    Context `{SAI : @SAInterp Σ SA}.
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
    Context `{ARROWRA: @GRA.inG (@ArrowRA ident_tgt Vars) Σ}.

    Definition to_semantics n (a : @t SA STT (_Formula n)) : iProp :=
      match a with
      (** Simple atoms. *)
      | satom s => saintp s
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
          OwnM (Auth.black (Excl.just (Some st_src): @Excl.t (option state_src)) : stateSrcRA _)
      | ow_st_src st_src =>
          St_src st_src
      | ob_st_tgt st_tgt =>
          OwnM (Auth.black (Excl.just (Some st_tgt): @Excl.t (option state_tgt)): stateTgtRA _)
      | ow_st_tgt st_tgt =>
          St_tgt st_tgt
      | fair_src im_src =>
          FairRA.sat_source im_src
      | fair_tgt im_tgt ths =>
          FairRA.sat_target im_tgt ths
      end.

  End INTERP.

End Atom.

Section TL.

  Context {SA : SimpleAtom}.
  Context {STT : StateTypes}.
  Local Notation state_src := (@state_src_type STT).
  Local Notation state_tgt := (@state_tgt_type STT).
  Local Notation ident_src := (@ident_src_type STT).
  Local Notation ident_tgt := (@ident_tgt_type STT).

  Definition _Formula := (@_formula (@Atom.t SA STT)).
  Definition Formula := (@formula (@Atom.t SA STT)).

  Context `{Σ : GRA.t}.
  Context `{SAI : @SAInterp Σ SA}.
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
  Context `{ARROWRA: @GRA.inG (@ArrowRA ident_tgt Vars) Σ}.

  Definition AtomSem := (@Atom.to_semantics SA STT Σ SAI _ _ _ _ _ _ _ _).
  Definition SynSem n := (@formula_sem (@Atom.t SA STT) Σ (@AtomSem) n).

  Global Instance SynIISet : @IInvSet Σ Formula :=
    (@Syntax.IISet _ _ _ Σ AtomSem).

  (* Global Instance IIIn (i : index) (p : Formula i) : @IInvIn Σ Formula SynIISet i (SynSem i p) := *)
  (*   @Syntax.IIIn _ _ _ Σ AtomSem0 AtomSem i p. *)

End TL.

(** Notations and coercions. *)
Coercion baseT : Sortclass >-> type.
Notation "'τ{' t ',' n '}'" := (@Typ (@_Formula _ _ n) t).
Notation "'⟪' A ',' n '⟫'" := (AtomSem n A).
Notation "'⟦' F ',' n '⟧'" := (SynSem n F).



Section RED.

  Context {SA : SimpleAtom}.
  Context {STT : StateTypes}.
  Local Notation state_src := (@state_src_type STT).
  Local Notation state_tgt := (@state_tgt_type STT).
  Local Notation ident_src := (@ident_src_type STT).
  Local Notation ident_tgt := (@ident_tgt_type STT).

  Context `{Σ : GRA.t}.
  Context `{SAI : @SAInterp Σ SA}.
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
  Context `{ARROWRA: @GRA.inG (@ArrowRA ident_tgt Vars) Σ}.

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
    ⟦(∀ x, p x)%F, n⟧ = (∀ (x : τ{ty, n}), ⟦p x, n⟧)%I.
  Proof. apply red_sem_univ. Qed.

  Lemma red_tl_ex n ty p :
    ⟦(∃ x, p x)%F, n⟧ = (∃ (x : τ{ty, n}), ⟦p x, n⟧)%I.
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
    ⟦(□ p)%F, n⟧ = (<pers> ⟦p, n⟧)%I.
  Proof. apply red_sem_persistently. Qed.

  Lemma red_tl_plainly n p :
    ⟦(■ p)%F, n⟧ = (IProp.Plainly ⟦p, n⟧)%I.
  Proof. apply red_sem_plainly. Qed.

  Lemma red_tl_upd n p :
    ⟦( |==> p)%F, n⟧ = ( |==> ⟦p, n⟧)%I.
  Proof. apply red_sem_upd. Qed.

  Lemma red_tl_big_sepM n A K {EQ : EqDecision K} {CNT : Countable K} I f :
    ⟦@syn_big_sepM (@Atom.t _ _) n K _ _ A I f, n⟧ = ([∗ map] i ↦ p ∈ I, ⟦f i p, n⟧)%I.
  Proof. apply red_syn_big_sepM. Qed.

  Lemma red_tl_big_sepL1 n A I f :
    ⟦@syn_big_sepL1 (@Atom.t _ _) n A I f, n⟧ = ([∗ list] a ∈ I, ⟦f a, n⟧)%I.
  Proof. apply red_syn_big_sepL1. Qed.

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
                           try rewrite ! @red_tl_upd
                          ).

Ltac red_tl_binary := repeat red_tl_binary_once.
Ltac red_tl_unary := repeat red_tl_unary_once.
Ltac red_tl := repeat (red_tl_binary; red_tl_unary).


Section WSATS.

  Context {SA : SimpleAtom}.
  Context {STT : StateTypes}.
  Local Notation state_src := (@state_src_type STT).
  Local Notation state_tgt := (@state_tgt_type STT).
  Local Notation ident_src := (@ident_src_type STT).
  Local Notation ident_tgt := (@ident_tgt_type STT).

  Context `{Σ : GRA.t}.
  Context `{SAI : @SAInterp Σ SA}.
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
  Context `{ARROWRA: @GRA.inG (@ArrowRA ident_tgt Vars) Σ}.


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
    syn_big_sepM n positive formulaT ps (syn_inv_satall_fun n).

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
    (∃ (I : τ{pgmapT formulaT, (S n)}), ↑(⟨syn_inv_auth n I⟩ ∗ (syn_inv_satall n I)))%F.

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

  Fixpoint syn_wsats n : Formula n :=
    match n with
    | O => emp%F
    | S m => ((↑(syn_wsats m)) ∗ (syn_wsat m))%F
    end.

  Lemma unfold_syn_wsats n :
    syn_wsats (S n) = (↑(syn_wsats n) ∗ (syn_wsat n))%F.
  Proof. ss. Qed.

  Lemma syn_wsats_to_wsats n :
    ⟦syn_wsats n, n⟧ ⊢ wsats n.
  Proof.
    induction n; ss. red_tl. iIntros "[A B]".
    iApply fold_wsats. rewrite red_syn_wsat. iFrame. iApply IHn. iFrame.
  Qed.

  Lemma wsats_to_syn_wsats n :
    wsats n ⊢ ⟦syn_wsats n, n⟧.
  Proof.
    induction n; ss. red_tl. iIntros "A".
    iPoseProof (unfold_wsats with "A") as "[A B]". rewrite red_syn_wsat. iFrame.
    iApply IHn. iFrame.
  Qed.

  (** Definitions for OwnEs. *)

  Definition syn_owne_satall_fun x : index -> coPset -> (Formula x) :=
    fun n E => ⟨owne n E⟩%F.

  Definition syn_owne_satall x (Es : coPsets) : Formula x :=
    syn_big_sepM x index coPset Es (syn_owne_satall_fun x).

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
    (∃ (i : τ{positive, n}), ⌜i ∈ (nclose N : coPset)⌝ ∧ ⟨owni i p⟩)%F.

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


Section TEST.

  Context {SA : SimpleAtom}.
  Context {STT : StateTypes}.
  Local Notation state_src := (@state_src_type STT).
  Local Notation state_tgt := (@state_tgt_type STT).
  Local Notation ident_src := (@ident_src_type STT).
  Local Notation ident_tgt := (@ident_tgt_type STT).

  Context `{Σ : GRA.t}.
  Context `{SAI : @SAInterp Σ SA}.
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
  Context `{ARROWRA: @GRA.inG (@ArrowRA ident_tgt Vars) Σ}.

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
