From iris.algebra Require Import cmra.
From stdpp Require Import coPset gmap namespaces.
From sflib Require Import sflib.
From Fairness Require Import PCM IProp IPM IndexedInvariants.
From Fairness Require Import SimWeakest.
From iris Require Import bi.big_op.
From iris Require base_logic.lib.invariants.
From Coq Require Import Program Arith.

Module SRA.

  Section SRA.

    Class t := SRA__INTERNAL : GRA.t.

    Class subG (Γ : t) (Σ : GRA.t) : Type := {
        subG_map : nat -> nat;
        subG_prf : forall i, (GRA.gra_map Σ) (subG_map i) = (GRA.gra_map Γ) i;
      }.

    Coercion subG_map : subG >-> Funclass.

  End SRA.

  Section SUB.

    Context `{sub : @subG Γ Σ}.

    Global Program Instance embed (i : nat) : @GRA.inG ((GRA.gra_map Γ) i) Σ := {
        inG_id := sub i;
      }.
    Next Obligation. i. symmetry. apply SRA.subG_prf. Qed.

    Global Program Instance in_subG `{M : ucmra} `{emb : @GRA.inG M Γ} : @GRA.inG M Σ := {
        inG_id := sub.(subG_map) emb.(GRA.inG_id);
      }.
    Next Obligation.
      destruct emb. subst. destruct sub. ss.
    Qed.

  End SUB.

End SRA.

Coercion SRA.subG_map: SRA.subG >-> Funclass.

Module sType.

  Class t : Type := mk {
                       car: Type;
                       interp: car -> forall sProp: Type, Type;
                     }.

End sType.

Coercion sType.car: sType.t >-> Sortclass.

Module sAtom.

  Class t: Type := car : forall (sProp: Type), Type.

End sAtom.

Local Notation index := nat.

Module Syntax.

  Section SYNTAX.

    Context `{τ : sType.t}.
    Context `{Γ : SRA.t}.
    Context `{A : Type}.

    Inductive t {form : Type} : Type :=
    | atom (a : A) : t
    | ownm (i : nat) (r : (GRA.gra_map Γ i)) : t
    | lift (p : form) : t
    | sepconj (p q : t) : t
    | pure (P : Prop) : t
    | univ (ty : τ) (p : τ.(sType.interp) ty form -> t) : t
    | ex   (ty : τ) (p : τ.(sType.interp) ty form -> t) : t
    | and (p q : t) : t
    | or (p q : t) : t
    | impl (p q : t) : t
    | wand (p q : t) : t
    | empty : t
    | persistently (p : t) : t
    | plainly (p : t) : t
    | upd (p : t) : t
    | sisim {state_src state_tgt ident_src ident_tgt : Type}
            (tid : thread_id)
            (I0 : TIdSet.t -> (@FairBeh.imap ident_src owf) -> (@FairBeh.imap (nat + ident_tgt) nat_wf) -> state_src -> state_tgt -> t)
            (I1 : TIdSet.t -> (@FairBeh.imap ident_src owf) -> (@FairBeh.imap (nat + ident_tgt) nat_wf) -> state_src -> state_tgt -> t)
            {R_src R_tgt : Type}
            (Q : R_src -> R_tgt -> t)
            (ps pt : bool)
            (itr_src : itree (threadE ident_src state_src) R_src)
            (itr_tgt : itree (threadE ident_tgt state_tgt) R_tgt)
            (ths : TIdSet.t)
            (ims : @FairBeh.imap ident_src owf)
            (imt : @FairBeh.imap (nat + ident_tgt) nat_wf)
            (sts : state_src)
            (stt : state_tgt)
    | striple_format {STT : StateTypes}
                     (tid : thread_id)
                     (I0 : TIdSet.t -> (@FairBeh.imap id_src_type owf) -> (@FairBeh.imap (nat + id_tgt_type) nat_wf) -> st_src_type -> st_tgt_type -> t)
                     (I1 : TIdSet.t -> (@FairBeh.imap id_src_type owf) -> (@FairBeh.imap (nat + id_tgt_type) nat_wf) -> st_src_type -> st_tgt_type -> t)
                     (I1 : TIdSet.t -> (@FairBeh.imap id_src_type owf) -> (@FairBeh.imap (nat + id_tgt_type) nat_wf) -> st_src_type -> st_tgt_type -> coPset -> t)
                     (P : t)
                     {RV : Type}
                     (Q : RV -> t)
                     (E1 E2 : coPset)
                     {R_src R_tgt : Type}
                     (TERM : R_src -> R_tgt -> t)
                     (ps pt : bool)
                     (itr_src : itree (threadE id_src_type st_src_type) R_src)
                     (code : itree (threadE id_tgt_type st_tgt_type) RV)
                     (ktr_tgt : ktree (threadE id_tgt_type st_tgt_type) RV R_tgt)
    .

  End SYNTAX.

  Section SPROP.

    Context `{τ : sType.t}.
    Context `{Γ : SRA.t}.
    Context `{As : sAtom.t}.

    Fixpoint _sProp (n : index) : Type :=
      match n with
      | O => Empty_set
      | S m => @t τ Γ (As (_sProp m)) (_sProp m)
      end.

    Definition sProp (n : index) : Type := _sProp (S n).

    Definition affinely {n} (p : sProp n) : sProp n :=
      and empty p.

    Definition ownM `{IN: @GRA.inG M Γ} {n} (r : M) : sProp n :=
      ownm IN.(GRA.inG_id) (eq_rect _ ucmra_car r _ IN.(GRA.inG_prf)).

  End SPROP.

End Syntax.

Module sAtomI.

  Section SATOM.

  Context `{τ : sType.t}.
  Context `{Γ : SRA.t}.
  Context `{As : sAtom.t}.
  Context `{Σ : GRA.t}.
  Notation iProp := (iProp Σ).

  Class t : Type := interp :
      forall (n : index), As (Syntax._sProp n) -> iProp.

  End SATOM.

End sAtomI.

Module SyntaxI.

  Section INTERP.

    Context `{Γ : SRA.t}.
    Context `{Σ : GRA.t}.
    Context `{sub: @SRA.subG Γ Σ}.
    Context `{α: sAtomI.t (Γ:=Γ) (Σ:=Σ)}.
    Notation iProp := (iProp Σ).

    Import Syntax.

    Fixpoint _interp n : _sProp n -> iProp :=
      match n with
      | O => fun _ => ⌜False⌝%I
      | S m =>
          fix _interp_aux (syn : _sProp (S m)) : iProp :=
        match syn with
        | atom a => α m a
        | ownm i r => OwnM r
        | lift p => _interp m p
        | sepconj p q => Sepconj (_interp_aux p) (_interp_aux q)
        | pure P => Pure P
        | univ ty p => Univ (fun (x : τ.(sType.interp) ty (_sProp m)) => _interp_aux (p x))
        | ex ty p => Ex (fun (x : τ.(sType.interp) ty (_sProp m)) => _interp_aux (p x))
        | and p q => And (_interp_aux p) (_interp_aux q)
        | or p q => Or (_interp_aux p) (_interp_aux q)
        | impl p q => Impl (_interp_aux p) (_interp_aux q)
        | wand p q => Wand (_interp_aux p) (_interp_aux q)
        | empty => Emp
        | persistently p => Persistently (_interp_aux p)
        | plainly p => IProp.Plainly (_interp_aux p)
        | upd p => Upd (_interp_aux p)
        | sisim tid I0 I1 Q ps pt itr_src itr_tgt ths ims imt sts stt =>
            isim_simple tid (intpF:=_interp_aux)
                        I0 I1 Q
                        ps pt itr_src itr_tgt ths ims imt sts stt
        | @striple_format _ _ _ _ STT tid I0 I1 I2 P RV Q E1 E2 RS RT TERM ps pt itr_src code ktr_tgt =>
            @triple_format
              Σ STT _ (_interp_aux)
              tid I0 I1 I2 P RV Q E1 E2 RS RT TERM
              ps pt itr_src code ktr_tgt
        end
      end.

    Definition interp n : sProp n -> iProp := _interp (S n).

  End INTERP.

End SyntaxI.

Section RED.

  Context `{sub: @SRA.subG Γ Σ}.
  Context `{α: sAtomI.t (Γ:=Γ) (Σ:=Σ)}.

  Import Syntax.
  Import SyntaxI.

  Lemma red_sem_atom n a :
    interp n (atom a) = α n a.
  Proof. reflexivity. Qed.

  Lemma red_sem_ownm n i a :
    interp n (ownm i a) = OwnM a.
  Proof. reflexivity. Qed.

  Lemma red_sem_ownM `{@GRA.inG M Γ} n (r: M) :
    interp n (ownM r) = OwnM r.
  Proof.
    unfold ownM. rewrite red_sem_ownm.
    destruct sub eqn: EQsub. subst. destruct H. subst. ss.
    f_equal. unfold SRA.in_subG, SRA.embed. ss.
    erewrite (UIP _ _ _ (SRA.embed_obligation_1 inG_id)).
    reflexivity.
  Qed.

  Lemma red_sem_lift_0 p :
    interp 0 (lift p) = ⌜False⌝%I.
  Proof. reflexivity. Qed.

  Lemma red_sem_lift n p :
    interp (S n) (lift p) = interp n p.
  Proof. reflexivity. Qed.

  Lemma red_sem_sepconj n p q :
    interp n (sepconj p q) = (interp n p ∗ interp n q)%I.
  Proof. reflexivity. Qed.

  Lemma red_sem_pure n P :
    interp n (pure P) = ⌜P⌝%I.
  Proof. reflexivity. Qed.

  Lemma red_sem_univ n ty p :
    interp n (univ ty p) = (∀ x, interp n (p x))%I.
  Proof. reflexivity. Qed.

  Lemma red_sem_ex n ty p :
    interp n (ex ty p) = (∃ x, interp n (p x))%I.
  Proof. reflexivity. Qed.

  Lemma red_sem_and n p q :
    interp n (and p q) = (interp n p ∧ interp n q)%I.
  Proof. reflexivity. Qed.

  Lemma red_sem_or n p q :
    interp n (or p q) = (interp n p ∨ interp n q)%I.
  Proof. reflexivity. Qed.

  Lemma red_sem_impl n p q :
    interp n (impl p q) = (interp n p → interp n q)%I.
  Proof. reflexivity. Qed.

  Lemma red_sem_wand n p q :
    interp n (wand p q) = (interp n p -∗ interp n q)%I.
  Proof. reflexivity. Qed.

  Lemma red_sem_empty n :
    interp n empty = emp%I.
  Proof. reflexivity. Qed.

  Lemma red_sem_persistently n p :
    interp n (persistently p) = (<pers> interp n p)%I.
  Proof. reflexivity. Qed.

  Lemma red_sem_plainly n p :
    interp n (plainly p) = (IProp.Plainly (interp n p))%I.
  Proof. reflexivity. Qed.

  Lemma red_sem_upd n p :
    interp n (upd p) = ( |==> interp n p)%I.
  Proof. reflexivity. Qed.

  Lemma red_sem_affinely n p :
    interp n (affinely p) = (<affine> interp n p)%I.
  Proof. reflexivity. Qed.

  Lemma red_sem_intuitionistically n p :
    interp n (affinely (persistently p)) = (□ interp n p)%I.
  Proof. reflexivity. Qed.

  Lemma red_sem_sisim n
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
    interp n (Syntax.sisim tid I0 I1 Q ps pt itr_src itr_tgt ths ims imt sts stt)
    = (isim_simple tid (intpF:=interp n) I0 I1 Q ps pt itr_src itr_tgt ths ims imt sts stt)%I.
  Proof. reflexivity. Qed.

  Lemma red_sem_striple_format n
        (STT : StateTypes)
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
    interp n (Syntax.striple_format tid I0 I1 I2 P Q E1 E2 TERM ps pt itr_src code ktr_tgt)
    =
      (triple_format (intpF:=interp n) tid
                     I0 I1 I2 P Q E1 E2 TERM
                     ps pt itr_src code ktr_tgt)%I.
  Proof. reflexivity. Qed.

End RED.
Global Opaque SyntaxI._interp SyntaxI.interp.

(** Simple sProp reduction tactics. *)
Ltac red_sem_binary_once := (try rewrite ! @red_sem_sepconj;
                            try rewrite ! @red_sem_and;
                            try rewrite ! @red_sem_or;
                            try rewrite ! @red_sem_impl;
                            try rewrite ! @red_sem_wand
                           ).

Ltac red_sem_unary_once := (
                           try rewrite ! @red_sem_atom;
                           try rewrite ! @red_sem_ownm;
                           try rewrite ! @red_sem_ownM;
                           try rewrite ! @red_sem_lift;
                           try rewrite ! @red_sem_pure;
                           try rewrite ! @red_sem_univ;
                           try rewrite ! @red_sem_ex;
                           try rewrite ! @red_sem_empty;
                           try rewrite ! @red_sem_persistently;
                           try rewrite ! @red_sem_plainly;
                           try rewrite ! @red_sem_upd;
                           try rewrite ! @red_sem_affinely;
                           try rewrite ! @red_sem_intuitionistically;
                           try rewrite ! @red_sem_sisim;
                           try rewrite ! @red_sem_striple_format
                          ).

Ltac red_sem_binary := repeat red_sem_binary_once.
Ltac red_sem_unary := repeat red_sem_unary_once.
Ltac red_sem := repeat (red_sem_binary; red_sem_unary).

Ltac red_sem_binary_once_every := (try rewrite ! @red_sem_sepconj in *;
                                  try rewrite ! @red_sem_and in *;
                                  try rewrite ! @red_sem_or in *;
                                  try rewrite ! @red_sem_impl in *;
                                  try rewrite ! @red_sem_wand in *
                                  ).

Ltac red_sem_unary_once_every := (
                                  try rewrite ! @red_sem_atom in *;
                                  try rewrite ! @red_sem_ownm in *;
                                  try rewrite ! @red_sem_ownM in *;
                                  try rewrite ! @red_sem_lift in *;
                                  try rewrite ! @red_sem_pure in *;
                                  try rewrite ! @red_sem_univ in *;
                                  try rewrite ! @red_sem_ex in *;
                                  try rewrite ! @red_sem_empty in *;
                                  try rewrite ! @red_sem_persistently in *;
                                  try rewrite ! @red_sem_plainly in *;
                                  try rewrite ! @red_sem_upd in *;
                                  try rewrite ! @red_sem_affinely in *;
                                  try rewrite ! @red_sem_intuitionistically in *;
                                  try rewrite ! @red_sem_sisim in *;
                                  try rewrite ! @red_sem_striple_format in *
                                ).

Ltac red_sem_binary_every := repeat red_sem_binary_once.
Ltac red_sem_unary_every := repeat red_sem_unary_once.
Ltac red_sem_every := repeat (red_sem_binary_every; red_sem_unary_every).

(** Notations *)

Declare Scope sProp_scope.
Delimit Scope sProp_scope with S.
Bind Scope sProp_scope with Syntax.sProp.

Local Open Scope sProp_scope.

Notation "'⌜' P '⌝'" := (Syntax.pure P) : sProp_scope.

Notation "'⟨' A '⟩'" := (Syntax.atom A) : sProp_scope.
Notation "'➢' r" := (Syntax.ownM r) (at level 20) : sProp_scope.
Notation "⤉ P" := (Syntax.lift P) (at level 20) : sProp_scope.

Notation "'<pers>' P" := (Syntax.persistently P) : sProp_scope.
Notation "'<affine>' P" := (Syntax.affinely P) : sProp_scope.
Notation "□ P" := (<affine> <pers> P) : sProp_scope.
Notation "■ P" := (Syntax.plainly P) : sProp_scope.
Notation "|==> P" := (Syntax.upd P) : sProp_scope.
Infix "∧" := (Syntax.and) : sProp_scope.
Infix "∨" := (Syntax.or) : sProp_scope.
Infix "→" := (Syntax.impl) : sProp_scope.
Notation "¬ P" := (P → False) : sProp_scope.
Infix "∗" := (Syntax.sepconj) : sProp_scope.
Infix "-∗" := (Syntax.wand) : sProp_scope.
Notation "P ==∗ Q" := (P -∗ |==> Q) : sProp_scope.
Notation f_forall A := (Syntax.univ A).
Notation "∀'" := (f_forall _) (only parsing) : sProp_scope.
Notation "∀ a .. z , P" := (f_forall _ (λ a, .. (f_forall _ (λ z, P%S)) ..)) : sProp_scope.
Notation f_exist A := (Syntax.ex A).
Notation "∃'" := (f_exist _) (only parsing) : sProp_scope.
Notation "∃ a .. z , P" := (f_exist _ (λ a, .. (f_exist _ (λ z, P%S)) ..)) : sProp_scope.
Notation "'emp'" := (Syntax.empty) : sProp_scope.
