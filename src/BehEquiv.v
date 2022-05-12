From sflib Require Import sflib.
From ITree Require Export ITree.
From Paco Require Import paco.

Export ITreeNotations.

Require Import Coq.Classes.RelationClasses.

From Fairness Require Import FairBeh.
From Fairness Require Import SelectBeh.

From Fairness Require Import Axioms.

Set Implicit Arguments.

Section MATCHTR.

  Context {Ident: ID}.

  Variant _raw_spin
          (raw_spin: forall (R: Type), RawTr.t -> Prop)
          R
    :
    (@RawTr.t _ R) -> Prop :=
    | raw_spin_silent
        (silent: silentE) tl
        (TL: raw_spin _ tl)
      :
      _raw_spin raw_spin (RawTr.cons (inl silent) tl)
    (* | raw_spin_ub *)
    (*   : *)
    (*   _raw_spin raw_spin (RawTr.ub) *)
  .

  Definition raw_spin: forall (R: Type), RawTr.t -> Prop := paco2 _raw_spin bot2.

  Lemma raw_spin_mon: monotone2 _raw_spin.
  Proof.
    ii. inv IN.
    - econs; eauto.
      (* - econs; eauto. *)
  Qed.


  Inductive _match_tr
            (match_tr: forall (R: Type), RawTr.t -> Tr.t -> Prop)
            R
    :
    (@RawTr.t _ R) -> Tr.t -> Prop :=
  | match_tr_done
      retv
    :
    _match_tr match_tr (RawTr.done retv) (Tr.done retv)
  | match_tr_spin
      raw
      (RSPIN: raw_spin raw)
    :
    _match_tr match_tr raw (Tr.spin)
  | match_tr_ub
    :
    _match_tr match_tr (RawTr.ub) (Tr.ub)
  | match_tr_nb
    :
    _match_tr match_tr (RawTr.nb) (Tr.nb)
  | match_tr_obs
      (obs: obsE) raw_tl tr_tl
      (TL: match_tr _ raw_tl tr_tl)
    :
    _match_tr match_tr (RawTr.cons (inr obs) raw_tl) (Tr.cons obs tr_tl)
  | match_tr_silent
      (silent: silentE) raw_tl tr_tl
      (TL: _match_tr match_tr raw_tl tr_tl)
    :
    _match_tr match_tr (RawTr.cons (inl silent) raw_tl) tr_tl
  .

  Definition match_tr: forall (R: Type), RawTr.t -> Tr.t -> Prop := paco3 _match_tr bot3.

  Lemma match_tr_ind
        (match_tr : forall R : Type, RawTr.t -> Tr.t -> Prop) (R : Type) (P: RawTr.t -> Tr.t -> Prop)
        (DONE: forall retv : R, P (RawTr.done retv) (Tr.done retv))
        (SPIN: forall (raw : RawTr.t) (RSPIN: raw_spin raw), P raw Tr.spin)
        (UB: P RawTr.ub Tr.ub)
        (NB: P RawTr.nb Tr.nb)
        (OBS: forall (obs : obsE) (raw_tl : RawTr.t) (tr_tl : Tr.t) (TL: match_tr R raw_tl tr_tl),
            P (RawTr.cons (inr obs) raw_tl) (Tr.cons obs tr_tl))
        (SILENT: forall (silent : silentE) (raw_tl : RawTr.t) (tr_tl : Tr.t)
                   (STEP: _match_tr match_tr raw_tl tr_tl) (IH: P raw_tl tr_tl),
            P (RawTr.cons (inl silent) raw_tl) tr_tl)
    :
    forall raw_tr tr, (_match_tr match_tr raw_tr tr) -> P raw_tr tr.
  Proof.
    fix IH 3; i.
    inv H; eauto.
  Qed.

  Lemma match_tr_mon: monotone3 _match_tr.
  Proof.
    ii. induction IN using match_tr_ind; econs; eauto.
  Qed.

  Hint Constructors _match_tr.
  Hint Unfold match_tr.
  Hint Resolve match_tr_mon: paco.
  Hint Resolve cpn3_wcompat: paco.

End MATCHTR.
#[export] Hint Constructors _raw_spin.
#[export] Hint Unfold raw_spin.
#[export] Hint Resolve raw_spin_mon: paco.
#[export] Hint Resolve cpn2_wcompat: paco.
#[export] Hint Constructors _match_tr.
#[export] Hint Unfold match_tr.
#[export] Hint Resolve match_tr_mon: paco.
#[export] Hint Resolve cpn3_wcompat: paco.



Section ConvertTR.

  Context {Ident: ID}.

  Lemma inhabited_tr R: inhabited (Tr.t (R:=R)).
  Proof.
    econs. exact Tr.ub.
  Qed.

  Lemma inhabited_raw R: inhabited (RawTr.t (R:=R)).
  Proof.
    econs. exact RawTr.ub.
  Qed.

  Definition Raw2Tr {R} (raw: @RawTr.t _ R): (@Tr.t R) :=
    epsilon _ (@inhabited_tr R) (match_tr raw).

  Definition Tr2Raw {R} (tr: @Tr.t R): (@RawTr.t _ R) :=
    epsilon _ (@inhabited_raw R) (fun raw => match_tr raw tr).

End ConvertTR.
