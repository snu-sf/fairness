From sflib Require Import sflib.
From ITree Require Export ITree.
From Paco Require Import paco.

Export ITreeNotations.

Require Import Coq.Classes.RelationClasses.

From Fairness Require Import FairBeh.
From Fairness Require Import SelectBeh.

From Fairness Require Import Axioms.

Set Implicit Arguments.

Section ConvertTR.

  Context {Ident: ID}.

  (* Variant _match_tr *)
  (*         (match_tr: forall (R: Type), RawTr.t -> Tr.t -> Prop) *)
  (*         R *)
  (*   : *)
  (*   (@RawTr.t _ R) -> Tr.t -> Prop := *)
  (*   | match_tr_done *)
  (*       retv *)
  (*     : *)
  (*     _match_tr match_tr (RawTr.done retv) (Tr.done retv) *)
  (*   | match_tr_spin *)
  (*     : *)
  (*     _match_tr match_tr (RawTr.spin) (Tr.spin) *)
  (*   | match_tr_ub *)
  (*     : *)
  (*     _match_tr match_tr (RawTr.ub) (Tr.ub) *)
  (*   | match_tr_nb *)
  (*     : *)
  (*     _match_tr match_tr (RawTr.nb) (Tr.nb) *)
  (*   | match_tr_obs *)
  (*       (obs: obsE) raw_tl tr_tl *)
  (*       (TL: match_tr _ raw_tl tr_tl) *)
  (*     : *)
  (*     _match_tr match_tr (RawTr.cons (inr obs) raw_tl) (Tr.cons obs tr_tl) *)
  (*   | match_tr_fair *)
  (*       (fair: fairE) raw_tl tr_tl *)
  (*       (TL: match_tr _ raw_tl tr_tl) *)
  (*     : *)
  (*     _match_tr match_tr (RawTr.cons (inl fair) raw_tl) tr_tl *)
  (* . *)

  (* Definition match_tr: forall (R: Type), RawTr.t -> Tr.t -> Prop := paco3 _match_tr bot3. *)

  (* Lemma match_tr_mon: monotone3 _match_tr. *)
  (* Proof. *)
  (*   ii. inv IN. *)
  (*   - econs; eauto. *)
  (*   - econs; eauto. *)
  (*   - econs; eauto. *)
  (*   - econs; eauto. *)
  (*   - econs; eauto. *)
  (*   - econs; eauto. *)
  (* Qed. *)

  (* Hint Constructors _match_tr. *)
  (* Hint Unfold match_tr. *)
  (* Hint Resolve match_tr_mon: paco. *)
  (* Hint Resolve cpn3_wcompat: paco. *)

End ConvertTR.

(* #[export] Hint Constructors _match_tr. *)
(* #[export] Hint Unfold match_tr. *)
(* #[export] Hint Resolve match_tr_mon: paco. *)
(* #[export] Hint Resolve cpn3_wcompat: paco. *)
