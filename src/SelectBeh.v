From sflib Require Import sflib.
From ITree Require Export ITree.
From Paco Require Import paco.
(* From Ordinal Require Import Ordinal. *)

Export ITreeNotations.

Require Import Coq.Classes.RelationClasses.

Require Import Lia.

From Fairness Require Import FairBeh.

Set Implicit Arguments.

Section RAWEVENT.
  Context {Ident: ID}.

  Variant silentE: Type :=
    | silentE_tau
    | silentE_fair (m: id -> Flag.t)
  .

  Definition rawE := (silentE + obsE)%type.

End RAWEVENT.

Module RawTr.
Section TR.
  Context {Ident: ID}.

  CoInductive t {R}: Type :=
  | done (retv: R)
  (* | spin *)
  | ub
  | nb
  | cons (hd: rawE) (tl: t)
  .

  Fixpoint app {R} (pre: list rawE) (bh: @t R): t :=
    match pre with
    | [] => bh
    | hd :: tl => cons hd (app tl bh)
    end
  .

  Lemma fold_app
        R s pre tl
    :
      (Tr.cons s (Tr.app pre tl)) = @Tr.app R (s :: pre) tl
  .
  Proof. reflexivity. Qed.

  Definition prefix {R} (pre: list rawE) (bh: @t R): Prop :=
    exists tl, <<PRE: app pre tl = bh>>
  .


  (** select fair trace with induction **)
  Variant _nofail_ind
          (nofail_ind: forall (R: Type) (i: id), (@t R) -> Prop)
          (R: Type) (i: id)
    :
    (@t R) -> Prop :=
    | nofail_ind_done
        retv
      :
      _nofail_ind nofail_ind i (done retv)
    (* | nofail_ind_spin *)
    (*   : *)
    (*   _nofail_ind nofail_ind i spin *)
    | nofail_ind_ub
      :
      _nofail_ind nofail_ind i ub
    | nofail_ind_nb
      :
      _nofail_ind nofail_ind i nb
    | nofail_ind_obs
        (obs: obsE) tl
        (TL: nofail_ind R i tl)
      :
      _nofail_ind nofail_ind i (cons (inr obs) tl)
    | nofail_ind_fair
        fmap tl
        (NOFAIL: Flag.le Flag.emp (fmap i))
        (TL: nofail_ind R i tl)
      :
      _nofail_ind nofail_ind i (cons (inl (silentE_fair fmap)) tl)
    | nofail_ind_tau
        tl
        (TL: nofail_ind R i tl)
      :
      _nofail_ind nofail_ind i (cons (inl silentE_tau) tl)
  .

  Definition nofail_ind: forall (R: Type) (i: id), (@t R) -> Prop := paco3 _nofail_ind bot3.

  Lemma nofail_ind_mon: monotone3 _nofail_ind.
  Proof.
    ii. inv IN; econs; eauto.
  Qed.


  Inductive _fair_ind
            (fair_ind: forall (R: Type) (i: id), (@t R) -> Prop)
            (R: Type) (i: id)
    :
    (@t R) -> Prop :=
  | fair_ind_nofail
      tr
      (NOFAIL: nofail_ind i tr)
    :
    _fair_ind fair_ind i tr
  | fair_ind_no_success
      fmap tl
      (NOSUCCESS: Flag.le (fmap i) Flag.emp)
      (TL: _fair_ind fair_ind i tl)
    :
    _fair_ind fair_ind i (cons (inl (silentE_fair fmap)) tl)
  | fair_ind_tau
      tl
      (TL: _fair_ind fair_ind i tl)
    :
    _fair_ind fair_ind i (cons (inl silentE_tau) tl)
  | fair_ind_obs
      (obs: obsE) tl
      (TL: _fair_ind fair_ind i tl)
    :
    _fair_ind fair_ind i (cons (inr obs) tl)
  | fair_ind_success
      fmap tl
      (SUCCESS: Flag.le Flag.success (fmap i))
      (TL: fair_ind R i tl)
    :
    _fair_ind fair_ind i (cons (inl (silentE_fair fmap)) tl)
  .

  Definition fair_ind: forall (R: Type) (i: id), (@t R) -> Prop := paco3 _fair_ind bot3.

  Lemma fair_ind_ind
        (r: forall (R: Type) (i: id), t -> Prop) R i (P: t -> Prop)
        (NOFAIL: forall tr (NOFAIL: nofail_ind i tr), P tr)
        (NOSUCCESS: forall fmap tl
                      (NOSUCCESS: Flag.le (fmap i) Flag.emp)
                      (TL: _fair_ind r i tl)
                      (IH: P tl),
            P (cons (inl (silentE_fair fmap)) tl))
        (TAU: forall tl
                (TL: _fair_ind r i tl)
                (IH: P tl),
            P (cons (inl silentE_tau) tl))
        (OBS: forall obs tl
                (TL: _fair_ind r i tl)
                (IH: P tl),
            P (cons (inr obs) tl))
        (SUCCESS: forall fmap tl
                    (SUCCESS: Flag.le Flag.success (fmap i))
                    (TL: r R i tl),
            P (cons (inl (silentE_fair fmap)) tl))
    :
    forall tr, _fair_ind r i tr -> P tr.
  Proof.
    fix IH 2. i.
    inv H; eauto.
  Qed.

  Lemma fair_ind_mon: monotone3 _fair_ind.
  Proof.
    ii. induction IN using fair_ind_ind; eauto.
    - econs 1. eauto.
    - econs 2; eauto.
    - econs 3; eauto.
    - econs 4; eauto.
    - econs 5; eauto.
  Qed.

  Definition is_fair_ind {R} (tr: @t R) := forall i, fair_ind i tr.


  (** select fair trace with well-founded order **)
  (* Context {WFOrd: WFO}. *)

  Variant _fair_ord
          (fair_ord: forall (R: Type) (m: imap), (@t R) -> Prop)
          (R: Type) (m: imap)
    :
    (@t R) -> Prop :=
    | fair_ord_done
        retv
      :
      _fair_ord fair_ord m (done retv)
    (* | nofail_ind_spin *)
    (*   : *)
    (*   _nofail_ind nofail_ind i spin *)
    | fair_ord_ub
      :
      _fair_ord fair_ord m ub
    | fair_ord_nb
      :
      _fair_ord fair_ord m nb
    | fair_ord_obs
        (obs: obsE) tl
        (TL: fair_ord R m tl)
      :
      _fair_ord fair_ord m (cons (inr obs) tl)
    | fair_ord_fair
        fmap tl m0
        (FAIR: fair_update m m0 fmap)
        (TL: fair_ord R m0 tl)
      :
      _fair_ord fair_ord m (cons (inl (silentE_fair fmap)) tl)
    | fair_ord_tau
        tl
        (TL: fair_ord R m tl)
      :
      _fair_ord fair_ord m (cons (inl silentE_tau) tl)
  .

  Definition fair_ord: forall (R: Type) (m: imap), (@t R) -> Prop := paco3 _fair_ord bot3.

  Lemma fair_ord_mon: monotone3 _fair_ord.
  Proof.
    ii. inv IN; econs; eauto.
  Qed.

  Definition is_fair_ord {R} (tr: @t R) := exists m, fair_ord m tr.

End TR.
End RawTr.
#[export] Hint Constructors RawTr._nofail_ind.
#[export] Hint Unfold RawTr.nofail_ind.
#[export] Hint Resolve RawTr.nofail_ind_mon: paco.
#[export] Hint Constructors RawTr._fair_ind.
#[export] Hint Unfold RawTr.fair_ind.
#[export] Hint Resolve RawTr.fair_ind_mon: paco.
#[export] Hint Constructors RawTr._fair_ord.
#[export] Hint Unfold RawTr.fair_ord.
#[export] Hint Resolve RawTr.fair_ord_mon: paco.
#[export] Hint Resolve cpn3_wcompat: paco.


Module RawBeh.
Section BEHAVES.

  Context {Ident: ID}.

  Definition t {R}: Type := @RawTr.t _ R -> Prop.
  Definition improves {R} (src tgt: @t R): Prop := tgt <1= src.

  (* Variant _diverge *)
  (*         (diverge: forall (R: Type) (itr: @state _ R), Prop) *)
  (*         (R: Type) *)
  (*   : *)
  (*   forall (itr: @state _ R), Prop := *)
  (*   | diverge_tau *)
  (*       itr *)
  (*       (DIV: diverge _ itr) *)
  (*     : *)
  (*     _diverge diverge (Tau itr) *)
  (*   | diverge_choose *)
  (*       X ktr x *)
  (*       (DIV: diverge _ (ktr x)) *)
  (*     : *)
  (*     _diverge diverge (Vis (Choose X) ktr) *)
  (*   | diverge_ub *)
  (*       ktr *)
  (*     : *)
  (*     _diverge diverge (Vis Undefined ktr) *)
  (* . *)

  (* Lemma diverge_mon: monotone2 _diverge. *)
  (* Proof. *)
  (*   ii. inv IN. *)
  (*   - econs 1; eauto. *)
  (*   - econs 2; eauto. *)
  (*   - econs 3; eauto. *)
  (* Qed. *)

  (* Definition diverge: forall (R: Type) (itr: state), Prop := paco2 _diverge bot2. *)

  (* Hint Constructors _diverge. *)
  (* Hint Unfold diverge. *)
  (* Hint Resolve diverge_mon: paco. *)
  (* Hint Resolve cpn2_wcompat: paco. *)



  Variant _of_state
            (of_state: forall (R: Type), (@state _ R) -> (@RawTr.t _ R) -> Prop)
            (R: Type)
    :
    (@state _ R) -> RawTr.t -> Prop :=
  | done
      retv
    :
    _of_state of_state (Ret retv) (RawTr.done retv)
  (* | spin *)
  (*     st0 *)
  (*     (SPIN: diverge st0) *)
  (*   : *)
  (*   _of_state of_state st0 (RawTr.spin) *)
  | nb
      st0
    :
    _of_state of_state st0 (RawTr.nb)
  | obs
      fn args rv ktr tl
      (TL: of_state _ (ktr rv) tl)
    :
    _of_state of_state (Vis (Observe fn args) ktr) (RawTr.cons (inr (obsE_syscall fn args rv)) tl)

  | tau
      itr tl
      (TL: of_state _ itr tl)
    :
    _of_state of_state (Tau itr) (RawTr.cons (inl silentE_tau) tl)
  | choose
      X ktr x tl
      (TL: of_state _ (ktr x) tl)
    :
    _of_state of_state (Vis (Choose X) ktr) (RawTr.cons (inl silentE_tau) tl)
  | fair
      fmap ktr tl
      (TL: of_state _ (ktr tt) tl)
    :
    _of_state of_state (Vis (Fair fmap) ktr) (RawTr.cons (inl (silentE_fair fmap)) tl)

  | ub
      ktr tr
    :
    _of_state of_state (Vis Undefined ktr) tr
  .

  Definition of_state: forall (R: Type), state -> RawTr.t -> Prop := paco3 _of_state bot3.

  Lemma of_state_mon: monotone3 _of_state.
  Proof.
    ii. inv IN; econs; eauto.
  Qed.

  Hint Constructors _of_state.
  Hint Unfold of_state.
  Hint Resolve of_state_mon: paco.
  Hint Resolve cpn3_wcompat: paco.

  Definition of_state_fair_ind {R} (st: @state _ R) (raw_tr: @RawTr.t _ R) :=
    (<<BEH: of_state st raw_tr>>) /\ (<<FAIR: RawTr.is_fair_ind raw_tr>>).

  Definition of_state_fair_ord {R} (st: @state _ R) (raw_tr: @RawTr.t _ R) :=
    (<<BEH: of_state st raw_tr>>) /\ (<<FAIR: RawTr.is_fair_ord raw_tr>>).



  (**********************************************************)
  (*********************** properties ***********************)
  (**********************************************************)

  Lemma prefix_closed_state
        R st0 pre bh
        (BEH: of_state st0 bh)
        (PRE: RawTr.prefix pre bh)
    :
    <<NB: @of_state R st0 (RawTr.app pre RawTr.nb)>>
  .
  Proof.
    revert_until Ident. pcofix CIH. i. punfold BEH. rr in PRE. des; subst.
    destruct pre; ss; clarify.
    { pfold. econs. }
    remember (RawTr.cons r0 (RawTr.app pre tl)) as tmp. revert Heqtmp.
    inv BEH; ii; ss; clarify.
    - pclearbot. pfold. econs; eauto. right. eapply CIH; eauto. rr; eauto.
    - pclearbot. pfold. econs 4; eauto. right. eapply CIH; eauto. rr; eauto.
    - pclearbot. pfold. econs 5; eauto. right. eapply CIH; eauto. rr; eauto.
    - pclearbot. pfold. econs 6; eauto. right. eapply CIH; eauto. rr; eauto.
    - pclearbot. pfold. econs 7; eauto.
  Qed.

  (* Theorem prefix_closed *)
  (*         pre bh *)
  (*         (BEH: of_program bh) *)
  (*         (PRE: Tr.prefix pre bh) *)
  (*   : *)
  (*   <<NB: of_program (Tr.app pre Tr.nb)>> *)
  (* . *)
  (* Proof. *)
  (*   eapply prefix_closed_state; eauto. *)
  (* Qed. *)

  Lemma nb_bottom
        R st0
    :
    <<NB: @of_state R st0 RawTr.nb>>
  .
  Proof. pfold. econs; eauto. Qed.

  Lemma ub_top
        R st0
        (UB: @of_state R st0 RawTr.ub)
    :
    forall beh, of_state st0 beh
  .
  Proof.
    pfold. i. punfold UB.
    remember RawTr.ub as tmp. inv UB; ss; clarify.
  Qed.

End BEHAVES.
End RawBeh.
#[export] Hint Unfold RawBeh.improves.
#[export] Hint Constructors RawBeh._of_state.
#[export] Hint Unfold RawBeh.of_state.
#[export] Hint Resolve RawBeh.of_state_mon: paco.
#[export] Hint Resolve cpn3_wcompat: paco.
