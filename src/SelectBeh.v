From sflib Require Import sflib.
From ITree Require Export ITree.
From Paco Require Import paco.

Export ITreeNotations.

Require Import Coq.Classes.RelationClasses.

Require Import Lia.

From Fairness Require Import FairBeh.

Set Implicit Arguments.

Section FAIR.
  Context {Ident: ID}.

  Variant fairE: Type :=
    | fairE_fair (m: id -> Flag.t)
  .

  Definition fairO := (fairE + obsE)%type.

End FAIR.

Module RawTr.
Section TR.
  Context {Ident: ID}.

  CoInductive t {R}: Type :=
  | done (retv: R)
  | spin
  | ub
  | nb
  | cons (hd: fairO) (tl: t)
  .

  Fixpoint app {R} (pre: list fairO) (bh: @t R): t :=
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

  Definition prefix {R} (pre: list fairO) (bh: @t R): Prop :=
    exists tl, <<PRE: app pre tl = bh>>
  .

  Variant _nofail_id
          (nofail_id: forall (R: Type) (i: id), (@t R) -> Prop)
          (R: Type) (i: id)
    :
    (@t R) -> Prop :=
    | nofail_id_done
        retv
      :
      _nofail_id nofail_id i (done retv)
    | nofail_id_spin
      :
      _nofail_id nofail_id i spin
    | nofail_id_ub
      :
      _nofail_id nofail_id i ub
    | nofail_id_nb
      :
      _nofail_id nofail_id i nb
    | nofail_id_obs
        (obs: obsE) tl
        (TL: nofail_id R i tl)
      :
      _nofail_id nofail_id i (cons (inr obs) tl)
    | nofail_id_fair
        fmap tl
        (NOFAIL: Flag.le Flag.emp (fmap i))
        (TL: nofail_id R i tl)
      :
      _nofail_id nofail_id i (cons (inl (fairE_fair fmap)) tl)
  .

  Definition nofail_id: forall (R: Type) (i: id), (@t R) -> Prop := paco3 _nofail_id bot3.

  Lemma nofail_id_mon: monotone3 _nofail_id.
  Proof.
    ii. inv IN; econs; eauto.
  Qed.


  Inductive _fair_id
            (fair_id: forall (R: Type) (i: id), (@t R) -> Prop)
            (R: Type) (i: id)
    :
    (@t R) -> Prop :=
  | fair_id_nofail
      tr
      (NOFAIL: nofail_id i tr)
    :
    _fair_id fair_id i tr
  | fair_id_no_success
      fmap tl
      (NOSUCCESS: Flag.le (fmap i) Flag.emp)
      (TL: _fair_id fair_id i tl)
    :
    _fair_id fair_id i (cons (inl (fairE_fair fmap)) tl)
  | fair_id_obs
      (obs: obsE) tl
      (TL: _fair_id fair_id i tl)
    :
    _fair_id fair_id i (cons (inr obs) tl)
  | fair_id_success
      fmap tl
      (SUCCESS: Flag.le Flag.success (fmap i))
      (TL: fair_id R i tl)
    :
    _fair_id fair_id i (cons (inl (fairE_fair fmap)) tl)
  .

  Definition fair_id: forall (R: Type) (i: id), (@t R) -> Prop := paco3 _fair_id bot3.

  Lemma fair_id_ind
        (r: forall (R: Type) (i: id), t -> Prop) R i (P: t -> Prop)
        (NOFAIL: forall tr (NOFAIL: nofail_id i tr), P tr)
        (NOSUCCESS: forall fmap tl
                      (NOSUCCESS: Flag.le (fmap i) Flag.emp)
                      (FAIRID: _fair_id r i tl)
                      (IH: P tl),
            P (cons (inl (fairE_fair fmap)) tl))
        (OBS: forall obs tl
                (FAIRID: _fair_id r i tl)
                (IH: P tl),
            P (cons (inr obs) tl))
        (SUCCESS: forall fmap tl
                    (SUCCESS: Flag.le Flag.success (fmap i))
                    (FAIRID: r R i tl),
            P (cons (inl (fairE_fair fmap)) tl))
    :
    forall tr, _fair_id r i tr -> P tr.
  Proof.
    fix IH 2. i.
    inv H; eauto.
  Qed.

  Lemma fair_id_mon: monotone3 _fair_id.
  Proof.
    ii. induction IN using fair_id_ind; eauto.
    - econs 1. eauto.
    - econs 2; eauto.
    - econs 3; eauto.
    - econs 4; eauto.
  Qed.

  Definition is_fair {R} (tr: @t R) := forall i, fair_id i tr.

End TR.
End RawTr.
#[export] Hint Constructors RawTr._nofail_id.
#[export] Hint Unfold RawTr.nofail_id.
#[export] Hint Resolve RawTr.nofail_id_mon: paco.
#[export] Hint Resolve cpn3_wcompat: paco.
#[export] Hint Constructors RawTr._fair_id.
#[export] Hint Unfold RawTr.fair_id.
#[export] Hint Resolve RawTr.fair_id_mon: paco.



Module RawBeh.
Section BEHAVES.

  Context {Ident: ID}.

  Definition t {R}: Type := @RawTr.t _ R -> Prop.
  Definition improves {R} (src tgt: @t R): Prop := tgt <1= src.

  Variant _diverge
          (diverge: forall (R: Type) (itr: @state _ R), Prop)
          (R: Type)
    :
    forall (itr: @state _ R), Prop :=
    | diverge_tau
        itr
        (DIV: diverge _ itr)
      :
      _diverge diverge (Tau itr)
    | diverge_choose
        X ktr x
        (DIV: diverge _ (ktr x))
      :
      _diverge diverge (Vis (Choose X) ktr)
    | diverge_ub
        ktr
      :
      _diverge diverge (Vis Undefined ktr)
  .

  Lemma diverge_mon: monotone2 _diverge.
  Proof.
    ii. inv IN.
    - econs 1; eauto.
    - econs 2; eauto.
    - econs 3; eauto.
  Qed.

  Definition diverge: forall (R: Type) (itr: state), Prop := paco2 _diverge bot2.

  Hint Constructors _diverge.
  Hint Unfold diverge.
  Hint Resolve diverge_mon: paco.
  Hint Resolve cpn2_wcompat: paco.



  Inductive _of_state
            (of_state: forall (R: Type), (@state _ R) -> (@RawTr.t _ R) -> Prop)
            (R: Type)
    :
    (@state _ R) -> RawTr.t -> Prop :=
  | done
      retv
    :
    _of_state of_state (Ret retv) (RawTr.done retv)
  | spin
      st0
      (SPIN: diverge st0)
    :
    _of_state of_state st0 (RawTr.spin)
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
      itr tr
      (STEP: _of_state of_state itr tr)
    :
    _of_state of_state (Tau itr) tr
  | choose
      X ktr x tr
      (STEP: _of_state of_state (ktr x) tr)
    :
    _of_state of_state (Vis (Choose X) ktr) tr

  | fair
      fmap ktr tl
      (TL: of_state _ (ktr tt) tl)
    :
    _of_state of_state (Vis (Fair fmap) ktr) (RawTr.cons (inl (fairE_fair fmap)) tl)

  | ub
      ktr tr
    :
    _of_state of_state (Vis Undefined ktr) tr
  .

  Definition of_state: forall (R: Type), state -> RawTr.t -> Prop := paco3 _of_state bot3.

  Theorem of_state_ind:
    forall (r: forall (R: Type), state -> RawTr.t -> Prop) R (P: state -> RawTr.t -> Prop),
      (forall retv, P (Ret retv) (RawTr.done retv)) ->
      (forall st0, diverge st0 -> P st0 RawTr.spin) ->
      (forall st0, P st0 RawTr.nb) ->
      (forall fn args rv ktr tl
         (TL: r _ (ktr rv) tl)
        ,
          P (Vis (Observe fn args) ktr) (RawTr.cons (inr (obsE_syscall fn args rv)) tl)) ->
      (forall itr tr
         (STEP: _of_state r itr tr)
         (IH: P itr tr)
        ,
          P (Tau itr) tr) ->
      (forall X ktr x tr
         (STEP: _of_state r (ktr x) tr)
         (IH: P (ktr x) tr)
        ,
          P (Vis (Choose X) ktr) tr) ->
      (forall fmap ktr tl
         (TL: r _ (ktr tt) tl)
        ,
          P (Vis (Fair fmap) ktr) (RawTr.cons (inl (fairE_fair fmap)) tl)) ->
      (forall ktr tr, P (Vis Undefined ktr) tr) ->
      forall s t, @_of_state r R s t -> P s t.
  Proof.
    fix IH 14. i.
    inv H7; eauto.
    - eapply H3; eauto. eapply IH; eauto.
    - eapply H4; eauto. eapply IH; eauto.
  Qed.

  Lemma of_state_mon: monotone3 _of_state.
  Proof.
    ii. induction IN using of_state_ind; eauto.
    - econs 1; eauto.
    - econs 2; eauto.
    - econs 3; eauto.
    - econs 4; eauto.
    - econs 5; eauto.
    - econs 6; eauto.
    - econs 7; eauto.
    - econs 8; eauto.
  Qed.

  Hint Constructors _of_state.
  Hint Unfold of_state.
  Hint Resolve of_state_mon: paco.
  Hint Resolve cpn3_wcompat: paco.

  Definition of_state_fair {R} (st: @state _ R) (raw_tr: @RawTr.t _ R) :=
    (<<BEH: of_state st raw_tr>>) /\ (<<FAIR: RawTr.is_fair raw_tr>>).

  (****************************************************)
  (*********************** upto ***********************)
  (****************************************************)

  Variant of_state_indC
          (of_state: forall R, (@state _ R) -> (@RawTr.t _ R) -> Prop)
          R
    :
    (@state _ R) -> (@RawTr.t _ R) -> Prop :=
  | of_state_indC_done
      retv
    :
    of_state_indC of_state (Ret retv) (RawTr.done retv)
  | of_state_indC_spin
      st0
      (SPIN: diverge st0)
    :
    of_state_indC of_state st0 (RawTr.spin)
  | of_state_indC_nb
      st0
    :
    of_state_indC of_state st0 (RawTr.nb)
  | of_state_indC_obs
      fn args rv ktr tl
      (TL: of_state _ (ktr rv) tl)
    :
    of_state_indC of_state (Vis (Observe fn args) ktr) (RawTr.cons (inr (obsE_syscall fn args rv)) tl)

  | of_state_indC_tau
      itr tr
      (STEP: of_state _ itr tr)
    :
    of_state_indC of_state (Tau itr) tr
  | of_state_indC_choose
      X ktr x tr
      (STEP: of_state _ (ktr x) tr)
    :
    of_state_indC of_state (Vis (Choose X) ktr) tr
  | of_state_indC_fair
      fmap ktr tl
      (TL: of_state _ (ktr tt) tl)
    :
    of_state_indC of_state (Vis (Fair fmap) ktr) (RawTr.cons (inl (fairE_fair fmap)) tl)

  | of_state_indC_ub
      ktr tr
    :
    of_state_indC of_state (Vis Undefined ktr) tr
  .

  Lemma of_state_indC_mon: monotone3 of_state_indC.
  Proof. ii. inv IN; econs; eauto. Qed.

  Hint Resolve of_state_indC_mon: paco.

  Lemma of_state_indC_wrespectful: wrespectful3 _of_state of_state_indC.
  Proof.
    econs; eauto with paco.
    i. inv PR; eauto.
    { econs; eauto. eapply rclo3_base. eauto. }
    { econs; eauto. eapply of_state_mon; eauto. i. eapply rclo3_base. auto. }
    { econs; eauto. eapply of_state_mon; eauto. i. eapply rclo3_base. auto. }
    { econs; eauto. eapply rclo3_base. eauto. }
  Qed.

  Lemma of_state_indC_spec: of_state_indC <4= gupaco3 _of_state (cpn3 _of_state).
  Proof. i. eapply wrespect3_uclo; eauto with paco. eapply of_state_indC_wrespectful. Qed.



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
    remember (RawTr.cons f (RawTr.app pre tl)) as tmp. revert Heqtmp.
    induction BEH using of_state_ind; ii; ss; clarify.
    - pclearbot. pfold. econs; eauto. right. eapply CIH; eauto. rr; eauto.
    - pfold. econs 5; eauto. hexploit IHBEH; eauto. intro A. punfold A.
    - pfold. econs 6; eauto. hexploit IHBEH; eauto. intro A. punfold A.
    - pfold. econs 7; eauto. right. eapply CIH. pclearbot. eapply TL. rr; eauto.
    - pfold. econs 8; eauto.
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
    remember RawTr.ub as tmp. revert Heqtmp.
    induction UB using of_state_ind; ii; ss; clarify.
    - econs; eauto.
    - econs 6; eauto.
  Qed.

  Lemma beh_tau
        R itr tr
        (BEH: @of_state R itr tr)
    :
    <<BEH: of_state (Tau itr) tr>>
  .
  Proof.
    ginit. guclo of_state_indC_spec. econs; eauto. gfinal. eauto.
  Qed.

  Lemma beh_choose
        R X ktr x tr
        (BEH: @of_state R (ktr x) tr)
    :
    <<BEH: of_state (Vis (Choose X) ktr) tr>>
  .
  Proof.
    ginit. guclo of_state_indC_spec. econs; eauto. gfinal. eauto.
  Qed.

End BEHAVES.
End RawBeh.
#[export] Hint Unfold RawBeh.improves.
#[export] Hint Constructors RawBeh._diverge.
#[export] Hint Unfold RawBeh.diverge.
#[export] Hint Resolve RawBeh.diverge_mon: paco.
#[export] Hint Constructors RawBeh._of_state.
#[export] Hint Unfold RawBeh.of_state.
#[export] Hint Resolve RawBeh.of_state_mon: paco.

#[export] Hint Resolve cpn2_wcompat: paco.
#[export] Hint Resolve cpn3_wcompat: paco.


Section AUX.

  Context {Ident: ID}.

  Theorem of_state_ind2:
    forall R (P: state -> RawTr.t -> Prop),
      (forall retv, P (Ret retv) (RawTr.done retv)) ->
      (forall st0, RawBeh.diverge st0 -> P st0 RawTr.spin) ->
      (forall st0, P st0 RawTr.nb) ->
      (forall fn args rv ktr tl
         (TL: RawBeh.of_state (ktr rv) tl)
        ,
          P (Vis (Observe fn args) ktr) (RawTr.cons (inr (obsE_syscall fn args rv)) tl)) ->
      (forall itr tr
         (STEP: RawBeh.of_state itr tr)
         (IH: P itr tr)
        ,
          P (Tau itr) tr) ->
      (forall X ktr x tr
         (STEP: RawBeh.of_state (ktr x) tr)
         (IH: P (ktr x) tr)
        ,
          P (Vis (Choose X) ktr) tr) ->
      (forall fmap ktr tl
         (TL: RawBeh.of_state (ktr tt) tl)
        ,
          P (Vis (Fair fmap) ktr) (RawTr.cons (inl (fairE_fair fmap)) tl)) ->
      (forall ktr tr, P (Vis Undefined ktr) tr) ->
      forall s t, (@RawBeh.of_state _ R s t) -> P s t.
  Proof.
    i. eapply RawBeh.of_state_ind; eauto.
    { i. eapply H3; eauto. pfold. eapply RawBeh.of_state_mon; eauto. }
    { i. eapply H4; eauto. pfold. eapply RawBeh.of_state_mon; eauto. }
    { punfold H7. eapply RawBeh.of_state_mon; eauto. i. pclearbot. eauto. }
  Qed.

End AUX.
