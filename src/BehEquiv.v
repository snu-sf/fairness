From sflib Require Import sflib.
From ITree Require Export ITree.
From Paco Require Import paco.

Export ITreeNotations.

Require Import Coq.Classes.RelationClasses.

From Fairness Require Import FairBeh.
From Fairness Require Import SelectBeh.

From Fairness Require Import Axioms.

Set Implicit Arguments.

Section MatchTr.

  Context {Ident: ID}.

  (** match between raw_tr and tr *)
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

End MatchTr.
#[export] Hint Constructors _raw_spin.
#[export] Hint Unfold raw_spin.
#[export] Hint Resolve raw_spin_mon: paco.
#[export] Hint Resolve cpn2_wcompat: paco.
#[export] Hint Constructors _match_tr.
#[export] Hint Unfold match_tr.
#[export] Hint Resolve match_tr_mon: paco.
#[export] Hint Resolve cpn3_wcompat: paco.



Section ExtractTr.

  Context {Ident: ID}.

  Lemma inhabited_tr R: inhabited (Tr.t (R:=R)).
  Proof.
    econs. exact Tr.ub.
  Qed.

  Lemma inhabited_raw R: inhabited (RawTr.t (R:=R)).
  Proof.
    econs. exact RawTr.ub.
  Qed.

  Definition raw2tr {R} (raw: @RawTr.t _ R): (@Tr.t R) :=
    epsilon _ (@inhabited_tr R) (match_tr raw).

  Lemma raw2tr_cons_obs
        R (raw: RawTr.t (R:=R))
        (obs: obsE)
    :
    raw2tr (RawTr.cons (inr obs) raw) = Tr.cons obs (raw2tr raw).
  Proof.
    unfold raw2tr at 1. unfold epsilon. unfold Epsilon.epsilon. unfold proj1_sig. des_ifs.
    
    unfold raw2tr. unfold epsilon. unfold Epsilon.epsilon. unfold proj1_sig. des_ifs.
    

  Lemma raw2tr_prop
        R (raw: RawTr.t (R:=R))
    :
    match_tr raw (raw2tr raw).
  Proof.
    revert raw. pcofix CIH. i.


    unfold raw2tr. eapply Epsilon.epsilon_spec.

    
    unfold raw2tr. unfold epsilon. unfold Epsilon.epsilon. unfold proj1_sig. des_ifs.
    rename x into tr, m into EPS.
    eapply sig_ind. i. eapply EPS. exists x. eapply p.
    eapply Epsilon.constructive_indefinite_description.
    econs.


    clear Heq.
    revert_until R. pcofix CIH. i.
    

    revert raw. pcofix CIH. i.
    destruct raw.
    4:{ destruct hd.
        2:{ 



    destruct (raw2tr raw) eqn:EQ.
    5:{ unfold raw2tr in EQ. unfold epsilon in EQ. unfold Epsilon.epsilon in EQ.
        unfold proj1_sig in EQ. des_ifs. unfold exist in Heq.

    unfold raw2tr. unfold epsilon. unfold Epsilon.epsilon. unfold proj1_sig. des_ifs.


    unfold raw2tr. eapply Epsilon.epsilon_spec.
    unfold proj1_sig.
    match goal with
    | |- match_tr _ (let (a, _) := ?ep in a) => destruct ep as [x Px]
    end.
    


    2:{ 



    destruct raw.
    - pfold. econs 1.


    
    unfold raw2tr. eapply Epsilon.epsilon_spec.

    unfold epsilon.

    unfold Epsilon.epsilon.
    

    
    unfold proj1_sig.
    match goal with
    | |- match_tr _ (let (a, _) := ?ep in a) => destruct ep as [x Px]
    end.
    


    hexploit proj2_sig. in Heq.

    
    eapply proj2_sig. econs.
    2:{ unfold proj1_sig. des_ifs.

    eauto.

  Definition st2raw {R} (st: state): (RawTr.t (R:=R)) :=
    epsilon _ (@inhabited_raw _ R) (RawBeh.of_state st).

End ExtractTr.



Section EQUIV.

  Context {Ident: ID}.
  Variable wf: WF.

  Theorem IndexBeh_implies_SelectBeh
          R (st: state (R:=R)) (tr: Tr.t (R:=R)) (im: imap wf)
          (BEH: Beh.of_state im st tr)
    :
    exists raw, (<<MATCH: match_tr raw tr>>) /\ (<<BEH: RawBeh.of_state_fair_ord (wf:=wf) st raw>>).
  Proof.
    exists (st2raw st). esplits.
    { admit. }
    { eapply proj2_sig.



  Admitted.

  Theorem SelectBeh_implies_IndexBeh
          R (st: state (R:=R)) (raw: RawTr.t (R:=R))
          (BEH: RawBeh.of_state_fair_ord (wf:=wf) st raw)
    :
    exists (im: imap wf) tr, (<<MATCH: match_tr raw tr>>) /\ (<<BEH: Beh.of_state im st tr>>).
  Proof.
  Admitted.

End EQUIV.
