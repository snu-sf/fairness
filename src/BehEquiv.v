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
  .

  Definition raw_spin: forall (R: Type), RawTr.t -> Prop := paco2 _raw_spin bot2.

  Lemma raw_spin_mon: monotone2 _raw_spin.
  Proof.
    ii. inv IN. econs; eauto.
  Qed.


  Inductive _extract_tr
            (extract_tr: forall (R: Type), RawTr.t -> Tr.t -> Prop)
            R
    :
    (@RawTr.t _ R) -> Tr.t -> Prop :=
  | extract_tr_done
      retv
    :
    _extract_tr extract_tr (RawTr.done retv) (Tr.done retv)
  | extract_tr_spin
      raw
      (RSPIN: raw_spin raw)
    :
    _extract_tr extract_tr raw (Tr.spin)
  | extract_tr_ub
    :
    _extract_tr extract_tr (RawTr.ub) (Tr.ub)
  | extract_tr_nb
    :
    _extract_tr extract_tr (RawTr.nb) (Tr.nb)
  | extract_tr_obs
      (obs: obsE) raw_tl tr_tl
      (TL: extract_tr _ raw_tl tr_tl)
    :
    _extract_tr extract_tr (RawTr.cons (inr obs) raw_tl) (Tr.cons obs tr_tl)
  | extract_tr_silent
      (silent: silentE) raw_tl tr_tl
      (TL: _extract_tr extract_tr raw_tl tr_tl)
    :
    _extract_tr extract_tr (RawTr.cons (inl silent) raw_tl) tr_tl
  .

  Definition extract_tr: forall (R: Type), RawTr.t -> Tr.t -> Prop := paco3 _extract_tr bot3.

  Lemma extract_tr_ind
        (extract_tr : forall R : Type, RawTr.t -> Tr.t -> Prop) (R : Type) (P: RawTr.t -> Tr.t -> Prop)
        (DONE: forall retv : R, P (RawTr.done retv) (Tr.done retv))
        (SPIN: forall (raw : RawTr.t) (RSPIN: raw_spin raw), P raw Tr.spin)
        (UB: P RawTr.ub Tr.ub)
        (NB: P RawTr.nb Tr.nb)
        (OBS: forall (obs : obsE) (raw_tl : RawTr.t) (tr_tl : Tr.t) (TL: extract_tr R raw_tl tr_tl),
            P (RawTr.cons (inr obs) raw_tl) (Tr.cons obs tr_tl))
        (SILENT: forall (silent : silentE) (raw_tl : RawTr.t) (tr_tl : Tr.t)
                   (STEP: _extract_tr extract_tr raw_tl tr_tl) (IH: P raw_tl tr_tl),
            P (RawTr.cons (inl silent) raw_tl) tr_tl)
    :
    forall raw_tr tr, (_extract_tr extract_tr raw_tr tr) -> P raw_tr tr.
  Proof.
    fix IH 3; i.
    inv H; eauto.
  Qed.

  Lemma extract_tr_mon: monotone3 _extract_tr.
  Proof.
    ii. induction IN using extract_tr_ind; econs; eauto.
  Qed.

End MatchTr.
#[export] Hint Constructors _raw_spin.
#[export] Hint Unfold raw_spin.
#[export] Hint Resolve raw_spin_mon: paco.
#[export] Hint Resolve cpn2_wcompat: paco.
#[export] Hint Constructors _extract_tr.
#[export] Hint Unfold extract_tr.
#[export] Hint Resolve extract_tr_mon: paco.
#[export] Hint Resolve cpn3_wcompat: paco.



Section ExtractTr.

  Context {Ident: ID}.

  Lemma extract_eq_done
        R (tr: @Tr.t R) retv
        (EXTRACT: extract_tr (RawTr.done retv) tr)
    :
    tr = Tr.done retv.
  Proof.
    punfold EXTRACT. inv EXTRACT; eauto. punfold RSPIN. inv RSPIN.
  Qed.

  Lemma extract_eq_ub
        R (tr: @Tr.t R)
        (EXTRACT: extract_tr RawTr.ub tr)
    :
    tr = Tr.ub.
  Proof.
    punfold EXTRACT. inv EXTRACT; eauto. punfold RSPIN. inv RSPIN.
  Qed.

  Lemma extract_eq_nb
        R (tr: @Tr.t R)
        (EXTRACT: extract_tr RawTr.nb tr)
    :
    tr = Tr.nb.
  Proof.
    punfold EXTRACT. inv EXTRACT; eauto. punfold RSPIN. inv RSPIN.
  Qed.



  (** observer of the raw trace **)
  Inductive observe_raw_first
          R
    :
    (@RawTr.t _ R) -> (prod (option obsE) RawTr.t) -> Prop :=
    | observe_raw_first_done
        retv
      :
      observe_raw_first (RawTr.done retv) (None, (RawTr.done retv))
    | observe_raw_first_ub
      :
      observe_raw_first RawTr.ub (None, RawTr.ub)
    | observe_raw_first_nb
      :
      observe_raw_first RawTr.nb (None, RawTr.nb)
    | observe_raw_first_obs
        (obs: obsE) tl
      :
      observe_raw_first (RawTr.cons (inr obs) tl) (Some obs, tl)
    | observe_raw_first_silent
        (silent: silentE) obs tl tl0
        (STEP: observe_raw_first tl (obs, tl0))
      :
      observe_raw_first (RawTr.cons (inl silent) tl) (obs, tl0)
  .

  Definition observe_raw_prop {R}
             (raw: @RawTr.t _ R)
             (obstl: option (prod (option obsE) RawTr.t)): Prop :=
    match obstl with
    | None => raw_spin raw
    | Some obstl0 => observe_raw_first raw obstl0
    end.

  Lemma inhabited_observe_raw R: inhabited (option (prod (option obsE) (@RawTr.t _ R))).
  Proof.
    econs. exact None.
  Qed.

  Definition observe_raw {R} (raw: (@RawTr.t _ R)): option (prod (option obsE) RawTr.t) :=
    epsilon _ (@inhabited_observe_raw R) (observe_raw_prop raw).


  (** properties **)
  (* helper lemmas *)
  Lemma spin_no_obs
        R (raw: @RawTr.t _ R)
        (SPIN: raw_spin raw)
    :
    forall ev tl, ~ observe_raw_first raw (ev, tl).
  Proof.
    ii. revert SPIN. induction H; i; ss; clarify.
    - punfold SPIN. inv SPIN.
    - punfold SPIN. inv SPIN.
    - punfold SPIN. inv SPIN.
    - punfold SPIN. inv SPIN.
    - eapply IHobserve_raw_first; clear IHobserve_raw_first.
      punfold SPIN. inv SPIN. pclearbot. auto.
  Qed.

  Lemma no_obs_spin
        R (raw: @RawTr.t _ R)
        (NOOBS: forall ev tl, ~ observe_raw_first raw (ev, tl))
    :
    raw_spin raw.
  Proof.
    revert_until R. pcofix CIH; i. destruct raw.
    - exfalso. eapply NOOBS. econs.
    - exfalso. eapply NOOBS. econs.
    - exfalso. eapply NOOBS. econs.
    - destruct hd as [silent | obs].
      2:{ exfalso. eapply NOOBS. econs. }
      pfold. econs. right. eapply CIH. ii. eapply NOOBS.
      econs 5. eauto.
  Qed.

  Lemma spin_iff_no_obs
        R (raw: @RawTr.t _ R)
    :
    (raw_spin raw) <-> (forall ev tl, ~ observe_raw_first raw (ev, tl)).
  Proof.
    esplits. split; i. eapply spin_no_obs; eauto. eapply no_obs_spin; eauto.
  Qed.

  Lemma observe_raw_first_inj
        R (raw: @RawTr.t _ R) obstl1 obstl2
        (ORP1: observe_raw_first raw obstl1)
        (ORP2: observe_raw_first raw obstl2)
    :
    obstl1 = obstl2.
  Proof.
    depgen obstl2. induction ORP1; i.
    - inv ORP2; eauto.
    - inv ORP2; eauto.
    - inv ORP2; eauto.
    - inv ORP2; eauto.
    - inv ORP2; eauto.
  Qed.

  Lemma observe_raw_inj
        R (raw: @RawTr.t _ R) obstl1 obstl2
        (ORP1: observe_raw_prop raw obstl1)
        (ORP2: observe_raw_prop raw obstl2)
    :
    obstl1 = obstl2.
  Proof.
    destruct obstl1 as [(obs1, tl1) | ]; ss.
    2:{ destruct obstl2 as [(obs2, tl2) | ]; ss.
        rewrite spin_iff_no_obs in ORP1. eapply ORP1 in ORP2. clarify.
    }
    destruct obstl2 as [(obs2, tl2) | ]; ss.
    2:{ rewrite spin_iff_no_obs in ORP2. eapply ORP2 in ORP1. clarify. }
    f_equal. eapply observe_raw_first_inj; eauto.
  Qed.


  Theorem observe_raw_prop_impl_observe_raw
          R (raw: @RawTr.t _ R) obstl
          (ORP: observe_raw_prop raw obstl)
    :
    observe_raw raw = obstl.
  Proof.
    eapply observe_raw_inj. 2: eauto.
    unfold observe_raw, epsilon. eapply Epsilon.epsilon_spec. eauto.
  Qed.

  Lemma observe_raw_prop_false
        R (raw: @RawTr.t _ R) ev tl
    :
    ~ observe_raw_prop raw (Some (None, RawTr.cons ev tl)).
  Proof.
    ii. ss. remember (None, RawTr.cons ev tl) as obstl. revert Heqobstl. revert ev tl. rename H into ORF.
    induction ORF; i; ss. clarify. eapply IHORF. eauto.
  Qed.

  (** observe_raw reductions **)
  Lemma observe_raw_spin
        R (raw: @RawTr.t _ R)
        (SPIN: raw_spin raw)
    :
    observe_raw raw = None.
  Proof.
    eapply observe_raw_prop_impl_observe_raw. ss.
  Qed.

  Lemma raw_spin_observe
        R (raw: @RawTr.t _ R)
        (NONE: observe_raw raw = None)
    :
    raw_spin raw.
  Proof.
    eapply spin_iff_no_obs. ii.
    assert (SOME: ~ observe_raw raw = Some (ev, tl)).
    { ii. clarify. }
    eapply SOME. eapply observe_raw_prop_impl_observe_raw. ss.
  Qed.

  Lemma observe_raw_done
        R (retv: R)
    :
    observe_raw (RawTr.done retv) = Some (None, RawTr.done retv).
  Proof.
    eapply observe_raw_prop_impl_observe_raw. ss. econs.
  Qed.

  Lemma observe_raw_ub
        R
    :
    observe_raw (R:=R) (RawTr.ub) = Some (None, RawTr.ub).
  Proof.
    eapply observe_raw_prop_impl_observe_raw. ss. econs.
  Qed.

  Lemma observe_raw_nb
        R
    :
    observe_raw (R:=R) (RawTr.nb) = Some (None, RawTr.nb).
  Proof.
    eapply observe_raw_prop_impl_observe_raw. ss. econs.
  Qed.

  Lemma observe_raw_obs
        R obs (tl: @RawTr.t _ R)
    :
    observe_raw (RawTr.cons (inr obs) tl) = Some (Some obs, tl).
  Proof.
    eapply observe_raw_prop_impl_observe_raw. ss. econs.
  Qed.


  Lemma observe_first_some_inj
        R (raw: @RawTr.t _ R) obstl1 obstl2
        (SOME: observe_raw raw = Some obstl1)
        (ORF: observe_raw_first raw obstl2)
    :
    obstl1 = obstl2.
  Proof.
    assert (A: observe_raw_prop raw (Some obstl2)). ss.
    apply observe_raw_prop_impl_observe_raw in A. rewrite SOME in A. clarify.
  Qed.

  Lemma observe_first_some
        R (raw: @RawTr.t _ R) obstl
        (SOME: observe_raw raw = Some obstl)
    :
    observe_raw_first raw obstl.
  Proof.
    assert (NOTSPIN: ~ raw_spin raw).
    { ii. eapply observe_raw_spin in H. clarify. }
    rewrite spin_iff_no_obs in NOTSPIN.
    assert (TEMP: ~ (forall obstl, ~ observe_raw_first raw obstl)).
    { ii. eapply NOTSPIN. i. eauto. }
    eapply Classical_Pred_Type.not_all_not_ex in TEMP. des.
    replace obstl with n; eauto. symmetry. eapply observe_first_some_inj; eauto.
  Qed.

  Theorem observe_raw_spec
          R (raw: @RawTr.t _ R)
    :
    observe_raw_prop raw (observe_raw raw).
  Proof.
    destruct (observe_raw raw) eqn:EQ.
    - ss. eapply observe_first_some; eauto.
    - ss. eapply raw_spin_observe; eauto.
  Qed.

  Lemma observe_raw_silent
        R (tl: @RawTr.t _ R) silent
    :
    observe_raw (RawTr.cons (inl silent) tl) = observe_raw tl.
  Proof.
    eapply observe_raw_prop_impl_observe_raw. destruct (observe_raw tl) eqn:EQ.
    2:{ ss. pfold. econs. left. eapply raw_spin_observe; eauto. }
    ss. destruct p as [obs tl0]. hexploit observe_first_some; eauto. i.
    econs. auto.
  Qed.



  (** raw trace to normal trace **)
  CoFixpoint raw2tr {R} (raw: @RawTr.t _ R): (@Tr.t R) :=
    match observe_raw raw with
    | None => Tr.spin
    | Some (None, RawTr.done retv) => Tr.done retv
    | Some (None, RawTr.ub) => Tr.ub
    | Some (None, RawTr.nb) => Tr.nb
    | Some (None, RawTr.cons _ _) => Tr.ub
    | Some (Some obs, tl) => Tr.cons obs (raw2tr tl)
    end.

  (** reduction lemmas **)
  Lemma raw2tr_red_done
        R (retv: R)
    :
    (raw2tr (RawTr.done retv)) = (Tr.done retv).
  Proof.
    replace (raw2tr (RawTr.done retv)) with (Tr.ob (raw2tr (RawTr.done retv))).
    2:{ symmetry. apply Tr.ob_eq. }
    ss. rewrite observe_raw_done. ss.
  Qed.

  Lemma raw2tr_red_ub
        R
    :
    (raw2tr (R:=R) RawTr.ub) = Tr.ub.
  Proof.
    replace (raw2tr RawTr.ub) with (Tr.ob (R:=R) (raw2tr RawTr.ub)).
    2:{ symmetry. apply Tr.ob_eq. }
    ss. rewrite observe_raw_ub. ss.
  Qed.

  Lemma raw2tr_red_nb
        R
    :
    (raw2tr (R:=R) RawTr.nb) = Tr.nb.
  Proof.
    replace (raw2tr RawTr.nb) with (Tr.ob (R:=R) (raw2tr RawTr.nb)).
    2:{ symmetry. apply Tr.ob_eq. }
    ss. rewrite observe_raw_nb. ss.
  Qed.

  Lemma raw2tr_red_obs
        R obs tl
    :
    (raw2tr (RawTr.cons (inr obs) tl)) = (Tr.cons (R:=R) obs (raw2tr tl)).
  Proof.
    match goal with | |- ?lhs = _ => replace lhs with (Tr.ob lhs) end.
    2:{ symmetry. apply Tr.ob_eq. }
    ss. rewrite observe_raw_obs. ss.
  Qed.

  Lemma raw2tr_red_spin
        R (raw: @RawTr.t _ R)
        (SPIN: raw_spin raw)
    :
    (raw2tr raw) = Tr.spin.
  Proof.
    match goal with | |- ?lhs = _ => replace lhs with (Tr.ob lhs) end.
    2:{ symmetry. apply Tr.ob_eq. }
    ss. rewrite observe_raw_spin; eauto.
  Qed.

  Lemma raw2tr_red_silent
        R silent tl
    :
    (raw2tr (RawTr.cons (inl silent) tl)) = (raw2tr (R:=R) tl).
  Proof.
    match goal with | |- ?lhs = ?rhs => replace lhs with (Tr.ob lhs); [replace rhs with (Tr.ob rhs) |] end.
    2:{ symmetry. apply Tr.ob_eq. }
    2:{ symmetry. apply Tr.ob_eq. }
    ss. rewrite observe_raw_silent. ss.
  Qed.

  Theorem raw2tr_extract
          R (raw: @RawTr.t _ R)
    :
    extract_tr raw (raw2tr raw).
  Proof.
    revert_until R. pcofix CIH. i.
    destruct raw.
    { rewrite raw2tr_red_done. pfold. econs. }
    { rewrite raw2tr_red_ub. pfold. econs. }
    { rewrite raw2tr_red_nb. pfold. econs. }
    destruct hd as [silent | obs].
    2:{ rewrite raw2tr_red_obs. pfold. econs. right. eauto. }
    destruct (observe_raw (RawTr.cons (inl silent) raw)) eqn:EQ.
    2:{ eapply raw_spin_observe in EQ. rewrite raw2tr_red_spin; eauto. }
    rename p into obstl.
    remember (RawTr.cons (inl silent) raw) as raw0. clear Heqraw0. clear silent raw.
    pose (observe_raw_spec) as ORS. specialize (ORS R raw0). rewrite EQ in ORS. ss.
    clear EQ. induction ORS; ss.
    { rewrite raw2tr_red_done. pfold. econs. }
    { rewrite raw2tr_red_ub. pfold. econs. }
    { rewrite raw2tr_red_nb. pfold. econs. }
    { rewrite raw2tr_red_obs. pfold. econs. right. eauto. }
    pfold. econs. punfold IHORS. remember (raw2tr tl) as tr. depgen silent. depgen tl0. revert Heqtr. depgen obs.
    induction IHORS using (@extract_tr_ind); i.
    { rewrite raw2tr_red_silent. rewrite raw2tr_red_done. econs. }
    { exfalso. eapply spin_iff_no_obs in RSPIN. eauto. }
    { rewrite raw2tr_red_silent. rewrite raw2tr_red_ub. econs. }
    { rewrite raw2tr_red_silent. rewrite raw2tr_red_nb. econs. }
    { rewrite raw2tr_red_silent. rewrite raw2tr_red_obs. econs. right. auto. }
    econs 6. rewrite raw2tr_red_silent. eapply IHIHORS; eauto.
    - rewrite raw2tr_red_silent in Heqtr. auto.
    - instantiate (1:=tl0). instantiate (1:=obs). inv ORS. auto.
  Qed.

End ExtractTr.



Section ExtractRaw.

  Context {Ident: ID}.

  (** observer of the state **)
  Variant observe_state_first
          R
    :
    (@state _ R) -> (prod (option rawE) state) -> Prop :=
    | observe_state_first_ret
        retv
      :
      observe_state_first (Ret retv) (None, Ret retv)
    | observe_state_first_obs
        fn args ktr rv
      :
      observe_state_first (Vis (Observe fn args) ktr)
                          (Some (inr (obsE_syscall fn args rv)), ktr rv)
    | observe_state_first_tau
        itr
      :
      observe_state_first (Tau itr) (Some (inl silentE_tau), itr)
    | observe_state_first_choose
        X ktr x
      :
      observe_state_first (Vis (Choose X) ktr) (Some (inl silentE_tau), ktr x)
    | observe_state_first_fair
        fm ktr
      :
      observe_state_first (Vis (Fair fm) ktr) (Some (inl (silentE_fair fm)), ktr tt)
  .

  Variant _state_stuck
          (state_stuck: forall R, (@state _ R) -> Prop)
          R
    :
    (@state _ R) -> Prop :=
    | state_stuck_tau
        (itr: @state _ R)
        (ST: state_stuck _ itr)
      :
      _state_stuck state_stuck (Tau itr)
    | state_stuck_obs
        ktr fn args rv
        (ST: state_stuck _ (ktr rv))
      :
      _state_stuck state_stuck (Vis (Observe fn args) ktr)
    | state_stuck_fair
        ktr fm
        (ST: state_stuck _ (ktr tt))
      :
      _state_stuck state_stuck (Vis (Fair fm) ktr)
    | state_stuck_choose
        X ktr
        (EMPTY: ~ inhabited X)
      :
      _state_stuck state_stuck (Vis (Choose X) ktr)
    | state_stuck_ub
        ktr
      :
      _state_stuck state_stuck (Vis Undefined ktr)
  .

  Definition state_stuck: forall R, (@state _ R) -> Prop := paco2 _state_stuck bot2.

  Lemma state_stuck_mon: monotone2 _state_stuck.
  Proof.
    ii. inv IN. all: econs; eauto.
  Qed.

  Local Hint Resolve state_stuck_mon: paco.

  Definition observe_state_prop
             R (st: @state _ R)
             (rawst: option (prod (option rawE) state)): Prop :=
    match rawst with
    | None => state_stuck st
    | Some rawst0 => observe_state_first st rawst0
    end.

  Lemma inhabited_observe_state R: inhabited (option (prod (option rawE) (@state _ R))).
  Proof.
    econs. exact None.
  Qed.

  Definition observe_state {R} (st: @state _ R): option (prod (option rawE) state) :=
    epsilon _ (@inhabited_observe_state R) (observe_state_prop st).

  (** properties **)
  (** observe_state reduction lemmas **)
  Lemma observe_state_ret
        R (retv: R)
    :
    observe_state (Ret retv) = Some (None, Ret retv).
  Proof.
    






  Theorem observe_raw_prop_impl_observe_raw
          R (raw: @RawTr.t _ R) obstl
          (ORP: observe_raw_prop raw obstl)
    :
    observe_raw raw = obstl.
  Proof.
    eapply observe_raw_inj. 2: eauto.
    unfold observe_raw, epsilon. eapply Epsilon.epsilon_spec. eauto.
  Qed.




  (** state to raw trace **)
  CoFixpoint st2raw {R} (st: @state _ R): (@RawTr.t _ R) :=
    match observe_state st with
    | None => RawTr.nb
    | Some (None, Ret retv) => RawTr.done retv
    | Some (Some ev, st0) => RawTr.cons ev (st2raw st0)
    (* impossible case *)
    | Some (None, _) => RawTr.ub
    end.

End ExtractRaw.



Section EQUIV.

  Context {Ident: ID}.
  Variable wf: WF.

  Lemma IndexBeh_implies_SelectBeh_extract_tr
        R (st: state (R:=R)) (tr: Tr.t (R:=R)) (im: imap wf)
        (BEH: Beh.of_state im st tr)
    :
    (<<EXTRACT: extract_tr (st2raw st) tr>>).
  Proof.
  Admitted.

  Theorem IndexBeh_implies_SelectBeh
          R (st: state (R:=R)) (tr: Tr.t (R:=R)) (im: imap wf)
          (BEH: Beh.of_state im st tr)
    :
    exists raw, (<<EXTRACT: extract_tr raw tr>>) /\ (<<BEH: RawBeh.of_state_fair_ord (wf:=wf) st raw>>).
  Proof.
  Admitted.


  Lemma SelectBeh_implies_IndexBeh_extract_tr
        R (st: state (R:=R)) (raw: RawTr.t (R:=R))
        (BEH: RawBeh.of_state st raw)
    :
    (<<EXTRACT: extract_tr raw (raw2tr raw)>>).
  Proof.
    red. revert_until R. pcofix CIH; i.
    punfold BEH. inv BEH.
    { rewrite raw2tr_done. pfold. econs. }
    { rewrite raw2tr_nb. pfold. econs. }
    { pclearbot. eapply CIH in TL.

      punfold TL.

      eapply extract_tr_mon.

      pfold. unfold raw2tr, epsilon. eapply Epsilon.epsilon_spec.


    
    unfold RawBeh.of_state in BEH. punfold BEH.



  Admitted.

  Theorem SelectBeh_implies_IndexBeh
          R (st: state (R:=R)) (raw: RawTr.t (R:=R))
          (BEH: RawBeh.of_state_fair_ord (wf:=wf) st raw)
    :
    exists (im: imap wf) tr, (<<EXTRACT: extract_tr raw tr>>) /\ (<<BEH: Beh.of_state im st tr>>).
  Proof.
  Admitted.

End EQUIV.
