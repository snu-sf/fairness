From sflib Require Import sflib.
From Paco Require Import paco.

Require Import Coq.Classes.RelationClasses.

From Fairness Require Import
  ITreeLib WFLib FairBeh SelectBeh.

From Fairness Require Import Axioms.

Set Implicit Arguments.

Section EXTRACT.

  Variable id: ID.

  (** match between raw_tr and tr *)
  Variant _raw_spin
          (raw_spin: forall (R: Type), (@RawTr.t id R) -> Prop)
          R
    :
    (@RawTr.t id R) -> Prop :=
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
    (@RawTr.t id R) -> Tr.t -> Prop :=
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

  Local Hint Constructors _raw_spin: core.
  Local Hint Unfold raw_spin: core.
  Local Hint Resolve raw_spin_mon: paco.
  Local Hint Constructors _extract_tr: core.
  Local Hint Unfold extract_tr: core.
  Local Hint Resolve extract_tr_mon: paco.

  Lemma extract_tr_ind2
        (R : Type) (P: RawTr.t -> Tr.t -> Prop)
        (DONE: forall retv : R, P (RawTr.done retv) (Tr.done retv))
        (SPIN: forall (raw : RawTr.t) (RSPIN: raw_spin raw), P raw Tr.spin)
        (UB: P RawTr.ub Tr.ub)
        (NB: P RawTr.nb Tr.nb)
        (OBS: forall (obs : obsE) (raw_tl : RawTr.t) (tr_tl : Tr.t) (TL: extract_tr raw_tl tr_tl),
            P (RawTr.cons (inr obs) raw_tl) (Tr.cons obs tr_tl))
        (SILENT: forall (silent : silentE) (raw_tl : RawTr.t) (tr_tl : Tr.t)
                   (STEP: extract_tr raw_tl tr_tl) (IH: P raw_tl tr_tl),
            P (RawTr.cons (inl silent) raw_tl) tr_tl)
    :
    forall raw_tr tr, (extract_tr raw_tr tr) -> P raw_tr tr.
  Proof.
    i. punfold H. induction H using extract_tr_ind; eauto.
    pclearbot. eapply OBS. eauto.
  Qed.

  Variant extract_tr_indC
          (extract_tr: forall (R: Type), RawTr.t -> Tr.t -> Prop)
          R
    :
    (@RawTr.t id R) -> Tr.t -> Prop :=
    | extract_tr_indC_done
        retv
      :
      extract_tr_indC extract_tr (RawTr.done retv) (Tr.done retv)
    | extract_tr_indC_spin
        raw
        (RSPIN: raw_spin raw)
      :
      extract_tr_indC extract_tr raw (Tr.spin)
    | extract_tr_indC_ub
      :
      extract_tr_indC extract_tr (RawTr.ub) (Tr.ub)
    | extract_tr_indC_nb
      :
      extract_tr_indC extract_tr (RawTr.nb) (Tr.nb)
    | extract_tr_indC_obs
        (obs: obsE) raw_tl tr_tl
        (TL: extract_tr _ raw_tl tr_tl)
      :
      extract_tr_indC extract_tr (RawTr.cons (inr obs) raw_tl) (Tr.cons obs tr_tl)
    | extract_tr_indC_silent
        (silent: silentE) raw_tl tr_tl
        (TL: extract_tr _ raw_tl tr_tl)
      :
      extract_tr_indC extract_tr (RawTr.cons (inl silent) raw_tl) tr_tl
  .

  Lemma extract_tr_indC_mon: monotone3 extract_tr_indC.
  Proof. ii. inv IN; econs; eauto. Qed.

  Local Hint Resolve extract_tr_indC_mon: paco.

  Lemma extract_tr_indC_wrespectful: wrespectful3 _extract_tr extract_tr_indC.
  Proof.
    econs; eauto with paco.
    i. inv PR; eauto.
    { econs; eauto. eapply rclo3_base. eauto. }
    { econs; eauto. eapply extract_tr_mon; eauto. i. eapply rclo3_base. auto. }
  Qed.

  Lemma extract_tr_indC_spec: extract_tr_indC <4= gupaco3 _extract_tr (cpn3 _extract_tr).
  Proof. i. eapply wrespect3_uclo; eauto with paco. eapply extract_tr_indC_wrespectful. Qed.

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

  Lemma extract_tr_raw_spin
        R (tr: @Tr.t R) raw
        (EXT: extract_tr raw tr)
        (RS: raw_spin raw)
    :
    tr = Tr.spin.
  Proof.
    revert RS. induction EXT using extract_tr_ind2; i; eauto.
    { punfold RS; inv RS. }
    { punfold RS; inv RS. }
    { punfold RS; inv RS. }
    { punfold RS; inv RS. }
    { punfold RS; inv RS. pclearbot. eauto. }
  Qed.

  Lemma extract_tr_inj_tr
        R (tr1 tr2: @Tr.t R) raw
        (EXT1: extract_tr raw tr1)
        (EXT2: extract_tr raw tr2)
    :
    Tr.eq tr1 tr2.
  Proof.
    revert_until R. pcofix CIH; i.
    depgen tr2. induction EXT1 using extract_tr_ind2; i.
    { punfold EXT2. inv EXT2; eauto. punfold RSPIN. inv RSPIN. }
    { punfold EXT2. inv EXT2; eauto. all: try (punfold RSPIN; inv RSPIN).
      pclearbot. eapply paco3_fold in TL. hexploit extract_tr_raw_spin; eauto.
      i; clarify. eauto using Tr.eq_equiv.
    }
    { punfold EXT2. inv EXT2; eauto. punfold RSPIN. inv RSPIN. }
    { punfold EXT2. inv EXT2; eauto. punfold RSPIN. inv RSPIN. }
    { punfold EXT2. inv EXT2; eauto. punfold RSPIN. inv RSPIN.
      pclearbot. pfold. econs. right; eauto.
    }
    { punfold EXT2. inv EXT2; eauto. punfold RSPIN. inv RSPIN.
      pclearbot. eauto.
    }
  Qed.

End EXTRACT.
#[export] Hint Constructors _raw_spin: core.
#[export] Hint Unfold raw_spin: core.
#[export] Hint Resolve raw_spin_mon: paco.
#[export] Hint Resolve cpn2_wcompat: paco.
#[export] Hint Constructors _extract_tr: core.
#[export] Hint Unfold extract_tr: core.
#[export] Hint Resolve extract_tr_mon: paco.
#[export] Hint Resolve cpn3_wcompat: paco.



Section ExtractTr.

  Variable id: ID.

  (** observer of the raw trace **)
  Inductive observe_raw_first
          R
    :
    (@RawTr.t id R) -> (prod (option obsE) RawTr.t) -> Prop :=
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
             (raw: @RawTr.t id R)
             (obstl: option (prod (option obsE) RawTr.t)): Prop :=
    match obstl with
    | None => raw_spin raw
    | Some obstl0 => observe_raw_first raw obstl0
    end.

  Lemma inhabited_observe_raw R: inhabited (option (prod (option obsE) (@RawTr.t id R))).
  Proof.
    econs. exact None.
  Qed.

  Definition observe_raw {R} (raw: (@RawTr.t id R)): option (prod (option obsE) RawTr.t) :=
    epsilon (@inhabited_observe_raw R) (observe_raw_prop raw).


  (** properties **)
  (* helper lemmas *)
  Lemma spin_no_obs
        R (raw: @RawTr.t id R)
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
        R (raw: @RawTr.t id R)
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
        R (raw: @RawTr.t id R)
    :
    (raw_spin raw) <-> (forall ev tl, ~ observe_raw_first raw (ev, tl)).
  Proof.
    esplits. split; i. eapply spin_no_obs; eauto. eapply no_obs_spin; eauto.
  Qed.

  Lemma observe_raw_first_inj
        R (raw: @RawTr.t id R) obstl1 obstl2
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
        R (raw: @RawTr.t id R) obstl1 obstl2
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
          R (raw: @RawTr.t id R) obstl
          (ORP: observe_raw_prop raw obstl)
    :
    observe_raw raw = obstl.
  Proof.
    eapply observe_raw_inj. 2: eauto.
    unfold observe_raw, epsilon. eapply Epsilon.epsilon_spec. eauto.
  Qed.

  Lemma observe_raw_prop_false
        R (raw: @RawTr.t id R) ev tl
    :
    ~ observe_raw_prop raw (Some (None, RawTr.cons ev tl)).
  Proof.
    ii. ss. remember (None, RawTr.cons ev tl) as obstl. revert Heqobstl. revert ev tl. rename H into ORF.
    induction ORF; i; ss. clarify. eapply IHORF. eauto.
  Qed.

  (** observe_raw reductions **)
  Lemma observe_raw_spin
        R (raw: @RawTr.t id R)
        (SPIN: raw_spin raw)
    :
    observe_raw raw = None.
  Proof.
    eapply observe_raw_prop_impl_observe_raw. ss.
  Qed.

  Lemma raw_spin_observe
        R (raw: @RawTr.t id R)
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
        R obs (tl: @RawTr.t id R)
    :
    observe_raw (RawTr.cons (inr obs) tl) = Some (Some obs, tl).
  Proof.
    eapply observe_raw_prop_impl_observe_raw. ss. econs.
  Qed.


  Lemma observe_first_some_inj
        R (raw: @RawTr.t id R) obstl1 obstl2
        (SOME: observe_raw raw = Some obstl1)
        (ORF: observe_raw_first raw obstl2)
    :
    obstl1 = obstl2.
  Proof.
    assert (A: observe_raw_prop raw (Some obstl2)). ss.
    apply observe_raw_prop_impl_observe_raw in A. rewrite SOME in A. clarify.
  Qed.

  Lemma observe_first_some
        R (raw: @RawTr.t id R) obstl
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
          R (raw: @RawTr.t id R)
    :
    observe_raw_prop raw (observe_raw raw).
  Proof.
    destruct (observe_raw raw) eqn:EQ.
    - ss. eapply observe_first_some; eauto.
    - ss. eapply raw_spin_observe; eauto.
  Qed.

  Lemma observe_raw_silent
        R (tl: @RawTr.t id R) silent
    :
    observe_raw (RawTr.cons (inl silent) tl) = observe_raw tl.
  Proof.
    eapply observe_raw_prop_impl_observe_raw. destruct (observe_raw tl) eqn:EQ.
    2:{ ss. pfold. econs. left. eapply raw_spin_observe; eauto. }
    ss. destruct p as [obs tl0]. hexploit observe_first_some; eauto. i.
    econs. auto.
  Qed.



  (** raw trace to normal trace **)
  CoFixpoint raw2tr {R} (raw: @RawTr.t id R): (@Tr.t R) :=
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
        R (raw: @RawTr.t id R)
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
          R (raw: @RawTr.t id R)
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

  Variable id: ID.
  Variable wf: WF.
  Variable wf0: T wf.
  Variable R: Type.

  Definition st_tr_im := ((@state id R) * (@Tr.t R) * (imap id wf))%type.

  (** observer of the state, needs trace for obs return value information **)
  Inductive observe_state_trace
    :
    st_tr_im -> (prod (list rawE) st_tr_im) -> Prop :=
  | observe_state_trace_ret
      (retv: R) im
    :
    observe_state_trace (Ret retv, Tr.done retv, im)
                        ([], (Ret retv, Tr.done retv, im))
  | observe_state_trace_obs
      fn args ktr rv tl im
    :
    observe_state_trace (Vis (Observe fn args) ktr, Tr.cons (obsE_syscall fn args rv) tl, im)
                        ([inr (obsE_syscall fn args rv)], (ktr rv, tl, im))
  | observe_state_trace_tau
      itr tr im evs sti
      (NNB: tr <> Tr.nb)
      (SPIN: tr = Tr.spin -> (Beh.diverge_index im itr /\ evs = [] /\ sti = (itr, tr, im)))
      (CONT: tr <> Tr.spin -> observe_state_trace (itr, tr, im) (evs, sti))
      (CONT: tr <> Tr.spin -> Beh.of_state im itr tr)
    :
    observe_state_trace (Tau itr, tr, im)
                        ((inl silentE_tau) :: evs, sti)
  | observe_state_trace_choose
      X ktr x tr im evs sti
      (NNB: tr <> Tr.nb)
      (SPIN: tr = Tr.spin -> (Beh.diverge_index im (ktr x) /\ evs = [] /\ sti = (ktr x, tr, im)))
      (CONT: tr <> Tr.spin -> observe_state_trace (ktr x, tr, im) (evs, sti))
      (BEH: tr <> Tr.spin -> Beh.of_state im (ktr x) tr)
    :
    observe_state_trace (Vis (Choose X) ktr, tr, im)
                        ((inl silentE_tau) :: evs, sti)
  | observe_state_trace_fair
      fm ktr tr im evs sti im0
      (NNB: tr <> Tr.nb)
      (SPIN: tr = Tr.spin -> (Beh.diverge_index im0 (ktr tt) /\ evs = [] /\ sti = (ktr tt, tr, im0)))
      (CONT: tr <> Tr.spin -> observe_state_trace (ktr tt, tr, im0) (evs, sti))
      (CONT: tr <> Tr.spin -> Beh.of_state im0 (ktr tt) tr)
      (FAIR: fair_update im im0 fm)
    :
    observe_state_trace (Vis (Fair fm) ktr, tr, im)
                        ((inl (silentE_fair fm)) :: evs, sti)
  | observe_state_trace_ub
      ktr tr im
    :
    observe_state_trace (Vis Undefined ktr, tr, im)
                        ([], (Vis Undefined ktr, tr, im))
  | observe_state_trace_nb
      itr im
    :
    observe_state_trace (itr, Tr.nb, im)
                        ([], (itr, Tr.nb, im))
  .


  Definition observe_state_prop (sti: st_tr_im) (rawsti: (prod (list rawE) st_tr_im)): Prop :=
    (let '(st, tr, im) := sti in (Beh.of_state im st tr)) -> observe_state_trace sti rawsti.

  Definition itree_loop R: (@state id R) :=
    @ITree.iter _ R unit (fun x: unit => Ret (inl x)) tt.

  Lemma inhabited_observe_state: inhabited (prod (list (@rawE id)) st_tr_im).
  Proof.
    econs. econs. exact []. econs. econs. exact (itree_loop R). exact Tr.ub. exact (fun _ => wf0).
  Qed.

  Definition observe_state (sti: st_tr_im): (prod (list rawE) st_tr_im) :=
    epsilon inhabited_observe_state (observe_state_prop sti).


  (** properties **)
  Lemma beh_implies_spin
        (im: imap id wf) (st: @state _ R)
        (BEH: Beh.of_state im st Tr.spin)
    :
    Beh.diverge_index im st.
  Proof.
    revert_until R. pcofix CIH; i. remember Tr.spin as tr. revert Heqtr.
    induction BEH using (@Beh.of_state_ind2); i; clarify; ss; eauto.
    { eapply paco3_mon; eauto. ss. }
    { pfold. econs. right. eauto. }
    { pfold. econs. right. eauto. }
    { pfold. econs. right. eauto. eauto. }
  Qed.

  Lemma observe_state_trace_exists
        (st: @state _ R) (tr: Tr.t) (im: imap id wf)
        (BEH: Beh.of_state im st tr)
    :
    exists rawsti, observe_state_trace (st, tr, im) rawsti.
  Proof.
    induction BEH using (@Beh.of_state_ind2).
    - eexists. econs.
    - punfold H. inv H.
      + pclearbot. eexists. econs; i; ss; eauto.
      + pclearbot. eexists. econs; i; ss; eauto.
      + pclearbot. eexists. econs; i; ss; eauto.
      + pclearbot. eexists. econs; i; ss; eauto.
    - eexists. econs.
    - eexists. econs.
    - destruct (classic (tr = Tr.nb)) as [NB | NNB]; clarify; ss.
      + eexists. econs 7.
      + destruct (classic (tr = Tr.spin)) as [SPIN | NSPIN]; clarify; ss.
        * des. eexists. econs; i; ss; clarify. splits; eauto. eapply beh_implies_spin; eauto.
        * des. destruct rawsti. eexists. econs; i; ss; clarify; eauto.
    - destruct (classic (tr = Tr.nb)) as [NB | NNB]; clarify; ss.
      + eexists. econs 7.
      + destruct (classic (tr = Tr.spin)) as [SPIN | NSPIN]; clarify; ss.
        * des. eexists. econs; i; ss; clarify. splits; eauto. eapply beh_implies_spin; eauto.
        * des. destruct rawsti. rr in IHBEH. eexists. econs; i; ss; clarify; eauto.
    - destruct (classic (tr = Tr.nb)) as [NB | NNB]; clarify; ss.
      + eexists. econs 7.
      + destruct (classic (tr = Tr.spin)) as [SPIN | NSPIN]; clarify; ss.
        * des. eexists. econs; i; ss; clarify. splits; eauto. eapply beh_implies_spin; eauto. eauto.
        * des. destruct rawsti. rr in IHBEH. eexists. econs; i; ss; clarify; eauto.
    - eexists. econs; eauto.
  Qed.

  Lemma observe_state_exists
        (st: @state _ R) (tr: Tr.t) (im: imap id wf)
    :
    exists rawsti, observe_state_prop (st, tr, im) rawsti.
  Proof.
    destruct (classic (Beh.of_state im st tr)) as [BEH | NBEH].
    - hexploit observe_state_trace_exists; eauto. i. des. eexists. ii. eauto.
    - eexists. ii. clarify.
      Unshelve. exact ([], (itree_loop R, Tr.ub, fun _ => wf0)).
  Qed.

  (** (state, trace, imap) to raw trace **)
  CoFixpoint raw_spin_trace: @RawTr.t id R :=
    RawTr.cons (R:=R) (inl silentE_tau) raw_spin_trace.

  Lemma raw_spin_trace_ob
    :
    raw_spin_trace = (@RawTr.ob _ R raw_spin_trace).
  Proof.
    apply RawTr.ob_eq.
  Qed.

  Lemma raw_spin_trace_red
    :
    raw_spin_trace = RawTr.cons (inl silentE_tau) raw_spin_trace.
  Proof.
    rewrite raw_spin_trace_ob at 1. ss.
  Qed.

  Lemma raw_spin_trace_spec
    :
    @raw_spin _ R raw_spin_trace.
  Proof.
    pcofix CIH. rewrite raw_spin_trace_ob. pfold. econs. right. eapply CIH.
  Qed.


  CoFixpoint tr2raw (tr: Tr.t): RawTr.t :=
    match tr with
    | Tr.done retv => RawTr.done retv
    | Tr.spin => raw_spin_trace
    | Tr.ub => RawTr.ub
    | Tr.nb => RawTr.nb
    | Tr.cons hd tl => RawTr.cons (inr hd) (tr2raw tl)
    end.

  Lemma tr2raw_red_ret
        retv
    :
    tr2raw (Tr.done retv) = RawTr.done retv.
  Proof.
    match goal with | |- ?lhs = _ => replace lhs with (RawTr.ob lhs) end.
    2:{ symmetry. apply RawTr.ob_eq. }
    ss.
  Qed.

  Lemma tr2raw_red_spin
    :
    tr2raw Tr.spin = raw_spin_trace.
  Proof.
    match goal with | |- ?lhs = _ => replace lhs with (RawTr.ob lhs) end.
    2:{ symmetry. apply RawTr.ob_eq. }
    rewrite raw_spin_trace_red. ss.
  Qed.

  Lemma tr2raw_red_ub
    :
    tr2raw Tr.ub = RawTr.ub.
  Proof.
    match goal with | |- ?lhs = _ => replace lhs with (RawTr.ob lhs) end.
    2:{ symmetry. apply RawTr.ob_eq. }
    ss.
  Qed.

  Lemma tr2raw_red_nb
    :
    tr2raw Tr.nb = RawTr.nb.
  Proof.
    match goal with | |- ?lhs = _ => replace lhs with (RawTr.ob lhs) end.
    2:{ symmetry. apply RawTr.ob_eq. }
    ss.
  Qed.

  Lemma tr2raw_red_cons
        hd tl
    :
    tr2raw (Tr.cons hd tl) = RawTr.cons (inr hd) (tr2raw tl).
  Proof.
    match goal with | |- ?lhs = _ => replace lhs with (RawTr.ob lhs) end.
    2:{ symmetry. apply RawTr.ob_eq. }
    ss.
  Qed.

  Lemma extract_tr_tr2raw
        tr
    :
    extract_tr (tr2raw tr) tr.
  Proof.
    revert_until wf0. pcofix CIH; i.
    replace (tr2raw tr) with (RawTr.ob (tr2raw tr)).
    2:{ symmetry. apply RawTr.ob_eq. }
    ss. destruct tr eqn:TR; clarify.
    { pfold; econs. }
    { rewrite raw_spin_trace_red. pfold. econs.
      rewrite <- raw_spin_trace_red. apply raw_spin_trace_spec. }
    { pfold; econs. }
    { pfold; econs. }
    { pfold; econs. eauto. }
  Qed.


  CoFixpoint _sti2raw (evs: list rawE) (sti: st_tr_im): (@RawTr.t id R) :=
    match evs with
    | hd :: tl => RawTr.cons hd (_sti2raw tl sti)
    | [] =>
        match observe_state sti with
        | (evs, (Ret _, Tr.done retv, _)) => RawTr.app evs (RawTr.done retv)
        | (evs, (_, Tr.nb, _)) => RawTr.app evs RawTr.nb
        | (evs, (Vis Undefined _, tr, _)) => RawTr.app evs (tr2raw tr)
        | (hd :: tl, sti0) => RawTr.cons hd (_sti2raw tl sti0)
        | (evs, _) => RawTr.app evs RawTr.ub
        end
    end.

  Definition sti2raw (sti: st_tr_im): (@RawTr.t id R) := _sti2raw [] sti.


  (** observe_state reduction lemmas **)
  Lemma observe_state_ret
        (im: imap id wf) (retv: R)
    :
    observe_state (Ret retv, Tr.done retv, im) = ([], (Ret retv, Tr.done retv, im)).
  Proof.
    unfold observe_state, epsilon. unfold Epsilon.epsilon. unfold proj1_sig. des_ifs.
    rename x into rawsti. clear Heq.
    hexploit (observe_state_exists). intros OSP. eapply o in OSP; clear o.
    unfold observe_state_prop in OSP. hexploit OSP; clear OSP; eauto.
    i. inv H. eauto.
  Qed.

  Lemma observe_state_obs
        (im: imap id wf) fn args rv tl ktr
        (BEH: Beh.of_state im (ktr rv) tl)
    :
    observe_state (Vis (Observe fn args) ktr, Tr.cons (obsE_syscall fn args rv) tl, im) =
      ([inr (obsE_syscall fn args rv)], (ktr rv, tl, im)).
  Proof.
    unfold observe_state, epsilon. unfold Epsilon.epsilon. unfold proj1_sig. des_ifs.
    rename x into rawsti. clear Heq.
    hexploit (observe_state_exists). intros OSP. eapply o in OSP; clear o.
    unfold observe_state_prop in OSP. hexploit OSP; clear OSP; eauto.
    { pfold. econs. eauto. }
    i. inv H. eapply inj_pair2 in H3. clarify.
  Qed.

  Lemma observe_state_tau
        (im: imap id wf) itr tr
        (BEH: Beh.of_state im (Tau itr) tr)
        (NNB: tr <> Tr.nb)
        (NSPIN: tr <> Tr.spin)
    :
    (Beh.of_state im itr tr) /\
      (exists evs sti, (observe_state_trace (itr, tr, im) (evs, sti)) /\
                    (observe_state (Tau itr, tr, im) = ((inl silentE_tau) :: evs, sti))).
  Proof.
    unfold observe_state, epsilon. unfold Epsilon.epsilon. unfold proj1_sig. des_ifs.
    rename x into rawsttr. clear Heq.
    hexploit (observe_state_exists). intros OSP. eapply o in OSP; clear o.
    unfold observe_state_prop in OSP. hexploit OSP; clear OSP; eauto.
    i. inv H; ss; eauto. hexploit CONT; eauto; i. des. esplits; eauto.
  Qed.

  Lemma observe_state_tau_spin
        (im: imap id wf) itr tr
        (BEH: Beh.of_state im (Tau itr) tr)
        (NNB: tr <> Tr.nb)
        (SPIN: tr = Tr.spin)
    :
    (Beh.diverge_index im itr) /\
      observe_state (Tau itr, tr, im) = ([inl silentE_tau], (itr, tr, im)).
  Proof.
    unfold observe_state, epsilon. unfold Epsilon.epsilon. unfold proj1_sig. des_ifs.
    rename x into rawsttr. clear Heq.
    hexploit (observe_state_exists). intros OSP. eapply o in OSP; clear o.
    unfold observe_state_prop in OSP. hexploit OSP; clear OSP; eauto.
    i. inv H; ss; eauto. hexploit SPIN; ss; i. des; clarify.
  Qed.

  Lemma observe_state_choose
        (im: imap id wf) tr X ktr
        (BEH: Beh.of_state im (Vis (Choose X) ktr) tr)
        (NNB: tr <> Tr.nb)
        (NSPIN: tr <> Tr.spin)
    :
    exists (x: X),
      (Beh.of_state im (ktr x) tr) /\
        (exists evs sti,
            (observe_state_trace (ktr x, tr, im) (evs, sti)) /\
              (observe_state (Vis (Choose X) ktr, tr, im) = ((inl silentE_tau) :: evs, sti))).
  Proof.
    unfold observe_state, epsilon. unfold Epsilon.epsilon. unfold proj1_sig. des_ifs.
    rename x into rawsttr. clear Heq.
    hexploit (observe_state_exists). intros OSP. eapply o in OSP; clear o.
    unfold observe_state_prop in OSP. hexploit OSP; clear OSP; eauto.
    i. inv H; clarify. eapply inj_pair2 in H0. clarify. hexploit CONT; eauto; i. des. esplits; eauto.
  Qed.

  Lemma observe_state_choose_spin
        (im: imap id wf) tr X ktr
        (BEH: Beh.of_state im (Vis (Choose X) ktr) tr)
        (NNB: tr <> Tr.nb)
        (SPIN: tr = Tr.spin)
    :
    exists (x: X),
      (Beh.diverge_index im (ktr x)) /\
        (observe_state (Vis (Choose X) ktr, tr, im) = ([inl silentE_tau], (ktr x, tr, im))).
  Proof.
    unfold observe_state, epsilon. unfold Epsilon.epsilon. unfold proj1_sig. des_ifs.
    rename x into rawsttr. clear Heq.
    hexploit (observe_state_exists). intros OSP. eapply o in OSP; clear o.
    unfold observe_state_prop in OSP. hexploit OSP; clear OSP; eauto.
    i. inv H; clarify. eapply inj_pair2 in H0. clarify. hexploit SPIN; eauto; i. des. clarify. eauto.
  Qed.

  Lemma observe_state_fair
        (im: imap id wf) tr fm ktr
        (BEH: Beh.of_state im (Vis (Fair fm) ktr) tr)
        (NNB: tr <> Tr.nb)
        (NSPIN: tr <> Tr.spin)
    :
    exists (im0: imap id wf),
      (fair_update im im0 fm) /\ (Beh.of_state im0 (ktr tt) tr) /\
        (exists evs sti,
            (observe_state_trace (ktr tt, tr, im0) (evs, sti)) /\
              (observe_state (Vis (Fair fm) ktr, tr, im) = ((inl (silentE_fair fm)) :: evs, sti))).
  Proof.
    unfold observe_state, epsilon. unfold Epsilon.epsilon. unfold proj1_sig. des_ifs.
    rename x into rawsttr. clear Heq.
    hexploit (observe_state_exists). intros OSP. eapply o in OSP; clear o.
    unfold observe_state_prop in OSP. hexploit OSP; clear OSP; eauto.
    i. inv H; ss; eauto. eapply inj_pair2 in H2. clarify. hexploit CONT; eauto; i. des. esplits; eauto.
  Qed.

  Lemma observe_state_fair_spin
        (im: imap id wf) tr fm ktr
        (BEH: Beh.of_state im (Vis (Fair fm) ktr) tr)
        (NNB: tr <> Tr.nb)
        (NSPIN: tr = Tr.spin)
    :
    exists (im0: imap id wf),
      (fair_update im im0 fm) /\
        (Beh.diverge_index im0 (ktr tt)) /\
        (observe_state (Vis (Fair fm) ktr, tr, im) = ([inl (silentE_fair fm)], (ktr tt, tr, im0))).
  Proof.
    unfold observe_state, epsilon. unfold Epsilon.epsilon. unfold proj1_sig. des_ifs.
    rename x into rawsttr. clear Heq.
    hexploit (observe_state_exists). intros OSP. eapply o in OSP; clear o.
    unfold observe_state_prop in OSP. hexploit OSP; clear OSP; eauto.
    i. inv H; ss; eauto. eapply inj_pair2 in H2. clarify. hexploit SPIN; eauto; i. des. clarify. esplits; eauto.
  Qed.

  Lemma observe_state_ub
        (im: imap id wf) tr ktr
    :
    observe_state (Vis Undefined ktr, tr, im) = ([], (Vis Undefined ktr, tr, im)).
  Proof.
    unfold observe_state, epsilon. unfold Epsilon.epsilon. unfold proj1_sig. des_ifs.
    rename x into rawsttr. clear Heq.
    hexploit (observe_state_exists). intros OSP. eapply o in OSP; clear o.
    unfold observe_state_prop in OSP. hexploit OSP; clear OSP; eauto.
    i. inv H; eauto. eapply inj_pair2 in H1. clarify.
  Qed.

  Lemma observe_state_nb
        (im: imap id wf) itr
    :
    observe_state (itr, Tr.nb, im) = ([], (itr, Tr.nb, im)).
  Proof.
    unfold observe_state, epsilon. unfold Epsilon.epsilon. unfold proj1_sig. des_ifs.
    rename x into rawsttr. clear Heq.
    hexploit (observe_state_exists). intros OSP. eapply o in OSP; clear o.
    unfold observe_state_prop in OSP. hexploit OSP; clear OSP; eauto.
    i. inv H; clarify.
  Qed.

  Lemma observe_state_spin_div
        (im: imap id wf) itr
        (DIV: @Beh.diverge_index _ _ R im itr)
    :
    observe_state_trace (itr, Tr.spin, im) (observe_state (itr, Tr.spin, im)).
  Proof.
    punfold DIV. inv DIV.
    - pclearbot. hexploit observe_state_tau_spin; ss. 2:ss.
      2:{ i. des. setoid_rewrite H0; clear H0. econs; ss. }
      pfold. econs; eauto. pfold. econs; eauto.
    - pclearbot. hexploit observe_state_choose_spin; ss. 2: ss.
      2:{ i. des. setoid_rewrite H0; clear H0. econs; eauto; ss. }
      pfold. econs; eauto. pfold. econs; eauto.
    - pclearbot. hexploit observe_state_fair_spin; ss. 2: ss.
      2:{ i. des. setoid_rewrite H1; clear H1. econs; eauto; ss. }
      pfold. econs; eauto. pfold. econs; eauto.
    - rewrite observe_state_ub. econs; eauto.
  Qed.

  Lemma observe_state_spin
        (im: imap id wf) itr
        (BEH: @Beh.of_state _ _ R im itr Tr.spin)
    :
    observe_state_trace (itr, Tr.spin, im) (observe_state (itr, Tr.spin, im)).
  Proof.
    remember Tr.spin as tr. revert Heqtr. induction BEH using @Beh.of_state_ind2; i; ss.
    - eapply observe_state_spin_div; eauto.
    - clarify. hexploit observe_state_tau_spin; ss. 2: ss.
      2:{ i. des. setoid_rewrite H0; clear H0. econs; ss. }
      pfold. econs 5. punfold BEH.
    - clarify. hexploit observe_state_choose_spin; ss. 2: ss.
      2:{ i. des. setoid_rewrite H0; clear H0. econs; ss. i. splits; eauto. }
      pfold. econs 6. punfold BEH.
    - clarify. hexploit observe_state_fair_spin; ss. 2: ss.
      2:{ i. des. setoid_rewrite H1; clear H1. econs; ss; eauto. }
      pfold. econs 7; eauto. punfold BEH.
    - clarify. rewrite observe_state_ub. econs.
  Qed.

  Theorem observe_state_spec
          (sti: st_tr_im)
    :
    observe_state_prop sti (observe_state sti).
  Proof.
    destruct sti as [[st tr] im]. ii. rename H into BEH.
    ides st.
    - punfold BEH. inv BEH.
      + rewrite observe_state_ret. econs.
      + punfold SPIN. inv SPIN.
      + rewrite observe_state_nb. econs.
    - destruct (classic (tr = Tr.nb)) as [NB | NNB]; clarify.
      { rewrite observe_state_nb. econs. }
      destruct (classic (tr = Tr.spin)) as [SPIN | NSPIN]; clarify.
      { eapply observe_state_spin; eauto. }
      hexploit observe_state_tau; ss.
      4:{ i; des. setoid_rewrite H1; clear H1. econs; ss. }
      all: eauto.
    - destruct e.
      + destruct (classic (tr = Tr.nb)) as [NB | NNB]; clarify.
        { rewrite observe_state_nb. econs. }
        destruct (classic (tr = Tr.spin)) as [SPIN | NSPIN]; clarify.
        { eapply observe_state_spin; eauto. }
        hexploit observe_state_choose; ss.
        4:{ i; des. setoid_rewrite H1; clear H1. econs; ss. all: eauto. }
        all: eauto.
      + destruct (classic (tr = Tr.nb)) as [NB | NNB]; clarify.
        { rewrite observe_state_nb. econs. }
        destruct (classic (tr = Tr.spin)) as [SPIN | NSPIN]; clarify.
        { eapply observe_state_spin; eauto. }
        hexploit observe_state_fair; ss.
        4:{ i; des. setoid_rewrite H2; clear H2. econs; ss. all: eauto. }
        all: eauto.
      + destruct (classic (tr = Tr.nb)) as [NB | NNB]; clarify.
        { rewrite observe_state_nb. econs. }
        destruct (classic (tr = Tr.spin)) as [SPIN | NSPIN]; clarify.
        { eapply observe_state_spin; eauto. }
        punfold BEH. inv BEH; ss. eapply inj_pair2 in H3. clarify. pclearbot.
        rewrite observe_state_obs; eauto. econs.
      + rewrite observe_state_ub. econs.
  Qed.

  Lemma observe_state_trace_preserves
        st0 tr0 im0 evs st1 tr1 im1
        (BEH: Beh.of_state im0 st0 tr0)
        (OST: observe_state_trace (st0, tr0, im0) (evs, (st1, tr1, im1)))
    :
    Beh.of_state im1 st1 tr1.
  Proof.
    remember (st0, tr0, im0) as sti0. remember (evs, (st1, tr1, im1)) as esti1.
    move OST before wf0. revert_until OST.
    induction OST; i; ss; clarify.
    { punfold BEH. inv BEH. eapply inj_pair2 in H3. clarify. pclearbot. eauto. }
    { destruct (classic (tr0 = Tr.spin)) as [TRS | TRNS]; clarify.
      { hexploit SPIN; eauto. i; des; clarify. pfold. econs. eauto. }
      eapply H. ss. 2,3: eauto. eauto.
    }
    { destruct (classic (tr0 = Tr.spin)) as [TRS | TRNS]; clarify.
      { hexploit SPIN; eauto. i; des; clarify. pfold. econs. eauto. }
      eapply H. ss. 2,3: eauto. eauto.
    }
    { destruct (classic (tr0 = Tr.spin)) as [TRS | TRNS]; clarify.
      { hexploit SPIN; eauto. i; des; clarify. pfold. econs. eauto. }
      eapply H. ss. 2,3: eauto. eauto.
    }
  Qed.


  (** sti2raw reduction lemmas **)
  Lemma _sti2raw_red_evs
        (evs: list rawE) (sti: st_tr_im)
    :
    _sti2raw evs sti = RawTr.app evs (sti2raw sti).
  Proof.
    revert sti. induction evs; i. ss.
    match goal with | |- ?lhs = _ => replace lhs with (RawTr.ob lhs) end.
    2:{ symmetry. apply RawTr.ob_eq. }
    ss. f_equal. eauto.
  Qed.

  Lemma sti2raw_red_ret
        (im: imap id wf) (retv: R)
    :
    sti2raw (Ret retv, Tr.done retv, im) = RawTr.done retv.
  Proof.
    match goal with | |- ?lhs = _ => replace lhs with (RawTr.ob lhs) end.
    2:{ symmetry. apply RawTr.ob_eq. }
    ss. rewrite observe_state_ret. ss.
  Qed.

  Lemma sti2raw_red_nb
        (im: imap id wf) (st: @state _ R)
    :
    sti2raw (st, Tr.nb, im) = RawTr.nb.
  Proof.
    match goal with | |- ?lhs = _ => replace lhs with (RawTr.ob lhs) end.
    2:{ symmetry. apply RawTr.ob_eq. }
    ss. rewrite observe_state_nb. ss. des_ifs.
  Qed.

  Lemma sti2raw_red_ub
        (im: imap id wf) ktr tr
        (NNB: tr <> Tr.nb)
    :
    sti2raw (Vis Undefined ktr, tr, im) = tr2raw tr.
  Proof.
    match goal with | |- ?lhs = _ => replace lhs with (RawTr.ob lhs) end.
    2:{ symmetry. apply RawTr.ob_eq. }
    ss. rewrite observe_state_ub. ss.
    match goal with | |- _ = ?rhs => replace rhs with (RawTr.ob rhs) end.
    2:{ symmetry. apply RawTr.ob_eq. }
    ss. des_ifs.
  Qed.

  Ltac ireplace H := symmetry in H; apply simpobs in H; apply bisim_is_eq in H; rewrite H; clarify.

  Lemma sti2raw_red_aux
        st0 tr0 im0 ev evs
        (BEH: Beh.of_state im0 st0 tr0)
    :
    match
      match _observe st0 with
      | RetF _ =>
          match tr0 with
          | Tr.done retv => RawTr.cons ev (RawTr.app evs (RawTr.done retv))
          | Tr.nb => RawTr.cons ev (RawTr.app evs RawTr.nb)
          | _ => RawTr.cons ev (_sti2raw evs (st0, tr0, im0))
          end
      | VisF Undefined _ =>
          match tr0 with
          | Tr.nb => RawTr.cons ev (RawTr.app evs RawTr.nb)
          | _ => RawTr.cons ev (RawTr.app evs (tr2raw tr0))
          end
      | _ =>
          match tr0 with
          | Tr.nb => RawTr.cons ev (RawTr.app evs RawTr.nb)
          | _ => RawTr.cons ev (_sti2raw evs (st0, tr0, im0))
          end
      end
    with
    | RawTr.done retv => RawTr.done retv
    | RawTr.ub => RawTr.ub
    | RawTr.nb => RawTr.nb
    | RawTr.cons ev tl => RawTr.cons ev tl
    end = RawTr.cons ev (RawTr.app evs (sti2raw (st0, tr0, im0))).
  Proof.
    destruct (_observe st0) eqn:EQ.
    - ireplace EQ. destruct tr0 eqn:TR; ss; clarify.
      + punfold BEH. inv BEH. rewrite sti2raw_red_ret. ss.
      + punfold BEH. inv BEH. punfold SPIN. inv SPIN.
      + punfold BEH. inv BEH.
      + rewrite sti2raw_red_nb. ss.
      + punfold BEH. inv BEH.
    - ireplace EQ. destruct tr0 eqn:TR; ss; clarify.
      + rewrite _sti2raw_red_evs. ss.
      + rewrite _sti2raw_red_evs. ss.
      + rewrite _sti2raw_red_evs. ss.
      + rewrite sti2raw_red_nb. ss.
      + rewrite _sti2raw_red_evs. ss.
    - ireplace EQ. destruct e eqn:EV; ss; clarify.
      { destruct tr0 eqn:TR; ss; clarify.
        - rewrite _sti2raw_red_evs. ss.
        - rewrite _sti2raw_red_evs. ss.
        - rewrite _sti2raw_red_evs. ss.
        - rewrite sti2raw_red_nb. ss.
        - rewrite _sti2raw_red_evs. ss.
      }
      { destruct tr0 eqn:TR; ss; clarify.
        - rewrite _sti2raw_red_evs. ss.
        - rewrite _sti2raw_red_evs. ss.
        - rewrite _sti2raw_red_evs. ss.
        - rewrite sti2raw_red_nb. ss.
        - rewrite _sti2raw_red_evs. ss.
      }
      { destruct tr0 eqn:TR; ss; clarify.
        - rewrite _sti2raw_red_evs. ss.
        - rewrite _sti2raw_red_evs. ss.
        - rewrite _sti2raw_red_evs. ss.
        - rewrite sti2raw_red_nb. ss.
        - rewrite _sti2raw_red_evs. ss.
      }
      { destruct tr0 eqn:TR; ss; clarify.
        - rewrite sti2raw_red_ub; ss.
        - rewrite sti2raw_red_ub; ss.
        - rewrite sti2raw_red_ub; ss.
        - rewrite sti2raw_red_nb. ss.
        - rewrite sti2raw_red_ub; ss.
      }
  Qed.

  Lemma sti2raw_red_aux2
        st0 tr0 im0 ev
        (BEH: Beh.of_state im0 st0 tr0)
    :
    match
      match _observe st0 with
      | RetF _ =>
          match tr0 with
          | Tr.done retv => RawTr.cons ev (RawTr.done retv)
          | Tr.nb => RawTr.cons ev RawTr.nb
          | _ => RawTr.cons ev (sti2raw (st0, tr0, im0))
          end
      | VisF Undefined _ =>
          match tr0 with
          | Tr.nb => RawTr.cons ev RawTr.nb
          | _ => RawTr.cons ev (tr2raw tr0)
          end
      | _ =>
          match tr0 with
          | Tr.nb => RawTr.cons ev RawTr.nb
          | _ => RawTr.cons ev (sti2raw (st0, tr0, im0))
          end
      end
    with
    | RawTr.done retv => RawTr.done retv
    | RawTr.ub => RawTr.ub
    | RawTr.nb => RawTr.nb
    | RawTr.cons ev tl => RawTr.cons ev tl
    end = RawTr.cons ev (sti2raw (st0, tr0, im0)).
  Proof.
    hexploit sti2raw_red_aux; eauto. i. instantiate (1:=[]) in H. ss. eauto.
  Qed.

  Lemma sti2raw_red_obs
        (im: imap id wf) fn args rv tl ktr
        (BEH: Beh.of_state im (ktr rv) tl)
    :
    sti2raw (Vis (Observe fn args) ktr, Tr.cons (obsE_syscall fn args rv) tl, im) =
      RawTr.cons (inr (obsE_syscall fn args rv)) (sti2raw (ktr rv, tl, im)).
  Proof.
    match goal with | |- ?lhs = _ => replace lhs with (RawTr.ob lhs) end.
    2:{ symmetry. apply RawTr.ob_eq. }
    ss. rewrite observe_state_obs; eauto.
    eapply sti2raw_red_aux; eauto.
  Qed.

  Lemma sti2raw_red_tau
        (im: imap id wf) itr tr
        (BEH: Beh.of_state im (Tau itr) tr)
        (NNB: tr <> Tr.nb)
        (NSPIN: tr <> Tr.spin)
    :
    (Beh.of_state im itr tr) /\
      exists evs sti,
        observe_state_trace (itr, tr, im) (evs, sti) /\
          (sti2raw (Tau itr, tr, im) =
             RawTr.app ((inl silentE_tau) :: evs) (sti2raw sti)).
  Proof.
    hexploit observe_state_tau; eauto. i. des. split; eauto. esplits; eauto.
    match goal with | |- ?lhs = _ => replace lhs with (RawTr.ob lhs) end.
    2:{ symmetry. apply RawTr.ob_eq. }
    ss. rewrite H1; clear H1. destruct sti as [[st0 tr0] im0].
    ss. eapply sti2raw_red_aux. eapply observe_state_trace_preserves; eauto.
  Qed.

  Lemma sti2raw_red_tau_spin
        (im: imap id wf) itr tr
        (BEH: Beh.of_state im (Tau itr) tr)
        (NNB: tr <> Tr.nb)
        (SPIN: tr = Tr.spin)
    :
    (Beh.diverge_index im itr) /\
      (sti2raw (Tau itr, tr, im) =
         RawTr.cons (inl silentE_tau) (sti2raw (itr, tr, im))).
  Proof.
    hexploit observe_state_tau_spin; eauto. i. des. split; eauto.
    match goal with | |- ?lhs = _ => replace lhs with (RawTr.ob lhs) end.
    2:{ symmetry. apply RawTr.ob_eq. }
    ss. rewrite H0; clear H0.
    ss. eapply sti2raw_red_aux2. clarify. pfold. econs. eauto.
  Qed.

  Lemma sti2raw_red_choose
        (im: imap id wf) tr X ktr
        (BEH: Beh.of_state im (Vis (Choose X) ktr) tr)
        (NNB: tr <> Tr.nb)
        (NSPIN: tr <> Tr.spin)
    :
    exists x,
      (Beh.of_state im (ktr x) tr) /\
        exists evs sti,
          observe_state_trace (ktr x, tr, im) (evs, sti) /\
            (sti2raw (Vis (Choose X) ktr, tr, im) =
               RawTr.app ((inl silentE_tau) :: evs) (sti2raw sti)).
  Proof.
    hexploit observe_state_choose; eauto. i. des. esplits; eauto.
    match goal with | |- ?lhs = _ => replace lhs with (RawTr.ob lhs) end.
    2:{ symmetry. apply RawTr.ob_eq. }
    ss. rewrite H1; clear H1. destruct sti as [[st0 tr0] im0].
    ss. eapply sti2raw_red_aux. eapply observe_state_trace_preserves; eauto.
  Qed.

  Lemma sti2raw_red_choose_spin
        (im: imap id wf) tr X ktr
        (BEH: Beh.of_state im (Vis (Choose X) ktr) tr)
        (NNB: tr <> Tr.nb)
        (SPIN: tr = Tr.spin)
    :
    exists x,
      (Beh.diverge_index im (ktr x)) /\
        (sti2raw (Vis (Choose X) ktr, tr, im) =
           RawTr.cons (inl silentE_tau) (sti2raw (ktr x, tr, im))).
  Proof.
    hexploit observe_state_choose_spin; eauto. i. des. esplits; eauto.
    match goal with | |- ?lhs = _ => replace lhs with (RawTr.ob lhs) end.
    2:{ symmetry. apply RawTr.ob_eq. }
    ss. rewrite H0; clear H0.
    ss. eapply sti2raw_red_aux2. clarify. pfold. econs; eauto.
  Qed.

  Lemma sti2raw_red_fair
        (im: imap id wf) tr fm ktr
        (BEH: Beh.of_state im (Vis (Fair fm) ktr) tr)
        (NNB: tr <> Tr.nb)
        (NSPIN: tr <> Tr.spin)
    :
    exists (im0: imap id wf),
      (fair_update im im0 fm) /\
        (Beh.of_state im0 (ktr tt) tr) /\
        exists evs sti,
          observe_state_trace (ktr tt, tr, im0) (evs, sti) /\
            (sti2raw (Vis (Fair fm) ktr, tr, im) =
               RawTr.app ((inl (silentE_fair fm)) :: evs) (sti2raw sti)).
  Proof.
    hexploit observe_state_fair; eauto. i. des. esplits; eauto.
    match goal with | |- ?lhs = _ => replace lhs with (RawTr.ob lhs) end.
    2:{ symmetry. apply RawTr.ob_eq. }
    ss. rewrite H2; clear H2. destruct sti as [[st0 tr0] im1].
    ss. eapply sti2raw_red_aux. eapply observe_state_trace_preserves; eauto.
  Qed.

  Lemma sti2raw_red_fair_spin
        (im: imap id wf) tr fm ktr
        (BEH: Beh.of_state im (Vis (Fair fm) ktr) tr)
        (NNB: tr <> Tr.nb)
        (SPIN: tr = Tr.spin)
    :
    exists (im0: imap id wf),
      (fair_update im im0 fm) /\
        (Beh.diverge_index im0 (ktr tt)) /\
        (sti2raw (Vis (Fair fm) ktr, tr, im) =
           RawTr.cons (inl (silentE_fair fm)) (sti2raw (ktr tt, tr, im0))).
  Proof.
    hexploit observe_state_fair_spin; eauto. i. des. esplits; eauto.
    match goal with | |- ?lhs = _ => replace lhs with (RawTr.ob lhs) end.
    2:{ symmetry. apply RawTr.ob_eq. }
    ss. rewrite H1; clear H1.
    ss. eapply sti2raw_red_aux2. clarify. pfold. econs; eauto.
  Qed.



  Lemma sti2raw_exists
        st0 tr0 im0
        (BEH: Beh.of_state im0 st0 tr0)
    :
    exists evs st1 tr1 im1,
      (sti2raw (st0, tr0, im0) = RawTr.app evs (sti2raw (st1, tr1, im1))) /\
        (observe_state_trace (st0, tr0, im0) (evs, (st1, tr1, im1))).
  Proof.
    induction BEH using @Beh.of_state_ind2.
    { exists []. ss. esplits; eauto. econs. }
    { punfold H. inv H.
      { pclearbot. hexploit sti2raw_red_tau_spin.
        4:{ i; des. rewrite H0; clear H0.
            match goal with | |- exists _ _ _ _, (RawTr.cons ?ev _ = _) /\ _ => exists [ev] end.
            ss. esplits; eauto. econs; ss. }
        all: ss. pfold. econs. pfold; econs; eauto.
      }
      { pclearbot. hexploit sti2raw_red_choose_spin.
        4:{ i; des. rewrite H0; clear H0.
            match goal with | |- exists _ _ _ _, (RawTr.cons ?ev _ = _) /\ _ => exists [ev] end.
            ss. esplits; eauto. econs; ss. i; eauto. }
        all: ss. pfold. econs. pfold; econs; eauto.
      }
      { pclearbot. hexploit sti2raw_red_fair_spin.
        4:{ i; des. rewrite H1; clear H1.
            match goal with | |- exists _ _ _ _, (RawTr.cons ?ev _ = _) /\ _ => exists [ev] end.
            ss. esplits; eauto. econs; ss; eauto. }
        all: ss. pfold. econs. pfold; econs; eauto.
      }
      { hexploit sti2raw_red_ub.
        2:{ i; des. eexists. exists (Vis Undefined ktr), (Tr.spin), (imap0).
            rewrite ! H. instantiate (1:=[]). ss. split; eauto. econs. }
        all: ss. }
    }
    { exists []. ss. esplits; eauto. econs. }
    { rewrite sti2raw_red_obs; eauto. exists [inr (obsE_syscall fn args rv)]. ss.
      esplits; eauto. econs. }
    { destruct (classic (tr = Tr.nb)) as [NB | NNB]; clarify.
      { des. exists []. ss. esplits; eauto. econs. }
      destruct (classic (tr = Tr.spin)) as [TRS | TRNS]; clarify.
      { des. hexploit sti2raw_red_tau_spin.
        4:{ i; des. rewrite H0; clear H0. exists [inl silentE_tau]. ss. esplits; eauto. econs; ss. }
        all: ss. eapply Beh.beh_tau0; eauto. }
      des. hexploit sti2raw_red_tau.
      4:{ i; des. rewrite H1; clear H1. destruct sti as [[st0 tr0] im0]. esplits; eauto.
          econs; ss. }
      all: ss. eapply Beh.beh_tau0; eauto.
    }
    { destruct (classic (tr = Tr.nb)) as [NB | NNB]; clarify.
      { des. exists []. ss. esplits; eauto. econs. }
      destruct (classic (tr = Tr.spin)) as [TRS | TRNS]; clarify.
      { des. hexploit sti2raw_red_choose_spin.
        4:{ i; des. rewrite H0; clear H0. exists [inl silentE_tau]. ss. esplits; eauto. econs; ss.
            i; splits; eauto. }
        all: ss. eapply Beh.beh_choose0; eauto. }
      des. hexploit sti2raw_red_choose.
      4:{ i; des. rewrite H1; clear H1. destruct sti as [[st0 tr0] im0]. esplits; eauto.
          econs; ss; eauto. }
      all: ss. eapply Beh.beh_choose0; eauto.
    }
    { destruct (classic (tr = Tr.nb)) as [NB | NNB]; clarify.
      { des. exists []. ss. esplits; eauto. econs. }
      destruct (classic (tr = Tr.spin)) as [TRS | TRNS]; clarify.
      { des. hexploit sti2raw_red_fair_spin.
        4:{ i; des. rewrite H1; clear H1. exists [inl (silentE_fair fmap)]. ss. esplits; eauto.
            econs; ss; eauto. }
        all: ss. eapply Beh.beh_fair; eauto. }
      des. hexploit sti2raw_red_fair.
      4:{ i; des. rewrite H2; clear H2. destruct sti as [[nst ntr] nim]. esplits; eauto.
          econs; ss; eauto. }
      all: ss. eapply Beh.beh_fair; eauto.
    }
    { destruct (classic (tr = Tr.nb)) as [NB | NNB]; clarify.
      { des. exists []. ss. esplits; eauto. econs. }
      hexploit sti2raw_red_ub.
      2:{ i; des. exists [], (Vis Undefined ktr), tr, imap0. rewrite ! H. ss. split; eauto. econs. }
      all: ss.
    }
  Qed.

  Lemma sti2raw_raw_beh_spin
        (im: imap id wf) st
        (DIV: Beh.diverge_index im st)
    :
    RawBeh.of_state (R:=R) st (sti2raw (st, Tr.spin, im)).
  Proof.
    revert_until wf0. pcofix CIH. i. punfold DIV. inv DIV.
    - pclearbot. hexploit sti2raw_red_tau_spin.
      4:{ i; des. rewrite H0; clear H0. pfold. econs. eauto. }
      2,3: ss. pfold. econs. pfold. econs. eauto.
    - pclearbot. hexploit sti2raw_red_choose_spin.
      4:{ i; des. rewrite H0; clear H0. pfold. econs. eauto. }
      2,3: ss. pfold. econs. pfold. econs. eauto.
    - pclearbot. hexploit sti2raw_red_fair_spin.
      4:{ i; des. rewrite H1; clear H1. pfold. econs. eauto. }
      2,3: ss. pfold. econs. pfold. econs; eauto.
    - hexploit sti2raw_red_ub.
      2:{ i; des. rewrite H; clear H. pfold. econs. }
      all: ss.
  Qed.

  Theorem sti2raw_raw_beh
          (im0: imap id wf) st0 tr0
          (BEH: Beh.of_state im0 st0 tr0)
    :
    RawBeh.of_state (R:=R) st0 (sti2raw (st0, tr0, im0)).
  Proof.
    revert_until wf0. pcofix CIH; i.
    hexploit sti2raw_exists; eauto. i. des. rewrite H; clear H. rename H0 into OST.
    remember (st0, tr0, im0) as sti0. remember (evs, (st1, tr1, im1)) as esti1.
    move OST before CIH. revert_until OST. induction OST; i; ss; clarify.
    { ss. rewrite sti2raw_red_ret. pfold. econs. }
    { ss. pfold. econs. punfold BEH. inv BEH. eapply inj_pair2 in H3; clarify.
      pclearbot. eauto. }
    { destruct (classic (tr0 = Tr.spin)) as [TRS | TRNS]; clarify.
      { hexploit SPIN; clear SPIN; eauto. i; des; clarify. ss.
        pfold. econs. right; eapply CIH. pfold. econs; eauto. }
      clear SPIN. ss. pfold. econs. left. eapply H; eauto.
    }
    { destruct (classic (tr0 = Tr.spin)) as [TRS | TRNS]; clarify.
      { hexploit SPIN; clear SPIN; eauto. i; des; clarify. ss.
        pfold. econs. right; eapply CIH. pfold. econs; eauto. }
      clear SPIN. ss. pfold. econs. left. eapply H; eauto.
    }
    { destruct (classic (tr0 = Tr.spin)) as [TRS | TRNS]; clarify.
      { hexploit SPIN; clear SPIN; eauto. i; des; clarify. ss.
        pfold. econs. right; eapply CIH. pfold. econs; eauto. }
      clear SPIN. ss. pfold. econs. left. eapply H; eauto.
    }
    { ss. pfold. econs. }
    { ss. rewrite sti2raw_red_nb. pfold. econs. }
  Qed.



  Lemma sti2raw_raw_spin
        itr im
        (DIV: @Beh.diverge_index _ wf R im itr)
    :
    raw_spin (sti2raw (itr, Tr.spin, im)).
  Proof.
    revert_until wf0. pcofix CIH; i. punfold DIV. inv DIV.
    - pclearbot. hexploit sti2raw_red_tau_spin.
      4:{ i; des. rewrite H0; clear H0. pfold. econs. eauto. }
      all: ss. pfold. econs. pfold. econs. eauto.
    - pclearbot. hexploit sti2raw_red_choose_spin.
      4:{ i; des. rewrite H0; clear H0. pfold. econs. eauto. }
      all: ss. pfold. econs. pfold. econs. eauto.
    - pclearbot. hexploit sti2raw_red_fair_spin.
      4:{ i; des. rewrite H1; clear H1. pfold. econs. eauto. }
      all: ss. pfold. econs. pfold. econs; eauto.
    - hexploit sti2raw_red_ub.
      2:{ i; des. rewrite H; clear H. rewrite tr2raw_red_spin.
          eapply paco2_mon. eapply raw_spin_trace_spec. ss. }
      all: ss.
  Qed.

  Lemma sti2raw_extract_spin
        st im
        (DIV: @Beh.diverge_index _ wf R im st)
    :
    extract_tr (sti2raw (st, Tr.spin, im)) Tr.spin.
  Proof.
    punfold DIV. inv DIV.
    - pclearbot. hexploit sti2raw_red_tau_spin.
      4:{ i; des. rewrite H0; clear H0. pfold. econs. pfold. econs.
          left. eapply sti2raw_raw_spin; eauto. }
      all: ss. pfold. econs. pfold. econs; eauto.
    - pclearbot. hexploit sti2raw_red_choose_spin.
      4:{ i; des. rewrite H0; clear H0. pfold. econs. pfold. econs.
          left. eapply sti2raw_raw_spin; eauto. }
      all: ss. pfold. econs. pfold. econs; eauto.
    - pclearbot. hexploit sti2raw_red_fair_spin.
      4:{ i; des. rewrite H1; clear H1. pfold. econs. pfold. econs.
          left. eapply sti2raw_raw_spin; eauto. }
      all: ss. pfold. econs. pfold. econs; eauto.
    - hexploit sti2raw_red_ub.
      2:{ i; des. rewrite H; clear H. rewrite tr2raw_red_spin.
          pfold. econs. eapply raw_spin_trace_spec. }
      all: ss.
  Qed.

  Theorem sti2raw_extract
          st0 tr0 im0
          (BEH: Beh.of_state im0 st0 tr0)
    :
    extract_tr (sti2raw (st0, tr0, im0)) tr0.
  Proof.
    ginit. revert_until wf0. gcofix CIH. i.
    destruct (classic (tr0 = Tr.spin)) as [TRS | TRNS]; clarify.
    { gfinal. right. eapply paco3_mon. eapply sti2raw_extract_spin.
      eapply beh_implies_spin; eauto. ss. }
    hexploit sti2raw_exists; eauto. i; des. rewrite H; clear H. rename H0 into OST.
    remember (st0, tr0, im0) as sti0. remember (evs, (st1, tr1, im1)) as esti1.
    move OST before CIH. revert_until OST. induction OST; i; ss; clarify.
    { ss. rewrite sti2raw_red_ret. guclo extract_tr_indC_spec. econs. }
    { punfold BEH. inv BEH. eapply inj_pair2 in H3. clarify. ss. pclearbot.
      gfinal. right. pfold. econs. eauto. }
    { ss. guclo extract_tr_indC_spec. econs. eauto. }
    { ss. guclo extract_tr_indC_spec. econs. eauto. }
    { ss. guclo extract_tr_indC_spec. econs. eauto. }
    { ss. gfinal. right.
      destruct (classic (tr0 = Tr.nb)) as [NB | NNB]; clarify.
      { rewrite sti2raw_red_nb. eauto. }
      rewrite sti2raw_red_ub; ss. eapply paco3_mon. eapply extract_tr_tr2raw. ss.
    }
    { ss. gfinal. right. rewrite sti2raw_red_nb. eauto. }
  Qed.

End ExtractRaw.



Section FAIR.

  Variable id: ID.
  Variable wf: WF.
  Variable wf0: T wf.
  Variable R: Type.

  Lemma raw_spin_trace_fair
        im
    :
    RawTr.fair_ord (id:=id) (wf:=wf) im (raw_spin_trace id R).
  Proof.
    revert_until R. pcofix CIH; i. rewrite raw_spin_trace_red.
    pfold. econs; eauto.
  Qed.

  Lemma tr2raw_fair
        im tr
    :
    RawTr.fair_ord (wf:=wf) (R:=R) im (tr2raw id tr).
  Proof.
    revert_until R. pcofix CIH; i. replace (tr2raw id tr) with (RawTr.ob (tr2raw id tr)).
    2:{ symmetry. apply RawTr.ob_eq. }
    ss. destruct tr eqn:TR; clarify.
    { pfold. econs. }
    { rewrite raw_spin_trace_red. pfold. econs. left.
      eapply paco3_mon. eapply raw_spin_trace_fair. ss. }
    { pfold; econs. }
    { pfold; econs. }
    { pfold. econs; eauto. }
  Qed.

  Theorem sti2raw_preserves_fairness
          (st: @state _ R) (im: imap id wf) tr
          (BEH: Beh.of_state im st tr)
    :
    RawTr.is_fair_ord wf (sti2raw wf0 (st, tr, im)).
  Proof.
    rr. exists im. revert_until R. pcofix CIH; i.
    hexploit sti2raw_exists; eauto. i. des. rewrite H; clear H. rename H0 into OST.
    remember (st, tr, im) as sti. remember (evs, (st1, tr1, im1)) as esti1.
    move OST before CIH. revert_until OST. induction OST; i; ss; clarify; ss.
    { rewrite @sti2raw_red_ret. pfold. econs. }
    { punfold BEH. inv BEH. eapply inj_pair2 in H3; clarify. pclearbot. pfold. econs; eauto. }
    { destruct (classic (tr0 = Tr.spin)) as [TRS | TRNS]; clarify.
      { hexploit SPIN; clear SPIN; eauto. i; des; clarify. ss.
        pfold. econs. right; eapply CIH. pfold. econs; eauto. }
      clear SPIN. pfold. econs; eauto.
    }
    { destruct (classic (tr0 = Tr.spin)) as [TRS | TRNS]; clarify.
      { hexploit SPIN; clear SPIN; eauto. i; des; clarify. ss.
        pfold. econs. right; eapply CIH. pfold. econs; eauto. }
      clear SPIN. pfold. econs; eauto.
    }
    { destruct (classic (tr0 = Tr.spin)) as [TRS | TRNS]; clarify.
      { hexploit SPIN; clear SPIN; eauto. i; des; clarify. ss.
        pfold. econs; eauto. right; eapply CIH. pfold. econs; eauto. }
      clear SPIN. pfold. econs; eauto.
    }
    { destruct (classic (tr0 = Tr.nb)) as [NB | NNB]; clarify.
      { rewrite @sti2raw_red_nb. pfold; econs. }
      rewrite @sti2raw_red_ub; eauto. eapply paco3_mon. eapply tr2raw_fair. ss.
    }
    { rewrite @sti2raw_red_nb. pfold; econs. }
  Qed.

  Lemma fair_spin_diverge_index
        st im raw
        (RSPIN: raw_spin raw)
        (BEH: RawBeh.of_state st raw)
        (FAIR: RawTr.fair_ord im raw)
    :
    Beh.diverge_index (id:=id) (wf:=wf) (R:=R) im st.
  Proof.
    revert_until R. pcofix CIH; i. punfold BEH. inv BEH.
    { punfold RSPIN. inv RSPIN. }
    { punfold RSPIN. inv RSPIN. }
    { punfold RSPIN. inv RSPIN. }
    { punfold RSPIN. inv RSPIN. punfold FAIR. inv FAIR. pclearbot. rr in TL1. des; ss.
      pfold. econs; eauto. }
    { punfold RSPIN. inv RSPIN. punfold FAIR. inv FAIR. pclearbot. rr in TL1. des; ss.
      pfold. econs; eauto. }
    { punfold RSPIN. inv RSPIN. punfold FAIR. inv FAIR. pclearbot. rr in TL1. des; ss.
      pfold. econs; eauto. }
    { pfold. econs. }
  Qed.

  Lemma rawbeh_extract_is_beh_fix
        (st: state (R:=R)) (raw: RawTr.t (R:=R)) tr (im: imap id wf)
        (BEH0: RawBeh.of_state st raw)
        (FAIR: RawTr.fair_ord im raw)
        (EXT: extract_tr raw tr)
    :
    Beh.of_state im st tr.
  Proof.
    ginit. revert_until R. gcofix CIH; i.
    move EXT before CIH. revert_until EXT. induction EXT using @extract_tr_ind2; i.
    { punfold BEH0. inv BEH0.
      { guclo Beh.of_state_indC_spec. econs. }
      { guclo Beh.of_state_indC_spec. econs. }
    }
    { guclo Beh.of_state_indC_spec. econs. eapply fair_spin_diverge_index; eauto. }
    { punfold BEH0. inv BEH0. guclo Beh.of_state_indC_spec. econs. }
    { guclo Beh.of_state_indC_spec. econs. }
    { punfold BEH0. inv BEH0.
      { pclearbot. gfinal. right. pfold. econs. right. eapply CIH. eauto. all: eauto.
        punfold FAIR. inv FAIR. pclearbot. eauto. }
      { guclo Beh.of_state_indC_spec. econs. }
    }
    { punfold BEH0. inv BEH0.
      { punfold FAIR. inv FAIR. pclearbot. guclo Beh.of_state_indC_spec. econs; eauto. }
      { punfold FAIR. inv FAIR. pclearbot. guclo Beh.of_state_indC_spec. econs; eauto. }
      { punfold FAIR. inv FAIR. pclearbot. guclo Beh.of_state_indC_spec. econs; eauto. }
      { guclo Beh.of_state_indC_spec. econs. }
    }
  Qed.

  Theorem rawbeh_extract_is_beh
          (st: state (R:=R)) (raw: RawTr.t (R:=R)) tr
          (BEH: RawBeh.of_state_fair_ord (wf:=wf) st raw)
          (EXT: extract_tr raw tr)
    :
    exists (im: imap id wf), Beh.of_state im st tr.
  Proof.
    rr in BEH. des. rr in FAIR. des.
    hexploit rawbeh_extract_is_beh_fix; eauto.
  Qed.

End FAIR.



Section EQUIV.

  Variable id: ID.
  Variable wf: WF.
  Variable wf0: T wf.
  Variable R: Type.

  Theorem IndexBeh_implies_SelectBeh
          (st: state (R:=R)) (tr: Tr.t (R:=R))
          (BEH: exists (im: imap id wf), Beh.of_state im st tr)
    :
    exists raw, (<<EXTRACT: extract_tr raw tr>>) /\ (<<BEH: RawBeh.of_state_fair_ord (wf:=wf) st raw>>).
  Proof.
    des. exists (sti2raw wf0 (st, tr, im)). splits. eapply sti2raw_extract; eauto.
    rr. splits. eapply sti2raw_raw_beh; eauto. eapply sti2raw_preserves_fairness; eauto.
  Qed.

  Lemma SelectBeh_implies_IndexBeh_fix
        (st: state (R:=R)) (raw: RawTr.t (R:=R)) (im: imap id wf)
        (BEH: RawBeh.of_state st raw)
        (FAIR: RawTr.fair_ord im raw)
    :
    exists tr, (<<EXTRACT: extract_tr raw tr>>) /\ (<<BEH: Beh.of_state im st tr>>).
  Proof.
    exists (raw2tr raw). splits. eapply raw2tr_extract.
    eapply rawbeh_extract_is_beh_fix; eauto. eapply raw2tr_extract.
  Qed.

  Theorem SelectBeh_implies_IndexBeh
          (st: state (R:=R)) (raw: RawTr.t (R:=R))
          (BEH: RawBeh.of_state_fair_ord (wf:=wf) st raw)
    :
    exists tr, (<<EXTRACT: extract_tr raw tr>>) /\ (exists (im: imap id wf), <<BEH: Beh.of_state im st tr>>).
  Proof.
    exists (raw2tr raw). splits. eapply raw2tr_extract.
    eapply rawbeh_extract_is_beh; eauto. eapply raw2tr_extract.
  Qed.

End EQUIV.
