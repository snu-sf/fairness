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

  (* Lemma inhabited_tr R: inhabited (Tr.t (R:=R)). *)
  (* Proof. *)
  (*   econs. exact Tr.ub. *)
  (* Qed. *)

  (* Lemma inhabited_raw R: inhabited (RawTr.t (R:=R)). *)
  (* Proof. *)
  (*   econs. exact RawTr.ub. *)
  (* Qed. *)

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

  Definition observe_raw_prop {R} (raw: @RawTr.t _ R) (obstl: option (prod (option obsE) RawTr.t)): Prop :=
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


  Lemma observe_raw_prop_impl_observe_raw
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

  (* observe_raw reductions *)
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


  (* Lemma observe_raw_eutt *)
  (*       R (raw: @RawTr.t _ R) silent *)
  (*   : *)
  (*   observe_raw (RawTr.cons (inl silent) raw) = observe_raw raw. *)
  (* Proof. *)
  (*   eapply observe_raw_prop_impl_observe_raw. destruct (observe_raw raw) eqn:EQ. *)
  (*   2:{ ss. eapply raw_spin_observe in EQ. pfold. econs. auto. } *)
  (*   destruct p as [obs tl]. ss. econs. *)

  (* Lemma observe_raw_spec *)
  (*       R (raw: @RawTr.t _ R) *)
  (*   : *)
  (*   observe_raw_prop raw (observe_raw raw). *)
  (* Proof. *)
  (*   destruct raw. *)
  (*   - rewrite observe_raw_done. econs. *)
  (*   - rewrite observe_raw_ub. econs. *)
  (*   - rewrite observe_raw_nb. econs. *)
  (*   - destruct hd as [silent | obs]. *)
  (*     2:{ rewrite observe_raw_obs. econs. } *)

  (* Lemma observe_raw_false *)
  (*       R (raw: @RawTr.t _ R) ev tl *)
  (*   : *)
  (*   observe_raw raw <> Some (None, RawTr.cons ev tl). *)
  (* Proof. *)
  (*   ii. eapply observe_raw_prop_false. *)
  (*   rewrite <- H. unfold observe_raw, epsilon. eapply Epsilon.epsilon_spec. eauto. *)


  CoFixpoint raw2tr {R} (raw: @RawTr.t _ R): (@Tr.t R) :=
    match observe_raw raw with
    | None => Tr.spin
    | Some (None, RawTr.done retv) => Tr.done retv
    | Some (None, RawTr.ub) => Tr.ub
    | Some (None, RawTr.nb) => Tr.nb
    | Some (None, RawTr.cons _ _) => Tr.ub
    | Some (Some obs, tl) => Tr.cons obs (raw2tr tl)
    end.

  (* reduction lemmas *)
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
        R (raw: @RawTr.t _ R) obs tl
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
        R (raw: @RawTr.t _ R) silent tl
    :
    (raw2tr (RawTr.cons (inl silent) tl)) = (raw2tr (R:=R) tl).
  Proof.
    match goal with | |- ?lhs = _ => replace lhs with (Tr.ob lhs) end.
    2:{ symmetry. apply Tr.ob_eq. }
    ss. rewrite observe_raw_obs. ss.
  Qed.

  Lemma raw2tr_extract
        R (raw: @RawTr.t _ R)
    :
    extract_tr raw (raw2tr raw).
  Proof.
    revert_until R. pcofix CIH. i.

    destruct raw.
    { 



    unfold raw2tr, epsilon. eapply Epsilon.epsilon_spec. eexists.

  (* Lemma match_eq_obs *)
  (*       R (tr: @Tr.t R) raw tl *)
  (*       obs *)
  (*       (MATCH0: extract_tr raw tl) *)
  (*       (EXTRACT: extract_tr (RawTr.cons (inr obs) raw) tr) *)
  (*   : *)
  (*   tr = Tr.cons obs tl. *)
  (* Proof. *)
  (*   punfold EXTRACT. inv EXTRACT; eauto. punfold RSPIN. inv RSPIN. *)
  (*   f_equal. pclearbot. *)
  (* Qed. *)

  (* Lemma extract_tr_cih *)
  (*       R (r: forall R, RawTr.t -> Tr.t -> Prop) *)
  (*       raw tr *)
  (*       (CIH: @r R raw tr) *)
  (*       (EXTRACT: _extract_tr (R:=R) (upaco3 _extract_tr r) raw tr) *)
  (*   : *)
  (*   Prop. *)

  (* CoFixpoint raw2tr {R} (raw: @RawTr.t _ R): (@Tr.t R) := *)
  (*   epsilon _ (@inhabited_tr R) *)
  (*           (fun tr => forall (r: forall R, RawTr.t -> Tr.t -> Prop) (CIH: forall raw0, @r R raw0 (raw2tr raw0)), *)
  (*                _extract_tr (R:=R) (upaco3 _extract_tr r) raw tr). *)


  (* Definition raw2tr {R} (raw: @RawTr.t _ R): (@Tr.t R) := *)
  (*   epsilon _ (@inhabited_tr R) (fun tr => forall etr (EQ: Tr.eq etr tr), extract_tr raw etr). *)

  (* Lemma raw2tr_match *)
  (*       R (raw: @RawTr.t _ R) *)
  (*   : *)
  (*   extract_tr raw (raw2tr raw). *)
  (* Proof. *)
  (*   remember (raw2tr raw) as tr. assert (EQ: Tr.eq tr (raw2tr raw)). *)
  (*   { rewrite Heqtr. reflexivity. } *)
  (*   clear Heqtr. revert_until raw. *)
  (*   unfold raw2tr, epsilon. eapply Epsilon.epsilon_spec. *)

  Definition raw2tr {R} (raw: @RawTr.t _ R): (@Tr.t R) :=
    epsilon _ (@inhabited_tr R) (extract_tr raw).

  Lemma raw2tr_match
        R (raw: @RawTr.t _ R)
    :
    extract_tr raw (raw2tr raw).
  Proof.
    unfold raw2tr, epsilon. eapply Epsilon.epsilon_spec. eexists.
    














  Definition raw2tr {R} (raw: @RawTr.t _ R): (@Tr.t R) :=
    epsilon _ (@inhabited_tr R)
            (fun tr => forall (r: forall R, RawTr.t -> Tr.t -> Prop)
                      (CIH: forall raw0 tr0 (EXTRACT: extract_tr (R:=R) raw0 tr0), @r R raw tr),
                 _extract_tr (R:=R) (upaco3 _extract_tr r) raw tr).

  Lemma extract_tr_is_raw2tr
        R raw tr
        (EXTRACT: extract_tr (R:=R) raw tr)
    :
    tr = raw2tr raw.
  Proof.
    punfold EXTRACT. inv EXTRACT.
    { symmetry. eapply match_eq_done.
      admit.
    }
    4:{ 

      
    5:{ 
    2:{ 

  Definition raw2tr {R} (raw: @RawTr.t _ R): (@Tr.t R) :=
    epsilon _ (@inhabited_tr R)
            (fun tr => forall (r: forall R, RawTr.t -> Tr.t -> Prop) (CIH: @r R raw tr),
                 _extract_tr (R:=R) (upaco3 _extract_tr r) raw tr).

  Lemma raw2tr_match
        R (raw: @RawTr.t _ R)
    :
    extract_tr raw (raw2tr raw).
  Proof.
    remember (raw2tr raw) as tr.
    revert_until R. pcofix CIH; i. destruct raw.
    { hexploit CIH. eapply Heqtr. intro CIH2.
      clear CIH. rewrite Heqtr. rewrite Heqtr in CIH2. clear Heqtr.
      depgen r. unfold raw2tr, epsilon. pfold.
      eapply Epsilon.epsilon_spec.
      exists (Tr.done retv). i. econs 1.
    }
    { hexploit CIH. eapply Heqtr. intro CIH2.
      clear CIH. rewrite Heqtr. rewrite Heqtr in CIH2. clear Heqtr.
      depgen r. unfold raw2tr, epsilon. pfold.
      eapply Epsilon.epsilon_spec.
      exists (Tr.ub). i. econs 3.
    }
    { hexploit CIH. eapply Heqtr. intro CIH2.
      clear CIH. rewrite Heqtr. rewrite Heqtr in CIH2. clear Heqtr.
      depgen r. unfold raw2tr, epsilon. pfold.
      eapply Epsilon.epsilon_spec.
      exists (Tr.nb). i. econs 4.
    }

    { destruct hd as [silent | obs].
      2:{ hexploit CIH. eapply Heqtr. intro CIH2.
          clear CIH. rewrite Heqtr. rewrite Heqtr in CIH2. clear Heqtr.
          depgen r. unfold raw2tr, epsilon. pfold.
          eapply Epsilon.epsilon_spec.
          exists (Tr.cons obs (raw2tr raw)). i. econs 5.
          right.
      }






  Definition raw2tr {R} (raw: @RawTr.t _ R): (@Tr.t R) :=
    epsilon _ (@inhabited_tr R) (extract_tr raw).

  Definition st2raw {R} (st: state): (RawTr.t (R:=R)) :=
    epsilon _ (@inhabited_raw R) (RawBeh.of_state st).


  Lemma raw2tr_match_done
        R (retv: R)
    :
    extract_tr (RawTr.done retv) (raw2tr (RawTr.done retv)).
  Proof.
    unfold raw2tr, epsilon. eapply Epsilon.epsilon_spec. eexists.
    pfold. econs 1.
  Qed.

  Lemma match_eq_done
        R (tr: @Tr.t R) retv
        (EXTRACT: extract_tr (RawTr.done retv) tr)
    :
    tr = Tr.done retv.
  Proof.
    punfold EXTRACT. inv EXTRACT; eauto. punfold RSPIN. inv RSPIN.
  Qed.

  Lemma raw2tr_done
        R (retv: R)
    :
    raw2tr (RawTr.done retv) = Tr.done retv.
  Proof.
    eapply match_eq_done. eapply raw2tr_match_done.
  Qed.

  Lemma raw2tr_match_ub
        R
    :
    @extract_tr _ R RawTr.ub (raw2tr RawTr.ub).
  Proof.
    unfold raw2tr, epsilon. eapply Epsilon.epsilon_spec. eexists.
    pfold. econs 3.
  Qed.

  Lemma match_eq_ub
        R (tr: @Tr.t R)
        (EXTRACT: extract_tr RawTr.ub tr)
    :
    tr = Tr.ub.
  Proof.
    punfold EXTRACT. inv EXTRACT; eauto. punfold RSPIN. inv RSPIN.
  Qed.

  Lemma raw2tr_ub
        R
    :
    @raw2tr R RawTr.ub = Tr.ub.
  Proof.
    eapply match_eq_ub. eapply raw2tr_match_ub.
  Qed.

  Lemma raw2tr_match_nb
        R
    :
    @extract_tr _ R RawTr.nb (raw2tr RawTr.nb).
  Proof.
    unfold raw2tr, epsilon. eapply Epsilon.epsilon_spec. eexists.
    pfold. econs 4.
  Qed.

  Lemma match_eq_nb
        R (tr: @Tr.t R)
        (EXTRACT: extract_tr RawTr.nb tr)
    :
    tr = Tr.nb.
  Proof.
    punfold EXTRACT. inv EXTRACT; eauto. punfold RSPIN. inv RSPIN.
  Qed.

  Lemma raw2tr_nb
        R
    :
    @raw2tr R RawTr.nb = Tr.nb.
  Proof.
    eapply match_eq_nb. eapply raw2tr_match_nb.
  Qed.


  (* Lemma raw2tr_match_obs1 *)
  (*       R obs (raw: @RawTr.t _ R) *)
  (*   : *)
  (*   @extract_tr _ R (RawTr.cons (inr obs) raw) (raw2tr (RawTr.cons (inr obs) raw)). *)
  (* Proof. *)
  (*   revert_until R. pcofix CIH; i. *)
  (*   pfold. eapply extract_tr_mon. *)
  (*   { instantiate (1:=bot3). *)

  (*     unfold raw2tr, epsilon. eapply Epsilon.epsilon_spec. eexists. *)
  (*   pfold. econs 4. *)
  (* Qed. *)

  (* Lemma raw2tr_match_obs *)
  (*       R obs (raw: @RawTr.t _ R) *)
  (*   : *)
  (*   @extract_tr _ R (RawTr.cons (inr obs) raw) (Tr.cons obs (raw2tr raw)). *)
  (* Proof. *)
  (*   unfold raw2tr, epsilon. eapply Epsilon.epsilon_spec. eexists. *)
  (*   pfold. econs 4. *)
  (* Qed. *)

  (* Lemma match_eq_nb *)
  (*       R (tr: @Tr.t R) *)
  (*       (EXTRACT: extract_tr RawTr.nb tr) *)
  (*   : *)
  (*   tr = Tr.nb. *)
  (* Proof. *)
  (*   punfold EXTRACT. inv EXTRACT; eauto. punfold RSPIN. inv RSPIN. *)
  (* Qed. *)

  (* Lemma raw2tr_nb *)
  (*       R *)
  (*   : *)
  (*   @raw2tr R RawTr.nb = Tr.nb. *)
  (* Proof. *)
  (*   eapply match_eq_nb. eapply raw2tr_match_nb. *)
  (* Qed. *)

  (* Lemma raw2tr_app_comm *)
  (*       R (raw: RawTr.t (R:=R)) *)
  (*       (obss: list obsE) *)
  (*   : *)
  (*   raw2tr (RawTr.app (List.map inr obss) raw) = Tr.app obss (raw2tr raw). *)
  (* Proof. *)
  (*   depgen raw. induction obss; i. *)
  (*   { ss. } *)
  (*   ss.  *)

  (* Lemma raw2tr_cons_obs *)
  (*       R (raw: RawTr.t (R:=R)) *)
  (*       (obs: obsE) *)
  (*   : *)
  (*   (raw2tr (RawTr.cons (inr obs) raw)) = (Tr.cons obs (raw2tr raw)). *)
  (* Proof. *)
  (*   replace raw with (RawTr.app [] raw) at 1. *)
  (*   2: ss. *)
  (*   rewrite RawTr.fold_app. *)
  (*   replace (raw2tr raw) with (Tr.app [] (raw2tr raw)). *)
  (*   2: ss. *)
  (*   rewrite Tr.fold_app. *)


    
  (*   revert_until R. pcofix CIH. i. *)
  (*   unfold Tr.eq in TR1. punfold TR1. inv TR1; pclearbot. *)
  (*   5:{ punfold TR2. inv TR2; pclearbot. *)

  (* Lemma raw2tr_cons_obs *)
  (*       R tr1 tr2 (raw: RawTr.t (R:=R)) *)
  (*       (obs: obsE) *)
  (*       (TR1: Tr.eq tr1 (raw2tr (RawTr.cons (inr obs) raw))) *)
  (*       (TR2: Tr.eq tr2 (Tr.cons obs (raw2tr raw))) *)
  (*   : *)
  (*   Tr.eq tr1 tr2. *)
  (* Proof. *)
  (*   revert_until R. pcofix CIH. i. *)
  (*   unfold Tr.eq in TR1. punfold TR1. inv TR1; pclearbot. *)
  (*   5:{ punfold TR2. inv TR2; pclearbot. *)
        
    

  (* Lemma raw2tr_prop *)
  (*       R (raw: RawTr.t (R:=R)) *)
  (*   : *)
  (*   extract_tr raw (raw2tr raw). *)
  (* Proof. *)
  (*   revert raw. pcofix CIH. i. *)


  (*   unfold raw2tr. eapply Epsilon.epsilon_spec. *)

    
  (*   unfold raw2tr. unfold epsilon. unfold Epsilon.epsilon. unfold proj1_sig. des_ifs. *)
  (*   rename x into tr, m into EPS. *)
  (*   eapply sig_ind. i. eapply EPS. exists x. eapply p. *)
  (*   eapply Epsilon.constructive_indefinite_description. *)
  (*   econs. *)

End ExtractTr.



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
