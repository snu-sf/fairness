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


  Inductive _compress_raw
            (compress_raw: forall (R: Type), RawTr.t -> Tr.t -> Prop)
            R
    :
    (@RawTr.t _ R) -> Tr.t -> Prop :=
  | compress_raw_done
      retv
    :
    _compress_raw compress_raw (RawTr.done retv) (Tr.done retv)
  | compress_raw_spin
      raw
      (RSPIN: raw_spin raw)
    :
    _compress_raw compress_raw raw (Tr.spin)
  | compress_raw_ub
    :
    _compress_raw compress_raw (RawTr.ub) (Tr.ub)
  | compress_raw_nb
    :
    _compress_raw compress_raw (RawTr.nb) (Tr.nb)
  | compress_raw_obs
      (obs: obsE) raw_tl tr_tl
      (TL: compress_raw _ raw_tl tr_tl)
    :
    _compress_raw compress_raw (RawTr.cons (inr obs) raw_tl) (Tr.cons obs tr_tl)
  | compress_raw_silent
      (silent: silentE) raw_tl tr_tl
      (TL: _compress_raw compress_raw raw_tl tr_tl)
    :
    _compress_raw compress_raw (RawTr.cons (inl silent) raw_tl) tr_tl
  .

  Definition compress_raw: forall (R: Type), RawTr.t -> Tr.t -> Prop := paco3 _compress_raw bot3.

  Lemma compress_raw_ind
        (compress_raw : forall R : Type, RawTr.t -> Tr.t -> Prop) (R : Type) (P: RawTr.t -> Tr.t -> Prop)
        (DONE: forall retv : R, P (RawTr.done retv) (Tr.done retv))
        (SPIN: forall (raw : RawTr.t) (RSPIN: raw_spin raw), P raw Tr.spin)
        (UB: P RawTr.ub Tr.ub)
        (NB: P RawTr.nb Tr.nb)
        (OBS: forall (obs : obsE) (raw_tl : RawTr.t) (tr_tl : Tr.t) (TL: compress_raw R raw_tl tr_tl),
            P (RawTr.cons (inr obs) raw_tl) (Tr.cons obs tr_tl))
        (SILENT: forall (silent : silentE) (raw_tl : RawTr.t) (tr_tl : Tr.t)
                   (STEP: _compress_raw compress_raw raw_tl tr_tl) (IH: P raw_tl tr_tl),
            P (RawTr.cons (inl silent) raw_tl) tr_tl)
    :
    forall raw_tr tr, (_compress_raw compress_raw raw_tr tr) -> P raw_tr tr.
  Proof.
    fix IH 3; i.
    inv H; eauto.
  Qed.

  Lemma compress_raw_mon: monotone3 _compress_raw.
  Proof.
    ii. induction IN using compress_raw_ind; econs; eauto.
  Qed.

End MatchTr.
#[export] Hint Constructors _raw_spin.
#[export] Hint Unfold raw_spin.
#[export] Hint Resolve raw_spin_mon: paco.
#[export] Hint Resolve cpn2_wcompat: paco.
#[export] Hint Constructors _compress_raw.
#[export] Hint Unfold compress_raw.
#[export] Hint Resolve compress_raw_mon: paco.
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

  Lemma compress_eq_done
        R (tr: @Tr.t R) retv
        (COMPR: compress_raw (RawTr.done retv) tr)
    :
    tr = Tr.done retv.
  Proof.
    punfold COMPR. inv COMPR; eauto. punfold RSPIN. inv RSPIN.
  Qed.

  Lemma compress_eq_ub
        R (tr: @Tr.t R)
        (COMPR: compress_raw RawTr.ub tr)
    :
    tr = Tr.ub.
  Proof.
    punfold COMPR. inv COMPR; eauto. punfold RSPIN. inv RSPIN.
  Qed.

  Lemma compress_eq_nb
        R (tr: @Tr.t R)
        (COMPR: compress_raw RawTr.nb tr)
    :
    tr = Tr.nb.
  Proof.
    punfold COMPR. inv COMPR; eauto. punfold RSPIN. inv RSPIN.
  Qed.



  (* Fixpoint observe_raw_first {R} (raw: @RawTr.t _ R): option obsE := *)
  (*   match raw with *)
  (*   | RawTr.done _ => None *)
  (*   | RawTr.ub => None *)
  (*   | RawTr.nb => None *)
  (*   | RawTr.cons (inr obs) tl => Some obs *)
  (*   | RawTr.cons (inl silent) tl => observe_raw_first tl *)
  (*   end. *)

  (* Inductive observe_raw_first *)
  (*           R (raw: @RawTr.t _ R) *)
  (*   : *)
  (*   (option obsE) -> Prop := *)
  (* | observe_raw_first_done *)
  (*     retv *)
  (*     (RAW: raw = RawTr.done retv) *)
  (*   : *)
  (*   observe_raw_first raw None *)
  (* | observe_raw_first_ub *)
  (*     (RAW: raw = RawTr.ub) *)
  (*   : *)
  (*   observe_raw_first raw None *)
  (* | observe_raw_first_nb *)
  (*     (RAW: raw = RawTr.nb) *)
  (*   : *)
  (*   observe_raw_first raw None *)
  (* | observe_raw_first_obs *)
  (*     obs tl *)
  (*     (RAW: raw = RawTr.cons (inr obs) tl) *)
  (*   : *)
  (*   observe_raw_first raw (Some obs) *)
  (* | observe_raw_first_silent *)
  (*     silent tl obs *)
  (*     (STEP: observe_raw_first tl obs) *)
  (*     (RAW: raw = RawTr.cons (inl silent) tl) *)
  (*   : *)
  (*   observe_raw_first raw obs *)
  (* . *)

  (* raw_spin raw <-> forall e, ~ observe_raw_first raw e. *)

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
    (* | observe_raw_prop_silent_diverge *)
    (*     (silent: silentE) tl *)
    (*     (SPIN: raw_spin tl) *)
    (*   : *)
    (*   observe_raw_prop (RawTr.cons (inl silent) tl) (None, None) *)
  .

  (* raw_spin raw <-> forall e tl, ~ observe_raw_first raw (e, tl). *)

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

  CoFixpoint raw2tr {R} (raw: @RawTr.t _ R): (@Tr.t R) :=
    match observe_raw raw with
    | None => Tr.spin
    | Some (None, RawTr.done retv) => Tr.done retv
    | Some (None, RawTr.ub) => Tr.ub
    | Some (None, RawTr.nb) => Tr.nb
    | Some (Some obs, tl) => Tr.cons obs (raw2tr tl)
    end.
  


      
    | (None, Some (RawTr.done retv)) => Tr.done retv
    | (None, Some RawTr.ub) => Tr.ub
    | (None, Some RawTr.nb) => Tr.nb
    | (Some obs, Some tl) => Tr.cons obs (raw2tr tl)
    | (None, Some tl) => raw2tr tl
    | (None, None) => Tr.spin
    | (Some _, None) => Tr.ub
    end.
  
    



  Definition raw2tr {R} (raw: @RawTr.t _ R): (@Tr.t R) :=
    epsilon _ (@inhabited_tr R) (compress_raw raw).

  Lemma raw2tr_match
        R (raw: @RawTr.t _ R)
    :
    compress_raw raw (raw2tr raw).
  Proof.
    unfold raw2tr, epsilon. eapply Epsilon.epsilon_spec. eexists.

  (* Lemma match_eq_obs *)
  (*       R (tr: @Tr.t R) raw tl *)
  (*       obs *)
  (*       (MATCH0: compress_raw raw tl) *)
  (*       (COMPR: compress_raw (RawTr.cons (inr obs) raw) tr) *)
  (*   : *)
  (*   tr = Tr.cons obs tl. *)
  (* Proof. *)
  (*   punfold COMPR. inv COMPR; eauto. punfold RSPIN. inv RSPIN. *)
  (*   f_equal. pclearbot. *)
  (* Qed. *)

  (* Lemma compress_raw_cih *)
  (*       R (r: forall R, RawTr.t -> Tr.t -> Prop) *)
  (*       raw tr *)
  (*       (CIH: @r R raw tr) *)
  (*       (COMPR: _compress_raw (R:=R) (upaco3 _compress_raw r) raw tr) *)
  (*   : *)
  (*   Prop. *)

  (* CoFixpoint raw2tr {R} (raw: @RawTr.t _ R): (@Tr.t R) := *)
  (*   epsilon _ (@inhabited_tr R) *)
  (*           (fun tr => forall (r: forall R, RawTr.t -> Tr.t -> Prop) (CIH: forall raw0, @r R raw0 (raw2tr raw0)), *)
  (*                _compress_raw (R:=R) (upaco3 _compress_raw r) raw tr). *)


  (* Definition raw2tr {R} (raw: @RawTr.t _ R): (@Tr.t R) := *)
  (*   epsilon _ (@inhabited_tr R) (fun tr => forall etr (EQ: Tr.eq etr tr), compress_raw raw etr). *)

  (* Lemma raw2tr_match *)
  (*       R (raw: @RawTr.t _ R) *)
  (*   : *)
  (*   compress_raw raw (raw2tr raw). *)
  (* Proof. *)
  (*   remember (raw2tr raw) as tr. assert (EQ: Tr.eq tr (raw2tr raw)). *)
  (*   { rewrite Heqtr. reflexivity. } *)
  (*   clear Heqtr. revert_until raw. *)
  (*   unfold raw2tr, epsilon. eapply Epsilon.epsilon_spec. *)

  Definition raw2tr {R} (raw: @RawTr.t _ R): (@Tr.t R) :=
    epsilon _ (@inhabited_tr R) (compress_raw raw).

  Lemma raw2tr_match
        R (raw: @RawTr.t _ R)
    :
    compress_raw raw (raw2tr raw).
  Proof.
    unfold raw2tr, epsilon. eapply Epsilon.epsilon_spec. eexists.
    














  Definition raw2tr {R} (raw: @RawTr.t _ R): (@Tr.t R) :=
    epsilon _ (@inhabited_tr R)
            (fun tr => forall (r: forall R, RawTr.t -> Tr.t -> Prop)
                      (CIH: forall raw0 tr0 (COMPR: compress_raw (R:=R) raw0 tr0), @r R raw tr),
                 _compress_raw (R:=R) (upaco3 _compress_raw r) raw tr).

  Lemma compress_raw_is_raw2tr
        R raw tr
        (COMPR: compress_raw (R:=R) raw tr)
    :
    tr = raw2tr raw.
  Proof.
    punfold COMPR. inv COMPR.
    { symmetry. eapply match_eq_done.
      admit.
    }
    4:{ 

      
    5:{ 
    2:{ 

  Definition raw2tr {R} (raw: @RawTr.t _ R): (@Tr.t R) :=
    epsilon _ (@inhabited_tr R)
            (fun tr => forall (r: forall R, RawTr.t -> Tr.t -> Prop) (CIH: @r R raw tr),
                 _compress_raw (R:=R) (upaco3 _compress_raw r) raw tr).

  Lemma raw2tr_match
        R (raw: @RawTr.t _ R)
    :
    compress_raw raw (raw2tr raw).
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
    epsilon _ (@inhabited_tr R) (compress_raw raw).

  Definition st2raw {R} (st: state): (RawTr.t (R:=R)) :=
    epsilon _ (@inhabited_raw R) (RawBeh.of_state st).


  Lemma raw2tr_match_done
        R (retv: R)
    :
    compress_raw (RawTr.done retv) (raw2tr (RawTr.done retv)).
  Proof.
    unfold raw2tr, epsilon. eapply Epsilon.epsilon_spec. eexists.
    pfold. econs 1.
  Qed.

  Lemma match_eq_done
        R (tr: @Tr.t R) retv
        (COMPR: compress_raw (RawTr.done retv) tr)
    :
    tr = Tr.done retv.
  Proof.
    punfold COMPR. inv COMPR; eauto. punfold RSPIN. inv RSPIN.
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
    @compress_raw _ R RawTr.ub (raw2tr RawTr.ub).
  Proof.
    unfold raw2tr, epsilon. eapply Epsilon.epsilon_spec. eexists.
    pfold. econs 3.
  Qed.

  Lemma match_eq_ub
        R (tr: @Tr.t R)
        (COMPR: compress_raw RawTr.ub tr)
    :
    tr = Tr.ub.
  Proof.
    punfold COMPR. inv COMPR; eauto. punfold RSPIN. inv RSPIN.
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
    @compress_raw _ R RawTr.nb (raw2tr RawTr.nb).
  Proof.
    unfold raw2tr, epsilon. eapply Epsilon.epsilon_spec. eexists.
    pfold. econs 4.
  Qed.

  Lemma match_eq_nb
        R (tr: @Tr.t R)
        (COMPR: compress_raw RawTr.nb tr)
    :
    tr = Tr.nb.
  Proof.
    punfold COMPR. inv COMPR; eauto. punfold RSPIN. inv RSPIN.
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
  (*   @compress_raw _ R (RawTr.cons (inr obs) raw) (raw2tr (RawTr.cons (inr obs) raw)). *)
  (* Proof. *)
  (*   revert_until R. pcofix CIH; i. *)
  (*   pfold. eapply compress_raw_mon. *)
  (*   { instantiate (1:=bot3). *)

  (*     unfold raw2tr, epsilon. eapply Epsilon.epsilon_spec. eexists. *)
  (*   pfold. econs 4. *)
  (* Qed. *)

  (* Lemma raw2tr_match_obs *)
  (*       R obs (raw: @RawTr.t _ R) *)
  (*   : *)
  (*   @compress_raw _ R (RawTr.cons (inr obs) raw) (Tr.cons obs (raw2tr raw)). *)
  (* Proof. *)
  (*   unfold raw2tr, epsilon. eapply Epsilon.epsilon_spec. eexists. *)
  (*   pfold. econs 4. *)
  (* Qed. *)

  (* Lemma match_eq_nb *)
  (*       R (tr: @Tr.t R) *)
  (*       (COMPR: compress_raw RawTr.nb tr) *)
  (*   : *)
  (*   tr = Tr.nb. *)
  (* Proof. *)
  (*   punfold COMPR. inv COMPR; eauto. punfold RSPIN. inv RSPIN. *)
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
  (*   compress_raw raw (raw2tr raw). *)
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

  Lemma IndexBeh_implies_SelectBeh_compress_raw
        R (st: state (R:=R)) (tr: Tr.t (R:=R)) (im: imap wf)
        (BEH: Beh.of_state im st tr)
    :
    (<<COMPR: compress_raw (st2raw st) tr>>).
  Proof.
  Admitted.

  Theorem IndexBeh_implies_SelectBeh
          R (st: state (R:=R)) (tr: Tr.t (R:=R)) (im: imap wf)
          (BEH: Beh.of_state im st tr)
    :
    exists raw, (<<COMPR: compress_raw raw tr>>) /\ (<<BEH: RawBeh.of_state_fair_ord (wf:=wf) st raw>>).
  Proof.
  Admitted.


  Lemma SelectBeh_implies_IndexBeh_compress_raw
        R (st: state (R:=R)) (raw: RawTr.t (R:=R))
        (BEH: RawBeh.of_state st raw)
    :
    (<<COMPR: compress_raw raw (raw2tr raw)>>).
  Proof.
    red. revert_until R. pcofix CIH; i.
    punfold BEH. inv BEH.
    { rewrite raw2tr_done. pfold. econs. }
    { rewrite raw2tr_nb. pfold. econs. }
    { pclearbot. eapply CIH in TL.

      punfold TL.

      eapply compress_raw_mon.

      pfold. unfold raw2tr, epsilon. eapply Epsilon.epsilon_spec.


    
    unfold RawBeh.of_state in BEH. punfold BEH.



  Admitted.

  Theorem SelectBeh_implies_IndexBeh
          R (st: state (R:=R)) (raw: RawTr.t (R:=R))
          (BEH: RawBeh.of_state_fair_ord (wf:=wf) st raw)
    :
    exists (im: imap wf) tr, (<<COMPR: compress_raw raw tr>>) /\ (<<BEH: Beh.of_state im st tr>>).
  Proof.
  Admitted.

End EQUIV.
