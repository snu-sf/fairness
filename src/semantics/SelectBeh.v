From sflib Require Import sflib.
From Fairness Require Import pind3 WFLib.
From Paco Require Import paco.

Require Import Coq.Classes.RelationClasses.

From Fairness Require Import Axioms ITreeLib FairBeh.

Set Implicit Arguments.

Section RAWEVENT.

  Variant silentE {id:ID}: Type :=
    | silentE_tau
    | silentE_fair (fm: @fmap id)
  .

  Definition rawE {id:ID} := ((@silentE id) + obsE)%type.

End RAWEVENT.

Module RawTr.
Section TR.

  CoInductive t {id} {R}: Type :=
  | done (retv: R)
  | ub
  | nb
  | cons (hd: (@rawE id)) (tl: t)
  .

  Let TTT {id} {R} := @t id R: Type@{Epsilon.epsilon.u0}.

  Fixpoint app {id} {R} (pre: list rawE) (bh: @t id R): t :=
    match pre with
    | [] => bh
    | hd :: tl => cons hd (app tl bh)
    end
  .

  Lemma fold_app
        id R s pre tl
    :
      (cons s (app pre tl)) = @app id R (s :: pre) tl
  .
  Proof. reflexivity. Qed.

  Definition prefix {id} {R} (pre: list rawE) (bh: @t id R): Prop :=
    exists tl, <<PRE: app pre tl = bh>>
  .

  Definition ob id R (s: @t id R) : t :=
    match s with
    | done retv => done retv
    | ub => ub
    | nb => nb
    | cons ev tl => cons ev tl
    end.

  Lemma ob_eq : forall id R (s: @t id R), s = ob s.
    destruct s; reflexivity.
  Qed.


  Variable id: ID.
  (** select fair trace with induction **)
  Variant _nofail (i: id)
          (nofail: forall (R: Type), (@t id R) -> Prop)
          (R: Type)
    :
    (@t id R) -> Prop :=
    | nofail_done
        retv
      :
      _nofail i nofail (done retv)
    | nofail_ub
      :
      _nofail i nofail ub
    | nofail_nb
      :
      _nofail i nofail nb
    | nofail_fair_success
        fmap tl
        (SUCCESS: (fmap i) = Flag.success)
        (TL: nofail R tl)
      :
      _nofail i nofail (cons (inl (silentE_fair fmap)) tl)
    | nofail_obs
        (obs: obsE) tl
        (TL: nofail R tl)
      :
      _nofail i nofail (cons (inr obs) tl)
    | nofail_tau
        tl
        (TL: nofail R tl)
      :
      _nofail i nofail (cons (inl silentE_tau) tl)
    | nofail_fair_emp
        fmap tl
        (EMP: (fmap i) = Flag.emp)
        (TL: nofail R tl)
      :
      _nofail i nofail (cons (inl (silentE_fair fmap)) tl)
  .

  Definition nofail i: forall (R: Type), (@t id R) -> Prop := paco2 (_nofail i) bot2.

  Lemma nofail_mon i: monotone2 (_nofail i).
  Proof.
    ii. inv IN; [econs 1 | econs 2 | econs 3 | econs 4 | econs 5 | econs 6 | econs 7 ]; eauto.
  Qed.

  Local Hint Constructors _nofail: core.
  Local Hint Unfold nofail: core.
  Local Hint Resolve nofail_mon: paco.


  Inductive must_fail i R: (@t id R) -> Prop :=
  | must_fail_fail
      fm tl
      (FAIL: fm i = Flag.fail)
    :
    must_fail i (cons (inl (silentE_fair fm)) tl)
  | must_fail_obs
      obs tl
      (MUSTF: must_fail i tl)
    :
    must_fail i (cons (inr obs) tl)
  | must_fail_tau
      tl
      (MUSTF: must_fail i tl)
    :
    must_fail i (cons (inl silentE_tau) tl)
  | must_fail_emp
      fm tl
      (EMP: fm i = Flag.emp)
      (MUSTF: must_fail i tl)
    :
    must_fail i (cons (inl (silentE_fair fm)) tl)
  .

  Inductive must_success i R: (@t id R) -> Prop :=
  | must_success_success
      fm tl
      (SUCCESS: fm i = Flag.success)
    :
    must_success i (cons (inl (silentE_fair fm)) tl)
  | must_success_obs
      obs tl
      (MUSTS: must_success i tl)
    :
    must_success i (cons (inr obs) tl)
  | must_success_tau
      tl
      (MUSTS: must_success i tl)
    :
    must_success i (cons (inl silentE_tau) tl)
  | must_success_emp
      fm tl
      (EMP: fm i = Flag.emp)
      (MUSTS: must_success i tl)
    :
    must_success i (cons (inl (silentE_fair fm)) tl)
  .

  Lemma must_fail_not_success
        i R (tr: @t id R)
        (MUST: must_fail i tr)
    :
    ~ must_success i tr.
  Proof.
    induction MUST.
    { ii. inv H. rewrite FAIL in SUCCESS; ss. rewrite FAIL in EMP; ss. }
    { ii. apply IHMUST; clear IHMUST. inv H. auto. }
    { ii. apply IHMUST; clear IHMUST. inv H. auto. }
    { ii. apply IHMUST; clear IHMUST. inv H. rewrite EMP in SUCCESS; ss. auto. }
  Qed.

  Lemma must_success_not_fail
        i R (tr: @t id R)
        (MUST: must_success i tr)
    :
    ~ must_fail i tr.
  Proof.
    induction MUST.
    { ii. inv H. rewrite SUCCESS in FAIL; ss. rewrite EMP in SUCCESS; ss. }
    { ii. apply IHMUST; clear IHMUST. inv H. auto. }
    { ii. apply IHMUST; clear IHMUST. inv H. auto. }
    { ii. apply IHMUST; clear IHMUST. inv H. rewrite FAIL in EMP; ss. auto. }
  Qed.

  Lemma must_fail_not_nofail
        i R (tr: @t id R)
        (MUST: must_fail i tr)
    :
    ~ nofail i tr.
  Proof.
    induction MUST.
    { ii. punfold H. inv H. rewrite FAIL in SUCCESS; ss. rewrite FAIL in EMP; ss. }
    { ii. apply IHMUST; clear IHMUST. punfold H. inv H. pclearbot. auto. }
    { ii. apply IHMUST; clear IHMUST. punfold H. inv H. pclearbot. auto. }
    { ii. apply IHMUST; clear IHMUST. punfold H. inv H. rewrite EMP in SUCCESS; ss. pclearbot. auto. }
  Qed.

  Lemma not_musts_nofail
        i R (tr: @t id R)
        (NMUSTF: ~ must_fail i tr)
        (NMUSTS: ~ must_success i tr)
    :
    nofail i tr.
  Proof.
    revert_until R. pcofix CIH. i. destruct tr.
    { pfold. econs. }
    { pfold. econs. }
    { pfold. econs. }
    { destruct hd as [silent | obs].
      2:{ pfold. econs. right. eapply CIH.
          - ii. eapply NMUSTF. econs. auto.
          - ii. eapply NMUSTS. econs. auto.
      }
      destruct silent as [| fm].
      { pfold. econs. right. eapply CIH.
        - ii. eapply NMUSTF. econs. auto.
        - ii. eapply NMUSTS. econs. auto.
      }
      { destruct (fm i) eqn:FM.
        { exfalso. eapply NMUSTF. econs; eauto. }
        { pfold. econs 7. auto. right. eapply CIH.
          - ii. eapply NMUSTF. econs 4; auto.
          - ii. eapply NMUSTS. econs 4; auto.
        }
        { exfalso. eapply NMUSTS. econs; eauto. }
      }
    }
  Qed.

  (* cases analysis: *)
  (* ~mf ms nf *)
  (* ~mf ~ms nf *)
  (* mf ~ms ~nf *)
  (* ~mf ms ~nf *)
  Variant __fair_ind
          (fair_ind: forall (R: Type) (i: id), (@t id R) -> Prop)
          (_fair_ind: forall (R: Type) (i: id), (@t id R) -> Prop)
          (R: Type) (i: id)
    :
    (@t id R) -> Prop :=
    (* base cases *)
    | fair_ind_nofail
        tr
        (NOFAIL: nofail i tr)
      :
      __fair_ind fair_ind _fair_ind i tr

    (* inner cases: depends on future success / fail *)
    | fair_ind_obs
        (obs: obsE) tl
        (NNF: ~ nofail i tl)
        (COI: must_success i tl -> fair_ind R i tl)
        (IND: must_fail i tl -> _fair_ind R i tl)
      :
      __fair_ind fair_ind _fair_ind i (cons (inr obs) tl)
    | fair_ind_tau
        tl
        (NNF: ~ nofail i tl)
        (COI: must_success i tl -> fair_ind R i tl)
        (IND: must_fail i tl -> _fair_ind R i tl)
      :
      __fair_ind fair_ind _fair_ind i (cons (inl silentE_tau) tl)
    | fair_ind_fair_emp
        fm tl
        (EMP: (fm i) = Flag.emp)
        (NNF: ~ nofail i tl)
        (COI: must_success i tl -> fair_ind R i tl)
        (IND: must_fail i tl -> _fair_ind R i tl)
      :
      __fair_ind fair_ind _fair_ind i (cons (inl (silentE_fair fm)) tl)
    | fair_ind_fair_fail
        fm tl
        (FAIL: (fm i) = Flag.fail)
        (COI: must_success i tl -> fair_ind R i tl)
        (IND: (~ must_success i tl) -> _fair_ind R i tl)
      :
      __fair_ind fair_ind _fair_ind i (cons (inl (silentE_fair fm)) tl)

    (* outermost coinductive case: i must success *)
    | fair_ind_fair_success
        fm tl
        (SUCCESS: (fm i) = Flag.success)
        (COI: fair_ind R i tl)
      :
      __fair_ind fair_ind _fair_ind i (cons (inl (silentE_fair fm)) tl)
  .

  Definition fair_ind: forall (R: Type) (i: id), (@t id R) -> Prop :=
    paco3 (fun r => pind3 (__fair_ind r) top3) bot3.

  Lemma fair_ind_mon1: forall r r' (LE: r <3= r'), (__fair_ind r) <4= (__fair_ind r').
  Proof.
    ii. inv PR.
    - econs 1; eauto.
    - econs 2; eauto.
    - econs 3; eauto.
    - econs 4; eauto.
    - econs 5; eauto.
    - econs 6; eauto.
  Qed.

  Lemma fair_ind_mon2: forall r q q' (LE: q <3= q'), (__fair_ind r q) <3= (__fair_ind r q').
  Proof.
    ii. inv PR.
    - econs 1; eauto.
    - econs 2; eauto.
    - econs 3; eauto.
    - econs 4; eauto.
    - econs 5; eauto.
    - econs 6; eauto.
  Qed.

  Lemma fair_ind_mon: forall q, monotone3 (fun r => pind3 (__fair_ind r) q).
  Proof.
    ii. eapply pind3_mon_gen; eauto. ii. eapply fair_ind_mon1; eauto.
  Qed.

  Definition is_fair_ind {R} (tr: @t id R) := forall i, fair_ind i tr.



  (** select fair trace with fixpoints **)
  Variant ___fair
          (fair: forall (R: Type) (i: id), (@t id R) -> Prop)
          (_fair: forall (R: Type) (i: id), (@t id R) -> Prop)
          (__fair: forall (R: Type) (i: id), (@t id R) -> Prop)
          (R: Type) (i: id)
    :
    (@t id R) -> Prop :=
    (* base cases *)
    | fair_done
        retv
      :
      ___fair fair _fair __fair i (done retv)
    | fair_ub
      :
      ___fair fair _fair __fair i ub
    | fair_nb
      :
      ___fair fair _fair __fair i nb

    (* innermost coinductive cases: no fair events for i *)
    | fair_obs
        (obs: obsE) tl
        (TL: __fair R i tl)
      :
      ___fair fair _fair __fair i (cons (inr obs) tl)
    | fair_tau
        tl
        (TL: __fair R i tl)
      :
      ___fair fair _fair __fair i (cons (inl silentE_tau) tl)
    | fair_fair_emp
        fmap tl
        (EMP: (fmap i) = Flag.emp)
        (TL: __fair R i tl)
      :
      ___fair fair _fair __fair i (cons (inl (silentE_fair fmap)) tl)

    (* middle inductive cases: i fails inductively *)
    | fair_fair_fail
        fmap tl
        (FAIL: (fmap i) = Flag.fail)
        (TL: _fair R i tl)
      :
      ___fair fair _fair __fair i (cons (inl (silentE_fair fmap)) tl)

    (* outermost coinductive cases: i successes *)
    | fair_fair_success
        fmap tl
        (SUCCESS: (fmap i) = Flag.success)
        (TL: fair R i tl)
      :
      ___fair fair _fair __fair i (cons (inl (silentE_fair fmap)) tl)
  .

  Definition fair: forall (R: Type) (i: id), (@t id R) -> Prop :=
    paco3 (fun r => pind3 (fun q => paco3 (___fair r q) bot3) top3) bot3.

  Lemma ___fair_mon: forall r r' (LE: r <3= r'), (___fair r) <5= (___fair r').
  Proof.
    ii. inv PR.
    - econs 1; eauto.
    - econs 2; eauto.
    - econs 3; eauto.
    - econs 4; eauto.
    - econs 5; eauto.
    - econs 6; eauto.
    - econs 7; eauto.
    - econs 8; eauto.
  Qed.

  Lemma __fair_mon: forall r q q' (LE: q <3= q'), (___fair r q) <4= (___fair r q').
  Proof.
    ii. inv PR.
    - econs 1; eauto.
    - econs 2; eauto.
    - econs 3; eauto.
    - econs 4; eauto.
    - econs 5; eauto.
    - econs 6; eauto.
    - econs 7; eauto.
    - econs 8; eauto.
  Qed.

  Lemma _fair_mon: forall r q, monotone3 (___fair r q).
  Proof.
    ii. inv IN.
    - econs 1; eauto.
    - econs 2; eauto.
    - econs 3; eauto.
    - econs 4; eauto.
    - econs 5; eauto.
    - econs 6; eauto.
    - econs 7; eauto.
    - econs 8; eauto.
  Qed.

  Lemma fair_mon: forall o p, monotone3 (fun r => pind3 (fun q => paco3 (___fair r q) p) o).
  Proof.
    ii. eapply pind3_mon_gen; eauto. ii. ss. eapply paco3_mon_gen; eauto. i. eapply ___fair_mon; eauto.
  Qed.

  Definition is_fair {R} (tr: @t id R) := forall i, fair i tr.



  (** select fair trace with well-founded order **)
  Variable wf: WF.

  Variant _fair_ord
          (fair_ord: forall (R: Type) (m: imap id wf), (@t id R) -> Prop)
          (R: Type) (m: imap id wf)
    :
    (@t id R) -> Prop :=
    | fair_ord_done
        retv
      :
      _fair_ord fair_ord m (done retv)
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

  Definition fair_ord: forall (R: Type) (m: imap id wf), (@t id R) -> Prop := paco3 _fair_ord bot3.

  Lemma fair_ord_mon: monotone3 _fair_ord.
  Proof.
    ii. inv IN; econs; eauto.
  Qed.

  Local Hint Resolve fair_ord_mon: paco.

  Definition is_fair_ord {R} (tr: @t id R) := exists m, fair_ord m tr.

  (** fair_ord upto *)

  Variant fair_ord_imap_le_ctx
          (fair_ord: forall (R: Type) (m: imap id wf), (@t id R) -> Prop)
          R
    :
    (imap id wf) -> (@t id R) -> Prop :=
    | fair_ord_imap_le_ctx_intro
        imap0 imap1 tr
        (ORD: @fair_ord R imap1 tr)
        (IMAP: soft_update imap0 imap1)
      :
      fair_ord_imap_le_ctx fair_ord imap0 tr.

  Lemma fair_ord_imap_le_ctx_mon: monotone3 fair_ord_imap_le_ctx.
  Proof. ii. inv IN. econs; eauto. Qed.

  Hint Resolve fair_ord_imap_le_ctx_mon: paco.

  Lemma fair_ord_imap_le_ctx_wrespectful: wrespectful3 _fair_ord fair_ord_imap_le_ctx.
  Proof.
    econs; eauto with paco.
    i. inv PR. apply GF in ORD. inv ORD; eauto.
    { econs 1. }
    { econs 2. }
    { econs 3. }
    { econs 4. eapply rclo3_clo_base. econs; eauto. }
    { econs 5.
      instantiate (1:=fun i => match fmap i with
                            | Flag.fail => match excluded_middle_informative (x1 i = imap1 i) with
                                          | left _ => m0 i
                                          | right _ => imap1 i
                                          end
                            | Flag.emp => x1 i
                            | Flag.success => m0 i
                            end).
      - unfold fair_update, soft_update in *. i. specialize (IMAP i). specialize (FAIR i).
        des_ifs. rewrite e. auto. unfold le in IMAP. des; auto. rewrite IMAP in n; ss.
      - eapply rclo3_clo_base. econs; eauto.
        unfold fair_update, soft_update in *. i. specialize (IMAP i). specialize (FAIR i).
        des_ifs; ss. left; auto. right; auto. rewrite FAIR. auto. left; auto.
    }
    { econs 6. eapply rclo3_clo_base. econs; eauto. }
  Qed.

  Lemma fair_ord_imap_le_ctx_spec: fair_ord_imap_le_ctx <4= gupaco3 _fair_ord (cpn3 _fair_ord).
  Proof. i. eapply wrespect3_uclo; eauto with paco. eapply fair_ord_imap_le_ctx_wrespectful. Qed.



  (** raw tr equivalence *)
  Variant _eq
          (eq: forall R, (@t id R) -> (@t id R) -> Prop)
          R
    :
    (@t id R) -> (@t id R) -> Prop :=
    | eq_done
        retv
      :
      _eq eq (done retv) (done retv)
    | eq_ub
      :
      _eq eq ub ub
    | eq_nb
      :
      _eq eq nb nb
    | eq_cons
        ev tl1 tl2
        (TL: eq _ tl1 tl2)
      :
      _eq eq (cons ev tl1) (cons ev tl2)
  .

  Definition eq: forall (R: Type), (@t id R) -> (@t id R) -> Prop := paco3 _eq bot3.

  Lemma eq_mon: monotone3 _eq.
  Proof.
    ii. inv IN. all: econs; eauto.
  Qed.

  Local Hint Resolve eq_mon: paco.

  Global Program Instance eq_equiv {R}: Equivalence (@eq R).
  Next Obligation.
    pcofix CIH. i. destruct x; try (pfold; econs; eauto).
  Qed.
  Next Obligation.
    pcofix CIH. i.
    unfold eq in H0. punfold H0.
    inv H0.
    1,2,3: pfold; econs; eauto.
    - pfold. econs; eauto. right. eapply CIH. pclearbot. auto.
  Qed.
  Next Obligation.
    pcofix CIH. i.
    unfold eq in H0, H1. punfold H0. punfold H1. inv H0; inv H1.
    1,2,3: pfold; econs; eauto.
    pclearbot. pfold. econs. right. eapply CIH; eauto.
  Qed.

End TR.
End RawTr.
#[export] Hint Constructors RawTr._nofail: core.
#[export] Hint Unfold RawTr.nofail: core.
#[export] Hint Resolve RawTr.nofail_mon: paco.
#[export] Hint Constructors RawTr.__fair_ind: core.
#[export] Hint Unfold RawTr.fair_ind: core.
#[export] Hint Resolve RawTr.fair_ind_mon1: paco.
#[export] Hint Resolve RawTr.fair_ind_mon2: paco.
#[export] Hint Resolve RawTr.fair_ind_mon: paco.

#[export] Hint Constructors RawTr.___fair: core.
#[export] Hint Unfold RawTr.fair: core.
#[export] Hint Resolve RawTr.___fair_mon: paco.
#[export] Hint Resolve RawTr.__fair_mon: paco.
#[export] Hint Resolve RawTr._fair_mon: paco.
#[export] Hint Resolve RawTr.fair_mon: paco.

#[export] Hint Constructors RawTr._fair_ord: core.
#[export] Hint Unfold RawTr.fair_ord: core.
#[export] Hint Resolve RawTr.fair_ord_mon: paco.
#[export] Hint Resolve RawTr.fair_ord_imap_le_ctx_mon: paco.

#[export] Hint Constructors RawTr._eq: core.
#[export] Hint Unfold RawTr.eq: core.
#[export] Hint Resolve RawTr.eq_mon: paco.
#[export] Hint Resolve cpn3_wcompat: paco.


Module RawBeh.
Section BEHAVES.

  Variable id: ID.

  Definition t {R}: Type := @RawTr.t id R -> Prop.

  Variant _of_state
            (of_state: forall (R: Type), (@state _ R) -> (@RawTr.t _ R) -> Prop)
            (R: Type)
    :
    (@state _ R) -> (@RawTr.t id R) -> Prop :=
  | done
      retv
    :
    _of_state of_state (Ret retv) (RawTr.done retv)
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

  Hint Constructors _of_state: core.
  Hint Unfold of_state: core.
  Hint Resolve of_state_mon: paco.
  Hint Resolve cpn3_wcompat: paco.

  Definition of_state_fair_ind {R} (st: @state _ R) (raw_tr: @RawTr.t _ R) :=
    (<<BEH: of_state st raw_tr>>) /\ (<<FAIR: RawTr.is_fair_ind raw_tr>>).

  Definition of_state_fair_ord {wf: WF} {R} (st: @state _ R) (raw_tr: @RawTr.t _ R) :=
    (<<BEH: of_state st raw_tr>>) /\ (<<FAIR: RawTr.is_fair_ord wf raw_tr>>).

  Definition of_state_fair {R} (st: @state _ R) (raw_tr: @RawTr.t _ R) :=
    (<<BEH: of_state st raw_tr>>) /\ (<<FAIR: RawTr.is_fair raw_tr>>).



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
#[export] Hint Constructors RawBeh._of_state: core.
#[export] Hint Unfold RawBeh.of_state: core.
#[export] Hint Resolve RawBeh.of_state_mon: paco.
#[export] Hint Resolve cpn3_wcompat: paco.
