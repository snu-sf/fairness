From sflib Require Import sflib.
From ITree Require Export ITree.
From Paco Require Import paco.

Export ITreeNotations.

Require Import Coq.Classes.RelationClasses.

Set Implicit Arguments.

Section OBS.

  Variant event: Type :=
    | event_syscall (fn: nat) (args: list nat) (retv: nat)
  .

End OBS.

Module Tr.
  CoInductive t {R}: Type :=
  | done (retv: R)
  | spin
  | ub
  | nb
  | cons (hd: event) (tl: t)
  .
  Infix "##" := cons (at level 60, right associativity).

  Fixpoint app {R} (pre: list event) (bh: @t R): t :=
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

  Definition prefix {R} (pre: list event) (bh: @t R): Prop :=
    exists tl, <<PRE: app pre tl = bh>>
  .

End Tr.


Module Flag.

  Variant t: Type :=
  | fail
  | emp
  | success
  .

  Definition le: t -> t -> Prop :=
    fun f0 f1 =>
      match f0, f1 with
      | fail, _ => True
      | _, fail => False
      | emp, _ => True
      | _, emp => False
      | success, _ => True
      end.

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
    ii. destruct x; ss.
  Qed.
  Next Obligation.
    ii. destruct x, y, z; ss.
  Qed.

End Flag.


Class ID : Type := mk { id: Type }.

Section EVENT.

  Context {Ident: ID}.

  Variant eventE: Type -> Type :=
    | Choose (X: Type): eventE X
    | Fair (m: id -> Flag.t): eventE unit
    | Syscall (fn: nat) (args: list nat) (retv: nat): eventE nat
  .

End EVENT.


Section BEHAVES.

  Context {Ident: ID}.

  Inductive terminate
            (R: Type)
    :
    forall (itr: itree eventE R), Prop :=
  | terminate_ret
      r
    :
    terminate (Ret r)
  | terminate_tau
      itr
      (TERM: terminate itr)
    :
    terminate (Tau itr)
  | terminate_choose
      X ktr x
      (TERM: terminate (ktr x))
    :
    terminate (Vis (Choose X) ktr)
  | terminate_fair
      m ktr
      (TERM: terminate (ktr tt))
    :
    terminate (Vis (Fair m) ktr)
  | terminate_syscall
      fn args retv ktr
      (TERM: terminate (ktr retv))
    :
    terminate (Vis (Syscall fn args retv) ktr)
  .

  Variant _diverge_index
          (diverge_index: forall (R: Type) (idx: id -> nat) (itr: itree eventE R), Prop)
          (R: Type)
    :
    forall (idx: id -> nat) (itr: itree eventE R), Prop :=
    | diverge_index_tau
        itr idx0 idx1
        (DIV: diverge_index _ idx1 itr)
        (IDX: forall i, idx1 i <= idx0 i)
      :
      _diverge_index diverge_index idx0 (Tau itr)
    | diverge_index_choose
        X ktr x idx0 idx1
        (DIV: diverge_index _ idx1 (ktr x))
        (IDX: forall i, idx1 i <= idx0 i)
      :
      _diverge_index diverge_index idx0 (Vis (Choose X) ktr)
    | diverge_index_fair
        m ktr idx0 idx1
        (DIV: diverge_index _ idx1 (ktr tt))
        (EMP: forall j (IDX: (m j) = Flag.emp), idx1 j <= idx0 j)
        (FAIL: forall j (IDX: (m j) = Flag.fail), idx1 j < idx0 j)
      :
      _diverge_index diverge_index idx0 (Vis (Fair m) ktr)
    | diverge_index_syscall
        fn args retv ktr idx0 idx1
        (DIV: diverge_index _ idx1 (ktr retv))
        (IDX: forall i, idx1 i <= idx0 i)
      :
      _diverge_index diverge_index idx0 (Vis (Syscall fn args retv) ktr)
  .

  Lemma diverge_index_mon: monotone3 _diverge_index.
  Proof.
    ii. inv IN.
    - econs 1; eauto.
    - econs 2; eauto.
    - econs 3; eauto.
    - econs 4; eauto.
  Qed.

  Definition diverge_index: forall (R: Type) (idx: id -> nat) (itr: itree eventE R), Prop := paco3 _diverge_index bot3.

  Definition diverge (R: Type) (itr: itree eventE R): Prop :=
    exists idx, diverge_index idx itr.

End BEHAVES.



Section STS.

  Context {Ident: ID}.

  Definition state {R} := itree eventE R.

  Inductive step {R}: @state R -> option event -> state -> Prop :=
  | step_tau
      itr
    :
    step (Tau itr) None itr
  | step_choose
      X ktr (x: X)
    :
    step (Vis (Choose X) ktr) None (ktr x)
  | step_fair
      m ktr
    :
    step (Vis (Fair m) ktr) None (ktr tt)
  | step_syscall
      fn args retv ktr
    :
    step (Vis (Syscall fn args retv) ktr) (Some (event_syscall fn args retv)) (ktr retv)
  .

  Lemma step_trigger_choose_iff X k itr e
        (STEP: step (trigger (Choose X) >>= k) e itr)
    :
      exists x,
        e = None /\ itr = k x.
  Proof.
    inv STEP.
    { eapply f_equal with (f:=observe) in H0. ss. }
    { eapply f_equal with (f:=observe) in H0. ss.
      unfold trigger in H0. ss. cbn in H0.
      dependent destruction H0. ired. et.  }
    { eapply f_equal with (f:=observe) in H0. ss. }
    { eapply f_equal with (f:=observe) in H0. ss. }
  Qed.

  Lemma step_trigger_take_iff X k itr e
        (STEP: step (trigger (Take X) >>= k) e itr)
    :
      exists x,
        e = None /\ itr = k x.
  Proof.
    inv STEP.
    { eapply f_equal with (f:=observe) in H0. ss. }
    { eapply f_equal with (f:=observe) in H0. ss. }
    { eapply f_equal with (f:=observe) in H0. ss.
      unfold trigger in H0. ss. cbn in H0.
      dependent destruction H0. ired. et.  }
    { eapply f_equal with (f:=observe) in H0. ss. }
  Qed.

  Lemma step_tau_iff itr0 itr1 e
        (STEP: step (Tau itr0) e itr1)
    :
      e = None /\ itr0 = itr1.
  Proof.
    inv STEP. et.
  Qed.

  Lemma step_ret_iff rv itr e
        (STEP: step (Ret rv) e itr)
    :
      False.
  Proof.
    inv STEP.
  Qed.

  Lemma step_trigger_syscall_iff fn args rvs k e itr
        (STEP: step (trigger (Syscall fn args rvs) >>= k) e itr)
    :
      exists rv, itr = k rv /\ e = Some (event_sys fn args rv)
                 /\ <<RV: rvs rv>> /\ <<SYS: syscall_sem (event_sys fn args rv)>>.
  Proof.
    inv STEP.
    { eapply f_equal with (f:=observe) in H0. ss. }
    { eapply f_equal with (f:=observe) in H0. ss. }
    { eapply f_equal with (f:=observe) in H0. ss. }
    { eapply f_equal with (f:=observe) in H0. ss.
      unfold trigger in H0. ss. cbn in H0.
      dependent destruction H0. ired. et. }
  Qed.


  Let itree_eta E R (itr0 itr1: itree E R)
      (OBSERVE: observe itr0 = observe itr1)
    :
      itr0 = itr1.
  Proof.
    rewrite (itree_eta_ itr0).
    rewrite (itree_eta_ itr1).
    rewrite OBSERVE. auto.
  Qed.

  Lemma step_trigger_choose X k x
    :
      step (trigger (Choose X) >>= k) None (k x).
  Proof.
    unfold trigger. ss.
    match goal with
    | [ |- step ?itr _ _] =>
      replace itr with (Subevent.vis (Choose X) k)
    end; ss.
    { econs. }
    { eapply itree_eta. ss. cbv. f_equal.
      extensionality x0. eapply itree_eta. ss. }
  Qed.

  Lemma step_trigger_take X k x
    :
      step (trigger (Take X) >>= k) None (k x).
  Proof.
    unfold trigger. ss.
    match goal with
    | [ |- step ?itr _ _] =>
      replace itr with (Subevent.vis (Take X) k)
    end; ss.
    { econs. }
    { eapply itree_eta. ss. cbv. f_equal.
      extensionality x0. eapply itree_eta. ss. }
  Qed.

  Lemma step_trigger_syscall fn args (rvs: Any.t -> Prop) k rv
        (RV: rvs rv) (SYS: syscall_sem (event_sys fn args rv))
    :
      step (trigger (Syscall fn args rvs) >>= k) (Some (event_sys fn args rv)) (k rv).
  Proof.
    unfold trigger. ss.
    match goal with
    | [ |- step ?itr _ _] =>
      replace itr with (Subevent.vis (Syscall fn args rvs) k)
    end; ss.
    { econs; et. }
    { eapply itree_eta. ss. cbv. f_equal.
      extensionality x0. eapply itree_eta. ss. }
  Qed.


End STS.




Module Beh.

Definition t: Type := Tr.t -> Prop.
Definition improves (src tgt: t): Prop := tgt <1= src.

Section BEHAVES.

  Definition union (st0: state) (P: (option event) -> state -> Prop) :=
    exists ev st1, (<<STEP: L.(step) st0 ev st1>>) /\ (<<UNION: P ev st1>>).
  (* Definition inter (st0: L.(state)) (P: (option event) -> L.(state) -> Prop) := *)
  (*   forall ev st1 (STEP: L.(step) st0 ev st1), <<INTER: P ev st1>>. *)

  Inductive _state_spin (state_spin: L.(state) -> Prop)
            (st0: L.(state)): Prop :=
  | state_spin_angelic
      (SRT: L.(state_sort) st0 = angelic)
      (STEP: forall ev st1 (STEP: L.(step) st0 ev st1), <<TL: state_spin st1>>)
  | state_spin_demonic
      (SRT: L.(state_sort) st0 = demonic)
      (STEP: exists ev st1 (STEP: L.(step) st0 ev st1), <<TL: state_spin st1>>)
  .

  Definition state_spin: _ -> Prop := paco1 _state_spin bot1.

  Lemma state_spin_mon: monotone1 _state_spin.
  Proof.
    ii. inv IN; try (by econs; eauto).
    - econs 1; et. ii. exploit STEP; et.
    - des. econs 2; et. esplits; et.
  Qed.

  Hint Constructors _state_spin.
  Hint Unfold state_spin.
  Hint Resolve state_spin_mon: paco.



  Inductive _of_state (of_state: L.(state) -> Tr.t -> Prop): L.(state) -> Tr.t -> Prop :=
  | sb_final
      st0 retv
      (FINAL: L.(state_sort) st0 = final retv)
    :
    _of_state of_state st0 (Tr.done retv)
  | sb_spin
      st0
      (SPIN: state_spin st0)
    :
    _of_state of_state st0 (Tr.spin)
  | sb_nb
      st0
    :
    _of_state of_state st0 (Tr.nb)
  | sb_vis
      st0 st1 ev evs
      (SRT: L.(state_sort) st0 = vis)
      (STEP: _.(step) st0 (Some ev) st1)
      (TL: of_state st1 evs)
    :
    _of_state of_state st0 (Tr.cons ev evs)
  | sb_demonic
      st0
      evs
      (SRT: L.(state_sort) st0 = demonic)
      (STEP: union st0 (fun e st1 => (<<HD: e = None>>) /\ (<<TL: _of_state of_state st1 evs>>)))
    :
    _of_state of_state st0 evs
  | sb_angelic
      st0
      evs
      (SRT: L.(state_sort) st0 = angelic)
      (STEP: inter st0 (fun e st1 => (<<HD: e = None>>) /\ (<<TL: _of_state of_state st1 evs>>)))
    :
    _of_state of_state st0 evs
  .

  Definition of_state: _ -> _ -> Prop := paco2 _of_state bot2.

  Theorem of_state_ind :
    forall (r P: _ -> _ -> Prop),
      (forall st0 retv, state_sort L st0 = final retv -> P st0 (Tr.done retv)) ->
      (forall st0, state_spin st0 -> P st0 Tr.spin) ->
      (forall st0, P st0 Tr.nb) ->

      (forall st0 st1 ev evs
         (SRT: state_sort L st0 = vis)
         (STEP: _.(step) st0 (Some ev) st1)
         (TL: r st1 evs)
        ,
          P st0 (Tr.cons ev evs)) ->
      (forall st0 evs
         (SRT: state_sort L st0 = demonic)
         (STEP: union st0
                      (fun e st1 =>
                         <<HD: e = None >> /\ <<TL: _of_state r st1 evs >> /\ <<IH: P st1 evs>>)), P st0 evs) ->
      (forall st0 evs
         (* (IH: forall st1 (STEP: L.(step) st0 None st1), P st1 evs) *)
         (SRT: state_sort L st0 = angelic)
         (STEP: inter st0
                      (fun e st1 => <<HD: e = None >> /\ <<TL: _of_state r st1 evs >> /\ <<IH: P st1 evs>>)),
          P st0 evs) ->
      forall s t, _of_state r s t -> P s t.
  Proof.
    (* fix IH 11. i. *)
    (* inv H5; eauto. *)
    (* - eapply H3; eauto. rr in STEP. des; clarify. *)
    (*   + esplits; eauto. rr. esplits; eauto. left. esplits; eauto. eapply IH; eauto. Guarded. *)
    (*   + esplits; eauto. rr. esplits; eauto. right. esplits; eauto. *)
    (* - eapply H4; eauto. ii. exploit STEP; eauto. i; des; clarify. *)
    (*   + esplits; eauto. left. esplits; eauto. eapply IH; eauto. *)
    (*   + esplits; eauto. right. esplits; eauto. *)
    fix IH 11. i.
    inv H5; eauto.
    - eapply H3; eauto. rr in STEP. des; clarify. esplits; eauto. rr. esplits; eauto. eapply IH; eauto.
    - eapply H4; eauto. ii. exploit STEP; eauto. i; des; clarify. esplits; eauto. eapply IH; eauto.
  Qed.

  Lemma of_state_mon: monotone2 _of_state.
  Proof.
    ii. induction IN using of_state_ind; eauto.
    - econs 1; et.
    - econs 2; et.
    - econs 3; et.
    - econs 4; et.
    - econs 5; et. rr in STEP. des; clarify. rr. esplits; et.
    - econs 6; et. ii. exploit STEP; eauto. i; des; clarify.
  Qed.

  Hint Constructors _of_state.
  Hint Unfold of_state.
  Hint Resolve of_state_mon: paco.

  Definition of_program: Tr.t -> Prop := of_state L.(initial_state).




  (**********************************************************)
  (*********************** properties ***********************)
  (**********************************************************)

  Lemma prefix_closed_state
        st0 pre bh
        (BEH: of_state st0 bh)
        (PRE: Tr.prefix pre bh)
    :
    <<NB: of_state st0 (Tr.app pre Tr.nb)>>
  .
  Proof.
    revert_until L. pcofix CIH. i. punfold BEH. rr in PRE. des; subst.
    destruct pre; ss; clarify.
    { pfold. econs; eauto. }

    remember (Tr.cons e (Tr.app pre tl)) as tmp. revert Heqtmp.
    induction BEH using of_state_ind; ii; ss; clarify.
    - pclearbot. pfold. econs; eauto. right. eapply CIH; et. rr; et.
    - pfold. econs 5; eauto. rr in STEP. des; clarify. rr. esplits; eauto.
      exploit IH; et. intro A. punfold A.
    - pfold. econs 6; eauto. ii. exploit STEP; eauto. clear STEP. i; des; clarify. esplits; eauto.
      exploit IH; et. intro A. punfold A.
  Qed.

  Theorem prefix_closed
          pre bh
          (BEH: of_program bh)
          (PRE: Tr.prefix pre bh)
    :
    <<NB: of_program (Tr.app pre Tr.nb)>>
  .
  Proof.
    eapply prefix_closed_state; eauto.
  Qed.

  Lemma nb_bottom
        st0
    :
    <<NB: of_state st0 Tr.nb>>
  .
  Proof. pfold. econs; et. Qed.

  Lemma ub_top
        st0
        (UB: of_state st0 Tr.ub)
    :
    forall beh, of_state st0 beh
  .
  Proof.
    revert_until L. pfold. i. punfold UB.
    remember Tr.ub as tmp. revert Heqtmp.
    induction UB using of_state_ind; ii; ss; clarify.
    - rr in STEP. des. clarify. econs; eauto. rr. esplits; eauto.
    - econs 6; eauto. ii. exploit STEP; eauto. i; des; clarify. esplits; eauto.
  Qed.

  Lemma _beh_astep
        r tr st0 ev st1
        (SRT: L.(state_sort) st0 = angelic)
        (STEP: _.(step) st0 ev st1)
        (BEH: paco2 _of_state r st0 tr)
    :
    <<BEH: paco2 _of_state r st1 tr>>
  .
  Proof.
    exploit wf_angelic; et. i; clarify.
    revert_until L.
    pcofix CIH; i.
    punfold BEH.
    {
      generalize dependent st1.
      induction BEH using of_state_ind; et; try rewrite SRT in *; ii; ss.
      - punfold H. inv H; rewrite SRT in *; ss.
        exploit STEP0; et. i; des. pclearbot. et.
      - rr in STEP. exploit STEP; et. i; des.
        pfold. eapply of_state_mon; et. ii; ss. eapply upaco2_mon; et.
    }
  Qed.

  Lemma beh_astep
        tr st0 ev st1
        (SRT: L.(state_sort) st0 = angelic)
        (STEP: _.(step) st0 ev st1)
        (BEH: of_state st0 tr)
    :
    <<BEH: of_state st1 tr>>
  .
  Proof.
    eapply _beh_astep; et.
  Qed.

  Lemma _beh_dstep
        r tr st0 ev st1
        (SRT: L.(state_sort) st0 = demonic)
        (STEP: _.(step) st0 ev st1)
        (BEH: paco2 _of_state r st1 tr)
    :
    <<BEH: paco2 _of_state r st0 tr>>
  .
  Proof.
    exploit wf_demonic; et. i; clarify.
    pfold. econs 5; et. rr. esplits; et. punfold BEH.
  Qed.

  Lemma beh_dstep
        tr st0 ev st1
        (SRT: L.(state_sort) st0 = demonic)
        (STEP: _.(step) st0 ev st1)
        (BEH: of_state st1 tr)
    :
    <<BEH: of_state st0 tr>>
  .
  Proof.
    eapply _beh_dstep; et.
  Qed.

  Variant dstep_clo (r: L.(state) -> Tr.t -> Prop): L.(state) -> Tr.t -> Prop :=
    | dstep_clo_intro
        st0 tr st1 ev
        (SRT: L.(state_sort) st0 = demonic)
        (STEP: _.(step) st0 ev st1)
        (STEP: r st1 tr)
      :
      dstep_clo r st0 tr
  .

  Lemma dstep_clo_mon: monotone2 dstep_clo.
  Proof. ii. inv IN. econs; et. Qed.

  Lemma dstep_clo_spec: dstep_clo <3= gupaco2 (_of_state) (cpn2 _of_state).
  Proof.
    intros. eapply prespect2_uclo; eauto with paco. econs.
    { eapply dstep_clo_mon. }
    i. inv PR0. pfold. econs 5; et.
    exploit wf_demonic; et. i; clarify.
    red. esplits; et. eapply of_state_mon; et.
  Qed.

  Variant astep_clo (r: L.(state) -> Tr.t -> Prop): L.(state) -> Tr.t -> Prop :=
    | astep_clo_intro
        st0 tr
        (SRT: L.(state_sort) st0 = angelic)
        (STEP: forall st1, _.(step) st0 None st1 -> r st1 tr)
      :
      astep_clo r st0 tr
  .

  Lemma astep_clo_mon: monotone2 astep_clo.
  Proof. ii. inv IN. econs; et. Qed.

  Lemma astep_clo_spec: astep_clo <3= gupaco2 (_of_state) (cpn2 _of_state).
  Proof.
    intros. eapply prespect2_uclo; eauto with paco. econs.
    { eapply astep_clo_mon. }
    i. inv PR0. pfold. econs 6; et. ii.
    exploit wf_angelic; et. i; clarify.
    red. esplits; et. eapply of_state_mon; et.
  Qed.

End BEHAVES.

End Beh.
Hint Unfold Beh.improves.
Hint Constructors Beh._state_spin.
Hint Unfold Beh.state_spin.
Hint Resolve Beh.state_spin_mon: paco.
Hint Constructors Beh._of_state.
Hint Unfold Beh.of_state.
Hint Resolve Beh.of_state_mon: paco.


