From sflib Require Import sflib.
From ITree Require Export ITree.
From Paco Require Import paco.

Export ITreeNotations.

Require Import Coq.Classes.RelationClasses.

Set Implicit Arguments.

Section OBS.

  Variant obs: Type :=
    | obs_syscall (fn: nat) (args: list nat) (retv: nat)
  .

End OBS.

Module Tr.
  CoInductive t {R}: Type :=
  | done (retv: R)
  | spin
  | ub
  | nb
  | cons (hd: obs) (tl: t)
  .
  Infix "##" := cons (at level 60, right associativity).

  Fixpoint app {R} (pre: list obs) (bh: @t R): t :=
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

  Definition prefix {R} (pre: list obs) (bh: @t R): Prop :=
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
    | Observe (fn: nat) (args: list nat) (retv: nat): eventE nat
    | Undefined: eventE void
  .

End EVENT.



(* Section STS. *)

(*   Context {Ident: ID}. *)

(*   Definition state {R} := itree eventE R. *)

(*   Inductive step {R}: @state R -> option event -> state -> Prop := *)
(*   | step_tau *)
(*       itr *)
(*     : *)
(*     step (Tau itr) None itr *)
(*   | step_choose *)
(*       X ktr (x: X) *)
(*     : *)
(*     step (Vis (Choose X) ktr) None (ktr x) *)
(*   | step_fair *)
(*       m ktr *)
(*     : *)
(*     step (Vis (Fair m) ktr) None (ktr tt) *)
(*   | step_syscall *)
(*       fn args retv ktr *)
(*     : *)
(*     step (Vis (Syscall fn args retv) ktr) (Some (event_syscall fn args retv)) (ktr retv) *)
(*   . *)

(*   Lemma step_trigger_choose_iff X k itr e *)
(*         (STEP: step (trigger (Choose X) >>= k) e itr) *)
(*     : *)
(*       exists x, *)
(*         e = None /\ itr = k x. *)
(*   Proof. *)
(*     inv STEP. *)
(*     { eapply f_equal with (f:=observe) in H0. ss. } *)
(*     { eapply f_equal with (f:=observe) in H0. ss. *)
(*       unfold trigger in H0. ss. cbn in H0. *)
(*       dependent destruction H0. ired. et.  } *)
(*     { eapply f_equal with (f:=observe) in H0. ss. } *)
(*     { eapply f_equal with (f:=observe) in H0. ss. } *)
(*   Qed. *)

(*   Lemma step_trigger_take_iff X k itr e *)
(*         (STEP: step (trigger (Take X) >>= k) e itr) *)
(*     : *)
(*       exists x, *)
(*         e = None /\ itr = k x. *)
(*   Proof. *)
(*     inv STEP. *)
(*     { eapply f_equal with (f:=observe) in H0. ss. } *)
(*     { eapply f_equal with (f:=observe) in H0. ss. } *)
(*     { eapply f_equal with (f:=observe) in H0. ss. *)
(*       unfold trigger in H0. ss. cbn in H0. *)
(*       dependent destruction H0. ired. et.  } *)
(*     { eapply f_equal with (f:=observe) in H0. ss. } *)
(*   Qed. *)

(*   Lemma step_tau_iff itr0 itr1 e *)
(*         (STEP: step (Tau itr0) e itr1) *)
(*     : *)
(*       e = None /\ itr0 = itr1. *)
(*   Proof. *)
(*     inv STEP. et. *)
(*   Qed. *)

(*   Lemma step_ret_iff rv itr e *)
(*         (STEP: step (Ret rv) e itr) *)
(*     : *)
(*       False. *)
(*   Proof. *)
(*     inv STEP. *)
(*   Qed. *)

(*   Lemma step_trigger_syscall_iff fn args rvs k e itr *)
(*         (STEP: step (trigger (Syscall fn args rvs) >>= k) e itr) *)
(*     : *)
(*       exists rv, itr = k rv /\ e = Some (event_sys fn args rv) *)
(*                  /\ <<RV: rvs rv>> /\ <<SYS: syscall_sem (event_sys fn args rv)>>. *)
(*   Proof. *)
(*     inv STEP. *)
(*     { eapply f_equal with (f:=observe) in H0. ss. } *)
(*     { eapply f_equal with (f:=observe) in H0. ss. } *)
(*     { eapply f_equal with (f:=observe) in H0. ss. } *)
(*     { eapply f_equal with (f:=observe) in H0. ss. *)
(*       unfold trigger in H0. ss. cbn in H0. *)
(*       dependent destruction H0. ired. et. } *)
(*   Qed. *)


(*   Let itree_eta E R (itr0 itr1: itree E R) *)
(*       (OBSERVE: observe itr0 = observe itr1) *)
(*     : *)
(*       itr0 = itr1. *)
(*   Proof. *)
(*     rewrite (itree_eta_ itr0). *)
(*     rewrite (itree_eta_ itr1). *)
(*     rewrite OBSERVE. auto. *)
(*   Qed. *)

(*   Lemma step_trigger_choose X k x *)
(*     : *)
(*       step (trigger (Choose X) >>= k) None (k x). *)
(*   Proof. *)
(*     unfold trigger. ss. *)
(*     match goal with *)
(*     | [ |- step ?itr _ _] => *)
(*       replace itr with (Subevent.vis (Choose X) k) *)
(*     end; ss. *)
(*     { econs. } *)
(*     { eapply itree_eta. ss. cbv. f_equal. *)
(*       extensionality x0. eapply itree_eta. ss. } *)
(*   Qed. *)

(*   Lemma step_trigger_take X k x *)
(*     : *)
(*       step (trigger (Take X) >>= k) None (k x). *)
(*   Proof. *)
(*     unfold trigger. ss. *)
(*     match goal with *)
(*     | [ |- step ?itr _ _] => *)
(*       replace itr with (Subevent.vis (Take X) k) *)
(*     end; ss. *)
(*     { econs. } *)
(*     { eapply itree_eta. ss. cbv. f_equal. *)
(*       extensionality x0. eapply itree_eta. ss. } *)
(*   Qed. *)

(*   Lemma step_trigger_syscall fn args (rvs: Any.t -> Prop) k rv *)
(*         (RV: rvs rv) (SYS: syscall_sem (event_sys fn args rv)) *)
(*     : *)
(*       step (trigger (Syscall fn args rvs) >>= k) (Some (event_sys fn args rv)) (k rv). *)
(*   Proof. *)
(*     unfold trigger. ss. *)
(*     match goal with *)
(*     | [ |- step ?itr _ _] => *)
(*       replace itr with (Subevent.vis (Syscall fn args rvs) k) *)
(*     end; ss. *)
(*     { econs; et. } *)
(*     { eapply itree_eta. ss. cbv. f_equal. *)
(*       extensionality x0. eapply itree_eta. ss. } *)
(*   Qed. *)


(* End STS. *)


Section STS.

  Context {Ident: ID}.

  Definition state {R} := itree eventE R.
  Definition imap := id -> nat.

  Definition fair_update (m0 m1: imap) (f: id -> Flag.t) : Prop :=
    forall j, match f j with
         | Flag.fail => lt (m1 j) (m0 j)
         | Flag.emp => le (m1 j) (m0 j)
         | Flag.success => True
         end.

End STS.

Module Beh.

Definition t {R}: Type := @Tr.t R -> Prop.
Definition improves {R} (src tgt: @t R): Prop := tgt <1= src.

Section BEHAVES.

  Context {Ident: ID}.

  Variant _diverge_index
          (diverge_index: forall (R: Type) (idx: imap) (itr: @state _ R), Prop)
          (R: Type)
    :
    forall (idx: imap) (itr: @state _ R), Prop :=
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
        fmap ktr idx0 idx1
        (DIV: diverge_index _ idx1 (ktr tt))
        (FAIR: fair_update idx0 idx1 fmap)
      :
      _diverge_index diverge_index idx0 (Vis (Fair fmap) ktr)
    (* | diverge_index_syscall *)
    (*     fn args retv ktr idx0 idx1 *)
    (*     (DIV: diverge_index _ idx1 (ktr retv)) *)
    (*     (IDX: forall i, idx1 i <= idx0 i) *)
    (*   : *)
    (*   _diverge_index diverge_index idx0 (Vis (Observe fn args retv) ktr) *)
  .

  Lemma diverge_index_mon: monotone3 _diverge_index.
  Proof.
    ii. inv IN.
    - econs 1; eauto.
    - econs 2; eauto.
    - econs 3; eauto.
    (* - econs 4; eauto. *)
  Qed.

  Definition diverge_index: forall (R: Type) (idx: imap) (itr: state), Prop := paco3 _diverge_index bot3.

  Hint Constructors _diverge_index.
  Hint Unfold diverge_index.
  Hint Resolve diverge_index_mon: paco.

  Definition diverge (R: Type) (itr: @state _ R): Prop :=
    exists idx, diverge_index idx itr.


  (* Definition union {R} (st0: @state R) (P: (option obs) -> (@state R) -> Prop) := *)
  (*   exists ev st1, (<<STEP: L.(step) st0 ev st1>>) /\ (<<UNION: P ev st1>>). *)
  (* Definition inter (st0: L.(state)) (P: (option event) -> L.(state) -> Prop) := *)
  (*   forall ev st1 (STEP: L.(step) st0 ev st1), <<INTER: P ev st1>>. *)


  Inductive _of_state
            (of_state: forall (R: Type), imap -> (@state _ R) -> (@Tr.t R) -> Prop)
            (R: Type)
    :
    imap -> (@state _ R) -> Tr.t -> Prop :=
  | done
      imap0 retv
    :
    _of_state of_state imap0 (Ret retv) (Tr.done retv)
  | spin
      imap0 st0
      (SPIN: diverge_index imap0 st0)
    :
    _of_state of_state imap0 st0 (Tr.spin)
  | nb
      imap0 st0
    :
    _of_state of_state imap0 st0 (Tr.nb)
  | obs
      imap0 imap1 fn args rv ktr tl
      (IMAP: forall j, le (imap1 j) (imap0 j))
      (TL: of_state _ imap1 (ktr rv) tl)
    :
    _of_state of_state imap0 (Vis (Observe fn args rv) ktr) (Tr.cons (obs_syscall fn args rv) tl)

  | tau
      imap0 imap1 itr tr
      (IMAP: forall j, le (imap1 j) (imap0 j))
      (STEP: _of_state of_state imap1 itr tr)
    :
    _of_state of_state imap0 (Tau itr) tr
  | choose
      imap0 imap1 X ktr x tr
      (IMAP: forall j, le (imap1 j) (imap0 j))
      (STEP: _of_state of_state imap1 (ktr x) tr)
    :
    _of_state of_state imap0 (Vis (Choose X) ktr) tr
  | fair
      imap0 imap1 fmap ktr tr
      (FMAP: fair_update imap0 imap1 fmap)
      (STEP: _of_state of_state imap1 (ktr tt) tr)
      (* (STEP: union st0 (fun e st1 => (<<HD: e = None>>) /\ (<<TL: _of_state of_state st1 evs>>))) *)
    :
    _of_state of_state imap0 (Vis (Fair fmap) ktr) tr
  (* | sb_angelic *)
  (*     st0 *)
  (*     evs *)
  (*     (SRT: L.(state_sort) st0 = angelic) *)
  (*     (STEP: inter st0 (fun e st1 => (<<HD: e = None>>) /\ (<<TL: _of_state of_state st1 evs>>))) *)
  (*   : *)
  (*   _of_state of_state st0 evs *)
  .

  Definition of_state: forall (R: Type),  imap -> state -> Tr.t -> Prop := paco4 _of_state bot4.

  Theorem of_state_ind:
    forall (r: forall (R: Type), imap -> state -> Tr.t -> Prop) R (P: imap -> state -> Tr.t -> Prop),
      (forall imap0 retv, P imap0 (Ret retv) (Tr.done retv)) ->
      (forall imap0 st0, diverge_index imap0 st0 -> P imap0 st0 Tr.spin) ->
      (forall imap0 st0, P imap0 st0 Tr.nb) ->
      (forall imap0 imap1 fn args rv ktr tl
         (IMAP: forall j, le (imap1 j) (imap0 j))
         (TL: r _ imap1 (ktr rv) tl)
        ,
          P imap0 (Vis (Observe fn args rv) ktr) (Tr.cons (obs_syscall fn args rv) tl)) ->
      (forall imap0 imap1 itr tr
         (IMAP: forall j, le (imap1 j) (imap0 j))
         (STEP: _of_state r imap1 itr tr)
         (IH: P imap1 itr tr)
        ,
          P imap0 (Tau itr) tr) ->
      (forall imap0 imap1 X ktr x tr
         (IMAP: forall j, le (imap1 j) (imap0 j))
         (STEP: _of_state r imap1 (ktr x) tr)
         (IH: P imap1 (ktr x) tr)
        ,
          P imap0 (Vis (Choose X) ktr) tr) ->
      (forall imap0 imap1 fmap ktr tr
         (FAIR: fair_update imap0 imap1 fmap)
         (STEP: _of_state r imap1 (ktr tt) tr)
         (IH: P imap1 (ktr tt) tr)
        ,
          P imap0 (Vis (Fair fmap) ktr) tr) ->
      forall i s t, @_of_state r R i s t -> P i s t.
  Proof.
    fix IH 14. i.
    inv H6; eauto.
    - eapply H3; eauto. eapply IH; eauto.
    - eapply H4; eauto. eapply IH; eauto.
    - eapply H5; eauto. eapply IH; eauto.
  Qed.

  Lemma of_state_mon: monotone4 _of_state.
  Proof.
    ii. induction IN using of_state_ind; eauto.
    - econs 1; eauto.
    - econs 2; eauto.
    - econs 3; eauto.
    - econs 4; eauto.
    - econs 5; eauto.
    - econs 6; eauto.
    - econs 7; eauto.
  Qed.

  Hint Constructors _of_state.
  Hint Unfold of_state.
  Hint Resolve of_state_mon: paco.


  (**********************************************************)
  (*********************** properties ***********************)
  (**********************************************************)

  Lemma prefix_closed_state
        R i0 st0 pre bh
        (BEH: of_state i0 st0 bh)
        (PRE: Tr.prefix pre bh)
    :
    <<NB: @of_state R i0 st0 (Tr.app pre Tr.nb)>>
  .
  Proof.
    revert_until Ident. pcofix CIH. i. punfold BEH. rr in PRE. des; subst.
    destruct pre; ss; clarify.
    { pfold. econs; eauto. }
    remember (Tr.cons o (Tr.app pre tl)) as tmp. revert Heqtmp.
    induction BEH using of_state_ind; ii; ss; clarify.
    - pclearbot. pfold. econs; eauto. right. eapply CIH; eauto. rr; eauto.
    - pfold. econs 5; eauto. hexploit IHBEH; eauto. intro A. punfold A.
    - pfold. econs 6; eauto. hexploit IHBEH; eauto. intro A. punfold A.
    - pfold. econs 7; eauto. hexploit IHBEH; eauto. intro A. punfold A.
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
        R i0 st0
    :
    <<NB: @of_state R i0 st0 Tr.nb>>
  .
  Proof. pfold. econs; eauto. Qed.

  Lemma ub_top
        R i0 st0
        (UB: @of_state R i0 st0 Tr.ub)
    :
    forall beh, of_state i0 st0 beh
  .
  Proof.
    pfold. i. punfold UB.
    remember Tr.ub as tmp. revert Heqtmp.
    induction UB using of_state_ind; ii; ss; clarify.
    - econs; eauto.
    - econs 6; eauto.
    - econs 7; eauto.
  Qed.

  (* Lemma _beh_astep *)
  (*       r tr st0 ev st1 *)
  (*       (SRT: L.(state_sort) st0 = angelic) *)
  (*       (STEP: _.(step) st0 ev st1) *)
  (*       (BEH: paco2 _of_state r st0 tr) *)
  (*   : *)
  (*   <<BEH: paco2 _of_state r st1 tr>> *)
  (* . *)
  (* Proof. *)
  (*   exploit wf_angelic; et. i; clarify. *)
  (*   revert_until L. *)
  (*   pcofix CIH; i. *)
  (*   punfold BEH. *)
  (*   { *)
  (*     generalize dependent st1. *)
  (*     induction BEH using of_state_ind; et; try rewrite SRT in *; ii; ss. *)
  (*     - punfold H. inv H; rewrite SRT in *; ss. *)
  (*       exploit STEP0; et. i; des. pclearbot. et. *)
  (*     - rr in STEP. exploit STEP; et. i; des. *)
  (*       pfold. eapply of_state_mon; et. ii; ss. eapply upaco2_mon; et. *)
  (*   } *)
  (* Qed. *)

  (* Lemma beh_astep *)
  (*       tr st0 ev st1 *)
  (*       (SRT: L.(state_sort) st0 = angelic) *)
  (*       (STEP: _.(step) st0 ev st1) *)
  (*       (BEH: of_state st0 tr) *)
  (*   : *)
  (*   <<BEH: of_state st1 tr>> *)
  (* . *)
  (* Proof. *)
  (*   eapply _beh_astep; et. *)
  (* Qed. *)

  Lemma _beh_tau
        R r i0 i1 itr tr
        (IMAP: forall j, le (i1 j) (i0 j))
        (BEH: paco4 _of_state r R i1 itr tr)
    :
    <<BEH: paco4 _of_state r R i0 (Tau itr) tr>>
  .
  Proof.
    pfold. econs 5; eauto. punfold BEH.
  Qed.

  Lemma beh_tau
        R i0 i1 itr tr
        (IMAP: forall j, le (i1 j) (i0 j))
        (BEH: @of_state R i1 itr tr)
    :
    <<BEH: of_state i0 (Tau itr) tr>>
  .
  Proof.
    eapply _beh_tau; eauto.
  Qed.

  Lemma _beh_choose
        R r i0 i1 X ktr x tr
        (IMAP: forall j, le (i1 j) (i0 j))
        (BEH: paco4 _of_state r R i1 (ktr x) tr)
    :
    <<BEH: paco4 _of_state r R i0 (Vis (Choose X) ktr) tr>>
  .
  Proof.
    pfold. econs 6; eauto. punfold BEH.
  Qed.

  Lemma beh_choose
        R i0 i1 X ktr x tr
        (IMAP: forall j, le (i1 j) (i0 j))
        (BEH: @of_state R i1 (ktr x) tr)
    :
    <<BEH: of_state i0 (Vis (Choose X) ktr) tr>>
  .
  Proof.
    eapply _beh_choose; eauto.
  Qed.

  Lemma _beh_fair
        R r i0 i1 f ktr tr
        (FAIR: fair_update i0 i1 f)
        (BEH: paco4 _of_state r R i1 (ktr tt) tr)
    :
    <<BEH: paco4 _of_state r R i0 (Vis (Fair f) ktr) tr>>
  .
  Proof.
    pfold. econs 7; eauto. punfold BEH.
  Qed.

  Lemma beh_fair
        R i0 i1 f ktr tr
        (FAIR: fair_update i0 i1 f)
        (BEH: @of_state R i1 (ktr tt) tr)
    :
    <<BEH: of_state i0 (Vis (Fair f) ktr) tr>>
  .
  Proof.
    eapply _beh_fair; eauto.
  Qed.

  Variant silent_clo (r: forall R, imap -> state -> Tr.t -> Prop) (R: Type): imap -> (@state _ R) -> (@Tr.t R) -> Prop :=
    | silent_clo_tau
        i0 i1 itr tr
        (IMAP: forall j, le (i1 j) (i0 j))
        (STEP: r R i1 itr tr)
      :
      silent_clo r i0 (Tau itr) tr
    | silent_clo_choose
        i0 i1 X ktr x tr
        (IMAP: forall j, le (i1 j) (i0 j))
        (STEP: r R i1 (ktr x) tr)
      :
      silent_clo r i0 (Vis (Choose X) ktr) tr
    | silent_clo_fair
        i0 i1 f ktr tr
        (FAIR: fair_update i0 i1 f)
        (STEP: r R i1 (ktr tt) tr)
      :
      silent_clo r i0 (Vis (Fair f) ktr) tr
  .

  Lemma silent_clo_mon: monotone4 silent_clo.
  Proof. ii. inv IN. all: econs; eauto. Qed.

  Lemma silent_clo_spec: silent_clo <5= gupaco4 (_of_state) (cpn4 _of_state).
  Proof.
    intros. eapply prespect4_uclo; eauto with paco. econs.
    { eapply silent_clo_mon. }
    i. inv PR0.
    - pfold. econs 5; eauto. eapply of_state_mon; eauto.
    - pfold. econs 6; eauto. eapply of_state_mon; eauto.
    - pfold. econs 7; eauto. eapply of_state_mon; eauto.
  Qed.

  (* Lemma _beh_dstep *)
  (*       r tr st0 ev st1 *)
  (*       (SRT: L.(state_sort) st0 = demonic) *)
  (*       (STEP: _.(step) st0 ev st1) *)
  (*       (BEH: paco2 _of_state r st1 tr) *)
  (*   : *)
  (*   <<BEH: paco2 _of_state r st0 tr>> *)
  (* . *)
  (* Proof. *)
  (*   exploit wf_demonic; et. i; clarify. *)
  (*   pfold. econs 5; et. rr. esplits; et. punfold BEH. *)
  (* Qed. *)

  (* Lemma beh_dstep *)
  (*       tr st0 ev st1 *)
  (*       (SRT: L.(state_sort) st0 = demonic) *)
  (*       (STEP: _.(step) st0 ev st1) *)
  (*       (BEH: of_state st1 tr) *)
  (*   : *)
  (*   <<BEH: of_state st0 tr>> *)
  (* . *)
  (* Proof. *)
  (*   eapply _beh_dstep; et. *)
  (* Qed. *)

  (* Variant dstep_clo (r: L.(state) -> Tr.t -> Prop): L.(state) -> Tr.t -> Prop := *)
  (*   | dstep_clo_intro *)
  (*       st0 tr st1 ev *)
  (*       (SRT: L.(state_sort) st0 = demonic) *)
  (*       (STEP: _.(step) st0 ev st1) *)
  (*       (STEP: r st1 tr) *)
  (*     : *)
  (*     dstep_clo r st0 tr *)
  (* . *)

  (* Lemma dstep_clo_mon: monotone2 dstep_clo. *)
  (* Proof. ii. inv IN. econs; et. Qed. *)

  (* Lemma dstep_clo_spec: dstep_clo <3= gupaco2 (_of_state) (cpn2 _of_state). *)
  (* Proof. *)
  (*   intros. eapply prespect2_uclo; eauto with paco. econs. *)
  (*   { eapply dstep_clo_mon. } *)
  (*   i. inv PR0. pfold. econs 5; et. *)
  (*   exploit wf_demonic; et. i; clarify. *)
  (*   red. esplits; et. eapply of_state_mon; et. *)
  (* Qed. *)

  (* Variant astep_clo (r: L.(state) -> Tr.t -> Prop): L.(state) -> Tr.t -> Prop := *)
  (*   | astep_clo_intro *)
  (*       st0 tr *)
  (*       (SRT: L.(state_sort) st0 = angelic) *)
  (*       (STEP: forall st1, _.(step) st0 None st1 -> r st1 tr) *)
  (*     : *)
  (*     astep_clo r st0 tr *)
  (* . *)

  (* Lemma astep_clo_mon: monotone2 astep_clo. *)
  (* Proof. ii. inv IN. econs; et. Qed. *)

  (* Lemma astep_clo_spec: astep_clo <3= gupaco2 (_of_state) (cpn2 _of_state). *)
  (* Proof. *)
  (*   intros. eapply prespect2_uclo; eauto with paco. econs. *)
  (*   { eapply astep_clo_mon. } *)
  (*   i. inv PR0. pfold. econs 6; et. ii. *)
  (*   exploit wf_angelic; et. i; clarify. *)
  (*   red. esplits; et. eapply of_state_mon; et. *)
  (* Qed. *)

End BEHAVES.

End Beh.
Hint Unfold Beh.improves.
Hint Constructors Beh._diverge_index.
Hint Unfold Beh.diverge_index.
Hint Resolve Beh.diverge_index_mon: paco.
Hint Constructors Beh._of_state.
Hint Unfold Beh.of_state.
Hint Resolve Beh.of_state_mon: paco.
