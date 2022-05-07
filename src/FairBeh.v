From sflib Require Import sflib.
From ITree Require Export ITree.
From Paco Require Import paco.

Export ITreeNotations.

Require Import Coq.Classes.RelationClasses.

Require Import Lia.

Set Implicit Arguments.

Section OBS.

  Variant obsE: Type :=
    | obsE_syscall (fn: nat) (args: list nat) (retv: nat)
  .

End OBS.

Module Tr.
  CoInductive t {R}: Type :=
  | done (retv: R)
  | spin
  | ub
  | nb
  | cons (hd: obsE) (tl: t)
  .
  Infix "##" := cons (at level 60, right associativity).

  Fixpoint app {R} (pre: list obsE) (bh: @t R): t :=
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

  Definition prefix {R} (pre: list obsE) (bh: @t R): Prop :=
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
    | Observe (fn: nat) (args: list nat): eventE nat
    | Undefined: eventE void
  .

End EVENT.



Section STS.

  Context {Ident: ID}.

  Definition state {R} := itree eventE R.
  Definition imap := id -> nat.

  Definition soft_update (m0 m1: imap): Prop :=
    forall i, le (m1 i) (m0 i).

  Global Program Instance soft_update_PreOrder: PreOrder soft_update.
  Next Obligation.
    ii. auto.
  Qed.
  Next Obligation.
    ii. unfold soft_update in *. specialize (H i). specialize (H0 i). lia.
  Qed.

  Definition fair_update (m0 m1: imap) (f: id -> Flag.t): Prop :=
    forall i, match f i with
         | Flag.fail => lt (m1 i) (m0 i)
         | Flag.emp => le (m1 i) (m0 i)
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
        itr idx0
        (DIV: diverge_index _ idx0 itr)
      :
      _diverge_index diverge_index idx0 (Tau itr)
    | diverge_index_choose
        X ktr x idx0
        (DIV: diverge_index _ idx0 (ktr x))
      :
      _diverge_index diverge_index idx0 (Vis (Choose X) ktr)
    | diverge_index_fair
        fmap ktr idx0 idx1
        (DIV: diverge_index _ idx1 (ktr tt))
        (FAIR: fair_update idx0 idx1 fmap)
      :
      _diverge_index diverge_index idx0 (Vis (Fair fmap) ktr)
    | diverge_index_ub
        ktr idx0
      :
      _diverge_index diverge_index idx0 (Vis Undefined ktr)
  .

  Lemma diverge_index_mon: monotone3 _diverge_index.
  Proof.
    ii. inv IN.
    - econs 1; eauto.
    - econs 2; eauto.
    - econs 3; eauto.
    - econs 4; eauto.
  Qed.

  Definition diverge_index: forall (R: Type) (idx: imap) (itr: state), Prop := paco3 _diverge_index bot3.

  Hint Constructors _diverge_index.
  Hint Unfold diverge_index.
  Hint Resolve diverge_index_mon: paco.
  Hint Resolve cpn3_wcompat: paco.

  Definition diverge (R: Type) (itr: @state _ R): Prop :=
    exists idx, diverge_index idx itr.



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
      imap0 fn args rv ktr tl
      (TL: of_state _ imap0 (ktr rv) tl)
    :
    _of_state of_state imap0 (Vis (Observe fn args) ktr) (Tr.cons (obsE_syscall fn args rv) tl)

  | tau
      imap0 itr tr
      (STEP: _of_state of_state imap0 itr tr)
    :
    _of_state of_state imap0 (Tau itr) tr
  | choose
      imap0 X ktr x tr
      (STEP: _of_state of_state imap0 (ktr x) tr)
    :
    _of_state of_state imap0 (Vis (Choose X) ktr) tr
  | fair
      imap0 imap1 fmap ktr tr
      (STEP: _of_state of_state imap1 (ktr tt) tr)
      (FMAP: fair_update imap0 imap1 fmap)
    :
    _of_state of_state imap0 (Vis (Fair fmap) ktr) tr

  | ub
      imap0 ktr tr
    :
    _of_state of_state imap0 (Vis Undefined ktr) tr
  .

  Definition of_state: forall (R: Type),  imap -> state -> Tr.t -> Prop := paco4 _of_state bot4.

  Theorem of_state_ind:
    forall (r: forall (R: Type), imap -> state -> Tr.t -> Prop) R (P: imap -> state -> Tr.t -> Prop),
      (forall imap0 retv, P imap0 (Ret retv) (Tr.done retv)) ->
      (forall imap0 st0, diverge_index imap0 st0 -> P imap0 st0 Tr.spin) ->
      (forall imap0 st0, P imap0 st0 Tr.nb) ->
      (forall imap0 fn args rv ktr tl
         (TL: r _ imap0 (ktr rv) tl)
        ,
          P imap0 (Vis (Observe fn args) ktr) (Tr.cons (obsE_syscall fn args rv) tl)) ->
      (forall imap0 itr tr
         (STEP: _of_state r imap0 itr tr)
         (IH: P imap0 itr tr)
        ,
          P imap0 (Tau itr) tr) ->
      (forall imap0 X ktr x tr
         (STEP: _of_state r imap0 (ktr x) tr)
         (IH: P imap0 (ktr x) tr)
        ,
          P imap0 (Vis (Choose X) ktr) tr) ->
      (forall imap0 imap1 fmap ktr tr
         (STEP: _of_state r imap1 (ktr tt) tr)
         (FAIR: fair_update imap0 imap1 fmap)
         (IH: P imap1 (ktr tt) tr)
        ,
          P imap0 (Vis (Fair fmap) ktr) tr) ->
      (forall imap0 ktr tr, P imap0 (Vis Undefined ktr) tr) ->
      forall i s t, @_of_state r R i s t -> P i s t.
  Proof.
    fix IH 15. i.
    inv H7; eauto.
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
    - econs 8; eauto.
  Qed.

  Hint Constructors _of_state.
  Hint Unfold of_state.
  Hint Resolve of_state_mon: paco.
  Hint Resolve cpn4_wcompat: paco.

  (****************************************************)
  (*********************** upto ***********************)
  (****************************************************)

  Variant diverge_imap_le_ctx
          (diverge_index: forall R, imap -> (@state _ R) -> Prop)
          R
    :
    imap -> (@state _ R) -> Prop :=
    | diverge_imap_le_ctx_intro
        imap0 imap1 st
        (DIV: @diverge_index R imap1 st)
        (IMAP: soft_update imap0 imap1)
      :
      diverge_imap_le_ctx diverge_index imap0 st.

  Lemma diverge_imap_le_ctx_mon: monotone3 diverge_imap_le_ctx.
  Proof. ii. inv IN. econs 1; eauto. Qed.

  Hint Resolve diverge_imap_le_ctx_mon: paco.

  Lemma diverge_imap_le_ctx_wrespectful: wrespectful3 _diverge_index diverge_imap_le_ctx.
  Proof.
    econs; eauto with paco.
    i. inv PR. dup DIV. apply GF in DIV. inv DIV; eauto.
    { econs 1. eapply rclo3_clo_base. econs 1; eauto. }
    { econs 2. eapply rclo3_clo_base. econs 1; eauto. }
    { econs 3. eapply rclo3_clo_base. econs 1. eauto. reflexivity.
      clear - IMAP FAIR. unfold fair_update, soft_update in *. i. specialize (IMAP i). specialize (FAIR i).
      des_ifs; nia.
    }
  Qed.

  Lemma diverge_imap_le_ctx_spec: diverge_imap_le_ctx <4= gupaco3 _diverge_index (cpn3 _diverge_index).
  Proof. i. eapply wrespect3_uclo; eauto with paco. eapply diverge_imap_le_ctx_wrespectful. Qed.



  Variant imap_le_ctx
          (of_state: forall R, imap -> (@state _ R) -> (@Tr.t R) -> Prop)
          R
    :
    imap -> (@state _ R) -> (@Tr.t R) -> Prop :=
    | imap_le_ctx_intro
        imap0 imap1 st tr
        (BEH: @of_state R imap1 st tr)
        (IMAP: soft_update imap0 imap1)
      :
      imap_le_ctx of_state imap0 st tr.

  Lemma imap_le_ctx_mon: monotone4 imap_le_ctx.
  Proof. ii. inv IN. econs 1; eauto. Qed.

  Hint Resolve imap_le_ctx_mon: paco.

  Lemma imap_le_ctx_wrespectful: wrespectful4 _of_state imap_le_ctx.
  Proof.
    econs; eauto with paco.
    i. inv PR. apply GF in BEH. depgen x1. induction BEH; i; eauto.
    { econs 2. ginit. guclo diverge_imap_le_ctx_spec. econs; eauto. gstep. punfold SPIN.
      eapply diverge_index_mon; eauto. i. gfinal. pclearbot. auto.
    }
    { econs. eapply rclo4_clo_base. econs; eauto. }
    { econs. eapply IHBEH. reflexivity. clear - IMAP FMAP. unfold fair_update, soft_update in *.
      i. specialize (FMAP i). specialize (IMAP i). des_ifs; lia.
    }
  Qed.

  Lemma imap_le_ctx_spec: imap_le_ctx <5= gupaco4 _of_state (cpn4 _of_state).
  Proof. i. eapply wrespect4_uclo; eauto with paco. eapply imap_le_ctx_wrespectful. Qed.



  Variant of_state_indC
          (of_state: forall R, imap -> (@state _ R) -> (@Tr.t R) -> Prop)
          R
    :
    imap -> (@state _ R) -> (@Tr.t R) -> Prop :=
  | of_state_indC_done
      imap0 retv
    :
    of_state_indC of_state imap0 (Ret retv) (Tr.done retv)
  | of_state_indC_spin
      imap0 st0
      (SPIN: diverge_index imap0 st0)
    :
    of_state_indC of_state imap0 st0 (Tr.spin)
  | of_state_indC_nb
      imap0 st0
    :
    of_state_indC of_state imap0 st0 (Tr.nb)
  | of_state_indC_obs
      imap0 fn args rv ktr tl
      (TL: of_state _ imap0 (ktr rv) tl)
    :
    of_state_indC of_state imap0 (Vis (Observe fn args) ktr) (Tr.cons (obsE_syscall fn args rv) tl)

  | of_state_indC_tau
      imap0 itr tr
      (STEP: of_state _ imap0 itr tr)
    :
    of_state_indC of_state imap0 (Tau itr) tr
  | of_state_indC_choose
      imap0 X ktr x tr
      (STEP: of_state _ imap0 (ktr x) tr)
    :
    of_state_indC of_state imap0 (Vis (Choose X) ktr) tr
  | of_state_indC_fair
      imap0 imap1 fmap ktr tr
      (STEP: of_state _ imap1 (ktr tt) tr)
      (FMAP: fair_update imap0 imap1 fmap)
    :
    of_state_indC of_state imap0 (Vis (Fair fmap) ktr) tr

  | of_state_indC_ub
      imap0 ktr tr
    :
    of_state_indC of_state imap0 (Vis Undefined ktr) tr
  .

  Lemma of_state_indC_mon: monotone4 of_state_indC.
  Proof. ii. inv IN; econs; eauto. Qed.

  Hint Resolve of_state_indC_mon: paco.

  Lemma of_state_indC_wrespectful: wrespectful4 _of_state of_state_indC.
  Proof.
    econs; eauto with paco.
    i. inv PR; eauto.
    { econs; eauto. eapply rclo4_base. eauto. }
    { econs; eauto. eapply of_state_mon; eauto. i. eapply rclo4_base. auto. }
    { econs; eauto. eapply of_state_mon; eauto. i. eapply rclo4_base. auto. }
    { econs; eauto. eapply of_state_mon; eauto. i. eapply rclo4_base. auto. }
  Qed.

  Lemma of_state_indC_spec: of_state_indC <5= gupaco4 _of_state (cpn4 _of_state).
  Proof. i. eapply wrespect4_uclo; eauto with paco. eapply of_state_indC_wrespectful. Qed.



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

  Lemma beh_tau
        R i0 i1 itr tr
        (IMAP: soft_update i0 i1)
        (BEH: @of_state R i1 itr tr)
    :
    <<BEH: of_state i0 (Tau itr) tr>>
  .
  Proof.
    ginit. guclo imap_le_ctx_spec. econs; eauto. guclo of_state_indC_spec. econs; eauto. gfinal. eauto.
  Qed.

  Lemma beh_choose
        R i0 i1 X ktr x tr
        (IMAP: soft_update i0 i1)
        (BEH: @of_state R i1 (ktr x) tr)
    :
    <<BEH: of_state i0 (Vis (Choose X) ktr) tr>>
  .
  Proof.
    ginit. guclo imap_le_ctx_spec. econs; eauto. guclo of_state_indC_spec. econs; eauto. gfinal. eauto.
  Qed.

  Lemma beh_fair
        R i0 i1 f ktr tr
        (FAIR: fair_update i0 i1 f)
        (BEH: @of_state R i1 (ktr tt) tr)
    :
    <<BEH: of_state i0 (Vis (Fair f) ktr) tr>>
  .
  Proof.
    ginit. guclo of_state_indC_spec. econs; eauto. gfinal. eauto.
  Qed.

End BEHAVES.

End Beh.
#[export] Hint Unfold Beh.improves.
#[export] Hint Constructors Beh._diverge_index.
#[export] Hint Unfold Beh.diverge_index.
#[export] Hint Resolve Beh.diverge_index_mon: paco.
#[export] Hint Constructors Beh._of_state.
#[export] Hint Unfold Beh.of_state.
#[export] Hint Resolve Beh.of_state_mon: paco.

#[export] Hint Resolve cpn3_wcompat: paco.
#[export] Hint Resolve cpn4_wcompat: paco.


Section AUX.

  Context {Ident: ID}.

  Theorem of_state_ind2:
    forall R (P: imap -> state -> Tr.t -> Prop),
      (forall imap0 retv, P imap0 (Ret retv) (Tr.done retv)) ->
      (forall imap0 st0, Beh.diverge_index imap0 st0 -> P imap0 st0 Tr.spin) ->
      (forall imap0 st0, P imap0 st0 Tr.nb) ->
      (forall imap0 fn args rv ktr tl
         (TL: Beh.of_state imap0 (ktr rv) tl)
        ,
          P imap0 (Vis (Observe fn args) ktr) (Tr.cons (obsE_syscall fn args rv) tl)) ->
      (forall imap0 itr tr
         (STEP: Beh.of_state imap0 itr tr)
         (IH: P imap0 itr tr)
        ,
          P imap0 (Tau itr) tr) ->
      (forall imap0 X ktr x tr
         (STEP: Beh.of_state imap0 (ktr x) tr)
         (IH: P imap0 (ktr x) tr)
        ,
          P imap0 (Vis (Choose X) ktr) tr) ->
      (forall imap0 imap1 fmap ktr tr
         (STEP: Beh.of_state imap1 (ktr tt) tr)
         (FAIR: fair_update imap0 imap1 fmap)
         (IH: P imap1 (ktr tt) tr)
        ,
          P imap0 (Vis (Fair fmap) ktr) tr) ->
      (forall imap0 ktr tr, P imap0 (Vis Undefined ktr) tr) ->
      forall i s t, (@Beh.of_state _ R i s t) -> P i s t.
  Proof.
    i. eapply Beh.of_state_ind; eauto.
    { i. eapply H3; eauto. pfold. eapply Beh.of_state_mon; eauto. }
    { i. eapply H4; eauto. pfold. eapply Beh.of_state_mon; eauto. }
    { i. eapply H5; eauto. pfold. eapply Beh.of_state_mon; eauto. }
    { punfold H7. eapply Beh.of_state_mon; eauto. i. pclearbot. eauto. }
  Qed.

End AUX.
