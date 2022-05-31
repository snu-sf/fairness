From Paco Require Export paconotation.
From Paco Require Import pacotac_internal paconotation_internal.
Set Implicit Arguments.
Set Primitive Projections.

(** ** Predicates of Arity 1
*)

Section Arg1_def.

Variable T0 : Type.
Variable lf : rel1 T0 -> rel1 T0.
Arguments lf : clear implicits.

Inductive pind (r: rel1 T0) x0 : Prop :=
| pind_pfold pin
    (* (GE : (pind r /1\ r) <1= pin) *)
    (LE : pin <1= (pind r /1\ r))
    (SIM: lf pin x0)
.

Lemma pind_proper
      r (P: T0 -> Prop)
      (PIND: forall x0 pin
               (LE: pin <1= (pind r /1\ r))
               (IH: pin <1= P)
               (SIM: lf pin x0),
          P x0)
  :
  forall x0 (PR: pind r x0), P x0.
Proof.
  fix IH 2. intros. destruct PR. eapply PIND; eauto.
  intros. apply IH. apply LE in PR. destruct PR. auto.
Qed.

Definition upind (r: rel1 T0) := pind r /1\ r.

End Arg1_def.

Arguments pind [ T0 ] lf r x0.
Arguments upind [ T0 ] lf r x0.
#[export] Hint Unfold upind : core.

(* Less than or equal - internal use only *)
Notation "p <_pind_1= q" :=
  (forall _pind_x0 (PR: p _pind_x0 : Prop), q _pind_x0 : Prop)
  (at level 50, no associativity).

(* (* coinduction automation - internal use only *) *)
(* Ltac pind_cofix_auto := *)
(*   let CIH := fresh "CIH" in cofix CIH; repeat intro; *)
(*   match goal with [H: _ |- _] => apply pind_observe in H; destruct H as [] end; do 2 econstructor; *)
(*   try (match goal with [H: _|-_] => apply H end); intros; *)
(*   lazymatch goal with [PR: _ |- _] => match goal with [H: _ |- _] => apply H in PR end end; *)
(*   repeat match goal with [ H : _ \/ _ |- _] => destruct H end; first [eauto; fail|eauto 10]. *)

Definition monotone T0 (lf: rel1 T0 -> rel1 T0) :=
  forall x0 r r' (IN: lf r x0) (LE: r <1= r'), lf r' x0.

Definition _monotone T0 (lf: rel1 T0 -> rel1 T0) :=
  forall r r' (LE: r <1= r'), lf r <1== lf r'.

Lemma monotone_eq T0 (lf: rel1 T0 -> rel1 T0) :
  monotone lf <-> _monotone lf.
Proof. unfold monotone, _monotone, le1. split; eauto. Qed.

Lemma pind_mon_gen T0 lf lf' r r' x
      (PR: @pind T0 lf r x)
      (LElf: lf <2= lf')
      (LEr: r <1= r'):
  pind lf' r' x.
Proof.
  generalize dependent lf'. generalize dependent r'. induction PR using pind_proper; intros.
  econstructor.
  2: eauto.
  intros. specialize (LE _ PR). destruct LE. split.
  2: eauto.
  eapply IH; eauto.
Qed.

Section Arg1.

Variable T0 : Type.
Variable lf : rel1 T0 -> rel1 T0.
Arguments lf : clear implicits.

Theorem pind_acc: forall
  l r (OBG: forall rr (DEC: rr <1= r) (IH: rr <1= l), pind lf rr <1= l),
  pind lf r <1= l.
Proof.
  intros. assert (SIM: pind lf (r /1\ l) x0).
  { generalize dependent l. induction PR using pind_proper; intros.
    econstructor. 2: eauto.
    intros. specialize (LE _ PR). destruct LE.
    repeat split; eauto.
    eapply (OBG (r /1\ l)); eauto. all: intros x2 AND; destruct AND; eauto.
  }
  clear PR. eapply (OBG (r /1\ l)); eauto. all: intros x1 AND; destruct AND; eauto.
Qed.

Theorem pind_mon: monotone (pind lf).
Proof.
  unfold monotone. intros. generalize dependent r'. induction IN using pind_proper; intros.
  econstructor. 2: eauto.
  intros. specialize (LE _ PR). destruct LE. split; eauto.
Qed.

Theorem pind_mult_strong: forall r,
    pind lf r <1= pind lf (upind lf r).
Proof.
  intros. unfold upind. induction PR using pind_proper. econstructor. 2: eauto.
  intros. specialize (LE _ PR). destruct LE. repeat split; eauto.
Qed.

Corollary pind_mult: forall r,
    pind lf r <1= pind lf (pind lf r).
Proof.
  intros. eapply pind_mult_strong in PR. eapply pind_mon; eauto. unfold upind. intros x1 AND; destruct AND; eauto.
Qed.

Theorem pind_fold: forall r,
  lf (upind lf r) <1= pind lf r.
Proof.
  intros. econstructor. 2: eauto. intros. destruct PR0. auto.
Qed.

Theorem pind_unfold: forall (MON: monotone lf) r,
  pind lf r <1= lf (upind lf r).
Proof.
  intros. unfold upind. induction PR using pind_proper. eapply MON; eauto.
Qed.

Theorem _pind_acc: forall
  l r (OBG: forall rr (INC: rr <1== r) (CIH: rr <1== l), pind lf rr <1== l),
  pind lf r <1== l.
Proof. unfold le1. eapply pind_acc. Qed.

Theorem _pind_mon: _monotone (pind lf).
Proof. apply monotone_eq. eapply pind_mon. Qed.

Theorem _pind_mult_strong: forall r,
  pind lf r <1== pind lf (upind lf r).
Proof. unfold le1. eapply pind_mult_strong. Qed.

Theorem _pind_fold: forall r,
  lf (upind lf r) <1== pind lf r.
Proof. unfold le1. eapply pind_fold. Qed.

Theorem _pind_unfold: forall (MON: _monotone lf) r,
  pind lf r <1== lf (upind lf r).
Proof.
  unfold le1. intro.
  eapply pind_unfold; apply monotone_eq; eauto.
Qed.

End Arg1.

#[export] Hint Unfold monotone : core.
#[export] Hint Resolve pind_fold : core.

Arguments pind_mon_gen        [ T0 ] lf lf' r r' x PR LElf LEr.
Arguments pind_acc            [ T0 ] lf l r OBG x0 PR.
Arguments pind_mon            [ T0 ] lf x0 r r' IN LE.
Arguments pind_mult_strong    [ T0 ] lf r x0 PR.
Arguments pind_mult           [ T0 ] lf r x0 PR.
Arguments pind_fold           [ T0 ] lf r x0 PR.
Arguments pind_unfold         [ T0 ] lf MON r x0 PR.
