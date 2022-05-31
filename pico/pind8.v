Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paconotation_internal pacotac_internal.
From Paco Require Export paconotation.
Require Import pind_internal.
Set Implicit Arguments.

Section PIND8.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.

(** ** Predicates of Arity 8
*)

Definition pind8(lf : rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7)(r: rel8 T0 T1 T2 T3 T4 T5 T6 T7) : rel8 T0 T1 T2 T3 T4 T5 T6 T7 :=
  @curry8 T0 T1 T2 T3 T4 T5 T6 T7 (pind (fun R0 => @uncurry8 T0 T1 T2 T3 T4 T5 T6 T7 (lf (@curry8 T0 T1 T2 T3 T4 T5 T6 T7 R0))) (@uncurry8 T0 T1 T2 T3 T4 T5 T6 T7 r)).

Definition upind8(lf : rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7)(r: rel8 T0 T1 T2 T3 T4 T5 T6 T7) := pind8 lf r /8\ r.
Arguments pind8 : clear implicits.
Arguments upind8 : clear implicits.
#[local] Hint Unfold upind8 : core.

Definition monotone8 (lf: rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 r r' (IN: lf r x0 x1 x2 x3 x4 x5 x6 x7) (LE: r <8= r'), lf r' x0 x1 x2 x3 x4 x5 x6 x7.

Definition _monotone8 (lf: rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7) :=
  forall r r'(LE: r <8= r'), lf r <8== lf r'.

Lemma monotone8_eq (lf: rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7) :
  monotone8 lf <-> _monotone8 lf.
Proof. unfold monotone8, _monotone8, le8. split; intros; eapply H; eassumption. Qed.

Lemma monotone8_map (lf: rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7)
      (MON: _monotone8 lf) :
  _monotone (fun R0 => @uncurry8 T0 T1 T2 T3 T4 T5 T6 T7 (lf (@curry8 T0 T1 T2 T3 T4 T5 T6 T7 R0))).
Proof.
  red; intros. apply uncurry_map8. apply MON; apply curry_map8; assumption.
Qed.

Lemma monotone8_compose (lf lf': rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7)
      (MON1: monotone8 lf)
      (MON2: monotone8 lf'):
  monotone8 (compose lf lf').
Proof.
  red; intros. eapply MON1. apply IN.
  intros. eapply MON2. apply PR. apply LE.
Qed.

Lemma monotone8_union (lf lf': rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7)
      (MON1: monotone8 lf)
      (MON2: monotone8 lf'):
  monotone8 (lf \9/ lf').
Proof.
  red; intros. destruct IN.
  - left. eapply MON1. apply H. apply LE.
  - right. eapply MON2. apply H. apply LE.
Qed.

Lemma monotone8_inter (lf lf': rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7)
      (MON1: monotone8 lf)
      (MON2: monotone8 lf'):
  monotone8 (lf /9\ lf').
Proof.
  red; intros. destruct IN. split.
  - eapply MON1. apply H. apply LE.
  - eapply MON2. apply H0. apply LE.
Qed.

Lemma _pind8_mon_gen (lf lf': rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7) r r'
    (LElf: lf <9= lf')
    (LEr: r <8= r'):
  pind8 lf r <8== pind8 lf' r'.
Proof.
  apply curry_map8. red; intros. eapply pind_mon_gen. apply PR.
  - intros. apply LElf, PR0.
  - intros. apply LEr, PR0.
Qed.

Lemma pind8_mon_gen (lf lf': rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7) r r' x0 x1 x2 x3 x4 x5 x6 x7
    (REL: pind8 lf r x0 x1 x2 x3 x4 x5 x6 x7)
    (LElf: lf <9= lf')
    (LEr: r <8= r'):
  pind8 lf' r' x0 x1 x2 x3 x4 x5 x6 x7.
Proof.
  eapply _pind8_mon_gen; [apply LElf | apply LEr | apply REL].
Qed.

Lemma pind8_mon_bot (lf lf': rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7) r' x0 x1 x2 x3 x4 x5 x6 x7
    (REL: pind8 lf bot8 x0 x1 x2 x3 x4 x5 x6 x7)
    (LElf: lf <9= lf'):
  pind8 lf' r' x0 x1 x2 x3 x4 x5 x6 x7.
Proof.
  eapply pind8_mon_gen; [apply REL | apply LElf | intros; contradiction PR].
Qed.

Definition top8 {T0 T1 T2 T3 T4 T5 T6 T7} (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) (x4: T4 x0 x1 x2 x3) (x5: T5 x0 x1 x2 x3 x4) (x6: T6 x0 x1 x2 x3 x4 x5) (x7: T7 x0 x1 x2 x3 x4 x5 x6) := True.

Lemma pind8_mon_top (lf lf': rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7) r x0 x1 x2 x3 x4 x5 x6 x7
    (REL: pind8 lf r x0 x1 x2 x3 x4 x5 x6 x7)
    (LElf: lf <9= lf'):
  pind8 lf' top8 x0 x1 x2 x3 x4 x5 x6 x7.
Proof.
  eapply pind8_mon_gen; eauto. red. auto.
Qed.

Lemma upind8_mon_gen (lf lf': rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7) r r' x0 x1 x2 x3 x4 x5 x6 x7
    (REL: upind8 lf r x0 x1 x2 x3 x4 x5 x6 x7)
    (LElf: lf <9= lf')
    (LEr: r <8= r'):
  upind8 lf' r' x0 x1 x2 x3 x4 x5 x6 x7.
Proof.
  destruct REL. split.
  - eapply pind8_mon_gen; [apply H | apply LElf | apply LEr].
  - apply LEr, H0.
Qed.

Lemma upind8_mon_bot (lf lf': rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7) r' x0 x1 x2 x3 x4 x5 x6 x7
    (REL: upind8 lf bot8 x0 x1 x2 x3 x4 x5 x6 x7)
    (LElf: lf <9= lf'):
  upind8 lf' r' x0 x1 x2 x3 x4 x5 x6 x7.
Proof.
  eapply upind8_mon_gen; [apply REL | apply LElf | intros; contradiction PR].
Qed.

Lemma upind8_mon_top (lf lf': rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7) r x0 x1 x2 x3 x4 x5 x6 x7
    (REL: upind8 lf r x0 x1 x2 x3 x4 x5 x6 x7)
    (LElf: lf <9= lf'):
  upind8 lf' top8 x0 x1 x2 x3 x4 x5 x6 x7.
Proof.
  eapply upind8_mon_gen; eauto. red. auto.
Qed.

Section Arg8.

Variable lf : rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7.
Arguments lf : clear implicits.

Theorem _pind8_mon: _monotone8 (pind8 lf).
Proof.
  red; intros. eapply curry_map8, _pind_mon; apply uncurry_map8; assumption.
Qed.

Theorem _pind8_acc: forall
  l r (OBG: forall rr (INC: rr <8== r) (CIH: rr <8== l), pind8 lf rr <8== l),
  pind8 lf r <8== l.
Proof.
  intros. apply curry_adjoint2_8.
  eapply _pind_acc. intros.
  apply curry_adjoint2_8 in INC. apply curry_adjoint2_8 in CIH.
  apply curry_adjoint1_8.
  eapply le8_trans. 2: eapply (OBG _ INC CIH).
  apply curry_map8.
  apply _pind_mon; try apply le1_refl; apply curry_bij2_8.
Qed.

Theorem _pind8_mult_strong: forall r,
  pind8 lf r <8== pind8 lf (upind8 lf r).
Proof.
  intros. apply curry_map8.
  eapply le1_trans; [eapply _pind_mult_strong |].
  apply _pind_mon. intros [] H. apply H.
Qed.

Theorem _pind8_fold: forall r,
  lf (upind8 lf r) <8== pind8 lf r.
Proof.
  intros. apply uncurry_adjoint1_8.
  eapply le1_trans; [| apply _pind_fold]. apply le1_refl.
Qed.

Theorem _pind8_unfold: forall (MON: _monotone8 lf) r,
  pind8 lf r <8== lf (upind8 lf r).
Proof.
  intros. apply curry_adjoint2_8.
  eapply _pind_unfold; apply monotone8_map; assumption.
Qed.

Theorem pind8_acc: forall
  l r (OBG: forall rr (INC: rr <8= r) (CIH: rr <8= l), pind8 lf rr <8= l),
  pind8 lf r <8= l.
Proof.
  apply _pind8_acc.
Qed.

Theorem pind8_mon: monotone8 (pind8 lf).
Proof.
  apply monotone8_eq.
  apply _pind8_mon.
Qed.

Theorem upind8_mon: monotone8 (upind8 lf).
Proof.
  red; intros.
  destruct IN. split.
  - eapply pind8_mon. apply H. apply LE.
  - apply LE, H0.
Qed.

Theorem pind8_mult_strong: forall r,
  pind8 lf r <8= pind8 lf (upind8 lf r).
Proof.
  apply _pind8_mult_strong.
Qed.

Corollary pind8_mult: forall r,
    pind8 lf r <8= pind8 lf (pind8 lf r).
Proof. intros. eapply pind8_mult_strong in PR. eapply pind8_mon; eauto. intros. destruct PR0; eauto. Qed.

Theorem pind8_fold: forall r,
  lf (upind8 lf r) <8= pind8 lf r.
Proof.
  apply _pind8_fold.
Qed.

Theorem pind8_unfold: forall (MON: monotone8 lf) r,
  pind8 lf r <8= lf (upind8 lf r).
Proof.
  intro. eapply _pind8_unfold; apply monotone8_eq; assumption.
Qed.

End Arg8.

Arguments pind8_acc : clear implicits.
Arguments pind8_mon : clear implicits.
Arguments upind8_mon : clear implicits.
Arguments pind8_mult_strong : clear implicits.
Arguments pind8_mult : clear implicits.
Arguments pind8_fold : clear implicits.
Arguments pind8_unfold : clear implicits.

(*TODO*)
Global Instance pind8_inst (lf : rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> _) r x0 x1 x2 x3 x4 x5 x6 x7 : pind_class (pind8 lf r x0 x1 x2 x3 x4 x5 x6 x7) :=
{ pacoacc    := pind8_acc lf;
  pacomult   := pind8_mult lf;
  pacofold   := pind8_fold lf;
  pacounfold := pind8_unfold lf }.

End PIND8.

Global Opaque pind8.

#[export] Hint Unfold upind8 : core.
#[export] Hint Resolve pind8_fold : core.
#[export] Hint Unfold monotone8 : core.
