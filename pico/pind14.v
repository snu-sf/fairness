Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paco.
From Paco Require Import paconotation_internal paco_internal pacotac_internal.
From Paco Require Export paconotation.
From Fairness Require Import pind_internal.
Set Implicit Arguments.

Section PIND14.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.
Variable T8 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6), Type.
Variable T9 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7), Type.
Variable T10 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8), Type.
Variable T11 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9), Type.
Variable T12 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10), Type.
Variable T13 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: @T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11), Type.

(** ** Predicates of Arity 14
*)

Definition pind14(gf : rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13)(r: rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) : rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 :=
  @curry14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 (pind (fun R0 => @uncurry14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 (gf (@curry14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 R0))) (@uncurry14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 r)).

Definition upind14(gf : rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13)(r: rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) := pind14 gf r /14\ r.
Arguments pind14 : clear implicits.
Arguments upind14 : clear implicits.
#[local] Hint Unfold upind14 : core.

Lemma monotone14_inter (gf gf': rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13)
      (MON1: monotone14 gf)
      (MON2: monotone14 gf'):
  monotone14 (gf /15\ gf').
Proof.
  red; intros. destruct IN. split; eauto.
Qed.

Lemma _pind14_mon_gen (gf gf': rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) r r'
    (LEgf: gf <15= gf')
    (LEr: r <14= r'):
  pind14 gf r <14== pind14 gf' r'.
Proof.
  apply curry_map14. red; intros. eapply pind_mon_gen. apply PR.
  - intros. apply LEgf, PR0.
  - intros. apply LEr, PR0.
Qed.

Lemma pind14_mon_gen (gf gf': rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) r r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
    (REL: pind14 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
    (LEgf: gf <15= gf')
    (LEr: r <14= r'):
  pind14 gf' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13.
Proof.
  eapply _pind14_mon_gen; [apply LEgf | apply LEr | apply REL].
Qed.

Lemma pind14_mon_bot (gf gf': rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
    (REL: pind14 gf bot14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
    (LEgf: gf <15= gf'):
  pind14 gf' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13.
Proof.
  eapply pind14_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Definition top14 { T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13} (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) (x4: T4 x0 x1 x2 x3) (x5: T5 x0 x1 x2 x3 x4) (x6: T6 x0 x1 x2 x3 x4 x5) (x7: T7 x0 x1 x2 x3 x4 x5 x6) (x8: T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) (x13: T13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) := True.

Lemma pind14_mon_top (gf gf': rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
    (REL: pind14 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
    (LEgf: gf <15= gf'):
  pind14 gf' top14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13.
Proof.
  eapply pind14_mon_gen; eauto. red. auto.
Qed.

Lemma upind14_mon_gen (gf gf': rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) r r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
    (REL: upind14 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
    (LEgf: gf <15= gf')
    (LEr: r <14= r'):
  upind14 gf' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13.
Proof.
  destruct REL. split; eauto.
  eapply pind14_mon_gen; [apply H | apply LEgf | apply LEr].
Qed.

Lemma upind14_mon_bot (gf gf': rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
    (REL: upind14 gf bot14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
    (LEgf: gf <15= gf'):
  upind14 gf' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13.
Proof.
  eapply upind14_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Lemma upind14mon_top (gf gf': rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
    (REL: upind14 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
    (LEgf: gf <15= gf'):
  upind14 gf' top14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13.
Proof.
  eapply upind14_mon_gen; eauto. red. auto.
Qed.

Section Arg14.

Variable gf : rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13.
Arguments gf : clear implicits.

Theorem _pind14_mon: _monotone14 (pind14 gf).
Proof.
  red; intros. eapply curry_map14, _pind_mon; apply uncurry_map14; assumption.
Qed.

Theorem _pind14_acc: forall
  l r (OBG: forall rr (DEC: rr <14== r) (IH: rr <14== l), pind14 gf rr <14== l),
  pind14 gf r <14== l.
Proof.
  intros. apply curry_adjoint2_14.
  eapply _pind_acc. intros.
  apply curry_adjoint2_14 in DEC. apply curry_adjoint2_14 in IH.
  apply curry_adjoint1_14.
  eapply le14_trans. 2: eapply (OBG _ DEC IH).
  apply curry_map14.
  apply _pind_mon; try apply le1_refl; apply curry_bij2_14.
Qed.

Theorem _pind14_mult_strong: forall r,
  pind14 gf r <14== pind14 gf (upind14 gf r).
Proof.
  intros. apply curry_map14.
  eapply le1_trans; [eapply _pind_mult_strong |].
  apply _pind_mon; intros [] H. apply H.
Qed.

Theorem _pind14_fold: forall r,
  gf (upind14 gf r) <14== pind14 gf r.
Proof.
  intros. apply uncurry_adjoint1_14.
  eapply le1_trans; [| apply _pind_fold]. apply le1_refl.
Qed.

Theorem _pind14_unfold: forall (MON: _monotone14 gf) r,
  pind14 gf r <14== gf (upind14 gf r).
Proof.
  intros. apply curry_adjoint2_14.
  eapply _pind_unfold; apply monotone14_map; assumption.
Qed.

Theorem pind14_acc: forall
  l r (OBG: forall rr (DEC: rr <14= r) (IH: rr <14= l), pind14 gf rr <14= l),
  pind14 gf r <14= l.
Proof.
  apply _pind14_acc.
Qed.

Theorem pind14_mon: monotone14 (pind14 gf).
Proof.
  apply monotone14_eq.
  apply _pind14_mon.
Qed.

Theorem upind14_mon: monotone14 (upind14 gf).
Proof.
  red; intros.
  destruct IN. split; eauto.
  eapply pind14_mon. apply H. apply LE.
Qed.

Theorem pind14_mult_strong: forall r,
  pind14 gf r <14= pind14 gf (upind14 gf r).
Proof.
  apply _pind14_mult_strong.
Qed.

Corollary pind14_mult: forall r,
  pind14 gf r <14= pind14 gf (pind14 gf r).
Proof. intros; eapply pind14_mult_strong in PR. eapply pind14_mon; eauto. intros. destruct PR0. eauto. Qed.

Theorem pind14_fold: forall r,
  gf (upind14 gf r) <14= pind14 gf r.
Proof.
  apply _pind14_fold.
Qed.

Theorem pind14_unfold: forall (MON: monotone14 gf) r,
  pind14 gf r <14= gf (upind14 gf r).
Proof.
  intro. eapply _pind14_unfold; apply monotone14_eq; assumption.
Qed.

End Arg14.

Arguments pind14_acc : clear implicits.
Arguments pind14_mon : clear implicits.
Arguments upind14_mon : clear implicits.
Arguments pind14_mult_strong : clear implicits.
Arguments pind14_mult : clear implicits.
Arguments pind14_fold : clear implicits.
Arguments pind14_unfold : clear implicits.

End PIND14.

Global Opaque pind14.

#[export] Hint Unfold upind14 : core.
#[export] Hint Resolve pind14_fold : core.
#[export] Hint Unfold monotone14 : core.

