Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paco.
From Paco Require Import paconotation_internal paco_internal pacotac_internal.
From Paco Require Export paconotation.
From Fairness Require Import pind_internal.
Set Implicit Arguments.

Section PIND13.

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

(** ** Predicates of Arity 13
*)

Definition pind13(gf : rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12)(r: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) : rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 :=
  @curry13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 (pind (fun R0 => @uncurry13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 (gf (@curry13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 R0))) (@uncurry13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 r)).

Definition upind13(gf : rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12)(r: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) := pind13 gf r /13\ r.
Arguments pind13 : clear implicits.
Arguments upind13 : clear implicits.
#[local] Hint Unfold upind13 : core.

Lemma monotone13_inter (gf gf': rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12)
      (MON1: monotone13 gf)
      (MON2: monotone13 gf'):
  monotone13 (gf /14\ gf').
Proof.
  red; intros. destruct IN. split; eauto.
Qed.

Lemma _pind13_mon_gen (gf gf': rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) r r'
    (LEgf: gf <14= gf')
    (LEr: r <13= r'):
  pind13 gf r <13== pind13 gf' r'.
Proof.
  apply curry_map13. red; intros. eapply pind_mon_gen. apply PR.
  - intros. apply LEgf, PR0.
  - intros. apply LEr, PR0.
Qed.

Lemma pind13_mon_gen (gf gf': rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) r r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
    (REL: pind13 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
    (LEgf: gf <14= gf')
    (LEr: r <13= r'):
  pind13 gf' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12.
Proof.
  eapply _pind13_mon_gen; [apply LEgf | apply LEr | apply REL].
Qed.

Lemma pind13_mon_bot (gf gf': rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
    (REL: pind13 gf bot13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
    (LEgf: gf <14= gf'):
  pind13 gf' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12.
Proof.
  eapply pind13_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Definition top13 { T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12} (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) (x4: T4 x0 x1 x2 x3) (x5: T5 x0 x1 x2 x3 x4) (x6: T6 x0 x1 x2 x3 x4 x5) (x7: T7 x0 x1 x2 x3 x4 x5 x6) (x8: T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) := True.

Lemma pind13_mon_top (gf gf': rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
    (REL: pind13 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
    (LEgf: gf <14= gf'):
  pind13 gf' top13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12.
Proof.
  eapply pind13_mon_gen; eauto. red. auto.
Qed.

Lemma upind13_mon_gen (gf gf': rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) r r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
    (REL: upind13 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
    (LEgf: gf <14= gf')
    (LEr: r <13= r'):
  upind13 gf' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12.
Proof.
  destruct REL. split; eauto.
  eapply pind13_mon_gen; [apply H | apply LEgf | apply LEr].
Qed.

Lemma upind13_mon_bot (gf gf': rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
    (REL: upind13 gf bot13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
    (LEgf: gf <14= gf'):
  upind13 gf' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12.
Proof.
  eapply upind13_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Lemma upind13mon_top (gf gf': rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
    (REL: upind13 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
    (LEgf: gf <14= gf'):
  upind13 gf' top13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12.
Proof.
  eapply upind13_mon_gen; eauto. red. auto.
Qed.

Section Arg13.

Variable gf : rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12.
Arguments gf : clear implicits.

Theorem _pind13_mon: _monotone13 (pind13 gf).
Proof.
  red; intros. eapply curry_map13, _pind_mon; apply uncurry_map13; assumption.
Qed.

Theorem _pind13_acc: forall
  l r (OBG: forall rr (DEC: rr <13== r) (IH: rr <13== l), pind13 gf rr <13== l),
  pind13 gf r <13== l.
Proof.
  intros. apply curry_adjoint2_13.
  eapply _pind_acc. intros.
  apply curry_adjoint2_13 in DEC. apply curry_adjoint2_13 in IH.
  apply curry_adjoint1_13.
  eapply le13_trans. 2: eapply (OBG _ DEC IH).
  apply curry_map13.
  apply _pind_mon; try apply le1_refl; apply curry_bij2_13.
Qed.

Theorem _pind13_mult_strong: forall r,
  pind13 gf r <13== pind13 gf (upind13 gf r).
Proof.
  intros. apply curry_map13.
  eapply le1_trans; [eapply _pind_mult_strong |].
  apply _pind_mon; intros [] H. apply H.
Qed.

Theorem _pind13_fold: forall r,
  gf (upind13 gf r) <13== pind13 gf r.
Proof.
  intros. apply uncurry_adjoint1_13.
  eapply le1_trans; [| apply _pind_fold]. apply le1_refl.
Qed.

Theorem _pind13_unfold: forall (MON: _monotone13 gf) r,
  pind13 gf r <13== gf (upind13 gf r).
Proof.
  intros. apply curry_adjoint2_13.
  eapply _pind_unfold; apply monotone13_map; assumption.
Qed.

Theorem pind13_acc: forall
  l r (OBG: forall rr (DEC: rr <13= r) (IH: rr <13= l), pind13 gf rr <13= l),
  pind13 gf r <13= l.
Proof.
  apply _pind13_acc.
Qed.

Theorem pind13_mon: monotone13 (pind13 gf).
Proof.
  apply monotone13_eq.
  apply _pind13_mon.
Qed.

Theorem upind13_mon: monotone13 (upind13 gf).
Proof.
  red; intros.
  destruct IN. split; eauto.
  eapply pind13_mon. apply H. apply LE.
Qed.

Theorem pind13_mult_strong: forall r,
  pind13 gf r <13= pind13 gf (upind13 gf r).
Proof.
  apply _pind13_mult_strong.
Qed.

Corollary pind13_mult: forall r,
  pind13 gf r <13= pind13 gf (pind13 gf r).
Proof. intros; eapply pind13_mult_strong in PR. eapply pind13_mon; eauto. intros. destruct PR0. eauto. Qed.

Theorem pind13_fold: forall r,
  gf (upind13 gf r) <13= pind13 gf r.
Proof.
  apply _pind13_fold.
Qed.

Theorem pind13_unfold: forall (MON: monotone13 gf) r,
  pind13 gf r <13= gf (upind13 gf r).
Proof.
  intro. eapply _pind13_unfold; apply monotone13_eq; assumption.
Qed.

End Arg13.

Arguments pind13_acc : clear implicits.
Arguments pind13_mon : clear implicits.
Arguments upind13_mon : clear implicits.
Arguments pind13_mult_strong : clear implicits.
Arguments pind13_mult : clear implicits.
Arguments pind13_fold : clear implicits.
Arguments pind13_unfold : clear implicits.

End PIND13.

Global Opaque pind13.

#[export] Hint Unfold upind13 : core.
#[export] Hint Resolve pind13_fold : core.
#[export] Hint Unfold monotone13 : core.

