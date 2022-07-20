Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paco.
From Paco Require Import paconotation_internal paco_internal pacotac_internal.
From Paco Require Export paconotation.
From Fairness Require Import pind_internal.
Set Implicit Arguments.

Section PIND11.

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

(** ** Predicates of Arity 11
*)

Definition pind11(gf : rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10)(r: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) : rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 :=
  @curry11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 (pind (fun R0 => @uncurry11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 (gf (@curry11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 R0))) (@uncurry11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 r)).

Definition upind11(gf : rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10)(r: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) := pind11 gf r /11\ r.
Arguments pind11 : clear implicits.
Arguments upind11 : clear implicits.
#[local] Hint Unfold upind11 : core.

Lemma monotone11_inter (gf gf': rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10)
      (MON1: monotone11 gf)
      (MON2: monotone11 gf'):
  monotone11 (gf /12\ gf').
Proof.
  red; intros. destruct IN. split; eauto.
Qed.

Lemma _pind11_mon_gen (gf gf': rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) r r'
    (LEgf: gf <12= gf')
    (LEr: r <11= r'):
  pind11 gf r <11== pind11 gf' r'.
Proof.
  apply curry_map11. red; intros. eapply pind_mon_gen. apply PR.
  - intros. apply LEgf, PR0.
  - intros. apply LEr, PR0.
Qed.

Lemma pind11_mon_gen (gf gf': rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) r r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
    (REL: pind11 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
    (LEgf: gf <12= gf')
    (LEr: r <11= r'):
  pind11 gf' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10.
Proof.
  eapply _pind11_mon_gen; [apply LEgf | apply LEr | apply REL].
Qed.

Lemma pind11_mon_bot (gf gf': rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
    (REL: pind11 gf bot11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
    (LEgf: gf <12= gf'):
  pind11 gf' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10.
Proof.
  eapply pind11_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Definition top11 { T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10} (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) (x4: T4 x0 x1 x2 x3) (x5: T5 x0 x1 x2 x3 x4) (x6: T6 x0 x1 x2 x3 x4 x5) (x7: T7 x0 x1 x2 x3 x4 x5 x6) (x8: T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) := True.

Lemma pind11_mon_top (gf gf': rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
    (REL: pind11 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
    (LEgf: gf <12= gf'):
  pind11 gf' top11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10.
Proof.
  eapply pind11_mon_gen; eauto. red. auto.
Qed.

Lemma upind11_mon_gen (gf gf': rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) r r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
    (REL: upind11 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
    (LEgf: gf <12= gf')
    (LEr: r <11= r'):
  upind11 gf' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10.
Proof.
  destruct REL. split; eauto.
  eapply pind11_mon_gen; [apply H | apply LEgf | apply LEr].
Qed.

Lemma upind11_mon_bot (gf gf': rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
    (REL: upind11 gf bot11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
    (LEgf: gf <12= gf'):
  upind11 gf' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10.
Proof.
  eapply upind11_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Lemma upind11mon_top (gf gf': rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
    (REL: upind11 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
    (LEgf: gf <12= gf'):
  upind11 gf' top11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10.
Proof.
  eapply upind11_mon_gen; eauto. red. auto.
Qed.

Section Arg11.

Variable gf : rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10.
Arguments gf : clear implicits.

Theorem _pind11_mon: _monotone11 (pind11 gf).
Proof.
  red; intros. eapply curry_map11, _pind_mon; apply uncurry_map11; assumption.
Qed.

Theorem _pind11_acc: forall
  l r (OBG: forall rr (DEC: rr <11== r) (IH: rr <11== l), pind11 gf rr <11== l),
  pind11 gf r <11== l.
Proof.
  intros. apply curry_adjoint2_11.
  eapply _pind_acc. intros.
  apply curry_adjoint2_11 in DEC. apply curry_adjoint2_11 in IH.
  apply curry_adjoint1_11.
  eapply le11_trans. 2: eapply (OBG _ DEC IH).
  apply curry_map11.
  apply _pind_mon; try apply le1_refl; apply curry_bij2_11.
Qed.

Theorem _pind11_mult_strong: forall r,
  pind11 gf r <11== pind11 gf (upind11 gf r).
Proof.
  intros. apply curry_map11.
  eapply le1_trans; [eapply _pind_mult_strong |].
  apply _pind_mon; intros [] H. apply H.
Qed.

Theorem _pind11_fold: forall r,
  gf (upind11 gf r) <11== pind11 gf r.
Proof.
  intros. apply uncurry_adjoint1_11.
  eapply le1_trans; [| apply _pind_fold]. apply le1_refl.
Qed.

Theorem _pind11_unfold: forall (MON: _monotone11 gf) r,
  pind11 gf r <11== gf (upind11 gf r).
Proof.
  intros. apply curry_adjoint2_11.
  eapply _pind_unfold; apply monotone11_map; assumption.
Qed.

Theorem pind11_acc: forall
  l r (OBG: forall rr (DEC: rr <11= r) (IH: rr <11= l), pind11 gf rr <11= l),
  pind11 gf r <11= l.
Proof.
  apply _pind11_acc.
Qed.

Theorem pind11_mon: monotone11 (pind11 gf).
Proof.
  apply monotone11_eq.
  apply _pind11_mon.
Qed.

Theorem upind11_mon: monotone11 (upind11 gf).
Proof.
  red; intros.
  destruct IN. split; eauto.
  eapply pind11_mon. apply H. apply LE.
Qed.

Theorem pind11_mult_strong: forall r,
  pind11 gf r <11= pind11 gf (upind11 gf r).
Proof.
  apply _pind11_mult_strong.
Qed.

Corollary pind11_mult: forall r,
  pind11 gf r <11= pind11 gf (pind11 gf r).
Proof. intros; eapply pind11_mult_strong in PR. eapply pind11_mon; eauto. intros. destruct PR0. eauto. Qed.

Theorem pind11_fold: forall r,
  gf (upind11 gf r) <11= pind11 gf r.
Proof.
  apply _pind11_fold.
Qed.

Theorem pind11_unfold: forall (MON: monotone11 gf) r,
  pind11 gf r <11= gf (upind11 gf r).
Proof.
  intro. eapply _pind11_unfold; apply monotone11_eq; assumption.
Qed.

End Arg11.

Arguments pind11_acc : clear implicits.
Arguments pind11_mon : clear implicits.
Arguments upind11_mon : clear implicits.
Arguments pind11_mult_strong : clear implicits.
Arguments pind11_mult : clear implicits.
Arguments pind11_fold : clear implicits.
Arguments pind11_unfold : clear implicits.

End PIND11.

Global Opaque pind11.

#[export] Hint Unfold upind11 : core.
#[export] Hint Resolve pind11_fold : core.
#[export] Hint Unfold monotone11 : core.

