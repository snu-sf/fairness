Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paco.
From Paco Require Import paconotation_internal paco_internal pacotac_internal.
From Paco Require Export paconotation.
From Fairness Require Import pind_internal.
Set Implicit Arguments.

Section PIND12.

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

(** ** Predicates of Arity 12
*)

Definition pind12(gf : rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11)(r: rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) : rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 :=
  @curry12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 (pind (fun R0 => @uncurry12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 (gf (@curry12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 R0))) (@uncurry12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 r)).

Definition upind12(gf : rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11)(r: rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) := pind12 gf r /12\ r.
Arguments pind12 : clear implicits.
Arguments upind12 : clear implicits.
#[local] Hint Unfold upind12 : core.

Lemma monotone12_inter (gf gf': rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11)
      (MON1: monotone12 gf)
      (MON2: monotone12 gf'):
  monotone12 (gf /13\ gf').
Proof.
  red; intros. destruct IN. split; eauto.
Qed.

Lemma _pind12_mon_gen (gf gf': rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) r r'
    (LEgf: gf <13= gf')
    (LEr: r <12= r'):
  pind12 gf r <12== pind12 gf' r'.
Proof.
  apply curry_map12. red; intros. eapply pind_mon_gen. apply PR.
  - intros. apply LEgf, PR0.
  - intros. apply LEr, PR0.
Qed.

Lemma pind12_mon_gen (gf gf': rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) r r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11
    (REL: pind12 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
    (LEgf: gf <13= gf')
    (LEr: r <12= r'):
  pind12 gf' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11.
Proof.
  eapply _pind12_mon_gen; [apply LEgf | apply LEr | apply REL].
Qed.

Lemma pind12_mon_bot (gf gf': rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11
    (REL: pind12 gf bot12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
    (LEgf: gf <13= gf'):
  pind12 gf' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11.
Proof.
  eapply pind12_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Definition top12 { T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11} (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) (x4: T4 x0 x1 x2 x3) (x5: T5 x0 x1 x2 x3 x4) (x6: T6 x0 x1 x2 x3 x4 x5) (x7: T7 x0 x1 x2 x3 x4 x5 x6) (x8: T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) := True.

Lemma pind12_mon_top (gf gf': rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11
    (REL: pind12 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
    (LEgf: gf <13= gf'):
  pind12 gf' top12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11.
Proof.
  eapply pind12_mon_gen; eauto. red. auto.
Qed.

Lemma upind12_mon_gen (gf gf': rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) r r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11
    (REL: upind12 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
    (LEgf: gf <13= gf')
    (LEr: r <12= r'):
  upind12 gf' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11.
Proof.
  destruct REL. split; eauto.
  eapply pind12_mon_gen; [apply H | apply LEgf | apply LEr].
Qed.

Lemma upind12_mon_bot (gf gf': rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11
    (REL: upind12 gf bot12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
    (LEgf: gf <13= gf'):
  upind12 gf' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11.
Proof.
  eapply upind12_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Lemma upind12mon_top (gf gf': rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11
    (REL: upind12 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
    (LEgf: gf <13= gf'):
  upind12 gf' top12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11.
Proof.
  eapply upind12_mon_gen; eauto. red. auto.
Qed.

Section Arg12.

Variable gf : rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11.
Arguments gf : clear implicits.

Theorem _pind12_mon: _monotone12 (pind12 gf).
Proof.
  red; intros. eapply curry_map12, _pind_mon; apply uncurry_map12; assumption.
Qed.

Theorem _pind12_acc: forall
  l r (OBG: forall rr (DEC: rr <12== r) (IH: rr <12== l), pind12 gf rr <12== l),
  pind12 gf r <12== l.
Proof.
  intros. apply curry_adjoint2_12.
  eapply _pind_acc. intros.
  apply curry_adjoint2_12 in DEC. apply curry_adjoint2_12 in IH.
  apply curry_adjoint1_12.
  eapply le12_trans. 2: eapply (OBG _ DEC IH).
  apply curry_map12.
  apply _pind_mon; try apply le1_refl; apply curry_bij2_12.
Qed.

Theorem _pind12_mult_strong: forall r,
  pind12 gf r <12== pind12 gf (upind12 gf r).
Proof.
  intros. apply curry_map12.
  eapply le1_trans; [eapply _pind_mult_strong |].
  apply _pind_mon; intros [] H. apply H.
Qed.

Theorem _pind12_fold: forall r,
  gf (upind12 gf r) <12== pind12 gf r.
Proof.
  intros. apply uncurry_adjoint1_12.
  eapply le1_trans; [| apply _pind_fold]. apply le1_refl.
Qed.

Theorem _pind12_unfold: forall (MON: _monotone12 gf) r,
  pind12 gf r <12== gf (upind12 gf r).
Proof.
  intros. apply curry_adjoint2_12.
  eapply _pind_unfold; apply monotone12_map; assumption.
Qed.

Theorem pind12_acc: forall
  l r (OBG: forall rr (DEC: rr <12= r) (IH: rr <12= l), pind12 gf rr <12= l),
  pind12 gf r <12= l.
Proof.
  apply _pind12_acc.
Qed.

Theorem pind12_mon: monotone12 (pind12 gf).
Proof.
  apply monotone12_eq.
  apply _pind12_mon.
Qed.

Theorem upind12_mon: monotone12 (upind12 gf).
Proof.
  red; intros.
  destruct IN. split; eauto.
  eapply pind12_mon. apply H. apply LE.
Qed.

Theorem pind12_mult_strong: forall r,
  pind12 gf r <12= pind12 gf (upind12 gf r).
Proof.
  apply _pind12_mult_strong.
Qed.

Corollary pind12_mult: forall r,
  pind12 gf r <12= pind12 gf (pind12 gf r).
Proof. intros; eapply pind12_mult_strong in PR. eapply pind12_mon; eauto. intros. destruct PR0. eauto. Qed.

Theorem pind12_fold: forall r,
  gf (upind12 gf r) <12= pind12 gf r.
Proof.
  apply _pind12_fold.
Qed.

Theorem pind12_unfold: forall (MON: monotone12 gf) r,
  pind12 gf r <12= gf (upind12 gf r).
Proof.
  intro. eapply _pind12_unfold; apply monotone12_eq; assumption.
Qed.

End Arg12.

Arguments pind12_acc : clear implicits.
Arguments pind12_mon : clear implicits.
Arguments upind12_mon : clear implicits.
Arguments pind12_mult_strong : clear implicits.
Arguments pind12_mult : clear implicits.
Arguments pind12_fold : clear implicits.
Arguments pind12_unfold : clear implicits.

End PIND12.

Global Opaque pind12.

#[export] Hint Unfold upind12 : core.
#[export] Hint Resolve pind12_fold : core.
#[export] Hint Unfold monotone12 : core.

