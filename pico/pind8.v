Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paco.
From Paco Require Import paconotation_internal paco_internal pacotac_internal.
From Paco Require Export paconotation.
From Fairness Require Import pind_internal.
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

Definition pind8(gf : rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7)(r: rel8 T0 T1 T2 T3 T4 T5 T6 T7) : rel8 T0 T1 T2 T3 T4 T5 T6 T7 :=
  @curry8 T0 T1 T2 T3 T4 T5 T6 T7 (pind (fun R0 => @uncurry8 T0 T1 T2 T3 T4 T5 T6 T7 (gf (@curry8 T0 T1 T2 T3 T4 T5 T6 T7 R0))) (@uncurry8 T0 T1 T2 T3 T4 T5 T6 T7 r)).

Definition upind8(gf : rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7)(r: rel8 T0 T1 T2 T3 T4 T5 T6 T7) := pind8 gf r /8\ r.
Arguments pind8 : clear implicits.
Arguments upind8 : clear implicits.
#[local] Hint Unfold upind8 : core.

Lemma monotone8_inter (gf gf': rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7)
      (MON1: monotone8 gf)
      (MON2: monotone8 gf'):
  monotone8 (gf /9\ gf').
Proof.
  red; intros. destruct IN. split; eauto.
Qed.

Lemma _pind8_mon_gen (gf gf': rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7) r r'
    (LEgf: gf <9= gf')
    (LEr: r <8= r'):
  pind8 gf r <8== pind8 gf' r'.
Proof.
  apply curry_map8. red; intros. eapply pind_mon_gen. apply PR.
  - intros. apply LEgf, PR0.
  - intros. apply LEr, PR0.
Qed.

Lemma pind8_mon_gen (gf gf': rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7) r r' x0 x1 x2 x3 x4 x5 x6 x7
    (REL: pind8 gf r x0 x1 x2 x3 x4 x5 x6 x7)
    (LEgf: gf <9= gf')
    (LEr: r <8= r'):
  pind8 gf' r' x0 x1 x2 x3 x4 x5 x6 x7.
Proof.
  eapply _pind8_mon_gen; [apply LEgf | apply LEr | apply REL].
Qed.

Lemma pind8_mon_bot (gf gf': rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7) r' x0 x1 x2 x3 x4 x5 x6 x7
    (REL: pind8 gf bot8 x0 x1 x2 x3 x4 x5 x6 x7)
    (LEgf: gf <9= gf'):
  pind8 gf' r' x0 x1 x2 x3 x4 x5 x6 x7.
Proof.
  eapply pind8_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Definition top8 { T0 T1 T2 T3 T4 T5 T6 T7} (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) (x4: T4 x0 x1 x2 x3) (x5: T5 x0 x1 x2 x3 x4) (x6: T6 x0 x1 x2 x3 x4 x5) (x7: T7 x0 x1 x2 x3 x4 x5 x6) := True.

Lemma pind8_mon_top (gf gf': rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7) r x0 x1 x2 x3 x4 x5 x6 x7
    (REL: pind8 gf r x0 x1 x2 x3 x4 x5 x6 x7)
    (LEgf: gf <9= gf'):
  pind8 gf' top8 x0 x1 x2 x3 x4 x5 x6 x7.
Proof.
  eapply pind8_mon_gen; eauto. red. auto.
Qed.

Lemma upind8_mon_gen (gf gf': rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7) r r' x0 x1 x2 x3 x4 x5 x6 x7
    (REL: upind8 gf r x0 x1 x2 x3 x4 x5 x6 x7)
    (LEgf: gf <9= gf')
    (LEr: r <8= r'):
  upind8 gf' r' x0 x1 x2 x3 x4 x5 x6 x7.
Proof.
  destruct REL. split; eauto.
  eapply pind8_mon_gen; [apply H | apply LEgf | apply LEr].
Qed.

Lemma upind8_mon_bot (gf gf': rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7) r' x0 x1 x2 x3 x4 x5 x6 x7
    (REL: upind8 gf bot8 x0 x1 x2 x3 x4 x5 x6 x7)
    (LEgf: gf <9= gf'):
  upind8 gf' r' x0 x1 x2 x3 x4 x5 x6 x7.
Proof.
  eapply upind8_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Lemma upind8mon_top (gf gf': rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7) r x0 x1 x2 x3 x4 x5 x6 x7
    (REL: upind8 gf r x0 x1 x2 x3 x4 x5 x6 x7)
    (LEgf: gf <9= gf'):
  upind8 gf' top8 x0 x1 x2 x3 x4 x5 x6 x7.
Proof.
  eapply upind8_mon_gen; eauto. red. auto.
Qed.

Section Arg8.

Variable gf : rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7.
Arguments gf : clear implicits.

Theorem _pind8_mon: _monotone8 (pind8 gf).
Proof.
  red; intros. eapply curry_map8, _pind_mon; apply uncurry_map8; assumption.
Qed.

Theorem _pind8_acc: forall
  l r (OBG: forall rr (DEC: rr <8== r) (IH: rr <8== l), pind8 gf rr <8== l),
  pind8 gf r <8== l.
Proof.
  intros. apply curry_adjoint2_8.
  eapply _pind_acc. intros.
  apply curry_adjoint2_8 in DEC. apply curry_adjoint2_8 in IH.
  apply curry_adjoint1_8.
  eapply le8_trans. 2: eapply (OBG _ DEC IH).
  apply curry_map8.
  apply _pind_mon; try apply le1_refl; apply curry_bij2_8.
Qed.

Theorem _pind8_mult_strong: forall r,
  pind8 gf r <8== pind8 gf (upind8 gf r).
Proof.
  intros. apply curry_map8.
  eapply le1_trans; [eapply _pind_mult_strong |].
  apply _pind_mon; intros [] H. apply H.
Qed.

Theorem _pind8_fold: forall r,
  gf (upind8 gf r) <8== pind8 gf r.
Proof.
  intros. apply uncurry_adjoint1_8.
  eapply le1_trans; [| apply _pind_fold]. apply le1_refl.
Qed.

Theorem _pind8_unfold: forall (MON: _monotone8 gf) r,
  pind8 gf r <8== gf (upind8 gf r).
Proof.
  intros. apply curry_adjoint2_8.
  eapply _pind_unfold; apply monotone8_map; assumption.
Qed.

Theorem pind8_acc: forall
  l r (OBG: forall rr (DEC: rr <8= r) (IH: rr <8= l), pind8 gf rr <8= l),
  pind8 gf r <8= l.
Proof.
  apply _pind8_acc.
Qed.

Theorem pind8_mon: monotone8 (pind8 gf).
Proof.
  apply monotone8_eq.
  apply _pind8_mon.
Qed.

Theorem upind8_mon: monotone8 (upind8 gf).
Proof.
  red; intros.
  destruct IN. split; eauto.
  eapply pind8_mon. apply H. apply LE.
Qed.

Theorem pind8_mult_strong: forall r,
  pind8 gf r <8= pind8 gf (upind8 gf r).
Proof.
  apply _pind8_mult_strong.
Qed.

Corollary pind8_mult: forall r,
  pind8 gf r <8= pind8 gf (pind8 gf r).
Proof. intros; eapply pind8_mult_strong in PR. eapply pind8_mon; eauto. intros. destruct PR0. eauto. Qed.

Theorem pind8_fold: forall r,
  gf (upind8 gf r) <8= pind8 gf r.
Proof.
  apply _pind8_fold.
Qed.

Theorem pind8_unfold: forall (MON: monotone8 gf) r,
  pind8 gf r <8= gf (upind8 gf r).
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

End PIND8.

Global Opaque pind8.

#[export] Hint Unfold upind8 : core.
#[export] Hint Resolve pind8_fold : core.
#[export] Hint Unfold monotone8 : core.

