Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paco.
From Paco Require Import paconotation_internal paco_internal pacotac_internal.
From Paco Require Export paconotation.
From Fairness Require Import pind_internal.
Set Implicit Arguments.

Section PIND10.

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

(** ** Predicates of Arity 10
*)

Definition pind10(gf : rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9)(r: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) : rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 :=
  @curry10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 (pind (fun R0 => @uncurry10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 (gf (@curry10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 R0))) (@uncurry10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 r)).

Definition upind10(gf : rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9)(r: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) := pind10 gf r /10\ r.
Arguments pind10 : clear implicits.
Arguments upind10 : clear implicits.
#[local] Hint Unfold upind10 : core.

Lemma monotone10_inter (gf gf': rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9)
      (MON1: monotone10 gf)
      (MON2: monotone10 gf'):
  monotone10 (gf /11\ gf').
Proof.
  red; intros. destruct IN. split; eauto.
Qed.

Lemma _pind10_mon_gen (gf gf': rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) r r'
    (LEgf: gf <11= gf')
    (LEr: r <10= r'):
  pind10 gf r <10== pind10 gf' r'.
Proof.
  apply curry_map10. red; intros. eapply pind_mon_gen. apply PR.
  - intros. apply LEgf, PR0.
  - intros. apply LEr, PR0.
Qed.

Lemma pind10_mon_gen (gf gf': rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) r r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
    (REL: pind10 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
    (LEgf: gf <11= gf')
    (LEr: r <10= r'):
  pind10 gf' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9.
Proof.
  eapply _pind10_mon_gen; [apply LEgf | apply LEr | apply REL].
Qed.

Lemma pind10_mon_bot (gf gf': rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
    (REL: pind10 gf bot10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
    (LEgf: gf <11= gf'):
  pind10 gf' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9.
Proof.
  eapply pind10_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Definition top10 { T0 T1 T2 T3 T4 T5 T6 T7 T8 T9} (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) (x4: T4 x0 x1 x2 x3) (x5: T5 x0 x1 x2 x3 x4) (x6: T6 x0 x1 x2 x3 x4 x5) (x7: T7 x0 x1 x2 x3 x4 x5 x6) (x8: T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) := True.

Lemma pind10_mon_top (gf gf': rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
    (REL: pind10 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
    (LEgf: gf <11= gf'):
  pind10 gf' top10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9.
Proof.
  eapply pind10_mon_gen; eauto. red. auto.
Qed.

Lemma upind10_mon_gen (gf gf': rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) r r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
    (REL: upind10 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
    (LEgf: gf <11= gf')
    (LEr: r <10= r'):
  upind10 gf' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9.
Proof.
  destruct REL. split; eauto.
  eapply pind10_mon_gen; [apply H | apply LEgf | apply LEr].
Qed.

Lemma upind10_mon_bot (gf gf': rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
    (REL: upind10 gf bot10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
    (LEgf: gf <11= gf'):
  upind10 gf' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9.
Proof.
  eapply upind10_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Lemma upind10mon_top (gf gf': rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
    (REL: upind10 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
    (LEgf: gf <11= gf'):
  upind10 gf' top10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9.
Proof.
  eapply upind10_mon_gen; eauto. red. auto.
Qed.

Section Arg10.

Variable gf : rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9.
Arguments gf : clear implicits.

Theorem _pind10_mon: _monotone10 (pind10 gf).
Proof.
  red; intros. eapply curry_map10, _pind_mon; apply uncurry_map10; assumption.
Qed.

Theorem _pind10_acc: forall
  l r (OBG: forall rr (DEC: rr <10== r) (IH: rr <10== l), pind10 gf rr <10== l),
  pind10 gf r <10== l.
Proof.
  intros. apply curry_adjoint2_10.
  eapply _pind_acc. intros.
  apply curry_adjoint2_10 in DEC. apply curry_adjoint2_10 in IH.
  apply curry_adjoint1_10.
  eapply le10_trans. 2: eapply (OBG _ DEC IH).
  apply curry_map10.
  apply _pind_mon; try apply le1_refl; apply curry_bij2_10.
Qed.

Theorem _pind10_mult_strong: forall r,
  pind10 gf r <10== pind10 gf (upind10 gf r).
Proof.
  intros. apply curry_map10.
  eapply le1_trans; [eapply _pind_mult_strong |].
  apply _pind_mon; intros [] H. apply H.
Qed.

Theorem _pind10_fold: forall r,
  gf (upind10 gf r) <10== pind10 gf r.
Proof.
  intros. apply uncurry_adjoint1_10.
  eapply le1_trans; [| apply _pind_fold]. apply le1_refl.
Qed.

Theorem _pind10_unfold: forall (MON: _monotone10 gf) r,
  pind10 gf r <10== gf (upind10 gf r).
Proof.
  intros. apply curry_adjoint2_10.
  eapply _pind_unfold; apply monotone10_map; assumption.
Qed.

Theorem pind10_acc: forall
  l r (OBG: forall rr (DEC: rr <10= r) (IH: rr <10= l), pind10 gf rr <10= l),
  pind10 gf r <10= l.
Proof.
  apply _pind10_acc.
Qed.

Theorem pind10_mon: monotone10 (pind10 gf).
Proof.
  apply monotone10_eq.
  apply _pind10_mon.
Qed.

Theorem upind10_mon: monotone10 (upind10 gf).
Proof.
  red; intros.
  destruct IN. split; eauto.
  eapply pind10_mon. apply H. apply LE.
Qed.

Theorem pind10_mult_strong: forall r,
  pind10 gf r <10= pind10 gf (upind10 gf r).
Proof.
  apply _pind10_mult_strong.
Qed.

Corollary pind10_mult: forall r,
  pind10 gf r <10= pind10 gf (pind10 gf r).
Proof. intros; eapply pind10_mult_strong in PR. eapply pind10_mon; eauto. intros. destruct PR0. eauto. Qed.

Theorem pind10_fold: forall r,
  gf (upind10 gf r) <10= pind10 gf r.
Proof.
  apply _pind10_fold.
Qed.

Theorem pind10_unfold: forall (MON: monotone10 gf) r,
  pind10 gf r <10= gf (upind10 gf r).
Proof.
  intro. eapply _pind10_unfold; apply monotone10_eq; assumption.
Qed.

End Arg10.

Arguments pind10_acc : clear implicits.
Arguments pind10_mon : clear implicits.
Arguments upind10_mon : clear implicits.
Arguments pind10_mult_strong : clear implicits.
Arguments pind10_mult : clear implicits.
Arguments pind10_fold : clear implicits.
Arguments pind10_unfold : clear implicits.

End PIND10.

Global Opaque pind10.

#[export] Hint Unfold upind10 : core.
#[export] Hint Resolve pind10_fold : core.
#[export] Hint Unfold monotone10 : core.

