Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paco.
From Paco Require Import paconotation_internal paco_internal pacotac_internal.
From Paco Require Export paconotation.
From Fairness Require Import pind_internal.
Set Implicit Arguments.

Section PIND9.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.
Variable T8 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6), Type.

(** ** Predicates of Arity 9
*)

Definition pind9(gf : rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8)(r: rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) : rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 :=
  @curry9 T0 T1 T2 T3 T4 T5 T6 T7 T8 (pind (fun R0 => @uncurry9 T0 T1 T2 T3 T4 T5 T6 T7 T8 (gf (@curry9 T0 T1 T2 T3 T4 T5 T6 T7 T8 R0))) (@uncurry9 T0 T1 T2 T3 T4 T5 T6 T7 T8 r)).

Definition upind9(gf : rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8)(r: rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) := pind9 gf r /9\ r.
Arguments pind9 : clear implicits.
Arguments upind9 : clear implicits.
#[local] Hint Unfold upind9 : core.

Lemma monotone9_inter (gf gf': rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8)
      (MON1: monotone9 gf)
      (MON2: monotone9 gf'):
  monotone9 (gf /10\ gf').
Proof.
  red; intros. destruct IN. split; eauto.
Qed.

Lemma _pind9_mon_gen (gf gf': rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) r r'
    (LEgf: gf <10= gf')
    (LEr: r <9= r'):
  pind9 gf r <9== pind9 gf' r'.
Proof.
  apply curry_map9. red; intros. eapply pind_mon_gen. apply PR.
  - intros. apply LEgf, PR0.
  - intros. apply LEr, PR0.
Qed.

Lemma pind9_mon_gen (gf gf': rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) r r' x0 x1 x2 x3 x4 x5 x6 x7 x8
    (REL: pind9 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8)
    (LEgf: gf <10= gf')
    (LEr: r <9= r'):
  pind9 gf' r' x0 x1 x2 x3 x4 x5 x6 x7 x8.
Proof.
  eapply _pind9_mon_gen; [apply LEgf | apply LEr | apply REL].
Qed.

Lemma pind9_mon_bot (gf gf': rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) r' x0 x1 x2 x3 x4 x5 x6 x7 x8
    (REL: pind9 gf bot9 x0 x1 x2 x3 x4 x5 x6 x7 x8)
    (LEgf: gf <10= gf'):
  pind9 gf' r' x0 x1 x2 x3 x4 x5 x6 x7 x8.
Proof.
  eapply pind9_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Definition top9 { T0 T1 T2 T3 T4 T5 T6 T7 T8} (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) (x4: T4 x0 x1 x2 x3) (x5: T5 x0 x1 x2 x3 x4) (x6: T6 x0 x1 x2 x3 x4 x5) (x7: T7 x0 x1 x2 x3 x4 x5 x6) (x8: T8 x0 x1 x2 x3 x4 x5 x6 x7) := True.

Lemma pind9_mon_top (gf gf': rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) r x0 x1 x2 x3 x4 x5 x6 x7 x8
    (REL: pind9 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8)
    (LEgf: gf <10= gf'):
  pind9 gf' top9 x0 x1 x2 x3 x4 x5 x6 x7 x8.
Proof.
  eapply pind9_mon_gen; eauto. red. auto.
Qed.

Lemma upind9_mon_gen (gf gf': rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) r r' x0 x1 x2 x3 x4 x5 x6 x7 x8
    (REL: upind9 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8)
    (LEgf: gf <10= gf')
    (LEr: r <9= r'):
  upind9 gf' r' x0 x1 x2 x3 x4 x5 x6 x7 x8.
Proof.
  destruct REL. split; eauto.
  eapply pind9_mon_gen; [apply H | apply LEgf | apply LEr].
Qed.

Lemma upind9_mon_bot (gf gf': rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) r' x0 x1 x2 x3 x4 x5 x6 x7 x8
    (REL: upind9 gf bot9 x0 x1 x2 x3 x4 x5 x6 x7 x8)
    (LEgf: gf <10= gf'):
  upind9 gf' r' x0 x1 x2 x3 x4 x5 x6 x7 x8.
Proof.
  eapply upind9_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Lemma upind9mon_top (gf gf': rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) r x0 x1 x2 x3 x4 x5 x6 x7 x8
    (REL: upind9 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8)
    (LEgf: gf <10= gf'):
  upind9 gf' top9 x0 x1 x2 x3 x4 x5 x6 x7 x8.
Proof.
  eapply upind9_mon_gen; eauto. red. auto.
Qed.

Section Arg9.

Variable gf : rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8.
Arguments gf : clear implicits.

Theorem _pind9_mon: _monotone9 (pind9 gf).
Proof.
  red; intros. eapply curry_map9, _pind_mon; apply uncurry_map9; assumption.
Qed.

Theorem _pind9_acc: forall
  l r (OBG: forall rr (DEC: rr <9== r) (IH: rr <9== l), pind9 gf rr <9== l),
  pind9 gf r <9== l.
Proof.
  intros. apply curry_adjoint2_9.
  eapply _pind_acc. intros.
  apply curry_adjoint2_9 in DEC. apply curry_adjoint2_9 in IH.
  apply curry_adjoint1_9.
  eapply le9_trans. 2: eapply (OBG _ DEC IH).
  apply curry_map9.
  apply _pind_mon; try apply le1_refl; apply curry_bij2_9.
Qed.

Theorem _pind9_mult_strong: forall r,
  pind9 gf r <9== pind9 gf (upind9 gf r).
Proof.
  intros. apply curry_map9.
  eapply le1_trans; [eapply _pind_mult_strong |].
  apply _pind_mon; intros [] H. apply H.
Qed.

Theorem _pind9_fold: forall r,
  gf (upind9 gf r) <9== pind9 gf r.
Proof.
  intros. apply uncurry_adjoint1_9.
  eapply le1_trans; [| apply _pind_fold]. apply le1_refl.
Qed.

Theorem _pind9_unfold: forall (MON: _monotone9 gf) r,
  pind9 gf r <9== gf (upind9 gf r).
Proof.
  intros. apply curry_adjoint2_9.
  eapply _pind_unfold; apply monotone9_map; assumption.
Qed.

Theorem pind9_acc: forall
  l r (OBG: forall rr (DEC: rr <9= r) (IH: rr <9= l), pind9 gf rr <9= l),
  pind9 gf r <9= l.
Proof.
  apply _pind9_acc.
Qed.

Theorem pind9_mon: monotone9 (pind9 gf).
Proof.
  apply monotone9_eq.
  apply _pind9_mon.
Qed.

Theorem upind9_mon: monotone9 (upind9 gf).
Proof.
  red; intros.
  destruct IN. split; eauto.
  eapply pind9_mon. apply H. apply LE.
Qed.

Theorem pind9_mult_strong: forall r,
  pind9 gf r <9= pind9 gf (upind9 gf r).
Proof.
  apply _pind9_mult_strong.
Qed.

Corollary pind9_mult: forall r,
  pind9 gf r <9= pind9 gf (pind9 gf r).
Proof. intros; eapply pind9_mult_strong in PR. eapply pind9_mon; eauto. intros. destruct PR0. eauto. Qed.

Theorem pind9_fold: forall r,
  gf (upind9 gf r) <9= pind9 gf r.
Proof.
  apply _pind9_fold.
Qed.

Theorem pind9_unfold: forall (MON: monotone9 gf) r,
  pind9 gf r <9= gf (upind9 gf r).
Proof.
  intro. eapply _pind9_unfold; apply monotone9_eq; assumption.
Qed.

End Arg9.

Arguments pind9_acc : clear implicits.
Arguments pind9_mon : clear implicits.
Arguments upind9_mon : clear implicits.
Arguments pind9_mult_strong : clear implicits.
Arguments pind9_mult : clear implicits.
Arguments pind9_fold : clear implicits.
Arguments pind9_unfold : clear implicits.

End PIND9.

Global Opaque pind9.

#[export] Hint Unfold upind9 : core.
#[export] Hint Resolve pind9_fold : core.
#[export] Hint Unfold monotone9 : core.

