Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paco.
From Paco Require Import paconotation_internal paco_internal pacotac_internal.
From Paco Require Export paconotation.
From Fairness Require Import pind_internal.
Set Implicit Arguments.

Section PIND6.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.

(** ** Predicates of Arity 6
*)

Definition pind6(gf : rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5)(r: rel6 T0 T1 T2 T3 T4 T5) : rel6 T0 T1 T2 T3 T4 T5 :=
  @curry6 T0 T1 T2 T3 T4 T5 (pind (fun R0 => @uncurry6 T0 T1 T2 T3 T4 T5 (gf (@curry6 T0 T1 T2 T3 T4 T5 R0))) (@uncurry6 T0 T1 T2 T3 T4 T5 r)).

Definition upind6(gf : rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5)(r: rel6 T0 T1 T2 T3 T4 T5) := pind6 gf r /6\ r.
Arguments pind6 : clear implicits.
Arguments upind6 : clear implicits.
#[local] Hint Unfold upind6 : core.

Lemma monotone6_inter (gf gf': rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5)
      (MON1: monotone6 gf)
      (MON2: monotone6 gf'):
  monotone6 (gf /7\ gf').
Proof.
  red; intros. destruct IN. split; eauto.
Qed.

Lemma _pind6_mon_gen (gf gf': rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5) r r'
    (LEgf: gf <7= gf')
    (LEr: r <6= r'):
  pind6 gf r <6== pind6 gf' r'.
Proof.
  apply curry_map6. red; intros. eapply pind_mon_gen. apply PR.
  - intros. apply LEgf, PR0.
  - intros. apply LEr, PR0.
Qed.

Lemma pind6_mon_gen (gf gf': rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5) r r' x0 x1 x2 x3 x4 x5
    (REL: pind6 gf r x0 x1 x2 x3 x4 x5)
    (LEgf: gf <7= gf')
    (LEr: r <6= r'):
  pind6 gf' r' x0 x1 x2 x3 x4 x5.
Proof.
  eapply _pind6_mon_gen; [apply LEgf | apply LEr | apply REL].
Qed.

Lemma pind6_mon_bot (gf gf': rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5) r' x0 x1 x2 x3 x4 x5
    (REL: pind6 gf bot6 x0 x1 x2 x3 x4 x5)
    (LEgf: gf <7= gf'):
  pind6 gf' r' x0 x1 x2 x3 x4 x5.
Proof.
  eapply pind6_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Definition top6 { T0 T1 T2 T3 T4 T5} (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) (x4: T4 x0 x1 x2 x3) (x5: T5 x0 x1 x2 x3 x4) := True.

Lemma pind6_mon_top (gf gf': rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5) r x0 x1 x2 x3 x4 x5
    (REL: pind6 gf r x0 x1 x2 x3 x4 x5)
    (LEgf: gf <7= gf'):
  pind6 gf' top6 x0 x1 x2 x3 x4 x5.
Proof.
  eapply pind6_mon_gen; eauto. red. auto.
Qed.

Lemma upind6_mon_gen (gf gf': rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5) r r' x0 x1 x2 x3 x4 x5
    (REL: upind6 gf r x0 x1 x2 x3 x4 x5)
    (LEgf: gf <7= gf')
    (LEr: r <6= r'):
  upind6 gf' r' x0 x1 x2 x3 x4 x5.
Proof.
  destruct REL. split; eauto.
  eapply pind6_mon_gen; [apply H | apply LEgf | apply LEr].
Qed.

Lemma upind6_mon_bot (gf gf': rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5) r' x0 x1 x2 x3 x4 x5
    (REL: upind6 gf bot6 x0 x1 x2 x3 x4 x5)
    (LEgf: gf <7= gf'):
  upind6 gf' r' x0 x1 x2 x3 x4 x5.
Proof.
  eapply upind6_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Lemma upind6mon_top (gf gf': rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5) r x0 x1 x2 x3 x4 x5
    (REL: upind6 gf r x0 x1 x2 x3 x4 x5)
    (LEgf: gf <7= gf'):
  upind6 gf' top6 x0 x1 x2 x3 x4 x5.
Proof.
  eapply upind6_mon_gen; eauto. red. auto.
Qed.

Section Arg6.

Variable gf : rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5.
Arguments gf : clear implicits.

Theorem _pind6_mon: _monotone6 (pind6 gf).
Proof.
  red; intros. eapply curry_map6, _pind_mon; apply uncurry_map6; assumption.
Qed.

Theorem _pind6_acc: forall
  l r (OBG: forall rr (DEC: rr <6== r) (IH: rr <6== l), pind6 gf rr <6== l),
  pind6 gf r <6== l.
Proof.
  intros. apply curry_adjoint2_6.
  eapply _pind_acc. intros.
  apply curry_adjoint2_6 in DEC. apply curry_adjoint2_6 in IH.
  apply curry_adjoint1_6.
  eapply le6_trans. 2: eapply (OBG _ DEC IH).
  apply curry_map6.
  apply _pind_mon; try apply le1_refl; apply curry_bij2_6.
Qed.

Theorem _pind6_mult_strong: forall r,
  pind6 gf r <6== pind6 gf (upind6 gf r).
Proof.
  intros. apply curry_map6.
  eapply le1_trans; [eapply _pind_mult_strong |].
  apply _pind_mon; intros [] H. apply H.
Qed.

Theorem _pind6_fold: forall r,
  gf (upind6 gf r) <6== pind6 gf r.
Proof.
  intros. apply uncurry_adjoint1_6.
  eapply le1_trans; [| apply _pind_fold]. apply le1_refl.
Qed.

Theorem _pind6_unfold: forall (MON: _monotone6 gf) r,
  pind6 gf r <6== gf (upind6 gf r).
Proof.
  intros. apply curry_adjoint2_6.
  eapply _pind_unfold; apply monotone6_map; assumption.
Qed.

Theorem pind6_acc: forall
  l r (OBG: forall rr (DEC: rr <6= r) (IH: rr <6= l), pind6 gf rr <6= l),
  pind6 gf r <6= l.
Proof.
  apply _pind6_acc.
Qed.

Theorem pind6_mon: monotone6 (pind6 gf).
Proof.
  apply monotone6_eq.
  apply _pind6_mon.
Qed.

Theorem upind6_mon: monotone6 (upind6 gf).
Proof.
  red; intros.
  destruct IN. split; eauto.
  eapply pind6_mon. apply H. apply LE.
Qed.

Theorem pind6_mult_strong: forall r,
  pind6 gf r <6= pind6 gf (upind6 gf r).
Proof.
  apply _pind6_mult_strong.
Qed.

Corollary pind6_mult: forall r,
  pind6 gf r <6= pind6 gf (pind6 gf r).
Proof. intros; eapply pind6_mult_strong in PR. eapply pind6_mon; eauto. intros. destruct PR0. eauto. Qed.

Theorem pind6_fold: forall r,
  gf (upind6 gf r) <6= pind6 gf r.
Proof.
  apply _pind6_fold.
Qed.

Theorem pind6_unfold: forall (MON: monotone6 gf) r,
  pind6 gf r <6= gf (upind6 gf r).
Proof.
  intro. eapply _pind6_unfold; apply monotone6_eq; assumption.
Qed.

End Arg6.

Arguments pind6_acc : clear implicits.
Arguments pind6_mon : clear implicits.
Arguments upind6_mon : clear implicits.
Arguments pind6_mult_strong : clear implicits.
Arguments pind6_mult : clear implicits.
Arguments pind6_fold : clear implicits.
Arguments pind6_unfold : clear implicits.

End PIND6.

Global Opaque pind6.

#[export] Hint Unfold upind6 : core.
#[export] Hint Resolve pind6_fold : core.
#[export] Hint Unfold monotone6 : core.

