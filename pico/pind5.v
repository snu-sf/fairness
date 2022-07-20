Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paco.
From Paco Require Import paconotation_internal paco_internal pacotac_internal.
From Paco Require Export paconotation.
From Fairness Require Import pind_internal.
Set Implicit Arguments.

Section PIND5.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.

(** ** Predicates of Arity 5
*)

Definition pind5(gf : rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4)(r: rel5 T0 T1 T2 T3 T4) : rel5 T0 T1 T2 T3 T4 :=
  @curry5 T0 T1 T2 T3 T4 (pind (fun R0 => @uncurry5 T0 T1 T2 T3 T4 (gf (@curry5 T0 T1 T2 T3 T4 R0))) (@uncurry5 T0 T1 T2 T3 T4 r)).

Definition upind5(gf : rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4)(r: rel5 T0 T1 T2 T3 T4) := pind5 gf r /5\ r.
Arguments pind5 : clear implicits.
Arguments upind5 : clear implicits.
#[local] Hint Unfold upind5 : core.

Lemma monotone5_inter (gf gf': rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4)
      (MON1: monotone5 gf)
      (MON2: monotone5 gf'):
  monotone5 (gf /6\ gf').
Proof.
  red; intros. destruct IN. split; eauto.
Qed.

Lemma _pind5_mon_gen (gf gf': rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4) r r'
    (LEgf: gf <6= gf')
    (LEr: r <5= r'):
  pind5 gf r <5== pind5 gf' r'.
Proof.
  apply curry_map5. red; intros. eapply pind_mon_gen. apply PR.
  - intros. apply LEgf, PR0.
  - intros. apply LEr, PR0.
Qed.

Lemma pind5_mon_gen (gf gf': rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4) r r' x0 x1 x2 x3 x4
    (REL: pind5 gf r x0 x1 x2 x3 x4)
    (LEgf: gf <6= gf')
    (LEr: r <5= r'):
  pind5 gf' r' x0 x1 x2 x3 x4.
Proof.
  eapply _pind5_mon_gen; [apply LEgf | apply LEr | apply REL].
Qed.

Lemma pind5_mon_bot (gf gf': rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4) r' x0 x1 x2 x3 x4
    (REL: pind5 gf bot5 x0 x1 x2 x3 x4)
    (LEgf: gf <6= gf'):
  pind5 gf' r' x0 x1 x2 x3 x4.
Proof.
  eapply pind5_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Definition top5 { T0 T1 T2 T3 T4} (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) (x4: T4 x0 x1 x2 x3) := True.

Lemma pind5_mon_top (gf gf': rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4) r x0 x1 x2 x3 x4
    (REL: pind5 gf r x0 x1 x2 x3 x4)
    (LEgf: gf <6= gf'):
  pind5 gf' top5 x0 x1 x2 x3 x4.
Proof.
  eapply pind5_mon_gen; eauto. red. auto.
Qed.

Lemma upind5_mon_gen (gf gf': rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4) r r' x0 x1 x2 x3 x4
    (REL: upind5 gf r x0 x1 x2 x3 x4)
    (LEgf: gf <6= gf')
    (LEr: r <5= r'):
  upind5 gf' r' x0 x1 x2 x3 x4.
Proof.
  destruct REL. split; eauto.
  eapply pind5_mon_gen; [apply H | apply LEgf | apply LEr].
Qed.

Lemma upind5_mon_bot (gf gf': rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4) r' x0 x1 x2 x3 x4
    (REL: upind5 gf bot5 x0 x1 x2 x3 x4)
    (LEgf: gf <6= gf'):
  upind5 gf' r' x0 x1 x2 x3 x4.
Proof.
  eapply upind5_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Lemma upind5mon_top (gf gf': rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4) r x0 x1 x2 x3 x4
    (REL: upind5 gf r x0 x1 x2 x3 x4)
    (LEgf: gf <6= gf'):
  upind5 gf' top5 x0 x1 x2 x3 x4.
Proof.
  eapply upind5_mon_gen; eauto. red. auto.
Qed.

Section Arg5.

Variable gf : rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4.
Arguments gf : clear implicits.

Theorem _pind5_mon: _monotone5 (pind5 gf).
Proof.
  red; intros. eapply curry_map5, _pind_mon; apply uncurry_map5; assumption.
Qed.

Theorem _pind5_acc: forall
  l r (OBG: forall rr (DEC: rr <5== r) (IH: rr <5== l), pind5 gf rr <5== l),
  pind5 gf r <5== l.
Proof.
  intros. apply curry_adjoint2_5.
  eapply _pind_acc. intros.
  apply curry_adjoint2_5 in DEC. apply curry_adjoint2_5 in IH.
  apply curry_adjoint1_5.
  eapply le5_trans. 2: eapply (OBG _ DEC IH).
  apply curry_map5.
  apply _pind_mon; try apply le1_refl; apply curry_bij2_5.
Qed.

Theorem _pind5_mult_strong: forall r,
  pind5 gf r <5== pind5 gf (upind5 gf r).
Proof.
  intros. apply curry_map5.
  eapply le1_trans; [eapply _pind_mult_strong |].
  apply _pind_mon; intros [] H. apply H.
Qed.

Theorem _pind5_fold: forall r,
  gf (upind5 gf r) <5== pind5 gf r.
Proof.
  intros. apply uncurry_adjoint1_5.
  eapply le1_trans; [| apply _pind_fold]. apply le1_refl.
Qed.

Theorem _pind5_unfold: forall (MON: _monotone5 gf) r,
  pind5 gf r <5== gf (upind5 gf r).
Proof.
  intros. apply curry_adjoint2_5.
  eapply _pind_unfold; apply monotone5_map; assumption.
Qed.

Theorem pind5_acc: forall
  l r (OBG: forall rr (DEC: rr <5= r) (IH: rr <5= l), pind5 gf rr <5= l),
  pind5 gf r <5= l.
Proof.
  apply _pind5_acc.
Qed.

Theorem pind5_mon: monotone5 (pind5 gf).
Proof.
  apply monotone5_eq.
  apply _pind5_mon.
Qed.

Theorem upind5_mon: monotone5 (upind5 gf).
Proof.
  red; intros.
  destruct IN. split; eauto.
  eapply pind5_mon. apply H. apply LE.
Qed.

Theorem pind5_mult_strong: forall r,
  pind5 gf r <5= pind5 gf (upind5 gf r).
Proof.
  apply _pind5_mult_strong.
Qed.

Corollary pind5_mult: forall r,
  pind5 gf r <5= pind5 gf (pind5 gf r).
Proof. intros; eapply pind5_mult_strong in PR. eapply pind5_mon; eauto. intros. destruct PR0. eauto. Qed.

Theorem pind5_fold: forall r,
  gf (upind5 gf r) <5= pind5 gf r.
Proof.
  apply _pind5_fold.
Qed.

Theorem pind5_unfold: forall (MON: monotone5 gf) r,
  pind5 gf r <5= gf (upind5 gf r).
Proof.
  intro. eapply _pind5_unfold; apply monotone5_eq; assumption.
Qed.

End Arg5.

Arguments pind5_acc : clear implicits.
Arguments pind5_mon : clear implicits.
Arguments upind5_mon : clear implicits.
Arguments pind5_mult_strong : clear implicits.
Arguments pind5_mult : clear implicits.
Arguments pind5_fold : clear implicits.
Arguments pind5_unfold : clear implicits.

End PIND5.

Global Opaque pind5.

#[export] Hint Unfold upind5 : core.
#[export] Hint Resolve pind5_fold : core.
#[export] Hint Unfold monotone5 : core.

