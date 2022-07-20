Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paco.
From Paco Require Import paconotation_internal paco_internal pacotac_internal.
From Paco Require Export paconotation.
From Fairness Require Import pind_internal.
Set Implicit Arguments.

Section PIND1.

Variable T0 : Type.

(** ** Predicates of Arity 1
*)

Definition pind1(gf : rel1 T0 -> rel1 T0)(r: rel1 T0) : rel1 T0 :=
  @curry1 T0 (pind (fun R0 => @uncurry1 T0 (gf (@curry1 T0 R0))) (@uncurry1 T0 r)).

Definition upind1(gf : rel1 T0 -> rel1 T0)(r: rel1 T0) := pind1 gf r /1\ r.
Arguments pind1 : clear implicits.
Arguments upind1 : clear implicits.
#[local] Hint Unfold upind1 : core.

Lemma monotone1_inter (gf gf': rel1 T0 -> rel1 T0)
      (MON1: monotone1 gf)
      (MON2: monotone1 gf'):
  monotone1 (gf /2\ gf').
Proof.
  red; intros. destruct IN. split; eauto.
Qed.

Lemma _pind1_mon_gen (gf gf': rel1 T0 -> rel1 T0) r r'
    (LEgf: gf <2= gf')
    (LEr: r <1= r'):
  pind1 gf r <1== pind1 gf' r'.
Proof.
  apply curry_map1. red; intros. eapply pind_mon_gen. apply PR.
  - intros. apply LEgf, PR0.
  - intros. apply LEr, PR0.
Qed.

Lemma pind1_mon_gen (gf gf': rel1 T0 -> rel1 T0) r r' x0
    (REL: pind1 gf r x0)
    (LEgf: gf <2= gf')
    (LEr: r <1= r'):
  pind1 gf' r' x0.
Proof.
  eapply _pind1_mon_gen; [apply LEgf | apply LEr | apply REL].
Qed.

Lemma pind1_mon_bot (gf gf': rel1 T0 -> rel1 T0) r' x0
    (REL: pind1 gf bot1 x0)
    (LEgf: gf <2= gf'):
  pind1 gf' r' x0.
Proof.
  eapply pind1_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Definition top1 { T0} (x0: T0) := True.

Lemma pind1_mon_top (gf gf': rel1 T0 -> rel1 T0) r x0
    (REL: pind1 gf r x0)
    (LEgf: gf <2= gf'):
  pind1 gf' top1 x0.
Proof.
  eapply pind1_mon_gen; eauto. red. auto.
Qed.

Lemma upind1_mon_gen (gf gf': rel1 T0 -> rel1 T0) r r' x0
    (REL: upind1 gf r x0)
    (LEgf: gf <2= gf')
    (LEr: r <1= r'):
  upind1 gf' r' x0.
Proof.
  destruct REL. split; eauto.
  eapply pind1_mon_gen; [apply H | apply LEgf | apply LEr].
Qed.

Lemma upind1_mon_bot (gf gf': rel1 T0 -> rel1 T0) r' x0
    (REL: upind1 gf bot1 x0)
    (LEgf: gf <2= gf'):
  upind1 gf' r' x0.
Proof.
  eapply upind1_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Lemma upind1mon_top (gf gf': rel1 T0 -> rel1 T0) r x0
    (REL: upind1 gf r x0)
    (LEgf: gf <2= gf'):
  upind1 gf' top1 x0.
Proof.
  eapply upind1_mon_gen; eauto. red. auto.
Qed.

Section Arg1.

Variable gf : rel1 T0 -> rel1 T0.
Arguments gf : clear implicits.

Theorem _pind1_mon: _monotone1 (pind1 gf).
Proof.
  red; intros. eapply curry_map1, _pind_mon; apply uncurry_map1; assumption.
Qed.

Theorem _pind1_acc: forall
  l r (OBG: forall rr (DEC: rr <1== r) (IH: rr <1== l), pind1 gf rr <1== l),
  pind1 gf r <1== l.
Proof.
  intros. apply curry_adjoint2_1.
  eapply _pind_acc. intros.
  apply curry_adjoint2_1 in DEC. apply curry_adjoint2_1 in IH.
  apply curry_adjoint1_1.
  eapply le1_trans. 2: eapply (OBG _ DEC IH).
  apply curry_map1.
  apply _pind_mon; try apply le1_refl; apply curry_bij2_1.
Qed.

Theorem _pind1_mult_strong: forall r,
  pind1 gf r <1== pind1 gf (upind1 gf r).
Proof.
  intros. apply curry_map1.
  eapply le1_trans; [eapply _pind_mult_strong |].
  apply _pind_mon; intros [] H. apply H.
Qed.

Theorem _pind1_fold: forall r,
  gf (upind1 gf r) <1== pind1 gf r.
Proof.
  intros. apply uncurry_adjoint1_1.
  eapply le1_trans; [| apply _pind_fold]. apply le1_refl.
Qed.

Theorem _pind1_unfold: forall (MON: _monotone1 gf) r,
  pind1 gf r <1== gf (upind1 gf r).
Proof.
  intros. apply curry_adjoint2_1.
  eapply _pind_unfold; apply monotone1_map; assumption.
Qed.

Theorem pind1_acc: forall
  l r (OBG: forall rr (DEC: rr <1= r) (IH: rr <1= l), pind1 gf rr <1= l),
  pind1 gf r <1= l.
Proof.
  apply _pind1_acc.
Qed.

Theorem pind1_mon: monotone1 (pind1 gf).
Proof.
  apply monotone1_eq.
  apply _pind1_mon.
Qed.

Theorem upind1_mon: monotone1 (upind1 gf).
Proof.
  red; intros.
  destruct IN. split; eauto.
  eapply pind1_mon. apply H. apply LE.
Qed.

Theorem pind1_mult_strong: forall r,
  pind1 gf r <1= pind1 gf (upind1 gf r).
Proof.
  apply _pind1_mult_strong.
Qed.

Corollary pind1_mult: forall r,
  pind1 gf r <1= pind1 gf (pind1 gf r).
Proof. intros; eapply pind1_mult_strong in PR. eapply pind1_mon; eauto. intros. destruct PR0. eauto. Qed.

Theorem pind1_fold: forall r,
  gf (upind1 gf r) <1= pind1 gf r.
Proof.
  apply _pind1_fold.
Qed.

Theorem pind1_unfold: forall (MON: monotone1 gf) r,
  pind1 gf r <1= gf (upind1 gf r).
Proof.
  intro. eapply _pind1_unfold; apply monotone1_eq; assumption.
Qed.

End Arg1.

Arguments pind1_acc : clear implicits.
Arguments pind1_mon : clear implicits.
Arguments upind1_mon : clear implicits.
Arguments pind1_mult_strong : clear implicits.
Arguments pind1_mult : clear implicits.
Arguments pind1_fold : clear implicits.
Arguments pind1_unfold : clear implicits.

End PIND1.

Global Opaque pind1.

#[export] Hint Unfold upind1 : core.
#[export] Hint Resolve pind1_fold : core.
#[export] Hint Unfold monotone1 : core.

