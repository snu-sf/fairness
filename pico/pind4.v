Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paco.
From Paco Require Import paconotation_internal paco_internal pacotac_internal.
From Paco Require Export paconotation.
From Fairness Require Import pind_internal.
Set Implicit Arguments.

Section PIND4.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.

(** ** Predicates of Arity 4
*)

Definition pind4(gf : rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3)(r: rel4 T0 T1 T2 T3) : rel4 T0 T1 T2 T3 :=
  @curry4 T0 T1 T2 T3 (pind (fun R0 => @uncurry4 T0 T1 T2 T3 (gf (@curry4 T0 T1 T2 T3 R0))) (@uncurry4 T0 T1 T2 T3 r)).

Definition upind4(gf : rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3)(r: rel4 T0 T1 T2 T3) := pind4 gf r /4\ r.
Arguments pind4 : clear implicits.
Arguments upind4 : clear implicits.
#[local] Hint Unfold upind4 : core.

Lemma monotone4_inter (gf gf': rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3)
      (MON1: monotone4 gf)
      (MON2: monotone4 gf'):
  monotone4 (gf /5\ gf').
Proof.
  red; intros. destruct IN. split; eauto.
Qed.

Lemma _pind4_mon_gen (gf gf': rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3) r r'
    (LEgf: gf <5= gf')
    (LEr: r <4= r'):
  pind4 gf r <4== pind4 gf' r'.
Proof.
  apply curry_map4. red; intros. eapply pind_mon_gen. apply PR.
  - intros. apply LEgf, PR0.
  - intros. apply LEr, PR0.
Qed.

Lemma pind4_mon_gen (gf gf': rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3) r r' x0 x1 x2 x3
    (REL: pind4 gf r x0 x1 x2 x3)
    (LEgf: gf <5= gf')
    (LEr: r <4= r'):
  pind4 gf' r' x0 x1 x2 x3.
Proof.
  eapply _pind4_mon_gen; [apply LEgf | apply LEr | apply REL].
Qed.

Lemma pind4_mon_bot (gf gf': rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3) r' x0 x1 x2 x3
    (REL: pind4 gf bot4 x0 x1 x2 x3)
    (LEgf: gf <5= gf'):
  pind4 gf' r' x0 x1 x2 x3.
Proof.
  eapply pind4_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Definition top4 { T0 T1 T2 T3} (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) := True.

Lemma pind4_mon_top (gf gf': rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3) r x0 x1 x2 x3
    (REL: pind4 gf r x0 x1 x2 x3)
    (LEgf: gf <5= gf'):
  pind4 gf' top4 x0 x1 x2 x3.
Proof.
  eapply pind4_mon_gen; eauto. red. auto.
Qed.

Lemma upind4_mon_gen (gf gf': rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3) r r' x0 x1 x2 x3
    (REL: upind4 gf r x0 x1 x2 x3)
    (LEgf: gf <5= gf')
    (LEr: r <4= r'):
  upind4 gf' r' x0 x1 x2 x3.
Proof.
  destruct REL. split; eauto.
  eapply pind4_mon_gen; [apply H | apply LEgf | apply LEr].
Qed.

Lemma upind4_mon_bot (gf gf': rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3) r' x0 x1 x2 x3
    (REL: upind4 gf bot4 x0 x1 x2 x3)
    (LEgf: gf <5= gf'):
  upind4 gf' r' x0 x1 x2 x3.
Proof.
  eapply upind4_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Lemma upind4mon_top (gf gf': rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3) r x0 x1 x2 x3
    (REL: upind4 gf r x0 x1 x2 x3)
    (LEgf: gf <5= gf'):
  upind4 gf' top4 x0 x1 x2 x3.
Proof.
  eapply upind4_mon_gen; eauto. red. auto.
Qed.

Section Arg4.

Variable gf : rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3.
Arguments gf : clear implicits.

Theorem _pind4_mon: _monotone4 (pind4 gf).
Proof.
  red; intros. eapply curry_map4, _pind_mon; apply uncurry_map4; assumption.
Qed.

Theorem _pind4_acc: forall
  l r (OBG: forall rr (DEC: rr <4== r) (IH: rr <4== l), pind4 gf rr <4== l),
  pind4 gf r <4== l.
Proof.
  intros. apply curry_adjoint2_4.
  eapply _pind_acc. intros.
  apply curry_adjoint2_4 in DEC. apply curry_adjoint2_4 in IH.
  apply curry_adjoint1_4.
  eapply le4_trans. 2: eapply (OBG _ DEC IH).
  apply curry_map4.
  apply _pind_mon; try apply le1_refl; apply curry_bij2_4.
Qed.

Theorem _pind4_mult_strong: forall r,
  pind4 gf r <4== pind4 gf (upind4 gf r).
Proof.
  intros. apply curry_map4.
  eapply le1_trans; [eapply _pind_mult_strong |].
  apply _pind_mon; intros [] H. apply H.
Qed.

Theorem _pind4_fold: forall r,
  gf (upind4 gf r) <4== pind4 gf r.
Proof.
  intros. apply uncurry_adjoint1_4.
  eapply le1_trans; [| apply _pind_fold]. apply le1_refl.
Qed.

Theorem _pind4_unfold: forall (MON: _monotone4 gf) r,
  pind4 gf r <4== gf (upind4 gf r).
Proof.
  intros. apply curry_adjoint2_4.
  eapply _pind_unfold; apply monotone4_map; assumption.
Qed.

Theorem pind4_acc: forall
  l r (OBG: forall rr (DEC: rr <4= r) (IH: rr <4= l), pind4 gf rr <4= l),
  pind4 gf r <4= l.
Proof.
  apply _pind4_acc.
Qed.

Theorem pind4_mon: monotone4 (pind4 gf).
Proof.
  apply monotone4_eq.
  apply _pind4_mon.
Qed.

Theorem upind4_mon: monotone4 (upind4 gf).
Proof.
  red; intros.
  destruct IN. split; eauto.
  eapply pind4_mon. apply H. apply LE.
Qed.

Theorem pind4_mult_strong: forall r,
  pind4 gf r <4= pind4 gf (upind4 gf r).
Proof.
  apply _pind4_mult_strong.
Qed.

Corollary pind4_mult: forall r,
  pind4 gf r <4= pind4 gf (pind4 gf r).
Proof. intros; eapply pind4_mult_strong in PR. eapply pind4_mon; eauto. intros. destruct PR0. eauto. Qed.

Theorem pind4_fold: forall r,
  gf (upind4 gf r) <4= pind4 gf r.
Proof.
  apply _pind4_fold.
Qed.

Theorem pind4_unfold: forall (MON: monotone4 gf) r,
  pind4 gf r <4= gf (upind4 gf r).
Proof.
  intro. eapply _pind4_unfold; apply monotone4_eq; assumption.
Qed.

End Arg4.

Arguments pind4_acc : clear implicits.
Arguments pind4_mon : clear implicits.
Arguments upind4_mon : clear implicits.
Arguments pind4_mult_strong : clear implicits.
Arguments pind4_mult : clear implicits.
Arguments pind4_fold : clear implicits.
Arguments pind4_unfold : clear implicits.

End PIND4.

Global Opaque pind4.

#[export] Hint Unfold upind4 : core.
#[export] Hint Resolve pind4_fold : core.
#[export] Hint Unfold monotone4 : core.

