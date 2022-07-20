Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paco.
From Paco Require Import paconotation_internal paco_internal pacotac_internal.
From Paco Require Export paconotation.
From Fairness Require Import pind_internal.
Set Implicit Arguments.

Section PIND2.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.

(** ** Predicates of Arity 2
*)

Definition pind2(gf : rel2 T0 T1 -> rel2 T0 T1)(r: rel2 T0 T1) : rel2 T0 T1 :=
  @curry2 T0 T1 (pind (fun R0 => @uncurry2 T0 T1 (gf (@curry2 T0 T1 R0))) (@uncurry2 T0 T1 r)).

Definition upind2(gf : rel2 T0 T1 -> rel2 T0 T1)(r: rel2 T0 T1) := pind2 gf r /2\ r.
Arguments pind2 : clear implicits.
Arguments upind2 : clear implicits.
#[local] Hint Unfold upind2 : core.

Lemma monotone2_inter (gf gf': rel2 T0 T1 -> rel2 T0 T1)
      (MON1: monotone2 gf)
      (MON2: monotone2 gf'):
  monotone2 (gf /3\ gf').
Proof.
  red; intros. destruct IN. split; eauto.
Qed.

Lemma _pind2_mon_gen (gf gf': rel2 T0 T1 -> rel2 T0 T1) r r'
    (LEgf: gf <3= gf')
    (LEr: r <2= r'):
  pind2 gf r <2== pind2 gf' r'.
Proof.
  apply curry_map2. red; intros. eapply pind_mon_gen. apply PR.
  - intros. apply LEgf, PR0.
  - intros. apply LEr, PR0.
Qed.

Lemma pind2_mon_gen (gf gf': rel2 T0 T1 -> rel2 T0 T1) r r' x0 x1
    (REL: pind2 gf r x0 x1)
    (LEgf: gf <3= gf')
    (LEr: r <2= r'):
  pind2 gf' r' x0 x1.
Proof.
  eapply _pind2_mon_gen; [apply LEgf | apply LEr | apply REL].
Qed.

Lemma pind2_mon_bot (gf gf': rel2 T0 T1 -> rel2 T0 T1) r' x0 x1
    (REL: pind2 gf bot2 x0 x1)
    (LEgf: gf <3= gf'):
  pind2 gf' r' x0 x1.
Proof.
  eapply pind2_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Definition top2 { T0 T1} (x0: T0) (x1: T1 x0) := True.

Lemma pind2_mon_top (gf gf': rel2 T0 T1 -> rel2 T0 T1) r x0 x1
    (REL: pind2 gf r x0 x1)
    (LEgf: gf <3= gf'):
  pind2 gf' top2 x0 x1.
Proof.
  eapply pind2_mon_gen; eauto. red. auto.
Qed.

Lemma upind2_mon_gen (gf gf': rel2 T0 T1 -> rel2 T0 T1) r r' x0 x1
    (REL: upind2 gf r x0 x1)
    (LEgf: gf <3= gf')
    (LEr: r <2= r'):
  upind2 gf' r' x0 x1.
Proof.
  destruct REL. split; eauto.
  eapply pind2_mon_gen; [apply H | apply LEgf | apply LEr].
Qed.

Lemma upind2_mon_bot (gf gf': rel2 T0 T1 -> rel2 T0 T1) r' x0 x1
    (REL: upind2 gf bot2 x0 x1)
    (LEgf: gf <3= gf'):
  upind2 gf' r' x0 x1.
Proof.
  eapply upind2_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Lemma upind2mon_top (gf gf': rel2 T0 T1 -> rel2 T0 T1) r x0 x1
    (REL: upind2 gf r x0 x1)
    (LEgf: gf <3= gf'):
  upind2 gf' top2 x0 x1.
Proof.
  eapply upind2_mon_gen; eauto. red. auto.
Qed.

Section Arg2.

Variable gf : rel2 T0 T1 -> rel2 T0 T1.
Arguments gf : clear implicits.

Theorem _pind2_mon: _monotone2 (pind2 gf).
Proof.
  red; intros. eapply curry_map2, _pind_mon; apply uncurry_map2; assumption.
Qed.

Theorem _pind2_acc: forall
  l r (OBG: forall rr (DEC: rr <2== r) (IH: rr <2== l), pind2 gf rr <2== l),
  pind2 gf r <2== l.
Proof.
  intros. apply curry_adjoint2_2.
  eapply _pind_acc. intros.
  apply curry_adjoint2_2 in DEC. apply curry_adjoint2_2 in IH.
  apply curry_adjoint1_2.
  eapply le2_trans. 2: eapply (OBG _ DEC IH).
  apply curry_map2.
  apply _pind_mon; try apply le1_refl; apply curry_bij2_2.
Qed.

Theorem _pind2_mult_strong: forall r,
  pind2 gf r <2== pind2 gf (upind2 gf r).
Proof.
  intros. apply curry_map2.
  eapply le1_trans; [eapply _pind_mult_strong |].
  apply _pind_mon; intros [] H. apply H.
Qed.

Theorem _pind2_fold: forall r,
  gf (upind2 gf r) <2== pind2 gf r.
Proof.
  intros. apply uncurry_adjoint1_2.
  eapply le1_trans; [| apply _pind_fold]. apply le1_refl.
Qed.

Theorem _pind2_unfold: forall (MON: _monotone2 gf) r,
  pind2 gf r <2== gf (upind2 gf r).
Proof.
  intros. apply curry_adjoint2_2.
  eapply _pind_unfold; apply monotone2_map; assumption.
Qed.

Theorem pind2_acc: forall
  l r (OBG: forall rr (DEC: rr <2= r) (IH: rr <2= l), pind2 gf rr <2= l),
  pind2 gf r <2= l.
Proof.
  apply _pind2_acc.
Qed.

Theorem pind2_mon: monotone2 (pind2 gf).
Proof.
  apply monotone2_eq.
  apply _pind2_mon.
Qed.

Theorem upind2_mon: monotone2 (upind2 gf).
Proof.
  red; intros.
  destruct IN. split; eauto.
  eapply pind2_mon. apply H. apply LE.
Qed.

Theorem pind2_mult_strong: forall r,
  pind2 gf r <2= pind2 gf (upind2 gf r).
Proof.
  apply _pind2_mult_strong.
Qed.

Corollary pind2_mult: forall r,
  pind2 gf r <2= pind2 gf (pind2 gf r).
Proof. intros; eapply pind2_mult_strong in PR. eapply pind2_mon; eauto. intros. destruct PR0. eauto. Qed.

Theorem pind2_fold: forall r,
  gf (upind2 gf r) <2= pind2 gf r.
Proof.
  apply _pind2_fold.
Qed.

Theorem pind2_unfold: forall (MON: monotone2 gf) r,
  pind2 gf r <2= gf (upind2 gf r).
Proof.
  intro. eapply _pind2_unfold; apply monotone2_eq; assumption.
Qed.

End Arg2.

Arguments pind2_acc : clear implicits.
Arguments pind2_mon : clear implicits.
Arguments upind2_mon : clear implicits.
Arguments pind2_mult_strong : clear implicits.
Arguments pind2_mult : clear implicits.
Arguments pind2_fold : clear implicits.
Arguments pind2_unfold : clear implicits.

End PIND2.

Global Opaque pind2.

#[export] Hint Unfold upind2 : core.
#[export] Hint Resolve pind2_fold : core.
#[export] Hint Unfold monotone2 : core.

