Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paco.
From Paco Require Import paconotation_internal paco_internal pacotac_internal.
From Paco Require Export paconotation.
From Fairness Require Import pind_internal.
Set Implicit Arguments.

Section PIND3.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.

(** ** Predicates of Arity 3
*)

Definition pind3(gf : rel3 T0 T1 T2 -> rel3 T0 T1 T2)(r: rel3 T0 T1 T2) : rel3 T0 T1 T2 :=
  @curry3 T0 T1 T2 (pind (fun R0 => @uncurry3 T0 T1 T2 (gf (@curry3 T0 T1 T2 R0))) (@uncurry3 T0 T1 T2 r)).

Definition upind3(gf : rel3 T0 T1 T2 -> rel3 T0 T1 T2)(r: rel3 T0 T1 T2) := pind3 gf r /3\ r.
Arguments pind3 : clear implicits.
Arguments upind3 : clear implicits.
#[local] Hint Unfold upind3 : core.

Lemma monotone3_inter (gf gf': rel3 T0 T1 T2 -> rel3 T0 T1 T2)
      (MON1: monotone3 gf)
      (MON2: monotone3 gf'):
  monotone3 (gf /4\ gf').
Proof.
  red; intros. destruct IN. split; eauto.
Qed.

Lemma _pind3_mon_gen (gf gf': rel3 T0 T1 T2 -> rel3 T0 T1 T2) r r'
    (LEgf: gf <4= gf')
    (LEr: r <3= r'):
  pind3 gf r <3== pind3 gf' r'.
Proof.
  apply curry_map3. red; intros. eapply pind_mon_gen. apply PR.
  - intros. apply LEgf, PR0.
  - intros. apply LEr, PR0.
Qed.

Lemma pind3_mon_gen (gf gf': rel3 T0 T1 T2 -> rel3 T0 T1 T2) r r' x0 x1 x2
    (REL: pind3 gf r x0 x1 x2)
    (LEgf: gf <4= gf')
    (LEr: r <3= r'):
  pind3 gf' r' x0 x1 x2.
Proof.
  eapply _pind3_mon_gen; [apply LEgf | apply LEr | apply REL].
Qed.

Lemma pind3_mon_bot (gf gf': rel3 T0 T1 T2 -> rel3 T0 T1 T2) r' x0 x1 x2
    (REL: pind3 gf bot3 x0 x1 x2)
    (LEgf: gf <4= gf'):
  pind3 gf' r' x0 x1 x2.
Proof.
  eapply pind3_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Definition top3 { T0 T1 T2} (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) := True.

Lemma pind3_mon_top (gf gf': rel3 T0 T1 T2 -> rel3 T0 T1 T2) r x0 x1 x2
    (REL: pind3 gf r x0 x1 x2)
    (LEgf: gf <4= gf'):
  pind3 gf' top3 x0 x1 x2.
Proof.
  eapply pind3_mon_gen; eauto. red. auto.
Qed.

Lemma upind3_mon_gen (gf gf': rel3 T0 T1 T2 -> rel3 T0 T1 T2) r r' x0 x1 x2
    (REL: upind3 gf r x0 x1 x2)
    (LEgf: gf <4= gf')
    (LEr: r <3= r'):
  upind3 gf' r' x0 x1 x2.
Proof.
  destruct REL. split; eauto.
  eapply pind3_mon_gen; [apply H | apply LEgf | apply LEr].
Qed.

Lemma upind3_mon_bot (gf gf': rel3 T0 T1 T2 -> rel3 T0 T1 T2) r' x0 x1 x2
    (REL: upind3 gf bot3 x0 x1 x2)
    (LEgf: gf <4= gf'):
  upind3 gf' r' x0 x1 x2.
Proof.
  eapply upind3_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Lemma upind3mon_top (gf gf': rel3 T0 T1 T2 -> rel3 T0 T1 T2) r x0 x1 x2
    (REL: upind3 gf r x0 x1 x2)
    (LEgf: gf <4= gf'):
  upind3 gf' top3 x0 x1 x2.
Proof.
  eapply upind3_mon_gen; eauto. red. auto.
Qed.

Section Arg3.

Variable gf : rel3 T0 T1 T2 -> rel3 T0 T1 T2.
Arguments gf : clear implicits.

Theorem _pind3_mon: _monotone3 (pind3 gf).
Proof.
  red; intros. eapply curry_map3, _pind_mon; apply uncurry_map3; assumption.
Qed.

Theorem _pind3_acc: forall
  l r (OBG: forall rr (DEC: rr <3== r) (IH: rr <3== l), pind3 gf rr <3== l),
  pind3 gf r <3== l.
Proof.
  intros. apply curry_adjoint2_3.
  eapply _pind_acc. intros.
  apply curry_adjoint2_3 in DEC. apply curry_adjoint2_3 in IH.
  apply curry_adjoint1_3.
  eapply le3_trans. 2: eapply (OBG _ DEC IH).
  apply curry_map3.
  apply _pind_mon; try apply le1_refl; apply curry_bij2_3.
Qed.

Theorem _pind3_mult_strong: forall r,
  pind3 gf r <3== pind3 gf (upind3 gf r).
Proof.
  intros. apply curry_map3.
  eapply le1_trans; [eapply _pind_mult_strong |].
  apply _pind_mon; intros [] H. apply H.
Qed.

Theorem _pind3_fold: forall r,
  gf (upind3 gf r) <3== pind3 gf r.
Proof.
  intros. apply uncurry_adjoint1_3.
  eapply le1_trans; [| apply _pind_fold]. apply le1_refl.
Qed.

Theorem _pind3_unfold: forall (MON: _monotone3 gf) r,
  pind3 gf r <3== gf (upind3 gf r).
Proof.
  intros. apply curry_adjoint2_3.
  eapply _pind_unfold; apply monotone3_map; assumption.
Qed.

Theorem pind3_acc: forall
  l r (OBG: forall rr (DEC: rr <3= r) (IH: rr <3= l), pind3 gf rr <3= l),
  pind3 gf r <3= l.
Proof.
  apply _pind3_acc.
Qed.

Theorem pind3_mon: monotone3 (pind3 gf).
Proof.
  apply monotone3_eq.
  apply _pind3_mon.
Qed.

Theorem upind3_mon: monotone3 (upind3 gf).
Proof.
  red; intros.
  destruct IN. split; eauto.
  eapply pind3_mon. apply H. apply LE.
Qed.

Theorem pind3_mult_strong: forall r,
  pind3 gf r <3= pind3 gf (upind3 gf r).
Proof.
  apply _pind3_mult_strong.
Qed.

Corollary pind3_mult: forall r,
  pind3 gf r <3= pind3 gf (pind3 gf r).
Proof. intros; eapply pind3_mult_strong in PR. eapply pind3_mon; eauto. intros. destruct PR0. eauto. Qed.

Theorem pind3_fold: forall r,
  gf (upind3 gf r) <3= pind3 gf r.
Proof.
  apply _pind3_fold.
Qed.

Theorem pind3_unfold: forall (MON: monotone3 gf) r,
  pind3 gf r <3= gf (upind3 gf r).
Proof.
  intro. eapply _pind3_unfold; apply monotone3_eq; assumption.
Qed.

End Arg3.

Arguments pind3_acc : clear implicits.
Arguments pind3_mon : clear implicits.
Arguments upind3_mon : clear implicits.
Arguments pind3_mult_strong : clear implicits.
Arguments pind3_mult : clear implicits.
Arguments pind3_fold : clear implicits.
Arguments pind3_unfold : clear implicits.

End PIND3.

Global Opaque pind3.

#[export] Hint Unfold upind3 : core.
#[export] Hint Resolve pind3_fold : core.
#[export] Hint Unfold monotone3 : core.

