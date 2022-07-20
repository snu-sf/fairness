Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paco.
From Paco Require Import paconotation_internal paco_internal pacotac_internal.
From Paco Require Export paconotation.
From Fairness Require Import pind_internal.
Set Implicit Arguments.

Section PIND7.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.

(** ** Predicates of Arity 7
*)

Definition pind7(gf : rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6)(r: rel7 T0 T1 T2 T3 T4 T5 T6) : rel7 T0 T1 T2 T3 T4 T5 T6 :=
  @curry7 T0 T1 T2 T3 T4 T5 T6 (pind (fun R0 => @uncurry7 T0 T1 T2 T3 T4 T5 T6 (gf (@curry7 T0 T1 T2 T3 T4 T5 T6 R0))) (@uncurry7 T0 T1 T2 T3 T4 T5 T6 r)).

Definition upind7(gf : rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6)(r: rel7 T0 T1 T2 T3 T4 T5 T6) := pind7 gf r /7\ r.
Arguments pind7 : clear implicits.
Arguments upind7 : clear implicits.
#[local] Hint Unfold upind7 : core.

Lemma monotone7_inter (gf gf': rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6)
      (MON1: monotone7 gf)
      (MON2: monotone7 gf'):
  monotone7 (gf /8\ gf').
Proof.
  red; intros. destruct IN. split; eauto.
Qed.

Lemma _pind7_mon_gen (gf gf': rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6) r r'
    (LEgf: gf <8= gf')
    (LEr: r <7= r'):
  pind7 gf r <7== pind7 gf' r'.
Proof.
  apply curry_map7. red; intros. eapply pind_mon_gen. apply PR.
  - intros. apply LEgf, PR0.
  - intros. apply LEr, PR0.
Qed.

Lemma pind7_mon_gen (gf gf': rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6) r r' x0 x1 x2 x3 x4 x5 x6
    (REL: pind7 gf r x0 x1 x2 x3 x4 x5 x6)
    (LEgf: gf <8= gf')
    (LEr: r <7= r'):
  pind7 gf' r' x0 x1 x2 x3 x4 x5 x6.
Proof.
  eapply _pind7_mon_gen; [apply LEgf | apply LEr | apply REL].
Qed.

Lemma pind7_mon_bot (gf gf': rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6) r' x0 x1 x2 x3 x4 x5 x6
    (REL: pind7 gf bot7 x0 x1 x2 x3 x4 x5 x6)
    (LEgf: gf <8= gf'):
  pind7 gf' r' x0 x1 x2 x3 x4 x5 x6.
Proof.
  eapply pind7_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Definition top7 { T0 T1 T2 T3 T4 T5 T6} (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) (x4: T4 x0 x1 x2 x3) (x5: T5 x0 x1 x2 x3 x4) (x6: T6 x0 x1 x2 x3 x4 x5) := True.

Lemma pind7_mon_top (gf gf': rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6) r x0 x1 x2 x3 x4 x5 x6
    (REL: pind7 gf r x0 x1 x2 x3 x4 x5 x6)
    (LEgf: gf <8= gf'):
  pind7 gf' top7 x0 x1 x2 x3 x4 x5 x6.
Proof.
  eapply pind7_mon_gen; eauto. red. auto.
Qed.

Lemma upind7_mon_gen (gf gf': rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6) r r' x0 x1 x2 x3 x4 x5 x6
    (REL: upind7 gf r x0 x1 x2 x3 x4 x5 x6)
    (LEgf: gf <8= gf')
    (LEr: r <7= r'):
  upind7 gf' r' x0 x1 x2 x3 x4 x5 x6.
Proof.
  destruct REL. split; eauto.
  eapply pind7_mon_gen; [apply H | apply LEgf | apply LEr].
Qed.

Lemma upind7_mon_bot (gf gf': rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6) r' x0 x1 x2 x3 x4 x5 x6
    (REL: upind7 gf bot7 x0 x1 x2 x3 x4 x5 x6)
    (LEgf: gf <8= gf'):
  upind7 gf' r' x0 x1 x2 x3 x4 x5 x6.
Proof.
  eapply upind7_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Lemma upind7mon_top (gf gf': rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6) r x0 x1 x2 x3 x4 x5 x6
    (REL: upind7 gf r x0 x1 x2 x3 x4 x5 x6)
    (LEgf: gf <8= gf'):
  upind7 gf' top7 x0 x1 x2 x3 x4 x5 x6.
Proof.
  eapply upind7_mon_gen; eauto. red. auto.
Qed.

Section Arg7.

Variable gf : rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6.
Arguments gf : clear implicits.

Theorem _pind7_mon: _monotone7 (pind7 gf).
Proof.
  red; intros. eapply curry_map7, _pind_mon; apply uncurry_map7; assumption.
Qed.

Theorem _pind7_acc: forall
  l r (OBG: forall rr (DEC: rr <7== r) (IH: rr <7== l), pind7 gf rr <7== l),
  pind7 gf r <7== l.
Proof.
  intros. apply curry_adjoint2_7.
  eapply _pind_acc. intros.
  apply curry_adjoint2_7 in DEC. apply curry_adjoint2_7 in IH.
  apply curry_adjoint1_7.
  eapply le7_trans. 2: eapply (OBG _ DEC IH).
  apply curry_map7.
  apply _pind_mon; try apply le1_refl; apply curry_bij2_7.
Qed.

Theorem _pind7_mult_strong: forall r,
  pind7 gf r <7== pind7 gf (upind7 gf r).
Proof.
  intros. apply curry_map7.
  eapply le1_trans; [eapply _pind_mult_strong |].
  apply _pind_mon; intros [] H. apply H.
Qed.

Theorem _pind7_fold: forall r,
  gf (upind7 gf r) <7== pind7 gf r.
Proof.
  intros. apply uncurry_adjoint1_7.
  eapply le1_trans; [| apply _pind_fold]. apply le1_refl.
Qed.

Theorem _pind7_unfold: forall (MON: _monotone7 gf) r,
  pind7 gf r <7== gf (upind7 gf r).
Proof.
  intros. apply curry_adjoint2_7.
  eapply _pind_unfold; apply monotone7_map; assumption.
Qed.

Theorem pind7_acc: forall
  l r (OBG: forall rr (DEC: rr <7= r) (IH: rr <7= l), pind7 gf rr <7= l),
  pind7 gf r <7= l.
Proof.
  apply _pind7_acc.
Qed.

Theorem pind7_mon: monotone7 (pind7 gf).
Proof.
  apply monotone7_eq.
  apply _pind7_mon.
Qed.

Theorem upind7_mon: monotone7 (upind7 gf).
Proof.
  red; intros.
  destruct IN. split; eauto.
  eapply pind7_mon. apply H. apply LE.
Qed.

Theorem pind7_mult_strong: forall r,
  pind7 gf r <7= pind7 gf (upind7 gf r).
Proof.
  apply _pind7_mult_strong.
Qed.

Corollary pind7_mult: forall r,
  pind7 gf r <7= pind7 gf (pind7 gf r).
Proof. intros; eapply pind7_mult_strong in PR. eapply pind7_mon; eauto. intros. destruct PR0. eauto. Qed.

Theorem pind7_fold: forall r,
  gf (upind7 gf r) <7= pind7 gf r.
Proof.
  apply _pind7_fold.
Qed.

Theorem pind7_unfold: forall (MON: monotone7 gf) r,
  pind7 gf r <7= gf (upind7 gf r).
Proof.
  intro. eapply _pind7_unfold; apply monotone7_eq; assumption.
Qed.

End Arg7.

Arguments pind7_acc : clear implicits.
Arguments pind7_mon : clear implicits.
Arguments upind7_mon : clear implicits.
Arguments pind7_mult_strong : clear implicits.
Arguments pind7_mult : clear implicits.
Arguments pind7_fold : clear implicits.
Arguments pind7_unfold : clear implicits.

End PIND7.

Global Opaque pind7.

#[export] Hint Unfold upind7 : core.
#[export] Hint Resolve pind7_fold : core.
#[export] Hint Unfold monotone7 : core.

