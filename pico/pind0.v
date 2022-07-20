Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paco.
From Paco Require Import paconotation_internal paco_internal pacotac_internal.
From Paco Require Export paconotation.
From Fairness Require Import pind_internal.
Set Implicit Arguments.

Section PIND0.


(** ** Predicates of Arity 0
*)

Definition pind0(gf : rel0 -> rel0)(r: rel0) : rel0 :=
  @curry0 (pind (fun R0 => @uncurry0 (gf (@curry0 R0))) (@uncurry0 r)).

Definition upind0(gf : rel0 -> rel0)(r: rel0) := pind0 gf r /0\ r.
Arguments pind0 : clear implicits.
Arguments upind0 : clear implicits.
#[local] Hint Unfold upind0 : core.

Lemma monotone0_inter (gf gf': rel0 -> rel0)
      (MON1: monotone0 gf)
      (MON2: monotone0 gf'):
  monotone0 (gf /1\ gf').
Proof.
  red; intros. destruct IN. split; eauto.
Qed.

Lemma _pind0_mon_gen (gf gf': rel0 -> rel0) r r'
    (LEgf: gf <1= gf')
    (LEr: r <0= r'):
  pind0 gf r <0== pind0 gf' r'.
Proof.
  apply curry_map0. red; intros. eapply pind_mon_gen. apply PR.
  - intros. apply LEgf, PR0.
  - intros. apply LEr, PR0.
Qed.

Lemma pind0_mon_gen (gf gf': rel0 -> rel0) r r'
    (REL: pind0 gf r)
    (LEgf: gf <1= gf')
    (LEr: r <0= r'):
  pind0 gf' r'.
Proof.
  eapply _pind0_mon_gen; [apply LEgf | apply LEr | apply REL].
Qed.

Lemma pind0_mon_bot (gf gf': rel0 -> rel0) r'
    (REL: pind0 gf bot0)
    (LEgf: gf <1= gf'):
  pind0 gf' r'.
Proof.
  eapply pind0_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Definition top0 := True.

Lemma pind0_mon_top (gf gf': rel0 -> rel0) r
    (REL: pind0 gf r)
    (LEgf: gf <1= gf'):
  pind0 gf' top0.
Proof.
  eapply pind0_mon_gen; eauto. red. auto.
Qed.

Lemma upind0_mon_gen (gf gf': rel0 -> rel0) r r'
    (REL: upind0 gf r)
    (LEgf: gf <1= gf')
    (LEr: r <0= r'):
  upind0 gf' r'.
Proof.
  destruct REL. split; eauto.
  eapply pind0_mon_gen; [apply H | apply LEgf | apply LEr].
Qed.

Lemma upind0_mon_bot (gf gf': rel0 -> rel0) r'
    (REL: upind0 gf bot0)
    (LEgf: gf <1= gf'):
  upind0 gf' r'.
Proof.
  eapply upind0_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Lemma upind0mon_top (gf gf': rel0 -> rel0) r
    (REL: upind0 gf r)
    (LEgf: gf <1= gf'):
  upind0 gf' top0.
Proof.
  eapply upind0_mon_gen; eauto. red. auto.
Qed.

Section Arg0.

Variable gf : rel0 -> rel0.
Arguments gf : clear implicits.

Theorem _pind0_mon: _monotone0 (pind0 gf).
Proof.
  red; intros. eapply curry_map0, _pind_mon; apply uncurry_map0; assumption.
Qed.

Theorem _pind0_acc: forall
  l r (OBG: forall rr (DEC: rr <0== r) (IH: rr <0== l), pind0 gf rr <0== l),
  pind0 gf r <0== l.
Proof.
  intros. apply curry_adjoint2_0.
  eapply _pind_acc. intros.
  apply curry_adjoint2_0 in DEC. apply curry_adjoint2_0 in IH.
  apply curry_adjoint1_0.
  eapply le0_trans. 2: eapply (OBG _ DEC IH).
  apply curry_map0.
  apply _pind_mon; try apply le1_refl; apply curry_bij2_0.
Qed.

Theorem _pind0_mult_strong: forall r,
  pind0 gf r <0== pind0 gf (upind0 gf r).
Proof.
  intros. apply curry_map0.
  eapply le1_trans; [eapply _pind_mult_strong |].
  apply _pind_mon; intros [] H. apply H.
Qed.

Theorem _pind0_fold: forall r,
  gf (upind0 gf r) <0== pind0 gf r.
Proof.
  intros. apply uncurry_adjoint1_0.
  eapply le1_trans; [| apply _pind_fold]. apply le1_refl.
Qed.

Theorem _pind0_unfold: forall (MON: _monotone0 gf) r,
  pind0 gf r <0== gf (upind0 gf r).
Proof.
  intros. apply curry_adjoint2_0.
  eapply _pind_unfold; apply monotone0_map; assumption.
Qed.

Theorem pind0_acc: forall
  l r (OBG: forall rr (DEC: rr <0= r) (IH: rr <0= l), pind0 gf rr <0= l),
  pind0 gf r <0= l.
Proof.
  apply _pind0_acc.
Qed.

Theorem pind0_mon: monotone0 (pind0 gf).
Proof.
  apply monotone0_eq.
  apply _pind0_mon.
Qed.

Theorem upind0_mon: monotone0 (upind0 gf).
Proof.
  red; intros.
  destruct IN. split; eauto.
  eapply pind0_mon. apply H. apply LE.
Qed.

Theorem pind0_mult_strong: forall r,
  pind0 gf r <0= pind0 gf (upind0 gf r).
Proof.
  apply _pind0_mult_strong.
Qed.

Corollary pind0_mult: forall r,
  pind0 gf r <0= pind0 gf (pind0 gf r).
Proof. intros; eapply pind0_mult_strong in PR. eapply pind0_mon; eauto. intros. destruct PR0. eauto. Qed.

Theorem pind0_fold: forall r,
  gf (upind0 gf r) <0= pind0 gf r.
Proof.
  apply _pind0_fold.
Qed.

Theorem pind0_unfold: forall (MON: monotone0 gf) r,
  pind0 gf r <0= gf (upind0 gf r).
Proof.
  intro. eapply _pind0_unfold; apply monotone0_eq; assumption.
Qed.

End Arg0.

Arguments pind0_acc : clear implicits.
Arguments pind0_mon : clear implicits.
Arguments upind0_mon : clear implicits.
Arguments pind0_mult_strong : clear implicits.
Arguments pind0_mult : clear implicits.
Arguments pind0_fold : clear implicits.
Arguments pind0_unfold : clear implicits.

End PIND0.

Global Opaque pind0.

#[export] Hint Unfold upind0 : core.
#[export] Hint Resolve pind0_fold : core.
#[export] Hint Unfold monotone0 : core.

