Require Export Program.Basics. Open Scope program_scope.
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

Definition pind3(lf : rel3 T0 T1 T2 -> rel3 T0 T1 T2)(r: rel3 T0 T1 T2) : rel3 T0 T1 T2 :=
  @curry3 T0 T1 T2 (pind (fun R0 => @uncurry3 T0 T1 T2 (lf (@curry3 T0 T1 T2 R0))) (@uncurry3 T0 T1 T2 r)).

Definition upind3(lf : rel3 T0 T1 T2 -> rel3 T0 T1 T2)(r: rel3 T0 T1 T2) := pind3 lf r /3\ r.
Arguments pind3 : clear implicits.
Arguments upind3 : clear implicits.
#[local] Hint Unfold upind3 : core.

Definition monotone3 (lf: rel3 T0 T1 T2 -> rel3 T0 T1 T2) :=
  forall x0 x1 x2 r r' (IN: lf r x0 x1 x2) (LE: r <3= r'), lf r' x0 x1 x2.

Definition _monotone3 (lf: rel3 T0 T1 T2 -> rel3 T0 T1 T2) :=
  forall r r'(LE: r <3= r'), lf r <3== lf r'.

Lemma monotone3_eq (lf: rel3 T0 T1 T2 -> rel3 T0 T1 T2) :
  monotone3 lf <-> _monotone3 lf.
Proof. unfold monotone3, _monotone3, le3. split; intros; eapply H; eassumption. Qed.

Lemma monotone3_map (lf: rel3 T0 T1 T2 -> rel3 T0 T1 T2)
      (MON: _monotone3 lf) :
  _monotone (fun R0 => @uncurry3 T0 T1 T2 (lf (@curry3 T0 T1 T2 R0))).
Proof.
  red; intros. apply uncurry_map3. apply MON; apply curry_map3; assumption.
Qed.

Lemma monotone3_compose (lf lf': rel3 T0 T1 T2 -> rel3 T0 T1 T2)
      (MON1: monotone3 lf)
      (MON2: monotone3 lf'):
  monotone3 (compose lf lf').
Proof.
  red; intros. eapply MON1. apply IN.
  intros. eapply MON2. apply PR. apply LE.
Qed.

Lemma monotone3_union (lf lf': rel3 T0 T1 T2 -> rel3 T0 T1 T2)
      (MON1: monotone3 lf)
      (MON2: monotone3 lf'):
  monotone3 (lf \4/ lf').
Proof.
  red; intros. destruct IN.
  - left. eapply MON1. apply H. apply LE.
  - right. eapply MON2. apply H. apply LE.
Qed.

Lemma monotone3_inter (lf lf': rel3 T0 T1 T2 -> rel3 T0 T1 T2)
      (MON1: monotone3 lf)
      (MON2: monotone3 lf'):
  monotone3 (lf /4\ lf').
Proof.
  red; intros. destruct IN. split; eauto.
Qed.

Lemma _pind3_mon_gen (lf lf': rel3 T0 T1 T2 -> rel3 T0 T1 T2) r r'
    (LElf: lf <4= lf')
    (LEr: r <3= r'):
  pind3 lf r <3== pind3 lf' r'.
Proof.
  apply curry_map3. red; intros. eapply pind_mon_gen. apply PR.
  - intros. apply LElf, PR0.
  - intros. apply LEr, PR0.
Qed.

Lemma pind3_mon_gen (lf lf': rel3 T0 T1 T2 -> rel3 T0 T1 T2) r r' x0 x1 x2
    (REL: pind3 lf r x0 x1 x2)
    (LElf: lf <4= lf')
    (LEr: r <3= r'):
  pind3 lf' r' x0 x1 x2.
Proof.
  eapply _pind3_mon_gen; [apply LElf | apply LEr | apply REL].
Qed.

Lemma pind3_mon_bot (lf lf': rel3 T0 T1 T2 -> rel3 T0 T1 T2) r' x0 x1 x2
    (REL: pind3 lf bot3 x0 x1 x2)
    (LElf: lf <4= lf'):
  pind3 lf' r' x0 x1 x2.
Proof.
  eapply pind3_mon_gen; [apply REL | apply LElf | intros; contradiction PR].
Qed.

Definition top3 { T0 T1 T2} (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) := True.

Lemma pind3_mon_top (lf lf': rel3 T0 T1 T2 -> rel3 T0 T1 T2) r x0 x1 x2
    (REL: pind3 lf r x0 x1 x2)
    (LElf: lf <4= lf'):
  pind3 lf' top3 x0 x1 x2.
Proof.
  eapply pind3_mon_gen; eauto. red. auto.
Qed.

Lemma upind3_mon_gen (lf lf': rel3 T0 T1 T2 -> rel3 T0 T1 T2) r r' x0 x1 x2
    (REL: upind3 lf r x0 x1 x2)
    (LElf: lf <4= lf')
    (LEr: r <3= r'):
  upind3 lf' r' x0 x1 x2.
Proof.
  destruct REL. split; eauto.
  eapply pind3_mon_gen; [apply H | apply LElf | apply LEr].
Qed.

Lemma upind3_mon_bot (lf lf': rel3 T0 T1 T2 -> rel3 T0 T1 T2) r' x0 x1 x2
    (REL: upind3 lf bot3 x0 x1 x2)
    (LElf: lf <4= lf'):
  upind3 lf' r' x0 x1 x2.
Proof.
  eapply upind3_mon_gen; [apply REL | apply LElf | intros; contradiction PR].
Qed.

Lemma upind3_mon_top (lf lf': rel3 T0 T1 T2 -> rel3 T0 T1 T2) r x0 x1 x2
    (REL: upind3 lf r x0 x1 x2)
    (LElf: lf <4= lf'):
  upind3 lf' top3 x0 x1 x2.
Proof.
  eapply upind3_mon_gen; eauto. red. auto.
Qed.

Section Arg3.

Variable lf : rel3 T0 T1 T2 -> rel3 T0 T1 T2.
Arguments lf : clear implicits.

Theorem _pind3_mon: _monotone3 (pind3 lf).
Proof.
  red; intros. eapply curry_map3, _pind_mon; apply uncurry_map3; assumption.
Qed.

Theorem _pind3_acc: forall
  l r (OBG: forall rr (DEC: rr <3== r) (IH: rr <3== l), pind3 lf rr <3== l),
  pind3 lf r <3== l.
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
  pind3 lf r <3== pind3 lf (upind3 lf r).
Proof.
  intros. apply curry_map3.
  eapply le1_trans; [eapply _pind_mult_strong |].
  apply _pind_mon. intros [] H. apply H.
Qed.

Theorem _pind3_fold: forall r,
  lf (upind3 lf r) <3== pind3 lf r.
Proof.
  intros. apply uncurry_adjoint1_3.
  eapply le1_trans; [| apply _pind_fold]. apply le1_refl.
Qed.

Theorem _pind3_unfold: forall (MON: _monotone3 lf) r,
  pind3 lf r <3== lf (upind3 lf r).
Proof.
  intros. apply curry_adjoint2_3.
  eapply _pind_unfold; apply monotone3_map; assumption.
Qed.

Theorem pind3_acc: forall
  l r (OBG: forall rr (DEC: rr <3= r) (IH: rr <3= l), pind3 lf rr <3= l),
  pind3 lf r <3= l.
Proof.
  apply _pind3_acc.
Qed.

Theorem pind3_mon: monotone3 (pind3 lf).
Proof.
  apply monotone3_eq.
  apply _pind3_mon.
Qed.

Theorem upind3_mon: monotone3 (upind3 lf).
Proof.
  red; intros.
  destruct IN. split; eauto.
  eapply pind3_mon. apply H. apply LE.
Qed.

Theorem pind3_mult_strong: forall r,
  pind3 lf r <3== pind3 lf (upind3 lf r).
Proof.
  apply _pind3_mult_strong.
Qed.

Corollary pind3_mult: forall r,
  pind3 lf r <3= pind3 lf (pind3 lf r).
Proof. intros; eapply pind3_mult_strong in PR. eapply pind3_mon; eauto. intros. destruct PR0. eauto. Qed.

Theorem pind3_fold: forall r,
  lf (upind3 lf r) <3= pind3 lf r.
Proof.
  apply _pind3_fold.
Qed.

Theorem pind3_unfold: forall (MON: monotone3 lf) r,
  pind3 lf r <3= lf (upind3 lf r).
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

(* Global Instance pind3_inst  (lf : rel3 T0 T1 T2->_) r x0 x1 x2 : paco_class (pind3 lf r x0 x1 x2) := *)
(* { pacoacc    := pind3_acc lf; *)
(*   pacomult   := pind3_mult lf; *)
(*   pacofold   := pind3_fold lf; *)
(*   pacounfold := pind3_unfold lf }. *)

End PIND3.

Global Opaque pind3.

#[export] Hint Unfold upind3 : core.
#[export] Hint Resolve pind3_fold : core.
#[export] Hint Unfold monotone3 : core.
