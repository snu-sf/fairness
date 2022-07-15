From sflib Require Import sflib.
Set Implicit Arguments.

(* TODO: definitions copied from Ordinal library *)

Variant double_rel A B (RA: A -> A -> Prop) (RB: B -> B -> Prop)
  : A * B -> A * B -> Prop :=
| double_rel_left a0 a1 b (LT: RA a0 a1): double_rel RA RB (a0, b) (a1, b)
| double_rel_right a b0 b1 (LT: RB b0 b1): double_rel RA RB (a, b0) (a, b1)
.

Lemma double_rel_well_founded A B (RA: A -> A -> Prop) (RB: B -> B -> Prop)
      (WFA: well_founded RA) (WFB: well_founded RB)
  :
  well_founded (double_rel RA RB).
Proof.
  cut (forall a b, Acc (double_rel RA RB) (a, b)).
  { ii. destruct a as [a b]. eapply H. }
  intros a0. pattern a0. revert a0.
  eapply (well_founded_induction WFA).
  intros a0 IHL. intros b0. pattern b0. revert b0.
  eapply (well_founded_induction WFB).
  intros b0 IHR. econs. intros [a1 b1]. i. inv H.
  { eapply IHL; eauto. }
  { eapply IHR; eauto. }
Qed.

Lemma double_well_founded_induction A B (RA: A -> A -> Prop) (RB: B -> B -> Prop)
      (WFA: well_founded RA) (WFB: well_founded RB)
      (P: A -> B -> Prop)
      (IND: forall a1 b1
                   (IHL: forall a0 (LT: RA a0 a1), P a0 b1)
                   (IHR: forall b0 (LT: RB b0 b1), P a1 b0),
          P a1 b1)
  :
  forall a b, P a b.
Proof.
  cut (forall ab, P (fst ab) (snd ab)).
  { i. apply (H (a, b)). }
  intros ab. pattern ab. revert ab.
  eapply (well_founded_induction (double_rel_well_founded WFA WFB)).
  intros [a b] ?. ss. eapply IND.
  { i. eapply (H (a0, b)). econstructor 1. auto. }
  { i. eapply (H (a, b0)). econstructor 2. auto. }
Qed.
