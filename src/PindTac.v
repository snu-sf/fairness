From sflib Require Import sflib.
From Paco Require Import paco.

From Fairness Require Import pind.
From Paco Require Import pacotac_internal.

Set Implicit Arguments.


Ltac pattern_args a x n :=
  match n with
  | 0 =>
      x
  | S ?n' =>
      match x with
      | ?hd ?tl =>
          let hd' := pattern_args a hd n' in
          let tl' := (eval pattern a in tl) in
          constr:(hd' tl')
      end
  end.

Ltac patterning n :=
  let a := fresh "a" in
  intros a;
  match goal with
  | |- ?H -> ?G =>
      let H' := pattern_args a H n in
      let G' := (eval pattern a in G) in
      change (H' -> G')
  end;
  revert a
.

Ltac pattern_n_aux n tac :=
  match n with
  | 0 =>
      match goal with
      | |- ?G =>
          let G' := tac G in
          change G'
      end
  | S ?n' =>
      let a := fresh "a" in
      intros a;
      let tac' := ltac:(fun x =>
                          let t := (eval pattern a in x) in
                          match constr:(t) with
                          | ?f ?arg =>
                              let f' := (tac f) in
                              constr:(f' arg)
                          end) in
      pattern_n_aux n' tac';
      revert a
  end.
Ltac pattern_n n := pattern_n_aux n ltac:(fun x => constr:(x)).

Lemma uncurry1_always
      (A0: Type)
      (P: forall (a0: @A0), Prop)
      (H: forall (a: @sig1T A0), @uncurry1 A0 P a)
  :
  forall (a0: @A0), P a0.
Proof.
  exact (fun a0 => H (@exist1T _ a0)).
Qed.

Lemma uncurry2_always
      (A0: Type)
      (A1: forall (a0: @A0), Type)
      (P: forall (a0: @A0) (a1: @A1 a0), Prop)
      (H: forall (a: @sig2T A0 A1), @uncurry2 A0 A1 P a)
  :
  forall (a0: @A0) (a1: @A1 a0), P a0 a1.
Proof.
  exact (fun a0 a1 => H (@exist2T _ _ a0 a1)).
Qed.

Lemma uncurry3_always
      (A0: Type)
      (A1: forall (a0: @A0), Type)
      (A2: forall (a0: @A0) (a1: @A1 a0), Type)
      (P: forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1), Prop)
      (H: forall (a: @sig3T A0 A1 A2), @uncurry3 A0 A1 A2 P a)
  :
  forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1), P a0 a1 a2.
Proof.
  exact (fun a0 a1 a2 => H (@exist3T _ _ _ a0 a1 a2)).
Qed.

Lemma uncurry4_always
      (A0: Type)
      (A1: forall (a0: @A0), Type)
      (A2: forall (a0: @A0) (a1: @A1 a0), Type)
      (A3: forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1), Type)
      (P: forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1) (a3: @A3 a0 a1 a2), Prop)
      (H: forall (a: @sig4T A0 A1 A2 A3), @uncurry4 A0 A1 A2 A3 P a)
  :
  forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1) (a3: @A3 a0 a1 a2), P a0 a1 a2 a3.
Proof.
  exact (fun a0 a1 a2 a3 => H (@exist4T _ _ _ _ a0 a1 a2 a3)).
Qed.

Lemma uncurry5_always
      (A0: Type)
      (A1: forall (a0: @A0), Type)
      (A2: forall (a0: @A0) (a1: @A1 a0), Type)
      (A3: forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1), Type)
      (A4: forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1) (a3: @A3 a0 a1 a2), Type)
      (P: forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1) (a3: @A3 a0 a1 a2) (a4: @A4 a0 a1 a2 a3), Prop)
      (H: forall (a: @sig5T A0 A1 A2 A3 A4), @uncurry5 A0 A1 A2 A3 A4 P a)
  :
  forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1) (a3: @A3 a0 a1 a2) (a4: @A4 a0 a1 a2 a3), P a0 a1 a2 a3 a4.
Proof.
  exact (fun a0 a1 a2 a3 a4 => H (@exist5T _ _ _ _ _ a0 a1 a2 a3 a4)).
Qed.

Lemma uncurry6_always
      (A0: Type)
      (A1: forall (a0: @A0), Type)
      (A2: forall (a0: @A0) (a1: @A1 a0), Type)
      (A3: forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1), Type)
      (A4: forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1) (a3: @A3 a0 a1 a2), Type)
      (A5: forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1) (a3: @A3 a0 a1 a2) (a4: @A4 a0 a1 a2 a3), Type)
      (P: forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1) (a3: @A3 a0 a1 a2) (a4: @A4 a0 a1 a2 a3) (a5: @A5 a0 a1 a2 a3 a4), Prop)
      (H: forall (a: @sig6T A0 A1 A2 A3 A4 A5), @uncurry6 A0 A1 A2 A3 A4 A5 P a)
  :
  forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1) (a3: @A3 a0 a1 a2) (a4: @A4 a0 a1 a2 a3) (a5: @A5 a0 a1 a2 a3 a4), P a0 a1 a2 a3 a4 a5.
Proof.
  exact (fun a0 a1 a2 a3 a4 a5 => H (@exist6T _ _ _ _ _ _ a0 a1 a2 a3 a4 a5)).
Qed.

Lemma uncurry7_always
      (A0: Type)
      (A1: forall (a0: @A0), Type)
      (A2: forall (a0: @A0) (a1: @A1 a0), Type)
      (A3: forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1), Type)
      (A4: forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1) (a3: @A3 a0 a1 a2), Type)
      (A5: forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1) (a3: @A3 a0 a1 a2) (a4: @A4 a0 a1 a2 a3), Type)
      (A6: forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1) (a3: @A3 a0 a1 a2) (a4: @A4 a0 a1 a2 a3) (a5: @A5 a0 a1 a2 a3 a4), Type)
      (P: forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1) (a3: @A3 a0 a1 a2) (a4: @A4 a0 a1 a2 a3) (a5: @A5 a0 a1 a2 a3 a4) (a6: @A6 a0 a1 a2 a3 a4 a5), Prop)
      (H: forall (a: @sig7T A0 A1 A2 A3 A4 A5 A6), @uncurry7 A0 A1 A2 A3 A4 A5 A6 P a)
  :
  forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1) (a3: @A3 a0 a1 a2) (a4: @A4 a0 a1 a2 a3) (a5: @A5 a0 a1 a2 a3 a4) (a6: @A6 a0 a1 a2 a3 a4 a5), P a0 a1 a2 a3 a4 a5 a6.
Proof.
  exact (fun a0 a1 a2 a3 a4 a5 a6 => H (@exist7T _ _ _ _ _ _ _ a0 a1 a2 a3 a4 a5 a6)).
Qed.

Lemma uncurry8_always
      (A0: Type)
      (A1: forall (a0: @A0), Type)
      (A2: forall (a0: @A0) (a1: @A1 a0), Type)
      (A3: forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1), Type)
      (A4: forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1) (a3: @A3 a0 a1 a2), Type)
      (A5: forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1) (a3: @A3 a0 a1 a2) (a4: @A4 a0 a1 a2 a3), Type)
      (A6: forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1) (a3: @A3 a0 a1 a2) (a4: @A4 a0 a1 a2 a3) (a5: @A5 a0 a1 a2 a3 a4), Type)
      (A7: forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1) (a3: @A3 a0 a1 a2) (a4: @A4 a0 a1 a2 a3) (a5: @A5 a0 a1 a2 a3 a4) (a6: @A6 a0 a1 a2 a3 a4 a5), Type)
      (P: forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1) (a3: @A3 a0 a1 a2) (a4: @A4 a0 a1 a2 a3) (a5: @A5 a0 a1 a2 a3 a4) (a6: @A6 a0 a1 a2 a3 a4 a5) (a7: @A7 a0 a1 a2 a3 a4 a5 a6), Prop)
      (H: forall (a: @sig8T A0 A1 A2 A3 A4 A5 A6 A7), @uncurry8 A0 A1 A2 A3 A4 A5 A6 A7 P a)
  :
  forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1) (a3: @A3 a0 a1 a2) (a4: @A4 a0 a1 a2 a3) (a5: @A5 a0 a1 a2 a3 a4) (a6: @A6 a0 a1 a2 a3 a4 a5) (a7: @A7 a0 a1 a2 a3 a4 a5 a6), P a0 a1 a2 a3 a4 a5 a6 a7.
Proof.
  exact (fun a0 a1 a2 a3 a4 a5 a6 a7 => H (@exist8T _ _ _ _ _ _ _ _ a0 a1 a2 a3 a4 a5 a6 a7)).
Qed.

Lemma uncurry9_always
      (A0: Type)
      (A1: forall (a0: @A0), Type)
      (A2: forall (a0: @A0) (a1: @A1 a0), Type)
      (A3: forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1), Type)
      (A4: forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1) (a3: @A3 a0 a1 a2), Type)
      (A5: forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1) (a3: @A3 a0 a1 a2) (a4: @A4 a0 a1 a2 a3), Type)
      (A6: forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1) (a3: @A3 a0 a1 a2) (a4: @A4 a0 a1 a2 a3) (a5: @A5 a0 a1 a2 a3 a4), Type)
      (A7: forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1) (a3: @A3 a0 a1 a2) (a4: @A4 a0 a1 a2 a3) (a5: @A5 a0 a1 a2 a3 a4) (a6: @A6 a0 a1 a2 a3 a4 a5), Type)
      (A8: forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1) (a3: @A3 a0 a1 a2) (a4: @A4 a0 a1 a2 a3) (a5: @A5 a0 a1 a2 a3 a4) (a6: @A6 a0 a1 a2 a3 a4 a5) (a7: @A7 a0 a1 a2 a3 a4 a5 a6), Type)
      (P: forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1) (a3: @A3 a0 a1 a2) (a4: @A4 a0 a1 a2 a3) (a5: @A5 a0 a1 a2 a3 a4) (a6: @A6 a0 a1 a2 a3 a4 a5) (a7: @A7 a0 a1 a2 a3 a4 a5 a6) (a8: @A8 a0 a1 a2 a3 a4 a5 a6 a7), Prop)
      (H: forall (a: @sig9T A0 A1 A2 A3 A4 A5 A6 A7 A8), @uncurry9 A0 A1 A2 A3 A4 A5 A6 A7 A8 P a)
  :
  forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1) (a3: @A3 a0 a1 a2) (a4: @A4 a0 a1 a2 a3) (a5: @A5 a0 a1 a2 a3 a4) (a6: @A6 a0 a1 a2 a3 a4 a5) (a7: @A7 a0 a1 a2 a3 a4 a5 a6) (a8: @A8 a0 a1 a2 a3 a4 a5 a6 a7), P a0 a1 a2 a3 a4 a5 a6 a7 a8.
Proof.
  exact (fun a0 a1 a2 a3 a4 a5 a6 a7 a8 => H (@exist9T _ _ _ _ _ _ _ _ _ a0 a1 a2 a3 a4 a5 a6 a7 a8)).
Qed.

Lemma uncurry10_always
      (A0: Type)
      (A1: forall (a0: @A0), Type)
      (A2: forall (a0: @A0) (a1: @A1 a0), Type)
      (A3: forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1), Type)
      (A4: forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1) (a3: @A3 a0 a1 a2), Type)
      (A5: forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1) (a3: @A3 a0 a1 a2) (a4: @A4 a0 a1 a2 a3), Type)
      (A6: forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1) (a3: @A3 a0 a1 a2) (a4: @A4 a0 a1 a2 a3) (a5: @A5 a0 a1 a2 a3 a4), Type)
      (A7: forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1) (a3: @A3 a0 a1 a2) (a4: @A4 a0 a1 a2 a3) (a5: @A5 a0 a1 a2 a3 a4) (a6: @A6 a0 a1 a2 a3 a4 a5), Type)
      (A8: forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1) (a3: @A3 a0 a1 a2) (a4: @A4 a0 a1 a2 a3) (a5: @A5 a0 a1 a2 a3 a4) (a6: @A6 a0 a1 a2 a3 a4 a5) (a7: @A7 a0 a1 a2 a3 a4 a5 a6), Type)
      (A9: forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1) (a3: @A3 a0 a1 a2) (a4: @A4 a0 a1 a2 a3) (a5: @A5 a0 a1 a2 a3 a4) (a6: @A6 a0 a1 a2 a3 a4 a5) (a7: @A7 a0 a1 a2 a3 a4 a5 a6) (a8: @A8 a0 a1 a2 a3 a4 a5 a6 a7), Type)
      (P: forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1) (a3: @A3 a0 a1 a2) (a4: @A4 a0 a1 a2 a3) (a5: @A5 a0 a1 a2 a3 a4) (a6: @A6 a0 a1 a2 a3 a4 a5) (a7: @A7 a0 a1 a2 a3 a4 a5 a6) (a8: @A8 a0 a1 a2 a3 a4 a5 a6 a7) (a9: @A9 a0 a1 a2 a3 a4 a5 a6 a7 a8), Prop)
      (H: forall (a: @sig10T A0 A1 A2 A3 A4 A5 A6 A7 A8 A9), @uncurry10 A0 A1 A2 A3 A4 A5 A6 A7 A8 A9 P a)
  :
  forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1) (a3: @A3 a0 a1 a2) (a4: @A4 a0 a1 a2 a3) (a5: @A5 a0 a1 a2 a3 a4) (a6: @A6 a0 a1 a2 a3 a4 a5) (a7: @A7 a0 a1 a2 a3 a4 a5 a6) (a8: @A8 a0 a1 a2 a3 a4 a5 a6 a7) (a9: @A9 a0 a1 a2 a3 a4 a5 a6 a7 a8), P a0 a1 a2 a3 a4 a5 a6 a7 a8 a9.
Proof.
  exact (fun a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 => H (@exist10T _ _ _ _ _ _ _ _ _ _ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9)).
Qed.

Lemma uncurry11_always
      (A0: Type)
      (A1: forall (a0: @A0), Type)
      (A2: forall (a0: @A0) (a1: @A1 a0), Type)
      (A3: forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1), Type)
      (A4: forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1) (a3: @A3 a0 a1 a2), Type)
      (A5: forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1) (a3: @A3 a0 a1 a2) (a4: @A4 a0 a1 a2 a3), Type)
      (A6: forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1) (a3: @A3 a0 a1 a2) (a4: @A4 a0 a1 a2 a3) (a5: @A5 a0 a1 a2 a3 a4), Type)
      (A7: forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1) (a3: @A3 a0 a1 a2) (a4: @A4 a0 a1 a2 a3) (a5: @A5 a0 a1 a2 a3 a4) (a6: @A6 a0 a1 a2 a3 a4 a5), Type)
      (A8: forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1) (a3: @A3 a0 a1 a2) (a4: @A4 a0 a1 a2 a3) (a5: @A5 a0 a1 a2 a3 a4) (a6: @A6 a0 a1 a2 a3 a4 a5) (a7: @A7 a0 a1 a2 a3 a4 a5 a6), Type)
      (A9: forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1) (a3: @A3 a0 a1 a2) (a4: @A4 a0 a1 a2 a3) (a5: @A5 a0 a1 a2 a3 a4) (a6: @A6 a0 a1 a2 a3 a4 a5) (a7: @A7 a0 a1 a2 a3 a4 a5 a6) (a8: @A8 a0 a1 a2 a3 a4 a5 a6 a7), Type)
      (A10: forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1) (a3: @A3 a0 a1 a2) (a4: @A4 a0 a1 a2 a3) (a5: @A5 a0 a1 a2 a3 a4) (a6: @A6 a0 a1 a2 a3 a4 a5) (a7: @A7 a0 a1 a2 a3 a4 a5 a6) (a8: @A8 a0 a1 a2 a3 a4 a5 a6 a7) (a9: @A9 a0 a1 a2 a3 a4 a5 a6 a7 a8), Type)
      (P: forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1) (a3: @A3 a0 a1 a2) (a4: @A4 a0 a1 a2 a3) (a5: @A5 a0 a1 a2 a3 a4) (a6: @A6 a0 a1 a2 a3 a4 a5) (a7: @A7 a0 a1 a2 a3 a4 a5 a6) (a8: @A8 a0 a1 a2 a3 a4 a5 a6 a7) (a9: @A9 a0 a1 a2 a3 a4 a5 a6 a7 a8) (a10: @A10 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9), Prop)
      (H: forall (a: @sig11T A0 A1 A2 A3 A4 A5 A6 A7 A8 A9 A10), @uncurry11 A0 A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 P a)
  :
  forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1) (a3: @A3 a0 a1 a2) (a4: @A4 a0 a1 a2 a3) (a5: @A5 a0 a1 a2 a3 a4) (a6: @A6 a0 a1 a2 a3 a4 a5) (a7: @A7 a0 a1 a2 a3 a4 a5 a6) (a8: @A8 a0 a1 a2 a3 a4 a5 a6 a7) (a9: @A9 a0 a1 a2 a3 a4 a5 a6 a7 a8) (a10: @A10 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9), P a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10.
Proof.
  exact (fun a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 => H (@exist11T _ _ _ _ _ _ _ _ _ _ _ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10)).
Qed.

Ltac currying1 tac :=
  pattern_n 1; refine (@uncurry1_always _ _ _); unfold uncurry1;
  tac;
  let r := fresh "r" in
  let LE := fresh "LE" in
  let IH := fresh "IH" in
  let IHaux := fresh "IHaux" in
  intros r LE IHaux;
  pose proof (IH := @curry_map1 _ _ _ IHaux); clear IHaux; unfold curry1, le1 in IH; simpl in IH;
  refine (@curry_map_rev1 _ _ _ _); unfold curry1, le1; simpl.

Ltac currying2 tac :=
  pattern_n 2; refine (@uncurry2_always _ _ _ _); unfold uncurry2;
  tac;
  let r := fresh "r" in
  let LE := fresh "LE" in
  let IH := fresh "IH" in
  let IHaux := fresh "IHaux" in
  intros r LE IHaux;
  pose proof (IH := @curry_map2 _ _ _ _ IHaux); clear IHaux; unfold curry2, le2 in IH; simpl in IH;
  refine (@curry_map_rev2 _ _ _ _ _); unfold curry2, le2; simpl.

Ltac currying3 tac :=
  pattern_n 3; refine (@uncurry3_always _ _ _ _ _); unfold uncurry3;
  tac;
  let r := fresh "r" in
  let LE := fresh "LE" in
  let IH := fresh "IH" in
  let IHaux := fresh "IHaux" in
  intros r LE IHaux;
  pose proof (IH := @curry_map3 _ _ _ _ _ IHaux); clear IHaux; unfold curry3, le3 in IH; simpl in IH;
  refine (@curry_map_rev3 _ _ _ _ _ _); unfold curry3, le3; simpl.

Ltac currying4 tac :=
  pattern_n 4; refine (@uncurry4_always _ _ _ _ _ _); unfold uncurry4;
  tac;
  let r := fresh "r" in
  let LE := fresh "LE" in
  let IH := fresh "IH" in
  let IHaux := fresh "IHaux" in
  intros r LE IHaux;
  pose proof (IH := @curry_map4 _ _ _ _ _ _ IHaux); clear IHaux; unfold curry4, le4 in IH; simpl in IH;
  refine (@curry_map_rev4 _ _ _ _ _ _ _); unfold curry4, le4; simpl.

Ltac currying5 tac :=
  pattern_n 5; refine (@uncurry5_always _ _ _ _ _ _ _); unfold uncurry5;
  tac;
  let r := fresh "r" in
  let LE := fresh "LE" in
  let IH := fresh "IH" in
  let IHaux := fresh "IHaux" in
  intros r LE IHaux;
  pose proof (IH := @curry_map5 _ _ _ _ _ _ _ IHaux); clear IHaux; unfold curry5, le5 in IH; simpl in IH;
  refine (@curry_map_rev5 _ _ _ _ _ _ _ _); unfold curry5, le5; simpl.

Ltac currying6 tac :=
  pattern_n 6; refine (@uncurry6_always _ _ _ _ _ _ _ _); unfold uncurry6;
  tac;
  let r := fresh "r" in
  let LE := fresh "LE" in
  let IH := fresh "IH" in
  let IHaux := fresh "IHaux" in
  intros r LE IHaux;
  pose proof (IH := @curry_map6 _ _ _ _ _ _ _ _ IHaux); clear IHaux; unfold curry6, le6 in IH; simpl in IH;
  refine (@curry_map_rev6 _ _ _ _ _ _ _ _ _); unfold curry6, le6; simpl.

Ltac currying7 tac :=
  pattern_n 7; refine (@uncurry7_always _ _ _ _ _ _ _ _ _); unfold uncurry7;
  tac;
  let r := fresh "r" in
  let LE := fresh "LE" in
  let IH := fresh "IH" in
  let IHaux := fresh "IHaux" in
  intros r LE IHaux;
  pose proof (IH := @curry_map7 _ _ _ _ _ _ _ _ _ IHaux); clear IHaux; unfold curry7, le7 in IH; simpl in IH;
  refine (@curry_map_rev7 _ _ _ _ _ _ _ _ _ _); unfold curry7, le7; simpl.

Ltac currying8 tac :=
  pattern_n 8; refine (@uncurry8_always _ _ _ _ _ _ _ _ _ _); unfold uncurry8;
  tac;
  let r := fresh "r" in
  let LE := fresh "LE" in
  let IH := fresh "IH" in
  let IHaux := fresh "IHaux" in
  intros r LE IHaux;
  pose proof (IH := @curry_map8 _ _ _ _ _ _ _ _ _ _ IHaux); clear IHaux; unfold curry8, le8 in IH; simpl in IH;
  refine (@curry_map_rev8 _ _ _ _ _ _ _ _ _ _ _); unfold curry8, le8; simpl.

Ltac currying9 tac :=
  pattern_n 9; refine (@uncurry9_always _ _ _ _ _ _ _ _ _ _ _); unfold uncurry9;
  tac;
  let r := fresh "r" in
  let LE := fresh "LE" in
  let IH := fresh "IH" in
  let IHaux := fresh "IHaux" in
  intros r LE IHaux;
  pose proof (IH := @curry_map9 _ _ _ _ _ _ _ _ _ _ _ IHaux); clear IHaux; unfold curry9, le9 in IH; simpl in IH;
  refine (@curry_map_rev9 _ _ _ _ _ _ _ _ _ _ _ _); unfold curry9, le9; simpl
.

Ltac currying10 tac :=
  pattern_n 10; refine (@uncurry10_always _ _ _ _ _ _ _ _ _ _ _ _); unfold uncurry10;
  tac;
  let r := fresh "r" in
  let LE := fresh "LE" in
  let IH := fresh "IH" in
  let IHaux := fresh "IHaux" in
  intros r LE IHaux;
  pose proof (IH := @curry_map10 _ _ _ _ _ _ _ _ _ _ _ _ IHaux); clear IHaux; unfold curry10, le10 in IH; simpl in IH;
  refine (@curry_map_rev10 _ _ _ _ _ _ _ _ _ _ _ _ _); unfold curry10, le10; simpl
.

Ltac currying11 tac :=
  pattern_n 11; refine (@uncurry11_always _ _ _ _ _ _ _ _ _ _ _ _ _); unfold uncurry11;
  tac;
  let r := fresh "r" in
  let LE := fresh "LE" in
  let IH := fresh "IH" in
  let IHaux := fresh "IHaux" in
  intros r LE IHaux;
  pose proof (IH := @curry_map11 _ _ _ _ _ _ _ _ _ _ _ _ _ IHaux); clear IHaux; unfold curry11, le11 in IH; simpl in IH;
  refine (@curry_map_rev11 _ _ _ _ _ _ _ _ _ _ _ _ _ _); unfold curry11, le11; simpl
.

Ltac currying n tac :=
  match n with
  | 1 => currying1 tac
  | 2 => currying2 tac
  | 3 => currying3 tac
  | 4 => currying4 tac
  | 5 => currying5 tac
  | 6 => currying6 tac
  | 7 => currying7 tac
  | 8 => currying8 tac
  | 9 => currying9 tac
  | 10 => currying10 tac
  | 11 => currying11 tac
  end.


Module TEST.
  Section TAC2.
    Variable T0: Type.
    Variable T1: forall (x0: T0), Type.
    Let rel := forall (x0: T0) (x1: T1 x0), Prop.

    Variable gf: rel -> rel.
    Hypothesis MON: monotone2 gf.
    Hint Resolve MON: paco.

    Lemma pind2_acc_gen
          (A: Type)
          (f0: forall (a: A), T0)
          (f1: forall (a: A), T1 (f0 a))
          r0 (q: A -> Prop)
          (IND: forall r1
                       (LE: r1 <2= r0)
                       (IH: forall a, r1 (f0 a) (f1 a) -> q a),
            forall a, pind2 gf r1 (f0 a) (f1 a) -> q a)
      :
      forall a, pind2 gf r0 (f0 a) (f1 a) -> q a.
    Proof.
      cut ((pind2 gf r0) <2= curry2 (fun x => forall a (EQ: @exist2T T0 T1 (f0 a) (f1 a) = x), q a)).
      { exact (fun P a H => uncurry_adjoint2_2 P (@exist2T T0 T1 (f0 a) (f1 a)) H a eq_refl). }
      { exact (@pind2_acc T0 T1 gf (curry2 (fun x => forall a (EQ: @exist2T T0 T1 (f0 a) (f1 a) = x), q a)) r0 (fun rr LE IH => @uncurry_adjoint1_2 T0 T1 (pind2 gf rr) (fun x => forall a (EQ: @exist2T T0 T1 (f0 a) (f1 a) = x), q a) (fun x PR a EQ => IND rr LE (fun a H => IH (f0 a) (f1 a) H a eq_refl) a (@eq_rect _ _ (uncurry2 (pind2 gf rr)) PR _ (eq_sym EQ))))).
      }
    Qed.

    Ltac pind2_gen := patterning 2; refine (@pind2_acc_gen _ _ _ _ _ _).

    Ltac pinduction2 n := currying n pind2_gen.

    Lemma pind2_acc_test3
          (A0: Type)
          (A1: forall (a0: @A0), Type)
          (A2: forall (a0: @A0) (a1: @A1 a0), Type)

          (f0: forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1), @T0)
          (f1: forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1), @T1 (@f0 a0 a1 a2))
          r0 (q: forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1), Prop)
          (IND: forall r1
                       (LE: r1 <2= r0)
                       (IH: forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1), r1 (@f0 a0 a1 a2) (@f1 a0 a1 a2) -> @q a0 a1 a2),
            forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1), pind2 gf r1 (@f0 a0 a1 a2) (@f1 a0 a1 a2) -> @q a0 a1 a2)
      :
      forall (a0: @A0) (a1: @A1 a0) (a2: @A2 a0 a1), pind2 gf r0 (@f0 a0 a1 a2) (@f1 a0 a1 a2) -> @q a0 a1 a2.
    Proof.
      pinduction2 3. eauto.
    Qed.
  End TAC2.
End TEST.
