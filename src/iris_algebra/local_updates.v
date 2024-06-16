From Fairness Require Import cmra.
From iris.prelude Require Import prelude options.

Local Open Scope iris_algebra_scope.

(** * Local updates *)
Definition local_update {A : cmra} (x y : A * A) := ∀ mz,
  ✓ x.1 → x.1 = x.2 ⋅? mz → ✓ y.1 ∧ y.1 = y.2 ⋅? mz.
Global Instance: Params (@local_update) 1 := {}.
Infix "~l~>" := local_update (at level 70) : iris_algebra_scope.

Section updates.
  Context {A : cmra}.
  Implicit Types x y : A.

  Global Instance local_update_proper :
    Proper ((=) ==> (=) ==> iff) (@local_update A).
  Proof. unfold local_update. by repeat intro; setoid_subst. Qed.

  Global Instance local_update_preorder : PreOrder (@local_update A).
  Proof. split; unfold local_update; red; naive_solver. Qed.

  Lemma exclusive_local_update `{!Exclusive y} x x' : ✓ x' → (x,y) ~l~> (x',x').
  Proof.
    intros ? mz Hxv Hx; simpl in *.
    move: Hxv; rewrite Hx; move=> /exclusive_opM=> ->; split; auto.
  Qed.

  Lemma op_local_update x y z :
    (✓ x → ✓ (z ⋅ x)) → (x,y) ~l~> (z ⋅ x, z ⋅ y).
  Proof.
    intros Hv mz Hxv Hx; simpl in *; split; [by auto|].
    by rewrite Hx -cmra_op_opM_assoc.
  Qed.
  Lemma op_local_update_discrete  x y z :
    (✓ x → ✓ (z ⋅ x)) → (x,y) ~l~> (z ⋅ x, z ⋅ y).
  Proof.
    intros; apply op_local_update=> n. auto.
  Qed.

  Lemma op_local_update_frame x y x' y' yf :
    (x,y) ~l~> (x',y') → (x,y ⋅ yf) ~l~> (x', y' ⋅ yf).
  Proof.
    intros Hup mz Hxv Hx; simpl in *.
    destruct (Hup (Some (yf ⋅? mz))); [done|by rewrite /= -cmra_op_opM_assoc|].
    by rewrite cmra_op_opM_assoc.
  Qed.

  Lemma cancel_local_update x y z `{!Cancelable x} :
    (x ⋅ y, x ⋅ z) ~l~> (y, z).
  Proof.
    intros f ? Heq. split; first by eapply cmra_valid_op_r. simpl in *.
    apply (cancelable x); [done..|].
    by rewrite -cmra_op_opM_assoc.
  Qed.

  Lemma replace_local_update x y `{!IdFree x} :
    ✓ y → (x, x) ~l~> (y, y).
  Proof.
    intros ? mz ? Heq; simpl in *; split; first done.
    destruct mz as [z|]; [|done]. by destruct (id_free_r x z).
  Qed.

  Lemma core_id_local_update x y z `{!CoreId y} :
    y ≼ x → (x, z) ~l~> (x, z ⋅ y).
  Proof.
    intros Hincl mf ? Heq; simpl in *; split; first done.
    rewrite [x](core_id_extract y x) // Heq. destruct mf as [f|]; last done.
    simpl. rewrite -assoc [f ⋅ y]comm assoc //.
  Qed.

  Lemma local_update_discrete  (x y x' y' : A) :
    (x,y) ~l~> (x',y') ↔ ∀ mz, ✓ x → x = y ⋅? mz → ✓ x' ∧ x' = y' ⋅? mz.
  Proof. rewrite /local_update /=. done. Qed.

  Lemma local_update_valid x y x' y' :
    (✓ x → ✓ y → Some y ≼ Some x → (x,y) ~l~> (x',y')) →
    (x,y) ~l~> (x',y').
  Proof.
    intros Hup mz Hmz Hz; simpl in *. apply Hup; auto.
    - move: Hmz; rewrite Hz. destruct mz; simpl; eauto using cmra_valid_op_l.
    - apply Some_included_opM. eauto.
  Qed.

  Lemma local_update_total_valid `{!CmraTotal A} x y x' y' :
    (✓ x → ✓ y → y ≼ x → (x,y) ~l~> (x',y')) → (x,y) ~l~> (x',y').
  Proof.
    intros Hup. apply local_update_valid=> ?? Hincl. apply Hup; auto.
    by apply Some_included_total.
  Qed.
End updates.

Section updates_unital.
  Context {A : ucmra}.
  Implicit Types x y : A.

  Lemma local_update_unital x y x' y' :
    (x,y) ~l~> (x',y') ↔ ∀ z,
      ✓ x → x = y ⋅ z → ✓ x' ∧ x' = y' ⋅ z.
  Proof.
    split.
    - intros Hup z. apply (Hup (Some z)).
    - intros Hup [z|]; simpl; [by auto|].
      rewrite -(right_id ε op y) -(right_id ε op y'). auto.
  Qed.

  Lemma local_update_unital_discrete  (x y x' y' : A) :
    (x,y) ~l~> (x',y') ↔ ∀ z, ✓ x → x = y ⋅ z → ✓ x' ∧ x' = y' ⋅ z.
  Proof.
    rewrite local_update_discrete. split.
    - intros Hup z. apply (Hup (Some z)).
    - intros Hup [z|]; simpl; [by auto|].
      rewrite -(right_id ε op y) -(right_id ε op y'). auto.
  Qed.

  Lemma cancel_local_update_unit x y `{!Cancelable x} :
    (x ⋅ y, x) ~l~> (y, ε).
  Proof. rewrite -{2}(right_id ε op x). by apply cancel_local_update. Qed.
End updates_unital.

(** * Unit *)
Lemma unit_local_update (x y x' y' : unit) : (x, y) ~l~> (x', y').
Proof. destruct x,y,x',y'; reflexivity. Qed.

(** * Product *)
Lemma prod_local_update {A B : cmra} (x y x' y' : A * B) :
  (x.1,y.1) ~l~> (x'.1,y'.1) → (x.2,y.2) ~l~> (x'.2,y'.2) →
  (x,y) ~l~> (x',y').
Proof.
  intros Hup1 Hup2 mz [??].
  destruct x as [x1 x2], y as [y1 y2]; simpl in *.
  intros EQ.
  destruct (Hup1 (fst <$> mz)); [done| |].
  { destruct mz as [[mz1 mz2]|]; simpl in *; try rewrite -pair_op in EQ.
    all: inversion_clear EQ; done.
  }
  destruct (Hup2 (snd <$> mz)); [done| |].
  { destruct mz as [[mz1 mz2]|]; simpl in *; try rewrite -pair_op in EQ.
    all: inversion_clear EQ; done.
  }
  destruct x' as [x'1 x'2], y' as [y'1 y'2]; simpl in *.
  destruct mz as [[mz1 mz2]|]; simpl in *; try rewrite -pair_op; try rewrite -pair_op in EQ.
  all: inversion_clear EQ.
  all: split; [done|f_equal; done].
Qed.

Lemma prod_local_update' {A B : cmra} (x1 y1 x1' y1' : A) (x2 y2 x2' y2' : B) :
  (x1,y1) ~l~> (x1',y1') → (x2,y2) ~l~> (x2',y2') →
  ((x1,x2),(y1,y2)) ~l~> ((x1',x2'),(y1',y2')).
Proof. intros. by apply prod_local_update. Qed.
Lemma prod_local_update_1 {A B : cmra} (x1 y1 x1' y1' : A) (x2 y2 : B) :
  (x1,y1) ~l~> (x1',y1') → ((x1,x2),(y1,y2)) ~l~> ((x1',x2),(y1',y2)).
Proof. intros. by apply prod_local_update. Qed.
Lemma prod_local_update_2 {A B : cmra} (x1 y1 : A) (x2 y2 x2' y2' : B) :
  (x2,y2) ~l~> (x2',y2') → ((x1,x2),(y1,y2)) ~l~> ((x1,x2'),(y1,y2')).
Proof. intros. by apply prod_local_update. Qed.

(** * Option *)
Lemma option_local_update {A : cmra} (x y x' y' : A) :
  (x, y) ~l~> (x',y') →
  (Some x, Some y) ~l~> (Some x', Some y').
Proof.
  intros Hup. apply local_update_unital=> mz Hxv Hx; simpl in *.
  destruct (Hup mz); first done.
  { destruct mz as [?|]; inversion_clear Hx; auto. }
  split; first done. destruct mz as [?|]; simpl in *; auto.
  - rewrite -Some_op. f_equal. done.
  - rewrite (right_id _). f_equal. done.
Qed.

Lemma option_local_update_None {A: ucmra} (x x' y': A):
  (x, ε) ~l~> (x', y') ->
  (Some x, None) ~l~> (Some x', Some y').
Proof.
  intros Hup. apply local_update_unital=> mz.
  rewrite left_id=> ? <-.
  destruct (Hup (Some x)); simpl in *; first done.
  - by rewrite left_id.
  - split; first done. rewrite -Some_op. f_equal. done.
Qed.

Lemma alloc_option_local_update {A : cmra} (x : A) y :
  ✓ x →
  (None, y) ~l~> (Some x, Some x).
Proof.
  move=>Hx. apply local_update_unital=> z _ /= Heq. split.
  { rewrite Some_valid. done. }
  destruct z as [z|]; last done. destruct y; inversion Heq.
Qed.

Lemma delete_option_local_update {A : cmra} (x : option A) (y : A) :
  Exclusive y → (x, Some y) ~l~> (None, None).
Proof.
  move=>Hex. apply local_update_unital=> z /= Hy Heq. split; first done.
  destruct z as [z|]; last done. exfalso.
  move: Hy. rewrite Heq /= -Some_op=>Hy. eapply Hex.
  eapply Hy.
Qed.

Lemma delete_option_local_update_cancelable {A : cmra} (mx : option A) :
  Cancelable mx → (mx, mx) ~l~> (None, None).
Proof.
  intros ?. apply local_update_unital=> mf /= Hmx Heq. split; first done.
  rewrite left_id. eapply (cancelable mx); try done; by rewrite right_id_L.
Qed.
