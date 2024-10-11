Require Import String Program.
From Fairness Require Export TRed.
From Fairness Require Import ITreeLib Event.

Definition itree_class: red_class := red_class_cons "itree".
Global Opaque itree_class.
Definition itree_unfold: red_class := red_class_cons "itree_unfold".
Global Opaque itree_unfold.
Definition itree_option: red_class := red_class_cons "itree_option".
Global Opaque itree_option.

#[export] Instance incl_itree_unfold_itree_class: red_db_incl itree_unfold itree_class := mk_red_db_incl.

#[export] Instance focus_bind E X Y (itr: itree E X) (ktr: X -> itree E Y)
  : red_db itree_class (itr >>= ktr) :=
  mk_red_db _ _ (@bind_ext E X Y) itr (inr itree_unfold).

#[export] Instance focus_option ID E `{H: @eventE ID -< E} R (r: option R)
  : red_db itree_unfold (@unwrap ID E H R r) :=
  mk_red_db _ _ (@f_equal _ _ (@unwrap ID E H R)) r (inr itree_option).

#[export] Instance red_upcast_downcast A (a: A)
  : red_db itree_option (@Any.downcast A (@Any.upcast A a)) :=
  mk_red_db _ _ (@Any.upcast_downcast A a) tt (inl _continue).

#[export] Instance red_split_pair a0 a1
  : red_db itree_option (Any.split (Any.pair a0 a1)) :=
  mk_red_db _ _ (@Any.pair_split a0 a1) tt (inl _continue).

#[export] Instance commute_bind_bind E R S T
 (s : itree E R)
 (k : R -> itree E S)
 (h : S -> itree E T)
  : red_db itree_unfold ((s >>= k) >>= h) :=
  mk_red_db _ _ (@bind_bind E R S T s k h) tt (inl _continue).

#[export] Instance commute_bind_tau E R U
 (t : itree E U)
 (k : U -> itree E R)
  : red_db itree_unfold ((tau;;t) >>= k) :=
  mk_red_db _ _ (@bind_tau E R U t k) tt (inl _break).

#[export] Instance commute_bind_ret_l E R S
 (r : R)
 (k : R -> itree E S)
  : red_db itree_unfold (Ret r >>= k) :=
  mk_red_db _ _ (@bind_ret_l E R S r k) tt (inl _continue).

#[export] Instance commute_bind_ret_r_rev {E F} `{H: E -< F} R (e: E R)
  : red_db itree_class (ITree.trigger (@subevent E F H _ e)) :=
  mk_red_db _ _ (@bind_ret_r_rev F R (trigger e)) tt (inl _break).

Module _TEST.
  Section TEST.

  Variable ID: Type.
  Variable E0: Type -> Type.
  Variable E1: Type -> Type.
  Variable E2: Type -> Type.
  Variable interp0: forall {X}, itree E0 X -> itree E1 X.
  Variable interp1: forall {X}, itree E1 X -> itree E2 X.

  Hypothesis interp0_bind: forall
      A B (itr: itree E0 A) (ktr: ktree E0 A B),
      interp0 (itr >>= ktr) = interp0 itr >>= (fun a => interp0 (ktr a)).

  Hypothesis interp0_tau: forall
      R (itr: itree E0 R),
      interp0 (Tau itr) = Tau (interp0 itr).

  Hypothesis interp0_ret: forall
      R (r: R),
      interp0 (Ret r) = Ret r.

  Hypothesis interp0_ext: forall
      A (itr0 itr1: itree E0 A),
      (itr0 = itr1) ->
      (interp0 itr0 = interp0 itr1).

  Hypothesis interp1_bind: forall
      A B (itr: itree E1 A) (ktr: ktree E1 A B),
      interp1 (itr >>= ktr) = interp1 itr >>= (fun a => interp1 (ktr a)).

  Hypothesis interp1_tau: forall
      R (itr: itree E1 R),
      interp1 (Tau itr) = Tau (interp1 itr).

  Hypothesis interp1_ret: forall
      R (r: R),
      interp1 (Ret r) = Ret r.

  Hypothesis interp1_ext: forall
      A (itr0 itr1: itree E1 A),
      (itr0 = itr1) ->
      (interp1 itr0 = interp1 itr1).

  Instance interp0_ext_red
           A (itr0: itree E0 A)
    : red_db itree_unfold (interp0 itr0) :=
    mk_red_db _ _ (@interp0_ext A itr0) itr0 (inr itree_unfold).

  Instance interp0_bind_red
           A B (itr: itree E0 A) (ktr: ktree E0 A B)
    : red_db itree_unfold (interp0 (itr >>= ktr)) :=
    mk_red_db _ _ (@interp0_bind A B itr ktr) tt (inl _continue).

  Instance interp0_tau_red
           R (itr: itree E0 R)
    : red_db itree_unfold (interp0 (Tau itr)) :=
    mk_red_db _ _ (@interp0_tau R itr) tt (inl _break).

  Instance interp0_ret_red
           R (r: R)
    : red_db itree_unfold (interp0 (Ret r)) :=
    mk_red_db _ _ (@interp0_ret R r) tt (inl _break).

  Instance interp1_ext_red
           A (itr0: itree E1 A)
    : red_db itree_unfold (interp1 itr0) :=
    mk_red_db _ _ (@interp1_ext A itr0) itr0 (inr itree_unfold).

  Instance interp1_bind_red
           A B (itr: itree E1 A) (ktr: ktree E1 A B)
    : red_db itree_unfold (interp1 (itr >>= ktr)) :=
    mk_red_db _ _ (@interp1_bind A B itr ktr) tt (inl _continue).

  Instance interp1_tau_red
           R (itr: itree E1 R)
    : red_db itree_unfold (interp1 (Tau itr)) :=
    mk_red_db _ _ (@interp1_tau R itr) tt (inl _break).

  Instance interp1_ret_red
           R (r: R)
    : red_db itree_unfold (interp1 (Ret r)) :=
    mk_red_db _ _ (@interp1_ret R r) tt (inl _break).

  Context `{H: @eventE ID -< E2}.

  Variable X: Type.
  Variable Y: Type.
  Variable Z: Type.

  Goal forall R (r: R),
      interp1 (interp0 (Ret r)) = Ret r.
  Proof.
    intros.
    repeat (prw ltac:(red_tac itree_class) 2 0).
    reflexivity.
  Qed.

  Goal forall R (r: R),
      interp1 (x <- interp0 (x <- Tau (Ret r);; Ret x);; Tau (Ret x)) = tau;; tau;; Ret r.
  Proof.
    intros.
    (prw ltac:(red_tac itree_class) 2 0).
    repeat (prw ltac:(red_tac itree_class) 2 0).
    repeat (prw ltac:(red_tac itree_class) 2 0).
    f_equal. f_equal.
    repeat (prw ltac:(red_tac itree_class) 2 0).
    f_equal. f_equal.
    repeat (prw ltac:(red_tac itree_class) 2 0).
    reflexivity.
  Qed.

  Goal forall (x: X) (e: @eventE ID X) (ktr: X -> itree E2 Y),
      (unwrap (@Any.downcast X (Any.upcast x)) >>= (fun x: X => trigger e >>= (fun _ => tau;; Ret x)) >>= ktr) >>= (fun _ => trigger e) = trigger e >>= (fun _ => tau;; (ktr x) >>= (fun _ => trigger e >>= (fun r => Ret r))).
  Proof.
    intros.
    (prw ltac:(red_tac itree_class) 2 0).
    f_equal. extensionality _x0.
    (prw ltac:(red_tac itree_class) 2 0).
    (prw ltac:(red_tac itree_class) 2 0).
    f_equal. f_equal.
    (prw ltac:(red_tac itree_class) 2 0).
    f_equal. extensionality _x1.
    (prw ltac:(red_tac itree_class) 2 0).
    reflexivity.
  Qed.

  End TEST.
End _TEST.
