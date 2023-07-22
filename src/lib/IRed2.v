Require Import String Program.
From Fairness Require Export TRed.
From Fairness Require Import ITreeLib Event.

Definition itree_class: red_class := red_class_cons "itree".
Definition itree_unfold: red_class := red_class_cons "itree_unfold".
Definition itree_option: red_class := red_class_cons "itree_option".

#[export] Instance incl_itree_unfold_itree_class: red_db_incl itree_unfold itree_class := mk_red_db_incl.

#[export] Instance focus_bind E X Y (itr: itree E X) (ktr: X -> itree E Y)
  : red_db itree_class (itr >>= ktr) :=
  mk_red_db _ _ (@bind_ext E X Y) itr (inr itree_unfold).

#[export] Instance focus_option ID E `{H: @eventE ID -< E} R (r: option R)
  : red_db itree_unfold (unwrap r) :=
  mk_red_db _ _ (@f_equal _ _ (@unwrap ID E H R)) r (inr itree_option).

#[export] Instance red_upcast_downcast A (a: A)
  : red_db itree_option (@Any.downcast A (@Any.upcast A a)) :=
  mk_red_db _ _ Any.upcast_downcast tt (inl _continue).

#[export] Instance red_split_pair a0 a1
  : red_db itree_option (Any.split (Any.pair a0 a1)) :=
  mk_red_db _ _ Any.pair_split tt (inl _continue).

#[export] Instance commute_bind_bind E R S T
 (s : itree E R)
 (k : R -> itree E S)
 (h : S -> itree E T)
  : red_db itree_unfold ((s >>= k) >>= h) :=
  mk_red_db _ _ bind_bind tt (inl _continue).

#[export] Instance commute_bind_tau E R U
 (t : itree E R)
 (k : R -> itree E U)
  : red_db itree_unfold ((tau;;t) >>= k) :=
  mk_red_db _ _ bind_tau tt (inl _break).

#[export] Instance commute_bind_ret_l E R S
 (r : R)
 (k : R -> itree E S)
  : red_db itree_unfold (Ret r >>= k) :=
  mk_red_db _ _ bind_ret_l tt (inl _continue).

#[export] Instance commute_bind_ret_r_rev {E F} `{E -< F} R (e: E R)
  : red_db itree_class (trigger e) :=
  mk_red_db _ _ bind_ret_r_rev tt (inl _break).

Module _TEST.
  Section TEST.

  Variable ID: Type.
  Variable E: Type -> Type.
  Context `{H: @eventE ID -< E}.

  Variable X: Type.
  Variable Y: Type.
  Variable Z: Type.

  Goal forall (x: X) (e: @eventE ID X) (ktr: X -> itree E Y),
      (unwrap (@Any.downcast X (Any.upcast x)) >>= (fun x: X => trigger e >>= (fun _ => tau;; Ret x)) >>= ktr) >>= (fun _ => trigger e) = trigger e >>= (fun _ => tau;; (ktr x) >>= (fun _ => trigger e >>= (fun r => Ret r))).
  Proof.
    intros.
    (prw ltac:(red_tac itree_class) 2 0).
    f_equal. extensionality _x0.
    repeat (prw ltac:(red_tac itree_class) 2 0).
    f_equal. f_equal.
    repeat (prw ltac:(red_tac itree_class) 2 0).
    f_equal. extensionality _x1.
    repeat (prw ltac:(red_tac itree_class) 2 0).
    reflexivity.
  Qed.

  End TEST.
End _TEST.
