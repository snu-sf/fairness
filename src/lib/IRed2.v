From Fairness Require Export TRed.
Require Import String.
From Fairness Require Import ITreeLib Event.

Definition itree_class: red_class := red_class_cons "itree".

Definition itree_unfold: red_class := red_class_cons "itree_unfold".

#[export] Instance focus_id c A (a: A): red_db c a :=
  mk_red_db _ _ (@id) a None.


(*** TODO: move to ITreeLib ***)
(*** TODO: remove redundancy with HoareDef - bind_eta ***)
Lemma bind_ext E X Y itr0 itr1 (ktr: ktree E X Y): itr0 = itr1 -> itr0 >>= ktr = itr1 >>= ktr.
Proof. intros. subst; reflexivity. Qed.

#[export] Instance focus_bind E X Y (itr: itree E X) (ktr: X -> itree E Y)
  : focus_db itree_class (itr >>= ktr) :=
  mk_focus_db _ _ (@bind_ext E X Y) itr.

#[export] Instance commute_bind_bind E R S T
 (s : itree E R)
 (k : R -> itree E S)
 (h : S -> itree E T)
  : commute_db itree_class ((s >>= k) >>= h) :=
  mk_commute_db _ _ bind_bind.

#[export] Instance commute_bind_tau E R U
 (t : itree E R)
 (k : R -> itree E U)
  : commute_db itree_class ((tau;;t) >>= k) :=
  mk_commute_db _ _ bind_tau.

#[export] Instance commute_bind_ret_l E R S
 (r : R)
 (k : R -> itree E S)
  : commute_db itree_class (Ret r >>= k) :=
  mk_commute_db _ _ bind_ret_l.

#[export] Instance commute_bind_ret_r_rev {E F} `{E -< F} R (e: E R)
  : commute_db itree_class (trigger e) :=
  mk_commute_db _ _ bind_ret_r_rev.

#[export] Instance commute_bind_ret_r_rev ID E `{eventE -< E} R (r: option R)
  : unfold_db itree_class (unwrap (@Any.down_cast

                             trigger e) :=
  mk_commute_db _ _ bind_ret_r_rev.

 {E F} `{E -< F} R (e: E R)
  : commute_db itree_class (unwrap (trigger e) :=
  mk_commute_db _ _ bind_ret_r_rev.

  match term with
  | unwrap (@Any.downcast ?A (@Any.upcast ?A ?a)) =>
    instantiate (f:=_continue); apply f_equal; apply Any.upcast_downcast; fail
  | unwrap (Any.split (Any.pair ?a0 ?a1)) =>
    instantiate (f:=_continue); apply f_equal; apply Any.pair_split; fail


Ltac _red_itree f :=
  lazymatch goal with
  | [ |- ITree.bind ?itr ?ktr = _] =>
    lazymatch itr with
    | ITree.bind _ _ =>
      instantiate (f:=_continue); apply bind_bind; fail
    | Tau _ =>
      instantiate (f:=_break); apply bind_tau; fail
    | Ret _ =>
      instantiate (f:=_continue); apply bind_ret_l; fail
    (* | _ => *)
    (*   eapply bind_extk; i; *)
    (*   _red_itree f *)
    end
  | [ |- trigger _ = _] =>
    instantiate (f:=_break); apply bind_ret_r_rev; fail
  (* | [ |- (tau;; _) = _ ] => *)
  (*   eapply tau_ext; _red_itree f *)
  | _ => fail
  end.

Ltac __red_interp f term :=
  match term with
  | unwrap (@Any.downcast ?A (@Any.upcast ?A ?a)) =>
    instantiate (f:=_continue); apply f_equal; apply Any.upcast_downcast; fail
  | unwrap (Any.split (Any.pair ?a0 ?a1)) =>
    instantiate (f:=_continue); apply f_equal; apply Any.pair_split; fail
  (* | unwrapN (@Any.downcast ?A (@Any.upcast ?A ?a)) => *)
  (*   instantiate (f:=_continue); apply f_equal; apply Any.upcast_downcast; fail *)
  (* | unwrapN (Any.split (Any.pair ?a0 ?a1)) => *)
  (*   instantiate (f:=_continue); apply f_equal; apply Any.pair_split; fail *)
  | _ =>

  (* idtac "__red_interp"; *)
  (* idtac term; *)
  let my_interp := get_head2 term in
  (* idtac itr; *)
  let tc := fresh "_TC_" in
  unshelve evar (tc: @red_database (mk_box (my_interp))); [typeclasses eauto|];
  let name := fresh "TMP" in
  let _nth := constr:(rdb_pos tc) in
  let nth := (eval simpl in _nth) in
  let itr := get_nth term nth in
  lazymatch itr with
  | ITree.bind ?i0 ?k0 =>
    (* idtac "bind"; *)
    instantiate (f:=_continue); pose (rdb_bind tc) as name; cbn in name;
    (*** Note: Why not just "apply lemma"? Because of Coq bug. (Anomaly) ***)
    match goal with | name := mk_box ?lemma |- _ => first[apply (@lemma _ _ i0 k0)|apply lemma] end
  | Tau _ =>
    instantiate (f:=_continue); pose (rdb_tau tc) as name; cbn in name;
    match goal with | name := mk_box ?lemma |- _ => apply lemma; fail 2 end
  | Ret _ =>
    (* idtac "ret"; *)
    instantiate (f:=_continue); pose (rdb_ret tc) as name; cbn in name;
    match goal with | name := mk_box ?lemma |- _ => apply lemma; fail 2 end
  | trigger ?e =>
    instantiate (f:=_continue);
    ((pose (rdb_trigger0 tc) as name; cbn in name; match goal with | name := mk_box ?lemma |- _ => apply lemma; fail 2 end) ||
     (pose (rdb_trigger1 tc) as name; cbn in name; match goal with | name := mk_box ?lemma |- _ => apply lemma; fail 2 end) ||
     (pose (rdb_trigger2 tc) as name; cbn in name; match goal with | name := mk_box ?lemma |- _ => apply lemma; fail 2 end) ||
     (pose (rdb_trigger3 tc) as name; cbn in name; match goal with | name := mk_box ?lemma |- _ => apply lemma; fail 2 end) ||
     (pose (rdb_trigger4 tc) as name; cbn in name; match goal with | name := mk_box ?lemma |- _ => apply lemma; fail 2 end) ||
     fail 3
    )
  | UB =>
    instantiate (f:=_continue); pose (rdb_UB tc) as name; cbn in name;
    match goal with | name := mk_box ?lemma |- _ => apply lemma; fail 2 end
  (* | triggerNB => *)
  (*   instantiate (f:=_continue); pose (rdb_NB tc) as name; cbn in name; *)
  (*   match goal with | name := mk_box ?lemma |- _ => apply lemma; fail 2 end *)
  | unwrap _ =>
    instantiate (f:=_continue); pose (rdb_unwrapU tc) as name; cbn in name;
    match goal with | name := mk_box ?lemma |- _ => apply lemma; fail 2 end
  (* | unwrapN _ => *)
  (*   instantiate (f:=_continue); pose (rdb_unwrapN tc) as name; cbn in name; *)
  (*   match goal with | name := mk_box ?lemma |- _ => apply lemma; fail 2 end *)
  (* | assume _ => *)
  (*   instantiate (f:=_continue); pose (rdb_assume tc) as name; cbn in name; *)
  (*   match goal with | name := mk_box ?lemma |- _ => apply lemma; fail 2 end *)
  (* | guarantee _ => *)
  (*   instantiate (f:=_continue); pose (rdb_guarantee tc) as name; cbn in name; *)
  (*   match goal with | name := mk_box ?lemma |- _ => apply lemma; fail 2 end *)
  | ?term =>
    (* idtac "term"; *)
    pose (rdb_ext tc) as name; cbn in name;
    match goal with | name := mk_box ?lemma |- _ => apply lemma end;
    subst tc;
    __red_interp f term
  end
end
.
