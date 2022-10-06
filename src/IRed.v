From Fairness Require Import Red ITreeLib Any.
From sflib Require Import sflib.
Require Import Program.

Local Open Scope nat_scope.

Set Implicit Arguments.



Ltac get_head term :=
  match term with
  | ?f ?x => get_head f
  | _ => term
  end
.

Ltac get_head2 term :=
  lazymatch term with
  | ?f ?x =>
    let ty := type of x in
    lazymatch ty with
    | context[ReSum] => term
    | _ => get_head2 f
    end
  | _ => term
  end
.

(* Ltac iSolveTC := *)
(*   solve [once (typeclasses eauto)]. *)

(* Ltac get_tail term := *)
(*   match term with *)
(*   | ?f ?x => x *)
(*   end *)
(* . *)

Ltac get_itr term :=
  (* repeat multimatch term with *)
  (*        | _ ?x => match type of x with itree _ _ => x end *)
  (*        | _ ?x _ => match type of x with itree _ _ => x end *)
  (*        | _ ?x _ _ => match type of x with itree _ _ => x end *)
  (*        | _ ?x _ _ _ => match type of x with itree _ _ => x end *)
  (*        | _ ?x _ _ _ _ => match type of x with itree _ _ => x end *)
  (*        | _ ?x _ _ _ _ _ => match type of x with itree _ _ => x end *)
  (*        end *)
  (* repeat multimatch term with *)
  (*        | _ ?x => match type of x with itree _ _ => constr:(x) end *)
  (*        | _ ?x _ => match type of x with itree _ _ => constr:(x) end *)
  (*        | _ ?x _ _ => match type of x with itree _ _ => constr:(x) end *)
  (*        | _ ?x _ _ _ => match type of x with itree _ _ => constr:(x) end *)
  (*        | _ ?x _ _ _ _ => match type of x with itree _ _ => constr:(x) end *)
  (*        | _ ?x _ _ _ _ _ => match type of x with itree _ _ => constr:(x) end *)
  (*        end *)
  match term with
  | _ ?x => match type of x with itree _ _ => constr:(x) end
  | _ ?x _ => match type of x with itree _ _ => constr:(x) end
  | _ ?x _ _ => match type of x with itree _ _ => constr:(x) end
  | _ ?x _ _ _ => match type of x with itree _ _ => constr:(x) end
  | _ ?x _ _ _ _ => match type of x with itree _ _ => constr:(x) end
  | _ ?x _ _ _ _ _ => match type of x with itree _ _ => constr:(x) end
  end
.

Ltac get_nth term n :=
  match term with
  | ?f ?x =>
    match n with
    | O => x
    | S ?m => get_nth f m
      (* let res := get_nth x m in *)
      (* constr:(res) *)
    end
  | ?x =>
    match n with
    | O => x
    end
  end
.

Goal forall (f: nat -> nat -> nat -> nat -> nat) a b c d, f a b c d = 0.
  i.
  let tmp := get_nth (f a b c d) 0 in pose tmp as d'. assert(d' = d) by reflexivity.
  let tmp := get_nth (f a b c d) 1 in pose tmp as c'. assert(c' = c) by reflexivity.
  let tmp := get_nth (f a b c d) 2 in pose tmp as b'. assert(b' = b) by reflexivity.
  let tmp := get_nth (f a b c d) 3 in pose tmp as a'. assert(a' = a) by reflexivity.
  let tmp := get_nth (f a b c d) 4 in pose tmp as f'. assert(f' = f) by reflexivity.
Abort.



(*** TODO: move to better place or use dedicated name (like ired_box) ***)
Variant Box: Type :=
| mk_box: forall (A:Type), A -> Box
.

Class red_database (interp: Box) := mk_rdb {
  rdb_pos: nat;
  rdb_bind: Box;
  rdb_tau: Box;
  rdb_ret: Box;
  rdb_trigger0: Box;
  rdb_trigger1: Box;
  rdb_trigger2: Box;
  rdb_trigger3: Box;
  rdb_UB: Box;
  rdb_NB: Box;
  rdb_unwrapU: Box;
  rdb_unwrapN: Box;
  rdb_assume: Box;
  rdb_guarantee: Box;
  rdb_ext: Box;
}
.
Arguments mk_rdb [interp].
Arguments rdb_pos [interp].
Arguments rdb_bind [interp].
Arguments rdb_tau [interp].
Arguments rdb_ret [interp].
Arguments rdb_trigger0 [interp].
Arguments rdb_trigger1 [interp].
Arguments rdb_trigger2 [interp].
Arguments rdb_trigger3 [interp].
Arguments rdb_UB [interp].
Arguments rdb_NB [interp].
Arguments rdb_unwrapU [interp].
Arguments rdb_unwrapN [interp].
Arguments rdb_assume [interp].
Arguments rdb_guarantee [interp].
Arguments rdb_ext [interp].






(*** TODO: move to ITreeLib ***)
(*** TODO: remove redundancy with HoareDef - bind_eta ***)
Lemma bind_ext E X Y itr0 itr1 (ktr: ktree E X Y): itr0 = itr1 -> itr0 >>= ktr = itr1 >>= ktr. i; subst; reflexivity. Qed.

Lemma bind_extk: forall [E : Type -> Type] [X Y : Type] [itr: itree E X] (ktr0 ktr1: ktree E X Y),
    (forall x, ktr0 x = ktr1 x) -> (itr >>= ktr0) = (itr >>= ktr1)
.
Proof. i. f_equiv. extensionality x. eauto. Qed.

Lemma tau_ext: forall [E : Type -> Type] [X : Type] [itr0 itr1: itree E X],
    itr0 = itr1 -> (tau;; itr0) = (tau;; itr1)
.
Proof. i. grind. Qed.


(* Tactic Notation "debug" string(str) := idtac str. (*** debug mode ***) *)
(* Tactic Notation "debug" string(str) := idtac. (*** release mode ***) *)

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

(* Ltac __red_interp f term := *)
(*   match term with *)
(*   | unwrapU (@Any.downcast ?A (@Any.upcast ?A ?a)) => *)
(*     instantiate (f:=_continue); apply f_equal; apply Any.upcast_downcast; fail *)
(*   | unwrapU (Any.split (Any.pair ?a0 ?a1)) => *)
(*     instantiate (f:=_continue); apply f_equal; apply Any.pair_split; fail *)
(*   | unwrapN (@Any.downcast ?A (@Any.upcast ?A ?a)) => *)
(*     instantiate (f:=_continue); apply f_equal; apply Any.upcast_downcast; fail *)
(*   | unwrapN (Any.split (Any.pair ?a0 ?a1)) => *)
(*     instantiate (f:=_continue); apply f_equal; apply Any.pair_split; fail *)
(*   | _ => *)

(*   (* idtac "__red_interp"; *) *)
(*   (* idtac term; *) *)
(*   let my_interp := get_head2 term in *)
(*   (* idtac itr; *) *)
(*   let tc := fresh "_TC_" in *)
(*   unshelve evar (tc: @red_database (mk_box (my_interp))); [typeclasses eauto|]; *)
(*   let name := fresh "TMP" in *)
(*   let _nth := constr:(rdb_pos tc) in *)
(*   let nth := (eval simpl in _nth) in *)
(*   let itr := get_nth term nth in *)
(*   lazymatch itr with *)
(*   | ITree.bind' ?k0 ?i0 => *)
(*     (* idtac "bind"; *) *)
(*     instantiate (f:=_continue); pose (rdb_bind tc) as name; cbn in name; *)
(*     (*** Note: Why not just "apply lemma"? Because of Coq bug. (Anomaly) ***) *)
(*     match goal with | name := mk_box ?lemma |- _ => first[apply (@lemma _ _ i0 k0)|apply lemma] end *)
(*   | Tau _ => *)
(*     instantiate (f:=_continue); pose (rdb_tau tc) as name; cbn in name; *)
(*     match goal with | name := mk_box ?lemma |- _ => apply lemma; fail 2 end *)
(*   | Ret _ => *)
(*     (* idtac "ret"; *) *)
(*     instantiate (f:=_continue); pose (rdb_ret tc) as name; cbn in name; *)
(*     match goal with | name := mk_box ?lemma |- _ => apply lemma; fail 2 end *)
(*   | trigger ?e => *)
(*     instantiate (f:=_continue); *)
(*     ((pose (rdb_trigger0 tc) as name; cbn in name; match goal with | name := mk_box ?lemma |- _ => apply lemma; fail 2 end) || *)
(*      (pose (rdb_trigger1 tc) as name; cbn in name; match goal with | name := mk_box ?lemma |- _ => apply lemma; fail 2 end) || *)
(*      (pose (rdb_trigger2 tc) as name; cbn in name; match goal with | name := mk_box ?lemma |- _ => apply lemma; fail 2 end) || *)
(*      (pose (rdb_trigger3 tc) as name; cbn in name; match goal with | name := mk_box ?lemma |- _ => apply lemma; fail 2 end) || *)
(*      fail 3 *)
(*     ) *)
(*   | triggerUB => *)
(*     instantiate (f:=_continue); pose (rdb_UB tc) as name; cbn in name; *)
(*     match goal with | name := mk_box ?lemma |- _ => apply lemma; fail 2 end *)
(*   | triggerNB => *)
(*     instantiate (f:=_continue); pose (rdb_NB tc) as name; cbn in name; *)
(*     match goal with | name := mk_box ?lemma |- _ => apply lemma; fail 2 end *)
(*   | unwrapU _ => *)
(*     instantiate (f:=_continue); pose (rdb_unwrapU tc) as name; cbn in name; *)
(*     match goal with | name := mk_box ?lemma |- _ => apply lemma; fail 2 end *)
(*   | unwrapN _ => *)
(*     instantiate (f:=_continue); pose (rdb_unwrapN tc) as name; cbn in name; *)
(*     match goal with | name := mk_box ?lemma |- _ => apply lemma; fail 2 end *)
(*   | assume _ => *)
(*     instantiate (f:=_continue); pose (rdb_assume tc) as name; cbn in name; *)
(*     match goal with | name := mk_box ?lemma |- _ => apply lemma; fail 2 end *)
(*   | guarantee _ => *)
(*     instantiate (f:=_continue); pose (rdb_guarantee tc) as name; cbn in name; *)
(*     match goal with | name := mk_box ?lemma |- _ => apply lemma; fail 2 end *)
(*   | ?term => *)
(*     (* idtac "term"; *) *)
(*     pose (rdb_ext tc) as name; cbn in name; *)
(*     match goal with | name := mk_box ?lemma |- _ => apply lemma end; *)
(*     subst tc; *)
(*     __red_interp f term *)
(*   end *)
(* end *)
(* . *)

(* Ltac _red_interp f := *)
(*   (* idtac "_red_interp"; *) *)
(*   lazymatch goal with *)
(*   | [ |- ITree.bind' _ ?term = _ ] => *)
(*     (* idtac "_red_interp_bind"; *) *)
(*     apply bind_ext; __red_interp f term *)
(*   | [ |- ?term = _] => *)
(*     (* idtac "_red_interp_term"; *) *)
(*     __red_interp f term *)
(*   end *)
(* . *)

(* Ltac _red_gen f := *)
(*   (* idtac "DEBUG:_red_gen"; *) *)
(*   _red_interp f || _red_itree f || fail. *)





Lemma resum_itr_bind
      E F (R S: Type)
      (s: itree E R) (k : R -> itree E S)
      `{E -< F}
  :
    (resum_itr (s >>= k))
    =
    ((resum_itr (E:=E) (F:=F) s) >>= (fun r => resum_itr (k r))).
Proof.
  unfold resum_itr in *. grind.
Qed.

(* Section RESUM. *)

(*   (*****************************************************) *)
(*   (****************** Reduction Lemmas *****************) *)
(*   (*****************************************************) *)

(*   Context {E F: Type -> Type}. *)
(*   (* Context `{eventE -< E}. *) *)
(*   (* Context `{E -< F}. *) *)
(*   Context `{PRF: E -< F}. *)
(*   Context `{eventE -< E}. *)
(*   Let eventE_F: eventE -< F. rr. ii. eapply PRF. eapply H. eapply X. Defined. *)
(*   Local Existing Instance eventE_F. *)

(*   (* Lemma resum_itr_bind *) *)
(*   (*       (R S: Type) *) *)
(*   (*       (s: itree _ R) (k : R -> itree _ S) *) *)
(*   (*   : *) *)
(*   (*     (resum_itr (s >>= k)) *) *)
(*   (*     = *) *)
(*   (*     ((resum_itr (E:=E) (F:=F) s) >>= (fun r => resum_itr (k r))). *) *)
(*   (* Proof. *) *)
(*   (*   unfold resum_itr in *. grind. *) *)
(*   (* Qed. *) *)

(*   Lemma resum_itr_tau *)
(*         (U: Type) *)
(*         (t : itree _ U) *)
(*     : *)
(*       (resum_itr (E:=E) (F:=F) (Tau t)) *)
(*       = *)
(*       (Tau (resum_itr t)). *)
(*   Proof. *)
(*     unfold resum_itr in *. grind. *)
(*   Qed. *)

(*   Lemma resum_itr_ret *)
(*         (U: Type) *)
(*         (t: U) *)
(*     : *)
(*       ((resum_itr (E:=E) (F:=F) (Ret t))) *)
(*       = *)
(*       Ret t. *)
(*   Proof. *)
(*     unfold resum_itr in *. grind. *)
(*   Qed. *)

(*   Lemma resum_itr_event *)
(*         (R: Type) *)
(*         (i: E R) *)
(*     : *)
(*       (resum_itr (E:=E) (F:=F) (trigger i)) *)
(*       = *)
(*       (trigger i >>= (fun r => tau;; Ret r)). *)
(*   Proof. *)
(*     unfold resum_itr in *. *)
(*     repeat rewrite interp_trigger. grind. *)
(*   Qed. *)

(*   Lemma resum_itr_triggerUB *)
(*         (R: Type) *)
(*     : *)
(*       (resum_itr (E:=E) (F:=F) (triggerUB)) *)
(*       = *)
(*       triggerUB (A:=R). *)
(*   Proof. *)
(*     unfold resum_itr, triggerUB in *. rewrite unfold_interp. cbn. grind. *)
(*   Qed. *)

(*   Lemma resum_itr_triggerNB *)
(*         (R: Type) *)
(*     : *)
(*       (resum_itr (E:=E) (F:=F) (triggerNB)) *)
(*       = *)
(*       triggerNB (A:=R). *)
(*   Proof. *)
(*     unfold resum_itr, triggerNB in *. rewrite unfold_interp. cbn. grind. *)
(*   Qed. *)

(*   Lemma resum_itr_unwrapU *)
(*         (R: Type) *)
(*         (i: option R) *)
(*     : *)
(*       (resum_itr (E:=E) (F:=F) (unwrapU i)) *)
(*       = *)
(*       (unwrapU i). *)
(*   Proof. *)
(*     unfold resum_itr. unfold unwrapU. des_ifs; grind. eapply resum_itr_triggerUB. *)
(*   Qed. *)

(*   Lemma resum_itr_unwrapN *)
(*         (R: Type) *)
(*         (i: option R) *)
(*     : *)
(*       (resum_itr (E:=E) (F:=F) (unwrapN i)) *)
(*       = *)
(*       (unwrapN i). *)
(*   Proof. *)
(*     unfold resum_itr. unfold unwrapN. des_ifs; grind. eapply resum_itr_triggerNB. *)
(*   Qed. *)

(*   Lemma resum_itr_assume *)
(*         P *)
(*     : *)
(*       (resum_itr (E:=E) (F:=F) (assume P)) *)
(*       = *)
(*       (assume P;;; tau;; Ret tt) *)
(*   . *)
(*   Proof. *)
(*     unfold resum_itr, assume. grind. rewrite unfold_interp; cbn. grind. *)
(*   Qed. *)

(*   Lemma resum_itr_guarantee *)
(*         P *)
(*     : *)
(*       (resum_itr (E:=E) (F:=F) (guarantee P)) *)
(*       = *)
(*       (guarantee P;;; tau;; Ret tt). *)
(*   Proof. *)
(*     unfold resum_itr, guarantee. grind. rewrite unfold_interp; cbn. grind. *)
(*   Qed. *)

(*   Lemma resum_itr_ext *)
(*         R (itr0 itr1: itree _ R) *)
(*         (EQ: itr0 = itr1) *)
(*     : *)
(*       (resum_itr (E:=E) (F:=F) itr0) *)
(*       = *)
(*       (resum_itr itr1) *)
(*   . *)
(*   Proof. subst; et. Qed. *)

(*   Global Program Instance resum_itr_rdb: red_database (mk_box (@resum_itr E F PRF)) := *)
(*     mk_rdb *)
(*       0 *)
(*       (mk_box resum_itr_bind) *)
(*       (mk_box resum_itr_tau) *)
(*       (mk_box resum_itr_ret) *)
(*       (mk_box resum_itr_event) *)
(*       (mk_box True) *)
(*       (mk_box True) *)
(*       (mk_box True) *)
(*       (mk_box resum_itr_triggerUB) *)
(*       (mk_box resum_itr_triggerNB) *)
(*       (mk_box resum_itr_unwrapU) *)
(*       (mk_box resum_itr_unwrapN) *)
(*       (mk_box resum_itr_assume) *)
(*       (mk_box resum_itr_guarantee) *)
(*       (mk_box resum_itr_ext) *)
(*   . *)

(*   Global Opaque resum_itr. *)

(* End RESUM. *)
