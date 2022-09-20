Require Import RelationClasses.

From sflib Require Import sflib.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Loc.

From PromisingLib Require Import Event.
From Fairness Require Import Time.
From Fairness Require Import View.
From Fairness Require Import Cell.

Set Implicit Arguments.


Module Memory.
  Definition t := Loc.t -> Cell.t.

  Definition get (loc:Loc.t) (ts:Time.t) (mem:t): option (Time.t * Message.t) :=
    Cell.get ts (mem loc).

  Lemma get_disjoint
        l f1 f2 t1 t2 msg1 msg2 m
        (GET1: get l t1 m = Some (f1, msg1))
        (GET2: get l t2 m = Some (f2, msg2)):
    (t1 = t2 /\ f1 = f2 /\ msg1 = msg2) \/
    Interval.disjoint (f1, t1) (f2, t2).
  Proof.
    eapply Cell.get_disjoint; eauto.
  Qed.

  Lemma ext
        lhs rhs
        (EXT: forall loc ts, get loc ts lhs = get loc ts rhs):
    lhs = rhs.
  Proof.
    apply LocFun.ext. i.
    apply Cell.ext. i.
    apply EXT.
  Qed.

  Lemma get_ts
        loc to mem from msg
        (GET: get loc to mem = Some (from, msg)):
    (from = Time.bot /\ to = Time.bot) \/ Time.lt from to.
  Proof.
    unfold get in *.
    apply Cell.get_ts in GET. auto.
  Qed.

  Definition le (lhs rhs:t): Prop :=
    forall loc to from msg
      (LHS: get loc to lhs = Some (from, msg)),
      get loc to rhs = Some (from, msg).

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation. ii. auto. Qed.
  Next Obligation. ii. eapply H0; eauto. Qed.

  Inductive disjoint (lhs rhs:t): Prop :=
  | disjoint_intro
      (DISJOINT: forall loc to1 to2 from1 from2 msg1 msg2
                   (GET1: get loc to1 lhs = Some (from1, msg1))
                   (GET2: get loc to2 rhs = Some (from2, msg2)),
          Interval.disjoint (from1, to1) (from2, to2) /\
          (to1, to2) <> (Time.bot, Time.bot))
  .
  #[global] Hint Constructors disjoint: core.

  Global Program Instance disjoint_Symmetric: Symmetric disjoint.
  Next Obligation.
    inv H. econs. i. exploit DISJOINT; eauto. i. des. splits.
    - symmetry. auto.
    - ii. inv H. congr.
  Qed.

  Lemma disjoint_get
        lhs rhs
        loc froml fromr to msgl msgr
        (DISJOINT: disjoint lhs rhs)
        (LMSG: get loc to lhs = Some (froml, msgl))
        (RMSG: get loc to rhs = Some (fromr, msgr)):
    False.
  Proof.
    inv DISJOINT. exploit DISJOINT0; eauto. intros x. des.
    destruct (Time.eq_dec to Time.bot).
    - subst. congr.
    - eapply x.
      + apply Interval.mem_ub. destruct (Cell.WF (lhs loc)).
        exploit VOLUME; eauto. intros x1. des; auto. inv x1. congr.
      + apply Interval.mem_ub. destruct (Cell.WF (rhs loc)).
        exploit VOLUME; eauto. intros x1. des; auto. inv x1. congr.
  Qed.

  Lemma disjoint_get_general
        lhs rhs
        loc ts0 ts1 ts2 ts3 msgl msgr
        (TS12: Time.lt ts1 ts2)
        (TS23: Time.le ts2 ts3)
        (DISJOINT: disjoint lhs rhs)
        (LMSG: get loc ts2 lhs = Some (ts0, msgl))
        (RMSG: get loc ts3 rhs = Some (ts1, msgr)):
    False.
  Proof.
    inv DISJOINT. exploit DISJOINT0; eauto. intros x. des.
    destruct (Time.le_lt_dec ts2 ts0).
    - destruct (Cell.WF (lhs loc)). exploit VOLUME; eauto. intros x1. des.
      + inv x1. inv TS12.
      + eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt; eauto.
    - eapply x.
      + eapply Interval.mem_ub. auto.
      + econs; auto.
  Qed.

  Definition bot_none (mem: t): Prop :=
    forall loc, get loc Time.bot mem = None.
  #[global] Hint Unfold bot_none: core.

  Definition bot: t := fun _ => Cell.bot.

  Lemma bot_get loc ts: get loc ts bot = None.
  Proof. unfold get. apply Cell.bot_get. Qed.

  Lemma bot_le mem: le bot mem.
  Proof. ii. rewrite bot_get in LHS. congr. Qed.

  Lemma bot_disjoint mem: disjoint bot mem.
  Proof.
    econs. i. rewrite bot_get in *. inv GET1.
  Qed.

  Lemma bot_bot_none: bot_none bot.
  Proof. ii. apply bot_get. Qed.

  Definition singleton
             (loc:Loc.t) (from to:Time.t) (msg:Message.t)
             (LT: Time.lt from to)
             (WF: Message.wf msg): t :=
    (LocFun.add loc (Cell.singleton LT WF)
                (fun _ => Cell.bot)).

  Lemma singleton_get
        loc from to msg l t
        (LT:Time.lt from to)
        (WF: Message.wf msg):
    get l t (singleton loc LT WF) =
    if Loc.eq_dec l loc
    then if Time.eq_dec t to
         then Some (from, msg)
         else None
    else None.
  Proof.
    unfold get, singleton. unfold LocFun.add, LocFun.find.
    repeat condtac; subst.
    - rewrite Cell.singleton_get. condtac; [|congr]. auto.
    - rewrite Cell.singleton_get. condtac; [congr|]. auto.
    - apply Cell.bot_get.
  Qed.

  Definition init: t := fun _ => Cell.init.

  Inductive message_to: forall (msg:Message.t) (loc:Loc.t) (to:Time.t), Prop :=
  | message_to_concrete
      val released loc to
      (TS: Time.le ((View.rlx (View.unwrap released)) loc) to):
      message_to (Message.concrete val released) loc to
  | message_to_undef
      loc to:
      message_to Message.undef loc to
  | message_to_reserve
      loc to:
      message_to Message.reserve loc to
  .
  #[global] Hint Constructors message_to: core.

  Definition closed_timemap (times:TimeMap.t) (mem:t): Prop :=
    forall loc, exists from val released, get loc (times loc) mem = Some (from, Message.concrete val released).

  Inductive closed_view (view:View.t) (mem:t): Prop :=
  | closed_view_intro
      (PLN: closed_timemap (View.pln view) mem)
      (RLX: closed_timemap (View.rlx view) mem)
  .
  #[global] Hint Constructors closed_view: core.

  Inductive closed_opt_view: forall (view:option View.t) (mem:t), Prop :=
  | closed_opt_view_some
      view mem
      (CLOSED: closed_view view mem):
      closed_opt_view (Some view) mem
  | closed_opt_view_none
      mem:
      closed_opt_view None mem
  .
  #[global] Hint Constructors closed_opt_view: core.

  Inductive closed_message: forall (msg:Message.t) (mem:t), Prop :=
  | closed_message_concrete
      val released mem
      (CLOSED: closed_opt_view released mem):
      closed_message (Message.concrete val released) mem
  | closed_message_undef
      mem:
      closed_message Message.undef mem
  | closed_message_reserve
      mem:
      closed_message Message.reserve mem
  .
  #[global] Hint Constructors closed_message: core.


  Definition inhabited (mem:t): Prop :=
    forall loc, get loc Time.bot mem = Some (Time.bot, Message.elt).
  #[global] Hint Unfold inhabited: core.

  Inductive closed (mem:t): Prop :=
  | closed_intro
      (CLOSED: forall loc from to msg
                 (MSG: get loc to mem = Some (from, msg)),
          <<MSG_WF: Message.wf msg>> /\
          <<MSG_TS: message_to msg loc to>> /\
          <<MSG_CLOSED: closed_message msg mem>>)
      (INHABITED: inhabited mem)
  .
  #[global] Hint Constructors closed: core.

  Lemma closed_timemap_bot
        mem
        (INHABITED: inhabited mem):
    closed_timemap TimeMap.bot mem.
  Proof. ii. esplits. eapply INHABITED. Qed.

  Lemma closed_view_bot
        mem
        (INHABITED: inhabited mem):
    closed_view View.bot mem.
  Proof. econs; apply closed_timemap_bot; auto. Qed.

  Lemma unwrap_closed_opt_view
        view mem
        (CLOSED: closed_opt_view view mem)
        (INHABITED: inhabited mem):
    closed_view (View.unwrap view) mem.
  Proof.
    inv CLOSED; ss. apply closed_view_bot. ss.
  Qed.

  Lemma le_closed_timemap
        tm mem1 mem2
        (LE: le mem1 mem2)
        (CLOSED: Memory.closed_timemap tm mem1):
    Memory.closed_timemap tm mem2.
  Proof.
    ii. exploit CLOSED; eauto. i. des.
    esplits; eauto.
  Qed.

  Lemma le_closed_view
        view mem1 mem2
        (LE: le mem1 mem2)
        (CLOSED: Memory.closed_view view mem1):
    Memory.closed_view view mem2.
  Proof.
    inv CLOSED. econs; eauto using le_closed_timemap.
  Qed.

  Lemma le_closed_opt_view
        view mem1 mem2
        (LE: le mem1 mem2)
        (CLOSED: Memory.closed_opt_view view mem1):
    Memory.closed_opt_view view mem2.
  Proof.
    inv CLOSED; econs.
    eapply le_closed_view; eauto.
  Qed.

  Lemma le_closed_message
        msg mem1 mem2
        (LE: le mem1 mem2)
        (CLOSED: Memory.closed_message msg mem1):
    Memory.closed_message msg mem2.
  Proof.
    inv CLOSED; econs.
    eapply le_closed_opt_view; eauto.
  Qed.

  Lemma init_closed: closed init.
  Proof.
    econs; i; ss.
    unfold get, init, Cell.get, Cell.init in MSG. ss.
    apply DOMap.singleton_find_inv in MSG. des. inv MSG0.
    splits; try econs; ss. refl.
  Qed.

  Inductive add (mem1:t) (loc:Loc.t) (from to:Time.t) (msg:Message.t) (mem2:t): Prop :=
  | add_intro
      r
      (ADD: Cell.add (mem1 loc) from to msg r)
      (MEM2: mem2 = LocFun.add loc r mem1)
  .
  #[global] Hint Constructors add: core.

  Inductive split (mem1:t) (loc:Loc.t) (ts1 ts2 ts3:Time.t) (msg2 msg3:Message.t) (mem2:t): Prop :=
  | split_intro
      r
      (SPLIT: Cell.split (mem1 loc) ts1 ts2 ts3 msg2 msg3 r)
      (MEM2: mem2 = LocFun.add loc r mem1)
  .
  #[global] Hint Constructors split: core.

  Inductive lower (mem1:t) (loc:Loc.t) (from to:Time.t) (msg1 msg2:Message.t) (mem2:t): Prop :=
  | lower_intro
      r
      (LOWER: Cell.lower (mem1 loc) from to msg1 msg2 r)
      (MEM2: mem2 = LocFun.add loc r mem1)
  .
  #[global] Hint Constructors lower: core.

  Inductive remove (mem1:t) (loc:Loc.t) (from1 to1:Time.t) (msg1:Message.t) (mem2:t): Prop :=
  | remove_intro
      r
      (REMOVE: Cell.remove (mem1 loc) from1 to1 msg1 r)
      (MEM2: mem2 = LocFun.add loc r mem1)
  .
  #[global] Hint Constructors remove: core.

  Inductive op_kind :=
  | op_kind_add
  | op_kind_split (ts3:Time.t) (msg3:Message.t)
  | op_kind_lower (msg1:Message.t)
  | op_kind_cancel
  .
  #[global] Hint Constructors op_kind: core.

  Inductive op_kind_match: forall (k1 k2:op_kind), Prop :=
  | op_kind_match_add:
      op_kind_match
        op_kind_add
        op_kind_add
  | op_kind_match_split
      to m1 m2:
      op_kind_match
        (op_kind_split to m1)
        (op_kind_split to m2)
  | op_kind_match_lower
      m1 m2:
      op_kind_match
        (op_kind_lower m1)
        (op_kind_lower m2)
  | op_kind_match_cancel:
      op_kind_match
        op_kind_cancel
        op_kind_cancel
  .

  Definition op_kind_is_add kind :=
    match kind with op_kind_add => true | _ => false end.

  Definition op_kind_is_split kind :=
    match kind with op_kind_split _ _ => true | _ => false end.

  Definition op_kind_is_lower kind: bool :=
    match kind with op_kind_lower _ => true | _ => false end.

  Definition op_kind_is_cancel kind :=
    match kind with op_kind_cancel => true | _ => false end.

  Inductive op mem1 loc from to msg mem2: forall (kind:op_kind), Prop :=
  | op_add
      (ADD: add mem1 loc from to msg mem2):
      op mem1 loc from to msg mem2 op_kind_add
  | op_split
      to3 msg3
      (SPLIT: split mem1 loc from to to3 msg msg3 mem2):
      op mem1 loc from to msg mem2 (op_kind_split to3 msg3)
  | op_lower
      msg0
      (LOWER: lower mem1 loc from to msg0 msg mem2):
      op mem1 loc from to msg mem2 (op_kind_lower msg0)
  | op_cancel
      (MSG: msg = Message.reserve)
      (REMOVE: remove mem1 loc from to msg mem2):
      op mem1 loc from to msg mem2 op_kind_cancel
  .
  #[global] Hint Constructors op: core.

  Inductive future_imm (mem1 mem2:t): Prop :=
  | future_imm_intro
      loc from to msg kind
      (OP: op mem1 loc from to msg mem2 kind)
      (CLOSED: closed_message msg mem2)
      (TS: message_to msg loc to)
  .
  #[global] Hint Constructors future_imm: core.

  Definition future := rtc future_imm.
  #[global] Hint Unfold future: core.

  Inductive promise
            (promises1 mem1:t)
            (loc:Loc.t) (from to:Time.t) (msg:Message.t)
            (promises2 mem2:t): forall (kind:op_kind), Prop :=
  | promise_add
      (PROMISES: add promises1 loc from to msg promises2)
      (MEM: add mem1 loc from to msg mem2)
      (TS: message_to msg loc to)
      (ATTACH: forall to' msg'
                 (MSG: msg <> Message.reserve)
                 (GET: get loc to' mem1 = Some (to, msg')), False):
      promise promises1 mem1 loc from to msg promises2 mem2 op_kind_add
  | promise_split
      ts3 msg3
      (PROMISES: split promises1 loc from to ts3 msg msg3 promises2)
      (MEM: split mem1 loc from to ts3 msg msg3 mem2)
      (TS: message_to msg loc to)
      (MSG: msg <> Message.reserve)
      (MSG3: msg3 <> Message.reserve):
      promise promises1 mem1 loc from to msg promises2 mem2 (op_kind_split ts3 msg3)
  | promise_lower
      msg0
      (PROMISES: lower promises1 loc from to msg0 msg promises2)
      (MEM: lower mem1 loc from to msg0 msg mem2)
      (TS: message_to msg loc to)
      (MSG: msg <> Message.reserve):
      promise promises1 mem1 loc from to msg promises2 mem2 (op_kind_lower msg0)
  | promise_cancel
      (PROMISES: remove promises1 loc from to msg promises2)
      (MEM: remove mem1 loc from to msg mem2)
      (MSG: msg = Message.reserve):
      promise promises1 mem1 loc from to msg promises2 mem2 op_kind_cancel
  .
  #[global] Hint Constructors promise: core.

  Inductive write
            (promises1 mem1:t)
            (loc:Loc.t) (from1 to1:Time.t) (msg:Message.t)
            (promises3 mem2:t) (kind:op_kind): Prop :=
  | write_intro
      promises2
      (PROMISE: promise promises1 mem1 loc from1 to1 msg promises2 mem2 kind)
      (REMOVE: remove promises2 loc from1 to1 msg promises3)
  .
  #[global] Hint Constructors write: core.

  Inductive write_na (ts: Time.t)
                     (promises1 mem1: t) (loc: Loc.t) (from to: Time.t) (val: Const.t)
                     (promises2 mem2: t):
    forall (msgs: list (Time.t * Time.t * Message.t)) (kinds: list op_kind) (kind: op_kind), Prop :=
  | write_na_base
      kind
      (WRITABLE: Time.lt ts to)
      (WRITE: write promises1 mem1 loc from to (Message.concrete val None) promises2 mem2 kind):
      write_na ts promises1 mem1 loc from to val promises2 mem2 [] [] kind
  | write_na_write
      msgs kinds kind
      from' to' msg' promises' mem' kind'
      (WRITABLE_EX: Time.lt ts to')
      (MSG_EX: __guard__ (msg' = Message.undef \/
                          exists val', msg' = Message.concrete val' None))
      (WRITE_EX: write promises1 mem1 loc from' to' msg' promises' mem' kind')
      (WRITE_NA: write_na to' promises' mem' loc from to val promises2 mem2 msgs kinds kind):
      write_na ts promises1 mem1 loc from to val promises2 mem2 ((from', to', msg')::msgs) (kind'::kinds) kind
  .
  #[global] Hint Constructors write_na: core.


  (* Lemmas on add, split, lower & remove *)

  Lemma add_o
        mem2 mem1 loc from to msg
        l t
        (ADD: add mem1 loc from to msg mem2):
    get l t mem2 =
    if loc_ts_eq_dec (l, t) (loc, to)
    then Some (from, msg)
    else get l t mem1.
  Proof.
    inv ADD. unfold get, LocFun.add. condtac.
    - subst. erewrite Cell.add_o; eauto.
      repeat (condtac; subst; des; ss; try congr).
    - repeat (condtac; subst; des; ss; try congr).
  Qed.

  Lemma split_o
        mem2 mem1 loc ts1 ts2 ts3 msg2 msg3
        l t
        (SPLIT: split mem1 loc ts1 ts2 ts3 msg2 msg3 mem2):
    get l t mem2 =
    if loc_ts_eq_dec (l, t) (loc, ts2)
    then Some (ts1, msg2)
    else if loc_ts_eq_dec (l, t) (loc, ts3)
         then Some (ts2, msg3)
         else get l t mem1.
  Proof.
    inv SPLIT. unfold get, LocFun.add. condtac.
    - subst. erewrite Cell.split_o; eauto.
      repeat (condtac; subst; des; ss; try congr).
    - repeat (condtac; subst; des; ss; try congr).
  Qed.

  Lemma lower_o
        mem2 mem1 loc from to msg1 msg2
        l t
        (LOWER: lower mem1 loc from to msg1 msg2 mem2):
    get l t mem2 =
    if loc_ts_eq_dec (l, t) (loc, to)
    then Some (from, msg2)
    else get l t mem1.
  Proof.
    inv LOWER. unfold get, LocFun.add. condtac.
    - subst. erewrite Cell.lower_o; eauto.
      repeat (condtac; subst; des; ss; try congr).
    - repeat (condtac; subst; des; ss; try congr).
  Qed.

  Lemma remove_o
        mem2 mem1 loc from to msg
        l t
        (REMOVE: remove mem1 loc from to msg mem2):
    get l t mem2 =
    if loc_ts_eq_dec (l, t) (loc, to)
    then None
    else get l t mem1.
  Proof.
    inv REMOVE. unfold get, LocFun.add. condtac.
    - subst. erewrite Cell.remove_o; eauto.
      repeat (condtac; subst; des; ss; try congr).
    - repeat (condtac; subst; des; ss; try congr).
  Qed.

  Lemma add_get0
        mem1 loc from1 to1 msg1 mem2
        (ADD: add mem1 loc from1 to1 msg1 mem2):
    <<GET: get loc to1 mem1 = None>> /\
    <<GET: get loc to1 mem2 = Some (from1, msg1)>>.
  Proof.
    inv ADD. eapply Cell.add_get0; eauto.
    unfold get, Cell.get, LocFun.add. condtac; ss.
  Qed.

  Lemma split_get0
        mem1 loc ts1 ts2 ts3 msg2 msg3 mem2
        (SPLIT: split mem1 loc ts1 ts2 ts3 msg2 msg3 mem2):
    <<GET: get loc ts2 mem1 = None>> /\
    <<GET: get loc ts3 mem1 = Some (ts1, msg3)>> /\
    <<GET: get loc ts2 mem2 = Some (ts1, msg2)>> /\
    <<GET: get loc ts3 mem2 = Some (ts2, msg3)>>.
  Proof.
    inv SPLIT. eapply Cell.split_get0; eauto.
    unfold get, Cell.get, LocFun.add. condtac; ss.
  Qed.

  Lemma lower_get0
        mem1 loc from to msg1 msg2 mem2
        (LOWER: lower mem1 loc from to msg1 msg2 mem2):
    <<GET: get loc to mem1 = Some (from, msg1)>> /\
    <<GET: get loc to mem2 = Some (from, msg2)>> /\
    <<MSG_LE: Message.le msg2 msg1>>.
  Proof.
    inv LOWER. eapply Cell.lower_get0; eauto.
    unfold get, Cell.get, LocFun.add. condtac; ss.
  Qed.

  Lemma remove_get0
        mem1 loc from1 to1 msg1 mem2
        (REMOVE: remove mem1 loc from1 to1 msg1 mem2):
    <<GET: get loc to1 mem1 = Some (from1, msg1)>> /\
    <<GET: get loc to1 mem2 = None>>.
  Proof.
    inv REMOVE. eapply Cell.remove_get0; eauto.
    unfold get, Cell.get, LocFun.add. condtac; ss.
  Qed.

  Lemma add_get1
        m1 loc from to msg m2
        l f t m
        (ADD: add m1 loc from to msg m2)
        (GET1: get l t m1 = Some (f, m)):
    get l t m2 = Some (f, m).
  Proof.
    erewrite add_o; eauto. condtac; ss.
    des. subst. exploit add_get0; eauto. i. des. congr.
  Qed.

  Lemma split_get1
        m1 loc ts1 ts2 ts3 msg2 msg3 m2
        l f t m
        (SPLIT: split m1 loc ts1 ts2 ts3 msg2 msg3 m2)
        (GET1: get l t m1 = Some (f, m)):
    exists f',
      <<GET2: get l t m2 = Some (f', m)>> /\
      <<FROM: Time.le f f'>>.
  Proof.
    erewrite split_o; eauto. repeat condtac; ss.
    - des. subst. exploit split_get0; eauto. i. des. congr.
    - guardH o. des. subst. exploit split_get0; eauto. i. des.
      rewrite GET1 in GET0. inv GET0.
      esplits; eauto.
      inv SPLIT. inv SPLIT0. left. ss.
    - esplits; eauto.
      refl.
  Qed.

  Lemma lower_get1
        m1 loc from to msg1 msg2 m2
        l f t m
        (LOWER: lower m1 loc from to msg1 msg2 m2)
        (GET1: get l t m1 = Some (f, m)):
    exists m',
      <<GET2: get l t m2 = Some (f, m')>> /\
      <<MSG_LE: Message.le m' m>>.
  Proof.
    erewrite lower_o; eauto. condtac; ss.
    - des. subst. exploit lower_get0; eauto. i. des.
      rewrite GET1 in GET. inv GET.
      esplits; eauto.
    - esplits; eauto.
      refl.
  Qed.

  Lemma remove_get1
        m1 loc from to msg m2
        l f t m
        (REMOVE: remove m1 loc from to msg m2)
        (GET1: get l t m1 = Some (f, m)):
    <<LOCTS: l = loc /\ t = to>> \/
    <<GET2: get l t m2 = Some (f, m)>>.
  Proof.
    erewrite remove_o; eauto. condtac; eauto.
  Qed.


  (* Lemmas on op *)

  Lemma promise_op
        promises1 mem1 loc from to msg promises2 mem2 kind
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind):
    op mem1 loc from to msg mem2 kind.
  Proof.
    inv PROMISE.
    - econs 1. ss.
    - econs 2. ss.
    - econs 3. ss.
    - econs 4; ss.
  Qed.

  Lemma promise_op_promise
        promises1 mem1 loc from to msg promises2 mem2 kind
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind):
    op promises1 loc from to msg promises2 kind.
  Proof.
    inv PROMISE.
    - econs 1. ss.
    - econs 2. ss.
    - econs 3. ss.
    - econs 4; ss.
  Qed.

  Lemma write_op
        promises1 mem1 loc from to msg promises2 mem2 kind
        (WRITE: write promises1 mem1 loc from to msg promises2 mem2 kind):
    op mem1 loc from to msg mem2 kind.
  Proof.
    inv WRITE. eapply promise_op; eauto.
  Qed.

  Lemma op_get1
        m1 loc from to msg m2 kind
        l f t m
        (OP: op m1 loc from to msg m2 kind)
        (KIND: op_kind_is_cancel kind = false)
        (GET: get l t m1 = Some (f, m)):
    exists f' m',
      <<GET: get l t m2 = Some (f', m')>> /\
      <<FROM: Time.le f f'>> /\
      <<MSG_LE: Message.le m' m>>.
  Proof.
    inv OP; ss.
    - exploit add_get1; eauto. i. des. esplits; eauto; refl.
    - exploit split_get1; eauto. i. des. esplits; eauto; refl.
    - exploit lower_get1; eauto. i. des. esplits; eauto; refl.
  Qed.

  Lemma op_get2
        m1 l f t msg m2 k
        (OP: op m1 l f t msg m2 k)
        (KIND: op_kind_is_cancel k = false):
    get l t m2 = Some (f, msg).
  Proof.
    inv OP; ss.
    - erewrite add_o; eauto. condtac; ss. des; congr.
    - erewrite split_o; eauto. condtac; ss. des; congr.
    - erewrite lower_o; eauto. condtac; ss. des; congr.
  Qed.

  Lemma op_get_inv
        m1 l f t msg m2 k
        loc from to msg'
        (OP: op m1 l f t msg m2 k)
        (GET2: get loc to m2 = Some (from, msg')):
    loc = l /\ from = f /\ to = t /\ msg' = msg \/
    exists from1,
      (<<GET: get loc to m1 = Some (from1, msg')>>) /\
      (<<FROM: Time.le from1 from>>).
  Proof.
    revert GET2. inv OP.
    - erewrite add_o; eauto. condtac; ss; i.
      + des. clarify. eauto.
      + right. esplits; eauto; refl.
    - erewrite split_o; eauto. repeat condtac; ss; i.
      + des. clarify. eauto.
      + guardH o. des. clarify.
        exploit split_get0; eauto. i. des.
        right. esplits; eauto; try refl.
        inv SPLIT. inv SPLIT0. econs. ss.
      + right. esplits; eauto; refl.
    - erewrite lower_o; eauto. condtac; ss; i.
      + des. clarify. eauto.
      + right. esplits; eauto; refl.
    - erewrite remove_o; eauto. condtac; ss; i.
      + right. esplits; eauto; refl.
  Qed.

  Lemma future_get1
        loc from to msg mem1 mem2
        (LE: future mem1 mem2)
        (GET: get loc to mem1 = Some (from, msg))
        (RESERVE: msg <> Message.reserve):
    exists from' msg',
      <<GET: get loc to mem2 = Some (from', msg')>> /\
      <<FROM: Time.le from from'>> /\
      <<MSG_LE: Message.le msg' msg>>.
  Proof.
    revert from msg GET RESERVE. induction LE.
    { i. esplits; eauto; refl. }
    i. inv H.
    destruct (op_kind_is_cancel kind) eqn:KIND.
    - destruct kind; ss. inv OP.
      exploit IHLE.
      { erewrite remove_o; eauto. condtac; ss; eauto.
        des. subst.
        exploit remove_get0; eauto. i. des. congr. }
      { ss. }
      i. des.
      esplits; eauto.
    - exploit op_get1; eauto. i. des.
      exploit IHLE; eauto.
      { inv MSG_LE; ss. }
      i. des.
      esplits; eauto. etrans; eauto.
  Qed.

  Lemma promise_get0
        promises1 promises2 mem1 mem2
        loc from to msg kind
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind)
        (KIND: op_kind_is_cancel kind = false):
    <<GET_PROMISES: get loc to promises2 = Some (from, msg)>> /\
    <<GET_MEM: get loc to mem2 = Some (from, msg)>>.
  Proof.
    inv PROMISE; ss.
    - erewrite (add_o _ _ PROMISES).
      erewrite (add_o _ _ MEM).
      condtac; ss. des; congr.
    - erewrite (split_o _ _ PROMISES).
      erewrite (split_o _ _ MEM).
      repeat condtac; ss; des; intuition.
    - erewrite (lower_o _ _ PROMISES).
      erewrite (lower_o _ _ MEM).
      condtac; ss. des; congr.
  Qed.

  Lemma promise_get1
        promises1 mem1 loc from to msg promises2 mem2 kind
        l t f m
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind)
        (KIND: op_kind_is_cancel kind = false)
        (GET: get l t mem1 = Some (f, m)):
    exists f' m',
      <<GET: get l t mem2 = Some (f', m')>> /\
      <<FROM: Time.le f f'>> /\
      <<MSG_LE: Message.le m' m>>.
  Proof.
    inv PROMISE; ss.
    - eapply op_get1; eauto.
    - eapply op_get1; eauto.
    - eapply op_get1; eauto.
  Qed.

  Lemma promise_get1_promise
        promises1 mem1 loc from to msg promises2 mem2 kind
        l t f m
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind)
        (KIND: op_kind_is_cancel kind = false)
        (GET: get l t promises1 = Some (f, m)):
    exists f' m',
      <<GET: get l t promises2 = Some (f', m')>> /\
      <<FROM: Time.le f f'>> /\
      <<MSG_LE: Message.le m' m>>.
  Proof.
    inv PROMISE; eapply op_get1; eauto.
  Qed.

  Lemma promise_get2
        promises1 mem1 loc from to msg promises2 mem2 kind
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind)
        (KIND: op_kind_is_cancel kind = false):
    <<GET_PROMISE: get loc to promises2 = Some (from, msg)>> /\
    <<GET_MEM: get loc to mem2 = Some (from, msg)>>.
  Proof.
    inv PROMISE; splits; eauto using op_get2.
  Qed.

  Lemma promise_get_inv
        promises1 mem1 loc from to msg promises2 mem2 kind
        loc2 to2 from2 msg2
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind)
        (GET2: get loc2 to2 mem2 = Some (from2, msg2)):
    loc2 = loc /\ from2 = from /\ to2 = to /\ msg2 = msg \/
    exists from1,
      (<<GET: get loc2 to2 mem1 = Some (from1, msg2)>>) /\
      (<<FROM: Time.le from1 from2>>).
  Proof.
    exploit promise_op; eauto. i.
    eauto using op_get_inv.
  Qed.

  Lemma write_not_cancel
        promises1 mem1 loc from to msg promises2 mem2 kind
        (WRITE: write promises1 mem1 loc from to msg promises2 mem2 kind):
    op_kind_is_cancel kind = false.
  Proof.
    inv WRITE. inv PROMISE; ss.
    exploit remove_get0; try exact PROMISES. i. des.
    exploit remove_get0; try exact REMOVE. i. des. congr.
  Qed.

  Lemma write_get2
        promises1 mem1 loc from to msg promises2 mem2 kind
        (WRITE: write promises1 mem1 loc from to msg promises2 mem2 kind):
    <<GET_PROMISE: get loc to promises2 = None>> /\
    <<GET_MEM: get loc to mem2 = Some (from, msg)>>.
  Proof.
    exploit write_not_cancel; eauto. i.
    inv WRITE. splits.
    - erewrite remove_o; eauto. condtac; ss. des; ss.
    - eapply promise_get2; eauto.
  Qed.

  Lemma write_get_inv
        promises1 mem1 loc from to msg promises2 mem2 kind
        loc2 to2 from2 msg2
        (WRITE: write promises1 mem1 loc from to msg promises2 mem2 kind)
        (GET2: get loc2 to2 mem2 = Some (from2, msg2)):
    loc2 = loc /\ from2 = from /\ to2 = to /\ msg2 = msg \/
    exists from1,
      (<<GET: get loc2 to2 mem1 = Some (from1, msg2)>>) /\
      (<<FROM: Time.le from1 from2>>).
  Proof.
    inv WRITE. eauto using promise_get_inv.
  Qed.


  (* inhabited *)

  Lemma add_inhabited
        mem1 mem2 loc from to msg
        (ADD: add mem1 loc from to msg mem2)
        (INHABITED: inhabited mem1):
    <<INHABITED: inhabited mem2>>.
  Proof.
    ii. erewrite add_o; eauto. condtac; ss.
    des. subst. inv ADD. inv ADD0. inv TO.
  Qed.

  Lemma split_inhabited
        mem1 mem2 loc ts1 ts2 ts3 msg2 msg3
        (SPLIT: split mem1 loc ts1 ts2 ts3 msg2 msg3 mem2)
        (INHABITED: inhabited mem1):
    <<INHABITED: inhabited mem2>>.
  Proof.
    ii. erewrite split_o; eauto. repeat (condtac; ss).
    - des. subst. inv SPLIT. inv SPLIT0. inv TS12.
    - des; subst; try congr. inv SPLIT. inv SPLIT0. inv TS23.
  Qed.

  Lemma lower_inhabited
        mem1 mem2 loc from to msg1 msg2
        (LOWER: lower mem1 loc from to msg1 msg2 mem2)
        (INHABITED: inhabited mem1):
    <<INHABITED: inhabited mem2>>.
  Proof.
    ii. erewrite lower_o; eauto. condtac; ss.
    des. subst. inv LOWER. inv LOWER0. inv TS.
  Qed.

  Lemma cancel_inhabited
        mem1 loc from to msg mem2
        (CANCEL: op mem1 loc from to msg mem2 op_kind_cancel)
        (INHABITED: inhabited mem1):
    <<INHABITED: inhabited mem2>>.
  Proof.
    inv CANCEL. ii.
    erewrite remove_o; eauto. condtac; ss.
    des. subst. exploit remove_get0; eauto. i. des.
    rewrite INHABITED in GET. ss.
  Qed.

  Lemma op_inhabited
        mem1 mem2 loc from to msg kind
        (OP: op mem1 loc from to msg mem2 kind)
        (INHABITED: inhabited mem1):
    inhabited mem2.
  Proof.
    inv OP.
    - eapply add_inhabited; eauto.
    - eapply split_inhabited; eauto.
    - eapply lower_inhabited; eauto.
    - eapply cancel_inhabited; eauto.
  Qed.

  Lemma promise_inhabited
        promises1 mem1 loc from to msg promises2 mem2 kind
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind)
        (INHABITED: inhabited mem1):
    inhabited mem2.
  Proof.
    exploit promise_op; eauto. i.
    eapply op_inhabited; eauto.
  Qed.

  Lemma write_inhabited
        promises1 mem1 loc from to msg promises2 mem2 kind
        (WRITE: write promises1 mem1 loc from to msg promises2 mem2 kind)
        (INHABITED: inhabited mem1):
    inhabited mem2.
  Proof.
    inv WRITE. eauto using promise_inhabited.
  Qed.

  Lemma write_na_inhabited
        ts promises1 mem1 loc from to val promises2 mem2 msgs kinds kind
        (WRITE: write_na ts promises1 mem1 loc from to val promises2 mem2 msgs kinds kind)
        (INHABITED: inhabited mem1):
    inhabited mem2.
  Proof.
    induction WRITE; eauto using write_inhabited.
  Qed.


  (* bot_none *)

  Lemma add_bot_none
        mem1 mem2 loc from to msg
        (ADD: add mem1 loc from to msg mem2)
        (BOT: bot_none mem1):
    <<BOT: bot_none mem2>>.
  Proof.
    ii. erewrite add_o; eauto. condtac; ss.
    des. subst. inv ADD. inv ADD0. inv TO.
  Qed.

  Lemma split_bot_none
        mem1 mem2 loc ts1 ts2 ts3 msg2 msg3
        (SPLIT: split mem1 loc ts1 ts2 ts3 msg2 msg3 mem2)
        (BOT: bot_none mem1):
    <<BOT: bot_none mem2>>.
  Proof.
    ii. erewrite split_o; eauto. repeat (condtac; ss).
    - des. subst. inv SPLIT. inv SPLIT0. inv TS12.
    - des; subst; try congr. inv SPLIT. inv SPLIT0. inv TS23.
  Qed.

  Lemma lower_bot_none
        mem1 mem2 loc from to msg1 msg2
        (LOWER: lower mem1 loc from to msg1 msg2 mem2)
        (BOT: bot_none mem1):
    <<BOT: bot_none mem2>>.
  Proof.
    ii. erewrite lower_o; eauto. condtac; ss.
    des. subst. inv LOWER. inv LOWER0. inv TS.
  Qed.

  Lemma remove_bot_none
        mem1 mem2 loc from to msg
        (CANCEL: remove mem1 loc from to msg mem2)
        (BOT: bot_none mem1):
    <<BOT: bot_none mem2>>.
  Proof.
    ii. erewrite remove_o; eauto. condtac; ss.
  Qed.

  Lemma op_bot_none
        mem1 loc from to msg mem2 kind
        (OP: op mem1 loc from to msg mem2 kind)
        (BOT: bot_none mem1):
    <<BOT: bot_none mem2>>.
  Proof.
    inv OP.
    - eapply add_bot_none; eauto.
    - eapply split_bot_none; eauto.
    - eapply lower_bot_none; eauto.
    - eapply remove_bot_none; eauto.
  Qed.

  Lemma promise_bot_none
        promises1 mem1 loc from to msg promises2 mem2 kind
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind)
        (BOT: bot_none promises1):
    <<BOT: bot_none promises2>>.
  Proof.
    exploit promise_op_promise; eauto. i.
    eapply op_bot_none; eauto.
  Qed.

  Lemma write_bot_none
        promises1 mem1 loc from to msg promises2 mem2 kind
        (WRITE: write promises1 mem1 loc from to msg promises2 mem2 kind)
        (BOT: bot_none promises1):
    <<BOT: bot_none promises2>>.
  Proof.
    inv WRITE.
    eapply remove_bot_none; eauto.
    eapply promise_bot_none; eauto.
  Qed.

  Lemma write_na_bot_none
        ts promises1 mem1 loc from to val promises2 mem2 msgs kinds kind
        (WRITE: write_na ts promises1 mem1 loc from to val promises2 mem2 msgs kinds kind)
        (BOT: bot_none promises1):
    <<BOT: bot_none promises2>>.
  Proof.
    induction WRITE; eauto using write_bot_none.
    apply IHWRITE.
    eapply write_bot_none; eauto.
  Qed.


  (* le *)

  Lemma remove_le
        promises1 loc from to msg promises2 mem
        (REMOVE: remove promises1 loc from to msg promises2)
        (LE1: le promises1 mem):
    <<LE2: le promises2 mem>>.
  Proof.
    ii. revert LHS.
    erewrite remove_o; eauto. condtac; ss. eauto.
  Qed.

  Lemma promise_le
        promises1 mem1 loc from to msg promises2 mem2 kind
        (LE_PROMISES1: le promises1 mem1)
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind):
    <<LE_PROMISES2: le promises2 mem2>>.
  Proof.
    inv PROMISE.
    - ii. revert LHS.
      erewrite add_o; eauto. erewrite (@add_o mem2); try exact MEM; eauto.
      condtac; ss. auto.
    - ii. revert LHS.
      erewrite split_o; eauto. erewrite (@split_o mem2); try exact MEM; eauto.
      repeat condtac; ss. auto.
    - ii. revert LHS.
      erewrite lower_o; eauto. erewrite (@lower_o mem2); try exact MEM; eauto.
      condtac; ss. auto.
    - ii. revert LHS.
      erewrite remove_o; eauto. erewrite (@remove_o mem2); try exact MEM; eauto.
      condtac; ss. auto.
  Qed.

  Lemma write_le
        promises1 mem1 loc from to msg promises2 mem2 kind
        (LE_PROMISES1: le promises1 mem1)
        (WRITE: write promises1 mem1 loc from to msg promises2 mem2 kind):
    <<LE_PROMISES2: le promises2 mem2>>.
  Proof.
    inv WRITE.
    eapply remove_le; eauto.
    eapply promise_le; eauto.
  Qed.

  Lemma write_na_le
        ts promises1 mem1 loc from to val promises2 mem2 msgs kinds kind
        (LE_PROMISES1: le promises1 mem1)
        (WRITE: write_na ts promises1 mem1 loc from to val promises2 mem2 msgs kinds kind):
    <<LE_PROMISES2: le promises2 mem2>>.
  Proof.
    induction WRITE; eauto using write_le.
    apply IHWRITE.
    eapply write_le; eauto.
  Qed.


  (* Lemmas on closedness *)

  Lemma join_closed_timemap
        lhs rhs mem
        (LHS: closed_timemap lhs mem)
        (RHS: closed_timemap rhs mem):
    closed_timemap (TimeMap.join lhs rhs) mem.
  Proof.
    ii. unfold TimeMap.join.
    destruct (Time.join_cases (lhs loc) (rhs loc)) as [X|X]; rewrite X.
    - apply LHS.
    - apply RHS.
  Qed.

  Lemma join_closed_view
        lhs rhs mem
        (LHS: closed_view lhs mem)
        (RHS: closed_view rhs mem):
    closed_view (View.join lhs rhs) mem.
  Proof.
    econs.
    - apply join_closed_timemap.
      + apply LHS.
      + apply RHS.
    - apply join_closed_timemap.
      + apply LHS.
      + apply RHS.
  Qed.

  Lemma add_closed_timemap
        times
        mem1 loc from to msg mem2
        (ADD: add mem1 loc from to msg mem2)
        (CLOSED: closed_timemap times mem1):
    closed_timemap times mem2.
  Proof.
    ii. erewrite add_o; eauto. condtac; ss.
    des. subst. exfalso.
    specialize (CLOSED loc). des.
    exploit add_get0; eauto. i. des. congr.
  Qed.

  Lemma add_closed_view
        view
        mem1 loc from to msg mem2
        (ADD: add mem1 loc from to msg mem2)
        (CLOSED: closed_view view mem1):
    closed_view view mem2.
  Proof.
    inv CLOSED. econs; eauto.
    - eapply add_closed_timemap; eauto.
    - eapply add_closed_timemap; eauto.
  Qed.

  Lemma add_closed_opt_view
        view
        mem1 loc from to msg mem2
        (ADD: add mem1 loc from to msg mem2)
        (CLOSED: closed_opt_view view mem1):
    closed_opt_view view mem2.
  Proof.
    inv CLOSED; econs. eapply add_closed_view; eauto.
  Qed.

  Lemma add_closed_message
        msg'
        mem1 loc from to msg mem2
        (ADD: add mem1 loc from to msg mem2)
        (CLOSED: closed_message msg' mem1):
    closed_message msg' mem2.
  Proof.
    destruct msg'; ss. inv CLOSED. econs.
    eapply add_closed_opt_view; eauto.
  Qed.

  Lemma add_closed
        mem1 loc from to msg mem2
        (ADD: add mem1 loc from to msg mem2)
        (CLOSED: closed mem1)
        (MSG_CLOSED: closed_message msg mem2)
        (MSG_TS: message_to msg loc to):
    closed mem2.
  Proof.
    inv CLOSED. econs.
    - i. revert MSG. erewrite add_o; eauto. condtac; ss.
      + des. subst. i. inv MSG. splits; auto.
        inv ADD. inv ADD0. auto.
      + guardH o. i. exploit CLOSED0; eauto. i. des. splits; auto.
        eapply add_closed_message; eauto.
    - eapply add_inhabited; eauto.
  Qed.

  Lemma split_closed_timemap
        times
        mem1 loc ts1 ts2 ts3 msg2 msg3 mem2
        (SPLIT: split mem1 loc ts1 ts2 ts3 msg2 msg3 mem2)
        (CLOSED: closed_timemap times mem1):
    closed_timemap times mem2.
  Proof.
    ii. erewrite split_o; eauto. repeat condtac; ss.
    - des. subst. exfalso.
      specialize (CLOSED loc). des.
      exploit split_get0; eauto. i. des. congr.
    - guardH o. des. subst.
      specialize (CLOSED loc). des.
      exploit split_get0; eauto. i. des.
      rewrite CLOSED in *. inv GET0. eauto.
  Qed.

  Lemma split_closed_view
        view
        mem1 loc ts1 ts2 ts3 msg2 msg3 mem2
        (SPLIT: split mem1 loc ts1 ts2 ts3 msg2 msg3 mem2)
        (CLOSED: closed_view view mem1):
    closed_view view mem2.
  Proof.
    inv CLOSED. econs; eauto.
    - eapply split_closed_timemap; eauto.
    - eapply split_closed_timemap; eauto.
  Qed.

  Lemma split_closed_opt_view
        view
        mem1 loc ts1 ts2 ts3 msg2 msg3 mem2
        (SPLIT: split mem1 loc ts1 ts2 ts3 msg2 msg3 mem2)
        (CLOSED: closed_opt_view view mem1):
    closed_opt_view view mem2.
  Proof.
    inv CLOSED; econs. eapply split_closed_view; eauto.
  Qed.

  Lemma split_closed_message
        msg'
        mem1 loc ts1 ts2 ts3 msg2 msg3 mem2
        (SPLIT: split mem1 loc ts1 ts2 ts3 msg2 msg3 mem2)
        (CLOSED: closed_message msg' mem1):
    closed_message msg' mem2.
  Proof.
    destruct msg'; ss. inv CLOSED. econs.
    eapply split_closed_opt_view; eauto.
  Qed.

  Lemma split_closed
        mem1 loc ts1 ts2 ts3 msg2 msg3 mem2
        (SPLIT: split mem1 loc ts1 ts2 ts3 msg2 msg3 mem2)
        (CLOSED: closed mem1)
        (MSG_CLOSED: closed_message msg2 mem2)
        (MSG_TS: message_to msg2 loc ts2):
    closed mem2.
  Proof.
    inv CLOSED. econs.
    - i. revert MSG. erewrite split_o; eauto. repeat condtac; ss.
      + des. subst. i. inv MSG. splits; eauto.
        inv SPLIT. inv SPLIT0. auto.
      + guardH o. des. subst. i. inv MSG.
        exploit split_get0; eauto. i. des. exploit CLOSED0; eauto. i. des.
        splits; eauto.
        eapply split_closed_message; eauto.
      + guardH o. guardH o0. i. exploit CLOSED0; eauto. i. des. splits; auto.
        eapply split_closed_message; eauto.
    - eapply split_inhabited; eauto.
  Qed.

  Lemma lower_closed_timemap
        times
        mem1 loc from to msg1 msg2 mem2
        (LOWER: lower mem1 loc from to msg1 msg2 mem2)
        (CLOSED: closed_timemap times mem1):
    closed_timemap times mem2.
  Proof.
    ii. erewrite lower_o; eauto. condtac; ss. des. subst.
    specialize (CLOSED loc). des.
    exploit lower_get0; eauto. i. des.
    rewrite CLOSED in *. inv GET. inv MSG_LE. eauto.
  Qed.

  Lemma lower_closed_view
        view
        mem1 loc from to msg1 msg2 mem2
        (LOWER: lower mem1 loc from to msg1 msg2 mem2)
        (CLOSED: closed_view view mem1):
    closed_view view mem2.
  Proof.
    inv CLOSED. econs; eauto.
    - eapply lower_closed_timemap; eauto.
    - eapply lower_closed_timemap; eauto.
  Qed.

  Lemma lower_closed_opt_view
        view
        mem1 loc from to msg1 msg2 mem2
        (LOWER: lower mem1 loc from to msg1 msg2 mem2)
        (CLOSED: closed_opt_view view mem1):
    closed_opt_view view mem2.
  Proof.
    inv CLOSED; econs. eapply lower_closed_view; eauto.
  Qed.

  Lemma lower_closed_message
        msg'
        mem1 loc from to msg1 msg2 mem2
        (LOWER: lower mem1 loc from to msg1 msg2 mem2)
        (CLOSED: closed_message msg' mem1):
    closed_message msg' mem2.
  Proof.
    destruct msg'; ss. inv CLOSED. econs.
    eapply lower_closed_opt_view; eauto.
  Qed.

  Lemma lower_closed
        mem1 loc from to msg1 msg2 mem2
        (LOWER: lower mem1 loc from to msg1 msg2 mem2)
        (CLOSED: closed mem1)
        (MSG_CLOSED: closed_message msg2 mem2)
        (MSG_TS: message_to msg2 loc to):
    closed mem2.
  Proof.
    inv CLOSED. econs.
    - i. revert MSG. erewrite lower_o; eauto. condtac; ss.
      + des. subst. i. inv MSG. splits; auto.
        inv LOWER. inv LOWER0. auto.
      + guardH o. i. exploit CLOSED0; eauto. i. des. splits; auto.
        eapply lower_closed_message; eauto.
    - eapply lower_inhabited; eauto.
  Qed.

  Lemma cancel_closed_timemap
        times
        mem1 loc from to mem2
        (CANCEL: remove mem1 loc from to Message.reserve mem2)
        (CLOSED: closed_timemap times mem1):
    closed_timemap times mem2.
  Proof.
    ii. erewrite remove_o; eauto. condtac; ss.
    des. subst. exploit remove_get0; eauto. i. des.
    destruct (CLOSED loc). des. congr.
  Qed.

  Lemma cancel_closed_view
        view
        mem1 loc from to mem2
        (CANCEL: remove mem1 loc from to Message.reserve mem2)
        (CLOSED: closed_view view mem1):
    closed_view view mem2.
  Proof.
    inv CLOSED. econs; eauto.
    - eapply cancel_closed_timemap; eauto.
    - eapply cancel_closed_timemap; eauto.
  Qed.

  Lemma cancel_closed_opt_view
        view
        mem1 loc from to mem2
        (CANCEL: remove mem1 loc from to Message.reserve mem2)
        (CLOSED: closed_opt_view view mem1):
    closed_opt_view view mem2.
  Proof.
    inv CLOSED; econs. eapply cancel_closed_view; eauto.
  Qed.

  Lemma cancel_closed_message
        msg'
        mem1 loc from to mem2
        (CANCEL: remove mem1 loc from to Message.reserve mem2)
        (CLOSED: closed_message msg' mem1):
    closed_message msg' mem2.
  Proof.
    destruct msg'; ss. inv CLOSED. econs.
    eapply cancel_closed_opt_view; eauto.
  Qed.

  Lemma cancel_closed
        mem1 loc from to mem2
        (CANCEL: remove mem1 loc from to Message.reserve mem2)
        (CLOSED: closed mem1):
    closed mem2.
  Proof.
    inv CLOSED. econs.
    - i. revert MSG. erewrite remove_o; eauto. condtac; ss.
      guardH o. i. exploit CLOSED0; eauto. i. des.
      splits; auto.
      eapply cancel_closed_message; eauto.
    - eapply cancel_inhabited; eauto.
  Qed.

  Lemma op_closed_timemap
        times
        mem1 loc from to msg mem2 kind
        (OP: op mem1 loc from to msg mem2 kind)
        (CLOSED: closed_timemap times mem1):
    closed_timemap times mem2.
  Proof.
    inv OP.
    - eapply add_closed_timemap; eauto.
    - eapply split_closed_timemap; eauto.
    - eapply lower_closed_timemap; eauto.
    - eapply cancel_closed_timemap; eauto.
  Qed.

  Lemma op_closed_view
        view
        mem1 loc from to msg mem2 kind
        (OP: op mem1 loc from to msg mem2 kind)
        (CLOSED: closed_view view mem1):
    closed_view view mem2.
  Proof.
    inv OP.
    - eapply add_closed_view; eauto.
    - eapply split_closed_view; eauto.
    - eapply lower_closed_view; eauto.
    - eapply cancel_closed_view; eauto.
  Qed.

  Lemma op_closed_opt_view
        kind view
        mem1 loc from to msg mem2
        (OP: Memory.op mem1 loc from to msg mem2 kind)
        (CLOSED: Memory.closed_opt_view view mem1):
    closed_opt_view view mem2.
  Proof.
    inv OP; eauto using add_closed_opt_view, split_closed_opt_view, lower_closed_opt_view, cancel_closed_opt_view.
  Qed.

  Lemma op_closed_message
        kind msg'
        mem1 loc from to msg mem2
        (OP: Memory.op mem1 loc from to msg mem2 kind)
        (CLOSED: Memory.closed_message msg' mem1):
    closed_message msg' mem2.
  Proof.
    inv OP; eauto using add_closed_message, split_closed_message, lower_closed_message, cancel_closed_message.
  Qed.

  Lemma op_closed
        mem1 loc from to msg mem2 kind
        (OP: op mem1 loc from to msg mem2 kind)
        (CLOSED: closed mem1)
        (MSG_CLOSED: closed_message msg mem2)
        (MSG_TS: message_to msg loc to):
    closed mem2.
  Proof.
    inv OP; eauto using add_closed, split_closed, lower_closed, cancel_closed.
  Qed.

  Lemma promise_closed
        promises1 mem1 loc from to msg promises2 mem2 kind
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind)
        (CLOSED: closed mem1)
        (MSG_CLOSED: closed_message msg mem2)
        (MSG_TS: message_to msg loc to):
    closed mem2.
  Proof.
    eapply op_closed; eauto.
    eapply promise_op; eauto.
  Qed.

  Lemma write_closed
        promises1 mem1 loc from to msg promises2 mem2 kind
        (WRITE: write promises1 mem1 loc from to msg promises2 mem2 kind)
        (CLOSED: closed mem1)
        (MSG_CLOSED: closed_message msg mem2)
        (MSG_TS: message_to msg loc to):
    closed mem2.
  Proof.
    inv WRITE.
    eapply promise_closed; eauto.
  Qed.

  Lemma write_na_closed
        ts promises1 mem1 loc from to val promises2 mem2 msgs kinds kind
        (WRITE: write_na ts promises1 mem1 loc from to val promises2 mem2 msgs kinds kind)
        (CLOSED: closed mem1):
    closed mem2.
  Proof.
    induction WRITE.
    { eapply write_closed; eauto.
      econs. apply Time.bot_spec. }
    apply IHWRITE.
    eapply write_closed; eauto.
    - unguard. des; subst; eauto.
    - unguard. des; subst; eauto.
      econs. apply Time.bot_spec.
  Qed.

  Lemma promise_closed_timemap
        times
        promises1 mem1 loc from to msg promises2 mem2 kind
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind)
        (CLOSED: closed_timemap times mem1):
    closed_timemap times mem2.
  Proof.
    eapply op_closed_timemap; eauto.
    eapply promise_op. eauto.
  Qed.

  Lemma promise_closed_view
        view
        promises1 mem1 loc from to msg promises2 mem2 kind
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind)
        (CLOSED: closed_view view mem1):
    closed_view view mem2.
  Proof.
    eapply op_closed_view; eauto.
    eapply promise_op. eauto.
  Qed.

  Lemma promise_closed_opt_view
        view
        promises1 mem1 loc from to msg promises2 mem2 kind
        (CLOSED: closed_opt_view view mem1)
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind):
    closed_opt_view view mem2.
  Proof.
    inv CLOSED; econs. eapply promise_closed_view; eauto.
  Qed.

  Lemma write_closed_timemap
        times
        promises1 mem1 loc from to msg promises2 mem2 kind
        (WRITE: write promises1 mem1 loc from to msg promises2 mem2 kind)
        (CLOSED: closed_timemap times mem1):
    closed_timemap times mem2.
  Proof.
    eapply op_closed_timemap; eauto.
    eapply write_op. eauto.
  Qed.

  Lemma write_closed_view
        view
        promises1 mem1 loc from to msg promises2 mem2 kind
        (WRITE: write promises1 mem1 loc from to msg promises2 mem2 kind)
        (CLOSED: closed_view view mem1):
    closed_view view mem2.
  Proof.
    eapply op_closed_view; eauto.
    eapply write_op. eauto.
  Qed.

  Lemma write_closed_opt_view
        view
        promises1 mem1 loc from to msg promises2 mem2 kind
        (CLOSED: closed_opt_view view mem1)
        (WRITE: write promises1 mem1 loc from to msg promises2 mem2 kind):
    closed_opt_view view mem2.
  Proof.
    inv CLOSED; econs. eapply write_closed_view; eauto.
  Qed.

  Lemma write_na_closed_timemap
        times
        ts promises1 mem1 loc from to val promises2 mem2 msgs kinds kind
        (WRITE: write_na ts promises1 mem1 loc from to val promises2 mem2 msgs kinds kind)
        (CLOSED: closed_timemap times mem1):
    closed_timemap times mem2.
  Proof.
    induction WRITE; eauto using write_closed_timemap.
  Qed.

  Lemma write_na_closed_view
        view
        ts promises1 mem1 loc from to val promises2 mem2 msgs kinds kind
        (WRITE: write_na ts promises1 mem1 loc from to val promises2 mem2 msgs kinds kind)
        (CLOSED: closed_view view mem1):
    closed_view view mem2.
  Proof.
    induction WRITE; eauto using write_closed_view.
  Qed.

  Lemma write_na_closed_opt_view
        view
        ts promises1 mem1 loc from to val promises2 mem2 msgs kinds kind
        (WRITE: write_na ts promises1 mem1 loc from to val promises2 mem2 msgs kinds kind)
        (CLOSED: closed_opt_view view mem1):
    closed_opt_view view mem2.
  Proof.
    inv CLOSED; econs. eapply write_na_closed_view; eauto.
  Qed.

  Lemma future_closed_timemap
        times mem1 mem2
        (CLOSED: closed_timemap times mem1)
        (FUTURE: future mem1 mem2):
    closed_timemap times mem2.
  Proof.
    revert CLOSED. induction FUTURE; auto. i.
    apply IHFUTURE. inv H. eapply op_closed_timemap; eauto.
  Qed.

  Lemma future_closed_view
        view mem1 mem2
        (FUTURE: future mem1 mem2)
        (CLOSED: closed_view view mem1):
    closed_view view mem2.
  Proof.
    revert CLOSED. induction FUTURE; auto. i.
    apply IHFUTURE. inv H. eapply op_closed_view; eauto.
  Qed.

  Lemma future_closed_opt_view
        view mem1 mem2
        (FUTURE: future mem1 mem2)
        (CLOSED: closed_opt_view view mem1):
    closed_opt_view view mem2.
  Proof.
    inv CLOSED; econs. eapply future_closed_view; eauto.
  Qed.

  Lemma future_closed_message
        msg mem1 mem2
        (FUTURE: future mem1 mem2)
        (CLOSED: closed_message msg mem1):
    closed_message msg mem2.
  Proof.
    inv CLOSED; econs. eapply future_closed_opt_view; eauto.
  Qed.

  Lemma future_closed
        mem1 mem2
        (FUTURE: future mem1 mem2)
        (CLOSED: closed mem1):
    closed mem2.
  Proof.
    revert CLOSED. induction FUTURE; auto. i. apply IHFUTURE.
    inv H. eapply op_closed; eauto.
  Qed.

  Lemma singleton_closed_timemap
        loc from to val released mem
        (GET: get loc to mem = Some (from, Message.concrete val released))
        (INHABITED: inhabited mem):
    closed_timemap (TimeMap.singleton loc to) mem.
  Proof.
    unfold TimeMap.singleton, LocFun.add, LocFun.find. ii. condtac.
    - subst. eauto.
    - apply closed_timemap_bot. auto.
  Qed.

  Lemma singleton_ur_closed_view
        loc from to val released mem
        (GET: get loc to mem = Some (from, Message.concrete val released))
        (INHABITED: inhabited mem):
    closed_view (View.singleton_ur loc to) mem.
  Proof.
    econs; s.
    - eapply singleton_closed_timemap; eauto.
    - eapply singleton_closed_timemap; eauto.
  Qed.

  Lemma singleton_rw_closed_view
        loc from to val released mem
        (GET: get loc to mem = Some (from, Message.concrete val released))
        (INHABITED: inhabited mem):
    closed_view (View.singleton_rw loc to) mem.
  Proof.
    econs; s.
    - apply closed_timemap_bot. auto.
    - eapply singleton_closed_timemap; eauto.
  Qed.

  Lemma singleton_ur_if_closed_view
        cond loc from to val released mem
        (GET: get loc to mem = Some (from, Message.concrete val released))
        (INHABITED: inhabited mem):
    closed_view (View.singleton_ur_if cond loc to) mem.
  Proof.
    destruct cond; ss.
    - eapply singleton_ur_closed_view; eauto.
    - eapply singleton_rw_closed_view; eauto.
  Qed.


  (* get from different loc *)

  Lemma add_get_diff
        mem1 loc from to msg mem2
        loc'
        (ADD: add mem1 loc from to msg mem2)
        (LOC: loc' <> loc):
    forall to', get loc' to' mem2 = get loc' to' mem1.
  Proof.
    i. erewrite add_o; eauto. condtac; ss. des. ss.
  Qed.

  Lemma split_get_diff
        mem1 loc ts1 ts2 ts3 msg2 msg3 mem2
        loc'
        (SPLIT: split mem1 loc ts1 ts2 ts3 msg2 msg3 mem2)
        (LOC: loc' <> loc):
    forall to', get loc' to' mem2 = get loc' to' mem1.
  Proof.
    i. erewrite split_o; eauto. repeat (condtac; ss); des; ss.
  Qed.

  Lemma lower_get_diff
        mem1 loc from to msg1 msg2 mem2
        loc'
        (LOWER: lower mem1 loc from to msg1 msg2 mem2)
        (LOC: loc' <> loc):
    forall to', get loc' to' mem2 = get loc' to' mem1.
  Proof.
    i. erewrite lower_o; eauto. condtac; ss. des. ss.
  Qed.

  Lemma remove_get_diff
        mem1 loc from to msg mem2
        loc'
        (REMOVE: remove mem1 loc from to msg mem2)
        (LOC: loc' <> loc):
    forall to', get loc' to' mem2 = get loc' to' mem1.
  Proof.
    i. erewrite remove_o; eauto. condtac; ss. des. ss.
  Qed.

  Lemma op_get_diff
        mem1 loc from to msg mem2 kind
        loc'
        (OP: op mem1 loc from to msg mem2 kind)
        (LOC: loc' <> loc):
    forall to', get loc' to' mem2 = get loc' to' mem1.
  Proof.
    inv OP; eauto using add_get_diff, split_get_diff, lower_get_diff, remove_get_diff.
  Qed.

  Lemma promise_get_diff
        promises1 mem1 loc from to msg promises2 mem2 kind
        loc'
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind)
        (LOC: loc' <> loc):
    forall to', get loc' to' mem2 = get loc' to' mem1.
  Proof.
    inv PROMISE; eauto using add_get_diff, split_get_diff, lower_get_diff, remove_get_diff.
  Qed.

  Lemma promise_get_diff_promise
        promises1 mem1 loc from to msg promises2 mem2 kind
        loc'
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind)
        (LOC: loc' <> loc):
    forall to', get loc' to' promises2 = get loc' to' promises1.
  Proof.
    inv PROMISE; eauto using add_get_diff, split_get_diff, lower_get_diff, remove_get_diff.
  Qed.

  Lemma write_get_diff
        promises1 mem1 loc from to msg promises2 mem2 kind
        loc'
        (WRITE: write promises1 mem1 loc from to msg promises2 mem2 kind)
        (LOC: loc' <> loc):
    forall to', get loc' to' mem2 = get loc' to' mem1.
  Proof.
    i. inv WRITE.
    eauto using promise_get_diff.
  Qed.

  Lemma write_get_diff_promise
        promises1 mem1 loc from to msg promises2 mem2 kind
        loc'
        (WRITE: write promises1 mem1 loc from to msg promises2 mem2 kind)
        (LOC: loc' <> loc):
    forall to', get loc' to' promises2 = get loc' to' promises1.
  Proof.
    i. inv WRITE.
    erewrite remove_get_diff; try exact REMOVE; ss.
    eauto using promise_get_diff_promise.
  Qed.

  Lemma write_na_get_diff
        ts promises1 mem1 loc from to val promises2 mem2 msgs kinds kind
        loc'
        (WRITE: write_na ts promises1 mem1 loc from to val promises2 mem2 msgs kinds kind)
        (LOC: loc' <> loc):
    forall to', get loc' to' mem2 = get loc' to' mem1.
  Proof.
    induction WRITE; eauto using write_get_diff.
    i. erewrite IHWRITE; eauto.
    eapply write_get_diff; eauto.
  Qed.

  Lemma write_na_get_diff_promise
        ts promises1 mem1 loc from to val promises2 mem2 msgs kinds kind
        loc'
        (WRITE: write_na ts promises1 mem1 loc from to val promises2 mem2 msgs kinds kind)
        (LOC: loc' <> loc):
    forall to', get loc' to' promises2 = get loc' to' promises1.
  Proof.
    induction WRITE; eauto using write_get_diff_promise.
    i. erewrite IHWRITE; eauto.
    eapply write_get_diff_promise; eauto.
  Qed.


  (* finite *)

  Definition finite (mem:t): Prop :=
    exists dom,
    forall loc from to msg (GET: get loc to mem = Some (from, msg)),
      List.In (loc, to) dom.

  Lemma bot_finite: finite bot.
  Proof.
    exists []. ii. rewrite bot_get in *. congr.
  Qed.

  Lemma add_finite
        mem1 loc from to msg mem2
        (ADD: add mem1 loc from to msg mem2)
        (FINITE: finite mem1):
    finite mem2.
  Proof.
    unfold finite in *. des. exists ((loc, to) :: dom). i.
    revert GET. erewrite add_o; eauto. condtac; ss; eauto.
    i. des. inv GET. auto.
  Qed.

  Lemma split_finite
        mem1 loc ts1 ts2 ts3 msg2 msg3 mem2
        (SPLIT: split mem1 loc ts1 ts2 ts3 msg2 msg3 mem2)
        (FINITE: finite mem1):
    finite mem2.
  Proof.
    unfold finite in *. des. exists ((loc, ts2) :: dom). i.
    revert GET. erewrite split_o; eauto. repeat condtac; ss; eauto.
    - i. des. inv GET. auto.
    - guardH o. i. des. inv GET. right. eapply FINITE.
      hexploit split_get0; eauto. i. des. eauto.
  Qed.

  Lemma lower_finite
        mem1 loc from to msg1 msg2 mem2
        (LOWER: lower mem1 loc from to msg1 msg2 mem2)
        (FINITE: finite mem1):
    finite mem2.
  Proof.
    unfold finite in *. des. exists dom. i.
    revert GET. erewrite lower_o; eauto. condtac; ss; eauto.
    i. des. inv GET. eapply FINITE.
    hexploit lower_get0; eauto. i. des. eauto.
  Qed.

  Lemma remove_finite
        mem1 loc from to msg mem2
        (REMOVE: remove mem1 loc from to msg mem2)
        (FINITE: finite mem1):
    finite mem2.
  Proof.
    unfold finite in *. des. exists dom. i.
    revert GET. erewrite remove_o; eauto. condtac; ss; eauto.
  Qed.

  Lemma op_finite
        mem1 loc from to msg mem2 kind
        (OP: op mem1 loc from to msg mem2 kind)
        (FINITE: finite mem1):
    finite mem2.
  Proof.
    inv OP; eauto using add_finite, split_finite, lower_finite, remove_finite.
  Qed.

  Lemma promise_finite
        promises1 mem1 loc from to msg promises2 mem2 kind
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind)
        (FINITE: finite promises1):
    finite promises2.
  Proof.
    exploit promise_op_promise; eauto. i.
    eapply op_finite; eauto.
  Qed.

  Lemma write_finite
        promises1 mem1 loc from to msg promises2 mem2 kind
        (WRITE: write promises1 mem1 loc from to msg promises2 mem2 kind)
        (FINITE: finite promises1):
    finite promises2.
  Proof.
    inv WRITE.
    eapply remove_finite; eauto.
    eapply promise_finite; eauto.
  Qed.

  Lemma write_na_finite
        ts promises1 mem1 loc from to val promises2 mem2 msgs kinds kind
        (WRITE: write_na ts promises1 mem1 loc from to val promises2 mem2 msgs kinds kind)
        (FINITE: finite promises1):
    finite promises2.
  Proof.
    induction WRITE; eauto using write_finite.
  Qed.


  (* future *)

  Lemma op_future
        mem1 loc from to msg mem2 kind
        (OP: op mem1 loc from to msg mem2 kind)
        (CLOSED1: closed mem1)
        (MSG_CLOSED: closed_message msg mem2)
        (MSG_TS: message_to msg loc to):
    <<CLOSED2: closed mem2>> /\
    <<FUTURE: future mem1 mem2>> /\
    <<MSG_WF: Message.wf msg>>.
  Proof.
    hexploit op_inhabited; try apply CLOSED1; eauto. i. splits; auto.
    - eapply op_closed; eauto.
    - econs 2; eauto.
    - inv OP.
      + inv ADD. inv ADD0. ss.
      + inv SPLIT. inv SPLIT0. ss.
      + inv LOWER. inv LOWER0. ss.
      + econs.
  Qed.

  Lemma promise_future
        promises1 mem1 loc from to msg promises2 mem2 kind
        (LE_PROMISES1: le promises1 mem1)
        (FINITE1: finite promises1)
        (BOT1: bot_none promises1)
        (CLOSED1: closed mem1)
        (MSG_CLOSED: closed_message msg mem2)
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind):
    <<LE_PROMISES2: le promises2 mem2>> /\
    <<FINITE2: finite promises2>> /\
    <<BOT2: bot_none promises2>> /\
    <<CLOSED2: closed mem2>> /\
    <<FUTURE: future mem1 mem2>>.
  Proof.
    hexploit promise_le; eauto. i. des.
    hexploit promise_inhabited; try apply CLOSED1; eauto. i.
    hexploit promise_finite; eauto. i.
    hexploit promise_bot_none; eauto. i.
    hexploit op_future; eauto.
    { eapply promise_op. eauto. }
    { by inv PROMISE. }
    i. des. eauto.
  Qed.

  Lemma promise_disjoint
        promises1 mem1 loc from to msg promises2 mem2 ctx kind
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind)
        (LE_CTX: le ctx mem1)
        (DISJOINT: disjoint promises1 ctx):
    <<DISJOINT: disjoint promises2 ctx>> /\
    <<LE_CTX: le ctx mem2>>.
  Proof.
    inv PROMISE.
    - splits.
      + inv DISJOINT. econs. i. revert GET1. erewrite add_o; eauto. condtac; ss.
        * des. subst. i. inv GET1. splits.
          { inv MEM. inv ADD. eauto. }
          { ii. inv H. inv MEM. inv ADD. inv TO. }
        * i. eapply DISJOINT0; eauto.
      + ii. erewrite add_o; eauto. condtac; ss; eauto.
        des. subst. exfalso. inv MEM. inv ADD. eapply DISJOINT0; eauto.
        * apply Interval.mem_ub. auto.
        * apply Interval.mem_ub.
          destruct (Cell.WF (mem1 loc)). exploit VOLUME; eauto. intros x. des; auto.
          inv x. inv TO.
    - splits.
      + inv DISJOINT. econs. i. revert GET1. erewrite split_o; eauto. repeat condtac; ss.
        * des. subst. i. inv GET1.
          exploit split_get0; try exact PROMISES; eauto. i. des.
          exploit DISJOINT0; try exact GET0; eauto. i. des.
          splits.
          { eapply Interval.le_disjoint; eauto. econs; [refl|].
            left. inv MEM. inv SPLIT. auto.
          }
          { ii. inv H. inv MEM. inv SPLIT. inv TS12. }
        * guardH o. des. subst. i. inv GET1.
          exploit split_get0; try exact PROMISES; eauto. i. des.
          exploit DISJOINT0; try exact GET0; eauto. i. des.
          splits.
          { eapply Interval.le_disjoint; eauto. econs; [|refl].
            left. inv MEM. inv SPLIT. auto.
          }
          { ii. inv H. inv MEM. inv SPLIT. inv TS23. }
        * i. eapply DISJOINT0; eauto.
      + ii. erewrite split_o; eauto. repeat condtac; ss; eauto.
        * des. subst. exfalso. inv DISJOINT. exploit DISJOINT0; eauto.
          { hexploit split_get0; try exact PROMISES; eauto. i. des. eauto. }
          intros x. des. eapply x.
          { inv MEM. inv SPLIT. econs. eauto. left. auto. }
          { apply Interval.mem_ub.
            destruct (Cell.WF (mem1 loc)). exploit VOLUME; eauto. intros x1. des; auto.
            inv x1. inv MEM. inv SPLIT. inv TS12.
          }
        * guardH o. des. subst. exfalso. inv DISJOINT. exploit DISJOINT0; eauto.
          { hexploit split_get0; try exact PROMISES; eauto. i. des. eauto. }
          intros x. des. eapply x.
          { apply Interval.mem_ub. inv MEM. inv SPLIT. etrans; eauto. }
          { apply Interval.mem_ub.
            destruct (Cell.WF (ctx loc)). exploit VOLUME; eauto. intros x1. des; auto.
            inv x1. inv MEM. inv SPLIT. inv TS23.
          }
    - splits.
      + inv DISJOINT. econs. i. revert GET1. erewrite lower_o; eauto. condtac; ss.
        * des. subst. i. inv GET1. eapply DISJOINT0; eauto.
          hexploit lower_get0; try eapply PROMISES; eauto. i. des. eauto.
        * i. eapply DISJOINT0; eauto.
      + ii. erewrite lower_o; eauto. condtac; ss; eauto.
        des. subst. exfalso. eapply disjoint_get; eauto.
        hexploit lower_get0; try exact PROMISES; eauto. i. des. eauto.
    - splits.
      + inv DISJOINT. econs. i. revert GET1. erewrite remove_o; eauto. condtac; ss.
        des. subst. i. inv GET1. eapply DISJOINT0; eauto.
        hexploit remove_get0; try eapply PROMISES; eauto.
      + ii. erewrite remove_o; eauto. condtac; ss; eauto.
        des. subst. exfalso. eapply disjoint_get; eauto.
        hexploit remove_get0; try exact PROMISES; eauto. i. des. eauto.
  Qed.

  Lemma remove_future
        promises1 mem1 loc from to msg promises2
        (REMOVE: remove promises1 loc from to msg promises2)
        (LE: le promises1 mem1)
        (FINITE: finite promises1):
    <<LE: le promises2 mem1>> /\
    <<FINITE: finite promises2>>.
  Proof.
    hexploit remove_le; eauto. i. des.
    hexploit remove_finite; eauto.
  Qed.

  Lemma remove_disjoint
        promises1 loc from to msg promises2 ctx
        (REMOVE: remove promises1 loc from to msg promises2)
        (DISJOINT: disjoint promises1 ctx):
    <<DISJOINT: disjoint promises2 ctx>>.
  Proof.
    econs. i. revert GET1. erewrite remove_o; eauto. condtac; ss.
    i. eapply DISJOINT; eauto.
  Qed.

  Lemma write_future
        promises1 mem1 loc from to msg promises2 mem2 kind
        (WRITE: write promises1 mem1 loc from to msg promises2 mem2 kind)
        (CLOSED: closed mem1)
        (MSG_CLOSED: closed_message msg mem2)
        (LE: le promises1 mem1)
        (FINITE: finite promises1)
        (BOT: bot_none promises1):
    <<CLOSED: closed mem2>> /\
    <<LE: le promises2 mem2>> /\
    <<FINITE: finite promises2>> /\
    <<BOT: bot_none promises2>> /\
    <<FUTURE: future mem1 mem2>>.
  Proof.
    inv WRITE.
    hexploit promise_future; eauto. i. des.
    hexploit remove_future; eauto. i. des.
    hexploit remove_bot_none; eauto.
  Qed.

  Lemma write_disjoint
        promises1 mem1 loc from to msg promises2 mem2 ctx kind
        (WRITE: write promises1 mem1 loc from to msg promises2 mem2 kind)
        (DISJOINT: disjoint promises1 ctx)
        (LE_CTX: le ctx mem1):
    <<DISJOINT: disjoint promises2 ctx>> /\
    <<LE_CTX: le ctx mem2>>.
  Proof.
    inv WRITE.
    hexploit promise_disjoint; try apply PROMISE; eauto. i. des.
    hexploit remove_disjoint; try apply REMOVE; eauto.
  Qed.

  Lemma write_promises_bot
        promises1 mem1 loc from to msg promises2 mem2 kind
        (WRITE: write promises1 mem1 loc from to msg promises2 mem2 kind)
        (PROMISES: promises1 = Memory.bot):
    promises2 = Memory.bot.
  Proof.
    subst. inv WRITE. inv PROMISE.
    - apply ext. i.
      exploit add_get0; try exact PROMISES. i. des.
      exploit remove_get0; eauto. i. des.
      erewrite remove_o; eauto. condtac; ss.
      + des. subst. ss.
      + erewrite add_o; eauto. condtac; ss.
    - exploit split_get0; try exact PROMISES. i. des.
      rewrite bot_get in *. ss.
    - exploit lower_get0; try exact PROMISES. i. des.
      rewrite bot_get in *. ss.
    - exploit remove_get0; try exact PROMISES. i. des.
      rewrite bot_get in *. ss.
  Qed.

  Lemma write_na_future
        ts promises1 mem1 loc from to val promises2 mem2 msgs kinds kind
        (WRITE: write_na ts promises1 mem1 loc from to val promises2 mem2 msgs kinds kind)
        (CLOSED: closed mem1)
        (LE: le promises1 mem1)
        (FINITE: finite promises1)
        (BOT: bot_none promises1):
    <<CLOSED: closed mem2>> /\
    <<LE: le promises2 mem2>> /\
    <<FINITE: finite promises2>> /\
    <<BOT: bot_none promises2>> /\
    <<FUTURE: future mem1 mem2>>.
  Proof.
    induction WRITE; eauto using write_future.
    exploit write_future; eauto.
    { unguard. des; subst; eauto. }
    i. des.
    exploit IHWRITE; eauto. i. des.
    splits; auto. etrans; eauto.
  Qed.

  Lemma write_na_disjoint
        ts promises1 mem1 loc from to val promises2 mem2 msgs kinds kind
        ctx
        (WRITE: write_na ts promises1 mem1 loc from to val promises2 mem2 msgs kinds kind)
        (DISJOINT: disjoint promises1 ctx)
        (LE_CTX: le ctx mem1):
    <<DISJOINT: disjoint promises2 ctx>> /\
    <<LE_CTX: le ctx mem2>>.
  Proof.
    induction WRITE; eauto using write_disjoint.
    exploit Memory.write_disjoint; try exact WRITE_EX; eauto. i. des. eauto.
  Qed.

  Lemma write_na_promises_bot
        ts promises1 mem1 loc from to val promises2 mem2 msgs kinds kind
        (WRITE: write_na ts promises1 mem1 loc from to val promises2 mem2 msgs kinds kind)
        (PROMISES: promises1 = Memory.bot):
    promises2 = Memory.bot.
  Proof.
    induction WRITE; eauto using write_promises_bot.
  Qed.


  (* future_weak *)

  Inductive future_weak (mem1 mem2: t): Prop :=
  | future_weak_intro
      (SOUND: forall loc from to msg
                (GET: get loc to mem1 = Some (from, msg))
                (MSG: msg <> Message.reserve),
          exists f m,
            get loc to mem2 = Some (f, m) /\
            Time.le from f /\
            (m = msg \/
             Message.wf m /\
             closed_message m mem2 /\
             Message.le m msg))
      (COMPLETE1: forall loc from to val released
                     (GET1: get loc to mem1 = None)
                     (GET2: get loc to mem2 = Some (from, Message.concrete val released)),
          View.opt_wf released /\
          closed_opt_view released mem2 /\
          Time.le ((View.rlx (View.unwrap released)) loc) to)
      (COMPLETE2: forall loc from to val released f
                     (GET1: get loc to mem1 = Some (f, Message.reserve))
                     (GET2: get loc to mem2 = Some (from, Message.concrete val released)),
          View.opt_wf released /\
          closed_opt_view released mem2 /\
          Time.le ((View.rlx (View.unwrap released)) loc) to)
  .
  #[global] Hint Constructors future_weak: core.

  Lemma future_weak_closed_timemap
        times mem1 mem2
        (FUTURE: future_weak mem1 mem2)
        (CLOSED: closed_timemap times mem1):
    closed_timemap times mem2.
  Proof.
    ii. specialize (CLOSED loc). des.
    inv FUTURE. exploit SOUND; eauto; ss. intros x. des; subst; eauto.
    inv x3. eauto.
  Qed.

  Lemma future_weak_closed_view
        view mem1 mem2
        (FUTURE: future_weak mem1 mem2)
        (CLOSED: closed_view view mem1):
    closed_view view mem2.
  Proof.
    inv CLOSED. econs; eauto using future_weak_closed_timemap.
  Qed.

  Lemma future_weak_closed_opt_view
        view mem1 mem2
        (FUTURE: future_weak mem1 mem2)
        (CLOSED: closed_opt_view view mem1):
    closed_opt_view view mem2.
  Proof.
    inv CLOSED; econs. eapply future_weak_closed_view; eauto.
  Qed.

  Lemma future_weak_closed_message
        msg mem1 mem2
        (FUTURE: future_weak mem1 mem2)
        (CLOSED: closed_message msg mem1):
    closed_message msg mem2.
  Proof.
    inv CLOSED; econs. eapply future_weak_closed_opt_view; eauto.
  Qed.

  Lemma future_weak_closed
        mem1 mem2
        (FUTURE: future_weak mem1 mem2)
        (CLOSED: closed mem1):
    closed mem2.
  Proof.
    inv FUTURE. inv CLOSED. econs; i.
    - destruct msg; try by (splits; econs).
      destruct (get loc to mem1) as [[f []]|] eqn:GET1.
      + exploit CLOSED0; eauto. i. des.
        exploit SOUND; eauto; ss. intros x. des.
        * rewrite MSG in *. inv x. inv H1.
          splits; auto. eapply future_weak_closed_message; eauto.
        * rewrite MSG in *. inv x. splits; eauto.
          econs. inv MSG_TS. etrans; eauto.
          inv x3. inv RELEASED; ss; try apply LE.
          unfold TimeMap.bot. apply Time.bot_spec.
      + exploit SOUND; eauto; ss. intros x. des; subst; try congr.
        inv x3. congr.
      + exploit COMPLETE2; eauto. i. des.
        splits; econs; eauto.
      + exploit COMPLETE1; eauto. i. des.
        splits; econs; eauto.
    - ii. specialize (INHABITED loc).
      exploit SOUND; eauto; ss. intros x. des.
      + subst. exploit get_ts; try exact x. intros x2. des; subst; eauto. inv x2.
      + exploit get_ts; try exact x. i. des.
        * subst. inv x3. inv RELEASED.
          exploit Const.undef_le_inv; eauto. i. subst. eauto.
        * inv x5.
  Qed.

  Global Program Instance future_weak_PreOrder: PreOrder future_weak.
  Next Obligation.
    ii. econs; try congr; i.
    esplits; eauto. refl.
  Qed.
  Next Obligation.
    ii. inv H. inv H0. econs; i.
    - exploit SOUND; eauto. i. des; subst.
      + exploit SOUND0; eauto. i. des; subst.
        * esplits; eauto.
        * esplits; eauto.
      + exploit SOUND0; eauto.
        { inv x4; ss. }
        i. des; subst.
        * esplits; eauto. right. splits; auto.
          eapply future_weak_closed_message; eauto.
        * esplits; eauto. right. splits; auto. etrans; eauto.
    - destruct (get loc to y) as [[f []]|] eqn:GET; eauto; cycle 1.
      { exploit SOUND0; eauto; ss. i. des; subst; try congr. inv x4. congr. }
      exploit COMPLETE1; eauto. i. des.
      exploit SOUND0; eauto; ss. intros x3. des; subst.
      + rewrite GET2 in *. inv x3. splits; eauto.
        eapply future_weak_closed_opt_view; eauto.
      + rewrite GET2 in *. inv x3. inv x5. inv x6. inv x7.
        splits; auto. etrans; eauto.
        inv RELEASED; try apply LE. apply Time.bot_spec.
    - destruct (get loc to y) as [[f' []]|] eqn:GET; eauto; cycle 1.
      { exploit SOUND0; eauto; ss. i. des; subst; try congr. inv x4. congr. }
      exploit COMPLETE2; eauto. i. des.
      exploit SOUND0; eauto; ss. intros x3. des; subst.
      + rewrite GET2 in *. inv x3. splits; eauto.
        eapply future_weak_closed_opt_view; eauto.
      + rewrite GET2 in *. inv x3. inv x5. inv x6. inv x7.
        splits; eauto. etrans; eauto.
        inv RELEASED; try apply LE. apply Time.bot_spec.
  Qed.

  Lemma future_future_weak
        mem1 mem2
        (FUTURE: future mem1 mem2):
    future_weak mem1 mem2.
  Proof.
    induction FUTURE; try refl.
    etrans; eauto. clear FUTURE IHFUTURE.
    inv H. inv OP.
    - econs; i.
      + exploit add_get1; eauto. i.
        esplits; eauto. refl.
      + revert GET2. erewrite add_o; eauto. condtac; ss; i.
        * des. subst. inv GET2.
          inv TS. inv CLOSED. splits; auto.
          inv ADD. inv ADD0. inv MSG_WF. ss.
        * congr.
      + revert GET2. erewrite add_o; eauto. condtac; ss; i.
        * des. subst. inv GET2.
          exploit add_get0; eauto. i. des. congr.
        * congr.
    - exploit split_get0; eauto. i. des.
      econs; i.
      + erewrite split_o; eauto. repeat condtac; ss; eauto.
        * des. subst. congr.
        * guardH o. des. subst.
          rewrite GET0 in *. inv GET3. esplits; eauto.
          inv SPLIT. inv SPLIT0. econs. ss.
        * esplits; eauto. refl.
      + revert GET4. erewrite split_o; eauto. repeat condtac; ss; i.
        * des. subst. inv GET4.
          inv TS. inv CLOSED. splits; auto.
          inv SPLIT. inv SPLIT0. inv MSG_WF. ss.
        * guardH o. des. subst. inv GET4. congr.
        * congr.
      + revert GET4. erewrite split_o; eauto. repeat condtac; ss; i.
        * des. subst. inv GET4.
          inv TS. inv CLOSED. splits; auto.
          inv SPLIT. inv SPLIT0. inv MSG_WF. ss.
        * guardH o. des. subst. inv GET4. congr.
        * congr.
    - exploit lower_get0; eauto. i. des.
      econs; i.
      + erewrite lower_o; eauto. condtac; ss.
        * des. subst.
          rewrite GET in *. inv GET1. inv MSG_LE; ss.
          { esplits; eauto; try refl.
            right. inv CLOSED. splits; auto.
            inv LOWER. inv LOWER0. inv MSG_WF. econs. ss. }
          { esplits; eauto. refl. }
        * esplits; eauto. refl.
      + revert GET2. erewrite lower_o; eauto. condtac; ss; i.
        * des. subst. congr.
        * congr.
      + revert GET2. erewrite lower_o; eauto. condtac; ss; i.
        * des. subst. inv GET2.
          rewrite GET in *. inv GET1.
          inv TS. inv CLOSED. splits; auto.
          inv LOWER. inv LOWER0. inv MSG_WF. ss.
        * congr.
    - exploit remove_get0; eauto. i. des.
      econs; i.
      + erewrite Memory.remove_o; eauto. condtac; ss.
        * des. subst. congr.
        * esplits; eauto. refl.
      + revert GET2. erewrite remove_o; eauto. condtac; ss; i.
        congr.
      + revert GET2. erewrite remove_o; eauto. condtac; ss; i.
        congr.
  Qed.

  Lemma future_weak_get1
        loc from to msg mem1 mem2
        (FUTURE: future_weak mem1 mem2)
        (GET: get loc to mem1 = Some (from, msg))
        (RESERVE: msg <> Message.reserve):
    exists from' msg',
      <<GET: get loc to mem2 = Some (from', msg')>> /\
      <<FROM: Time.le from from'>> /\
      <<MSG_LE: Message.le msg' msg>>.
  Proof.
    inv FUTURE. exploit SOUND; eauto; ss. i. des.
    - subst. esplits; eauto. refl.
    - esplits; eauto.
  Qed.


  (* Lemmas on max_timemap *)

  Definition max_ts (loc:Loc.t) (mem:t): Time.t :=
    Cell.max_ts (mem loc).

  Lemma max_ts_spec
        loc ts from msg mem
        (GET: get loc ts mem = Some (from, msg)):
    <<GET: exists from msg, get loc (max_ts loc mem) mem = Some (from, msg)>> /\
    <<MAX: Time.le ts (max_ts loc mem)>>.
  Proof. eapply Cell.max_ts_spec; eauto. Qed.

  Lemma max_ts_spec2
        tm mem loc
        (CLOSED: closed_timemap tm mem):
    Time.le (tm loc) (max_ts loc mem).
  Proof.
    exploit CLOSED. i. des.
    eapply max_ts_spec. eauto.
  Qed.

  Definition max_timemap (mem:t): TimeMap.t :=
    fun loc => max_ts loc mem.

  Lemma max_timemap_spec tm mem
        (TIMEMAP: closed_timemap tm mem)
        (INHABITED: inhabited mem):
    TimeMap.le tm (max_timemap mem).
  Proof.
    ii. specialize (INHABITED loc). des.
    exploit TIMEMAP. i. des.
    eapply max_ts_spec; eauto.
  Qed.

  Lemma max_timemap_spec' tm mem
        (TIMEMAP: forall loc, exists from to val released, Time.le (tm loc) to /\ get loc to mem = Some (from, Message.concrete val released))
        (INHABITED: inhabited mem):
    TimeMap.le tm (max_timemap mem).
  Proof.
    ii. exploit TIMEMAP; eauto. i. des.
    etrans; eauto. eapply max_ts_spec; eauto.
  Qed.

  Definition max_view (mem:t): View.t :=
    View.mk (max_timemap mem) (max_timemap mem).

  Lemma max_view_wf mem: View.wf (max_view mem).
  Proof. econs. refl. Qed.

  Lemma max_view_spec tm mem
        (VIEW: closed_view tm mem)
        (INHABITED: inhabited mem):
    View.le tm (max_view mem).
  Proof.
    econs; apply max_timemap_spec; try apply VIEW; auto.
  Qed.

  Lemma closed_timemap_add
        loc from to val released mem tm
        (GET: get loc to mem = Some (from, Message.concrete val released))
        (CLOSED: closed_timemap tm mem):
    closed_timemap (TimeMap.add loc to tm) mem.
  Proof.
    ii. unfold TimeMap.add. condtac.
    - subst. esplits; eauto.
    - apply CLOSED.
  Qed.


  (* lemmas on min_concrete_ts *)

  Definition min_concrete_ts (mem: t) (loc: Loc.t) (ts: Time.t): Prop :=
    Cell.min_concrete_ts (mem loc) ts.

  Lemma min_concrete_ts_exists
        mem loc from to msg
        (INHABITED: get loc to mem = Some (from, msg))
        (RESERVE: msg <> Message.reserve):
    exists ts, min_concrete_ts mem loc ts.
  Proof.
    eapply Cell.min_concrete_ts_exists; eauto.
  Qed.

  Lemma min_concrete_ts_inj
        mem loc ts1 ts2
        (MIN1: min_concrete_ts mem loc ts1)
        (MIN2: min_concrete_ts mem loc ts2):
    ts1 = ts2.
  Proof.
    eapply Cell.min_concrete_ts_inj; eauto.
  Qed.

  Lemma min_concrete_ts_spec
        loc ts from msg mem mts
        (MIN: min_concrete_ts mem loc mts)
        (GET: get loc ts mem = Some (from, msg))
        (RESERVE: msg <> Message.reserve):
    <<GET: exists from msg', get loc mts mem = Some (from, msg') /\ msg' <> Message.reserve>> /\
    <<MIN: Time.le mts ts>>.
  Proof.
    eapply Cell.min_concrete_ts_spec; eauto.
  Qed.


  (* Lemmas on max_concrete_timemap *)

  Definition max_concrete_ts (mem: t) (loc: Loc.t) (ts: Time.t): Prop :=
    Cell.max_concrete_ts (mem loc) ts.

  Lemma max_concrete_ts_exists
        mem loc
        (INHABITED: inhabited mem):
    exists ts, max_concrete_ts mem loc ts.
  Proof.
    eapply Cell.max_concrete_ts_exists. apply INHABITED.
  Qed.

  Lemma max_concrete_ts_inj
        mem loc ts1 ts2
        (MAX1: max_concrete_ts mem loc ts1)
        (MAX2: max_concrete_ts mem loc ts2):
    ts1 = ts2.
  Proof.
    eapply Cell.max_concrete_ts_inj; eauto.
  Qed.

  Lemma max_concrete_ts_spec
        loc ts from val released mem mts
        (MAX: max_concrete_ts mem loc mts)
        (GET: get loc ts mem = Some (from, Message.concrete val released)):
    <<GET: exists from val' released', get loc mts mem = Some (from, Message.concrete val' released')>> /\
    <<MAX: Time.le ts mts>>.
  Proof.
    eapply Cell.max_concrete_ts_spec; eauto.
  Qed.

  Lemma max_concrete_ts_spec2
        tm mem loc mts
        (MAX: max_concrete_ts mem loc mts)
        (CLOSED: closed_timemap tm mem):
    Time.le (tm loc) mts.
  Proof.
    exploit CLOSED. i. des.
    eapply max_concrete_ts_spec; eauto.
  Qed.

  Definition max_concrete_timemap (mem: t) (tm: TimeMap.t): Prop :=
    forall loc, max_concrete_ts mem loc (tm loc).

  Lemma max_concrete_timemap_exists
        mem
        (INHABITED: inhabited mem):
    exists tm, max_concrete_timemap mem tm.
  Proof.
    apply choice. i. apply max_concrete_ts_exists. auto.
  Qed.

  Lemma max_concrete_timemap_inj
        mem tm1 tm2
        (MAX1: max_concrete_timemap mem tm1)
        (MAX2: max_concrete_timemap mem tm2):
    tm1 = tm2.
  Proof.
    extensionality l.
    specialize (MAX1 l). specialize (MAX2 l).
    eapply max_concrete_ts_inj; eauto.
  Qed.

  Lemma max_concrete_timemap_closed
        mem tm
        (MAX: max_concrete_timemap mem tm):
    closed_timemap tm mem.
  Proof.
    ii. specialize (MAX loc). inv MAX. des.
    esplits; eauto.
  Qed.

  Lemma max_concrete_timemap_spec
        tm mem mtm
        (MAX: max_concrete_timemap mem mtm)
        (TIMEMAP: closed_timemap tm mem):
    TimeMap.le tm mtm.
  Proof.
    ii. specialize (MAX loc). specialize (TIMEMAP loc).
    des. eapply max_concrete_ts_spec; eauto.
  Qed.

  Inductive max_concrete_view (mem: t): forall (view: View.t), Prop :=
  | max_concrete_view_intro
      tm
      (MAX: max_concrete_timemap mem tm):
      max_concrete_view mem (View.mk tm tm)
  .
  #[global] Hint Constructors max_concrete_view: core.

  Lemma max_concrete_view_exists
        mem
        (INHABITED: inhabited mem):
    exists view, max_concrete_view mem view.
  Proof.
    exploit max_concrete_timemap_exists; eauto. i. des.
    esplits. econs; eauto.
  Qed.

  Lemma max_concrete_view_inj
        mem view1 view2
        (MAX1: max_concrete_view mem view1)
        (MAX2: max_concrete_view mem view2):
    view1 = view2.
  Proof.
    inv MAX1. inv MAX2.
    exploit max_concrete_timemap_inj; [exact MAX|exact MAX0|..].
    i. subst. refl.
  Qed.

  Lemma max_concrete_view_wf
        mem view
        (MAX: max_concrete_view mem view):
    View.wf view.
  Proof.
    inv MAX. econs. refl.
  Qed.

  Lemma max_concrete_view_closed
        mem view
        (MAX: max_concrete_view mem view):
    closed_view view mem.
  Proof.
    inv MAX. econs; apply max_concrete_timemap_closed; auto.
  Qed.

  Lemma max_concrete_view_spec
        view mem mview
        (MAX: max_concrete_view mem mview)
        (VIEW: closed_view view mem):
    View.le view mview.
  Proof.
    inv MAX. inv VIEW.
    econs; eapply max_concrete_timemap_spec; eauto.
  Qed.


  (* Lemmas on max_non_reserve_timemap *)

  Definition max_non_reserve_ts (mem: t) (loc: Loc.t) (ts: Time.t): Prop :=
    Cell.max_non_reserve_ts (mem loc) ts.

  Lemma max_non_reserve_ts_exists
        mem loc
        (INHABITED: inhabited mem):
    exists ts, max_non_reserve_ts mem loc ts.
  Proof.
    eapply Cell.max_non_reserve_ts_exists. apply INHABITED.
  Qed.

  Lemma max_non_reserve_ts_inj
        mem loc ts1 ts2
        (MAX1: max_non_reserve_ts mem loc ts1)
        (MAX2: max_non_reserve_ts mem loc ts2):
    ts1 = ts2.
  Proof.
    eapply Cell.max_non_reserve_ts_inj; eauto.
  Qed.

  Lemma max_non_reserve_ts_spec
        loc ts from msg mem mts
        (MAX: max_non_reserve_ts mem loc mts)
        (GET: get loc ts mem = Some (from, msg))
        (RESERVE: msg <> Message.reserve):
    <<GET: exists from msg', get loc mts mem = Some (from, msg') /\ msg' <> Message.reserve>> /\
    <<MAX: Time.le ts mts>>.
  Proof.
    eapply Cell.max_non_reserve_ts_spec; eauto.
  Qed.

  Lemma max_non_reserve_ts_spec2
        tm mem loc mts
        (MAX: max_non_reserve_ts mem loc mts)
        (CLOSED: closed_timemap tm mem):
    Time.le (tm loc) mts.
  Proof.
    exploit CLOSED. i. des.
    eapply max_non_reserve_ts_spec; eauto. ss.
  Qed.

  Definition max_non_reserve_timemap (mem: t) (tm: TimeMap.t): Prop :=
    forall loc, max_non_reserve_ts mem loc (tm loc).

  Lemma max_non_reserve_timemap_exists
        mem
        (INHABITED: inhabited mem):
    exists tm, max_non_reserve_timemap mem tm.
  Proof.
    apply choice. i. apply max_non_reserve_ts_exists. auto.
  Qed.

  Lemma max_non_reserve_timemap_inj
        mem tm1 tm2
        (MAX1: max_non_reserve_timemap mem tm1)
        (MAX2: max_non_reserve_timemap mem tm2):
    tm1 = tm2.
  Proof.
    extensionality l.
    specialize (MAX1 l). specialize (MAX2 l).
    eapply max_non_reserve_ts_inj; eauto.
  Qed.

  Lemma max_non_reserve_timemap_spec
        tm mem mtm
        (MAX: max_non_reserve_timemap mem mtm)
        (TIMEMAP: closed_timemap tm mem):
    TimeMap.le tm mtm.
  Proof.
    ii. specialize (MAX loc). specialize (TIMEMAP loc).
    des. eapply max_non_reserve_ts_spec; eauto. ss.
  Qed.

  Inductive max_non_reserve_view (mem: t): forall (view: View.t), Prop :=
  | max_non_reserve_view_intro
      tm
      (MAX: max_non_reserve_timemap mem tm):
      max_non_reserve_view mem (View.mk tm tm)
  .
  #[global] Hint Constructors max_non_reserve_view: core.

  Lemma max_non_reserve_view_exists
        mem
        (INHABITED: inhabited mem):
    exists view, max_non_reserve_view mem view.
  Proof.
    exploit max_non_reserve_timemap_exists; eauto. i. des.
    esplits. econs; eauto.
  Qed.

  Lemma max_non_reserve_view_inj
        mem view1 view2
        (MAX1: max_non_reserve_view mem view1)
        (MAX2: max_non_reserve_view mem view2):
    view1 = view2.
  Proof.
    inv MAX1. inv MAX2.
    exploit max_non_reserve_timemap_inj; [exact MAX|exact MAX0|..].
    i. subst. refl.
  Qed.

  Lemma max_non_reserve_view_wf
        mem view
        (MAX: max_non_reserve_view mem view):
    View.wf view.
  Proof.
    inv MAX. econs. refl.
  Qed.

  Lemma max_non_reserve_view_spec
        view mem mview
        (MAX: max_non_reserve_view mem mview)
        (VIEW: closed_view view mem):
    View.le view mview.
  Proof.
    inv MAX. inv VIEW.
    econs; eapply max_non_reserve_timemap_spec; eauto.
  Qed.


  (* Lemmas on existence of memory op *)

  Lemma add_exists
        mem1 loc from to msg
        (DISJOINT: forall to2 from2 msg2
                     (GET2: get loc to2 mem1 = Some (from2, msg2)),
            Interval.disjoint (from, to) (from2, to2))
        (TO1: Time.lt from to)
        (MSG_WF: Message.wf msg):
    exists mem2, add mem1 loc from to msg mem2.
  Proof.
    exploit Cell.add_exists; eauto. i. des.
    eexists. econs; eauto.
  Qed.

  Lemma add_exists_max_ts
        mem1 loc to msg
        (TS: Time.lt (max_ts loc mem1) to)
        (MSG_WF: Message.wf msg):
    exists mem2,
      add mem1 loc (max_ts loc mem1) to msg mem2.
  Proof.
    eapply add_exists; eauto.
    i. exploit max_ts_spec; eauto. i. des.
    ii. inv LHS. inv RHS. ss.
    rewrite MAX in TO0. eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt; eauto.
  Qed.

  Lemma add_exists_le
        promises1 mem1 loc from to msg mem2
        (LE: le promises1 mem1)
        (ADD: add mem1 loc from to msg mem2):
    exists promises2, add promises1 loc from to msg promises2.
  Proof.
    inv ADD.
    exploit Cell.add_exists_le; eauto.
    { ii. eapply LE. eauto. }
    i. des.
    eexists. econs; eauto.
  Qed.

  Lemma split_exists
        mem1 loc ts1 ts2 ts3 msg2 msg3
        (GET2: get loc ts3 mem1 = Some (ts1, msg3))
        (TS12: Time.lt ts1 ts2)
        (TS23: Time.lt ts2 ts3)
        (MSG_WF: Message.wf msg2):
    exists mem2, split mem1 loc ts1 ts2 ts3 msg2 msg3 mem2.
  Proof.
    exploit Cell.split_exists; eauto. i. des.
    eexists. econs; eauto.
  Qed.

  Lemma split_exists_le
        promises1 mem1 loc ts1 ts2 ts3 msg2 msg3 promises2
        (LE: le promises1 mem1)
        (SPLIT: split promises1 loc ts1 ts2 ts3 msg2 msg3 promises2):
    exists mem2, split mem1 loc ts1 ts2 ts3 msg2 msg3 mem2.
  Proof.
    inv SPLIT.
    exploit Cell.split_exists_le; eauto.
    { ii. eapply LE. eauto. }
    i. des.
    eexists. econs; eauto.
  Qed.

  Lemma lower_exists
        mem1 loc from to msg1 msg2
        (GET: get loc to mem1 = Some (from, msg1))
        (TS: Time.lt from to)
        (MSG_WF: Message.wf msg2)
        (MSG_LE: Message.le msg2 msg1):
    exists mem2, lower mem1 loc from to msg1 msg2 mem2.
  Proof.
    exploit Cell.lower_exists; eauto. i. des.
    eexists. econs; eauto.
  Qed.

  Lemma lower_exists_le
        promises1 mem1 loc from to msg1 msg2 promises2
        (LE: le promises1 mem1)
        (LOWER: lower promises1 loc from to msg1 msg2 promises2):
    exists mem2, lower mem1 loc from to msg1 msg2 mem2.
  Proof.
    inv LOWER.
    exploit Cell.lower_exists_le; eauto.
    { ii. eapply LE. eauto. }
    i. des.
    eexists. econs; eauto.
  Qed.

  Lemma lower_exists_same
        mem1 loc from to msg
        (GET: get loc to mem1 = Some (from, msg))
        (TS: Time.lt from to)
        (MSG_WF: Message.wf msg):
    lower mem1 loc from to msg msg mem1.
  Proof.
    exploit lower_exists; eauto; try refl. i. des.
    cut (mem2 = mem1).
    { i. subst. auto. }
    apply ext. i.
    erewrite lower_o; eauto. condtac; ss. des. subst. auto.
  Qed.

  Lemma remove_singleton
        loc from to msg
        (LT: Time.lt from to)
        (MSG_WF: Message.wf msg):
    remove (singleton loc LT MSG_WF) loc from to msg bot.
  Proof.
    assert (bot = LocFun.add loc Cell.bot (singleton loc LT MSG_WF)).
    { apply ext. i. rewrite bot_get.
      unfold get, LocFun.add, LocFun.find. condtac.
      - rewrite Cell.bot_get. auto.
      - unfold singleton, LocFun.add, LocFun.find. condtac; [congr|].
        rewrite Cell.bot_get. auto.
    }
    rewrite H. econs; ss.
    unfold singleton, LocFun.add, LocFun.find. condtac; [|congr].
    eapply Cell.remove_singleton.
  Qed.

  Lemma add_inj
        mem loc to from msg mem1 mem2
        (REMOVE1: Memory.add mem loc from to msg mem1)
        (REMOVE2: Memory.add mem loc from to msg mem2):
    mem1 = mem2.
  Proof.
    apply Memory.ext. i.
    setoid_rewrite Memory.add_o; eauto.
  Qed.

  Lemma split_inj
        mem loc to to' from msg1 msg2 mem1 mem2
        (REMOVE1: Memory.split mem loc from to to' msg1 msg2 mem1)
        (REMOVE2: Memory.split mem loc from to to' msg1 msg2 mem2):
    mem1 = mem2.
  Proof.
    apply Memory.ext. i.
    setoid_rewrite Memory.split_o; eauto.
  Qed.

  Lemma lower_inj
        mem loc to from msg1 msg2 mem1 mem2
        (LOWER1: Memory.lower mem loc from to msg1 msg2 mem1)
        (LOWER2: Memory.lower mem loc from to msg1 msg2 mem2):
    mem1 = mem2.
  Proof.
    apply Memory.ext. i.
    setoid_rewrite Memory.lower_o; eauto.
  Qed.

  Lemma remove_inj
        mem loc to from1 from2 msg1 msg2 mem1 mem2
        (REMOVE1: Memory.remove mem loc from1 to msg1 mem1)
        (REMOVE2: Memory.remove mem loc from2 to msg2 mem2):
    mem1 = mem2.
  Proof.
    apply Memory.ext. i.
    setoid_rewrite Memory.remove_o; eauto.
  Qed.

  Lemma op_inj
        mem loc from to msg mem1 mem2 kind
        (OP1: op mem loc from to msg mem1 kind)
        (OP2: op mem loc from to msg mem2 kind):
    mem1 = mem2.
  Proof.
    inv OP1; inv OP2;
      eauto using add_inj, split_inj, lower_inj, remove_inj.
  Qed.

  Lemma promise_inj
        promises mem loc from to msg promises1 promises2 mem1 mem2 kind
        (PROMISE1: promise promises mem loc from to msg promises1 mem1 kind)
        (PROMISE2: promise promises mem loc from to msg promises2 mem2 kind):
    promises1 = promises2 /\ mem1 = mem2.
  Proof.
    exploit promise_op; try exact PROMISE1. i.
    exploit promise_op; try exact PROMISE2. i.
    exploit promise_op_promise; try exact PROMISE1. i.
    exploit promise_op_promise; try exact PROMISE2. i.
    exploit op_inj; [exact x0|exact x1|]. i. subst.
    exploit op_inj; [exact x2|exact x3|]. i. subst.
    eauto.
  Qed.

  Lemma write_inj
        promises mem loc from to msg promises1 promises2 mem1 mem2 kind
        (WRITE1: write promises mem loc from to msg promises1 mem1 kind)
        (WRITE2: write promises mem loc from to msg promises2 mem2 kind):
    promises1 = promises2 /\ mem1 = mem2.
  Proof.
    inv WRITE1. inv WRITE2.
    exploit promise_inj; [exact PROMISE|exact PROMISE0|]. i. des. subst.
    exploit remove_inj; [exact REMOVE|exact REMOVE0|]; eauto.
  Qed.

  Lemma write_na_inj
        ts promises mem loc from to msg promises1 promises2 mem1 mem2 msgs kinds kind
        (WRITE1: write_na ts promises mem loc from to msg promises1 mem1 msgs kinds kind)
        (WRITE2: write_na ts promises mem loc from to msg promises2 mem2 msgs kinds kind):
    promises1 = promises2 /\ mem1 = mem2.
  Proof.
    revert promises2 mem2 WRITE2.
    induction WRITE1; i; inv WRITE2; eauto using write_inj.
    exploit write_inj; [exact WRITE_EX|exact WRITE_EX0|]. i. des. subst. eauto.
  Qed.

  Lemma remove_exists
        mem1 loc from to msg
        (GET: get loc to mem1 = Some (from, msg)):
    exists mem2, remove mem1 loc from to msg mem2.
  Proof.
    exploit Cell.remove_exists; eauto. i. des.
    eexists. econs; ss. eauto.
  Qed.

  Lemma remove_exists_le
        promises1 mem1 loc from to msg promises2
        (LE: le promises1 mem1)
        (LOWER: remove promises1 loc from to msg promises2):
    exists mem2, remove mem1 loc from to msg mem2.
  Proof.
    exploit remove_get0; eauto. i. des.
    exploit LE; eauto. intros x.
    exploit remove_exists; try exact x. eauto.
  Qed.

  Definition nonsynch_loc (loc:Loc.t) (mem:t): Prop :=
    forall f t msg (GET: get loc t mem = Some (f, msg)),
      match msg with
      | Message.concrete _ rel => rel = None
      | _ => True
      end.

  Definition nonsynch (mem:t): Prop :=
    forall loc, nonsynch_loc loc mem.

  Lemma bot_nonsynch_loc loc: nonsynch_loc loc Memory.bot.
  Proof. ii. rewrite bot_get in *. congr. Qed.

  Lemma bot_nonsynch: nonsynch Memory.bot.
  Proof. ii. eapply bot_nonsynch_loc. eauto. Qed.


  (* next and previous message *)

  Lemma next_exists
        mem loc f t m ts
        (GET: get loc t mem = Some (f, m))
        (TS: Time.lt ts (max_ts loc mem)):
    exists from to msg,
      get loc to mem = Some (from, msg) /\
      Time.lt ts to /\
      forall ts' (TS1: Time.lt ts ts') (TS2: Time.lt ts' to),
        get loc ts' mem = None.
  Proof.
    exploit Cell.next_exists; eauto.
  Qed.


  (* adjacent *)

  Inductive adjacent (loc: Loc.t) (from1 to1 from2 to2: Time.t) (mem: t): Prop :=
  | adjacent_intro
      m1 m2
      (GET1: get loc to1 mem = Some (from1, m1))
      (GET2: get loc to2 mem = Some (from2, m2))
      (TS: Time.lt to1 to2)
      (EMPTY: forall ts (TS1: Time.lt to1 ts) (TS2: Time.le ts from2),
          get loc ts mem = None)
  .

  Lemma adjacent_ts
        loc from1 to1 from2 to2 mem
        (ADJ: adjacent loc from1 to1 from2 to2 mem):
    Time.le to1 from2.
  Proof.
    destruct (Time.le_lt_dec to1 from2); auto.
    exfalso. inv ADJ.
    exploit get_ts; try exact GET1. i. des.
    { subst. inv l. }
    exploit get_ts; try exact GET2. i. des.
    { subst. inv TS. }
    exploit get_disjoint; [exact GET1|exact GET2|..]. i. des.
    { subst. timetac. }
    apply (x2 to1); econs; ss.
    - refl.
    - econs. auto.
  Qed.

  Lemma adjacent_inj
        loc to mem
        from1 from2 from3 to3 from4 to4
        (ADJ1: adjacent loc from1 to from3 to3 mem)
        (ADJ2: adjacent loc from2 to from4 to4 mem):
    from1 = from2 /\ from3 = from4 /\ to3 = to4.
  Proof.
    inv ADJ1. inv ADJ2.
    rewrite GET1 in GET0. inv GET0.
    destruct (Time.le_lt_dec to3 to4); cycle 1.
    { exfalso.
      destruct (Time.le_lt_dec to4 from3).
      - exploit EMPTY; try exact l0; eauto. i. congr.
      - exploit get_ts; try exact GET2. i. des.
        { subst. inv l. }
        exploit get_ts; try exact GET3. i. des.
        { subst. inv l0. }
        exploit get_disjoint; [exact GET2|exact GET3|..]. i. des.
        { subst. timetac. }
        apply (x2 to4); econs; ss.
        + econs. ss.
        + refl. }
    inv l.
    { exfalso.
      destruct (Time.le_lt_dec to3 from4).
      - exploit EMPTY0; try exact l; eauto. i. congr.
      - exploit get_ts; try exact GET2. i. des.
        { subst. inv l. }
        exploit get_ts; try exact GET3. i. des.
        { subst. inv H. }
        exploit get_disjoint; [exact GET2|exact GET3|..]. i. des.
        { subst. timetac. }
        apply (x2 to3); econs; ss.
        + refl.
        + econs. ss. }
    inv H. rewrite GET2 in GET3. inv GET3.
    splits; auto.
  Qed.

  Lemma adjacent_exists
        loc from1 to1 msg mem
        (GET: get loc to1 mem = Some (from1, msg))
        (TO: Time.lt to1 (max_ts loc mem)):
    exists from2 to2,
      adjacent loc from1 to1 from2 to2 mem.
  Proof.
    exploit next_exists; eauto. i. des.
    esplits. econs; try exact x0; eauto. i.
    eapply x2; eauto.
    exploit get_ts; try exact x0. i. des.
    - subst. inv x1.
    - eapply TimeFacts.le_lt_lt; eauto.
  Qed.


  (* cap *)

  Inductive cap (mem1 mem2: t): Prop :=
  | cap_intro
      (SOUND: le mem1 mem2)
      (MIDDLE: forall loc from1 to1 from2 to2
                 (ADJ: adjacent loc from1 to1 from2 to2 mem1)
                 (TO: Time.lt to1 from2),
          get loc from2 mem2 = Some (to1, Message.reserve))
      (BACK: forall loc, get loc (Time.incr (max_ts loc mem1)) mem2 =
                    Some (max_ts loc mem1, Message.reserve))
      (COMPLETE: forall loc from to msg
                   (GET1: get loc to mem1 = None)
                   (GET2: get loc to mem2 = Some (from, msg)),
          (exists f m, get loc from mem1 = Some (f, m)))
  .
  #[global] Hint Constructors cap: core.

  Lemma cap_inv
        mem1 mem2
        loc from to msg
        (CLOSED: closed mem1)
        (CAP: cap mem1 mem2)
        (GET: get loc to mem2 = Some (from, msg)):
    get loc to mem1 = Some (from, msg) \/
    (get loc to mem1 = None /\
     exists from1 to2,
        adjacent loc from1 from to to2 mem1 /\
        Time.lt from to /\
        msg = Message.reserve) \/
    (get loc to mem1 = None /\
     from = max_ts loc mem1 /\
     to = Time.incr from /\
     msg = Message.reserve).
  Proof.
    inv CAP. move GET at bottom.
    destruct (get loc to mem1) as [[]|] eqn:GET1.
    { exploit SOUND; eauto. intros x.
      rewrite GET in x. inv x. auto. }
    right. exploit COMPLETE; eauto. intros x. des.
    exploit max_ts_spec; eauto. intros x0. des. inv MAX.
    - left.
      exploit adjacent_exists; try eapply H; eauto. intros x1. des.
      assert (LT: Time.lt from from2).
      { clear MIDDLE BACK COMPLETE GET0 H.
        inv x1. rewrite GET0 in x. inv x.
        exploit get_ts; try exact GET2. i. des.
        { subst. inv TS. }
        destruct (Time.le_lt_dec from2 from); auto.
        inv l.
        - exfalso.
          exploit get_ts; try exact GET0. i. des.
          { subst. inv H. }
          exploit get_disjoint; [exact GET0|exact GET2|..]. i. des.
          { subst. timetac. }
          apply (x2 from); econs; ss.
          + refl.
          + econs. auto.
        - exfalso. inv H.
          exploit SOUND; try exact GET2. intros x.
          exploit get_ts; try exact GET. i. des.
          { subst. rewrite GET1 in GET0. inv GET0. }
          exploit get_disjoint; [exact GET|exact x|..]. i. des.
          { subst. rewrite GET1 in GET2. inv GET2. }
          destruct (Time.le_lt_dec to to2).
          + apply (x3 to); econs; ss. refl.
          + apply (x3 to2); econs; ss.
            * econs. auto.
            * refl.
      }
      exploit MIDDLE; try eapply x1; eauto. intros x0.
      destruct (Time.eq_dec to from2).
      + subst. rewrite GET in x0. inv x0. esplits; eauto.
      + exfalso. inv x1.
        exploit get_ts; try exact GET. i. des.
        { subst. rewrite GET1 in x. inv x. }
        exploit get_ts; try exact x0. i. des.
        { subst. exploit SOUND; try exact GET3. intros x1.
          exploit get_disjoint; [exact GET|exact x1|..]. i. des.
          { subst. rewrite GET1 in GET3. inv GET3. }
          destruct (Time.le_lt_dec to to2).
          - apply (x4 to); econs; ss. refl.
          - apply (x4 to2); econs; ss.
            + econs. auto.
            + refl.
        }
        exploit get_disjoint; [exact GET|exact x0|..]. i. des; try congr.
        destruct (Time.le_lt_dec to from2).
        * apply (x4 to); econs; ss. refl.
        * apply (x4 from2); econs; ss.
          { econs. auto. }
          { refl. }
    - right. inv H. do 2 (split; auto).
      rewrite GET0 in x. inv x.
      specialize (BACK loc).
      exploit get_ts; try exact GET. i. des; try congr.
      exploit get_disjoint; [exact GET|exact BACK|..]. i. des.
      { subst. esplits; eauto. }
      exfalso.
      destruct (Time.le_lt_dec to (Time.incr (max_ts loc mem1))).
      + apply (x1 to); econs; ss. refl.
      + apply (x1 (Time.incr (max_ts loc mem1))); econs; s;
          eauto using Time.incr_spec; try refl.
        econs. ss.
  Qed.

  Lemma cap_closed_timemap
        mem1 mem2 tm
        (CAP: cap mem1 mem2)
        (CLOSED: closed_timemap tm mem1):
    closed_timemap tm mem2.
  Proof.
    inv CAP. ii.
    specialize (CLOSED loc). des.
    exploit SOUND; eauto.
  Qed.

  Lemma cap_closed_view
        mem1 mem2 view
        (CAP: cap mem1 mem2)
        (CLOSED: closed_view view mem1):
    closed_view view mem2.
  Proof.
    inv CLOSED.
    econs; eauto using cap_closed_timemap.
  Qed.

  Lemma cap_closed_opt_view
        mem1 mem2 view
        (CAP: cap mem1 mem2)
        (CLOSED: closed_opt_view view mem1):
    closed_opt_view view mem2.
  Proof.
    inv CLOSED; eauto using cap_closed_view.
  Qed.

  Lemma cap_closed_message
        mem1 mem2 msg
        (CAP: cap mem1 mem2)
        (CLOSED: closed_message msg mem1):
    closed_message msg mem2.
  Proof.
    inv CLOSED; eauto using cap_closed_opt_view.
  Qed.

  Lemma cap_future_weak
        mem1 mem2
        (CAP: cap mem1 mem2)
        (CLOSED: closed mem1):
    future_weak mem1 mem2.
  Proof.
    dup CAP. inv CAP. econs; ii.
    - exploit SOUND; eauto. i.
      esplits; eauto. refl.
    - exploit cap_inv; eauto. i. des; try congr.
    - exploit SOUND; eauto. congr.
  Qed.

  Lemma cap_closed
        mem1 mem2
        (CAP: cap mem1 mem2)
        (CLOSED: closed mem1):
    closed mem2.
  Proof.
    eapply future_weak_closed; eauto.
    eapply cap_future_weak; eauto.
  Qed.

  Lemma cap_inj
        mem mem1 mem2
        (CAP1: cap mem mem1)
        (CAP2: cap mem mem2)
        (CLOSED: closed mem):
    mem1 = mem2.
  Proof.
    apply ext. i.
    destruct (get loc ts mem1) as [[from1 msg1]|] eqn:GET1.
    - inv CAP2. exploit cap_inv; try exact GET1; eauto. i. des.
      + exploit SOUND; eauto.
      + subst. exploit MIDDLE; eauto.
      + subst. exploit BACK; eauto.
    - destruct (get loc ts mem2) as [[from2 msg2]|] eqn:GET2; ss.
      inv CAP1. exploit cap_inv; try exact GET2; eauto. i. des.
      + exploit SOUND; eauto. i. congr.
      + subst. exploit MIDDLE; eauto. i. congr.
      + subst. congr.
  Qed.

  Lemma cap_le
        promises mem1 mem2
        (CAP: cap mem1 mem2)
        (LE: le promises mem1):
    le promises mem2.
  Proof.
    ii. inv CAP. eauto.
  Qed.

  Lemma cap_max_ts
        mem1 mem2
        (CLOSED: closed mem1)
        (CAP: cap mem1 mem2):
    forall loc, max_ts loc mem2 = Time.incr (max_ts loc mem1).
  Proof.
    i. dup CAP. inv CAP0. specialize (BACK loc).
    exploit max_ts_spec; try exact BACK. i. des.
    apply TimeFacts.antisym; ss.
    destruct (Time.le_lt_dec (max_ts loc mem2) (Time.incr (max_ts loc mem1))); ss.
    specialize (Time.incr_spec (max_ts loc mem1)). i.
    exploit cap_inv; try exact GET; eauto. i. des.
    - exploit max_ts_spec; try exact x0. i. des.
      exploit TimeFacts.lt_le_lt; try exact l; try exact MAX0. i.
      rewrite x1 in H. timetac.
    - inv x1. exploit get_ts; try exact GET2. i. des.
      { rewrite x1 in *. inv l. }
      exploit max_ts_spec; try exact GET2. i. des.
      exploit TimeFacts.lt_le_lt; try exact x1; try exact MAX0. i.
      rewrite x3 in l. rewrite l in H. timetac.
    - subst. rewrite x2 in *. timetac.
  Qed.


  (* Existence of cap *)

  Lemma cap_exists
        mem1
        (CLOSED1: closed mem1):
    exists mem2, <<CAP: cap mem1 mem2>>.
  Proof.
    cut (exists mem2,
            forall loc,
              (fun loc cell =>
                 Cell.cap (mem1 loc) cell) loc (mem2 loc)).
    { i. des.
      exists mem2. econs; ii.
      - destruct (H loc). eauto.
      - destruct (H loc). inv ADJ.
        eapply MIDDLE; eauto. econs; eauto.
      - destruct (H loc). eauto.
      - destruct (H loc).
        exploit COMPLETE; eauto.
    }
    apply choice. i.
    apply Cell.cap_exists; try apply CLOSED1; ss.
  Qed.


  (* prev_None *)

  Definition prev_None (mem1 mem2: t): Prop :=
    forall loc from to msg
      (GET: get loc to mem1 = Some (from, msg))
      (RESERVE: msg <> Message.reserve)
      (GET_PREV: forall from' msg' (GET_PREV: get loc from mem1 = Some (from', msg')),
          msg' = Message.reserve),
    forall from' msg' (GET2: get loc from mem2 = Some (from', msg')),
      msg' = Message.reserve.

  Lemma promise_prev_None
        promises1 mem1 loc from to msg promises2 mem2 kind
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind):
    prev_None mem1 mem2.
  Proof.
    ii. apply NNPP. ii.
    revert GET2. inv PROMISE.
    - erewrite add_o; eauto. condtac; ss; eauto.
      i. des. inv GET2. eauto.
    - erewrite split_o; eauto. repeat condtac; ss; eauto.
      + i. des. inv GET2.
        exploit split_get0; try exact MEM. i. des.
        inv MEM. inv SPLIT.
        exploit get_ts; try exact GET. i. des.
        { subst. inv TS12. }
        exploit get_disjoint; [exact GET|exact GET1|..]. i. des.
        { subst. rewrite GET in *. inv GET1. timetac. }
        destruct (TimeFacts.le_lt_dec to0 ts3).
        * apply (x1 to0); econs; ss; try refl.
          etrans; try exact TS12. ss.
        * apply (x1 ts3); econs; ss; try refl.
          { econs; ss. }
          { etrans; eauto. }
      + guardH o. i. des. inv GET2.
        exploit split_get0; try exact MEM. i. des.
        exploit GET_PREV; eauto.
    - erewrite lower_o; eauto. condtac; ss; eauto.
      i. des. inv GET2.
      exploit lower_get0; try exact MEM. i. des.
      exploit GET_PREV; eauto. i. subst. inv MSG_LE. ss.
    - erewrite remove_o; eauto. condtac; ss; eauto.
  Qed.

  Lemma write_prev_None
        promises1 mem1 loc from to msg promises2 mem2 kind
        (WRITE: write promises1 mem1 loc from to msg promises2 mem2 kind):
    prev_None mem1 mem2.
  Proof.
    inv WRITE. eauto using promise_prev_None.
  Qed.

  Lemma promise_get_from
        promises1 mem1 loc from to msg promises2 mem2 kind
        l t f m
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind)
        (GET: get l t mem1 = Some (f, m))
        (RESERVE: m <> Message.reserve):
    exists t' m',
      (<<GET2: get l t' mem2 = Some (f, m')>>) /\
      (<<RESERVE2: m' <> Message.reserve>>).
  Proof.
    inv PROMISE.
    - exploit add_get1; eauto.
    - exploit split_get1; eauto. i. des.
      exploit split_get0; eauto. i. des.
      dup GET2. revert GET2.
      erewrite split_o; eauto. repeat condtac; ss; i.
      + des. subst. inv GET2. congr.
      + guardH o. des. subst. inv GET2.
        rewrite GET in *. inv GET1. eauto.
      + rewrite GET in *. inv GET2. eauto.
    - exploit lower_get1; eauto. i. des. esplits; eauto.
      ii. subst. inv MSG_LE. ss.
    - exploit remove_get1; try exact GET; eauto. i. des; eauto.
      subst. exploit remove_get0; try exact MEM. i. des. congr.
  Qed.

  Lemma prev_None_promise_prev_None
        mem
        promises1 mem1 loc from to msg promises2 mem2 kind
        (PREV: prev_None mem2 mem)
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind):
    prev_None mem1 mem.
  Proof.
    ii. exploit promise_get_from; eauto. i. des.
    hexploit promise_prev_None; eauto.
  Qed.

  Lemma prev_None_write_prev_None
        mem
        promises1 mem1 loc from to msg promises2 mem2 kind
        (PREV: prev_None mem2 mem)
        (WRITE: write promises1 mem1 loc from to msg promises2 mem2 kind):
    prev_None mem1 mem.
  Proof.
    inv WRITE. eauto using prev_None_promise_prev_None.
  Qed.

  Lemma prev_None_write_na_prev_None
        mem
        ts promises1 mem1 loc from to msg promises2 mem2 msgs kinds kind
        (PREV: prev_None mem2 mem)
        (WRITE: write_na ts promises1 mem1 loc from to msg promises2 mem2 msgs kinds kind):
    prev_None mem1 mem.
  Proof.
    induction WRITE; eauto using prev_None_write_prev_None.
  Qed.

  Lemma write_na_prev_None
        ts promises1 mem1 loc from to msg promises2 mem2 msgs kinds kind
        (WRITE: write_na ts promises1 mem1 loc from to msg promises2 mem2 msgs kinds kind):
    prev_None mem1 mem2.
  Proof.
    induction WRITE; eauto using write_prev_None, prev_None_write_prev_None.
  Qed.


  (* non-promised *)

  Lemma promise_non_promised
        promises1 mem1 loc from to msg promises2 mem2 kind
        l f t m
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind)
        (GET: Memory.get l t mem1 = Some (f, m))
        (GETP: Memory.get l t promises1 = None):
    (<<GET: Memory.get l t mem2 = Some (f, m)>>) /\
    (<<GETP: Memory.get l t promises2 = None>>).
  Proof.
    inv PROMISE.
    - erewrite (@Memory.add_o mem2); eauto.
      erewrite (@Memory.add_o promises2); eauto.
      condtac; ss. des. subst.
      exploit Memory.add_get0; try exact MEM. i. des. congr.
    - erewrite (@Memory.split_o mem2); eauto.
      erewrite (@Memory.split_o promises2); eauto.
      repeat (condtac; ss).
      + des. subst.
        exploit Memory.split_get0; try exact MEM. i. des. congr.
      + guardH o. des. subst.
        exploit Memory.split_get0; try exact PROMISES. i. des. congr.
    - erewrite (@Memory.lower_o mem2); eauto.
      erewrite (@Memory.lower_o promises2); eauto.
      condtac; ss. des. subst.
      exploit Memory.lower_get0; try exact PROMISES. i. des. congr.
    - erewrite (@Memory.remove_o mem2); eauto.
      erewrite (@Memory.remove_o promises2); eauto.
      condtac; ss. des. subst.
      exploit Memory.remove_get0; try exact PROMISES. i. des. congr.
  Qed.

  Lemma write_non_promised
        promises1 mem1 loc from to msg promises2 mem2 kind
        l f t m
        (WRITE: write promises1 mem1 loc from to msg promises2 mem2 kind)
        (GET: Memory.get l t mem1 = Some (f, m))
        (GETP: Memory.get l t promises1 = None):
    (<<GET: Memory.get l t mem2 = Some (f, m)>>) /\
    (<<GETP: Memory.get l t promises2 = None>>).
  Proof.
    inv WRITE.
    exploit promise_non_promised; eauto. i. des.
    split; auto.
    erewrite (@Memory.remove_o promises2); eauto. condtac; ss.
  Qed.

  Lemma write_na_non_promised
        ts promises1 mem1 loc from to val promises2 mem2 msgs kinds kind
        l f t m
        (WRITE: write_na ts promises1 mem1 loc from to val promises2 mem2 msgs kinds kind)
        (GET: Memory.get l t mem1 = Some (f, m))
        (GETP: Memory.get l t promises1 = None):
    (<<GET: Memory.get l t mem2 = Some (f, m)>>) /\
    (<<GETP: Memory.get l t promises2 = None>>).
  Proof.
    induction WRITE; eauto using write_non_promised.
    exploit write_non_promised; eauto. i. des. eauto.
  Qed.

  Lemma write_na_times
        ts promises1 mem1 loc from to val promises2 mem2 msgs kinds kind
        (WRITE: write_na ts promises1 mem1 loc from to val promises2 mem2 msgs kinds kind):
    List.Forall (fun m => Time.lt ts (snd (fst m))) msgs /\
    Time.lt ts to.
  Proof.
    induction WRITE; eauto.
    des. split; [|etrans; eauto].
    econs; eauto.
    rewrite List.Forall_forall in *. i.
    etrans; eauto.
  Qed.
End Memory.
