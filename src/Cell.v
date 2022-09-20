Require Import RelationClasses.
Require Import Decidable.
Require Import Coq.Lists.ListDec.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Loc.

From PromisingLib Require Import Event.
From Fairness Require Import Time.
From Fairness Require Import View.

Set Implicit Arguments.


Module Message.
  (* TODO: undef -> na message *)
  Inductive t :=
  | concrete (val: Const.t) (released: option View.t)
  | undef
  | reserve
  .
  #[global] Hint Constructors t: core.

  Definition elt: t := concrete Const.undef None.

  Inductive le : t -> t -> Prop :=
  | le_concrete
      val val' released released'
      (VAL: Const.le val' val)
      (RELEASED: View.opt_le released released'):
      le (concrete val released) (concrete val' released')
  | le_undef:
      le undef undef
  | le_reserve:
      le reserve reserve
  .
  #[global] Hint Constructors le: core.

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
    ii. destruct x; econs; refl.
  Qed.
  Next Obligation.
    ii. inv H; inv H0; econs; etrans; eauto.
  Qed.

  Lemma antisym a b
        (AB: le a b)
        (BA: le b a):
    a = b.
  Proof.
    inv AB; inv BA; ss. f_equal.
    - apply Const.antisym; auto.
    - apply View.opt_antisym; auto.
  Qed.

  Inductive wf: t -> Prop :=
  | wf_view
      val released
      (WF: View.opt_wf released):
      wf (concrete val released)
  | wf_undef:
      wf undef
  | wf_reserve:
      wf reserve
  .
  #[global] Hint Constructors wf: core.

  Definition elt_wf: wf elt.
  Proof. econs; ss. Qed.

  Definition is_reserve (msg: t): bool :=
    match msg with
    | reserve => true
    | _ => false
    end.

  Definition is_released_none (msg: t): bool :=
    match msg with
    | concrete _ None => true
    | _ => false
    end.
End Message.


Module Cell.
  Module Raw.
    Definition t := DOMap.t (DenseOrder.t * Message.t).

    Inductive wf (cell:t): Prop :=
    | wf_intro
        (VOLUME: forall from to msg
                   (GET: DOMap.find to cell = Some (from, msg)),
            (from, to) = (Time.bot, Time.bot) \/ Time.lt from to)
        (WF: forall from to msg
               (GET: DOMap.find to cell = Some (from, msg)),
            Message.wf msg)
        (DISJOINT: forall to1 to2 from1 from2 msg1 msg2
                     (GET1: DOMap.find to1 cell = Some (from1, msg1))
                     (GET2: DOMap.find to2 cell = Some (from2, msg2))
                     (NEQ: to1 <> to2),
            Interval.disjoint (from1, to1) (from2, to2))
    .
    #[global] Hint Constructors wf: core.

    Definition bot: t := DOMap.empty _.

    Lemma bot_wf: wf bot.
    Proof.
      econs; i.
      - rewrite DOMap.gempty in GET. inv GET.
      - rewrite DOMap.gempty in GET. inv GET.
      - rewrite DOMap.gempty in GET1. inv GET1.
    Qed.

    Definition singleton (from to:Time.t) (msg:Message.t): t :=
      DOMap.singleton to (from, msg).

    Lemma singleton_wf
          from to msg
          (LT: Time.lt from to)
          (WF: Message.wf msg):
      wf (singleton from to msg).
    Proof.
      unfold singleton. econs; s; i.
      - apply DOMap.singleton_find_inv in GET. des. inv GET0. auto.
      - apply DOMap.singleton_find_inv in GET. des. inv GET0. auto.
      - apply DOMap.singleton_find_inv in GET1. des. inv GET0.
        apply DOMap.singleton_find_inv in GET2. des. inv GET0.
        congr.
    Qed.

    Definition init: t :=
      DOMap.singleton Time.bot (Time.bot, Message.elt).

    Lemma init_wf: wf init.
    Proof.
      unfold init. econs; s; i.
      - apply DOMap.singleton_find_inv in GET. des. inv GET0. auto.
      - apply DOMap.singleton_find_inv in GET. des. inv GET0.
        apply Message.elt_wf.
      - apply DOMap.singleton_find_inv in GET1. des. inv GET0.
        apply DOMap.singleton_find_inv in GET2. des. inv GET0.
        congr.
    Qed.

    Lemma find_mem_ub
          from to msg cell
          (WF: wf cell)
          (FIND: DOMap.find to cell = Some (from, msg)):
      (from, to) = (Time.bot, Time.bot) \/
      Interval.mem (from, to) to.
    Proof.
      inv WF. exploit VOLUME; eauto. i. des; auto.
      right. econs; eauto. refl.
    Qed.

    Inductive add (cell1:t) (from to:Time.t) (msg:Message.t) (cell2:t): Prop :=
    | add_intro
        (DISJOINT: forall to2 from2 msg2
                          (GET2: DOMap.find to2 cell1 = Some (from2, msg2)),
            Interval.disjoint (from, to) (from2, to2))
        (TO: Time.lt from to)
        (MSG_WF: Message.wf msg)
        (CELL2: cell2 = DOMap.add to (from, msg) cell1):
        add cell1 from to msg cell2.
    #[global] Hint Constructors add: core.

    Lemma add_o
          cell2 cell1 from to msg
          t
          (ADD: add cell1 from to msg cell2):
      DOMap.find t cell2 =
      if Time.eq_dec t to
      then Some (from, msg)
      else DOMap.find t cell1.
    Proof.
      inv ADD. rewrite DOMap.gsspec.
      repeat condtac; auto; congr.
    Qed.

    Lemma add_wf
          cell1 from to msg cell2
          (ADD: add cell1 from to msg cell2)
          (CELL1: wf cell1):
      wf cell2.
    Proof.
      inv CELL1. econs; i.
      - revert GET. erewrite add_o; eauto. condtac; auto.
        + i. inv GET. inv ADD. auto.
        + i. eapply VOLUME; eauto.
      - revert GET. erewrite add_o; eauto. condtac; auto.
        + i. inv GET. inv ADD. auto.
        + i. eapply WF; eauto.
      - revert GET1 GET2.
        erewrite (add_o to1); eauto.
        erewrite (add_o to2); eauto.
        repeat condtac; s; i.
        + inv GET1. congr.
        + inv GET1. inv ADD. hexploit DISJOINT0; eauto.
        + inv GET2. inv ADD. symmetry. hexploit DISJOINT0; eauto.
        + eapply DISJOINT; eauto.
    Qed.

    Inductive split (cell1:t) (ts1 ts2 ts3:Time.t) (msg2 msg3:Message.t) (cell2:t): Prop :=
    | split_intro
        (GET2: DOMap.find ts3 cell1 = Some (ts1, msg3))
        (TS12: Time.lt ts1 ts2)
        (TS23: Time.lt ts2 ts3)
        (MSG_WF: Message.wf msg2)
        (CELL2: cell2 = DOMap.add ts2 (ts1, msg2)
                                  (DOMap.add ts3 (ts2, msg3) cell1))
    .
    #[global] Hint Constructors split: core.

    Lemma split_o
          cell2 cell1 ts1 ts2 ts3 msg2 msg3
          t
          (SPLIT: split cell1 ts1 ts2 ts3 msg2 msg3 cell2):
      DOMap.find t cell2 =
      if Time.eq_dec t ts2
      then Some (ts1, msg2)
      else if Time.eq_dec t ts3
           then Some (ts2, msg3)
           else DOMap.find t cell1.
    Proof.
      inv SPLIT. rewrite ? DOMap.gsspec.
      repeat condtac; repeat subst; try congr.
    Qed.

    Lemma split_wf
          cell2 cell1 ts1 ts2 ts3 msg2 msg3
          (SPLIT: split cell1 ts1 ts2 ts3 msg2 msg3 cell2)
          (CELL1: wf cell1):
      wf cell2.
    Proof.
      inv CELL1. econs; i.
      - revert GET. erewrite split_o; eauto. repeat condtac; auto.
        + i. inv GET. inv SPLIT. auto.
        + i. inv GET. inv SPLIT. auto.
        + i. eapply VOLUME; eauto.
      - revert GET. erewrite split_o; eauto. repeat condtac; auto.
        + i. inv GET. inv SPLIT. eauto.
        + i. inv GET. inv SPLIT. eauto.
        + i. eapply WF; eauto.
      - revert GET1 GET2.
        erewrite (split_o to1); eauto.
        erewrite (split_o to2); eauto.
        repeat condtac; repeat subst; try congr; i.
        + inv GET1. inv GET2.
          eapply Interval.disjoint_imm.
        + inv GET1.
          inv SPLIT. hexploit DISJOINT; try exact n0; eauto. i.
          symmetry in H. eapply Interval.le_disjoint; eauto.
          econs; [refl|by left].
        + inv GET1. inv GET2.
          symmetry. eapply Interval.disjoint_imm.
        + inv GET1.
          inv SPLIT. hexploit DISJOINT; try exact NEQ; eauto. i.
          eapply Interval.le_disjoint; eauto.
          econs; [by left|refl].
        + inv GET2.
          inv SPLIT. hexploit DISJOINT; try exact n0; eauto. i.
          symmetry in H. symmetry. eapply Interval.le_disjoint; eauto.
          econs; [refl|by left].
        + inv GET2.
          inv SPLIT. hexploit DISJOINT; try exact n0; eauto. i.
          symmetry in H. symmetry. eapply Interval.le_disjoint; eauto.
          econs; [by left|refl].
        + eapply DISJOINT; eauto.
    Qed.

    Inductive lower (cell1:t) (from to:Time.t) (msg1 msg2: Message.t) (cell2:t): Prop :=
    | update_intro
        (GET2: DOMap.find to cell1 = Some (from, msg1))
        (TS: Time.lt from to)
        (MSG_WF: Message.wf msg2)
        (MSG_LE: Message.le msg2 msg1)
        (CELL2: cell2 = DOMap.add to (from, msg2) cell1)
    .
    #[global] Hint Constructors lower: core.

    Lemma lower_o
          cell2 cell1 from to msg1 msg2
          t
          (LOWER: lower cell1 from to msg1 msg2 cell2):
      DOMap.find t cell2 =
      if Time.eq_dec t to
      then Some (from, msg2)
      else DOMap.find t cell1.
    Proof.
      inv LOWER. rewrite DOMap.gsspec.
      repeat condtac; auto; congr.
    Qed.

    Lemma lower_wf
          cell2 cell1 from to msg1 msg2
          (LOWER: lower cell1 from to msg1 msg2 cell2)
          (CELL1: wf cell1)
          (MSG2: Message.wf msg2):
      wf cell2.
    Proof.
      inv CELL1. econs; i.
      - revert GET. erewrite lower_o; eauto. condtac; auto.
        + i. inv GET. inv LOWER. eapply VOLUME. eauto.
        + i. eapply VOLUME; eauto.
      - revert GET. erewrite lower_o; eauto. condtac.
        + i. inv GET. inv LOWER. auto.
        + i. eapply WF. eauto.
      - revert GET1 GET2.
        erewrite (lower_o to1); eauto.
        erewrite (lower_o to2); eauto.
        repeat condtac; repeat subst; try congr; i.
        + inv GET1. inv LOWER. eapply DISJOINT; eauto.
        + inv GET2. inv LOWER. eapply DISJOINT; eauto.
        + eapply DISJOINT; eauto.
    Qed.

    Inductive remove (cell1:t) (from to:Time.t) (msg:Message.t) (cell2:t): Prop :=
    | remove_intro
        (GET: DOMap.find to cell1 = Some (from, msg))
        (CELL2: cell2 = DOMap.remove to cell1)
    .
    #[global] Hint Constructors remove: core.

    Lemma remove_o
          cell2 cell1 from to msg
          t
          (REMOVE: remove cell1 from to msg cell2):
      DOMap.find t cell2 =
      if Time.eq_dec t to
      then None
      else DOMap.find t cell1.
    Proof.
      inv REMOVE. rewrite DOMap.grspec.
      repeat condtac; auto; congr.
    Qed.

    Lemma remove_wf
          cell1 from to msg cell2
          (REMOVE: remove cell1 from to msg cell2)
          (CELL1: wf cell1):
      wf cell2.
    Proof.
      inv CELL1. econs; i.
      - revert GET. erewrite remove_o; eauto. condtac; try congr.
        i. eapply VOLUME; eauto.
      - revert GET. erewrite remove_o; eauto. condtac; ss. apply WF.
      - revert GET1 GET2.
        erewrite (remove_o to1); eauto.
        erewrite (remove_o to2); eauto.
        repeat condtac; repeat subst; try congr; i.
        eapply DISJOINT; eauto.
    Qed.
  End Raw.

  Structure t := mk {
    raw :> Raw.t;
    WF: Raw.wf raw;
  }.

  Definition get (ts:Time.t) (cell:t): option (Time.t * Message.t) := DOMap.find ts (raw cell).

  Lemma ext
        (lhs rhs:t)
        (EXT: forall ts, get ts lhs = get ts rhs):
    lhs = rhs.
  Proof.
    destruct lhs, rhs.
    assert (raw0 = raw1).
    { apply DOMap.eq_leibniz. ii. apply EXT. }
    subst raw1. f_equal. apply proof_irrelevance.
  Qed.

  Lemma get_ts
        to cell from msg
        (GET: get to cell = Some (from, msg)):
    (from = Time.bot /\ to = Time.bot) \/ Time.lt from to.
  Proof.
    destruct cell. unfold get in *. ss.
    inv WF0. exploit VOLUME; eauto. intros x. des.
    - inv x. auto.
    - generalize (Time.le_lteq from to). i. des. auto.
  Qed.

  Lemma get_disjoint
        f1 f2 t1 t2 msg1 msg2 cell
        (GET1: get t1 cell = Some (f1, msg1))
        (GET2: get t2 cell = Some (f2, msg2)):
    (t1 = t2 /\ f1 = f2 /\ msg1 = msg2) \/
    Interval.disjoint (f1, t1) (f2, t2).
  Proof.
    destruct (Time.eq_dec t1 t2).
    { subst. rewrite GET1 in GET2. inv GET2. auto. }
    unfold get in *. unfold Cell.get in *.
    destruct cell; ss. inv WF0.
    hexploit DISJOINT; [exact GET1|exact GET2|..]; eauto.
  Qed.

  Definition le (lhs rhs:t): Prop :=
    forall to from msg
      (LHS: get to lhs = Some (from, msg)),
      get to rhs = Some (from, msg).

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation. ii. auto. Qed.
  Next Obligation. ii. eapply H0; eauto. Qed.

  Definition bot: t := mk Raw.bot_wf.

  Lemma bot_get ts: get ts bot = None.
  Proof. unfold get, bot, Raw.bot. s. apply DOMap.gempty. Qed.

  Lemma bot_le cell: le bot cell.
  Proof. ii. rewrite bot_get in LHS. congr. Qed.

  Lemma finite cell:
    exists dom,
    forall from to msg (GET: get to cell = Some (from, msg)),
      List.In to dom.
  Proof.
    exists (List.map (fun e => (fst e)) (DOMap.elements (Cell.raw cell))). i.
    exploit DOMap.elements_correct; eauto. i.
    eapply in_prod; eauto.
  Qed.

  Definition singleton
             (from to:Time.t) (msg:Message.t)
             (LT: Time.lt from to)
             (WF: Message.wf msg): t :=
    mk (Raw.singleton_wf LT WF).

  Lemma singleton_get
        from to msg t
        (LT: Time.lt from to)
        (WF: Message.wf msg):
    get t (singleton LT WF) =
    if Time.eq_dec t to
    then Some (from, msg)
    else None.
  Proof.
    unfold get, singleton, Raw.singleton. ss. condtac.
    - subst. rewrite DOMap.singleton_eq. auto.
    - rewrite DOMap.singleton_neq; auto.
  Qed.

  Definition init: t := mk Raw.init_wf.

  Lemma init_get t:
    get t init =
    if Time.eq_dec t Time.bot
    then Some (Time.bot, Message.elt)
    else None.
  Proof.
    unfold get, init, Raw.init. ss. condtac.
    - subst. rewrite DOMap.singleton_eq. auto.
    - rewrite DOMap.singleton_neq; auto.
  Qed.

  Definition add (cell1:t) (from to:Time.t) (msg: Message.t) (cell2:t): Prop :=
    Raw.add cell1 from to msg cell2.

  Definition split (cell1:t) (ts1 ts2 ts3:Time.t) (msg2 msg3: Message.t) (cell2:t): Prop :=
    Raw.split cell1 ts1 ts2 ts3 msg2 msg3 cell2.

  Definition lower (cell1:t) (from to:Time.t) (msg1 msg2: Message.t) (cell2:t): Prop :=
    Raw.lower cell1 from to msg1 msg2 cell2.

  Definition remove (cell1:t) (from to:Time.t) (msg: Message.t) (cell2:t): Prop :=
    Raw.remove cell1 from to msg cell2.

  Lemma add_o
        cell2 cell1 from to msg
        t
        (ADD: add cell1 from to msg cell2):
    get t cell2 =
    if Time.eq_dec t to
    then Some (from, msg)
    else get t cell1.
  Proof. apply Raw.add_o. auto. Qed.

  Lemma split_o
        cell2 cell1 ts1 ts2 ts3 msg2 msg3
        t
        (SPLIT: split cell1 ts1 ts2 ts3 msg2 msg3 cell2):
    get t cell2 =
    if Time.eq_dec t ts2
    then Some (ts1, msg2)
    else if Time.eq_dec t ts3
         then Some (ts2, msg3)
         else get t cell1.
  Proof. apply Raw.split_o. auto. Qed.

  Lemma lower_o
        cell2 cell1 from to msg1 msg2
        t
        (LOWER: lower cell1 from to msg1 msg2 cell2):
    get t cell2 =
    if Time.eq_dec t to
    then Some (from, msg2)
    else get t cell1.
  Proof. eapply Raw.lower_o. eauto. Qed.

  Lemma remove_o
        cell2 cell1 from to msg
        t
        (REMOVE: remove cell1 from to msg cell2):
    get t cell2 =
    if Time.eq_dec t to
    then None
    else get t cell1.
  Proof. eapply Raw.remove_o. eauto. Qed.

  Definition max_ts (cell:t): Time.t :=
    DOMap.max_key (raw cell).

  Lemma max_ts_spec
        ts from msg cell
        (GET: get ts cell = Some (from, msg)):
    <<GET: exists from msg, get (max_ts cell) cell = Some (from, msg)>> /\
    <<MAX: Time.le ts (max_ts cell)>>.
  Proof.
    unfold get in GET.
    generalize (DOMap.max_key_spec (Cell.raw cell)). i. des. splits; eauto.
    - destruct (DOMap.find
                  (DOMap.max_key (Cell.raw cell))
                  (Cell.raw cell)) as [[]|]eqn:X.
      + esplits; eauto.
      + exfalso. eapply FIND; eauto. rewrite GET. congr.
    - apply MAX. rewrite GET. auto. congr.
  Qed.

  Lemma add_exists
        cell1 from to msg
        (DISJOINT: forall to2 from2 msg2
                     (GET2: get to2 cell1 = Some (from2, msg2)),
            Interval.disjoint (from, to) (from2, to2))
        (TO1: Time.lt from to)
        (WF: Message.wf msg):
    exists cell2, add cell1 from to msg cell2.
  Proof.
    destruct cell1. eexists (mk _). econs; s; eauto.
    Unshelve.
    eapply Raw.add_wf; eauto.
  Qed.

  Lemma add_exists_max_ts
        cell1 to msg
        (TO: Time.lt (max_ts cell1) to)
        (WF: Message.wf msg):
    exists cell2, add cell1 (max_ts cell1) to msg cell2.
  Proof.
    apply add_exists; auto. i.
    exploit max_ts_spec; eauto. i. des.
    ii. inv LHS. inv RHS. ss.
    rewrite MAX in TO1. eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt; eauto.
  Qed.

  Lemma add_exists_le
        promises1 cell1 from to msg cell2
        (LE: le promises1 cell1)
        (ADD: add cell1 from to msg cell2):
    exists promises2, add promises1 from to msg promises2.
  Proof.
    inv ADD. apply add_exists; auto. i.
    eapply DISJOINT. eauto.
  Qed.

  Lemma split_exists
        cell1 ts1 ts2 ts3 msg2 msg3
        (GET2: get ts3 cell1 = Some (ts1, msg3))
        (TS12: Time.lt ts1 ts2)
        (TS23: Time.lt ts2 ts3)
        (REL_WF: Message.wf msg2):
    exists cell2, split cell1 ts1 ts2 ts3 msg2 msg3 cell2.
  Proof.
    destruct cell1. eexists (mk _). econs; s; eauto.
    Unshelve.
    eapply Raw.split_wf; eauto.
  Qed.

  Lemma split_exists_le
        promises1 cell1 ts1 ts2 ts3 msg2 msg3 promises2
        (LE: le promises1 cell1)
        (SPLIT: split promises1 ts1 ts2 ts3 msg2 msg3 promises2):
    exists cell2, split cell1 ts1 ts2 ts3 msg2 msg3 cell2.
  Proof.
    inv SPLIT. eapply split_exists; eauto.
  Qed.

  Lemma lower_exists
        cell1 from to msg1 msg2
        (GET2: get to cell1 = Some (from, msg1))
        (TS: Time.lt from to)
        (REL_WF: Message.wf msg2)
        (REL_LE: Message.le msg2 msg1):
    exists cell2, lower cell1 from to msg1 msg2 cell2.
  Proof.
    destruct cell1. eexists (mk _). unfold lower. econs; eauto. ss.
    Unshelve.
    eapply Raw.lower_wf; eauto.
  Qed.

  Lemma lower_exists_le
        promises1 cell1 from to msg1 msg2 promises2
        (LE: le promises1 cell1)
        (LOWER: lower promises1 from to msg1 msg2 promises2):
    exists cell2, lower cell1 from to msg1 msg2 cell2.
  Proof.
    inv LOWER. apply lower_exists; auto.
  Qed.


  (* Lemmas on add, split, lower & remove *)

  Lemma add_get0
        cell1 from1 to1 msg1 cell2
        (ADD: add cell1 from1 to1 msg1 cell2):
    <<GET: get to1 cell1 = None>> /\
    <<GET: get to1 cell2 = Some (from1, msg1)>>.
  Proof.
    inv ADD. unfold get. splits.
    - destruct (DOMap.find to1 (raw cell1)) as [[]|] eqn:X; auto.
      exfalso. exploit DISJOINT; eauto.
      + apply Interval.mem_ub. auto.
      + apply Interval.mem_ub.
        destruct (Cell.WF cell1). exploit VOLUME; eauto. intros x. des; ss.
        inv x. inv TO.
    - rewrite CELL2, DOMap.gsspec. condtac; ss.
  Qed.

  Lemma split_get0
        cell1 ts1 ts2 ts3 msg2 msg3 cell2
        (SPLIT: split cell1 ts1 ts2 ts3 msg2 msg3 cell2):
    <<GET: get ts2 cell1 = None>> /\
    <<GET: get ts3 cell1 = Some (ts1, msg3)>> /\
    <<GET: get ts2 cell2 = Some (ts1, msg2)>> /\
    <<GET: get ts3 cell2 = Some (ts2, msg3)>>.
  Proof.
    inv SPLIT. splits; auto.
    - destruct (get ts2 cell1) as [[]|] eqn:X; auto.
      destruct (WF cell1). exfalso. eapply DISJOINT.
      + apply X.
      + apply GET2.
      + ii. subst. eapply Time.lt_strorder. eauto.
      + apply Interval.mem_ub. exploit VOLUME; eauto. intros x. des; auto.
        inv x. inv TS12.
      + econs; ss. left. auto.
    - unfold get. rewrite CELL2. rewrite ? DOMap.gsspec.
      repeat condtac; ss.
    - unfold get. rewrite CELL2. rewrite ? DOMap.gsspec.
      repeat condtac; ss.
      subst. timetac.
  Qed.

  Lemma lower_get0
        cell1 from to msg1 msg2 cell2
        (LOWER: lower cell1 from to msg1 msg2 cell2):
    <<GET: get to cell1 = Some (from, msg1)>> /\
    <<GET: get to cell2 = Some (from, msg2)>> /\
    <<MSG_LE: Message.le msg2 msg1>>.
  Proof.
    inv LOWER. splits; auto.
    unfold get. rewrite CELL2. rewrite DOMap.gsspec. condtac; ss.
  Qed.

  Lemma remove_get0
        cell1 from to msg cell2
        (REMOVE: remove cell1 from to msg cell2):
    <<GET: get to cell1 = Some (from, msg)>> /\
    <<GET: get to cell2 = None>>.
  Proof.
    inv REMOVE. splits; auto.
    unfold get. rewrite CELL2. rewrite DOMap.grspec. condtac; ss.
  Qed.

  Lemma add_get1
        cell1 from to msg cell2
        f t m
        (ADD: add cell1 from to msg cell2)
        (GET1: get t cell1 = Some (f, m)):
    get t cell2 = Some (f, m).
  Proof.
    erewrite add_o; eauto. condtac; ss.
    des. subst. exploit add_get0; eauto. i. des. congr.
  Qed.

  Lemma add_inhabited
        cell1 cell2 from to msg
        (ADD: add cell1 from to msg cell2)
        (INHABITED: get Time.bot cell1 = Some (Time.bot, Message.elt)):
    <<INHABITED: get Time.bot cell2 = Some (Time.bot, Message.elt)>>.
  Proof.
    erewrite add_o; eauto. condtac; auto. subst.
    inv ADD. inv TO.
  Qed.

  Lemma split_inhabited
        cell1 ts1 ts2 ts3 msg2 msg3 cell2
        (SPLIT: split cell1 ts1 ts2 ts3 msg2 msg3 cell2)
        (INHABITED: get Time.bot cell1 = Some (Time.bot, Message.elt)):
    <<INHABITED: get Time.bot cell2 = Some (Time.bot, Message.elt)>>.
  Proof.
    erewrite split_o; eauto. repeat condtac; subst; ss.
    - inv SPLIT. inv TS12.
    - inv SPLIT. inv TS23.
  Qed.

  Lemma lower_inhabited
        cell1 from to msg1 msg2 cell2
        (LOWER: lower cell1 from to msg1 msg2 cell2)
        (INHABITED: get Time.bot cell1 = Some (Time.bot, Message.elt)):
    <<INHABITED: get Time.bot cell2 = Some (Time.bot, Message.elt)>>.
  Proof.
    erewrite lower_o; eauto. condtac; auto.
    subst. inv LOWER. inv TS.
  Qed.

  Lemma add_max_ts
        cell1 to msg cell2
        (ADD: add cell1 (max_ts cell1) to msg cell2)
        (INHABITED: get Time.bot cell1 = Some (Time.bot, Message.elt)):
    max_ts cell2 = to.
  Proof.
    hexploit add_inhabited; eauto. i. des.
    exploit max_ts_spec; eauto. i. des.
    revert GET. erewrite add_o; eauto. condtac; auto. i.
    apply TimeFacts.antisym.
    - left. eapply TimeFacts.le_lt_lt.
      + eapply max_ts_spec. eauto.
      + inv ADD. auto.
    - eapply max_ts_spec. erewrite add_o; eauto. condtac; ss.
  Qed.

  Lemma remove_singleton
        from to msg
        (LT:Time.lt from to)
        (WF: Message.wf msg):
    remove (singleton LT WF) from to msg bot.
  Proof.
    assert (Raw.bot = DOMap.remove to ((raw (singleton LT WF)))).
    { apply DOMap.eq_leibniz. ii.
      unfold Raw.bot. rewrite DOMap.gempty.
      rewrite DOMap.grspec. condtac; auto.
      unfold singleton, Raw.singleton, raw.
      rewrite DOMap.singleton_neq; auto.
    }
    unfold remove. s. rewrite H. econs; ss.
    unfold Raw.singleton. rewrite DOMap.singleton_eq. auto.
  Qed.

  Lemma remove_exists
        cell1 from to msg
        (GET: get to cell1 = Some (from, msg)):
    exists cell2, remove cell1 from to msg cell2.
  Proof.
    eexists (mk _). destruct cell1. ss.
    Unshelve.
    { eapply Raw.remove_wf.
      - econs; eauto.
      - apply WF.
    }
  Qed.

  Lemma get_opt_wf
        cell from to msg
        (GET: get to cell = Some (from, msg)):
    Message.wf msg.
  Proof.
    destruct cell. destruct WF0. eauto.
  Qed.


  (* min_concrete_ts *)

  Inductive min_concrete_ts (cell: t) (ts: Time.t): Prop :=
  | min_concrete_ts_intro
      from msg
      (GET: get ts cell = Some (from, msg))
      (RESERVE: msg <> Message.reserve)
      (MIN: forall to from' msg'
              (GET: get to cell = Some (from', msg'))
              (RESERVE: msg' <> Message.reserve),
          Time.le ts to)
  .

  Lemma min_concrete_ts_exists_aux
        A t a
        (l: list (Time.t * A))
        (f: A -> bool)
        (INHABITED1: f a = true)
        (INHABITED2: List.In (t, a) l):
    exists min_t min_a,
      f min_a = true /\
      List.In (min_t, min_a) l /\
      (forall t' a' (IN: List.In (t', a') l) (F: f a' = true), Time.le min_t t').
  Proof.
    remember (length l) eqn:LEN.
    revert INHABITED1 INHABITED2 LEN. revert t a l.
    induction n; i.
    { destruct l; inv LEN. inv INHABITED2. }
    destruct l; inv LEN.
    destruct p as [t1 a1]. ss. des.
    - inv INHABITED2. destruct l.
      + esplits; eauto. i. des; inv IN. refl.
      + exploit (IHn t0 a ((t0, a)::l)); auto; try by econs.
        i. des. destruct p as [new_t new_a]. ss.
        destruct (f new_a) eqn:FNEW; cycle 1.
        { esplits; try exact x0.
          - des; eauto.
          - i. guardH x1. des.
            + inv IN. eapply x2; eauto.
            + inv IN. rewrite F in FNEW. inv FNEW.
            + eapply x2; eauto. }
        destruct (Time.le_lt_dec min_t new_t).
        { esplits; try exact x0.
          - des; eauto.
          - i. guardH x1. des.
            + inv IN. eapply x2; eauto.
            + inv IN. auto.
            + eapply x2; eauto. }
        exists new_t. exists new_a. splits; auto.
        i. guardH x1. des.
        * inv IN. exploit (x2 t' a'); eauto. i.
          etrans; eauto. econs. auto.
        * inv IN. refl.
        * etrans; [econs; try exact l0|].
          eapply x2; eauto.
    - exploit (IHn t0 a l); eauto. i. des.
      destruct (f a1) eqn:FNEW; cycle 1.
      { esplits; try exact x0; eauto.
        i. des.
        - inv IN. rewrite FNEW in F. inv F.
        - eapply x2; eauto. }
      destruct (Time.le_lt_dec min_t t1).
      { esplits; try exact x0; eauto.
        i. des.
        - inv IN. auto.
        - eapply x2; eauto. }
      exists t1. exists a1. esplits; eauto.
      i. des.
      + inv IN. refl.
      + etrans; [econs; exact l0|].
        eapply x2; eauto.
  Qed.

  Lemma min_concrete_ts_exists
        from to msg cell
        (INHABITED: get to cell = Some (from, msg))
        (RESERVE: msg <> Message.reserve):
    exists ts, min_concrete_ts cell ts.
  Proof.
    destruct cell. unfold get in *. ss.
    remember (DOMap.elements raw0) as l eqn:DOM.
    exploit (min_concrete_ts_exists_aux
               to (from, msg) l
               (fun (a: Time.t * Message.t) => match a with
                                            | (_, Message.reserve) => false
                                            | _ => true
                                            end)).
    { destruct msg; ss. }
    { subst. eapply DOMap.elements_correct. auto. }
    i. des. destruct min_a.
    exists min_t. econs.
    - subst. esplits. unfold get. ss.
      eapply DOMap.elements_complete. eauto.
    - destruct t1; ss.
    - i. unfold get in GET. ss.
      apply DOMap.elements_correct in GET. subst.
      eapply x2; eauto. ss.
      destruct msg'; ss.
  Qed.

  Lemma min_concrete_ts_inj
        cell ts1 ts2
        (MIN1: min_concrete_ts cell ts1)
        (MIN2: min_concrete_ts cell ts2):
    ts1 = ts2.
  Proof.
    inv MIN1. inv MIN2.
    apply MIN0 in GET; eauto.
    apply MIN in GET0; eauto.
    apply TimeFacts.antisym; auto.
  Qed.

  Lemma min_concrete_ts_spec
        ts from msg cell mts
        (MIN: min_concrete_ts cell mts)
        (GET: get ts cell = Some (from, msg))
        (RESERVE: msg <> Message.reserve):
    <<GET: exists f m, get mts cell = Some (f, m) /\ m <> Message.reserve>> /\
    <<MIN: Time.le mts ts>>.
  Proof.
    inv MIN. esplits; eauto.
  Qed.


  (* max_concrete_ts *)

  Inductive max_concrete_ts (cell: t) (ts: Time.t): Prop :=
  | max_concrete_ts_intro
      (GET: exists from val released, get ts cell = Some (from, Message.concrete val released))
      (MAX: forall to from' val' released'
              (GET: get to cell = Some (from', Message.concrete val' released')),
          Time.le to ts)
  .

  Lemma max_concrete_ts_exists_aux
        A t a
        (l: list (Time.t * A))
        (f: A -> bool)
        (INHABITED1: f a = true)
        (INHABITED2: List.In (t, a) l):
    exists max_t max_a,
      f max_a = true /\
      List.In (max_t, max_a) l /\
      (forall t' a' (IN: List.In (t', a') l) (F: f a' = true), Time.le t' max_t).
  Proof.
    remember (length l) eqn:LEN.
    revert INHABITED1 INHABITED2 LEN. revert t a l.
    induction n; i.
    { destruct l; inv LEN. inv INHABITED2. }
    destruct l; inv LEN.
    destruct p as [t1 a1]. ss. des.
    - inv INHABITED2. destruct l.
      + esplits; eauto. i. des; inv IN. refl.
      + exploit (IHn t0 a ((t0, a)::l)); auto; try by econs.
        i. des. destruct p as [new_t new_a]. ss.
        destruct (f new_a) eqn:FNEW; cycle 1.
        { esplits; try exact x0.
          - des; eauto.
          - i. guardH x1. des.
            + inv IN. eapply x2; eauto.
            + inv IN. rewrite F in FNEW. inv FNEW.
            + eapply x2; eauto. }
        destruct (Time.le_lt_dec new_t max_t).
        { esplits; try exact x0.
          - des; eauto.
          - i. guardH x1. des.
            + inv IN. eapply x2; eauto.
            + inv IN. auto.
            + eapply x2; eauto. }
        exists new_t. exists new_a. splits; auto.
        i. guardH x1. des.
        * inv IN. exploit (x2 t' a'); eauto. i.
          etrans; eauto. econs. auto.
        * inv IN. refl.
        * etrans; [|econs; exact l0].
          eapply x2; eauto.
    - exploit (IHn t0 a l); eauto. i. des.
      destruct (f a1) eqn:FNEW; cycle 1.
      { esplits; try exact x0; eauto.
        i. des.
        - inv IN. rewrite FNEW in F. inv F.
        - eapply x2; eauto. }
      destruct (Time.le_lt_dec t1 max_t).
      { esplits; try exact x0; eauto.
        i. des.
        - inv IN. auto.
        - eapply x2; eauto. }
      exists t1. exists a1. esplits; eauto.
      i. des.
      + inv IN. refl.
      + etrans; [|econs; exact l0].
        eapply x2; eauto.
  Qed.

  Lemma max_concrete_ts_exists
        cell
        (INHABITED: get Time.bot cell = Some (Time.bot, Message.elt)):
    exists ts, max_concrete_ts cell ts.
  Proof.
    destruct cell. unfold get in *. ss.
    remember (DOMap.elements raw0) as l eqn:DOM.
    exploit (max_concrete_ts_exists_aux
               Time.bot (Time.bot, Message.elt) l
               (fun (a: Time.t * Message.t) => match a with
                                            | (_, Message.concrete _ _) => true
                                            | _ => false
                                            end)).
    { ss. }
    { subst. eapply DOMap.elements_correct. auto. }
    i. des. destruct max_a. destruct t1; ss.
    exists max_t. econs.
    - subst. esplits. unfold get. ss.
      eapply DOMap.elements_complete. eauto.
    - i. unfold get in GET. ss.
      apply DOMap.elements_correct in GET. subst.
      eapply x2; eauto.
  Qed.

  Lemma max_concrete_ts_inj
        cell ts1 ts2
        (MAX1: max_concrete_ts cell ts1)
        (MAX2: max_concrete_ts cell ts2):
    ts1 = ts2.
  Proof.
    inv MAX1. inv MAX2. des.
    apply MAX0 in GET. apply MAX in GET0.
    apply TimeFacts.antisym; auto.
  Qed.

  Lemma max_concrete_ts_spec
        ts from val released cell mts
        (MAX: max_concrete_ts cell mts)
        (GET: get ts cell = Some (from, Message.concrete val released)):
    <<GET: exists f v r, get mts cell = Some (f, Message.concrete v r)>> /\
    <<MAX: Time.le ts mts>>.
  Proof.
    inv MAX. des. esplits; eauto.
  Qed.


  (* max_non_reserve_ts *)

  Inductive max_non_reserve_ts (cell: t) (ts: Time.t): Prop :=
  | max_non_reserve_ts_intro
      (GET: exists from msg (RESERVE: msg <> Message.reserve),
          get ts cell = Some (from, msg))
      (MAX: forall to from' msg' (RESERVE: msg' <> Message.reserve)
              (GET: get to cell = Some (from', msg')),
          Time.le to ts)
  .

  Lemma max_non_reserve_ts_exists
        cell
        (INHABITED: get Time.bot cell = Some (Time.bot, Message.elt)):
    exists ts, max_non_reserve_ts cell ts.
  Proof.
    destruct cell. unfold get in *. ss.
    remember (DOMap.elements raw0) as l eqn:DOM.
    exploit (max_concrete_ts_exists_aux
               Time.bot (Time.bot, Message.elt) l
               (fun (a: Time.t * Message.t) => match a with
                                            | (_, Message.reserve) => false
                                            | _ => true
                                            end)).
    { ss. }
    { subst. eapply DOMap.elements_correct. auto. }
    i. des. destruct max_a.
    exists max_t. econs.
    - subst. esplits; cycle 1.
      + unfold get. ss. eapply DOMap.elements_complete. eauto.
      + destruct t1; ss.
    - i. unfold get in GET. ss.
      apply DOMap.elements_correct in GET. subst.
      eapply x2; eauto. destruct msg'; ss.
  Qed.

  Lemma max_non_reserve_ts_inj
        cell ts1 ts2
        (MAX1: max_non_reserve_ts cell ts1)
        (MAX2: max_non_reserve_ts cell ts2):
    ts1 = ts2.
  Proof.
    inv MAX1. inv MAX2. des.
    apply MAX0 in GET; ss.
    apply MAX in GET0; ss.
    apply TimeFacts.antisym; auto.
  Qed.

  Lemma max_non_reserve_ts_spec
        ts from msg cell mts
        (MAX: max_non_reserve_ts cell mts)
        (GET: get ts cell = Some (from, msg))
        (RESERVE: msg <> Message.reserve):
    <<GET: exists f m, get mts cell = Some (f, m) /\ m <> Message.reserve>> /\
    <<MAX: Time.le ts mts>>.
  Proof.
    inv MAX. des. esplits; eauto.
  Qed.


  (* next greater timestamp *)

  Fixpoint next (t: Time.t) (l: list Time.t) (res: option Time.t): option Time.t :=
    match l with
    | [] => res
    | hd :: tl =>
      if (Time.le_lt_dec hd t)
      then next t tl res
      else
        match res with
        | Some res =>
          if (Time.le_lt_dec res hd)
          then next t tl (Some res)
          else next t tl (Some hd)
        | None => next t tl (Some hd)
        end
    end.

  Lemma next_le
        t tnext init l
        (NEXT: next t l (Some init) = Some tnext):
    Time.le tnext init.
  Proof.
    revert init NEXT. induction l; ss; i.
    - inv NEXT. refl.
    - revert NEXT. repeat (condtac; ss); i.
      + exploit IHl; try exact NEXT. i. auto.
      + exploit IHl; try exact NEXT. i. auto.
      + exploit IHl; try exact NEXT. i.
        econs. eapply TimeFacts.le_lt_lt; eauto.
  Qed.

  Lemma next_spec_Some_aux
        t tnext init l
        (NEXT: next t l init = Some tnext):
    (init = Some tnext /\
     forall ts (TS1: Time.lt t ts) (TS2: Time.lt ts tnext),
       ~ List.In ts l) \/
    (List.In tnext l /\
     Time.lt t tnext /\
     forall ts (TS1: Time.lt t ts) (TS2: Time.lt ts tnext),
       ~ List.In ts l).
  Proof.
    revert t tnext init NEXT. induction l; ss; i.
    { left. ss. }
    revert NEXT. condtac; ss; i.
    - exploit IHl; eauto. intros x. des.
      + subst. left. split; auto. ii. des.
        * subst. timetac.
        * eapply x0; eauto.
      + right. splits; eauto. ii. des.
        * subst. timetac.
        * eapply x1; eauto.
    - destruct init0.
      + revert NEXT. condtac; ss; i.
        * exploit IHl; eauto. intros x. des.
          { inv x. left. split; auto. ii. des.
            - subst. timetac.
            - eapply x0; eauto. }
          { right. splits; eauto. ii. des.
            - subst. exploit next_le; eauto. i.
              rewrite l1 in x3. timetac.
            - eapply x1; eauto. }
        * exploit IHl; eauto. intros x. des.
          { inv x. right. splits; eauto. ii. des.
            - subst. timetac.
            - eapply x0; eauto. }
          { right. splits; eauto. ii. des.
            - subst. exploit next_le; eauto. i. timetac.
            - eapply x1; eauto. }
      + right. exploit IHl; eauto. intros x. des.
        * inv x. esplits; eauto. ii. des.
          { subst. timetac. }
          { eapply x0; eauto. }
        * esplits; eauto. ii. des.
          { subst. exploit next_le; eauto. i. timetac. }
          { eapply x1; eauto. }
  Qed.

  Lemma next_spec_Some
        t tnext l
        (NEXT: next t l None = Some tnext):
    List.In tnext l /\
    Time.lt t tnext /\
    forall ts (TS1: Time.lt t ts) (TS2: Time.lt ts tnext),
      ~ List.In ts l.
  Proof.
    exploit next_spec_Some_aux; eauto. i.
    des; try congr; eauto.
  Qed.

  Lemma next_spec_None_aux
        t init l:
    next t l (Some init) <> None.
  Proof.
    revert t init. induction l; ss; i.
    repeat condtac; ss; eauto.
  Qed.

  Lemma next_spec_None
        t l
        (NEXT: next t l None = None):
    forall ts (IN: List.In ts l),
      Time.le ts t.
  Proof.
    revert t NEXT. induction l; ss; i. des.
    - subst. revert NEXT. condtac; ss; i.
      specialize (next_spec_None_aux t0 ts l). congr.
    - revert NEXT. condtac; ss; i.
      + exploit IHl; eauto.
      + specialize (next_spec_None_aux t0 a l). congr.
  Qed.

  Lemma next_exists
        cell f t m ts
        (INHABITED: get t cell = Some (f, m))
        (TS: Time.lt ts (max_ts cell)):
    exists from to msg,
      get to cell = Some (from, msg) /\
      Time.lt ts to /\
      forall ts' (TS1: Time.lt ts ts') (TS2: Time.lt ts' to),
        get ts' cell = None.
  Proof.
    destruct cell. unfold get in *. ss.
    destruct (next ts (List.map (fun x => fst x) (DOMap.elements raw0)) None) eqn:NEXT.
    - exploit next_spec_Some; eauto. i. des.
      exploit in_prod_inv; eauto. i. des. destruct b.
      exploit DOMap.elements_complete; eauto. i.
      esplits; try exact x4; eauto. i.
      destruct (DOMap.find ts' raw0) as [[]|] eqn:GET; ss.
      exploit DOMap.elements_correct; try exact GET. i.
      exploit in_prod; try exact x5. i.
      exploit x2; eauto. ss.
    - exploit (@max_ts_spec t f m (Cell.mk WF0)); ss. i. des.
      unfold get in *. ss.
      exploit DOMap.elements_correct; try exact GET. i.
      exploit in_prod; try exact x0. i.
      exploit next_spec_None; eauto. i. timetac.
  Qed.


  (* adjacent *)

  Inductive adjacent (from1 to1 from2 to2: Time.t) (cell: t): Prop :=
  | adjacent_intro
      m1 m2
      (GET1: get to1 cell = Some (from1, m1))
      (GET2: get to2 cell = Some (from2, m2))
      (TS: Time.lt to1 to2)
      (EMPTY: forall ts (TS1: Time.lt to1 ts) (TS2: Time.le ts from2),
          get ts cell = None)
  .

  Lemma adjacent_ts
        from1 to1 from2 to2 mem
        (ADJ: adjacent from1 to1 from2 to2 mem):
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
        to mem
        from1 from2 from3 to3 from4 to4
        (ADJ1: adjacent from1 to from3 to3 mem)
        (ADJ2: adjacent from2 to from4 to4 mem):
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
        from1 to1 msg cell
        (GET: get to1 cell = Some (from1, msg))
        (TO: Time.lt to1 (max_ts cell)):
    exists from2 to2,
      adjacent from1 to1 from2 to2 cell.
  Proof.
    exploit next_exists; eauto. i. des.
    esplits. econs; try exact x0; eauto. i.
    eapply x2; eauto.
    exploit get_ts; try exact x0. i. des.
    - subst. inv x1.
    - eapply TimeFacts.le_lt_lt; eauto.
  Qed.


  (* cap *)

  Inductive cap (cell1 cell2: t): Prop :=
  | cap_intro
      (SOUND: le cell1 cell2)
      (MIDDLE: forall from1 to1 from2 to2
                 (ADJ: adjacent from1 to1 from2 to2 cell1)
                 (TO: Time.lt to1 from2),
          get from2 cell2 = Some (to1, Message.reserve))
      (BACK: get (Time.incr (max_ts cell1)) cell2 =
             Some (max_ts cell1, Message.reserve))
      (COMPLETE: forall from to msg
                   (GET1: get to cell1 = None)
                   (GET2: get to cell2 = Some (from, msg)),
          (exists f m, get from cell1 = Some (f, m)))
  .

  Inductive cap_aux (dom: list Time.t) (cell1 cell2: t): Prop :=
  | cap_aux_intro
      (SOUND: le cell1 cell2)
      (MIDDLE: forall from1 to1 from2 to2
                 (IN: List.In to1 dom)
                 (ADJ: adjacent from1 to1 from2 to2 cell1)
                 (TO: Time.lt to1 from2),
          get from2 cell2 = Some (to1, Message.reserve))
      (BACK: forall (IN: List.In (max_ts cell1) dom),
          get (Time.incr (max_ts cell1)) cell2 =
          Some (max_ts cell1, Message.reserve))
      (COMPLETE: forall from to msg
                   (GET1: get to cell1 = None)
                   (GET2: get to cell2 = Some (from, msg)),
          List.In from dom /\
          (exists f m, get from cell1 = Some (f, m)))
  .

  Lemma cap_aux_exists
        dom cell1
        (INHABITED: get Time.bot cell1 = Some (Time.bot, Message.elt)):
    exists cell2, cap_aux dom cell1 cell2.
  Proof.
    revert cell1 INHABITED.
    induction dom; i.
    { exists cell1. econs; ss; i. congr. }
    exploit IHdom; eauto. intros x. des. clear IHdom.
    destruct (In_decidable time_decidable a dom).
    { exists cell2. inv x. econs; ii; eauto.
      - inv IN; eauto.
      - inv IN; eauto.
      - exploit COMPLETE; eauto. i. des.
        split; eauto. econs 2; eauto.
    }
    destruct (get a cell1) as [[from msg]|] eqn:GET1; cycle 1.
    { exists cell2. inv x. econs; ii; eauto.
      - inv IN; eauto. inv ADJ. congr.
      - inv IN; eauto.
        exploit max_ts_spec; eauto. i. des. congr.
      - exploit COMPLETE; eauto. i. des.
        split; eauto. econs 2; eauto.
    }
    exploit max_ts_spec; eauto. i. des.
    inv MAX.
    { exploit adjacent_exists; try exact GET1; ss. i. des.
      exploit adjacent_ts; eauto. i. inv x2; cycle 1.
      { inv H1.
        exists cell2. inv x. econs; ii; eauto.
        - inv IN; eauto.
          exploit adjacent_inj; [exact x1|exact ADJ|..]. i. des. subst.
          timetac.
        - inv IN; eauto. timetac.
        - exploit COMPLETE; eauto. i. des.
          split; eauto. econs 2; eauto.
      }
      exploit (@add_exists cell2 a from2 Message.reserve); ii.
      { inv x. inv x1. inv LHS. inv RHS. ss.
        clear MIDDLE BACK.
        destruct (get to0 cell1) as [[]|] eqn:GET4.
        - exploit SOUND; try exact GET4. intros x.
          rewrite x in *. inv GET2.
          destruct (Time.le_lt_dec to0 from2).
          { exploit (EMPTY to0); try congr.
            eapply TimeFacts.lt_le_lt; try exact FROM; ss. }
          exploit get_ts; try exact GET3. i. des.
          { subst. inv TS. }
          exploit get_ts; try exact GET4. i. des.
          { subst. inv l. }
          exploit get_disjoint; [exact GET3|exact GET4|..]. i. des.
          { subst. timetac. }
          destruct (Time.le_lt_dec to0 to2).
          + apply (x4 to0); econs; ss; try refl.
          + apply (x4 to2); econs; ss; try refl.
            * eapply TimeFacts.le_lt_lt; try exact x2.
              etrans; try exact TO. econs. ss.
            * econs. ss.
        - exploit COMPLETE; try exact GET2; eauto. intros x. des.
          cut (from1 = a); try by (i; subst; ss).
          clear COMPLETE.
          destruct (Time.le_lt_dec from1 a).
          + inv l; try by (inv H2; ss).
            exploit SOUND; try exact GET0. intros x2.
            exploit get_ts; try exact x2. i. des.
            { subst. inv H2. }
            exploit get_disjoint; [exact x2|exact GET2|..]. i. des.
            { subst. timetac. }
            exfalso.
            apply (x5 a); econs; ss; try refl.
            econs. eapply TimeFacts.lt_le_lt; try exact FROM. ss.
          + exploit (EMPTY from1); try congr.
            econs. eapply TimeFacts.lt_le_lt; try exact FROM0. ss.
      }
      { ss. }
      { econs. }
      des.
      exists cell0. inv x. econs; ii; ss.
      - exploit SOUND; eauto. i.
        eapply add_get1; eauto.
      - exploit add_get0; eauto. i. des.
        des; subst.
        + exploit adjacent_inj; [exact x1|exact ADJ|..]. i. des.
          subst. ss.
        + exploit MIDDLE; eauto. i.
          eapply add_get1; eauto.
      - des; subst; timetac.
        exploit BACK; eauto. i.
        eapply add_get1; eauto.
      - revert GET2. erewrite add_o; eauto. condtac; ss; i.
        + subst. inv GET2. splits; eauto.
        + exploit COMPLETE; eauto. i. des.
          esplits; eauto.
    }
    inv H0. clear from0 msg0 GET.
    exploit (@add_exists cell2 (max_ts cell1) (Time.incr (max_ts cell1)) Message.reserve); ii.
    { inv x. inv LHS. inv RHS. ss.
      destruct (get to2 cell1) as [[]|] eqn:GET3.
      { exploit SOUND; eauto. intros x.
        rewrite x in *. inv GET2.
        exploit max_ts_spec; try exact GET3. i. des.
        exploit TimeFacts.le_lt_lt; try exact FROM; try exact MAX. i.
        timetac. }
      exploit COMPLETE; eauto. intros x. des.
      cut (from2 = max_ts cell1); try by (i; subst; ss).
      destruct (Time.le_lt_dec from2 (max_ts cell1)).
      - inv l; try by (inv H0; ss).
        exploit SOUND; try exact GET1. intros x2.
        exploit get_ts; try exact x2. i. des.
        { subst. rewrite x3 in *. inv H0. }
        exploit get_ts; try exact GET2. i. des.
        { subst. timetac. }
        exploit get_disjoint; [exact x2|exact GET2|..]. i. des.
        { subst. timetac. }
        exfalso.
        apply (x6 (max_ts cell1)); econs; ss; try refl.
        econs. eapply TimeFacts.lt_le_lt; try exact FROM. ss.
      - exploit max_ts_spec; try exact x1. i. des.
        timetac.
    }
    { apply Time.incr_spec. }
    { econs. }
    des.
    exists cell0. inv x. econs; ii; ss; eauto.
    - exploit SOUND; eauto. i.
      eapply add_get1; eauto.
    - exploit add_get0; eauto. i. des.
      + inv ADJ. exploit max_ts_spec; try exact GET3. i. des. timetac.
      + eapply add_get1; eauto.
    - eapply add_get0; eauto.
    - revert GET2. erewrite add_o; eauto. condtac; ss; i.
      + subst. inv GET2. esplits; eauto.
      + exploit COMPLETE; eauto. i. des.
        esplits; eauto.
  Qed.

  Lemma cap_exists
        cell1
        (INHABITED: get Time.bot cell1 = Some (Time.bot, Message.elt)):
    exists cell2, cap cell1 cell2.
  Proof.
    destruct (@finite cell1).
    exploit (@cap_aux_exists x); eauto. i. des.
    exists cell2. inv x1. econs; i; ss; eauto.
    - eapply MIDDLE; eauto. inv ADJ. eauto.
    - eapply BACK; eauto.
      exploit max_ts_spec; eauto. i. des. eauto.
    - exploit COMPLETE; eauto. i. des.
      esplits; eauto.
  Qed.
End Cell.
