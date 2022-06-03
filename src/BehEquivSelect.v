From sflib Require Import sflib.
From ITree Require Export ITree.

Export ITreeNotations.

Require Import Coq.Classes.RelationClasses.

(* Require Import Lia. *)

From Fairness Require Import Axioms.
From Fairness Require Import FairBeh.
From Fairness Require Import pind3.
From Fairness Require Import SelectBeh.

From Paco Require Import paco.

Set Implicit Arguments.


Section EQUIV1.

  Context {Ident: ID}.
  Hypothesis ID_DEC: forall (i0 i1: Ident.(id)), {i0 = i1} + {i0 <> i1}.

  Variable wft: WF.
  Hypothesis WFTR: Transitive wft.(lt).

  Theorem Ord_implies_Ind
          R
          (tr: @RawTr.t Ident R)
          (ORD: RawTr.is_fair_ord wft tr)
    :
    RawTr.is_fair_ind tr.
  Proof.
    ii. unfold RawTr.is_fair_ord in ORD. des.
    revert_until R. pcofix CIH1. i.
    eapply paco3_fold.
    remember (m i) as idx. move idx before CIH1. revert_until idx.
    induction (wft.(wf) idx). rename H into ACC, H0 into IH, x into idx. i.
    eapply pind3_fold.
    revert_until IH. pcofix CIH2. i.
    eapply paco3_fold. eapply paco3_unfold.
    { eapply RawTr._fair_ind_mon. }
    punfold ORD. inv ORD.
    { pfold. econs 1. }
    { pfold. econs 2. }
    { pfold. econs 3. }
    { pclearbot. pfold. econs 4. right. eapply CIH2; eauto. }
    { pclearbot. destruct (fmap i) eqn:FM.
      { pfold. econs 7. auto. split; ss. eapply IH. 2: eauto. all: eauto.
        unfold fair_update in FAIR. specialize (FAIR i). rewrite FM in FAIR. auto.
      }
      { dup FAIR. unfold fair_update in FAIR. specialize (FAIR i). rewrite FM in FAIR. destruct FAIR as [EQ | LT].
        - pfold. econs 6. auto. right. eapply CIH2; eauto.
        - pfold. econs 6. auto. right. eapply CIH2.
          instantiate (1:= fun id => if (ID_DEC id i) then (m i) else (m0 id)).
          + ginit. guclo RawTr.fair_ord_imap_le_ctx_spec. econs. gfinal; eauto.
            unfold soft_update. i. destruct (ID_DEC i0 i) as [EQ | NEQ].
            * clarify. right. auto.
            * left. auto.
          + ss. des_ifs.
      }
      { pfold. econs 8. auto. right. eapply CIH1; eauto. }
    }
    { pclearbot. pfold. econs 5. right. eapply CIH2; eauto. }
  Qed.

End EQUIV1.



Section EQUIV2.

  Context {Ident: ID}.
  Hypothesis ID_DEC: forall (i0 i1: Ident.(id)), {i0 = i1} + {i0 <> i1}.

  Variable wft: WF.
  Hypothesis WFTR: Transitive wft.(lt).

  (* the other direction *)
  Lemma fair_ind_fair_red
        R
        i fm (tr: @RawTr.t Ident R)
        (IND: RawTr.fair_ind i (RawTr.cons (inl (silentE_fair fm)) tr))
    :
    RawTr.fair_ind i tr.
  Proof.
    punfold IND.
    2:{ clear. ii. eapply pind3_mon_gen; eauto. ii. ss. eapply paco3_mon_gen. eapply PR. 2: ss.
        i. eapply RawTr.___fair_ind_mon; eauto.
    } (*make lemma*)
    eapply pind3_unfold in IND.
    2:{ clear. ii. eapply paco3_mon_gen. eapply IN. 2: ss.
        i. eapply RawTr.__fair_ind_mon; eauto.
    } (*make lemma*)
    punfold IND.
    2:{ eapply RawTr._fair_ind_mon. }
    inv IND.
    { pclearbot. eapply paco3_mon. eauto. ss. }
    2:{ pclearbot. eapply paco3_mon. eauto. ss. }
    unfold upind3 in TL. des.

    eapply pind3_unfold in TL.
    2:{ clear. ii. eapply paco3_mon_gen. eapply IN. 2: ss.
        i. eapply RawTr.__fair_ind_mon; eauto.
    } (*make lemma*)
    punfold TL.
    { eapply RawTr._fair_ind_mon. }
  Qed.



  (* Variant _nofail_tr (i: id) *)
  (*         (nofail_tr: forall (R: Type), (@RawTr.t _ R) -> Prop) *)
  (*         (R: Type) *)
  (*   : *)
  (*   (@RawTr.t _ R) -> Prop := *)
  (*   | nofail_tr_done *)
  (*       retv *)
  (*     : *)
  (*     _nofail_tr i nofail_tr (RawTr.done retv) *)
  (*   | nofail_tr_ub *)
  (*     : *)
  (*     _nofail_tr i nofail_tr RawTr.ub *)
  (*   | nofail_tr_nb *)
  (*     : *)
  (*     _nofail_tr i nofail_tr RawTr.nb *)
  (*   | nofail_tr_obs *)
  (*       (obs: obsE) tl *)
  (*       (TL: nofail_tr R tl) *)
  (*     : *)
  (*     _nofail_tr i nofail_tr (RawTr.cons (inr obs) tl) *)
  (*   | nofail_tr_fair_emp *)
  (*       fmap tl *)
  (*       (EMP: Flag.emp = (fmap i)) *)
  (*       (TL: nofail_tr R tl) *)
  (*     : *)
  (*     _nofail_tr i nofail_tr (RawTr.cons (inl (silentE_fair fmap)) tl) *)
  (*   | nofail_tr_fair_success *)
  (*       fmap tl *)
  (*       (SUCCESS: Flag.success = (fmap i)) *)
  (*     : *)
  (*     _nofail_tr i nofail_tr (RawTr.cons (inl (silentE_fair fmap)) tl) *)
  (*   | nofail_tr_tau *)
  (*       tl *)
  (*       (TL: nofail_tr R tl) *)
  (*     : *)
  (*     _nofail_tr i nofail_tr (RawTr.cons (inl silentE_tau) tl) *)
  (* . *)

  (* Definition nofail_tr i: forall (R: Type), (@RawTr.t _ R) -> Prop := paco2 (_nofail_tr i) bot2. *)

  (* Lemma nofail_tr_mon i: monotone2 (_nofail_tr i). *)
  (* Proof. *)
  (*   ii. inv IN; [econs 1 | econs 2 | econs 3 | econs 4 | econs 5 | econs 6 | econs 7]; eauto. *)
  (* Qed. *)

  (* Local Hint Constructors _nofail_tr: core. *)
  (* Local Hint Unfold nofail_tr: core. *)
  (* Local Hint Resolve nofail_tr_mon: paco. *)


  (* Variant _ord_tr (i: id) *)
  (*         (ord_tr: forall (R: Type) (o: wft.(T)), (@RawTr.t _ R) -> Prop) *)
  (*         R o *)
  (*   : *)
  (*   (@RawTr.t _ R) -> Prop := *)
  (*   | ord_tr_obs *)
  (*       (obs: obsE) tl *)
  (*       (TL: ord_tr R o tl) *)
  (*     : *)
  (*     _ord_tr i ord_tr o (RawTr.cons (inr obs) tl) *)
  (*   | ord_Tr_tau *)
  (*       tl *)
  (*       (TL: ord_tr R o tl) *)
  (*     : *)
  (*     _ord_tr i ord_tr o (RawTr.cons (inl silentE_tau) tl) *)
  (*   | ord_tr_fair_emp *)
  (*       fmap tl *)
  (*       (EMP: Flag.emp = (fmap i)) *)
  (*       (TL: ord_tr R o tl) *)
  (*     : *)
  (*     _ord_tr i ord_tr o (RawTr.cons (inl (silentE_fair fmap)) tl) *)
  (*   | ord_tr_fair_fail *)
  (*       fmap tl o0 *)
  (*       (FAIL: Flag.fail = (fmap i)) *)
  (*       (LT: wft.(lt) o0 o) *)
  (*       (TL: ord_tr R o0 tl) *)
  (*     : *)
  (*     _ord_tr i ord_tr o (RawTr.cons (inl (silentE_fair fmap)) tl) *)
  (*   | ord_tr_nofail *)
  (*       tr *)
  (*       (NOFAIL: nofail_tr i tr) *)
  (*     : *)
  (*     _ord_tr i ord_tr o tr *)
  (* . *)

  (* Definition ord_tr i: forall (R: Type) o, (@RawTr.t _ R) -> Prop := paco3 (_ord_tr i) bot3. *)

  (* Lemma ord_tr_mon i: monotone3 (_ord_tr i). *)
  (* Proof. *)
  (*   ii. inv IN; [econs 1 | econs 2 | econs 3 | econs 4 | econs 5]; eauto. *)
  (* Qed. *)

  (* Local Hint Constructors _ord_tr: core. *)
  (* Local Hint Unfold ord_tr: core. *)
  (* Local Hint Resolve ord_tr_mon: paco. *)


  (* Variant _next_fail (i: id) *)
  (*         (next_fail: forall R, (@RawTr.t _ R) -> (@RawTr.t _ R) -> Prop) *)
  (*         R *)
  (*   : *)
  (*   (@RawTr.t _ R) -> (@RawTr.t _ R) -> Prop := *)
  (*   | next_fail_obs *)
  (*       obs tl next *)
  (*       (TL: next_fail R tl next) *)
  (*     : *)
  (*     _next_fail i next_fail (RawTr.cons (inr obs) tl) next *)
  (*   | next_fail_tau *)
  (*       tl next *)
  (*       (TL: next_fail R tl next) *)
  (*     : *)
  (*     _next_fail i next_fail (RawTr.cons (inl silentE_tau) tl) next *)
  (*   | next_fail_emp *)
  (*       fmap tl next *)
  (*       (EMP: Flag.emp = (fmap i)) *)
  (*       (TL: next_fail R tl next) *)
  (*     : *)
  (*     _next_fail i next_fail (RawTr.cons (inl (silentE_fair fmap)) tl) next *)
  (*   | next_fail_fail *)
  (*       fmap tl1 tl2 *)
  (*       (FAIL: Flag.emp = (fmap i)) *)
  (*     : *)
  (*     _next_fail i next_fail *)
  (*                (RawTr.cons (inl (silentE_fair fmap)) tl1) *)
  (*                (RawTr.cons (inl (silentE_fair fmap)) tl2) *)
  (* . *)

  (* Definition next_fail i: forall (R: Type), (@RawTr.t _ R) -> (@RawTr.t _ R) -> Prop := paco3 (_next_fail i) bot3. *)

  (* Lemma next_fail_mon i: monotone3 (_next_fail i). *)
  (* Proof. *)
  (*   ii. inv IN; [econs 1 | econs 2 | econs 3 | econs 4]; eauto. *)
  (* Qed. *)

  (* Local Hint Constructors _next_fail: core. *)
  (* Local Hint Unfold next_fail: core. *)
  (* Local Hint Resolve next_fail_mon: paco. *)



  Variable wft0: wft.(T).

  (* coinductive-inductive *)
  Variant __tr_ord (i: id)
          (tr_ord: forall (R: Type), (@RawTr.t _ R) -> wft.(T) -> Prop)
          (_tr_ord: forall (R: Type), (@RawTr.t _ R) -> wft.(T) -> Prop)
          (R: Type)
    :
    (@RawTr.t _ R) -> wft.(T) -> Prop :=
    (* base cases *)
    | tr_ord_done
        retv o
      :
      __tr_ord i tr_ord _tr_ord (RawTr.done retv) o
    | tr_ord_ub
        o
      :
      __tr_ord i tr_ord _tr_ord RawTr.ub o
    | tr_ord_nb
        o
      :
      __tr_ord i tr_ord _tr_ord RawTr.nb o
    | tr_ord_fair_success
        fmap tl o
        (SUCCESS: Flag.success = (fmap i))
      :
      __tr_ord i tr_ord _tr_ord (RawTr.cons (inl (silentE_fair fmap)) tl) o

    (* inner coinductive cases: no fair events for i *)
    | tr_ord_obs
        (obs: obsE) tl o
        (TL: _tr_ord R tl o)
      :
      __tr_ord i tr_ord _tr_ord (RawTr.cons (inr obs) tl) o
    | tr_ord_tau
        tl o
        (TL: _tr_ord R tl o)
      :
      __tr_ord i tr_ord _tr_ord (RawTr.cons (inl silentE_tau) tl) o
    | tr_ord_fair_emp
        fmap tl o
        (EMP: Flag.emp = (fmap i))
        (TL: _tr_ord R tl o)
      :
      __tr_ord i tr_ord _tr_ord (RawTr.cons (inl (silentE_fair fmap)) tl) o

    (* outer inductive cases: i fails inductively *)
    | tr_ord_fair_fail
        fmap tl o o0
        (FAIL: Flag.fail = (fmap i))
        (LT: wft.(lt) o0 o)
        (TL: tr_ord R tl o0)
      :
      __tr_ord i tr_ord _tr_ord (RawTr.cons (inl (silentE_fair fmap)) tl) o
  .

  Lemma __tr_ord_mon i: forall r r' (LE: r <3= r'), (__tr_ord i r) <4= (__tr_ord i r').
  Proof.
    ii. inv PR.
    - econs 1; eauto.
    - econs 2; eauto.
    - econs 3; eauto.
    - econs 4; eauto.
    - econs 5; eauto.
    - econs 6; eauto.
    - econs 7; eauto.
    - econs 8; eauto.
  Qed.

  Lemma _tr_ord_mon i: forall r, monotone3 (__tr_ord i r).
  Proof.
    ii. inv IN.
    - econs 1; eauto.
    - econs 2; eauto.
    - econs 3; eauto.
    - econs 4; eauto.
    - econs 5; eauto.
    - econs 6; eauto.
    - econs 7; eauto.
    - econs 8; eauto.
  Qed.

  Lemma tr_ord_mon i: forall p, monotone3 (fun q => (__tr_ord i q) p).
  Proof.
    ii. eapply __tr_ord_mon; eauto.
  Qed.

  Definition tr_ord (i: id): forall (R: Type), (@RawTr.t _ R) -> wft.(T) -> Prop :=
    pind3 (fun q => paco3 (__tr_ord i q) bot3) top3.


  Lemma inhabited_tr_ord: inhabited (T wft).
  Proof. econs. exact wft0. Qed.

  Definition tr2ord_i {R} i (raw: (@RawTr.t _ R)): wft.(T) :=
    epsilon _ (inhabited_tr_ord) (tr_ord i raw).

  Definition tr2ord {R} (raw: (@RawTr.t _ R)): imap wft :=
    fun i => tr2ord_i i raw.

  Theorem tr2ord_i_spec
          R i (tr: @RawTr.t _ R)
          (IND: RawTr.is_fair_ind tr)
    :
    exists o, tr_ord i tr o.
  Proof.
    specialize (IND i). punfold IND.
    2:{ clear. ii. eapply pind3_mon_gen; eauto. ii. ss. eapply paco3_mon_gen. eapply PR. 2: ss.
        i. eapply RawTr.___fair_ind_mon; eauto.
    } (*make lemma*)
    revert R i tr IND.
    eapply (@pind3_acc _ _ _ _ (fun (R: Type) => (fun (i: id) => fun (tr: @RawTr.t Ident R) => exists o, tr_ord i tr o))).
    (* eapply (@pind3_acc _ _ _ _ (fun (R: Type) => (fun (i: id) => fun (tr: @RawTr.t Ident R) => tr_ord i tr (@tr2ord_i R i tr)))). *)
    i. rename x0 into R, x1 into i, x2 into tr.
    eapply pind3_unfold in PR.
    2:{ clear. ii. eapply paco3_mon_gen. eapply IN. 2: ss.
        i. eapply RawTr.__fair_ind_mon; eauto.
    } (*make lemma*)


    unfold tr_ord.

    assert (A:
  exists o : T wft,
    pind3
      (fun q : rel3 Type (@RawTr.t Ident) (fun (x0 : Type) (_ : RawTr.t) => T wft) =>
         paco3 (fun p =>
                   (fun R0 => (fun tr0 => (fun o0 =>
                     (exists o, (@__tr_ord i q p R0 tr0 o) /\ (wft.(lt) o o0)))))) bot3)
      top3 R tr o).
    2:{ des. exists o.
        eapply pind3_mon_gen. eauto. 2: ss.
        i. ss. eapply paco3_mon_gen. eauto. 2: ss.
        i. ss. des.
        assert (MAYBE: forall R r1 r2 (t: @RawTr.t _ R) o1 o2 (LT: lt wft o1 o2),
                   __tr_ord i r1 r2 t o1 -> __tr_ord i r1 r2 t o2).
        { admit. }
        eapply MAYBE. eauto. eauto.
    }

    assert (A:
  exists o : T wft,
    pind3
      (fun q : rel3 Type (@RawTr.t Ident) (fun (x0 : Type) (_ : RawTr.t) => T wft) =>
       upaco3
         (fun (p : rel3 Type (@RawTr.t Ident) (fun (x0 : Type) (_ : RawTr.t) => T wft))
            (R0 : Type) (tr0 : RawTr.t) (o0 : T wft) =>
            exists o1 : T wft, __tr_ord i q p tr0 o1 /\ lt wft o1 o0) bot3) top3 R tr o).
    2:{ des. exists o. eapply pind3_mon_gen. eauto. 2: ss. i. ss. pclearbot. auto. }
    assert (A:
         (fun (p : rel3 Type (@RawTr.t Ident) (fun (x0 : Type) (_ : RawTr.t) => T wft))
            (R0 : Type) (tr0 : RawTr.t) (o0 : T wft) =>
            exists o1 : T wft, __tr_ord i top3 p tr0 o1 /\ lt wft o1 o0)
           (upaco3
         (fun (p : rel3 Type (@RawTr.t Ident) (fun (x0 : Type) (_ : RawTr.t) => T wft))
            (R0 : Type) (tr0 : RawTr.t) (o0 : T wft) =>
            exists o1 : T wft, __tr_ord i top3 p tr0 o1 /\ lt wft o1 o0) bot3) R tr (tr2ord_i i tr)).
    2:{ ss. des. eexists. eapply pind3_fold. left. eapply paco3_fold. exists o1.
        
             

        eapply pind3_unfold in PR1. punfold PR1.
        2:{ ii. eapply _tr_ord_mon; eauto. }
        2:{ ii. eapply paco3_mon_gen. eapply IN. 2: ss. i. eapply __tr_ord_mon; eauto. }
        eapply __tr_ord_mon.
        2:{ eapply _tr_ord_mon.
            {
              assert (MAYBE: forall R r1 r2 (t: @RawTr.t _ R) o1 o2 (LT: lt wft o1 o2),
                         __tr_ord i r1 r2 t o1 -> __tr_ord i r1 r2 t o2).
              { admit. }
              eapply MAYBE. eauto. eauto.
            }
            i. destruct PR3. 2:{ auto. }


    assert (A:
  exists o : T wft,
    pind3
      (fun q : rel3 Type (@RawTr.t Ident) (fun (x0 : Type) (_ : RawTr.t) => T wft) =>
         paco3 (fun p =>
                   (fun R0 => (fun tr0 => (fun o0 =>
                     (exists o, (pind3 (fun r => paco3 (__tr_ord i r) p) q R0 tr0 o) /\ (wft.(lt) o o0)))))) bot3)
      top3 R tr o).
    2:{ des. exists o.
        eapply pind3_mon_gen. eauto. 2: ss.
        i. ss. eapply paco3_mon_gen. eauto. 2: ss.
        i. ss. des. eapply pind3_unfold in PR1. punfold PR1.
        2:{ ii. eapply _tr_ord_mon; eauto. }
        2:{ ii. eapply paco3_mon_gen. eapply IN. 2: ss. i. eapply __tr_ord_mon; eauto. }
        eapply __tr_ord_mon.
        2:{ eapply _tr_ord_mon.
            { assert (MAYBE: forall R r1 r2 (t: @RawTr.t _ R) o1 o2 (LT: lt wft o1 o2),
                         __tr_ord i r1 r2 t o1 -> __tr_ord i r1 r2 t o2).
              { admit. }
              eapply MAYBE. eauto. eauto.
            }
            i. destruct PR3. 2:{ auto. }

        eapply tr_ord_mon.

        eapply pind3_unfold in A.




    
    eapply pind3_mon_gen. 3: ss. instantiate (1:=top3).
    instantiate (1:= fun r => (upaco3 (__tr_ord i r)) bot3).
    2:{ i. ss. pclearbot. auto. }
    eapply paco3_unfold.

        instantiate (1:= fun r => (upaco3 (__tr_ord i r))) in PR0.

        eapply paco3_fold. eauto.
    instantiate (1:= (fun q : rel3 Type (@RawTr.t Ident) (fun (x0 : Type) (_ : RawTr.t) => T wft) =>
     upaco3 (__tr_ord i q) bot3) top3 R tr (tr2ord_i i tr)).
    2:{ instantiate (1:= upaco3 (__tr_ord i x0)).


    
    eapply pind3_fold. revert_until i. pcofix CIH. i.
    punfold PR.
    2:{ eapply RawTr._fair_ind_mon. }
    pfold. inv PR.
    { econs 1. }
    { econs 2. }
    { econs 3. }
    { pclearbot. eapply pind3_fold in TL.

      econs. right.
      match goal with
      | |- r R ?_tl ?rhs => assert (RED: rhs = tr2ord_i i _tl)
      end.
      { unfold tr2ord_i, epsilon. unfold Epsilon.epsilon. unfold proj1_sig. des_ifs.
        clear Heq Heq0. hexploit t0; clear t0.
        { exists (tr2ord_i i tl). clear t x x0. punfold TL.
          2:{ eapply RawTr._fair_ind_mon. }
          inv TL.
          { eapply pind3_fold. pfold. econs. }
          { eapply pind3_fold. pfold. econs. }
          { eapply pind3_fold. pfold. econs. }
          { eapply pind3_fold. pfold. econs. left. }
          { 


          
        des. hexploit t0; clear t0; eauto; i. hexploit t.


      hexploit tr2ord_i_red_obs. i; des.
      { pfold. econs. right. rewrite H; clear H. eapply CIH. eauto. }
      (* ??? *)
    

  Lemma tr2ord_i_red_obs
        R i obs (tr: RawTr.t (R:=R))
    :
    (tr2ord_i i (RawTr.cons (inr obs) tr) = tr2ord_i i tr) \/ (~ exists o, tr_ord i tr o).
  Proof.
    destruct (classic (exists o, tr_ord i tr o)) as [EX | NOT]; auto.
    left. unfold tr2ord_i, epsilon. unfold Epsilon.epsilon. unfold proj1_sig. des_ifs. clear Heq Heq0.
    des. hexploit t0; clear t0; eauto; i. hexploit t.
    { exists o. eapply pind3_fold. pfold. econs. left. unfold tr_ord in EX.
      eapply pind3_unfold in EX. eauto.
      ii. eapply paco3_mon_gen. eauto. i. eapply __tr_ord_mon; eauto. ss.
    }
    i. eapply pind3_unfold in H0.
    2:{ ii. eapply paco3_mon_gen. eauto. i. eapply __tr_ord_mon; eauto. ss. }
    punfold H0.
    2:{ eapply _tr_ord_mon. }
    inv H0. pclearbot.
    assert (A: tr_ord i tr x).
    { eapply pind3_fold. eauto. }
    clear EX TL.
    admit.
  Admitted.


  Lemma tr_ord_not_exists
        i R (tr: @RawTr.t Ident R)
        (IND: RawTr.is_fair_ind tr)
        (NOT: ~ exists o, tr_ord i tr o)
    :
    False.
  Proof.
    eapply Classical_Pred_Type.not_ex_all_not in NOT. instantiate (1:= tr2ord_i i tr) in NOT.
    remember (tr2ord_i i tr) as idx. move idx before R. revert_until idx. induction (wft.(wf) idx). i.
    rename H0 into IH. clear H. specialize (IND i). clarify. eapply NOT; clear NOT.

    punfold IND.
    2:{ clear. ii. eapply pind3_mon_gen; eauto. ii. ss. eapply paco3_mon_gen. eapply PR. 2: ss.
        i. eapply RawTr.___fair_ind_mon; eauto.
    } (*make lemma*)
    (* revert R i tr IH IND. *)
    (* eapply (@pind3_acc _ _ _ _ (fun (R: Type) => (fun (i: id) => fun (tr: @RawTr.t Ident R) => exists o, tr_ord i tr o))). *)
    (* eapply (@pind3_acc _ _ _ _ (fun (R: Type) => (fun (i: id) => fun (tr: @RawTr.t Ident R) => tr_ord i tr (@tr2ord_i R i tr)))). *)
    eapply pind3_unfold in IND.
    2:{ clear. ii. eapply paco3_mon_gen. eapply IN. 2: ss.
        i. eapply RawTr.__fair_ind_mon; eauto.
    } (*make lemma*)
    eapply pind3_fold. revert_until i. pcofix CIH. i.
    punfold IND.
    2:{ eapply RawTr._fair_ind_mon. }
    inv IND.
    { pfold. econs 1. }
    { pfold. econs 2. }
    { pfold. econs 3. }
    { pclearbot. hexploit tr2ord_i_red_obs. i; des.
      { pfold. econs. right. rewrite H; clear H. eapply CIH; eauto. i. eapply IH. }

    



  Lemma tr_ord_exists
        i R (tr: @RawTr.t Ident R)
        (IND: RawTr.is_fair_ind tr)
    :
    exists o, tr_ord i tr o.
  Proof.
    exists (tr2ord_i i tr).
    specialize (IND i).
    remember (tr2ord_i i tr) as idx. move idx before wft0. revert_until idx.
    induction (wft.(wf) idx). i.
    clarify. rename H0 into IH. clear H.

    depgen IND. induction (well_founded (tr2ord_i i tr)).


    punfold IND.
    2:{ clear. ii. eapply pind3_mon_gen; eauto. ii. ss. eapply paco3_mon_gen. eapply PR. 2: ss.
        i. eapply RawTr.___fair_ind_mon; eauto.
    } (*make lemma*)
    revert R i tr IND.
    (* eapply (@pind3_acc _ _ _ _ (fun (R: Type) => (fun (i: id) => fun (tr: @RawTr.t Ident R) => exists o, tr_ord i tr o))). *)
    eapply (@pind3_acc _ _ _ _ (fun (R: Type) => (fun (i: id) => fun (tr: @RawTr.t Ident R) => tr_ord i tr (@tr2ord_i R i tr)))).
    i. rename x0 into R, x1 into i, x2 into tr.
    eapply pind3_unfold in PR.
    2:{ clear. ii. eapply paco3_mon_gen. eapply IN. 2: ss.
        i. eapply RawTr.__fair_ind_mon; eauto.
    } (*make lemma*)
    eapply pind3_fold. revert_until i. pcofix CIH. i.
    punfold PR.
    2:{ eapply RawTr._fair_ind_mon. }
    inv PR.
    { pfold. econs 1. }
    { pfold. econs 2. }
    { pfold. econs 3. }
    { pclearbot. hexploit tr2ord_i_red_obs. i; des.
      { pfold. econs. right. rewrite H; clear H. eapply CIH. eauto. }
      (* ??? *)
      
      




      cut (paco3 (__tr_ord i (upind3 (fun q => paco3 (__tr_ord i q) bot3) top3)) bot3 R tl i).

      (lf (upind3 lf r) x0 x1 x2 : Pr

  Lemma tr2ord_red_obs
        R (tr: @RawTr.t Ident R)
        obs
    :
    tr2ord (RawTr.cons (inr obs) tr) = tr2ord tr.
  Proof.
    extensionalities. rename H into i.
    unfold tr2ord, tr2ord_i, epsilon. unfold Epsilon.epsilon. unfold proj1_sig. des_ifs.
    clear Heq Heq0.
    hexploit (observe_state_exists). intros OSP. eapply o in OSP; clear o.
    unfold observe_state_prop in OSP. hexploit OSP; clear OSP; eauto.
    i. inv H; ss; eauto. hexploit CONT; eauto; i. des. esplits; eauto.
  Qed.
    
    
        


  Theorem Ind_implies_Ord
          R (tr: @RawTr.t Ident R)
          (IND: RawTr.is_fair_ind tr)
    :
    RawTr.is_fair_ord wft tr.
  Proof.
    unfold RawTr.is_fair_ord. unfold RawTr.is_fair_ind in IND. exists (tr2ord tr).
    revert_until R. pcofix CIH. i.
    destruct tr eqn:TR.
    { pfold. econs. }
    { pfold. econs. }
    { pfold. econs. }
    { destruct hd as [silent | obs].
      2:{ pfold. econs. right.
          assert (A: tr2ord (RawTr.cons (inr obs) t) = tr2ord t).
          { admit. }
          rewrite A; clear A.
          eapply CIH. i.
          specialize (IND i). punfold IND.
          2:{ clear. ii. eapply pind3_mon_gen; eauto. ii. ss. eapply paco3_mon_gen. eapply PR. 2: ss.
              i. eapply RawTr.___fair_ind_mon; eauto.
          } (*make lemma*)
          eapply pind3_unfold in IND.
          2:{ clear. ii. eapply paco3_mon_gen. eapply IN. 2: ss.
              i. eapply RawTr.__fair_ind_mon; eauto.
          } (*make lemma*)
          punfold IND.
          2:{ eapply RawTr._fair_ind_mon. }
          inv IND. pclearbot. eapply paco3_mon. eauto. ss.
      }
      destruct silent as [ | fm].
      { pfold. econs. right.
        assert (A: tr2ord (RawTr.cons (inl silentE_tau) t) = tr2ord t).
        { admit. }
        rewrite A; clear A.
        eapply CIH. i.
        specialize (IND i). punfold IND.
        2:{ clear. ii. eapply pind3_mon_gen; eauto. ii. ss. eapply paco3_mon_gen. eapply PR. 2: ss.
            i. eapply RawTr.___fair_ind_mon; eauto.
        } (*make lemma*)
        eapply pind3_unfold in IND.
        2:{ clear. ii. eapply paco3_mon_gen. eapply IN. 2: ss.
            i. eapply RawTr.__fair_ind_mon; eauto.
        } (*make lemma*)
        punfold IND.
        2:{ eapply RawTr._fair_ind_mon. }
        inv IND. pclearbot. eapply paco3_mon. eauto. ss.
      }
      { pfold. econs.
        2:{ right. eapply CIH. i.
            specialize (IND i). eapply fair_ind_fair_red; eauto.
        }
  fair_update (tr2ord (RawTr.cons (inl (silentE_fair fm)) t)) (tr2ord t) fm
        admit.
      }
    } 

















  Variant _consume_tr (i: id)
          (consume_tr: forall (R: Type), (@RawTr.t _ R) -> (@RawTr.t _ R) -> Prop)
          (R: Type)
    :
    (@RawTr.t _ R) -> (@RawTr.t _ R) -> Prop :=
    | consume_tr_done
        retv
      :
      _consume_tr i consume_tr (RawTr.done retv) (RawTr.done retv)
    | consume_tr_ub
      :
      _consume_tr i consume_tr RawTr.ub RawTr.ub
    | consume_tr_nb
      :
      _consume_tr i consume_tr RawTr.nb RawTr.nb

    | consume_tr_obs
        (obs: obsE) tl res
        (TL: consume_tr R tl res)
      :
      _consume_tr i consume_tr (RawTr.cons (inr obs) tl) res
    | consume_tr_tau
        tl res
        (TL: consume_tr R tl res)
      :
      _consume_tr i consume_tr (RawTr.cons (inl silentE_tau) tl) res
    | consume_tr_fair_emp
        fmap tl res
        (EMP: Flag.emp = (fmap i))
        (TL: consume_tr R tl res)
      :
      _consume_tr i consume_tr (RawTr.cons (inl (silentE_fair fmap)) tl) res

    | consume_tr_fair
        fmap1 tl1 fmap2 tl2
        (FAIR: (<<FAIL: (Flag.fail = (fmap1 i)) /\ (Flag.fail = (fmap2 i))>>) \/
                 (<<SUCCESS: (Flag.success = (fmap1 i)) /\ (Flag.success = (fmap2 i))>>))
      :
      _consume_tr i consume_tr
                  (RawTr.cons (inl (silentE_fair fmap1)) tl1)
                  (RawTr.cons (inl (silentE_fair fmap2)) tl2)

    (* | consume_tr_fair_success *)
    (*     fmap1 tl1 fmap2 tl2 *)
    (*     (SUCCESS1: Flag.success = (fmap1 i)) *)
    (*     (SUCCESS2: Flag.success = (fmap2 i)) *)
    (*   : *)
    (*   _consume_tr i consume_tr *)
    (*               (RawTr.cons (inl (silentE_fair fmap1)) tl1) *)
    (*               (RawTr.cons (inl (silentE_fair fmap2)) tl2) *)
  .

  Definition consume_tr i: forall (R: Type), (@RawTr.t _ R) -> (@RawTr.t _ R) -> Prop := paco3 (_consume_tr i) bot3.

  Lemma consume_tr_mon i: monotone3 (_consume_tr i).
  Proof.
    ii. inv IN.
    - econs 1; eauto.
    - econs 2; eauto.
    - econs 3; eauto.
    - econs 4; eauto.
    - econs 5; eauto.
    - econs 6; eauto.
    - econs 7; eauto.
  Qed.

  Local Hint Resolve consume_tr_mon: paco.

  Inductive tr_ord (i: id)
            (R: Type)
    :
    wft.(T) -> (@RawTr.t _ R) -> Prop :=
  | tr_ord_done
      o retv
    :
    tr_ord i o (RawTr.done retv)
  | tr_ord_ub
      o
    :
    tr_ord i o RawTr.ub
  | tr_ord_nb
      o
    :
    tr_ord i o RawTr.nb

  | tr_ord_fair_success
      o fmap tl
      (SUCCESS: Flag.success = (fmap i))
    :
    tr_ord i o (RawTr.cons (inl (silentE_fair fmap)) tl)

  | tr_ord_obs
      o (obs: obsE) tl res
      (TL: tr_ord i o res)
      (RES: consume_tr i tl res)
    :
    tr_ord i o (RawTr.cons (inr obs) tl)
  | tr_ord_tau
      o tl res
      (TL: tr_ord i o res)
      (RES: consume_tr i tl res)
    :
    tr_ord i o (RawTr.cons (inl silentE_tau) tl)
  | tr_ord_fair_emp
      o fmap tl res
      (EMP: Flag.emp = (fmap i))
      (TL: tr_ord i o res)
      (RES: consume_tr i tl res)
    :
    tr_ord i o (RawTr.cons (inl (silentE_fair fmap)) tl)

  | tr_ord_fair_fail
      o fmap tl o0
      (FAIL: Flag.fail = (fmap i))
      (LT: wft.(lt) o0 o)
      (TL: tr_ord i o0 tl)
    :
    tr_ord i o (RawTr.cons (inl (silentE_fair fmap)) tl)
  .

  Variable wft0: wft.(T).
  Variable S: wft.(T) -> wft.(T).
  Hypothesis lt_succ_diag_r: forall (t: wft.(T)), wft.(lt) t (S t).

  Lemma fair_ind_implies_tr_ord
        R (tr: @RawTr.t Ident R)
        (IND: RawTr.is_fair_ind tr)
    :
    forall i, exists o, tr_ord i o tr.
  Proof.
    i. specialize (IND i).
    punfold IND.
    2:{ clear. ii. eapply pind3_mon_gen; eauto. ii. ss. eapply paco3_mon_gen. eapply PR. 2: ss.
        i. eapply RawTr.___fair_ind_mon; eauto.
    } (*make lemma*)

    (* match goal with *)
    (* | IND: pind3 ?lf _ _ _ _ |- _ => *)
    (*     eapply (pind3_acc (l:= upind3 lf)) *)
    (* end. *)
    (* { i. *)
    
    revert R i tr IND.
    eapply (@pind3_acc _ _ _ _ (fun (R: Type) => (fun (i: id) => fun (tr: @RawTr.t Ident R) => exists o, tr_ord i o tr))).
    i. rename x0 into R, x1 into i, x2 into tr.
    eapply pind3_unfold in PR.
    2:{ clear. ii. eapply paco3_mon_gen. eapply IN. 2: ss.
        i. eapply RawTr.__fair_ind_mon; eauto.
    } (*make lemma*)
    punfold PR.
    2:{ eapply RawTr._fair_ind_mon. }
    inv PR.
    7:{ destruct TL. eapply IH in H0. des. rename H0 into ORD. exists (S o).
        econs 8. eauto. 2: eauto. eauto.
    }
    5:{ pclearbot. eexists. econs 6.

        clear DEC IH. punfold TL.
        2:{ eapply RawTr._fair_ind_mon. }
        inv TL.




  (* coinductive-inductive *)
  Definition terminal_tr {R} (tr: @RawTr.t _ R) :=
    match tr with
    | RawTr.done _ | RawTr.ub | RawTr.nb => True
    | _ => False
    end.

  Variant __lt_tr (i: id)
          (lt_tr: forall (R: Type), (@RawTr.t _ R) -> (@RawTr.t _ R) -> Prop)
          (_lt_tr: forall (R: Type), (@RawTr.t _ R) -> (@RawTr.t _ R) -> Prop)
          (R: Type)
    :
    (@RawTr.t _ R) -> (@RawTr.t _ R) -> Prop :=
    (* inner coinductive cases: no fail for i *)
    | lt_tr_obs_r
        tr (obs: obsE) tl
        (TL: _lt_tr R tr tl)
      :
      __lt_tr i lt_tr _lt_tr tr (RawTr.cons (inr obs) tl)
    | lt_tr_tau_r
        tr tl
        (TL: _lt_tr R tr tl)
      :
      __lt_tr i lt_tr _lt_tr tr (RawTr.cons (inl silentE_tau) tl)
    | lt_tr_fair_nofail_r
        tr fm tl
        (TL: _lt_tr R tr tl)
        (NOFAIL: Flag.le Flag.emp (fm i))
      :
      __lt_tr i lt_tr _lt_tr tr (RawTr.cons (inl (silentE_fair fm)) tl)

    | lt_tr_obs_l
        (obs: obsE) tl tr
        (TL: _lt_tr R tr tl)
      :
      __lt_tr i lt_tr _lt_tr (RawTr.cons (inr obs) tl) tr
    | lt_tr_tau_l
        tl tr
        (TL: _lt_tr R tr tl)
      :
      __lt_tr i lt_tr _lt_tr (RawTr.cons (inl silentE_tau) tl) tr
    | lt_tr_fair_nofail_l
        fm tl tr
        (TL: _lt_tr R tr tl)
        (NOFAIL: Flag.le Flag.emp (fm i))
      :
      __lt_tr i lt_tr _lt_tr (RawTr.cons (inl (silentE_fair fm)) tl) tr

    (* outer inductive cases: i fails inductively *)
    (* base cases *)
    | lt_tr_terminal
        tr1 tr2
        (IND: lt_tr R tr1 tr2)
        (TERM: terminal_tr tr1)
        (TERM: terminal_tr tr2)
      :
      __lt_tr i lt_tr _lt_tr tr1 tr2

    | lt_tr_fair_fail_r
        tr fm tl
        (TL: lt_tr R tr tl)
        (FAIL: Flag.fail = (fm i))
      :
      __lt_tr i lt_tr _lt_tr tr (RawTr.cons (inl (silentE_fair fm)) tl)
    | lt_tr_fair_fail_l
        fm1 tl1 fm2 tl2
        (TL: lt_tr R tl1 tl2)
        (FAIL1: Flag.fail = (fm1 i))
        (FAIL2: Flag.fail = (fm2 i))
      :
      __lt_tr i lt_tr _lt_tr
              (RawTr.cons (inl (silentE_fair fm1)) tl1)
              (RawTr.cons (inl (silentE_fair fm2)) tl2)
  .

  Definition lt_tr (i: id): forall (R: Type), (@RawTr.t _ R) -> (@RawTr.t _ R) -> Prop :=
    pind3 (fun q => paco3 (__lt_tr i q) bot3) top3.

  Lemma __lt_tr_mon i: forall r r' (LE: r <3= r'), (__lt_tr i r) <4= (__lt_tr i r').
  Proof.
    ii. inv PR.
    - econs 1; eauto.
    - econs 2; eauto.
    - econs 3; eauto.
    - econs 4; eauto.
    - econs 5; eauto.
    - econs 6; eauto.
    - econs 7; eauto.
    - econs 8; eauto.
    - econs 9; eauto.
  Qed.

  Lemma _lt_tr_mon i: forall r, monotone3 (__lt_tr i r).
  Proof.
    ii. inv IN.
    - econs 1; eauto.
    - econs 2; eauto.
    - econs 3; eauto.
    - econs 4; eauto.
    - econs 5; eauto.
    - econs 6; eauto.
    - econs 7; eauto.
    - econs 8; eauto.
    - econs 9; eauto.
  Qed.

  Lemma lt_tr_mon i: forall p, monotone3 (fun q => (__lt_tr i q) p).
  Proof.
    ii. eapply __lt_tr_mon; eauto.
  Qed.

(* Section INDEX. *)
(*   Lemma nat_ind *)
(*         (P: nat -> Prop) *)
(*         (ZERO: P O) *)
(*         (SUCC: forall a (IND: P a), P (S a)) *)
(*     : *)
(*     forall n, P n. *)
(*   Proof. *)
(*     revert_until P. revert P. fix IH 4. i. destruct n; auto. *)
(*     eapply SUCC. eapply IH. auto. i. eapply SUCC. auto. *)
(*   Qed. *)

(*   Lemma nat_strong_ind *)
(*         (P: nat -> Prop) *)
(*         (ZERO: P O) *)
(*         (SUCC: forall a (STR: forall b (LT: lt b (S a)), P b), P (S a)) *)
(*     : *)
(*     forall n, P n. *)
(*   Proof. *)
(*     cut (forall a b (LT: lt b (S a)), P b). *)
(*     { i. eapply H. instantiate (1:=n). auto. } *)
(*     induction a; i; auto. *)
(*     { inv LT; auto. inv H0. } *)
(*     unfold lt in LT. inv LT. *)
(*     { eapply SUCC. auto. } *)
(*     eapply IHa. lia. *)
(*   Qed. *)

(*   Lemma aux2: well_founded lt. *)
(*   Proof. *)
(*     ii. induction a using nat_strong_ind. *)
(*     { econs. i. inv H. } *)
(*     econs. i. eapply STR. auto. *)
(*   Qed. *)

(* End INDEX. *)


  Lemma wf_lt_tr {R}: forall i, well_founded (lt_tr i (R:=R)).
  Proof.
    ii. econs. i. eapply Acc_inv. 2: eauto. unfold lt_tr in H. econs. eapply pind3_acc.
    (* 2:{ eauto. } *)
    2:{ eapply pind3_mult_strong in H. eapply H. }
    i. eapply pind3_unfold in PR.
    2:{ clear. ii. eapply paco3_mon_gen. eapply IN. 2: ss.
        i. eapply __lt_tr_mon; eauto.
    } (*make lemma*)
    punfold PR.
    2:{ eapply _lt_tr_mon. }
    (*TODO*)
    inv PR.
    { pclearbot. punfold TL.
      2:{ eapply _lt_tr_mon. }
      econs. i.
      


    }
    { 


  (* Variable wft0: wft.(T). *)

  (* Lemma fair_ind_implies_tr_ord *)
  (*       (tr: @RawTr.t Ident R) *)
  (*       (IND: RawTr.is_fair_ind tr) *)
  (*   : *)
  (*   forall i, exists o, tr_ord i o tr. *)
  (* Proof. *)
  (*   i. specialize (IND i). *)
  (*   punfold IND. *)
  (*   2:{ clear. ii. eapply pind3_mon_gen; eauto. ii. ss. eapply paco3_mon_gen. eapply PR. 2: ss. *)
  (*       i. eapply RawTr.___fair_ind_mon; eauto. *)
  (*   } (*make lemma*) *)

  (*   (* match goal with *) *)
  (*   (* | IND: pind3 ?lf _ _ _ _ |- _ => *) *)
  (*   (*     eapply (pind3_acc (l:= upind3 lf)) *) *)
  (*   (* end. *) *)
  (*   (* { i. *) *)

  (*   eapply pind3_acc. *)
  (*   2:{ eapply pind3_mult_strong in IND. eauto. } *)
  (*   i. clear IND. *)
  (*   eapply pind3_unfold in PR. *)
  (*   2:{ clear. ii. eapply paco3_mon_gen. eapply IN. 2: ss. *)
  (*       i. eapply RawTr.__fair_ind_mon; eauto. *)
  (*   } (*make lemma*) *)
  (*   punfold PR. *)
  (*   2:{ eapply RawTr._fair_ind_mon. } *)
  (*   rename x0 into R0, x1 into i0, x2 into tr0. *)
  (*   inv PR. *)
  (*   7:{ destruct TL. eauto. } *)
  (*   5:{  *)




  Theorem Ind_implies_Ord
          (tr: @RawTr.t Ident R)
          (IND: RawTr.is_fair_ind tr)
    :
    RawTr.is_fair_ord wft tr.
  Proof.
    unfold RawTr.is_fair_ord. unfold RawTr.is_fair_ind in IND.
    eexists. revert_until lt_succ_diag_r. pcofix CIH. i.
    destruct tr eqn:TR.
    { pfold. econs. }
    { pfold. econs. }
    { pfold. econs. }
    { destruct hd as [silent | obs].
      2:{ pfold. econs. right. eapply CIH. i.
          specialize (IND i). punfold IND.
          2:{ clear. ii. eapply pind3_mon_gen; eauto. ii. ss. eapply paco3_mon_gen. eapply PR. 2: ss.
              i. eapply RawTr.___fair_ind_mon; eauto.
          } (*make lemma*)
          eapply pind3_unfold in IND.
          2:{ clear. ii. eapply paco3_mon_gen. eapply IN. 2: ss.
              i. eapply RawTr.__fair_ind_mon; eauto.
          } (*make lemma*)
          punfold IND.
          2:{ eapply RawTr._fair_ind_mon. }
          inv IND. pclearbot. eapply paco3_mon. eauto. ss.
      }
      destruct silent as [ | fm].
      { pfold. econs. right. eapply CIH. i.
        specialize (IND i). punfold IND.
        2:{ clear. ii. eapply pind3_mon_gen; eauto. ii. ss. eapply paco3_mon_gen. eapply PR. 2: ss.
            i. eapply RawTr.___fair_ind_mon; eauto.
        } (*make lemma*)
        eapply pind3_unfold in IND.
        2:{ clear. ii. eapply paco3_mon_gen. eapply IN. 2: ss.
            i. eapply RawTr.__fair_ind_mon; eauto.
        } (*make lemma*)
        punfold IND.
        2:{ eapply RawTr._fair_ind_mon. }
        inv IND. pclearbot. eapply paco3_mon. eauto. ss.
      }
      { pfold. econs.
        2:{ right. eapply CIH. i.
            specialize (IND i). eapply fair_ind_fair_red; eauto.
        }
        admit.
      }
    } 

End EQUIV2.
