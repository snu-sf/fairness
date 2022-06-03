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


Section EQUIV.

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

  Inductive ord_tr (i: id)
            (R: Type)
    :
    wft.(T) -> (@RawTr.t _ R) -> Prop :=
  | ord_tr_done
      o retv
    :
    ord_tr i o (RawTr.done retv)
  | ord_tr_ub
      o
    :
    ord_tr i o RawTr.ub
  | ord_tr_nb
      o
    :
    ord_tr i o RawTr.nb

  | ord_tr_fair_success
      o fmap tl
      (SUCCESS: Flag.success = (fmap i))
    :
    ord_tr i o (RawTr.cons (inl (silentE_fair fmap)) tl)

  | ord_tr_obs
      o (obs: obsE) tl res
      (TL: ord_tr i o res)
      (RES: consume_tr i tl res)
    :
    ord_tr i o (RawTr.cons (inr obs) tl)
  | ord_tr_tau
      o tl res
      (TL: ord_tr i o res)
      (RES: consume_tr i tl res)
    :
    ord_tr i o (RawTr.cons (inl silentE_tau) tl)
  | ord_tr_fair_emp
      o fmap tl res
      (EMP: Flag.emp = (fmap i))
      (TL: ord_tr i o res)
      (RES: consume_tr i tl res)
    :
    ord_tr i o (RawTr.cons (inl (silentE_fair fmap)) tl)

  | ord_tr_fair_fail
      o fmap tl o0
      (FAIL: Flag.fail = (fmap i))
      (LT: wft.(lt) o0 o)
      (TL: ord_tr i o0 tl)
    :
    ord_tr i o (RawTr.cons (inl (silentE_fair fmap)) tl)
  .

  Variable wft0: wft.(T).
  Variable S: wft.(T) -> wft.(T).
  Hypothesis lt_succ_diag_r: forall (t: wft.(T)), wft.(lt) t (S t).

  Lemma fair_ind_implies_ord_tr
        R (tr: @RawTr.t Ident R)
        (IND: RawTr.is_fair_ind tr)
    :
    forall i, exists o, ord_tr i o tr.
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
    eapply (@pind3_acc _ _ _ _ (fun (R: Type) => (fun (i: id) => fun (tr: @RawTr.t Ident R) => exists o, ord_tr i o tr))).
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
  Variant __ord_tr (i: id)
          (ord_tr: forall (R: Type) (t: wft.(T)), (@RawTr.t _ R) -> Prop)
          (_ord_tr: forall (R: Type) (t: wft.(T)), (@RawTr.t _ R) -> Prop)
          (R: Type) (o: wft.(T))
    :
    (@RawTr.t _ R) -> Prop :=
    (* base cases *)
    | ord_tr_done
        retv
      :
      __ord_tr i ord_tr _ord_tr o (RawTr.done retv)
    | ord_tr_ub
      :
      __ord_tr i ord_tr _ord_tr o RawTr.ub
    | ord_tr_nb
      :
      __ord_tr i ord_tr _ord_tr o RawTr.nb
    | ord_tr_fair_success
        fmap tl
        (SUCCESS: Flag.success = (fmap i))
      :
      __ord_tr i ord_tr _ord_tr o (RawTr.cons (inl (silentE_fair fmap)) tl)

    (* inner coinductive cases: no fair events for i *)
    | ord_tr_obs
        (obs: obsE) tl
        (TL: _ord_tr R o tl)
      :
      __ord_tr i ord_tr _ord_tr o (RawTr.cons (inr obs) tl)
    | ord_tr_tau
        tl
        (TL: _ord_tr R o tl)
      :
      __ord_tr i ord_tr _ord_tr o (RawTr.cons (inl silentE_tau) tl)
    | ord_tr_fair_emp
        fmap tl
        (EMP: Flag.emp = (fmap i))
        (TL: _ord_tr R o tl)
      :
      __ord_tr i ord_tr _ord_tr o (RawTr.cons (inl (silentE_fair fmap)) tl)

    (* outer inductive cases: i fails inductively *)
    | ord_tr_fair_fail
        fmap tl o0
        (FAIL: Flag.fail = (fmap i))
        (LT: wft.(lt) o0 o)
        (TL: ord_tr R o0 tl)
      :
      __ord_tr i ord_tr _ord_tr o (RawTr.cons (inl (silentE_fair fmap)) tl)
  .

  Definition ord_tr (i: id): forall (R: Type) (o: wft.(T)), (@RawTr.t _ R) -> Prop :=
    pind3 (fun q => paco3 (__ord_tr i q) bot3) top3.

  Lemma __ord_tr_mon i: forall r r' (LE: r <3= r'), (__ord_tr i r) <4= (__ord_tr i r').
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

  Lemma _ord_tr_mon i: forall r, monotone3 (__ord_tr i r).
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

  Lemma ord_tr_mon i: forall p, monotone3 (fun q => (__ord_tr i q) p).
  Proof.
    ii. eapply __ord_tr_mon; eauto.
  Qed.


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

  (* Lemma fair_ind_implies_ord_tr *)
  (*       (tr: @RawTr.t Ident R) *)
  (*       (IND: RawTr.is_fair_ind tr) *)
  (*   : *)
  (*   forall i, exists o, ord_tr i o tr. *)
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

End EQUIV.
