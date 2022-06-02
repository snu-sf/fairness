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

  Variable R: Type.

  Theorem Ord_implies_Ind
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


  (* Variable S: wft.(T) -> wft.(T). *)
  (* Hypothesis lt_succ_diag_r: forall (t: wft.(T)), wft.(lt) t (S t). *)

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
