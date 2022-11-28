From sflib Require Import sflib.

Require Import Coq.Classes.RelationClasses.

From Fairness Require Import
  Axioms ITreeLib WFLib FairBeh pind_internal pind3 SelectBeh.

From Paco Require Import paco.

Set Implicit Arguments.

Section AUX.

  Variable id: ID.

  Lemma fair_ind_cases
        i R (tr: @RawTr.t id R)
    :
    (<<NF: (RawTr.nofail i tr) /\ (~ RawTr.must_fail i tr)>>) \/
      (<<MF: (RawTr.must_fail i tr) /\ (~ RawTr.must_success i tr) /\ (~ RawTr.nofail i tr)>>) \/
      (<<MS: (RawTr.must_success i tr) /\ (~ RawTr.must_fail i tr) /\ (~ RawTr.nofail i tr)>>).
  Proof.
    destruct (classic (RawTr.nofail i tr)) as [NF | NNF]; auto.
    - destruct (classic (RawTr.must_fail i tr)) as [MF | NMF]; auto.
      apply RawTr.must_fail_not_nofail in MF. clarify.
    - destruct (classic (RawTr.must_fail i tr)) as [MF | NMF]; auto.
      + destruct (classic (RawTr.must_success i tr)) as [MS | NMS]; auto.
        * apply RawTr.must_fail_not_success in MF. clarify.
        * right. left. auto.
      + destruct (classic (RawTr.must_success i tr)) as [MS | NMS]; auto.
        * right. right. auto.
        * hexploit RawTr.not_musts_nofail; eauto.
  Qed.



  Variable wft: WF.
  Variable wft0: wft.(T).
  Variable S: wft.(T) -> wft.(T).

  (* fix an unique ordering for the first list of fail *)
  Inductive ord_tr (i: id) R: wft.(T) -> (@RawTr.t id R) -> Prop :=
  (* base case1: no more fail *)
  | ord_tr_nofail
      tr
      (NOFAIL: RawTr.nofail i tr)
    :
    ord_tr i wft0 tr
  (* base case2: must success *)
  | ord_tr_ms
      tr
      (NNF: ~ RawTr.nofail i tr)
      (MS: RawTr.must_success i tr)
    :
    ord_tr i wft0 tr

  (* inductive cases *)
  | ord_tr_obs
      o (obs: obsE) tl
      (NNF: ~ RawTr.nofail i tl)
      (MF: RawTr.must_fail i tl)
      (ORD: ord_tr i o tl)
    :
    ord_tr i o (RawTr.cons (inr obs) tl)
  | ord_tr_tau
      o tl
      (NNF: ~ RawTr.nofail i tl)
      (MF: RawTr.must_fail i tl)
      (ORD: ord_tr i o tl)
    :
    ord_tr i o (RawTr.cons (inl silentE_tau) tl)
  | ord_tr_fair_emp
      o fm tl
      (EMP: (fm i) = Flag.emp)
      (NNF: ~ RawTr.nofail i tl)
      (MF: RawTr.must_fail i tl)
      (ORD: ord_tr i o tl)
    :
    ord_tr i o (RawTr.cons (inl (silentE_fair fm)) tl)
  | ord_tr_fair_fail
      o fm tl
      (FAIL: (fm i) = Flag.fail)
      (ORD: ord_tr i o tl)
    :
    ord_tr i (S o) (RawTr.cons (inl (silentE_fair fm)) tl)
  .


  Lemma nofail_ex_ord_tr
        i R (tr: @RawTr.t id R)
        (NOFAIL: RawTr.nofail i tr)
    :
    exists o, ord_tr i o tr.
  Proof.
    exists wft0. econs 1. auto.
  Qed.

  Lemma fair_ind_ex_ord_tr
        i R (tr: @RawTr.t id R)
        (IND: RawTr.is_fair_ind tr)
    :
    exists o, ord_tr i o tr.
  Proof.
    specialize (IND i). punfold IND.
    revert R i tr IND.
    eapply (@pind3_acc _ _ _ _ (fun R i (tr: @RawTr.t id R) => (exists o, ord_tr i o tr))).
    i. rename x0 into R, x1 into i, x2 into tr.
    eapply pind3_unfold in PR.
    2:{ clear. ii. eapply RawTr.fair_ind_mon2; eauto. }
    inv PR.
    { eexists. econs 1. auto. }
    { destruct (fair_ind_cases i tl) as [NF | [MF | MS]]; des.
      { clarify. }
      { hexploit IND; clear IND; eauto. intro IND.
        destruct IND as [PIND IND]. eapply IH in IND. des. exists o. econs 3; eauto. }
      { eexists. econs 2.
        - intro NF. apply MS1. punfold NF. inv NF. pclearbot. eauto.
        - econs. eauto.
      }
    }
    { destruct (fair_ind_cases i tl) as [NF | [MF | MS]]; des.
      { clarify. }
      { hexploit IND; clear IND; eauto. intro IND.
        destruct IND as [PIND IND]. eapply IH in IND. des. exists o. econs 4; eauto. }
      { eexists. econs 2.
        - intro NF. apply MS1. punfold NF. inv NF. pclearbot. eauto.
        - econs. eauto.
      }
    }
    { destruct (fair_ind_cases i tl) as [NF | [MF | MS]]; des.
      { clarify. }
      { hexploit IND; clear IND; eauto. intro IND.
        destruct IND as [PIND IND]. eapply IH in IND. des. exists o. econs 5; eauto. }
      { eexists. econs 2.
        - intro NF. apply MS1. punfold NF. inv NF. rewrite EMP in SUCCESS; ss. pclearbot. eauto.
        - econs 4; eauto.
      }
    }
    { destruct (fair_ind_cases i tl) as [NF | [MF | MS]]; des.
      { eexists. econs 6; auto. econs 1; eauto. }
      { hexploit IND; clear IND; eauto. intro IND.
        destruct IND as [PIND IND]. eapply IH in IND. des. exists (S o). econs 6; eauto. }
      { eexists. econs 6; eauto. econs 2; eauto. }
    }
    { destruct (fair_ind_cases i (RawTr.cons (inl (silentE_fair fm)) tl)) as [NF | [MF | MS]]; des.
      { eexists. econs 1; eauto. }
      { inv MF. rewrite SUCCESS in FAIL; ss. rewrite SUCCESS in EMP; ss. }
      { eexists. econs 2; eauto. }
    }
  Qed.

End AUX.



Section EQUIV.

  Variable id: ID.
  Hypothesis ID_DEC: forall (i0 i1: id), {i0 = i1} + {i0 <> i1}.

  Variable wft: WF.
  Variable wft0: wft.(T).
  Variable S: wft.(T) -> wft.(T).
  Hypothesis lt_succ_diag_r: forall (t: wft.(T)), wft.(lt) t (S t).
  Hypothesis WFTR: Transitive wft.(lt).

  Theorem Ord_implies_Fair
          R
          (tr: @RawTr.t id R)
          (ORD: RawTr.is_fair_ord wft tr)
    :
    RawTr.is_fair tr.
  Proof.
    ii. unfold RawTr.is_fair_ord in ORD. des.
    revert_until R. pcofix CIH1. i.
    eapply paco3_fold.
    remember (m i) as idx. move idx before CIH1. revert_until idx.
    induction (wft.(wf) idx). rename H0 into IH, x into idx. clear H. i.
    eapply pind3_fold. revert_until IH. pcofix CIH2. i.
    eapply paco3_fold. eapply paco3_unfold.
    { eapply RawTr._fair_mon. }
    punfold ORD. inv ORD.
    { pfold. econs 1. }
    { pfold. econs 2. }
    { pfold. econs 3. }
    { pclearbot. pfold. econs 4. right. eapply CIH2; eauto. }
    { pclearbot. destruct (fmap i) eqn:FM.
      { pfold. econs 7. auto. split; ss. eapply IH. 2: eauto. all: eauto.
        unfold fair_update in FAIR. specialize (FAIR i). rewrite FM in FAIR. auto.
      }
      { dup FAIR. unfold fair_update in FAIR. specialize (FAIR i). rewrite FM in FAIR.
        pfold. econs 6. auto. right. eapply CIH2; eauto.
      }
      { pfold. econs 8. auto. right. eapply CIH1; eauto. }
    }
    { pclearbot. pfold. econs 5. right. eapply CIH2; eauto. }
  Qed.

  Theorem Fair_implies_Ind
          R
          (tr: @RawTr.t id R)
          (IND: RawTr.is_fair tr)
    :
    RawTr.is_fair_ind tr.
  Proof.
    ii. specialize (IND i). depgen tr. pcofix CIH. i.
    punfold IND. pfold. revert R i tr IND CIH.
    eapply (@pind3_acc _ _ _ _ (fun R i (tr: @RawTr.t id R) =>
                                  (forall tr0 : RawTr.t, RawTr.fair i tr0 -> r R i tr0) ->
                                  pind3
                                    (RawTr.__fair_ind
                                       (upaco3 (fun r0 => pind3 (RawTr.__fair_ind r0) top3) r)) top3 R i tr)).
    i. rename x0 into R, x1 into i, x2 into tr. rename H into CIH. clear DEC.
    eapply pind3_unfold in PR.
    2:{ clear. ii. eapply paco3_mon_gen. eauto. 2: ss. i. eapply RawTr.__fair_mon; eauto. }
    destruct (fair_ind_cases i tr) as [NF | [MF | MS]]; des.
    { eapply pind3_fold. econs 1; auto. }
    { move CIH before i. move MF before tr. revert_until MF. induction MF; i.
      { eapply pind3_fold. punfold PR. inv PR.
        { rewrite FAIL in EMP; ss. }
        2:{ rewrite FAIL in SUCCESS; ss. }
        destruct TL as [PIND IND]. econs 5; auto.
        i. split; ss. eapply IH; eauto.
      }
      { punfold PR. inv PR. pclearbot.
        assert (NMS: ~ RawTr.must_success i tl).
        { intros MS; apply MF0. econs. auto. }
        assert (NNF: ~ RawTr.nofail i tl).
        { intros NF. apply MF1. pfold; econs. eauto. }
        eapply IHMF in TL; clear IHMF; auto.
        eapply pind3_fold. econs 2; auto. i. split; ss.
      }
      { punfold PR. inv PR. pclearbot.
        assert (NMS: ~ RawTr.must_success i tl).
        { intros MS; apply MF0. econs. auto. }
        assert (NNF: ~ RawTr.nofail i tl).
        { intros NF. apply MF1. pfold; econs. eauto. }
        eapply IHMF in TL; clear IHMF; auto.
        eapply pind3_fold. econs 3; eauto. i. split; ss.
      }
      { punfold PR. inv PR.
        2:{ rewrite EMP in FAIL; ss. }
        2:{ rewrite EMP in SUCCESS; ss. }
        pclearbot.
        assert (NMS: ~ RawTr.must_success i tl).
        { intros MS; apply MF0. econs 4; auto. }
        assert (NNF: ~ RawTr.nofail i tl).
        { intros NF. apply MF1. pfold; econs 7; eauto. }
        eapply IHMF in TL; clear IHMF; auto.
        eapply pind3_fold. econs 4; eauto. split; ss.
      }
    }
    { move CIH before i. move MS before tr. revert_until MS. induction MS; i.
      { eapply pind3_fold. punfold PR. inv PR.
        { rewrite SUCCESS in EMP; ss. }
        { rewrite SUCCESS in FAIL; ss. }
        pclearbot. econs 6; eauto.
      }
      { punfold PR. inv PR. pclearbot.
        assert (NMF: ~ RawTr.must_fail i tl).
        { intros MF; apply MS0. econs. auto. }
        assert (NNF: ~ RawTr.nofail i tl).
        { intros NF. apply MS1. pfold; econs. eauto. }
        eapply IHMS in TL; clear IHMS; auto.
        eapply pind3_fold. econs 2; auto. i. split; ss.
      }
      { punfold PR. inv PR. pclearbot.
        assert (NMF: ~ RawTr.must_fail i tl).
        { intros MF; apply MS0. econs. auto. }
        assert (NNF: ~ RawTr.nofail i tl).
        { intros NF. apply MS1. pfold; econs. eauto. }
        eapply IHMS in TL; clear IHMS; auto.
        eapply pind3_fold. econs 3; eauto. i. split; ss.
      }
      { punfold PR. inv PR.
        2:{ rewrite EMP in FAIL; ss. }
        2:{ rewrite EMP in SUCCESS; ss. }
        pclearbot.
        assert (NMS: ~ RawTr.must_fail i tl).
        { intros MF; apply MS0. econs 4; auto. }
        assert (NNF: ~ RawTr.nofail i tl).
        { intros NF. apply MS1. pfold; econs 7; eauto. }
        eapply IHMS in TL; clear IHMS; auto.
        eapply pind3_fold. econs 4; eauto. split; ss.
      }
    }
  Qed.

End EQUIV.



Section EQUIV2.

  Context {id: ID}.

  Variable wft: WF.
  Variable wft0: wft.(T).
  Variable S: wft.(T) -> wft.(T).
  Hypothesis lt_succ_diag_r: forall (t: wft.(T)), wft.(lt) t (S t).


  Lemma ord_tr_red_obs
        R i obs (tr: @RawTr.t id R) o
        (ORD: ord_tr wft wft0 S i o (RawTr.cons (inr obs) tr))
    :
    ord_tr wft wft0 S i o tr.
  Proof.
    remember (RawTr.cons (inr obs) tr) as otr. move ORD before R. revert_until ORD. induction ORD; i; ss; clarify.
    { punfold NOFAIL. inv NOFAIL. pclearbot. econs 1; auto. }
    { econs 2.
      - intro NF; apply NNF. pfold. econs. auto.
      - inv MS. auto.
    }
  Qed.

  Lemma ord_tr_red_tau
        R i (tr: @RawTr.t id R) o
        (ORD: ord_tr wft wft0 S i o (RawTr.cons (inl silentE_tau) tr))
    :
    ord_tr wft wft0 S i o tr.
  Proof.
    remember (RawTr.cons (inl silentE_tau) tr) as otr. move ORD before R. revert_until ORD. induction ORD; i; ss; clarify.
    { punfold NOFAIL. inv NOFAIL. pclearbot. econs 1; auto. }
    { econs 2.
      - intro NF; apply NNF. pfold. econs. auto.
      - inv MS. auto.
    }
  Qed.



  Lemma inhabited_tr_ord: inhabited (T wft).
  Proof. econs. exact wft0. Qed.

  Definition tr2ord_i {R} i (tr: (@RawTr.t id R)): wft.(T) :=
    epsilon (inhabited_tr_ord) (fun o => ord_tr wft wft0 S i o tr).

  Theorem tr2ord_i_spec
          i R (tr: @RawTr.t id R)
          (IND: RawTr.is_fair_ind tr)
    :
    ord_tr wft wft0 S i (tr2ord_i i tr) tr.
  Proof.
    unfold tr2ord_i, epsilon. unfold Epsilon.epsilon, proj1_sig. des_ifs. clear Heq.
    hexploit o; clear o. eapply fair_ind_ex_ord_tr; eauto. intros ORD. auto.
  Qed.


  Lemma ord_tr_nofail_fix
        R i o (tr: @RawTr.t id R)
        (ORD: ord_tr wft wft0 S i o tr)
        (NF: RawTr.nofail i tr)
    :
    o = wft0.
  Proof.
    inv ORD; eauto.
    { punfold NF. inv NF. pclearbot. clarify. }
    { punfold NF. inv NF. pclearbot. clarify. }
    { punfold NF. inv NF. rewrite EMP in SUCCESS; ss. pclearbot. clarify. }
    { punfold NF. inv NF. rewrite FAIL in SUCCESS; ss. rewrite FAIL in EMP; ss. }
  Qed.

  Lemma ord_tr_ms_fix
        R i o (tr: @RawTr.t id R)
        (ORD: ord_tr wft wft0 S i o tr)
        (NNF: ~ RawTr.nofail i tr)
        (MS: RawTr.must_success i tr)
    :
    o = wft0.
  Proof.
    inv ORD; eauto.
    { inv MS. apply RawTr.must_fail_not_success in MF. clarify. }
    { inv MS. apply RawTr.must_fail_not_success in MF. clarify. }
    { inv MS. rewrite EMP in SUCCESS; ss. apply RawTr.must_fail_not_success in MF. clarify. }
    { inv MS. rewrite FAIL in SUCCESS; ss. rewrite FAIL in EMP; ss. }
  Qed.

  Lemma ord_tr_eq
        R i o1 o2 (tr: @RawTr.t id R)
        (ORD1: ord_tr wft wft0 S i o1 tr)
        (ORD2: ord_tr wft wft0 S i o2 tr)
    :
    o1 = o2.
  Proof.
    depgen o2. induction ORD1; i.
    { inv ORD2; eauto.
      all: punfold NOFAIL; inv NOFAIL; pclearbot; clarify.
      rewrite FAIL in SUCCESS; ss. rewrite FAIL in EMP; ss.
    }
    { inv ORD2; eauto.
      - inv MS; apply RawTr.must_fail_not_success in MF; clarify.
      - inv MS. apply RawTr.must_fail_not_success in MF; clarify.
      - inv MS. rewrite EMP in SUCCESS; ss. apply RawTr.must_fail_not_success in MF; clarify.
      - inv MS. rewrite FAIL in SUCCESS; ss. rewrite FAIL in EMP; ss.
    }
    { inv ORD2; eauto.
      - punfold NOFAIL; inv NOFAIL. pclearbot. eapply RawTr.must_fail_not_nofail in MF. clarify.
      - inv MS. eapply RawTr.must_fail_not_success in MF. clarify.
    }
    { inv ORD2; eauto.
      - punfold NOFAIL; inv NOFAIL. pclearbot. eapply RawTr.must_fail_not_nofail in MF. clarify.
      - inv MS. eapply RawTr.must_fail_not_success in MF. clarify.
    }
    { inv ORD2; eauto.
      - punfold NOFAIL; inv NOFAIL. rewrite EMP in SUCCESS; ss.
        pclearbot. eapply RawTr.must_fail_not_nofail in MF. clarify.
      - inv MS. rewrite EMP in SUCCESS; ss. eapply RawTr.must_fail_not_success in MF. clarify.
      - rewrite EMP in FAIL; ss.
    }
    { inv ORD2; eauto.
      - punfold NOFAIL; inv NOFAIL. rewrite FAIL in SUCCESS; ss. rewrite FAIL in EMP; ss.
      - inv MS. rewrite FAIL in SUCCESS; ss. rewrite FAIL in EMP; ss.
      - rewrite FAIL in EMP; ss.
      - f_equal. eauto.
    }
  Qed.


  Lemma ord_tr_fair_case
        R (tr: @RawTr.t id R) fm m
        (IND: RawTr.is_fair_ind tr)
        (ORD: forall i : id, ord_tr wft wft0 S i (m i) (RawTr.cons (inl (silentE_fair fm)) tr))
    :
    exists m0, (fair_update m m0 fm) /\ (forall i : id, ord_tr wft wft0 S i (m0 i) tr).
  Proof.
    exists (fun i => tr2ord_i i tr). split.
    2:{ i. eapply tr2ord_i_spec. eauto. }
    ii. specialize (ORD i). des_ifs.
    { destruct (fair_ind_cases i tr) as [NF | [MF | MS]]; des.
      { inv ORD.
        { punfold NOFAIL. inv NOFAIL. rewrite Heq in SUCCESS; ss. rewrite Heq in EMP; ss. }
        { inv MS. rewrite Heq in SUCCESS; ss. rewrite Heq in EMP; ss. }
        { rewrite Heq in EMP; ss. }
        { assert (tr2ord_i i tr = o).
          { eapply ord_tr_eq; eauto. eapply tr2ord_i_spec; eauto. }
          rewrite H; auto.
        }
      }
      { inv ORD.
        { punfold NOFAIL. inv NOFAIL. rewrite Heq in SUCCESS; ss. rewrite Heq in EMP; ss. }
        { inv MS. rewrite Heq in SUCCESS; ss. rewrite Heq in EMP; ss. }
        { rewrite Heq in EMP; ss. }
        { assert (tr2ord_i i tr = o).
          { eapply ord_tr_eq; eauto. eapply tr2ord_i_spec; eauto. }
          rewrite H; auto.
        }
      }
      { inv ORD.
        { punfold NOFAIL. inv NOFAIL; pclearbot; clarify. }
        { inv MS2. rewrite Heq in SUCCESS; ss. rewrite Heq in EMP; ss. }
        { rewrite Heq in EMP; ss. }
        { assert (tr2ord_i i tr = o).
          { eapply ord_tr_eq; eauto. eapply tr2ord_i_spec; eauto. }
          rewrite H; auto.
        }
      }
    }
    { destruct (fair_ind_cases i tr) as [NF | [MF | MS]]; des.
      { inv ORD.
        { rewrite <- H. eapply ord_tr_eq; eauto. eapply tr2ord_i_spec; eauto. econs 1. auto. }
        { rewrite <- H. eapply ord_tr_eq; eauto. eapply tr2ord_i_spec; eauto. econs 1. auto. }
        { clarify. }
        { rewrite Heq in FAIL; ss. }
      }
      { inv ORD.
        { punfold NOFAIL. inv NOFAIL. rewrite Heq in SUCCESS; ss. pclearbot. clarify. }
        { inv MS. rewrite Heq in SUCCESS; ss. clarify. }
        { eapply ord_tr_eq; eauto. eapply tr2ord_i_spec; eauto. }
        { rewrite Heq in FAIL; ss. }
      }
      { inv ORD.
        { punfold NOFAIL. inv NOFAIL; pclearbot; clarify. }
        { rewrite <- H. eapply ord_tr_eq; eauto. eapply tr2ord_i_spec; eauto. econs 2; auto. }
        { eapply ord_tr_eq; eauto. eapply tr2ord_i_spec; eauto. }
        { rewrite Heq in FAIL; ss. }
      }
    }
  Qed.


  Lemma fair_ind_red_fair
        R (tr: @RawTr.t id R) fm
        (IND: RawTr.is_fair_ind (RawTr.cons (inl (silentE_fair fm)) tr))
    :
    RawTr.is_fair_ind tr.
  Proof.
    ii. specialize (IND i). revert_until lt_succ_diag_r. pcofix CIH. i.
    remember (RawTr.cons (inl (silentE_fair fm)) tr) as ftr.
    punfold IND. revert R i ftr IND fm tr Heqftr.
    eapply (@pind3_acc _ _ _ _ (fun R i (ftr: @RawTr.t id R) =>
                                  forall (fm : fmap id) (tr : RawTr.t),
                                    ftr = RawTr.cons (inl (silentE_fair fm)) tr ->
                                    paco3
                                      (fun r0 =>
                                         pind3 (RawTr.__fair_ind r0) top3) r R i tr)).
    i. rename x0 into R, x1 into i, x2 into ftr. clarify.
    eapply pind3_unfold in PR.
    2:{ clear. ii. eapply RawTr.fair_ind_mon2; eauto. }
    inv PR.
    { pfold. destruct (fair_ind_cases i tr) as [NF | [MF | MS]]; des.
      { eapply pind3_fold. econs 1; eauto. }
      { destruct (fm i) eqn:FM.
        { punfold NOFAIL. inv NOFAIL. rewrite FM in SUCCESS; ss. rewrite FM in EMP; ss. }
        { punfold NOFAIL. inv NOFAIL. rewrite FM in SUCCESS; ss. pclearbot. clarify. }
        { punfold NOFAIL. inv NOFAIL. pclearbot. clarify. rewrite FM in EMP; ss. }
      }
      { destruct (fm i) eqn:FM.
        { punfold NOFAIL. inv NOFAIL. rewrite FM in SUCCESS; ss. rewrite FM in EMP; ss. }
        { punfold NOFAIL. inv NOFAIL. rewrite FM in SUCCESS; ss. pclearbot. clarify. }
        { punfold NOFAIL. inv NOFAIL. pclearbot. clarify. rewrite FM in EMP; ss. }
      }
    }
    { destruct (fair_ind_cases i tr) as [NF | [MF | MS]]; des.
      { clarify. }
      { hexploit IND; clear IND; eauto. intro IND. destruct IND as [PI IND].
        pfold. eapply pind3_mon_top. eauto. i. eapply RawTr.fair_ind_mon1. 2: eauto.
        i. pclearbot. left. eapply paco3_mon. eauto. ss.
      }
      { hexploit COI; clear COI; eauto. i. pclearbot. eapply paco3_mon; eauto. ss. }
    }
    { destruct (fair_ind_cases i tr) as [NF | [MF | MS]]; des.
      { pfold. eapply pind3_fold. econs 1. eauto. }
      { hexploit IND; clear IND; eauto. intro IND. destruct IND as [PI IND].
        pfold. eapply pind3_mon_top. eauto. i. eapply RawTr.fair_ind_mon1. 2: eauto.
        i. pclearbot. left. eapply paco3_mon. eauto. ss.
      }
      { hexploit COI; clear COI; eauto. i. pclearbot. eapply paco3_mon; eauto. ss. }
    }
    { pclearbot. eapply paco3_mon; eauto. ss. }
  Qed.

  Lemma fair_ind_red_obs
        R (tr: @RawTr.t id R) obs
        (IND: RawTr.is_fair_ind (RawTr.cons (inr obs) tr))
    :
    RawTr.is_fair_ind tr.
  Proof.
    ii. specialize (IND i). revert_until lt_succ_diag_r. pcofix CIH. i.
    remember (RawTr.cons (inr obs) tr) as ftr.
    punfold IND. revert R i ftr IND obs tr Heqftr.
    eapply (@pind3_acc _ _ _ _ (fun R i (ftr: @RawTr.t id R) =>
                                  forall (obs : obsE) (tr : RawTr.t),
                                    ftr = RawTr.cons (inr obs) tr ->
                                    paco3 (fun r0 => pind3 (RawTr.__fair_ind r0) top3) r R i tr)).
    i. rename x0 into R, x1 into i, x2 into ftr. clarify.
    eapply pind3_unfold in PR.
    2:{ clear. ii. eapply RawTr.fair_ind_mon2; eauto. }
    inv PR.
    { punfold NOFAIL. inv NOFAIL. pclearbot. pfold. eapply pind3_fold. econs 1; eauto. }
    { destruct (fair_ind_cases i tr) as [NF | [MF | MS]]; des.
      { clarify. }
      { hexploit IND; clear IND; eauto. intro IND. destruct IND as [PI IND].
        pfold. eapply pind3_mon_top. eauto. i. eapply RawTr.fair_ind_mon1. 2: eauto.
        i. pclearbot. left. eapply paco3_mon. eauto. ss.
      }
      { hexploit COI; clear COI; eauto. i. pclearbot. eapply paco3_mon; eauto. ss. }
    }
  Qed.

  Lemma fair_ind_red_tau
        R (tr: @RawTr.t id R)
        (IND: RawTr.is_fair_ind (RawTr.cons (inl silentE_tau) tr))
    :
    RawTr.is_fair_ind tr.
  Proof.
    ii. specialize (IND i). revert_until lt_succ_diag_r. pcofix CIH. i.
    remember (RawTr.cons (inl silentE_tau) tr) as ftr.
    punfold IND. revert R i ftr IND tr Heqftr.
    eapply (@pind3_acc _ _ _ _ (fun R i (ftr: @RawTr.t id R) =>
                                  forall tr : RawTr.t,
                                    ftr = RawTr.cons (inl silentE_tau) tr ->
                                    paco3 (fun r0 => pind3 (RawTr.__fair_ind r0) top3) r R i tr)).
    i. rename x0 into R, x1 into i, x2 into ftr. clarify.
    eapply pind3_unfold in PR.
    2:{ clear. ii. eapply RawTr.fair_ind_mon2; eauto. }
    inv PR.
    { punfold NOFAIL. inv NOFAIL. pclearbot. pfold. eapply pind3_fold. econs 1; eauto. }
    { destruct (fair_ind_cases i tr) as [NF | [MF | MS]]; des.
      { clarify. }
      { hexploit IND; clear IND; eauto. intro IND. destruct IND as [PI IND].
        pfold. eapply pind3_mon_top. eauto. i. eapply RawTr.fair_ind_mon1. 2: eauto.
        i. pclearbot. left. eapply paco3_mon. eauto. ss.
      }
      { hexploit COI; clear COI; eauto. i. pclearbot. eapply paco3_mon; eauto. ss. }
    }
  Qed.


  Lemma fair_ind_fair_ord
        R (tr: @RawTr.t id R) m
        (IND: RawTr.is_fair_ind tr)
        (ORD: forall i, ord_tr wft wft0 S i (m i) tr)
    :
    RawTr.fair_ord m tr.
  Proof.
    revert_until R. pcofix CIH. i. destruct tr.
    { pfold. econs. }
    { pfold. econs. }
    { pfold. econs. }
    { destruct hd as [silent | obs].
      2:{ pfold. econs. right. eapply CIH. eapply fair_ind_red_obs; eauto. i. eapply ord_tr_red_obs; eauto. }
      destruct silent as [| fm].
      { pfold. econs. right. eapply CIH. eapply fair_ind_red_tau; eauto. i. eapply ord_tr_red_tau; eauto. }
      hexploit fair_ind_red_fair; eauto. i. hexploit ord_tr_fair_case. eapply H. eauto. i; des.
      pfold. econs; eauto.
    }
  Qed.

  Lemma Ind_implies_Ord_fix
        R
        (tr: @RawTr.t id R)
        (IND: RawTr.is_fair_ind tr)
    :
    RawTr.fair_ord (fun i => tr2ord_i i tr) tr.
  Proof.
    eapply fair_ind_fair_ord; eauto. i. eapply tr2ord_i_spec; auto.
  Qed.

  Theorem Ind_implies_Ord
          R
          (tr: @RawTr.t id R)
          (IND: RawTr.is_fair_ind tr)
    :
    RawTr.is_fair_ord wft tr.
  Proof.
    eapply Ind_implies_Ord_fix in IND. eexists; eauto.
  Qed.

End EQUIV2.
