From sflib Require Import sflib.
From ITree Require Export ITree.

Export ITreeNotations.

Require Import Coq.Classes.RelationClasses.

From Fairness Require Import Axioms.
From Fairness Require Import FairBeh.
From Fairness Require Import pind_internal.
From Fairness Require Import pind3.
From Fairness Require Import SelectBeh.

From Paco Require Import paco.

Set Implicit Arguments.



Section AUX.

  (*TODO: move to Axioms*)
  Lemma not_ex_all_not_help
        A (P: A -> Prop)
        (NOT: ~ (exists a: A, P a))
    :
    <<NA: forall a, ~ P a>>.
  Proof.
    ii. eapply Classical_Pred_Type.not_ex_all_not in NOT. eauto.
  Qed.

  Ltac nean H := eapply not_ex_all_not_help in H; red in H.



  Context {Ident: ID}.

  Lemma fair_ind_cases
        i R (tr: @RawTr.t _ R)
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

  (* Lemma not_ex_next_fail_nofail *)
  (*       i R (tr: @RawTr.t _ R) *)
  (*       (NOT: ~ exists tl, RawTr.next_fail i tr tl) *)
  (*   : *)
  (*   RawTr.nofail i tr. *)
  (* Proof. *)
  (*   nean NOT. *)
  (*   revert_until i. pcofix CIH. i. *)
  (*   destruct tr. *)
  (*   { pfold. econs. } *)
  (*   { pfold. econs. } *)
  (*   { pfold. econs. } *)
  (*   { destruct hd as [silent | obs]. *)
  (*     2:{ pfold. econs. right. eapply CIH. i. specialize (NOT a). ii. eapply NOT; clear NOT. pfold. econs; eauto. } *)
  (*     destruct silent as [ | fm]. *)
  (*     { pfold. econs. right. eapply CIH. i. specialize (NOT a). ii. eapply NOT; clear NOT. pfold. econs; eauto. } *)
  (*     { destruct (fm i) eqn:FM. *)
  (*       { exfalso. eapply (NOT tr); clear NOT. pfold. econs 1. auto. } *)
  (*       { pfold. econs 7. rewrite FM; ss. right. eapply CIH. i. specialize (NOT a). ii. eapply NOT; clear NOT. pfold. econs; eauto. } *)
  (*       { pfold. econs 4. rewrite FM; ss. right. eapply CIH. i. specialize (NOT a). ii. eapply NOT; clear NOT. pfold. econs; eauto. } *)
  (*     } *)
  (*   } *)
  (* Qed. *)

  (* Inductive must_fail i R: (@RawTr.t _ R) -> Prop := *)
  (* | must_fail_fail *)
  (*     fm tl *)
  (*     (FAIL: Flag.fail = fm i) *)
  (*   : *)
  (*   must_fail i (RawTr.cons (inl (silentE_fair fm)) tl) *)
  (* | must_fail_obs *)
  (*     obs tl *)
  (*     (MUST: must_fail i tl) *)
  (*   : *)
  (*   must_fail i (RawTr.cons (inr obs) tl) *)
  (* | must_fail_tau *)
  (*     tl *)
  (*     (MUST: must_fail i tl) *)
  (*   : *)
  (*   must_fail i (RawTr.cons (inl silentE_tau) tl) *)
  (* | must_fail_emp *)
  (*     fm tl *)
  (*     (EMP: Flag.emp = fm i) *)
  (*     (MUST: must_fail i tl) *)
  (*   : *)
  (*   must_fail i (RawTr.cons (inl (silentE_fair fm)) tl) *)
  (* (* | must_fail_success *) *)
  (* (*     fm tl *) *)
  (* (*     (SUCCESS: Flag.success = fm i) *) *)
  (* (*     (MUST: must_fail i tl) *) *)
  (* (*   : *) *)
  (* (*   must_fail i (RawTr.cons (inl (silentE_fair fm)) tl) *) *)
  (* . *)

  (* Lemma must_fail_not_nofail *)
  (*       i R (tr: @RawTr.t _ R) *)
  (*       (MUST: must_fail i tr) *)
  (*   : *)
  (*   ~ RawTr.nofail i tr. *)
  (* Proof. *)
  (*   induction MUST. *)
  (*   { ii. punfold H. inv H. rewrite <- FAIL in SUCCESS; ss. rewrite <- FAIL in EMP; ss. } *)
  (*   { ii. apply IHMUST; clear IHMUST. punfold H. inv H. pclearbot. auto. } *)
  (*   { ii. apply IHMUST; clear IHMUST. punfold H. inv H. pclearbot. auto. } *)
  (*   { ii. apply IHMUST; clear IHMUST. punfold H. inv H. rewrite <- EMP in SUCCESS; ss. *)
  (*     pclearbot. auto. } *)
  (*   (* { ii. apply IHMUST; clear IHMUST. punfold H. inv H. *) *)
  (*   (*   2:{ rewrite <- EMP in SUCCESS; ss. } *) *)
  (*   (*   pclearbot. auto. } *) *)
  (* Qed. *)

  (* Lemma not_must_fail_nofail *)
  (*       i R (tr: @RawTr.t _ R) *)
  (*       (NMUST: ~ must_fail i tr) *)
  (*   : *)
  (*   RawTr.nofail i tr. *)
  (* Proof. *)
  (*   revert_until R. pcofix CIH. i. destruct tr. *)
  (*   { pfold. econs. } *)
  (*   { pfold. econs. } *)
  (*   { pfold. econs. } *)
  (*   { destruct hd as [silent | obs]. *)
  (*     2:{ pfold. econs. right. eapply CIH. *)
  (*         ii. eapply NMUST. econs. auto. *)
  (*     } *)
  (*     destruct silent as [| fm]. *)
  (*     { pfold. econs. right. eapply CIH. *)
  (*       ii. eapply NMUST. econs. auto. *)
  (*     } *)
  (*     { destruct (fm i) eqn:FM. *)
  (*       { exfalso. eapply NMUST. econs; eauto. } *)
  (*       { pfold. econs 7. auto. right. eapply CIH. *)
  (*         ii. eapply NMUST. econs 4; auto. *)
  (*       } *)
  (*       { pfold. econs 4. ss. right. eapply CIH. ii. eapply NMUST. econs 5; auto. } *)
  (*     } *)
  (*   } *)
  (* Qed. *)

  (* Lemma must_fail_or_nofail *)
  (*       i R (tr: @RawTr.t Ident R) *)
  (*   : *)
  (*   (must_fail i tr) \/ (RawTr.nofail i tr). *)
  (* Proof. *)
  (*   destruct (classic (must_fail i tr)) as [MUST | NM]; auto. *)
  (*   eapply not_must_fail_nofail in NM. auto. *)
  (* Qed. *)


  Variable wft: WF.
  Variable wft0: wft.(T).
  Variable S: wft.(T) -> wft.(T).
  Hypothesis lt_succ_diag_r: forall (t: wft.(T)), wft.(lt) t (S t).

  (* fix an unique ordering for the first list of fail *)
  Inductive ord_tr (i: id) R: wft.(T) -> (@RawTr.t _ R) -> Prop :=
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
      (* (NNF: ~ RawTr.nofail i tl) *)
      (ORD: ord_tr i o tl)
    :
    ord_tr i (S o) (RawTr.cons (inl (silentE_fair fm)) tl)
  .

  (* Inductive ord_tr (i: id) R: wft.(T) -> (@RawTr.t _ R) -> Prop := *)
  (* (* base cases: no more fail *) *)
  (* | ord_tr_nofail *)
  (*     tr *)
  (*     (NOFAIL: RawTr.nofail i tr) *)
  (*   : *)
  (*   ord_tr i wft0 tr *)

  (* (* inductive cases *) *)
  (* | ord_tr_obs *)
  (*     o (obs: obsE) tl next *)
  (*     (NEXT: RawTr.next_fail i tl next) *)
  (*     (ORD: ord_tr i o next) *)
  (*   : *)
  (*   ord_tr i (S o) (RawTr.cons (inr obs) tl) *)
  (* | ord_tr_tau *)
  (*     o tl next *)
  (*     (NEXT: RawTr.next_fail i tl next) *)
  (*     (ORD: ord_tr i o next) *)
  (*   : *)
  (*   ord_tr i (S o) (RawTr.cons (inl silentE_tau) tl) *)
  (* | ord_tr_fair_emp *)
  (*     o fmap tl next *)
  (*     (EMP: Flag.emp = (fmap i)) *)
  (*     (NEXT: RawTr.next_fail i tl next) *)
  (*     (ORD: ord_tr i o next) *)
  (*   : *)
  (*   ord_tr i (S o) (RawTr.cons (inl (silentE_fair fmap)) tl) *)
  (* | ord_tr_fair_fail *)
  (*     o fmap tl *)
  (*     (FAIL: Flag.fail = (fmap i)) *)
  (*     (TL: ord_tr i o tl) *)
  (*   : *)
  (*   ord_tr i (S o) (RawTr.cons (inl (silentE_fair fmap)) tl) *)
  (* . *)


  (* Lemma not_must_fail_all_next_fail *)
  (*       i R (tr: @RawTr.t _ R) *)
  (*       (NMUST: ~ must_fail i tr) *)
  (*       (NEXT: exists next, RawTr.next_fail i tr next) *)
  (*   : *)
  (*   forall raw, RawTr.next_fail i tr raw. *)
  (* Proof. *)
  (*   i. revert_until R. pcofix CIH. i. destruct tr. *)
  (*   { punfold NEXT. inv NEXT. } *)
  (*   { punfold NEXT. inv NEXT. } *)
  (*   { punfold NEXT. inv NEXT. } *)
  (*   { destruct hd as [silent | obs]. *)
  (*     2:{ pfold. econs. right. eapply CIH. *)
  (*         { ii. eapply NMUST. econs. auto. } *)
  (*         { punfold NEXT. inv NEXT. pclearbot. eauto. } *)
  (*     } *)
  (*     destruct silent as [| fm]. *)
  (*     { pfold. econs. right. eapply CIH. *)
  (*       { ii. eapply NMUST. econs. auto. } *)
  (*       { punfold NEXT. inv NEXT. pclearbot. eauto. } *)
  (*     } *)
  (*     { destruct (fm i) eqn:FM. *)
  (*       { exfalso. eapply NMUST. econs; eauto. } *)
  (*       { pfold. econs. auto. right. eapply CIH. *)
  (*         { ii. eapply NMUST. econs 4; auto. } *)
  (*         { punfold NEXT. inv NEXT. rewrite FM in FAIL; ss. pclearbot. eauto. } *)
  (*       } *)
  (*       { exfalso. punfold NEXT. inv NEXT. rewrite FM in FAIL; ss. rewrite FM in EMP; ss. } *)
  (*     } *)
  (*   } *)
  (* Qed. *)

  (* Lemma nofail_all_ord_tr *)
  (*       i R (tr: @RawTr.t _ R) *)
  (*       (NOFAIL: RawTr.nofail i tr) *)
  (*   : *)
  (*   forall o, ord_tr i o tr. *)
  (* Proof. *)
  (*   i. econs 1. auto. *)
  (* Qed. *)

  Lemma nofail_ex_ord_tr
        i R (tr: @RawTr.t _ R)
        (NOFAIL: RawTr.nofail i tr)
    :
    exists o, ord_tr i o tr.
  Proof.
    exists wft0. econs 1. auto.
  Qed.


  (* Variant _coind_fail i *)
  (*         (coind_fail: forall R, (@RawTr.t _ R) -> Prop) *)
  (*         R *)
  (*   : *)
  (*   (@RawTr.t _ R) -> Prop := *)
  (*   | coind_fail_intro *)
  (*       tr next *)
  (*       (NEXT: RawTr.next_fail i tr next) *)
  (*       (FAIL: coind_fail R next) *)
  (*     : *)
  (*     _coind_fail i coind_fail tr *)
  (* . *)

  (* Lemma coind_fail_mon i: monotone2 (_coind_fail i). *)
  (* Proof. ii. inv IN. econs; eauto. Qed. *)

  (* Definition coind_fail i: forall R, (@RawTr.t _ R) -> Prop := paco2 (_coind_fail i) bot2. *)

  (* Local Hint Constructors _coind_fail: core. *)
  (* Local Hint Unfold coind_fail: core. *)
  (* Local Hint Resolve coind_fail_mon: paco. *)



  (* Lemma not_ex_ord_tr_coind_fail *)
  (*       i R (tr: @RawTr.t _ R) *)
  (*       (NOT: ~ exists o, ord_tr i o tr) *)
  (*   : *)
  (*   coind_fail i tr. *)
  (* Proof. *)
  (*   nean NOT. *)
  (*   revert_until i. pcofix CIH. i. *)
  (*   destruct tr. *)
  (*   { exfalso. eapply (NOT wft0). econs. pfold. econs. } *)
  (*   { exfalso. eapply (NOT wft0). econs. pfold. econs. } *)
  (*   { exfalso. eapply (NOT wft0). econs. pfold. econs. } *)
  (*   { destruct hd as [silent | obs]. *)
  (*     2:{ destruct (classic (exists next, RawTr.next_fail i tr next)) as [NEXT | NONE]. *)
  (*         { des. destruct (classic (exists o, ord_tr i o next)) as [ORD | NONE]. *)
  (*           { des. exfalso. eapply (NOT (o)); clear NOT. econs 2; eauto. } *)
  (*           nean NONE. *)
  (*           pfold. econs. *)
  (*           { pfold. econs. left. eauto. } *)
  (*           right. eapply CIH. eauto. *)
  (*         } *)
  (*         { eapply not_ex_next_fail_nofail in NONE. *)
  (*           match goal with *)
  (*           | H: forall a, ~ ord_tr _ _ ?tr2 |- _ => assert (NONE2: RawTr.nofail i tr2) *)
  (*           end. *)
  (*           { pfold. econs. eauto. } *)
  (*           eapply nofail_ex_ord_tr in NONE2. des. specialize (NOT o). clarify. *)
  (*         } *)
  (*     } *)
  (*     destruct silent as [ | fm]. *)
  (*     { destruct (classic (exists next, RawTr.next_fail i tr next)) as [NEXT | NONE]. *)
  (*       { des. destruct (classic (exists o, ord_tr i o next)) as [ORD | NONE]. *)
  (*         { des. exfalso. eapply (NOT (o)); clear NOT. econs 3; eauto. } *)
  (*         nean NONE. *)
  (*         pfold. econs. *)
  (*         { pfold. econs. left. eauto. } *)
  (*         right. eapply CIH. eauto. *)
  (*       } *)
  (*       { eapply not_ex_next_fail_nofail in NONE. *)
  (*         match goal with *)
  (*         | H: forall a, ~ ord_tr _ _ ?tr2 |- _ => assert (NONE2: RawTr.nofail i tr2) *)
  (*         end. *)
  (*         { pfold. econs. eauto. } *)
  (*         eapply nofail_ex_ord_tr in NONE2. des. specialize (NOT o). clarify. *)
  (*       } *)
  (*     } *)
  (*     { destruct (fm i) eqn:FM. *)
  (*       { destruct (classic (exists o, ord_tr i o tr)) as [ORD | NONE]. *)
  (*         { des. exfalso. eapply (NOT (S o)); clear NOT. econs 5; eauto. } *)
  (*         nean NONE. *)
  (*         pfold. econs. *)
  (*         { pfold. econs. eauto. } *)
  (*         right. eapply CIH. eauto. *)
  (*       } *)
  (*       { destruct (classic (exists next, RawTr.next_fail i tr next)) as [NEXT | NONE]. *)
  (*         { des. destruct (classic (exists o, ord_tr i o next)) as [ORD | NONE]. *)
  (*           { des. exfalso. eapply (NOT (o)); clear NOT. econs 4; eauto. } *)
  (*           nean NONE. *)
  (*           pfold. econs. *)
  (*           { pfold. econs 4; eauto. } *)
  (*           right. eapply CIH. eauto. *)
  (*         } *)
  (*         { eapply not_ex_next_fail_nofail in NONE. *)
  (*           match goal with *)
  (*           | H: forall a, ~ ord_tr _ _ ?tr2 |- _ => assert (NONE2: RawTr.nofail i tr2) *)
  (*           end. *)
  (*           { pfold. econs 7; eauto. } *)
  (*           eapply nofail_ex_ord_tr in NONE2. des. specialize (NOT o). clarify. *)
  (*         } *)
  (*       } *)
  (*       { exfalso. eapply (NOT wft0). econs. pfold. econs 4. auto. } *)
  (*     } *)
  (*   } *)
  (* Qed. *)

  (* Lemma must_fail_ex_next *)
  (*       i R (tr: @RawTr.t _ R) *)
  (*       (MUST: must_fail i tr) *)
  (*   : *)
  (*   exists next, RawTr.next_fail i tr next. *)
  (* Proof. *)
  (*   induction MUST. *)
  (*   { exists tl. pfold. econs 1. auto. } *)
  (*   { des. eexists. pfold. econs; eauto. } *)
  (*   { des. eexists. pfold. econs; eauto. } *)
  (*   { des. eexists. pfold. econs 4; eauto. } *)
  (* Qed. *)



  Lemma fair_ind_ex_ord_tr
        i R (tr: @RawTr.t _ R)
        (IND: RawTr.is_fair_ind tr)
    :
    exists o, ord_tr i o tr.
  Proof.
    specialize (IND i). punfold IND.
    revert R i tr IND.
    eapply (@pind3_acc _ _ _ _ (fun R i (tr: @RawTr.t Ident R) => (exists o, ord_tr i o tr))).
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

  (** this should not hold; ord_tr only gives ordering up to the first success *)
  (* Lemma ex_ord_tr_fair_ind *)
  (*       i R (tr: @RawTr.t _ R) *)
  (*       (ORD: exists o, ord_tr i o tr) *)
  (*   : *)
  (*   RawTr.fair_ind i tr. *)
  (* Proof. *)
  (*   des. revert_until R. pcofix CIH. i. pfold. *)
  (*   induction ORD. *)
  (*   { eapply pind3_fold. econs 1; eauto. } *)
  (*   { eapply pind3_fold. destruct tr. *)
  (*     { econs 1. pfold. econs. } *)
  (*     { econs 1. pfold. econs. } *)
  (*     { econs 1. pfold. econs. } *)
  (*     { destruct hd as [sil | obs]. *)
  (*       { destruct sil as [| fm]. *)
  (*         { econs 3. *)
  (*           { intro NF; apply NNF. pfold. econs; eauto. } *)
  (*           { i. right. eapply CIH. econs 2; eauto. intro NF; apply NNF. pfold. econs; eauto. } *)
  (*           i. exfalso. inv MS. apply RawTr.must_success_not_fail in MUSTS. clarify. *)
  (*         } *)
  (*         destruct (fm i) eqn: FM. *)
  (*         { exfalso. inv MS. rewrite FM in SUCCESS; ss. rewrite FM in EMP; ss. } *)
  (*         { econs 4; auto. *)
  (*           { intro NF; apply NNF. pfold. econs 7; eauto. } *)
  (*           { i. right. eapply CIH. econs 2; eauto. intro NF; apply NNF. pfold. econs 7; eauto. } *)
  (*           i. exfalso. inv MS. rewrite FM in SUCCESS; ss. apply RawTr.must_success_not_fail in MUSTS. clarify. *)
  (*         } *)
  (*         { econs 6; auto. right. eapply CIH.  *)
  (* Qed. *)

End AUX.
(* #[export] Hint Constructors _coind_fail: core. *)
(* #[export] Hint Unfold coind_fail: core. *)
(* #[export] Hint Resolve coind_fail_mon: paco. *)



Section EQUIV.

  Context {Ident: ID}.
  Hypothesis ID_DEC: forall (i0 i1: Ident.(id)), {i0 = i1} + {i0 <> i1}.

  Variable wft: WF.
  Variable wft0: wft.(T).
  Variable S: wft.(T) -> wft.(T).
  Hypothesis lt_succ_diag_r: forall (t: wft.(T)), wft.(lt) t (S t).
  Hypothesis WFTR: Transitive wft.(lt).

  Theorem Ord_implies_Ind
          R
          (tr: @RawTr.t Ident R)
          (ORD: RawTr.is_fair_ord wft tr)
    :
    RawTr.is_fair tr.
  Proof.
    ii. unfold RawTr.is_fair_ord in ORD. des.
    revert_until WFTR. pcofix CIH1. i.
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


  (*TODO*)
  (* Lemma must_fail_fair_ind *)
  (*       i R r (tr: @RawTr.t _ R) *)
  (*       (MUST: must_fail i tr) *)
  (*       (IND: pind3 (RawTr.__fair_ind (upaco3 (fun r0 => pind3 (RawTr.__fair_ind r0) top3) r)) top3 R i tr) *)
  (*   : *)
  (*   exists next, (RawTr.next_fail i tr next) /\ *)
  (*             (pind3 (RawTr.__fair_ind (upaco3 (fun r0 => pind3 (RawTr.__fair_ind r0) top3) r)) top3 R i next). *)
  (* Proof. *)
  (*   eapply pind3_unfold in IND. *)
  (*   2:{ ii. eapply RawTr.fair_ind_mon2; eauto. } *)
  (*   inv IND. *)
  (*   { hexploit must_fail_not_nofail; eauto. i; clarify. } *)
  (*   { destruct IND0 as [PI IND]. esplits; eauto. pfold. econs. eauto. } *)
  (*   { destruct IND0 as [PI IND]. esplits; eauto. pfold. econs. eauto. } *)
  (*   { destruct IND0 as [PI IND]. esplits; eauto. pfold. econs 4; eauto. } *)
  (*   { destruct IND0 as [PI IND]. esplits; eauto. } *)
  (*   { inv MUST. rewrite <- SUCCESS in FAIL; ss. rewrite <- SUCCESS in EMP; ss. } *)
  (* Qed. *)

  Theorem Fair_implies_Ind
          R
          (tr: @RawTr.t Ident R)
          (IND: RawTr.is_fair tr)
    :
    RawTr.is_fair_ind tr.
  Proof.
    ii. specialize (IND i). depgen tr. pcofix CIH. i.
    punfold IND. pfold. revert R i tr IND CIH.
    eapply (@pind3_acc _ _ _ _ (fun R i (tr: @RawTr.t Ident R) =>
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


  (* Lemma fair_ord_ex_lt *)
  (*       R i m *)
  (*       (tr: @RawTr.t Ident R) *)
  (*       (ORD: RawTr.fair_ord (wf:=wft) m tr) *)
  (*       (MUST: must_fail i tr) *)
  (*   : *)
  (*   exists o, (lt wft o (m i)). *)
  (* Proof. *)
  (*   depgen m. induction MUST; i. *)
  (*   { punfold ORD. inv ORD. specialize (FAIR i). rewrite <- FAIL in FAIR. eauto. } *)
  (*   { punfold ORD. inv ORD. pclearbot. eauto. } *)
  (*   { punfold ORD. inv ORD. pclearbot. eauto. } *)
  (*   { punfold ORD. inv ORD. pclearbot. specialize (FAIR i). rewrite <- EMP in FAIR. *)
  (*     destruct FAIR as [EQ | LT]. *)
  (*     - rewrite <- EQ. eauto. *)
  (*     - eauto. *)
  (*   } *)
  (* Qed. *)

End EQUIV.


(* (*TODO: move to Flag.t*) *)
(* Lemma ff_eq_dec: forall (f1 f2: Flag.t), {f1 = f2} + {f1 <> f2}. *)
(* Proof. *)
(*   i. destruct f1; destruct f2; ss; eauto. all: right; ss. *)
(* Qed. *)



Section EQUIV2.

  Context {Ident: ID}.
  (* Hypothesis ID_DEC: forall (i0 i1: Ident.(id)), {i0 = i1} + {i0 <> i1}. *)

  Variable wft: WF.
  Variable wft0: wft.(T).
  (* Hypothesis WFTR: Transitive wft.(lt). *)

  Variable S: wft.(T) -> wft.(T).
  Hypothesis lt_succ_diag_r: forall (t: wft.(T)), wft.(lt) t (S t).
  Hypothesis S_inj: forall o1 o2, (S o1 = S o2) -> o1 = o2.

  Variable P: wft.(T) -> wft.(T).
  Hypothesis wft0_zero_P: P wft0 = wft0.
  Hypothesis wft0_zero_S: forall o, S o <> wft0.
  Hypothesis P_inj_or_zero: forall o1 o2, (P o1 = P o2) -> ((o1 = o2) \/ (o1 = wft0) \/ (o2 = wft0)).
  Hypothesis SP: forall o, (o <> wft0) -> (S (P o)) = o.
  Hypothesis PS: forall o, (P (S o)) = o.


  Lemma ord_tr_red_obs
        R i obs (tr: @RawTr.t Ident R) o
        (ORD: ord_tr wft wft0 S i o (RawTr.cons (inr obs) tr))
    :
    ord_tr wft wft0 S i o tr.
  Proof.
    remember (RawTr.cons (inr obs) tr) as otr. move ORD before PS. revert_until ORD. induction ORD; i; ss; clarify.
    { punfold NOFAIL. inv NOFAIL. pclearbot. econs 1; auto. }
    { econs 2.
      - intro NF; apply NNF. pfold. econs. auto.
      - inv MS. auto.
    }
  Qed.

  Lemma ord_tr_red_tau
        R i (tr: @RawTr.t Ident R) o
        (ORD: ord_tr wft wft0 S i o (RawTr.cons (inl silentE_tau) tr))
    :
    ord_tr wft wft0 S i o tr.
  Proof.
    remember (RawTr.cons (inl silentE_tau) tr) as otr. move ORD before PS. revert_until ORD. induction ORD; i; ss; clarify.
    { punfold NOFAIL. inv NOFAIL. pclearbot. econs 1; auto. }
    { econs 2.
      - intro NF; apply NNF. pfold. econs. auto.
      - inv MS. auto.
    }
  Qed.


  Definition fair_update_i (o: wft.(T)) (f: Flag.t): wft.(T) :=
    match f with
    | Flag.success => wft0
    | Flag.emp => o
    | Flag.fail => (P o)
    end.

  (* Definition update_imap (m: imap wft) (fm: fmap): imap wft := *)
  (*   fun i => match (fm i) with *)
  (*         | Flag.success => wft0 *)
  (*         | Flag.emp => (m i) *)
  (*         | Flag.fail => (P (m i)) *)
  (*         end. *)

  (* Lemma ord_tr_red_fair *)
  (*       R i fm (tr: @RawTr.t Ident R) o *)
  (*       (ORD: ord_tr wft wft0 S i o (RawTr.cons (inl (silentE_fair fm)) tr)) *)
  (*   : *)
  (*   ord_tr wft wft0 S i (fair_update_i o (fm i)) tr. *)
  (* Proof. *)
  (*   remember (RawTr.cons (inl (silentE_fair fm)) tr) as otr. move ORD before PS. revert_until ORD. induction ORD; i; ss; clarify. *)
  (*   { punfold NOFAIL. inv NOFAIL; pclearbot. *)
  (*     - rewrite SUCCESS. ss. econs 1; eauto. *)
  (*     - rewrite EMP. ss. econs 1; eauto. *)
  (*   } *)
  (*   { remember (RawTr.cons (inl (silentE_fair fm)) tr0) as otr. move MS before PS. revert_until MS. induction MS; i; ss; clarify. *)
  (*     { rewrite SUCCESS; ss. econs 2. *)



  (*     econs 2. *)
  (*     - intro NF; apply NNF. pfold. econs. auto. *)
  (*     - inv MS. auto. *)
  (*   } *)
  (* Qed. *)


  (* Lemma fair_ind_fair_ord *)
  (*       R (tr: @RawTr.t Ident R) m *)
  (*       (ORD: forall i, ord_tr wft wft0 S i (m i) tr) *)
  (*   : *)
  (*   RawTr.fair_ord m tr. *)
  (* Proof. *)
  (*   revert_until R. pcofix CIH. i. destruct tr. *)
  (*   { pfold. econs. } *)
  (*   { pfold. econs. } *)
  (*   { pfold. econs. } *)
  (*   { destruct hd as [silent | obs]. *)
  (*     2:{ pfold. econs. right. eapply CIH. i. eapply ord_tr_red_obs; eauto. } *)
  (*     destruct silent as [| fm]. *)
  (*     { pfold. econs. right. eapply CIH. i. eapply ord_tr_red_tau; eauto. } *)
  (*     pfold. econs. *)
  (*     2:{ right. eapply CIH. *)


  Lemma inhabited_tr_ord: inhabited (T wft).
  Proof. econs. exact wft0. Qed.

  Definition tr2ord_i {R} i (tr: (@RawTr.t _ R)): wft.(T) :=
    epsilon _ (inhabited_tr_ord) (fun o => ord_tr wft wft0 S i o tr).

  Theorem tr2ord_i_spec
          i R (tr: @RawTr.t _ R)
          (IND: RawTr.is_fair_ind tr)
    :
    ord_tr wft wft0 S i (tr2ord_i i tr) tr.
  Proof.
    unfold tr2ord_i, epsilon. unfold Epsilon.epsilon, proj1_sig. des_ifs. clear Heq.
    hexploit o; clear o. eapply fair_ind_ex_ord_tr; eauto. intros ORD. auto.
  Qed.

  (* Lemma next_ord_tr *)
  (*       i R (tr next: @RawTr.t _ R) o *)
  (*       (MUST: must_fail i tr) *)
  (*       (NEXT: RawTr.next_fail i tr next) *)
  (*       (ORD: ord_tr wft wft0 S i o next) *)
  (*   : *)
  (*   ord_tr wft wft0 S i (S o) tr. *)
  (* Proof. *)
  (*   destruct tr. *)
  (*   { punfold NEXT. inv NEXT. } *)
  (*   { punfold NEXT. inv NEXT. } *)
  (*   { punfold NEXT. inv NEXT. } *)
  (*   { destruct hd as [sil | obs]. *)
  (*     2:{ inv MUST. econs 2; eauto. punfold NEXT. inv NEXT. pclearbot. eauto. } *)
  (*     destruct sil as [| fm]. *)
  (*     { inv MUST. econs 3; eauto. punfold NEXT. inv NEXT. pclearbot. eauto. } *)
  (*     punfold NEXT. inv NEXT. *)
  (*     { econs 5; eauto. } *)
  (*     { inv MUST. rewrite <- EMP in FAIL; ss. pclearbot. econs 4; eauto. } *)
  (*   } *)
  (* Qed. *)


  Lemma ord_tr_nofail_fix
        R i o (tr: @RawTr.t _ R)
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
        R i o (tr: @RawTr.t _ R)
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

  (* Lemma must_fail_next_fail_eq *)
  (*       R i (tr next1 next2: @RawTr.t _ R) *)
  (*       (NEXT1: RawTr.next_fail i tr next1) *)
  (*       (NEXT2: RawTr.next_fail i tr next2) *)
  (*       (MUST: must_fail i tr) *)
  (*   : *)
  (*   next1 = next2. *)
  (* Proof. *)
  (*   depgen next2. depgen next1. induction MUST; i. *)
  (*   { punfold NEXT1. inv NEXT1. *)
  (*     2:{ rewrite <- FAIL in EMP; ss. } *)
  (*     punfold NEXT2. inv NEXT2. *)
  (*     2:{ rewrite <- FAIL in EMP; ss. } *)
  (*     ss. *)
  (*   } *)
  (*   { punfold NEXT1. inv NEXT1. punfold NEXT2. inv NEXT2. pclearbot. eauto. } *)
  (*   { punfold NEXT1. inv NEXT1. punfold NEXT2. inv NEXT2. pclearbot. eauto. } *)
  (*   { punfold NEXT1. inv NEXT1. rewrite <- EMP in FAIL; ss. *)
  (*     punfold NEXT2. inv NEXT2. rewrite <- EMP in FAIL; ss. pclearbot. eauto. } *)
  (* Qed. *)

  Lemma ord_tr_eq
        R i o1 o2 (tr: @RawTr.t _ R)
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
      all: try (punfold NOFAIL; inv NOFAIL; eapply must_fail_not_nofail in MUST;
                pclearbot; clarify).
      hexploit must_fail_next_fail_eq. 3: eauto. eapply NEXT. eapply NEXT0. i; clarify.
      f_equal. eauto.
    }
    { inv ORD2; eauto.
      all: try (punfold NOFAIL; inv NOFAIL; eapply must_fail_not_nofail in MUST;
                pclearbot; clarify).
      hexploit must_fail_next_fail_eq. 3: eauto. eapply NEXT. eapply NEXT0. i; clarify.
      f_equal. eauto.
    }
    { inv ORD2; eauto.
      all: try (punfold NOFAIL; inv NOFAIL; eapply must_fail_not_nofail in MUST;
                pclearbot; clarify).
      rewrite <- EMP in SUCCESS; ss.
      2:{ rewrite <- EMP in FAIL; ss. }
      hexploit must_fail_next_fail_eq. 3: eauto. eapply NEXT. eapply NEXT0. i; clarify.
      f_equal. eauto.
    }
    { inv ORD2; eauto.
      { punfold NOFAIL. inv NOFAIL. rewrite <- FAIL in SUCCESS; ss. rewrite <- FAIL in EMP; ss. }
      rewrite <- FAIL in EMP; ss.
      f_equal. eauto.
    }
  Qed.


  (* Definition update_imap (m: imap wft) (fm: fmap): imap wft := *)
  (*   fun i => match (fm i) with *)
  (*         | Flag.success => wft0 *)
  (*         | Flag.emp => (m i) *)
  (*         | Flag.fail => (P (m i)) *)
  (*         end. *)

  (* Definition fair_update_i (o1 o2: wft.(T)) (f: Flag.t): Prop := *)
  (*   match f with *)
  (*   | Flag.fail => wft.(lt) o2 o1 *)
  (*   | Flag.emp => wft.(le) o2 o1 *)
  (*   | Flag.success => True *)
  (*   end. *)

  (* Lemma ord_tr_fair_case_i *)
  (*       R i (tr: @RawTr.t _ R) fm m *)
  (*       (ORD: ord_tr wft wft0 S i (m i) (RawTr.cons (inl (silentE_fair fm)) tr)) *)
  (*   : *)
  (*   exists o, (fair_update_i (m i) o (fm i)) /\ (ord_tr wft wft0 S i o tr). *)
  (*   exists m0, (fair_update m m0 fm) /\ (forall i : id, ord_tr wft wft0 S i (m0 i) tr). *)
  (* Proof. *)

  Lemma ord_tr_fair_case
        R (tr: @RawTr.t _ R) fm m
        (IND: RawTr.is_fair_ind tr)
        (ORD: forall i : id, ord_tr wft wft0 S i (m i) (RawTr.cons (inl (silentE_fair fm)) tr))
    :
    exists m0, (fair_update m m0 fm) /\ (forall i : id, ord_tr wft wft0 S i (m0 i) tr).
  Proof.
    exists (fun i => tr2ord_i i tr). split.
    2:{ i. eapply tr2ord_i_spec. eauto. }
    ii. specialize (ORD i). des_ifs.
    { inv ORD.
      { punfold NOFAIL. inv NOFAIL. rewrite Heq in SUCCESS; ss. rewrite Heq in EMP; ss. }
      { rewrite Heq in EMP; ss. }
      { assert (tr2ord_i i tr = o).
        { eapply ord_tr_eq; eauto. eapply tr2ord_i_spec; eauto. }
        rewrite H; auto.
      }
    }
    { inv ORD.
      { punfold NOFAIL. inv NOFAIL. rewrite Heq in SUCCESS; ss. pclearbot.
        assert (tr2ord_i i tr = wft0).
        { eapply ord_tr_nofail_fix; eauto. eapply tr2ord_i_spec; eauto. }
        rewrite H0; rewrite <- H; left; auto.
      }
      { assert (tr2ord_i i tr = S o).
        { hexploit next_ord_tr; eauto. i. eapply ord_tr_eq; eauto. eapply tr2ord_i_spec; eauto. }
        rewrite H; left; auto.
      }
      { rewrite Heq in FAIL; ss. }
    }
  Qed.

  Lemma all_ord_tr_is_fair_ind
        R (tr: @RawTr.t Ident R) m
        (ORD: forall i, ord_tr wft wft0 S i (m i) tr)
    :
    RawTr.is_fair_ind tr.
  Proof.
    ii. specialize (ORD i). eapply ex_ord_tr_fair_ind; eauto.
  Qed.


  Lemma fair_ind_red_cons
        R (tr: @RawTr.t _ R) fm
        (IND: RawTr.is_fair_ind (RawTr.cons (inl (silentE_fair fm)) tr))
    :
    RawTr.is_fair_ind tr.
  Proof.
    ii. specialize (IND i). revert_until PS. pcofix CIH. i.
    remember (RawTr.cons (inl (silentE_fair fm)) tr) as ftr.
    punfold IND. revert R i ftr IND fm tr Heqftr.
    eapply (@pind3_acc _ _ _ _ (fun R i (ftr: @RawTr.t Ident R) =>
                                  forall (fm : fmap) (tr : RawTr.t),
                                    ftr = RawTr.cons (inl (silentE_fair fm)) tr ->
                                    paco3
                                      (fun r0 =>
                                         pind3 (RawTr.__fair_ind r0) top3) r R i tr)).
    i. rename x0 into R, x1 into i, x2 into ftr. clarify.
    eapply pind3_unfold in PR.
    2:{ clear. ii. eapply RawTr.fair_ind_mon2; eauto. }
    inv PR.
    { punfold NOFAIL. inv NOFAIL.
      -
        (*TODO*)
    


  Lemma fair_ind_fair_ord
        R (tr: @RawTr.t Ident R) m
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
      2:{ pfold. econs. right. eapply CIH.
          2:{ i. specialize (ORD i). inv ORD.
              - punfold NOFAIL. inv NOFAIL. pclearbot. econs 1; eauto.
              - eapply next_ord_tr; eauto.
          }
          eapply all_ord_tr_is_fair_ind.
          { i. specialize (ORD i). inv ORD.
            - punfold NOFAIL. inv NOFAIL. pclearbot. econs 1; eauto.
            - rewrite <- H0. eapply next_ord_tr; eauto.
          }
      }
      destruct silent as [| fm].
      { pfold. econs. right. eapply CIH.
        2:{ i. specialize (ORD i). inv ORD.
            - punfold NOFAIL. inv NOFAIL. pclearbot. econs 1; eauto.
            - eapply next_ord_tr; eauto.
        }
        eapply all_ord_tr_is_fair_ind.
        { i. specialize (ORD i). inv ORD.
          - punfold NOFAIL. inv NOFAIL. pclearbot. econs 1; eauto.
          - rewrite <- H0. eapply next_ord_tr; eauto.
        }
      }
      { hexploit ord_tr_fair_case.
        2: eauto.
        2:{ i; des. pfold. econs; eauto. right. eapply CIH; eauto.

        hexploit ord_tr_fair_ev_update. eauto. i.
        hexploit ord_tr_fair_case; eauto.
        { eapply all_ord_tr_is_fair_ind; eauto. i. specialize (ORD i).


  (* Lemma tr2ord_i_red_obs *)
  (*       i R (tr: @RawTr.t _ R) obs *)
  (*       (IND : RawTr.is_fair_ind (RawTr.cons (inr obs) tr)) *)
  (*   : *)
  (*   tr2ord_i i (RawTr.cons (inr obs) tr) = tr2ord_i i tr. *)
  (* Proof. *)
  (*   specialize (IND i). *)
  (*   destruct (must_fail_or_nofail i tr) as [MUST | NF]. *)
  (*   { punfold IND. eapply pind3_unfold in IND. *)
  (*     2:{ ii. eapply RawTr.fair_ind_mon2; eauto. } *)
  (*     inv IND. *)
  (*     { eapply must_fail_not_nofail in MUST. punfold NOFAIL; inv NOFAIL. pclearbot. clarify. } *)
      
  (*   eapply ord_tr_eq. eauto. *)

    
  (*   unfold tr2ord_i, epsilon. unfold Epsilon.epsilon, proj1_sig. des_ifs. clear Heq Heq0. *)
  (*   hexploit o; clear o. eapply fair_ind_ex_ord_tr; eauto. intros ORD. rename x into o. *)
  (*   hexploit o0; clear o0. *)
  (*   { inv ORD. *)
  (*     { punfold NOFAIL. inv NOFAIL. pclearbot. eexists. econs 1; eauto. } *)
  (*     { exists (S o0). eapply next_ord_tr; eauto. } *)
  (*   } *)
  (*   intros ORD0. rename x0 into o0. inv ORD. *)
  (*   2:{ hexploit next_ord_tr; eauto. i. admit. } *)
  (*   rename o into wft0. *)
  (*   punfold NOFAIL. inv NOFAIL. pclearbot. eapply (ord_tr_nofail _ wft0 S) in TL. *)
  (* Admitted. *)

  Lemma ord_tr_fair_ord
        R (tr: @RawTr.t Ident R)
        (IND: RawTr.is_fair_ind tr)
    :
    RawTr.fair_ord (fun i => tr2ord_i i tr) tr.
  Proof.
    revert_until R. pcofix CIH. i. destruct tr.
    { pfold. econs. }
    { pfold. econs. }
    { pfold. econs. }
    { destruct hd as [silent | obs].
      2:{ pfold. econs. right.
          assert ((fun i : id => tr2ord_i i (RawTr.cons (inr obs) tr)) = (fun i : id => tr2ord_i i tr)).
          { extensionalities i. eapply tr2ord_i_red_obs; eauto. }
          rewrite H; clear H. eapply CIH.
          ii. specialize (IND i). punfold IND. eapply pind3_unfold in IND.
          2:{ admit. }
          inv IND.
          { punfold NOFAIL. inv NOFAIL. pclearbot. pfold. eapply pind3_fold. econs 1; eauto. }
          destruct IND0 as [PI IND]. clear IND.

  (*         punfold IND. *)


          
  (*         rewrite tr2ord_i_red_obs; eauto. *)



  (*         eapply CIH. i. specialize (ORD i). inv ORD. *)
  (*         - punfold NOFAIL. inv NOFAIL. pclearbot. econs 1; eauto. *)
  (*         - eapply next_ord_tr; eauto. *)
  (*     } *)
  (*     destruct silent as [| fm]. *)
  (*     { pfold. econs. right. eapply CIH. i. specialize (ORD i). inv ORD. *)
  (*       - punfold NOFAIL. inv NOFAIL. pclearbot. econs 1; eauto. *)
  (*       - eapply next_ord_tr; eauto. *)
  (*     } *)
  (*     { pfold. econs. 2:{ right. eapply CIH. i. specialize (ORD i). inv ORD. *)
  (*                         { punfold NOFAIL. inv NOFAIL. *)

        
  (*     destruct (fm i) *)



  Lemma ord_tr_fair_ord
        R (tr: @RawTr.t Ident R) m
        (ORD: forall i, ord_tr wft wft0 S i (m i) tr)
    :
    RawTr.fair_ord m tr.
  Proof.
    revert_until R. pcofix CIH. i. destruct tr.
    { pfold. econs. }
    { pfold. econs. }
    { pfold. econs. }
    { destruct hd as [silent | obs].
      2:{ pfold. econs. right. eapply CIH.
          i. specialize (ORD i). inv ORD.
          - punfold NOFAIL. inv NOFAIL. pclearbot. econs 1; eauto.
          - eapply next_ord_tr; eauto.
      }
      destruct silent as [| fm].
      { pfold. econs. right. eapply CIH. i. specialize (ORD i). inv ORD.
        - punfold NOFAIL. inv NOFAIL. pclearbot. econs 1; eauto.
        - eapply next_ord_tr; eauto.
      }
      { hexploit ord_tr_fair_ev_update. eauto. i.
        hexploit ord_tr_fair_case; eauto.
        { eapply all_ord_tr_is_fair_ind; eauto. i. specialize (ORD i).


        
        pfold. econs. 2:{ right. eapply CIH. i. specialize (ORD i). inv ORD.
                          { punfold NOFAIL. inv NOFAIL.

        hexploit ord_tr_fair_case; eauto.
        { eapply all_ord_tr_is_fair_ind; eauto. i. specialize (ORD i).

        pfold. econs. 2:{ right. eapply CIH. i. specialize (ORD i). inv ORD.
                          { punfold NOFAIL. inv NOFAIL.

        
      destruct (fm i)

            pose proof (must_fail_or_nofail i tr). destruct H as [MUST | NOF].
            { 



  (* Lemma next_ord_tr *)
  (*       i R (tr next: @RawTr.t _ R) *)
  (*       o1 o2 *)
  (*       (NEXT: RawTr.next_fail i tr next) *)
  (*       (LT: lt wft o2 o1) *)
  (*       (ORD: ord_tr wft i o2 next) *)
  (*   : *)
  (*   ord_tr wft i o1 tr. *)
  (* Proof. *)
  (*   destruct tr. *)
  (*   { punfold NEXT. inv NEXT. } *)
  (*   { punfold NEXT. inv NEXT. } *)
  (*   { punfold NEXT. inv NEXT. } *)
  (*   { destruct hd as [sil | obs]. *)
  (*     2:{ econs 2; eauto. punfold NEXT. inv NEXT. pclearbot. eauto. } *)
  (*     destruct sil as [| fm]. *)
  (*     { econs 3; eauto. punfold NEXT. inv NEXT. pclearbot. eauto. } *)
  (*     punfold NEXT. inv NEXT. *)
  (*     { econs 5; eauto. } *)
  (*     { pclearbot. econs 4; eauto. } *)
  (*   } *)
  (* Qed. *)

  Lemma tr2ord_i_red_obs
        i R (tr: @RawTr.t _ R) obs
        (IND : RawTr.is_fair_ind (RawTr.cons (inr obs) tr))
    :
    tr2ord_i i (RawTr.cons (inr obs) tr) = tr2ord_i i tr.
  Proof.
    unfold tr2ord_i, epsilon. unfold Epsilon.epsilon, proj1_sig. des_ifs. clear Heq Heq0.
    hexploit o; clear o. eapply fair_ind_ex_ord_tr; eauto. intros ORD. rename x into o.
    hexploit o0; clear o0.
    { inv ORD.
      { punfold NOFAIL. inv NOFAIL. pclearbot. eexists. econs 1; eauto. }
      { exists (S o0). eapply next_ord_tr; eauto. }
    }
    intros ORD0. rename x0 into o0. inv ORD.
    2:{ hexploit next_ord_tr; eauto. i. admit. }
    rename o into wft0.
    punfold NOFAIL. inv NOFAIL. pclearbot. eapply (ord_tr_nofail _ wft0 S) in TL.
  Admitted.

  Lemma next_fail_fair_ind
        i R (tr next: @RawTr.t Ident R)
        (NEXT: RawTr.next_fail i tr next)
        (IND: pind3 (RawTr.__fair_ind (upaco3 (fun r => pind3 (RawTr.__fair_ind r) top3) bot3)) top3 R i next)
    :
    RawTr.fair_ind i tr.
  Proof.
    pfold. depgen tr.
    revert R i next IND.
    eapply (@pind3_acc _ _ _ _ (fun R i (next: @RawTr.t Ident R) =>
                                  forall tr : RawTr.t,
                                    RawTr.next_fail i tr next ->
                                    pind3
                                      (RawTr.__fair_ind
                                         (upaco3 (fun r => pind3 (RawTr.__fair_ind r) top3) bot3)) top3 R i tr)).
    (* eapply (@pind3_acc _ _ _ _ (fun R i (next: @RawTr.t Ident R) => *)
    (*                               forall tr : RawTr.t, RawTr.next_fail i tr next -> RawTr.fair_ind i tr)). *)
    i. rename x0 into R, x1 into i, x2 into next. rename H into NEXT.
    eapply pind3_unfold in PR.
    2:{ clear. ii. eapply RawTr.fair_ind_mon2; eauto. }
    inv PR.
    { admit. }
    { destruct IND as [PI IND]. hexploit IH. eauto. eauto. i.

  Lemma ord_tr_fair_ord
        R (tr: @RawTr.t Ident R)
        (IND: RawTr.is_fair_ind tr)
    :
    RawTr.fair_ord (fun i => tr2ord_i i tr) tr.
  Proof.
    revert_until R. pcofix CIH. i. destruct tr.
    { pfold. econs. }
    { pfold. econs. }
    { pfold. econs. }
    { destruct hd as [silent | obs].
      2:{ pfold. econs. right.
          assert ((fun i : id => tr2ord_i i (RawTr.cons (inr obs) tr)) = (fun i : id => tr2ord_i i tr)).
          { extensionalities i. eapply tr2ord_i_red_obs; eauto. }
          rewrite H; clear H. eapply CIH.
          ii. specialize (IND i). punfold IND. eapply pind3_unfold in IND.
          2:{ admit. }
          inv IND.
          { punfold NOFAIL. inv NOFAIL. pclearbot. pfold. eapply pind3_fold. econs 1; eauto. }
          destruct IND0 as [PI IND]. clear IND.

          punfold IND.


          
          rewrite tr2ord_i_red_obs; eauto.



          eapply CIH. i. specialize (ORD i). inv ORD.
          - punfold NOFAIL. inv NOFAIL. pclearbot. econs 1; eauto.
          - eapply next_ord_tr; eauto.
      }
      destruct silent as [| fm].
      { pfold. econs. right. eapply CIH. i. specialize (ORD i). inv ORD.
        - punfold NOFAIL. inv NOFAIL. pclearbot. econs 1; eauto.
        - eapply next_ord_tr; eauto.
      }
      { pfold. econs. 2:{ right. eapply CIH. i. specialize (ORD i). inv ORD.
                          { punfold NOFAIL. inv NOFAIL.

        
      destruct (fm i)

            pose proof (must_fail_or_nofail i tr). destruct H as [MUST | NOF].
            { 

  (* Lemma ord_tr_ex_fair_update *)
  (*       R (tr: @RawTr.t Ident R) m fm *)
  (*       (ORD: forall i : id, ord_tr wft i (m i) (RawTr.cons (inl (silentE_fair fm)) tr)) *)
  (*   : *)
  (*   exists m0, (fair_update m m0 fm) /\ (forall i, ord_tr wft i (m0 i) tr). *)
  (* Proof. *)

  Lemma ord_tr_fair_ord
        R (tr: @RawTr.t Ident R) m
        (ORD: forall i, ord_tr wft i (m i) tr)
    :
    RawTr.fair_ord m tr.
  Proof.
    revert_until R. pcofix CIH. i. destruct tr.
    { pfold. econs. }
    { pfold. econs. }
    { pfold. econs. }
    { destruct hd as [silent | obs].
      2:{ pfold. econs. right. eapply CIH. i. specialize (ORD i). inv ORD.
          - punfold NOFAIL. inv NOFAIL. pclearbot. econs 1; eauto.
          - eapply next_ord_tr; eauto.
      }
      destruct silent as [| fm].
      { pfold. econs. right. eapply CIH. i. specialize (ORD i). inv ORD.
        - punfold NOFAIL. inv NOFAIL. pclearbot. econs 1; eauto.
        - eapply next_ord_tr; eauto.
      }
      { pfold. econs. 2:{ right. eapply CIH. i. specialize (ORD i). inv ORD.
                          { punfold NOFAIL. inv NOFAIL.

        
      destruct (fm i)

            pose proof (must_fail_or_nofail i tr). destruct H as [MUST | NOF].
            { 


End EQUIV2.





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



  Variant _coind_fail i
          (coind_fail: forall R, (@RawTr.t _ R) -> Prop)
          R
    :
    (@RawTr.t _ R) -> Prop :=
    | coind_fail_intro
        tr next
        (NEXT: next_fail i tr next)
        (FAIL: coind_fail R next)
      :
      _coind_fail i coind_fail tr
  .

  Lemma coind_fail_mon i: monotone2 (_coind_fail i).
  Proof. ii. inv IN. econs; eauto. Qed.

  Definition coind_fail i: forall R, (@RawTr.t _ R) -> Prop := paco2 (_coind_fail i) bot2.

  Local Hint Constructors _coind_fail: core.
  Local Hint Unfold coind_fail: core.
  Local Hint Resolve coind_fail_mon: paco.



  Lemma not_ex_ord_tr_coind_fail
        i R (tr: @RawTr.t _ R)
        (NOT: ~ exists o, ord_tr i o tr)
    :
    coind_fail i tr.
  Proof.
    nean NOT.
    revert_until i. pcofix CIH. i.
    destruct tr.
    { exfalso. eapply (NOT wft0). econs. pfold. econs. }
    { exfalso. eapply (NOT wft0). econs. pfold. econs. }
    { exfalso. eapply (NOT wft0). econs. pfold. econs. }
    { destruct hd as [silent | obs].
      2:{ destruct (classic (exists next, next_fail i tr next)) as [NEXT | NONE].
          { des. destruct (classic (exists o, ord_tr i o next)) as [ORD | NONE].
            { des. exfalso. eapply (NOT (S o)); clear NOT. econs; eauto. }
            nean NONE.
            pfold. econs.
            { pfold. econs. left. eauto. }
            right. eapply CIH. eauto.
          }
          { eapply not_ex_next_fail_nofail in NONE.
            match goal with
            | H: forall a, ~ ord_tr _ _ ?tr2 |- _ => assert (NONE2: nofail i tr2)
            end.
            { pfold. econs. eauto. }
            eapply nofail_ex_ord_tr in NONE2. des. specialize (NOT o). clarify.
          }
      }
      destruct silent as [ | fm].
      { destruct (classic (exists next, next_fail i tr next)) as [NEXT | NONE].
        { des. destruct (classic (exists o, ord_tr i o next)) as [ORD | NONE].
          { des. exfalso. eapply (NOT (S o)); clear NOT. econs; eauto. }
          nean NONE.
          pfold. econs.
          { pfold. econs. left. eauto. }
          right. eapply CIH. eauto.
        }
        { eapply not_ex_next_fail_nofail in NONE.
          match goal with
          | H: forall a, ~ ord_tr _ _ ?tr2 |- _ => assert (NONE2: nofail i tr2)
          end.
          { pfold. econs. eauto. }
          eapply nofail_ex_ord_tr in NONE2. des. specialize (NOT o). clarify.
        }
      }
      { destruct (fm i) eqn:FM.
        { destruct (classic (exists o, ord_tr i o tr)) as [ORD | NONE].
          { des. exfalso. eapply (NOT (S o)); clear NOT. econs 5; eauto. }
          nean NONE.
          pfold. econs.
          { pfold. econs. eauto. }
          right. eapply CIH. eauto.
        }
        { destruct (classic (exists next, next_fail i tr next)) as [NEXT | NONE].
          { des. destruct (classic (exists o, ord_tr i o next)) as [ORD | NONE].
            { des. exfalso. eapply (NOT (S o)); clear NOT. econs; eauto. }
            nean NONE.
            pfold. econs.
            { pfold. econs 4; eauto. }
            right. eapply CIH. eauto.
          }
          { eapply not_ex_next_fail_nofail in NONE.
            match goal with
            | H: forall a, ~ ord_tr _ _ ?tr2 |- _ => assert (NONE2: nofail i tr2)
            end.
            { pfold. econs 7; eauto. }
            eapply nofail_ex_ord_tr in NONE2. des. specialize (NOT o). clarify.
          }
        }
        { exfalso. eapply (NOT wft0). econs. pfold. econs 4. auto. }
      }
    }
  Qed.



  Variable wft0: wft.(T).
  (* Variable S: wft.(T) -> wft.(T). *)
  (* Hypothesis lt_succ_diag_r: forall (t: wft.(T)), wft.(lt) t (S t). *)

  (* coinductive2-inductive3 *)
  Variant __tr_ord (i: id)
          (tr_ord: forall (R: Type), wft.(T) -> (@RawTr.t _ R) -> Prop)
          (_tr_ord: forall (R: Type), (@RawTr.t _ R) -> Prop)
          (R: Type)
    :
    wft.(T) -> (@RawTr.t _ R) -> Prop :=
    (* base cases *)
    | tr_ord_done
        o retv
      :
      __tr_ord i tr_ord _tr_ord o (RawTr.done retv)
    | tr_ord_ub
        o
      :
      __tr_ord i tr_ord _tr_ord o RawTr.ub
    | tr_ord_nb
        o
      :
      __tr_ord i tr_ord _tr_ord o RawTr.nb
    | tr_ord_fair_success
        o fmap tl
        (SUCCESS: Flag.success = (fmap i))
      :
      __tr_ord i tr_ord _tr_ord o (RawTr.cons (inl (silentE_fair fmap)) tl)

    (* inner coinductive cases: no fair events for i *)
    | tr_ord_obs
        o (obs: obsE) tl
        (TL: _tr_ord R tl)
      :
      __tr_ord i tr_ord _tr_ord o (RawTr.cons (inr obs) tl)
    | tr_ord_tau
        o tl
        (TL: _tr_ord R tl)
      :
      __tr_ord i tr_ord _tr_ord o (RawTr.cons (inl silentE_tau) tl)
    | tr_ord_fair_emp
        o fmap tl
        (EMP: Flag.emp = (fmap i))
        (TL: _tr_ord R tl)
      :
      __tr_ord i tr_ord _tr_ord o (RawTr.cons (inl (silentE_fair fmap)) tl)

    (* outer inductive cases: i fails inductively *)
    | tr_ord_fair_fail
        o fmap tl o0
        (FAIL: Flag.fail = (fmap i))
        (LT: wft.(lt) o0 o)
        (TL: tr_ord R o0 tl)
      :
      __tr_ord i tr_ord _tr_ord o (RawTr.cons (inl (silentE_fair fmap)) tl)
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

  Lemma _tr_ord_mon i: forall r q q' (LE: q <2= q'), (__tr_ord i r q) <3= (__tr_ord i r q').
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

  Lemma tr_ord_mon i: forall p, monotone3 (fun q => (__tr_ord i q) p).
  Proof.
    ii. eapply __tr_ord_mon; eauto.
  Qed.

  Definition tr_ord (i: id): forall (R: Type), wft.(T) -> (@RawTr.t _ R) -> Prop :=
    pind3 (fun q R o (tr: @RawTr.t _ R) =>
             paco2 (fun p R tr => @__tr_ord i q p R o tr) bot2 R tr) top3.

  Lemma inhabited_tr_ord: inhabited (T wft).
  Proof. econs. exact wft0. Qed.

  Definition tr2ord_i {R} i (raw: (@RawTr.t _ R)): wft.(T) :=
    epsilon _ (inhabited_tr_ord) (fun o => tr_ord i o raw).


  Lemma tr_ord_exists
        i R (tr: @RawTr.t Ident R)
        (IND: RawTr.is_fair_ind tr)
    :
    exists o, tr_ord i o tr.
  Proof.
    eapply cpex_exists. revert_until wft0. pcofix CIH. i.
    (* exists (tr2ord_i i tr). *)
    specialize (IND i).
    punfold IND.
    2:{ clear. ii. eapply pind3_mon_gen; eauto. ii. ss. eapply paco3_mon_gen. eapply PR. 2: ss.
        i. eapply RawTr.___fair_ind_mon; eauto.
    } (*make lemma*)
    revert R i tr IND.
    (* eapply (@pind3_acc _ _ _ _ (fun (R: Type) => (fun (i: id) => fun (tr: @RawTr.t Ident R) => exists o, tr_ord i tr o))). *)
    eapply (@pind3_acc _ _ _ _ (fun R i (tr: @RawTr.t Ident R) => paco1 (_pex (A:=T wft)) r (fun x : T wft => tr_ord i x tr))).
    (* eapply (@pind3_acc _ _ _ _ (fun R i (tr: @RawTr.t Ident R) => tr_ord i (@tr2ord_i R i tr) tr)). *)
    i. rename x0 into R, x1 into i, x2 into tr.
    eapply pind3_unfold in PR.
    2:{ clear. ii. eapply paco3_mon_gen. eapply IN. 2: ss.
        i. eapply RawTr.__fair_ind_mon; eauto.
    } (*make lemma*)



    punfold PR.
    2:{ eapply RawTr._fair_ind_mon. }
    inv PR.
    { pfold. econs. eapply pind3_fold. pfold. econs 1. right. eapply CIH. ii. pfold. eapply pind3_fold. pfold. econs 1. }
    { pfold. econs. eapply pind3_fold. pfold. econs 2. right. eapply CIH. ii. pfold. eapply pind3_fold. pfold. econs 2. }
    { pfold. econs. eapply pind3_fold. pfold. econs 3. right. eapply CIH. ii. pfold. eapply pind3_fold. pfold. econs 3. }
    { pfold. econs. eapply pind3_fold. pfold. econs 5. right. left.
      


      destruct TL; ss. rename H into TL. pfold. econs. right. eapply CIH. eauto. }
    { destruct TL; ss. rename H into TL. pfold. econs. right. eapply CIH. eauto. }
    { destruct TL; ss. rename H into TL. pfold. econs 7. auto. right. eapply CIH. eauto. }
    { destruct TL; ss. rename H into TL. rename H0 into IND.
      pfold. econs 8. auto.
      2:{ split; ss. eapply IH in IND. eauto. }
      admit.
    }
    { destruct TL; ss. rename H into TL. pfold. econs 4. auto. }
    (* exists (tr2ord_i i tr). *)
    eapply pind3_fold.

    eapply paco2_acc.
    2:{ instantiate (1:=
                       fun R (tr: @RawTr.t _ R) =>
                         paco3
         (RawTr.___fair_ind
            (upaco3
               (fun r : rel3 Type (fun _ : Type => id) (fun (x0 : Type) (_ : id) => RawTr.t) =>
                pind3
                  (fun q : rel3 Type (fun _ : Type => id) (fun (x0 : Type) (_ : id) => RawTr.t)
                   => paco3 (RawTr.___fair_ind r q) bot3) top3) bot3)
            (upind3
               (fun q : rel3 Type (fun _ : Type => id) (fun (x0 : Type) (_ : id) => RawTr.t) =>
                paco3
                  (RawTr.___fair_ind
                     (upaco3
                        (fun
                           r : rel3 Type (fun _ : Type => id)
                                 (fun (x0 : Type) (_ : id) => RawTr.t) =>
                         pind3
                           (fun
                              q0 : rel3 Type (fun _ : Type => id)
                                     (fun (x0 : Type) (_ : id) => RawTr.t) =>
                            paco3 (RawTr.___fair_ind r q0) bot3) top3) bot3) q) bot3) rr)) bot3 R
         i tr).
        ss.
    }
    clear PR.
    i. ss. rename x0 into R0, x1 into tr0.
    (* clear tr. *)
    (* revert R tr PR. pcofix CIH. i. *)
    (* punfold PR0. *)
    (* 2:{ eapply RawTr._fair_ind_mon. } *)
    (* inv PR0. *)
    punfold PR.
    2:{ eapply RawTr._fair_ind_mon. }
    inv PR.
    { pfold. econs 1. }
    { pfold. econs 2. }
    { pfold. econs 3. }
    { destruct TL; ss. rename H into TL. pfold. econs. right. eapply CIH. eauto. }
    { destruct TL; ss. rename H into TL. pfold. econs. right. eapply CIH. eauto. }
    { destruct TL; ss. rename H into TL. pfold. econs 7. auto. right. eapply CIH. eauto. }
    { destruct TL; ss. rename H into TL. rename H0 into IND.
      pfold. econs 8. auto.
      2:{ split; ss. eapply IH in IND. eauto. }
      admit.
    }
    { destruct TL; ss. rename H into TL. pfold. econs 4. auto. }
  Qed.
  



    right. eapply CIH. eauto. }
    { 

      right. eapply CIH. eauto. }
    { 
    


      hexploit tr2ord_i_red_obs. i; des.
      { pfold. econs. right. rewrite H; clear H. eapply CIH. eauto. }
      (* ??? *)

  Definition tr_ord_inv (i: id): forall (R: Type), (@RawTr.t _ R) -> Prop :=
    paco2 (fun p R tr => exists o, pind3 (fun q R o tr => @__tr_ord i q p R o tr) top3 R o tr) bot2.

  Lemma tr_ord_impl1
        R i (tr: @RawTr.t _ R)
        (INV: tr_ord_inv i tr)
    :
    exists o, tr_ord i o tr.
  Proof.
    punfold INV.
    2:{ ii. des. exists o. eapply pind3_mon_gen. eauto. 2: ss.
        i. ss. eapply _tr_ord_mon; eauto.
    }
    des. exists o.
    eapply pind3_fold. move o before wft0. move i before wft0. revert_until o. pcofix CIH. i.
    eapply paco2_fold. revert R o tr INV.
    eapply pind3_acc.
    
    eapply (@pind3_acc _ _ _ _ (fun R o (tr: @RawTr.t _ R) =>
  __tr_ord i
    (upind3
       (fun (q : rel3 Type (fun _ : Type => T wft) (fun (R0 : Type) (_ : T wft) => RawTr.t))
          (R0 : Type) (o0 : T wft) (tr0 : RawTr.t) =>
        paco2
          (fun (p : rel2 Type (@RawTr.t Ident)) (R1 : Type) (tr1 : RawTr.t) =>
           __tr_ord i q p o0 tr1) bot2 R0 tr0) top3)
    (upaco2
       (fun (p : rel2 Type (@RawTr.t Ident)) (R0 : Type) (tr0 : RawTr.t) =>
        __tr_ord i
          (upind3
             (fun
                (q : rel3 Type (fun _ : Type => T wft) (fun (R1 : Type) (_ : T wft) => RawTr.t))
                (R1 : Type) (o0 : T wft) (tr1 : RawTr.t) =>
              paco2
                (fun (p0 : rel2 Type (@RawTr.t Ident)) (R2 : Type) (tr2 : RawTr.t) =>
                 __tr_ord i q p0 o0 tr2) bot2 R1 tr1) top3) p o tr0) r) o tr)).




                                  tr_ord i o tr)).




    revert R o tr INV.
    eapply (@pind3_acc _ _ _ _ (fun R o (tr: @RawTr.t _ R) => tr_ord i o tr)).
    (* eapply (@pind3_acc _ _ _ _ (fun (R: Type) => (fun (i: id) => fun (tr: @RawTr.t Ident R) => exists o, tr_ord i o tr))). *)
    (* eapply (@pind3_acc _ _ _ _ (fun (R: Type) => (fun (i: id) => fun (tr: @RawTr.t Ident R) => tr_ord i tr (@tr2ord_i R i tr)))). *)
    i. rename x0 into R, x1 into o, x2 into tr.
    eapply pind3_unfold in PR.
    2:{ clear. ii. eapply __tr_ord_mon; eauto. }
    eapply pind3_fold. move o before IH. revert_until o. pcofix CIH. i.
    pfold. inv PR.
    { econs 1. }
    { econs 2. }
    { econs 3. }
    { econs 4; eauto. }
    { pclearbot. econs 5. right. eapply CIH. punfold TL.
      2:{ ii. des. exists o0. eapply pind3_mon_gen. eauto. 2: ss.
          i. ss. eapply _tr_ord_mon; eauto.
      }
      des. eapply pind3_unfold in TL.
      2:{ ii. eapply __tr_ord_mon; eauto. }
      eapply tr_ord_mon.
      2:{ eapply __tr_ord_mon. 2: eauto.
          2:{ eapply tr_ord_mon.



      2:{ ii. des.

      eauto. }


    
        eapply paco3_mon_gen. eapply IN. 2: ss.
        i. eapply RawTr.__fair_ind_mon; eauto.
    } (*make lemma*)

    eapply (@paco2_acc _ _ _ (fun R (tr: @RawTr.t _ R) => forall o,
  __tr_ord i
         (upind3
            (fun (q : rel3 Type (fun _ : Type => T wft) (fun (x0 : Type) (_ : T wft) => RawTr.t))
               (R : Type) (o : T wft) (tr : RawTr.t) =>
             __tr_ord i q
               (upaco2
                  (fun (p : rel2 Type (@RawTr.t Ident)) (R0 : Type) (tr0 : RawTr.t) =>
                   exists o0 : T wft,
                     pind3
                       (fun
                          (q0 : rel3 Type (fun _ : Type => T wft)
                                  (fun (x0 : Type) (_ : T wft) => RawTr.t)) 
                          (R1 : Type) (o1 : T wft) (tr1 : RawTr.t) => 
                        __tr_ord i q0 p o1 tr1) top3 R0 o0 tr0) bot2) o tr) rr)
         (upaco2
            (fun (p : rel2 Type (@RawTr.t Ident)) (R : Type) (tr : RawTr.t) =>
             exists o : T wft,
               pind3
                 (fun
                    (q : rel3 Type (fun _ : Type => T wft)
                           (fun (x0 : Type) (_ : T wft) => RawTr.t)) 
                    (R0 : Type) (o0 : T wft) (tr0 : RawTr.t) => __tr_ord i q p o0 tr0) top3 R o
                 tr) bot2) o tr)).
    { i. ss. specialize (PR0 o).
      pfold. inv PR0.
      { econs 1. }
      { econs 2. }
      { econs 3. }
      { econs 4; eauto. }
      { pclearbot. econs 5. right. eapply CIH. i. punfold TL.
        2:{ ii. des. exists o1. eapply pind3_mon_gen. eauto. 2: ss.
            i. ss. eapply _tr_ord_mon; eauto.
        }
        des. eapply pind3_unfold in TL.
        2:{ ii. eapply __tr_ord_mon; eauto. }
        eapply tr_ord_mon.
        2:{ eapply __tr_ord_mon. 2: eauto.
            2:{ eapply tr_ord_mon.
                2:{ i. 


                  )



  Lemma inhabited_tr_ord: inhabited (T wft).
  Proof. econs. exact wft0. Qed.

  Definition tr2ord_i {R} i (raw: (@RawTr.t _ R)): wft.(T) :=
    epsilon _ (inhabited_tr_ord) (fun o => tr_ord i o raw).

  Definition tr2ord {R} (raw: (@RawTr.t _ R)): imap wft :=
    fun i => tr2ord_i i raw.

  Theorem tr2ord_i_spec
          R i (tr: @RawTr.t _ R)
          (IND: RawTr.is_fair_ind tr)
    :
    exists o, tr_ord i o tr.
  Proof.
    specialize (IND i). punfold IND.
    2:{ clear. ii. eapply pind3_mon_gen; eauto. ii. ss. eapply paco3_mon_gen. eapply PR. 2: ss.
        i. eapply RawTr.___fair_ind_mon; eauto.
    } (*make lemma*)
    revert R i tr IND.
    eapply (@pind3_acc _ _ _ _ (fun R i tr => exists o, tr_ord i o tr)).
    (* eapply (@pind3_acc _ _ _ _ (fun (R: Type) => (fun (i: id) => fun (tr: @RawTr.t Ident R) => exists o, tr_ord i o tr))). *)
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
      (fun (q : rel3 Type (fun _ : Type => T wft) (fun (R0 : Type) (_ : T wft) => RawTr.t))
         (R0 : Type) (o0 : T wft) (tr0 : RawTr.t) =>
       upaco2
         (fun (p : rel2 Type (@RawTr.t Ident)) (R1 : Type) (tr1 : RawTr.t) =>
            __tr_ord i q p o0 tr1) bot2 R0 tr0) top3 R o tr).
    2:{ des. exists o. eapply pind3_mon_gen. eauto. 2: ss.
        i. ss. pclearbot. auto. }
    eexists.
    eapply paco3_unfold.

    
    assert 


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
