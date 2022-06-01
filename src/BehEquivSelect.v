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
  Variable wft: WF.
  Variable R: Type.

  Lemma cannot_fail_nofail
        i im (tr: @RawTr.t Ident R)
        (CNTF: ~ (exists t, wft.(lt) t (im i)))
        (ORD: RawTr.fair_ord im tr)
    :
    RawTr.fair_ind i tr.
    (* RawTr.nofail_ind i tr. *)
  Proof.
    punfold ORD.

    
    revert_until R. pcofix CIH; i.
    punfold ORD. inv ORD.
    { pfold; eauto. }
    { pfold; eauto. }
    { pfold; eauto. }
    { pclearbot. pfold. eapply pind3_fold. econs 1. pfold. econs. right. eapply CIH; eauto. }
    { pclearbot. unfold fair_update in FAIR. specialize (FAIR i).
      pfold. econs 5.
      2:{ right. eapply CIH.

          2: eauto. ii. eapply CNTF. des.

          eauto.





    eapply Classical_Pred_Type.not_ex_all_not in CNTF.

  Theorem Ord_implies_Ind
          (tr: @RawTr.t Ident R)
          (ORD: RawTr.is_fair_ord wft tr)
    :
    RawTr.is_fair_ind tr.
  Proof.
    unfold RawTr.is_fair_ord in ORD. des. ii. revert_until R. pcofix CIH. i.
    (* eapply paco3_mon_gen. *)
    (* 3: eauto. *)
    (* 2:{ i. eapply pind3_mon_top. eauto. i.  *)
    eapply paco3_fold.
    (* eapply pind3_mon_top. 2: eauto. *)
    (* eapply pind3_mon_gen. 3: eauto. *)
    (* 2:{ i. eapply RawTr.__fair_ind_mon. *)
    (*     { i. left. eauto. } *)
    (*     eauto. *)
    (* } *)
    depgen tr. remember (m i) as idx. move idx before CIH. revert_until idx.
    induction (wft.(wf) idx). rename H into ACC, H0 into IH. i.
    punfold ORD. inv ORD.
    { eapply pind3_fold. econs. pfold. econs. }
    { eapply pind3_fold. econs. pfold. econs. }
    { eapply pind3_fold. econs. pfold. econs. }
    { pclearbot. eapply pind3_fold. econs 4. split; ss. eapply IH. eauto. admit. }
    { pclearbot. eapply pind3_fold. destruct (fmap i) eqn:FM.
      - econs 2.
        { rewrite FM. ss. }
        split; ss. eapply IH; eauto.
        unfold fair_update in FAIR. specialize (FAIR i). rewrite FM in FAIR. eauto.
      - econs 2.
        { rewrite FM. ss. }
        split; ss.
        unfold fair_update in FAIR. specialize (FAIR i). rewrite FM in FAIR.
        destruct FAIR.
        2:{ eapply IH; eauto. }
        admit.
      - econs 5.
        { rewrite FM. ss. }
        right. eapply CIH. eauto.
    }
    { pclearbot. eapply pind3_fold. econs 3. split; ss. eapply IH; eauto. admit. }
  Admitted.


End EQUIV.
