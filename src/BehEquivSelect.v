From sflib Require Import sflib.
From ITree Require Export ITree.

Export ITreeNotations.

Require Import Coq.Classes.RelationClasses.

(* Require Import Lia. *)

From Fairness Require Import FairBeh.
From Fairness Require Import pind3.
From Fairness Require Import SelectBeh.

From Paco Require Import paco.

Set Implicit Arguments.


Section EQUIV.

  Context {Ident: ID}.
  Variable wft: WF.
  Variable R: Type.

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
    depgen tr. induction (wft.(wf) (m i)). rename H into ACC, H0 into IH. i.
    punfold ORD. inv ORD.
    { eapply pind3_fold. econs. pfold. econs. }
    { eapply pind3_fold. econs. pfold. econs. }
    { eapply pind3_fold. econs. pfold. econs. }
    { pclearbot. eapply pind3_fold. econs 4. split; ss. eapply IH; eauto. admit. }
    { pclearbot. eapply pind3_fold. destruct (fmap i) eqn:FM.
      - econs 2.
        { rewrite FM. ss. }
        split; ss. eapply IH; eauto. admit. admit.
      - econs 2.
        { rewrite FM. ss. }
        split; ss. eapply IH; eauto. admit. admit.
      - econs 5.
        { rewrite FM. ss. }
        right. eapply CIH. eauto.
    }
    { pclearbot. eapply pind3_fold. econs 3. split; ss. eapply IH; eauto. admit. }
    Unshelve. all: exact (m i).
  Admitted.


End EQUIV.
