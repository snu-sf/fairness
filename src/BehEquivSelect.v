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
          all: admit. (* construct an imap m1 with (m1 i) = (m i), (m1 i' = m0 i')*)
      }
      { pfold. econs 8. auto. right. eapply CIH1; eauto. }
    }
    { pclearbot. pfold. econs 5. right. eapply CIH2; eauto. }
  Qed.
  
    
    


    
    pcofix CIH2.











    eapply paco3_fold.
    destruct (classic (exists idx, wft.(lt) idx (m i))) as [EXIST | BOT].
    (* destruct (classic (exists m1, wft.(lt) (m1 i) (m i))) as [EXIST | BOT]. *)
    { des.
      move idx before CIH. revert_until idx.
      induction (wft.(wf) idx). rename H into ACC, H0 into IH, x into idx. i.
      (* destruct (classic (exists idx1, wft.(lt) idx1 idx0)) as [EXIST2 | BOT2]. *)
      (* (* destruct (classic (exists m2, wft.(lt) (m2 i) (m1 i))) as [EXIST2 | BOT2]. *) *)
      (* { des. punfold ORD. } *)
      (* (* eapply Classical_Pred_Type.not_ex_all_not in BOT2. *) *)
      punfold ORD. inv ORD.
      { eapply pind3_fold. econs. pfold. econs. }
      { eapply pind3_fold. econs. pfold. econs. }
      { eapply pind3_fold. econs. pfold. econs. }
      { pclearbot. eapply pind3_fold. econs 4. split; ss. eapply IH. all: eauto. }
      { pclearbot. eapply pind3_fold. unfold fair_update in FAIR. specialize (FAIR i).
        des_ifs.
        { econs 2.
          { rewrite Heq. ss. }
          split; ss. eapply IH.
          2:{ ginit. guclo RawTr.fair_ord_imap_le_ctx_spec. econs; eauto.
              gfinal. right. eauto. instantiate (1:=m). clear - FAIR.
              unfold soft_update. i.

              2: eauto. 3: eauto. all: eauto.

            all: eauto.
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
