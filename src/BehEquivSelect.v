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

  (* Lemma cannot_fail_nofail *)
  (*       i im (tr: @RawTr.t Ident R) *)
  (*       (CNTF: ~ (exists t, wft.(lt) t (im i))) *)
  (*       (ORD: RawTr.fair_ord im tr) *)
  (*   : *)
  (*   (* RawTr.fair_ind i tr. *) *)
  (*   RawTr.nofail_ind i tr. *)
  (* Proof. *)
  (*   revert_until R. pcofix CIH; i. *)
  (*   remember (im i) as idx. move idx before CIH. revert_until idx. *)
  (*   induction (wft.(wf) idx). rename H into ACC, H0 into IH. i. *)
  (*   punfold ORD. inv ORD. *)
  (*   { pfold; eauto. } *)
  (*   { pfold; eauto. } *)
  (*   { pfold; eauto. } *)
  (*   { pclearbot. pfold. econs. right. eapply CIH; eauto. } *)
  (*   { pclearbot. unfold fair_update in FAIR. specialize (FAIR i). des_ifs. *)
  (*     { exfalso; apply CNTF. eauto. } *)
  (*     - destruct FAIR. *)
  (*       + pfold. econs 5. rewrite Heq; ss. right. eapply CIH. 2: eauto. rewrite H; auto. *)
  (*       + pfold. econs 5. rewrite Heq; ss. left. eapply IH; eauto. *)
  (*     - pfold. econs 5. rewrite Heq; ss. left. eapply IH. *)
        

  (*       econs 5. rewrite Heq; ss. left. *)
  (*       destruct FAIR. *)
  (*       + eapply IH.  *)

  (*       eapply IH. 4: eauto. 2: eauto. *)

  (*     pfold. econs 5. *)
  (*     2:{ left. eapply IH. *)

  (*     unfold fair_update in FAIR. specialize (FAIR i). *)
  (*     pfold. econs 5. *)
  (*     2:{ right. eapply CIH. *)

  (*         2: eauto. ii. eapply CNTF. des. *)

  (*         eauto. *)





  (*   eapply Classical_Pred_Type.not_ex_all_not in CNTF. *)

  (* Lemma Ord_implies_Ind_strong *)
  (*       (tr: @RawTr.t Ident R) im0 *)
  (*       (* (ORD: forall im (LE: soft_update im0 im), RawTr.fair_ord (wf:=wft) im tr) *) *)
  (*       (ORD: forall im (LE: soft_update im im0), RawTr.fair_ord (wf:=wft) im tr) *)
  (*       (* (ORD: forall im (LT: wft.(lt) (im i) (im0 i)), RawTr.fair_ord im tr) *) *)
  (*   : *)
  (*   RawTr.is_fair_ind tr. *)
  (* Proof. *)
  (*   ii. revert_until R. pcofix CIH. i. *)
  (*   eapply paco3_fold. *)
  (*   (* assert (GE: exists img, soft_update img im0). *) *)
  (*   (* { admit. } *) *)
  (*   depgen tr. des. *)
  (*   remember (im0 i) as idx. move idx before CIH. revert_until idx. *)
  (*   induction (wft.(wf) idx). rename H into ACC, H0 into IH. i. *)
  (*   des. *)
  (*   specialize (ORD im0). hexploit ORD; clear ORD. reflexivity. intro ORD. *)
  (*   (* specialize (ORD im0). hexploit ORD; clear ORD. reflexivity. intro ORD. *) *)
  (*   destruct (classic (exists im1, (wft.(lt) (im1 i) (im0 i)))) as [EXIST | BOT]. *)
  (*   { des. punfold ORD. inv ORD. *)
  (*     { eapply pind3_fold. econs. pfold. econs. } *)
  (*     { eapply pind3_fold. econs. pfold. econs. } *)
  (*     { eapply pind3_fold. econs. pfold. econs. } *)
  (*     { pclearbot. eapply pind3_fold. econs 4. split; ss. eapply IH. *)
  (*       3:{ i. instantiate (1:=im0) in LE. *)
  (*           ginit. guclo RawTr.fair_ord_imap_le_ctx_spec. econs; eauto. *)
  (*           gfinal. right. eauto. *)
  (*       } *)
  (*       2: eauto. *)
            
  (*           { clear - EXIST LE. unfold soft_update in *. i. specialize (LE i0). *)

  (*       1,2: eauto. *)
  (*       i. *)
        

  (*       admit. } *)
  (*     { pclearbot. eapply pind3_fold. destruct (fmap i) eqn:FM. *)
  (*       - econs 2. *)
  (*         { rewrite FM. ss. } *)
  (*         split; ss. eapply IH; eauto. *)
  (*         unfold fair_update in FAIR. specialize (FAIR i). rewrite FM in FAIR. eauto. *)
  (*       - econs 2. *)
  (*         { rewrite FM. ss. } *)
  (*         split; ss. *)
  (*         unfold fair_update in FAIR. specialize (FAIR i). rewrite FM in FAIR. *)
  (*         destruct FAIR. *)
  (*         2:{ eapply IH; eauto. } *)
  (*         admit. *)
  (*       - econs 5. *)
  (*         { rewrite FM. ss. } *)
  (*         right. eapply CIH. eauto. *)
  (*     } *)
  (*     { pclearbot. eapply pind3_fold. econs 3. split; ss. eapply IH; eauto. admit. } *)
  (* Admitted. *)


  Theorem Ord_implies_Ind
          (tr: @RawTr.t Ident R)
          (ORD: RawTr.is_fair_ord wft tr)
    :
    RawTr.is_fair_ind tr.
  Proof.
  (*   unfold RawTr.is_fair_ord in ORD. des. eapply Ord_implies_Ind_strong. i. *)
  (*   ginit. guclo RawTr.fair_ord_imap_le_ctx_spec. econs; eauto. *)
  (*   gfinal. right. eauto. *)
  (* Qed. *)
    ii. unfold RawTr.is_fair_ord in ORD. des. revert_until R. pcofix CIH. i.
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
