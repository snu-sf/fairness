From sflib Require Import sflib.
From Paco Require Import paco.

Require Export Coq.Strings.String.
Require Import Coq.Classes.RelationClasses.
Require Import Program.
Require Import Permutation.
From iris.algebra Require Import cmra.

From Fairness Require Import Axioms.
From Fairness Require Export ITreeLib FairBeh FairSim NatStructs.
From Fairness Require Import pind PCM.
From Fairness Require Export Mod ModSimStutter Concurrency.
From Fairness Require Import KnotSim.

Set Implicit Arguments.

Section AUX.

  Context `{M: ucmra}.

  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable _ident_src: ID.
  Let ident_src := sum_tid _ident_src.
  Variable _ident_tgt: ID.
  Let ident_tgt := sum_tid _ident_tgt.

  Variable wf_src: WF.
  Variable wf_tgt: WF.

  Notation srcE := (threadE _ident_src state_src).
  Notation tgtE := (threadE _ident_tgt state_tgt).

  Variable wf_stt: Type -> Type -> WF.

  Let shared := shared state_src state_tgt _ident_src _ident_tgt wf_src wf_tgt.

  Notation threads_src1 R0 := (threads _ident_src (sE state_src) R0).
  Notation threads_src2 R0 := (threads2 _ident_src (sE state_src) R0).
  Notation threads_tgt R1 := (threads _ident_tgt (sE state_tgt) R1).

  Variable I: shared -> (cmra_car M) -> Prop.

  Definition local_sim_pick {R0 R1} (RR: R0 -> R1 -> Prop) src tgt tid o r_own :=
    forall ths0 im_src0 im_tgt0 st_src0 st_tgt0 r_shared0 r_ctx0
      (INV: I (ths0, im_src0, im_tgt0, st_src0, st_tgt0) r_shared0)
      (VALID: ✓ (r_shared0 ⋅ r_own ⋅ r_ctx0)),
    forall im_tgt1 (FAIR: fair_update im_tgt0 im_tgt1 (prism_fmap inlp (tids_fmap tid ths0))),
    exists im_src1, (fair_update im_src0 im_src1 (prism_fmap inlp (tids_fmap tid ths0))) /\
                 (forall fs ft,
                     lsim wf_stt I tid (local_RR I RR tid)
                          fs ft r_ctx0 (o, src) tgt
                          (ths0, im_src1, im_tgt1, st_src0, st_tgt0)).

  Definition local_sim_sync {R0 R1} (RR: R0 -> R1 -> Prop) src tgt tid o r_own :=
    forall ths0 im_src0 im_tgt0 st_src0 st_tgt0 r_shared0 r_ctx0
      (INV: I (ths0, im_src0, im_tgt0, st_src0, st_tgt0) r_shared0)
      (VALID: ✓ (r_shared0 ⋅ r_own ⋅ r_ctx0))
      fs ft,
    forall im_tgt1 (FAIR: fair_update im_tgt0 im_tgt1 (prism_fmap inlp (tids_fmap tid ths0))),
      (lsim wf_stt I tid (local_RR I RR tid)
            fs ft r_ctx0 (o, Vis (inl1 (inl1 (inr1 Yield))) (fun _ => src)) tgt
            (ths0, im_src0, im_tgt1, st_src0, st_tgt0)).

  Definition th_wf_pair {elt1 elt2} := @nm_wf_pair elt1 elt2.

  Lemma th_wf_pair_pop_cases
        R0 R1
        (ths_src: threads_src2 R0)
        (ths_tgt: threads_tgt R1)
        (WFx: th_wf_pair ths_src ths_tgt)
    :
    forall x, ((nm_pop x ths_src = None) /\ (nm_pop x ths_tgt = None)) \/
           (exists th_src th_tgt ths_src0 ths_tgt0,
               (nm_pop x ths_src = Some (th_src, ths_src0)) /\
                 (nm_pop x ths_tgt = Some (th_tgt, ths_tgt0)) /\
                 (th_wf_pair ths_src0 ths_tgt0)).
  Proof.
    eapply nm_wf_pair_pop_cases. eauto.
  Qed.


  Lemma proj_aux
        e tid tid0 elem
        (ths ths0 : NatMap.t e)
        (TH : Th.find (elt:=e) tid ths = None)
        (H : nm_pop tid0 ths = Some (elem, ths0))
    :
    NatSet.remove tid (NatSet.add tid (key_set ths)) = NatSet.add tid0 (key_set ths0).
  Proof.
    unfold NatSet.add, NatSet.remove in *. erewrite nm_rm_add_rm_eq. rewrite nm_find_none_rm_eq.
    2:{ eapply key_set_find_none1. auto. }
    erewrite <- key_set_pull_add_eq. erewrite <- nm_pop_res_is_add_eq; eauto.
  Qed.

  Lemma find_some_aux
        e tid0 tid1 elem0 elem1
        (ths ths0: NatMap.t e)
        (H : nm_pop tid0 ths = Some (elem0, ths0))
        (LSRC : Th.find (elt:=e) tid1 ths0 = Some elem1)
    :
    Th.find (elt:=e) tid1 ths = Some elem1.
  Proof.
    eapply nm_pop_res_is_rm_eq in H. rewrite <- H in LSRC. rewrite NatMapP.F.remove_o in LSRC. des_ifs.
  Qed.

  Lemma find_none_aux
        e tid0 elem0
        (ths ths0: NatMap.t e)
        (H : nm_pop tid0 ths = Some (elem0, ths0))
    :
    Th.find (elt:=e) tid0 ths0 = None.
  Proof.
    eapply nm_pop_res_is_rm_eq in H. rewrite <- H. apply nm_find_rm_eq.
  Qed.

  Lemma in_aux
        e tid tid0 elem0
        (ths ths0: NatMap.t e)
        (H : nm_pop tid0 ths = Some (elem0, ths0))
        (THSRC : Th.find (elt:=e) tid ths = None)
    :
    NatMap.In (elt:=()) tid0 (NatSet.remove tid (NatSet.add tid (key_set ths))).
  Proof.
    unfold NatSet.remove, NatSet.add in *. rewrite nm_find_none_rm_add_eq.
    eapply nm_pop_find_some in H. eapply key_set_find_some1 in H. rewrite NatMapP.F.in_find_iff. ii; clarify.
    eapply key_set_find_none1 in THSRC. auto.
  Qed.

  Lemma in_add_aux
        e tid tid0 elem elem0
        (ths ths0: NatMap.t e)
        (H : nm_pop tid0 (Th.add tid elem ths) = Some (elem0, ths0))
    :
    NatMap.In tid0 (NatSet.add tid (key_set ths)).
  Proof.
    eapply nm_pop_find_some in H. eapply NatMapP.F.in_find_iff. eapply key_set_find_some1 in H.
    rewrite key_set_pull_add_eq in H. unfold NatSet.add. rewrite H. ss.
  Qed.

  Lemma proj_add_aux
        e tid tid0 elem elem0
        (ths ths0 : NatMap.t e)
        (H : nm_pop tid0 (Th.add tid elem ths) = Some (elem0, ths0))
    :
    NatSet.add tid (key_set ths) = NatSet.add tid0 (key_set ths0).
  Proof.
    eapply nm_pop_res_is_add_eq in H. unfold NatSet.add in *. erewrite <- ! key_set_pull_add_eq. erewrite H. eauto.
  Qed.

  Lemma find_some_neq_aux
        e tid tid0 tid1 elem0 elem1 elem2
        (ths ths0: NatMap.t e)
        (H : nm_pop tid0 (Th.add tid elem0 ths) = Some (elem1, ths0))
        (n0 : tid <> tid1)
        (LSRC : Th.find (elt:=e) tid1 ths0 = Some elem2)
    :
    Th.find (elt:=e) tid1 ths = Some elem2.
  Proof.
    eapply nm_pop_res_is_rm_eq in H. rewrite <- H in LSRC. rewrite NatMapP.F.remove_o in LSRC. des_ifs.
    rewrite nm_find_add_neq in LSRC; auto.
  Qed.

  Lemma find_some_neq_simpl_aux
        e tid tid0 elem elem0
        (ths ths0 : NatMap.t e)
        (H : nm_pop tid0 (Th.add tid elem ths) = Some (elem0, ths0))
        (n : tid <> tid0)
    :
    Th.find (elt:=e) tid0 ths = Some elem0.
  Proof.
    eapply nm_pop_find_some in H. rewrite nm_find_add_neq in H; auto.
  Qed.

  Lemma proj_aux2
        e tid tid0 elem elem0
        (ths ths0 : NatMap.t e)
        (TH : Th.find (elt:=e) tid ths = None)
        (H : nm_pop tid0 ths = Some (elem, ths0))
    :
    Th.remove tid (Th.add tid elem0 ths) = Th.add tid0 elem ths0.
  Proof.
    rewrite nm_rm_add_rm_eq. rewrite nm_find_none_rm_eq; auto. apply nm_pop_res_is_add_eq in H. auto.
  Qed.

End AUX.
