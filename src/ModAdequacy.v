From sflib Require Import sflib.
From ITree Require Export ITree.
From Paco Require Import paco.

Require Export Coq.Strings.String Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Program.
Require Import Permutation.

Export ITreeNotations.

From Fairness Require Import Axioms.
From Fairness Require Export ITreeLib FairBeh FairSim NatStructs.
From Fairness Require Import pind PCM World.
From Fairness Require Export Mod Concurrency.
From Fairness Require Import KnotSim LocalAdequacyAux.
From Fairness Require Import
     ModSim MSim2YOrd YOrd2Stid Stid2NoSync NoSync2Stutter
     Stutter2Knot Knot2Glob.
From Fairness Require Import SchedSim Adequacy.

Set Implicit Arguments.

Section AUX.

  Lemma list_forall2_implies
        A B (f1 f2: A -> B -> Prop) la lb
        (FA: List.Forall2 f1 la lb)
        (IMP: forall a b, (f1 a b) -> (f2 a b))
    :
    List.Forall2 f2 la lb.
  Proof.
    move FA before B. revert_until FA. induction FA; i; ss.
    econs; eauto.
  Qed.

  Inductive Forall3 (A B C : Type) (R : A -> B -> C -> Prop) : list A -> list B -> list C -> Prop :=
    Forall3_nil : Forall3 R [] [] []
  | Forall3_cons : forall (x : A) (y : B) (z : C) (l1 : list A) (l2 : list B) (l3: list C),
      R x y z -> Forall3 R l1 l2 l3 -> Forall3 R (x :: l1) (y :: l2) (z :: l3).

  Lemma list_forall3_implies_forall2_3
        A B C (f1: A -> B -> C -> Prop) (f2: A -> C -> Prop)
        la lb lc
        (FA: Forall3 f1 la lb lc)
        (IMP: forall a b c, (f1 a b c) -> (f2 a c))
    :
    List.Forall2 f2 la lc.
  Proof.
    move FA before C. revert_until FA. induction FA; i; ss.
    econs; eauto.
  Qed.

  Lemma list_forall3_implies_forall2_2
        A B C (f1: A -> B -> C -> Prop) (f2: A -> B -> Prop)
        la lb lc
        (FA: Forall3 f1 la lb lc)
        (IMP: forall a b c, (f1 a b c) -> (f2 a b))
    :
    List.Forall2 f2 la lb.
  Proof.
    move FA before C. revert_until FA. induction FA; i; ss.
    econs; eauto.
  Qed.

  Import NatMap.
  Import NatMapP.

  Lemma nm_forall3_implies_find_some
        elt1 elt2 elt3 (m1: NatMap.t elt1) (m2: NatMap.t elt2) (m3: NatMap.t elt3)
        P
        (FA: Forall3 (fun '(k1, e1) '(k2, e2) '(k3, e3) => (k1 = k2) /\ (k1 = k3) /\ (P e1 e2 e3 k1))
                     (elements m1) (elements m2) (elements m3))
    :
    forall k e1 e2 e3 (FIND1: find k m1 = Some e1) (FIND2: find k m2 = Some e2) (FIND3: find k m3 = Some e3),
      P e1 e2 e3 k.
  Proof.
    match goal with
    | FA: Forall3 _ ?_ml1 ?_ml2 ?_ml3 |- _ => remember _ml1 as ml1; remember _ml2 as ml2; remember _ml3 as ml3
    end.
    move FA before elt3. revert_until FA. induction FA; i.
    { symmetry in Heqml1; apply elements_Empty in Heqml1.
      symmetry in Heqml2; apply elements_Empty in Heqml2.
      symmetry in Heqml3; apply elements_Empty in Heqml3.
      apply nm_empty_eq in Heqml1, Heqml2, Heqml3. subst. rewrite F.empty_o in FIND1; ss.
    }
    des_ifs. des; clarify. destruct (F.eq_dec k k2); clarify.
    { eapply nm_elements_cons_find_some in Heqml1, Heqml2, Heqml3. clarify. }
    hexploit nm_elements_cons_rm. eapply Heqml1. intro RM1.
    hexploit nm_elements_cons_rm. eapply Heqml2. intro RM2.
    hexploit nm_elements_cons_rm. eapply Heqml3. intro RM3.
    eapply IHFA; eauto. rewrite nm_find_rm_neq; auto. rewrite nm_find_rm_neq; auto. rewrite nm_find_rm_neq; auto.
  Qed.

  Lemma nm_find_some_implies_forall3
        elt1 elt2 elt3 (m1: NatMap.t elt1) (m2: NatMap.t elt2) (m3: NatMap.t elt3)
        (P: elt1 -> elt2 -> elt3 -> key -> Prop)
        (WFP1: nm_wf_pair m1 m2)
        (WFP2: nm_wf_pair m1 m3)
        (PROP: forall k e1 e2 e3
                 (FIND1: find k m1 = Some e1) (FIND2: find k m2 = Some e2) (FIND3: find k m3 = Some e3), P e1 e2 e3 k)
    :
    Forall3 (fun '(k1, e1) '(k2, e2) '(k3, e3) => (k1 = k2) /\ (k1 = k3) /\ (P e1 e2 e3 k1))
            (elements m1) (elements m2) (elements m3).
  Proof.
    remember (elements m1) as l1. move l1 before elt3. revert_until l1. induction l1; i; ss.
    { symmetry in Heql1. apply elements_Empty in Heql1. dup Heql1.
      hexploit nm_wf_pair_empty. eapply WFP1. i. apply H in Heql0. apply nm_empty_eq in Heql0. subst. rewrite elements_empty.
      hexploit nm_wf_pair_empty. eapply WFP2. i. apply H0 in Heql1. apply nm_empty_eq in Heql1. subst. rewrite elements_empty.
      econs.
    }
    destruct a as [k e1]. hexploit nm_elements_cons_rm. eauto. intros ELEM1. rewrite ELEM1 in Heql1.
    destruct (elements m2) eqn:Heql2.
    { exfalso. apply elements_Empty in Heql2. hexploit nm_wf_pair_empty. eapply WFP1. i. apply H in Heql2.
      apply nm_empty_eq in Heql2. subst. rewrite elements_empty in Heql1. inv Heql1. }
    destruct (elements m3) eqn:Heql3.
    { exfalso. apply elements_Empty in Heql3. hexploit nm_wf_pair_empty. eapply WFP2. i. apply H in Heql3.
      apply nm_empty_eq in Heql3. subst. rewrite elements_empty in Heql1. inv Heql1. }
    destruct p as [k0 e2]. rename l into l2. symmetry in Heql2.
    destruct p0 as [k1 e3]. rename l0 into l3. symmetry in Heql3.
    hexploit nm_elements_cons_rm. eapply Heql2. intro ELEM2. rewrite ELEM2 in Heql2.
    hexploit nm_elements_cons_rm. eapply Heql3. intro ELEM3. rewrite ELEM3 in Heql3.
    assert (k = k0).
    { hexploit nm_wf_pair_elements_forall2. eapply WFP1. rewrite <- Heql1, <- Heql2. i. inv H. auto. }
    assert (k = k1).
    { hexploit nm_wf_pair_elements_forall2. eapply WFP2. rewrite <- Heql1, <- Heql3. i. inv H0. auto. }
    replace k0 with k in *. replace k1 with k in *. clear H H0. econs.
    2:{ rewrite ELEM2, ELEM3. eapply IHl1; eauto.
        apply nm_wf_pair_rm; auto. apply nm_wf_pair_rm; auto.
        i. eapply PROP.
        rewrite F.remove_o in FIND1. des_ifs. rewrite F.remove_o in FIND2. des_ifs. rewrite F.remove_o in FIND3. des_ifs.
    }
    splits; auto. eapply PROP. all: eapply nm_elements_cons_find_some; eauto.
  Qed.

  Inductive Forall4 (A B C D : Type) (R : A -> B -> C -> D -> Prop) : list A -> list B -> list C -> list D -> Prop :=
    Forall4_nil : Forall4 R [] [] [] []
  | Forall4_cons : forall (x : A) (y : B) (z : C) (w : D) (l1 : list A) (l2 : list B) (l3: list C) (l4: list D),
      R x y z w -> Forall4 R l1 l2 l3 l4 -> Forall4 R (x :: l1) (y :: l2) (z :: l3) (w :: l4).

  Lemma list_forall4_implies_forall2_4
        A B C D (f1: A -> B -> C -> D -> Prop) (f2: A -> D -> Prop)
        la lb lc ld
        (FA: Forall4 f1 la lb lc ld)
        (IMP: forall a b c d, (f1 a b c d) -> (f2 a d))
    :
    List.Forall2 f2 la ld.
  Proof.
    move FA before D. revert_until FA. induction FA; i; ss. econs; eauto.
  Qed.

  Lemma list_forall4_implies_forall2_3
        A B C D (f1: A -> B -> C -> D -> Prop) (f2: A -> C -> Prop)
        la lb lc ld
        (FA: Forall4 f1 la lb lc ld)
        (IMP: forall a b c d, (f1 a b c d) -> (f2 a c))
    :
    List.Forall2 f2 la lc.
  Proof.
    move FA before D. revert_until FA. induction FA; i; ss. econs; eauto.
  Qed.

  Lemma list_forall4_implies_forall2_2
        A B C D (f1: A -> B -> C -> D -> Prop) (f2: A -> B -> Prop)
        la lb lc ld
        (FA: Forall4 f1 la lb lc ld)
        (IMP: forall a b c d, (f1 a b c d) -> (f2 a b))
    :
    List.Forall2 f2 la lb.
  Proof.
    move FA before D. revert_until FA. induction FA; i; ss. econs; eauto.
  Qed.

  Import NatMap.
  Import NatMapP.

  Lemma nm_forall4_implies_find_some
        elt1 elt2 elt3 elt4 (m1: NatMap.t elt1) (m2: NatMap.t elt2) (m3: NatMap.t elt3) (m4: NatMap.t elt4)
        P
        (FA: Forall4 (fun '(k1, e1) '(k2, e2) '(k3, e3) '(k4, e4) => (k1 = k2) /\ (k1 = k3) /\ (k1 = k4) /\ (P e1 e2 e3 e4 k1))
                     (elements m1) (elements m2) (elements m3) (elements m4))
    :
    forall k e1 e2 e3 e4
      (FIND1: find k m1 = Some e1) (FIND2: find k m2 = Some e2) (FIND3: find k m3 = Some e3) (FIND4: find k m4 = Some e4),
      P e1 e2 e3 e4 k.
  Proof.
    match goal with
    | FA: Forall4 _ ?_ml1 ?_ml2 ?_ml3 ?_ml4 |- _ =>
        remember _ml1 as ml1; remember _ml2 as ml2; remember _ml3 as ml3; remember _ml4 as ml4
    end.
    move FA before elt4. revert_until FA. induction FA; i.
    { symmetry in Heqml1; apply elements_Empty in Heqml1.
      apply nm_empty_eq in Heqml1. subst. rewrite F.empty_o in FIND1; ss.
    }
    des_ifs. des; clarify. destruct (F.eq_dec k k3); clarify.
    { eapply nm_elements_cons_find_some in Heqml1, Heqml2, Heqml3, Heqml4. clarify. }
    hexploit nm_elements_cons_rm. eapply Heqml1. intro RM1.
    hexploit nm_elements_cons_rm. eapply Heqml2. intro RM2.
    hexploit nm_elements_cons_rm. eapply Heqml3. intro RM3.
    hexploit nm_elements_cons_rm. eapply Heqml4. intro RM4.
    eapply IHFA; eauto. all: rewrite nm_find_rm_neq; auto.
  Qed.

End AUX.



Section LADEQ.

  Context `{M: URA.t}.

  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable _ident_src: ID.
  Let ident_src := sum_tid _ident_src.
  Variable _ident_tgt: ID.
  Let ident_tgt := sum_tid _ident_tgt.

  Variable wf_src: WF.
  Variable wf_tgt: WF.

  Notation srcE := ((@eventE _ident_src +' cE) +' sE state_src).
  Notation tgtE := ((@eventE _ident_tgt +' cE) +' sE state_tgt).

  Variable wf_stt: Type -> Type -> WF.
  Let nm_wf_stt: Type -> Type -> WF := nm_wf_stt wf_stt.

  Let shared := shared state_src state_tgt _ident_src _ident_tgt wf_src wf_tgt.

  Notation threads_src1 R0 := (threads _ident_src (sE state_src) R0).
  Notation threads_src2 R0 := (threads2 _ident_src (sE state_src) R0).
  Notation threads_tgt R1 := (threads _ident_tgt (sE state_tgt) R1).

  Variable I: shared -> URA.car -> Prop.

  Variable St: wf_tgt.(T) -> wf_tgt.(T).
  Hypothesis lt_succ_diag_r_t: forall (t: wf_tgt.(T)), wf_tgt.(lt) t (St t).

  Lemma ModSimStutter_lsim_implies_gsim
        R0 R1 (RR: R0 -> R1 -> Prop)
        (ths_src: threads_src1 R0)
        (ths_tgt: threads_tgt R1)
        (WF: th_wf_pair ths_src ths_tgt)
        tid
        (FINDS: Th.find tid ths_src = None)
        (FINDT: Th.find tid ths_tgt = None)
        src tgt
        (st_src: state_src) (st_tgt: state_tgt)
        ps pt
        (LSIM: forall im_tgt, exists im_src (os: (nm_wf_stt R0 R1).(T)) rs_ctx o,
            (<<RSWF: Th.find tid rs_ctx = None>>) /\
              (<<OSWF: (forall tid', Th.In tid' ths_src -> Th.In tid' os) /\ (Th.find tid os = None)>>) /\
              (<<LSIM:
                forall im_tgt0
                  (FAIR: fair_update im_tgt im_tgt0 (sum_fmap_l (tids_fmap tid (NatSet.add tid (key_set ths_tgt))))),
                exists im_src0,
                  (fair_update im_src im_src0 (sum_fmap_l (tids_fmap tid (NatSet.add tid (key_set ths_src))))) /\
                    (ModSimStutter.lsim (wf_stt) I tid (local_RR I RR tid)
                          ps pt (sum_of_resources rs_ctx) (o, src) tgt
                          (NatSet.add tid (key_set ths_src),
                            im_src0, im_tgt0, st_src, st_tgt))>>) /\
              (<<LOCAL: forall tid (src: itree srcE R0) (tgt: itree tgtE R1) o r_own
                          (OWN: r_own = fst (get_resource tid rs_ctx))
                          (LSRC: Th.find tid ths_src = Some src)
                          (LTGT: Th.find tid ths_tgt = Some tgt)
                          (ORD: Th.find tid os = Some o),
                    (local_sim_pick wf_stt I RR src tgt tid o r_own)>>))
    :
    gsim wf_src wf_tgt RR
         (interp_all st_src (Th.add tid src ths_src) tid)
         (interp_all st_tgt (Th.add tid tgt ths_tgt) tid).
  Proof.
    remember (Th.map (fun th => (false, th)) ths_src) as ths_src2.
    assert (FINDS2: Th.find tid ths_src2 = None).
    { subst. rewrite NatMapP.F.map_o. rewrite FINDS. ss. }
    assert (WF0: th_wf_pair ths_src2 ths_tgt).
    { subst. unfold th_wf_pair, nm_wf_pair in *. rewrite <- WF. unfold key_set. rewrite nm_map_unit1_map_eq. auto. }
    replace ths_src with (nm_proj_v2 ths_src2).
    2:{ subst. unfold nm_proj_v2. rewrite nm_map_map_eq. ss. apply nm_map_self_eq. }
    eapply ksim_implies_gsim; auto.
    eapply Stutter2Knot.lsim_implies_ksim; eauto.
    i. specialize (LSIM im_tgt). des.
    replace (NatSet.add tid (key_set ths_src2)) with (NatSet.add tid (key_set ths_src)).
    2:{ unfold key_set. clarify. rewrite nm_map_unit1_map_eq. auto. }
    esplits; eauto.
    { i. apply OSWF. rewrite Heqths_src2 in H. eapply Th.map_2 in H. auto. }
    i. assert (SF: sf = false).
    { clarify. rewrite NatMapP.F.map_o in LSRC.
      destruct (NatMap.find (elt:=thread _ident_src (sE state_src) R0) tid0 ths_src); ss. clarify. }
    subst sf. split; i; ss. eapply LOCAL; auto.
    clarify. rewrite NatMapP.F.map_o in LSRC.
    destruct (NatMap.find (elt:=thread _ident_src (sE state_src) R0) tid0 ths_src); ss. clarify.
    Unshelve. exact true.
  Qed.

  Definition ModSimStutter_local_sim_threads
             R0 R1 (RR: R0 -> R1 -> Prop)
             (ths_src: threads_src1 R0)
             (ths_tgt: threads_tgt R1)
    :=
    List.Forall2
      (fun '(t1, src) '(t2, tgt) => (t1 = t2) /\ (ModSimStutter.local_sim wf_stt I RR src tgt))
      (Th.elements ths_src) (Th.elements ths_tgt).

  Lemma ModSimStutter_local_sim_threads_local_sim_pick
        R0 R1 (RR: R0 -> R1 -> Prop)
        (ths_src: threads_src1 R0)
        (ths_tgt: threads_tgt R1)
        (LOCAL: ModSimStutter_local_sim_threads RR ths_src ths_tgt)
        (st_src: state_src) (st_tgt: state_tgt)
        (INV: forall im_tgt, exists im_src r_shared,
            (I (NatSet.empty, im_src, im_tgt, st_src, st_tgt) r_shared) /\ (URA.wf r_shared))
    :
    forall im_tgt,
    exists (im_src0 : imap ident_src wf_src) r_shared0 (os: (nm_wf_stt R0 R1).(T)) (rs_local: local_resources),
      (I (key_set ths_src, im_src0, im_tgt, st_src, st_tgt) r_shared0) /\
        (resources_wf r_shared0 rs_local) /\
        (Forall4 (fun '(t1, src) '(t2, tgt) '(t3, r_own) '(t4, o) =>
                    (t1 = t2) /\ (t1 = t3) /\ (t1 = t4) /\ (local_sim_pick wf_stt I RR src tgt t1 o r_own))
                 (Th.elements (elt:=thread _ident_src (sE state_src) R0) ths_src)
                 (Th.elements (elt:=thread _ident_tgt (sE state_tgt) R1) ths_tgt)
                 (Th.elements rs_local) (Th.elements os)).
  Proof.
    unfold ModSimStutter_local_sim_threads in LOCAL.
    match goal with
    | FA: List.Forall2 _ ?_ml1 ?_ml2 |- _ => remember _ml1 as tl_src; remember _ml2 as tl_tgt
    end.
    move LOCAL before RR. revert_until LOCAL. induction LOCAL; i.
    { specialize (INV im_tgt). des.
      symmetry in Heqtl_src; apply NatMapP.elements_Empty in Heqtl_src.
      symmetry in Heqtl_tgt; apply NatMapP.elements_Empty in Heqtl_tgt.
      apply nm_empty_eq in Heqtl_src, Heqtl_tgt. clarify.
      esplits; ss; eauto.
      - unfold NatSet.empty in *. rewrite !key_set_empty_empty_eq. eauto.
      - instantiate (1:=@NatMap.empty _). unfold resources_wf. r_wf INV0. rewrite sum_of_resources_empty. r_solve.
      - instantiate (1:=NatMap.empty _). econs.
    }

    des_ifs. des; clarify. rename k0 into tid1, i into src1, i0 into tgt1.
    hexploit nm_elements_cons_rm. eapply Heqtl_src. intro RESS.
    hexploit nm_elements_cons_rm. eapply Heqtl_tgt. intro REST.
    hexploit IHLOCAL; clear IHLOCAL; eauto. intro IND.
    des. clear INV.
    unfold ModSimStutter.local_sim in H0.
    specialize (H0 _ _ _ _ _ _ (sum_of_resources rs_local) IND tid1 (key_set ths_src)).
    hexploit H0; clear H0.
    { econs. rewrite key_set_pull_rm_eq. eapply nm_find_rm_eq.
      erewrite <- key_set_pull_add_eq. instantiate (1:=src1).
      rewrite <- nm_find_some_rm_add_eq; auto. eapply nm_elements_cons_find_some; eauto.
    }
    { r_wf IND0. }
    { instantiate (2:=im_tgt). instantiate (1:=im_tgt). clear. ii. unfold sum_fmap_l. des_ifs. }
    i; des.
    assert (WFPAIR: nm_wf_pair (NatMap.remove (elt:=thread _ident_src (sE state_src) R0) tid1 ths_src) rs_local).
    { hexploit list_forall4_implies_forall2_3. eauto.
      { i. instantiate (1:=fun '(t1, src) '(t3, r_own) => t1 = t3). ss. des_ifs. des; auto. }
      intros FA2. rewrite RESS in FA2. apply nm_forall2_wf_pair in FA2. auto.
    }
    assert (RSL: NatMap.find (elt:=M) tid1 rs_local = None).
    { eapply nm_wf_pair_find_cases in WFPAIR. des. eapply WFPAIR. apply nm_find_rm_eq. }
    assert (WFPAIRO: nm_wf_pair (NatMap.remove (elt:=thread _ident_src (sE state_src) R0) tid1 ths_src) os).
    { hexploit list_forall4_implies_forall2_4. eauto.
      { i. instantiate (1:=fun '(t1, src) '(t4, o) => t1 = t4). ss. des_ifs. des; auto. }
      intros FA2. rewrite RESS in FA2. apply nm_forall2_wf_pair in FA2. auto.
    }
    assert (FINDOS: NatMap.find tid1 os = None).
    { eapply nm_wf_pair_find_cases in WFPAIRO. des. eapply WFPAIRO. apply nm_find_rm_eq. }

    esplits; eauto.
    { instantiate (1:=Th.add tid1 r_own rs_local). unfold resources_wf. rewrite sum_of_resources_add. r_wf VALID. auto. }
    replace (Th.elements (Th.add tid1 r_own rs_local)) with ((tid1, r_own) :: (Th.elements rs_local)).
    instantiate (1:=Th.add tid1 o os).
    replace (Th.elements (Th.add tid1 o os)) with ((tid1, o) :: (Th.elements os)).
    { econs; auto. }
    { remember (Th.add tid1 o os) as os1.
      assert (REP: os = (NatMap.remove tid1 os1)).
      { rewrite Heqos1. rewrite nm_find_none_rm_add_eq; auto. }
      rewrite REP. rewrite REP in WFPAIRO. rewrite RESS in Heqtl_src.
      eapply wf_pair_elements_cons_rm; eauto.
      { eapply nm_wf_pair_rm_inv; eauto.
        - unfold NatMap.In, NatMap.Raw.PX.In. exists src1. unfold NatMap.Raw.PX.MapsTo. ss.
          unfold Th.elements, Th.Raw.elements in Heqtl_src. rewrite <- Heqtl_src. econs 1. ss.
        - rewrite Heqos1. apply NatMapP.F.add_in_iff. auto.
      }
      { rewrite Heqos1. rewrite nm_find_add_eq; auto. }
    }
    { remember (Th.add tid1 r_own rs_local) as rs_local1.
      assert (REP: rs_local = (NatMap.remove tid1 rs_local1)).
      { rewrite Heqrs_local1. rewrite nm_find_none_rm_add_eq; auto. }
      rewrite REP. rewrite REP in WFPAIR. rewrite RESS in Heqtl_src.
      eapply wf_pair_elements_cons_rm; eauto.
      { eapply nm_wf_pair_rm_inv; eauto.
        - unfold NatMap.In, NatMap.Raw.PX.In. exists src1. unfold NatMap.Raw.PX.MapsTo. ss.
          unfold Th.elements, Th.Raw.elements in Heqtl_src. rewrite <- Heqtl_src. econs 1. ss.
        - rewrite Heqrs_local1. apply NatMapP.F.add_in_iff. auto.
      }
      { rewrite Heqrs_local1. rewrite nm_find_add_eq; auto. }
    }
  Qed.

  Theorem ModSimStutter_local_sim_implies_gsim
          R0 R1 (RR: R0 -> R1 -> Prop)
          (ths_src: threads_src1 R0)
          (ths_tgt: threads_tgt R1)
          (LOCAL: ModSimStutter_local_sim_threads RR ths_src ths_tgt)
          (st_src: state_src) (st_tgt: state_tgt)
          (INV: forall im_tgt, exists im_src r_shared,
              (I (NatSet.empty, im_src, im_tgt, st_src, st_tgt) r_shared) /\ (URA.wf r_shared))
          tid
          (* (INS: Th.In tid ths_src) *)
          (* (INT: Th.In tid ths_tgt) *)
    :
    gsim wf_src wf_tgt RR
         (interp_all st_src ths_src tid)
         (interp_all st_tgt ths_tgt tid).
  Proof.
    assert (WFP: nm_wf_pair ths_src ths_tgt).
    { eapply nm_forall2_wf_pair. eapply list_forall2_implies. eauto. i. des_ifs. des; auto. }
    destruct (NatMapP.F.In_dec ths_src tid).
    2:{ destruct (NatMapP.F.In_dec ths_tgt tid).
        { eapply nm_wf_pair_find_cases in WFP. des. eapply NatMapP.F.not_find_in_iff in n.
          eapply WFP in n. eapply NatMapP.F.not_find_in_iff in n. clarify. }
        eapply NatMapP.F.not_find_in_iff in n. eapply NatMapP.F.not_find_in_iff in n0.
        unfold interp_all.
        rewrite (unfold_interp_sched_nondet_None tid _ _ n).
        rewrite (unfold_interp_sched_nondet_None tid _ _ n0).
        rewrite !interp_state_vis. unfold gsim. i.
        specialize (INV mt). des. exists im_src, false, false.
        rewrite <- bind_trigger. pfold. econs 10.
    }
    rename i into INS.
    assert (INT: Th.In tid ths_tgt).
    { destruct (NatMapP.F.In_dec ths_tgt tid); auto.
      apply nm_wf_pair_sym in WFP. eapply nm_wf_pair_find_cases in WFP. des.
      eapply NatMapP.F.not_find_in_iff in n. eapply WFP in n.
      eapply NatMapP.F.not_find_in_iff in n. clarify.
    }
    clear WFP.

    unfold ModSimStutter_local_sim_threads in LOCAL.
    eapply NatMapP.F.in_find_iff in INS, INT.
    destruct (Th.find tid ths_src) eqn:FINDS.
    2:{ clarify. }
    destruct (Th.find tid ths_tgt) eqn:FINDT.
    2:{ clarify. }
    clear INS INT. rename i into src0, i0 into tgt0.
    remember (Th.remove tid ths_src) as ths_src0.
    remember (Th.remove tid ths_tgt) as ths_tgt0.
    assert (POPS: nm_pop tid ths_src = Some (src0, ths_src0)).
    { unfold nm_pop. rewrite FINDS. rewrite Heqths_src0. auto. }
    assert (POPT: nm_pop tid ths_tgt = Some (tgt0, ths_tgt0)).
    { unfold nm_pop. rewrite FINDT. rewrite Heqths_tgt0. auto. }
    i. replace ths_src with (Th.add tid src0 ths_src0).
    2:{ symmetry; eapply nm_pop_res_is_add_eq; eauto. }
    replace ths_tgt with (Th.add tid tgt0 ths_tgt0).
    2:{ symmetry; eapply nm_pop_res_is_add_eq; eauto. }

    assert (WFST0: nm_wf_pair ths_src0 ths_tgt0).
    { subst. eapply nm_wf_pair_rm. eapply nm_forall2_wf_pair.
      eapply list_forall2_implies; eauto. i. des_ifs. des; auto.
    }
    eapply ModSimStutter_lsim_implies_gsim; auto.
    { eapply nm_pop_res_find_none; eauto. }
    { eapply nm_pop_res_find_none; eauto. }

    cut (forall im_tgt0, exists im_src0 r_shared0 (os0: (nm_wf_stt R0 R1).(T)) rs_ctx0,
            (I (key_set ths_src, im_src0, im_tgt0, st_src, st_tgt) r_shared0) /\
              (resources_wf r_shared0 rs_ctx0) /\
              (nm_wf_pair ths_src os0) /\
              (forall (tid0 : Th.key) (src : thread _ident_src (sE state_src) R0)
                 (tgt : thread _ident_tgt (sE state_tgt) R1) o r_own,
                  (r_own = fst (get_resource tid0 rs_ctx0)) ->
                  (Th.find (elt:=thread _ident_src (sE state_src) R0) tid0 ths_src = Some src) ->
                  (Th.find (elt:=thread _ident_tgt (sE state_tgt) R1) tid0 ths_tgt = Some tgt) ->
                  (Th.find tid0 os0 = Some o) ->
                  local_sim_pick wf_stt I RR src tgt tid0 o r_own)).
    { i. specialize (H im_tgt). des.
      assert (POPOS: exists o os, nm_pop tid os0 = Some (o, os)).
      { hexploit nm_wf_pair_pop_cases. eapply H1. instantiate (1:=tid). i; des; eauto.
        unfold nm_pop in H3. rewrite FINDS in H3. ss. }
      des. exists im_src0, os, (snd (get_resource tid rs_ctx0)), o. splits.
      - eapply get_resource_snd_find_eq_none.
      - i. eapply nm_wf_pair_pop_cases in H1. des. erewrite POPS in H1. ss.
        rewrite POPS in H1; rewrite POPOS in H4. clarify.
        eapply nm_wf_pair_find_cases in H5. des. eapply NatMapP.F.in_find_iff. eapply H1.
        eapply NatMapP.F.in_find_iff. auto.
      - eapply find_none_aux; eauto.
      - ii. specialize (H2 tid src0 tgt0 o (fst (get_resource tid rs_ctx0))). hexploit H2; clear H2; auto.
        { eapply nm_pop_find_some; eauto. }
        i. unfold local_sim_pick in H2.
        assert (SETS: NatSet.add tid (key_set ths_src0) = key_set ths_src).
        { subst. rewrite key_set_pull_rm_eq. unfold NatSet.add.
          rewrite <- nm_find_some_rm_add_eq; auto. eapply key_set_find_some1; eauto.
        }
        hexploit H2; clear H2. eapply H.
        { instantiate (1:=sum_of_resources (snd (get_resource tid rs_ctx0))).
          hexploit resources_wf_get_wf. eapply H0.
          2:{ i. des. eapply WF. }
          instantiate (1:=tid). destruct (get_resource tid rs_ctx0); ss.
        }
        { rewrite <- SETS; eauto. unfold nm_wf_pair in WFST0. rewrite WFST0. eauto. }
        rewrite !SETS. i; des. esplits; eauto.
      - i. eapply H2.
        { rewrite OWN. eapply get_resource_rs_neq. destruct (tid_dec tid tid0); auto. clarify.
          rewrite nm_find_rm_eq in LSRC. ss. }
        eapply find_some_aux; eauto. eapply find_some_aux; eauto. eapply find_some_aux; eauto.
    }

    cut (forall im_tgt, exists (im_src0 : imap ident_src wf_src) r_shared0 (os0: (nm_wf_stt R0 R1).(T)) rs_ctx0,
            (I (key_set ths_src, im_src0, im_tgt, st_src, st_tgt) r_shared0) /\
              (resources_wf r_shared0 rs_ctx0) /\
              (Forall3 (fun '(t1, src) '(t2, tgt) '(t3, o) =>
                          (t1 = t2) /\ (t1 = t3) /\
                            (local_sim_pick wf_stt I RR src tgt t1 o (fst (get_resource t1 rs_ctx0))))
                       (Th.elements (elt:=thread _ident_src (sE state_src) R0) ths_src)
                       (Th.elements (elt:=thread _ident_tgt (sE state_tgt) R1) ths_tgt)
                       (Th.elements os0))).
    { intro FA. i. specialize (FA im_tgt0). des. esplits; eauto.
      { hexploit list_forall3_implies_forall2_3. eauto.
        { i. instantiate (1:= fun '(t1, src) '(t3, o) => t1 = t3). ss. des_ifs. des; auto. }
        intros FA2. apply nm_forall2_wf_pair in FA2. eauto.
      }
      i. subst. eapply nm_forall3_implies_find_some in FA1; eauto.
    }

    i. hexploit ModSimStutter_local_sim_threads_local_sim_pick; eauto. intros FAALL. instantiate (1:=im_tgt) in FAALL.
    clear LOCAL. des.
    exists im_src0, r_shared0, os, rs_local. splits; auto.
    clear - FAALL1.
    eapply nm_find_some_implies_forall3.
    { hexploit list_forall4_implies_forall2_2. eauto.
      { i. instantiate (1:=fun '(t1, src) '(t2, tgt) => t1 = t2). ss. des_ifs. des; auto. }
      intros FA2. apply nm_forall2_wf_pair; auto.
    }
    { hexploit list_forall4_implies_forall2_4. eauto.
      { i. instantiate (1:=fun '(t1, src) '(t4, o) => t1 = t4). ss. des_ifs. des; auto. }
      intros FA2. apply nm_forall2_wf_pair; auto.
    }
    { i. hexploit nm_forall4_implies_find_some. eapply FAALL1. all: eauto.
      2:{ ss. eauto. }
      assert (WFPAIR: nm_wf_pair ths_src rs_local).
      { hexploit list_forall4_implies_forall2_3. eauto.
        { i. instantiate (1:=fun '(t1, src) '(t3, r_own) => t1 = t3). ss. des_ifs. des; auto. }
        intros FA2. apply nm_forall2_wf_pair in FA2. auto.
      }
      hexploit nm_wf_pair_find_cases. eapply WFPAIR. i. des. clear H. hexploit H0.
      { ii. rewrite FIND1 in H. ss. }
      i. destruct (NatMap.find k rs_local) eqn:FRS; ss. erewrite get_resource_find_some_fst; eauto.
    }
    Unshelve. all: exact true.
  Qed.

End LADEQ.


Section ADEQ.

  Definition program := list (fname * (list Val))%type.

  Definition fn2th (m: Mod.t) (fn: fname) (args: list Val): @thread (Mod.ident m) (sE (Mod.state m)) Val :=
    match Mod.funs m fn with
    | Some ktr => ktr args
    | None => (Vis (inl1 (inl1 Undefined)) (Empty_set_rect _))
    end.

  Definition fn2th_wf (m: Mod.t) (fn: fname): Prop :=
    match Mod.funs m fn with
    | Some ktr => True
    | None => False
    end.

  Fixpoint _numbering {E} (l: list E) (n: NatMap.key): list (NatMap.key * E) :=
    match l with
    | hd :: tl => (n, hd) :: (_numbering tl (S n))
    | [] => []
    end.

  Definition numbering {E} (l: list E): list (NatMap.key * E) := _numbering l O.

  Definition prog2ths (m: Mod.t) (p: program): @threads (Mod.ident m) (sE (Mod.state m)) Val :=
    let pre_threads := List.map (fun '(fn, args) => fn2th m fn args) p in
    NatMapP.of_list (numbering pre_threads).

  Definition prog2ths_wf (m: Mod.t) (p: program): Prop :=
    Forall (fun '(fn, args) => fn2th_wf m fn) p.

  Lemma _numbering_cons
        E (l: list E) n x
    :
    _numbering (x :: l) n = (n, x) :: (_numbering l (S n)).
  Proof. reflexivity. Qed.

  Lemma of_list_cons
        elt (l: list (NatMap.key * elt)) k e
    :
    NatMapP.of_list ((k, e) :: l) = Th.add k e (NatMapP.of_list l).
  Proof. reflexivity. Qed.

  Theorem modsim_adequacy
          m_src m_tgt
          (MSIM: ModSim.ModSim.mod_sim m_src m_tgt)
    :
    forall tid (p: program),
      Adequacy.improves (interp_all m_src.(Mod.st_init) (prog2ths m_src p) tid)
                        (interp_all m_tgt.(Mod.st_init) (prog2ths m_tgt p) tid).
  Proof.
    apply modsim_implies_yord_mod in MSIM.
    apply yord_implies_stid_mod in MSIM.
    apply stid_implies_nosync_mod in MSIM.
    apply nosync_implies_stutter_mod in MSIM.
    inv MSIM. i.
    eapply Adequacy.adequacy. eapply wf_tgt_inhabited. eapply wf_tgt_open.
    instantiate (1:=wf_src).


  (*   Forall_Exists_dec: *)
  (* forall [A : Type] (P : A -> Prop), *)
  (* (forall x : A, {P x} + {~ P x}) -> *)
  (* forall l : list A, {Forall P l} + {Exists (fun x : A => ~ P x) l} *)

  (*   Exists_exists: *)
  (* forall [A : Type] (P : A -> Prop) (l : list A), Exists P l <-> (exists x : A, In x l /\ P x) *)

    eapply ModSimStutter_local_sim_implies_gsim. 3: eapply init.
    instantiate (1:= fun o0 => @epsilon _ wf_tgt_inhabited (fun o1 => wf_tgt.(lt) o0 o1)).
    { i. hexploit (@epsilon_spec _ wf_tgt_inhabited (fun o1 => wf_tgt.(lt) t o1)); eauto. }
    instantiate (1:=wf_stt).
    unfold ModSimStutter_local_sim_threads, prog2ths. unfold numbering.
    remember 0 as k. clear Heqk. revert_until p.
    induction p; i.
    { ss. unfold NatMap.Raw.empty. econs. }
    rewrite !map_cons, !_numbering_cons. destruct a as [fn args].
    rewrite !of_list_cons. eapply nm_find_some_implies_forall2.
    { admit. }
    i. destruct (tid_dec k k0); clarify.
    { clear IHp. rewrite nm_find_add_eq in FIND1, FIND2. clarify. unfold fn2th.
      specialize (funs fn args). des_ifs; ss.
      admit.
    }
    rewrite nm_find_add_neq in FIND1, FIND2; auto.
    specialize (IHp (S k)). eapply nm_forall2_implies_find_some in IHp; eauto.
  Abort.

End ADEQ.
