From iris.algebra Require Import cmra updates.
From sflib Require Import sflib.
From Paco Require Import paco.

Require Export Coq.Strings.String Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Program.
Require Import Permutation.

From Fairness Require Import Axioms.
From Fairness Require Export ITreeLib FairBeh FairSim NatStructsLarge.
From Fairness Require Import pind PCM World.
From Fairness Require Export Mod Concurrency.
From Fairness Require Import KnotSim LocalAdequacyAux.
From Fairness Require Import
     ModSim MSim2YOrd YOrd2Stid Stid2NoSync NoSync2Stutter
     Stutter2Knot Knot2Glob.
From Fairness Require Import SchedSim Adequacy.
From Fairness Require Import DisableSsreflect.


Set Implicit Arguments.


Section LADEQ.

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
  Let nm_wf_stt: Type -> Type -> WF := nm_wf_stt wf_stt.

  Let shared := shared state_src state_tgt _ident_src _ident_tgt wf_src wf_tgt.

  Notation threads_src1 R0 := (threads _ident_src (sE state_src) R0).
  Notation threads_src2 R0 := (threads2 _ident_src (sE state_src) R0).
  Notation threads_tgt R1 := (threads _ident_tgt (sE state_tgt) R1).

  (* Variable I: shared -> (cmra_car M) -> Prop. *)

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
        (LSIM: forall im_tgt,
          exists (I: shared -> (cmra_car M) -> Prop),
          exists im_src (os: (nm_wf_stt R0 R1).(T)) rs_ctx o,
            (<<RSWF: Th.find tid rs_ctx = None>>) /\
              (<<OSWF: (forall tid', Th.In tid' ths_src -> Th.In tid' os) /\ (Th.find tid os = None)>>) /\
              (<<LSIM:
                forall im_tgt0
                  (FAIR: fair_update im_tgt im_tgt0 (prism_fmap inlp (tids_fmap tid (NatSet.add tid (key_set ths_tgt))))),
                exists im_src0,
                  (fair_update im_src im_src0 (prism_fmap inlp (tids_fmap tid (NatSet.add tid (key_set ths_src))))) /\
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
    clarify. subst. rewrite NatMapP.F.map_o in LSRC.
    destruct (NatMap.find (elt:=thread _ident_src (sE state_src) R0) tid0 ths_src); ss. clarify.
    Unshelve. exact true.
  Qed.

  Definition ModSimStutter_local_sim_threads
             (I: shared -> (cmra_car M) -> Prop)
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
        (* (LOCAL: ModSimStutter_local_sim_threads RR ths_src ths_tgt) *)
        (st_src: state_src) (st_tgt: state_tgt)
        (INV: forall im_tgt, exists (I: shared -> (cmra_car M) -> Prop), exists im_src r_shared,
            (ModSimStutter_local_sim_threads I RR ths_src ths_tgt) /\
              (I (NatSet.empty, im_src, im_tgt, st_src, st_tgt) r_shared) /\ (✓ r_shared))
    :
    forall im_tgt,
    exists (I: shared -> (cmra_car M) -> Prop),
    exists (im_src0 : imap ident_src wf_src) r_shared0 (os: (nm_wf_stt R0 R1).(T)) (rs_local: local_resources),
      (I (key_set ths_src, im_src0, im_tgt, st_src, st_tgt) r_shared0) /\
        (resources_wf r_shared0 rs_local) /\
        (Forall4 (fun '(t1, src) '(t2, tgt) '(t3, r_own) '(t4, o) =>
                    (t1 = t2) /\ (t1 = t3) /\ (t1 = t4) /\ (local_sim_pick wf_stt I RR src tgt t1 o r_own))
                 (Th.elements (elt:=thread _ident_src (sE state_src) R0) ths_src)
                 (Th.elements (elt:=thread _ident_tgt (sE state_tgt) R1) ths_tgt)
                 (Th.elements rs_local) (Th.elements os)).
  Proof.
    i. specialize (INV im_tgt). des. rename INV into LOCAL. exists I. move I after St.
    unfold ModSimStutter_local_sim_threads in LOCAL.
    match goal with
    | FA: List.Forall2 _ ?_ml1 ?_ml2 |- _ => remember _ml1 as tl_src; remember _ml2 as tl_tgt
    end.
    move LOCAL before RR. revert_until LOCAL. induction LOCAL; i.
    {
      (* specialize (INV im_tgt). des. *)
      symmetry in Heqtl_src; apply NatMapP.elements_Empty in Heqtl_src.
      symmetry in Heqtl_tgt; apply NatMapP.elements_Empty in Heqtl_tgt.
      apply nm_empty_eq in Heqtl_src, Heqtl_tgt. clarify.
      esplits; ss; eauto.
      - unfold NatSet.empty in *. rewrite !key_set_empty_empty_eq. eauto.
      - instantiate (1:=@NatMap.empty _). unfold resources_wf. r_wf INV1.
      - instantiate (1:=NatMap.empty _). econs.
    }

    des_ifs. des; clarify. rename k0 into tid1, i into src1, i0 into tgt1.
    hexploit nm_elements_cons_rm. eapply Heqtl_src. intro RESS.
    hexploit nm_elements_cons_rm. eapply Heqtl_tgt. intro REST.
    hexploit IHLOCAL; clear IHLOCAL; eauto. intro IND.
    des.
    (* clear INV. *)
    unfold ModSimStutter.local_sim in H0.
    specialize (H0 _ _ _ _ _ _ (sum_of_resources rs_local) IND tid1 (key_set ths_src)).
    hexploit H0; clear H0.
    { econs. rewrite key_set_pull_rm_eq. eapply nm_find_rm_eq.
      erewrite <- key_set_pull_add_eq. instantiate (1:=src1).
      rewrite <- nm_find_some_rm_add_eq; auto. eapply nm_elements_cons_find_some; eauto.
    }
    { r_wf IND0. }
    { instantiate (1:=im_tgt). clear. ii. unfold prism_fmap; ss. des_ifs. }
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
    { instantiate (1:=Th.add tid1 r_own rs_local).
      unfold resources_wf. rewrite sum_of_resources_add; auto.
      r_wf VALID.
    }
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

  Lemma forall4_implies_gsim
        R0 R1 (RR: R0 -> R1 -> Prop)
        (ths_src: threads_src1 R0)
        (ths_tgt: threads_tgt R1)
        (st_src: state_src) (st_tgt: state_tgt)
        tid
    :
    (forall im_tgt,
      exists (I: shared -> (cmra_car M) -> Prop),
      exists (im_src0 : imap ident_src wf_src) r_shared0 (os: (nm_wf_stt R0 R1).(T)) (rs_local: local_resources),
        (I (key_set ths_src, im_src0, im_tgt, st_src, st_tgt) r_shared0) /\
          (resources_wf r_shared0 rs_local) /\
          (Forall4 (fun '(t1, src) '(t2, tgt) '(t3, r_own) '(t4, o) =>
                      (t1 = t2) /\ (t1 = t3) /\ (t1 = t4) /\ (local_sim_pick wf_stt I RR src tgt t1 o r_own))
                   (Th.elements (elt:=thread _ident_src (sE state_src) R0) ths_src)
                   (Th.elements (elt:=thread _ident_tgt (sE state_tgt) R1) ths_tgt)
                   (Th.elements rs_local) (Th.elements os))) ->
    gsim wf_src wf_tgt RR
         (interp_all st_src ths_src tid)
         (interp_all st_tgt ths_tgt tid).
  Proof.
    intros USIM. ii. assert (WFP: nm_wf_pair ths_src ths_tgt).
    { specialize (USIM mt). des. eapply list_forall4_implies_forall2_2 in USIM1.
      2:{ i. instantiate (1:= fun '(k1, _) '(k2, _) => k1 = k2). des_ifs. des; clarify. }
      eapply nm_forall2_wf_pair.  auto.
    }
    cut (gsim wf_src wf_tgt RR (interp_all st_src ths_src tid) (interp_all st_tgt ths_tgt tid)).
    { i. specialize (H mt). auto. }
    clear mt.

    destruct (NatMapP.F.In_dec ths_src tid).
    2:{ destruct (NatMapP.F.In_dec ths_tgt tid).
        { eapply nm_wf_pair_find_cases in WFP. des. eapply NatMapP.F.not_find_in_iff in n.
          eapply WFP in n. eapply NatMapP.F.not_find_in_iff in n. clarify. }
        eapply NatMapP.F.not_find_in_iff in n. eapply NatMapP.F.not_find_in_iff in n0.
        unfold interp_all.
        rewrite (unfold_interp_sched_nondet_None tid _ _ n).
        rewrite (unfold_interp_sched_nondet_None tid _ _ n0).
        rewrite !interp_state_vis. unfold gsim. i.
        specialize (USIM mt). des. exists im_src0, false, false.
        rewrite <- bind_trigger. pfold. econs 10.
    }
    rename i into INS.
    assert (INT: Th.In tid ths_tgt).
    { destruct (NatMapP.F.In_dec ths_tgt tid); auto.
      apply nm_wf_pair_sym in WFP. eapply nm_wf_pair_find_cases in WFP. des.
      eapply NatMapP.F.not_find_in_iff in n. eapply WFP in n.
      eapply NatMapP.F.not_find_in_iff in n. clarify.
    }
    (* clear WFP. *)

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
    { subst. eapply nm_wf_pair_rm. auto. }
    clear WFP.
    eapply ModSimStutter_lsim_implies_gsim; auto.
    { eapply nm_pop_res_find_none; eauto. }
    { eapply nm_pop_res_find_none; eauto. }

    cut (forall im_tgt0,
            exists (I: shared -> (cmra_car M) -> Prop),
          exists im_src0 r_shared0 (os0: (nm_wf_stt R0 R1).(T)) rs_ctx0,
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
      des. exists I, im_src0, os, (snd (get_resource tid rs_ctx0)), o. splits.
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
          hexploit (resources_wf_get_wf (M:=M)). eapply H0.
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

    cut (forall im_tgt,
            exists (I: shared -> (cmra_car M) -> Prop),
          exists (im_src0 : imap ident_src wf_src) r_shared0 (os0: (nm_wf_stt R0 R1).(T)) rs_ctx0,
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

    i. rename USIM into FAALL. specialize (FAALL im_tgt). des.
    exists I, im_src0, r_shared0, os, rs_local. splits; auto.
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
      { ii. erewrite FIND1 in H. ss. }
      i. destruct (NatMap.find k rs_local) eqn:FRS; ss. erewrite get_resource_find_some_fst; eauto.
    }
    Unshelve. all: exact true.
  Qed.

  Theorem ModSimStutter_local_sim_implies_gsim
          R0 R1 (RR: R0 -> R1 -> Prop)
          (ths_src: threads_src1 R0)
          (ths_tgt: threads_tgt R1)
          (* (LOCAL: ModSimStutter_local_sim_threads RR ths_src ths_tgt) *)
          (st_src: state_src) (st_tgt: state_tgt)
          (INV: forall im_tgt, exists (I: shared -> (cmra_car M) -> Prop), exists im_src r_shared,
              (ModSimStutter_local_sim_threads I RR ths_src ths_tgt) /\
                (I (NatSet.empty, im_src, im_tgt, st_src, st_tgt) r_shared) /\ (✓ r_shared))
          tid
    :
    gsim wf_src wf_tgt RR
         (interp_all st_src ths_src tid)
         (interp_all st_tgt ths_tgt tid).
  Proof.
    eapply forall4_implies_gsim. i.
    i. hexploit ModSimStutter_local_sim_threads_local_sim_pick; eauto.
  Qed.

End LADEQ.


Section ADEQ.

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

  Lemma mod_funs_cases
        (m: Mod.t)
    :
    (forall fn, Mod.funs m fn = None) \/ (exists fn ktr, Mod.funs m fn = Some ktr).
  Proof.
    destruct (classic (forall fn, Mod.funs m fn = None)); auto.
    apply Classical_Pred_Type.not_all_ex_not in H. right. des.
    destruct (Mod.funs m n) eqn:FUNS; ss; eauto.
  Qed.

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
    destruct (mod_funs_cases m_src).
    { ii. specialize (init mt). des. exists im_src, false, false.
      destruct (Th.find tid (prog2ths m_src p)) eqn:FIND.
      2:{ unfold interp_all. rewrite unfold_interp_sched_nondet_None.
          rewrite interp_state_vis. rewrite <- bind_trigger. pfold. econs 10. auto.
      }
      unfold interp_all. erewrite unfold_interp_sched_nondet_Some.
      2: eauto.
      rename init0 into funs.
      assert (UB: i = (Vis (inl1 (inl1 (inl1 Undefined))) (Empty_set_rect _))).
      { revert_until funs. clear. i. unfold prog2ths, numbering in FIND.
        remember 0 as k. clear Heqk. move p after tid. revert_until p. induction p; i; ss.
        destruct a as [fn args]. unfold NatMapP.uncurry in FIND. ss.
        destruct (tid_dec tid k); clarify.
        { rewrite nm_find_add_eq in FIND. clarify. unfold fn2th. rewrite H. auto. }
        rewrite nm_find_add_neq in FIND; auto. eapply IHp; eauto.
      }
      clarify. rewrite interp_thread_vis_eventE. ired. rewrite interp_state_vis.
      rewrite <- bind_trigger. pfold. econs 10.
    }

    des. rename fn into fn0, ktr into ktr0, H into SOME0.
    eapply (ModSimStutter_local_sim_implies_gsim (M:=world)).
    instantiate (1:= fun o0 => @epsilon _ wf_tgt_inhabited (fun o1 => wf_tgt.(lt) o0 o1)).
    { i. hexploit (@epsilon_spec _ wf_tgt_inhabited (fun o1 => wf_tgt.(lt) t o1)); eauto. }
    instantiate (1:=wf_stt).
    i. specialize (init im_tgt). des. esplits; eauto.
    unfold ModSimStutter_local_sim_threads, prog2ths. unfold numbering.
    remember 0 as k. clear Heqk. move p before k. revert_until p.
    induction p; i.
    { ss. unfold NatMap.Raw.empty. econs. }
    rewrite !map_cons. rewrite !_numbering_cons. destruct a as [fn args].
    rewrite !of_list_cons. eapply nm_find_some_implies_forall2.
    { apply nm_wf_pair_add. clear. move p after m_src. revert_until p. induction p; i.
      { ss. apply nm_wf_pair_empty_empty_eq. }
      ss. destruct a as [fn args]. unfold NatMapP.uncurry. ss. eapply nm_wf_pair_add.
      eauto.
    }
    i. destruct (tid_dec k k0); clarify.
    { clear IHp. rewrite nm_find_add_eq in FIND1.
      rewrite nm_find_add_eq in FIND2. clarify. unfold fn2th.
      rename init0 into funs.
      dup funs. specialize (funs0 fn0 ([]: list Val)↑). rewrite SOME0 in funs0.
      specialize (funs fn args). des_ifs; ss.
      unfold local_sim in funs0. ii.
      specialize (funs0 _ _ _ _ _ _ _ INV _ _ THS VALID _ UPD). des.
      esplits; eauto. i. specialize (funs0 _ _ _ _ _ _ _ INV1 VALID1 _ TGT). des.
      esplits. eapply SRC. i. instantiate (1:=o).
      pfold. eapply pind6_fold. rewrite <- bind_trigger. eapply lsim_UB.
    }
    rewrite nm_find_add_neq in FIND1;
    rewrite nm_find_add_neq in FIND2; auto.
    specialize (IHp (S k)). eapply nm_forall2_implies_find_some in IHp; eauto.
  Qed.

End ADEQ.



Section USERADEQ.

  Theorem usersim_adequacy
          m_src m_tgt
          p_src p_tgt
          (MSIM: ModSim.UserSim.sim m_src m_tgt p_src p_tgt)
    :
    forall tid,
      Adequacy.improves (interp_all m_src.(Mod.st_init) p_src tid)
                        (interp_all m_tgt.(Mod.st_init) p_tgt tid).
  Proof.
    apply modsim_implies_yord_user in MSIM.
    apply yord_implies_stid_user in MSIM.
    apply stid_implies_nosync_user in MSIM.
    apply nosync_implies_stutter_user in MSIM.
    inv MSIM. i.
    eapply Adequacy.adequacy. eapply wf_tgt_inhabited. eapply wf_tgt_open.
    instantiate (1:=wf_src).
    set (St := fun o0 => @epsilon _ wf_tgt_inhabited (fun o1 => wf_tgt.(lt) o0 o1)).
    assert (lt_succ_diag_r_tgt: forall (t: wf_tgt.(T)), wf_tgt.(lt) t (St t)).
    { i. unfold St. hexploit (@epsilon_spec _ wf_tgt_inhabited (fun o1 => wf_tgt.(lt) t o1)); eauto. }
    eapply forall4_implies_gsim. eauto.
    instantiate (1:=wf_stt). i. specialize (funs im_tgt). des. exists I. esplits; eauto.
  Qed.

End USERADEQ.
