From iris.algebra Require Import cmra updates.

From sflib Require Import sflib.
From Paco Require Import paco.

Require Export Coq.Strings.String.
Require Import Coq.Classes.RelationClasses.
Require Import Program.
Require Import Permutation.

From Fairness Require Import Axioms.
From Fairness Require Export ITreeLib FairBeh FairSim NatStructsLarge.
From Fairness Require Import pind PCM World.
From Fairness Require Export Mod Concurrency.
From Fairness Require Import KnotSim LocalAdequacyAux.

Set Implicit Arguments.

Section PROOF.

  Ltac gfold := gfinal; right; pfold.

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

  Let kshared := kshared state_src state_tgt _ident_src _ident_tgt wf_src wf_tgt.

  Notation threads_src1 R0 := (threads _ident_src (sE state_src) R0).
  Notation threads_src2 R0 := (threads2 _ident_src (sE state_src) R0).
  Notation threads_tgt R1 := (threads _ident_tgt (sE state_tgt) R1).

  Lemma gsim_ret_emp
        R0 R1 (RR: R0 -> R1 -> Prop)
        (r : forall x x0 : Type,
            (x -> x0 -> Prop) -> bool -> (@imap ident_src wf_src) -> bool -> (@imap ident_tgt wf_tgt) -> _ -> _ -> Prop)
        (ths_src : threads_src2 R0) (ths_tgt : threads_tgt R1)
        tid ps pt
        (THSRC : Th.find (elt:=bool * thread _ident_src (sE state_src) R0) tid ths_src = None)
        (THTGT : Th.find (elt:=thread _ident_tgt (sE state_tgt) R1) tid ths_tgt = None)
        (WF : th_wf_pair ths_src ths_tgt)
        (st_src : state_src) (st_tgt : state_tgt)
        (mt : @imap ident_tgt wf_tgt)
        (ms : @imap ident_src wf_src)
        (r_src : R0)
        (r_tgt : R1)
        (RET : RR r_src r_tgt)
        (NILS : Th.is_empty (elt:=bool * thread _ident_src (sE state_src) R0) ths_src = true)
        (NILT : Th.is_empty (elt:=thread _ident_tgt (sE state_tgt) R1) ths_tgt = true)
    :
    gpaco9 (_sim (wft:=wf_tgt)) (cpn9 (_sim (wft:=wf_tgt))) bot9 r R0 R1 RR ps ms pt mt
           (interp_all st_src (Th.add tid (Ret r_src) (nm_proj_v2 ths_src)) tid)
           (interp_all st_tgt (Th.add tid (Ret r_tgt) ths_tgt) tid).
  Proof.
    unfold interp_all. erewrite ! unfold_interp_sched_nondet_Some.
    2:{ instantiate (1:= Ret r_tgt). rewrite nm_find_add_eq; auto. }
    2:{ instantiate (1:= Ret r_src). rewrite nm_find_add_eq; auto. }
    rewrite ! interp_thread_ret. rewrite ! bind_ret_l.
    assert (EMPS: NatMap.is_empty (NatSet.remove tid (key_set (Th.add tid (Ret r_src) (nm_proj_v2 ths_src)))) = true).
    { apply NatMap.is_empty_2 in NILS. apply NatMap.is_empty_1. rewrite key_set_pull_add_eq. unfold NatSet.remove.
      rewrite nm_find_none_rm_add_eq; auto. do 2 apply nm_map_empty1. auto.
      unfold key_set, nm_proj_v2. do 2 rewrite NatMapP.F.map_o. rewrite THSRC. ss. }
    assert (EMPT: NatMap.is_empty (NatSet.remove tid (key_set (Th.add tid (Ret r_tgt) ths_tgt))) = true).
    { apply NatMap.is_empty_2 in NILT. apply NatMap.is_empty_1. rewrite key_set_pull_add_eq. unfold NatSet.remove.
      rewrite nm_find_none_rm_add_eq; auto. do 1 apply nm_map_empty1. auto.
      unfold key_set. rewrite NatMapP.F.map_o. rewrite THTGT. ss. }
    rewrite EMPS EMPT. rewrite ! interp_sched_ret. rewrite ! interp_state_tau. rewrite ! interp_state_ret.
    guclo sim_indC_spec. eapply sim_indC_tauL. guclo sim_indC_spec. eapply sim_indC_tauR.
    guclo sim_indC_spec. eapply sim_indC_ret. auto.
  Qed.

  Lemma kgsim_ret_cont
        R0 R1 (RR : R0 -> R1 -> Prop)
        (r : forall x x0 : Type,
            (x -> x0 -> Prop) -> bool -> (@imap ident_src wf_src) -> bool -> (@imap ident_tgt wf_tgt) -> _ -> _ -> Prop)
        (CIH : forall (ths_src : threads_src2 R0) (ths_tgt : threads_tgt R1) (tid : Th.key),
            Th.find (elt:=bool * thread _ident_src (sE state_src) R0) tid ths_src = None ->
            Th.find (elt:=thread _ident_tgt (sE state_tgt) R1) tid ths_tgt = None ->
            th_wf_pair ths_src ths_tgt ->
            forall (sf : bool) (src : thread _ident_src (sE state_src) R0)
              (tgt : thread _ident_tgt (sE state_tgt) R1) (st_src : state_src)
              (st_tgt : state_tgt) (ps pt : bool) (o : T (wf_stt R0 R1)) rs_ctx
              (mt : imap ident_tgt wf_tgt) (ms : imap ident_src wf_src),
              sim_knot (M:=M) (wf_stt) RR ths_src ths_tgt tid rs_ctx ps pt (sf, src) tgt
                       (ms, mt, st_src, st_tgt) o ->
              r R0 R1 RR ps ms pt mt (interp_all st_src (Th.add tid src (nm_proj_v2 ths_src)) tid)
                (interp_all st_tgt (Th.add tid tgt ths_tgt) tid))
        (o : T (wf_stt R0 R1)) ps
        (IHo : (ps = true) \/
                 (forall y : T (wf_stt R0 R1),
                     lt (wf_stt R0 R1) y o ->
                     forall (ths_src : threads_src2 R0) (ths_tgt : threads_tgt R1) (tid : Th.key),
                       Th.find (elt:=bool * thread _ident_src (sE state_src) R0) tid ths_src = None ->
                       Th.find (elt:=thread _ident_tgt (sE state_tgt) R1) tid ths_tgt = None ->
                       th_wf_pair ths_src ths_tgt ->
                       forall (sf : bool) (src : thread _ident_src (sE state_src) R0)
                         (tgt : thread _ident_tgt (sE state_tgt) R1) (st_src : state_src)
                         (st_tgt : state_tgt) (ps pt : bool) rs_ctx (mt : imap ident_tgt wf_tgt)
                         (ms : imap ident_src wf_src),
                         sim_knot (M:=M) (wf_stt) RR ths_src ths_tgt tid rs_ctx ps pt (sf, src) tgt
                                  (ms, mt, st_src, st_tgt) y ->
                         gpaco9 (_sim (wft:=wf_tgt)) (cpn9 (_sim (wft:=wf_tgt))) bot9 r R0 R1 RR ps ms pt mt
                                (interp_all st_src (Th.add tid src (nm_proj_v2 ths_src)) tid)
                                (interp_all st_tgt (Th.add tid tgt ths_tgt) tid)))
        (ths_src : threads_src2 R0) (ths_tgt : threads_tgt R1)
        tid pt
        (THSRC : Th.find (elt:=bool * thread _ident_src (sE state_src) R0) tid ths_src = None)
        (THTGT : Th.find (elt:=thread _ident_tgt (sE state_tgt) R1) tid ths_tgt = None)
        (WF : th_wf_pair ths_src ths_tgt)
        (st_src : state_src) (st_tgt : state_tgt)
        mt ms (r_src : R0) (r_tgt : R1) o1
        r_own r_shared0 rs_local
        (RSWF: resources_wf r_shared0 (NatMap.add tid r_own rs_local))
        (STUTTER : lt (wf_stt R0 R1) o1 o)
        (RET : RR r_src r_tgt)
        (NNILS : Th.is_empty (elt:=bool * thread _ident_src (sE state_src) R0) ths_src = false)
        (NNILT : Th.is_empty (elt:=thread _ident_tgt (sE state_tgt) R1) ths_tgt = false)
        (KSIM0 : forall tid0 : NatMap.key,
            nm_pop tid0 ths_src = None /\ nm_pop tid0 ths_tgt = None \/
              (exists (b : bool) (th_src : thread _ident_src (sE state_src) R0)
                 (thsl0 : NatMap.t (bool * thread _ident_src (sE state_src) R0))
                 (th_tgt : thread _ident_tgt (sE state_tgt) R1) (thsr0 : threads_tgt R1),
                  nm_pop tid0 ths_src = Some (b, th_src, thsl0) /\
                    nm_pop tid0 ths_tgt = Some (th_tgt, thsr0) /\
                    (b = true ->
                     forall im_tgt0 : imap ident_tgt wf_tgt,
                       fair_update mt im_tgt0 (prism_fmap inlp (tids_fmap tid0 (key_set thsr0))) ->
                         upaco10 (fun r => pind10 (__sim_knot (wf_stt) RR r) top10) bot10 thsl0 thsr0 tid0 (snd (get_resource tid0 (NatMap.add tid r_own rs_local))) true true
                                (b, Vis (((|Yield)|)|)%sum (fun _ : () => th_src)) th_tgt
                                (ms, im_tgt0, st_src, st_tgt) o1) /\
                    (b = false ->
                     forall im_tgt0 : imap ident_tgt wf_tgt,
                       fair_update mt im_tgt0 (prism_fmap inlp (tids_fmap tid0 (key_set thsr0))) ->
                       exists (im_src0 : imap ident_src wf_src),
                         fair_update ms im_src0 (prism_fmap inlp (tids_fmap tid0 (key_set thsl0))) /\
                           (upaco10 (fun r => pind10 (__sim_knot (M:=M) (wf_stt) RR r) top10) bot10 thsl0 thsr0 tid0 (snd (get_resource tid0 (NatMap.add tid r_own rs_local))) true true
                                      (b, th_src) th_tgt
                                      (im_src0, im_tgt0, st_src, st_tgt) o1))))
    :
    gpaco9 (_sim (wft:=wf_tgt)) (cpn9 (_sim (wft:=wf_tgt))) bot9 r R0 R1 RR ps ms pt mt
           (interp_all st_src (Th.add tid (Ret r_src) (nm_proj_v2 ths_src)) tid)
           (interp_all st_tgt (Th.add tid (Ret r_tgt) ths_tgt) tid).
  Proof.
    ss. unfold interp_all. erewrite ! unfold_interp_sched_nondet_Some; eauto using nm_find_add_eq.
    rewrite ! interp_thread_ret. rewrite ! bind_ret_l.
    assert (EMPS: NatMap.is_empty (NatSet.remove tid (key_set (Th.add tid (Ret r_src) (nm_proj_v2 ths_src)))) = false).
    { clear KSIM0.
      rewrite key_set_pull_add_eq. unfold NatSet.remove.
      rewrite nm_find_none_rm_add_eq; auto.
      2:{ unfold key_set, nm_proj_v2. do 2 rewrite NatMapP.F.map_o. rewrite THSRC. ss. }
      match goal with | |- ?lhs = _ => destruct lhs eqn:CASE; ss end.
      apply NatMap.is_empty_2 in CASE. do 2 apply nm_map_empty2 in CASE.
      apply NatMap.is_empty_1 in CASE. clarify. }
    assert (EMPT: NatMap.is_empty (NatSet.remove tid (key_set (Th.add tid (Ret r_tgt) ths_tgt))) = false).
    { clear KSIM0.
      rewrite key_set_pull_add_eq. unfold NatSet.remove.
      rewrite nm_find_none_rm_add_eq; auto.
      2:{ unfold key_set. rewrite NatMapP.F.map_o. rewrite THTGT. ss. }
      match goal with | |- ?lhs = _ => destruct lhs eqn:CASE; ss end.
      apply NatMap.is_empty_2 in CASE. do 1 apply nm_map_empty2 in CASE.
      apply NatMap.is_empty_1 in CASE. clarify. }
    rewrite EMPS EMPT; clear EMPS EMPT.
    match goal with
    | |- gpaco9 _ _ _ _ _ _ _ _ _ _ _ ?_src_temp _ => remember _src_temp as src_temp eqn:TEMP
    end.
    rewrite ! interp_state_tau. guclo sim_indC_spec. eapply sim_indC_tauR.
    rewrite bind_trigger. rewrite interp_sched_vis. ss.
    rewrite interp_state_vis. rewrite <- ! bind_trigger.
    guclo sim_indC_spec. eapply sim_indC_chooseR. intro tid0.
    rewrite interp_state_tau.
    do 2 (guclo sim_indC_spec; eapply sim_indC_tauR).
    specialize (KSIM0 tid0). revert IHo. des; i.
    { assert (POPT: nm_pop tid0 (NatSet.remove tid (key_set (Th.add tid (Ret r_tgt) ths_tgt))) = None).
      { rewrite key_set_pull_add_eq. unfold NatSet.remove. rewrite nm_find_none_rm_add_eq.
        eapply nm_pop_none_map1; auto. unfold key_set. rewrite NatMapP.F.map_o. rewrite THTGT. ss. }
      rewrite POPT; clear POPT.
      rewrite bind_trigger. rewrite interp_sched_vis. ss. rewrite interp_state_vis. rewrite <- bind_trigger.
      guclo sim_indC_spec. eapply sim_indC_chooseR. intro x; destruct x. }
    assert (POPT: nm_pop tid0 (NatSet.remove tid (key_set (Th.add tid (Ret r_tgt) ths_tgt))) = Some (tt, key_set thsr0)).
    { rewrite key_set_pull_add_eq. unfold key_set. unfold NatSet.remove. rewrite nm_find_none_rm_add_eq.
      eapply nm_pop_some_map1 in KSIM1. erewrite KSIM1. ss. rewrite NatMapP.F.map_o. rewrite THTGT. ss. }
    rewrite POPT; clear POPT.
    rewrite bind_trigger. rewrite interp_sched_vis. rewrite interp_state_vis. rewrite <- bind_trigger. ss.
    guclo sim_indC_spec. eapply sim_indC_fairR. i. rewrite interp_sched_tau. do 2 rewrite interp_state_tau.
    do 3 (guclo sim_indC_spec; eapply sim_indC_tauR).
    destruct b.

    - hexploit KSIM2; clear KSIM2 KSIM3; ss.
      eauto. i.
      assert (CHANGE: src_temp = interp_all st_src (Th.add tid0 (Vis (((|Yield)|)|)%sum (fun _ : () => th_src)) (nm_proj_v2 thsl0)) tid0).
      { unfold interp_all. erewrite unfold_interp_sched_nondet_Some; eauto using nm_find_add_eq.
        rewrite interp_thread_vis_yield. ired. rewrite TEMP.
        assert (RA: Th.remove tid (Th.add tid (Ret r_src) (nm_proj_v2 ths_src)) = nm_proj_v2 ths_src).
        { rewrite nm_find_none_rm_add_eq; auto. unfold nm_proj_v2. rewrite NatMapP.F.map_o. rewrite THSRC. ss. }
        rewrite ! RA.
        assert (RA1: Th.add tid0 th_src (Th.add tid0 (Vis (((|Yield)|)|)%sum (fun _ : () => th_src)) (nm_proj_v2 thsl0)) = nm_proj_v2 ths_src).
        { rewrite nm_add_add_eq. unfold nm_proj_v2. replace th_src with (snd (true, th_src)); auto.
          rewrite nm_map_add_comm_eq. f_equal. apply nm_pop_res_is_add_eq in KSIM0. auto. }
        rewrite ! RA1.
        assert (RA2: NatSet.remove tid (key_set (Th.add tid (Ret r_src) (nm_proj_v2 ths_src))) = key_set (nm_proj_v2 ths_src)).
        { rewrite key_set_pull_add_eq. unfold NatSet.remove, nm_proj_v2, key_set. rewrite nm_find_none_rm_add_eq; auto.
          do 2 rewrite NatMapP.F.map_o. rewrite THSRC. ss. }
        rewrite RA2.
        assert (RA3: (NatSet.add tid0 (NatSet.remove tid0 (key_set (Th.add tid0 (Vis (((|Yield)|)|)%sum (fun _ : () => th_src)) (nm_proj_v2 thsl0))))) = key_set (nm_proj_v2 ths_src)).
        { rewrite key_set_pull_add_eq. unfold NatSet.add, NatSet.remove, nm_proj_v2, key_set.
          rewrite nm_add_rm_eq. rewrite nm_add_add_eq. apply nm_pop_res_is_add_eq in KSIM0. rewrite KSIM0.
          rewrite <- 2 nm_map_add_comm_eq. ss. }
        rewrite RA3. ss.
      }
      rewrite CHANGE; clear CHANGE.
      match goal with
      | |- gpaco9 _ _ _ _ _ _ _ _ _ _ _ _ ?_tgt => replace _tgt with (interp_all st_tgt (Th.add tid0 th_tgt thsr0) tid0)
      end.
      2:{ assert (PROJT: Th.remove tid (Th.add tid (Ret r_tgt) ths_tgt) = Th.add tid0 th_tgt thsr0).
          { eapply proj_aux2; eauto. }
          rewrite PROJT. unfold interp_all.
          replace (NatSet.remove tid0 (key_set (Th.add tid0 th_tgt thsr0))) with (key_set thsr0); auto.
          rewrite key_set_pull_add_eq. unfold NatSet.remove. rewrite nm_find_none_rm_add_eq; auto.
          apply key_set_find_none1. eapply nm_pop_res_find_none; eauto.
      }
      destruct H; ss.
      des.
      + subst. gfold. eapply sim_progress; auto. right. eapply CIH.
        eapply find_none_aux; eauto. eapply find_none_aux; eauto.
        { hexploit nm_wf_pair_pop_cases; eauto. instantiate (1:=tid0). i; des; clarify. }
        eapply ksim_set_prog; eauto.
      + eapply IHo. eauto.
        eapply find_none_aux; eauto. eapply find_none_aux; eauto.
        { hexploit nm_wf_pair_pop_cases; eauto. instantiate (1:=tid0). i; des; clarify. }
        eapply ksim_set_prog. eauto.

    - hexploit KSIM3; clear KSIM2 KSIM3; ss.
      assert (RA: (NatSet.remove tid (NatSet.add tid (key_set ths_tgt))) = (key_set ths_tgt)).
      { unfold NatSet.remove, NatSet.add. rewrite nm_find_none_rm_add_eq; auto.
        unfold key_set. rewrite NatMapP.F.map_o. rewrite THTGT. ss. }
      eauto. i. revert IHo. des; i. clarify.
      rewrite interp_state_tau. guclo sim_indC_spec; eapply sim_indC_tauL.
      rewrite bind_trigger. rewrite interp_sched_vis. rewrite interp_state_vis. rewrite <- bind_trigger.
      guclo sim_indC_spec. eapply sim_indC_chooseL. exists tid0.
      assert (POPS: nm_pop tid0 (NatSet.remove tid (key_set (Th.add tid (Ret r_src) (nm_proj_v2 ths_src)))) = Some (tt, key_set thsl0)).
      { rewrite key_set_pull_add_eq. unfold NatSet.remove, key_set, nm_proj_v2. rewrite nm_find_none_rm_add_eq.
        do 2 eapply nm_pop_some_map1 in KSIM0. erewrite KSIM0. ss. do 2 f_equal. rewrite nm_map_unit1_map_eq. auto.
        rewrite nm_map_map_eq. rewrite NatMapP.F.map_o. rewrite THSRC. ss. }
      rewrite POPS; clear POPS.
      rewrite interp_state_tau. do 2 (guclo sim_indC_spec; eapply sim_indC_tauL).
      rewrite bind_trigger. rewrite interp_sched_vis. rewrite interp_state_vis. rewrite <- bind_trigger.
      guclo sim_indC_spec. eapply sim_indC_fairL.
      esplits; eauto.
      rewrite interp_sched_tau. do 2 rewrite interp_state_tau. do 3 (guclo sim_indC_spec; eapply sim_indC_tauL).
      pclearbot.
      match goal with
      | |- gpaco9 _ _ _ _ _ _ _ _ _ _ _ _ ?_tgt => replace _tgt with (interp_all st_tgt (Th.add tid0 th_tgt thsr0) tid0)
      end.
      2:{ assert (PROJT: Th.remove tid (Th.add tid (Ret r_tgt) ths_tgt) = Th.add tid0 th_tgt thsr0).
          { eapply proj_aux2; eauto. }
          rewrite PROJT. unfold interp_all.
          replace (NatSet.remove tid0 (key_set (Th.add tid0 th_tgt thsr0))) with (key_set thsr0); auto.
          rewrite key_set_pull_add_eq. unfold NatSet.remove. rewrite nm_find_none_rm_add_eq; auto.
          apply key_set_find_none1. eapply nm_pop_res_find_none; eauto.
      }
      match goal with
      | |- gpaco9 _ _ _ _ _ _ _ _ _ _ _ ?_src _ => replace _src with (interp_all st_src (Th.add tid0 th_src (nm_proj_v2 thsl0)) tid0)
      end.
      2:{ assert (PROJS: Th.remove tid (Th.add tid (Ret r_src) (nm_proj_v2 ths_src)) = Th.add tid0 th_src (nm_proj_v2 thsl0)).
          { unfold nm_proj_v2. rewrite nm_find_none_rm_add_eq. apply nm_pop_res_is_add_eq in KSIM0. rewrite KSIM0.
            rewrite <- nm_map_add_comm_eq. ss. rewrite NatMapP.F.map_o. rewrite THSRC. ss. }
          rewrite PROJS. unfold interp_all.
          replace (NatSet.remove tid0 (key_set (Th.add tid0 th_src (nm_proj_v2 thsl0)))) with (key_set thsl0); auto.
          rewrite key_set_pull_add_eq. unfold NatSet.remove. rewrite nm_find_none_rm_add_eq; auto.
          2:{ unfold key_set, nm_proj_v2. rewrite nm_map_map_eq. rewrite NatMapP.F.map_o.
              apply nm_pop_res_find_none in KSIM0. rewrite KSIM0. ss. }
          unfold key_set, nm_proj_v2. rewrite nm_map_unit1_map_eq. auto.
      }
      gfold. eapply sim_progress. right. eapply CIH.
      eapply find_none_aux; eauto. eapply find_none_aux; eauto.
      { hexploit nm_wf_pair_pop_cases; eauto. instantiate (1:=tid0). i; des; clarify. }
      eapply ksim_set_prog; eauto. all: auto.
  Qed.

  Lemma kgsim_sync
        R0 R1 (RR : R0 -> R1 -> Prop)
        (r : forall x x0 : Type,
            (x -> x0 -> Prop) -> bool -> (@imap ident_src wf_src) -> bool -> (@imap ident_tgt wf_tgt) -> _ -> _ -> Prop)
        (CIH : forall (ths_src : threads_src2 R0) (ths_tgt : threads_tgt R1) (tid : Th.key),
            Th.find (elt:=bool * thread _ident_src (sE state_src) R0) tid ths_src = None ->
            Th.find (elt:=thread _ident_tgt (sE state_tgt) R1) tid ths_tgt = None ->
            th_wf_pair ths_src ths_tgt ->
            forall (sf : bool) (src : thread _ident_src (sE state_src) R0)
              (tgt : thread _ident_tgt (sE state_tgt) R1) (st_src : state_src)
              (st_tgt : state_tgt) (ps pt : bool) (o : T (wf_stt R0 R1)) r_ctx
              (mt : imap ident_tgt wf_tgt) (ms : imap ident_src wf_src),
              sim_knot (M:=M) (wf_stt) RR ths_src ths_tgt tid r_ctx ps pt (sf, src) tgt
                       (ms, mt, st_src, st_tgt) o ->
              r R0 R1 RR ps ms pt mt (interp_all st_src (Th.add tid src (nm_proj_v2 ths_src)) tid)
                (interp_all st_tgt (Th.add tid tgt ths_tgt) tid))
        (o : T (wf_stt R0 R1)) ps
        (IHo : (ps = true) \/
                 (forall y : T (wf_stt R0 R1),
                     lt (wf_stt R0 R1) y o ->
                     forall (ths_src : threads_src2 R0) (ths_tgt : threads_tgt R1) (tid : Th.key),
                       Th.find (elt:=bool * thread _ident_src (sE state_src) R0) tid ths_src = None ->
                       Th.find (elt:=thread _ident_tgt (sE state_tgt) R1) tid ths_tgt = None ->
                       th_wf_pair ths_src ths_tgt ->
                       forall (sf : bool) (src : thread _ident_src (sE state_src) R0)
                         (tgt : thread _ident_tgt (sE state_tgt) R1) (st_src : state_src)
                         (st_tgt : state_tgt) (ps pt : bool) r_ctx (mt : imap ident_tgt wf_tgt)
                         (ms : imap ident_src wf_src),
                         sim_knot (M:=M) (wf_stt) RR ths_src ths_tgt tid r_ctx ps pt (sf, src) tgt
                                  (ms, mt, st_src, st_tgt) y ->
                         gpaco9 (_sim (wft:=wf_tgt)) (cpn9 (_sim (wft:=wf_tgt))) bot9 r R0 R1 RR ps ms pt mt
                                (interp_all st_src (Th.add tid src (nm_proj_v2 ths_src)) tid)
                                (interp_all st_tgt (Th.add tid tgt ths_tgt) tid)))
        (ths_src : threads_src2 R0) (ths_tgt : threads_tgt R1) tid pt
        (THSRC : Th.find (elt:=bool * thread _ident_src (sE state_src) R0) tid ths_src = None)
        (THTGT : Th.find (elt:=thread _ident_tgt (sE state_tgt) R1) tid ths_tgt = None)
        (WF : th_wf_pair ths_src ths_tgt)
        (st_src : state_src) (st_tgt : state_tgt) mt ms
        (ktr_src : () -> thread _ident_src (sE state_src) R0)
        (ktr_tgt : () -> thread _ident_tgt (sE state_tgt) R1)
        r_own r_shared0 rs_ctx
        (RSWF: resources_wf r_shared0 (NatMap.add tid r_own rs_ctx))
        (KSIM0 : forall tid0 : NatMap.key,
            nm_pop tid0 (Th.add tid (true, ktr_src ()) ths_src) = None /\
              nm_pop tid0 (Th.add tid (ktr_tgt ()) ths_tgt) = None \/
              (exists (b : bool) (th_src : thread _ident_src (sE state_src) R0)
                 (thsl1 : NatMap.t (bool * thread _ident_src (sE state_src) R0))
                 (th_tgt : thread _ident_tgt (sE state_tgt) R1) (thsr1 : threads_tgt R1),
                  nm_pop tid0 (Th.add tid (true, ktr_src ()) ths_src) = Some (b, th_src, thsl1) /\
                    nm_pop tid0 (Th.add tid (ktr_tgt ()) ths_tgt) = Some (th_tgt, thsr1) /\
                    (b = true ->
                     (forall im_tgt0 : imap ident_tgt wf_tgt,
                         fair_update mt im_tgt0 (prism_fmap inlp (tids_fmap tid0 (key_set thsr1))) ->
                         exists (o0 : T (wf_stt R0 R1)),
                           lt (wf_stt R0 R1) o0 o /\
                             upaco10
                               (fun r => pind10 (__sim_knot (wf_stt) RR r) top10) bot10 thsl1 thsr1 tid0 (snd (get_resource tid0 (NatMap.add tid r_own rs_ctx))) true true
                               (b, Vis (((|Yield)|)|)%sum (fun _ : () => th_src)) th_tgt
                               (ms, im_tgt0, st_src, st_tgt) o0)) /\
                    (b = false ->
                     (forall im_tgt0 : imap ident_tgt wf_tgt,
                         fair_update mt im_tgt0 (prism_fmap inlp (tids_fmap tid0 (key_set thsr1))) ->
                         exists (im_src0 : imap ident_src wf_src) o0,
                           fair_update ms im_src0 (prism_fmap inlp (tids_fmap tid0 (key_set thsl1))) /\
                             lt (wf_stt R0 R1) o0 o /\
                             (upaco10
                                (fun r => pind10 (__sim_knot (M:=M) (wf_stt) RR r) top10) bot10 thsl1 thsr1 tid0 (snd (get_resource tid0 (NatMap.add tid r_own rs_ctx))) true true
                                (b, th_src) th_tgt
                                (im_src0, im_tgt0, st_src, st_tgt) o0)))))
    :
    gpaco9 (_sim (wft:=wf_tgt)) (cpn9 (_sim (wft:=wf_tgt))) bot9 r R0 R1 RR ps ms pt mt
           (interp_all st_src (Th.add tid (Vis (((|Yield)|)|)%sum ktr_src) (nm_proj_v2 ths_src)) tid)
           (interp_all st_tgt (Th.add tid (Vis (((|Yield)|)|)%sum ktr_tgt) ths_tgt) tid).
  Proof.
    match goal with
    | |- gpaco9 _ _ _ _ _ _ _ _ _ _ _ ?_src_temp _ => remember _src_temp as src_temp eqn:TEMP
    end.
    unfold interp_all. erewrite ! unfold_interp_sched_nondet_Some; auto using nm_find_add_eq.
    rewrite interp_thread_vis_yield. ired.
    rewrite interp_state_tau. guclo sim_indC_spec; eapply sim_indC_tauR.
    rewrite bind_trigger. rewrite interp_sched_vis. ss.
    rewrite interp_state_vis. rewrite <- ! bind_trigger.
    guclo sim_indC_spec. eapply sim_indC_chooseR. intro tid0.
    rewrite interp_state_tau.
    do 2 (guclo sim_indC_spec; eapply sim_indC_tauR).
    specialize (KSIM0 tid0). revert IHo; des; i.
    { assert (POPT: nm_pop tid0 (NatSet.add tid (NatSet.remove tid (key_set (Th.add tid (x <- ITree.trigger (((|Yield)|)|)%sum;; ktr_tgt x) ths_tgt)))) = None).
      { rewrite key_set_pull_add_eq. unfold NatSet.remove, NatSet.add. rewrite nm_find_none_rm_add_eq.
        erewrite <- key_set_pull_add_eq. unfold key_set. eapply nm_pop_none_map1; eauto.
        unfold key_set. rewrite NatMapP.F.map_o. rewrite THTGT. ss. }
      rewrite POPT; clear POPT.
      rewrite ! bind_trigger. rewrite interp_sched_vis. ss. rewrite interp_state_vis. rewrite <- bind_trigger.
      guclo sim_indC_spec. eapply sim_indC_chooseR. intro x; destruct x. }
    assert (POPT: nm_pop tid0 (NatSet.add tid (NatSet.remove tid (key_set (Th.add tid (x <- ITree.trigger (((|Yield)|)|)%sum;; ktr_tgt x) ths_tgt)))) = Some (tt, key_set thsr1)).
    { rewrite key_set_pull_add_eq. unfold NatSet.remove, NatSet.add. rewrite nm_find_none_rm_add_eq.
      erewrite <- key_set_pull_add_eq. unfold key_set. eapply nm_pop_some_map1 in KSIM1. erewrite KSIM1. ss.
      unfold key_set. rewrite NatMapP.F.map_o. rewrite THTGT. ss.
    }
    rewrite POPT; clear POPT.
    rewrite ! bind_trigger. rewrite interp_sched_vis. rewrite interp_state_vis. rewrite <- bind_trigger. ss.
    guclo sim_indC_spec. eapply sim_indC_fairR. i. rewrite interp_sched_tau. do 2 rewrite interp_state_tau.
    do 3 (guclo sim_indC_spec; eapply sim_indC_tauR).
    destruct b.

    - hexploit KSIM2; clear KSIM2 KSIM3; ss. eauto.
      i. revert IHo; des; i.
      assert (CHANGE: src_temp = interp_all st_src (Th.add tid0 (Vis (((|Yield)|)|)%sum (fun _ : () => th_src)) (nm_proj_v2 thsl1)) tid0).
      { rewrite TEMP. unfold interp_all. erewrite ! unfold_interp_sched_nondet_Some; auto using nm_find_add_eq.
        rewrite ! interp_thread_vis_yield. ired.
        assert (RA: Th.add tid (ktr_src ()) (Th.add tid (Vis (((|Yield)|)|)%sum ktr_src) (nm_proj_v2 ths_src)) = Th.add tid0 th_src (Th.add tid0 (Vis (((|Yield)|)|)%sum (fun _ : () => th_src)) (nm_proj_v2 thsl1))).
        { rewrite ! nm_add_add_eq. unfold nm_proj_v2. apply nm_pop_res_is_add_eq in KSIM0.
          replace (ktr_src ()) with (snd (true, ktr_src ())); auto. replace th_src with (snd (true, th_src)); auto.
          rewrite ! nm_map_add_comm_eq. rewrite KSIM0. ss.
        }
        rewrite ! RA.
        assert (RA1: (NatSet.add tid (NatSet.remove tid (key_set (Th.add tid (Vis (((|Yield)|)|)%sum ktr_src) (nm_proj_v2 ths_src))))) = (NatSet.add tid0 (NatSet.remove tid0 (key_set (Th.add tid0 (Vis (((|Yield)|)|)%sum (fun _ : () => th_src)) (nm_proj_v2 thsl1)))))).
        { unfold NatSet.add, NatSet.remove. rewrite <- !key_set_pull_rm_eq. erewrite <- !key_set_pull_add_eq. f_equal.
          rewrite ! nm_add_rm_eq. rewrite ! nm_add_add_eq. unfold nm_proj_v2. apply nm_pop_res_is_add_eq in KSIM0.
          erewrite ! nm_map_add_comm_eq. erewrite KSIM0. ss.
        }
        rewrite ! RA1. auto.
      }
      rewrite CHANGE; clear CHANGE.
      hexploit H0; clear H0. eauto. i. destruct H0; ss.
      match goal with
      | |- gpaco9 _ _ _ _ _ _ _ _ _ _ _ _ ?_tgt => replace _tgt with (interp_all st_tgt (Th.add tid0 th_tgt thsr1) tid0)
      end.
      2:{ unfold interp_all.
          replace (Th.add tid (ktr_tgt ()) (Th.add tid (Vis (((|Yield)|)|)%sum (fun x : () => ktr_tgt x)) ths_tgt)) with (Th.add tid0 th_tgt thsr1).
          2:{ rewrite nm_add_add_eq. apply nm_pop_res_is_add_eq in KSIM1. auto. }
          replace (NatSet.remove tid0 (key_set (Th.add tid0 th_tgt thsr1))) with (key_set thsr1).
          2:{ rewrite key_set_pull_add_eq. unfold NatSet.remove. rewrite nm_find_none_rm_add_eq. auto.
              unfold key_set. rewrite NatMapP.F.map_o. eapply find_none_aux in KSIM1. rewrite KSIM1; eauto.
          }
          auto.
      }
      des.
      + subst.
        gfold. eapply sim_progress; auto. right; eapply CIH.
        eapply find_none_aux; eauto. eapply find_none_aux; eauto.
        { apply nm_pop_res_is_rm_eq in KSIM0, KSIM1. rewrite <- KSIM0, <- KSIM1. eapply nm_wf_pair_rm. eapply nm_wf_pair_add. auto. }
        replace (NatSet.add tid0 (key_set thsl1)) with (NatSet.add tid (key_set ths_src)).
        2:{ unfold NatSet.add. apply nm_pop_res_is_add_eq in KSIM0. erewrite <- !key_set_pull_add_eq. erewrite KSIM0. eauto. }
        replace (NatSet.add tid0 (key_set thsr1)) with (NatSet.add tid (key_set ths_tgt)).
        2:{ unfold NatSet.add. apply nm_pop_res_is_add_eq in KSIM1. erewrite <- !key_set_pull_add_eq. erewrite KSIM1. eauto. }
        eapply ksim_set_prog; eauto.
      + eapply IHo; eauto.
        eapply find_none_aux; eauto. eapply find_none_aux; eauto.
        { apply nm_pop_res_is_rm_eq in KSIM0, KSIM1. rewrite <- KSIM0, <- KSIM1. eapply nm_wf_pair_rm. eapply nm_wf_pair_add. auto. }
        replace (NatSet.add tid0 (key_set thsl1)) with (NatSet.add tid (key_set ths_src)).
        2:{ unfold NatSet.add. apply nm_pop_res_is_add_eq in KSIM0. erewrite <- !key_set_pull_add_eq. erewrite KSIM0. eauto. }
        replace (NatSet.add tid0 (key_set thsr1)) with (NatSet.add tid (key_set ths_tgt)).
        2:{ unfold NatSet.add. apply nm_pop_res_is_add_eq in KSIM1. erewrite <- !key_set_pull_add_eq. erewrite KSIM1. eauto. }
        eapply ksim_set_prog; eauto.

    - hexploit KSIM3; clear KSIM2 KSIM3; ss. eauto.
      i. revert IHo; des; i. clarify. unfold interp_all.
      erewrite unfold_interp_sched_nondet_Some; auto using nm_find_add_eq.
      rewrite interp_thread_vis_yield. ired. rewrite interp_state_tau. guclo sim_indC_spec; eapply sim_indC_tauL.
      rewrite bind_trigger. rewrite interp_sched_vis. rewrite interp_state_vis.
      rewrite <- bind_trigger. guclo sim_indC_spec. eapply sim_indC_chooseL. exists tid0.
      assert (POPS: nm_pop tid0 (NatSet.add tid (NatSet.remove tid (key_set (Th.add tid (Vis (((|Yield)|)|)%sum ktr_src) (nm_proj_v2 ths_src))))) = Some (tt, key_set thsl1)).
      { rewrite key_set_pull_add_eq. unfold NatSet.remove, NatSet.add. rewrite nm_find_none_rm_add_eq.
        erewrite <- key_set_pull_add_eq. unfold key_set, nm_proj_v2. erewrite nm_map_add_comm_eq.
        rewrite nm_map_map_eq. erewrite nm_pop_some_map1; eauto.
        unfold key_set, nm_proj_v2. rewrite nm_map_map_eq. rewrite NatMapP.F.map_o. rewrite THSRC. ss.
      }
      rewrite POPS; clear POPS. rewrite interp_state_tau. do 2 (guclo sim_indC_spec; eapply sim_indC_tauL).
      rewrite bind_trigger. rewrite interp_sched_vis. rewrite interp_state_vis. rewrite <- bind_trigger.
      guclo sim_indC_spec. eapply sim_indC_fairL.
      hexploit H0; clear H0. eauto. i. revert IHo; des; i; pclearbot.
      esplits; eauto. eauto.
      rewrite interp_sched_tau. do 2 rewrite interp_state_tau. do 3 (guclo sim_indC_spec; eapply sim_indC_tauL).
      match goal with
      | |- gpaco9 _ _ _ _ _ _ _ _ _ _ _ _ ?_tgt => replace _tgt with (interp_all st_tgt (Th.add tid0 th_tgt thsr1) tid0)
      end.
      2:{ unfold interp_all.
          replace (Th.add tid (ktr_tgt ()) (Th.add tid (Vis (((|Yield)|)|)%sum (fun x : () => ktr_tgt x)) ths_tgt)) with (Th.add tid0 th_tgt thsr1).
          2:{ rewrite nm_add_add_eq. apply nm_pop_res_is_add_eq in KSIM1. auto. }
          replace (NatSet.remove tid0 (key_set (Th.add tid0 th_tgt thsr1))) with (key_set thsr1).
          2:{ rewrite key_set_pull_add_eq. unfold NatSet.remove. rewrite nm_find_none_rm_add_eq. auto.
              unfold key_set. rewrite NatMapP.F.map_o. eapply find_none_aux in KSIM1. rewrite KSIM1; eauto.
          }
          auto.
      }
      match goal with
      | |- gpaco9 _ _ _ _ _ _ _ _ _ _ _ ?_src _ => replace _src with (interp_all st_src (Th.add tid0 th_src (nm_proj_v2 thsl1)) tid0)
      end.
      2:{ unfold interp_all.
          replace (Th.add tid (ktr_src ()) (Th.add tid (Vis (((|Yield)|)|)%sum ktr_src) (nm_proj_v2 ths_src))) with (Th.add tid0 th_src (nm_proj_v2 thsl1)).
          2:{ rewrite nm_add_add_eq. apply nm_pop_res_is_add_eq in KSIM0. unfold nm_proj_v2.
              replace (ktr_src ()) with (snd (true, ktr_src ())); auto. replace th_src with (snd (false, th_src)); auto.
              rewrite ! nm_map_add_comm_eq. rewrite KSIM0. ss.
          }
          replace (NatSet.remove tid0 (key_set (Th.add tid0 th_src (nm_proj_v2 thsl1)))) with (key_set thsl1).
          2:{ rewrite key_set_pull_add_eq. unfold NatSet.remove. rewrite nm_find_none_rm_add_eq.
              unfold key_set, nm_proj_v2. rewrite nm_map_unit1_map_eq. ss.
              unfold key_set, nm_proj_v2. rewrite nm_map_map_eq.
              rewrite NatMapP.F.map_o. eapply find_none_aux in KSIM0. rewrite KSIM0; eauto.
          }
          auto.
      }
      des.
      + subst.
        gfold. eapply sim_progress; auto. right; eapply CIH.
        eapply find_none_aux; eauto. eapply find_none_aux; eauto.
        { apply nm_pop_res_is_rm_eq in KSIM0, KSIM1. rewrite <- KSIM0, <- KSIM1. eapply nm_wf_pair_rm. eapply nm_wf_pair_add. auto. }
        replace (NatSet.add tid0 (key_set thsl1)) with (NatSet.add tid (key_set ths_src)).
        2:{ unfold NatSet.add. apply nm_pop_res_is_add_eq in KSIM0. erewrite <- !key_set_pull_add_eq. erewrite KSIM0. eauto. }
        replace (NatSet.add tid0 (key_set thsr1)) with (NatSet.add tid (key_set ths_tgt)).
        2:{ unfold NatSet.add. apply nm_pop_res_is_add_eq in KSIM1. erewrite <- !key_set_pull_add_eq. erewrite KSIM1. eauto. }
        eapply ksim_set_prog; eauto.
      + eapply IHo; eauto.
        eapply find_none_aux; eauto. eapply find_none_aux; eauto.
        { apply nm_pop_res_is_rm_eq in KSIM0, KSIM1. rewrite <- KSIM0, <- KSIM1. eapply nm_wf_pair_rm. eapply nm_wf_pair_add. auto. }
  Qed.

  Lemma kgsim_true
        R0 R1 (RR : R0 -> R1 -> Prop)
        (r : forall x x0 : Type,
            (x -> x0 -> Prop) -> bool -> @imap ident_src wf_src -> bool -> @imap ident_tgt wf_tgt -> _ -> _ -> Prop)
        (CIH : forall (ths_src : threads_src2 R0) (ths_tgt : threads_tgt R1) (tid : Th.key),
            Th.find (elt:=bool * thread _ident_src (sE state_src) R0) tid ths_src = None ->
            Th.find (elt:=thread _ident_tgt (sE state_tgt) R1) tid ths_tgt = None ->
            th_wf_pair ths_src ths_tgt ->
            forall (sf : bool) (src : thread _ident_src (sE state_src) R0)
              (tgt : thread _ident_tgt (sE state_tgt) R1) (st_src : state_src)
              (st_tgt : state_tgt) (ps pt : bool) (o : T (wf_stt R0 R1)) rs_ctx
              (mt : imap ident_tgt wf_tgt) (ms : imap ident_src wf_src),
              sim_knot (M:=M) (wf_stt) RR ths_src ths_tgt tid rs_ctx ps pt (sf, src) tgt
                       (ms, mt, st_src, st_tgt) o ->
              r R0 R1 RR ps ms pt mt (interp_all st_src (Th.add tid src (nm_proj_v2 ths_src)) tid)
                (interp_all st_tgt (Th.add tid tgt ths_tgt) tid))
        (ths_src : threads_src2 R0) (ths_tgt : threads_tgt R1) tid pt
        (tgt : thread _ident_tgt (sE state_tgt) R1)
        (THSRC : Th.find (elt:=bool * thread _ident_src (sE state_src) R0) tid ths_src = None)
        (THTGT : Th.find (elt:=thread _ident_tgt (sE state_tgt) R1) tid ths_tgt = None)
        (WF : th_wf_pair ths_src ths_tgt)
        (st_src : state_src) (st_tgt : state_tgt) rs_local mt ms (o : T (wf_stt R0 R1))
        (src : thread _ident_src (sE state_src) R0)
        sf
        (KSIM : sim_knot (M:=M) (wf_stt) RR ths_src ths_tgt tid rs_local true pt (sf, src) tgt
                         (ms, mt, st_src, st_tgt) o)
    :
    gpaco9 (_sim (wft:=wf_tgt)) (cpn9 (_sim (wft:=wf_tgt))) bot9 r R0 R1 RR true ms pt mt
           (interp_all st_src (Th.add tid src (nm_proj_v2 ths_src)) tid)
           (interp_all st_tgt (Th.add tid tgt ths_tgt) tid).
  Proof.
    match goal with
    | KSIM: sim_knot _ _ _ _ _ _ _ _ ?_src _ ?_shr _ |- _ => remember _src as ssrc; remember _shr as shr
    end.
    remember true as ps in KSIM.
    punfold KSIM.
    move KSIM before CIH. revert_until KSIM.
    pattern ths_src, ths_tgt, tid, rs_local, ps, pt, ssrc, tgt, shr, o.
    revert ths_src ths_tgt tid rs_local ps pt ssrc tgt shr o KSIM.
    eapply pind10_acc.
    intros rr DEC IH ths_src ths_tgt tid rs_local ps pt ssrc tgt shr o KSIM. clear DEC.
    intros THSRC THTGT WF st_src st_tgt mt ms src sf Essrc Eshr Eps.
    clarify.
    eapply pind10_unfold in KSIM.
    2:{ eapply _ksim_mon. }
    inv KSIM.

    { clear rr IH. eapply gsim_ret_emp; eauto. }

    { clear rr IH. eapply kgsim_ret_cont; eauto. }

    { clarify. clear rr IH. eapply kgsim_sync; eauto. }

    { des. destruct KSIM1 as [KSIM1 IND].
      unfold interp_all at 1. erewrite unfold_interp_sched_nondet_Some; eauto using nm_find_add_eq.
      rewrite interp_thread_vis_yield. ired. rewrite interp_state_tau. guclo sim_indC_spec; eapply sim_indC_tauL.
      rewrite bind_trigger. rewrite interp_sched_vis. rewrite interp_state_vis. rewrite <- bind_trigger.
      guclo sim_indC_spec. eapply sim_indC_chooseL. exists tid.
      replace (nm_pop tid (NatSet.add tid (NatSet.remove tid (key_set (Th.add tid (Vis (((|Yield)|)|)%sum ktr_src) (nm_proj_v2 ths_src)))))) with (Some (tt, NatSet.remove tid (key_set ths_src))).
      2:{ rewrite key_set_pull_add_eq. unfold NatSet.add, NatSet.remove. rewrite nm_add_rm_eq. rewrite nm_add_add_eq.
          rewrite nm_pop_add_eq. unfold key_set, nm_proj_v2. rewrite nm_map_unit1_map_eq. auto. }
      rewrite interp_state_tau. do 2 (guclo sim_indC_spec; eapply sim_indC_tauL).
      rewrite bind_trigger. rewrite interp_sched_vis. rewrite interp_state_vis. rewrite <- bind_trigger.
      guclo sim_indC_spec. eapply sim_indC_fairL.
      replace (tids_fmap tid (NatSet.remove tid (key_set ths_src))) with (tids_fmap tid (key_set ths_src)).
      2:{ rewrite <- tids_fmap_rm_same_eq. auto. }
      esplits; eauto. rewrite interp_sched_tau. do 2 rewrite interp_state_tau.
      do 3 (guclo sim_indC_spec; eapply sim_indC_tauL).
      match goal with
      | |- gpaco9 _ _ _ _ _ _ _ _ _ _ _ ?_src _ => replace _src with (interp_all st_src (Th.add tid (ktr_src ()) (nm_proj_v2 ths_src)) tid)
      end.
      2:{ unfold interp_all.
          replace (Th.add tid (ktr_src ()) (Th.add tid (Vis (((|Yield)|)|)%sum ktr_src) (nm_proj_v2 ths_src))) with (Th.add tid (ktr_src ()) (nm_proj_v2 ths_src)).
          2:{ rewrite nm_add_add_eq. auto. }
          replace (NatSet.remove tid (key_set (Th.add tid (ktr_src ()) (nm_proj_v2 ths_src)))) with (NatSet.remove tid (key_set ths_src)).
          2:{ rewrite key_set_pull_add_eq. unfold NatSet.remove. rewrite nm_rm_add_rm_eq.
              unfold key_set, nm_proj_v2. rewrite nm_map_unit1_map_eq. auto. }
          auto.
      }
      eapply IH. eauto. all: auto.
    }

    { destruct KSIM0 as [KSIM0 IND]. rewrite interp_all_tau.
      guclo sim_indC_spec. eapply sim_indC_tauL.
      eapply IH; eauto.
    }

    { des. destruct KSIM0 as [KSIM0 IND]. rewrite interp_all_vis. rewrite <- bind_trigger.
      guclo sim_indC_spec. eapply sim_indC_chooseL. eexists.
      do 2 (guclo sim_indC_spec; eapply sim_indC_tauL).
      eapply IH; eauto.
    }

    { destruct KSIM0 as [KSIM0 IND]. rewrite interp_all_state.
      do 2 (guclo sim_indC_spec; eapply sim_indC_tauL).
      eapply IH; eauto.
    }

    { destruct KSIM0 as [KSIM0 IND]. rewrite interp_all_tid.
      do 1 (guclo sim_indC_spec; eapply sim_indC_tauL).
      eapply IH; eauto.
    }

    { rewrite interp_all_vis.
      rewrite <- bind_trigger. guclo sim_indC_spec. eapply sim_indC_ub.
    }

    { des. destruct KSIM1 as [KSIM1 IND]. rewrite interp_all_vis. rewrite <- bind_trigger.
      guclo sim_indC_spec. eapply sim_indC_fairL. esplits; eauto.
      do 2 (guclo sim_indC_spec; eapply sim_indC_tauL).
      eapply IH; eauto.
    }

    { destruct KSIM0 as [KSIM0 IND]. rewrite interp_all_tau.
      guclo sim_indC_spec. eapply sim_indC_tauR.
      eapply IH; eauto.
    }

    { rewrite interp_all_vis. rewrite <- bind_trigger.
      guclo sim_indC_spec. eapply sim_indC_chooseR. i.
      do 2 (guclo sim_indC_spec; eapply sim_indC_tauR).
      specialize (KSIM0 x). destruct KSIM0 as [KSIM0 IND].
      eapply IH; eauto.
    }

    { destruct KSIM0 as [KSIM0 IND]. rewrite interp_all_state.
      do 2 (guclo sim_indC_spec; eapply sim_indC_tauR).
      eapply IH; eauto.
    }

    { destruct KSIM0 as [KSIM0 IND]. rewrite interp_all_tid.
      do 1 (guclo sim_indC_spec; eapply sim_indC_tauR).
      eapply IH; eauto.
    }

    { rewrite interp_all_vis. rewrite <- bind_trigger.
      guclo sim_indC_spec. eapply sim_indC_fairR. i.
      do 2 (guclo sim_indC_spec; eapply sim_indC_tauR).
      specialize (KSIM0 _ FAIR). destruct KSIM0 as [KSIM0 IND].
      eapply IH; eauto.
    }

    { rewrite ! interp_all_vis. ss. gfold. econs. i. subst. rename r_tgt into ret. specialize (KSIM0 ret).
      rewrite <- !interp_all_tau. right. eapply CIH; eauto.
      pfold.
      eapply pind10_fold. econs. split; ss.
      eapply pind10_fold. econs. split; ss.
      eapply pind10_fold. econs. split; ss.
      eapply pind10_fold. econs. split; ss.
      destruct KSIM0; ss. punfold p.
      Unshelve. all: exact o1.
    }

    { rewrite interp_all_call. gfold. eapply sim_ub. }

    { clear rr IH. gfold. eapply sim_progress. right; eapply CIH; eauto. pclearbot. eapply KSIM0. all: auto. }

  Qed.

  Lemma ksim_implies_gsim
        R0 R1 (RR: R0 -> R1 -> Prop)
        (ths_src: threads_src2 R0)
        (ths_tgt: threads_tgt R1)
        tid
        (THSRC: Th.find tid ths_src = None)
        (THTGT: Th.find tid ths_tgt = None)
        (WF: th_wf_pair ths_src ths_tgt)
        sf src tgt
        (st_src: state_src) (st_tgt: state_tgt)
        ps pt
        (KSIM: forall im_tgt, exists im_src (o: T (wf_stt R0 R1)) rs_ctx,
            sim_knot (M:=M) (wf_src:=wf_src) (wf_tgt:=wf_tgt) (wf_stt)
                     RR ths_src ths_tgt tid rs_ctx ps pt (sf, src) tgt
                     (im_src, im_tgt, st_src, st_tgt) o)
    :
    gsim wf_src wf_tgt RR
         (interp_all st_src (Th.add tid src (nm_proj_v2 ths_src)) tid)
         (interp_all st_tgt (Th.add tid tgt ths_tgt) tid).
  Proof.
    ii. specialize (KSIM mt). des. rename im_src into ms. exists ms, ps, pt.
    revert_until RR. ginit. gcofix CIH. i.
    move o before CIH. revert_until o. induction ((wf_stt R0 R1).(wf) o).
    clear H; rename x into o, H0 into IHo. i.
    match goal with
    | KSIM: sim_knot _ _ _ _ _ _ _ _ ?_src _ ?_shr ?_ox |- _ => remember _src as ssrc; remember _shr as shr; remember _ox as ox in KSIM
    end.
    punfold KSIM.
    move KSIM before IHo. revert_until KSIM.
    pattern ths_src, ths_tgt, tid, rs_ctx, ps, pt, ssrc, tgt, shr, ox.
    revert ths_src ths_tgt tid rs_ctx ps pt ssrc tgt shr ox KSIM.
    apply pind10_acc.
    intros rr DEC IH ths_src ths_tgt tid rs_ctx ps pt ssrc tgt shr ox KSIM. clear DEC.
    intros THSRC THTGT WF sf src st_src st_tgt mt ms Essrc Eshr Eox.
    clarify.
    eapply pind10_unfold in KSIM.
    2:{ eapply _ksim_mon. }
    inv KSIM.

    { clear rr IH IHo. eapply gsim_ret_emp; eauto. }

    { clear rr IH. eapply kgsim_ret_cont; eauto. }

    { clear rr IH. eapply kgsim_sync; eauto. }

    { des; clarify. destruct KSIM1 as [KSIM1 IND].
      assert (KSIM: sim_knot (wf_stt) RR ths_src ths_tgt tid rs_ctx true pt
                             (false, ktr_src ()) tgt
                             (im_src0, mt, st_src, st_tgt) o0).
      { pfold. eapply pind10_mon_top; eauto. }
      unfold interp_all. erewrite unfold_interp_sched_nondet_Some; auto using nm_find_add_eq.
      rewrite interp_thread_vis_yield. ired. rewrite interp_state_tau. guclo sim_indC_spec; eapply sim_indC_tauL.
      rewrite bind_trigger. rewrite interp_sched_vis. rewrite interp_state_vis. rewrite <- bind_trigger.
      guclo sim_indC_spec. eapply sim_indC_chooseL. exists tid.
      replace (nm_pop tid (NatSet.add tid (NatSet.remove tid (key_set (Th.add tid (Vis (((|Yield)|)|)%sum ktr_src) (nm_proj_v2 ths_src)))))) with (Some (tt, key_set ths_src)).
      2:{ rewrite key_set_pull_add_eq. unfold NatSet.add, NatSet.remove. rewrite nm_add_rm_eq. rewrite nm_add_add_eq.
          rewrite nm_pop_add_eq. unfold key_set, nm_proj_v2. rewrite nm_map_unit1_map_eq.
          rewrite nm_map_rm_comm_eq. rewrite nm_find_none_rm_eq; auto. }
      rewrite interp_state_tau. do 2 (guclo sim_indC_spec; eapply sim_indC_tauL).
      rewrite bind_trigger. rewrite interp_sched_vis. rewrite interp_state_vis. rewrite <- bind_trigger.
      guclo sim_indC_spec. eapply sim_indC_fairL.
      esplits; eauto.
      rewrite interp_sched_tau. do 2 rewrite interp_state_tau. do 3 (guclo sim_indC_spec; eapply sim_indC_tauL).

      clear - ident_src ident_tgt M CIH THSRC THTGT WF KSIM.
      rename o0 into o.
      remember (ktr_src ()) as src. rename im_src0 into ms.
      match goal with
      | |- gpaco9 _ _ _ _ _ _ _ _ _ _ _ _ ?_tgt => replace _tgt with (interp_all st_tgt (Th.add tid tgt ths_tgt) tid)
      end.
      2:{ ss. }
      match goal with
      | |- gpaco9 _ _ _ _ _ _ _ _ _ _ _ ?_src _ => replace _src with (interp_all st_src (Th.add tid src (nm_proj_v2 ths_src)) tid)
      end.
      2:{ unfold interp_all.
          replace (Th.add tid src (Th.add tid (Vis (((|Yield)|)|)%sum ktr_src) (nm_proj_v2 ths_src))) with (Th.add tid src (nm_proj_v2 ths_src)).
          2:{ rewrite nm_add_add_eq. auto. }
          replace (NatSet.remove tid (key_set (Th.add tid src (nm_proj_v2 ths_src)))) with (key_set ths_src).
          2:{ rewrite key_set_pull_add_eq. unfold NatSet.remove. rewrite nm_rm_add_rm_eq.
              unfold key_set, nm_proj_v2. rewrite nm_map_unit1_map_eq.
              rewrite nm_map_rm_comm_eq. rewrite nm_find_none_rm_eq; auto. }
          auto.
      }
      clear Heqsrc ktr_src.
      eapply kgsim_true; eauto.
    }

    { destruct KSIM0 as [KSIM0 IND]. rewrite interp_all_tau.
      guclo sim_indC_spec. eapply sim_indC_tauL.
      eapply IH; eauto.
    }

    { des. destruct KSIM0 as [KSIM0 IND]. rewrite interp_all_vis. rewrite <- bind_trigger.
      guclo sim_indC_spec. eapply sim_indC_chooseL. eexists.
      do 2 (guclo sim_indC_spec; eapply sim_indC_tauL).
      eapply IH; eauto.
    }

    { destruct KSIM0 as [KSIM0 IND]. rewrite interp_all_state.
      do 2 (guclo sim_indC_spec; eapply sim_indC_tauL).
      eapply IH; eauto.
    }

    { destruct KSIM0 as [KSIM0 IND]. rewrite interp_all_tid.
      do 1 (guclo sim_indC_spec; eapply sim_indC_tauL).
      eapply IH; eauto.
    }

    { rewrite interp_all_vis.
      rewrite <- bind_trigger. guclo sim_indC_spec. eapply sim_indC_ub.
    }

    { des. destruct KSIM1 as [KSIM1 IND]. rewrite interp_all_vis. rewrite <- bind_trigger.
      guclo sim_indC_spec. eapply sim_indC_fairL. esplits; eauto.
      do 2 (guclo sim_indC_spec; eapply sim_indC_tauL).
      eapply IH; eauto.
    }

    { destruct KSIM0 as [KSIM0 IND]. rewrite interp_all_tau.
      guclo sim_indC_spec. eapply sim_indC_tauR.
      eapply IH; eauto.
    }

    { rewrite interp_all_vis. rewrite <- bind_trigger.
      guclo sim_indC_spec. eapply sim_indC_chooseR. i.
      do 2 (guclo sim_indC_spec; eapply sim_indC_tauR).
      specialize (KSIM0 x). destruct KSIM0 as [KSIM0 IND].
      eapply IH; eauto.
    }

    { destruct KSIM0 as [KSIM0 IND]. rewrite interp_all_state.
      do 2 (guclo sim_indC_spec; eapply sim_indC_tauR).
      eapply IH; eauto.
    }

    { destruct KSIM0 as [KSIM0 IND]. rewrite interp_all_tid.
      do 1 (guclo sim_indC_spec; eapply sim_indC_tauR).
      eapply IH; eauto.
    }

    { rewrite interp_all_vis. rewrite <- bind_trigger.
      guclo sim_indC_spec. eapply sim_indC_fairR. i.
      do 2 (guclo sim_indC_spec; eapply sim_indC_tauR).
      specialize (KSIM0 _ FAIR). destruct KSIM0 as [KSIM0 IND].
      eapply IH; eauto.
    }

    { rewrite ! interp_all_vis. ss. gfold. econs. i. subst. rename r_tgt into ret. specialize (KSIM0 ret).
      rewrite <- !interp_all_tau. right. eapply CIH; eauto.
      pfold.
      eapply pind10_fold. econs. split; ss.
      eapply pind10_fold. econs. split; ss.
      eapply pind10_fold. econs. split; ss.
      eapply pind10_fold. econs. split; ss.
      destruct KSIM0; ss. punfold p.
      Unshelve. all: exact o1.
    }

    { rewrite interp_all_call. gfold. eapply sim_ub. }

    { clear rr IH. gfold. eapply sim_progress. right; eapply CIH; eauto. destruct KSIM0; ss. eapply p. all: auto. }

  Qed.

End PROOF.
