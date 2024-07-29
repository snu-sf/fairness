From sflib Require Import sflib.
From Paco Require Import paco.

Require Export Coq.Strings.String.
Require Import Coq.Classes.RelationClasses.
Require Import Program.
Require Import Permutation.
From iris.algebra Require Import cmra updates.

From Fairness Require Import Axioms.
From Fairness Require Export ITreeLib FairBeh FairSim WFLibLarge NatStructsLarge.
From Fairness Require Import pind PCM World.
From Fairness Require Export Mod Concurrency.
From Fairness Require Import ModSimStutter KnotSim LocalAdequacyAux.

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

  Definition nm_wf_stt: Type -> Type -> WF := fun R0 R1 => nm_wf (wf_stt R0 R1).

  Let shared := shared state_src state_tgt _ident_src _ident_tgt wf_src wf_tgt.
  Let kshared := kshared state_src state_tgt _ident_src _ident_tgt wf_src wf_tgt.

  Notation threads_src1 R0 := (threads _ident_src (sE state_src) R0).
  Notation threads_src2 R0 := (threads2 _ident_src (sE state_src) R0).
  Notation threads_tgt R1 := (threads _ident_tgt (sE state_tgt) R1).

  (* Variable I: shared -> (cmra_car M) -> Prop. *)

  Variable St: wf_tgt.(T) -> wf_tgt.(T).
  Hypothesis lt_succ_diag_r_t: forall (t: wf_tgt.(T)), wf_tgt.(lt) t (St t).

  Lemma lsim_implies_ksim
        R0 R1 (RR: R0 -> R1 -> Prop)
        (ths_src: threads_src2 R0)
        (ths_tgt: threads_tgt R1)
        tid
        (THSRC: Th.find tid ths_src = None)
        (THTGT: Th.find tid ths_tgt = None)
        (WF: th_wf_pair ths_src ths_tgt)
        sf src tgt
        (st_src: state_src) (st_tgt: state_tgt)
        gps gpt
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
                    (lsim (wf_stt) I tid (local_RR I RR tid)
                          gps gpt (sum_of_resources rs_ctx) (o, src) tgt
                          (NatSet.add tid (key_set ths_src),
                            im_src0, im_tgt0, st_src, st_tgt))>>) /\
              (<<LOCAL: forall tid sf (src: itree srcE R0) (tgt: itree tgtE R1) o r_own
                          (OWN: r_own = fst (get_resource tid rs_ctx))
                          (LSRC: Th.find tid ths_src = Some (sf, src))
                          (LTGT: Th.find tid ths_tgt = Some tgt)
                          (ORD: Th.find tid os = Some o),
                  ((sf = true) -> (local_sim_sync wf_stt I RR src tgt tid o r_own)) /\
                    ((sf = false) -> (local_sim_pick wf_stt I RR src tgt tid o r_own))>>))
    :
    forall im_tgt, exists im_src os rs_ctx,
      (sim_knot (M:=M) (wf_src:=wf_src) (wf_tgt:=wf_tgt) (nm_wf_stt)
                RR ths_src ths_tgt tid rs_ctx gps gpt (sf, src) tgt
                (im_src, im_tgt, st_src, st_tgt) os).
  Proof.
    ii. remember (fun i => match prism_fmap inlp (tids_fmap tid (NatSet.add tid (key_set ths_tgt))) i with
                        | Flag.fail => St (im_tgt i)
                        | Flag.emp => im_tgt i
                        | Flag.success => im_tgt i
                        end) as im_tgt1.
    specialize (LSIM im_tgt1). des. move I after St.
    assert (FAIR: fair_update im_tgt1 im_tgt (prism_fmap inlp (tids_fmap tid (NatSet.add tid (key_set ths_tgt))))).
    { rewrite Heqim_tgt1. unfold fair_update. i. des_ifs. }
    specialize (LSIM im_tgt FAIR). des. clear LSIM Heqim_tgt1 FAIR im_tgt1.
    clear im_src; rename im_src0 into im_src.
    move LOCAL before RR. rename LSIM0 into LSIM.
    exists im_src, (Th.add tid o os), rs_ctx.

    revert_until RR. pcofix CIH. i.
    match goal with
    | LSIM: lsim _ _ _ ?_LRR _ _ ?_rs ?_osrc _ ?_shr |- _ => remember _LRR as LRR; remember _shr as shr; remember _rs as rs; remember _osrc as osrc
    end.
    match goal with
    | |- paco10 _ _ _ _ tid _ _ _ _ _ ?_kshr _ => replace _kshr with (to_kshared shr); [|unfold to_kshared; des_ifs]
    end.
    move LSIM before LOCAL. revert_until LSIM. punfold LSIM.
    pattern gps, gpt, rs, osrc, tgt, shr.
    revert gps gpt rs osrc tgt shr LSIM.
    apply pind6_acc.
    intros rr DEC IH gps gpt rs src tgt shr LSIM. clear DEC.
    intros THSRC THTGT WF sf src0 st_src st_tgt o RSWF OSWF0 OSWF1 im_tgt im_src ELRR Eshr Ers Esrc.
    assert (LBASE: lsim _ I tid LRR gps gpt rs src tgt shr).
    { clarify. pfold. eapply pind6_mon_top; eauto. }
    eapply pind6_unfold in LSIM.
    2:{ eapply _lsim_mon. }
    inv LSIM.

    { clear IH rr. unfold local_RR in LSIM0. des. clarify.
      destruct (Th.is_empty ths_src) eqn:EMPS.
      { destruct (Th.is_empty ths_tgt) eqn:EMPT.
        { pfold. eapply pind10_fold. econs 1; eauto. }
        { exfalso. erewrite nm_wf_pair_is_empty in EMPS. 2:eapply WF. rewrite EMPT in EMPS. ss. }
      }
      { destruct (Th.is_empty ths_tgt) eqn:EMPT.
        { exfalso. erewrite nm_wf_pair_is_empty in EMPS. 2:eapply WF. rewrite EMPT in EMPS. ss. }
        { pfold. eapply pind10_fold. econs 2; eauto.
          { instantiate (1:=r_own). instantiate (1:=r_shared). unfold resources_wf.
            rewrite sum_of_resources_add; auto. r_wf VALID.
          }
          { instantiate (1:=Th.add tid o1 os). ss. econs. all: eauto.
            - apply nm_find_add_eq.
            - apply nm_find_add_eq.
            - i. rewrite !nm_find_add_neq; auto.
          }
          i. hexploit th_wf_pair_pop_cases.
          { eapply WF. }
          intros H. instantiate (1:=tid0) in H. des; auto.
          right. destruct th_src as [sf0 th_src].
          assert (FINDS: Th.find tid0 ths_src = Some (sf0, th_src)).
          { eapply nm_pop_find_some; eauto. }
          assert (FINDT: Th.find tid0 ths_tgt = Some (th_tgt)).
          { eapply nm_pop_find_some; eauto. }
          assert (FINDO: exists o', Th.find tid0 os = Some o').
          { destruct (Th.find tid0 os) eqn:FINDOS. eauto. exfalso.
            apply NatMapP.F.not_find_in_iff in FINDOS. apply FINDOS.
            apply OSWF0. apply NatMapP.F.in_find_iff. ii. rewrite FINDS in H2. ss.
          }
          des.
          exists sf0, th_src, ths_src0, th_tgt, ths_tgt0.
          splits; auto.

          - i; clarify. hexploit LOCAL. eauto. eapply FINDS. eapply FINDT. eapply FINDO.
            i; des.
            hexploit H2; clear H2 H3; ss. i. unfold local_sim_sync in H2.
            assert (NEQ: tid <> tid0).
            { destruct (tid_dec tid tid0); auto. clarify. }
            replace (Th.add tid o1 os) with (Th.add tid0 o' (Th.remove tid0 (Th.add tid o1 os))).
            2:{ rewrite <- nm_find_some_rm_add_eq; auto. rewrite nm_find_add_neq; auto. }

            right. eapply CIH.
            { i. destruct (tid_dec tid tid1).
              { exfalso. revert THTGT H0 LTGT e. clear; i. clarify.
                hexploit nm_pop_res_is_rm_eq. eapply H0. i. clarify.
                destruct (tid_dec tid0 tid1); clarify.
                + rewrite nm_find_rm_eq in LTGT. ss.
                + rewrite nm_find_rm_neq in LTGT; clarify.
              }
              hexploit LOCAL. eauto.
              eapply find_some_aux; eauto. eapply find_some_aux; eauto.
              { rewrite NatMapP.F.remove_o in ORD. des_ifs.
                rewrite nm_find_add_neq in ORD; auto. rewrite ORD. eauto.
              }
              i; des. split.
              - intro SYNC. eapply H3 in SYNC. ii. unfold local_sim_sync in SYNC.
                assert (URAWF: ✓ (r_shared0 ⋅ fst (get_resource tid1 rs_ctx) ⋅ r_ctx0)).
                { assert ((fst (get_resource tid1 rs_ctx)) ≡ r_own0) as ->; auto. rewrite OWN.
                  rewrite get_resource_rs_neq. rewrite get_resource_add_neq_fst. all: auto.
                  destruct (tid_dec tid0 tid1); auto. clarify.
                  exfalso. revert H0 FINDT LTGT. clear; i.
                  hexploit nm_pop_res_is_rm_eq. eapply H0. i. clarify.
                  rewrite nm_find_rm_eq in LTGT. ss.
                }
                specialize (SYNC _ _ _ _ _ _ _ INV0 URAWF fs ft _ FAIR0). auto.
              - intro PICK. eapply H4 in PICK. ii. unfold local_sim_pick in PICK.
                assert (URAWF: ✓ (r_shared0 ⋅ fst (get_resource tid1 rs_ctx) ⋅ r_ctx0)).
                { assert ((fst (get_resource tid1 rs_ctx)) ≡ r_own0) as ->; auto. rewrite OWN.
                  rewrite get_resource_rs_neq. rewrite get_resource_add_neq_fst. all: auto.
                  destruct (tid_dec tid0 tid1); auto. clarify.
                  exfalso. revert H0 FINDT LTGT. clear; i.
                  hexploit nm_pop_res_is_rm_eq. eapply H0. i. clarify.
                  rewrite nm_find_rm_eq in LTGT. ss.
                }
                specialize (PICK _ _ _ _ _ _ _ INV0 URAWF _ FAIR0). auto.
            }

            eapply find_none_aux; eauto. eapply find_none_aux; eauto. auto.
            { destruct (NatMap.find tid0 (NatMap.add tid r_own rs_ctx)) eqn:FIND0.
              { erewrite get_resource_find_some_snd; eauto. apply nm_find_rm_eq. }
              { rewrite get_resource_find_none_snd; auto. }
            }
            { move OSWF0 after NEQ. i. eapply NatMapP.F.remove_in_iff. split.
              { eapply nm_pop_res_find_none in H. eapply NatMapP.F.not_find_in_iff in H.
                destruct (tid_dec tid0 tid'); clarify; ss.
              }
              eapply NatMapP.F.add_in_iff. destruct (tid_dec tid' tid).
              { left; auto. }
              right. apply OSWF0. eapply nm_pop_res_is_add_eq in H. rewrite H.
              eapply NatMapP.F.add_in_iff. right; auto.
            }
            { apply nm_find_rm_eq. }
            assert (PROJS: NatSet.remove tid (NatSet.add tid (key_set ths_src)) = NatSet.add tid0 (key_set ths_src0)).
            { eapply proj_aux; eauto. }
            rewrite <- PROJS.
            eapply H2; eauto.
            { revert VALID. eapply ura_wf_get_resource_neq; auto. }
            { rewrite PROJS. unfold NatSet.add. rewrite <- tids_fmap_add_same_eq. rewrite H1; auto. }

          - i. clarify.
            hexploit LOCAL. eauto. eapply FINDS. eapply FINDT. eapply FINDO.
            i; des. hexploit H3; clear H2 H3; ss. i. unfold local_sim_pick in H2.
            assert (PROJS: NatSet.remove tid (NatSet.add tid (key_set ths_src)) = NatSet.add tid0 (key_set ths_src0)).
            { eapply proj_aux; eauto. }
            hexploit H2; clear H2; eauto.
            { instantiate (1:= sum_of_resources (snd (get_resource tid0 (NatMap.add tid r_own rs_ctx)))).
              revert VALID. eapply ura_wf_get_resource_neq; auto.
              destruct (tid_dec tid tid0); auto. clarify.
            }
            { unfold NatSet.remove, NatSet.add in *. rewrite PROJS. rewrite <- tids_fmap_add_same_eq. rewrite H1; eauto. }
            i; des. esplits; eauto.
            { unfold NatSet.remove, NatSet.add in *. rewrite PROJS in H2. rewrite <- tids_fmap_add_same_eq in H2. eauto. }

            assert (NEQ: tid <> tid0).
            { destruct (tid_dec tid tid0); auto. clarify. }
            replace (Th.add tid o1 os) with (Th.add tid0 o' (Th.remove tid0 (Th.add tid o1 os))).
            2:{ rewrite <- nm_find_some_rm_add_eq; auto. rewrite nm_find_add_neq; auto. }

            right. eapply CIH.
            { i. destruct (tid_dec tid tid1); auto.
              { clarify. exfalso. revert THTGT H0 LTGT. clear; i.
                hexploit nm_pop_res_is_rm_eq. eapply H0. i. clarify.
                destruct (tid_dec tid0 tid1); clarify.
                - rewrite nm_find_rm_eq in LTGT. ss.
                - rewrite nm_find_rm_neq in LTGT; clarify.
              }
              hexploit LOCAL. eauto.
              eapply find_some_aux; eauto. eapply find_some_aux; eauto.
              { rewrite NatMapP.F.remove_o in ORD. des_ifs.
                rewrite nm_find_add_neq in ORD; auto. rewrite ORD. eauto.
              }
              i; des. split.
              - intro SYNC. eapply H4 in SYNC. clear H4 H5. ii. unfold local_sim_sync in SYNC.
                eapply SYNC; eauto. rewrite OWN in VALID0.
                assert ((fst (get_resource tid1 rs_ctx)) ≡ (fst (get_resource tid1 (snd (get_resource tid0 (NatMap.add tid r_own rs_ctx)))))) as ->. auto.
                rewrite get_resource_rs_neq. rewrite get_resource_add_neq_fst. all: auto.
                destruct (tid_dec tid0 tid1); auto. clarify.
                exfalso. revert H0 FINDT LTGT. clear; i.
                hexploit nm_pop_res_is_rm_eq. eapply H0. i. clarify.
                rewrite nm_find_rm_eq in LTGT. ss.

              - intro PICK. eapply H5 in PICK. clear H4 H5. ii. unfold local_sim_pick in PICK.
                eapply PICK; eauto. rewrite OWN in VALID0.
                assert ((fst (get_resource tid1 rs_ctx)) ≡ (fst (get_resource tid1 (snd (get_resource tid0 (NatMap.add tid r_own rs_ctx)))))) as ->. auto.
                rewrite get_resource_rs_neq. rewrite get_resource_add_neq_fst. all: auto.
                destruct (tid_dec tid0 tid1); auto. clarify.
                exfalso. revert H0 FINDT LTGT. clear; i.
                hexploit nm_pop_res_is_rm_eq. eapply H0. i. clarify.
                rewrite nm_find_rm_eq in LTGT. ss.
            }
            eapply find_none_aux; eauto. eapply find_none_aux; eauto. auto.
            { destruct (NatMap.find tid0 (NatMap.add tid r_own rs_ctx)) eqn:FIND0.
              { erewrite get_resource_find_some_snd; eauto. apply nm_find_rm_eq. }
              { rewrite get_resource_find_none_snd; auto. }
            }
            { move OSWF0 after NEQ. i. eapply NatMapP.F.remove_in_iff. split.
              { eapply nm_pop_res_find_none in H. eapply NatMapP.F.not_find_in_iff in H.
                destruct (tid_dec tid0 tid'); clarify; ss.
              }
              eapply NatMapP.F.add_in_iff. destruct (tid_dec tid' tid).
              { left; auto. }
              right. apply OSWF0. eapply nm_pop_res_is_add_eq in H. rewrite H.
              eapply NatMapP.F.add_in_iff. right; auto.
            }
            { apply nm_find_rm_eq. }
            rewrite <- PROJS. auto.
        }
      }
    }

    { clarify. destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      pfold. eapply pind10_fold. eapply ksim_tauL. split; [|ss].
      hexploit IH; eauto. i. punfold H.
    }

    { des. clarify. destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      pfold. eapply pind10_fold. rewrite bind_trigger. eapply ksim_chooseL. exists x. split; [|ss].
      hexploit IH; eauto. i. punfold H.
    }

    { clarify. destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      pfold. eapply pind10_fold. rewrite bind_trigger. eapply ksim_stateL. split; [|ss].
      hexploit IH; eauto. i. punfold H.
    }

    { clarify. destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      pfold. eapply pind10_fold. rewrite bind_trigger. eapply ksim_tidL. split; [|ss].
      hexploit IH; eauto. i. punfold H.
    }

    { clarify. pfold. eapply pind10_fold. rewrite bind_trigger. eapply ksim_UB. }

    { des. clarify. destruct LSIM as [LSIM IND]. clear LSIM.
      pfold. eapply pind10_fold. rewrite bind_trigger. eapply ksim_fairL.
      exists im_src1. splits; eauto. split; [|ss].
      hexploit IH; eauto. i. punfold H.
    }

    { clarify. destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      pfold. eapply pind10_fold. eapply ksim_tauR. split; [|ss].
      hexploit IH; eauto. i. punfold H.
    }

    { clarify.
      pfold. eapply pind10_fold. rewrite bind_trigger. eapply ksim_chooseR. split; [|ss].
      specialize (LSIM0 x). destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      hexploit IH; eauto. i. punfold H.
    }

    { clarify. destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      pfold. eapply pind10_fold. rewrite bind_trigger. eapply ksim_stateR. split; [|ss].
      hexploit IH; eauto. i. punfold H.
    }

    { clarify. destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      pfold. eapply pind10_fold. rewrite bind_trigger. eapply ksim_tidR. split; [|ss].
      hexploit IH; eauto. i. punfold H.
    }

    { clarify.
      pfold. eapply pind10_fold. rewrite bind_trigger. eapply ksim_fairR. split; [|ss].
      specialize (LSIM0 im_tgt0 FAIR). des. destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      hexploit IH; eauto. i. punfold H.
    }

    { clear IH rr. clarify. rewrite ! bind_trigger.
      pfold. eapply pind10_fold. eapply ksim_observe. i.
      specialize (LSIM0 ret). pclearbot. right. eapply CIH; auto.
    }

    { clear IH rr. clarify.
      pfold. eapply pind10_fold. eapply ksim_call. }

    { clear IH rr. clarify. rewrite ! bind_trigger.
      pfold. eapply pind10_fold. eapply ksim_sync; eauto.
      { instantiate (1:=r_own). instantiate (1:=r_shared). unfold resources_wf.
        rewrite sum_of_resources_add; auto. r_wf VALID.
      }
      i.
      assert (WF0: th_wf_pair (Th.add tid (true, ktr_src ()) ths_src) (Th.add tid (ktr_tgt ()) ths_tgt)).
      { unfold th_wf_pair, nm_wf_pair in *. rewrite ! key_set_pull_add_eq. rewrite WF. reflexivity. }
      exploit th_wf_pair_pop_cases.
      { eapply WF0. }
      intros H. instantiate (1:=tid0) in H. des; auto.
      right. destruct th_src as [sf0 th_src].
      exists sf0, th_src, ths_src0, th_tgt, ths_tgt0.
      splits; auto.

      - i; clarify.
        destruct (tid_dec tid tid0) eqn:TID; subst.
        { rename tid0 into tid.
          assert (ths_tgt0 = ths_tgt /\ th_tgt = (ktr_tgt ())).
          { hexploit nm_pop_find_none_add_same_eq. eapply THTGT. eauto. i; des; clarify. }
          assert (ths_src0 = ths_src /\ th_src = (ktr_src ())).
          { hexploit nm_pop_find_none_add_same_eq. eapply THSRC. eauto. i; des; clarify. }
          des; clarify.
          hexploit LSIM0; clear LSIM0; eauto.
          { unfold NatSet.add. rewrite <- tids_fmap_add_same_eq. rewrite WF; eauto. }
          intro LSIM0. des; pclearbot.
          exists (Th.add tid o1 os). split.
          { ss. econs. all: eauto.
            - apply nm_find_add_eq.
            - apply nm_find_add_eq.
            - i. rewrite !nm_find_add_neq; auto.
          }

          right. eapply CIH; eauto.
          { i. hexploit LOCAL. eauto. 1,2: eauto. eauto. i; des. split.
            - intro SYNC. eapply H2 in SYNC. clear H2 H3. ii. unfold local_sim_sync in SYNC.
              eapply SYNC; eauto.
              rewrite OWN in VALID0.
              assert ((fst (get_resource tid0 rs_ctx)) ≡ (fst (get_resource tid0 (snd (get_resource tid (NatMap.add tid r_own rs_ctx)))))) as ->. auto.
              destruct (tid_dec tid tid0); clarify.
              rewrite get_resource_rs_neq; auto. rewrite get_resource_add_neq_fst; auto.
              done.
            - intro PICK. eapply H3 in PICK. clear H2 H3. ii. unfold local_sim_pick in PICK.
              eapply PICK; eauto.
              rewrite OWN in VALID0.
              assert ((fst (get_resource tid0 rs_ctx)) ≡ (fst (get_resource tid0 (snd (get_resource tid (NatMap.add tid r_own rs_ctx)))))) as ->. auto.
              destruct (tid_dec tid tid0); clarify.
              rewrite get_resource_rs_neq; auto. rewrite get_resource_add_neq_fst; auto. done.
          }
          { rewrite get_resource_add_eq nm_find_rm_eq. done. }

          match goal with
          | |- lsim _ _ tid _ _ _ _ (_, ?_itr) _ _ => assert (_itr = (x <- trigger Yield;; ktr_src x))
          end.
          { rewrite bind_trigger. f_equal. f_equal. extensionality x. destruct x. ss. }
          rewrite H2; clear H2.
          replace (sum_of_resources (snd (get_resource tid (NatMap.add tid r_own rs_ctx)))) with
            (sum_of_resources rs_ctx). auto.
          by rewrite get_resource_add_eq nm_find_none_rm_eq.
        }

        exists (Th.add tid o1 os). split.
        { ss. econs. all: eauto.
          - apply nm_find_add_eq.
          - apply nm_find_add_eq.
          - i. rewrite !nm_find_add_neq; auto.
        }
        assert (FINDO: exists o', Th.find tid0 os = Some o').
        { destruct (Th.find tid0 os) eqn:FINDOS. eauto. exfalso.
          apply NatMapP.F.not_find_in_iff in FINDOS. apply FINDOS.
          apply OSWF0. apply NatMapP.F.in_find_iff. ii.
          eapply nm_pop_find_some in H. rewrite nm_find_add_neq in H; auto.
          rewrite H in H2; ss.
        }
        des.
        replace (Th.add tid o1 os) with (Th.add tid0 o' (Th.remove tid0 (Th.add tid o1 os))).
        2:{ rewrite <- nm_find_some_rm_add_eq; auto. rewrite nm_find_add_neq; auto. }

        right. eapply CIH.
        { i. destruct (tid_dec tid tid1) eqn:TID2; subst.
          { rename tid1 into tid.
            pose nm_pop_neq_find_some_eq. dup H. eapply e in H2; eauto. dup H0. eapply e in H3; eauto.
            inv H2. split; i; ss. clear H2.
            ii. hexploit LSIM0. eapply INV0.
            { rewrite get_resource_rs_neq in VALID0; auto.
              rewrite get_resource_add_eq in VALID0. eauto.
            }
            eauto.
            i. pclearbot.
            match goal with
            | |- lsim _ _ tid _ _ _ _ (_, ?_itr) _ _ => assert (_itr = (x <- trigger Yield;; ktr_src x))
            end.
            { rewrite bind_trigger. f_equal. f_equal. extensionality x. destruct x. ss. }
            rewrite H3. eapply lsim_set_prog. replace o0 with o1; auto.
            { move ORD after H3. rewrite nm_find_rm_neq in ORD; auto.
              rewrite nm_find_add_eq in ORD. clarify.
            }
          }

          { hexploit LOCAL. eauto.
            eapply find_some_neq_aux; eauto. eapply find_some_neq_aux; eauto.
            { rewrite NatMapP.F.remove_o in ORD. des_ifs. rewrite nm_find_add_neq in ORD; eauto. }
            i; des. split.
            - intro SYNC. eapply H2 in SYNC. clear H2 H3. ii. unfold local_sim_sync in SYNC.
              eapply SYNC; eauto.
              rewrite get_resource_rs_neq in VALID0. rewrite get_resource_add_neq_fst in VALID0; auto.
              destruct (tid_dec tid0 tid1); auto; subst.
              exfalso. revert LTGT H0. clear; i.
              hexploit nm_pop_res_is_rm_eq; eauto. i. rewrite <- H in LTGT.
              rewrite nm_find_rm_eq in LTGT. ss.
            - intro PICK. eapply H3 in PICK. clear H2 H3. ii. unfold local_sim_pick in PICK.
              eapply PICK; eauto.
              rewrite get_resource_rs_neq in VALID0. rewrite get_resource_add_neq_fst in VALID0; auto.
              destruct (tid_dec tid0 tid1); auto; subst.
              exfalso. revert LTGT H0. clear; i.
              hexploit nm_pop_res_is_rm_eq; eauto. i. rewrite <- H in LTGT.
              rewrite nm_find_rm_eq in LTGT. ss.
          }
        }

        eapply find_none_aux; eauto. eapply find_none_aux; eauto. auto.
        { destruct (NatMap.find tid0 (NatMap.add tid r_own rs_ctx)) eqn:FIND0.
          { erewrite get_resource_find_some_snd; eauto. apply nm_find_rm_eq. }
          { rewrite get_resource_find_none_snd; auto. }
        }
        { move OSWF0 after FINDO. i. eapply NatMapP.F.remove_in_iff. split.
          { eapply nm_pop_res_find_none in H. eapply NatMapP.F.not_find_in_iff in H.
            destruct (tid_dec tid0 tid'); clarify; ss.
          }
          eapply NatMapP.F.add_in_iff. destruct (tid_dec tid' tid).
          { left; auto. }
          right. apply OSWF0.
          eapply nm_pop_res_is_rm_eq in H. rewrite <- H in H2.
          eapply NatMapP.F.remove_in_iff in H2. des.
          eapply NatMapP.F.add_in_iff in H3. des; clarify.
        }
        { apply nm_find_rm_eq. }

        hexploit LOCAL. eauto.
        eapply find_some_neq_simpl_aux; eauto. eapply find_some_neq_simpl_aux; eauto.
        eapply FINDO. i; des. hexploit H2; ss. clear H2 H3.
        intro SYNC. unfold local_sim_sync in SYNC.
        assert (PROJS: (NatSet.add tid (key_set ths_src)) = (NatSet.add tid0 (key_set ths_src0))).
        { eapply proj_add_aux; eauto. }
        rewrite <- PROJS.
        eapply SYNC; eauto; clear SYNC.
        + eapply ura_wf_get_resource_neq; eauto.
        + rewrite PROJS. unfold NatSet.add. rewrite <- tids_fmap_add_same_eq. rewrite H1; auto.

      - i; clarify. destruct (tid_dec tid tid0) eqn:TID1.
        { clarify. exfalso. hexploit nm_pop_find_none_add_same_equal. eapply THSRC. eauto. i; des; clarify. }
        assert (FINDO: exists o', Th.find tid0 os = Some o').
        { destruct (Th.find tid0 os) eqn:FINDOS. eauto. exfalso.
          apply NatMapP.F.not_find_in_iff in FINDOS. apply FINDOS.
          apply OSWF0. apply NatMapP.F.in_find_iff. ii.
          eapply nm_pop_find_some in H. rewrite nm_find_add_neq in H; auto.
          rewrite H in H2; ss.
        }
        des.
        hexploit LOCAL. eauto.
        eapply find_some_neq_simpl_aux; eauto. eapply find_some_neq_simpl_aux; eauto. eauto.
        i; des. hexploit H3; ss. clear H2 H3. intro PICK.
        assert (PROJS: (NatSet.add tid (key_set ths_src)) = (NatSet.add tid0 (key_set ths_src0))).
        { eapply proj_add_aux; eauto. }
        unfold local_sim_pick in PICK. hexploit PICK; clear PICK.
        eauto.
        { instantiate (1:= sum_of_resources (snd (get_resource tid0 (NatMap.add tid r_own rs_ctx)))).
          revert VALID. eapply ura_wf_get_resource_neq; auto.
        }
        { rewrite PROJS. unfold NatSet.add. rewrite <- tids_fmap_add_same_eq. rewrite H1; eauto. }
        i; des. esplits; eauto.
        { rewrite PROJS in H2. unfold NatSet.add in H2. rewrite <- tids_fmap_add_same_eq in H2. eauto. }
        { instantiate (1:=Th.add tid o1 os). econs. all: eauto.
          - apply nm_find_add_eq.
          - apply nm_find_add_eq.
          - i. rewrite !nm_find_add_neq; auto.
        }
        replace (Th.add tid o1 os) with (Th.add tid0 o' (Th.remove tid0 (Th.add tid o1 os))).
        2:{ rewrite <- nm_find_some_rm_add_eq; auto. rewrite nm_find_add_neq; auto. }

        right. eapply CIH.
        { i. destruct (tid_dec tid tid1) eqn:TID2; subst.
          { rename tid1 into tid.
            pose nm_pop_neq_find_some_eq. dup H. eapply e in H4; eauto. dup H0. eapply e in H5; eauto.
            inv H4. split; i; ss. clear H4.
            ii. hexploit LSIM0. eapply INV0.
            { instantiate (1:=r_ctx0).
              rewrite get_resource_rs_neq in VALID0; auto.
              rewrite get_resource_add_eq in VALID0. ss.
            }
            eauto. i. pclearbot.
            match goal with
            | |- lsim _ _ tid _ _ _ _ (_, ?_itr) _ _ => assert (_itr = (x <- trigger Yield;; ktr_src x))
            end.
            { rewrite bind_trigger. f_equal. f_equal. extensionality x. destruct x. ss. }
            rewrite H5. eapply lsim_set_prog. replace o0 with o1; auto.
            { move ORD after H5. rewrite nm_find_rm_neq in ORD; auto.
              rewrite nm_find_add_eq in ORD. clarify.
            }
          }

          { hexploit LOCAL. eauto.
            eapply find_some_neq_aux; eauto. eapply find_some_neq_aux; eauto.
            { rewrite NatMapP.F.remove_o in ORD. des_ifs. rewrite nm_find_add_neq in ORD; eauto. }
            i; des. split.
            - intro SYNC. eapply H4 in SYNC. clear H4 H5. ii. unfold local_sim_sync in SYNC.
              eapply SYNC; eauto.
              rewrite get_resource_rs_neq in VALID0. rewrite get_resource_add_neq_fst in VALID0; auto.
              destruct (tid_dec tid0 tid1); auto; subst.
              exfalso. revert LTGT H0. clear; i.
              hexploit nm_pop_res_is_rm_eq; eauto. i. rewrite <- H in LTGT.
              rewrite nm_find_rm_eq in LTGT. ss.
            - intro PICK. eapply H5 in PICK. clear H4 H5. ii. unfold local_sim_pick in PICK.
              eapply PICK; eauto.
              rewrite get_resource_rs_neq in VALID0. rewrite get_resource_add_neq_fst in VALID0; auto.
              destruct (tid_dec tid0 tid1); auto; subst.
              exfalso. revert LTGT H0. clear; i.
              hexploit nm_pop_res_is_rm_eq; eauto. i. rewrite <- H in LTGT.
              rewrite nm_find_rm_eq in LTGT. ss.
          }
        }

        eapply find_none_aux; eauto. eapply find_none_aux; eauto. auto.
        { destruct (NatMap.find tid0 (NatMap.add tid r_own rs_ctx)) eqn:FIND0.
          { erewrite get_resource_find_some_snd; eauto. apply nm_find_rm_eq. }
          { rewrite get_resource_find_none_snd; auto. }
        }
        { move OSWF0 after FINDO. i. eapply NatMapP.F.remove_in_iff. split.
          { eapply nm_pop_res_find_none in H. eapply NatMapP.F.not_find_in_iff in H.
            destruct (tid_dec tid0 tid'); clarify; ss.
          }
          eapply NatMapP.F.add_in_iff. destruct (tid_dec tid' tid).
          { left; auto. }
          right. apply OSWF0.
          eapply nm_pop_res_is_rm_eq in H. rewrite <- H in H4.
          eapply NatMapP.F.remove_in_iff in H4. des.
          eapply NatMapP.F.add_in_iff in H5. des; clarify.
        }
        { apply nm_find_rm_eq. }
        rewrite <- PROJS. eauto.
    }

    { des. clarify. destruct LSIM as [LSIM0 IND]. clear LSIM0.
      hexploit IH; eauto. i.
      pfold. eapply pind10_fold. rewrite bind_trigger. eapply ksim_yieldL.
      esplits; eauto.
      { unfold NatSet.add in FAIR. rewrite <- tids_fmap_add_same_eq in FAIR. eauto. }
      split; [|ss].
      punfold H.
    }

    { clarify. clear rr IH. pclearbot. clear LSIM0. pfold. eapply pind10_fold. eapply ksim_progress. right. eapply CIH; eauto.
      eapply lsim_set_prog; eauto.
    }

  Qed.

End PROOF.
