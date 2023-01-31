Unset Universe Checking.
From sflib Require Import sflib.
From Paco Require Import paco.
From ITree Require Import ITree.
From Fairness Require Import
  ITreeLib WFLib Axioms pind PCM Mod ModSim ModSimAux ModSimNat AddWorld ModAddSim OpenMod.

Import Lia.
Import OMod.
Import Mod.
Import RelationClasses.

Section CLOSE_MONO_SIM.

  Context {M1: Mod.t} {M2_src M2_tgt : Mod.t}.
  Context {wf_src : WF}.
  Context `{world : URA.t}.

  Variable I : shared (state M2_src) (state M2_tgt) (ident M2_src) (ident M2_tgt) wf_src nat_wf -> world -> Prop.

  Definition lift_ma :=
    fun (x : @shared
            (OMod.close M1 M2_src).(state) (OMod.close M1 M2_tgt).(state)
            (OMod.close M1 M2_src).(ident) (OMod.close M1 M2_tgt).(ident)
            (sum_wf wf_src nat_wf) nat_wf)
      (r : URA.prod threadsRA world)
    => let '(ths, IM_SRC, IM_TGT, st_src, st_tgt) := x in
      exists im_src0 ths_ctx0 ths_usr0,
        let im_ctx0 := pick_ctx IM_TGT in
        let im_tgt0 := chop_ctx ths_usr0 IM_TGT in
        IM_SRC = add_ctx im_ctx0 im_src0
        /\ NatMapP.Partition ths ths_ctx0 ths_usr0
        /\ fst r = global_th ths_ctx0 ths_usr0
        /\ fst st_src = fst st_tgt
        /\ lifted I (ths_usr0, im_src0, im_tgt0, snd st_src, snd st_tgt) (snd r).

  Opaque lifted threadsRA URA.prod.

  Lemma lift_ma_local_sim_ub R_src R_tgt (RR : R_src -> R_tgt -> Prop) ktr_src itr_tgt
    : local_sim lift_ma RR (Vis (inl1 (inl1 (inl1 Undefined))) ktr_src) itr_tgt.
  Proof.
    (* treat as if tid ∈ ths_ctx *)
    intros ths IM_SRC0 IM_TGT0 st_src0 st_tgt0 [r_sha_th0 r_sha_w0] [r_ctx_th0 r_ctx_w0] INV0_0 tid ths0 THS0 VALID0_0 IM_TGT1 TID_TGT.
    simpl in INV0_0. des. subst r_sha_th0. unfold_prod VALID0_0.
    assert (CTX_TGT : pick_ctx IM_TGT0 = pick_ctx IM_TGT1).
    { extensionalities i. specialize (TID_TGT (inr (inl i))). ss. }
    assert (USR_TGT : chop_ctx ths_usr0 IM_TGT0 = chop_ctx ths_usr0 IM_TGT1).
    { extensionalities i. destruct i as [i|i].
      - specialize (TID_TGT (inl i)). ss. des_ifs. exfalso.
        eapply inv_add_new in THS0. des. eapply THS0.
        eapply Partition_In_right in INV0_1. eapply INV0_1.
        ss.
      - specialize (TID_TGT (inr (inr i))). ss.
    }
    exists (global_th (TIdSet.add tid ths_ctx0) ths_usr0, r_sha_w0), (local_th_context tid, URA.unit). splits.
    { exists im_src0, (TIdSet.add tid ths_ctx0), ths_usr0. splits; ss.
      - subst. rewrite CTX_TGT. ss.
      - eauto using NatMapP.Partition_sym, Partition_add.
      - rewrite USR_TGT in INV0_4. ss.
    }
    { unfold_prod. split.
      - eapply inv_add_new in THS0. des; subst. eapply global_th_alloc_context.
        + eauto.
        + eapply inv_add_new. split; ss.
          ii. eapply THS0. eapply (Partition_In_left INV0_1). ss.
        + ii. eapply THS0. eapply (Partition_In_right INV0_1). ss.
      - rewrite URA.unit_id. eauto.
    }
    i. pfold. eapply pind9_fold. rewrite <- bind_trigger. econs.
  Qed.

  Notation pind := (fun r => pind9 (__lsim _ _ r) top9).
  Notation cpn := (cpn9 _).
  Tactic Notation "muclo" uconstr(H) :=
    eapply gpaco9_uclo; [auto with paco|apply H|].

  Lemma lift_ma_local_sim_usr R_src R_tgt (RR : R_src -> R_tgt -> Prop) itr_src itr_tgt
        (SIM : local_sim (lifted I) RR itr_src itr_tgt)
    :
    forall ths0 im_src0
           im_tgt0 st_src0 st_tgt0
           (r_shared0 r_ctx0 : URA.prod threadsRA world)
           (INV: lift_ma (ths0, im_src0, im_tgt0, st_src0, st_tgt0) r_shared0)
           (tid : NatMap.key) (ths1 : NatMap.t unit)
           (THS: TIdSet.add_new tid ths0 ths1)
           (VALID: URA.wf (r_shared0 ⋅ r_ctx0)),
    forall im_tgt1
           (TID_TGT: fair_update im_tgt0 im_tgt1 (sum_fmap_l (fun i : thread_id => if tid_dec i tid then Flag.success else Flag.emp))),
    exists r_shared1 r_own : URA.prod threadsRA world,
      (<<INV: lift_ma (ths1, im_src0, im_tgt1, st_src0, st_tgt0) r_shared1 >>) /\
        (<<VALID: URA.wf (r_shared1 ⋅ r_own ⋅ r_ctx0) >>) /\
        (forall ths im_src1 im_tgt2 st_src2 st_tgt2
                (r_shared2 r_ctx2 : URA.prod threadsRA world)
                (INV: lift_ma (ths, im_src1, im_tgt2, st_src2, st_tgt2) r_shared2)
                (VALID: URA.wf (r_shared2 ⋅ r_own ⋅ r_ctx2)),
          forall im_tgt3
                 (TGT: fair_update im_tgt2 im_tgt3 (sum_fmap_l (tids_fmap tid ths))),
            (<<LSIM:
              forall fs ft : bool,
                lsim lift_ma tid (fun (r_src: R_src) (r_tgt: R_tgt) (r_ctx: URA.car) '(ths2, im_src1, im_tgt1, st_src1, st_tgt1) =>
                                    (exists ths3 r_own r_shared,
                                        (<<TIN: TIdSet.In tid ths2>>) /\
                                          (<<THS: NatMap.remove tid ths2 = ths3>>) /\
                                          (<<VALID: URA.wf (r_shared ⋅ r_own ⋅ r_ctx)>>) /\
                                          (<<INV: lift_ma (ths3, im_src1, im_tgt1, st_src1, st_tgt1) r_shared>>) /\
                                          (<<RET: RR r_src r_tgt>>))) fs ft r_ctx2 (embed_itree M1 M2_src itr_src) (embed_itree M1 M2_tgt itr_tgt)
                     (ths, im_src1, im_tgt3, st_src2, st_tgt2) >>))
  .
  Proof.
    (* tid ∈ ths_usr *)
    intros ths IM_SRC0 IM_TGT0 st_src0 st_tgt0 [r_sha_th0 r_sha_w0] [r_ctx_th0 r_ctx_w0] INV0_0 tid ths0 THS0 VALID0_0. i.
    simpl in INV0_0. des. subst r_sha_th0. unfold_prod VALID0_0.
    move SIM at bottom.
    assert (THS0' : TIdSet.add_new tid ths_usr0 (TIdSet.add tid ths_usr0)).
    { eapply inv_add_new. split; ss. eapply inv_add_new in THS0. des.
      eapply Partition_In_right in INV0_1. eauto.
    }
    assert (TID_TGT' : fair_update (chop_ctx ths_usr0 IM_TGT0) (chop_ctx (NatSet.add tid ths_usr0) im_tgt1) (sum_fmap_l (fun i => if Nat.eq_dec i tid then Flag.success else Flag.emp))).
    { ii. destruct i as [i|i]; ss.
      - specialize (TID_TGT (inl i)). ss. destruct (Nat.eq_dec i tid); ss.
        assert (H : tid <> i) by lia.
        eapply NatMapP.F.add_neq_in_iff with (m := ths_usr0) (e := tt) in H.
        des_ifs; tauto.
      - specialize (TID_TGT (inr (inr i))). des_ifs.
    }
    specialize (SIM ths_usr0 im_src0 (chop_ctx ths_usr0 IM_TGT0) (snd st_src0) (snd st_tgt0) r_sha_w0 r_ctx_w0 INV0_4 tid (NatSet.add tid ths_usr0) THS0' VALID0_1 (chop_ctx (NatSet.add tid ths_usr0) im_tgt1) TID_TGT').
    destruct SIM as [r_sha_w1 [r_own_w1 [INV_USR [VALID_USR SIM]]]].
    exists (global_th ths_ctx0 (NatSet.add tid ths_usr0), r_sha_w1), (local_th_user tid, r_own_w1). splits.
    { eapply inv_add_new in THS0. des. subst.
      ss. esplits; ss.
      - instantiate (1 := im_src0). extensionalities i. destruct i; ss.
        specialize (TID_TGT (inr (inl i))). ss.
        unfold pick_ctx. f_equal. ss.
      - eapply Partition_add; eauto.
        eapply inv_add_new; eauto.
      - eapply INV_USR.
    }
    { unfold_prod. split.
      - eapply global_th_alloc_user; eauto.
        eapply inv_add_new in THS0. des. ii. eapply THS0.
        eapply Partition_In_left in INV0_1. eapply INV0_1. ss.
      - eauto.
    }
    intros ths2 IM_SRC2 IM_TGT2 st_src2 st_tgt2 [r_sha_th2 r_sha_w2] [r_ctx_th2 r_ctx_w2] INV2_0 VALID2_0 IM_TGT2' TGT fs ft.
    simpl in INV2_0. destruct INV2_0 as [im_src2 [ths_ctx2 [ths_usr2 INV2_0]]]. des. subst r_sha_th2. unfold_prod VALID2_0.
    assert (TGT' : @fair_update _ nat_wf (chop_ctx ths_usr2 IM_TGT2) (chop_ctx ths_usr2 IM_TGT2') (sum_fmap_l (tids_fmap tid ths_usr2))).
    { eapply chop_ctx_fair_thread2.
      - eapply Partition_In_right in INV2_1. eapply INV2_1.
      - eauto.
    }
    specialize (SIM ths_usr2 im_src2 (chop_ctx ths_usr2 IM_TGT2) (snd st_src2) (snd st_tgt2) r_sha_w2 r_ctx_w2 INV2_4 VALID2_1 (chop_ctx ths_usr2 IM_TGT2') TGT' fs ft).
    unfold embed_l, embed_r.
    eapply pick_ctx_fair_thread in TGT. rewrite TGT in INV2_0.
    clear - INV2_0 INV2_1 INV2_3 VALID2_0 VALID2_1 SIM.
    move tid before I.
    rename
      ths2 into ths0, ths_ctx2 into ths_ctx0, ths_usr2 into ths_usr0,
      im_src2 into im_src0, IM_SRC2 into IM_SRC0, IM_TGT2' into IM_TGT0, st_src2 into st_src0, st_tgt2 into st_tgt0,
      r_sha_w2 into r_sha_w0, r_ctx_th2 into r_ctx_th0, r_ctx_w2 into r_ctx_w0, r_own_w1 into r_own_w0,
      INV2_0 into INV0, INV2_1 into INV1, INV2_3 into INV2, VALID2_0 into VALID_TH0, VALID2_1 into VALID_W0.
    revert_until tid. ginit. gcofix CIH. i. gstep. punfold SIM.
    match type of SIM with pind9 _ _ _ _ ?RR _ _ _ _ _ ?SHA => remember RR as RR_MEM; remember SHA as SHA_MEM end.
    revert RR ths0 ths_ctx0 ths_usr0 st_src0 st_tgt0 r_sha_w0 r_own_w0 r_ctx_th0 im_src0 IM_SRC0 IM_TGT0 INV0 INV1 INV2 VALID_TH0 VALID_W0 HeqRR_MEM HeqSHA_MEM.
    pattern R_src, R_tgt, RR_MEM, fs, ft, r_ctx_w0, itr_src, itr_tgt, SHA_MEM.
    revert R_src R_tgt RR_MEM fs ft r_ctx_w0 itr_src itr_tgt SHA_MEM SIM.
    eapply pind9_acc. intros rr DEC IH R_src R_tgt RR_MEM fs ft r_ctx_w0 itr_src itr_tgt SHA_MEM. i.
    clear DEC. subst RR_MEM SHA_MEM.
    eapply pind9_unfold in PR; eauto with paco. eapply pind9_fold. inv PR.
    - clear - LSIM VALID_TH0 VALID_W0 INV1 INV2.
      rewrite 2 embed_itree_ret. econs.
      ss. des. subst. (* inversion INV2. clear INV2. subst ths_ctx1 ths_usr1 ths3 IM_SRC0. *)
      exists (NatMap.remove tid ths0), (URA.unit, r_own), (global_th ths_ctx0 (NatMap.remove tid ths_usr0), r_shared).
      splits; ss.
      + eapply Partition_In_right; eauto.
        eapply local_th_user_in_user in VALID_TH0. exact VALID_TH0.
      + unfold_prod. split.
        * eapply global_th_dealloc_user; eauto.
        * ss.
      + esplits; ss.
        * eapply local_th_user_in_user in VALID_TH0.
          eapply Partition_remove; eauto.
        * eapply lifted_drop_imap; eauto.
          { i. destruct i as [i|i]; ss.
            - assert (i = tid \/ tid <> i) by lia. destruct H.
              + pose proof NatMap.remove_1 H (m := ths_usr0). des_ifs; unfold le; ss; lia.
              + pose proof (@NatMapP.F.remove_neq_in_iff _ ths_usr0 tid i H). des_ifs; try tauto; reflexivity.
            - des_ifs. left. ss.
          }
    - rewrite embed_itree_tau. econs. split; ss.
      destruct LSIM. eapply IH; eauto.
    - rewrite embed_itree_trigger_eventE. econs.
      des. destruct LSIM. exists x. split; ss.
      eapply pind9_fold. econs. split; ss. eapply IH; eauto.
    - rewrite embed_itree_trigger_put. econs. split; ss. eapply pind9_fold. econs. split; ss.
      eapply pind9_fold. econs. split; ss. destruct LSIM. eapply IH; eauto.
      + destruct st_src0, st_tgt0. ss.
      + destruct st_src0. ss.
    - rewrite embed_itree_trigger_get. econs. split; ss.
      eapply pind9_fold. econs; ss. split; ss.
      destruct LSIM. eapply IH; eauto.
    - rewrite embed_itree_trigger_cE. econs. split; ss. eapply pind9_fold. econs; ss. split; ss.
      destruct LSIM. eapply IH; eauto.
    - rewrite embed_itree_trigger_eventE. econs.
    - rewrite embed_itree_trigger_eventE. econs.
      des. destruct LSIM0. exists (add_ctx (pick_ctx IM_TGT0) im_src1). splits.
      { clear - FAIR. ii. destruct i as [i|i]; ss.
        specialize (FAIR i). des_ifs.
        - econs. ss.
        - f_equal. ss.
      }
      split; ss. eapply pind9_fold. econs; ss. split; ss. eapply IH; eauto.
    - rewrite embed_itree_tau. econs. split; ss.
      destruct LSIM. eapply IH; eauto.
    - rewrite embed_itree_trigger_eventE. econs. i. specialize (LSIM x). split; ss.
      eapply pind9_fold. econs. split; ss.
      destruct LSIM. eapply IH; eauto.
    - rewrite embed_itree_trigger_put. econs. split; ss. eapply pind9_fold. econs; ss. split; ss.
      eapply pind9_fold. econs. split; ss.
      destruct LSIM. eapply IH; eauto.
      + destruct st_src0, st_tgt0. ss.
      + destruct st_tgt0. ss.
    - rewrite embed_itree_trigger_get. econs. split; ss. eapply pind9_fold. econs; ss. split; ss.
      destruct LSIM. eapply IH; eauto.
    - rewrite embed_itree_trigger_cE. econs. split; ss. eapply pind9_fold. econs; ss. split; ss.
      destruct LSIM. eapply IH; eauto.
    - rewrite embed_itree_trigger_eventE. econs. intros IM_TGT1 FAIR. split; ss.
      eapply pind9_fold. econs; ss. split; ss.
      assert (FAIR' : fair_update (chop_ctx ths_usr0 IM_TGT0) (chop_ctx ths_usr0 IM_TGT1) (sum_fmap_r f)).
      { ii. destruct i as [i|i]; ss.
        - specialize (FAIR (inl i)). ss. des_ifs.
        - specialize (FAIR (inr (inr i))). ss.
      }
      specialize (LSIM (chop_ctx ths_usr0 IM_TGT1) FAIR').
      destruct LSIM. eapply IH; eauto.
      + extensionalities i. destruct i; ss. f_equal.
        specialize (FAIR (inr (inl i))). ss.
    - rewrite 2 embed_itree_trigger_eventE. econs. i. specialize (LSIM ret). pclearbot.
      muclo lsim_indC_spec. cbn. econs; eauto.
      muclo lsim_indC_spec. cbn. econs; eauto.
      gfinal. left. eapply CIH; eauto.
    - rewrite 2 embed_itree_trigger_callE. apply lsim_call.
      i. specialize (LSIM ret). pclearbot.
      muclo lsim_indC_spec. ss. econs.
      muclo lsim_indC_spec. ss. econs.
      gfinal. left. eapply CIH; eauto.
    - rewrite 2 embed_itree_trigger_cE.
      eapply lsim_yieldL. split; ss.
      rewrite <- embed_itree_trigger_cE.
      eapply pind9_fold. econs. split; ss.
      destruct LSIM. eapply IH; eauto.
    - rewrite 2 embed_itree_trigger_cE.
      eapply lsim_yieldR.
      { instantiate (1 := (global_th ths_ctx0 ths_usr0, r_shared)).
        ss. exists im_src0, ths_ctx0, ths_usr0. splits; ss.
      }
      { instantiate (1 := (local_th_user tid, r_own)). unfold_prod. split; ss. }
      intros ths1 IM_SRC1 IM_TGT1 st_src1 st_tgt1 [r_sha_th1 r_sha_w1] [r_ctx_th1 r_ctx_w1] INV1_0 VALID1_0 IM_TGT2 TGT.
      split; ss. des. unfold_prod VALID1_0.
      assert (TGT' : fair_update (chop_ctx ths_usr1 IM_TGT1) (chop_ctx ths_usr1 IM_TGT2) (sum_fmap_l (tids_fmap tid ths_usr1))).
      { ii. destruct i as [i|i]; ss.
        - eapply Partition_In_right in INV1_1. specialize (INV1_1 i). specialize (TGT (inl i)). ss.
          unfold tids_fmap in *. destruct (Nat.eq_dec i tid); ss. des_ifs.
          exfalso. tauto.
        - specialize (TGT (inr (inr i))). ss.
      }
      specialize (LSIM ths_usr1 im_src1 (chop_ctx ths_usr1 IM_TGT1) (snd st_src1) (snd st_tgt1) r_sha_w1 r_ctx_w1 INV1_4 VALID1_1 (chop_ctx ths_usr1 IM_TGT2) TGT').
      eapply pind9_fold. econs; ss. split; ss.
      rewrite <- embed_itree_trigger_cE.
      destruct LSIM. eapply IH; eauto.
      + subst. extensionalities i. destruct i as [i|i]; ss. f_equal.
        specialize (TGT (inr (inl i))). ss.
      + subst. ss.
    - rewrite 2 embed_itree_trigger_cE. eapply lsim_sync.
      { instantiate (1 := (global_th ths_ctx0 ths_usr0, r_shared)).
        ss. exists im_src0, ths_ctx0, ths_usr0. splits; ss.
      }
      { instantiate (1 := (local_th_user tid, r_own)). unfold_prod. split; ss. }
      intros ths1 IM_SRC1 IM_TGT1 st_src1 st_tgt1 [r_sha_th1 r_sha_w1] [r_ctx_th1 r_ctx_w1] INV1_0 VALID1_0 IM_TGT2 TGT.
      ss. des. unfold_prod VALID1_0.
      assert (TGT' : fair_update (chop_ctx ths_usr1 IM_TGT1) (chop_ctx ths_usr1 IM_TGT2) (sum_fmap_l (tids_fmap tid ths_usr1))).
      { ii. destruct i as [i|i]; ss.
        - eapply Partition_In_right in INV1_1. specialize (INV1_1 i). specialize (TGT (inl i)). ss.
          unfold tids_fmap in *. destruct (Nat.eq_dec i tid); ss. des_ifs.
          exfalso. tauto.
        - specialize (TGT (inr (inr i))). ss.
      }
      specialize (LSIM ths_usr1 im_src1 (chop_ctx ths_usr1 IM_TGT1) (snd st_src1) (snd st_tgt1) r_sha_w1 r_ctx_w1 INV1_4 VALID1_1 (chop_ctx ths_usr1 IM_TGT2) TGT').
      pclearbot.
      muclo lsim_indC_spec. cbn. econs; eauto.
      muclo lsim_indC_spec. cbn. econs; eauto.
      gfinal. left. eapply CIH; eauto.
      + subst. extensionalities i. destruct i as [i|i]; ss. f_equal.
        specialize (TGT (inr (inl i))). ss.
      + subst. ss.
    - econs. pclearbot. gfinal. left. eapply CIH; eauto.
  Qed.

  Lemma lift_ma_local_sim_ctx
        (FSIM: forall (fn : string) (args : Any.t),
            match funs M2_src fn with
            | Some ktr_src =>
                match funs M2_tgt fn with
                | Some ktr_tgt => local_sim I eq (ktr_src args) (ktr_tgt args)
                | None => False
                end
            | None => match funs M2_tgt fn with
                      | Some _ => False
                      | None => True
                      end
            end)
    :
    forall R (itr: itree _ R),
      local_sim (lift_ma) eq (close_itree M1 M2_src itr) (close_itree M1 M2_tgt itr)
  .
  Proof.
    i.
    intros ths IM_SRC0 IM_TGT0 st_src0 st_tgt0 [r_sha_th0 r_sha_w0] [r_ctx_th0 r_ctx_w0] INV0_0 tid ths0 THS0 VALID0_0 IM_TGT1 TID_TGT.
    simpl in INV0_0. des. subst r_sha_th0. unfold_prod VALID0_0.
    assert (CTX_TGT : pick_ctx IM_TGT0 = pick_ctx IM_TGT1).
    { extensionalities i. specialize (TID_TGT (inr (inl i))). ss. }
    assert (USR_TGT : chop_ctx ths_usr0 IM_TGT0 = chop_ctx ths_usr0 IM_TGT1).
    { extensionalities i. destruct i as [i|i].
      - specialize (TID_TGT (inl i)). ss. des_ifs. exfalso.
        eapply inv_add_new in THS0. des. eapply THS0.
        eapply Partition_In_right in INV0_1. eapply INV0_1.
        ss.
      - specialize (TID_TGT (inr (inr i))). ss.
    }
    exists (global_th (TIdSet.add tid ths_ctx0) ths_usr0, r_sha_w0), (local_th_context tid, URA.unit). splits.
    { exists im_src0, (TIdSet.add tid ths_ctx0), ths_usr0. splits; ss.
      - subst. rewrite CTX_TGT. ss.
      - eauto using NatMapP.Partition_sym, Partition_add.
      - rewrite USR_TGT in INV0_4. ss.
    }
    { unfold_prod. split.
      - eapply inv_add_new in THS0. des; subst. eapply global_th_alloc_context.
        + eauto.
        + eapply inv_add_new. split; ss.
          ii. eapply THS0. eapply (Partition_In_left INV0_1). ss.
        + ii. eapply THS0. eapply (Partition_In_right INV0_1). ss.
      - rewrite URA.unit_id. eauto.
    }
    intros ths1 IM_SRC1 IM_TGT2 st_src1 st_tgt1 [r_sha_th1 r_sha_w1] [r_ctx_th1 r_ctx_w1] INV1_0 VALID1_0.
    intros IM_TGT2' TGT fs ft.
    simpl in INV1_0. des. subst r_sha_th1. unfold_prod VALID1_0.
    unfold embed_l, embed_r.
    assert (INV : lift_ma (ths1, IM_SRC1, IM_TGT2', st_src1, st_tgt1) (global_th ths_ctx1 ths_usr1, r_sha_w1)).
    { ss. exists im_src1, ths_ctx1, ths_usr1. splits; ss.
      - eapply pick_ctx_fair_thread in TGT. rewrite <- TGT. ss.
      - eapply shared_rel_wf_lifted; eauto.
        eapply chop_ctx_fair_thread1; eauto.
        eapply local_th_context_in_context; eauto.
    }
    clear - FSIM INV VALID1_0 VALID1_1. move itr after tid.
    rename
      ths1 into ths0, ths_ctx1 into ths_ctx0, ths_usr1 into ths_usr0,
      IM_SRC1 into IM_SRC0, IM_TGT2' into IM_TGT0, st_src1 into st_src0, st_tgt1 into st_tgt0,
      r_sha_w1 into r_sha_w0, r_ctx_th1 into r_ctx_th0, r_ctx_w1 into r_ctx_w0,
      INV into INV0, VALID1_0 into VALID_TH0, VALID1_1 into VALID_W0.
    revert_until tid. ginit. gcofix CIH. i.
    destruct_itree itr; [| | destruct e as [[[|]|]|] ].
    - rewrite 2 close_itree_ret.
      gstep. eapply pind9_fold. econs. ss.
      exists (NatSet.remove tid ths0), (URA.unit, URA.unit), (global_th (NatSet.remove tid ths_ctx0) ths_usr0, r_sha_w0).
      splits; ss.
      { unfold_prod. split.
        - eapply global_th_dealloc_context; eauto.
        - eauto.
      }
      { des. inversion INV2. subst ths_ctx1 ths_usr1. exists im_src0, (NatSet.remove tid ths_ctx0), ths_usr0. splits; ss.
        eapply local_th_context_in_context in VALID_TH0.
        eauto using NatMapP.Partition_sym, Partition_remove.
      }
    - rewrite 2 close_itree_tau.
      gstep.
      eapply pind9_fold. econs. split; ss.
      eapply pind9_fold. econs. split; ss.
      eapply pind9_fold. econs.
      gfinal. left. eapply CIH; eauto.
    - rewrite 2 close_itree_vis_eventE.
      rewrite <- 2 bind_trigger.
      gstep. destruct e; ss.
      + eapply pind9_fold. eapply lsim_chooseR. i. esplit; ss.
        eapply pind9_fold. eapply lsim_chooseL. exists x. esplit; ss.
        eapply pind9_fold. econs. split; ss.
        eapply pind9_fold. econs. split; ss.
        eapply pind9_fold. eapply lsim_progress.
        gfinal. left. eapply CIH; eauto.
      + eapply pind9_fold. eapply lsim_fairR. intros IM_TGT1 FAIR. esplit; ss.
        eapply pind9_fold. eapply lsim_fairL.
        des. inversion INV2. subst ths_ctx1 ths_usr1. exists (add_ctx (pick_ctx IM_TGT1) im_src0). split.
        { subst. ii. destruct i; ss.
          specialize (FAIR (inr (inl i))). unfold pick_ctx. ss. des_ifs.
          + econs. ss.
          + f_equal. ss.
        }
        split; ss.
        eapply pind9_fold. econs. split; ss.
        eapply pind9_fold. econs. split; ss.
        eapply pind9_fold. eapply lsim_progress.
        gfinal. left. des. eapply CIH; eauto.
        { esplits; eauto. eapply chop_ctx_fair_ctx in FAIR. rewrite <- FAIR. ss. }
      + eapply pind9_fold. eapply lsim_observe. i.
        gstep.
        eapply pind9_fold. econs. split; ss.
        eapply pind9_fold. econs. split; ss.
        eapply pind9_fold. econs.
        gfinal. left. eapply CIH; eauto.
      + eapply pind9_fold. eapply lsim_UB.
    - rewrite 2 close_itree_vis_cE.
      rewrite <- 2 bind_trigger.
      gstep. destruct c.
      + eapply pind9_fold. eapply lsim_sync.
        { eapply INV0. }
        { instantiate (1 := (local_th_context tid, ε)). unfold_prod. split; ss. }
        intros ths1 IM_SRC1 IM_TGT1 st_src1 st_tgt1 [r_sha_th1 r_sha_w1] [r_ctx_th1 r_ctx_w1] INV1_0 VALID1_0 IM_TGT1' TGT.
        simpl in INV1_0. des. subst r_sha_th1. rename im_src0 into im_src1. unfold_prod VALID1_0.
        gstep.
        eapply pind9_fold. econs. split; ss.
        eapply pind9_fold. econs. split; ss.
        eapply pind9_fold. econs.
        gfinal. left. eapply CIH; eauto.
        { exists im_src1, ths_ctx1, ths_usr1. ss. splits; ss.
          - eapply pick_ctx_fair_thread in TGT. rewrite <- TGT. ss.
          - eapply shared_rel_wf_lifted; eauto.
            eapply chop_ctx_fair_thread1; eauto.
            eapply local_th_context_in_context; eauto.
        }
      + eapply pind9_fold. eapply lsim_tidR. esplit; ss.
        eapply pind9_fold. eapply lsim_tidL. esplit; ss.
        eapply pind9_fold. econs. split; ss.
        eapply pind9_fold. econs. split; ss.
        eapply pind9_fold. eapply lsim_progress.
        gfinal. left. eapply CIH; eauto.
    - destruct c. rewrite 2 close_itree_vis_call. simpl.
      specialize (FSIM fn arg).
      des_ifs.
      + rewrite <- 2 bind_trigger.
        gstep. eapply pind9_fold. eapply lsim_sync; eauto.
        { instantiate (1:=(local_th_context tid, ε)). unfold_prod; ss. }
        move FSIM at bottom.
        eapply local_sim_clos_trans in FSIM; [|econs; exact 0].
        eapply local_sim_wft_mono with (wft_lt := lt (wf_clos_trans nat_wf)) in FSIM; cycle 1.
        { i; econs; ss. eauto. }

        (*** TODO: somehow exploit FSIM ***)
        i.

        Set Nested Proofs Allowed.
        Lemma lift_ma_pop_push ths0 im_src im_tgt st_src st_tgt r0 r_ctx
              tid
              (INV: lift_ma (ths0, im_src, im_tgt, st_src, st_tgt) r0)
              (WF: URA.wf (r0 ⋅ (local_th_context tid, ε) ⋅ r_ctx))
          :
          exists ths1 r1,
            (<<INV: lift_ma (ths1, im_src, im_tgt, st_src, st_tgt) r1>>) /\
              (<<WF: URA.wf (r1 ⋅ r_ctx)>>) /\
              (<<ADD: TIdSet.add_new tid ths1 ths0>>).
        Proof.
          red in INV. des. subst. destruct r0, r_ctx. ss. subst.
          rewrite unfold_prod_wf in WF. rewrite unfold_prod_add in WF. ss. des.
          hexploit local_th_context_in_context; eauto. i.
          hexploit Partition_remove.
          { eapply NatMapP.Partition_sym. eauto. }
          { eauto. }
          intros PART. hexploit global_th_dealloc_context; eauto.
          intros WF1. eexists _, (_, _). esplits.
          { eauto. }
          { eapply NatMapP.Partition_sym. eauto. }
          { ss. }
          { eauto. }
          { eauto. }
          { rewrite URA.unit_id in WF1. rewrite URA.unit_id in WF0.
            rewrite unfold_prod_wf. rewrite unfold_prod_add. auto.
          }
          { rr. econs.
            { eapply nm_find_rm_eq. }
            { eapply nm_find_some_rm_add_eq.
              eapply Partition_In_left in H; eauto.
              eapply NatMapP.F.in_find_iff in H.
              destruct (NatMap.find tid ths0) as [[]|]; ss.
            }
          }
        Qed.

        Lemma lift_ma_push_pop ths im_src im_tgt st_src st_tgt r0 r_ctx
              tid r_own
              (INV: lift_ma (NatMap.remove tid ths, im_src, im_tgt, st_src, st_tgt) r0)
              (WF: URA.wf (r0 ⋅ r_own ⋅ r_ctx))
              (IN: TIdSet.In tid ths)
          :
          exists r1,
            (<<INV: lift_ma (ths, im_src, im_tgt, st_src, st_tgt) r1>>) /\
              (<<WF: URA.wf (r1 ⋅ (local_th_context tid, ε) ⋅ r_ctx)>>).
        Proof.
          red in INV. des. subst. destruct r0, r_own, r_ctx. ss. subst.
          rewrite unfold_prod_wf in WF. rewrite unfold_prod_add in WF. ss. des.
          hexploit global_th_alloc_context.
          { rewrite <- URA.add_assoc in WF. eapply WF. }
          { econs.
            { eapply NatMapP.F.not_find_in_iff. ii.
              eapply Partition_In_left in H; eauto.
              eapply NatMap.remove_1 in H; eauto.
            }
            { ss. }
          }
          { ii. eapply Partition_In_right in H; eauto.
            eapply NatMap.remove_1 in H; eauto.
          }
          i. eexists (_, _). esplits.
          { ss. }
          { eapply NatMapP.Partition_sym.
            eapply Partition_add.
            { eapply NatMapP.Partition_sym. eauto. }
            econs; eauto.
            { eapply NatMapP.F.not_find_in_iff.
              eapply NatMap.remove_1; eauto.
            }
            { eapply nm_find_some_rm_add_eq.
              instantiate (1:=tt). destruct (NatMap.find tid ths) as [[]|] eqn:EQ; ss.
              eapply NatMapP.F.not_find_in_iff in EQ; eauto. ss.
            }
          }
          { ss. }
          { ss. }
          { eauto. }
          rewrite unfold_prod_wf. rewrite unfold_prod_add. ss. split.
          { eapply URA.wf_mon. instantiate (1:=c1). r_wf H. }
          { eapply URA.wf_mon. instantiate (1:=c2). r_wf WF0. }
        Qed.

        hexploit lift_ma_pop_push; eauto. i. des.
        muclo lsim_bindC'_spec. cbn. econs; eauto.
        * hexploit lift_ma_local_sim_usr; eauto.
          { instantiate (1:=im_tgt1). ii. unfold sum_fmap_l. des_ifs. }
          i. des. hexploit H1; eauto. i.
          gfinal. right. eapply paco9_mon; [eapply H|]; ss.
        * i. destruct r_ctx as [r_ctx0 r_ctx2]. destruct shr as [[[[shr0 shr1] shr2] shr3] shr4].
          muclo lsim_indC_spec. cbn. econs; eauto.
          muclo lsim_indC_spec. cbn. econs; eauto.
          des. subst.
          hexploit lift_ma_push_pop; eauto.
          i. des. destruct r0.
          rewrite unfold_prod_wf in WF0. rewrite unfold_prod_add in WF0. ss. des. subst.
          gbase. eapply CIH; eauto.
          esplits; eauto.
      + rewrite <- 2 bind_trigger.
        gstep. eapply pind9_fold. econs; eauto.
    - destruct s.
      + rewrite 2 close_itree_vis_put. ss.
        rewrite <- 2 bind_trigger.
        gstep.
        eapply pind9_fold. eapply lsim_getL. esplit; ss.
        eapply pind9_fold. eapply lsim_getR. esplit; ss.
        rewrite <- 2 bind_trigger.
        eapply pind9_fold. eapply lsim_putL. esplit; ss.
        eapply pind9_fold. eapply lsim_putR. esplit; ss.
        eapply pind9_fold. econs. split; ss.
        eapply pind9_fold. econs. split; ss.
        eapply pind9_fold. eapply lsim_progress.
        gfinal. left. eapply CIH; eauto.
        destruct st_src0, st_tgt0; ss. des; esplits; eauto.
      + rewrite 2 close_itree_vis_get. ss.
        rewrite <- 2 bind_trigger.
        gstep.
        eapply pind9_fold. eapply lsim_getL. esplit; ss.
        eapply pind9_fold. eapply lsim_getR. esplit; ss.
        eapply pind9_fold. econs. split; ss.
        eapply pind9_fold. econs. split; ss.
        eapply pind9_fold. eapply lsim_progress.
        des. rewrite INV3.
        gfinal. left. eapply CIH; eauto. esplits; eauto.
  Qed.

End CLOSE_MONO_SIM.

Section MODADD_THEOREM.

  Theorem ModClose_mono M1 M2_src M2_tgt :
    ModSim.mod_sim M2_src M2_tgt ->
    ModSim.mod_sim (close M1 M2_src) (close M1 M2_tgt).
  Proof.
    i. eapply modsim_nat_modsim_exist in H. inv H.
    pose (I' := @lift_ma M1 M2_src M2_tgt _ _ I).
    constructor 1 with _ _ _ I'.
    { econs. exact 0. }
    { i. exists (S o0). ss. }
    { clear - init.
      intro IM_TGT. specialize (init (chop_ctx NatSet.empty IM_TGT)).
      destruct init as [im_src [r_shared [init R_SHARED]]].
      pose (pick_ctx IM_TGT) as im_ctx.
      exists (add_ctx im_ctx im_src), (global_th NatSet.empty NatSet.empty, r_shared). ss. split.
      - exists im_src. exists NatSet.empty, NatSet.empty. splits; ss.
        + eapply Partition_empty.
        + exists (chop_ctx NatSet.empty IM_TGT). split; ss. ii. left. ss.
      - unfold_prod. split; ss. rewrite URA.unfold_wf. econs; ss. eapply Disjoint_empty.
    }
    i. unfold close, closed_funs; ss. des_ifs.
    - eapply lift_ma_local_sim_ctx; eauto.
  Qed.

  Tactic Notation "muclo" uconstr(H) :=
    eapply gpaco9_uclo; [auto with paco|apply H|].

  Theorem ModClose_assoc M1 M2 M3 :
    ModSim.mod_sim (close M1 (close M2 M3)) (close (close M1 M2) M3).
  Proof.
    pose Unit_wf as VALID.
    pose (conv_im :=
            (fun im_tgt i =>
               match i with
               | inl i => im_tgt (inr (inl (inl i)))
               | inr (inl i) => im_tgt (inr (inl (inr i)))
               | inr (inr i) => im_tgt (inr (inr i))
               end)
            : @imap (ident_tgt (close (close M1 M2) M3).(ident)) nat_wf ->
              @imap (close M1 (close M2 M3)).(ident) nat_wf).
    pose (I := fun (x : @shared
                        (close M1 (close M2 M3)).(state) (close (close M1 M2) M3).(state)
                        (close M1 (close M2 M3)).(ident) (close (close M1 M2) M3).(ident)
                        nat_wf nat_wf)
                 (w : Unit)
               => let '(ths, im_src, im_tgt, st_src, st_tgt) := x in
                 (fst st_src : state M1) = fst (fst st_tgt)
                 /\ (fst (snd st_src) : state M2) = snd (fst st_tgt)
                 /\ (snd (snd st_src) : state M3) = snd st_tgt
                 /\ im_src = conv_im im_tgt
         ).
    constructor 1 with nat_wf nat_wf Unit I.
    { econs. exact 0. }
    { i. exists (S o0). ss. }
    { i. exists (conv_im im_tgt), tt. splits; ss. }
    i. do 2 (ss; unfold closed_funs). destruct (funs M1 fn); ss.
    remember (k args) as itr; clear k args Heqitr.
    ii. exists tt, tt. splits; ss.
    { des. splits; ss.
      rewrite INV2. extensionalities i. destruct i as [|[|]].
      - specialize (TID_TGT (inr (inl (inl i)))); ss.
      - specialize (TID_TGT (inr (inl (inr i)))); ss.
      - specialize (TID_TGT (inr (inr i))); ss.
    }
    i.
    assert (INV_CIH : I (ths, im_src1, im_tgt3, st_src2, st_tgt2) tt).
    { des. ss. splits; ss.
      rewrite INV3. extensionalities i. destruct i as [|[|]].
      - specialize (TGT (inr (inl (inl i)))); ss.
      - specialize (TGT (inr (inl (inr i)))); ss.
      - specialize (TGT (inr (inr i))); ss.
    }
    clear - INV_CIH. move itr after tid. revert_until tid.
    pose proof Unit_wf as VALID.
    ginit. gcofix CIH. i. destruct_itree itr.
    - rewrite ! close_itree_ret.
      gstep. eapply pind9_fold. eapply lsim_ret.
      ss. eexists. exists tt, tt. des. splits; ss.
    - rewrite ! close_itree_tau.
      gstep.
      eapply pind9_fold. eapply lsim_tauL. split; ss.
      eapply pind9_fold. eapply lsim_tauR. split; ss.
      eapply pind9_fold. eapply lsim_progress.
      gfinal. left. eapply CIH. des. splits; ss.
    - destruct e as [[[e|ce]|cae]|s].
      + rewrite ! close_itree_vis_eventE.
        rewrite <- ! bind_trigger.
        destruct e.
        * gstep. eapply pind9_fold. eapply lsim_chooseR. i. split; ss.
          eapply pind9_fold. eapply lsim_chooseL. exists x. split; ss.
          eapply pind9_fold. eapply lsim_tauL. split; ss.
          rewrite close_itree_tau.
          eapply pind9_fold. eapply lsim_tauR. split; ss.
          eapply pind9_fold. eapply lsim_tauR. split; ss.
          eapply pind9_fold. eapply lsim_progress.
          gfinal. left. eapply CIH. des. splits; ss.
        * gstep. eapply pind9_fold. eapply lsim_fairR. i. split; ss.
          eapply pind9_fold. eapply lsim_fairL. exists (conv_im im_tgt1). split.
          { des. rewrite INV_CIH2. ii. destruct i as [|[|]].
            unfold sum_fmap_r, sum_fmap_l in *. ss.
            - specialize (FAIR (inr (inl (inl i)))). ss.
            - specialize (FAIR (inr (inl (inr i)))). ss.
            - specialize (FAIR (inr (inr i))). ss.
          }
          split; ss.
          eapply pind9_fold. eapply lsim_tauL. split; ss.
          rewrite close_itree_tau.
          eapply pind9_fold. eapply lsim_tauR. split; ss.
          eapply pind9_fold. eapply lsim_tauR. split; ss.
          eapply pind9_fold. eapply lsim_progress.
          gfinal. left. eapply CIH. des. splits; ss.
        * gstep. eapply pind9_fold. eapply lsim_observe. i.
          gstep. eapply pind9_fold. eapply lsim_tauL. split; ss.
          rewrite close_itree_tau.
          eapply pind9_fold. eapply lsim_tauR. split; ss.
          eapply pind9_fold. eapply lsim_tauR. split; ss.
          eapply pind9_fold. eapply lsim_progress.
          gfinal. left. eapply CIH. des. splits; ss.
        * gstep. eapply pind9_fold. eapply lsim_UB.
      + rewrite ! close_itree_vis_cE.
        rewrite <- ! bind_trigger.
        destruct ce.
        * gstep. eapply pind9_fold. eapply lsim_sync; ss. i.
          gstep. eapply pind9_fold. eapply lsim_tauL. split; ss.
          rewrite close_itree_tau.
          eapply pind9_fold. eapply lsim_tauR. split; ss.
          eapply pind9_fold. eapply lsim_tauR. split; ss.
          eapply pind9_fold. eapply lsim_progress.
          gfinal. left. eapply CIH. des. splits; ss.
          { rewrite INV2. extensionalities i. destruct i as [|[|]].
            - specialize (TGT (inr (inl (inl i)))). ss.
            - specialize (TGT (inr (inl (inr i)))). ss.
            - specialize (TGT (inr (inr i))). ss.
          }
        * gstep. eapply pind9_fold. eapply lsim_tidR. split; ss.
          eapply pind9_fold. eapply lsim_tidL. split; ss.
          eapply pind9_fold. eapply lsim_tauL. split; ss.
          rewrite close_itree_tau.
          eapply pind9_fold. eapply lsim_tauR. split; ss.
          eapply pind9_fold. eapply lsim_tauR. split; ss.
          eapply pind9_fold. eapply lsim_progress.
          gfinal. left. eapply CIH. des. splits; ss.
      + destruct cae. rewrite ! close_itree_vis_call.
        ss. unfold closed_funs. destruct (funs M2 fn).
        * rewrite close_itree_vis_cE.
          rewrite <- ! bind_trigger.
          rewrite close_itree_bind.
          gstep. eapply pind9_fold. eapply lsim_sync; ss.
          i.
          assert (INV_CIH2 : I (ths1, im_src0, im_tgt2, st_src1, st_tgt1) tt).
          { des. ss. splits; ss.
            rewrite INV2.
            extensionalities i. destruct i as [|[|]].
            - specialize (TGT (inr (inl (inl i)))). ss.
            - specialize (TGT (inr (inl (inr i)))). ss.
            - specialize (TGT (inr (inr i))). ss.
          }
          clear - CIH INV_CIH2.
          gstep. eapply pind9_fold. eapply lsim_tauR. split; ss.
          eapply pind9_fold. eapply lsim_progress. split; ss.
          muclo lsim_bindC'_spec. econs.
          { instantiate (1 := fun r_src r_tgt r_ctx shr => r_src = r_tgt /\ I shr tt).
            remember (k0 arg) as itr; clear - INV_CIH2.
            revert_until r. gcofix CIH. i.
            pose Unit_wf as VALID.
            destruct_itree itr.
            - rewrite ! close_itree_ret.
              rewrite ! embed_itree_ret.
              rewrite ! close_itree_ret.
              gstep. eapply pind9_fold. eapply lsim_ret. esplits; ss.
            - rewrite ! close_itree_tau.
              rewrite ! embed_itree_tau.
              rewrite ! close_itree_tau.
              gstep. eapply pind9_fold. eapply lsim_tauL. split; ss.
              eapply pind9_fold. eapply lsim_tauR. split; ss.
              eapply pind9_fold. eapply lsim_progress.
              gfinal. left. eapply CIH; ss.
            - destruct e as [[[e|ce]|cae]|s].
              + rewrite ! close_itree_vis_eventE.
                rewrite ! embed_itree_vis_eventE.
                rewrite ! close_itree_vis_eventE.
                rewrite <- ! bind_trigger.
                destruct e.
                * gstep. eapply pind9_fold. eapply lsim_chooseR. i. split; ss.
                  eapply pind9_fold. eapply lsim_chooseL. exists x. split; ss.
                  eapply pind9_fold. eapply lsim_tauL. split; ss.
                  rewrite embed_itree_tau.
                  rewrite close_itree_tau.
                  eapply pind9_fold. eapply lsim_tauR. split; ss.
                  eapply pind9_fold. eapply lsim_tauR. split; ss.
                  eapply pind9_fold. eapply lsim_tauL. split; ss.
                  eapply pind9_fold. eapply lsim_progress.
                  gfinal. left. eapply CIH; ss.
                * gstep. eapply pind9_fold. eapply lsim_fairR. i. split; ss.
                  eapply pind9_fold. eapply lsim_fairL. exists (conv_im im_tgt1). split.
                  { des. rewrite INV_CIH3. ii. destruct i as [|[|]].
                    unfold sum_fmap_r, sum_fmap_l in *. ss.
                    - specialize (FAIR (inr (inl (inl i)))). ss.
                    - specialize (FAIR (inr (inl (inr i)))). ss.
                    - specialize (FAIR (inr (inr i))). ss.
                  }
                  split; ss.
                  rewrite embed_itree_tau.
                  rewrite close_itree_tau.
                  eapply pind9_fold. eapply lsim_tauL. split; ss.
                  eapply pind9_fold. eapply lsim_tauL. split; ss.
                  eapply pind9_fold. eapply lsim_tauR. split; ss.
                  eapply pind9_fold. eapply lsim_tauR. split; ss.
                  eapply pind9_fold. eapply lsim_progress.
                  gfinal. left. eapply CIH; ss.
                * gstep. eapply pind9_fold. eapply lsim_observe. i.
                  rewrite embed_itree_tau.
                  rewrite close_itree_tau.
                  gstep.
                  eapply pind9_fold. eapply lsim_tauL. split; ss.
                  eapply pind9_fold. eapply lsim_tauL. split; ss.
                  eapply pind9_fold. eapply lsim_tauR. split; ss.
                  eapply pind9_fold. eapply lsim_tauR. split; ss.
                  eapply pind9_fold. eapply lsim_progress.
                  gfinal. left. eapply CIH; ss.
                * gstep. eapply pind9_fold. eapply lsim_UB.
              + rewrite ! close_itree_vis_cE.
                rewrite ! embed_itree_vis_cE.
                rewrite ! close_itree_vis_cE.
                rewrite <- ! bind_trigger.
                destruct ce.
                * gstep. eapply pind9_fold. eapply lsim_sync; ss. i.
                  rewrite embed_itree_tau.
                  rewrite close_itree_tau.
                  gstep.
                  eapply pind9_fold. eapply lsim_tauL. split; ss.
                  eapply pind9_fold. eapply lsim_tauL. split; ss.
                  eapply pind9_fold. eapply lsim_tauR. split; ss.
                  eapply pind9_fold. eapply lsim_tauR. split; ss.
                  eapply pind9_fold. eapply lsim_progress.
                  gfinal. left. des. eapply CIH; ss.
                  { rewrite INV2. extensionalities i. destruct i as [|[|]].
                    - specialize (TGT (inr (inl (inl i)))). ss.
                    - specialize (TGT (inr (inl (inr i)))). ss.
                    - specialize (TGT (inr (inr i))). ss.
                  }
                * gstep. eapply pind9_fold. eapply lsim_tidR. split; ss.
                  eapply pind9_fold. eapply lsim_tidL. split; ss.
                  rewrite embed_itree_tau.
                  rewrite close_itree_tau.
                  eapply pind9_fold. eapply lsim_tauL. split; ss.
                  eapply pind9_fold. eapply lsim_tauL. split; ss.
                  eapply pind9_fold. eapply lsim_tauR. split; ss.
                  eapply pind9_fold. eapply lsim_tauR. split; ss.
                  eapply pind9_fold. eapply lsim_progress.
                  gfinal. left. des. eapply CIH; ss.
              + destruct cae.
                rewrite ! embed_itree_vis_callE.
                rewrite ! close_itree_vis_call.
                destruct (funs M3 fn).
                * rewrite embed_itree_vis_cE.
                  rewrite <- ! bind_trigger.
                  gstep. eapply pind9_fold. eapply lsim_sync; ss. i.
                  assert (INV_CIH4 : I (ths0, im_src1, im_tgt0, st_src0, st_tgt0) tt).
                  { des. ss. splits; ss.
                    rewrite INV2.
                    extensionalities i. destruct i as [|[|]].
                    - specialize (TGT (inr (inl (inl i)))). ss.
                    - specialize (TGT (inr (inl (inr i)))). ss.
                    - specialize (TGT (inr (inr i))). ss.
                  }
                  clear - CIH INV_CIH4.
                  gstep. eapply pind9_fold. eapply lsim_tauL. split; ss.
                  eapply pind9_fold. eapply lsim_progress.
                  rewrite embed_itree_bind.
                  muclo lsim_bindC'_spec. econs.
                  { instantiate (1 := fun r_src r_tgt r_ctx shr => r_src = r_tgt /\ I shr tt).
                    remember (k0 arg) as itr; clear - INV_CIH4.
                    revert_until r0. gcofix CIH. i.
                    pose Unit_wf as VALID.
                    destruct_itree itr.
                    - rewrite ! embed_itree_ret.
                      gstep. eapply pind9_fold. eapply lsim_ret. esplits; ss.
                    - rewrite ! embed_itree_tau.
                      gstep. eapply pind9_fold. eapply lsim_tauL. split; ss.
                      eapply pind9_fold. eapply lsim_tauR. split; ss.
                      eapply pind9_fold. eapply lsim_progress.
                      gfinal. left. eapply CIH; ss.
                    - destruct e as [[[e|ce]|cae]|s].
                      + rewrite ! embed_itree_vis_eventE.
                        rewrite <- ! bind_trigger.
                        destruct e.
                        * gstep. eapply pind9_fold. eapply lsim_chooseR. i. split; ss.
                          eapply pind9_fold. eapply lsim_chooseL. exists x. split; ss.
                          rewrite embed_itree_tau.
                          eapply pind9_fold. eapply lsim_tauL. split; ss.
                          eapply pind9_fold. eapply lsim_tauL. split; ss.
                          eapply pind9_fold. eapply lsim_tauR. split; ss.
                          eapply pind9_fold. eapply lsim_progress.
                          gfinal. left. eapply CIH; ss.
                        * gstep. eapply pind9_fold. eapply lsim_fairR. i. split; ss.
                          eapply pind9_fold. eapply lsim_fairL. exists (conv_im im_tgt1). split.
                          { des. rewrite INV_CIH2. ii. destruct i as [|[|]].
                            unfold sum_fmap_r, sum_fmap_l in *. ss.
                            - specialize (FAIR (inr (inl (inl i)))). ss.
                            - specialize (FAIR (inr (inl (inr i)))). ss.
                            - specialize (FAIR (inr (inr i))). ss.
                          }
                          split; ss.
                          rewrite embed_itree_tau.
                          eapply pind9_fold. eapply lsim_tauL. split; ss.
                          eapply pind9_fold. eapply lsim_tauL. split; ss.
                          eapply pind9_fold. eapply lsim_tauR. split; ss.
                          eapply pind9_fold. eapply lsim_progress.
                          gfinal. left. eapply CIH; ss.
                        * gstep. eapply pind9_fold. eapply lsim_observe. i.
                          rewrite embed_itree_tau.
                          gstep. eapply pind9_fold. eapply lsim_tauL. split; ss.
                          eapply pind9_fold. eapply lsim_tauL. split; ss.
                          eapply pind9_fold. eapply lsim_tauR. split; ss.
                          eapply pind9_fold. eapply lsim_progress.
                          gfinal. left. eapply CIH; ss.
                        * gstep. eapply pind9_fold. eapply lsim_UB.
                      + rewrite ! embed_itree_vis_cE.
                        rewrite <- ! bind_trigger.
                        destruct ce.
                        * gstep. eapply pind9_fold. eapply lsim_sync; ss. i.
                          rewrite embed_itree_tau.
                          gstep.
                          eapply pind9_fold. eapply lsim_tauL. split; ss.
                          eapply pind9_fold. eapply lsim_tauL. split; ss.
                          eapply pind9_fold. eapply lsim_tauR. split; ss.
                          eapply pind9_fold. eapply lsim_progress.
                          gfinal. left. des. eapply CIH; ss.
                          { rewrite INV2. extensionalities i. destruct i as [|[|]].
                            - specialize (TGT (inr (inl (inl i)))). ss.
                            - specialize (TGT (inr (inl (inr i)))). ss.
                            - specialize (TGT (inr (inr i))). ss.
                          }
                        * gstep. eapply pind9_fold. eapply lsim_tidR. split; ss.
                          eapply pind9_fold. eapply lsim_tidL. split; ss.
                          rewrite embed_itree_tau.
                          eapply pind9_fold. eapply lsim_tauL. split; ss.
                          eapply pind9_fold. eapply lsim_tauL. split; ss.
                          eapply pind9_fold. eapply lsim_tauR. split; ss.
                          eapply pind9_fold. eapply lsim_progress.
                          gfinal. left. des. eapply CIH; ss.
                      + rewrite ! embed_itree_vis_callE.
                        rewrite <- ! bind_trigger.
                        destruct cae.
                        gstep. eapply pind9_fold. eapply lsim_call. i.
                        rewrite embed_itree_tau.
                        gstep.
                        eapply pind9_fold. eapply lsim_tauL. split; ss.
                        eapply pind9_fold. eapply lsim_tauL. split; ss.
                        eapply pind9_fold. eapply lsim_tauR. split; ss.
                        eapply pind9_fold. eapply lsim_progress.
                        gfinal. left. des. eapply CIH; ss.
                      + destruct s.
                        * rewrite ! embed_itree_vis_sE.
                          rewrite ! embed_state_put. grind.
                          rewrite embed_itree_vis_sE.
                          rewrite ! embed_state_get. grind.
                          rewrite <- ! bind_trigger.
                          gstep.
                          eapply pind9_fold. eapply lsim_getR. split; ss.
                          eapply pind9_fold. eapply lsim_getL. split; ss.
                          rewrite ! embed_state_ret. grind.
                          rewrite embed_itree_vis_sE.
                          rewrite ! embed_state_put. grind.
                          rewrite <- ! bind_trigger.
                          eapply pind9_fold. eapply lsim_tauL. split; ss.
                          eapply pind9_fold. eapply lsim_getL. split; ss.
                          rewrite <- ! bind_trigger. grind.
                          eapply pind9_fold. eapply lsim_putR. split; ss.
                          eapply pind9_fold. eapply lsim_putL. split; ss.
                          rewrite ! embed_state_ret. grind.
                          rewrite embed_itree_tau.
                          eapply pind9_fold. eapply lsim_tauL. split; ss.
                          eapply pind9_fold. eapply lsim_tauL. split; ss.
                          eapply pind9_fold. eapply lsim_tauR. split; ss.
                          eapply pind9_fold. eapply lsim_progress.
                          gfinal. left. des.
                          destruct st_src0 as [s0 []], st_tgt0 as [[] s2]. ss. subst.
                          eapply CIH; ss.
                        * rewrite ! embed_itree_vis_sE.
                          rewrite ! embed_state_get. grind.
                          rewrite embed_itree_vis_sE.
                          rewrite ! embed_state_get. grind.
                          rewrite <- ! bind_trigger.
                          gstep.
                          eapply pind9_fold. eapply lsim_getR. split; ss.
                          eapply pind9_fold. eapply lsim_getL. split; ss.
                          rewrite ! embed_state_ret. grind.
                          rewrite embed_itree_tau.
                          eapply pind9_fold. eapply lsim_tauL. split; ss.
                          eapply pind9_fold. eapply lsim_tauL. split; ss.
                          eapply pind9_fold. eapply lsim_tauR. split; ss.
                          eapply pind9_fold. eapply lsim_progress.
                          gfinal. left. des.
                          destruct st_src0 as [s0 []], st_tgt0 as [[] s2]. ss. subst.
                          eapply CIH; ss.
                  }
                  i. destruct shr as [[[[ths2 im_src] im_tgt] st_src] st_tgt]. destruct SAT. subst.
                  rewrite embed_itree_tau.
                  rewrite close_itree_tau.
                  gstep. eapply pind9_fold. eapply lsim_tauL. split; ss.
                  eapply pind9_fold. eapply lsim_tauR. split; ss.
                  eapply pind9_fold. eapply lsim_tauR. split; ss.
                  eapply pind9_fold. eapply lsim_progress.
                  gfinal. left. des. eapply CIH; ss.
                * rewrite embed_itree_vis_eventE.
                  rewrite <- ! bind_trigger.
                  gstep. eapply pind9_fold. eapply lsim_UB.
              + destruct s.
                * rewrite embed_itree_vis_sE, close_itree_vis_sE.
                  rewrite ! embed_state_put. grind.
                  rewrite embed_itree_vis_sE, close_itree_vis_sE.
                  rewrite ! embed_state_get. grind.
                  rewrite <- ! bind_trigger.
                  gstep.
                  eapply pind9_fold. eapply lsim_getR. split; ss.
                  eapply pind9_fold. eapply lsim_getL. split; ss.
                  rewrite ! embed_state_ret. grind.
                  rewrite embed_itree_vis_sE, close_itree_vis_sE.
                  rewrite ! embed_state_put. grind.
                  rewrite <- ! bind_trigger.
                  eapply pind9_fold. eapply lsim_tauL. split; ss.
                  eapply pind9_fold. eapply lsim_tauR. split; ss.
                  eapply pind9_fold. eapply lsim_getR. split; ss.
                  eapply pind9_fold. eapply lsim_getL. split; ss.
                  grind. rewrite <- ! bind_trigger.
                  eapply pind9_fold. eapply lsim_putR. split; ss.
                  eapply pind9_fold. eapply lsim_putL. split; ss.
                  rewrite ! embed_state_ret. grind.
                  rewrite embed_itree_tau.
                  rewrite close_itree_tau.
                  eapply pind9_fold. eapply lsim_tauL. split; ss.
                  eapply pind9_fold. eapply lsim_tauL. split; ss.
                  eapply pind9_fold. eapply lsim_tauR. split; ss.
                  eapply pind9_fold. eapply lsim_tauR. split; ss.
                  eapply pind9_fold. eapply lsim_progress.
                  gfinal. left. des.
                  destruct st_src1 as [s0 []], st_tgt1 as [[] s2]. ss. subst.
                  eapply CIH; ss.
                * rewrite embed_itree_vis_sE, close_itree_vis_sE.
                  rewrite ! embed_state_get. grind.
                  rewrite embed_itree_vis_sE, close_itree_vis_sE.
                  rewrite ! embed_state_get. grind.
                  rewrite <- ! bind_trigger.
                  gstep.
                  eapply pind9_fold. eapply lsim_getR. split; ss.
                  eapply pind9_fold. eapply lsim_getL. split; ss.
                  rewrite ! embed_state_ret. grind.
                  rewrite embed_itree_tau.
                  rewrite close_itree_tau.
                  eapply pind9_fold. eapply lsim_tauL. split; ss.
                  eapply pind9_fold. eapply lsim_tauL. split; ss.
                  eapply pind9_fold. eapply lsim_tauR. split; ss.
                  eapply pind9_fold. eapply lsim_tauR. split; ss.
                  eapply pind9_fold. eapply lsim_progress.
                  gfinal. left. des.
                  destruct st_src1 as [s0 []], st_tgt1 as [[] s2]. ss. subst.
                  eapply CIH; ss.
          }
          i. destruct shr as [[[[ths2 im_src] im_tgt] st_src] st_tgt]. destruct SAT. subst.
          rewrite close_itree_tau.
          gstep. eapply pind9_fold. eapply lsim_tauR. split; ss.
          eapply pind9_fold. eapply lsim_tauL. split; ss.
          eapply pind9_fold. eapply lsim_progress.
          gfinal. left. eapply CIH. des. splits; ss.
        * rewrite ! close_itree_vis_eventE.
          rewrite <- ! bind_trigger.
          gstep. eapply pind9_fold. eapply lsim_UB.
      + destruct s.
        * rewrite ! close_itree_vis_sE.
          rewrite ! embed_state_put. grind.
          rewrite ! close_itree_vis_sE.
          rewrite ! embed_state_get. grind.
          rewrite <- ! bind_trigger.
          gstep. eapply pind9_fold. eapply lsim_getR. split; ss.
          eapply pind9_fold. eapply lsim_getL. split; ss.
          rewrite ! embed_state_ret. grind.
          rewrite close_itree_vis_sE.
          rewrite embed_state_put. grind.
          rewrite <- ! bind_trigger.
          eapply pind9_fold. eapply lsim_tauR. split; ss.
          eapply pind9_fold. eapply lsim_getR. split; ss.
          rewrite <- ! bind_trigger.
          rewrite ! embed_state_ret. grind.
          eapply pind9_fold. eapply lsim_putR. split; ss.
          eapply pind9_fold. eapply lsim_putL. split; ss.
          eapply pind9_fold. eapply lsim_tauL. split; ss.
          rewrite close_itree_tau.
          eapply pind9_fold. eapply lsim_tauR. split; ss.
          eapply pind9_fold. eapply lsim_tauR. split; ss.
          eapply pind9_fold. eapply lsim_progress.
          gfinal. left. eapply CIH.
          des. destruct st_src2 as [s1 []], st_tgt2 as [[] s2]. splits; ss.
        * rewrite ! close_itree_vis_sE.
          rewrite ! embed_state_get. grind.
          rewrite ! close_itree_vis_sE.
          rewrite ! embed_state_get. grind.
          rewrite <- ! bind_trigger.
          gstep. eapply pind9_fold. eapply lsim_getR. split; ss.
          eapply pind9_fold. eapply lsim_getL. split; ss.
          rewrite ! embed_state_ret. grind.
          eapply pind9_fold. eapply lsim_tauL. split; ss.
          rewrite close_itree_tau.
          eapply pind9_fold. eapply lsim_tauR. split; ss.
          eapply pind9_fold. eapply lsim_tauR. split; ss.
          eapply pind9_fold. eapply lsim_progress.
          gfinal. left. destruct st_src2 as [s1 []], st_tgt2 as [[] s2]. des; ss; subst.
          eapply CIH. splits; ss.
          Unshelve. all: exact tt.
  Qed.

End MODADD_THEOREM.
