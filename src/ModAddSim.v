From sflib Require Import sflib.
From Paco Require Import paco.
From ITree Require Import ITree.
From Fairness Require Import
  ITreeLib WFLib Axioms pind PCM Mod ModSim ModSimAux AddWorld.

Import Lia.
Import Mod.
Import RelationClasses.

Section ADD_COMM.
  
  Definition conv {id1 id2 wf} (m_tgt : @imap (ident_tgt (id_sum id2 id1)) wf) :
    @imap (id_sum id1 id2) wf :=
    fun i =>
      match i with
      | inl i => m_tgt (inr (inr i))
      | inr i => m_tgt (inr (inl i))
      end.

  Program Definition Unit : URA.t := {| URA.unit := tt; URA._add := fun _ _ => tt; URA._wf := fun _ => True |}.
  Next Obligation. unseal "ra". destruct a. ss. Qed.
  Next Obligation. unseal "ra". ss. Qed.
  Next Obligation. unseal "ra". ss. Qed.
  Next Obligation. unseal "ra". destruct a. ss. Qed.
  Next Obligation. unseal "ra". ss. Qed.

  Lemma Unit_wf : forall x, @URA.wf Unit x.
  Proof. unfold URA.wf. unseal "ra". ss. Qed.
  
  Lemma ModAdd_comm M1 M2 : ModSim.mod_sim (ModAdd M1 M2) (ModAdd M2 M1).
  Proof.
    Local Opaque Unit.
    pose proof Unit_wf.
    pose (I := fun x : @shared Unit
                       (ModAdd M1 M2).(state) (ModAdd M2 M1).(state)
                       (ModAdd M1 M2).(ident) (ModAdd M2 M1).(ident)
                       nat_wf nat_wf
               => let '(ths, m_src, m_tgt, st_src, st_tgt, w) := x in
                 fst st_src = snd st_tgt
                 /\ snd st_src = fst st_tgt
                 /\ (forall i, m_src (inl i) = m_tgt (inr (inr i)))
                 /\ (forall i, m_src (inr i) = m_tgt (inr (inl i)))
         ).
    constructor 1 with nat_wf nat_wf Unit I.
    - econs. exact 0.
    - i. exists (S o0). ss.
    - i. exists (conv im_tgt). exists tt. ss.
    - i.
      destruct M1 as [state1 ident1 st_init1 funs1].
      destruct M2 as [state2 ident2 st_init2 funs2].
      ss. unfold add_funs. ss.
      destruct (funs1 fn), (funs2 fn).
      + ii. esplits; ss. i. pfold. eapply pind9_fold. rewrite <- bind_trigger. econs.
      + ii. exists tt, tt. splits; ss. i.
        unfold embed_l, embed_r. remember (k args) as itr.
        assert (INV_CIH : I (ths, im_src1, im_tgt2, st_src, st_tgt, tt)).
        { des. ss. splits; ss.
          - ii. specialize (TGT (inr (inr i))). specialize (INV2 i). ss. transitivity (im_tgt1 (inr (inr i))); eauto.
          - ii. specialize (TGT (inr (inl i))). specialize (INV3 i). ss. transitivity (im_tgt1 (inr (inl i))); eauto.
        }
          
        clear - INV_CIH VALID0.
        rename INV_CIH into INV, VALID0 into VALID, im_src1 into im_src0, im_tgt2 into im_tgt0.
        revert_until tid. ginit. gcofix CIH. i.

        destruct_itree itr.
        * rewrite 2 embed_state_ret.
          rewrite 2 map_event_ret.
          gstep. eapply pind9_fold.
          econs. inv INV. des. ss. esplits; eauto.
        * rewrite 2 embed_state_tau.
          rewrite 2 map_event_tau.
          gstep.
          eapply pind9_fold. econs. split; ss.
          eapply pind9_fold. econs. split; ss.
          eapply pind9_fold. econs.
          gfinal. left. eapply CIH; ss.
        * { destruct e as [[|] | ].
            - rewrite 2 embed_state_vis.
              rewrite 2 map_event_vis.
              rewrite <- 2 bind_trigger.
              gstep. destruct e; ss.
              + eapply pind9_fold. eapply lsim_chooseR. i. esplit; ss.
                eapply pind9_fold. eapply lsim_chooseL. exists x. esplit; ss.
                eapply pind9_fold. eapply lsim_progress.
                gfinal. left. eapply CIH; ss.
              + eapply pind9_fold. eapply lsim_fairR. i. esplit; ss.
                eapply pind9_fold. eapply lsim_fairL. exists (conv im_tgt1). esplit.
                { des. ii. destruct i; ss.
                  - specialize (FAIR (inr (inr i))). rewrite INV1. ss.
                  - specialize (FAIR (inr (inl i))). rewrite INV2. ss.
                }
                esplit; ss.
                eapply pind9_fold. eapply lsim_progress.
                gfinal. left. des. eapply CIH; ss. 
              + eapply pind9_fold. eapply lsim_observe. i.
                gfinal. left. eapply CIH; ss.
              + eapply pind9_fold. eapply lsim_UB.
            - rewrite 2 embed_state_vis.
              rewrite 2 map_event_vis. ss.
              rewrite <- 2 bind_trigger.
              gstep. destruct c.
              + eapply pind9_fold. eapply lsim_sync; eauto.
                gfinal. left. eapply CIH; ss. des; splits; ss.
                * i. specialize (TGT (inr (inr i))). ss. transitivity (im_tgt1 (inr (inr i))); eauto.
                * i. specialize (TGT (inr (inl i))). ss. transitivity (im_tgt1 (inr (inl i))); eauto.
              + eapply pind9_fold. eapply lsim_tidR. esplit; ss.
                eapply pind9_fold. eapply lsim_tidL. esplit; ss.
                eapply pind9_fold. eapply lsim_progress.
                gfinal. left. eapply CIH; ss.
            - destruct s.
              + rewrite 2 embed_state_put. ss.
                rewrite 2 map_event_vis. ss.
                rewrite <- 2 bind_trigger.
                gstep.
                eapply pind9_fold. eapply lsim_getL. esplit; ss.
                eapply pind9_fold. eapply lsim_getR. esplit; ss.
                rewrite 2 map_event_vis. ss.
                rewrite <- 2 bind_trigger.
                eapply pind9_fold. eapply lsim_putL. esplit; ss.
                eapply pind9_fold. eapply lsim_putR. esplit; ss.
                eapply pind9_fold. eapply lsim_progress.
                gfinal. left. eapply CIH; ss.
                des. destruct st_src, st_tgt. ss.
              + rewrite 2 embed_state_get. ss.
                rewrite 2 map_event_vis. ss.
                rewrite <- 2 bind_trigger.
                gstep.
                eapply pind9_fold. eapply lsim_getL. esplit; ss.
                eapply pind9_fold. eapply lsim_getR. esplit; ss.
                eapply pind9_fold. eapply lsim_progress.
                gfinal. left.
                destruct st_src, st_tgt. des. ss. subst.
                eapply CIH; ss.
          }
      + ii. exists tt, tt. splits; ss. i.
        unfold embed_l, embed_r. remember (k args) as itr.
        assert (INV_CIH : I (ths, im_src1, im_tgt2, st_src, st_tgt, tt)).
        { des. ss. splits; ss.
          - ii. specialize (TGT (inr (inr i))). specialize (INV2 i). ss. transitivity (im_tgt1 (inr (inr i))); eauto.
          - ii. specialize (TGT (inr (inl i))). specialize (INV3 i). ss. transitivity (im_tgt1 (inr (inl i))); eauto.
        }
          
        clear - INV_CIH VALID0.
        rename INV_CIH into INV, VALID0 into VALID, im_src1 into im_src0, im_tgt2 into im_tgt0.
        revert_until tid. ginit. gcofix CIH. i.

        destruct_itree itr.
        * rewrite 2 embed_state_ret.
          rewrite 2 map_event_ret.
          gstep. eapply pind9_fold.
          econs. inv INV. des. ss. esplits; eauto.
        * rewrite 2 embed_state_tau.
          rewrite 2 map_event_tau.
          gstep.
          eapply pind9_fold. econs. split; ss.
          eapply pind9_fold. econs. split; ss.
          eapply pind9_fold. econs.
          gfinal. left. eapply CIH; ss.
        * { destruct e as [[|] | ].
            - rewrite 2 embed_state_vis.
              rewrite 2 map_event_vis.
              rewrite <- 2 bind_trigger.
              gstep. destruct e; ss.
              + eapply pind9_fold. eapply lsim_chooseR. i. esplit; ss.
                eapply pind9_fold. eapply lsim_chooseL. exists x. esplit; ss.
                eapply pind9_fold. eapply lsim_progress.
                gfinal. left. eapply CIH; ss.
              + eapply pind9_fold. eapply lsim_fairR. i. esplit; ss.
                eapply pind9_fold. eapply lsim_fairL. exists (conv im_tgt1). esplit.
                { des. ii. destruct i; ss.
                  - specialize (FAIR (inr (inr i))). rewrite INV1. ss.
                  - specialize (FAIR (inr (inl i))). rewrite INV2. ss.
                }
                esplit; ss.
                eapply pind9_fold. eapply lsim_progress.
                gfinal. left. des. eapply CIH; ss. 
              + eapply pind9_fold. eapply lsim_observe. i.
                gfinal. left. eapply CIH; ss.
              + eapply pind9_fold. eapply lsim_UB.
            - rewrite 2 embed_state_vis.
              rewrite 2 map_event_vis. ss.
              rewrite <- 2 bind_trigger.
              gstep. destruct c.
              + eapply pind9_fold. eapply lsim_sync; eauto.
                gfinal. left. eapply CIH; ss. des; splits; ss.
                * i. specialize (TGT (inr (inr i))). ss. transitivity (im_tgt1 (inr (inr i))); eauto.
                * i. specialize (TGT (inr (inl i))). ss. transitivity (im_tgt1 (inr (inl i))); eauto.
              + eapply pind9_fold. eapply lsim_tidR. esplit; ss.
                eapply pind9_fold. eapply lsim_tidL. esplit; ss.
                eapply pind9_fold. eapply lsim_progress.
                gfinal. left. eapply CIH; ss.
            - destruct s.
              + rewrite 2 embed_state_put. ss.
                rewrite 2 map_event_vis. ss.
                rewrite <- 2 bind_trigger.
                gstep.
                eapply pind9_fold. eapply lsim_getL. esplit; ss.
                eapply pind9_fold. eapply lsim_getR. esplit; ss.
                rewrite 2 map_event_vis. ss.
                rewrite <- 2 bind_trigger.
                eapply pind9_fold. eapply lsim_putL. esplit; ss.
                eapply pind9_fold. eapply lsim_putR. esplit; ss.
                eapply pind9_fold. eapply lsim_progress.
                gfinal. left. eapply CIH; ss.
                des. destruct st_src, st_tgt. ss.
              + rewrite 2 embed_state_get. ss.
                rewrite 2 map_event_vis. ss.
                rewrite <- 2 bind_trigger.
                gstep.
                eapply pind9_fold. eapply lsim_getL. esplit; ss.
                eapply pind9_fold. eapply lsim_getR. esplit; ss.
                eapply pind9_fold. eapply lsim_progress.
                gfinal. left.
                destruct st_src, st_tgt. des. ss. subst.
                eapply CIH; ss.
          }
      + ss.
        Unshelve. all: exact tt.
  Qed.

End ADD_COMM.

Section IMAP_OPERATIONS.

  Context {id_ctx id_src id_tgt : ID}.
  Context {wf_src wf_tgt : WF}.
  Context (wf_tgt_inhabited : inhabited wf_tgt.(T)).

  Let zero: wf_tgt.(T) := epsilon wf_tgt_inhabited (fun _ => True).

  Definition sum_wf wf1 wf2 := {| wf := sum_lt_well_founded (wf wf1) (wf wf2) |}.

  Definition pick_ctx
    (IM_TGT : @imap (ident_tgt (id_sum id_ctx id_tgt)) wf_tgt)
    : @imap id_ctx wf_tgt := fun i => IM_TGT (inr (inl i)).

  Definition chop_ctx
    (ths : TIdSet.t)
    (IM_TGT : @imap (ident_tgt (id_sum id_ctx id_tgt)) wf_tgt)
    : @imap (ident_tgt id_tgt) wf_tgt :=
    fun i => match i with
          | inl i => if NatMapP.F.In_dec ths i then IM_TGT (inl i) else zero
          | inr i => IM_TGT (inr (inr i))
          end.

  Definition add_ctx
    {id_ctx id_src wf_src wf_tgt}
    (im_ctx : imap id_ctx wf_tgt)
    (im_src : imap id_src wf_src)
    : forall i, (sum_wf wf_src wf_tgt).(T)
    := fun i => match i with
             | inl i => inr (im_ctx i)
             | inr i => inl (im_src i)
             end.

  Lemma pick_ctx_fair_thread IM_TGT0 IM_TGT1 m
    (FAIR : fair_update IM_TGT0 IM_TGT1 (sum_fmap_l m))
    : pick_ctx IM_TGT0 = pick_ctx IM_TGT1.
  Proof.
    extensionalities i. specialize (FAIR (inr (inl i))). ss.
  Qed.

  Lemma chop_ctx_fair_ctx ths_usr IM_TGT0 IM_TGT1 m
    (FAIR : fair_update IM_TGT0 IM_TGT1 (sum_fmap_r (sum_fmap_l m)))
    : chop_ctx ths_usr IM_TGT0 = chop_ctx ths_usr IM_TGT1.
  Proof.
    extensionalities i. destruct i as [i|i]; ss.
    - specialize (FAIR (inl i)). ss. des_ifs.
    - specialize (FAIR (inr (inr i))). ss.
  Qed.

  Lemma chop_ctx_fair_thread1 ths ths_ctx ths_usr tid IM_TGT0 IM_TGT1
    (PARTITION : NatMapP.Partition ths ths_ctx ths_usr)
    (TID_CTX : NatMap.In tid ths_ctx)
    (FAIR : fair_update IM_TGT0 IM_TGT1 (sum_fmap_l (tids_fmap tid ths)))
    : fair_update (chop_ctx ths_usr IM_TGT0) (chop_ctx ths_usr IM_TGT1) (sum_fmap_l (tids_fmap_all ths_usr)).
  Proof.
    ii. destruct i as [i|i]; ss.
    - specialize (FAIR (inl i)). ss. destruct (tids_fmap_all ths_usr i) eqn:E; ss.
      + unfold tids_fmap_all, tids_fmap in FAIR, E. destruct (NatMapP.F.In_dec ths_usr i); ss.
        assert (NatMap.In i ths). (* i ∈ ths_usr ⊂ ths *)
        { eapply Partition_In_right in PARTITION; eauto. }
        assert (i <> tid). (* ths_ctx ∩ ths_usr = ∅, i ∈ ths_usr, tid ∈ ths_ctx *)
        { ii. subst. destruct PARTITION. eapply H0. eauto. }
        des_ifs.
      + unfold tids_fmap_all, tids_fmap in FAIR, E. des_ifs.
    - specialize (FAIR (inr (inr i))). ss.
  Qed.

  Lemma chop_ctx_fair_thread2 ths ths_usr tid IM_TGT0 IM_TGT1
    (LE : KeySetLE ths_usr ths)
    (FAIR : fair_update IM_TGT0 IM_TGT1 (sum_fmap_l (tids_fmap tid ths)))
    : fair_update (chop_ctx ths_usr IM_TGT0) (chop_ctx ths_usr IM_TGT1) (sum_fmap_l (tids_fmap tid ths_usr)).
  Proof.
    ii. destruct i as [i|i]; ss.
    - specialize (FAIR (inl i)); ss. destruct (NatMapP.F.In_dec ths_usr i).
      + pose proof (LE _ i0). unfold tids_fmap in *. des_ifs.
      + unfold tids_fmap in *. des_ifs.
    - specialize (FAIR (inr (inr i))); ss.
  Qed.

End IMAP_OPERATIONS.

Section URA_PROD.

  Lemma unfold_prod_add (M0 M1 : URA.t) : @URA.add (URA.prod M0 M1) = fun '(a0, a1) '(b0, b1) => (a0 ⋅ b0, a1 ⋅ b1).
  Proof. rewrite URA.unfold_add. extensionalities r0 r1. destruct r0, r1. ss. Qed.

  Lemma unfold_prod_wf (M0 M1 : URA.t) : @URA.wf (URA.prod M0 M1) = fun r => URA.wf (fst r) /\ URA.wf (snd r).
  Proof. rewrite URA.unfold_wf. extensionalities r. destruct r. ss. Qed.

End URA_PROD.

Tactic Notation "unfold_prod" :=
  try rewrite ! unfold_prod_add;
  rewrite unfold_prod_wf;
  simpl.

Tactic Notation "unfold_prod" hyp(H) :=
  try rewrite ! unfold_prod_add in H;
  rewrite unfold_prod_wf in H;
  simpl in H;
  let H1 := fresh H in
  destruct H as [H H1].

Section ADD_RIGHT_CONG_SIM.

  Context {M1 M2_src M2_tgt : Mod.t}.
  Context {wf_src wf_tgt : WF}.
  Context `{world : URA.t}.
  Context (inh : inhabited wf_tgt.(T)).

  Variable I : shared (state M2_src) (state M2_tgt) (ident M2_src) (ident M2_tgt) wf_src wf_tgt -> Prop.

  Definition lift_ma :=
    fun x : @shared (URA.prod threadsRA world)
            (ModAdd M1 M2_src).(state) (ModAdd M1 M2_tgt).(state)
            (ModAdd M1 M2_src).(ident) (ModAdd M1 M2_tgt).(ident)
            (sum_wf wf_src wf_tgt) wf_tgt
    => let '(ths, IM_SRC, IM_TGT, st_src, st_tgt, r) := x in
      exists im_src0 ths_ctx0 ths_usr0,
        let im_ctx0 := pick_ctx IM_TGT in
        let im_tgt0 := chop_ctx inh ths_usr0 IM_TGT in
        IM_SRC = add_ctx im_ctx0 im_src0
        /\ NatMapP.Partition ths ths_ctx0 ths_usr0
        /\ fst r = global_th ths_ctx0 ths_usr0
        /\ fst st_src = fst st_tgt
        /\ lifted I (ths_usr0, im_src0, im_tgt0, snd st_src, snd st_tgt, snd r).

  Opaque lifted threadsRA URA.prod.

  Lemma lift_ma_local_sim_ub R_src R_tgt (RR : R_src -> R_tgt -> Prop) ktr_src itr_tgt
    : local_sim lift_ma RR (Vis (inl1 (inl1 Undefined)) ktr_src) itr_tgt.
  Proof.
    (* treat as if tid ∈ ths_ctx *)
    intros ths IM_SRC0 IM_TGT0 st_src0 st_tgt0 [r_sha_th0 r_sha_w0] [r_ctx_th0 r_ctx_w0] INV0_0 tid ths0 THS0 VALID0_0.
    simpl in INV0_0. des. subst r_sha_th0. unfold_prod VALID0_0.
    exists (global_th (TIdSet.add tid ths_ctx0) ths_usr0, r_sha_w0). exists (local_th_context tid, URA.unit). splits.
    { exists im_src0, (TIdSet.add tid ths_ctx0), ths_usr0. splits; ss.
      eauto using NatMapP.Partition_sym, Partition_add.
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

  Lemma lift_ma_local_sim_ctx R (itr : itree _ R)
    : local_sim lift_ma eq (embed_l M1 M2_src itr) (embed_l M1 M2_tgt itr).
  Proof.
    (* tid ∈ ths_ctx *)
    intros ths IM_SRC0 IM_TGT0 st_src0 st_tgt0 [r_sha_th0 r_sha_w0] [r_ctx_th0 r_ctx_w0] INV0_0 tid ths0 THS0 VALID0_0.
    simpl in INV0_0. des. subst r_sha_th0. unfold_prod VALID0_0.
    exists (global_th (TIdSet.add tid ths_ctx0) ths_usr0, r_sha_w0), (local_th_context tid, URA.unit). splits.
    { exists im_src0, (TIdSet.add tid ths_ctx0), ths_usr0. splits; ss.
      eauto using NatMapP.Partition_sym, Partition_add.
    }
    { unfold_prod. split.
      - eapply inv_add_new in THS0. des; subst. eapply global_th_alloc_context.
        + eauto.
        + eapply inv_add_new. split; ss.
          ii. eapply THS0. eapply (Partition_In_left INV0_1). ss.
        + ii. eapply THS0. eapply (Partition_In_right INV0_1). ss.
      - rewrite URA.unit_id. eauto.
    }
    intros ths1 IM_SRC1 IM_TGT1 st_src1 st_tgt1 [r_sha_th1 r_sha_w1] [r_ctx_th1 r_ctx_w1] INV1_0 VALID1_0.
    intros IM_TGT1' TGT fs ft.
    simpl in INV1_0. des. subst r_sha_th1. unfold_prod VALID1_0.
    unfold embed_l, embed_r.
    assert (INV : lift_ma (ths1, IM_SRC1, IM_TGT1', st_src1, st_tgt1, (global_th ths_ctx1 ths_usr1, r_sha_w1))).
    { ss. exists im_src1, ths_ctx1, ths_usr1. splits; ss.
      - eapply pick_ctx_fair_thread in TGT. rewrite <- TGT. ss.
      - eapply shared_rel_wf_lifted; eauto.
        eapply chop_ctx_fair_thread1; eauto.
        eapply local_th_context_in_context; eauto.
    }
    clear - INV VALID1_0 VALID1_1. move itr after tid.
    rename
      ths1 into ths0, ths_ctx1 into ths_ctx0, ths_usr1 into ths_usr0,
      IM_SRC1 into IM_SRC0, IM_TGT1' into IM_TGT0, st_src1 into st_src0, st_tgt1 into st_tgt0,
      r_sha_w1 into r_sha_w0, r_ctx_th1 into r_ctx_th0, r_ctx_w1 into r_ctx_w0,
      INV into INV0, VALID1_0 into VALID_TH0, VALID1_1 into VALID_W0.
    revert_until tid. ginit. gcofix CIH. i.
    destruct_itree itr; [| | destruct e as [[|]|] ].
    - rewrite 2 embed_state_ret, 2 map_event_ret.
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
    - rewrite 2 embed_state_tau, 2 map_event_tau.
      gstep.
      eapply pind9_fold. econs. split; ss.
      eapply pind9_fold. econs. split; ss.
      eapply pind9_fold. econs.
      gfinal. left. eapply CIH; ss.
    - rewrite 2 embed_state_vis.
      rewrite 2 map_event_vis.
      rewrite <- 2 bind_trigger.
      gstep. destruct e; ss.
      + eapply pind9_fold. eapply lsim_chooseR. i. esplit; ss.
        eapply pind9_fold. eapply lsim_chooseL. exists x. esplit; ss.
        eapply pind9_fold. eapply lsim_progress.
        gfinal. left. eapply CIH; ss.
      + eapply pind9_fold. eapply lsim_fairR. intros IM_TGT1 FAIR. esplit; ss.
        eapply pind9_fold. eapply lsim_fairL.
        des. inversion INV2. subst ths_ctx1 ths_usr1. exists (add_ctx (pick_ctx IM_TGT1) im_src0). split.
        { subst. ii. destruct i; ss.
          specialize (FAIR (inr (inl i))). unfold pick_ctx. ss. des_ifs.
          + econs. ss.
          + f_equal. ss.
        }
        split; ss.
        eapply pind9_fold. eapply lsim_progress.
        gfinal. left. des. eapply CIH; ss.
        { esplits; eauto. eapply chop_ctx_fair_ctx in FAIR. rewrite <- FAIR. ss. }
      + eapply pind9_fold. eapply lsim_observe. i.
        gfinal. left. eapply CIH; ss.
      + eapply pind9_fold. eapply lsim_UB.
    - rewrite 2 embed_state_vis.
      rewrite 2 map_event_vis. simpl.
      rewrite <- 2 bind_trigger.
      gstep. destruct c.
      + eapply pind9_fold. eapply lsim_sync.
        { eapply INV0. }
        { instantiate (1 := (local_th_context tid, ε)). unfold_prod. split; ss. }
        intros ths1 IM_SRC1 IM_TGT1 st_src1 st_tgt1 [r_sha_th1 r_sha_w1] [r_ctx_th1 r_ctx_w1] INV1_0 VALID1_0 IM_TGT1' TGT.
        simpl in INV1_0. des. subst r_sha_th1. rename im_src0 into im_src1. unfold_prod VALID1_0.
        gfinal. left. eapply CIH; ss.
        { exists im_src1, ths_ctx1, ths_usr1. splits; ss.
          - eapply pick_ctx_fair_thread in TGT. rewrite <- TGT. ss.
          - eapply shared_rel_wf_lifted; eauto.
            eapply chop_ctx_fair_thread1; eauto.
            eapply local_th_context_in_context; eauto.
        }
      + eapply pind9_fold. eapply lsim_tidR. esplit; ss.
        eapply pind9_fold. eapply lsim_tidL. esplit; ss.
        eapply pind9_fold. eapply lsim_progress.
        gfinal. left. eapply CIH; ss.
    - destruct s.
      + rewrite 2 embed_state_put. ss.
        rewrite 2 map_event_vis. ss.
        rewrite <- 2 bind_trigger.
        gstep.
        eapply pind9_fold. eapply lsim_getL. esplit; ss.
        eapply pind9_fold. eapply lsim_getR. esplit; ss.
        rewrite 2 map_event_vis. ss.
        rewrite <- 2 bind_trigger.
        eapply pind9_fold. eapply lsim_putL. esplit; ss.
        eapply pind9_fold. eapply lsim_putR. esplit; ss.
        eapply pind9_fold. eapply lsim_progress.
        gfinal. left. eapply CIH; ss.
        destruct st_src0, st_tgt0; ss. des; esplits; eauto.
      + rewrite 2 embed_state_get. ss.
        rewrite 2 map_event_vis. ss.
        rewrite <- 2 bind_trigger.
        gstep.
        eapply pind9_fold. eapply lsim_getL. esplit; ss.
        eapply pind9_fold. eapply lsim_getR. esplit; ss.
        eapply pind9_fold. eapply lsim_progress.
        des. rewrite INV3.
        gfinal. left. eapply CIH; ss. esplits; eauto.
  Qed.

  Lemma lift_ma_local_sim_usr R_src R_tgt (RR : R_src -> R_tgt -> Prop) itr_src itr_tgt
    (SIM : local_sim I RR itr_src itr_tgt)
    : local_sim lift_ma RR (embed_r M1 M2_src itr_src) (embed_r M1 M2_tgt itr_tgt).
  Proof.
    (* tid ∈ ths_usr *)
    eapply local_sim_clos_trans in SIM; ss.
    intros ths IM_SRC0 IM_TGT0 st_src0 st_tgt0 [r_sha_th0 r_sha_w0] [r_ctx_th0 r_ctx_w0] INV0_0 tid ths0 THS0 VALID0_0.
    simpl in INV0_0. des. subst r_sha_th0. unfold_prod VALID0_0.
    move SIM at bottom.
    assert (THS0' : TIdSet.add_new tid ths_usr0 (TIdSet.add tid ths_usr0)).
    { eapply inv_add_new. split; ss. eapply inv_add_new in THS0. des.
      eapply Partition_In_right in INV0_1. eauto.
    }
    specialize (SIM ths_usr0 im_src0 (chop_ctx inh ths_usr0 IM_TGT0) (snd st_src0) (snd st_tgt0) r_sha_w0 r_ctx_w0 INV0_4 tid (NatSet.add tid ths_usr0) THS0' VALID0_1).
    destruct SIM as [r_sha_w1 [r_own_w1 [INV_USR [VALID_USR SIM]]]].
    exists (global_th (NatSet.add tid ths_ctx0) ths_usr0, r_sha_w1), (local_th_user tid, r_own_w1). splits.
    { admit. }
    { admit. }
    intros ths2 IM_SRC2 IM_TGT2 st_src2 st_tgt2 [r_sha_th2 r_sha_w2] [r_ctx_th2 r_ctx_w2] INV2_0 VALID2_0 IM_TGT2' TGT fs ft.
    simpl in INV2_0. destruct INV2_0 as [im_src2 [ths_ctx2 [ths_usr2 INV2_0]]]. des. subst r_sha_th2. unfold_prod VALID2_0.
    assert (TGT' : @fair_update _ (wf_clos_trans wf_tgt) (chop_ctx inh ths_usr2 IM_TGT2) (chop_ctx inh ths_usr2 IM_TGT2') (sum_fmap_l (tids_fmap tid ths_usr2))).
    { eapply fair_mono with (wft_lt' := lt wf_tgt) (wft_wf' := wf wf_tgt).
      { econs. ss. }
      destruct wf_tgt. eapply chop_ctx_fair_thread2.
      - eapply Partition_In_right in INV2_1. eapply INV2_1.
      - eauto.
    }
    specialize (SIM ths_usr2 im_src2 (chop_ctx inh ths_usr2 IM_TGT2) (snd st_src2) (snd st_tgt2) r_sha_w2 r_ctx_w2 INV2_4 VALID2_1 (chop_ctx inh ths_usr2 IM_TGT2') TGT' fs ft).
    unfold embed_l, embed_r.
    assert (INV : lift_ma (ths2, IM_SRC2, IM_TGT2', st_src2, st_tgt2, (global_th ths_ctx2 ths_usr2, r_sha_w2))).
    { admit. }
    clear - INV VALID2_0 VALID2_1 SIM. move tid before I.
    rename
      ths2 into ths0, ths_ctx2 into ths_ctx0, ths_usr2 into ths_usr0,
      im_src2 into im_src0, IM_SRC2 into IM_SRC0, IM_TGT2' into IM_TGT0, st_src2 into st_src0, st_tgt2 into st_tgt0,
      r_sha_w2 into r_sha_w0, r_ctx_th2 into r_ctx_th0, r_ctx_w2 into r_ctx_w0, r_own_w1 into r_own_w0,
      INV into INV0, VALID2_0 into VALID_TH0, VALID2_1 into VALID_W0.
    revert_until tid. ginit. gcofix CIH. i. gstep. punfold SIM.
    match type of SIM with pind9 _ _ _ _ ?RR _ _ _ _ _ ?SHA => remember RR as RR_MEM; remember SHA as SHA_MEM end.
    revert RR ths0 ths_ctx0 ths_usr0 st_src0 st_tgt0 r_sha_w0 r_own_w0 r_ctx_th0 im_src0 IM_SRC0 IM_TGT0 INV0 VALID_TH0 VALID_W0 HeqRR_MEM HeqSHA_MEM.
    pattern R_src, R_tgt, RR_MEM, fs, ft, r_ctx_w0, itr_src, itr_tgt, SHA_MEM.
    revert R_src R_tgt RR_MEM fs ft r_ctx_w0 itr_src itr_tgt SHA_MEM SIM.
    eapply pind9_acc. intros rr DEC IH R_src R_tgt RR_MEM fs ft r_ctx_w0 itr_src itr_tgt SHA_MEM. i.
    clear DEC. subst RR_MEM SHA_MEM.
    eapply pind9_unfold in PR; eauto with paco. eapply pind9_fold. inv PR.
    - rewrite 2 embed_state_ret, 2 map_event_ret. econs.
      ss. des. inversion INV2. clear INV2. subst ths_ctx1 ths_usr1 ths3 IM_SRC0.
      exists (NatMap.remove tid ths0), (URA.unit, r_own), (global_th ths_ctx0 (NatMap.remove tid ths_usr0), r_shared2).
      splits; ss.
      + unfold_prod. split.
        * eapply global_th_dealloc_user; eauto.
        * ss.
      + esplits; ss.
        * eapply local_th_user_in_user in VALID_TH0.
          eapply Partition_remove; eauto.
        * admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
  Admitted.

End ADD_RIGHT_CONG_SIM.

Section ADD_RIGHT_CONG.

  Opaque lifted threadsRA URA.prod.

  Lemma ModAdd_right_cong M1 M2_src M2_tgt :
    ModSim.mod_sim M2_src M2_tgt ->
    ModSim.mod_sim (ModAdd M1 M2_src) (ModAdd M1 M2_tgt).
  Proof.
    i. inv H. rename wf_tgt_inhabited into inh.
    pose (I' := @lift_ma M1 M2_src M2_tgt _ _ _ inh I).
    constructor 1 with _ _ _ I'; eauto.
    { clear - init.
      intro IM_TGT. specialize (init (chop_ctx inh NatSet.empty IM_TGT)).
      destruct init as [im_src [r_shared [init R_SHARED]]].
      pose (pick_ctx IM_TGT) as im_ctx.
      exists (add_ctx im_ctx im_src), (global_th NatSet.empty NatSet.empty, r_shared). ss. split.
      - exists im_src. exists NatSet.empty, NatSet.empty. splits; ss.
        + eapply Partition_empty.
        + exists (chop_ctx inh NatSet.empty IM_TGT). split; ss. ii. left. ss.
      - unfold_prod. split; ss. rewrite URA.unfold_wf. econs; ss. eapply Disjoint_empty.
    }
    i. specialize (funs0 fn args).
    unfold ModAdd, add_funs; ss. des_ifs.
    - eapply lift_ma_local_sim_ub.
    - eapply lift_ma_local_sim_ctx.
    - eapply lift_ma_local_sim_usr; eauto.
  Qed.

End ADD_RIGHT_CONG.
