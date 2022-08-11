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

End IMAP_OPERATIONS.

Section ADD_RIGHT_CONG.

  Lemma ModAdd_right_cong M1 M2_src M2_tgt :
    ModSim.mod_sim M2_src M2_tgt ->
    ModSim.mod_sim (ModAdd M1 M2_src) (ModAdd M1 M2_tgt).
  Proof.
    Opaque lifted.
    i. inv H. rename wf_tgt_inhabited into inh.
    Check URA.prod.
    pose (I' := fun x : @shared (URA.prod threadsRA world)
                       (ModAdd M1 M2_src).(state) (ModAdd M1 M2_tgt).(state)
                       (ModAdd M1 M2_src).(ident) (ModAdd M1 M2_tgt).(ident)
                       (sum_wf wf_src wf_tgt) wf_tgt
                => let '(ths, IM_SRC, IM_TGT, st_src, st_tgt, r) := x in
                  exists im_src ths_ctx ths_mod,
                    let im_ctx := pick_ctx IM_TGT in
                    let im_tgt := chop_ctx inh ths_mod IM_TGT in
                    IM_SRC = add_ctx im_ctx im_src
                    /\ NatMapP.Partition ths ths_ctx ths_mod
                    /\ fst r = global_th ths_ctx ths_mod
                    /\ lifted I (ths_mod, im_src, im_tgt, snd st_src, snd st_tgt, snd r)
         ).
    constructor 1 with _ _ _ I'; eauto.
    { i. specialize (init (chop_ctx inh NatSet.empty im_tgt)). des.
      pose (pick_ctx im_tgt) as im_ctx. exists (add_ctx im_ctx im_src).
      exists (global_th NatSet.empty NatSet.empty, r_shared). ss. split.
      - exists im_src. exists NatSet.empty, NatSet.empty. splits; ss. admit. exists (chop_ctx inh NatSet.empty im_tgt). split; ss. ii. reflexivity.
      - rewrite URA.unfold_wf. ss. split; ss. rewrite URA.unfold_wf. ss. econs; ss. eapply Disjoint_empty.
    }
    i. specialize (funs0 fn args).
    destruct M1 as [state1 ident1 st_init1 funs1].
    destruct M2_src as [state2_src ident2_src st_init2_src funs2_src].
    destruct M2_tgt as [state2_tgt ident2_tgt st_init2_tgt funs2_tgt].
    ss. unfold add_funs. ss.
    destruct (funs1 fn) eqn: E1, (funs2_src fn) eqn: E2, (funs2_tgt fn) eqn: E3; ss.
    - ii. exists r_shared0, URA.unit. splits.
      { ss. des. exists im_src, (NatSet.add tid ths_ctx), ths_mod. splits; ss.
        inv THS. admit. admit.
      }
      { rewrite URA.unit_id. eauto. }
      i. pfold. eapply pind9_fold. rewrite <- bind_trigger. econs.
    - (* tid ∈ ths_ctx *)
      ii. simpl in INV. des. destruct r_shared0 as [r_shared_th r_shared_w], r_ctx0 as [r_ctx_th r_ctx_w].
      rewrite URA.unfold_wf, URA.unfold_add in VALID. simpl in VALID, INV1. subst. des.
      exists (global_th (TIdSet.add tid ths_ctx) ths_mod, r_shared_w), (local_th_context tid, URA.unit). splits.
      { admit. }
      { rewrite URA.unfold_wf, URA.unfold_add. ss. split.
        - eapply global_th_alloc_context.
          + eapply VALID.
          + admit.
          + admit.
        - rewrite URA.unit_id. eauto.
      }
      i. unfold embed_l, embed_r. remember (k args) as itr.
      rename im_src1 into IM_SRC, im_tgt2 into IM_TGT.
      assert (INV_CIH : I' (ths, IM_SRC, IM_TGT, st_src, st_tgt, r_shared2)).
      { ss. des. exists im_src0, ths_ctx, ths_mod0. splits; ss.
        - assert (@pick_ctx _ _ wf_tgt IM_TGT = pick_ctx im_tgt1).
          { extensionalities i. specialize (TGT (inr (inl i))). ss. }
          rewrite H. ss.
        - admit.
        - admit.
        - eapply shared_rel_wf_lifted.
          + eexact INV4.
          + ii. destruct i as [i|i]; ss.
            * specialize (TGT (inl i)). ss. destruct (tids_fmap_all ths_mod0 i) eqn:E; ss.
              -- unfold tids_fmap_all, tids_fmap in TGT, E. destruct (NatMapP.F.In_dec ths_mod0 i); ss.
                 assert (NatMap.In i ths). (* i ∈ ths_mod ⊂ ths *)
                 { eapply Partition_In_right in INV1; eauto. }
                 assert (i <> tid). (* ths_ctx ∩ ths_mod = ∅, i ∈ ths_mod, tid ∈ ths_ctx *)
                 { ii. subst. destruct INV1. eapply H0. eauto. split; [| eapply i0 ]. admit. }
                 des_ifs.
              -- unfold tids_fmap_all, tids_fmap in TGT, E. des_ifs.
            * specialize (TGT (inr (inr i))). ss.
      }
      clear - INV0 VALID0.
      rename INV0 into INV, VALID0 into VALID, r_shared2 into r_shared0, r_ctx2 into r_ctx0.
      revert_until tid. ginit. gcofix CIH. i.
      destruct_itree itr.
      + rewrite 2 embed_state_ret. rewrite 2 map_event_ret.
        gstep. eapply pind9_fold. econs. ss. eexists. admit.
      + admit.
      + admit.
    - eapply local_sim_clos_trans in funs0; ss.
      admit.
  Admitted.

End ADD_RIGHT_CONG.
