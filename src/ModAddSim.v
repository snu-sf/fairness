From sflib Require Import sflib.
From Paco Require Import paco.
From ITree Require Import ITree.
From Fairness Require Import
  ITreeLib
  WFLib
  Mod
  ModSim
  pind
  PCM.

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


Section ADD_RIGHT_CONG.

  Definition sum_wf wf1 wf2 := {| wf := sum_lt_well_founded (wf wf1) (wf wf2) |}.

  Definition pick_ctx
    {id_ctx id_tgt wf_tgt}
    (IM_TGT : @imap (ident_tgt (id_sum id_ctx id_tgt)) wf_tgt)
    : @imap id_ctx wf_tgt := fun i => IM_TGT (inr (inl i)).

  Definition chop_ctx
    {id_ctx id_tgt wf_tgt}
    (IM_TGT : @imap (ident_tgt (id_sum id_ctx id_tgt)) wf_tgt)
    : @imap (ident_tgt id_tgt) wf_tgt :=
    fun i => match i with
          | inl i => IM_TGT (inl i)
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

  Lemma ModAdd_right_cong M1 M2_src M2_tgt :
    ModSim.mod_sim M2_src M2_tgt ->
    ModSim.mod_sim (ModAdd M1 M2_src) (ModAdd M1 M2_tgt).
  Proof.
    i. inv H.
    pose (I' := fun x : @shared world
                       (ModAdd M1 M2_src).(state) (ModAdd M1 M2_tgt).(state)
                       (ModAdd M1 M2_src).(ident) (ModAdd M1 M2_tgt).(ident)
                       (sum_wf wf_src wf_tgt) wf_tgt
                => let '(ths, IM_SRC, IM_TGT, st_src, st_tgt, w) := x in
                  let im_ctx := pick_ctx IM_TGT in
                  let im_tgt := chop_ctx IM_TGT in
                  exists im_src ths_mod,
                    IM_SRC = add_ctx im_ctx im_src
                    /\ I (ths_mod, im_src, im_tgt, snd st_src, snd st_tgt, w)
         ).
    constructor 1 with (sum_wf wf_src wf_tgt) wf_tgt world I'; eauto.
    { i. specialize (init (chop_ctx im_tgt)). des.
      pose (pick_ctx im_tgt) as im_ctx. exists (add_ctx im_ctx im_src). exists r_shared. ss. eauto.
    }
    i. specialize (funs0 fn args).
    destruct M1 as [state1 ident1 st_init1 funs1].
    destruct M2_src as [state2_src ident2_src st_init2_src funs2_src].
    destruct M2_tgt as [state2_tgt ident2_tgt st_init2_tgt funs2_tgt].
    ss. unfold add_funs. ss.
    destruct (funs1 fn) eqn: E1, (funs2_src fn) eqn: E2, (funs2_tgt fn) eqn: E3; ss.
    - ii. exists r_shared0, URA.unit. splits; eauto. rewrite URA.unit_id. eauto. i.
      pfold. eapply pind9_fold. rewrite <- bind_trigger. econs.
    - ii. exists r_shared0, URA.unit. splits; eauto. rewrite URA.unit_id. eauto. i.
      unfold embed_l, embed_r. remember (k args) as itr.
      rename im_src1 into IM_SRC, im_tgt2 into IM_TGT.
      assert (INV_CIH : I' (ths, IM_SRC, IM_TGT, st_src, st_tgt, r_shared2)).
      { ss. des. exists im_src, ths_mod.
        assert (pick_ctx IM_TGT = pick_ctx im_tgt1).
        { extensionalities i. specialize (TGT (inr (inl i))). ss. }
        rewrite H. split. eauto. admit.
      }

      clear - INV0 VALID0.
      rename INV0 into INV, VALID0 into VALID, r_shared2 into r_shared0, r_ctx2 into r_ctx0.
      revert_until tid. ginit. gcofix CIH. i.
      destruct_itree itr.
      + rewrite 2 embed_state_ret. rewrite 2 map_event_ret.
        gstep. eapply pind9_fold. econs. ss. eexists. exists URA.unit, r_shared0. splits; ss.
        des. esplits; ss.
  Admitted.

End ADD_RIGHT_CONG.
