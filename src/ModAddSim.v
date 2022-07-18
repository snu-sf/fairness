From sflib Require Import sflib.
From Paco Require Import paco.
From ITree Require Import ITree.
From Fairness Require Import
  ITreeLib
  Mod
  ModSim.

Import Lia.
Import Mod.
Import RelationClasses.

Section ADD_MODSIM.

  Definition m_conv {id1 id2 wf} (m_tgt : @imap (ident_tgt (id_sum id2 id1)) wf) :
    @imap (ident_src (id_sum id1 id2)) wf :=
    fun i =>
      match i with
      | inl i => m_tgt (inl i)
      | inr (inl i) => m_tgt (inr (inr i))
      | inr (inr i) => m_tgt (inr (inl i))
      end.

  Definition m_eq
    {id1 id2 wf}
    (m_src : @imap (ident_src (id_sum id1 id2)) wf)
    (m_tgt : @imap (ident_tgt (id_sum id2 id1)) wf) : Prop :=
    (forall i, m_src (inl i) = m_tgt (inl i))
    /\ (forall i, m_src (inr (inl i)) = m_tgt (inr (inr i)))
    /\ (forall i, m_src (inr (inr i)) = m_tgt (inr (inl i))).

  Lemma ModAdd_comm M1 M2 : ModSim.mod_sim (ModAdd M1 M2) (ModAdd M2 M1).
  Proof.
    pose (world_le := fun (_ _ : unit) => True).
    pose (I := fun x : @shared
                       (ModAdd M1 M2).(state) (ModAdd M2 M1).(state)
                       (ModAdd M1 M2).(ident) (ModAdd M2 M1).(ident)
                       nat_wf nat_wf unit
               => let '(ths, m_src, m_tgt, st_src, st_tgt, w) := x in
                 fst st_src = snd st_tgt
                 /\ snd st_src = fst st_tgt
                 /\ m_eq m_src m_tgt
         ).
    constructor 1 with nat_wf nat_wf S unit world_le I.
    - unfold Transitive. ss. lia.
    - ss. lia.
    - i. exists (m_conv im_tgt). exists tt. ss.
    - i.
      destruct M1 as [state1 ident1 st_init1 funs1].
      destruct M2 as [state2 ident2 st_init2 funs2].
      ss. unfold add_funs. ss.
      destruct (funs1 fn), (funs2 fn).
      + ii. pfold. eapply pind5.pind5_fold. rewrite <- bind_trigger. eapply lsim_UB.
      + ii. unfold embed_l, embed_r.
        remember (k args) as itr; clear fn k args Heqitr THS.
        revert fs ft itr ths0 im_src0 im_tgt0 st_src0 st_tgt0 w0 tid INV.
        ginit. gcofix CIH. i.

        destruct_itree itr.
        * rewrite 2 embed_state_ret.
          rewrite 2 map_event_ret.
          gstep.
          eapply pind5.pind5_fold.
          econs. inv INV. des. ss. esplits; ss.
        * rewrite 2 embed_state_tau.
          rewrite 2 map_event_tau.
          gstep.
          eapply pind5.pind5_fold. eapply lsim_tauL. esplit; ss.
          eapply pind5.pind5_fold. eapply lsim_tauR. esplit; ss.
          eapply pind5.pind5_fold. eapply lsim_progress.
          gfinal. left. eapply CIH; ss.
        * { destruct e as [[|] | ].
            - rewrite 2 embed_state_vis.
              rewrite 2 map_event_vis.
              rewrite <- 2 bind_trigger.
              gstep. destruct e; ss.
              + eapply pind5.pind5_fold. eapply lsim_chooseR. i. esplit; ss.
                eapply pind5.pind5_fold. eapply lsim_chooseL. exists x. esplit; ss.
                eapply pind5.pind5_fold. eapply lsim_progress.
                gfinal. left. eapply CIH; ss.
              + eapply pind5.pind5_fold. eapply lsim_fairR. i. esplit; ss.
                eapply pind5.pind5_fold. eapply lsim_fairL. exists (m_conv im_tgt1). esplit.
                { unfold m_eq in INV; des. ii.
                  destruct i as [|[]]; ss.
                  - specialize (FAIR (inl i)). rewrite INV1. ss.
                  - specialize (FAIR (inr (inr i))). rewrite INV2. ss.
                  - specialize (FAIR (inr (inl i))). rewrite INV3. ss.
                }
                esplit; ss.
                eapply pind5.pind5_fold. eapply lsim_progress.
                gfinal. left. des. eapply CIH; ss. 
              + eapply pind5.pind5_fold. eapply lsim_observe. i.
                gfinal. left. eapply CIH; ss.
              + eapply pind5.pind5_fold. eapply lsim_UB.
            - rewrite 2 embed_state_vis.
              rewrite 2 map_event_vis. ss.
              rewrite <- 2 bind_trigger.
              gstep. destruct c.
              + eapply pind5.pind5_fold. eapply lsim_sync; ss. i. esplit; ss.
                eapply pind5.pind5_fold. eapply lsim_yieldL. exists (m_conv im_tgt2). esplit.
                { unfold m_eq in INV0; des. ii.
                  destruct i as [|[]]; ss.
                  - specialize (TGT (inl i)). rewrite INV2. ss.
                  - specialize (TGT (inr (inr i))). rewrite INV3. ss.
                  - specialize (TGT (inr (inl i))). rewrite INV4. ss.
                }
                esplit; ss.
                eapply pind5.pind5_fold. eapply lsim_progress.
                gfinal. left. des. eapply CIH; ss.
              + eapply pind5.pind5_fold. eapply lsim_tidR. esplit; ss.
                eapply pind5.pind5_fold. eapply lsim_tidL. esplit; ss.
                eapply pind5.pind5_fold. eapply lsim_progress.
                gfinal. left. eapply CIH; ss.
            - destruct s.
              + rewrite 2 embed_state_put. ss.
                rewrite 2 map_event_vis. ss.
                rewrite <- 2 bind_trigger.
                gstep.
                eapply pind5.pind5_fold. eapply lsim_getL. esplit; ss.
                eapply pind5.pind5_fold. eapply lsim_getR. esplit; ss.
                rewrite 2 map_event_vis. ss.
                rewrite <- 2 bind_trigger.
                eapply pind5.pind5_fold. eapply lsim_putL. esplit; ss.
                eapply pind5.pind5_fold. eapply lsim_putR. esplit; ss.
                eapply pind5.pind5_fold. eapply lsim_progress.
                gfinal. left. eapply CIH; ss.
                inv INV. destruct st_src0, st_tgt0. ss.
              + rewrite 2 embed_state_get. ss.
                rewrite 2 map_event_vis. ss.
                rewrite <- 2 bind_trigger.
                gstep.
                eapply pind5.pind5_fold. eapply lsim_getL. esplit; ss.
                eapply pind5.pind5_fold. eapply lsim_getR. esplit; ss.
                eapply pind5.pind5_fold. eapply lsim_progress.
                gfinal. left.
                destruct st_src0, st_tgt0. des. ss. subst.
                eapply CIH; ss.
          }
      + ii. unfold embed_l, embed_r.
        remember (k args) as itr; clear fn k args Heqitr THS.
        revert fs ft itr ths0 im_src0 im_tgt0 st_src0 st_tgt0 w0 tid INV.
        ginit. gcofix CIH. i.

        destruct_itree itr.
        * rewrite 2 embed_state_ret.
          rewrite 2 map_event_ret.
          gstep.
          eapply pind5.pind5_fold.
          econs. inv INV. des. ss. esplits; ss.
        * rewrite 2 embed_state_tau.
          rewrite 2 map_event_tau.
          gstep.
          eapply pind5.pind5_fold. eapply lsim_tauL. esplit; ss.
          eapply pind5.pind5_fold. eapply lsim_tauR. esplit; ss.
          eapply pind5.pind5_fold. eapply lsim_progress.
          gfinal. left. eapply CIH; ss.
        * { destruct e as [[|] | ].
            - rewrite 2 embed_state_vis.
              rewrite 2 map_event_vis.
              rewrite <- 2 bind_trigger.
              gstep. destruct e; ss.
              + eapply pind5.pind5_fold. eapply lsim_chooseR. i. esplit; ss.
                eapply pind5.pind5_fold. eapply lsim_chooseL. exists x. esplit; ss.
                eapply pind5.pind5_fold. eapply lsim_progress.
                gfinal. left. eapply CIH; ss.
              + eapply pind5.pind5_fold. eapply lsim_fairR. i. esplit; ss.
                eapply pind5.pind5_fold. eapply lsim_fairL. exists (m_conv im_tgt1). esplit.
                { unfold m_eq in INV; des. ii.
                  destruct i as [|[]]; ss.
                  - specialize (FAIR (inl i)). rewrite INV1. ss.
                  - specialize (FAIR (inr (inr i))). rewrite INV2. ss.
                  - specialize (FAIR (inr (inl i))). rewrite INV3. ss.
                }
                esplit; ss.
                eapply pind5.pind5_fold. eapply lsim_progress.
                gfinal. left. des. eapply CIH; ss. 
              + eapply pind5.pind5_fold. eapply lsim_observe. i.
                gfinal. left. eapply CIH; ss.
              + eapply pind5.pind5_fold. eapply lsim_UB.
            - rewrite 2 embed_state_vis.
              rewrite 2 map_event_vis. ss.
              rewrite <- 2 bind_trigger.
              gstep. destruct c.
              + eapply pind5.pind5_fold. eapply lsim_sync; ss. i. esplit; ss.
                eapply pind5.pind5_fold. eapply lsim_yieldL. exists (m_conv im_tgt2). esplit.
                { unfold m_eq in INV0; des. ii.
                  destruct i as [|[]]; ss.
                  - specialize (TGT (inl i)). rewrite INV2. ss.
                  - specialize (TGT (inr (inr i))). rewrite INV3. ss.
                  - specialize (TGT (inr (inl i))). rewrite INV4. ss.
                }
                esplit; ss.
                eapply pind5.pind5_fold. eapply lsim_progress.
                gfinal. left. des. eapply CIH; ss.
              + eapply pind5.pind5_fold. eapply lsim_tidR. esplit; ss.
                eapply pind5.pind5_fold. eapply lsim_tidL. esplit; ss.
                eapply pind5.pind5_fold. eapply lsim_progress.
                gfinal. left. eapply CIH; ss.
            - destruct s.
              + rewrite 2 embed_state_put. ss.
                rewrite 2 map_event_vis. ss.
                rewrite <- 2 bind_trigger.
                gstep.
                eapply pind5.pind5_fold. eapply lsim_getL. esplit; ss.
                eapply pind5.pind5_fold. eapply lsim_getR. esplit; ss.
                rewrite 2 map_event_vis. ss.
                rewrite <- 2 bind_trigger.
                eapply pind5.pind5_fold. eapply lsim_putL. esplit; ss.
                eapply pind5.pind5_fold. eapply lsim_putR. esplit; ss.
                eapply pind5.pind5_fold. eapply lsim_progress.
                gfinal. left. eapply CIH; ss.
                des. destruct st_src0, st_tgt0. ss.
              + rewrite 2 embed_state_get. ss.
                rewrite 2 map_event_vis. ss.
                rewrite <- 2 bind_trigger.
                gstep.
                eapply pind5.pind5_fold. eapply lsim_getL. esplit; ss.
                eapply pind5.pind5_fold. eapply lsim_getR. esplit; ss.
                eapply pind5.pind5_fold. eapply lsim_progress.
                gfinal. left.
                destruct st_src0, st_tgt0. des. ss. subst.
                eapply CIH; ss.
          }
      + ss.
        Unshelve. all: eauto.
  Qed.

  Lemma ModAdd_right_cong M1 M2_src M2_tgt :
    ModSim.mod_sim M2_src M2_tgt ->
    ModSim.mod_sim (ModAdd M1 M2_src) (ModAdd M1 M2_tgt).
  Proof.
    i. inv H. econs.
  Admitted.

End ADD_MODSIM.
