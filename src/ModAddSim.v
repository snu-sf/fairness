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

  Lemma ModAdd_comm M1 M2 : ModSim.mod_sim (ModAdd M1 M2) (ModAdd M2 M1).
  Proof.
    pose (world_le := fun (_ _ : unit) => True).
    pose (I := fun x : @shared
                       (ModAdd M1 M2).(state) (ModAdd M2 M1).(state)
                       (ModAdd M1 M2).(ident) (ModAdd M2 M1).(ident)
                       nat_wf nat_wf unit
               => let '(ths, m_src, m_tgt, st_src, st_tgt, w) := x in
                 fst st_src = snd st_tgt /\ snd st_src = fst st_tgt).
    constructor 1 with nat_wf nat_wf S unit world_le I.
    - unfold Transitive. ss. lia.
    - ss. lia.
    - i. exists (fun _ => 0). exists tt. ss.
    - i.
      destruct M1 as [state1 ident1 st_init1 funs1].
      destruct M2 as [state2 ident2 st_init2 funs2].
      ss.
      unfold add_funs.
      ss.
      destruct (funs1 fn), (funs2 fn).
      + ii. pfold. eapply pind5.pind5_fold. rewrite <- bind_trigger. eapply lsim_UB.
      + ii. unfold embed_l, embed_r.
        remember (k args) as itr; clear fn k args Heqitr.
        revert fs ft itr ths0 im_src0 im_tgt0 st_src0 st_tgt0 w0 tid THS INV.
        
        ginit.
        
        gcofix CIH.
        i.

        destruct_itree itr.
        * rewrite 2 embed_state_ret.
          rewrite 2 map_event_ret.
          gstep.
          eapply pind5.pind5_fold.
          econs. inv INV. ss. esplits; ss.
        * rewrite 2 embed_state_tau.
          rewrite 2 map_event_tau.
          gstep.
          eapply pind5.pind5_fold. eapply lsim_tauL. esplit; ss.
          eapply pind5.pind5_fold. eapply lsim_tauR. esplit; ss.
          eapply pind5.pind5_fold. eapply lsim_progress.
          gfinal. left. eapply CIH; ss.
        * { destruct e as [[|] | ].
            - admit.
            - rewrite 2 embed_state_vis.
              rewrite 2 map_event_vis. ss.
              destruct c.
              + admit.
              + admit.
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
      + unfold embed_l, embed_r. ii. admit.
      + ss.
  Admitted.

  Lemma ModAdd_right_cong M1 M2_src M2_tgt :
    ModSim.mod_sim M2_src M2_tgt ->
    ModSim.mod_sim (ModAdd M1 M2_src) (ModAdd M1 M2_tgt).
  Proof.
    i. inv H. econs.
  Admitted.

End ADD_MODSIM.
