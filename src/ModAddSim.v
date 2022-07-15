From sflib Require Import sflib.
From Paco Require Import paco.
From ITree Require Import ITree.
From Fairness Require Import
  ITreeLib
  Mod
  ModSimPico.

Import Lia.
Import Mod.
Import RelationClasses.

Section ADD_MODSIM.


  Lemma ModAdd_comm M1 M2 : ModSim.mod_sim (ModAdd M1 M2) (ModAdd M2 M1).
  Proof.
    pose (world_le := fun (_ _ : unit) => True).
    pose (I := fun (x : @shared
                        (ModAdd M1 M2).(state) (ModAdd M2 M1).(state)
                        (ModAdd M1 M2).(ident) (ModAdd M2 M1).(ident)
                        nat_wf nat_wf unit)
               => True).
    (*
    { i. exact True.
      destruct X as [[[[[[[ths_src ths_tgt] im_src] im_tgt] st_src] st_tgt] o] w].
      exact (fst st_src = snd st_tgt /\ snd st_src = fst st_tgt).
    }
     *)
    constructor 1 with nat_wf nat_wf S unit world_le I.
    - unfold Transitive. ss. lia.
    - ss. lia.
    - i. exists ths_tgt. exists (fun _ => 0). exists 0. exists tt. ss.
    - i.
      destruct M1 as [state1 ident1 st_init1 funs1].
      destruct M2 as [state2 ident2 st_init2 funs2].
      ss.
      unfold add_funs.
      ss.
      destruct (funs1 fn), (funs2 fn).
      + ii. pfold. eapply pind5.pind5_fold. rewrite <- bind_trigger. eapply lsim_UB.
      + unfold embed_l, embed_r. ii.
        remember (k args) as itr; clear Heqitr.
        admit.
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
