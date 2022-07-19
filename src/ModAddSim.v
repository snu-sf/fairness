From sflib Require Import sflib.
From Paco Require Import paco.
From ITree Require Import ITree.
From Fairness Require Import
  ITreeLib
  WFLib
  Mod
  ModSim.

Import Lia.
Import Mod.
Import RelationClasses.

Section WF.

  Inductive sum_rel {A B} (RA : A -> A -> Prop) (RB : B -> B -> Prop) : A + B -> A + B -> Prop :=
  | sum_rel_l a0 a1 (R : RA a0 a1) : sum_rel RA RB (inl a0) (inl a1)
  | sum_rel_r b0 b1 (R : RB b0 b1) : sum_rel RA RB (inr b0) (inr b1)
  .

  Lemma sum_rel_well_founded A B (RA : A -> A -> Prop) (RB : B -> B -> Prop)
    (WFA : well_founded RA)
    (WFB : well_founded RB)
    : well_founded (sum_rel RA RB).
  Proof.
    ii. destruct a.
    - specialize (WFA a). induction WFA.
      econs. i. inv H1. eauto.
    - specialize (WFB b). induction WFB.
      econs. i. inv H1. eauto.
  Qed.

  Program Definition sum_wf (wf1 wf2 : WF) : WF :=
    {| lt := sum_rel wf1.(lt) wf2.(lt) |}.
  Next Obligation.
    destruct wf1, wf2. eapply sum_rel_well_founded; ss.
  Qed.    

  (* TODO : move to WFLib *)
  Definition double_wf (wf1 wf2 : WF) : WF :=
    {| wf := double_rel_well_founded wf1.(wf) wf2.(wf) |}.

End WF.

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

  Import pind8.
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
    constructor 1 with nat_wf nat_wf unit world_le I.
    - econs. exact 0.
    - i. exists (S o0). ss.
    - econs; ss.
    - i. exists (m_conv im_tgt). exists tt. ss.
    - i.
      destruct M1 as [state1 ident1 st_init1 funs1].
      destruct M2 as [state2 ident2 st_init2 funs2].
      ss. unfold add_funs. ss.
      destruct (funs1 fn), (funs2 fn).
      + ii. esplits; ss. i. exists (m_conv im_tgt2). esplits; ss.
        { unfold m_eq in INV0; des. ii.
          destruct i as [|[]]; ss.
          - specialize (TGT (inl i)). rewrite INV2. ss.
          - specialize (TGT (inr (inr i))). rewrite INV3. ss.
          - specialize (TGT (inr (inl i))). rewrite INV4. ss.
        }
        i. pfold. eapply pind8_fold. rewrite <- bind_trigger. eapply lsim_UB.
      + ii. exists tt. splits; ss. i. exists (m_conv im_tgt2). exists tt. splits; ss.
        { unfold m_eq in INV0; des. ii.
          destruct i as [|[]]; ss.
          - specialize (TGT (inl i)). rewrite INV2. ss.
          - specialize (TGT (inr (inr i))). rewrite INV3. ss.
          - specialize (TGT (inr (inl i))). rewrite INV4. ss.
        }
        i. unfold embed_l, embed_r. remember (k args) as itr. remember (m_conv im_tgt2) as im_src2.
        assert (INV_CIH : I (ths, im_src2, im_tgt2, st_src, st_tgt, tt)) by (subst; des; ss).
        clear - INV_CIH.
        rename INV_CIH into INV, im_src2 into im_src0, im_tgt2 into im_tgt0.
        revert_until tid. ginit. gcofix CIH. i.

        destruct_itree itr.
        * rewrite 2 embed_state_ret.
          rewrite 2 map_event_ret.
          gstep. eapply pind8_fold.
          econs. inv INV. des. ss. esplits; ss.
        * rewrite 2 embed_state_tau.
          rewrite 2 map_event_tau.
          gstep.
          eapply pind8_fold. eapply lsim_tauL. esplit; ss.
          eapply pind8_fold. eapply lsim_tauR. esplit; ss.
          eapply pind8_fold. eapply lsim_progress.
          gfinal. left. eapply CIH; ss.
        * { destruct e as [[|] | ].
            - rewrite 2 embed_state_vis.
              rewrite 2 map_event_vis.
              rewrite <- 2 bind_trigger.
              gstep. destruct e; ss.
              + eapply pind8_fold. eapply lsim_chooseR. i. esplit; ss.
                eapply pind8_fold. eapply lsim_chooseL. exists x. esplit; ss.
                eapply pind8_fold. eapply lsim_progress.
                gfinal. left. eapply CIH; ss.
              + eapply pind8_fold. eapply lsim_fairR. i. esplit; ss.
                eapply pind8_fold. eapply lsim_fairL. exists (m_conv im_tgt1). esplit.
                { unfold m_eq in INV; des. ii.
                  destruct i as [|[]]; ss.
                  - specialize (FAIR (inl i)). rewrite INV1. ss.
                  - specialize (FAIR (inr (inr i))). rewrite INV2. ss.
                  - specialize (FAIR (inr (inl i))). rewrite INV3. ss.
                }
                esplit; ss.
                eapply pind8_fold. eapply lsim_progress.
                gfinal. left. des. eapply CIH; ss. 
              + eapply pind8_fold. eapply lsim_observe. i.
                gfinal. left. eapply CIH; ss.
              + eapply pind8_fold. eapply lsim_UB.
            - rewrite 2 embed_state_vis.
              rewrite 2 map_event_vis. ss.
              rewrite <- 2 bind_trigger.
              gstep. destruct c.
              + eapply pind8_fold. eapply lsim_sync; ss. i. esplit; ss.
                eapply pind8_fold. eapply lsim_yieldL. exists (m_conv im_tgt2). esplit.
                { unfold m_eq in INV0; des. ii.
                  destruct i as [|[]]; ss.
                  - specialize (TGT (inl i)). rewrite INV2. ss.
                  - specialize (TGT (inr (inr i))). rewrite INV3. ss.
                  - specialize (TGT (inr (inl i))). rewrite INV4. ss.
                }
                esplit; ss.
                eapply pind8_fold. eapply lsim_progress.
                gfinal. left. des. destruct w1. eapply CIH; ss.
              + eapply pind8_fold. eapply lsim_tidR. esplit; ss.
                eapply pind8_fold. eapply lsim_tidL. esplit; ss.
                eapply pind8_fold. eapply lsim_progress.
                gfinal. left. eapply CIH; ss.
            - destruct s.
              + rewrite 2 embed_state_put. ss.
                rewrite 2 map_event_vis. ss.
                rewrite <- 2 bind_trigger.
                gstep.
                eapply pind8_fold. eapply lsim_getL. esplit; ss.
                eapply pind8_fold. eapply lsim_getR. esplit; ss.
                rewrite 2 map_event_vis. ss.
                rewrite <- 2 bind_trigger.
                eapply pind8_fold. eapply lsim_putL. esplit; ss.
                eapply pind8_fold. eapply lsim_putR. esplit; ss.
                eapply pind8_fold. eapply lsim_progress.
                gfinal. left. eapply CIH; ss.
                des. destruct st_src, st_tgt. ss.
              + rewrite 2 embed_state_get. ss.
                rewrite 2 map_event_vis. ss.
                rewrite <- 2 bind_trigger.
                gstep.
                eapply pind8_fold. eapply lsim_getL. esplit; ss.
                eapply pind8_fold. eapply lsim_getR. esplit; ss.
                eapply pind8_fold. eapply lsim_progress.
                gfinal. left.
                destruct st_src, st_tgt. des. ss. subst.
                eapply CIH; ss.
          }
      + ii. exists tt. splits; ss. i. exists (m_conv im_tgt2). exists tt. splits; ss.
        { unfold m_eq in INV0; des. ii.
          destruct i as [|[]]; ss.
          - specialize (TGT (inl i)). rewrite INV2. ss.
          - specialize (TGT (inr (inr i))). rewrite INV3. ss.
          - specialize (TGT (inr (inl i))). rewrite INV4. ss.
        }
        i. unfold embed_l, embed_r. remember (k args) as itr. remember (m_conv im_tgt2) as im_src2.
        assert (INV_CIH : I (ths, im_src2, im_tgt2, st_src, st_tgt, tt)) by (subst; des; ss).
        clear - INV_CIH.
        rename INV_CIH into INV, im_src2 into im_src0, im_tgt2 into im_tgt0.
        revert_until tid. ginit. gcofix CIH. i.

        destruct_itree itr.
        * rewrite 2 embed_state_ret.
          rewrite 2 map_event_ret.
          gstep. eapply pind8_fold.
          econs. inv INV. des. ss. esplits; ss.
        * rewrite 2 embed_state_tau.
          rewrite 2 map_event_tau.
          gstep.
          eapply pind8_fold. eapply lsim_tauL. esplit; ss.
          eapply pind8_fold. eapply lsim_tauR. esplit; ss.
          eapply pind8_fold. eapply lsim_progress.
          gfinal. left. eapply CIH; ss.
        * { destruct e as [[|] | ].
            - rewrite 2 embed_state_vis.
              rewrite 2 map_event_vis.
              rewrite <- 2 bind_trigger.
              gstep. destruct e; ss.
              + eapply pind8_fold. eapply lsim_chooseR. i. esplit; ss.
                eapply pind8_fold. eapply lsim_chooseL. exists x. esplit; ss.
                eapply pind8_fold. eapply lsim_progress.
                gfinal. left. eapply CIH; ss.
              + eapply pind8_fold. eapply lsim_fairR. i. esplit; ss.
                eapply pind8_fold. eapply lsim_fairL. exists (m_conv im_tgt1). esplit.
                { unfold m_eq in INV; des. ii.
                  destruct i as [|[]]; ss.
                  - specialize (FAIR (inl i)). rewrite INV1. ss.
                  - specialize (FAIR (inr (inr i))). rewrite INV2. ss.
                  - specialize (FAIR (inr (inl i))). rewrite INV3. ss.
                }
                esplit; ss.
                eapply pind8_fold. eapply lsim_progress.
                gfinal. left. des. eapply CIH; ss. 
              + eapply pind8_fold. eapply lsim_observe. i.
                gfinal. left. eapply CIH; ss.
              + eapply pind8_fold. eapply lsim_UB.
            - rewrite 2 embed_state_vis.
              rewrite 2 map_event_vis. ss.
              rewrite <- 2 bind_trigger.
              gstep. destruct c.
              + eapply pind8_fold. eapply lsim_sync; ss. i. esplit; ss.
                eapply pind8_fold. eapply lsim_yieldL. exists (m_conv im_tgt2). esplit.
                { unfold m_eq in INV0; des. ii.
                  destruct i as [|[]]; ss.
                  - specialize (TGT (inl i)). rewrite INV2. ss.
                  - specialize (TGT (inr (inr i))). rewrite INV3. ss.
                  - specialize (TGT (inr (inl i))). rewrite INV4. ss.
                }
                esplit; ss.
                eapply pind8_fold. eapply lsim_progress.
                gfinal. left. des. destruct w1. eapply CIH; ss.
              + eapply pind8_fold. eapply lsim_tidR. esplit; ss.
                eapply pind8_fold. eapply lsim_tidL. esplit; ss.
                eapply pind8_fold. eapply lsim_progress.
                gfinal. left. eapply CIH; ss.
            - destruct s.
              + rewrite 2 embed_state_put. ss.
                rewrite 2 map_event_vis. ss.
                rewrite <- 2 bind_trigger.
                gstep.
                eapply pind8_fold. eapply lsim_getL. esplit; ss.
                eapply pind8_fold. eapply lsim_getR. esplit; ss.
                rewrite 2 map_event_vis. ss.
                rewrite <- 2 bind_trigger.
                eapply pind8_fold. eapply lsim_putL. esplit; ss.
                eapply pind8_fold. eapply lsim_putR. esplit; ss.
                eapply pind8_fold. eapply lsim_progress.
                gfinal. left. eapply CIH; ss.
                des. destruct st_src, st_tgt. ss.
              + rewrite 2 embed_state_get. ss.
                rewrite 2 map_event_vis. ss.
                rewrite <- 2 bind_trigger.
                gstep.
                eapply pind8_fold. eapply lsim_getL. esplit; ss.
                eapply pind8_fold. eapply lsim_getR. esplit; ss.
                eapply pind8_fold. eapply lsim_progress.
                gfinal. left.
                destruct st_src, st_tgt. des. ss. subst.
                eapply CIH; ss.
          }
      + ss.
        Unshelve. all: exact tt.
  Qed.

  Definition imap_proj
    {id1 id2 wf}
    (im : @imap (ident_src (id_sum id1 id2)) wf)
    : @imap (ident_src id2) wf :=
    fun i => match i with
          | inl i => im (inl i)
          | inr i => im (inr (inr i))
          end.

  Lemma ModAdd_right_cong M1 M2_src M2_tgt :
    ModSim.mod_sim M2_src M2_tgt ->
    ModSim.mod_sim (ModAdd M1 M2_src) (ModAdd M1 M2_tgt).
  Proof.
    i. inv H.
    (*
    pose (I' := fun x : @shared
                       (ModAdd M1 M2_src).(state) (ModAdd M1 M2_tgt).(state)
                       (ModAdd M1 M2_src).(ident) (ModAdd M1 M2_tgt).(ident)
                       (sum_wf wf_src wf_tgt) wf_tgt world
                => let '(ths, m_src, m_tgt, st_src, st_tgt, w) := x in
                  fst st_src = fst st_tgt
                  /\ I (ths, imap_proj m_src, imap_proj m_tgt, snd st_src, snd st_tgt, w)
         ).
    constructor 1 with wf_src wf_tgt succ world world_le I'; eauto.
    { i. specialize (init (imap_proj im_tgt)). des.
      exists (fun i => match i with
               | inl i => im_src (inl i)
               | inr (inl i) => im_src (inl 0)
               | inr (inr i) => im_src (inr i)
               end).
      exists w. ss. split; ss. unfold imap_proj at 1.
      match goal with
      | [ |- I (_, ?IM_SRC, _, _, _, _) ] => replace IM_SRC with im_src; cycle 1
      end.
      { extensionalities i. destruct i; ss. }
      ss.
    }
    i. specialize (funs0 fn args).
    destruct M1 as [state1 ident1 st_init1 funs1].
    destruct M2 as [state2 ident2 st_init2 funs2].
    destruct M1.
     *)
  Admitted.

End ADD_MODSIM.
