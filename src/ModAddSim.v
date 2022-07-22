From sflib Require Import sflib.
From Paco Require Import paco.
From ITree Require Import ITree.
From Fairness Require Import
  ITreeLib
  WFLib
  Mod
  ModSim
  pind8.

Import Lia.
Import Mod.
Import RelationClasses.

Section WF_SUM.

  Context {Id : ID}.
  Context (wfs : Id -> WF).

  Definition union : Type := {i : Id & (wfs i).(T)}.

  Inductive union_rel (ix1 ix2 : union) : Prop :=
    intro_union_rel
      (p : projT1 ix1 = projT1 ix2)
      (LT : lt (wfs (projT1 ix2)) (eq_rect _ _ (projT2 ix1) _ p) (projT2 ix2))
      : union_rel ix1 ix2
  .

  Lemma union_rel_well_founded : well_founded union_rel.
  Proof.
    intros [i x]. pose proof (wf (wfs i) x). induction H as [x H IH].
    econs. intros [i' y] [p LT]; ss. destruct p; ss. eauto.
  Qed.

  Definition union_wf := {| wf := union_rel_well_founded |}.

  Lemma sig_eq A (B : A -> Type) (x y : sigT B) (p : x = y)
    : (eq_rect _ _ (projT2 x) _ (f_equal (@projT1 A B) p)) = projT2 y.
  Proof. destruct p. ss. Qed.

  Definition from_dep (m_dep : forall i, (wfs i).(T)) : imap Id union_wf :=
    fun i => existT _ i (m_dep i).

  Definition imap_eqdep (m : imap Id union_wf) (m_dep : forall i, (wfs i).(T)) : Prop :=
    forall i, m i = existT _ i (m_dep i).

End WF_SUM.

Section ADD_COMM.

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
          - specialize (TGT (inl n)). rewrite INV2. ss.
          - specialize (TGT (inr (inr i))). rewrite INV3. ss.
          - specialize (TGT (inr (inl i))). rewrite INV4. ss.
        }
        i. pfold. eapply pind8_fold. rewrite <- bind_trigger. eapply lsim_UB.
      + ii. exists tt. splits; ss. i. exists (m_conv im_tgt2). exists tt. splits; ss.
        { unfold m_eq in INV0; des. ii.
          destruct i as [|[]]; ss.
          - specialize (TGT (inl n)). rewrite INV2. ss.
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
                  - specialize (FAIR (inl n)). rewrite INV1. ss.
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
                  - specialize (TGT (inl n)). rewrite INV2. ss.
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
          - specialize (TGT (inl n)). rewrite INV2. ss.
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
                  - specialize (FAIR (inl n)). rewrite INV1. ss.
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
                  - specialize (TGT (inl n)). rewrite INV2. ss.
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

End ADD_COMM.

Section ADD_RIGHT_CONG.

  Definition mk_m2_tgt
    {id1 id2 wf_tgt}
    (m : @imap (ident_tgt (id_sum id1 id2)) wf_tgt)
    : @imap (ident_src id2) wf_tgt :=
    fun i => match i with
          | inl i => m (inl i)
          | inr i => m (inr (inr i))
          end.

  Definition wfs_src
    {id1 id2 wf_src wf_tgt} (i : ident_src (id_sum id1 id2)) : WF :=
    match i with
    | inl _ => wf_src
    | inr (inl _) => wf_tgt
    | inr (inr _) => wf_src
    end.

  Definition mk_m_src
    {id1 id2_src id2_tgt wf_src wf_tgt}
    (m2_src : imap (ident_src id2_src) wf_src)
    (m_tgt : imap (ident_tgt (id_sum id1 id2_tgt)) wf_tgt)
    : forall i, (@wfs_src id1 id2_src wf_src wf_tgt i).(T)
    := fun i => match i with
             | inl i => m2_src (inl i)
             | inr (inl i) => m_tgt (inr (inl i))
             | inr (inr i) => m2_src (inr i)
             end.

  Lemma ModAdd_right_cong M1 M2_src M2_tgt :
    ModSim.mod_sim M2_src M2_tgt ->
    ModSim.mod_sim (ModAdd M1 M2_src) (ModAdd M1 M2_tgt).
  Proof.
    i. inv H.
    pose (I' := fun x : @shared
                       (ModAdd M1 M2_src).(state) (ModAdd M1 M2_tgt).(state)
                       (ModAdd M1 M2_src).(ident) (ModAdd M1 M2_tgt).(ident)
                       (union_wf wfs_src) wf_tgt world
                => let '(ths, m_src, m_tgt, st_src, st_tgt, w) := x in
                  exists M2_m_src,
                    I (ths, M2_m_src, mk_m2_tgt m_tgt, snd st_src, snd st_tgt, w)
                    /\ imap_eqdep wfs_src m_src (mk_m_src M2_m_src m_tgt)
         ).
    constructor 1 with _ _ world world_le I'; eauto.
    { i. specialize (init (mk_m2_tgt im_tgt)). des.
      exists (from_dep wfs_src (mk_m_src im_src im_tgt)), w. ss.
      esplits; [eauto | ss].
    }
    i. specialize (funs0 fn args).
    destruct M1 as [state1 ident1 st_init1 funs1].
    destruct M2_src as [state2_src ident2_src st_init2_src funs2_src].
    destruct M2_tgt as [state2_tgt ident2_tgt st_init2_tgt funs2_tgt].
    ss. unfold add_funs. ss.
    destruct (funs1 fn) eqn: E1, (funs2_src fn) eqn: E2, (funs2_tgt fn) eqn: E3; ss.
    - admit.
    - admit.
    - (* here *) admit.
  Admitted.

End ADD_RIGHT_CONG.
