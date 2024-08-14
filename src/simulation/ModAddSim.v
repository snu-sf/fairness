From iris.algebra Require Import cmra updates.
From sflib Require Import sflib.
From Paco Require Import paco.
From ITree Require Import ITree.
From Fairness Require Import
  ITreeLib WFLibLarge Axioms pind Mod Linking ModSim ModSimAux ModSimNat AddWorld.

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

End ADD_COMM.

Section IMAP_OPERATIONS.

  Context {id_ctx id_src id_tgt : ID}.
  Context {wf_src : WF}.

  Definition sum_wf wf1 wf2 := {| wf := sum_lt_well_founded (wf wf1) (wf wf2) |}.

  Definition pick_ctx
    (IM_TGT : @imap (ident_tgt (id_sum id_ctx id_tgt)) nat_wf)
    : @imap id_ctx nat_wf := fun i => IM_TGT (inr (inl i)).

  Definition chop_ctx
    (ths : TIdSet.t)
    (IM_TGT : @imap (ident_tgt (id_sum id_ctx id_tgt)) nat_wf)
    : @imap (ident_tgt id_tgt) nat_wf:=
    fun i => match i with
          | inl i => if NatMapP.F.In_dec ths i then IM_TGT (inl i) else 0
          | inr i => IM_TGT (inr (inr i))
          end.

  Definition add_ctx
    (im_ctx : imap id_ctx nat_wf)
    (im_src : imap id_src wf_src)
    : forall i, (sum_wf wf_src nat_wf).(T)
    := fun i => match i with
             | inl i => inr (im_ctx i)
             | inr i => inl (im_src i)
             end.

  Lemma pick_ctx_fair_thread IM_TGT0 IM_TGT1 m
    (FAIR : fair_update IM_TGT0 IM_TGT1 (prism_fmap inlp m))
    : pick_ctx IM_TGT0 = pick_ctx IM_TGT1.
  Proof.
    extensionalities i. specialize (FAIR (inr (inl i))). ss.
  Qed.

  Lemma chop_ctx_fair_ctx ths_usr IM_TGT0 IM_TGT1 m
    (FAIR : fair_update IM_TGT0 IM_TGT1 (prism_fmap inrp (prism_fmap inlp m)))
    : chop_ctx ths_usr IM_TGT0 = chop_ctx ths_usr IM_TGT1.
  Proof.
    extensionalities i. destruct i as [i|i]; ss.
    - specialize (FAIR (inl i)). ss. des_ifs.
    - specialize (FAIR (inr (inr i))). ss.
  Qed.

  Lemma chop_ctx_fair_thread1 ths ths_ctx ths_usr tid IM_TGT0 IM_TGT1
    (PARTITION : NatMapP.Partition ths ths_ctx ths_usr)
    (TID_CTX : NatMap.In tid ths_ctx)
    (FAIR : fair_update IM_TGT0 IM_TGT1 (prism_fmap inlp (tids_fmap tid ths)))
    : fair_update (chop_ctx ths_usr IM_TGT0) (chop_ctx ths_usr IM_TGT1) (prism_fmap inlp (tids_fmap_all ths_usr)).
  Proof.
    ii. unfold prism_fmap in *; ss. destruct i as [i|i]; ss.
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
    (FAIR : fair_update IM_TGT0 IM_TGT1 (prism_fmap inlp (tids_fmap tid ths)))
    : fair_update (chop_ctx ths_usr IM_TGT0) (chop_ctx ths_usr IM_TGT1) (prism_fmap inlp (tids_fmap tid ths_usr)).
  Proof.
    ii. unfold prism_fmap in *; ss. destruct i as [i|i]; ss.
    - specialize (FAIR (inl i)); ss. destruct (NatMapP.F.In_dec ths_usr i).
      + pose proof (LE _ i0). unfold tids_fmap in *. des_ifs.
      + unfold tids_fmap in *. des_ifs.
    - specialize (FAIR (inr (inr i))); ss.
  Qed.

End IMAP_OPERATIONS.

Section SIM_REFLEXIVE.

  Context {A S_src S_tgt : Type}.
  Context {J K_src K_tgt : Type}.
  Context {l_src : Lens.t S_src A}.
  Context {l_tgt : Lens.t S_tgt A}.
  Context {p_src : Prism.t K_src J}.
  Context {p_tgt : Prism.t K_tgt J}.

  Variable I : @shared S_src S_tgt K_src K_tgt nat_wf nat_wf -> unitUR -> Prop.

  Hypothesis I_update_thread :
    forall ths im_src im_tgt st_src st_tgt w,
      I (ths, im_src, im_tgt, st_src, st_tgt) w ->
        forall ths' w', I (ths', im_src, im_tgt, st_src, st_tgt) w'.

  Hypothesis I_update_state :
    forall ths im_src im_tgt st_src st_tgt w,
      I (ths, im_src, im_tgt, st_src, st_tgt) w ->
      Lens.view l_src st_src = Lens.view l_tgt st_tgt /\
        forall st st_src' st_tgt' w',
          st_src' = Lens.set l_src st st_src ->
          st_tgt' = Lens.set l_tgt st st_tgt ->
          I (ths, im_src, im_tgt, st_src', st_tgt') w'.

  Hypothesis I_update_imap :
    forall ths im_src im_tgt st_src st_tgt w,
      I (ths, im_src, im_tgt, st_src, st_tgt) w ->
      Lens.view (prisml p_src) im_src = Lens.view (prisml (inrp ⋅ p_tgt)%prism) im_tgt /\
        forall im im_src' im_tgt' w',
          im_src' = Lens.set (prisml p_src) im im_src ->
          im_tgt' = Lens.set (prisml (inrp ⋅ p_tgt)%prism) im im_tgt ->
          I (ths, im_src', im_tgt', st_src, st_tgt) w'.

  Hypothesis I_update_imap_thread_id :
    forall ths im_src im_tgt st_src st_tgt w,
      I (ths, im_src, im_tgt, st_src, st_tgt) w ->
      forall im im_tgt' w',
        im_tgt' = Lens.set (prisml inlp) im im_tgt ->
        I (ths, im_src, im_tgt', st_src, st_tgt) w'.

  Lemma I_update_imap_fair
    ths im_src im_tgt st_src st_tgt w
    fm im_src' im_tgt' w'
    (FAIR : fair_update im_tgt im_tgt' (prism_fmap (inrp ⋅ p_tgt)%prism fm))
    (SRC : im_src' = Lens.set (prisml p_src) (Lens.view (prisml (inrp ⋅ p_tgt)%prism) im_tgt') im_src)
    (INV : I (ths, im_src, im_tgt, st_src, st_tgt) w)
    : I (ths, im_src', im_tgt', st_src, st_tgt) w'.
  Proof.
    eapply I_update_imap.
    - eapply INV.
    - eapply SRC.
    - extensionalities i. specialize (FAIR i). destruct i; ss.
      unfold prism_fmap in FAIR. cbn in FAIR. cbn. destruct (Prism.preview p_tgt k) eqn: Heq; ss.
      eapply Prism.review_preview in Heq. subst. des_ifs.
  Qed.

  Lemma I_update_imap_thread_id_fair
    ths im_src im_tgt st_src st_tgt w
    fm im_tgt' w'
    (FAIR : fair_update im_tgt im_tgt' (prism_fmap inlp fm))
    (INV : I (ths, im_src, im_tgt, st_src, st_tgt) w)
    : I (ths, im_src, im_tgt', st_src, st_tgt) w'.
  Proof.
    eapply I_update_imap_thread_id.
    - eapply INV.
    - extensionalities i. specialize (FAIR i). destruct i; ss.
  Qed.

  Tactic Notation "hspecialize" hyp(H) "with" uconstr(x) :=
    apply (_equal_f _ _ _ _ x) in H.

  Section LSIM.

    Variable R : Type.
    Variable RR : R -> R -> unitUR -> shared S_src S_tgt K_src K_tgt nat_wf nat_wf -> Prop.

    Hypothesis I_RR_compatible :
      forall r ths im_src im_tgt st_src st_tgt w w',
        I (ths, im_src, im_tgt, st_src, st_tgt) w ->
        RR r r w' (ths, im_src, im_tgt, st_src, st_tgt).

    Lemma lsim_refl :
      forall tid (itr : itree (threadE J A) R)
        fs ft r_ctx ths im_src im_tgt st_src st_tgt
        (INV : I (ths, im_src, im_tgt, st_src, st_tgt) tt),
        lsim I tid RR fs ft r_ctx
          (map_event (plmap p_src l_src) itr)
          (map_event (plmap p_tgt l_tgt) itr)
          (ths, im_src, im_tgt, st_src, st_tgt).
    Proof.
      clear I_update_thread.
      intro tid. ginit. gcofix CIH. i.
      destruct_itree itr.
      - rewrite ! map_event_ret.
        gstep. eapply pind9_fold. eapply lsim_ret. eauto.
      - rewrite ! map_event_tau.
        gstep.
        eapply pind9_fold. eapply lsim_tauL. split; ss.
        eapply pind9_fold. eapply lsim_tauR. split; ss.
        eapply pind9_fold. eapply lsim_progress.
        gbase. eapply CIH; eauto.
      - rewrite !map_event_vis -!bind_trigger. gstep.
        destruct e as [[[e|e]|e]|e]; destruct e.
        + eapply pind9_fold. eapply lsim_chooseR. i. esplit; ss.
          eapply pind9_fold. eapply lsim_chooseL. exists x. esplit; ss.
          eapply pind9_fold. eapply lsim_progress.
          gbase. eapply CIH; eauto.
        + eapply pind9_fold. eapply lsim_fairR. i. esplit; ss.
          eapply pind9_fold. eapply lsim_fairL.
          exists (Lens.set (prisml p_src) (Lens.view (prisml (inrp ⋅ p_tgt)%prism) im_tgt1) im_src). split.
          { eapply I_update_imap in INV. des. ii.
            unfold prism_fmap; cbn. destruct (Prism.preview p_src i) eqn: Heq; ss.
            eapply Prism.review_preview in Heq; subst.
            hspecialize INV with j. cbn in INV. rewrite INV.
            specialize (FAIR (Prism.review (inrp ⋅ p_tgt)%prism j)). cbn in FAIR.
            unfold prism_fmap in FAIR. rewrite Prism.preview_review in FAIR; ss.
          }
          split; ss.
          eapply pind9_fold. eapply lsim_progress.
          gbase. des. eapply CIH.
          { rewrite <- prism_fmap_compose in FAIR. eapply I_update_imap_fair; eauto. }
        + eapply pind9_fold. eapply lsim_observe. i.
          gbase. eapply CIH; eauto.
        + eapply pind9_fold. eapply lsim_UB.
        + eapply pind9_fold. eapply lsim_sync; eauto.
          { Unshelve. all: done. }
          i. gbase. eapply CIH.
          { eapply I_update_imap_thread_id_fair; eauto. }
        + eapply pind9_fold. eapply lsim_tidR. esplit; ss.
          eapply pind9_fold. eapply lsim_tidL. esplit; ss.
          eapply pind9_fold. eapply lsim_progress.
          gbase. eapply CIH; eauto.
        + eapply pind9_fold. eapply lsim_call. i.
          gbase. eapply CIH; eauto.
        + eapply pind9_fold. eapply lsim_stateL. esplit; ss.
          eapply pind9_fold. eapply lsim_stateR. esplit; ss.
          eapply pind9_fold. eapply lsim_progress.
          eapply I_update_state in INV. des. rewrite INV.
          gbase. eapply CIH; eauto.
    Qed.

  End LSIM.

  Lemma local_sim_refl R (itr : itree (threadE J A) R) :
    local_sim I eq (map_event (plmap p_src l_src) itr) (map_event (plmap p_tgt l_tgt) itr).
  Proof.
    ii. exists tt, tt. splits; eauto.
    { eapply I_update_imap_thread_id_fair; eauto. }
    i.
    assert (INV_CIH : I (ths, im_src1, im_tgt3, st_src2, st_tgt2) tt).
    { eapply I_update_imap_thread_id_fair; eauto. }
    eapply lsim_refl; eauto.
    i. ss. esplits; eauto.
    Unshelve. all: exact tt.
  Qed.

End SIM_REFLEXIVE.

Section ADD_RIGHT_MONO_SIM.

  Context {M1 M2_src M2_tgt : Mod.t}.
  Context {wf_src : WF}.
  Context `{world : ucmra}.

  Variable I : shared (state M2_src) (state M2_tgt) (ident M2_src) (ident M2_tgt) wf_src nat_wf -> world -> Prop.

  Definition lift_ma :=
    fun (x : @shared
            (ModAdd M1 M2_src).(state) (ModAdd M1 M2_tgt).(state)
            (ModAdd M1 M2_src).(ident) (ModAdd M1 M2_tgt).(ident)
            (sum_wf wf_src nat_wf) nat_wf)
      (r : prodUR threadsRA world)
    => let '(ths, IM_SRC, IM_TGT, st_src, st_tgt) := x in
      exists im_src0 ths_ctx0 ths_usr0,
        let im_ctx0 := pick_ctx IM_TGT in
        let im_tgt0 := chop_ctx ths_usr0 IM_TGT in
        IM_SRC = add_ctx im_ctx0 im_src0
        /\ NatMapP.Partition ths ths_ctx0 ths_usr0
        /\ fst r = global_th ths_ctx0 ths_usr0
        /\ fst st_src = fst st_tgt
        /\ lifted I (ths_usr0, im_src0, im_tgt0, snd st_src, snd st_tgt) (snd r).

  Opaque lifted threadsRA prodUR.

  Lemma lift_ma_local_sim_ub R_src R_tgt (RR : R_src -> R_tgt -> Prop) ktr_src itr_tgt
    : local_sim lift_ma RR (Vis (inl1 (inl1 (inl1 Undefined))) ktr_src) itr_tgt.
  Proof.
    (* treat as if tid ∈ ths_ctx *)
    intros ths IM_SRC0 IM_TGT0 st_src0 st_tgt0 [r_sha_th0 r_sha_w0] [r_ctx_th0 r_ctx_w0] INV0_0 tid ths0 THS0 VALID0_0 IM_TGT1 TID_TGT.
    simpl in INV0_0. des. subst r_sha_th0.
    rewrite -pair_op pair_valid in VALID0_0. des.
    assert (CTX_TGT : pick_ctx IM_TGT0 = pick_ctx IM_TGT1).
    { extensionalities i. specialize (TID_TGT (inr (inl i))). ss. }
    assert (USR_TGT : chop_ctx ths_usr0 IM_TGT0 = chop_ctx ths_usr0 IM_TGT1).
    { extensionalities i. destruct i as [i|i].
      - specialize (TID_TGT (inl i)). unfold prism_fmap in *; ss. des_ifs. exfalso.
        eapply inv_add_new in THS0. des. eapply THS0.
        eapply Partition_In_right in INV0_1. eapply INV0_1.
        ss.
      - specialize (TID_TGT (inr (inr i))). ss.
    }
    exists (global_th (TIdSet.add tid ths_ctx0) ths_usr0, r_sha_w0), (local_th_context tid, ε). splits.
    { exists im_src0, (TIdSet.add tid ths_ctx0), ths_usr0. splits; ss.
      - subst. rewrite CTX_TGT. ss.
      - eauto using NatMapP.Partition_sym, Partition_add.
      - rewrite USR_TGT in INV0_4. ss.
    }
    { rewrite -!pair_op /= pair_valid. split.
      - eapply inv_add_new in THS0. des; subst. eapply global_th_alloc_context.
        + eauto.
        + eapply inv_add_new. split; ss.
          ii. eapply THS0. eapply (Partition_In_left INV0_1). ss.
        + ii. eapply THS0. eapply (Partition_In_right INV0_1). ss.
      - rewrite right_id. eauto.
    }
    i. pfold. eapply pind9_fold. rewrite <- bind_trigger. econs.
  Qed.

  Lemma lift_ma_local_sim_ctx R (itr : itree _ R)
    : local_sim lift_ma eq (map_event (emb_l M1 M2_src) itr) (map_event (emb_l M1 M2_tgt) itr).
  Proof.
    (* tid ∈ ths_ctx *)
    intros ths IM_SRC0 IM_TGT0 st_src0 st_tgt0 [r_sha_th0 r_sha_w0] [r_ctx_th0 r_ctx_w0] INV0_0 tid ths0 THS0 VALID0_0 IM_TGT1 TID_TGT.
    simpl in INV0_0. des. subst r_sha_th0.
    rewrite -pair_op pair_valid in VALID0_0. des.
    assert (CTX_TGT : pick_ctx IM_TGT0 = pick_ctx IM_TGT1).
    { extensionalities i. specialize (TID_TGT (inr (inl i))). ss. }
    assert (USR_TGT : chop_ctx ths_usr0 IM_TGT0 = chop_ctx ths_usr0 IM_TGT1).
    { extensionalities i. destruct i as [i|i].
      - specialize (TID_TGT (inl i)). unfold prism_fmap in *; ss. des_ifs. exfalso.
        eapply inv_add_new in THS0. des. eapply THS0.
        eapply Partition_In_right in INV0_1. eapply INV0_1.
        ss.
      - specialize (TID_TGT (inr (inr i))). ss.
    }
    exists (global_th (TIdSet.add tid ths_ctx0) ths_usr0, r_sha_w0), (local_th_context tid, ε). splits.
    { exists im_src0, (TIdSet.add tid ths_ctx0), ths_usr0. splits; ss.
      - subst. rewrite CTX_TGT. ss.
      - eauto using NatMapP.Partition_sym, Partition_add.
      - rewrite USR_TGT in INV0_4. ss.
    }
    { rewrite -!pair_op /= pair_valid. split.
      - eapply inv_add_new in THS0. des; subst. eapply global_th_alloc_context.
        + eauto.
        + eapply inv_add_new. split; ss.
          ii. eapply THS0. eapply (Partition_In_left INV0_1). ss.
        + ii. eapply THS0. eapply (Partition_In_right INV0_1). ss.
      - rewrite right_id. eauto.
    }
    intros ths1 IM_SRC1 IM_TGT2 st_src1 st_tgt1 [r_sha_th1 r_sha_w1] [r_ctx_th1 r_ctx_w1] INV1_0 VALID1_0.
    intros IM_TGT2' TGT fs ft.
    simpl in INV1_0. des. subst r_sha_th1.
    rewrite -!pair_op /= pair_valid right_id in VALID1_0. des.
    unfold emb_l, emb_r.
    assert (INV : lift_ma (ths1, IM_SRC1, IM_TGT2', st_src1, st_tgt1) (global_th ths_ctx1 ths_usr1, r_sha_w1)).
    { ss. exists im_src1, ths_ctx1, ths_usr1. splits; ss.
      - eapply pick_ctx_fair_thread in TGT. rewrite <- TGT. ss.
      - eapply shared_rel_wf_lifted; eauto.
        eapply chop_ctx_fair_thread1; eauto.
        eapply local_th_context_in_context; eauto.
    }
    clear - INV VALID1_0 VALID1_1. move itr after tid.
    rename
      ths1 into ths0, ths_ctx1 into ths_ctx0, ths_usr1 into ths_usr0,
      IM_SRC1 into IM_SRC0, IM_TGT2' into IM_TGT0, st_src1 into st_src0, st_tgt1 into st_tgt0,
      r_sha_w1 into r_sha_w0, r_ctx_th1 into r_ctx_th0, r_ctx_w1 into r_ctx_w0,
      INV into INV0, VALID1_0 into VALID_TH0, VALID1_1 into VALID_W0.
    revert_until tid. ginit. gcofix CIH. i.
    destruct_itree itr; [| | destruct e as [[[]|]|] ].
    - rewrite ! map_event_ret.
      gstep. eapply pind9_fold. econs. ss.
      exists (NatSet.remove tid ths0), (ε, ε), (global_th (NatSet.remove tid ths_ctx0) ths_usr0, r_sha_w0).
      splits; ss.
      { rewrite -!pair_op /= pair_valid !right_id. split.
        - eapply global_th_dealloc_context; eauto.
        - eauto.
      }
      { des. inversion INV2. subst ths_ctx1 ths_usr1. exists im_src0, (NatSet.remove tid ths_ctx0), ths_usr0. splits; ss.
        eapply local_th_context_in_context in VALID_TH0.
        eauto using NatMapP.Partition_sym, Partition_remove.
      }
    - rewrite ! map_event_tau.
      gstep.
      eapply pind9_fold. econs. split; ss.
      eapply pind9_fold. econs. split; ss.
      eapply pind9_fold. econs.
      gfinal. left. eapply CIH; eauto.
    - rewrite ! map_event_vis.
      rewrite <- 2 bind_trigger.
      gstep. destruct e; ss.
      + eapply pind9_fold. eapply lsim_chooseR. i. esplit; ss.
        eapply pind9_fold. eapply lsim_chooseL. exists x. esplit; ss.
        eapply pind9_fold. eapply lsim_progress.
        gfinal. left. eapply CIH; eauto.
      + eapply pind9_fold. eapply lsim_fairR. intros IM_TGT1 FAIR. esplit; ss.
        eapply pind9_fold. eapply lsim_fairL.
        des. inversion INV2. subst ths_ctx1 ths_usr1. exists (add_ctx (pick_ctx IM_TGT1) im_src0). split.
        { subst. ii. destruct i; ss.
          specialize (FAIR (inr (inl i))). unfold pick_ctx. ss.
          unfold prism_fmap in *. ss. des_ifs.
          + econs. ss.
          + f_equal. ss.
        }
        split; ss.
        eapply pind9_fold. eapply lsim_progress.
        gfinal. left. des. eapply CIH; eauto.
        { esplits; eauto. eapply chop_ctx_fair_ctx in FAIR. rewrite <- FAIR. ss. }
      + eapply pind9_fold. eapply lsim_observe. i.
        gfinal. left. eapply CIH; eauto.
      + eapply pind9_fold. eapply lsim_UB.
    - rewrite ! map_event_vis. simpl.
      rewrite <- 2 bind_trigger.
      gstep. destruct c.
      + eapply pind9_fold. eapply lsim_sync.
        { eapply INV0. }
        { instantiate (1 := (local_th_context tid, ε)). rewrite -!pair_op right_id pair_valid. split; ss. }
        intros ths1 IM_SRC1 IM_TGT1 st_src1 st_tgt1 [r_sha_th1 r_sha_w1] [r_ctx_th1 r_ctx_w1] INV1_0 VALID1_0 IM_TGT1' TGT.
        simpl in INV1_0. des. subst r_sha_th1. rename im_src0 into im_src1. rewrite -!pair_op right_id pair_valid in VALID1_0. des.
        gfinal. left. eapply CIH; eauto.
        { exists im_src1, ths_ctx1, ths_usr1. ss. splits; ss.
          - eapply pick_ctx_fair_thread in TGT. rewrite <- TGT. ss.
          - eapply shared_rel_wf_lifted; eauto.
            eapply chop_ctx_fair_thread1; eauto.
            eapply local_th_context_in_context; eauto.
        }
      + eapply pind9_fold. eapply lsim_tidR. esplit; ss.
        eapply pind9_fold. eapply lsim_tidL. esplit; ss.
        eapply pind9_fold. eapply lsim_progress.
        gfinal. left. eapply CIH; eauto.
    - rewrite ! map_event_vis. ss.
      rewrite <- 2 bind_trigger.
      destruct c. gstep. eapply pind9_fold. eapply lsim_call.
      i. gfinal. left. eapply CIH; eauto.
    - destruct s.
      rewrite ! map_event_vis. ss.
      rewrite <- 2 bind_trigger.
      gstep.
      eapply pind9_fold. eapply lsim_stateL. esplit; ss.
      eapply pind9_fold. eapply lsim_stateR. esplit; ss.
      eapply pind9_fold. eapply lsim_progress.
      gbase. des. destruct st_src0, st_tgt0; ss. subst.
      eapply CIH; eauto. esplits; eauto.
  Qed.

  Lemma lift_ma_local_sim_usr R_src R_tgt (RR : R_src -> R_tgt -> Prop) itr_src itr_tgt
    (SIM : local_sim (lifted I) RR itr_src itr_tgt)
    : local_sim lift_ma RR (map_event (emb_r M1 M2_src) itr_src) (map_event (emb_r M1 M2_tgt) itr_tgt).
  Proof.
    (* tid ∈ ths_usr *)
    intros ths IM_SRC0 IM_TGT0 st_src0 st_tgt0 [r_sha_th0 r_sha_w0] [r_ctx_th0 r_ctx_w0] INV0_0 tid ths0 THS0 VALID0_0. i.
    simpl in INV0_0. des. subst r_sha_th0. rewrite -!pair_op pair_valid in VALID0_0. des.
    move SIM at bottom.
    assert (THS0' : TIdSet.add_new tid ths_usr0 (TIdSet.add tid ths_usr0)).
    { eapply inv_add_new. split; ss. eapply inv_add_new in THS0. des.
      eapply Partition_In_right in INV0_1. eauto.
    }
    assert (TID_TGT' : fair_update (chop_ctx ths_usr0 IM_TGT0) (chop_ctx (NatSet.add tid ths_usr0) im_tgt1) (prism_fmap inlp (fun i => if Nat.eq_dec i tid then Flag.success else Flag.emp))).
    { ii. destruct i as [i|i]; ss.
      - specialize (TID_TGT (inl i)). unfold prism_fmap in *; ss. destruct (Nat.eq_dec i tid); ss.
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
    { rewrite -!pair_op pair_valid. split.
      - eapply global_th_alloc_user; eauto.
        eapply inv_add_new in THS0. des. ii. eapply THS0.
        eapply Partition_In_left in INV0_1. eapply INV0_1. ss.
      - eauto.
    }
    intros ths2 IM_SRC2 IM_TGT2 st_src2 st_tgt2 [r_sha_th2 r_sha_w2] [r_ctx_th2 r_ctx_w2] INV2_0 VALID2_0 IM_TGT2' TGT fs ft.
    simpl in INV2_0. destruct INV2_0 as [im_src2 [ths_ctx2 [ths_usr2 INV2_0]]]. des. subst r_sha_th2. rewrite -!pair_op pair_valid /= in VALID2_0. des.
    assert (TGT' : @fair_update _ nat_wf (chop_ctx ths_usr2 IM_TGT2) (chop_ctx ths_usr2 IM_TGT2') (prism_fmap inlp (tids_fmap tid ths_usr2))).
    { eapply chop_ctx_fair_thread2.
      - eapply Partition_In_right in INV2_1. eapply INV2_1.
      - eauto.
    }
    specialize (SIM ths_usr2 im_src2 (chop_ctx ths_usr2 IM_TGT2) (snd st_src2) (snd st_tgt2) r_sha_w2 r_ctx_w2 INV2_4 VALID2_1 (chop_ctx ths_usr2 IM_TGT2') TGT' fs ft).
    unfold emb_r.

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
      rewrite ! map_event_ret. econs.
      ss. des. subst.
      exists (NatMap.remove tid ths0), (ε, r_own), (global_th ths_ctx0 (NatMap.remove tid ths_usr0), r_shared).
      splits; ss.
      + rewrite -!pair_op /= right_id pair_valid. split.
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
    - rewrite ! map_event_tau. econs. split; ss.
      destruct LSIM. eapply IH; eauto.
    - rewrite ! map_event_trigger. econs.
      des. destruct LSIM. exists x. split; ss. eapply IH; eauto.
    - rewrite ! map_event_trigger. econs. split; ss.
      destruct LSIM. eapply IH; eauto.
    - rewrite ! map_event_trigger. econs. split; ss.
      destruct LSIM. eapply IH; eauto.
    - rewrite ! map_event_trigger. econs.
    - rewrite ! map_event_trigger. econs.
      des. destruct LSIM0. exists (add_ctx (pick_ctx IM_TGT0) im_src1). splits.
      { clear - FAIR. ii. destruct i as [i|i]; ss.
        unfold prism_fmap; ss. specialize (FAIR i). des_ifs.
        - econs. ss.
        - f_equal. ss.
      }
      split; ss. eapply IH; eauto.
    - rewrite ! map_event_tau. econs. split; ss.
      destruct LSIM. eapply IH; eauto.
    - rewrite ! map_event_trigger. econs. i. specialize (LSIM x). split; ss.
      destruct LSIM. eapply IH; eauto.
    - rewrite ! map_event_trigger. econs. split; ss.
      destruct LSIM. eapply IH; eauto.
    - rewrite ! map_event_trigger. econs. split; ss.
      destruct LSIM. eapply IH; eauto.
    - rewrite ! map_event_trigger. econs. intros IM_TGT1 FAIR. split; ss.
      assert (FAIR' : fair_update (chop_ctx ths_usr0 IM_TGT0) (chop_ctx ths_usr0 IM_TGT1) (prism_fmap inrp f)).
      { ii. destruct i as [i|i]; ss.
        - specialize (FAIR (inl i)). ss. des_ifs.
        - specialize (FAIR (inr (inr i))). ss.
      }
      specialize (LSIM (chop_ctx ths_usr0 IM_TGT1) FAIR').
      destruct LSIM. eapply IH; eauto.
      + extensionalities i. destruct i; ss. f_equal.
        specialize (FAIR (inr (inl i))). ss.
    - rewrite ! map_event_trigger. econs. i. specialize (LSIM ret). pclearbot.
      gfinal. left. eapply CIH; eauto.
    - rewrite ! map_event_trigger. econs. i. specialize (LSIM ret). pclearbot.
      gfinal. left. eapply CIH; eauto.
    - match goal with [ |- __lsim _ _ _ _ _ _ _ _ _ (map_event ?EMB _) _ ] => set EMB as emb end.
      rewrite ! map_event_trigger.
      eapply lsim_yieldL. split; ss.
      replace (trigger Yield) with
              (ITree.trigger
                (subevent _ (F:=threadE _ _)
                  (emb unit (subevent unit Yield)))
              ) by ss.
      rewrite <- ! map_event_trigger.
      destruct LSIM. eapply IH; eauto.
    - match goal with [ |- __lsim _ _ _ _ _ _ _ _ (map_event ?EMB _) _ _ ] => set EMB as emb end.
      rewrite ! map_event_trigger.
      eapply lsim_yieldR.
      { instantiate (1 := (global_th ths_ctx0 ths_usr0, r_shared)).
        ss. exists im_src0, ths_ctx0, ths_usr0. splits; ss.
      }
      { instantiate (1 := (local_th_user tid, r_own)). rewrite -!pair_op pair_valid. split; ss. }
      intros ths1 IM_SRC1 IM_TGT1 st_src1 st_tgt1 [r_sha_th1 r_sha_w1] [r_ctx_th1 r_ctx_w1] INV1_0 VALID1_0 IM_TGT2 TGT.
      split; ss. des. rewrite -!pair_op pair_valid in VALID1_0. des.
      assert (TGT' : fair_update (chop_ctx ths_usr1 IM_TGT1) (chop_ctx ths_usr1 IM_TGT2) (prism_fmap inlp (tids_fmap tid ths_usr1))).
      { ii. unfold prism_fmap. destruct i as [i|i]; ss.
        - eapply Partition_In_right in INV1_1. specialize (INV1_1 i). specialize (TGT (inl i)). unfold prism_fmap in *; ss.
          unfold tids_fmap in *. destruct (Nat.eq_dec i tid); ss; des_ifs.
          exfalso. tauto.
        - specialize (TGT (inr (inr i))). ss.
      }
      specialize (LSIM ths_usr1 im_src1 (chop_ctx ths_usr1 IM_TGT1) (snd st_src1) (snd st_tgt1) r_sha_w1 r_ctx_w1 INV1_4 VALID1_1 (chop_ctx ths_usr1 IM_TGT2) TGT').
      replace (trigger Yield) with
              (ITree.trigger
                (subevent _ (F:=threadE _ _)
                  (emb unit (subevent unit Yield)))
              ) by ss.
      rewrite <- ! map_event_trigger.
      destruct LSIM. eapply IH; eauto.
      + subst. extensionalities i. destruct i as [i|i]; ss. f_equal.
        specialize (TGT (inr (inl i))). ss.
      + subst. ss.
    - rewrite ! map_event_trigger. eapply lsim_sync.
      { instantiate (1 := (global_th ths_ctx0 ths_usr0, r_shared)).
        ss. exists im_src0, ths_ctx0, ths_usr0. splits; ss.
      }
      { instantiate (1 := (local_th_user tid, r_own)). rewrite -!pair_op pair_valid. split; ss. }
      intros ths1 IM_SRC1 IM_TGT1 st_src1 st_tgt1 [r_sha_th1 r_sha_w1] [r_ctx_th1 r_ctx_w1] INV1_0 VALID1_0 IM_TGT2 TGT.
      ss. des. rewrite -!pair_op pair_valid in VALID1_0. des.
      assert (TGT' : fair_update (chop_ctx ths_usr1 IM_TGT1) (chop_ctx ths_usr1 IM_TGT2) (prism_fmap inlp (tids_fmap tid ths_usr1))).
      { ii. destruct i as [i|i]; ss.
        - eapply Partition_In_right in INV1_1. specialize (INV1_1 i). specialize (TGT (inl i)). unfold prism_fmap in *; ss.
          unfold tids_fmap in *. destruct (Nat.eq_dec i tid); ss; des_ifs.
          exfalso. tauto.
        - specialize (TGT (inr (inr i))). ss.
      }
      specialize (LSIM ths_usr1 im_src1 (chop_ctx ths_usr1 IM_TGT1) (snd st_src1) (snd st_tgt1) r_sha_w1 r_ctx_w1 INV1_4 VALID1_1 (chop_ctx ths_usr1 IM_TGT2) TGT').
      pclearbot. gfinal. left. eapply CIH; eauto.
      + subst. ss.
      + subst. extensionalities i. destruct i as [i|i]; ss. f_equal.
        specialize (TGT (inr (inl i))). ss.
    - econs. pclearbot. gfinal. left. eapply CIH; eauto.
  Qed.

End ADD_RIGHT_MONO_SIM.

Section MODADD_THEOREM.

  Theorem ModAdd_comm M1 M2 : ModSim.mod_sim (ModAdd M1 M2) (ModAdd M2 M1).
  Proof.
    (* pose proof Unit_wf. *)
    pose (I := fun (x : @shared
                       (ModAdd M1 M2).(state) (ModAdd M2 M1).(state)
                       (ModAdd M1 M2).(ident) (ModAdd M2 M1).(ident)
                       nat_wf nat_wf)
                 (w : unitUR)
               => let '(ths, m_src, m_tgt, st_src, st_tgt) := x in
                 fst st_src = snd st_tgt
                 /\ snd st_src = fst st_tgt
                 /\ (forall i, m_src (inl i) = m_tgt (inr (inr i)))
                 /\ (forall i, m_src (inr i) = m_tgt (inr (inl i)))
         ).
    constructor 1 with nat_wf nat_wf unitUR.
    - econs. exact 0.
    - i. exists (S o0). ss.
    (* - i. exists (conv im_tgt). exists tt. ss. *)
    - i.
      exists I. split.
      { exists (conv im_tgt). exists tt. ss. }
      destruct M1 as [state1 ident1 st_init1 funs1].
      destruct M2 as [state2 ident2 st_init2 funs2].
      ss. unfold add_funs. ss.
      i. destruct (funs1 fn), (funs2 fn).
      + ii. exists tt, tt. splits; ss.
        { des. splits; ss.
          - i. specialize (TID_TGT (inr (inr i))). specialize (INV1 i). ss. rewrite TID_TGT. ss.
          - i. specialize (TID_TGT (inr (inl i))). specialize (INV2 i). ss. rewrite TID_TGT. ss.
        }
        i. pfold. eapply pind9_fold. rewrite <- bind_trigger. econs.
      + eapply local_sim_refl.
        * firstorder.
        * firstorder.
          -- subst; destruct st_src, st_tgt; ss.
          -- subst; destruct st_src, st_tgt; ss.
        * firstorder.
          -- cbn. extensionalities i. specialize (H1 i). ss.
          -- subst. ss.
          -- subst. cbn. specialize (H2 i). ss.
        * firstorder.
          -- subst. cbn. specialize (H2 i). ss.
          -- subst. cbn. specialize (H3 i). ss.
      + eapply local_sim_refl.
        * firstorder.
        * firstorder.
          -- subst; destruct st_src, st_tgt; ss.
          -- subst; destruct st_src, st_tgt; ss.
        * firstorder.
          -- cbn. extensionalities i. specialize (H2 i). ss.
          -- subst. cbn. specialize (H1 i). ss.
          -- subst. ss.
        * firstorder.
          -- subst. cbn. specialize (H2 i). ss.
          -- subst. cbn. specialize (H3 i). ss.
      + eauto.
  Qed.

  Theorem ModAdd_right_mono M1 M2_src M2_tgt :
    ModSim.mod_sim M2_src M2_tgt ->
    ModSim.mod_sim (ModAdd M1 M2_src) (ModAdd M1 M2_tgt).
  Proof.
    i. eapply modsim_nat_modsim_exist in H. inv H.
    (* econs. *)
    econstructor 1 with (world:=prodUR threadsRA world).
    (* pose (I' := @lift_ma M1 M2_src M2_tgt _ _ I). *)
    (* constructor 1 with _ _ _ I'. *)
    { instantiate (1:=nat_wf). econs. exact 0. }
    { i. exists (S o0). ss. }
    intro IM_TGT. specialize (init (chop_ctx NatSet.empty IM_TGT)). des.
    pose (I' := @lift_ma M1 M2_src M2_tgt _ _ I). exists I'.
    pose (pick_ctx IM_TGT) as im_ctx.
    split.
    { exists (add_ctx im_ctx im_src), (global_th NatSet.empty NatSet.empty, r_shared). ss. split.
      - exists im_src. exists NatSet.empty, NatSet.empty. splits; ss.
        + eapply Partition_empty.
        + exists (chop_ctx NatSet.empty IM_TGT). split; ss. ii. left. ss.
      - rewrite pair_valid. split; ss. econs; ss. eapply Disjoint_empty.
    }
    rename init0 into funs0.
    i. specialize (funs0 fn args).
    unfold ModAdd, add_funs; ss. des_ifs.
    - eapply lift_ma_local_sim_ub.
    - eapply lift_ma_local_sim_ctx.
    - eapply lift_ma_local_sim_usr.
      eapply local_sim_clos_trans in funs0; cycle 1. { econs. exact 0. }
      eapply local_sim_wft_mono with (wft_lt := lt (wf_clos_trans nat_wf)). { i. econs. ss. }
      eapply funs0.
  Qed.

End MODADD_THEOREM.
