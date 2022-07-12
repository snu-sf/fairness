From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Program.
Require Import Arith.
Require Import Permutation.
Require Import SetoidList.
Require Import SetoidPermutation.
Require Import Lists.List.
Require Import Lia.
From Fairness Require Import
  Mod
  FairSim
  Concurrency.
From ExtLib Require Import FMapAList.

Set Implicit Arguments.

Ltac destruct_itree itr :=
  let E := fresh "E" in
  destruct (observe itr) eqn: E;
  symmetry in E;
  apply simpobs in E;
  apply bisim_is_eq in E;
  subst itr.

Section SSIM.

  Variable wf_src : WF.
  Variable wf_tgt : WF.

  Inductive _ssim
    (ssim : forall RT R0 R1 (RR : R0 -> R1 -> Prop), bool -> (@imap thread_id wf_src) -> bool -> (@imap thread_id wf_tgt) -> scheduler RT R0 -> scheduler RT R1 -> Prop)
    {RT R0 R1} (RR : R0 -> R1 -> Prop)
    (p_src : bool) (m_src : @imap thread_id wf_src) (p_tgt : bool) (m_tgt : @imap thread_id wf_tgt)
    : scheduler RT R0 -> scheduler RT R1 -> Prop :=

  | ssim_ret
      r_src r_tgt
      (SIM : RR r_src r_tgt)
    : _ssim ssim RR p_src m_src p_tgt m_tgt (Ret r_src) (Ret r_tgt)

  | ssim_tauL
      itr_src itr_tgt
      (SIM : _ssim ssim RR true m_src p_tgt m_tgt itr_src itr_tgt)
    : _ssim ssim RR p_src m_src p_tgt m_tgt (Tau itr_src) itr_tgt

  | ssim_tauR
      itr_src itr_tgt
      (SIM : _ssim ssim RR p_src m_src true m_tgt itr_src itr_tgt)
    : _ssim ssim RR p_src m_src p_tgt m_tgt itr_src (Tau itr_tgt)

  | ssim_exe
      tid ktr_src ktr_tgt
      (SIM : forall rt,
          ssim _ _ _ RR true m_src true m_tgt (ktr_src rt) (ktr_tgt rt))
    : _ssim ssim RR p_src m_src p_tgt m_tgt (Vis (inl1 (Execute _ tid)) ktr_src) (Vis (inl1 (Execute _ tid)) ktr_tgt)

  | ssim_obs
      ktr_src ktr_tgt fn args
      (SIM : forall r,
          ssim _ _ _ RR true m_src true m_tgt (ktr_src r) (ktr_tgt r))
    : _ssim ssim RR p_src m_src p_tgt m_tgt (Vis (inr1 (Observe fn args)) ktr_src) (Vis (inr1 (Observe fn args)) ktr_tgt)

  | ssim_chooseL
      X ktr_src itr_tgt
      (SIM : exists x, _ssim ssim RR true m_src p_tgt m_tgt (ktr_src x) itr_tgt)
    : _ssim ssim RR p_src m_src p_tgt m_tgt (Vis (inr1 (Choose X)) ktr_src) itr_tgt

  | ssim_chooseR
      X itr_src ktr_tgt
      (SIM : forall x, _ssim ssim RR p_src m_src true m_tgt itr_src (ktr_tgt x))
    : _ssim ssim RR p_src m_src p_tgt m_tgt itr_src (Vis (inr1 (Choose X)) ktr_tgt)

  | ssim_fairL
      f_src ktr_src itr_tgt
      (SIM : exists m_src0, (<<FAIR : fair_update m_src m_src0 f_src>>) /\
                         (<<SIM : _ssim ssim RR true m_src0 p_tgt m_tgt (ktr_src tt) itr_tgt>>))
    : _ssim ssim RR p_src m_src p_tgt m_tgt (Vis (inr1 (Fair f_src)) ktr_src) itr_tgt

  | ssim_fairR
      f_tgt itr_src ktr_tgt
      (SIM : forall m_tgt0 (FAIR : fair_update m_tgt m_tgt0 f_tgt),
          _ssim ssim RR p_src m_src true m_tgt0 itr_src (ktr_tgt tt))
    : _ssim ssim RR p_src m_src p_tgt m_tgt itr_src (Vis (inr1 (Fair f_tgt)) ktr_tgt)

  | ssim_ub
      ktr_src itr_tgt
    : _ssim ssim RR p_src m_src p_tgt m_tgt (Vis (inr1 Undefined) ktr_src) itr_tgt

  | ssim_progress
      itr_src itr_tgt
      (PSRC : p_src = true) (PTGT : p_tgt = true)
      (SIM : ssim _ _ _ RR false m_src false m_tgt itr_src itr_tgt)
    : _ssim ssim RR p_src m_src p_tgt m_tgt itr_src itr_tgt
  .

  Definition ssim : forall RT R0 R1 (RR : R0 -> R1 -> Prop), bool -> (@imap thread_id wf_src) -> bool -> (@imap thread_id wf_tgt) -> scheduler RT R0 -> scheduler RT R1 -> Prop
    := paco10 _ssim bot10.

  Fixpoint ssim_ind
    (ssim : forall RT R0 R1 (RR : R0 -> R1 -> Prop), bool -> imap wf_src -> bool -> imap wf_tgt -> scheduler RT R0 -> scheduler RT R1 -> Prop)
    (RT R0 R1 : Type) (RR : R0 -> R1 -> Prop)
    (P : bool -> @imap thread_id wf_src -> bool -> @imap thread_id wf_tgt -> scheduler RT R0 -> scheduler RT R1 -> Prop)
    (RET : forall (p_src : bool) (m_src : imap wf_src) (p_tgt : bool) (m_tgt : imap wf_tgt) (r_src : R0) (r_tgt : R1),
        RR r_src r_tgt -> P p_src m_src p_tgt m_tgt (Ret r_src) (Ret r_tgt))
    (TAUL : forall (p_src : bool) (m_src : imap wf_src) (p_tgt : bool) (m_tgt : imap wf_tgt) (itr_src : scheduler RT R0) (itr_tgt : scheduler RT R1),
        _ssim ssim RR true m_src p_tgt m_tgt itr_src itr_tgt ->
        P true m_src p_tgt m_tgt itr_src itr_tgt -> P p_src m_src p_tgt m_tgt (Tau itr_src) itr_tgt)
    (TAUR : forall (p_src : bool) (m_src : imap wf_src) (p_tgt : bool) (m_tgt : imap wf_tgt) (itr_src : scheduler RT R0)
              (itr_tgt : scheduler RT R1),
        _ssim ssim RR p_src m_src true m_tgt itr_src itr_tgt ->
        P p_src m_src true m_tgt itr_src itr_tgt -> P p_src m_src p_tgt m_tgt itr_src (Tau itr_tgt))
    (EXE : forall (p_src : bool) (m_src : imap wf_src) (p_tgt : bool) (m_tgt : imap wf_tgt) (tid : id)
             (ktr_src : option RT -> scheduler RT R0) (ktr_tgt : option RT -> scheduler RT R1),
        (forall rt : option RT, ssim RT R0 R1 RR true m_src true m_tgt (ktr_src rt) (ktr_tgt rt)) ->
        P p_src m_src p_tgt m_tgt (Vis (Execute RT tid|)%sum ktr_src) (Vis (Execute RT tid|)%sum ktr_tgt))
    (OBS : forall (p_src : bool) (m_src : imap wf_src) (p_tgt : bool) (m_tgt : imap wf_tgt)
             (ktr_src : nat -> scheduler RT R0) (ktr_tgt : nat -> scheduler RT R1) (fn : nat) (args : list nat),
        (forall r : nat, ssim RT R0 R1 RR true m_src true m_tgt (ktr_src r) (ktr_tgt r)) ->
        P p_src m_src p_tgt m_tgt (Vis (|Observe fn args)%sum ktr_src) (Vis (|Observe fn args)%sum ktr_tgt))
    (CHOOSEL : forall (p_src : bool) (m_src : imap wf_src) (p_tgt : bool) (m_tgt : imap wf_tgt) (X : Type)
                 (ktr_src : X -> scheduler RT R0) (itr_tgt : scheduler RT R1),
        (exists x : X, _ssim ssim RR true m_src p_tgt m_tgt (ktr_src x) itr_tgt /\
                    P true m_src p_tgt m_tgt (ktr_src x) itr_tgt) ->
        P p_src m_src p_tgt m_tgt (Vis (|Choose X)%sum ktr_src) itr_tgt)
    (CHOOSER : forall (p_src : bool) (m_src : imap wf_src) (p_tgt : bool) (m_tgt : imap wf_tgt) (X : Type)
                 (itr_src : scheduler RT R0) (ktr_tgt : X -> scheduler RT R1),
        (forall x : X, _ssim ssim RR p_src m_src true m_tgt itr_src (ktr_tgt x)) ->
        (forall x : X, P p_src m_src true m_tgt itr_src (ktr_tgt x)) ->
        P p_src m_src p_tgt m_tgt itr_src (Vis (|Choose X)%sum ktr_tgt))
    (FAIRL : forall (p_src : bool) (m_src : imap wf_src) (p_tgt : bool) (m_tgt : imap wf_tgt) (f_src : fmap)
               (ktr_src : () -> scheduler RT R0) (itr_tgt : scheduler RT R1),
        (exists m_src0 : imap wf_src,
            (<< FAIR : fair_update m_src m_src0 f_src >>) /\
              (<< SIM : _ssim ssim RR true m_src0 p_tgt m_tgt (ktr_src ()) itr_tgt >>) /\
              P true m_src0 p_tgt m_tgt (ktr_src ()) itr_tgt) ->
        P p_src m_src p_tgt m_tgt (Vis (|Fair f_src)%sum ktr_src) itr_tgt)
    (FAIRR : forall (p_src : bool) (m_src : imap wf_src) (p_tgt : bool) (m_tgt : imap wf_tgt) (f_tgt : fmap)
               (itr_src : scheduler RT R0) (ktr_tgt : () -> scheduler RT R1),
        (forall m_tgt0 : imap wf_tgt,
            fair_update m_tgt m_tgt0 f_tgt -> _ssim ssim RR p_src m_src true m_tgt0 itr_src (ktr_tgt ())) ->
        (forall m_tgt0 : imap wf_tgt, fair_update m_tgt m_tgt0 f_tgt -> P p_src m_src true m_tgt0 itr_src (ktr_tgt ())) ->
        P p_src m_src p_tgt m_tgt itr_src (Vis (|Fair f_tgt)%sum ktr_tgt))
    (UB : forall (p_src : bool) (m_src : imap wf_src) (p_tgt : bool) (m_tgt : imap wf_tgt)
            (ktr_src : void -> itree (schedulerE RT +' eventE) R0) (itr_tgt : scheduler RT R1),
        P p_src m_src p_tgt m_tgt (Vis (|Undefined)%sum ktr_src) itr_tgt)
    (PROGRESS : forall (p_src : bool) (m_src : imap wf_src) (p_tgt : bool) (m_tgt : imap wf_tgt) (itr_src : scheduler RT R0)
                  (itr_tgt : scheduler RT R1),
        p_src = true ->
        p_tgt = true ->
        ssim RT R0 R1 RR false m_src false m_tgt itr_src itr_tgt -> P p_src m_src p_tgt m_tgt itr_src itr_tgt)
    p_src m_src p_tgt m_tgt (sch_src : scheduler RT R0) (sch_tgt : scheduler RT R1)
    (SIM : _ssim ssim RR p_src m_src p_tgt m_tgt sch_src sch_tgt) : P p_src m_src p_tgt m_tgt sch_src sch_tgt.
  Proof.
    inv SIM; eauto.
    - eapply TAUL. eauto. eapply ssim_ind; eauto.
    - eapply TAUR. eauto. eapply ssim_ind; eauto.
    - eapply CHOOSEL. des. esplits. eauto. eapply ssim_ind; eauto.
    - eapply CHOOSER. eauto. i. eapply ssim_ind; eauto.
    - eapply FAIRL. des. esplits; eauto. eapply ssim_ind; eauto.
    - eapply FAIRR. eauto. i. eapply ssim_ind; eauto.
  Qed.

  Lemma ssim_mon : monotone10 _ssim.
  Proof. ii. induction IN using ssim_ind; des; econs; eauto. Qed.

  Hint Constructors _ssim : core.
  Hint Unfold ssim : core.
  Hint Resolve ssim_mon : paco.
  Hint Resolve cpn10_wcompat : paco.

  Lemma ssim_deflag RT R0 R1 (RR : R0 -> R1 -> Prop)
    p_src p_tgt p_src' p_tgt'
    m_src m_tgt (sched_src : scheduler RT R0) sched_tgt :
    ssim RR p_src m_src p_tgt m_tgt sched_src sched_tgt ->
    ssim RR p_src' m_src p_tgt' m_tgt sched_src sched_tgt.
  Proof.
    i. revert p_src' p_tgt'. punfold H.
    induction H using ssim_ind; i.
    - pfold. econs; eauto.
    - pfold. econs. specialize (IH_ssim true p_tgt'). punfold IH_ssim.
    - pfold. econs. specialize (IH_ssim p_src' true). punfold IH_ssim.
    - pfold. econs; eauto.
    - pfold. econs; eauto.
    - pfold. econs. des. eexists. specialize (H0 true p_tgt'). punfold H0.
    - pfold. econs. i. specialize (H0 x p_src' true). punfold H0.
    - pfold. econs. des. esplits; eauto. specialize (H1 true p_tgt'). punfold H1.
    - pfold. econs. i. specialize (H0 m_tgt0 FAIR p_src' true). punfold H0.
    - pfold. econs.
    - clarify. pclearbot.
      
      revert p_src' p_tgt' itr_src itr_tgt m_src m_tgt H1.
      pcofix CIH. i.
      
      remember false as p_src0 in H1 at 1.
      remember false as p_tgt0 in H1 at 1.
      assert (P_SRC : p_src0 = true -> p_src' = true) by (subst; ss).
      assert (P_TGT : p_tgt0 = true -> p_tgt' = true) by (subst; ss).
      clear Heqp_src0 Heqp_tgt0.
      revert p_src' p_tgt' P_SRC P_TGT. punfold H1.
      induction H1 using ssim_ind; i.
      + pfold. econs; eauto.
      + pfold. econs. specialize (IH_ssim true p_tgt' ltac:(ss) P_TGT). punfold IH_ssim.
      + pfold. econs. specialize (IH_ssim p_src' true P_SRC ltac:(ss)). punfold IH_ssim.
      + pfold. econs; eauto. i. eapply upaco10_mon; ss.
      + pfold. econs; eauto. i. eapply upaco10_mon; ss.
      + pfold. econs. des. eexists. specialize (H0 true p_tgt' ltac:(ss) P_TGT). punfold H0.
      + pfold. econs. i. specialize (H0 x p_src' true P_SRC ltac:(ss)). punfold H0.
      + pfold. econs. des. esplits; eauto. specialize (H1 true p_tgt' ltac:(ss) P_TGT). punfold H1.
      + pfold. econs. i. specialize (H0 m_tgt0 FAIR p_src' true P_SRC ltac:(ss)). punfold H0.
      + pfold. econs.
      + pfold. econs; eauto. pclearbot. right. eapply CIH; eauto.
  Qed.

End SSIM.

#[export] Hint Constructors _ssim : core.
#[export] Hint Unfold ssim : core.
#[export] Hint Resolve ssim_mon : paco.

Section SIM.

  Context {_Ident : ID}.
  Variable E : Type -> Type.

  Let eventE1 := @eventE _Ident.
  Let eventE2 := @eventE (sum_tid _Ident).

  Variable State : Type.

  Let thread R := thread _Ident (sE State) R.
  Import Th.

  Lemma nth_error_Some' A (l : list A) x i : nth_error l i = Some x -> i < List.length l.
  Proof. i. eapply nth_error_Some. intro. rewrite H in H0; ss. Qed.

  Variable wf_tgt : WF.
  Variable wf_src : WF.
  Variable wf_emb : wf_tgt.(T) -> wf_src.(T).
  Hypothesis WF_TRANS : Transitive (lt wf_tgt).
  Hypothesis EMB_MON : forall x y, lt wf_tgt x y -> lt wf_src (wf_emb x) (wf_emb y).

  Lemma monotone_weak : forall x y, le wf_tgt x y -> le wf_src (wf_emb x) (wf_emb y).
  Proof. i. unfold le. destruct H; subst; eauto. Qed.

  Theorem ssim_implies_gsim
    RT R0 R1 RR p_src p_tgt sched_src sched_tgt
    (SSIM : forall m_tgt, exists m_src, @ssim wf_src wf_tgt RT R0 R1 RR p_src m_src p_tgt m_tgt sched_src sched_tgt)
    st (ths : @threads _Ident (sE State) RT)
    : gsim wf_src wf_tgt RR p_src p_tgt
        (interp_state (st, interp_sched (ths, sched_src)))
        (interp_state (st, interp_sched (ths, sched_tgt))).
  Proof.
    unfold gsim. intro gm_tgt.

    remember (gm_tgt ∘ inl) as m_tgt.
    assert (M_TGT : forall i, m_tgt i = gm_tgt (inl i)) by (subst; ss).
    specialize (SSIM m_tgt). des.
    remember (fun (i : (sum_tid _Ident).(id)) =>
                match i with
                | inl i => m_src i
                | inr i => wf_emb (gm_tgt (inr i))
                end) as gm_src.
    assert (M_SRC0 : forall i, gm_src (inl i) = m_src i) by (subst; ss).
    assert (M_SRC1 : forall i, gm_src (inr i) = wf_emb (gm_tgt (inr i))) by (subst; reflexivity).
    clear Heqm_tgt Heqgm_src.
    exists gm_src.
 
    revert p_src p_tgt gm_src gm_tgt st ths m_src m_tgt sched_src sched_tgt SSIM M_TGT M_SRC0 M_SRC1.
    ginit. gcofix CIH. i.

    revert gm_src gm_tgt M_TGT M_SRC0 M_SRC1.
    punfold SSIM. induction SSIM using ssim_ind; i.
    - rewrite 2 interp_sched_ret, 2 interp_state_ret.
      guclo sim_indC_spec. econs; eauto.
    - rewrite interp_sched_tau, interp_state_tau.
      guclo sim_indC_spec. econs. eapply IHSSIM; eauto.
    - rewrite interp_sched_tau, interp_state_tau.
      guclo sim_indC_spec. econs. eapply IHSSIM; eauto.
    - pclearbot.
      destruct (Th.find tid ths) as [t|]eqn: H0; cycle 1.
      { rewrite 2 interp_sched_execute_None; eauto.
        rewrite 2 interp_state_vis.
        rewrite <- 2 bind_trigger.
        guclo sim_indC_spec. eapply sim_indC_ub.
      }
      
      erewrite 2 interp_sched_execute_Some; eauto.
      rewrite 2 interp_state_bind.
      rewrite unfold_interp_thread.
      rewrite interp_state_aux_map_event.

      remember (interp_state_aux (st, interp_thread_aux (tid, t))) as itr.
      clear Heqitr.

      revert p_src p_tgt gm_src gm_tgt itr M_SRC0 M_SRC1 M_TGT.
      gcofix CIH2; i.
      
      destruct_itree itr.
      + destruct r0 as [st' lr]. rewrite map_event_ret, 2 bind_ret_l. destruct lr; ss.
        * rewrite 2 interp_state_tau.
          gstep. do 3 econs; eauto. gfinal. left. eapply CIH; eauto. eapply ssim_deflag, H.
        * rewrite 2 interp_state_tau.
          gstep. do 3 econs; eauto. gfinal. left. eapply CIH; eauto. eapply ssim_deflag, H.
      + rewrite map_event_tau. grind.
        gstep. do 3 econs; eauto. gfinal. left. eapply CIH2; eauto.
      + rewrite map_event_vis, 2 bind_vis.
        destruct e.
        * rewrite <- 2 bind_trigger.
          gstep. eapply sim_chooseR. i. eapply sim_chooseL. exists x. econs; eauto. gfinal. left. eapply CIH2; eauto.
        * rewrite <- 2 bind_trigger.
          gstep. eapply sim_fairR. intros gm_tgt0 FAIR. eapply sim_fairL.
          remember (fun i => match i with
                          | inl i => gm_src (inl i)
                          | inr i => wf_emb (gm_tgt0 (inr i))
                          end) as gm_src0.
          exists gm_src0. splits.
          { subst. intros []; ss.
            - reflexivity.
            - rewrite M_SRC1. specialize (FAIR (inr i)); ss. destruct (m i); eauto using monotone_weak.
          }
          econs; eauto.
          guclo sim_imap_ctxR_spec; ss. econs; cycle 1.
          instantiate (1 := fun i => match i with
                                  | inl i => gm_tgt (inl i)
                                  | inr i => gm_tgt0 (inr i)
                                  end).
          { ii. destruct i. specialize (FAIR (inl i)). ss. reflexivity. }
          gfinal. left. eapply CIH2.
          -- subst; eauto.
          -- subst; reflexivity.
          -- i. specialize (M_TGT i). ss.
        * gstep. econs. i. subst. gfinal. left. eapply CIH2; eauto.
        * rewrite <- 2 bind_trigger. gstep. eapply sim_ub.
    - rewrite 2 interp_sched_vis, 2 interp_state_vis.
      gstep. econs. i. subst.
      rewrite 2 interp_state_tau.
      gstep. do 5 econs; eauto. pclearbot. gfinal. left. eapply CIH; ss. eapply ssim_deflag. eapply H.
    - des. rewrite interp_sched_vis, interp_state_vis, <- bind_trigger.
      guclo sim_indC_spec. econs. eexists.
      rewrite interp_state_tau.
      do 2 (guclo sim_indC_spec; econs). eapply H0; eauto.
    - rewrite interp_sched_vis, interp_state_vis, <- bind_trigger.
      guclo sim_indC_spec. econs. i.
      rewrite interp_state_tau.
      do 2 (guclo sim_indC_spec; econs). eapply H0; eauto.
    - des. rewrite interp_sched_vis, interp_state_vis, <- bind_trigger.
      guclo sim_indC_spec. econs.
      remember (fun (i : (sum_tid _Ident).(id)) =>
                  match i with
                  | inl i => m_src0 i
                  | inr i => wf_emb (gm_tgt (inr i))
                  end) as gm_src0.
      exists gm_src0. splits.
      { subst. intros []; ss.
        - rewrite M_SRC0. eapply FAIR.
        - rewrite M_SRC1. reflexivity.
      }
      rewrite interp_state_tau.
      do 2 (guclo sim_indC_spec; econs). eapply H1; subst; eauto.
    - rewrite interp_sched_vis, interp_state_vis, <- bind_trigger.
      guclo sim_indC_spec. econs. intros gm_tgt0 FAIR.
      rewrite interp_state_tau.
      do 2 (guclo sim_indC_spec; econs).
      guclo sim_imap_ctxR_spec; ss. econs; cycle 1.
      instantiate (1 := fun i => match i with
                              | inl i => gm_tgt0 (inl i)
                              | inr i => gm_tgt (inr i)
                              end).
      { ii. destruct i. reflexivity. specialize (FAIR (inr i)). ss. }
      eapply H0. instantiate (1 := fun i => gm_tgt0 (inl i)).
      + ii. rewrite M_TGT. specialize (FAIR (inl i)); ss.
      + reflexivity.
      + eauto.
      + i. rewrite M_SRC1. specialize (FAIR (inr i)). ss.
    - rewrite interp_sched_vis, interp_state_vis, <- bind_trigger. ss.
      gstep. eapply sim_ub.
    - gstep. econs; eauto. pclearbot. gfinal. left. eapply CIH; eauto.
  Qed.

End SIM.
