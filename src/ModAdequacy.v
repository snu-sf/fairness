From sflib Require Import sflib.
From ITree Require Export ITree.
From Paco Require Import paco.

Require Export Coq.Strings.String.
Require Import Program.
Require Import Permutation.

From ExtLib Require Import FMapAList.

Export ITreeNotations.

From Fairness Require Import pind5 pind8.
From Fairness Require Import Axioms.
From Fairness Require Export ITreeLib FairBeh FairSim.
From Fairness Require Export Mod ModSimPico Concurrency.

Set Implicit Arguments.



Section ADEQ.

  Ltac gfold := gfinal; right; pfold.

  Variable state_src: Type.

  Variable _ident_src: ID.
  Let ident_src := sum_tid _ident_src.
  Variable _ident_tgt: ID.
  Let ident_tgt := sum_tid _ident_tgt.

  Variable wf_src: WF.
  Variable wf_tgt: WF.

  Lemma sim_perm_l
        R0 R1 (RR: R0 -> R1 -> Prop)
        ps pt (ms: @imap ident_src wf_src) (mt: @imap ident_tgt wf_tgt)
        tgt
        (st_src: state_src)
        (ths_src: @threads _ident_src (sE state_src) R0)
        (* (WF0: threads_wf ths_src0) *)
        (* (PERM: Permutation ths_src0 ths_src1) *)
        (SIM: sim RR true ms pt mt
                  (interp_state
                     (st_src,
                       x <-
                         Vis (Choose thread_id.(id)|)%sum
                             (fun tid' : nat =>
                                match th_pop tid' ths_src with
                                | Some (t', ts') =>
                                    Vis (Fair (sum_fmap_l (tids_fmap tid' (th_proj1 ts')))|)%sum
                                        (fun _ : () => Ret (inl (tid', t', ts')))
                                | None =>
                                    Vis (Choose void|)%sum (Empty_set_rect _)
                                end);; match x with
                                       | inl tts => Tau (interp_sched tts)
                                       | inr r => Ret r
                                       end)) tgt)
    :
    sim RR ps ms pt mt
        (interp_state
           (st_src,
             x <-
               Vis (Choose thread_id.(id)|)%sum
                   (fun tid' : nat =>
                      match th_pop tid' ths_src with
                      | Some (t', ts') =>
                          Vis (Fair (sum_fmap_l (tids_fmap tid' (th_proj1 ts')))|)%sum
                              (fun _ : () => Ret (inl (tid', t', ts')))
                      | None =>
                          Vis (Choose void|)%sum
                              (Empty_set_rect _)
                      end);; match x with
                             | inl tts => Tau (interp_sched tts)
                             | inr r => Ret r
                             end)) tgt.
  Proof.
    revert SIM. ired. i. rewrite interp_state_vis in *.
    ginit. revert_until RR. gcofix CIH. i.
    match goal with
    | SIM: sim RR _ _ _ _ ?_itr_src _ |- _ => remember _itr_src as itr_src
    end.
    remember true as ps0 in SIM.
    move SIM before CIH. revert_until SIM. induction SIM using sim_ind2; i; ss; clarify.
    { guclo sim_indC_spec. econs 4. eapply IHSIM; eauto. }
    2:{ guclo sim_indC_spec. econs 6. i. specialize (SIM x). des. eapply IH; eauto. }
    2:{ rewrite bind_trigger in Heqitr_src. inv Heqitr_src. }
    2:{ guclo sim_indC_spec. econs 8. i. specialize (SIM m_tgt0 FAIR). des. eapply IH; eauto. }
    2:{ guclo sim_progress_ctx_spec. econs. gfinal; right. eapply paco9_mon_bot. eauto. eauto. all: i; ss. }
    2:{ rewrite bind_trigger in Heqitr_src. inv Heqitr_src. }
    des. rewrite bind_trigger in Heqitr_src. inv Heqitr_src.
    guclo sim_indC_spec. econs 5. exists x.
    gfinal; right. eapply paco9_mon_bot; eauto.
  Qed.

  (*   eapply inj_pair2 in H2. hexploit (equal_f H2 x); clear H2. i. rewrite H in SIM0. *)
  (*   eapply gpaco9_mon_bot; eauto with paco. *)
  (*   revert SIM0 PERM WF0. clear. i. rename SIM0 into SIM. *)
  (*   remember true as p_src. clear Heqp_src. *)
  (*   revert_until RR. gcofix CIH. i. *)
  (*   match goal with *)
  (*   | SIM: sim RR _ _ _ _ ?_itr_src _ |- _ => *)
  (*       remember _itr_src as itr_src *)
  (*   end. *)
  (*   move SIM before CIH. revert_until SIM. induction SIM using sim_ind2; i; ss; clarify. *)
  (*   2:{ guclo sim_indC_spec. econs 4. eapply IHSIM; eauto. } *)
  (*   2:{ rewrite bind_trigger in Heqitr_src. inv Heqitr_src. } *)
  (*   2:{ guclo sim_indC_spec. econs 6. i. specialize (SIM x0). des. eapply IH; eauto. } *)
  (*   2:{ rewrite bind_trigger in Heqitr_src. inv Heqitr_src. } *)
  (*   2:{ guclo sim_indC_spec. econs 8. i. specialize (SIM m_tgt0 FAIR). des. eapply IH; eauto. } *)
  (*   2:{ gfold. econs 9. right. eapply CIH; eauto. all: ss. } *)
  (*   2:{ rewrite bind_trigger in Heqitr_src. inv Heqitr_src. } *)
  (*   guclo sim_indC_spec. rewrite <- bind_trigger. econs 3. *)
  (*   eapply gpaco9_mon_bot; eauto with paco. *)
  (*   revert SIM PERM WF0. clear. i. *)
  (*   remember true as p_src. clear Heqp_src. *)
  (*   hexploit (ths_wf_perm_pop_cases PERM WF0 x). i. des. *)
  (*   { rewrite H. rewrite H0 in SIM. revert SIM. ired. clear. i. *)
  (*     rewrite bind_trigger. rewrite interp_state_vis in *. *)
  (*     revert_until RR. gcofix CIH. i. *)
  (*     match goal with *)
  (*     | SIM: sim RR _ _ _ _ ?_itr_src _ |- _ => *)
  (*         remember _itr_src as itr_src *)
  (*     end. *)
  (*     move SIM before CIH. revert_until SIM. induction SIM using sim_ind2; i; ss; clarify. *)
  (*     { guclo sim_indC_spec. econs 4. eapply IHSIM; eauto. } *)
  (*     { rewrite bind_trigger in Heqitr_src. inv Heqitr_src. des. destruct x. } *)
  (*     { guclo sim_indC_spec. econs 6. i. specialize (SIM x). des. eapply IH; eauto. } *)
  (*     { rewrite bind_trigger in Heqitr_src. inv Heqitr_src. } *)
  (*     { guclo sim_indC_spec. econs 8. i. specialize (SIM m_tgt0 FAIR). des. eapply IH; eauto. } *)
  (*     { gfold. econs 9. right. eapply CIH; eauto. all: ss. } *)
  (*     { rewrite bind_trigger in Heqitr_src. inv Heqitr_src. } *)
  (*   } *)
  (*   rewrite H. rewrite H0 in SIM. clear H H0 WF0 PERM. rename H1 into PERM, H2 into WF. *)
  (*   revert SIM. ired. i. rewrite interp_state_vis in *. revert SIM WF PERM. clear. i. *)
  (*   revert_until RR. gcofix CIH. i. *)
  (*   match goal with *)
  (*   | SIM: sim RR _ _ _ _ ?_itr_src _ |- _ => *)
  (*       remember _itr_src as itr_src *)
  (*   end. *)
  (*   move SIM before CIH. revert_until SIM. induction SIM using sim_ind2; i; ss; clarify. *)
  (*   { guclo sim_indC_spec. econs 4. eapply IHSIM; eauto. } *)
  (*   { rewrite bind_trigger in Heqitr_src. inv Heqitr_src. } *)
  (*   { guclo sim_indC_spec. econs 6. i. specialize (SIM x0). des. eapply IH; eauto. } *)
  (*   2:{ guclo sim_indC_spec. econs 8. i. specialize (SIM m_tgt0 FAIR). des. eapply IH; eauto. } *)
  (*   2:{ gfold. econs 9. right. eapply CIH; eauto. all: ss. } *)
  (*   2:{ rewrite bind_trigger in Heqitr_src. inv Heqitr_src. } *)
  (*   rewrite bind_trigger in Heqitr_src. inv Heqitr_src. des. *)
  (*   eapply inj_pair2 in H1. hexploit (equal_f H1 tt); clear H1. i. rewrite H in SIM. *)
  (*   guclo sim_indC_spec. rewrite <- bind_trigger. econs 7. esplits; eauto. *)
  (*   erewrite tids_fmap_perm_eq; eauto. eapply alist_proj1_preserves_perm; eauto. *)
  (*   eapply gpaco9_mon_bot; eauto with paco. *)
  (*   revert SIM PERM WF. clear. i. *)
  (*   remember true as p_src. clear Heqp_src. *)
  (*   revert_until RR. gcofix CIH. i. *)
  (*   match goal with *)
  (*   | SIM: sim RR _ _ _ _ ?_itr_src _ |- _ => *)
  (*       remember _itr_src as itr_src *)
  (*   end. *)
  (*   move SIM before CIH. revert_until SIM. induction SIM using sim_ind2; i; ss; clarify. *)
  (*   2:{ guclo sim_indC_spec. econs 4. eapply IHSIM; eauto. } *)
  (*   2:{ rewrite bind_trigger in Heqitr_src. inv Heqitr_src. } *)
  (*   2:{ guclo sim_indC_spec. econs 6. i. specialize (SIM x0). des. eapply IH; eauto. } *)
  (*   2:{ rewrite bind_trigger in Heqitr_src. inv Heqitr_src. } *)
  (*   2:{ guclo sim_indC_spec. econs 8. i. specialize (SIM m_tgt0 FAIR). des. eapply IH; eauto. } *)
  (*   2:{ gfold. econs 9. right. eapply CIH; eauto. all: ss. } *)
  (*   2:{ rewrite bind_trigger in Heqitr_src. inv Heqitr_src. } *)
  (*   guclo sim_indC_spec. econs 3. *)
  (*   eapply gpaco9_mon_bot; eauto with paco. *)
  (*   revert SIM PERM WF. clear. i. *)
  (*   rewrite interp_state_tau in *. *)
  (*   remember true as p_src. clear Heqp_src. *)
  (*   revert_until RR. gcofix CIH. i. *)
  (*   match goal with *)
  (*   | SIM: sim RR _ _ _ _ ?_itr_src _ |- _ => *)
  (*       remember _itr_src as itr_src *)
  (*   end. *)
  (*   move SIM before CIH. revert_until SIM. induction SIM using sim_ind2; i; ss; clarify. *)
  (*   2:{ guclo sim_indC_spec. econs 4. eapply IHSIM; eauto. } *)
  (*   2:{ rewrite bind_trigger in Heqitr_src. inv Heqitr_src. } *)
  (*   2:{ guclo sim_indC_spec. econs 6. i. specialize (SIM x0). des. eapply IH; eauto. } *)
  (*   2:{ rewrite bind_trigger in Heqitr_src. inv Heqitr_src. } *)
  (*   2:{ guclo sim_indC_spec. econs 8. i. specialize (SIM m_tgt0 FAIR). des. eapply IH; eauto. } *)
  (*   2:{ gfold. econs 9. right. eapply CIH; eauto. all: ss. } *)
  (*   2:{ rewrite bind_trigger in Heqitr_src. inv Heqitr_src. } *)
  (*   guclo sim_indC_spec. econs 3. *)
  (*   eapply gpaco9_mon_bot; eauto with paco. *)
  (*   revert SIM PERM WF. clear. i. *)
  (*   rename x into tid, ths2 into ths0, ths3 into ths1, itr_tgt0 into itr_tgt. *)
  (*   pose (@interp_all_perm_equiv _ident_src _ R0 tid th ths0 ths1 PERM WF). *)
  (*   eapply bisim_is_eq in e. ss. rewrite e. *)
  (*   gfinal. right. eauto. *)
  (* Qed. *)

  Lemma sim_yieldL_change
        R0 R1 (RR: R0 -> R1 -> Prop)
        ps pt (ms: @imap ident_src wf_src) (mt: @imap ident_tgt wf_tgt)
        tgt
        tid0 tid1
        (st_src: state_src)
        (ths_src0 ths_src1: @threads _ident_src (sE state_src) R0)
        (ktr_src0: unit -> @thread _ident_src (sE state_src) R0)
        (src: @thread _ident_src (sE state_src) R0)
        (POP: th_pop tid1 (Th.add tid0 (ktr_src0 tt) ths_src0) = Some (src, ths_src1))
        (SIM: sim RR true ms pt mt
                  (interp_all st_src ths_src1 tid1 (Vis (inl1 (inr1 Yield)) (fun _ => src)))
                  tgt)
    :
    sim RR ps ms pt mt
        (interp_all st_src ths_src0 tid0 (Vis (inl1 (inr1 Yield)) ktr_src0))
        tgt.
  Proof.
    unfold interp_all in *. rewrite unfold_interp_sched in *.
    rewrite interp_thread_vis_yield in *. rewrite bind_ret_l in *.
    (* rewrite pick_thread_nondet_yield in SIM. *)
    rewrite pick_thread_nondet_yield in *.

  Admitted.



  Variable state_tgt: Type.
  Let srcE := ((@eventE _ident_src +' cE) +' sE state_src).
  Let tgtE := ((@eventE _ident_tgt +' cE) +' sE state_tgt).

  Variable world: Type.
  Variable world_le: world -> world -> Prop.

  Let shared := @shared state_src state_tgt _ident_src _ident_tgt wf_src wf_tgt world.

  Definition threads2 _id ev R := Th.t (prod bool (@thread _id ev R)).
  Let threads_src1 R0 := threads _ident_src (sE state_src) R0.
  Let threads_src2 R0 := threads2 _ident_src (sE state_src) R0.
  Let threads_tgt R1 := threads _ident_tgt (sE state_tgt) R1.

  Variant __sim_knot R0 R1 (RR: R0 -> R1 -> Prop)
          (sim_knot: threads_src2 R0 -> threads_tgt R1 -> thread_id.(id) -> bool -> bool -> (prod bool (itree srcE R0)) -> (itree tgtE R1) -> shared -> Prop)
          (_sim_knot: threads_src2 R0 -> threads_tgt R1 -> thread_id.(id) -> bool -> bool -> (prod bool (itree srcE R0)) -> (itree tgtE R1) -> shared -> Prop)
          (thsl: threads_src2 R0) (thsr: threads_tgt R1)
    :
    thread_id.(id) -> bool -> bool -> (prod bool (itree srcE R0)) -> itree tgtE R1 -> shared -> Prop :=
    | ksim_ret_term
        tid f_src f_tgt
        sf r_src r_tgt
        ths tht im_src im_tgt st_src st_tgt o w
        ths0 tht0 w0
        (THSR: tid_list_remove ths tid ths0)
        (THTR: tid_list_remove tht tid tht0)
        (WORLD: world_le w w0)
        (RET: RR r_src r_tgt)
        (NILS: Th.is_empty thsl = true)
        (NILT: Th.is_empty thsr = true)
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid f_src f_tgt
                 (sf, Ret r_src)
                 (Ret r_tgt)
                 (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)
    | ksim_ret_cont
        tid f_src f_tgt
        sf r_src r_tgt
        ths tht im_src im_tgt st_src st_tgt o w
        ths0 tht0 w0
        (THSR: tid_list_remove ths tid ths0)
        (THTR: tid_list_remove tht tid tht0)
        (WORLD: world_le w w0)
        (RET: RR r_src r_tgt)
        (NNILS: Th.is_empty thsl = false)
        (NNILT: Th.is_empty thsr = false)
        (KSIM: forall tid0,
            ((th_pop tid0 thsl = None) /\ (th_pop tid0 thsr = None)) \/
              (exists b th_src thsl0 th_tgt thsr0,
                  (th_pop tid0 thsl = Some ((b, th_src), thsl0)) /\
                    (th_pop tid0 thsr = Some (th_tgt, thsr0)) /\
                    ((b = true) ->
                     (forall im_tgt0
                        (FAIR: fair_update im_tgt im_tgt0 (sum_fmap_l (tids_fmap tid0 tht0))),
                         sim_knot thsl0 thsr0 tid0 true true
                                  (b, Vis (inl1 (inr1 Yield)) (fun _ => th_src))
                                  (th_tgt)
                                  (ths0, tht0, im_src, im_tgt0, st_src, st_tgt, o, w0))) /\
                    ((b = false) ->
                     forall im_tgt0
                       (FAIR: fair_update im_tgt im_tgt0 (sum_fmap_l (tids_fmap tid0 tht0))),
                     exists im_src0,
                       (fair_update im_src im_src0 (sum_fmap_l (tids_fmap tid0 ths0))) /\
                         (sim_knot thsl0 thsr0 tid0 true true
                                   (b, th_src)
                                   th_tgt
                                   (ths0, tht0, im_src0, im_tgt0, st_src, st_tgt, o, w0)))))
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid f_src f_tgt
                 (sf, Ret r_src)
                 (Ret r_tgt)
                 (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)

    | ksim_sync
        tid f_src f_tgt
        sf ktr_src ktr_tgt
        ths tht im_src im_tgt st_src st_tgt o w
        thsl0 thsr0
        (THSL: thsl0 = Th.add tid (true, ktr_src tt) thsl)
        (THSR: thsr0 = Th.add tid (ktr_tgt tt) thsr)
        (KSIM: forall tid0,
            ((th_pop tid0 thsl0 = None) /\ (th_pop tid0 thsr0 = None)) \/
              (exists b th_src thsl1 th_tgt thsr1,
                  (th_pop tid0 thsl0 = Some ((b, th_src), thsl1)) /\
                    (th_pop tid0 thsr0 = Some (th_tgt, thsr1)) /\
                    ((b = true) ->
                     exists o0 w0,
                       (wf_src.(lt) o0 o) /\ (world_le w w0) /\
                         (forall im_tgt0
                            (FAIR: fair_update im_tgt im_tgt0 (sum_fmap_l (tids_fmap tid0 tht))),
                             sim_knot thsl1 thsr1 tid0 true true
                                      (b, Vis (inl1 (inr1 Yield)) (fun _ => th_src))
                                      (th_tgt)
                                      (ths, tht, im_src, im_tgt0, st_src, st_tgt, o0, w0))) /\
                    ((b = false) ->
                     exists o0 w0,
                       (wf_src.(lt) o0 o) /\ (world_le w w0) /\
                         (forall im_tgt0
                            (FAIR: fair_update im_tgt im_tgt0 (sum_fmap_l (tids_fmap tid0 tht))),
                           exists im_src0,
                             (fair_update im_src im_src0 (sum_fmap_l (tids_fmap tid0 ths))) /\
                               (sim_knot thsl1 thsr1 tid0 true true
                                         (b, th_src)
                                         th_tgt
                                         (ths, tht, im_src0, im_tgt0, st_src, st_tgt, o0, w0))))))
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid f_src f_tgt
                 (sf, Vis (inl1 (inr1 Yield)) ktr_src)
                 (Vis (inl1 (inr1 Yield)) ktr_tgt)
                 (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)

    | ksim_yieldL
        tid f_src f_tgt
        sf ktr_src itr_tgt
        ths tht im_src im_tgt st_src st_tgt o w
        (KSIM: exists im_src0 o0,
            (fair_update im_src im_src0 (sum_fmap_l (tids_fmap tid ths))) /\
              (_sim_knot thsl thsr tid true f_tgt
                         (false, ktr_src tt)
                         itr_tgt
                         (ths, tht, im_src0, im_tgt, st_src, st_tgt, o0, w)))
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid f_src f_tgt
                 (sf, Vis (inl1 (inr1 Yield)) ktr_src)
                 (itr_tgt)
                 (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)

    | ksim_tauL
        tid f_src f_tgt
        sf itr_src itr_tgt
        ths tht im_src im_tgt st_src st_tgt o w
        (KSIM: _sim_knot thsl thsr tid true f_tgt
                         (sf, itr_src)
                         itr_tgt
                         (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w))
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid f_src f_tgt
                 (sf, Tau itr_src)
                 (itr_tgt)
                 (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)
    | ksim_chooseL
        tid f_src f_tgt
        sf X ktr_src itr_tgt
        ths tht im_src im_tgt st_src st_tgt o w
        (KSIM: exists x, _sim_knot thsl thsr tid true f_tgt
                         (sf, ktr_src x)
                         itr_tgt
                         (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w))
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid f_src f_tgt
                 (sf, Vis (inl1 (inl1 (Choose X))) ktr_src)
                 (itr_tgt)
                 (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)
    | ksim_putL
        tid f_src f_tgt
        sf st_src0 ktr_src itr_tgt
        ths tht im_src im_tgt st_src st_tgt o w
        (KSIM: _sim_knot thsl thsr tid true f_tgt
                         (sf, ktr_src tt)
                         itr_tgt
                         (ths, tht, im_src, im_tgt, st_src0, st_tgt, o, w))
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid f_src f_tgt
                 (sf, Vis (inr1 (Mod.Put st_src0)) ktr_src)
                 (itr_tgt)
                 (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)
    | ksim_getL
        tid f_src f_tgt
        sf ktr_src itr_tgt
        ths tht im_src im_tgt st_src st_tgt o w
        (KSIM: _sim_knot thsl thsr tid true f_tgt
                         (sf, ktr_src st_src)
                         itr_tgt
                         (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w))
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid f_src f_tgt
                 (sf, Vis (inr1 (@Mod.Get _)) ktr_src)
                 (itr_tgt)
                 (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)
    | ksim_tidL
        tid f_src f_tgt
        sf ktr_src itr_tgt
        ths tht im_src im_tgt st_src st_tgt o w
        (KSIM: _sim_knot thsl thsr tid true f_tgt
                         (sf, ktr_src tid)
                         itr_tgt
                         (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w))
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid f_src f_tgt
                 (sf, Vis (inl1 (inr1 GetTid)) ktr_src)
                 (itr_tgt)
                 (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)
    | ksim_UB
        tid f_src f_tgt
        sf ktr_src itr_tgt
        ths tht im_src im_tgt st_src st_tgt o w
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid f_src f_tgt
                 (sf, Vis (inl1 (inl1 Undefined)) ktr_src)
                 (itr_tgt)
                 (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)
    | ksim_fairL
        tid f_src f_tgt
        sf fm ktr_src itr_tgt
        ths tht im_src im_tgt st_src st_tgt o w
        (KSIM: exists im_src0,
            (<<FAIR: fair_update im_src im_src0 (sum_fmap_r fm)>>) /\
              (_sim_knot thsl thsr tid true f_tgt
                         (sf, ktr_src tt)
                         itr_tgt
                         (ths, tht, im_src0, im_tgt, st_src, st_tgt, o, w)))
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid f_src f_tgt
                 (sf, Vis (inl1 (inl1 (Fair fm))) ktr_src)
                 (itr_tgt)
                 (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)

    | ksim_tauR
        tid f_src f_tgt
        sf itr_src itr_tgt
        ths tht im_src im_tgt st_src st_tgt o w
        (KSIM: _sim_knot thsl thsr tid f_src true
                         (sf, itr_src)
                         itr_tgt
                         (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w))
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid f_src f_tgt
                 (sf, itr_src)
                 (Tau itr_tgt)
                 (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)
    | ksim_chooseR
        tid f_src f_tgt
        sf itr_src X ktr_tgt
        ths tht im_src im_tgt st_src st_tgt o w
        (KSIM: forall x, _sim_knot thsl thsr tid f_src true
                         (sf, itr_src)
                         (ktr_tgt x)
                         (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w))
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid f_src f_tgt
                 (sf, itr_src)
                 (Vis (inl1 (inl1 (Choose X))) ktr_tgt)
                 (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)
    | ksim_putR
        tid f_src f_tgt
        sf itr_src st_tgt0 ktr_tgt
        ths tht im_src im_tgt st_src st_tgt o w
        (KSIM: _sim_knot thsl thsr tid f_src true
                         (sf, itr_src)
                         (ktr_tgt tt)
                         (ths, tht, im_src, im_tgt, st_src, st_tgt0, o, w))
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid f_src f_tgt
                 (sf, itr_src)
                 (Vis (inr1 (Mod.Put st_tgt0)) ktr_tgt)
                 (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)
    | ksim_getR
        tid f_src f_tgt
        sf itr_src ktr_tgt
        ths tht im_src im_tgt st_src st_tgt o w
        (KSIM: _sim_knot thsl thsr tid f_src true
                         (sf, itr_src)
                         (ktr_tgt st_tgt)
                         (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w))
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid f_src f_tgt
                 (sf, itr_src)
                 (Vis (inr1 (@Mod.Get _)) ktr_tgt)
                 (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)
    | ksim_tidR
        tid f_src f_tgt
        sf itr_src ktr_tgt
        ths tht im_src im_tgt st_src st_tgt o w
        (KSIM: _sim_knot thsl thsr tid f_src true
                         (sf, itr_src)
                         (ktr_tgt tid)
                         (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w))
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid f_src f_tgt
                 (sf, itr_src)
                 (Vis (inl1 (inr1 GetTid)) ktr_tgt)
                 (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)
    | ksim_fairR
        tid f_src f_tgt
        sf itr_src fm ktr_tgt
        ths tht im_src im_tgt st_src st_tgt o w
        (KSIM: forall im_tgt0 (FAIR: fair_update im_tgt im_tgt0 (sum_fmap_r fm)),
            (_sim_knot thsl thsr tid f_src true
                       (sf, itr_src)
                       (ktr_tgt tt)
                       (ths, tht, im_src, im_tgt0, st_src, st_tgt, o, w)))
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid f_src f_tgt
                 (sf, itr_src)
                 (Vis (inl1 (inl1 (Fair fm))) ktr_tgt)
                 (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)

    | ksim_observe
        tid f_src f_tgt
        sf fn args ktr_src ktr_tgt
        ths tht im_src im_tgt st_src st_tgt o w
        (KSIM: forall ret, sim_knot thsl thsr tid true true
                               (sf, ktr_src ret)
                               (ktr_tgt ret)
                               (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w))
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid f_src f_tgt
                 (sf, Vis (inl1 (inl1 (Observe fn args))) ktr_src)
                 (Vis (inl1 (inl1 (Observe fn args))) ktr_tgt)
                 (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)

    | ksim_progress
        tid
        sf itr_src itr_tgt
        ths tht im_src im_tgt st_src st_tgt o w
        (KSIM: sim_knot thsl thsr tid false false
                        (sf, itr_src)
                        itr_tgt
                        (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w))
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid true true
                 (sf, itr_src)
                 (itr_tgt)
                 (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)
  .

  Definition sim_knot R0 R1 (RR: R0 -> R1 -> Prop):
    threads_src2 R0 -> threads_tgt R1 -> thread_id.(id) ->
    bool -> bool -> (prod bool (itree srcE R0)) -> (itree tgtE R1) -> shared -> Prop :=
    paco8 (fun r => pind8 (__sim_knot RR r) top8) bot8.

  Lemma __ksim_mon R0 R1 (RR: R0 -> R1 -> Prop):
    forall r r' (LE: r <8= r'), (__sim_knot RR r) <9= (__sim_knot RR r').
  Proof.
    ii. inv PR; try (econs; eauto; fail).
    { econs 2; eauto. i. specialize (KSIM tid0). des; eauto. right.
      esplits; eauto.
      i. specialize (KSIM2 H _ FAIR). des. esplits; eauto.
    }
    { econs 3; eauto. i. specialize (KSIM tid0). des; eauto. right.
      esplits; eauto.
      i. specialize (KSIM1 H). des. esplits; eauto.
      i. specialize (KSIM2 H). des. esplits; eauto. i. specialize (KSIM4 _ FAIR). des; eauto.
    }
  Qed.

  Lemma _ksim_mon R0 R1 (RR: R0 -> R1 -> Prop): forall r, monotone8 (__sim_knot RR r).
  Proof.
    ii. inv IN; try (econs; eauto; fail).
    { des. econs; eauto. }
    { des. econs; eauto. }
    { des. econs; eauto. }
  Qed.

  Lemma ksim_mon R0 R1 (RR: R0 -> R1 -> Prop): forall q, monotone8 (fun r => pind8 (__sim_knot RR r) q).
  Proof.
    ii. eapply pind8_mon_gen; eauto.
    ii. eapply __ksim_mon; eauto.
  Qed.

  Local Hint Constructors __sim_knot: core.
  Local Hint Unfold sim_knot: core.
  Local Hint Resolve __ksim_mon: paco.
  Local Hint Resolve _ksim_mon: paco.
  Local Hint Resolve ksim_mon: paco.



  Variable I: shared -> Prop.

  Definition local_sim_pick {R0 R1} (RR: R0 -> R1 -> Prop) src tgt tid :=
    forall ths0 tht0 im_src0 im_tgt0 st_src0 st_tgt0 o0 w0
      (THS: tid_list_in tid ths0)
      (THT: tid_list_in tid tht0)
      (INV: I (ths0, tht0, im_src0, im_tgt0, st_src0, st_tgt0, o0, w0))
      fs ft,
    forall im_tgt1 (FAIR: fair_update im_tgt0 im_tgt1 (sum_fmap_l (tids_fmap tid tht0))),
    exists im_src1, (fair_update im_src0 im_src1 (sum_fmap_l (tids_fmap tid ths0))) /\
                 (lsim
                    world_le
                    I
                    (local_RR world_le I RR tid)
                    tid
                    fs ft
                    src tgt
                    (ths0, tht0, im_src1, im_tgt1, st_src0, st_tgt0, o0, w0)).

  Definition local_sim_sync {R0 R1} (RR: R0 -> R1 -> Prop) src tgt tid w :=
    forall ths0 tht0 im_src0 im_tgt0 st_src0 st_tgt0 o0 w0
      (THS: tid_list_in tid ths0)
      (THT: tid_list_in tid tht0)
      (INV: I (ths0, tht0, im_src0, im_tgt0, st_src0, st_tgt0, o0, w0))
      (WORLD: world_le w w0),
    forall im_tgt1 (FAIR: fair_update im_tgt0 im_tgt1 (sum_fmap_l (tids_fmap tid tht0))),
      (lsim
         world_le
         I
         (local_RR world_le I RR tid)
         tid
         true true
         (Vis (inl1 (inr1 Yield)) (fun _ => src))
         tgt
         (ths0, tht0, im_src0, im_tgt1, st_src0, st_tgt0, o0, w0)).

  Definition th_wf_pair {elt1 elt2} (m1: Th.t elt1) (m2: Th.t elt2) :=
    th_proj1 m1 = th_proj1 m2.

  Lemma th_wf_pair_pop_cases
        R0 R1
        (ths_src: threads_src2 R0)
        (ths_tgt: threads_tgt R1)
        (WF: th_wf_pair ths_src ths_tgt)
    :
    forall x, ((th_pop x ths_src = None) /\ (th_pop x ths_tgt = None)) \/
           (exists th_src th_tgt ths_src0 ths_tgt0,
               (th_pop x ths_src = Some (th_src, ths_src0)) /\
                 (th_pop x ths_tgt = Some (th_tgt, ths_tgt0)) /\
                 (th_wf_pair ths_src0 ths_tgt0)).
  Proof.

  Admitted.

  (*invariant for tid_list & threads: tid_list_add threads.proj1 tid tid_list*)

  Definition src_default {R0}: itree srcE R0 := Vis (inl1 (inl1 Undefined)) (Empty_set_rect _).
  Definition src_default2 {R0}: prod bool (itree srcE R0) := (false, Vis (inl1 (inl1 Undefined)) (Empty_set_rect _)).
  Definition tgt_default {R1}: itree tgtE R1 := Vis (inl1 (inl1 Undefined)) (Empty_set_rect _).

  Lemma lsim_implies_ksim
        R0 R1 (RR: R0 -> R1 -> Prop)
        (ths_src: threads_src2 R0)
        (ths_tgt: threads_tgt R1)
        w
        (LOCAL: forall tid sf (src: itree srcE R0) (tgt: itree tgtE R1)
                  (LSRC: Th.find tid ths_src = Some (sf, src))
                  (LTGT: Th.find tid ths_tgt = Some tgt),
            ((sf = true) -> (local_sim_sync RR src tgt tid w)) /\
              ((sf = false) -> (local_sim_pick RR src tgt tid)))
        tid
        (THSRC: Th.find tid ths_src = None)
        (THTGT: Th.find tid ths_tgt = None)
        sf src tgt
        (WF: th_wf_pair (Th.add tid src_default2 ths_src) (Th.add tid tgt_default ths_tgt))
        (st_src: state_src) (st_tgt: state_tgt)
        gps gpt
        o
        (LSIM: forall im_tgt, exists im_src,
            lsim world_le I (local_RR world_le I RR tid) tid gps gpt src tgt
                 (th_proj1 (Th.add tid src_default2 ths_src), th_proj1 (Th.add tid tgt_default ths_tgt),
                   im_src, im_tgt, st_src, st_tgt, o, w))
    :
    forall im_tgt, exists im_src,
      sim_knot RR ths_src ths_tgt tid gps gpt (sf, src) tgt
               (th_proj1 (Th.add tid src_default2 ths_src), th_proj1 (Th.add tid tgt_default ths_tgt),
                 im_src, im_tgt, st_src, st_tgt, o, w).
  Proof.
    ii. specialize (LSIM im_tgt). des. exists im_src.
    revert_until RR. pcofix CIH. i.
    match goal with
    | LSIM: lsim _ _ ?_LRR tid _ _ _ _ ?_shr |- _ => remember _LRR as LRR; remember _shr as shr
    end.
    punfold LSIM.
    2:{ ii. eapply pind5_mon_gen; eauto. i. eapply __lsim_mon; eauto. }
    move LSIM before LOCAL. revert_until LSIM.
    eapply pind5_acc in LSIM.

    { instantiate (1:= (fun gps gpt src tgt shr =>
                          Th.find (elt:=bool * thread _ident_src (sE state_src) R0) tid ths_src = None ->
                          Th.find (elt:=thread _ident_tgt (sE state_tgt) R1) tid ths_tgt = None ->
                          forall sf : bool,
                            th_wf_pair (Th.add tid src_default2 ths_src) (Th.add tid tgt_default ths_tgt) ->
                            forall (st_src : state_src) (st_tgt : state_tgt) (o : T wf_src) (im_tgt : imap wf_tgt) (im_src : imap wf_src),
                              LRR = local_RR world_le I RR tid ->
                              shr =
                                (th_proj1 (Th.add tid src_default2 ths_src), th_proj1 (Th.add tid tgt_default ths_tgt), im_src, im_tgt, st_src, st_tgt, o, w) ->
                              paco8 (fun r0 => pind8 (__sim_knot RR r0) top8) r ths_src ths_tgt tid gps gpt (sf, src) tgt shr)) in LSIM; auto. }

    ss. clear gps gpt src tgt shr LSIM.
    intros rr DEC IH gps gpt src tgt shr LSIM. clear DEC.
    intros THSRC THTGT sf WF st_src st_tgt o im_tgt im_src ELRR Eshr.
    eapply pind5_unfold in LSIM.
    2:{ eapply _lsim_mon. }
    inv LSIM.

    { clear IH rr. unfold local_RR in LSIM0. des. clarify.
      assert (WF0: th_wf_pair ths_src ths_tgt).
      { admit. }
      destruct (Th.is_empty ths_src) eqn:EMPS.
      { destruct (Th.is_empty ths_tgt) eqn:EMPT.
        { pfold. eapply pind8_fold. econs 1. eapply THSR. eapply THTR. all: eauto. }
        { exfalso. admit. }
      }
      { destruct (Th.is_empty ths_tgt) eqn:EMPT.
        { exfalso. admit. }
        { pfold. eapply pind8_fold. econs 2; eauto. i.
          hexploit th_wf_pair_pop_cases.
          { eapply WF0. }
          i. instantiate (1:=tid0) in H. des; auto.
          right. destruct th_src as [sf0 th_src].
          assert (FINDS: Th.find tid0 ths_src = Some (sf0, th_src)).
          { admit. }
          assert (FINDT: Th.find tid0 ths_tgt = Some (th_tgt)).
          { admit. }
          exists sf0, th_src, ths_src0, th_tgt, ths_tgt0.
          splits; auto.
          - i; clarify. 
            hexploit LOCAL. eapply FINDS. eapply FINDT. i; des.
            hexploit H2; clear H2 H3; ss. i. unfold local_sim_sync in H2.
            assert (PROJS: ths3 = th_proj1 (Th.add tid0 src_default2 ths_src0)).
            { admit. }
            assert (PROJT: tht3 = th_proj1 (Th.add tid0 tgt_default ths_tgt0)).
            { admit. }
            rewrite PROJS, PROJT. right. eapply CIH.
            { i. hexploit LOCAL.
              3:{ i; des. split.
                  2:{ eapply H4. }
                  intro SYNC. eapply H3 in SYNC. ii. unfold local_sim_sync in SYNC.
                  assert (WORLD1: world_le w w0).
                  { admit. }
                  specialize (SYNC _ _ _ _ _ _ _ _ THS THT INV0 WORLD1 _ FAIR0). auto.
              }
              1,2: admit.
            }
            1,2: admit.
            admit.
            rewrite <- PROJS, <- PROJT. eapply H2; eauto. 1,2: admit.

          - i. clarify.
            hexploit LOCAL. eapply FINDS. eapply FINDT. i; des.
            hexploit H3; clear H2 H3; ss. i. unfold local_sim_pick in H2.
            assert (PROJS: ths3 = th_proj1 (Th.add tid0 src_default2 ths_src0)).
            { admit. }
            assert (PROJT: tht3 = th_proj1 (Th.add tid0 tgt_default ths_tgt0)).
            { admit. }
            hexploit H2; eauto. 1,2: admit. i; des. esplits; eauto.
            rewrite PROJS, PROJT. right. eapply CIH.
            { i. hexploit LOCAL.
              3:{ i; des. split.
                  2:{ eapply H6. }
                  intro SYNC. eapply H5 in SYNC. ii. unfold local_sim_sync in SYNC.
                  assert (WORLD1: world_le w w0).
                  { admit. }
                  specialize (SYNC _ _ _ _ _ _ _ _ THS THT INV0 WORLD1 _ FAIR0). auto.
              }
              1,2: admit.
            }
            1,2: admit.
            admit.
            rewrite <- PROJS, <- PROJT. eauto.
        }
      }
    }

    { clarify. destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      pfold. eapply pind8_fold. eapply ksim_tauL. split; ss.
      hexploit IH; eauto. i. punfold H. eapply ksim_mon.
    }

    { des. clarify. destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      pfold. eapply pind8_fold. rewrite bind_trigger. eapply ksim_chooseL. exists x. split; ss.
      hexploit IH; eauto. i. punfold H. eapply ksim_mon.
    }

    { clarify. destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      pfold. eapply pind8_fold. rewrite bind_trigger. eapply ksim_putL. split; ss.
      hexploit IH; eauto. i. punfold H. eapply ksim_mon.
    }

    { clarify. destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      pfold. eapply pind8_fold. rewrite bind_trigger. eapply ksim_getL. split; ss.
      hexploit IH; eauto. i. punfold H. eapply ksim_mon.
    }

    { clarify. destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      pfold. eapply pind8_fold. rewrite bind_trigger. eapply ksim_tidL. split; ss.
      hexploit IH; eauto. i. punfold H. eapply ksim_mon.
    }

    { clarify. pfold. eapply pind8_fold. rewrite bind_trigger. eapply ksim_UB. }

    { des. clarify. destruct LSIM as [LSIM IND]. clear LSIM.
      pfold. eapply pind8_fold. rewrite bind_trigger. eapply ksim_fairL. exists im_src1. splits; eauto. split; ss.
      hexploit IH; eauto. i. punfold H. eapply ksim_mon.
    }

    { clarify. destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      pfold. eapply pind8_fold. eapply ksim_tauR. split; ss.
      hexploit IH; eauto. i. punfold H. eapply ksim_mon.
    }

    { clarify.
      pfold. eapply pind8_fold. rewrite bind_trigger. eapply ksim_chooseR. split; ss.
      specialize (LSIM0 x). destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      hexploit IH; eauto. i. punfold H. eapply ksim_mon.
    }

    { clarify. destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      pfold. eapply pind8_fold. rewrite bind_trigger. eapply ksim_putR. split; ss.
      hexploit IH; eauto. i. punfold H. eapply ksim_mon.
    }

    { clarify. destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      pfold. eapply pind8_fold. rewrite bind_trigger. eapply ksim_getR. split; ss.
      hexploit IH; eauto. i. punfold H. eapply ksim_mon.
    }

    { clarify. destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      pfold. eapply pind8_fold. rewrite bind_trigger. eapply ksim_tidR. split; ss.
      hexploit IH; eauto. i. punfold H. eapply ksim_mon.
    }

    { clarify.
      pfold. eapply pind8_fold. rewrite bind_trigger. eapply ksim_fairR. split; ss.
      specialize (LSIM0 im_tgt0 FAIR). des. destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      hexploit IH; eauto. i. punfold H. eapply ksim_mon.
    }

    { clear IH rr. clarify. rewrite ! bind_trigger.
      pfold. eapply pind8_fold. eapply ksim_observe. i.
      specialize (LSIM0 ret). pclearbot. right. eapply CIH; auto.
    }

    { clear IH rr. clarify. rewrite ! bind_trigger.
      pfold. eapply pind8_fold. eapply ksim_sync; eauto. i.
      assert (WF0: th_wf_pair (Th.add tid (true, ktr_src ()) ths_src) (Th.add tid (ktr_tgt ()) ths_tgt)).
      { admit. }
      hexploit th_wf_pair_pop_cases.
      { eapply WF0. }
      i. instantiate (1:=tid0) in H. des; auto.
      right. destruct th_src as [sf0 th_src].
      exists sf0, th_src, ths_src0, th_tgt, ths_tgt0.
      splits; auto.
      - i; clarify. esplits; eauto. i.
        assert (PROJS: th_proj1 (Th.add tid src_default2 ths_src) = th_proj1 (Th.add tid0 src_default2 ths_src0)).
        { admit. }
        assert (PROJT: th_proj1 (Th.add tid tgt_default ths_tgt) = th_proj1 (Th.add tid0 tgt_default ths_tgt0)).
        { admit. }
        rewrite PROJS, PROJT.
        destruct (tid_dec tid tid0) eqn:TID; clarify.
        { rename tid0 into tid.
          assert (ths_tgt0 = ths_tgt /\ th_tgt = (ktr_tgt ())).
          { admit. }
          assert (ths_src0 = ths_src /\ th_src = (ktr_src ())).
          { admit. }
          des; clarify. right. eapply CIH; eauto.
          { i. hexploit LOCAL. 1,2: eauto. i; des. split.
            2:{ eapply H3. }
            intro SYNC. eapply H2 in SYNC. ii. unfold local_sim_sync in SYNC.
            assert (WORLD1: world_le w w0).
            { admit. }
            specialize (SYNC _ _ _ _ _ _ _ _ THS THT INV0 WORLD1 _ FAIR0). auto.
          }
          hexploit LSIM0; eauto. admit.
          i. pclearbot.
          match goal with
          | |- lsim _ _ _ tid _ _ ?_itr _ _ => assert (_itr = (x <- trigger Yield;; ktr_src x))
          end.
          { rewrite bind_trigger. f_equal. f_equal. extensionality x. destruct x. ss. }
          rewrite H3; eauto.
        }
        right. eapply CIH.
        { i. destruct (tid_dec tid tid1) eqn:TID2; clarify.
          { rename tid1 into tid.
            assert (sf0 = true).
            { admit. }
            clarify; split; i; ss. clear H2.
            assert (src = ktr_src ()).
            { admit. }
            assert (tgt = ktr_tgt ()).
            { admit. }
            clarify. ii.
            hexploit LSIM0. eapply INV0. auto. eauto.
            i. pclearbot.
            match goal with
            | |- lsim _ _ _ tid _ _ ?_itr _ _ => assert (_itr = (x <- trigger Yield;; ktr_src x))
            end.
            { rewrite bind_trigger. f_equal. f_equal. extensionality x. destruct x. ss. }
            rewrite H3; eauto.
          }
          { hexploit LOCAL.
            3:{ i; des. split.
                2:{ eapply H3. }
                intro SYNC. eapply H2 in SYNC. ii. unfold local_sim_sync in SYNC.
                assert (WORLD1: world_le w w0).
                { admit. }
                specialize (SYNC _ _ _ _ _ _ _ _ THS THT INV0 WORLD1 _ FAIR0). auto.
            }
            1,2: admit.
          }
        }
        1,2: admit.
        admit.
        hexploit LOCAL.
        3:{ i; des. hexploit H2; ss.
            intro SYNC. unfold local_sim_sync in SYNC.
            hexploit SYNC.
            3,4,5: eauto.
            1,2: admit.
            i. rewrite <- PROJS, <- PROJT. eauto.
        }
        1,2: admit.

      - i; clarify. destruct (tid_dec tid tid0) eqn:TID1.
        { clarify. exfalso. admit. }
        esplits; eauto. i.
        hexploit LOCAL.
        3:{ i; des. hexploit H3; ss. intro PICK. unfold local_sim_pick in PICK. hexploit PICK.
            3,4: eauto.
            1,2: admit.
            i; des. esplits; eauto.
            assert (PROJS: th_proj1 (Th.add tid src_default2 ths_src) = th_proj1 (Th.add tid0 src_default2 ths_src0)).
            { admit. }
            assert (PROJT: th_proj1 (Th.add tid tgt_default ths_tgt) = th_proj1 (Th.add tid0 tgt_default ths_tgt0)).
            { admit. }
            rewrite PROJS, PROJT.
            right. eapply CIH.
            { i. destruct (tid_dec tid tid1) eqn:TID2; clarify.
              { rename tid1 into tid.
                assert (sf0 = true).
                { admit. }
                clarify; split; i; ss. clear H2.
                assert (src = ktr_src ()).
                { admit. }
                assert (tgt = ktr_tgt ()).
                { admit. }
                clarify. ii.
                hexploit LSIM0. eapply INV0. auto. eauto.
                i. pclearbot.
                match goal with
                | |- lsim _ _ _ tid _ _ ?_itr _ _ => assert (_itr = (x <- trigger Yield;; ktr_src x))
                end.
                { rewrite bind_trigger. f_equal. f_equal. extensionality x. destruct x. ss. }
                rewrite H7; eauto.
              }
              { hexploit LOCAL.
                3:{ i; des. split.
                    2:{ eapply H7. }
                    intro SYNC. eapply H6 in SYNC. ii. unfold local_sim_sync in SYNC.
                    assert (WORLD1: world_le w w0).
                    { admit. }
                    specialize (SYNC _ _ _ _ _ _ _ _ THS THT INV0 WORLD1 _ FAIR0). auto.
                }
                1,2: admit.
              }
            }
            1,2: admit.
            admit.
            rewrite <- PROJS, <- PROJT. eauto.
        }
        1,2: admit.
    }

    { des. clarify. destruct LSIM as [LSIM0 IND]. clear LSIM0.
      pfold. eapply pind8_fold. rewrite bind_trigger. eapply ksim_yieldL. esplits; eauto. split; ss.
      hexploit IH; eauto. i. punfold H. eapply ksim_mon.
    }

    { clarify. pclearbot. pfold. eapply pind8_fold. eapply ksim_progress. right. eapply CIH; eauto. }

  Admitted.

    (* unfold local_sim in LSIM. *)
    (* hexploit LSIM; clear LSIM. 3: eauto. *)
    (* { instantiate (1:=tid). ss. auto. } *)
    (* { ss. auto. } *)
    (* intro LSIM. clear INV. *)
    (* instantiate (1:=gpt) in LSIM. instantiate (1:=gps) in LSIM. *)
    (* (* instantiate (1:=true) in LSIM. instantiate (1:=true) in LSIM. *) *)

    (* ginit. revert_until RR. gcofix CIH. i. *)
    (* move o before CIH. revert_until o. induction (wf_src.(wf) o). clear H. rename x into o, H0 into IHo. i. *)

    (* match goal with *)
    (* | LSIM: lsim _ _ ?_LRR tid _ _ _ _ ?_shr |- _ => remember _LRR as LRR; remember _shr as shr *)
    (* end. *)
    (* (* remember true as ps in LSIM at 1. remember true as pt in LSIM at 1. *) *)
    (* (* clear Heqps Heqpt. *) *)
    (* (* remember tid as tid0 in LSIM. *) *)
    (* punfold LSIM. *)
    (* 2:{ ii. eapply pind5_mon_gen; eauto. i. eapply __lsim_mon; eauto. } *)
    (* move LSIM before LOCAL. revert_until LSIM. *)
    (* eapply pind5_acc in LSIM. *)

    (* { instantiate (1:= (fun gps gpt (src: itree srcE R0) (tgt: itree tgtE R1) shr => *)
    (*                       Th.find tid ths_src = None -> *)
    (*                       Th.find tid ths_tgt = None -> *)
    (*                       forall (st_src : state_src) (st_tgt : state_tgt) (mt : imap wf_tgt) (ms : imap wf_src) (w : world), *)
    (*                         LRR = local_RR world_le I RR tid -> *)
    (*                         shr = (tid :: alist_proj1 ths_src, tid :: alist_proj1 ths_tgt, ms, mt, st_src, st_tgt, o, w) -> *)
    (*                         gpaco9 (_sim (wft:=wf_tgt)) (cpn9 (_sim (wft:=wf_tgt))) bot9 r R0 R1 RR gps ms gpt mt (interp_all st_src ths_src tid src) *)
    (*                                (interp_all st_tgt ths_tgt tid tgt))) in LSIM. auto. } *)

    (* ss. clear gps gpt src tgt shr LSIM. *)
    (* intros rr DEC IH ps pt src tgt shr LSIM. clear DEC. *)
    (* intros THSRC THTGT st_src st_tgt mt ms w ELRR Eshr. *)
    (* (* intros THSRC THTGT st_src st_tgt mt ms o w gps gpt ELRR Eshr Eps Ept. clarify. *) *)
    (* eapply pind5_unfold in LSIM. *)
    (* 2:{ eapply _lsim_mon. } *)
    (* inv LSIM. *)

    (* { clear IH rr. unfold local_RR in LSIM0. des. clarify. *)
    (*   unfold interp_all. rewrite ! interp_sched_ret. rewrite ! interp_state_tau. *)
    (*   guclo sim_indC_spec. econs 3. guclo sim_indC_spec. econs 4. *)
    (*   rewrite ! interp_sched_pick_ret. *)
    (*   (*TODO: case analysis; all threads done / some other gets the turn -> CIH*) *)
    (*   admit. *)
    (* } *)

    (* { clarify. destruct LSIM0 as [LSIM0 IND]. clear LSIM0. *)
    (*   unfold interp_all at 1. pull_tau. *)
    (*   guclo sim_indC_spec. econs 3. *)
    (*   eapply IH. eauto. all: eauto. *)
    (* } *)

    (* { des. clarify. destruct LSIM0 as [LSIM0 IND]. clear LSIM0. *)
    (*   unfold interp_all at 1. pull_eventE_l. *)
    (*   guclo sim_indC_spec. econs 5. exists x. *)
    (*   rewrite interp_state_tau. do 2 (guclo sim_indC_spec; econs 3). *)
    (*   eapply IH. eauto. all: eauto. *)
    (* } *)

    (* { clarify. destruct LSIM0 as [LSIM0 IND]. clear LSIM0. *)
    (*   unfold interp_all at 1. pull_sE_l. rewrite interp_state_put. *)
    (*   rewrite interp_state_tau. do 2 (guclo sim_indC_spec; econs 3). *)
    (*   eapply IH. eauto. all: eauto. *)
    (* } *)

    (* { clarify. destruct LSIM0 as [LSIM0 IND]. clear LSIM0. *)
    (*   unfold interp_all at 1. pull_sE_l. rewrite interp_state_get. *)
    (*   rewrite interp_state_tau. do 2 (guclo sim_indC_spec; econs 3). *)
    (*   eapply IH. eauto. all: eauto. *)
    (* } *)

    (* { clarify. destruct LSIM0 as [LSIM0 IND]. clear LSIM0. *)
    (*   unfold interp_all at 1. rewrite_cE_l. rewrite interp_sched_gettid. *)
    (*   rewrite interp_state_tau. do 1 (guclo sim_indC_spec; econs 3). *)
    (*   eapply IH. eauto. all: eauto. *)
    (* } *)

    (* { clarify. unfold interp_all at 1. pull_eventE_l. *)
    (*   guclo sim_indC_spec. econs 10. *)
    (* } *)

    (* { des. clarify. destruct LSIM as [LSIM IND]. clear LSIM. *)
    (*   unfold interp_all at 1. pull_eventE_l. *)
    (*   guclo sim_indC_spec. econs 7. esplits; eauto. *)
    (*   rewrite interp_state_tau. do 2 (guclo sim_indC_spec; econs 3). *)
    (*   eapply IH. eauto. all: eauto. *)
    (* } *)

    (* { clarify. destruct LSIM0 as [LSIM0 IND]. clear LSIM0. *)
    (*   unfold interp_all at 2. pull_tau. *)
    (*   guclo sim_indC_spec. econs 4. *)
    (*   eapply IH. eauto. all: eauto. *)
    (* } *)

    (* { clarify. unfold interp_all at 2. pull_eventE_r. *)
    (*   guclo sim_indC_spec. econs 6. i. *)
    (*   specialize (LSIM0 x). destruct LSIM0 as [LSIM0 IND]. clear LSIM0. *)
    (*   rewrite interp_state_tau. do 2 (guclo sim_indC_spec; econs 4). *)
    (*   eapply IH. eauto. all: eauto. *)
    (* } *)

    (* { clarify. destruct LSIM0 as [LSIM0 IND]. clear LSIM0. *)
    (*   unfold interp_all at 2. pull_sE_r. rewrite interp_state_put. *)
    (*   rewrite interp_state_tau. do 2 (guclo sim_indC_spec; econs 4). *)
    (*   eapply IH. eauto. all: eauto. *)
    (* } *)

    (* { clarify. destruct LSIM0 as [LSIM0 IND]. clear LSIM0. *)
    (*   unfold interp_all at 2. pull_sE_r. rewrite interp_state_get. *)
    (*   rewrite interp_state_tau. do 2 (guclo sim_indC_spec; econs 4). *)
    (*   eapply IH. eauto. all: eauto. *)
    (* } *)

    (* { clarify. destruct LSIM0 as [LSIM0 IND]. clear LSIM0. *)
    (*   unfold interp_all at 2. rewrite_cE_r. rewrite interp_sched_gettid. *)
    (*   rewrite interp_state_tau. do 1 (guclo sim_indC_spec; econs 4). *)
    (*   eapply IH. eauto. all: eauto. *)
    (* } *)

    (* { clarify. unfold interp_all at 2. pull_eventE_r. *)
    (*   guclo sim_indC_spec. econs 8. i. *)
    (*   specialize (LSIM0 m_tgt0 FAIR). des. destruct LSIM0 as [LSIM0 IND]. clear LSIM0. *)
    (*   rewrite interp_state_tau. do 2 (guclo sim_indC_spec; econs 4). *)
    (*   eapply IH. eauto. all: eauto. *)
    (* } *)

    (* { clarify. unfold interp_all. pull_eventE_l. pull_eventE_r. *)
    (*   rewrite ! bind_trigger. gfold. econs 2. i; clarify. *)
    (*   rename r_tgt into retv. specialize (LSIM0 retv). pclearbot. *)
    (*   clear IH rr. *)
    (*   rewrite <- ! interp_state_tau. rewrite <- ! interp_sched_tau. *)
    (*   right. eapply CIH; auto. *)
    (*   pfold. *)
    (*   eapply pind5_fold. econs 2. split; ss. eapply pind5_fold. econs 9. split; ss. *)
    (*   eapply pind5_fold. econs 2. split; ss. eapply pind5_fold. econs 9. split; ss. *)
    (*   punfold LSIM0. eapply lsim_mon. *)
    (* } *)

    (* { clarify. clear IH rr. *)
    (*   unfold interp_all at 2. rewrite_cE_r. *)
    (*   rewrite interp_sched_yield. rewrite interp_sched_pick_yield2. *)
    (*   rewrite interp_state_tau. rewrite interp_state_trigger. *)
    (*   guclo sim_indC_spec. econs 4. *)
    (*   guclo sim_indC_spec. econs 6. i. *)
    (*   guclo sim_indC_spec. econs 4. *)
  (*   (*destruct cases: UB case /  *)
   (*     x = tid: ind on o1, ind on LSIM0, trivial case: LSIM0, sync: case analysis: IHo1|CIH / *)
   (*     x <> tid: CIH, LOCAL*) *)
    (*   des_ifs. *)
    (*   2:{ admit. } *)
    (*   destruct (tid_dec x tid) eqn:TID. *)
    (*   { clarify. eapply IHo. eauto. 1,2,3: admit. *)
    (*     admit. *)
    (*   } *)
    (*   unfold interp_all at 1. rewrite_cE_l. *)
    (*   rewrite interp_sched_yield. rewrite interp_sched_pick_yield2. *)
    (*   rewrite interp_state_tau. rewrite interp_state_trigger. *)
    (*   guclo sim_indC_spec. econs 3. *)
    (*   guclo sim_indC_spec. econs 5. exists x. *)
    (*   guclo sim_indC_spec. econs 3. *)
    (*   (* make lemma for th_pop *) *)
    (*   des_ifs. *)
    (*   2:{ admit. } *)
    (*   hexploit LOCAL. *)
    (*   { instantiate (1:=t1). instantiate (1:=x). admit. } *)
    (*   { instantiate (1:=t). admit. } *)
    (*   intros LSIM. unfold local_sim in LSIM. hexploit LSIM. 3: eauto. *)
    (*   { instantiate (1:=x). admit. } *)
    (*   { admit. } *)
    (*   clear LSIM; intro LSIM. *)



    
    (*   gfold. econs 9. right. eapply CIH; ss; auto. all: ss. *)
    (*   1,2,3: admit. *)
    


    
    (*     match goal with *)
    (*     | |- gpaco9 _ _ _ _ _ _ _ _ _ _ _ _ (interp_state (_, trigger ?EV >>= Tau (interp_sched ?a))) => *)
    (*         replace (trigger EV >>= Tau (interp_sched a)) with (x <- trigger EV >>= Tau (interp_sched a)) *)
    (*     end; auto; rewrite <- interp_sched_eventE_trigger. *)

    (*     push_eventE_r. *)

    
    (*     rewrite interp_state_trigger. *)
    (*     rewrite bind_trigger. rewrite <- interp_sched_eventE_trigger. *)
    (*     rewrite interp_sched_tau. *)

    (*   admit. } *)

    (* { des. clarify. destruct LSIM as [LSIM IND]. clear LSIM. *)
    (*   unfold interp_all at 1. rewrite_cE_l. *)
    (*   rewrite interp_sched_yield. rewrite interp_sched_pick_yield. *)
    (*   rewrite interp_state_tau. rewrite interp_state_trigger. *)
    (*   guclo sim_indC_spec. econs 3. *)
    (*   guclo sim_indC_spec. econs 5. exists tid. *)
    (*   guclo sim_indC_spec. econs 3. *)
    (*   (* lemma for th_pop, etc., induction *) *)
    (*   admit. *)
    (* } *)

    (* { clarify. pclearbot. gfold. econs 9; auto. *)
    (*   clear IH rr. *)
    (*   right. eapply CIH; auto. eauto. *)
    (* } *)

  (* Abort. *)

  (* Ltac pull_tau := rewrite interp_sched_tau; rewrite interp_state_tau. *)

  (* Ltac pull_eventE_l := *)
  (*   match goal with *)
  (*   | |- gpaco9 _ _ _ _ _ _ _ _ _ _ _ (interp_state (_, interp_sched (_, inl (_, trigger ?EV >>= ?ktr)))) _ => replace (trigger EV >>= ktr) with (trigger (inl1 (inl1 EV)) >>= ktr) *)
  (*   end; auto; rewrite interp_sched_eventE_trigger; rewrite interp_state_trigger. *)

  (* Ltac pull_eventE_r := *)
  (*   match goal with *)
  (*   | |- gpaco9 _ _ _ _ _ _ _ _ _ _ _ _ (interp_state (_, interp_sched (_, inl (_, trigger ?EV >>= ?ktr)))) => replace (trigger EV >>= ktr) with (trigger (inl1 (inl1 EV)) >>= ktr) *)
  (*   end; auto; rewrite interp_sched_eventE_trigger; rewrite interp_state_trigger. *)

  (* Ltac pull_sE_l := *)
  (*   match goal with *)
  (*   | |- gpaco9 _ _ _ _ _ _ _ _ _ _ _ (interp_state (_, interp_sched (_, inl (_, trigger ?EV >>= ?ktr)))) _ => replace (trigger EV >>= ktr) with (trigger (inr1 EV) >>= ktr) *)
  (*   end; auto; rewrite interp_sched_trigger. *)

  (* Ltac pull_sE_r := *)
  (*   match goal with *)
  (*   | |- gpaco9 _ _ _ _ _ _ _ _ _ _ _ _ (interp_state (_, interp_sched (_, inl (_, trigger ?EV >>= ?ktr)))) => replace (trigger EV >>= ktr) with (trigger (inr1 EV) >>= ktr) *)
  (*   end; auto; rewrite interp_sched_trigger. *)

  (* Ltac rewrite_cE_l := *)
  (*   match goal with *)
  (*   | |- gpaco9 _ _ _ _ _ _ _ _ _ _ _ (interp_state (_, interp_sched (_, inl (_, trigger ?EV >>= ?ktr)))) _ => replace (trigger EV >>= ktr) with (trigger (inl1 (inr1 EV)) >>= ktr) *)
  (*   end; auto. *)

  (* Ltac rewrite_cE_r := *)
  (*   match goal with *)
  (*   | |- gpaco9 _ _ _ _ _ _ _ _ _ _ _ _ (interp_state (_, interp_sched (_, inl (_, trigger ?EV >>= ?ktr)))) => replace (trigger EV >>= ktr) with (trigger (inl1 (inr1 EV)) >>= ktr) *)
  (*   end; auto. *)



  Lemma ksim_implies_gsim
        R0 R1 (RR: R0 -> R1 -> Prop)
        (ths_src: threads_src2 R0)
        (ths_tgt: threads_tgt R1)
        tid
        (THSRC: Th.find tid ths_src = None)
        (THTGT: Th.find tid ths_tgt = None)
        (WF: th_wf_pair (Th.add tid src_default2 ths_src) (Th.add tid tgt_default ths_tgt))
        sf src tgt
        (st_src: state_src) (st_tgt: state_tgt)
        ps pt
        o w
        (KSIM: forall im_tgt, exists im_src,
            sim_knot RR ths_src ths_tgt tid ps pt (sf, src) tgt
                     (th_proj1 (Th.add tid src_default2 ths_src), th_proj1 (Th.add tid tgt_default ths_tgt),
                       im_src, im_tgt, st_src, st_tgt, o, w))
    :
    gsim wf_src wf_tgt RR ps pt
         (interp_all st_src (th_proj_v2 ths_src) tid src)
         (interp_all st_tgt ths_tgt tid tgt).
  Proof.
    ii. specialize (KSIM mt). des. rename im_src into ms. exists ms.


  Abort.

  (* Permutation ths_src0 ths_src1 /\ Permutation ths_tgt0 ths_tgt1 /\ I (ths_src0, ths_tgt0, ...) -> I (ths_src1, ths_tgt1, ...). *)


  (* Lemma ths_find_none_ths_pop_some: *)
  (*   Th.find tid ths = None /\ th_pop t ths <> None *)
  (*   -> t <> tid. *)
  (* Abort. *)

  (* Lemma ths_find_none_tlist_remove: *)
  (*   Th.find tid ths = None /\ tid_list_remove (tid :: alist_proj1 ths) tid tl *)
  (*   -> tl = alist_proj1 ths. *)
  (* Abort. *)

  (* Lemma perm_ths_pop: *)
  (*   Permutation (alist_proj1 ths1) (alist_proj1 ths2) /\ th_pop tid ths1 = Some (th1, ths3) *)
  (*   -> exists th1 ths4, th_pop tid ths2 = Some (th1, ths4) /\ *)
  (*                   Permutation (alist_proj1 ths3) (alist_proj1 ths4). *)
  (* Abort. *)

  (* Lemma ths_pop_cons_perm: *)
  (*   th_pop tid ths = Some (th, ths0) /\ List.NoDup (alist_proj1 ths) *)
  (*   -> Permutation (alist_proj1 ths) (tid :: alist_proj1 ths0). *)
  (* Abort. *)

  (* Lemma ths_pop_update_ths_eq: *)
  (*   List.NoDup (alist_proj1 ths) -> *)
  (*   th_pop tid (update_threads tid itr ths) = Some (itr, ths). *)
  (* Abort. *)

  (* Lemma ths_pop_update_ths_perm: *)
  (*   List.NoDup (alist_proj1 ths) /\ *)
  (*     th_pop t (update_threads tid itr ths) = Some (th, ths0) -> *)
  (*   Permutation (tid :: alist_proj1 ths) (t :: alist_proj1 ths0). *)
  (* Abort. *)


End ADEQ.
