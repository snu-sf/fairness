From sflib Require Import sflib.
From ITree Require Export ITree.
From Paco Require Import paco.

Require Export Coq.Strings.String.
Require Import Coq.Classes.RelationClasses.
Require Import Program.
Require Import Permutation.

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

  Lemma sim_yield_l_prog
        R0 R1 (RR: R0 -> R1 -> Prop)
        ps pt (ms: @imap ident_src wf_src) (mt: @imap ident_tgt wf_tgt)
        (tgt: @state ident_tgt R1)
        (st_src: state_src)
        (ths_src: @threads _ident_src (sE state_src) R0)
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
  Notation srcE := ((@eventE _ident_src +' cE) +' sE state_src).
  Notation tgtE := ((@eventE _ident_tgt +' cE) +' sE state_tgt).

  Variable world: Type.
  Variable world_le: world -> world -> Prop.
  Hypothesis world_le_PreOrder: PreOrder world_le.
  Program Instance wle_PreOrder: PreOrder world_le.

  Let shared := @shared state_src state_tgt _ident_src _ident_tgt wf_src wf_tgt world.

  Definition threads2 _id ev R := Th.t (prod bool (@thread _id ev R)).
  Notation threads_src1 R0 := (threads _ident_src (sE state_src) R0).
  Notation threads_src2 R0 := (threads2 _ident_src (sE state_src) R0).
  Notation threads_tgt R1 := (threads _ident_tgt (sE state_tgt) R1).

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
        ths0 tht0 o0 w0
        (THSR: tid_list_remove ths tid ths0)
        (THTR: tid_list_remove tht tid tht0)
        (WORLD: world_le w w0)
        (STUTTER: wf_src.(lt) o0 o)
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
                         forall ps pt, sim_knot thsl0 thsr0 tid0 ps pt
                                  (b, Vis (inl1 (inr1 Yield)) (fun _ => th_src))
                                  (th_tgt)
                                  (ths0, tht0, im_src, im_tgt0, st_src, st_tgt, o0, w0))) /\
                    ((b = false) ->
                     forall im_tgt0
                       (FAIR: fair_update im_tgt im_tgt0 (sum_fmap_l (tids_fmap tid0 tht0))),
                     exists im_src0,
                       (fair_update im_src im_src0 (sum_fmap_l (tids_fmap tid0 ths0))) /\
                         (forall ps pt, sim_knot thsl0 thsr0 tid0 ps pt
                                   (b, th_src)
                                   th_tgt
                                   (ths0, tht0, im_src0, im_tgt0, st_src, st_tgt, o0, w0)))))
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
                             forall ps pt, sim_knot thsl1 thsr1 tid0 ps pt
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
                               (forall ps pt, sim_knot thsl1 thsr1 tid0 ps pt
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

  Lemma ksim_reset_prog
        R0 R1 (RR: R0 -> R1 -> Prop)
        ths_src ths_tgt tid
        ssrc tgt shr
        ps0 pt0 ps1 pt1
        (KSIM: sim_knot RR ths_src ths_tgt tid ps1 pt1 ssrc tgt shr)
        (SRC: ps1 = true -> ps0 = true)
        (TGT: pt1 = true -> pt0 = true)
    :
    sim_knot RR ths_src ths_tgt tid ps0 pt0 ssrc tgt shr.
  Proof.
    revert_until RR. pcofix CIH. i.
    move KSIM before CIH. revert_until KSIM. punfold KSIM.
    2:{ eapply ksim_mon. }
    eapply pind8_acc in KSIM.

    { instantiate (1:= (fun ths_src ths_tgt tid ps1 pt1 ssrc tgt shr =>
                          forall ps0 pt0 : bool,
                            (ps1 = true -> ps0 = true) ->
                            (pt1 = true -> pt0 = true) ->
                            paco8
                              (fun
                                  r0 : rel8 (threads_src2 R0) (fun _ : threads_src2 R0 => threads_tgt R1)
                                            (fun (_ : threads_src2 R0) (_ : threads_tgt R1) => id)
                                            (fun (_ : threads_src2 R0) (_ : threads_tgt R1) (_ : id) => bool)
                                            (fun (_ : threads_src2 R0) (_ : threads_tgt R1) (_ : id) (_ : bool) => bool)
                                            (fun (_ : threads_src2 R0) (_ : threads_tgt R1) (_ : id) (_ _ : bool) =>
                                               (bool * thread _ident_src (sE state_src) R0)%type)
                                            (fun (_ : threads_src2 R0) (_ : threads_tgt R1) (_ : id) (_ _ : bool) (_ : bool * thread _ident_src (sE state_src) R0)
                                             => thread _ident_tgt (sE state_tgt) R1)
                                            (fun (_ : threads_src2 R0) (_ : threads_tgt R1) (_ : id) (_ _ : bool) (_ : bool * thread _ident_src (sE state_src) R0)
                                               (_ : thread _ident_tgt (sE state_tgt) R1) => shared) => pind8 (__sim_knot RR r0) top8) r ths_src ths_tgt tid ps0
                              pt0 ssrc tgt shr)) in KSIM; auto. }

    ss. clear ths_src ths_tgt tid ps1 pt1 ssrc tgt shr KSIM.
    intros rr DEC IH ths_src ths_tgt tid ps1 pt1 ssrc tgt shr KSIM. clear DEC.
    intros ps0 pt0 SRC TGT.
    eapply pind8_unfold in KSIM.
    2:{ eapply _ksim_mon. }
    inv KSIM.

    { pfold. eapply pind8_fold. econs; eauto. }

    { clear rr IH. pfold. eapply pind8_fold. eapply ksim_ret_cont; eauto. i.
      specialize (KSIM0 tid0). des; eauto. right.
      esplits; eauto.
      - i; hexploit KSIM2; clear KSIM2 KSIM3; eauto. i. eapply upaco8_mon_bot; eauto.
      - i; hexploit KSIM3; clear KSIM2 KSIM3; eauto. i. des. esplits; eauto. i. eapply upaco8_mon_bot; eauto.
    }

    { clear rr IH. pfold. eapply pind8_fold. eapply ksim_sync; eauto. i.
      specialize (KSIM0 tid0). des; eauto. right.
      esplits; eauto.
      - i; hexploit KSIM2; clear KSIM2 KSIM3; eauto. i. des. esplits; eauto. i. eapply upaco8_mon_bot; eauto.
      - i; hexploit KSIM3; clear KSIM2 KSIM3; eauto. i. des. esplits; eauto. i. specialize (H2 _ FAIR); des.
        esplits; eauto. i. eapply upaco8_mon_bot; eauto.
    }

    { des. pfold. eapply pind8_fold. eapply ksim_yieldL. esplits; eauto. split; ss.
      destruct KSIM1 as [KSIM1 IND]. hexploit IH; eauto. i. punfold H. eapply ksim_mon.
    }

    { pfold. eapply pind8_fold. eapply ksim_tauL. split; ss.
      destruct KSIM0 as [KSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply ksim_mon.
    }

    { des. pfold. eapply pind8_fold. eapply ksim_chooseL. esplits. split; ss.
      destruct KSIM0 as [KSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply ksim_mon.
    }

    { pfold. eapply pind8_fold. eapply ksim_putL. split; ss.
      destruct KSIM0 as [KSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply ksim_mon.
    }

    { pfold. eapply pind8_fold. eapply ksim_getL. split; ss.
      destruct KSIM0 as [KSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply ksim_mon.
    }

    { pfold. eapply pind8_fold. eapply ksim_tidL. split; ss.
      destruct KSIM0 as [KSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply ksim_mon.
    }

    { pfold. eapply pind8_fold. eapply ksim_UB. }

    { des. pfold. eapply pind8_fold. eapply ksim_fairL. esplits; eauto. split; ss.
      destruct KSIM1 as [KSIM1 IND]. hexploit IH; eauto. i. punfold H. eapply ksim_mon.
    }

    { pfold. eapply pind8_fold. eapply ksim_tauR. split; ss.
      destruct KSIM0 as [KSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply ksim_mon.
    }

    { pfold. eapply pind8_fold. eapply ksim_chooseR. i. split; ss. specialize (KSIM0 x).
      destruct KSIM0 as [KSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply ksim_mon.
    }

    { pfold. eapply pind8_fold. eapply ksim_putR. split; ss.
      destruct KSIM0 as [KSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply ksim_mon.
    }

    { pfold. eapply pind8_fold. eapply ksim_getR. split; ss.
      destruct KSIM0 as [KSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply ksim_mon.
    }

    { pfold. eapply pind8_fold. eapply ksim_tidR. split; ss.
      destruct KSIM0 as [KSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply ksim_mon.
    }

    { pfold. eapply pind8_fold. eapply ksim_fairR. i. split; ss. specialize (KSIM0 _ FAIR).
      destruct KSIM0 as [KSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply ksim_mon.
    }

    { pfold. eapply pind8_fold. eapply ksim_observe. i. specialize (KSIM0 ret). pclearbot.
      right; eapply CIH; eauto.
    }

    { hexploit SRC; ss; i; clarify. hexploit TGT; ss; i; clarify.
      pfold. eapply pind8_fold. eapply ksim_progress. pclearbot.
      right; eapply CIH; eauto.
    }

  Qed.

  Lemma ksim_set_prog
        R0 R1 (RR: R0 -> R1 -> Prop)
        ths_src ths_tgt tid
        ssrc tgt shr
        (KSIM: sim_knot RR ths_src ths_tgt tid true true ssrc tgt shr)
    :
    forall ps pt, sim_knot RR ths_src ths_tgt tid ps pt ssrc tgt shr.
  Proof.
    revert_until RR. pcofix CIH. i.
    remember true as ps1 in KSIM at 1. remember true as pt1 in KSIM at 1.
    move KSIM before CIH. revert_until KSIM. punfold KSIM.
    2:{ eapply ksim_mon. }
    eapply pind8_acc in KSIM.

    { instantiate (1:= (fun ths_src ths_tgt tid ps1 pt1 ssrc tgt shr =>
                          ps1 = true ->
                          pt1 = true ->
                          forall ps pt : bool,
                            paco8
                              (fun
                                  r0 : rel8 (threads_src2 R0) (fun _ : threads_src2 R0 => threads_tgt R1)
                                            (fun (_ : threads_src2 R0) (_ : threads_tgt R1) => id)
                                            (fun (_ : threads_src2 R0) (_ : threads_tgt R1) (_ : id) => bool)
                                            (fun (_ : threads_src2 R0) (_ : threads_tgt R1) (_ : id) (_ : bool) => bool)
                                            (fun (_ : threads_src2 R0) (_ : threads_tgt R1) (_ : id) (_ _ : bool) =>
                                               (bool * thread _ident_src (sE state_src) R0)%type)
                                            (fun (_ : threads_src2 R0) (_ : threads_tgt R1) (_ : id) (_ _ : bool) (_ : bool * thread _ident_src (sE state_src) R0)
                                             => thread _ident_tgt (sE state_tgt) R1)
                                            (fun (_ : threads_src2 R0) (_ : threads_tgt R1) (_ : id) (_ _ : bool) (_ : bool * thread _ident_src (sE state_src) R0)
                                               (_ : thread _ident_tgt (sE state_tgt) R1) => shared) => pind8 (__sim_knot RR r0) top8) r ths_src ths_tgt tid ps pt
                              ssrc tgt shr)) in KSIM; auto. }

    ss. clear ths_src ths_tgt tid ps1 pt1 ssrc tgt shr KSIM.
    intros rr DEC IH ths_src ths_tgt tid ps1 pt1 ssrc tgt shr KSIM. clear DEC.
    intros Eps1 Ept1 ps pt. clarify.
    eapply pind8_unfold in KSIM.
    2:{ eapply _ksim_mon. }
    inv KSIM.

    { pfold. eapply pind8_fold. econs; eauto. }

    { clear rr IH. pfold. eapply pind8_fold. eapply ksim_ret_cont; eauto. i.
      specialize (KSIM0 tid0). des; eauto. right.
      esplits; eauto.
      - i; hexploit KSIM2; clear KSIM2 KSIM3; eauto. i. eapply upaco8_mon_bot; eauto.
      - i; hexploit KSIM3; clear KSIM2 KSIM3; eauto. i. des. esplits; eauto. i. eapply upaco8_mon_bot; eauto.
    }

    { clear rr IH. pfold. eapply pind8_fold. eapply ksim_sync; eauto. i.
      specialize (KSIM0 tid0). des; eauto. right.
      esplits; eauto.
      - i; hexploit KSIM2; clear KSIM2 KSIM3; eauto. i. des. esplits; eauto. i. eapply upaco8_mon_bot; eauto.
      - i; hexploit KSIM3; clear KSIM2 KSIM3; eauto. i. des. esplits; eauto. i. specialize (H2 _ FAIR); des.
        esplits; eauto. i. eapply upaco8_mon_bot; eauto.
    }

    { des. pfold. eapply pind8_fold. eapply ksim_yieldL. esplits; eauto. split; ss.
      destruct KSIM1 as [KSIM1 IND]. hexploit IH; eauto. i. punfold H. eapply ksim_mon.
    }

    { pfold. eapply pind8_fold. eapply ksim_tauL. split; ss.
      destruct KSIM0 as [KSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply ksim_mon.
    }

    { des. pfold. eapply pind8_fold. eapply ksim_chooseL. esplits. split; ss.
      destruct KSIM0 as [KSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply ksim_mon.
    }

    { pfold. eapply pind8_fold. eapply ksim_putL. split; ss.
      destruct KSIM0 as [KSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply ksim_mon.
    }

    { pfold. eapply pind8_fold. eapply ksim_getL. split; ss.
      destruct KSIM0 as [KSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply ksim_mon.
    }

    { pfold. eapply pind8_fold. eapply ksim_tidL. split; ss.
      destruct KSIM0 as [KSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply ksim_mon.
    }

    { pfold. eapply pind8_fold. eapply ksim_UB. }

    { des. pfold. eapply pind8_fold. eapply ksim_fairL. esplits; eauto. split; ss.
      destruct KSIM1 as [KSIM1 IND]. hexploit IH; eauto. i. punfold H. eapply ksim_mon.
    }

    { pfold. eapply pind8_fold. eapply ksim_tauR. split; ss.
      destruct KSIM0 as [KSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply ksim_mon.
    }

    { pfold. eapply pind8_fold. eapply ksim_chooseR. i. split; ss. specialize (KSIM0 x).
      destruct KSIM0 as [KSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply ksim_mon.
    }

    { pfold. eapply pind8_fold. eapply ksim_putR. split; ss.
      destruct KSIM0 as [KSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply ksim_mon.
    }

    { pfold. eapply pind8_fold. eapply ksim_getR. split; ss.
      destruct KSIM0 as [KSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply ksim_mon.
    }

    { pfold. eapply pind8_fold. eapply ksim_tidR. split; ss.
      destruct KSIM0 as [KSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply ksim_mon.
    }

    { pfold. eapply pind8_fold. eapply ksim_fairR. i. split; ss. specialize (KSIM0 _ FAIR).
      destruct KSIM0 as [KSIM0 IND]. hexploit IH; eauto. i. punfold H. eapply ksim_mon.
    }

    { pfold. eapply pind8_fold. eapply ksim_observe. i. specialize (KSIM0 ret). pclearbot.
      right; eapply CIH; eauto.
    }

    { pclearbot. eapply paco8_mon_bot; eauto. eapply ksim_reset_prog. eauto. all: auto. }

  Qed.



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
    forall ths0 tht0 im_src0 im_tgt0 st_src0 st_tgt0 w0 o0
      (THS: tid_list_in tid ths0)
      (THT: tid_list_in tid tht0)
      (INV: I (ths0, tht0, im_src0, im_tgt0, st_src0, st_tgt0, o0, w0))
      (WORLD: world_le w w0)
      fs ft,
    forall im_tgt1 (FAIR: fair_update im_tgt0 im_tgt1 (sum_fmap_l (tids_fmap tid tht0))),
      (lsim
         world_le
         I
         (local_RR world_le I RR tid)
         tid
         fs ft
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
                            forall (st_src : state_src) (st_tgt : state_tgt) o (im_tgt : imap wf_tgt) (im_src : imap wf_src),
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
                  { etransitivity; eauto. }
                  specialize (SYNC _ _ _ _ _ _ _ _ THS THT INV0 WORLD1 fs ft _ FAIR0). auto.
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
            hexploit H2; eauto. 1,2: admit. i; des. esplits; eauto. i.
            rewrite PROJS, PROJT. right. eapply CIH.
            { i. hexploit LOCAL.
              3:{ i; des. split.
                  2:{ eapply H6. }
                  intro SYNC. eapply H5 in SYNC. ii. unfold local_sim_sync in SYNC.
                  assert (WORLD1: world_le w w0).
                  { etransitivity; eauto. }
                  specialize (SYNC _ _ _ _ _ _ _ _ THS THT INV0 WORLD1 fs ft _ FAIR0). auto.
              }
              1,2: admit.
            }
            1,2: admit.
            admit.
            rewrite <- PROJS, <- PROJT. eapply lsim_set_prog. eauto.
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
      pfold. eapply pind8_fold. rewrite bind_trigger. eapply ksim_fairL.
      exists im_src1. splits; eauto. split; ss.
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
            { etransitivity; eauto. }
            (* assert (STUTTER1: lt wf_src o0 o). *)
            (* { depgen o1. clear. i. admit. } *)
            specialize (SYNC _ _ _ _ _ _ _ _ THS THT INV0 WORLD1 fs ft _ FAIR0). auto.
          }
          hexploit LSIM0; eauto. reflexivity.
          i. pclearbot.
          match goal with
          | |- lsim _ _ _ tid _ _ ?_itr _ _ => assert (_itr = (x <- trigger Yield;; ktr_src x))
          end.
          { rewrite bind_trigger. f_equal. f_equal. extensionality x. destruct x. ss. }
          rewrite H3. eapply lsim_set_prog. auto.
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
            rewrite H3. eapply lsim_set_prog. auto.
          }
          { hexploit LOCAL.
            3:{ i; des. split.
                2:{ eapply H3. }
                intro SYNC. eapply H2 in SYNC. ii. unfold local_sim_sync in SYNC.
                assert (WORLD1: world_le w w0).
                { etransitivity; eauto. }
                specialize (SYNC _ _ _ _ _ _ _ _ THS THT INV0 WORLD1 fs ft _ FAIR0). auto.
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
                rewrite H7. eapply lsim_set_prog. auto.
              }
              { hexploit LOCAL.
                3:{ i; des. split.
                    2:{ eapply H7. }
                    intro SYNC. eapply H6 in SYNC. ii. unfold local_sim_sync in SYNC.
                    assert (WORLD1: world_le w w0).
                    { etransitivity; eauto. }
                    specialize (SYNC _ _ _ _ _ _ _ _ THS THT INV0 WORLD1 fs ft _ FAIR0). auto.
                }
                1,2: admit.
              }
            }
            1,2: admit.
            admit.
            rewrite <- PROJS, <- PROJT. eapply lsim_set_prog. eauto.
        }
        1,2: admit.
    }

    { des. clarify. destruct LSIM as [LSIM0 IND]. clear LSIM0.
      pfold. eapply pind8_fold. rewrite bind_trigger. eapply ksim_yieldL.
      esplits; eauto. split; ss.
      hexploit IH; eauto. i. punfold H. eapply ksim_mon.
    }

    { clarify. pclearbot. pfold. eapply pind8_fold. eapply ksim_progress. right. eapply CIH; eauto. }

  Admitted.


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
    ginit. revert_until RR. gcofix CIH. i.
    move o before CIH. revert_until o. induction (wf_src.(wf) o).
    clear H; rename x into o, H0 into IHo. i.
    match goal with
    | KSIM: sim_knot _ _ _ _ _ _ ?_src _ ?_shr |- _ => remember _src as ssrc; remember _shr as shr
    end.
    punfold KSIM.
    2:{ ii. eapply pind8_mon_gen; eauto. i. eapply __ksim_mon; eauto. }
    move KSIM before IHo. revert_until KSIM.
    (* move KSIM before CIH. revert_until KSIM. *)
    eapply pind8_acc in KSIM.

    { instantiate (1:= (fun ths_src ths_tgt tid ps pt ssrc tgt shr =>
                          Th.find (elt:=bool * thread _ident_src (sE state_src) R0) tid ths_src = None ->
                          Th.find (elt:=thread _ident_tgt (sE state_tgt) R1) tid ths_tgt = None ->
                          th_wf_pair (Th.add tid src_default2 ths_src) (Th.add tid tgt_default ths_tgt) ->
                          forall (sf : bool) (src : itree srcE R0) (st_src : state_src) (st_tgt : state_tgt)
                            (w : world) (mt : imap wf_tgt) (ms : imap wf_src),
                            ssrc = (sf, src) ->
                            shr =
                              (th_proj1 (Th.add tid src_default2 ths_src), th_proj1 (Th.add tid tgt_default ths_tgt), ms, mt,
                                st_src, st_tgt, o, w) ->
                            gpaco9 (_sim (wft:=wf_tgt)) (cpn9 (_sim (wft:=wf_tgt))) bot9 r R0 R1 RR ps ms pt mt
                                   (interp_all st_src (th_proj_v2 ths_src) tid src) (interp_all st_tgt ths_tgt tid tgt))) in KSIM; auto. }

    ss. clear ths_src ths_tgt tid ps pt ssrc tgt shr KSIM.
    intros rr DEC IH ths_src ths_tgt tid ps pt ssrc tgt shr KSIM. clear DEC.
    intros THSRC THTGT WF sf src st_src st_tgt w mt ms Essrc Eshr.
    eapply pind8_unfold in KSIM.
    2:{ eapply _ksim_mon. }
    inv KSIM.

    { clarify. clear rr IH IHo.
      unfold interp_all. rewrite ! unfold_interp_sched. rewrite ! interp_thread_ret.
      ired. rewrite ! pick_thread_nondet_terminate.
      destruct (Th.is_empty (th_proj_v2 ths_src)) eqn:EMPS.
      { destruct (Th.is_empty ths_tgt) eqn:EMPT.
        { ired. rewrite ! interp_state_ret. guclo sim_indC_spec. eapply sim_indC_ret. auto. }
        { exfalso. ss. }
      }
      { exfalso. admit. }
    }

    { clarify. clear rr IH.
      unfold interp_all. rewrite ! unfold_interp_sched. rewrite ! interp_thread_ret.
      ired. rewrite ! pick_thread_nondet_terminate.
      destruct (Th.is_empty (th_proj_v2 ths_src)) eqn:EMPS.
      { exfalso. admit. }
      { destruct (Th.is_empty ths_tgt) eqn:EMPT.
        { ss. }
        { rewrite ! bind_vis.
          match goal with
          | |- gpaco9 _ _ _ _ _ _ _ _ _ _ _ ?_src_temp _ => remember _src_temp as src_temp eqn:TEMP
          end.
          rewrite interp_state_vis. rewrite <- ! bind_trigger.
          guclo sim_indC_spec. eapply sim_indC_chooseR. intro tid0.
          guclo sim_indC_spec. eapply sim_indC_tauR.
          assert (WF0: th_wf_pair ths_src ths_tgt).
          { admit. }
          specialize (KSIM0 tid0). des.
          { rewrite KSIM1. ired. rewrite bind_trigger. rewrite interp_state_vis.
            rewrite <- bind_trigger.
            guclo sim_indC_spec. eapply sim_indC_chooseR. intro x; destruct x. }
          rewrite KSIM1. ired. rewrite interp_state_vis. rewrite <- bind_trigger.
          guclo sim_indC_spec. eapply sim_indC_fairR. i. rewrite interp_state_tau.
          do 2 (guclo sim_indC_spec; eapply sim_indC_tauR).
          destruct b.

          - hexploit KSIM2; clear KSIM2 KSIM3; ss.
            assert (FMT: tids_fmap tid0 tht0 = tids_fmap tid0 (th_proj1 thsr0)).
            { admit. }
            rewrite FMT. eauto. i; pclearbot.
            assert (CHANGE: src_temp = interp_state (st_src, interp_sched (tid0, Vis ((|Yield)|)%sum (fun _ : () => th_src), th_proj_v2 thsl0))).
            { rewrite unfold_interp_sched. rewrite interp_thread_vis_yield. ired.
              rewrite pick_thread_nondet_yield. rewrite TEMP.
              replace (th_proj_v2 ths_src) with (Th.add tid0 th_src (th_proj_v2 thsl0)).
              grind.
              revert KSIM0. clear; i. admit.
            }
            rewrite CHANGE; clear CHANGE.
            assert (PROJS: th_proj1 (Th.add tid0 src_default2 thsl0) = ths0).
            { admit. }
            assert (PROJT: th_proj1 (Th.add tid0 tgt_default thsr0) = tht0).
            { admit. }
            eapply IHo. eauto.
            1,2: admit.
            admit.
            rewrite PROJS, PROJT. punfold H. eapply ksim_mon.

          - hexploit KSIM3; clear KSIM2 KSIM3; ss.
            assert (FMT: tids_fmap tid0 tht0 = tids_fmap tid0 (th_proj1 thsr0)).
            { admit. }
            rewrite FMT. eauto. i; pclearbot.
            des. clarify.
            rewrite interp_state_vis. rewrite <- bind_trigger.
            guclo sim_indC_spec. eapply sim_indC_chooseL. exists tid0.
            guclo sim_indC_spec. eapply sim_indC_tauL.
            assert (POPS: th_pop tid0 (th_proj_v2 ths_src) = Some (th_src, th_proj_v2 thsl0)).
            { admit. }
            rewrite POPS. rewrite bind_vis. rewrite interp_state_vis. rewrite <- bind_trigger.
            guclo sim_indC_spec. eapply sim_indC_fairL.
            assert (FMS: tids_fmap tid0 (th_proj1 (th_proj_v2 thsl0)) = tids_fmap tid0 ths0).
            { admit. }
            esplits; eauto. rewrite FMS; eauto.
            ired. rewrite interp_state_tau.
            do 2 (guclo sim_indC_spec; eapply sim_indC_tauL).
            specialize (H0 false false). pclearbot.
            gfold. eapply sim_progress. right. eapply CIH.
            1,2: admit.
            admit.
            assert (PROJS: th_proj1 (Th.add tid0 src_default2 thsl0) = ths0).
            { admit. }
            assert (PROJT: th_proj1 (Th.add tid0 tgt_default thsr0) = tht0).
            { admit. }
            rewrite PROJS, PROJT. eauto.
            all: auto.
        }
      }
    }

    { clarify. clear rr IH. unfold interp_all.
      match goal with
      | |- gpaco9 _ _ _ _ _ _ _ _ _ _ _ ?_src_temp _ => remember _src_temp as src_temp eqn:TEMP
      end.
      rewrite ! unfold_interp_sched. rewrite ! interp_thread_vis_yield.
      ired. rewrite ! pick_thread_nondet_yield.
      rewrite ! bind_vis. rewrite interp_state_vis. rewrite <- ! bind_trigger.
      guclo sim_indC_spec. eapply sim_indC_chooseR. intro tid0.
      guclo sim_indC_spec. eapply sim_indC_tauR.
      specialize (KSIM0 tid0). des.
      { rewrite KSIM1. ired. rewrite bind_trigger. rewrite interp_state_vis.
        rewrite <- bind_trigger.
        guclo sim_indC_spec. eapply sim_indC_chooseR. intro x; destruct x. }
      rewrite KSIM1. ired. rewrite interp_state_vis. rewrite <- bind_trigger.
      guclo sim_indC_spec. eapply sim_indC_fairR. i. rewrite interp_state_tau.
      do 2 (guclo sim_indC_spec; eapply sim_indC_tauR).
      destruct b.

      - hexploit KSIM2; clear KSIM2 KSIM3; ss.
        i; des.
        assert (CHANGE: src_temp = interp_state (st_src, interp_sched (tid0, Vis ((|Yield)|)%sum (fun _ : () => th_src), th_proj_v2 thsl1))).
        { rewrite unfold_interp_sched. rewrite interp_thread_vis_yield. ired.
          rewrite pick_thread_nondet_yield. rewrite TEMP.
          rewrite unfold_interp_sched. rewrite interp_thread_vis_yield. ired. rewrite pick_thread_nondet_yield. ired.
          replace (Th.add tid (ktr_src ()) (th_proj_v2 ths_src)) with (Th.add tid0 th_src (th_proj_v2 thsl1)). ss.
          revert KSIM0. clear; i. admit.
        }
        rewrite CHANGE; clear CHANGE.
        assert (tids_fmap tid0 (th_proj1 thsr1) = tids_fmap tid0 (th_proj1 (Th.add tid tgt_default ths_tgt))).
        { admit. }
        hexploit H1; clear H1. rewrite <- H2; eauto. i; pclearbot.
        assert (PROJS: th_proj1 (Th.add tid src_default2 ths_src) = th_proj1 (Th.add tid0 src_default2 thsl1)).
        { admit. }
        assert (PROJT: th_proj1 (Th.add tid tgt_default ths_tgt) = th_proj1 (Th.add tid0 tgt_default thsr1)).
        { admit. }
        eapply IHo; eauto.
        1,2: admit.
        admit.
        rewrite <- PROJS, <- PROJT; eauto.

      - hexploit KSIM3; clear KSIM2 KSIM3; ss.
        i; des. clarify.
        rewrite unfold_interp_sched. rewrite interp_thread_vis_yield. ired. rewrite pick_thread_nondet_yield. ired.
        rewrite interp_state_vis. rewrite <- bind_trigger.
        guclo sim_indC_spec. eapply sim_indC_chooseL. exists tid0.
        guclo sim_indC_spec. eapply sim_indC_tauL.
        assert (POPS: th_pop tid0 (Th.add tid (ktr_src ()) (th_proj_v2 ths_src)) = Some (th_src, th_proj_v2 thsl1)).
        { admit. }
        rewrite POPS. rewrite bind_vis. rewrite interp_state_vis. rewrite <- bind_trigger.
        guclo sim_indC_spec. eapply sim_indC_fairL.
        assert (FMT: tids_fmap tid0 (th_proj1 thsr1) = tids_fmap tid0 (th_proj1 (Th.add tid tgt_default ths_tgt))).
        { admit. }
        hexploit H1; clear H1. rewrite <- FMT; eauto. i; des; pclearbot.
        assert (FMS: tids_fmap tid0 (th_proj1 (th_proj_v2 thsl1)) = tids_fmap tid0 (th_proj1 (Th.add tid src_default2 ths_src))).
        { admit. }
        esplits; eauto. rewrite FMS; eauto.
        ired. rewrite interp_state_tau.
        do 2 (guclo sim_indC_spec; eapply sim_indC_tauL).
        specialize (H2 false false).
        eapply IHo; eauto.
        1,2: admit.
        admit.
        assert (PROJS: th_proj1 (Th.add tid src_default2 ths_src) = th_proj1 (Th.add tid0 src_default2 thsl1)).
        { admit. }
        assert (PROJT: th_proj1 (Th.add tid tgt_default ths_tgt) = th_proj1 (Th.add tid0 tgt_default thsr1)).
        { admit. }
        rewrite <- PROJS, <- PROJT. eapply ksim_reset_prog; eauto.
    }

    { des; clarify. destruct KSIM1 as [KSIM1 IND].
      assert (KSIM: sim_knot RR ths_src ths_tgt tid true pt
                             (false, ktr_src ()) tgt
                             (th_proj1 (Th.add tid src_default2 ths_src),
                               th_proj1 (Th.add tid tgt_default ths_tgt), im_src0, mt, st_src, st_tgt, o1, w)).
      { pfold. eapply pind8_mon_top; eauto. }
      unfold interp_all. rewrite unfold_interp_sched. rewrite interp_thread_vis_yield.
      ired. rewrite pick_thread_nondet_yield. ired.
      rewrite interp_state_vis. rewrite <- bind_trigger.
      guclo sim_indC_spec. eapply sim_indC_chooseL. exists tid.
      guclo sim_indC_spec. eapply sim_indC_tauL.
      assert (POPS: th_pop tid (Th.add tid (ktr_src ()) (th_proj_v2 ths_src)) = Some (ktr_src (), th_proj_v2 ths_src)).
      { admit. }
      rewrite POPS; clear POPS. rewrite bind_vis.
      rewrite interp_state_vis. rewrite <- bind_trigger.
      guclo sim_indC_spec. eapply sim_indC_fairL.
      assert (FMS: tids_fmap tid (th_proj1 (th_proj_v2 ths_src)) = tids_fmap tid (th_proj1 (Th.add tid src_default2 ths_src))).
      { admit. }
      rewrite FMS; clear FMS. esplits; eauto. ired. rewrite interp_state_tau.
      do 2 (guclo sim_indC_spec; eapply sim_indC_tauL).

      clear - I CIH THSRC THTGT WF KSIM. rename o1 into o.
      remember (ktr_src ()) as src. clear Heqsrc ktr_src. rename im_src0 into ms.
      match goal with
      | KSIM: sim_knot _ _ _ _ _ _ ?_src _ ?_shr |- _ => remember _src as ssrc; remember _shr as shr
      end.
      remember true as ps in KSIM.
      punfold KSIM.
      2:{ ii. eapply pind8_mon_gen; eauto. i. eapply __ksim_mon; eauto. }
      move KSIM before CIH. revert_until KSIM.
      eapply pind8_acc in KSIM.

      { instantiate (1:= (fun ths_src ths_tgt tid ps pt ssrc tgt shr =>
                            Th.find (elt:=bool * thread _ident_src (sE state_src) R0) tid ths_src = None ->
                            Th.find (elt:=thread _ident_tgt (sE state_tgt) R1) tid ths_tgt = None ->
                            th_wf_pair (Th.add tid src_default2 ths_src) (Th.add tid tgt_default ths_tgt) ->
                            forall (st_src : state_src) (st_tgt : state_tgt) (w : world) (mt : imap wf_tgt) (ms : imap wf_src) (o : T wf_src)
                              (src : thread _ident_src (sE state_src) R0),
                              ssrc = (false, src) ->
                              shr = (th_proj1 (Th.add tid src_default2 ths_src), th_proj1 (Th.add tid tgt_default ths_tgt), ms, mt, st_src, st_tgt, o, w) ->
                              ps = true ->
                              gpaco9 (_sim (wft:=wf_tgt)) (cpn9 (_sim (wft:=wf_tgt))) bot9 r R0 R1 RR true ms pt mt
                                     (interp_state (st_src, interp_sched (tid, src, th_proj_v2 ths_src))) (interp_state (st_tgt, interp_sched (tid, tgt, ths_tgt))))) in KSIM; auto. }

      ss. clear ths_src ths_tgt tid ps pt ssrc tgt shr KSIM.
      intros rr DEC IH ths_src ths_tgt tid ps pt ssrc tgt shr KSIM. clear DEC.
      intros THSRC THTGT WF st_src st_tgt w mt ms o src Essrc Eshr Eps.
      clarify.
      eapply pind8_unfold in KSIM.
      2:{ eapply _ksim_mon. }
      inv KSIM.

      { clear rr IH.
        rewrite ! unfold_interp_sched. rewrite ! interp_thread_ret.
        ired. rewrite ! pick_thread_nondet_terminate.
        destruct (Th.is_empty (th_proj_v2 ths_src)) eqn:EMPS.
        { destruct (Th.is_empty ths_tgt) eqn:EMPT.
          { ired. rewrite ! interp_state_ret. guclo sim_indC_spec. eapply sim_indC_ret. auto. }
          { exfalso. ss. }
        }
        { exfalso. admit. }
      }

      { clear rr IH.
        rewrite ! unfold_interp_sched. rewrite ! interp_thread_ret.
        ired. rewrite ! pick_thread_nondet_terminate.
        destruct (Th.is_empty (th_proj_v2 ths_src)) eqn:EMPS.
        { exfalso. admit. }
        { destruct (Th.is_empty ths_tgt) eqn:EMPT.
          { ss. }
          { rewrite ! bind_vis.
            match goal with
            | |- gpaco9 _ _ _ _ _ _ _ _ _ _ _ ?_src_temp _ => remember _src_temp as src_temp eqn:TEMP
            end.
            rewrite interp_state_vis. rewrite <- ! bind_trigger.
            guclo sim_indC_spec. eapply sim_indC_chooseR. intro tid0.
            guclo sim_indC_spec. eapply sim_indC_tauR.
            assert (WF0: th_wf_pair ths_src ths_tgt).
            { admit. }
            specialize (KSIM0 tid0). des.
            { rewrite KSIM1. ired. rewrite bind_trigger. rewrite interp_state_vis.
              rewrite <- bind_trigger.
              guclo sim_indC_spec. eapply sim_indC_chooseR. intro x; destruct x. }
            rewrite KSIM1. ired. rewrite interp_state_vis. rewrite <- bind_trigger.
            guclo sim_indC_spec. eapply sim_indC_fairR. i. rewrite interp_state_tau.
            do 2 (guclo sim_indC_spec; eapply sim_indC_tauR).
            destruct b.

            - hexploit KSIM2; clear KSIM2 KSIM3; ss.
              assert (FMT: tids_fmap tid0 tht0 = tids_fmap tid0 (th_proj1 thsr0)).
              { admit. }
              rewrite FMT. eauto. i; pclearbot.
              assert (CHANGE: src_temp = interp_state (st_src, interp_sched (tid0, Vis ((|Yield)|)%sum (fun _ : () => th_src), th_proj_v2 thsl0))).
              { rewrite unfold_interp_sched. rewrite interp_thread_vis_yield. ired.
                rewrite pick_thread_nondet_yield. rewrite TEMP.
                replace (th_proj_v2 ths_src) with (Th.add tid0 th_src (th_proj_v2 thsl0)).
                grind.
                revert KSIM0. clear; i. admit.
              }
              rewrite CHANGE; clear CHANGE.
              assert (PROJS: th_proj1 (Th.add tid0 src_default2 thsl0) = ths0).
              { admit. }
              assert (PROJT: th_proj1 (Th.add tid0 tgt_default thsr0) = tht0).
              { admit. }
              gfold. eapply sim_progress; auto. right. eapply CIH.
              1,2: admit.
              admit.
              rewrite PROJS, PROJT. eauto.

            - hexploit KSIM3; clear KSIM2 KSIM3; ss.
              assert (FMT: tids_fmap tid0 tht0 = tids_fmap tid0 (th_proj1 thsr0)).
              { admit. }
              rewrite FMT. eauto. i; pclearbot.
              des. clarify.
              rewrite interp_state_vis. rewrite <- bind_trigger.
              guclo sim_indC_spec. eapply sim_indC_chooseL. exists tid0.
              guclo sim_indC_spec. eapply sim_indC_tauL.
              assert (POPS: th_pop tid0 (th_proj_v2 ths_src) = Some (th_src, th_proj_v2 thsl0)).
              { admit. }
              rewrite POPS. rewrite bind_vis. rewrite interp_state_vis. rewrite <- bind_trigger.
              guclo sim_indC_spec. eapply sim_indC_fairL.
              assert (FMS: tids_fmap tid0 (th_proj1 (th_proj_v2 thsl0)) = tids_fmap tid0 ths0).
              { admit. }
              esplits; eauto. rewrite FMS; eauto.
              ired. rewrite interp_state_tau.
              do 2 (guclo sim_indC_spec; eapply sim_indC_tauL).
              specialize (H0 false false). pclearbot.
              gfold. eapply sim_progress. right. eapply CIH.
              1,2: admit.
              admit.
              assert (PROJS: th_proj1 (Th.add tid0 src_default2 thsl0) = ths0).
              { admit. }
              assert (PROJT: th_proj1 (Th.add tid0 tgt_default thsr0) = tht0).
              { admit. }
              rewrite PROJS, PROJT. eauto.
              all: auto.
          }
        }
      }

      { clear rr IH.
        match goal with
        | |- gpaco9 _ _ _ _ _ _ _ _ _ _ _ ?_src_temp _ => remember _src_temp as src_temp eqn:TEMP
        end.
        rewrite ! unfold_interp_sched. rewrite ! interp_thread_vis_yield.
        ired. rewrite ! pick_thread_nondet_yield.
        rewrite ! bind_vis. rewrite interp_state_vis. rewrite <- ! bind_trigger.
        guclo sim_indC_spec. eapply sim_indC_chooseR. intro tid0.
        guclo sim_indC_spec. eapply sim_indC_tauR.
        (* assert (WF0: th_wf_pair ths_src ths_tgt). *)
        (* { admit. } *)
        specialize (KSIM0 tid0). des.
        { rewrite KSIM1. ired. rewrite bind_trigger. rewrite interp_state_vis.
          rewrite <- bind_trigger.
          guclo sim_indC_spec. eapply sim_indC_chooseR. intro x; destruct x. }
        rewrite KSIM1. ired. rewrite interp_state_vis. rewrite <- bind_trigger.
        guclo sim_indC_spec. eapply sim_indC_fairR. i. rewrite interp_state_tau.
        do 2 (guclo sim_indC_spec; eapply sim_indC_tauR).
        destruct b.

        - hexploit KSIM2; clear KSIM2 KSIM3; ss.
          i; des.
          assert (CHANGE: src_temp = interp_state (st_src, interp_sched (tid0, Vis ((|Yield)|)%sum (fun _ : () => th_src), th_proj_v2 thsl1))).
          { rewrite unfold_interp_sched. rewrite interp_thread_vis_yield. ired.
            rewrite pick_thread_nondet_yield. rewrite TEMP.
            rewrite unfold_interp_sched. rewrite interp_thread_vis_yield. ired. rewrite pick_thread_nondet_yield. ired.
            replace (Th.add tid (ktr_src ()) (th_proj_v2 ths_src)) with (Th.add tid0 th_src (th_proj_v2 thsl1)). ss.
            revert KSIM0. clear; i. admit.
          }
          rewrite CHANGE; clear CHANGE.
          assert (tids_fmap tid0 (th_proj1 thsr1) = tids_fmap tid0 (th_proj1 (Th.add tid tgt_default ths_tgt))).
          { admit. }
          hexploit H1; clear H1. rewrite <- H2; eauto. i; pclearbot.
          assert (PROJS: th_proj1 (Th.add tid src_default2 ths_src) = th_proj1 (Th.add tid0 src_default2 thsl1)).
          { admit. }
          assert (PROJT: th_proj1 (Th.add tid tgt_default ths_tgt) = th_proj1 (Th.add tid0 tgt_default thsr1)).
          { admit. }
          gfold. eapply sim_progress; auto. right. eapply CIH.
          1,2: admit.
          admit.
          rewrite <- PROJS, <- PROJT; eauto.

        - hexploit KSIM3; clear KSIM2 KSIM3; ss.
          i; des. clarify.
          rewrite unfold_interp_sched. rewrite interp_thread_vis_yield. ired. rewrite pick_thread_nondet_yield. ired.
          rewrite interp_state_vis. rewrite <- bind_trigger.
          guclo sim_indC_spec. eapply sim_indC_chooseL. exists tid0.
          guclo sim_indC_spec. eapply sim_indC_tauL.
          assert (POPS: th_pop tid0 (Th.add tid (ktr_src ()) (th_proj_v2 ths_src)) = Some (th_src, th_proj_v2 thsl1)).
          { admit. }
          rewrite POPS. rewrite bind_vis. rewrite interp_state_vis. rewrite <- bind_trigger.
          guclo sim_indC_spec. eapply sim_indC_fairL.
          assert (FMT: tids_fmap tid0 (th_proj1 thsr1) = tids_fmap tid0 (th_proj1 (Th.add tid tgt_default ths_tgt))).
          { admit. }
          hexploit H1; clear H1. rewrite <- FMT; eauto. i; des; pclearbot.
          assert (FMS: tids_fmap tid0 (th_proj1 (th_proj_v2 thsl1)) = tids_fmap tid0 (th_proj1 (Th.add tid src_default2 ths_src))).
          { admit. }
          esplits; eauto. rewrite FMS; eauto.
          ired. rewrite interp_state_tau.
          do 2 (guclo sim_indC_spec; eapply sim_indC_tauL).
          specialize (H2 false false).
          gfold. eapply sim_progress. right. eapply CIH.
          1,2: admit.
          admit.
          assert (PROJS: th_proj1 (Th.add tid src_default2 ths_src) = th_proj1 (Th.add tid0 src_default2 thsl1)).
          { admit. }
          assert (PROJT: th_proj1 (Th.add tid tgt_default ths_tgt) = th_proj1 (Th.add tid0 tgt_default thsr1)).
          { admit. }
          rewrite <- PROJS, <- PROJT. eauto.
          all: auto.
      }

      { des. destruct KSIM1 as [KSIM1 IND].
        rewrite unfold_interp_sched. rewrite interp_thread_vis_yield. ired. rewrite pick_thread_nondet_yield. ired.
        rewrite interp_state_vis. rewrite <- bind_trigger.
        guclo sim_indC_spec. eapply sim_indC_chooseL. exists tid.
        replace (th_pop tid (Th.add tid (ktr_src ()) (th_proj_v2 ths_src))) with (Some (ktr_src (), th_proj_v2 ths_src)).
        2:{ admit. }
        rewrite bind_vis. guclo sim_indC_spec. eapply sim_indC_tauL.
        rewrite interp_state_vis. rewrite <- bind_trigger.
        guclo sim_indC_spec. eapply sim_indC_fairL.
        replace (tids_fmap tid (th_proj1 (th_proj_v2 ths_src))) with (tids_fmap tid (th_proj1 (Th.add tid src_default2 ths_src))).
        2:{ admit. }
        esplits; eauto. ired. rewrite interp_state_tau.
        do 2 (guclo sim_indC_spec; eapply sim_indC_tauL).
        eapply IH. eauto. all: auto.
      }

      { destruct KSIM0 as [KSIM0 IND].
        rewrite unfold_interp_sched. rewrite interp_thread_tau. ired. rewrite interp_state_tau. rewrite <- unfold_interp_sched.
        guclo sim_indC_spec. eapply sim_indC_tauL. eapply IH; eauto.
      }

      { des. destruct KSIM0 as [KSIM0 IND].
        rewrite unfold_interp_sched. rewrite interp_thread_vis_eventE. ired. rewrite interp_state_vis. rewrite <- bind_trigger.
        guclo sim_indC_spec. eapply sim_indC_chooseL. eexists.
        ired. rewrite interp_state_tau.
        do 2 (guclo sim_indC_spec; eapply sim_indC_tauL). rewrite <- unfold_interp_sched.
        eapply IH; eauto.
      }

      { destruct KSIM0 as [KSIM0 IND].
        rewrite unfold_interp_sched. rewrite interp_thread_vis. ired.
        rewrite interp_state_put_vis. ired. rewrite interp_state_tau.
        do 2 (guclo sim_indC_spec; eapply sim_indC_tauL). rewrite <- unfold_interp_sched.
        eapply IH; eauto.
      }

      { destruct KSIM0 as [KSIM0 IND].
        rewrite unfold_interp_sched. rewrite interp_thread_vis. ired.
        rewrite interp_state_get_vis. ired. rewrite interp_state_tau.
        do 2 (guclo sim_indC_spec; eapply sim_indC_tauL). rewrite <- unfold_interp_sched.
        eapply IH; eauto.
      }

      { destruct KSIM0 as [KSIM0 IND].
        rewrite unfold_interp_sched. rewrite interp_thread_vis_gettid. ired.
        rewrite interp_state_tau.
        do 1 (guclo sim_indC_spec; eapply sim_indC_tauL). rewrite <- unfold_interp_sched.
        eapply IH; eauto.
      }

      { rewrite unfold_interp_sched. rewrite interp_thread_vis_eventE. ired. rewrite interp_state_vis.
        rewrite <- bind_trigger. guclo sim_indC_spec. eapply sim_indC_ub.
      }

      { des. destruct KSIM1 as [KSIM1 IND].
        rewrite unfold_interp_sched. rewrite interp_thread_vis_eventE. ired. rewrite interp_state_vis. rewrite <- bind_trigger.
        guclo sim_indC_spec. eapply sim_indC_fairL. esplits; eauto.
        ired. rewrite interp_state_tau.
        do 2 (guclo sim_indC_spec; eapply sim_indC_tauL). rewrite <- unfold_interp_sched.
        eapply IH; eauto.
      }

      { destruct KSIM0 as [KSIM0 IND].
        rewrite (unfold_interp_sched (R:=R1)). rewrite interp_thread_tau. ired. rewrite interp_state_tau.
        rewrite <- unfold_interp_sched.
        guclo sim_indC_spec. eapply sim_indC_tauR. eapply IH; eauto.
      }

      { rewrite (unfold_interp_sched (R:=R1)). rewrite interp_thread_vis_eventE. ired. rewrite interp_state_vis.
        rewrite <- bind_trigger.
        guclo sim_indC_spec. eapply sim_indC_chooseR. i.
        ired. rewrite interp_state_tau.
        do 2 (guclo sim_indC_spec; eapply sim_indC_tauR). rewrite <- unfold_interp_sched.
        specialize (KSIM0 x). destruct KSIM0 as [KSIM0 IND].
        eapply IH; eauto.
      }

      { destruct KSIM0 as [KSIM0 IND].
        rewrite (unfold_interp_sched (R:=R1)). rewrite interp_thread_vis. ired.
        rewrite interp_state_put_vis. ired. rewrite interp_state_tau.
        do 2 (guclo sim_indC_spec; eapply sim_indC_tauR). rewrite <- unfold_interp_sched.
        eapply IH; eauto.
      }

      { destruct KSIM0 as [KSIM0 IND].
        rewrite (unfold_interp_sched (R:=R1)). rewrite interp_thread_vis. ired.
        rewrite interp_state_get_vis. ired. rewrite interp_state_tau.
        do 2 (guclo sim_indC_spec; eapply sim_indC_tauR). rewrite <- unfold_interp_sched.
        eapply IH; eauto.
      }

      { destruct KSIM0 as [KSIM0 IND].
        rewrite (unfold_interp_sched (R:=R1)). rewrite interp_thread_vis_gettid. ired.
        rewrite interp_state_tau.
        do 1 (guclo sim_indC_spec; eapply sim_indC_tauR). rewrite <- unfold_interp_sched.
        eapply IH; eauto.
      }

      { rewrite (unfold_interp_sched (R:=R1)). rewrite interp_thread_vis_eventE. ired. rewrite interp_state_vis.
        rewrite <- bind_trigger.
        guclo sim_indC_spec. eapply sim_indC_fairR. i.
        ired. rewrite interp_state_tau.
        do 2 (guclo sim_indC_spec; eapply sim_indC_tauR). rewrite <- unfold_interp_sched.
        specialize (KSIM0 _ FAIR). destruct KSIM0 as [KSIM0 IND].
        eapply IH; eauto.
      }

      { rewrite ! unfold_interp_sched. rewrite ! interp_thread_vis_eventE. ired. rewrite ! interp_state_vis.
        rewrite <- ! bind_trigger. guclo sim_indC_spec. eapply sim_indC_obs. i; clarify.
        ired. rewrite ! interp_state_tau.
        do 2 (guclo sim_indC_spec; eapply sim_indC_tauL; guclo sim_indC_spec; eapply sim_indC_tauR).
        rewrite <- ! unfold_interp_sched.
        gfold. eapply sim_progress; auto. right. eapply CIH; eauto.
        specialize (KSIM0 r_tgt). pclearbot. eapply ksim_set_prog. eauto.
      }

      { clear rr IH. gfold. eapply sim_progress. right; eapply CIH; eauto. pclearbot. eapply KSIM0. all: auto. }
    }

    { clarify. unfold interp_all.
      destruct KSIM0 as [KSIM0 IND].
      rewrite unfold_interp_sched. rewrite interp_thread_tau. ired. rewrite interp_state_tau. rewrite <- unfold_interp_sched.
      guclo sim_indC_spec. eapply sim_indC_tauL. eapply IH; eauto.
    }

    { clarify. unfold interp_all.
      des. destruct KSIM0 as [KSIM0 IND].
      rewrite unfold_interp_sched. rewrite interp_thread_vis_eventE. ired. rewrite interp_state_vis. rewrite <- bind_trigger.
      guclo sim_indC_spec. eapply sim_indC_chooseL. eexists.
      ired. rewrite interp_state_tau.
      do 2 (guclo sim_indC_spec; eapply sim_indC_tauL). rewrite <- unfold_interp_sched.
      eapply IH; eauto.
    }

    { clarify. unfold interp_all.
      destruct KSIM0 as [KSIM0 IND].
      rewrite unfold_interp_sched. rewrite interp_thread_vis. ired.
      rewrite interp_state_put_vis. ired. rewrite interp_state_tau.
      do 2 (guclo sim_indC_spec; eapply sim_indC_tauL). rewrite <- unfold_interp_sched.
      eapply IH; eauto.
    }

    { clarify. unfold interp_all.
      destruct KSIM0 as [KSIM0 IND].
      rewrite unfold_interp_sched. rewrite interp_thread_vis. ired.
      rewrite interp_state_get_vis. ired. rewrite interp_state_tau.
      do 2 (guclo sim_indC_spec; eapply sim_indC_tauL). rewrite <- unfold_interp_sched.
      eapply IH; eauto.
    }

    { clarify. unfold interp_all.
      destruct KSIM0 as [KSIM0 IND].
      rewrite unfold_interp_sched. rewrite interp_thread_vis_gettid. ired.
      rewrite interp_state_tau.
      do 1 (guclo sim_indC_spec; eapply sim_indC_tauL). rewrite <- unfold_interp_sched.
      eapply IH; eauto.
    }

    { clarify. unfold interp_all.
      rewrite unfold_interp_sched. rewrite interp_thread_vis_eventE. ired. rewrite interp_state_vis.
      rewrite <- bind_trigger. guclo sim_indC_spec. eapply sim_indC_ub.
    }

    { clarify. unfold interp_all.
      des. destruct KSIM1 as [KSIM1 IND].
      rewrite unfold_interp_sched. rewrite interp_thread_vis_eventE. ired. rewrite interp_state_vis. rewrite <- bind_trigger.
      guclo sim_indC_spec. eapply sim_indC_fairL. esplits; eauto.
      ired. rewrite interp_state_tau.
      do 2 (guclo sim_indC_spec; eapply sim_indC_tauL). rewrite <- unfold_interp_sched.
      eapply IH; eauto.
    }

    { clarify. unfold interp_all.
      destruct KSIM0 as [KSIM0 IND].
      rewrite (unfold_interp_sched (R:=R1)). rewrite interp_thread_tau. ired. rewrite interp_state_tau.
      rewrite <- unfold_interp_sched.
      guclo sim_indC_spec. eapply sim_indC_tauR. eapply IH; eauto.
    }

    { clarify. unfold interp_all.
      rewrite (unfold_interp_sched (R:=R1)). rewrite interp_thread_vis_eventE. ired. rewrite interp_state_vis.
      rewrite <- bind_trigger.
      guclo sim_indC_spec. eapply sim_indC_chooseR. i.
      ired. rewrite interp_state_tau.
      do 2 (guclo sim_indC_spec; eapply sim_indC_tauR). rewrite <- unfold_interp_sched.
      specialize (KSIM0 x). destruct KSIM0 as [KSIM0 IND].
      eapply IH; eauto.
    }

    { clarify. unfold interp_all.
      destruct KSIM0 as [KSIM0 IND].
      rewrite (unfold_interp_sched (R:=R1)). rewrite interp_thread_vis. ired.
      rewrite interp_state_put_vis. ired. rewrite interp_state_tau.
      do 2 (guclo sim_indC_spec; eapply sim_indC_tauR). rewrite <- unfold_interp_sched.
      eapply IH; eauto.
    }

    { clarify. unfold interp_all.
      destruct KSIM0 as [KSIM0 IND].
      rewrite (unfold_interp_sched (R:=R1)). rewrite interp_thread_vis. ired.
      rewrite interp_state_get_vis. ired. rewrite interp_state_tau.
      do 2 (guclo sim_indC_spec; eapply sim_indC_tauR). rewrite <- unfold_interp_sched.
      eapply IH; eauto.
    }

    { clarify. unfold interp_all.
      destruct KSIM0 as [KSIM0 IND].
      rewrite (unfold_interp_sched (R:=R1)). rewrite interp_thread_vis_gettid. ired.
      rewrite interp_state_tau.
      do 1 (guclo sim_indC_spec; eapply sim_indC_tauR). rewrite <- unfold_interp_sched.
      eapply IH; eauto.
    }

    { clarify. unfold interp_all.
      rewrite (unfold_interp_sched (R:=R1)). rewrite interp_thread_vis_eventE. ired. rewrite interp_state_vis.
      rewrite <- bind_trigger.
      guclo sim_indC_spec. eapply sim_indC_fairR. i.
      ired. rewrite interp_state_tau.
      do 2 (guclo sim_indC_spec; eapply sim_indC_tauR). rewrite <- unfold_interp_sched.
      specialize (KSIM0 _ FAIR). destruct KSIM0 as [KSIM0 IND].
      eapply IH; eauto.
    }

    { clarify. unfold interp_all.
      rewrite ! unfold_interp_sched. rewrite ! interp_thread_vis_eventE. ired. rewrite ! interp_state_vis.
      rewrite <- ! bind_trigger. guclo sim_indC_spec. eapply sim_indC_obs. i; clarify.
      ired. rewrite ! interp_state_tau.
      do 2 (guclo sim_indC_spec; eapply sim_indC_tauL; guclo sim_indC_spec; eapply sim_indC_tauR).
      rewrite <- ! unfold_interp_sched.
      gfold. eapply sim_progress; auto. right. eapply CIH; eauto.
      specialize (KSIM0 r_tgt). pclearbot. eapply ksim_set_prog. eauto.
    }

    { clarify. unfold interp_all.
      clear rr IH. gfold. eapply sim_progress. right; eapply CIH; eauto. pclearbot. eapply KSIM0. all: auto. }

  Admitted.

  Theorem lsim_implies_gsim
          R0 R1 (RR: R0 -> R1 -> Prop)
          (ths_src: threads_src1 R0)
          (ths_tgt: threads_tgt R1)
          (LOCAL: forall tid (src: itree srcE R0) (tgt: itree tgtE R1)
                    (LSRC: Th.find tid ths_src = Some src)
                    (LTGT: Th.find tid ths_tgt = Some tgt),
              (local_sim_pick RR src tgt tid))
          (WF: th_wf_pair ths_src ths_tgt)
          tid
          (FINDS: Th.find tid ths_src = None)
          (FINDT: Th.find tid ths_tgt = None)
          src tgt
          (st_src: state_src) (st_tgt: state_tgt) o w
          ps pt
          (LSIM: forall im_tgt, exists im_src,
              (<<INV: I (th_proj1 (Th.add tid src_default ths_src), th_proj1 (Th.add tid tgt_default ths_tgt),
                          im_src, im_tgt, st_src, st_tgt, o, w)>>) /\
                ((I (th_proj1 (Th.add tid src_default ths_src), th_proj1 (Th.add tid tgt_default ths_tgt),
                     im_src, im_tgt, st_src, st_tgt, o, w)) ->
              lsim world_le I (local_RR world_le I RR tid) tid ps pt src tgt
                   (th_proj1 (Th.add tid src_default ths_src), th_proj1 (Th.add tid tgt_default ths_tgt),
                     im_src, im_tgt, st_src, st_tgt, o, w)))
    :
    gsim wf_src wf_tgt RR ps pt
         (interp_all st_src ths_src tid src)
         (interp_all st_tgt ths_tgt tid tgt).
  Proof.
    remember (Th.map (fun th => (false, th)) ths_src) as ths_src2.
    assert (FINDS2: Th.find tid ths_src2 = None).
    { admit. }
    assert (WF0: th_wf_pair (Th.add tid src_default2 ths_src2) (Th.add tid tgt_default ths_tgt)).
    { admit. }
    replace ths_src with (th_proj_v2 ths_src2).
    2:{ admit. }
    eapply ksim_implies_gsim; auto.
    eapply lsim_implies_ksim; auto.
    { i. assert (SF: sf = false).
      { clarify. admit. }
      subst sf. split; i; ss. eapply LOCAL; auto.
      admit.
    }
    { replace (th_proj1 (Th.add tid src_default2 ths_src2)) with (th_proj1 (Th.add tid src_default ths_src)).
      i. specialize (LSIM im_tgt). des. eexists. eapply LSIM0; eauto.
      admit. }
    Unshelve. exact true.

  Abort.

End ADEQ.
