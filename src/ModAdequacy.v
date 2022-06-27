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



Section AUX.

  Variable E1: Type -> Type.
  Variable E2: Type -> Type.

  Variable _ident_src: ID.
  Variable _ident_tgt: ID.

  Definition wf_ths {R0 R1}
             (ths_src: @threads _ident_src E1 R0)
             (ths_tgt: @threads _ident_tgt E2 R1) :=
    List.NoDup (alist_proj1 ths_src) /\
      (* List.NoDup (alist_proj1 ths_tgt) /\ *)
      Permutation (alist_proj1 ths_src) (alist_proj1 ths_tgt).

  Lemma reldec_correct_tid_dec: RelDec.RelDec_Correct (RelDec.RelDec_from_dec eq tid_dec).
  Proof. eapply RelDec.RelDec_Correct_eq_typ. Qed.

  Lemma ths_find_none_tid_add
        R (ths: @threads _ident_src E1 R) tid
        (NONE: threads_find tid ths = None)
    :
    tid_list_add (alist_proj1 ths) tid (tid :: (alist_proj1 ths)).
  Proof.
    revert_until ths. induction ths; i; ss.
    { econs; ss. }
    des_ifs. ss. destruct (tid_dec tid n) eqn:TID.
    { clarify. eapply RelDec.neg_rel_dec_correct in Heq. ss. }
    eapply IHths in NONE. inv NONE. econs; ss.
    eapply List.not_in_cons. split; auto.
  Qed.

  Lemma ths_pop_find_none
        R (ths ths0: @threads _ident_src E1 R) th tid
        (POP: threads_pop tid ths = Some (th, ths0))
    :
    threads_find tid ths0 = None.
  Proof.
    unfold threads_pop, alist_pop in POP. des_ifs.
    unfold threads_find, threads_remove. eapply remove_eq_alist.
    eapply reldec_correct_tid_dec.
  Qed.

  Lemma ths_pop_find_some
        R (ths ths0: @threads _ident_src E1 R) th tid
        (POP: threads_pop tid ths = Some (th, ths0))
    :
    threads_find tid ths = Some th.
  Proof.
    unfold threads_pop, alist_pop in POP. des_ifs.
  Qed.

  Lemma ths_find_some_tid_in
        R (ths: @threads _ident_src E1 R) tid th
        (FIND: threads_find tid ths = Some th)
    :
    tid_list_in tid (alist_proj1 ths).
  Proof.
    revert_until ths. induction ths; i; ss. des_ifs; ss.
    - left. symmetry. eapply RelDec.rel_dec_correct. eauto.
    - right. eapply IHths. eauto.
      Unshelve. eapply reldec_correct_tid_dec.
  Qed.

  Lemma ths_wf_perm_pop_eq
        R (ths0 ths1: @threads _ident_src E1 R)
        (PERM: Permutation ths0 ths1)
        (WF0: threads_wf ths0)
        (* (WF1: threads_wf ths1) *)
    :
    forall x, ((threads_pop x ths0 = None) /\ (threads_pop x ths1 = None)) \/
           (exists th ths2 ths3, (threads_pop x ths0 = Some (th, ths2)) /\
                              (threads_pop x ths1 = Some (th, ths3)) /\
                              (Permutation ths2 ths3) /\ (threads_wf ths2)).
  Proof.
    i. unfold threads_wf, threads_pop in *. revert_until PERM. induction PERM; i; ss.
    { left. ss. }
    { inv WF0. specialize (IHPERM H2 x0). des.
      { destruct x as [tid th]. destruct (tid_dec x0 tid).
        { right. clarify. unfold alist_pop. ss. rewrite RelDec.rel_dec_eq_true; auto.
          2: apply reldec_correct_tid_dec. ss. esplits; eauto.
          admit.
          unfold alist_wf. admit.
        }
        { left. unfold alist_pop. ss. rewrite RelDec.rel_dec_neq_false; auto.
          2: apply reldec_correct_tid_dec. ss.
          unfold alist_pop in *. des_ifs; ss.
        }
      }
      { destruct x as [tid th0]. destruct (tid_dec x0 tid).
        { right. clarify. unfold alist_pop. ss. rewrite RelDec.rel_dec_eq_true; auto.
          2: apply reldec_correct_tid_dec. ss. esplits; eauto.
          admit.
          unfold alist_wf. admit.
        }
        { right. unfold alist_pop. ss. rewrite RelDec.rel_dec_neq_false; auto.
          2: apply reldec_correct_tid_dec. ss.
          unfold alist_pop in *. des_ifs; ss.
          esplits; eauto.
          unfold alist_wf. ss. eapply List.NoDup_cons.
          - ii. apply H1; clear H1. admit.
          - admit.
        }
      }
    }
    { admit. }
    { assert (WF1: alist_wf l').
      { admit. }
      specialize (IHPERM1 WF0 x). specialize (IHPERM2 WF1 x). des; clarify; eauto.
      right. esplits; eauto. eapply perm_trans; eauto.
    }
  Admitted.

End AUX.



Section ADEQ.

  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable _ident_src: ID.
  Definition ident_src := sum_tids _ident_src.
  Variable _ident_tgt: ID.
  Definition ident_tgt := sum_tids _ident_tgt.

  Variable wf_src: WF.
  Variable wf_tgt: WF.

  Ltac gfold := gfinal; right; pfold.

  Lemma sim_perm_l
        R0 R1 (RR: R0 -> R1 -> Prop)
        ps pt (ms: @imap ident_src wf_src) (mt: @imap ident_tgt wf_tgt)
        tgt
        (st_src: state_src)
        (ths_src0 ths_src1: @threads _ident_src (sE state_src) R0)
        (WF0: threads_wf ths_src0)
        (* (WF1: threads_wf ths_src1) *)
        (PERM: Permutation ths_src0 ths_src1)
        (SIM: sim RR ps ms pt mt
                  (interp_state
                     (st_src,
                       x <-
                         Vis (Choose tids.(id)|)%sum
                             (fun tid' : nat =>
                                match threads_pop tid' ths_src1 with
                                | Some (t', ts') =>
                                    Vis (Fair (sum_fmap_l (thread_fmap tid'))|)%sum
                                        (fun _ : () => Ret (inl (tid', t', ts')))
                                | None =>
                                    Vis (Choose void|)%sum
                                        (Empty_set_rect
                                           (fun _ : void =>
                                              itree (eventE +' sE state_src)
                                                    (nat * itree ((eventE +' cE) +' sE state_src) R0 *
                                                       alist nat (itree ((eventE +' cE) +' sE state_src) R0) + R0)))
                                end);; match x with
                                       | inl tts => Tau (interp_sched tts)
                                       | inr r => Ret r
                                       end)) tgt)
    :
    sim RR ps ms pt mt
        (interp_state
           (st_src,
             x <-
               Vis (Choose tids.(id)|)%sum
                   (fun tid' : nat =>
                      match threads_pop tid' ths_src0 with
                      | Some (t', ts') =>
                          Vis (Fair (sum_fmap_l (thread_fmap tid'))|)%sum
                              (fun _ : () => Ret (inl (tid', t', ts')))
                      | None =>
                          Vis (Choose void|)%sum
                              (Empty_set_rect
                                 (fun _ : void =>
                                    itree (eventE +' sE state_src)
                                          (nat * itree ((eventE +' cE) +' sE state_src) R0 *
                                             alist nat (itree ((eventE +' cE) +' sE state_src) R0) + R0)))
                      end);; match x with
                             | inl tts => Tau (interp_sched tts)
                             | inr r => Ret r
                             end)) tgt.
  Proof.
    revert SIM. ired. i. rewrite interp_state_vis in *.
    ginit. revert_until RR. gcofix CIH. i.
    match goal with
    | SIM: sim RR _ _ _ _ ?_itr_src _ |- _ =>
        remember _itr_src as itr_src
    end.
    move SIM before CIH. revert_until SIM. induction SIM using sim_ind2; i; ss; clarify.
    { guclo sim_indC_spec. econs 4. eapply IHSIM; eauto. }
    2:{ guclo sim_indC_spec. econs 6. i. specialize (SIM x). des. eapply IH; eauto. }
    2:{ rewrite bind_trigger in Heqitr_src. inv Heqitr_src. }
    2:{ guclo sim_indC_spec. econs 8. i. specialize (SIM m_tgt0 FAIR). des. eapply IH; eauto. }
    2:{ gfold. econs 9. right. eapply CIH; eauto. all: ss. }
    2:{ rewrite bind_trigger in Heqitr_src. inv Heqitr_src. }
    des. rewrite bind_trigger in Heqitr_src. inv Heqitr_src.
    guclo sim_indC_spec. rewrite <- bind_trigger. econs 5. exists x.
    eapply inj_pair2 in H2. hexploit (equal_f H2 x); clear H2. i. rewrite H in SIM0.
    eapply gpaco9_mon_bot; eauto with paco.
    revert SIM0 PERM WF0. clear. i. rename SIM0 into SIM.
    remember true as p_src. clear Heqp_src.
    revert_until RR. gcofix CIH. i.
    match goal with
    | SIM: sim RR _ _ _ _ ?_itr_src _ |- _ =>
        remember _itr_src as itr_src
    end.
    move SIM before CIH. revert_until SIM. induction SIM using sim_ind2; i; ss; clarify.
    2:{ guclo sim_indC_spec. econs 4. eapply IHSIM; eauto. }
    2:{ rewrite bind_trigger in Heqitr_src. inv Heqitr_src. }
    2:{ guclo sim_indC_spec. econs 6. i. specialize (SIM x0). des. eapply IH; eauto. }
    2:{ rewrite bind_trigger in Heqitr_src. inv Heqitr_src. }
    2:{ guclo sim_indC_spec. econs 8. i. specialize (SIM m_tgt0 FAIR). des. eapply IH; eauto. }
    2:{ gfold. econs 9. right. eapply CIH; eauto. all: ss. }
    2:{ rewrite bind_trigger in Heqitr_src. inv Heqitr_src. }
    guclo sim_indC_spec. rewrite <- bind_trigger. econs 3.
    eapply gpaco9_mon_bot; eauto with paco.
    revert SIM PERM WF0. clear. i.
    remember true as p_src. clear Heqp_src.
    hexploit (ths_wf_perm_pop_eq (sE state_src) (_ident_src) PERM WF0 x). i. des.
    { rewrite H. rewrite H0 in SIM. revert SIM. ired. clear. i.
      rewrite bind_trigger. rewrite interp_state_vis in *.
      revert_until RR. gcofix CIH. i.
      match goal with
      | SIM: sim RR _ _ _ _ ?_itr_src _ |- _ =>
          remember _itr_src as itr_src
      end.
      move SIM before CIH. revert_until SIM. induction SIM using sim_ind2; i; ss; clarify.
      { guclo sim_indC_spec. econs 4. eapply IHSIM; eauto. }
      { rewrite bind_trigger in Heqitr_src. inv Heqitr_src. des. destruct x. }
      { guclo sim_indC_spec. econs 6. i. specialize (SIM x). des. eapply IH; eauto. }
      { rewrite bind_trigger in Heqitr_src. inv Heqitr_src. }
      { guclo sim_indC_spec. econs 8. i. specialize (SIM m_tgt0 FAIR). des. eapply IH; eauto. }
      { gfold. econs 9. right. eapply CIH; eauto. all: ss. }
      { rewrite bind_trigger in Heqitr_src. inv Heqitr_src. }
    }
    rewrite H. rewrite H0 in SIM. clear H H0 WF0 PERM. rename H1 into PERM, H2 into WF.
    revert SIM. ired. i. rewrite interp_state_vis in *. revert SIM WF PERM. clear. i.
    revert_until RR. gcofix CIH. i.
    match goal with
    | SIM: sim RR _ _ _ _ ?_itr_src _ |- _ =>
        remember _itr_src as itr_src
    end.
    move SIM before CIH. revert_until SIM. induction SIM using sim_ind2; i; ss; clarify.
    { guclo sim_indC_spec. econs 4. eapply IHSIM; eauto. }
    { rewrite bind_trigger in Heqitr_src. inv Heqitr_src. }
    { guclo sim_indC_spec. econs 6. i. specialize (SIM x0). des. eapply IH; eauto. }
    2:{ guclo sim_indC_spec. econs 8. i. specialize (SIM m_tgt0 FAIR). des. eapply IH; eauto. }
    2:{ gfold. econs 9. right. eapply CIH; eauto. all: ss. }
    2:{ rewrite bind_trigger in Heqitr_src. inv Heqitr_src. }
    rewrite bind_trigger in Heqitr_src. inv Heqitr_src. des.
    eapply inj_pair2 in H1. hexploit (equal_f H1 tt); clear H1. i. rewrite H in SIM.
    guclo sim_indC_spec. rewrite <- bind_trigger. econs 7. esplits; eauto.
    eapply gpaco9_mon_bot; eauto with paco.
    revert SIM PERM WF. clear. i.
    remember true as p_src. clear Heqp_src.
    revert_until RR. gcofix CIH. i.
    match goal with
    | SIM: sim RR _ _ _ _ ?_itr_src _ |- _ =>
        remember _itr_src as itr_src
    end.
    move SIM before CIH. revert_until SIM. induction SIM using sim_ind2; i; ss; clarify.
    2:{ guclo sim_indC_spec. econs 4. eapply IHSIM; eauto. }
    2:{ rewrite bind_trigger in Heqitr_src. inv Heqitr_src. }
    2:{ guclo sim_indC_spec. econs 6. i. specialize (SIM x0). des. eapply IH; eauto. }
    2:{ rewrite bind_trigger in Heqitr_src. inv Heqitr_src. }
    2:{ guclo sim_indC_spec. econs 8. i. specialize (SIM m_tgt0 FAIR). des. eapply IH; eauto. }
    2:{ gfold. econs 9. right. eapply CIH; eauto. all: ss. }
    2:{ rewrite bind_trigger in Heqitr_src. inv Heqitr_src. }
    guclo sim_indC_spec. econs 3.
    eapply gpaco9_mon_bot; eauto with paco.
    revert SIM PERM WF. clear. i.
    rewrite interp_state_tau in *.
    remember true as p_src. clear Heqp_src.
    revert_until RR. gcofix CIH. i.
    match goal with
    | SIM: sim RR _ _ _ _ ?_itr_src _ |- _ =>
        remember _itr_src as itr_src
    end.
    move SIM before CIH. revert_until SIM. induction SIM using sim_ind2; i; ss; clarify.
    2:{ guclo sim_indC_spec. econs 4. eapply IHSIM; eauto. }
    2:{ rewrite bind_trigger in Heqitr_src. inv Heqitr_src. }
    2:{ guclo sim_indC_spec. econs 6. i. specialize (SIM x0). des. eapply IH; eauto. }
    2:{ rewrite bind_trigger in Heqitr_src. inv Heqitr_src. }
    2:{ guclo sim_indC_spec. econs 8. i. specialize (SIM m_tgt0 FAIR). des. eapply IH; eauto. }
    2:{ gfold. econs 9. right. eapply CIH; eauto. all: ss. }
    2:{ rewrite bind_trigger in Heqitr_src. inv Heqitr_src. }
    guclo sim_indC_spec. econs 3.
    eapply gpaco9_mon_bot; eauto with paco.
    revert SIM PERM WF. clear. i.
    rename x into tid, ths2 into ths0, ths3 into ths1, itr_tgt0 into itr_tgt.

  Admitted.

  Lemma sim_yieldL_change
        R0 R1 (RR: R0 -> R1 -> Prop)
        ps pt (ms: @imap ident_src wf_src) (mt: @imap ident_tgt wf_tgt)
        (st_src: state_src) (st_tgt: state_tgt)
        tid0 tid1 ths_tgt tgt
        (ths_src0 ths_src1: @threads _ident_src (sE state_src) R0)
        (ktr_src0: unit -> @thread _ident_src (sE state_src) R0)
        (src: @thread _ident_src (sE state_src) R0)
        (WF: threads_wf (threads_add tid0 (ktr_src0 tt) ths_src0))
        (POP: threads_pop tid1 (threads_add tid0 (ktr_src0 tt) ths_src0) = Some (src, ths_src1))
        (SIM: sim RR ps ms pt mt
                  (interp_all st_src ths_src1 tid1 (Vis (inl1 (inr1 Yield)) (fun _ => src)))
                  (interp_all st_tgt ths_tgt tid1 tgt))
    :
    sim RR ps ms pt mt
        (interp_all st_src ths_src0 tid0 (Vis (inl1 (inr1 Yield)) ktr_src0))
        (interp_all st_tgt ths_tgt tid1 tgt).
  Proof.
    unfold interp_all in *. rewrite unfold_interp_sched in *.
    unfold thread in *. rewrite interp_thread_vis_yield in *.
    rewrite bind_ret_l in *.
    pose (@pick_thread_nondet_yield _ident_src (sE state_src) R0).
    unfold thread in *. rewrite e. rewrite e in SIM. clear e.
    eapply sim_perm_l. 3: eauto. auto.
    revert POP WF. clear. i.

  Admitted.



  Let srcE := ((@eventE ident_src +' cE) +' sE state_src).
  Let tgtE := ((@eventE ident_tgt +' cE) +' sE state_tgt).
  Let gsrcE := @eventE ident_src.
  Let gtgtE := @eventE ident_tgt.

  Variable world: Type.
  Variable world_le: world -> world -> Prop.

  Let shared := @shared state_src state_tgt _ident_src _ident_tgt wf_src wf_tgt world.

  Definition threads2 _id ev R := alist tids.(id) (prod bool (@thread _id ev R)).
  Let threads_src R0 := threads2 _ident_src (sE state_src) R0.
  Let threads_tgt R1 := @threads _ident_tgt (sE state_tgt) R1.


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



  Variable I: shared -> Prop.

  (*invariant for tid_list & threads: tid_list_add threads.proj1 tid tid_list*)
  Theorem local_adequacy
          R0 R1 (RR: R0 -> R1 -> Prop)
          (ths_src: @threads _ident_src (sE state_src) R0)
          (ths_tgt: @threads _ident_tgt (sE state_tgt) R1)
          (* (WFTHS: wf_ths ths_src ths_tgt) *)
          (LOCAL: forall tid (src: itree srcE R0) (tgt: itree tgtE R1)
                    (LSRC: threads_find tid ths_src = Some src)
                    (LTGT: threads_find tid ths_tgt = Some tgt),
              (local_sim world_le I RR src tgt))
          tid
          (THSRC: threads_find tid ths_src = None)
          (THTGT: threads_find tid ths_tgt = None)
          src tgt
          (LSIM: local_sim world_le I RR src tgt)
          (st_src: state_src) (st_tgt: state_tgt)
          (INV: forall im_tgt, exists im_src o w,
              I (tid :: alist_proj1 ths_src, tid :: alist_proj1 ths_tgt, im_src, im_tgt, st_src, st_tgt, o, w))
          (* (INV: forall im_tgt, exists im_src o w, *)
          (*     I (tid :: alist_proj1 ths_src, tid :: alist_proj1 ths_tgt, im_src, im_tgt, st_src, st_tgt, o, w)) *)
          (* ths_src0 ths_tgt0 *)
          (* (THSRC: threads_pop tid ths_src = Some (src0, ths_src0)) *)
          (* (THTGT: threads_pop tid ths_tgt = Some (tgt0, ths_tgt0)) *)
          gps gpt
    :
    gsim wf_src wf_tgt RR gps gpt
         (interp_all st_src ths_src tid src)
         (interp_all st_tgt ths_tgt tid tgt).
  Proof.
    ii. specialize (INV mt). des. rename im_src into ms. exists ms.
    unfold local_sim in LSIM.
    hexploit LSIM; clear LSIM. 3: eauto.
    { instantiate (1:=tid). ss. auto. }
    { ss. auto. }
    intro LSIM. clear INV.
    instantiate (1:=gpt) in LSIM. instantiate (1:=gps) in LSIM.
    (* instantiate (1:=true) in LSIM. instantiate (1:=true) in LSIM. *)

    ginit. revert_until RR. gcofix CIH. i.
    move o before CIH. revert_until o. induction (wf_src.(wf) o). clear H. rename x into o, H0 into IHo. i.

    match goal with
    | LSIM: lsim _ _ ?_LRR tid _ _ _ _ ?_shr |- _ => remember _LRR as LRR; remember _shr as shr
    end.
    (* remember true as ps in LSIM at 1. remember true as pt in LSIM at 1. *)
    (* clear Heqps Heqpt. *)
    (* remember tid as tid0 in LSIM. *)
    punfold LSIM.
    2:{ ii. eapply pind5_mon_gen; eauto. i. eapply __lsim_mon; eauto. }
    move LSIM before LOCAL. revert_until LSIM.
    eapply pind5_acc in LSIM.

    { instantiate (1:= (fun gps gpt (src: itree srcE R0) (tgt: itree tgtE R1) shr =>
                          threads_find tid ths_src = None ->
                          threads_find tid ths_tgt = None ->
                          forall (st_src : state_src) (st_tgt : state_tgt) (mt : imap wf_tgt) (ms : imap wf_src) (w : world),
                            LRR = local_RR world_le I RR tid ->
                            shr = (tid :: alist_proj1 ths_src, tid :: alist_proj1 ths_tgt, ms, mt, st_src, st_tgt, o, w) ->
                            gpaco9 (_sim (wft:=wf_tgt)) (cpn9 (_sim (wft:=wf_tgt))) bot9 r R0 R1 RR gps ms gpt mt (interp_all st_src ths_src tid src)
                                   (interp_all st_tgt ths_tgt tid tgt))) in LSIM. auto. }

    ss. clear gps gpt src tgt shr LSIM.
    intros rr DEC IH ps pt src tgt shr LSIM. clear DEC.
    intros THSRC THTGT st_src st_tgt mt ms w ELRR Eshr.
    (* intros THSRC THTGT st_src st_tgt mt ms o w gps gpt ELRR Eshr Eps Ept. clarify. *)
    eapply pind5_unfold in LSIM.
    2:{ eapply _lsim_mon. }
    inv LSIM.

    { clear IH rr. unfold local_RR in LSIM0. des. clarify.
      unfold interp_all. rewrite ! interp_sched_ret. rewrite ! interp_state_tau.
      guclo sim_indC_spec. econs 3. guclo sim_indC_spec. econs 4.
      rewrite ! interp_sched_pick_ret.
      (*TODO: case analysis; all threads done / some other gets the turn -> CIH*)
      admit.
    }

    { clarify. destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      unfold interp_all at 1. pull_tau.
      guclo sim_indC_spec. econs 3.
      eapply IH. eauto. all: eauto.
    }

    { des. clarify. destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      unfold interp_all at 1. pull_eventE_l.
      guclo sim_indC_spec. econs 5. exists x.
      rewrite interp_state_tau. do 2 (guclo sim_indC_spec; econs 3).
      eapply IH. eauto. all: eauto.
    }

    { clarify. destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      unfold interp_all at 1. pull_sE_l. rewrite interp_state_put.
      rewrite interp_state_tau. do 2 (guclo sim_indC_spec; econs 3).
      eapply IH. eauto. all: eauto.
    }

    { clarify. destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      unfold interp_all at 1. pull_sE_l. rewrite interp_state_get.
      rewrite interp_state_tau. do 2 (guclo sim_indC_spec; econs 3).
      eapply IH. eauto. all: eauto.
    }

    { clarify. destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      unfold interp_all at 1. rewrite_cE_l. rewrite interp_sched_gettid.
      rewrite interp_state_tau. do 1 (guclo sim_indC_spec; econs 3).
      eapply IH. eauto. all: eauto.
    }

    { clarify. unfold interp_all at 1. pull_eventE_l.
      guclo sim_indC_spec. econs 10.
    }

    { des. clarify. destruct LSIM as [LSIM IND]. clear LSIM.
      unfold interp_all at 1. pull_eventE_l.
      guclo sim_indC_spec. econs 7. esplits; eauto.
      rewrite interp_state_tau. do 2 (guclo sim_indC_spec; econs 3).
      eapply IH. eauto. all: eauto.
    }

    { clarify. destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      unfold interp_all at 2. pull_tau.
      guclo sim_indC_spec. econs 4.
      eapply IH. eauto. all: eauto.
    }

    { clarify. unfold interp_all at 2. pull_eventE_r.
      guclo sim_indC_spec. econs 6. i.
      specialize (LSIM0 x). destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      rewrite interp_state_tau. do 2 (guclo sim_indC_spec; econs 4).
      eapply IH. eauto. all: eauto.
    }

    { clarify. destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      unfold interp_all at 2. pull_sE_r. rewrite interp_state_put.
      rewrite interp_state_tau. do 2 (guclo sim_indC_spec; econs 4).
      eapply IH. eauto. all: eauto.
    }

    { clarify. destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      unfold interp_all at 2. pull_sE_r. rewrite interp_state_get.
      rewrite interp_state_tau. do 2 (guclo sim_indC_spec; econs 4).
      eapply IH. eauto. all: eauto.
    }

    { clarify. destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      unfold interp_all at 2. rewrite_cE_r. rewrite interp_sched_gettid.
      rewrite interp_state_tau. do 1 (guclo sim_indC_spec; econs 4).
      eapply IH. eauto. all: eauto.
    }

    { clarify. unfold interp_all at 2. pull_eventE_r.
      guclo sim_indC_spec. econs 8. i.
      specialize (LSIM0 m_tgt0 FAIR). des. destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      rewrite interp_state_tau. do 2 (guclo sim_indC_spec; econs 4).
      eapply IH. eauto. all: eauto.
    }

    { clarify. unfold interp_all. pull_eventE_l. pull_eventE_r.
      rewrite ! bind_trigger. gfold. econs 2. i; clarify.
      rename r_tgt into retv. specialize (LSIM0 retv). pclearbot.
      clear IH rr.
      rewrite <- ! interp_state_tau. rewrite <- ! interp_sched_tau.
      right. eapply CIH; auto.
      pfold.
      eapply pind5_fold. econs 2. split; ss. eapply pind5_fold. econs 9. split; ss.
      eapply pind5_fold. econs 2. split; ss. eapply pind5_fold. econs 9. split; ss.
      punfold LSIM0. eapply lsim_mon.
    }

    { clarify. clear IH rr.
      unfold interp_all at 2. rewrite_cE_r.
      rewrite interp_sched_yield. rewrite interp_sched_pick_yield2.
      rewrite interp_state_tau. rewrite interp_state_trigger.
      guclo sim_indC_spec. econs 4.
      guclo sim_indC_spec. econs 6. i.
      guclo sim_indC_spec. econs 4.
      (*destruct cases: UB case / 
        x = tid: ind on o1, ind on LSIM0, trivial case: LSIM0, sync: case analysis: IHo1|CIH /
        x <> tid: CIH, LOCAL*)
      des_ifs.
      2:{ admit. }
      destruct (tid_dec x tid) eqn:TID.
      { clarify. eapply IHo. eauto. 1,2,3: admit.
        admit.
      }
      unfold interp_all at 1. rewrite_cE_l.
      rewrite interp_sched_yield. rewrite interp_sched_pick_yield2.
      rewrite interp_state_tau. rewrite interp_state_trigger.
      guclo sim_indC_spec. econs 3.
      guclo sim_indC_spec. econs 5. exists x.
      guclo sim_indC_spec. econs 3.
      (* make lemma for threads_pop *)
      des_ifs.
      2:{ admit. }
      hexploit LOCAL.
      { instantiate (1:=t1). instantiate (1:=x). admit. }
      { instantiate (1:=t). admit. }
      intros LSIM. unfold local_sim in LSIM. hexploit LSIM. 3: eauto.
      { instantiate (1:=x). admit. }
      { admit. }
      clear LSIM; intro LSIM.



      
      gfold. econs 9. right. eapply CIH; ss; auto. all: ss.
      1,2,3: admit.
      


          
        match goal with
        | |- gpaco9 _ _ _ _ _ _ _ _ _ _ _ _ (interp_state (_, trigger ?EV >>= Tau (interp_sched ?a))) =>
            replace (trigger EV >>= Tau (interp_sched a)) with (x <- trigger EV >>= Tau (interp_sched a))
        end; auto; rewrite <- interp_sched_eventE_trigger.

        push_eventE_r.

        
        rewrite interp_state_trigger.
        rewrite bind_trigger. rewrite <- interp_sched_eventE_trigger.
        rewrite interp_sched_tau.

      admit. }

    { des. clarify. destruct LSIM as [LSIM IND]. clear LSIM.
      unfold interp_all at 1. rewrite_cE_l.
      rewrite interp_sched_yield. rewrite interp_sched_pick_yield.
      rewrite interp_state_tau. rewrite interp_state_trigger.
      guclo sim_indC_spec. econs 3.
      guclo sim_indC_spec. econs 5. exists tid.
      guclo sim_indC_spec. econs 3.
      (* lemma for threads_pop, etc., induction *)
      admit.
    }

    { clarify. pclearbot. gfold. econs 9; auto.
      clear IH rr.
      right. eapply CIH; auto. eauto.
    }

  Abort.

  (* Permutation ths_src0 ths_src1 /\ Permutation ths_tgt0 ths_tgt1 /\ I (ths_src0, ths_tgt0, ...) -> I (ths_src1, ths_tgt1, ...). *)


  Lemma ths_find_none_ths_pop_some:
    threads_find tid ths = None /\ threads_pop t ths <> None
    -> t <> tid.
  Abort.

  Lemma ths_find_none_tlist_remove:
    threads_find tid ths = None /\ tid_list_remove (tid :: alist_proj1 ths) tid tl
    -> tl = alist_proj1 ths.
  Abort.

  Lemma perm_ths_pop:
    Permutation (alist_proj1 ths1) (alist_proj1 ths2) /\ threads_pop tid ths1 = Some (th1, ths3)
    -> exists th1 ths4, threads_pop tid ths2 = Some (th1, ths4) /\
                    Permutation (alist_proj1 ths3) (alist_proj1 ths4).
  Abort.

  Lemma ths_pop_cons_perm:
    threads_pop tid ths = Some (th, ths0) /\ List.NoDup (alist_proj1 ths)
    -> Permutation (alist_proj1 ths) (tid :: alist_proj1 ths0).
  Abort.

  Lemma ths_pop_update_ths_eq:
    List.NoDup (alist_proj1 ths) ->
    threads_pop tid (update_threads tid itr ths) = Some (itr, ths).
  Abort.

  Lemma ths_pop_update_ths_perm:
    List.NoDup (alist_proj1 ths) /\
      threads_pop t (update_threads tid itr ths) = Some (th, ths0) ->
    Permutation (tid :: alist_proj1 ths) (t :: alist_proj1 ths0).
  Abort.

  



End ADEQ.
