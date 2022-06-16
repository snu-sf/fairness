From sflib Require Import sflib.
From ITree Require Export ITree.
From Paco Require Import paco.

Require Export Coq.Strings.String.
Require Import Program.
Require Import Permutation.

From ExtLib Require Import FMapAList.

Export ITreeNotations.

From Fairness Require Import pind5.
From Fairness Require Export ITreeLib FairBeh FairSim.
From Fairness Require Export Mod ModSimPico Concurrency.

Set Implicit Arguments.



Section AUX.

  Definition alist_proj1 {K} {V} (a: alist K V): list K :=
    List.map fst a.

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
    unfold threads_pop in POP. des_ifs. unfold threads_find, threads_remove. eapply remove_eq_alist.
    eapply reldec_correct_tid_dec.
  Qed.

  Lemma ths_pop_find_some
        R (ths ths0: @threads _ident_src E1 R) th tid
        (POP: threads_pop tid ths = Some (th, ths0))
    :
    threads_find tid ths = Some th.
  Proof.
    unfold threads_pop in POP. des_ifs.
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

  Let srcE := ((@eventE ident_src +' cE) +' sE state_src).
  Let tgtE := ((@eventE ident_tgt +' cE) +' sE state_tgt).

  Variable world: Type.
  Variable world_le: world -> world -> Prop.

  Variable I: (@shared state_src state_tgt _ident_src _ident_tgt wf_src wf_tgt world) -> Prop.


  Ltac gfold := gfinal; right; pfold.

  Ltac pull_tau := rewrite interp_sched_tau; rewrite interp_state_tau.

  Ltac pull_eventE_l :=
    match goal with
    | |- gpaco9 _ _ _ _ _ _ _ _ _ _ _ (interp_state (_, interp_sched (_, inl (_, trigger ?EV >>= ?ktr)))) _ => replace (trigger EV >>= ktr) with (trigger (inl1 (inl1 EV)) >>= ktr)
    end; auto; rewrite interp_sched_eventE_trigger; rewrite interp_state_trigger.

  Ltac pull_eventE_r :=
    match goal with
    | |- gpaco9 _ _ _ _ _ _ _ _ _ _ _ _ (interp_state (_, interp_sched (_, inl (_, trigger ?EV >>= ?ktr)))) => replace (trigger EV >>= ktr) with (trigger (inl1 (inl1 EV)) >>= ktr)
    end; auto; rewrite interp_sched_eventE_trigger; rewrite interp_state_trigger.

  (* Ltac push_eventE_l := *)
  (*   match goal with *)
  (*   | |- gpaco9 _ _ _ _ _ _ _ _ _ _ _ (interp_state (_, trigger ?EV >>= Tau (interp_sched ?a))) _ => *)
  (*       replace (trigger EV >>= Tau (interp_sched a)) with (trigger (inl1 EV);; Tau (interp_sched a)) *)
  (*   end; auto; rewrite <- interp_sched_eventE_trigger. *)

  (* Ltac push_eventE_r := *)
  (*   match goal with *)
  (*   | |- gpaco9 _ _ _ _ _ _ _ _ _ _ _ _ (interp_state (_, trigger ?EV >>= Tau (interp_sched ?a))) => *)
  (*       replace (trigger EV >>= Tau (interp_sched a)) with (trigger (inl1 EV);; Tau (interp_sched a)) *)
  (*   end; auto; rewrite <- interp_sched_eventE_trigger. *)

  Ltac pull_sE_l :=
    match goal with
    | |- gpaco9 _ _ _ _ _ _ _ _ _ _ _ (interp_state (_, interp_sched (_, inl (_, trigger ?EV >>= ?ktr)))) _ => replace (trigger EV >>= ktr) with (trigger (inr1 EV) >>= ktr)
    end; auto; rewrite interp_sched_trigger.

  Ltac pull_sE_r :=
    match goal with
    | |- gpaco9 _ _ _ _ _ _ _ _ _ _ _ _ (interp_state (_, interp_sched (_, inl (_, trigger ?EV >>= ?ktr)))) => replace (trigger EV >>= ktr) with (trigger (inr1 EV) >>= ktr)
    end; auto; rewrite interp_sched_trigger.

  Ltac rewrite_cE_l :=
    match goal with
    | |- gpaco9 _ _ _ _ _ _ _ _ _ _ _ (interp_state (_, interp_sched (_, inl (_, trigger ?EV >>= ?ktr)))) _ => replace (trigger EV >>= ktr) with (trigger (inl1 (inr1 EV)) >>= ktr)
    end; auto.

  Ltac rewrite_cE_r :=
    match goal with
    | |- gpaco9 _ _ _ _ _ _ _ _ _ _ _ _ (interp_state (_, interp_sched (_, inl (_, trigger ?EV >>= ?ktr)))) => replace (trigger EV >>= ktr) with (trigger (inl1 (inr1 EV)) >>= ktr)
    end; auto.


  (*invariant for tid_list & threads: tid_list_add threads.proj1 tid tid_list*)
  Theorem local_adequacy
          (* (LSIM: forall R0 R1 (RR: R0 -> R1 -> Prop) (src0: itree srcE R0) (tgt0: itree tgtE R1), *)
          (*     local_sim world_le I RR src0 tgt0) *)
          R0 R1 (RR: R0 -> R1 -> Prop)
          (ths_src: @threads _ident_src (sE state_src) R0)
          (ths_tgt: @threads _ident_tgt (sE state_tgt) R1)
          (WFTHS: wf_ths ths_src ths_tgt)
          (* (LOCAL: forall tid (src: itree srcE R0) (tgt: itree tgtE R1) *)
          (*           (LSRC: threads_find tid ths_src = Some src) *)
          (*           (LTGT: threads_find tid ths_tgt = Some tgt) *)
          (*   , *)
          (*     local_sim world_le I RR src tgt) *)
          tid
          (THSRC: threads_find tid ths_src = None)
          (THTGT: threads_find tid ths_tgt = None)
          src tgt
          (LSIM: local_sim world_le I RR src tgt)
          (st_src: state_src) (st_tgt: state_tgt)
          (INV: forall im_tgt, exists im_src o w,
              I (tid :: alist_proj1 ths_src, tid :: alist_proj1 ths_tgt, im_src, im_tgt, st_src, st_tgt, o, w))
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
    (* move o before LOCAL. revert_until o. induction (wf_src.(wf) o). clear H. rename x into o, H0 into IHo. i. *)
    (* ginit. revert_until IHo. gcofix CIH. i. *)

    match goal with
    | LSIM: lsim _ _ ?_LRR tid _ _ _ _ ?_shr |- _ => remember _LRR as LRR; remember _shr as shr
    end.
    (* remember true as ps in LSIM at 1. remember true as pt in LSIM at 1. *)
    (* clear Heqps Heqpt. *)
    (* remember tid as tid0 in LSIM. *)
    punfold LSIM.
    2:{ ii. eapply pind5_mon_gen; eauto. i. eapply __lsim_mon; eauto. }
    move LSIM before WFTHS. revert_until LSIM.
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
      eapply IHo. eauto. all: auto. instantiate (1:=w1). dup INV. specialize (INV0 tid).
      pfold. eapply pind5_fold. econs 16.



      
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
      { destruct (tid_dec x tid) eqn:TID.
        { clarify. unfold interp_all at 1. rewrite_cE_l.
          rewrite interp_sched_yield. rewrite interp_sched_pick_yield2.
          rewrite interp_state_tau. rewrite interp_state_trigger.
          guclo sim_indC_spec. econs 3.
          guclo sim_indC_spec. econs 5. exists tid.
          guclo sim_indC_spec. econs 3.
          (* make lemma for threads_pop *)
          des_ifs.
          { gfold. econs 9. right. eapply CIH; ss; auto. all: ss.
            1,2,3,4: admit.
            


          
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
