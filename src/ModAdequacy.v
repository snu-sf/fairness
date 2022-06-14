From sflib Require Import sflib.
From ITree Require Export ITree.
From Paco Require Import paco.

Require Export Coq.Strings.String.
Require Import Program.

From ExtLib Require Import FMapAList.

Export ITreeNotations.

From Fairness Require Import pind8.
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
    (alist_proj1 ths_src) = (alist_proj1 ths_tgt).

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
    eapply RelDec.RelDec_Correct_eq_typ.
  Qed.

  Lemma ths_pop_find_some
        R (ths ths0: @threads _ident_src E1 R) th tid
        (POP: threads_pop tid ths = Some (th, ths0))
    :
    threads_find tid ths = Some th.
  Proof.
    unfold threads_pop in POP. des_ifs.
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

  (*invariant for tid_list & threads: tid_list_add threads.proj1 tid tid_list*)
  Theorem local_adequacy
          (* (LSIM: forall R0 R1 (RR: R0 -> R1 -> Prop) (src0: itree srcE R0) (tgt0: itree tgtE R1), *)
          (*     local_sim world_le I RR src0 tgt0) *)
          R0 R1 (RR: R0 -> R1 -> Prop)
          (ths_src: @threads _ident_src (sE state_src) R0)
          (ths_tgt: @threads _ident_tgt (sE state_tgt) R1)
          (WFTHS: wf_ths ths_src ths_tgt)
          (LSIM: forall tid (src: itree srcE R0) (tgt: itree tgtE R1)
                   (LSRC: threads_find tid ths_src = Some src)
                   (LTGT: threads_find tid ths_tgt = Some tgt)
            ,
              local_sim world_le I RR src tgt)
          tid src0 tgt0 ths_src0 ths_tgt0
          (THSRC: threads_pop tid ths_src = Some (src0, ths_src0))
          (THTGT: threads_pop tid ths_tgt = Some (tgt0, ths_tgt0))
          (st_src: state_src) (st_tgt: state_tgt)
          (INV: forall im_tgt, exists im_src o w,
              I (alist_proj1 ths_src0, alist_proj1 ths_tgt0, im_src, im_tgt, st_src, st_tgt, o, w))
    :
    gsim wf_src wf_tgt RR false false
         (interp_all st_src ths_src0 tid src0)
         (interp_all st_tgt ths_tgt0 tid tgt0).
  Proof.
    ii. specialize (INV mt). des. rename im_src into ms. exists ms. dup LSIM. move LSIM0 before RR.
    pose proof (ths_pop_find_none ths_src tid THSRC) as NONE1.
    pose proof (ths_find_none_tid_add ths_src0 tid NONE1) as TADD1; clear NONE1.
    pose proof (ths_pop_find_none ths_tgt tid THTGT) as NONE2.
    pose proof (ths_find_none_tid_add ths_tgt0 tid NONE2) as TADD2; clear NONE2.
    pose proof (ths_pop_find_some ths_src tid THSRC) as FIND1.
    pose proof (ths_pop_find_some ths_tgt tid THTGT) as FIND2.
    unfold local_sim in LSIM. specialize (LSIM tid src0 tgt0 FIND1 FIND2 _ _ _ _ _ _ _ _ INV tid _ _ TADD1 TADD2).
    clear TADD1 TADD2 FIND1 FIND2.

    ginit. revert_until I. gcofix CIH. i.
    match goal with
    | LSIM: lsim _ _ tid ?_LRR _ _ _ _ ?_shr |- _ => remember _LRR as LRR; remember _shr as shr
    end.
    remember false as ps in LSIM at 1. remember false as pt in LSIM at 1.
    (* remember tid as tid0 in LSIM. *)
    punfold LSIM.
    2:{ ii. eapply pind8_mon_gen; eauto. i. eapply __lsim_mon; eauto. }
    move LSIM before CIH. revert_until LSIM.
    eapply pind8_acc in LSIM.

    { instantiate (1:= (fun R0 R1 (LRR: R0 -> R1 -> tid_list * imap wf_src * imap wf_tgt * state_src * state_tgt * T wf_src * world -> Prop) ps pt (src: itree srcE R0) (tgt: itree tgtE R1) shr =>
                          forall (RR : R0 -> R1 -> Prop) (ths_src : threads (sE state_src)) (st_src : state_src) (st_tgt : state_tgt)
                            (mt : imap wf_tgt) (ms : imap wf_src) (o : T wf_src) (w : world) (tlist : list nat),
                            tlist = tid :: alist_proj1 ths_src ->
                            LRR = local_RR world_le I RR tid ->
                            shr = (tlist, ms, mt, st_src, st_tgt, o, w) ->
                            ps = false ->
                            pt = false ->
                            forall ths_tgt : threads (sE state_tgt),
                              wf_ths ths_src ths_tgt ->
                              threads_find tid ths_src = None ->
                              threads_find tid ths_tgt = None ->
                              I (alist_proj1 ths_src, ms, mt, st_src, st_tgt, o, w) ->
                              tid_list_add (alist_proj1 ths_src) tid tlist ->
                              gpaco9 (_sim (wft:=wf_tgt)) (cpn9 (_sim (wft:=wf_tgt))) bot9 r R0 R1 RR false ms false mt (interp_all st_src ths_src tid src)
                                     (interp_all st_tgt ths_tgt tid tgt))) in LSIM. auto. }

    (* { instantiate (1:= *)
    (*                  (fun R0 R1 (LRR: R0 -> R1 -> tid_list * imap wf_src * imap wf_tgt * state_src * state_tgt * T wf_src * world -> Prop) ps pt (src: itree srcE R0) (tgt: itree tgtE R1) shr => *)
    (*                     forall (RR : R0 -> R1 -> Prop) (ths_src : threads (sE state_src)) (tid : nat) (st_src : state_src) (st_tgt : state_tgt) *)
    (*                       (mt : imap wf_tgt) (ms : imap wf_src) (o : T wf_src) (w : world) (tlist : list nat), *)
    (*                       tlist = tid :: alist_proj1 ths_src -> *)
    (*                       LRR = local_RR world_le I RR tid -> *)
    (*                       shr = (tlist, ms, mt, st_src, st_tgt, o, w) -> *)
    (*                       ps = false -> *)
    (*                       pt = false -> *)
    (*                       tid0 = tid -> *)
    (*                       forall ths_tgt : threads (sE state_tgt), *)
    (*                         wf_ths ths_src ths_tgt -> *)
    (*                         threads_find tid ths_src = None -> *)
    (*                         threads_find tid ths_tgt = None -> *)
    (*                         I (alist_proj1 ths_src, ms, mt, st_src, st_tgt, o, w) -> *)
    (*                         tid_list_add (alist_proj1 ths_src) tid tlist -> *)
    (*                         gpaco9 (_sim (wft:=wf_tgt)) (cpn9 (_sim (wft:=wf_tgt))) bot9 r R0 R1 RR false ms false mt (interp_all st_src ths_src tid src) *)
    (*                                (interp_all st_tgt ths_tgt tid tgt))) in LSIM. auto. } *)

    clear R0 R1 LRR ps pt src tgt shr LSIM. i.
    rename x0 into R0, x1 into R1, x2 into LRR, x3 into ps, x4 into pt, x5 into src, x6 into tgt, x7 into shr, PR into LSIM.
    clear DEC. ss. intros RR ths_src st_src st_tgt mt ms o w tlist Etlist ELRR Eshr Eps Ept.
    intros ths_tgt WFTHS STHS TTHS INV TADD.
    eapply pind8_unfold in LSIM.
    2:{ eapply _lsim_mon. }
    inv LSIM.

    { clear IH rr. unfold local_RR in LSIM0. des. clarify.
      unfold interp_all. rewrite ! interp_sched_ret. rewrite ! interp_state_tau.
      guclo sim_indC_spec. econs 3. guclo sim_indC_spec. econs 4.
      rewrite ! interp_sched_pick_ret.
      (*TODO: case analysis; all threads done / some other gets the turn -> CIH*)

      
      match goal with
      | |- gpaco9 _ _ _ _ _ _ _ _ _ _ _ ?_interp_src _ => set (interp_src:=_interp_src)
      end.
      rewrite interp_sched_pick. rewrite interp_state_trigger. guclo sim_indC_spec. econs 6. i.
      subst interp_src. rewrite interp_sched_pick. rewrite interp_state_trigger. guclo sim_indC_spec. econs 5. exists x.
      guclo sim_indC_spec. econs 3. guclo sim_indC_spec. econs 4.
      
      rewrite interp_sched_pick.
      gfold. econs 3. econs 4.

      gfold.

      econs 1.

      gfinal. right. pfold.







                        


  Abort.

End ADEQ.
