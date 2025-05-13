From sflib Require Import sflib.
From Paco Require Import paco.
From iris.algebra Require Import cmra.

Require Import Coq.Classes.RelationClasses.
Require Import Program.

From Fairness Require Export ITreeLib FairBeh NatStructsLarge.
From Fairness Require Export Mod ModSimStutter Concurrency.
From Fairness Require Import pind World.

Set Implicit Arguments.



Section KSIM.

  Context `{M: ucmra}.

  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable _ident_src: ID.
  Let ident_src := sum_tid _ident_src.
  Variable _ident_tgt: ID.
  Let ident_tgt := sum_tid _ident_tgt.

  Variable wf_src: WF.
  Variable wf_tgt: WF.

  Notation srcE := (threadE _ident_src state_src).
  Notation tgtE := (threadE _ident_tgt state_tgt).

  Variable wf_stt: Type -> Type -> WF.

  Definition kshared :=
    ((@imap ident_src wf_src) *
       (@imap ident_tgt wf_tgt) *
       state_src *
       state_tgt)%type.

  Definition to_kshared (shr: shared state_src state_tgt _ident_src _ident_tgt wf_src wf_tgt): kshared :=
    let '(ths, im_src, im_tgt, st_src, st_tgt) := shr in
    (im_src, im_tgt, st_src, st_tgt).

  Definition threads2 _id ev R := Th.t (prod bool (@thread _id ev R)).
  Notation threads_src1 R0 := (threads _ident_src (sE state_src) R0).
  Notation threads_src2 R0 := (threads2 _ident_src (sE state_src) R0).
  Notation threads_tgt R1 := (threads _ident_tgt (sE state_tgt) R1).

  Variant __sim_knot R0 R1 (RR: R0 -> R1 -> Prop)
          (sim_knot: threads_src2 R0 -> threads_tgt R1 -> thread_id -> local_resources -> bool -> bool -> (prod bool (itree srcE R0)) -> (itree tgtE R1) -> kshared -> (wf_stt R0 R1).(T) -> Prop)
          (_sim_knot: threads_src2 R0 -> threads_tgt R1 -> thread_id -> local_resources -> bool -> bool -> (prod bool (itree srcE R0)) -> (itree tgtE R1) -> kshared -> (wf_stt R0 R1).(T) -> Prop)
          (thsl: threads_src2 R0) (thsr: threads_tgt R1)
    :
    thread_id -> local_resources -> bool -> bool -> (prod bool (itree srcE R0)) -> itree tgtE R1 -> kshared -> (wf_stt R0 R1).(T) -> Prop :=
    | ksim_ret_term
        tid f_src f_tgt
        sf r_src r_tgt
        rs_local
        im_src im_tgt st_src st_tgt o
        (RET: RR r_src r_tgt)
        (NILS: Th.is_empty thsl = true)
        (NILT: Th.is_empty thsr = true)
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid rs_local f_src f_tgt
                 (sf, Ret r_src)
                 (Ret r_tgt)
                 (im_src, im_tgt, st_src, st_tgt) o

    | ksim_ret_cont
        tid f_src f_tgt
        sf r_src r_tgt
        rs_local
        im_src im_tgt st_src st_tgt o
        o0
        rs_local0 r_own r_shared0
        (UPDRS: rs_local0 = NatMap.add tid r_own rs_local)
        (WF: resources_wf r_shared0 rs_local0)
        (STUTTER: (wf_stt R0 R1).(lt) o0 o)
        (RET: RR r_src r_tgt)
        (NNILS: Th.is_empty thsl = false)
        (NNILT: Th.is_empty thsr = false)
        (KSIM: forall tid0,
            ((nm_pop tid0 thsl = None) /\ (nm_pop tid0 thsr = None)) \/
              (exists b th_src thsl0 th_tgt thsr0,
                  (nm_pop tid0 thsl = Some ((b, th_src), thsl0)) /\
                    (nm_pop tid0 thsr = Some (th_tgt, thsr0)) /\
                    ((b = true) ->
                     (forall im_tgt0
                        (FAIR: fair_update im_tgt im_tgt0 (prism_fmap inlp (tids_fmap tid0 (key_set thsr0)))),
                         (sim_knot thsl0 thsr0 tid0
                                   (snd (@get_resource M tid0 rs_local0))
                                   true true
                                   (b, Vis (inl1 (inl1 (inr1 Yield))) (fun _ => th_src))
                                   (th_tgt)
                                   (im_src, im_tgt0, st_src, st_tgt) o0))) /\
                    ((b = false) ->
                     (forall im_tgt0
                        (FAIR: fair_update im_tgt im_tgt0 (prism_fmap inlp (tids_fmap tid0 (key_set thsr0)))),
                       exists im_src0,
                         (fair_update im_src im_src0 (prism_fmap inlp (tids_fmap tid0 (key_set thsl0)))) /\
                           (sim_knot thsl0 thsr0 tid0
                                     (snd (@get_resource M tid0 rs_local0))
                                     true true
                                     (b, th_src)
                                     th_tgt
                                     (im_src0, im_tgt0, st_src, st_tgt) o0)))))
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid rs_local f_src f_tgt
                 (sf, Ret r_src)
                 (Ret r_tgt)
                 (im_src, im_tgt, st_src, st_tgt) o

    | ksim_sync
        tid f_src f_tgt
        sf ktr_src ktr_tgt
        rs_local
        im_src im_tgt st_src st_tgt o
        thsl0 thsr0
        rs_local0 r_own r_shared0
        (UPDRS: rs_local0 = NatMap.add tid r_own rs_local)
        (WF: resources_wf r_shared0 rs_local0)
        (THSL: thsl0 = Th.add tid (true, ktr_src tt) thsl)
        (THSR: thsr0 = Th.add tid (ktr_tgt tt) thsr)
        (KSIM: forall tid0,
            ((nm_pop tid0 thsl0 = None) /\ (nm_pop tid0 thsr0 = None)) \/
              (exists b th_src thsl1 th_tgt thsr1,
                  (nm_pop tid0 thsl0 = Some ((b, th_src), thsl1)) /\
                    (nm_pop tid0 thsr0 = Some (th_tgt, thsr1)) /\
                    ((b = true) ->
                     (forall im_tgt0 (FAIR: fair_update im_tgt im_tgt0 (prism_fmap inlp (tids_fmap tid0 (key_set thsr1)))),
                       exists o0, ((wf_stt R0 R1).(lt) o0 o) /\
                               (sim_knot thsl1 thsr1 tid0
                                         (snd (@get_resource M tid0 rs_local0))
                                         true true
                                         (b, Vis (inl1 (inl1 (inr1 Yield))) (fun _ => th_src))
                                         (th_tgt)
                                         (im_src, im_tgt0, st_src, st_tgt) o0))) /\
                    ((b = false) ->
                     (forall im_tgt0 (FAIR: fair_update im_tgt im_tgt0 (prism_fmap inlp (tids_fmap tid0 (key_set thsr1)))),
                       exists im_src0 o0,
                         (fair_update im_src im_src0 (prism_fmap inlp (tids_fmap tid0 (key_set thsl1)))) /\
                           ((wf_stt R0 R1).(lt) o0 o) /\
                           (sim_knot thsl1 thsr1 tid0
                                     (snd (@get_resource M tid0 rs_local0))
                                     true true
                                     (b, th_src)
                                     th_tgt
                                     (im_src0, im_tgt0, st_src, st_tgt) o0)))))
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid rs_local f_src f_tgt
                 (sf, Vis (inl1 (inl1 (inr1 Yield))) ktr_src)
                 (Vis (inl1 (inl1 (inr1 Yield))) ktr_tgt)
                 (im_src, im_tgt, st_src, st_tgt) o

    | ksim_yieldL
        tid f_src f_tgt
        sf ktr_src itr_tgt
        rs_local
        im_src im_tgt st_src st_tgt o
        (KSIM: exists im_src0 o0,
            (fair_update im_src im_src0 (prism_fmap inlp (tids_fmap tid (key_set thsl)))) /\
              (_sim_knot thsl thsr tid rs_local true f_tgt
                         (false, ktr_src tt)
                         itr_tgt
                         (im_src0, im_tgt, st_src, st_tgt) o0))
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid rs_local f_src f_tgt
                 (sf, Vis (inl1 (inl1 (inr1 Yield))) ktr_src)
                 (itr_tgt)
                 (im_src, im_tgt, st_src, st_tgt) o

    | ksim_tauL
        tid f_src f_tgt
        sf itr_src itr_tgt
        rs_local
        im_src im_tgt st_src st_tgt o
        (KSIM: _sim_knot thsl thsr tid rs_local true f_tgt
                         (sf, itr_src)
                         itr_tgt
                         (im_src, im_tgt, st_src, st_tgt) o)
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid rs_local f_src f_tgt
                 (sf, Tau itr_src)
                 (itr_tgt)
                 (im_src, im_tgt, st_src, st_tgt) o
    | ksim_chooseL
        tid f_src f_tgt
        sf X ktr_src itr_tgt
        rs_local
        im_src im_tgt st_src st_tgt o
        (KSIM: exists x, _sim_knot thsl thsr tid rs_local true f_tgt
                              (sf, ktr_src x)
                              itr_tgt
                              (im_src, im_tgt, st_src, st_tgt) o)
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid rs_local f_src f_tgt
                 (sf, Vis (inl1 (inl1 (inl1 (Choose X)))) ktr_src)
                 (itr_tgt)
                 (im_src, im_tgt, st_src, st_tgt) o
    | ksim_stateL
        tid f_src f_tgt
        sf X run ktr_src itr_tgt
        rs_local
        im_src im_tgt st_src st_tgt o
        (KSIM: _sim_knot thsl thsr tid rs_local true f_tgt
                         (sf, ktr_src (snd (run st_src) : X))
                         itr_tgt
                         (im_src, im_tgt, fst (run st_src), st_tgt) o)
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid rs_local f_src f_tgt
                 (sf, Vis (inr1 (State run)) ktr_src)
                 (itr_tgt)
                 (im_src, im_tgt, st_src, st_tgt) o
    | ksim_tidL
        tid f_src f_tgt
        sf ktr_src itr_tgt
        rs_local
        im_src im_tgt st_src st_tgt o
        (KSIM: _sim_knot thsl thsr tid rs_local true f_tgt
                         (sf, ktr_src tid)
                         itr_tgt
                         (im_src, im_tgt, st_src, st_tgt) o)
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid rs_local f_src f_tgt
                 (sf, Vis (inl1 (inl1 (inr1 GetTid))) ktr_src)
                 (itr_tgt)
                 (im_src, im_tgt, st_src, st_tgt) o
    | ksim_UB
        tid f_src f_tgt
        sf ktr_src itr_tgt
        rs_local
        im_src im_tgt st_src st_tgt o
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid rs_local f_src f_tgt
                 (sf, Vis (inl1 (inl1 (inl1 Undefined))) ktr_src)
                 (itr_tgt)
                 (im_src, im_tgt, st_src, st_tgt) o
    | ksim_fairL
        tid f_src f_tgt
        sf fm ktr_src itr_tgt
        rs_local
        im_src im_tgt st_src st_tgt o
        (KSIM: exists im_src0,
            (<<FAIR: fair_update im_src im_src0 (prism_fmap inrp fm)>>) /\
              (_sim_knot thsl thsr tid rs_local true f_tgt
                         (sf, ktr_src tt)
                         itr_tgt
                         (im_src0, im_tgt, st_src, st_tgt) o))
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid rs_local f_src f_tgt
                 (sf, Vis (inl1 (inl1 (inl1 (Fair fm)))) ktr_src)
                 (itr_tgt)
                 (im_src, im_tgt, st_src, st_tgt) o

    | ksim_tauR
        tid f_src f_tgt
        sf itr_src itr_tgt
        rs_local
        im_src im_tgt st_src st_tgt o
        (KSIM: _sim_knot thsl thsr tid rs_local f_src true
                         (sf, itr_src)
                         itr_tgt
                         (im_src, im_tgt, st_src, st_tgt) o)
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid rs_local f_src f_tgt
                 (sf, itr_src)
                 (Tau itr_tgt)
                 (im_src, im_tgt, st_src, st_tgt) o
    | ksim_chooseR
        tid f_src f_tgt
        sf itr_src X ktr_tgt
        rs_local
        im_src im_tgt st_src st_tgt o
        (KSIM: forall x, _sim_knot thsl thsr tid rs_local f_src true
                              (sf, itr_src)
                              (ktr_tgt x)
                              (im_src, im_tgt, st_src, st_tgt) o)
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid rs_local f_src f_tgt
                 (sf, itr_src)
                 (Vis (inl1 (inl1 (inl1 (Choose X)))) ktr_tgt)
                 (im_src, im_tgt, st_src, st_tgt) o
    | ksim_stateR
        tid f_src f_tgt
        sf itr_src X run ktr_tgt
        rs_local
        im_src im_tgt st_src st_tgt o
        (KSIM: _sim_knot thsl thsr tid rs_local f_src true
                         (sf, itr_src)
                         (ktr_tgt (snd (run st_tgt) : X))
                         (im_src, im_tgt, st_src, fst (run st_tgt)) o)
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid rs_local f_src f_tgt
                 (sf, itr_src)
                 (Vis (inr1 (State run)) ktr_tgt)
                 (im_src, im_tgt, st_src, st_tgt) o
    | ksim_tidR
        tid f_src f_tgt
        sf itr_src ktr_tgt
        rs_local
        im_src im_tgt st_src st_tgt o
        (KSIM: _sim_knot thsl thsr tid rs_local f_src true
                         (sf, itr_src)
                         (ktr_tgt tid)
                         (im_src, im_tgt, st_src, st_tgt) o)
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid rs_local f_src f_tgt
                 (sf, itr_src)
                 (Vis (inl1 (inl1 (inr1 GetTid))) ktr_tgt)
                 (im_src, im_tgt, st_src, st_tgt) o
    | ksim_fairR
        tid f_src f_tgt
        sf itr_src fm ktr_tgt
        rs_local
        im_src im_tgt st_src st_tgt o
        (KSIM: forall im_tgt0 (FAIR: fair_update im_tgt im_tgt0 (prism_fmap inrp fm)),
            (_sim_knot thsl thsr tid rs_local f_src true
                       (sf, itr_src)
                       (ktr_tgt tt)
                       (im_src, im_tgt0, st_src, st_tgt) o))
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid rs_local f_src f_tgt
                 (sf, itr_src)
                 (Vis (inl1 (inl1 (inl1 (Fair fm)))) ktr_tgt)
                 (im_src, im_tgt, st_src, st_tgt) o

    | ksim_observe
        tid f_src f_tgt
        sf fn args ktr_src ktr_tgt
        rs_local
        im_src im_tgt st_src st_tgt o
        (KSIM: forall ret, sim_knot thsl thsr tid rs_local true true
                               (sf, ktr_src ret)
                               (ktr_tgt ret)
                               (im_src, im_tgt, st_src, st_tgt) o)
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid rs_local f_src f_tgt
                 (sf, Vis (inl1 (inl1 (inl1 (Observe fn args)))) ktr_src)
                 (Vis (inl1 (inl1 (inl1 (Observe fn args)))) ktr_tgt)
                 (im_src, im_tgt, st_src, st_tgt) o

    | ksim_call
        tid f_src f_tgt
        sf fn args ktr_src itr_tgt
        rs_local
        im_src im_tgt st_src st_tgt o
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid rs_local f_src f_tgt
                 (sf, (trigger (Call fn args) >>= ktr_src))
                 itr_tgt
                 (im_src, im_tgt, st_src, st_tgt) o

    | ksim_progress
        tid
        sf itr_src itr_tgt
        rs_local
        im_src im_tgt st_src st_tgt o
        (KSIM: sim_knot thsl thsr tid rs_local false false
                        (sf, itr_src)
                        itr_tgt
                        (im_src, im_tgt, st_src, st_tgt) o)
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid rs_local true true
                 (sf, itr_src)
                 (itr_tgt)
                 (im_src, im_tgt, st_src, st_tgt) o
  .

  Definition sim_knot R0 R1 (RR: R0 -> R1 -> Prop):
    threads_src2 R0 -> threads_tgt R1 -> thread_id -> local_resources ->
    bool -> bool -> (prod bool (itree srcE R0)) -> (itree tgtE R1) -> kshared -> (wf_stt R0 R1).(T) -> Prop :=
    paco10 (fun r => pind10 (__sim_knot RR r) top10) bot10.

  Lemma __ksim_mon R0 R1 (RR: R0 -> R1 -> Prop):
    forall r r' (LE: r <10= r'), (__sim_knot RR r) <11= (__sim_knot RR r').
  Proof.
    ii. inv PR; try (econs; eauto; fail).
    { econs 2; eauto. i. specialize (KSIM tid0). des; eauto. right.
      esplits; eauto.
      i. specialize (KSIM2 H _ FAIR). des. esplits; eauto.
    }
    { econs 3; eauto. i. specialize (KSIM tid0). des; eauto. right.
      esplits; eauto.
      i. specialize (KSIM1 H _ FAIR). des. esplits; eauto.
      i. specialize (KSIM2 H _ FAIR). des. esplits; eauto.
    }
  Qed.

  Lemma _ksim_mon R0 R1 (RR: R0 -> R1 -> Prop): forall r, monotone10 (__sim_knot RR r).
  Proof.
    ii. inv IN; try (econs; eauto; fail).
    { des. econs; eauto. }
    { des. econs; eauto. }
    { des. econs; eauto. }
  Qed.

  Lemma ksim_mon R0 R1 (RR: R0 -> R1 -> Prop): forall q, monotone10 (fun r => pind10 (__sim_knot RR r) q).
  Proof.
    ii. eapply pind10_mon_gen; eauto.
    ii. eapply __ksim_mon; eauto.
  Qed.

  Local Hint Constructors __sim_knot: core.
  Local Hint Unfold sim_knot: core.
  Local Hint Resolve __ksim_mon: paco.
  Local Hint Resolve _ksim_mon: paco.
  Local Hint Resolve ksim_mon: paco.

  Lemma ksim_reset_prog
        R0 R1 (RR: R0 -> R1 -> Prop)
        ths_src ths_tgt tid rs_local
        ssrc tgt shr o
        ps0 pt0 ps1 pt1
        (KSIM: sim_knot RR ths_src ths_tgt tid rs_local ps1 pt1 ssrc tgt shr o)
        (SRC: ps1 = true -> ps0 = true)
        (TGT: pt1 = true -> pt0 = true)
    :
    sim_knot RR ths_src ths_tgt tid rs_local ps0 pt0 ssrc tgt shr o.
  Proof.
    revert_until RR. pcofix CIH. i.
    move KSIM before CIH. revert_until KSIM. punfold KSIM.
    pattern ths_src, ths_tgt, tid, rs_local, ps1, pt1, ssrc, tgt, shr, o.
    revert ths_src ths_tgt tid rs_local ps1 pt1 ssrc tgt shr o KSIM.
    eapply pind10_acc.
    intros rr DEC IH ths_src ths_tgt tid rs_local ps1 pt1 ssrc tgt shr o KSIM. clear DEC.
    intros ps0 pt0 SRC TGT.
    eapply pind10_unfold in KSIM.
    2:{ eapply _ksim_mon. }
    inv KSIM.

    { pfold. eapply pind10_fold. econs; eauto. }

    { clear rr IH. pfold. eapply pind10_fold. eapply ksim_ret_cont; eauto. i.
      specialize (KSIM0 tid0). des; eauto. right.
      esplits; eauto.
      - i; hexploit KSIM2; clear KSIM2 KSIM3; eauto. i. eapply upaco10_mon_bot; eauto.
      - i; hexploit KSIM3; clear KSIM2 KSIM3; eauto. i. des. esplits; eauto. i. eapply upaco10_mon_bot; eauto.
    }

    { clear rr IH. pfold. eapply pind10_fold. eapply ksim_sync; eauto. i.
      specialize (KSIM0 tid0). des; eauto. right.
      esplits; eauto.
      - i; hexploit KSIM2; clear KSIM2 KSIM3; eauto. i. des. esplits; eauto. i. eapply upaco10_mon_bot; eauto.
      - i; hexploit KSIM3; clear KSIM2 KSIM3; eauto. i. des. esplits; eauto. i. eapply upaco10_mon_bot; eauto.
    }

    { des. pfold. eapply pind10_fold. eapply ksim_yieldL. esplits; eauto. split; ss.
      destruct KSIM1 as [KSIM1 IND]. hexploit IH; eauto. i. punfold H.
    }

    { pfold. eapply pind10_fold. eapply ksim_tauL. split; ss.
      destruct KSIM0 as [KSIM0 IND]. hexploit IH; eauto. i. punfold H.
    }

    { des. pfold. eapply pind10_fold. eapply ksim_chooseL. esplits. split; ss.
      destruct KSIM0 as [KSIM0 IND]. hexploit IH; eauto. i. punfold H.
    }

    { pfold. eapply pind10_fold. eapply ksim_stateL. split; ss.
      destruct KSIM0 as [KSIM0 IND]. hexploit IH; eauto. i. punfold H.
    }

    { pfold. eapply pind10_fold. eapply ksim_tidL. split; ss.
      destruct KSIM0 as [KSIM0 IND]. hexploit IH; eauto. i. punfold H.
    }

    { pfold. eapply pind10_fold. eapply ksim_UB. }

    { des. pfold. eapply pind10_fold. eapply ksim_fairL. esplits; eauto. split; ss.
      destruct KSIM1 as [KSIM1 IND]. hexploit IH; eauto. i. punfold H.
    }

    { pfold. eapply pind10_fold. eapply ksim_tauR. split; ss.
      destruct KSIM0 as [KSIM0 IND]. hexploit IH; eauto. i. punfold H.
    }

    { pfold. eapply pind10_fold. eapply ksim_chooseR. i. split; ss. specialize (KSIM0 x).
      destruct KSIM0 as [KSIM0 IND]. hexploit IH; eauto. i. punfold H.
    }

    { pfold. eapply pind10_fold. eapply ksim_stateR. split; ss.
      destruct KSIM0 as [KSIM0 IND]. hexploit IH; eauto. i. punfold H.
    }

    { pfold. eapply pind10_fold. eapply ksim_tidR. split; ss.
      destruct KSIM0 as [KSIM0 IND]. hexploit IH; eauto. i. punfold H.
    }

    { pfold. eapply pind10_fold. eapply ksim_fairR. i. split; ss. specialize (KSIM0 _ FAIR).
      destruct KSIM0 as [KSIM0 IND]. hexploit IH; eauto. i. punfold H.
    }

    { pfold. eapply pind10_fold. eapply ksim_observe. i. specialize (KSIM0 ret). pclearbot.
      right; eapply CIH; eauto.
    }

    { pfold. eapply pind10_fold. eapply ksim_call. }

    { hexploit SRC; ss; i; clarify. hexploit TGT; ss; i; clarify.
      pfold. eapply pind10_fold. eapply ksim_progress. pclearbot.
      right; eapply CIH; eauto.
    }

  Qed.

  Lemma ksim_set_prog
        R0 R1 (RR: R0 -> R1 -> Prop)
        ths_src ths_tgt tid rs_local
        ssrc tgt shr o
        (KSIM: sim_knot RR ths_src ths_tgt tid rs_local true true ssrc tgt shr o)
    :
    forall ps pt, sim_knot RR ths_src ths_tgt tid rs_local ps pt ssrc tgt shr o.
  Proof.
    revert_until RR. pcofix CIH. i.
    remember true as ps1 in KSIM at 1. remember true as pt1 in KSIM at 1.
    move KSIM before CIH. revert_until KSIM. punfold KSIM.
    pattern ths_src, ths_tgt, tid, rs_local, ps1, pt1, ssrc, tgt, shr, o.
    revert ths_src ths_tgt tid rs_local ps1 pt1 ssrc tgt shr o KSIM.
    eapply pind10_acc.
    intros rr DEC IH ths_src ths_tgt tid rs_local ps1 pt1 ssrc tgt shr o KSIM. clear DEC.
    intros Eps1 Ept1 ps pt. clarify.
    eapply pind10_unfold in KSIM.
    2:{ eapply _ksim_mon. }
    inv KSIM.

    { pfold. eapply pind10_fold. econs; eauto. }

    { clear rr IH. pfold. eapply pind10_fold. eapply ksim_ret_cont; eauto. i.
      specialize (KSIM0 tid0). des; eauto. right.
      esplits; eauto.
      - i; hexploit KSIM2; clear KSIM2 KSIM3; eauto. i. eapply upaco10_mon_bot; eauto.
      - i; hexploit KSIM3; clear KSIM2 KSIM3; eauto. i. des. esplits; eauto.
        i. eapply upaco10_mon_bot; eauto.
    }

    { clear rr IH. pfold. eapply pind10_fold. eapply ksim_sync; eauto. i.
      specialize (KSIM0 tid0). des; eauto. right.
      esplits; eauto.
      - i; hexploit KSIM2; clear KSIM2 KSIM3; eauto. i. des. esplits; eauto. i. eapply upaco10_mon_bot; eauto.
      - i; hexploit KSIM3; clear KSIM2 KSIM3; eauto. i. des. esplits; eauto. i. eapply upaco10_mon_bot; eauto.
    }

    { des. pfold. eapply pind10_fold. eapply ksim_yieldL. esplits; eauto. split; ss.
      destruct KSIM1 as [KSIM1 IND]. hexploit IH; eauto. i. punfold H.
    }

    { pfold. eapply pind10_fold. eapply ksim_tauL. split; ss.
      destruct KSIM0 as [KSIM0 IND]. hexploit IH; eauto. i. punfold H.
    }

    { des. pfold. eapply pind10_fold. eapply ksim_chooseL. esplits. split; ss.
      destruct KSIM0 as [KSIM0 IND]. hexploit IH; eauto. i. punfold H.
    }

    { pfold. eapply pind10_fold. eapply ksim_stateL. split; ss.
      destruct KSIM0 as [KSIM0 IND]. hexploit IH; eauto. i. punfold H.
    }

    { pfold. eapply pind10_fold. eapply ksim_tidL. split; ss.
      destruct KSIM0 as [KSIM0 IND]. hexploit IH; eauto. i. punfold H.
    }

    { pfold. eapply pind10_fold. eapply ksim_UB. }

    { des. pfold. eapply pind10_fold. eapply ksim_fairL. esplits; eauto. split; ss.
      destruct KSIM1 as [KSIM1 IND]. hexploit IH; eauto. i. punfold H.
    }

    { pfold. eapply pind10_fold. eapply ksim_tauR. split; ss.
      destruct KSIM0 as [KSIM0 IND]. hexploit IH; eauto. i. punfold H.
    }

    { pfold. eapply pind10_fold. eapply ksim_chooseR. i. split; ss. specialize (KSIM0 x).
      destruct KSIM0 as [KSIM0 IND]. hexploit IH; eauto. i. punfold H.
    }

    { pfold. eapply pind10_fold. eapply ksim_stateR. split; ss.
      destruct KSIM0 as [KSIM0 IND]. hexploit IH; eauto. i. punfold H.
    }

    { pfold. eapply pind10_fold. eapply ksim_tidR. split; ss.
      destruct KSIM0 as [KSIM0 IND]. hexploit IH; eauto. i. punfold H.
    }

    { pfold. eapply pind10_fold. eapply ksim_fairR. i. split; ss. specialize (KSIM0 _ FAIR).
      destruct KSIM0 as [KSIM0 IND]. hexploit IH; eauto. i. punfold H.
    }

    { pfold. eapply pind10_fold. eapply ksim_observe. i. specialize (KSIM0 ret). pclearbot.
      right; eapply CIH; eauto.
    }

    { pfold. eapply pind10_fold. eapply ksim_call. }

    { pclearbot. eapply paco10_mon_bot; eauto. eapply ksim_reset_prog. eauto. all: auto. }

  Qed.

End KSIM.
#[export] Hint Constructors __sim_knot: core.
#[export] Hint Unfold sim_knot: core.
#[export] Hint Resolve __ksim_mon: paco.
#[export] Hint Resolve _ksim_mon: paco.
#[export] Hint Resolve ksim_mon: paco.
