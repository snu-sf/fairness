From sflib Require Import sflib.
From Paco Require Import paco.

Require Import Coq.Classes.RelationClasses.
Require Import Program.

From Fairness Require Import ITreeLib WFLibLarge.
From Fairness Require Import FairBeh.
From Fairness Require Import FairSim.

From Fairness Require Import SelectBeh.
From Fairness Require Import BehEquiv BehEquivSelect.

Require Import Setoid Morphisms.
From Fairness Require Import Axioms.

Set Implicit Arguments.

Section ADEQ.

  Variable ids: ID.
  Variable idt: ID.
  Variable wfs: WF.
  Variable wft: WF.

  Lemma adequacy_spin
        R0 R1 (RR: R0 -> R1 -> Prop)
        psrc0 ptgt0 msrc0 mtgt0 ssrc0 stgt0
        (SIM: sim (ids:=ids) (idt:=idt) (wfs:=wfs) (wft:=wft) RR psrc0 msrc0 ptgt0 mtgt0 ssrc0 stgt0)
        (SPIN: Beh.diverge_index mtgt0 stgt0)
    :
    <<SPIN: Beh.diverge_index msrc0 ssrc0>>.
  Proof.
    ginit. revert_until RR. gcofix CIH. i. revert SPIN.
    induction SIM using @sim_ind2; i; clarify.
    { exfalso. punfold SPIN. inv SPIN. }
    { exfalso. punfold SPIN. inv SPIN. }
    { gstep. econs. eapply gpaco3_mon. eapply IHSIM; eauto. i. inv PR. auto.
    }
    { punfold SPIN. inv SPIN. pclearbot. eauto. }
    { des. gstep. rewrite bind_trigger. econs. eapply gpaco3_mon. eapply IH; eauto.
      i. inv PR. auto.
    }
    { punfold SPIN. rewrite bind_trigger in SPIN. inv SPIN. eapply inj_pair2 in H3. clarify.
      pclearbot. eapply SIM. eauto.
    }
    { des. gstep. rewrite bind_trigger. econs.
      { eapply gpaco3_mon. eapply IH; eauto. i. inv PR. auto. }
      auto.
    }
    { punfold SPIN. rewrite bind_trigger in SPIN. inv SPIN. eapply inj_pair2 in H2. clarify.
      pclearbot. eapply SIM; eauto.
    }
    { remember false in SIM at 1. remember false in SIM at 1.
      revert Heqb. clear Heqb0. revert SPIN.
      induction SIM using @sim_ind2; i; clarify.
      { exfalso. punfold SPIN. inv SPIN. }
      { exfalso. punfold SPIN. inv SPIN. }
      { clear IHSIM. gstep. econs. gbase. eapply CIH; eauto. }
      { punfold SPIN. inv SPIN. pclearbot; eauto. }
      { des. clear IH. gstep. rewrite bind_trigger. econs. gbase. eapply CIH; eauto. }
      { rewrite bind_trigger in SPIN. punfold SPIN. inv SPIN. eapply inj_pair2 in H3. clarify.
        pclearbot. eapply SIM; eauto.
      }
      { des. clear IH. gstep. rewrite bind_trigger. econs. gbase. eapply CIH; eauto. auto. }
      { rewrite bind_trigger in SPIN. punfold SPIN. inv SPIN. eapply inj_pair2 in H2. clarify.
        pclearbot. eapply SIM; eauto.
      }
      { rewrite bind_trigger. gstep. econs. }
    }
    { rewrite bind_trigger. gstep. econs. }
  Qed.

  Theorem global_adequacy
          R
          ssrc0 stgt0
          (SIM: gsim (ids:=ids) (idt:=idt) wfs wft (@eq R) ssrc0 stgt0)
    :
    <<IMPR: Beh.improves (ids:=ids) (idt:=idt) (wfs:=wfs) (wft:=wft) ssrc0 stgt0>>.
  Proof.
    ii. specialize (SIM mtgt). des. exists ms. rename mtgt into mtgt0, ms into msrc0. intro PR.
    revert SIM. ginit. revert_until R. gcofix CIH.
    i. revert ps pt msrc0 ssrc0 SIM.
    induction PR using @Beh.of_state_ind2; ii.
    { match goal with
      | SIM: sim _ _ _ _ _ _ ?a |- _ => remember a as stgt0
      end.
      rename imap0 into mtgt0. depgen retv.
      induction SIM using @sim_ind2; i; ss; clarify; eauto.
      { gstep. econs 1. }
      { guclo (@Beh.of_state_indC_spec ids). econs. eauto. }
      { des. rewrite bind_trigger. guclo (@Beh.of_state_indC_spec ids). econs; eauto. }
      { rewrite bind_trigger in Heqstgt0. clarify. }
      { des. rewrite bind_trigger. guclo Beh.of_state_indC_spec. econs; eauto. }
      { rewrite bind_trigger in Heqstgt0. clarify. }
      { remember false in SIM at 1. remember false in SIM at 1.
        clear Heqb. revert Heqb0.
        match goal with
        | SIM: sim _ _ _ _ _ _ ?a |- _ => remember a as itr_tgt0
        end.
        depgen retv.
        induction SIM using @sim_ind2; ii; ss; clarify; eauto.
        { gstep. econs 1. }
        { guclo Beh.of_state_indC_spec. econs. eauto. }
        { des. rewrite bind_trigger. guclo Beh.of_state_indC_spec. econs; eauto. }
        { rewrite bind_trigger in Heqitr_tgt0. clarify. }
        { des. rewrite bind_trigger. guclo Beh.of_state_indC_spec. econs; eauto. }
        { rewrite bind_trigger in Heqitr_tgt0. clarify. }
        { gstep. rewrite bind_trigger. econs. }
      }
      { gstep. rewrite bind_trigger. econs. }
    }

    { gstep. econs 2. eapply adequacy_spin; eauto. }
    { gstep. econs 3. }
    { depgen tl.
      match goal with
      | SIM: sim _ _ _ _ _ _ ?a |- _ => remember a as stgt0
      end.
      revert fn args rv ktr Heqstgt0. rename imap0 into mtgt0.
      induction SIM using @sim_ind2; ii; ss; clarify.
      { eapply inj_pair2 in H0. clarify. gstep. econs. gfinal. left; eapply CIH; eauto. }
      { guclo Beh.of_state_indC_spec. econs 5. eapply IHSIM; eauto. }
      { des. guclo Beh.of_state_indC_spec. rewrite bind_trigger. econs 6; eauto. }
      { rewrite bind_trigger in Heqstgt0. inv Heqstgt0. }
      { des. guclo Beh.of_state_indC_spec. rewrite bind_trigger. econs 7; eauto. }
      { rewrite bind_trigger in Heqstgt0. inv Heqstgt0. }
      { remember false in SIM at 1. remember false in SIM at 1.
        clear Heqb. revert Heqb0. revert_until SIM.
        match goal with
        | SIM: sim _ _ _ _ _ _ ?a |- _ => remember a as itr_tgt0
        end.
        revert fn args ktr Heqitr_tgt0.
        induction SIM using @sim_ind2; ii; ss; clarify.
        { eapply inj_pair2 in H0. clarify. gstep. econs. gfinal. left; eapply CIH; eauto. }
        { guclo Beh.of_state_indC_spec. econs 5. eapply IHSIM; eauto. }
        { des. guclo Beh.of_state_indC_spec. rewrite bind_trigger. econs 6; eauto. }
        { rewrite bind_trigger in Heqitr_tgt0. inv Heqitr_tgt0. }
        { des. guclo Beh.of_state_indC_spec. rewrite bind_trigger. econs 7; eauto. }
        { rewrite bind_trigger in Heqitr_tgt0. inv Heqitr_tgt0. }
        { rewrite bind_trigger. gstep. econs 8. }
      }
      { rewrite bind_trigger. gstep. econs 8. }
    }

    { rename imap0 into mtgt0.
      match goal with
      | SIM: sim _ _ _ _ _ _ ?a |- _ => remember a as stgt0
      end.
      depgen itr. revert tr. induction SIM using @sim_ind2; ii; ss; clarify; eauto.
      { guclo Beh.of_state_indC_spec. econs; eauto. }
      { des. rewrite bind_trigger. guclo Beh.of_state_indC_spec. econs; eauto. }
      { rewrite bind_trigger in Heqstgt0. clarify. }
      { des. rewrite bind_trigger. guclo Beh.of_state_indC_spec. econs; eauto. }
      { rewrite bind_trigger in Heqstgt0. clarify. }
      { remember false in SIM at 1. remember false in SIM at 1.
        clear Heqb. revert Heqb0.
        match goal with
        | SIM: sim _ _ _ _ _ _ ?a |- _ => remember a as itr_tgt0
        end.
        depgen itr. revert tr. induction SIM using @sim_ind2; ii; ss; clarify; eauto.
        { guclo Beh.of_state_indC_spec. econs; eauto. }
        { des. rewrite bind_trigger. guclo Beh.of_state_indC_spec. econs; eauto. }
        { rewrite bind_trigger in Heqitr_tgt0. clarify. }
        { des. rewrite bind_trigger. guclo Beh.of_state_indC_spec. econs; eauto. }
        { rewrite bind_trigger in Heqitr_tgt0. clarify. }
      }
    }

    { rename imap0 into mtgt0.
      match goal with
      | SIM: sim _ _ _ _ _ _ ?a |- _ => remember a as stgt0
      end.
      depgen ktr. revert tr. revert X x.
      induction SIM using @sim_ind2; ii; ss; clarify; eauto.
      { guclo Beh.of_state_indC_spec. econs; eauto. }
      { des. rewrite bind_trigger. guclo Beh.of_state_indC_spec. econs; eauto. }
      { rewrite bind_trigger in Heqstgt0. clarify. eapply inj_pair2 in H0. clarify.
        specialize (SIM x). des. clear IH. eauto. }
      { des. rewrite bind_trigger. guclo Beh.of_state_indC_spec. econs; eauto. }
      { rewrite bind_trigger in Heqstgt0. clarify. }
      { remember false in SIM at 1. remember false in SIM at 1.
        clear Heqb. revert Heqb0.
        match goal with
        | SIM: sim _ _ _ _ _ _ ?a |- _ => remember a as itr_tgt0
        end.
        depgen ktr. revert tr. revert X x.
        induction SIM using @sim_ind2; ii; ss; clarify; eauto.
        { guclo Beh.of_state_indC_spec. econs; eauto. }
        { des. rewrite bind_trigger. guclo Beh.of_state_indC_spec. econs; eauto. }
        { rewrite bind_trigger in Heqitr_tgt0. clarify. eapply inj_pair2 in H0. clarify.
          specialize (SIM x). des. clear IH. eauto. }
        { des. rewrite bind_trigger. guclo Beh.of_state_indC_spec. econs; eauto. }
        { rewrite bind_trigger in Heqitr_tgt0. clarify. }
      }
    }

    { rename imap0 into mtgt0.
      match goal with
      | SIM: sim _ _ _ _ _ _ ?a |- _ => remember a as stgt0
      end.
      depgen ktr. revert tr. revert fmap imap1 FAIR.
      induction SIM using @sim_ind2; ii; ss; clarify; eauto.
      { guclo Beh.of_state_indC_spec. econs; eauto. }
      { des. rewrite bind_trigger. guclo Beh.of_state_indC_spec. econs; eauto. }
      { rewrite bind_trigger in Heqstgt0. clarify. }
      { des. rewrite bind_trigger. guclo Beh.of_state_indC_spec. econs; eauto. }
      { rewrite bind_trigger in Heqstgt0. clarify. eapply inj_pair2 in H0. clarify.
        specialize (SIM imap1 FAIR). des. clear IH. eauto. }
      { remember false in SIM at 1. remember false in SIM at 1.
        clear Heqb. revert Heqb0.
        match goal with
        | SIM: sim _ _ _ _ _ _ ?a |- _ => remember a as itr_tgt0
        end.
        depgen ktr. revert tr. revert fmap imap1 FAIR.
        induction SIM using @sim_ind2; ii; ss; clarify; eauto.
        { guclo Beh.of_state_indC_spec. econs; eauto. }
        { des. rewrite bind_trigger. guclo Beh.of_state_indC_spec. econs; eauto. }
        { rewrite bind_trigger in Heqitr_tgt0. clarify. }
        { des. rewrite bind_trigger. guclo Beh.of_state_indC_spec. econs; eauto. }
        { rewrite bind_trigger in Heqitr_tgt0. clarify. eapply inj_pair2 in H0. clarify.
          specialize (SIM imap1 FAIR). des. clear IH. eauto. }
      }
    }

    { rename imap0 into mtgt0.
      match goal with
      | SIM: sim _ _ _ _ _ _ ?a |- _ => remember a as stgt0
      end.
      depgen ktr. revert tr.
      induction SIM using @sim_ind2; ii; ss; clarify; eauto.
      { guclo Beh.of_state_indC_spec. econs; eauto. }
      { des. rewrite bind_trigger. guclo Beh.of_state_indC_spec. econs; eauto. }
      { rewrite bind_trigger in Heqstgt0. clarify. }
      { des. rewrite bind_trigger. guclo Beh.of_state_indC_spec. econs; eauto. }
      { rewrite bind_trigger in Heqstgt0. inv Heqstgt0. }
      { remember false in SIM at 1. remember false in SIM at 1.
        clear Heqb. revert Heqb0.
        match goal with
        | SIM: sim _ _ _ _ _ _ ?a |- _ => remember a as itr_tgt0
        end.
        depgen ktr. revert tr.
        induction SIM using @sim_ind2; ii; ss; clarify; eauto.
        { guclo Beh.of_state_indC_spec. econs; eauto. }
        { des. rewrite bind_trigger. guclo Beh.of_state_indC_spec. econs; eauto. }
        { rewrite bind_trigger in Heqitr_tgt0. clarify. }
        { des. rewrite bind_trigger. guclo Beh.of_state_indC_spec. econs; eauto. }
        { rewrite bind_trigger in Heqitr_tgt0. inv Heqitr_tgt0. }
        { gstep. rewrite bind_trigger. econs. }
      }
      gstep. rewrite bind_trigger. econs.
    }
    Unshelve. all: exact true.
  Qed.

End ADEQ.


Section ADEQ2.
  Definition FairBeh_of_state {id: ID} {R} (st: @state id R) (obs: @Tr.t R): Prop :=
    exists (raw: @RawTr.t _ R), (extract_tr raw obs) /\ (RawBeh.of_state_fair st raw).

  Definition improves (ids idt: ID) {R}
             (src: @state ids R) (tgt: @state idt R) :=
    forall (obs_tr: @Tr.t R),
      (FairBeh_of_state tgt obs_tr) -> (FairBeh_of_state src obs_tr).

  Lemma improves_trans
        (id1 id2 id3: ID) R
        (st1: @state id1 R)
        (st2: @state id2 R)
        (st3: @state id3 R)
        (IMP1: improves st2 st1)
        (IMP2: improves st3 st2)
    :
    improves st3 st1.
  Proof.
    ii. eapply IMP2. eapply IMP1. auto.
  Qed.

  Variable ids: ID.
  Variable idt: ID.
  Variable wfs: WF.
  Variable wft: WF.

  Hypothesis wft_inhabited: inhabited wft.(T).
  Hypothesis wft_open: forall (o0: wft.(T)), exists o1, wft.(lt) o0 o1.


  (* Auxilary Definitions *)
  Let wfs_lift_T := option wfs.(T).
  Let wfs_lift_lt: wfs_lift_T -> wfs_lift_T -> Prop :=
        fun o0 o1 =>
          match o0, o1 with
          | Some o0, Some o1 => (clos_trans_n1 _ wfs.(lt)) o0 o1
          | _, _ => False
          end.
  Program Let wfs_lift: WF := @mk_wf wfs_lift_T wfs_lift_lt _.
  Next Obligation.
  Proof.
    ii. destruct a.
    2:{ econs. ii. destruct y; ss. }
    induction (clos_trans_well_founded wfs.(wf) t).
    econs. i. destruct y; ss. eauto.
  Qed.
  Let wfs_embed: wfs.(T) -> wfs_lift.(T) := fun o => Some o.
  #[clearbody]
  Let wfs_embed_lt: forall o0 o1 (LT: wfs.(lt) o0 o1), wfs_lift.(lt) (wfs_embed o0) (wfs_embed o1).
  Proof.
    i. ss. econs 1. eauto.
  Defined.
  Let wfs0: wfs_lift.(T) := None.
  #[clearbody]
  Let WFSTR: Transitive wfs_lift.(lt).
  Proof.
    ii. destruct x, y, z; ss.
    eapply Operators_Properties.clos_tn1_trans in H.
    eapply Operators_Properties.clos_tn1_trans in H0.
    eapply Operators_Properties.clos_trans_tn1_iff. econs 2; eauto.
  Defined.
  Let wft0: wft.(T) := @epsilon _ wft_inhabited (fun _ => True).
  Let St: wft.(T) -> wft.(T) := fun o0 => @epsilon _ wft_inhabited (fun o1 => wft.(lt) o0 o1).
  #[clearbody]
  Let lt_succ_diag_r_t: forall (t: wft.(T)), wft.(lt) t (St t).
  Proof.
    i. unfold St.
    hexploit (@epsilon_spec _ wft_inhabited (fun o1 => wft.(lt) t o1)); eauto.
  Defined.

  Theorem adequacy
          R
          (src: @state ids R) (tgt: @state idt R)
          (SIM: gsim wfs wft (@eq R) src tgt)
    :
    improves src tgt.
  Proof.
    eapply gsim_embedded_src_ord in SIM.
    2:{ eapply wfs_embed_lt. }
    eapply global_adequacy in SIM. intros obs TGT. unfold FairBeh_of_state in *. des.
    unfold RawBeh.of_state_fair in TGT0. des.
    eapply Fair_implies_Ind in FAIR.
    eapply (@Ind_implies_Ord _ wft wft0) in FAIR; eauto.
    hexploit SelectBeh_implies_IndexBeh; eauto. split; eauto.
    i; des. unfold Beh.improves in SIM. specialize (SIM obs im). des.
    hexploit (@IndexBeh_implies_SelectBeh ids wfs_lift).
    { eauto. }
    { eexists. eapply SIM. eauto. hexploit (extract_tr_inj_tr TGT EXTRACT).
      i. rewrite H; clear H. eauto. }
    i; des. esplits. eapply EXTRACT0. destruct BEH1. des. split; eauto.
    eapply (@Ord_implies_Fair _ wfs_lift); eauto.
  Qed.

End ADEQ2.
