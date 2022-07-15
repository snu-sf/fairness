From sflib Require Import sflib.
From ITree Require Export ITree.
From Paco Require Import paco.

Export ITreeNotations.

Require Import Coq.Classes.RelationClasses.
Require Import Program.

From Fairness Require Import ITreeLib.
From Fairness Require Import FairBeh.
From Fairness Require Import FairSim.

From Fairness Require Import SelectBeh.
From Fairness Require Import BehEquiv BehEquivSelect.

Require Import Setoid Morphisms.

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
          psrc0 ptgt0 ssrc0 stgt0
          (SIM: gsim (ids:=ids) (idt:=idt) wfs wft (@eq R) psrc0 ptgt0 ssrc0 stgt0)
    :
    <<IMPR: Beh.improves (ids:=ids) (idt:=idt) (wfs:=wfs) (wft:=wft) ssrc0 stgt0>>.
  Proof.
    ii. specialize (SIM mtgt). des. exists ms. rename mtgt into mtgt0, ms into msrc0. intro PR.
    ginit. revert_until R. gcofix CIH.
    i. revert psrc0 ptgt0 msrc0 ssrc0 SIM.
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

  Context {Ident: ID}.

  Definition FairBeh_of_state {R} (st: @state _ R) (obs: @Tr.t R): Prop :=
    exists (raw: @RawTr.t _ R), (extract_tr raw obs) /\ (RawBeh.of_state_fair st raw).

  Definition improves {R} (src tgt: @state _ R) :=
    forall (obs_tr: @Tr.t R),
      (FairBeh_of_state tgt obs_tr) -> (FairBeh_of_state src obs_tr).


  Hypothesis ID_DEC: forall (i0 i1: Ident.(id)), {i0 = i1} + {i0 <> i1}.

  Variable wfs: WF.
  Variable wfs0: T wfs.
  Hypothesis WFSTR: Transitive wfs.(lt).

  Variable wft: WF.
  Variable wft0: T wft.
  Variable St: wft.(T) -> wft.(T).
  Hypothesis lt_succ_diag_r_t: forall (t: wft.(T)), wft.(lt) t (St t).

  Theorem adequacy
          R
          psrc ptgt src tgt
          (SIM: gsim wfs wft (@eq R) psrc ptgt src tgt)
    :
    improves src tgt.
  Proof.
    eapply global_adequacy in SIM. intros obs TGT. unfold FairBeh_of_state in *. des.
    unfold RawBeh.of_state_fair in TGT0. des.
    eapply Fair_implies_Ind in FAIR.
    eapply (@Ind_implies_Ord _ wft wft0) in FAIR; eauto.
    hexploit SelectBeh_implies_IndexBeh; eauto. split; eauto.
    i; des. unfold Beh.improves in SIM. specialize (SIM obs im). des.
    hexploit (@IndexBeh_implies_SelectBeh _ wfs). eauto.
    { eexists. eapply SIM. eauto. hexploit (extract_tr_inj_tr TGT EXTRACT).
      i. rewrite H; clear H. eauto. }
    i; des. esplits. eapply EXTRACT0. destruct BEH1. des. split; eauto.
    eapply (@Ord_implies_Fair _ _ wfs); eauto.
    Unshelve. exact ID_DEC.
  Qed.

End ADEQ2.
