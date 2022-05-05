From sflib Require Import sflib.
From ITree Require Export ITree.
From Paco Require Import paco.

Export ITreeNotations.

Require Import Coq.Classes.RelationClasses.
Require Import Program.
Require Import Lia.

From Fairness Require Import ITreeLib.
From Fairness Require Import FairBeh.
From Fairness Require Import FairSim.

Set Implicit Arguments.

Section ADEQ.

  Ltac pc H := rr in H; desH H; ss.

  Context {Ident: ID}.

  Lemma adequacy_spin
        R0 R1 (RR: R0 -> R1 -> Prop)
        psrc0 ptgt0 msrc0 mtgt0 ssrc0 stgt0
        (SIM: sim RR psrc0 msrc0 ptgt0 mtgt0 ssrc0 stgt0)
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

  Theorem adequacy
          R0 R1 (RR: R0 -> R1 -> Prop)
          psrc0 ptgt0 msrc0 mtgt0 ssrc0 stgt0
          (SIM: sim RR psrc0 msrc0 ptgt0 mtgt0 ssrc0 stgt0)
    :
    <<IMPR: Beh.improves RR (Beh.of_state msrc0 ssrc0) (Beh.of_state mtgt0 stgt0)>>.
  Proof.
    ginit. revert_until RR. gcofix CIH.
    i. revert tr0 REL psrc0 ptgt0 msrc0 ssrc0 SIM.
    induction PR using @of_state_ind2; ii; ss.
    { punfold REL. inv REL. rename r0 into r_src, retv into r_tgt.
      revert r_src REL0.
      admit.
      (* induction SIM using @sim_ind2; i; ss; clarify. *)
      (* { guclo Beh.of_state_indC_spec. econs 1. *)
    }
    { punfold REL. inv REL. gstep. econs 2. eapply adequacy_spin; eauto. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }

  Admitted.

End ADEQ.
