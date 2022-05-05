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
    { (*TODO*)
      remember false in SIM at 1. remember false in SIM at 1.
      revert Heqb. clear Heqb0. revert SPIN. revert m_src m_tgt.
      induction SIM using @sim_ind2; i; clarify.
      { exfalso. punfold SPIN. inv SPIN. }
      { exfalso. punfold SPIN. inv SPIN. }
      { clear IHSIM. gstep. econs. gbase. eapply CIH. 2: eauto.

        eapply gpaco3_mon. eapply IHSIM; eauto. i. inv PR. auto. }
      { punfold SPIN. inv SPIN. pclearbot. 
      6:{ 

        gbase. eapply CIH. 

        eapply CIH. eapply SIM. eapply gpaco3_mon. eapply IHSIM; eauto. i. inv PR. auto. }
      6:{ gfinal.

        gfinal. left. eapply CIH; eauto.

        exfalso. punfold SPIN. inv SPIN. }

      eapply gpaco3_mon; eauto.

End ADEQ.
