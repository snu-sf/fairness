From sflib Require Import sflib.
From Paco Require Import paco.

Require Import Coq.Classes.RelationClasses.
Require Import Program.
From iris.algebra Require Import cmra.

From Fairness Require Import Axioms.
From Fairness Require Export ITreeLib FairBeh FairSim NatStructsLarge.
From Fairness Require Import pind PCM World.
From Fairness Require Import Mod ModSimStid ModSimNoSync.

Set Implicit Arguments.

Section PROOF.

  Context `{M: ucmra}.

  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable _ident_src: ID.
  Definition ident_src := sum_tid _ident_src.
  Variable _ident_tgt: ID.
  Definition ident_tgt := sum_tid _ident_tgt.

  Variable wf_src: WF.
  Variable wf_tgt: WF.

  Let srcE := threadE _ident_src state_src.
  Let tgtE := threadE _ident_tgt state_tgt.

  Let shared :=
        (TIdSet.t *
           (@imap ident_src wf_src) *
           (@imap ident_tgt wf_tgt) *
           state_src *
           state_tgt)%type.
  Let shared_rel: Type := shared -> Prop.
  Variable I: shared -> (cmra_car M) -> Prop.

  Theorem stid_implies_nosync
          tid
          R0 R1 (RR: R0 -> R1 -> (cmra_car M) -> shared_rel)
          ps pt r_ctx src tgt
          (shr: shared)
          (LSIM: ModSimStid.lsim I tid RR ps pt r_ctx src tgt shr)
    :
    ModSimNoSync.lsim I tid RR ps pt r_ctx src tgt shr.
  Proof.
    revert_until tid. pcofix CIH; i.
    punfold LSIM.
    pattern R0, R1, RR, ps, pt, r_ctx, src, tgt, shr.
    revert R0 R1 RR ps pt r_ctx src tgt shr LSIM. apply pind9_acc.
    intros rr DEC IH. clear DEC. intros R0 R1 RR ps pt r_ctx src tgt shr LSIM.
    eapply pind9_unfold in LSIM.
    2:{ eapply ModSimStid._lsim_mon. }
    inv LSIM.

    { pfold. eapply pind9_fold. econs 1; eauto. }
    { pfold. eapply pind9_fold. econs 2; eauto.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 3; eauto.
      des. exists x.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 4; eauto.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 5; eauto.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 6; eauto. }
    { pfold. eapply pind9_fold. econs 7; eauto.
      des. esplits; eauto.
      split; ss. destruct LSIM as [LSIM IND]. eapply IH in IND. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 8; eauto.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 9; eauto.
      i. specialize (LSIM0 x).
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 10; eauto.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 11; eauto.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 12; eauto.
      i. specialize (LSIM0 _ FAIR).
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND.
    }

    { pfold. eapply pind9_fold. econs 13; eauto.
      i. specialize (LSIM0 ret). pclearbot.
      split; ss. eapply pind9_fold. eapply ModSimNoSync.lsim_progress.
      right. eapply CIH; eauto. eapply ModSimStid.lsim_set_prog. auto.
    }

    { pfold. eapply pind9_fold. eapply lsim_call. }

    { pfold. eapply pind9_fold. eapply ModSimNoSync.lsim_yieldL.
      des. esplits; eauto.
      split; ss. destruct LSIM as [LSIM IND]. eapply IH in IND. punfold IND.
    }

    { pfold. eapply pind9_fold. eapply ModSimNoSync.lsim_yieldR; eauto.
      i. specialize (LSIM0 _ _ _ _ _ _ _ INV0 VALID0 _ TGT).
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND.
    }

    { pfold. eapply pind9_fold. eapply ModSimNoSync.lsim_yieldR; eauto.
      i. specialize (LSIM0 _ _ _ _ _ _ _ INV0 VALID0 _ TGT).
      split; ss. eapply pind9_fold. eapply ModSimNoSync.lsim_yieldL.
      des. esplits. eapply FAIR. split; ss. pclearbot.
      eapply pind9_fold. eapply ModSimNoSync.lsim_progress. right.
      eapply CIH. apply ModSimStid.lsim_set_prog; auto.
    }

    { pfold. eapply pind9_fold. eapply ModSimNoSync.lsim_progress. right.
      eapply CIH. pclearbot. auto.
    }

  Qed.

End PROOF.

Section MODSIM.

  Lemma stid_implies_nosync_mod
        md_src md_tgt
        (MDSIM: ModSimStid.ModSim.mod_sim md_src md_tgt)
    :
    ModSimNoSync.ModSim.mod_sim md_src md_tgt.
  Proof.
    inv MDSIM.
    set (_ident_src := Mod.ident md_src). set (_ident_tgt := Mod.ident md_tgt).
    set (state_src := Mod.state md_src). set (state_tgt := Mod.state md_tgt).
    set (srcE := threadE _ident_src state_src).
    set (tgtE := threadE _ident_tgt state_tgt).
    set (ident_src := @ident_src _ident_src).
    set (ident_tgt := @ident_tgt _ident_tgt).
    set (shared := (TIdSet.t * (@imap ident_src wf_src) * (@imap ident_tgt wf_tgt) * state_src * state_tgt)%type).
    econs; eauto.
    i. specialize (init im_tgt). des. rename init0 into funs. exists I. esplits; eauto.
    i. specialize (funs fn args). des_ifs.
    unfold ModSimStid.local_sim in funs.
    ii. specialize (funs _ _ _ _ _ _ _ INV tid _ THS VALID _ UPD).
    des. esplits; eauto.
    i. specialize (funs1 _ _ _ _ _ _ _ INV1 VALID1 _ TGT).
    des. esplits; eauto. i. specialize (LSIM fs ft).
    eapply stid_implies_nosync in LSIM. apply LSIM.
  Qed.

End MODSIM.

Section USERSIM.

  Lemma stid_implies_nosync_user
        md_src md_tgt p_src p_tgt
        (MDSIM: ModSimStid.UserSim.sim md_src md_tgt p_src p_tgt)
    :
    ModSimNoSync.UserSim.sim md_src md_tgt p_src p_tgt.
  Proof.
    inv MDSIM.
    set (_ident_src := Mod.ident md_src). set (_ident_tgt := Mod.ident md_tgt).
    set (state_src := Mod.state md_src). set (state_tgt := Mod.state md_tgt).
    set (ident_src := @ident_src _ident_src).
    set (ident_tgt := @ident_tgt _ident_tgt).
    set (shared := (TIdSet.t * (@imap ident_src wf_src) * (@imap ident_tgt wf_tgt) * state_src * state_tgt)%type).
    econs; eauto.
    i. specialize (funs im_tgt). des. esplits; eauto.
    eapply nm_find_some_implies_forall3.
    { apply nm_forall2_wf_pair. eapply list_forall3_implies_forall2_2; eauto. clear. i. des. des_ifs. des; clarify. }
    { apply nm_forall2_wf_pair. eapply list_forall3_implies_forall2_3; eauto. clear. i. des. des_ifs. des; clarify. }
    i. eapply nm_forall3_implies_find_some in SIM; eauto.
    unfold ModSimStid.local_sim_init in SIM. ii. specialize (SIM _ _ _ _ _ _ _ INV VALID _ FAIR). des. esplits; eauto.
    i. eapply stid_implies_nosync. eauto.
  Qed.

End USERSIM.
