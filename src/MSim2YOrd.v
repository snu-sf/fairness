From sflib Require Import sflib.
From Paco Require Import paco.
Require Export Coq.Strings.String.
Require Import Coq.Classes.RelationClasses.

From Fairness Require Export ITreeLib FairBeh Mod.
From Fairness Require Import pind PCM WFLib.
From Fairness Require Import ModSim ModSimYOrd GenYOrd.

Set Implicit Arguments.

Section PROOF.
  Context `{M: URA.t}.

  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable ident_src: ID.
  Variable _ident_tgt: ID.
  Let ident_tgt := @ident_tgt _ident_tgt.

  Variable wf_src: WF.
  Variable wf_tgt: WF.

  Let srcE := ((@eventE ident_src +' cE) +' sE state_src).
  Let tgtE := ((@eventE _ident_tgt +' cE) +' sE state_tgt).

  Let shared := shared state_src state_tgt ident_src _ident_tgt wf_src wf_tgt.
  Let shared_rel: Type := shared -> Prop.
  Variable I: shared_rel.

  Definition lift_wf (wf: WF): WF := sum_WF wf (option_WF wf).

  Definition mk_o {El Er} (wf: WF) R (o: wf.(T)) (pf: bool) (itr: itree ((El +' cE) +' Er) R): (lift_wf wf).(T) :=
    if pf
    then match (observe itr) with
         | VisF ((|Yield)|)%sum _ => (inr (Some o))
         | _ => (inr None)
         end
    else match (observe itr) with
         | VisF ((|Yield)|)%sum _ => (inl o)
         | _ => (inr None)
         end.

  Let A R0 R1 := (bool * bool * URA.car * (itree srcE R0) * (itree tgtE R1) * shared)%type.
  Let wf_ot R0 R1 := @ord_tree_WF (A R0 R1).
  Let wf_stt R0 R1 := lift_wf (@wf_ot R0 R1).

  Lemma modsim_implies_yord
        tid
        R0 R1 (LRR: R0 -> R1 -> URA.car -> shared_rel)
        ps pt r_ctx src tgt
        (shr: shared)
        (LSIM: ModSim.lsim I tid LRR ps pt r_ctx src tgt shr)
    :
    exists (os ot: (@wf_stt R0 R1).(T)),
      ModSimYOrd.lsim I wf_stt tid LRR ps pt r_ctx (os, src) (ot, tgt) shr.
  Proof.
    eapply modsim_implies_gensim in LSIM. eapply gensim_genos in LSIM. des.
    exists (mk_o (@wf_ot R0 R1) os pt tgt).
    exists (mk_o (@wf_ot R0 R1) ot ps src).
    revert_until tid. ginit. gcofix CIH; i.
    remember (os, src) as osrc. remember (ot, tgt) as otgt.
    move LSIM before CIH. revert_until LSIM.
    pattern R0, R1, LRR, ps, pt, r_ctx, osrc, otgt, shr.
    revert R0 R1 LRR ps pt r_ctx osrc otgt shr LSIM. apply pind9_acc.
    intros rr DEC IH. clear DEC. intros R0 R1 LRR ps pt r_ctx osrc otgt shr LSIM.
    i; clarify.
    eapply pind9_unfold in LSIM; eauto with paco.
    inv LSIM.

    { guclo lsim_indC_spec. econs 1; eauto. }

    { destruct GENOS as [GENOS IND]. eapply IH in IND; eauto.
      guclo lsim_indC_spec. econs 2; eauto.
      guclo lsim_ord_weakRC_spec. econs; eauto.
      clear. unfold mk_o. des_ifs; try reflexivity.
      - right. ss. do 2 econs.
      - right. ss. do 2 econs.
    }
    { des. destruct GENOS as [GENOS IND]. eapply IH in IND; eauto.
      guclo lsim_indC_spec. econs 3; eauto. exists x.
      guclo lsim_ord_weakRC_spec. econs; eauto.
      clear. unfold mk_o. des_ifs; try reflexivity.
      - right. ss. do 2 econs.
      - right. ss. do 2 econs.
    }
    { destruct GENOS as [GENOS IND]. eapply IH in IND; eauto.
      guclo lsim_indC_spec. econs 4; eauto.
      guclo lsim_ord_weakRC_spec. econs; eauto.
      clear. unfold mk_o. des_ifs; try reflexivity.
      - right. ss. do 2 econs.
      - right. ss. do 2 econs.
    }
    { destruct GENOS as [GENOS IND]. eapply IH in IND; eauto.
      guclo lsim_indC_spec. econs 5; eauto.
      guclo lsim_ord_weakRC_spec. econs; eauto.
      clear. unfold mk_o. des_ifs; try reflexivity.
      - right. ss. do 2 econs.
      - right. ss. do 2 econs.
    }
    { destruct GENOS as [GENOS IND]. eapply IH in IND; eauto.
      guclo lsim_indC_spec. econs 6; eauto.
      guclo lsim_ord_weakRC_spec. econs; eauto.
      clear. unfold mk_o. des_ifs; try reflexivity.
      - right. ss. do 2 econs.
      - right. ss. do 2 econs.
    }
    { guclo lsim_indC_spec. econs 7; eauto. }
    { des. destruct GENOS0 as [GENOS IND]. eapply IH in IND; eauto.
      guclo lsim_indC_spec. econs 8; eauto. esplits; eauto.
      guclo lsim_ord_weakRC_spec. econs; eauto.
      clear. unfold mk_o. des_ifs; try reflexivity.
      - right. ss. do 2 econs.
      - right. ss. do 2 econs.
    }

    { destruct GENOS as [GENOS IND]. eapply IH in IND; eauto.
      guclo lsim_indC_spec. econs 9; eauto.
      guclo lsim_ord_weakLC_spec. econs; eauto.
      clear. unfold mk_o. des_ifs; try reflexivity.
      - right. ss. do 2 econs.
      - right. ss. do 2 econs.
    }
    { guclo lsim_indC_spec. econs 10; eauto. i. specialize (GENOS x).
      destruct GENOS as [GENOS IND]. eapply IH in IND; eauto.
      guclo lsim_ord_weakLC_spec. econs; eauto.
      clear. unfold mk_o. des_ifs; try reflexivity.
      - right. ss. do 2 econs.
      - right. ss. do 2 econs.
    }
    { destruct GENOS as [GENOS IND]. eapply IH in IND; eauto.
      guclo lsim_indC_spec. econs 11; eauto.
      guclo lsim_ord_weakLC_spec. econs; eauto.
      clear. unfold mk_o. des_ifs; try reflexivity.
      - right. ss. do 2 econs.
      - right. ss. do 2 econs.
    }
    { destruct GENOS as [GENOS IND]. eapply IH in IND; eauto.
      guclo lsim_indC_spec. econs 12; eauto.
      guclo lsim_ord_weakLC_spec. econs; eauto.
      clear. unfold mk_o. des_ifs; try reflexivity.
      - right. ss. do 2 econs.
      - right. ss. do 2 econs.
    }
    { destruct GENOS as [GENOS IND]. eapply IH in IND; eauto.
      guclo lsim_indC_spec. econs 13; eauto.
      guclo lsim_ord_weakLC_spec. econs; eauto.
      clear. unfold mk_o. des_ifs; try reflexivity.
      - right. ss. do 2 econs.
      - right. ss. do 2 econs.
    }
    { guclo lsim_indC_spec. econs 14; eauto. i. specialize (GENOS _ FAIR).
      destruct GENOS as [GENOS IND]. eapply IH in IND; eauto.
      guclo lsim_ord_weakLC_spec. econs; eauto.
      clear. unfold mk_o. des_ifs; try reflexivity.
      - right. ss. do 2 econs.
      - right. ss. do 2 econs.
    }

    { guclo lsim_indC_spec. econs 15; eauto. i. specialize (GENOS ret).
      destruct GENOS as [GENOS IND]. eapply IH in IND; eauto.
      guclo lsim_ord_weakLC_spec. econs; eauto.
      guclo lsim_ord_weakRC_spec. econs; eauto.
      - clear. unfold mk_o. ss. des_ifs; try reflexivity.
        + right. ss. do 2 econs.
        + right. ss. do 2 econs.
      - clear. unfold mk_o. ss. des_ifs; try reflexivity.
        + right. ss. do 2 econs.
        + right. ss. do 2 econs.
    }

    { des. destruct GENOS0 as [GENOS IND]. eapply IH in IND; eauto.
      guclo lsim_indC_spec. econs 16; eauto.
      esplits; eauto.
      clear - LT. unfold mk_o. des_ifs; try reflexivity.
      - ss. do 2 econs. auto.
      - ss. do 1 econs. auto.
    }

    { guclo lsim_indC_spec. econs 17; eauto. i.
      specialize (GENOS _ _ _ _ _ _ _ INV0 VALID0 _ TGT). des.
      destruct GENOS0 as [GENOS IND]. eapply IH in IND; eauto.
      esplits; eauto.
      clear - LT. unfold mk_o. des_ifs; try reflexivity.
      - ss. do 2 econs. auto.
      - ss. do 1 econs. auto.
    }

    { guclo lsim_indC_spec. econs 18; eauto. i.
      specialize (GENOS _ _ _ _ _ _ _ INV0 VALID0 _ TGT). des.
      destruct GENOS0 as [GENOS IND]. eapply IH in IND; eauto.
    }

    { eapply gensim_genos in GENOS. des.
      guclo lsim_ord_weakLC_spec. econs.
      guclo lsim_ord_weakRC_spec. econs.
      instantiate (1:=mk_o (@wf_ot R0 R1) ot0 false src).
      instantiate (1:=mk_o (@wf_ot R0 R1) os0 false tgt).
      gfinal. right. pfold. eapply pind9_fold. econs 19. right. eapply CIH. auto.
      - ss. des_ifs; try reflexivity. right. ss. do 2 econs.
      - ss. des_ifs; try reflexivity. right. ss. do 2 econs.
    }

  Qed.

End PROOF.
