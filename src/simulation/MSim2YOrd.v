From sflib Require Import sflib.
From Paco Require Import paco.
Require Export Coq.Strings.String.
Require Import Coq.Classes.RelationClasses.
From Coq Require Import Program.
From iris.algebra Require Import cmra.

From Fairness Require Export ITreeLib FairBeh Mod.
From Fairness Require Import pind PCM WFLibLarge.
From Fairness Require Import ModSim ModSimYOrd GenYOrd.

Set Implicit Arguments.

Section PROOF.
  Context `{M: ucmra}.

  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable ident_src: ID.
  Variable _ident_tgt: ID.
  Let ident_tgt := @ident_tgt _ident_tgt.

  Variable wf_src: WF.
  Variable wf_tgt: WF.

  Let srcE := threadE ident_src state_src.
  Let tgtE := threadE _ident_tgt state_tgt.

  Let shared := shared state_src state_tgt ident_src _ident_tgt wf_src wf_tgt.
  Let shared_rel: Type := shared -> Prop.
  Variable I: shared -> (cmra_car M) -> Prop.

  Definition lift_wf (wf: WF): WF := sum_WF wf (option_WF wf).

  Definition mk_o {El Er} (wf: WF) R (o: wf.(T)) (pf: bool) (itr: itree (((El +' cE) +' callE) +' Er) R): (lift_wf wf).(T) :=
    if pf
    then match (observe itr) with
         | VisF (((|Yield)|)|)%sum _ => (inr (Some o))
         | _ => (inr None)
         end
    else match (observe itr) with
         | VisF (((|Yield)|)|)%sum _ => (inl o)
         | _ => (inr None)
         end.

  Let A R0 R1 := (bool * bool * (cmra_car M) * (itree srcE R0) * (itree tgtE R1) * shared)%type.
  Let wf_ot R0 R1 := @ord_tree_WF (A R0 R1).
  Let wf_stt R0 R1 := lift_wf (@wf_ot R0 R1).

  Lemma modsim_implies_yord
        tid
        R0 R1 (LRR: R0 -> R1 -> (cmra_car M) -> shared_rel)
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

    { guclo (@lsim_indC_spec M). econs 1; eauto. }

    { destruct GENOS as [GENOS IND]. eapply IH in IND; eauto.
      guclo (@lsim_indC_spec M). econs 2; eauto.
      guclo (@lsim_ord_weakRC_spec M). econs; eauto.
      clear. unfold mk_o. des_ifs; try reflexivity.
      - right. ss. do 2 econs.
      - right. ss. do 2 econs.
    }
    { des. destruct GENOS as [GENOS IND]. eapply IH in IND; eauto.
      guclo (@lsim_indC_spec M). econs 3; eauto. exists x.
      guclo (@lsim_ord_weakRC_spec M). econs; eauto.
      clear. unfold mk_o. des_ifs; try reflexivity.
      - right. ss. do 2 econs.
      - right. ss. do 2 econs.
    }
    { destruct GENOS as [GENOS IND]. eapply IH in IND; eauto.
      guclo (@lsim_indC_spec M). econs 4; eauto.
      guclo (@lsim_ord_weakRC_spec M). econs; eauto.
      clear. unfold mk_o. des_ifs; try reflexivity.
      - right. ss. do 2 econs.
      - right. ss. do 2 econs.
    }
    { destruct GENOS as [GENOS IND]. eapply IH in IND; eauto.
      guclo (@lsim_indC_spec M). econs 5; eauto.
      guclo (@lsim_ord_weakRC_spec M). econs; eauto.
      clear. unfold mk_o. des_ifs; try reflexivity.
      - right. ss. do 2 econs.
      - right. ss. do 2 econs.
    }
    { guclo (@lsim_indC_spec M). econs 6; eauto. }
    { des. destruct GENOS0 as [GENOS IND]. eapply IH in IND; eauto.
      guclo (@lsim_indC_spec M). econs 7; eauto. esplits; eauto.
      guclo (@lsim_ord_weakRC_spec M). econs; eauto.
      clear. unfold mk_o. des_ifs; try reflexivity.
      - right. ss. do 2 econs.
      - right. ss. do 2 econs.
    }

    { destruct GENOS as [GENOS IND]. eapply IH in IND; eauto.
      guclo (@lsim_indC_spec M). econs 8; eauto.
      guclo (@lsim_ord_weakLC_spec M). econs; eauto.
      clear. unfold mk_o. des_ifs; try reflexivity.
      - right. ss. do 2 econs.
      - right. ss. do 2 econs.
    }
    { guclo (@lsim_indC_spec M). econs 9; eauto. i. specialize (GENOS x).
      destruct GENOS as [GENOS IND]. eapply IH in IND; eauto.
      guclo (@lsim_ord_weakLC_spec M). econs; eauto.
      clear. unfold mk_o. des_ifs; try reflexivity.
      - right. ss. do 2 econs.
      - right. ss. do 2 econs.
    }
    { destruct GENOS as [GENOS IND]. eapply IH in IND; eauto.
      guclo (@lsim_indC_spec M). econs 10; eauto.
      guclo (@lsim_ord_weakLC_spec M). econs; eauto.
      clear. unfold mk_o. des_ifs; try reflexivity.
      - right. ss. do 2 econs.
      - right. ss. do 2 econs.
    }
    { destruct GENOS as [GENOS IND]. eapply IH in IND; eauto.
      guclo (@lsim_indC_spec M). econs 11; eauto.
      guclo (@lsim_ord_weakLC_spec M). econs; eauto.
      clear. unfold mk_o. des_ifs; try reflexivity.
      - right. ss. do 2 econs.
      - right. ss. do 2 econs.
    }
    { guclo (@lsim_indC_spec M). econs 12; eauto. i. specialize (GENOS _ FAIR).
      destruct GENOS as [GENOS IND]. eapply IH in IND; eauto.
      guclo (@lsim_ord_weakLC_spec M). econs; eauto.
      clear. unfold mk_o. des_ifs; try reflexivity.
      - right. ss. do 2 econs.
      - right. ss. do 2 econs.
    }

    { guclo (@lsim_indC_spec M). econs 13; eauto. i. specialize (GENOS ret).
      destruct GENOS as [GENOS IND]. eapply IH in IND; eauto.
      guclo (@lsim_ord_weakLC_spec M). econs; eauto.
      guclo (@lsim_ord_weakRC_spec M). econs; eauto.
      - clear. unfold mk_o. ss. des_ifs; try reflexivity.
        + right. ss. do 2 econs.
        + right. ss. do 2 econs.
      - clear. unfold mk_o. ss. des_ifs; try reflexivity.
        + right. ss. do 2 econs.
        + right. ss. do 2 econs.
    }

    { guclo (@lsim_indC_spec M). econs 14. }

    { des. destruct GENOS0 as [GENOS IND]. eapply IH in IND; eauto.
      guclo (@lsim_indC_spec M). econs 15; eauto.
      esplits; eauto.
      clear - LT. unfold mk_o. des_ifs; try reflexivity.
      - ss. do 2 econs. auto.
      - ss. do 1 econs. auto.
    }

    { guclo (@lsim_indC_spec M). econs 16; eauto. i.
      specialize (GENOS _ _ _ _ _ _ _ INV0 VALID0 _ TGT). des.
      destruct GENOS0 as [GENOS IND]. eapply IH in IND; eauto.
      esplits; eauto.
      clear - LT. unfold mk_o. des_ifs; try reflexivity.
      - ss. do 2 econs. auto.
      - ss. do 1 econs. auto.
    }

    { guclo (@lsim_indC_spec M). econs 17; eauto. i.
      specialize (GENOS _ _ _ _ _ _ _ INV0 VALID0 _ TGT). des.
      destruct GENOS0 as [GENOS IND]. eapply IH in IND; eauto.
    }

    { eapply gensim_genos in GENOS. des.
      guclo (@lsim_ord_weakLC_spec M). econs.
      guclo (@lsim_ord_weakRC_spec M). econs.
      instantiate (1:=mk_o (@wf_ot R0 R1) ot0 false src).
      instantiate (1:=mk_o (@wf_ot R0 R1) os0 false tgt).
      gfinal. right. pfold. eapply pind9_fold. econs 18. right. eapply CIH. auto.
      - ss. des_ifs; try reflexivity. right. ss. do 2 econs.
      - ss. des_ifs; try reflexivity. right. ss. do 2 econs.
    }

  Qed.

End PROOF.

Section MODSIM.

  Lemma modsim_implies_yord_mod
        md_src md_tgt
        (MDSIM: ModSim.ModSim.mod_sim md_src md_tgt)
    :
    ModSimYOrd.ModSim.mod_sim md_src md_tgt.
  Proof.
    inv MDSIM.
    set (ident_src := Mod.ident md_src). set (_ident_tgt := Mod.ident md_tgt).
    set (state_src := Mod.state md_src). set (state_tgt := Mod.state md_tgt).
    set (srcE := threadE ident_src state_src).
    set (tgtE := threadE _ident_tgt state_tgt).
    set (ident_tgt := @ident_tgt _ident_tgt).
    set (shared := (TIdSet.t * (@imap ident_src wf_src) * (@imap ident_tgt wf_tgt) * state_src * state_tgt)%type).
    set (wf_stt:=fun R0 R1 => lift_wf (@ord_tree_WF (bool * bool * (cmra_car world) * (itree srcE R0) * (itree tgtE R1) * shared)%type)).
    econs; eauto. instantiate (1:=wf_stt).
    { i. exact (inr None). }
    i. specialize (init im_tgt). des. exists I. esplits; eauto.
    rename init0 into funs. i. specialize (funs fn args). des_ifs.
    unfold ModSim.local_sim in funs.
    ii. specialize (funs _ _ _ _ _ _ _ INV tid _ THS VALID _ UPD).
    des. do 2 eexists. exists (inr None), (inr None). splits. 1,2: eauto.
    i. specialize (funs1 _ _ _ _ _ _ _ INV1 VALID1 _ TGT fs ft).
    eapply modsim_implies_yord in funs1. des.
    ginit. guclo (@lsim_ord_weakRC_spec world). econs. guclo (@lsim_ord_weakLC_spec world). econs.
    gfinal. right. eapply funs1.
    - clear. destruct os.
      { right. econs. }
      destruct t.
      { right. do 2 econs. }
      { left. auto. }
    - clear. destruct ot.
      { right. econs. }
      destruct t.
      { right. do 2 econs. }
      { left. auto. }
  Qed.

End MODSIM.

From Fairness Require Import Concurrency World.
Require Import List.

Section USERSIM.

  Lemma modsim_implies_yord_user
        md_src md_tgt
        p_src p_tgt
        (MDSIM: ModSim.UserSim.sim md_src md_tgt p_src p_tgt)
    :
    ModSimYOrd.UserSim.sim md_src md_tgt p_src p_tgt.
  Proof.
    inv MDSIM.
    set (ident_src := Mod.ident md_src). set (_ident_tgt := Mod.ident md_tgt).
    set (state_src := Mod.state md_src). set (state_tgt := Mod.state md_tgt).
    set (srcE := threadE ident_src state_src).
    set (tgtE := threadE _ident_tgt state_tgt).
    set (ident_tgt := @ident_tgt _ident_tgt).
    set (shared := (TIdSet.t * (@imap ident_src wf_src) * (@imap ident_tgt wf_tgt) * state_src * state_tgt)%type).
    set (wf_stt:=fun R0 R1 => lift_wf (@ord_tree_WF (bool * bool * (cmra_car world) * (itree srcE R0) * (itree tgtE R1) * shared)%type)).
    econs; eauto. instantiate (1:=wf_stt).
    { i. exact (inr None). }
    i. specialize (funs im_tgt).
    des. esplits; eauto.
    instantiate (1:=NatMap.map (fun r => (r, (inr None, inr None))) rs).
    2:{ assert ((@NatMap.fold (world * (T (wf_stt Any.t Any.t) * T (wf_stt Any.t Any.t))) _ (fun (_ : NatMap.key) '(r, _) (s : world) => r ⋅ s) (NatMap.map (fun r : world => (r, (inr None, inr None))) rs) ε) ≡ (NatMap.fold (fun (_ : NatMap.key) (r s : world) => r ⋅ s) rs ε)) as ->; auto.
        rewrite ! NatMap.fold_1. rewrite <- list_map_elements_nm_map.
        remember (NatMap.elements (elt:=world) rs) as l. clear.
        move: ε=> w. revert w.
        induction l; ss. intros w. des_ifs. ss. clarify.
    }
    eapply nm_find_some_implies_forall3.
    { apply nm_forall2_wf_pair. eapply list_forall3_implies_forall2_2; eauto. clear. i. des. des_ifs. des; clarify. }
    { unfold nm_wf_pair, key_set. rewrite nm_map_unit1_map_eq.
      apply nm_forall2_wf_pair. eapply list_forall3_implies_forall2_3; eauto. clear. i. des. des_ifs. des; clarify. }
    i. dup FIND3. rewrite NatMapP.F.map_o in FIND0. unfold option_map in FIND0. des_ifs.
    eapply nm_forall3_implies_find_some in SIM; eauto.
    unfold ModSim.local_sim_init in SIM. unfold local_sim_init. ss.
    i. specialize (SIM _ _ _ _ _ _ _ INV VALID _ FAIR fs ft).
    eapply modsim_implies_yord in SIM. des.
    ginit. guclo (@lsim_ord_weakRC_spec world). econs. guclo (@lsim_ord_weakLC_spec world). econs.
    gfinal. right. eapply SIM.
    - clear. destruct os.
      { right. econs. }
      destruct t.
      { right. do 2 econs. }
      { left. auto. }
    - clear. destruct ot.
      { right. econs. }
      destruct t.
      { right. do 2 econs. }
      { left. auto. }
  Qed.

End USERSIM.
