From sflib Require Import sflib.
From iris.algebra Require Import cmra.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Import pind Axioms ITreeLib Red TRed IRed2 WFLibLarge.
From Fairness Require Import FairBeh Mod Concurrency Linking.
From Fairness Require Import PCM IPM IPropAux.
From Fairness Require Import IndexedInvariants OpticsInterp SimWeakest SimWeakestAdequacy.
From Fairness Require Import TemporalLogic SCMemSpec ucmra_list.
From Fairness Require Import Client05 AuthExclsRA OneShotsRA.
From Fairness Require Export ModSim ModAdequacy ModCloseSim ModAddSim.
From Fairness Require Export FIFOSched SchedSim FIFOSched FIFOSchedSim.

Module Client05Correct.

  Definition config := [("thread1", tt↑); ("thread2", tt↑)].

  Notation src_state := (Mod.state Client05Spec.module).
  Notation src_ident := (Mod.ident Client05Spec.module).
  Notation tgt_state := (Mod.state Client05.module).
  Notation tgt_ident := (Mod.ident Client05.module).

  Local Instance STT : StateTypes := Build_StateTypes src_state tgt_state src_ident tgt_ident.

  Local Instance Γ : SRA.t:=
    GRA.of_list [
        (* Default RAs. *)
        OwnERA;
        OwnDRA;
        ThreadRA;
        (stateSrcRA st_src_type);
        (stateTgtRA st_tgt_type);
        (identSrcRA id_src_type);
        (identTgtRA id_tgt_type);
        ObligationRA.t;
        EdgeRA;
        ArrowShotRA;
        (* Additional RAs. *)
        memRA;
        (OneShots.t unit);
        (AuthExcls.t (nat * nat))
      ].

  (* Default RAs. *)
  Local Instance _OWNERA : GRA.inG OwnERA Γ := (@GRA.InG _ Γ 0 (@eq_refl _ _)).
  Local Instance _OWNDRA : GRA.inG OwnDRA Γ := (@GRA.InG _ Γ 1 (@eq_refl _ _)).
  Local Instance _THDRA : GRA.inG ThreadRA Γ := (@GRA.InG _ Γ 2 (@eq_refl _ _)).
  Local Instance _STATESRC : GRA.inG (stateSrcRA st_src_type) Γ := (@GRA.InG _ Γ 3 (@eq_refl _ _)).
  Local Instance _STATETGT : GRA.inG (stateTgtRA st_tgt_type) Γ := (@GRA.InG _ Γ 4 (@eq_refl _ _)).
  Local Instance _IDENTSRC : GRA.inG (identSrcRA id_src_type) Γ := (@GRA.InG _ Γ 5 (@eq_refl _ _)).
  Local Instance _IDENTTGT : GRA.inG (identTgtRA id_tgt_type) Γ := (@GRA.InG _ Γ 6 (@eq_refl _ _)).
  Local Instance _OBLGRA : GRA.inG ObligationRA.t Γ := (@GRA.InG _ Γ 7 (@eq_refl _ _)).
  Local Instance _EDGERA : GRA.inG EdgeRA Γ := (@GRA.InG _ Γ 8 (@eq_refl _ _)).
  Local Instance _ARROWSHOTRA : GRA.inG ArrowShotRA Γ := (@GRA.InG _ Γ 9 (@eq_refl _ _)).
  Local Instance HasMemRA : GRA.inG memRA Γ := (@GRA.InG _ Γ 10 (@eq_refl _ _)).
  Local Instance HasOneShots : GRA.inG (OneShots.t unit) Γ := (@GRA.InG _ Γ 11 (@eq_refl _ _)).
  Local Instance HasAuthExcls2 : GRA.inG (AuthExcls.t (nat * nat)) Γ := (@GRA.InG _ Γ 12 (@eq_refl _ _)).

  Local Instance TLRASs : TLRAs_small STT Γ :=
    @Build_TLRAs_small STT Γ _ _ _ _ _ _ _ _ _ _.

  Definition Σ : GRA.t:=
    GRA.of_list [
        (* Default RAs. *)
        OwnERA;
        OwnDRA;
        ThreadRA;
        (stateSrcRA st_src_type);
        (stateTgtRA st_tgt_type);
        (identSrcRA id_src_type);
        (identTgtRA id_tgt_type);
        ObligationRA.t;
        EdgeRA;
        ArrowShotRA;
        (* Additional RAs. *)
        memRA;
        (OneShots.t unit);
        (AuthExcls.t (nat * nat));
        (* Maps from empty RAs of Γ. *)
        (optionUR Empty_setR);
        (* Default RAs depending on sProp. *)
        (IInvSetRA sProp);
        (ArrowRA id_tgt_type (Vars:=sProp));
        (ShareDutyRA id_tgt_type (Vars:=sProp))
      ].

  Local Program Instance sub : @SRA.subG Γ Σ :=
    { subG_map := fun i => if (le_lt_dec i 12) then i else 13 }.
  Next Obligation.
    i. ss. unfold Σ, Γ. des_ifs.
  Qed.

  Local Instance _IINVSETRA : GRA.inG (IInvSetRA sProp) Σ := (@GRA.InG _ Σ 14 (@eq_refl _ _)).
  Local Instance _ARROWRA : GRA.inG (ArrowRA id_tgt_type (Vars:=sProp)) Σ := (@GRA.InG _ Σ 15 (@eq_refl _ _)).
  Local Instance _SHAREDUTY : GRA.inG (ShareDutyRA id_tgt_type (Vars:=sProp)) Σ := (@GRA.InG _ Σ 16 (@eq_refl _ _)).

  Local Instance TLRAs : TLRAs STT Γ Σ :=
    @Build_TLRAs STT Γ Σ _ _ _.

  (* Additional initial resources. *)
  Local Definition init_res : Σ :=
    (GRA.embed (memory_init_resource Client05.gvs))
      ⋅ (GRA.embed (AuthExcls.rest_ra (gt_dec 0) (0, 0))).

  Arguments wpsim_bind_top {_ _ _ _ _ _}.
  Arguments wpsim_wand {_ _ _ _ _ _}.
  Arguments wpsim_ret {_ _ _ _ _ _}.

  Ltac red_tl_all := red_tl; red_tl_memra; red_tl_authexcls; red_tl_oneshots.

  Lemma correct:
    UserSim.sim Client05Spec.module Client05.module
                (prog2ths Client05Spec.module config) (prog2ths Client05.module config).
  Proof.
    eapply WSim.whole_sim_implies_usersim. econs.
    { instantiate (1:=init_res). rr. splits.
      { unfold init_res, default_initial_res. disj_tac. }
      { ndtac. }
      { unfold init_res. grawf_tac.
        { apply memory_init_resource_wf. }
        { rewrite /AuthExcls.rest_ra. intros k. des_ifs.
          { apply ucmra_unit_valid. }
          { apply excl_auth.excl_auth_valid. }
        }
      }
    }
    unfold init_res. repeat rewrite <- GRA.embed_add.
    exists 2, 1. exists. lia.
    eexists _. iIntros "(A & INIT)".
    iPoseProof (init_sat with "[A INIT]") as "RES".
    { instantiate (1:=1). instantiate (1:=0). ss. }
    { simpl. iDestruct "A" as "[? ?]". rewrite -!OwnM_uPred_ownM_eq. iFrame. }
    iEval (rewrite red_syn_fairI) in "RES". simpl. iMod "RES".
    iDestruct "RES" as "(% & % & % & #INV1 & TGTST & #SPIN & TID1 & TID2)".
    iEval (rewrite red_syn_tgt_interp_as) in "TGTST". iPoseProof "TGTST" as "#TGTST".

    iModIntro. unfold natmap_prop_sum. ss.
    iSplitL "TID1".
    { iPoseProof (Client05_thread1_spec) as "RES". instantiate (1:=N_Client05).
      pose proof mask_disjoint_N_Client05_state_tgt. set_solver.
      iEval (red_tl) in "RES". iSpecialize ("RES" $! γw).
      iEval (red_tl) in "RES". iSpecialize ("RES" $! κw).
      iEval (red_tl) in "RES". iSpecialize ("RES" $! γL). simpl. red_tl_all.
      iEval (rewrite red_syn_wpsim) in "RES". iApply ("RES" with "[-]").
      rewrite red_syn_inv. rewrite red_syn_tgt_interp_as. simpl.
      iFrame "#". iDestruct "TID1" as "($ & $ & $)".
    }
    iSplitL. 2: done.
    { iPoseProof (Client05_thread2_spec) as "RES". instantiate (1:=N_Client05).
      pose proof mask_disjoint_N_Client05_state_tgt. set_solver.
      iEval (red_tl) in "RES". iSpecialize ("RES" $! γw).
      iEval (red_tl) in "RES". iSpecialize ("RES" $! κw).
      iEval (red_tl) in "RES". iSpecialize ("RES" $! γL). simpl. red_tl_all.
      iEval (rewrite red_syn_wpsim) in "RES". iApply ("RES" with "[-]").
      rewrite red_syn_inv. rewrite red_syn_tgt_interp_as. simpl.
      iFrame "#". iDestruct "TID2" as "($ & $ & $ & $ & $)".
    }
  Qed.

End Client05Correct.

Section ALL.

  Definition client := Client05.module.
  Definition client_spec := Client05Spec.module.

  Lemma client_all_aux
    :
    Adequacy.improves
      (interp_all
         (client_spec.(Mod.st_init))
         (prog2ths client_spec [("thread1", tt↑); ("thread2", tt↑)]) 0)
      (interp_all_fifo
         (client.(Mod.st_init))
         (prog2ths client [("thread1", tt↑); ("thread2", tt↑)]) 0)
  .
  Proof.
    eapply Adequacy.improves_trans.
    { eapply Adequacy.adequacy.
      { instantiate (1:=nat_wf). econs. exact 0. }
      { i. ss. eauto. }
      { eapply ssim_implies_gsim; ss.
        { instantiate (1:=id). ss. }
        { eapply ssim_nondet_fifo; ss. ii. compute in H. des. inv H; des; ss. inv H1; ss. }
      }
    }
    eapply usersim_adequacy. eapply Client05Correct.correct.
    Unshelve. all: constructor.
  Qed.

  Theorem client_all
    :
    Adequacy.improves
      (interp_concurrency
         (prog2ths client_spec [("thread1", tt↑); ("thread2", tt↑)])
         (sched_nondet _)
         (client_spec.(Mod.st_init))
      )
      (interp_concurrency
         (prog2ths client [("thread1", tt↑); ("thread2", tt↑)])
         (sched_fifo_set _)
         (client.(Mod.st_init))
      )
  .
  Proof.
    eapply client_all_aux.
  Qed.

  Theorem client_fair_sched
    :
    Adequacy.improves
      (interp_concurrency
         (prog2ths client_spec [("thread1", tt↑); ("thread2", tt↑)])
         (sched_nondet _)
         (client_spec.(Mod.st_init))
      )
      (interp_concurrency
         (prog2ths client [("thread1", tt↑); ("thread2", tt↑)])
         (sched_nondet _)
         (client.(Mod.st_init))
      )
  .
  Proof.
    eapply usersim_adequacy. eapply Client05Correct.correct.
  Qed.

End ALL.
