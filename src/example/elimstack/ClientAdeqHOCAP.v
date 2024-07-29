From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Import pind Axioms ITreeLib Red TRed IRed2 WFLibLarge.
From Fairness Require Import FairBeh Mod Concurrency Linking.
From Fairness Require Import PCM IPM IPropAux.
From Fairness Require Import IndexedInvariants OpticsInterp SimWeakest SimWeakestAdequacy.
From Fairness Require Import TemporalLogic SCMemSpec LifetimeRA ghost_excl ghost_map ghost_var ucmra_list.
From Fairness.elimstack Require Import SpecHOCAP ClientCode ClientSpecHOCAP.
From Fairness Require Export ModSim ModAdequacy ModCloseSim ModAddSim.
From Fairness Require Export FIFOSched SchedSim FIFOSched FIFOSchedSim.

Module ElimStackClientCorrect.

  Definition config := [("thread_push", tt↑); ("thread_pop", tt↑)].

  Notation src_state := (Mod.state ElimStackClientSpec.module).
  Notation src_ident := (Mod.ident ElimStackClientSpec.module).
  Notation tgt_state := (Mod.state ElimStackClient.module).
  Notation tgt_ident := (Mod.ident ElimStackClient.module).

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
        Lifetime.t;
        (ghost_mapURA nat maybe_null_ptr);
        (ghost_varURA (list SCMem.val));
        (ghost_exclURA unit)
      ].

  (* Default RAs. *)
  Local Instance _OWNERA : GRA.inG OwnERA Γ := GRA.InG Γ 0 eq_refl.
  Local Instance _OWNDRA : GRA.inG OwnDRA Γ := GRA.InG Γ 1 eq_refl.
  Local Instance _THDRA : GRA.inG ThreadRA Γ := GRA.InG Γ 2 eq_refl.
  Local Instance _STATESRC : GRA.inG (stateSrcRA st_src_type) Γ := GRA.InG Γ 3 eq_refl.
  Local Instance _STATETGT : GRA.inG (stateTgtRA st_tgt_type) Γ := GRA.InG Γ 4 eq_refl.
  Local Instance _IDENTSRC : GRA.inG (identSrcRA id_src_type) Γ := GRA.InG Γ 5 eq_refl.
  Local Instance _IDENTTGT : GRA.inG (identTgtRA id_tgt_type) Γ := GRA.InG Γ 6 eq_refl.
  Local Instance _OBLGRA : GRA.inG ObligationRA.t Γ := GRA.InG Γ 7 eq_refl.
  Local Instance _EDGERA : GRA.inG EdgeRA Γ := GRA.InG Γ 8 eq_refl.
  Local Instance _ARROWSHOTRA : GRA.inG ArrowShotRA Γ := GRA.InG Γ 9 eq_refl.
  Local Instance HasMemRA : GRA.inG memRA Γ := GRA.InG Γ 10 eq_refl.
  Local Instance HasLifetime : GRA.inG Lifetime.t Γ := GRA.InG Γ 11 eq_refl.
  Local Instance HasGhostMap : GRA.inG (ghost_mapURA nat maybe_null_ptr) Γ := GRA.InG Γ 12 eq_refl.
  Local Instance HasGhostVar : GRA.inG (ghost_varURA (list SCMem.val)) Γ := GRA.InG Γ 13 eq_refl.
  Local Instance HasGhostExcl : GRA.inG (ghost_exclURA unit) Γ := GRA.InG Γ 14 eq_refl.

  Local Instance TLRASs : TLRAs_small STT Γ := Build_TLRAs_small STT Γ _ _ _ _ _ _ _ _ _ _.

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
        Lifetime.t;
        (ghost_mapURA nat maybe_null_ptr);
        (ghost_varURA (list SCMem.val));
        (ghost_exclURA unit);
        (* Maps from empty RAs of Γ. *)
        (optionUR Empty_setR);
        (* Default RAs depending on sProp. *)
        (IInvSetRA sProp);
        (ArrowRA id_tgt_type (Vars:=sProp));
        (ShareDutyRA id_tgt_type (Vars:=sProp))
      ].

  Local Program Instance sub : SRA.subG Γ Σ :=
    { subG_map := fun i => if (le_lt_dec i 14) then i else 15 }.
  Next Obligation.
    i. ss. unfold Σ, Γ. des_ifs.
  Qed.

  Local Instance _IINVSETRA : GRA.inG (IInvSetRA sProp) Σ := GRA.InG Σ 16 eq_refl.
  Local Instance _ARROWRA : GRA.inG (ArrowRA id_tgt_type) Σ := GRA.InG Σ 17 eq_refl.
  Local Instance _SHAREDUTY : GRA.inG (ShareDutyRA id_tgt_type) Σ := GRA.InG Σ 18 eq_refl.

  Local Instance TLRAs : TLRAs STT Γ Σ := Build_TLRAs STT Γ Σ _ _ _.

  (* Additional initial resources. *)
  Local Definition init_res : Σ :=
    (GRA.embed (memory_init_resource ElimStackClient.gvs)).

  Arguments wpsim_bind_top {_ _ _ _ _ _}.
  Arguments wpsim_wand {_ _ _ _ _ _}.
  Arguments wpsim_ret {_ _ _ _ _ _}.

  Ltac red_tl_all := red_tl; red_tl_lifetime; red_tl_ghost_excl.

  Lemma correct:
    UserSim.sim ElimStackClientSpec.module ElimStackClient.module
                (prog2ths ElimStackClientSpec.module config) (prog2ths ElimStackClient.module config).
  Proof.
    eapply WSim.whole_sim_implies_usersim. econs.
    { instantiate (1:=init_res). rr. splits.
      { unfold init_res, default_initial_res. disj_tac. }
      { ndtac. }
      { unfold init_res. grawf_tac.
        apply memory_init_resource_wf.
      }
    }
    unfold init_res. repeat rewrite <- GRA.embed_add.
    exists 4, 1. exists. lia.
    eexists _. iIntros "(A & INIT)".
    iDestruct (init_sat 0 1 with "[$A $INIT]") as "RES"; [ss|].

    iEval (rewrite red_syn_fairI) in "RES". simpl. iMod "RES".
    iDestruct "RES" as (?????) "(TGTST & #IsES & #CInv & Tpush & Dpush & Pc_kt_push & Pc_k_push & live_k & #Act_k & Tok & Pc_kt_pop & Tpop & Dpop)".
    iEval (rewrite red_syn_tgt_interp_as) in "TGTST".
    iDestruct "TGTST" as "#TGTST".
    red_tl. simpl.

    iModIntro. unfold natmap_prop_sum. ss.
    iSplitR "Tpop Dpop Pc_kt_pop Tok".
    { iDestruct (ElimStackClient_push_sim _ _ γk k kt γs γpop) as "RES".
      red_tl_all. simpl.
      iEval (rewrite red_syn_wpsim) in "RES".
      iApply ("RES" with "[-]"). iClear "RES".
      red_tl_all.
      rewrite red_syn_tgt_interp_as. simpl. iFrame "∗#".
    }
    iSplit; [|done].
    { iDestruct (ElimStackClient_pop_sim _ _ γk k kt γs γpop) as "RES".
      red_tl_all. simpl.
      iEval (rewrite red_syn_wpsim) in "RES".
      iApply ("RES" with "[-]"). iClear "RES".
      rewrite red_syn_tgt_interp_as. red_tl_all. iFrame "∗#".
    }
  Qed.

End ElimStackClientCorrect.

Section ALL.

  Definition client := ElimStackClient.module.
  Definition client_spec := ElimStackClientSpec.module.

  Lemma client_all_aux
    :
    Adequacy.improves
      (interp_all
         (client_spec.(Mod.st_init))
         (prog2ths client_spec [("thread_push", tt↑); ("thread_pop", tt↑)]) 0)
      (interp_all_fifo
         (client.(Mod.st_init))
         (prog2ths client [("thread_push", tt↑); ("thread_pop", tt↑)]) 0)
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
    eapply usersim_adequacy. eapply ElimStackClientCorrect.correct.
    Unshelve. all: constructor.
  Qed.

  Theorem client_all
    :
    Adequacy.improves
      (interp_concurrency
         (prog2ths client_spec [("thread_push", tt↑); ("thread_pop", tt↑)])
         (sched_nondet _)
         (client_spec.(Mod.st_init))
      )
      (interp_concurrency
         (prog2ths client [("thread_push", tt↑); ("thread_pop", tt↑)])
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
         (prog2ths client_spec [("thread_push", tt↑); ("thread_pop", tt↑)])
         (sched_nondet _)
         (client_spec.(Mod.st_init))
      )
      (interp_concurrency
         (prog2ths client [("thread_push", tt↑); ("thread_pop", tt↑)])
         (sched_nondet _)
         (client.(Mod.st_init))
      )
  .
  Proof.
    eapply usersim_adequacy. eapply ElimStackClientCorrect.correct.
  Qed.

End ALL.
