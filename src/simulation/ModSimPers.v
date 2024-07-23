From sflib Require Import sflib.
From Paco Require Import paco.
Require Export Coq.Strings.String.
Require Import Coq.Classes.RelationClasses.
From iris.algebra Require Import cmra.

From Fairness Require Export ITreeLib FairBeh Mod.
From Fairness Require Import pind.
From Fairness Require Import PCM.
From Fairness Require Import PindTac.
From Fairness Require Import ModSim.

Set Implicit Arguments.



Section PRIMIVIESIM.
  Context `{M: ucmra}.

  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable ident_src: ID.
  Variable _ident_tgt: ID.

  Variable wf_src: WF.
  Variable wf_tgt: WF.

  Let srcE := threadE ident_src state_src.
  Let tgtE := threadE _ident_tgt state_tgt.

  Variable I: shared state_src state_tgt ident_src _ident_tgt wf_src wf_tgt -> (cmra_car M) -> Prop.

  Definition local_sim_arg {R0 R1} (RR: R0 -> R1 -> Prop) src tgt r_arg :=
    forall ths0 im_src0 im_tgt0 st_src0 st_tgt0 r_shared0 r_ctx0
           (INV: I (ths0, im_src0, im_tgt0, st_src0, st_tgt0) r_shared0)
           tid ths1
           (THS: TIdSet.add_new tid ths0 ths1)
           (VALID: ✓ (r_shared0 ⋅ (r_ctx0 ⋅ r_arg))),
    forall im_tgt1
           (TID_TGT : fair_update im_tgt0 im_tgt1 (prism_fmap inlp (fun i => if tid_dec i tid then Flag.success else Flag.emp))),
    exists r_shared1 r_own,
      (<<INV: I (ths1, im_src0, im_tgt1, st_src0, st_tgt0) r_shared1>>) /\
        (<<VALID: ✓ (r_shared1 ⋅ r_own ⋅ r_ctx0)>>) /\
        (forall ths im_src1 im_tgt2 st_src2 st_tgt2 r_shared2 r_ctx2
                (INV: I (ths, im_src1, im_tgt2, st_src2, st_tgt2) r_shared2)
                (VALID: ✓ (r_shared2 ⋅ r_own ⋅ r_ctx2)),
          forall im_tgt3 (TGT: fair_update im_tgt2 im_tgt3 (prism_fmap inlp (tids_fmap tid ths))),
            (<<LSIM: forall fs ft,
                @lsim
                  _
                  state_src state_tgt ident_src _ident_tgt wf_src wf_tgt
                  I
                  tid
                  R0 R1
                  (@local_RR _ state_src state_tgt ident_src _ident_tgt wf_src wf_tgt  I R0 R1 RR tid)
                  fs ft
                  r_ctx2
                  src tgt
                  (ths, im_src1, im_tgt3, st_src2, st_tgt2)
                  >>)).

End PRIMIVIESIM.


Module ModSimPers.
  Section MODSIM.

    Variable md_src: Mod.t.
    Variable md_tgt: Mod.t.

    Record mod_sim: Prop :=
      mk {
          wf_src : WF;
          wf_tgt : WF;
          wf_tgt_inhabited: inhabited wf_tgt.(T);
          wf_tgt_open: forall (o0: wf_tgt.(T)), exists o1, wf_tgt.(lt) o0 o1;

          world: ucmra;

          (* I: (@shared md_src.(Mod.state) md_tgt.(Mod.state) md_src.(Mod.ident) md_tgt.(Mod.ident) wf_src wf_tgt) -> world -> Prop; *)
          init: forall im_tgt,
          exists (I: (@shared md_src.(Mod.state) md_tgt.(Mod.state) md_src.(Mod.ident) md_tgt.(Mod.ident) wf_src wf_tgt) -> world -> Prop),
          (exists im_src r_shared,
            (I (NatSet.empty, im_src, im_tgt, md_src.(Mod.st_init), md_tgt.(Mod.st_init)) r_shared) /\
              (✓ r_shared)
            /\
              (forall fn args, match md_src.(Mod.funs) fn, md_tgt.(Mod.funs) fn with
                               | Some ktr_src, Some ktr_tgt => local_sim_arg I (@eq Any.t) (ktr_src args) (ktr_tgt args) (core r_shared)
                               | None, None => True
                               | _, _ => False
                               end));
        }.

    Ltac pind_gen := patterning 9; refine (@lsim_acc_gen
                                             _ _ _ _ _ _ _ _
                                             _ _ _
                                             _ _ _ _ _ _ _ _ _
                                             _ _ _).
    Ltac pinduction n := currying n pind_gen.

    Lemma imply_mod_sim (SIM: mod_sim):
      ModSim.mod_sim md_src md_tgt.
    Proof.
      inv SIM.
      eapply (@ModSim.mk _ _ wf_src wf_tgt wf_tgt_inhabited wf_tgt_open world).
      i. specialize (init im_tgt). des.
      assert (DUP: core r_shared ≡ core r_shared ⋅ core r_shared).
      { rewrite <- cmra_core_idemp at 3. rewrite cmra_core_r. auto. }
      eexists (fun sh r => exists r0, I sh r0 /\ core r_shared ⋅ r0 = r).
      split.
      { esplits; eauto. rewrite cmra_core_l. auto. }
      i. specialize (init1 fn args). des_ifs.
      ii. des. subst. exploit init1; eauto.
      { instantiate (1:=r_ctx0 ⋅ core r_shared).
        rewrite -(assoc cmra.op). rewrite <- DUP.
        rewrite (comm cmra.op r_ctx0) (assoc cmra.op) (comm cmra.op r0).
        done.
      }
      i. des. esplits; eauto.
      { instantiate (1:=r_own).
        r_wf VALID0.
        do 2 rewrite -(assoc cmra.op r_shared1).
        rewrite (comm cmra.op _ (core r_shared)).
        rewrite !(assoc cmra.op) (comm cmra.op r_shared1).
        done.
      }
      i. des. subst. hexploit x0; eauto.
      { instantiate (1:=r_ctx2 ⋅ core r_shared). r_wf VALID1.
        rewrite -(assoc cmra.op (core r_shared)) (comm cmra.op (core r_shared)).
        rewrite -(assoc cmra.op r1).
        do 2 rewrite -(assoc cmra.op _ _ r_ctx2).
        rewrite -(assoc cmra.op r_own) (comm cmra.op (core r_shared)).
        by rewrite !(assoc cmra.op).
      }
      ii. specialize (H fs ft).

      ginit. revert H. generalize (k args), (k0 args).
      generalize (ths, im_src1, im_tgt3, st_src2, st_tgt2). clear.
      revert fs ft r_ctx2. gcofix CIH.
      i. punfold H0. revert p i i0 fs ft r_ctx2 H0. pinduction 6.
      i. eapply pind9_unfold in PR.
      2:{ eauto with paco. }
      inv PR.

      { guclo (@lsim_indC_spec world). econs 1; eauto.
        rr in LSIM. des. rr. esplits; eauto. instantiate (1:=r_own). r_wf VALID.
        rewrite (comm cmra.op _ (core r_shared)).
        rewrite !(assoc cmra.op).
        done.
      }

      { guclo (@lsim_indC_spec world). econs 2; eauto.
        rr in LSIM. des. eapply IH. auto.
      }

      { guclo (@lsim_indC_spec world). econs 3; eauto.
        rr in LSIM. des. rr in LSIM. des. esplits. eapply IH. eauto.
      }

      { guclo (@lsim_indC_spec world). econs 4; eauto.
        rr in LSIM. des. eapply IH. eauto.
      }

      { guclo (@lsim_indC_spec world). econs 5; eauto.
        rr in LSIM. des. eapply IH. eauto.
      }

      { guclo (@lsim_indC_spec world). econs 6; eauto. }

      { guclo (@lsim_indC_spec world). econs 7; eauto.
        rr in LSIM. des. rr in LSIM0. des. esplits; eauto.
      }

      { guclo (@lsim_indC_spec world). econs 8; eauto.
        rr in LSIM. des. eapply IH. eauto.
      }

      { guclo (@lsim_indC_spec world). econs 9; eauto. i.
        hexploit LSIM; eauto. intros SIM. rr in SIM. des. esplits; eauto.
      }

      { guclo (@lsim_indC_spec world). econs 10; eauto.
        rr in LSIM. des. eapply IH. eauto.
      }

      { guclo (@lsim_indC_spec world). econs 11; eauto.
        rr in LSIM. des. eapply IH. eauto.
      }

      { guclo (@lsim_indC_spec world). econs 12; eauto. i.
        hexploit LSIM; eauto. intros SIM. rr in SIM. des. esplits; eauto.
      }

      { gstep. eapply pind9_fold. econs 13; eauto. i.
        hexploit LSIM; eauto. intros SIM. rr in SIM. des; ss.
        gbase. eapply CIH; eauto.
      }

      { gstep. eapply pind9_fold. econs 14; eauto. i.
        hexploit LSIM; eauto. intros SIM. rr in SIM. des; ss.
        gbase. eapply CIH; eauto.
      }

      { guclo (@lsim_indC_spec world). econs 15; eauto.
        rr in LSIM. des. eapply IH. eauto.
      }

      { guclo (@lsim_indC_spec world). econs 16; eauto.
        { instantiate (1:=r_own). r_wf VALID.
          rewrite (comm cmra.op (r_shared0 ⋅ r_own)).
          rewrite (comm cmra.op _ (core r_shared)).
          rewrite (comm cmra.op x5).
          by rewrite !(assoc cmra.op).
        }
        { i. des. subst. hexploit LSIM; eauto.
          { instantiate (1:= r_ctx1 ⋅ core r_shared).
            clear -VALID0.
            rewrite (comm cmra.op r_ctx1).
            rewrite (assoc cmra.op) (comm cmra.op _ (core r_shared)).
            rewrite !(assoc cmra.op).
            done.
          }
          { i. rr in H. des.
            clear -IH H0.
            eapply IH; eauto.
          }
        }
      }

      { gstep. eapply pind9_fold. econs 17; eauto.
        { instantiate (1:=r_own). r_wf VALID.
          rewrite (comm cmra.op _ (core _)).
          rewrite !(assoc cmra.op).
          done.
        }
        { i. des. subst. hexploit LSIM; eauto.
          { instantiate (1:=r_ctx1 ⋅ core r_shared). r_wf VALID0.
            rewrite (comm cmra.op _ (core r_shared)).
            rewrite !(assoc cmra.op).
            done.
          }
          { i. rr in H. des; ss. gbase. eapply CIH; eauto. }
        }
      }

      { gstep. eapply pind9_fold. econs 18; eauto. i.
        rr in LSIM. des; ss. gbase. eapply CIH; eauto.
      }
    Qed.
  End MODSIM.
End ModSimPers.
