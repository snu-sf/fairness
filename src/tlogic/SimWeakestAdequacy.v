From iris.algebra Require Import cmra.
From sflib Require Import sflib.
From Paco Require Import paco.
From Fairness Require Import ITreeLib ModSim ModSimPers Concurrency ModAdequacy Axioms.
From Fairness.base_logic Require Import upred base_logic.
From Fairness Require Import PCM IPM ISim SimDefaultRA SimWeakest.
From Fairness Require Import FairBeh.
Require Import Coq.Logic.PropExtensionality.
From Fairness Require PCM.
Require Import Program.

Set Implicit Arguments.



Lemma list_of_numbering_nm_wf_pair A B (l0: list A) (l1: list B)
      (LEN: List.length l0 = List.length l1):
  nm_wf_pair (NatMapP.of_list (numbering l0)) (NatMapP.of_list (numbering l1)).
Proof.
  unfold numbering. generalize 0.
  revert l1 LEN. induction l0; ss; i.
  { destruct l1; ss. apply nm_wf_pair_empty_empty_eq. }
  { destruct l1; ss. inv LEN. ss.
    unfold NatMapP.uncurry. ss. eapply nm_wf_pair_add. eauto. }
Qed.

Lemma prog2ths_nm_wf_pair md0 md1 c:
  nm_wf_pair (prog2ths md0 c) (prog2ths md1 c).
Proof.
  eapply list_of_numbering_nm_wf_pair.
  repeat rewrite map_length. auto.
Qed.

Lemma key_set_idempotent (m: NatMap.t unit)
  :
  key_set m = m.
Proof.
  pattern m. revert m. eapply nm_ind.
  { apply key_set_empty_empty_eq. }
  i. destruct v. rewrite key_set_pull_add_eq.
  f_equal. auto.
Qed.


Section DISJOINTWF.
  Context `{Σ: GRA.t}.

  Definition disjoint_GRA (r0 r1: Σ): Prop :=
    forall n, r0 n ≡ ε \/ r1 n ≡ ε.

  Definition disjoint_GRA_sym r0 r1
             (DISJ: disjoint_GRA r0 r1)
    :
    disjoint_GRA r1 r0.
  Proof.
    ii. exploit DISJ; auto. i. des; eauto.
  Qed.

  Definition disjoint_GRA_unit_r r
    :
    disjoint_GRA r ε.
  Proof.
    ii. auto.
  Qed.

  Definition disjoint_GRA_unit_l r
    :
    disjoint_GRA ε r.
  Proof.
    ii. auto.
  Qed.

  Lemma disjoint_GRA_dist_r r0 r1 r2
        (DISJ0: disjoint_GRA r0 r1)
        (DISJ1: disjoint_GRA r0 r2)
    :
    disjoint_GRA r0 (r1 ⋅ r2).
  Proof.
    Local Transparent GRA.to_URA.
    ii. hexploit (DISJ0 n); auto. i.
    hexploit (DISJ1 n); auto. i. des; auto.
    right. rewrite discrete_fun_lookup_op.
    rewrite H. rewrite H0. by rewrite right_id.
  Qed.

  Lemma disjoint_GRA_dist_l r0 r1 r2
        (DISJ0: disjoint_GRA r0 r1)
        (DISJ1: disjoint_GRA r0 r2)
    :
    disjoint_GRA (r1 ⋅ r2) r0.
  Proof.
    eapply disjoint_GRA_sym. eapply disjoint_GRA_dist_r; auto.
  Qed.

  Lemma disjoint_GRA_embed M0 M1
        `{ING0: @GRA.inG M0 Σ}
        `{ING1: @GRA.inG M1 Σ}
        (r0: M0) (r1: M1)
        (DIFF: ING0.(GRA.inG_id) <> ING1.(GRA.inG_id))
    :
    disjoint_GRA (GRA.embed r0) (GRA.embed r1).
  Proof.
    Local Transparent GRA.to_URA.
    ii. revert r0 r1. dependent destruction ING0.
    dependent destruction ING1.
    ss. unfold GRA.embed. des_ifs; ss; auto.
    i. dependent destruction e. ss.
  Qed.

  Lemma res_wf_disjoint (r0 r1: Σ)
        (WF0: ✓ r0)
        (WF1: ✓ r1)
        (DISJ: disjoint_GRA r0 r1)
    :
    ✓ (r0 ⋅ r1).
  Proof.
    Local Transparent GRA.to_URA.
    intros k. rewrite discrete_fun_lookup_op.
    specialize (WF0 k). specialize (WF1 k).
    exploit DISJ. i. des.
    { rewrite x0. rewrite left_id. auto. }
    { rewrite x0. rewrite right_id. auto. }
  Qed.
End DISJOINTWF.

From Fairness Require Import DisableSsreflect.

Ltac disj_tac :=
  try
    match goal with
    | |- disjoint_GRA (cmra.op _ _) _ =>
        eapply disjoint_GRA_dist_l;[disj_tac|disj_tac]
    | |- disjoint_GRA _ (cmra.op _ _) =>
        eapply disjoint_GRA_dist_r;[disj_tac|disj_tac]
    | |- disjoint_GRA (@GRA.embed _ _ _ _) (@GRA.embed _ _ _ _) =>
        eapply disjoint_GRA_embed; (try by ss)
    end.

Ltac grawf_tac :=
  try
    match goal with
    | |- valid (cmra.op _ _) =>
        eapply res_wf_disjoint;
        [grawf_tac|grawf_tac|disj_tac]
    | |- valid (@GRA.embed _ _ _ _) =>
        eapply GRA.wf_embed
    end.

Ltac ndtac :=
  try match goal with
      | |- NoDup _ => econs; ii; ss; des; ss; ndtac
      end.

Ltac seal_with key x :=
  replace x with (Seal.sealing key x); [|eapply Seal.sealing_eq].
Ltac seal x :=
  let key := fresh "key" in
  assert (key:= "_deafult_");
  seal_with key x.
Ltac unseal x :=
  match (type of x) with
  | string => repeat rewrite (@Seal.sealing_eq x) in *; try clear x
  | _ => repeat rewrite (@Seal.sealing_eq _ _ x) in *;
         repeat match goal with
                | [ H: string |- _ ] => try clear H
                end
  end
.


Module WSim.
  Section WSIM.
    Variable md_src: Mod.t.
    Variable md_tgt: Mod.t.

    Let NUNBOUND: forall n, exists m, n < m.
    Proof. i. exists (S n). econs. Qed.

    Let THSEQ: forall c,
        (NatMapP.of_list (numbering (List.map (fun _ => tt) c))) = (key_set (prog2ths md_src c)).
    Proof.
      i. etrans.
      { symmetry. apply key_set_idempotent. }
      eapply list_of_numbering_nm_wf_pair.
      repeat rewrite map_length. auto.
    Qed.

    Local Notation index := nat.
    Context `{Vars : index -> Type}.
    Context `{Σ: GRA.t}.
    Notation iProp := (iProp Σ).

    Lemma iProp_satisfable (r0: Σ) (P: iProp) (WF: ✓ r0)
          (IMPL: Own r0 ⊢ #=> P)
      :
      exists r1, Fairness.base_logic.upred.uPred_holds (to_upred P) r1 /\ ✓ r1.
    Proof.
      revert IMPL. rewrite Own_eq. unfold IPM.Own_def. uPred.unseal. intros [IMPL].
      rr in IMPL. hexploit (IMPL r0); auto.
      { rr. exists ε. rewrite right_id; [done|apply _]. }
      { instantiate (1:=ε). rewrite right_id; [done|apply _]. }
      i. des. rewrite right_id in H; [|apply _]. eauto.
    Qed.


    Context `{Invs : @IInvSet Σ Vars}.

    (* Invariant related default RAs *)
    Context `{OWNERA : @GRA.inG OwnERA Σ}.
    Context `{OWNDRA : @GRA.inG OwnDRA Σ}.
    Context `{IINVSETRA : @GRA.inG (IInvSetRA Vars) Σ}.
    (* State related default RAs *)
    Context `{THDRA: @GRA.inG ThreadRA Σ}.
    Context `{STATESRC: @GRA.inG (stateSrcRA md_src.(Mod.state)) Σ}.
    Context `{STATETGT: @GRA.inG (stateTgtRA md_tgt.(Mod.state)) Σ}.
    Context `{IDENTSRC: @GRA.inG (identSrcRA md_src.(Mod.ident)) Σ}.
    Context `{IDENTTGT: @GRA.inG (identTgtRA md_tgt.(Mod.ident)) Σ}.
    (* Liveness logic related default RAs *)
    Context `{OBLGRA: @GRA.inG ObligationRA.t Σ}.
    Context `{EDGERA: @GRA.inG EdgeRA Σ}.
    Context `{ONESHOTRA: @GRA.inG ArrowShotRA Σ}.
    Context `{ARROWRA: @GRA.inG (@ArrowRA md_tgt.(Mod.ident) Vars) Σ}.


    Definition initial_res_wf (init_res: Σ): Prop :=
      (<<INITDISJ: (disjoint_GRA init_res (@default_initial_res _ md_src.(Mod.state) md_tgt.(Mod.state) md_src.(Mod.ident) md_tgt.(Mod.ident) _ _ _ _ _ _ _ _ _ _))>>) /\
        (<<DEFAULTDISJ:
          (NoDup [THDRA.(GRA.inG_id);
                  STATESRC.(GRA.inG_id);
                  STATETGT.(GRA.inG_id);
                  IDENTSRC.(GRA.inG_id);
                  IDENTTGT.(GRA.inG_id);
                  OBLGRA.(GRA.inG_id);
                  ARROWRA.(GRA.inG_id);
                  EDGERA.(GRA.inG_id);
                  OWNERA.(GRA.inG_id);
                  OWNDRA.(GRA.inG_id);
                  IINVSETRA.(GRA.inG_id)])>>) /\
        (<<INITRES: ✓ init_res>>).

    Lemma reswf_gen
          init_res
          (WF: initial_res_wf init_res)
      : ✓ (init_res ⋅ (@default_initial_res _ md_src.(Mod.state) md_tgt.(Mod.state) md_src.(Mod.ident) md_tgt.(Mod.ident) _ _ _ _ _ _ _ _ _ _)).
    Proof.
      r in WF. des. inv DEFAULTDISJ. ss.
      inv H2. ss. inv H4. inv H5. ss. inv H6. ss. inv H7. ss. inv H8; ss. inv H9; ss. inv H10. inv H11. inv H12. ss.
      grawf_tac; auto.
      unfold default_initial_res.
      grawf_tac; (try match goal with | |- _ <> _ => auto 15 end).
      all: try done.
      { intros k. apply auth.auth_auth_valid. done. }
      { apply auth.auth_auth_valid. done. }
      { apply excl_auth.excl_auth_valid. }
      { apply excl_auth.excl_auth_valid. }
      { intros k. apply OneShot.pending_one_wf. }
      { unfold Regions.nauth_ra. ss. intros ??. apply OneShot.pending_one_wf. }
    Qed.

    Definition initial_prop n (ths: TIdSet.t) o: iProp :=
      ((FairRA.whites Prism.id (fun _ => True: Prop) o)
         ∗
         (FairRA.blacks Prism.id (fun i => match i with | inr _ => True | _ => False end: Prop))
         ∗
         (natmap_prop_sum ths (fun tid _ => ObligationRA.duty n inlp tid []))
         ∗
         (natmap_prop_sum ths (fun tid _ => own_thread tid))
         ∗
         (St_src md_src.(Mod.st_init))
         ∗
         (St_tgt md_tgt.(Mod.st_init)))%I
    .

    Lemma wpsim_lsim x tid (r r_shared r_ctx: Σ)
          ths im_src im_tgt0 im_tgt1 (st_src: md_src.(Mod.state)) (st_tgt: md_tgt.(Mod.state)) (fs ft: bool)
          (th0: thread (Mod.ident md_src) (sE (Mod.state md_src)) Any.t)
          (th1: thread (Mod.ident md_tgt) (sE (Mod.state md_tgt)) Any.t)
          y
          (DUTYLEVEL: y < x)
          (SIM: Fairness.base_logic.upred.uPred_holds (to_upred (wpsim x tid ⊤ ibot7 ibot7
                      (fun r_src r_tgt =>
                         ((own_thread tid ∗ ObligationRA.duty y inlp tid []) ∗ ⌜r_src = r_tgt⌝)%I) false false th0 th1)) r)
          (INV: Fairness.base_logic.upred.uPred_holds ((to_upred (default_I x ths im_src im_tgt0 st_src st_tgt
                           ∗ (wsat_auth x ∗ wsats x ∗ OwnE ⊤))%I)) r_shared)
          (FUPD: fair_update im_tgt0 im_tgt1 (prism_fmap inlp (tids_fmap tid ths)))
          (WF: ✓ ((r_shared ⋅ r) ⋅ r_ctx))
      :
      (@lsim
         ( (GRA.to_URA Σ)) (Mod.state md_src) (Mod.state md_tgt)
         (Mod.ident md_src) (Mod.ident md_tgt) owf nat_wf
         (liftI
            (fun (ths : TIdSet.t)
               (im_src : imap (Mod.ident md_src) owf)
               (im_tgt : imap (sum_tid (Mod.ident md_tgt)) nat_wf)
               (st_src : Mod.state md_src) (st_tgt : Mod.state md_tgt) =>
               (default_I x ths im_src im_tgt st_src st_tgt
                          ∗ (wsat_auth x ∗ wsats x ∗ OwnE ⊤))%I))
         tid
         Any.t Any.t
         (@local_RR
            ( (GRA.to_URA Σ)) (Mod.state md_src) (Mod.state md_tgt)
            (Mod.ident md_src) (Mod.ident md_tgt) owf nat_wf
            (liftI
               (fun (ths : TIdSet.t)
                  (im_src : imap (Mod.ident md_src) owf)
                  (im_tgt : imap (sum_tid (Mod.ident md_tgt)) nat_wf)
                  (st_src : Mod.state md_src) (st_tgt : Mod.state md_tgt) =>
                  (default_I x ths im_src im_tgt st_src st_tgt
                             ∗ (wsat_auth x ∗ wsats x ∗ OwnE ⊤))%I))
            Any.t Any.t
            eq tid)) fs ft r_ctx th0 th1
                     (ths, im_src, im_tgt1, st_src, st_tgt).
    Proof.
      Local Opaque GRA.to_URA.
      unfold wpsim in SIM. revert SIM. uPred.unseal. intros SIM.
      specialize (SIM ths im_src im_tgt1 st_src st_tgt).
      simpl in *.
      revert INV. uPred.unseal. intros INV.
      rr in SIM. hexploit (SIM r_shared).
      { rewrite (comm cmra.op). eapply cmra_valid_op_l. done. }
      { rr in INV. rr. des. setoid_rewrite INV. esplits.
        { eauto. }
        { unfold default_I_past. uPred.unseal. rr. esplits. rr. esplits.
          { instantiate (2:=ε). rewrite left_id; [|apply _]. done. }
          { rr. eauto. }
          { auto. }
        }
        { auto. }
      }
      { instantiate (1:=r_ctx). r_wf WF. }
      i. eapply lsim_flag_any. eapply lsim_monoR.
      { ginit. ss. refine (@eq_rect _ _ id H _ _).
        f_equal; cycle 1.
        { i. subst. f_equal. repeat (let x := fresh "x" in extensionality x).
          eapply propositional_extensionality. split; i; ss.
          dependent destruction H0. rr in REL. des.
          rr in REL. des. subst.
          rr in REL. des. subst.
          revert REL0. unfold ibot7. uPred.unseal.
          intros REL0. rr in REL0. ss.
        }
        { repeat (let x := fresh "x" in extensionality x).
          eapply propositional_extensionality. split; i; ss.
          dependent destruction H0. rr in REL. des.
          rr in REL. des. subst.
          rr in REL. des. subst.
          revert REL0. unfold ibot7. uPred.unseal.
          intros REL0. rr in REL0. ss.
        }
        { reflexivity. }
        { i. auto. clarify. rewrite H12. rewrite H10. rewrite H9. auto. }
      }
      { i. ss. des_ifs. des.
        rr in RET0. des. subst.
        rr in RET2. des. subst.
        rr in RET3. subst.
        rr in RET1. des. subst.
        hexploit (@default_I_past_final md_src.(Mod.state) md_tgt.(Mod.state) md_src.(Mod.ident) md_tgt.(Mod.ident)).
        apply DUTYLEVEL.
        uPred.unseal.
        intro HEMP. rr in HEMP. destruct HEMP as [HEMP]. hexploit HEMP.
        { instantiate (1:=ε). apply ucmra_unit_valid. }
        { clear. uPred.unseal. rr. ss. }
        clear HEMP.
        i. rr in H0. hexploit H0.
        { rewrite left_id; [|apply _].
          rewrite RET0 in WF0.
          rewrite RET1 in WF0.
          repeat apply cmra_valid_op_l in WF0.
          apply WF0.
        }
        { eauto. }
        { rewrite RET0 in WF0.
          rewrite RET1 in WF0.
          rewrite RET2 in WF0.
          rewrite RET3 in WF0.
          instantiate (1:=x4 ⋅ x5).
          eapply (cmra_valid_op_l _ x3),(cmra_valid_op_l _ r_ctx0),(cmra_valid_op_l _ x7).
          r_wf WF0.
        }
        { rr. eauto. }
        { instantiate (1:=x7⋅r_ctx0).
          rewrite RET0 in WF0.
          rewrite RET1 in WF0.
          rewrite RET2 in WF0.
          rewrite RET3 in WF0.
          clear -WF0.
          eapply (cmra_valid_op_l _ x3).
          r_wf WF0.
        }
        i. des.
        rr in H2. des.
        rr in H2. des. rewrite H2 in H1.
        rr in H3.
        rr. esplits.
        { eauto. }
        2:{ rr. exists x9,x7. esplits; eauto. }
        2:{ rr in RET4. auto. }
        { instantiate (1:=x8).
          r_wf H1.
        }
      }
    Qed.

    Lemma wpsim_local_sim_init x tid (r: Σ)
          (th0: thread (Mod.ident md_src) (sE (Mod.state md_src)) Any.t)
          (th1: thread (Mod.ident md_tgt) (sE (Mod.state md_tgt)) Any.t)
          y
          (DUTYLEVEL: y < x)
          (SIM: Fairness.base_logic.upred.uPred_holds
                    (to_upred (wpsim x tid ⊤ ibot7 ibot7
                      (fun r_src r_tgt =>
                         ((own_thread tid ∗ ObligationRA.duty y inlp tid []) ∗ ⌜r_src = r_tgt⌝)%I) false false th0 th1)) r)
      :
      @local_sim_init
        ( (GRA.to_URA Σ)) (Mod.state md_src) (Mod.state md_tgt)
        (Mod.ident md_src) (Mod.ident md_tgt) owf nat_wf
        (liftI
           (fun (ths : TIdSet.t)
              (im_src : imap (Mod.ident md_src) owf)
              (im_tgt : imap (sum_tid (Mod.ident md_tgt)) nat_wf)
              (st_src : Mod.state md_src) (st_tgt : Mod.state md_tgt) =>
              (default_I x ths im_src im_tgt st_src st_tgt ∗
                         (wsat_auth x ∗ wsats x ∗ OwnE ⊤))%I)) Any.t Any.t eq r tid th0 th1.
    Proof.
      ii. eapply wpsim_lsim; eauto.
    Qed.

    Lemma wpsim_local_sim x
          (th0: thread (Mod.ident md_src) (sE (Mod.state md_src)) Any.t)
          (th1: thread (Mod.ident md_tgt) (sE (Mod.state md_tgt)) Any.t)
          r_arg
          y
          (DUTYLEVEL : y < x)
          (SIM: forall tid,
              Fairness.base_logic.upred.uPred_holds
                (to_upred ((own_thread tid)
                 -∗
                 (ObligationRA.duty y inlp tid [])
                 -∗
                 (wpsim x tid ⊤ ibot7 ibot7
                        (fun r_src r_tgt =>
                           ((own_thread tid ∗ ObligationRA.duty y inlp tid []) ∗ ⌜r_src = r_tgt⌝)%I) false false th0 th1))%I) r_arg)
      :
      @local_sim_arg
        ( (GRA.to_URA Σ)) (Mod.state md_src) (Mod.state md_tgt)
        (Mod.ident md_src) (Mod.ident md_tgt) owf nat_wf
        (liftI
           (fun (ths : TIdSet.t)
              (im_src : imap (Mod.ident md_src) owf)
              (im_tgt : imap (sum_tid (Mod.ident md_tgt)) nat_wf)
              (st_src : Mod.state md_src) (st_tgt : Mod.state md_tgt) =>
              (default_I x ths im_src im_tgt st_src st_tgt ∗
                         (wsat_auth x ∗ wsats x ∗ OwnE ⊤))%I)) Any.t Any.t eq th0 th1 r_arg.
    Proof.
      ii. specialize (SIM tid). r in INV.
      assert (IMPL:
               ((Own r_arg) ∗ (default_I x ths0 im_src0 im_tgt0 st_src0 st_tgt0 ∗
                                          (wsat_auth x ∗ wsats x ∗ OwnE ⊤)))
                 ⊢
                 #=> (((default_I x ths1 im_src0 im_tgt1 st_src0 st_tgt0)
                        ∗
                        (wsat_auth x ∗ wsats x ∗ OwnE ⊤))
                        ∗
                        wpsim x tid ⊤ ibot7 ibot7
                        (λ r_src r_tgt : Any.t,
                            ((own_thread tid ∗ ObligationRA.duty y inlp tid []) ∗ ⌜r_src = r_tgt⌝)%I)
                        false false th0 th1)).
      { iIntros "[ARG [D SAT]]".
        iPoseProof (default_I_thread_alloc with "D") as "> [OWN [DUTY D]]".
        { eauto. }
        { eauto. }
        iModIntro. iFrame.
        iRevert "OWN DUTY". iStopProof.
        rewrite Own_eq. unfold IPM.Own_def. uPred.unseal. rr.
        split. ii. rr in H0. des. rewrite H0 in H1. rewrite H0 in H3.
        revert SIM. uPred.unseal. intros SIM.
        eapply Fairness.base_logic.upred.uPred_mono.
        { apply SIM; eauto.
          - eapply (cmra_valid_op_l _ z). r_wf H1.
          - eapply (cmra_valid_op_l _ z). r_wf H3.
        }
        rewrite H0. exists z. r_solve.
      }
      revert IMPL. rewrite Own_eq. unfold IPM.Own_def.
      uPred.unseal. intros [IMPL].
       (* rr in IMPL. *)
      hexploit IMPL; [|eauto|..]; cycle 1.
      { rr. eexists _,_. esplits; eauto. rr. eexists. reflexivity.
        revert INV. uPred.unseal. intros INV. done.
      }
      i. rr in H.  hexploit H; last first.
      i. des.
      rr in H1. des. subst.
      eexists _, _. splits.
      { done. }
      { rewrite H1 in H0. exact H0. }
      i. ss. hexploit wpsim_lsim.
      { apply DUTYLEVEL. }
      { uPred.unseal. eauto. }
      { uPred.unseal. eapply INV0. }
      { eauto. }
      { eauto. }
      uPred.unseal. eauto.
      { instantiate (1:=ε). r_wf VALID. }
      { eapply (cmra_valid_op_l _ r_ctx0). r_wf VALID. }
    Qed.

    Section WHOLE_PROGRAM_SIM.
      Variable c: list (fname * Any.t).

      Definition fun_pairs :=
        (NatMapP.of_list (numbering (List.map (fun '(fn, arg) => (fn2th md_src fn arg, fn2th md_tgt fn arg)) c))).

      Local Instance nat_map_equiv : Proper (eq ==> eq ==> equiv ==> equiv)
        (λ (_ : NatMap.key) (r s : Σ), r ⋅ s).
      Proof. intros ???????? EQm. rewrite EQm. subst. done. Qed.

      Lemma natmap_prop_sum_resmap A (P: nat -> A -> iProp) (m: NatMap.t A) rs
            (SAT: Fairness.base_logic.upred.uPred_holds (to_upred (natmap_prop_sum m P)) rs)
            (WF: ✓ rs)
        :
        exists (rm: NatMap.t Σ),
          (<<EXT: (NatMap.fold (fun _ r s => r ⋅ s) rm ε) ≼ rs>>)/\
            (<<PAIR: nm_wf_pair m rm>>) /\
            (<<FORALL: forall k a r
                              (FINDA: NatMap.find k m = Some a)
                              (FINDR: NatMap.find k rm ≡ Some r),
                Fairness.base_logic.upred.uPred_holds
                  (to_upred (P k a)) r>>).
      Proof.
        revert rs SAT WF.
        pattern m. revert m. eapply nm_ind; i.
        { exists (NatMap.empty _). splits.
          { exists rs. rewrite left_id. auto. apply _. }
          { eapply nm_wf_pair_empty_empty_eq. }
          { i. rewrite NatMapP.F.empty_o in FINDA. ss. }
        }
        hexploit (natmap_prop_remove_find (Σ:=Σ)).
        { eapply nm_find_add_eq. }
        uPred.unseal. intros [H].
        hexploit H.
        { eapply WF. }
        { eauto. }
        i. rr in H0. des. rewrite H0 in SAT. subst.
        rewrite nm_find_none_rm_add_eq in H2; auto.
        hexploit IH; eauto.
        { eapply (cmra_valid_op_r x1). rewrite H0 in WF. apply WF. }
        i. des. eexists (NatMap.add k _ rm). splits.
        { r in EXT. des. exists z.
          rewrite EXT in H0.
          rewrite H0.
          erewrite (NatMapP.fold_add (eqA := equiv) _ _ _ _).
          { rewrite assoc; [done|apply _]. }
          Unshelve.
          { eapply nm_wf_pair_find_cases in PAIR. des.
            apply NatMapP.F.not_find_in_iff. eapply PAIR; auto.
          }
          { ii. r_solve. }
        }
        { eapply nm_wf_pair_add; eauto. }
        { i. rewrite NatMapP.F.add_o in FINDA.
          rewrite NatMapP.F.add_o in FINDR. des_ifs.
          - inv FINDR. unfold iProp in *. eapply Fairness.base_logic.upred.uPred_mono; [exact H1|].
            exists ε. rewrite right_id; [|apply _]. done.
          - eapply FORALL; auto.
        }
      Qed.

      Record whole_sim: Prop :=
        mk_whole_sim {
            init_res: Σ;
            init_res_cond: initial_res_wf init_res;
            init_inv:
            exists (l1 l0: index) (DL: l0 < l1) (o: Ord.t),
              (Own init_res ∗ (initial_prop l0 (key_set (prog2ths md_src c)) o)) (* INIT *)
                -∗
                (=|l1|=(fairI (ident_tgt:=md_tgt.(Mod.ident)) l1)={⊤}=>
                      (
                        (natmap_prop_sum
                           fun_pairs
                           (fun tid '(th_src, th_tgt) =>
                              wpsim
                                l1
                                tid ⊤
                                ibot7 ibot7
                                (fun r_src r_tgt => (own_thread tid ∗ ObligationRA.duty l0 inlp tid []) ∗ ⌜r_src = r_tgt⌝)
                                false false th_src th_tgt))
                ));
          }.

      Lemma whole_sim_implies_usersim
            (SIM: whole_sim)
        :
        UserSim.sim md_src md_tgt (prog2ths md_src c) (prog2ths md_tgt c).
      Proof.
        Local Transparent FUpd.
        inv SIM. des.
        assert (forall im_tgt,
                 exists (r: Σ),
                   (<<SAT:
                     Fairness.base_logic.upred.uPred_holds (to_upred (∃ im_src,
                         ((default_I l1 (key_set (prog2ths md_src c)) im_src im_tgt (Mod.st_init md_src) (Mod.st_init md_tgt))
                            ∗
                            (wsat_auth l1 ∗ wsats l1 ∗ OwnE ⊤))
                           ∗
                           (natmap_prop_sum
                              fun_pairs
                              (fun tid '(th_src, th_tgt) =>
                                 wpsim
                                   l1
                                   tid ⊤
                                   ibot7 ibot7
                                   (fun r_src r_tgt => ((own_thread tid ∗ ObligationRA.duty l0 inlp tid [])) ∗ ⌜r_src = r_tgt⌝)
                                   false false th_src th_tgt)))%I) r>>) /\
                     (<<WF: ✓ r>>)).
        { i. eapply iProp_satisfable.
          { eapply reswf_gen; eauto. }
          iIntros "[H0 H1]".
          iPoseProof (default_initial_res_init with "H1") as "H1".
          apply DL.
          iPoseProof ("H1" $! _ _ _ _ _) as ">[% [A [B [C [D [E [F [G [H [I J]]]]]]]]]]".
          unfold initial_prop in init_inv.
          iDestruct "A" as "(A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8)".
          iPoseProof (init_inv with "[H0 D E B C F G] [A6 A7 I J]") as ">[F [W [E init_ctx]]]".
          { iFrame "H0 D E B C F G". }
          { iFrame "A6 A7 I J". }
          iModIntro. iExists _. iFrame "A1 A2 A3 A4 A5 A8 H F W E init_ctx".
        }
        apply (@UserSim.mk
                 md_src md_tgt (prog2ths md_src c) (prog2ths md_tgt c) owf nat_wf (inhabits 0) NUNBOUND ( Σ)).
        i. specialize (H im_tgt). des.
        revert SAT. uPred.unseal.
        intros [im_src SAT].
        rr in SAT. des. subst.
        rr in SAT0. des. subst.
        hexploit natmap_prop_sum_resmap.
        { eauto. }
        { eapply cmra_valid_op_r. rewrite SAT in WF. exact WF. }
        i. des.
        eexists (liftI (fun ths im_src im_tgt st_src st_tgt => (@default_I md_src.(Mod.state) md_tgt.(Mod.state) md_src.(Mod.ident) md_tgt.(Mod.ident) _ Σ _ _ _ _ _ _ _ _ _ _ l1 ths im_src im_tgt st_src st_tgt ∗ (wsat_auth l1 ∗ wsats l1 ∗ OwnE ⊤))%I)), im_src, rm, _.
        splits.
        { ss. uPred.unseal. rr. esplits; eauto. }
        { apply nm_find_some_implies_forall3.
          { eapply prog2ths_nm_wf_pair. }
          { etrans; [|apply PAIR].
            eapply list_of_numbering_nm_wf_pair.
            repeat rewrite map_length. auto.
          }
          i. hexploit (FORALL k (e1, e2) e3).
          { clear - FIND1 FIND2. unfold fun_pairs, prog2ths in *.
            unfold numbering in *. revert FIND1 FIND2.
            generalize 0. revert e1 e2. induction c; ss; i.
            { unfold NatMapP.uncurry in *. destruct a. ss.
              rewrite NatMapP.F.add_o in *. des_ifs.
              eapply IHl; eauto.
            }
          }
          { rewrite -FIND3. auto. }
          i. ii. eapply wpsim_local_sim_init; eauto.
          uPred.unseal. eauto.
        }
        { rr in EXT. des.
          rewrite EXT in SAT. rewrite SAT in WF.
          eapply (cmra_valid_op_l _ z). r_wf WF.
        }
        Local Opaque FUpd.
      Qed.

      Lemma whole_sim_implies_refinement
            (SIM: whole_sim)
        :
        Adequacy.improves (interp_all md_src.(Mod.st_init) (prog2ths md_src c) 0)
                          (interp_all md_tgt.(Mod.st_init) (prog2ths md_tgt c) 0).
      Proof.
        eapply usersim_adequacy. eapply whole_sim_implies_usersim. auto.
      Qed.

      Record whole_sim_simple: Prop :=
        mk_whole_sim_simple {

            whole_sim_simple_invariant: iProp; (* I *)

            whole_sim_funs_simple:
            exists l1 l0 (DL: l0 < l1) (r: Σ),
              (<<WF: initial_res_wf r>>) /\
                (<<SIM: ((Own r ∗ (initial_prop l0 (key_set (prog2ths md_src c)) Ord.omega))
                           ⊢ #=>
                           (whole_sim_simple_invariant
                              ∗
                              (natmap_prop_sum
                                 fun_pairs
                                 (fun tid '(th_src, th_tgt) =>
                                    wpsim
                                      l1
                                      tid ⊤
                                      ibot7 ibot7
                                      (fun r_src r_tgt => ((own_thread tid ∗ FairRA.black_ex inlp tid 1) ∗ ⌜r_src = r_tgt⌝)%I)
                                      false false th_src th_tgt))))>>);
          }.

      Lemma whole_sim_simple_whole_sim
            (SIM: whole_sim_simple)
        :
        whole_sim.
      Proof.
        Local Transparent FUpd.
        inv SIM. des. econs.
        { eauto. }
        exists l1, l0, DL, Ord.omega. iIntros "H (A & B & C)".
        iPoseProof (SIM with "H") as "> [H0 H1]".
        iModIntro. iFrame.
        iApply (natmap_prop_sum_impl with "H1"). i. des_ifs.
        iApply (wpsim_mono). i.
        iIntros "[[H0 H1] H2]". iModIntro. iFrame.
        iApply ObligationRA.black_to_duty. auto.
        Local Opaque FUpd.
      Qed.

      Theorem whole_sim_simple_implies_refinement
              (SIM: whole_sim_simple)
        :
        Adequacy.improves (interp_all md_src.(Mod.st_init) (prog2ths md_src c) 0)
                          (interp_all md_tgt.(Mod.st_init) (prog2ths md_tgt c) 0).
      Proof.
        apply whole_sim_implies_refinement.
        apply whole_sim_simple_whole_sim. auto.
      Qed.

    End WHOLE_PROGRAM_SIM.


    Section CONTEXT_SIM.

      Record context_sim: Prop :=
        mk_context_sim {
            init_res: Σ;
            init_res_cond: initial_res_wf init_res;
            init_inv:
            exists l1 l0 (DL: l0 < l1) o,
              (Own init_res ∗ (initial_prop l0 TIdSet.empty o)) (* INIT *)
                -∗
                (=|l1|=(fairI (ident_tgt:=md_tgt.(Mod.ident)) l1)={⊤}=>
                       (□(∀ fn args,
                                match md_src.(Mod.funs) fn, md_tgt.(Mod.funs) fn with
                                | Some ktr_src, Some ktr_tgt =>
                                    ∀ tid,
                                      (own_thread tid)
                                        -∗
                                        (ObligationRA.duty l0 inlp tid [])
                                        -∗
                                        (wpsim
                                           l1
                                           tid ⊤
                                           ibot7 ibot7
                                           (fun r_src r_tgt => (own_thread tid ∗ ObligationRA.duty l0 inlp tid []) ∗ ⌜r_src = r_tgt⌝)
                                           false false (ktr_src args) (ktr_tgt args))
                                | None, None => True
                                | _, _ => False
                                end)));
          }.

      Lemma context_sim_implies_modsim
            (SIM: context_sim)
        :
        ModSim.mod_sim md_src md_tgt.
      Proof.
        eapply ModSimPers.imply_mod_sim.
        Local Transparent FUpd.
        inv SIM. des.
        i. assert (forall im_tgt,
                    exists (r: Σ),
                      (<<SAT:
                        Fairness.base_logic.upred.uPred_holds
                          (to_upred (∃ im_src,
                             ((default_I l1 NatSet.empty im_src im_tgt (Mod.st_init md_src) (Mod.st_init md_tgt) ∗ (wsat_auth l1 ∗ wsats l1 ∗ OwnE ⊤)))
                             ∧
                               (□ ∀ fn args,
                                     match md_src.(Mod.funs) fn, md_tgt.(Mod.funs) fn with
                                     | Some ktr_src, Some ktr_tgt =>
                                         ∀ tid,
                                           (own_thread tid)
                                             -∗
                                             (ObligationRA.duty l0 inlp tid [])
                                             -∗
                                             (wpsim
                                                l1
                                                tid ⊤
                                                ibot7 ibot7
                                                (fun r_src r_tgt => (own_thread tid ∗ ObligationRA.duty l0 inlp tid []) ∗ ⌜r_src = r_tgt⌝)
                                                false false (ktr_src args) (ktr_tgt args))
                                     | None, None => True
                                     | _, _ => False
                                     end))%I) r>>) /\
                        (<<WF: ✓ r>>)).
        { i. eapply iProp_satisfable.
          { eapply reswf_gen; eauto. }
          iIntros "[H0 H1]".
          iPoseProof (default_initial_res_init with "H1") as "H1".
          apply DL.
          iPoseProof ("H1" $! _ _ _ _ _) as ">[% [A [B [C [D [E [F [G [H [I J]]]]]]]]]]".
          unfold initial_prop in init_inv.
          iDestruct "A" as "(A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8)".
          iPoseProof (init_inv with "[H0 D E B C F G] [A6 A7 I J]") as ">[F [W [E init_ctx]]]".
          { iFrame "H0 D E B C F G". }
          { iFrame "A6 A7 I J". }
          iModIntro. iExists _. iFrame "A1 A2 A3 A4 A5 A8 H F W E init_ctx".
        }
        apply (@ModSimPers.mk
                 md_src md_tgt owf nat_wf (inhabits 0) NUNBOUND ( Σ)).
        i. specialize (H im_tgt). des.
        revert SAT. uPred.unseal. intros SAT.
        rr in SAT. des. rename a into im_src.
        rr in SAT. des.
        (* rr in SAT2. des. *)
        revert SAT0. unfold bi_intuitionistically,bi_affinely,bi_affinely. uPred.unseal.
        intros SAT0.
        rr in SAT0. des.
        (* unseal "iProp". *)
        exists (liftI (fun ths im_src im_tgt st_src st_tgt => (@default_I md_src.(Mod.state) md_tgt.(Mod.state) md_src.(Mod.ident) md_tgt.(Mod.ident) _ Σ _ _ _ _ _ _ _ _ _ _ l1 ths im_src im_tgt st_src st_tgt ∗ (wsat_auth l1 ∗ wsats l1 ∗ OwnE ⊤))%I)).
        esplits.
        { ss. uPred.unseal. eauto. }
        { auto. }
        i. specialize (SAT1 fn args).
        des_ifs; ss.
        { eapply wpsim_local_sim; eauto. i.
          specialize (SAT1 tid). uPred.unseal. auto.
        }
      Qed.

      Lemma context_sim_implies_contextual_refinement
            (SIM: context_sim)
        :
        forall p,
          Adequacy.improves (interp_all md_src.(Mod.st_init) (prog2ths md_src p) 0)
                            (interp_all md_tgt.(Mod.st_init) (prog2ths md_tgt p) 0).
      Proof.
        eapply modsim_adequacy. eapply context_sim_implies_modsim. auto.
      Qed.

      Record context_sim_simple: Prop :=
        mk_context_sim_simple {

            context_sim_simple_invariant: iProp; (* I *)

            l1 : index;
            l0 : index;
            DL : l0 < l1;

            init_satisfied:
            exists (r: Σ),
              (<<WF: initial_res_wf r>>) /\
                (<<SAT: ((Own r ∗ (initial_prop l0 TIdSet.empty Ord.omega))
                           ⊢ #=> context_sim_simple_invariant)%I>>);

            sim_funs:
            forall fn args,
              match md_src.(Mod.funs) fn, md_tgt.(Mod.funs) fn with
              | Some ktr_src, Some ktr_tgt =>
                  forall tid,
                      (FairRA.black_ex inlp tid 1)
                      -∗
                      (wpsim
                         l1
                         tid ⊤
                         ibot7 ibot7
                         (fun r_src r_tgt => FairRA.black_ex inlp tid 1 ∗ ⌜r_src = r_tgt⌝)
                         false false (ktr_src args) (ktr_tgt args))
              | None, None => True
              | _, _ => False
              end;
          }.

      Lemma context_sim_simple_context_sim
            (SIM: context_sim_simple)
        :
        context_sim.
      Proof.
        inv SIM. des. econs.
        { eauto. }
        { exists l1, l0, DL, Ord.omega. iIntros "H".
          iPoseProof (SAT with "H") as "> SAT". iModIntro.
          iModIntro. iIntros. specialize (sim_funs fn args).
          destruct (Mod.funs md_src fn) eqn:Es; last first.
          { des_ifs. }
          destruct (Mod.funs md_tgt fn) eqn:Et; last first.
          { done. }
          iIntros (?) "H B". iPoseProof (sim_funs with "[B]") as "B".
          { iApply ObligationRA.duty_to_black. auto. }
          iApply (wpsim_wand with "B [H]").
          iIntros (? ?) "[H0 H1]". iModIntro. iFrame.
          iApply ObligationRA.black_to_duty. auto.
        }
      Qed.

      Theorem context_sim_simple_implies_contextual_refinement
              (SIM: context_sim_simple)
        :
        forall p,
          Adequacy.improves (interp_all md_src.(Mod.st_init) (prog2ths md_src p) 0)
                            (interp_all md_tgt.(Mod.st_init) (prog2ths md_tgt p) 0).
      Proof.
        apply context_sim_implies_contextual_refinement.
        apply context_sim_simple_context_sim. auto.
      Qed.

    End CONTEXT_SIM.
  End WSIM.
End WSim.
