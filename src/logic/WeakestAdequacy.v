From sflib Require Import sflib.
From Paco Require Import paco.
From Fairness Require Import ITreeLib IProp IPM ModSim ModSimNat PCM Weakest Concurrency ModAdequacy Axioms.
Require Import Coq.Logic.PropExtensionality.
From Fairness Require LPCM.
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

    Context `{Σ: GRA.t}.

    Lemma iProp_satisfable (r0: Σ) (P: iProp) (WF: URA.wf r0)
          (IMPL: Own r0 ⊢ #=> P)
      :
      exists r1, P r1 /\ URA.wf r1.
    Proof.
      rr in IMPL. unseal "iProp". hexploit (IMPL r0); auto.
      { rr. unseal "iProp". reflexivity. }
      i. rr in H. unseal "iProp".
      hexploit (H URA.unit).
      { rewrite URA.unit_id. auto. }
      i. des. rewrite URA.unit_id in H0. esplits; eauto.
    Qed.

    Context `{MONORA: @GRA.inG monoRA Σ}.
    Context `{THDRA: @GRA.inG ThreadRA Σ}.
    Context `{STATESRC: @GRA.inG (stateSrcRA md_src.(Mod.state)) Σ}.
    Context `{STATETGT: @GRA.inG (stateTgtRA md_tgt.(Mod.state)) Σ}.
    Context `{IDENTSRC: @GRA.inG (identSrcRA md_src.(Mod.ident)) Σ}.
    Context `{IDENTTGT: @GRA.inG (identTgtRA md_tgt.(Mod.ident)) Σ}.
    Context `{OBLGRA: @GRA.inG ObligationRA.t Σ}.
    Context `{ARROWRA: @GRA.inG (ArrowRA md_tgt.(Mod.ident)) Σ}.
    Context `{EDGERA: @GRA.inG EdgeRA Σ}.
    Context `{ONESHOTRA: @GRA.inG (@FiniteMap.t (OneShot.t unit)) Σ}.
    Variable init_res: Σ.
    Hypothesis RESWF: URA.wf (init_res ⋅ (@default_initial_res _ md_src.(Mod.state) md_tgt.(Mod.state) md_src.(Mod.ident) md_tgt.(Mod.ident) _ _ _ _ _ _ _)).

    Definition initial_prop (ths: TIdSet.t) o: iProp :=
      ((FairRA.whites (fun _ => True: Prop) o)
         **
         (FairRA.blacks (fun i => match i with | inr _ => True | _ => False end: Prop))
         **
         (natmap_prop_sum ths (fun tid _ => ObligationRA.duty (inl tid) []))
         **
         (natmap_prop_sum ths (fun tid _ => own_thread tid))
         **
         (St_src md_src.(Mod.st_init))
         **
         (St_tgt md_tgt.(Mod.st_init)))%I
    .

    Lemma stsim_lsim (I: list iProp) tid (r r_shared r_ctx: Σ)
          ths im_src im_tgt0 im_tgt1 (st_src: md_src.(Mod.state)) (st_tgt: md_tgt.(Mod.state)) (fs ft: bool)
          (th0: thread (Mod.ident md_src) (sE (Mod.state md_src)) Any.t)
          (th1: thread (Mod.ident md_tgt) (sE (Mod.state md_tgt)) Any.t)
          (SIM: stsim I tid (topset I) ibot7 ibot7
                      (fun r_src r_tgt =>
                         ((own_thread tid ** ObligationRA.duty (inl tid) []) ** ⌜r_src = r_tgt⌝)%I) false false th0 th1 r)
          (INV: (default_I ths im_src im_tgt0 st_src st_tgt **
                              mset_all (nth_default True%I I) (topset I)) r_shared)
          (FUPD: fair_update im_tgt0 im_tgt1 (sum_fmap_l (tids_fmap tid ths)))
          (WF: URA.wf ((r_shared ⋅ r) ⋅ r_ctx))
      :
      (@lsim
         (to_LURA (GRA.to_URA Σ)) (Mod.state md_src) (Mod.state md_tgt)
         (Mod.ident md_src) (Mod.ident md_tgt) owf nat_wf
         (liftI
            (fun (ths : TIdSet.t)
                 (im_src : imap (Mod.ident md_src) owf)
                 (im_tgt : imap (sum_tid (Mod.ident md_tgt)) nat_wf)
                 (st_src : Mod.state md_src) (st_tgt : Mod.state md_tgt) =>
               default_I ths im_src im_tgt st_src st_tgt **
                         mset_all (nth_default True%I I) (topset I)))
         tid
         Any.t Any.t
         (@local_RR
            (to_LURA (GRA.to_URA Σ)) (Mod.state md_src) (Mod.state md_tgt)
            (Mod.ident md_src) (Mod.ident md_tgt) owf nat_wf
            (liftI
               (fun (ths : TIdSet.t)
                    (im_src : imap (Mod.ident md_src) owf)
                    (im_tgt : imap (sum_tid (Mod.ident md_tgt)) nat_wf)
                    (st_src : Mod.state md_src) (st_tgt : Mod.state md_tgt) =>
                  default_I ths im_src im_tgt st_src st_tgt **
                            mset_all (nth_default True%I I) (topset I)))
            Any.t Any.t
            eq tid)) fs ft r_ctx th0 th1
                     (ths, im_src, im_tgt1, st_src, st_tgt).
    Proof.
      ii. rr in SIM. unseal "iProp". specialize (SIM ths).
      rr in SIM. unseal "iProp". specialize (SIM im_src).
      rr in SIM. unseal "iProp". specialize (SIM im_tgt1).
      rr in SIM. unseal "iProp". specialize (SIM st_src).
      rr in SIM. unseal "iProp". specialize (SIM st_tgt).
      r in INV.
      rr in SIM. unseal "iProp". hexploit (SIM r_shared).
      { eapply URA.wf_mon. instantiate (1:=r_ctx). r_wf WF. }
      { rr in INV. rr. unseal "iProp". des. subst. esplits.
        { eauto. }
        { rr. unseal "iProp". esplits. rr. unseal "iProp". esplits.
          { symmetry. apply URA.unit_idl. }
          { rr. unseal "iProp". eauto. }
          { auto. }
        }
        { auto. }
      }
      i. rr in H. unseal "iProp". hexploit H.
      { instantiate (1:=r_ctx). r_wf WF. }
      i. eapply lsim_flag_any. eapply lsim_monoR.
      { ginit. ss. refine (@eq_rect _ _ id H0 _ _).
        repeat f_equal.
        { repeat (let x := fresh "x" in extensionality x).
          eapply propositional_extensionality. split; i; ss.
          dependent destruction H1. rr in REL. unseal "iProp". des.
          rr in REL. unseal "iProp". des. subst.
          rr in REL. unseal "iProp". des. subst.
          rr in REL0. unseal "iProp". ss.
        }
        { repeat (let x := fresh "x" in extensionality x).
          eapply propositional_extensionality. split; i; ss.
          dependent destruction H1. rr in REL. unseal "iProp". des.
          rr in REL. unseal "iProp". des. subst.
          rr in REL. unseal "iProp". des. subst.
          rr in REL0. unseal "iProp". ss.
        }
        { reflexivity. }
      }
      { i. ss. des_ifs. des.
        rr in RET0. unseal "iProp". des. subst.
        rr in RET2. unseal "iProp". des. subst.
        rr in RET3. unseal "iProp". subst.
        rr in RET1. unseal "iProp". des. subst.
        hexploit (@default_I_past_final md_src.(Mod.state) md_tgt.(Mod.state) md_src.(Mod.ident) md_tgt.(Mod.ident)).
        i. rr in H1. unseal "iProp". hexploit H1.
        { instantiate (1:=a1). eapply URA.wf_mon.
          instantiate (1:=b ⋅ (a0 ⋅ b0) ⋅ r_ctx0). r_wf WF0.
        }
        { eauto. }
        i. rr in H2. unseal "iProp".
        hexploit H2.
        { instantiate (1:=a0). eapply URA.wf_mon.
          instantiate (1:=b ⋅ b0 ⋅ r_ctx0). r_wf WF0.
        }
        { eauto. }
        i. rr in H3. unseal "iProp".
        hexploit H3.
        { instantiate (1:=b ⋅ b0 ⋅ r_ctx0). r_wf WF0. }
        i. des.
        rr in H5. unseal "iProp". des.
        rr in H5. unseal "iProp". des. subst.
        rr in H6. unseal "iProp".
        rr. esplits.
        { eauto. }
        2:{ rr. unseal "iProp". esplits; eauto. }
        { instantiate (1:=URA.unit).
          rewrite LPCM.URA.unfold_wf.
          rewrite LPCM.URA.unfold_add. ss.
          cut (URA.wf (((b1 ⋅ b) ⋅ ε) ⋅ r_ctx0)).
          { intros WFH. rewrite URA.unfold_wf in WFH.
            rewrite URA.unfold_add in WFH.
            rewrite URA.unfold_add. ss.
          }
          eapply URA.wf_mon. instantiate (1:=a ⋅ b0). r_wf H4.
        }
        { auto. }
      }
    Qed.

    Lemma stsim_local_sim_init (I: list iProp) tid (r: Σ)
          (th0: thread (Mod.ident md_src) (sE (Mod.state md_src)) Any.t)
          (th1: thread (Mod.ident md_tgt) (sE (Mod.state md_tgt)) Any.t)
          (SIM: stsim I tid (topset I) ibot7 ibot7
                      (fun r_src r_tgt =>
                         ((own_thread tid ** ObligationRA.duty (inl tid) []) ** ⌜r_src = r_tgt⌝)%I) false false th0 th1 r)
      :
      @local_sim_init
        (to_LURA (GRA.to_URA Σ)) (Mod.state md_src) (Mod.state md_tgt)
        (Mod.ident md_src) (Mod.ident md_tgt) owf nat_wf
        (liftI
           (fun (ths : TIdSet.t)
                (im_src : imap (Mod.ident md_src) owf)
                (im_tgt : imap (sum_tid (Mod.ident md_tgt)) nat_wf)
                (st_src : Mod.state md_src) (st_tgt : Mod.state md_tgt) =>
              default_I ths im_src im_tgt st_src st_tgt **
                        mset_all (nth_default True%I I) (topset I))) Any.t Any.t eq r tid th0 th1.
    Proof.
      ii. assert (WF: URA.wf ((r_shared ⋅ r) ⋅ r_ctx)).
      { rewrite LPCM.URA.unfold_wf in VALID.
        rewrite LPCM.URA.unfold_add in VALID.
        rewrite URA.unfold_wf.
        rewrite URA.unfold_add. auto.
      }
      eapply stsim_lsim; eauto.
    Qed.

    Lemma stsim_local_sim (I: list iProp)
          (th0: thread (Mod.ident md_src) (sE (Mod.state md_src)) Any.t)
          (th1: thread (Mod.ident md_tgt) (sE (Mod.state md_tgt)) Any.t)
          (SIM: forall tid,
              ((own_thread tid)
                 ⊢
                 (ObligationRA.duty (inl tid) [])
                 -∗
                 (stsim I tid (topset I) ibot7 ibot7
                        (fun r_src r_tgt =>
                           ((own_thread tid ** ObligationRA.duty (inl tid) []) ** ⌜r_src = r_tgt⌝)%I) false false th0 th1))%I)
      :
      @local_sim
        (to_LURA (GRA.to_URA Σ)) (Mod.state md_src) (Mod.state md_tgt)
        (Mod.ident md_src) (Mod.ident md_tgt) owf nat_wf
        (liftI
           (fun (ths : TIdSet.t)
                (im_src : imap (Mod.ident md_src) owf)
                (im_tgt : imap (sum_tid (Mod.ident md_tgt)) nat_wf)
                (st_src : Mod.state md_src) (st_tgt : Mod.state md_tgt) =>
              default_I ths im_src im_tgt st_src st_tgt **
                        mset_all (nth_default True%I I) (topset I))) Any.t Any.t eq th0 th1.
    Proof.
      ii. assert (WF: URA.wf (r_shared0 ⋅ r_ctx0)).
      { rewrite LPCM.URA.unfold_wf in VALID.
        rewrite LPCM.URA.unfold_add in VALID.
        rewrite URA.unfold_wf.
        rewrite URA.unfold_add. auto.
      }
      specialize (SIM tid). r in INV.
      assert (IMPL:
               (default_I ths0 im_src0 im_tgt0 st_src0 st_tgt0 **
                          mset_all (nth_default True%I I) (topset I))
                 ⊢
                 #=> ((default_I ths1 im_src0 im_tgt1 st_src0 st_tgt0)
                        **
                        (mset_all (nth_default True%I I) (topset I))
                        **
                        stsim I tid (topset I) ibot7 ibot7
                        (λ r_src r_tgt : Any.t,
                            (own_thread tid ** ObligationRA.duty (inl tid) []) ** ⌜r_src = r_tgt⌝)
                        false false th0 th1)).
      { iIntros "[D SAT]".
        iPoseProof (default_I_thread_alloc with "D") as "> [[OWN DUTY] D]".
        { eauto. }
        { eauto. }
        iModIntro. iFrame. iApply (SIM with "OWN DUTY").
      }
      rr in IMPL. unseal "iProp".
      hexploit IMPL; [|eauto|..].
      { eapply URA.wf_mon. instantiate (1:=r_ctx0). r_wf WF. }
      i. rr in H. unseal "iProp".
      hexploit H.
      { eauto. }
      i. des.
      rr in H1. unseal "iProp". des. subst.
      exists a, b. splits.
      { r. auto. }
      { rewrite LPCM.URA.unfold_wf.
        rewrite LPCM.URA.unfold_add. ss.
        rewrite URA.unfold_wf in H0.
        rewrite URA.unfold_add in H0. auto.
      }
      i. ss. eapply stsim_lsim.
      { eauto. }
      { eapply INV0. }
      { eauto. }
      { rewrite LPCM.URA.unfold_wf in VALID0.
        rewrite LPCM.URA.unfold_add in VALID0. ss.
        rewrite URA.unfold_wf.
        rewrite URA.unfold_add. auto.
      }
    Qed.

    Section WHOLE_PROGRAM_SIM.
      Variable c: list (fname * Any.t).

      Definition fun_pairs :=
        (NatMapP.of_list (numbering (List.map (fun '(fn, arg) => (fn2th md_src fn arg, fn2th md_tgt fn arg)) c))).

      (* TODO: Change Ord.omega to user defined values *)
      Record whole_sim: Prop :=
        mk_whole_sim {
            I_whole: list iProp;
            init_whole:
            (Own init_res ** (initial_prop (NatMapP.of_list (numbering (List.map (fun _ => tt) c))) Ord.omega) (* INIT *)
                 -∗
                 (#=>
                    ((mset_all (nth_default True%I I_whole) (topset I_whole)) (* I *)
                       **
                       (natmap_prop_sum
                          fun_pairs
                          (fun tid '(th_src, th_tgt) =>
                             stsim
                               I_whole tid (topset I_whole)
                               ibot7 ibot7
                               (fun r_src r_tgt => own_thread tid ** ObligationRA.duty (inl tid) [] ** ⌜r_src = r_tgt⌝)
                               false false th_src th_tgt)))))
          }.

      Lemma natmap_prop_sum_resmap A (P: nat -> A -> iProp) (m: NatMap.t A) rs
            (SAT: natmap_prop_sum m P rs)
            (WF: URA.wf rs)
        :
        exists (rm: NatMap.t Σ),
          (<<EXT: URA.extends (NatMap.fold (fun _ r s => URA.add r s) rm URA.unit) rs>>)/\
            (<<PAIR: nm_wf_pair m rm>>) /\
            (<<FORALL: forall k a r
                              (FINDA: NatMap.find k m = Some a)
                              (FINDR: NatMap.find k rm = Some r),
                P k a r>>).
      Proof.
        revert rs SAT WF.
        pattern m. revert m. eapply nm_ind; i.
        { exists (NatMap.empty _). splits.
          { exists rs. eapply URA.unit_idl. }
          { eapply nm_wf_pair_empty_empty_eq. }
          { i. rewrite NatMapP.F.empty_o in FINDA. ss. }
        }
        hexploit natmap_prop_remove_find.
        { eapply nm_find_add_eq. }
        i. rr in H. unseal "iProp".
        hexploit H.
        { eapply WF. }
        { eauto. }
        i. rr in H0. unseal "iProp". des. subst.
        rewrite nm_find_none_rm_add_eq in H2; auto.
        hexploit IH; eauto.
        { eapply URA.wf_mon. instantiate (1:=a). r_wf WF. }
        i. des. exists (NatMap.add k a rm). splits.
        { r in EXT. des. subst. exists ctx. rewrite NatMapP.fold_add; auto.
          { r_solve. }
          { ii. subst. auto. }
          { ii. r_solve. }
          { eapply nm_wf_pair_find_cases in PAIR. des.
            apply NatMapP.F.not_find_in_iff. eapply PAIR; auto.
          }
        }
        { eapply nm_wf_pair_add; eauto. }
        { i. rewrite NatMapP.F.add_o in FINDA.
          rewrite NatMapP.F.add_o in FINDR. des_ifs.
          eapply FORALL; auto.
        }
      Qed.

      Lemma whole_sim_implies_usersim
            (SIM: whole_sim)
        :
        UserSim.sim md_src md_tgt (prog2ths md_src c) (prog2ths md_tgt c).
      Proof.
        inv SIM.
        apply (@UserSim.mk
                 md_src md_tgt (prog2ths md_src c) (prog2ths md_tgt c) owf nat_wf (inhabits 0) NUNBOUND (to_LURA Σ)
                 (liftI (fun ths im_src im_tgt st_src st_tgt => @default_I md_src.(Mod.state) md_tgt.(Mod.state) md_src.(Mod.ident) md_tgt.(Mod.ident) Σ _ _ _ _ _ _ _ _ _ ths im_src im_tgt st_src st_tgt ** mset_all (nth_default True%I I_whole0) (topset I_whole0)%I))).
        i.
        assert (exists (r: Σ),
                   (<<SAT: (∃ im_src, ((mset_all (nth_default True%I I_whole0) (topset I_whole0) **
                                                 natmap_prop_sum fun_pairs
                                                 (λ (tid : nat) '(th_src, th_tgt),
                                                   stsim I_whole0 tid (topset I_whole0) ibot7 ibot7
                                                         (λ r_src r_tgt : Any.t,
                                                             (own_thread tid ** ObligationRA.duty (inl tid) []) **                                                                                                    ⌜r_src = r_tgt⌝) false false th_src th_tgt))
                                         **
                                         (default_I (key_set (prog2ths md_src c)) im_src im_tgt
                                                    (Mod.st_init md_src) (Mod.st_init md_tgt))))%I
                                                                                                r>>) /\
                     (<<WF: URA.wf r>>)).
        { eapply iProp_satisfable.
          { eapply RESWF. }
          iIntros "[H0 H1]".
          iPoseProof (default_initial_res_init with "H1") as "H1".
          iPoseProof ("H1" $! _ _ _ _ _) as "> [% [[[[[[A B] C] D] E] F] G]]".
          iPoseProof (init_whole0 with "[H0 B C D E F G]") as "> H".
          { iFrame. }
          iModIntro. iExists _. iSplitL "H"; [auto|].
          rewrite THSEQ. eauto.
        }
        des. rr in SAT. unseal "iProp". des.
        rr in SAT. unseal "iProp". des. subst.
        rr in SAT0. unseal "iProp". des. subst.
        hexploit natmap_prop_sum_resmap.
        { eauto. }
        { eapply URA.wf_mon. instantiate (1:=a0 ⋅ b). r_wf WF. }
        i. des. eexists _, rm, _. splits.
        { ss. rr. unseal "iProp". esplits; [|eauto|eauto]. eauto. }
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
              rewrite NatMapP.F.add_o in FIND1. rewrite NatMapP.F.add_o in FIND2.
              rewrite NatMapP.F.add_o. des_ifs.
              eapply IHl; eauto.
            }
          }
          { auto. }
          i. ii. eapply stsim_local_sim_init; eauto.
        }
        { cut (URA.wf ((b ⋅ a0) ⋅ (NatMap.fold (fun _ r s => r ⋅ s) rm URA.unit))).
          { i. rewrite LPCM.URA.unfold_wf. s.
            rewrite LPCM.URA.unfold_add. s.
            change (@LPCM.URA.unit (to_LURA (GRA.to_URA Σ))) with (@URA.unit Σ).
            rewrite URA.unfold_wf in H.
            rewrite URA.unfold_add in H.
            rewrite URA.unfold_add. auto.
          }
          eapply URA.wf_extends; [|apply WF].
          rr in EXT. des. exists ctx. rewrite <- EXT. r_solve.
        }
      Qed.

      Lemma whole_sim_implies_refinement
            (SIM: whole_sim)
        :
        Adequacy.improves (interp_all md_src.(Mod.st_init) (prog2ths md_src c) 0)
                          (interp_all md_tgt.(Mod.st_init) (prog2ths md_tgt c) 0).
      Proof.
        eapply usersim_adequacy. eapply whole_sim_implies_usersim. auto.
      Qed.
    End WHOLE_PROGRAM_SIM.


    Section CONTEXT_SIM.

      (* TODO: Change Ord.omega to user defined values *)
      Record context_sim: Prop :=
        mk_context_sim {
            I_ctx: list iProp;
            init_ctx:
            ((initial_prop TIdSet.empty Ord.omega) (* INIT *)
               -∗
               (#=> (mset_all (nth_default True%I I_ctx) (topset I_ctx))));
            funs_ctx:
            forall fn args,
              match md_src.(Mod.funs) fn, md_tgt.(Mod.funs) fn with
              | Some ktr_src, Some ktr_tgt =>
                  forall tid,
                    (own_thread tid)
                      -∗
                      (ObligationRA.duty (inl tid) [])
                      -∗
                      (stsim
                         I_ctx tid (topset I_ctx)
                         ibot7 ibot7
                         (fun r_src r_tgt => own_thread tid ** ObligationRA.duty (inl tid) [] ** ⌜r_src = r_tgt⌝)
                         false false (ktr_src args) (ktr_tgt args))
              | None, None => True
              | _, _ => False
              end;
          }.

      Lemma context_sim_implies_modsim
            (SIM: context_sim)
        :
        ModSim.mod_sim md_src md_tgt.
      Proof.
        inv SIM.
        apply (@ModSim.mk
                 md_src md_tgt owf nat_wf (inhabits 0) NUNBOUND (to_LURA Σ)
                 (liftI (fun ths im_src im_tgt st_src st_tgt => @default_I md_src.(Mod.state) md_tgt.(Mod.state) md_src.(Mod.ident) md_tgt.(Mod.ident) Σ _ _ _ _ _ _ _ _ _ ths im_src im_tgt st_src st_tgt ** mset_all (nth_default True%I I_ctx0) (topset I_ctx0)%I))).
        { i. assert (exists (r: Σ),
                        (<<SAT: (∃ im_src, ((mset_all (nth_default True%I I_ctx0) (topset I_ctx0) ** (default_I NatSet.empty im_src im_tgt (Mod.st_init md_src) (Mod.st_init md_tgt)))))%I r>>) /\
                          (<<WF: URA.wf r>>)).
          { eapply iProp_satisfable.
            { eapply RESWF. }
            iIntros "[H0 H1]".
            iPoseProof (default_initial_res_init with "H1") as "H1".
            iPoseProof ("H1" $! _ _ _ _ _) as "> [% [[[[[[A B] C] D] E] F] G]]".
            iPoseProof (init_ctx0 with "[H0 B C D E F G]") as "> H".
            { iFrame. }
            iModIntro. iExists _. iSplitL "H"; [auto|].
            eauto.
          }
          des. rr in SAT. unseal "iProp". des.
          rr in SAT. unseal "iProp". des. subst.
          eexists _, _. splits.
          { ss. rr. unseal "iProp". esplits; [|eauto|eauto]. eauto. }
          { rewrite LPCM.URA.unfold_wf. rewrite URA.add_comm. rewrite URA.unfold_wf in WF. auto. }
        }
        { i. specialize (funs_ctx0 fn args). des_ifs.
          eapply stsim_local_sim; eauto.
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
    End CONTEXT_SIM.
  End WSIM.
End WSim.
