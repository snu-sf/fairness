From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Program.
Require Import Arith.
Require Import Permutation.
Require Import SetoidList.
Require Import SetoidPermutation.
Require Import Lists.List.
Require Import Lia.
From Fairness Require Import
  Mod
  FairSim
  Concurrency
  FIFOSched
  SchedSim.
From ExtLib Require Import FMapAList.

Section SIM.

  Context {_Ident : ID}.
  Variable E : Type -> Type.

  Let eventE1 := @eventE _Ident.
  Let eventE2 := @eventE (sum_tid _Ident).

  Variable wf : WF.
  Variable State : Type.
  Variable R : Type.

  Let thread R := thread _Ident (sE State) R.
  Import Th.

  Theorem ssim_nondet_fifo
    p_src p_tgt tid ths_src ths_tgt
    (THREADS : Permutation (TIdSet.elements ths_src) ths_tgt)
    (TID : ~ NatMap.In tid ths_src)
    : forall m_tgt, exists m_src, @ssim nat_wf nat_wf R R R eq p_src m_src p_tgt m_tgt
                          (sched_nondet R (tid, ths_src))
                          (sched_fifo R (tid, ths_tgt)).
  Proof.
    i.

    remember (fun (i : thread_id) => List.length ths_tgt + 1) as m_src.
    assert (M_SRC0 : m_src tid > List.length ths_tgt) by (subst; lia).
    assert (M_SRC1 : forall i tid, nth_error ths_tgt i = Some tid -> m_src tid > i).
    { subst. i. eapply nth_error_Some' in H. lia. }
    clear Heqm_src.
    exists m_src.

    revert p_src p_tgt m_src m_tgt tid ths_src ths_tgt THREADS TID M_SRC0 M_SRC1.
    pcofix CIH. i.

    rewrite unfold_sched_nondet.
    rewrite unfold_sched_fifo.
    rewrite ! bind_trigger.
    pfold. econs. intros [].
    - left.
      destruct (NatMap.is_empty ths_src) eqn: H.
      + eapply NatMap.is_empty_2 in H.
        eapply Empty_nil in H.
        rewrite H in THREADS.
        eapply Permutation_nil in THREADS.
        subst ths_tgt.
        pfold. econs; ss.
      + assert (~ TIdSet.Empty ths_src).
        { ii. eapply NatMap.is_empty_1 in H0. rewrite H in H0; ss. }
        clear H. eapply Empty_nil_neg in H0.
        destruct ths_tgt as [| tid' ths_tgt' ].
        { symmetry in THREADS. eapply Permutation_nil in THREADS. ss. }
        pfold. eapply ssim_chooseL. exists tid'. unfold nm_pop.
        replace (NatMap.find tid' ths_src) with (Some tt); cycle 1.
        { symmetry. eapply find_1. eapply NatSet_In_MapsTo. eapply In_NatSetIn.
          rewrite THREADS. econs; ss.
        }
        rewrite bind_trigger.
        eapply ssim_fairL.
        remember (fun i => if Nat.eq_dec i tid'
                        then List.length ths_tgt' + 1
                        else if NatMapP.F.In_dec (NatMap.remove tid' ths_src) i
                             then m_src i - 1
                             else m_src i) as m_src'.
        exists m_src'. splits.
        { ii. unfold tids_fmap; ss. des_ifs.
          assert (List.In i (TIdSet.elements ths_src)).
          { eapply NatSetIn_In. eapply NatMapP.F.remove_neq_in_iff with (x := tid'). eauto. ss. }
          rewrite THREADS in H. eapply In_nth_error in H. destruct H as [i' H].
          enough (m_src i > i') by lia. eapply M_SRC1; eauto.
        }
        do 3 econs; eauto. right. eapply CIH.
        * eapply NatSet_Permutation_remove. eapply THREADS.
        * eapply NatMap.remove_1; ss.
        * subst. des_if; ss. lia.
        * subst. i. des_if.
          -- eapply nth_error_Some' in H. lia.
          -- enough (m_src tid0 > 1 + i) by (des_if; lia). eapply M_SRC1. eauto.
    - left.
      match goal with
      | [ |- paco10 _ _ _ _ _ _ _ _ _ _ _ (match ?x with
                                          | [] => _
                                          | t' :: ts' => _
                                          end)] => destruct x as [| tid' ths_tgt'] eqn: E_ths_tgt
      end.
      { eapply app_eq_nil in E_ths_tgt. des. ss. }
      pfold. eapply ssim_chooseL. exists tid'. unfold nm_pop.
      replace (NatMap.find tid' (TIdSet.add tid ths_src)) with (Some tt); cycle 1.
      { symmetry. eapply find_1.
        destruct ths_tgt; ss; inversion E_ths_tgt; subst.
        - eapply NatMap.add_1; ss.
        - eapply NatMap.add_2.
          + intro. subst. eapply TID. eapply In_NatSetIn. rewrite THREADS. econs; ss.
          + eapply NatSet_In_MapsTo. eapply In_NatSetIn. rewrite THREADS. econs; ss.
      }
      rewrite bind_trigger. eapply ssim_fairL.
      remember (fun i => if Nat.eq_dec i tid'
                      then List.length ths_tgt' + 1
                      else if NatMapP.F.In_dec (NatMap.remove tid' (NatSet.add tid ths_src)) i
                           then m_src i - 1
                           else m_src i) as m_src'.
      exists m_src'. splits.
      { ii. unfold tids_fmap; ss. des_ifs.
        assert (i = tid \/ i <> tid) by lia. destruct H; try (subst; lia).
        assert (List.In i (TIdSet.elements ths_src)).
        { eapply NatSetIn_In. exists tt. eapply NatSet_In_MapsTo, NatMap.remove_3, NatMap.add_3 in i0; eauto. }
        rewrite THREADS in H0. eapply In_nth_error in H0. destruct H0 as [i' H0].
        enough (m_src i > i') by lia. eapply M_SRC1; eauto.
      }
      do 3 econs; ss. right. unfold NatMap.key in *. eapply CIH.
      + eapply NatSet_Permutation_remove.
        rewrite NatSet_Permutation_add.
        * eapply Permutation_refl' in E_ths_tgt. rewrite Permutation_app_comm in E_ths_tgt. eapply E_ths_tgt.
        * intro H. eapply TID. eapply H.
        * ss.
      + eapply NatMap.remove_1; ss.
      + subst. des_if; ss. lia.
      + subst. i. des_if.
        * eapply nth_error_Some' in H. lia.
        * enough (m_src tid0 > 1 + i) by (des_if; lia).
          assert (nth_error (ths_tgt ++ [tid]) (1 + i) = Some tid0) by (rewrite E_ths_tgt; ss).
          assert (1 + i < List.length ths_tgt \/ 1 + i >= List.length ths_tgt) by lia.
          destruct H1.
          -- rewrite nth_error_app1 in H0 by ss. eapply M_SRC1; eauto.
          -- rewrite nth_error_app2 in H0 by ss.
             assert (1 + i - List.length ths_tgt = 0)
               by (destruct (1 + i - List.length ths_tgt) as [|[]] in *; ss).
             rewrite H2 in H0. inversion H0. subst. lia.
  Qed.

  Theorem gsim_nondet_fifo tid st (ths : @threads _Ident (sE State) R)
    : gsim nat_wf nat_wf eq
           (interp_all st ths tid)
           (interp_all_fifo st ths tid).
  Proof. 
    eapply ssim_implies_gsim.
    { instantiate (1 := fun x => x). ss. }
    eapply ssim_nondet_fifo; ss.
    eapply NatMap.remove_1; ss.
    Unshelve. all: exact true.
  Qed.

End SIM.
