From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Program.
Require Import Arith.
Require Import Permutation.
Require Import Lists.List.
Require Import Lia.
From Fairness Require Import
  Mod
  FairSim
  Concurrency
  FIFOSched.
From ExtLib Require Import FMapAList.

Tactic Notation "repl" constr(e) "with" constr(e') "at" ne_integer_list(n) :=
  let x := fresh in
  set e as x at n;
  replace x with e';
  subst x.

Tactic Notation "repl" constr(e) "with" constr(e') "at" ne_integer_list(n) "by" tactic(tac) :=
  let x := fresh in
  set e as x at n;
  replace x with e' by tac;
  subst x.

Ltac destruct_itree itr :=
  let E := fresh "E" in
  destruct (observe itr) eqn: E;
  let H := fresh "H" in
  pose proof (H := itree_eta_ itr);
  rewrite E in H;
  clear E;
  subst itr.

Section SIM.

  Context {_Ident : ID}.
  Variable E : Type -> Type.

  Let eventE1 := @eventE _Ident.
  Let eventE2 := @eventE (sum_tid _Ident).

  Variable wf : WF.
  Variable State : Type.
  Variable R : Type.

  Print thread_id.
  Print Th.
  Require Import Sorted.
  Check Sorted.
  Print Th.add.
  Print Th.Raw.add.
  
  Let thread R := thread _Ident (sE State) R.
  Import Th.

  Lemma In_MapsTo A k e (m : Th.t A) : List.In (k, e) (elements m) -> MapsTo k e m.
  Admitted.
  
  Lemma In_th_proj1 A k (m : Th.t A) : List.In k (th_proj1 m) -> exists e, MapsTo k e m.
  Admitted.

  Lemma Permutation_remove A k e (m : Th.t A) l : Permutation (elements m) ((k, e) :: l) -> Permutation (elements (remove k m)) l.
  Admitted.

  Lemma setoid_in_in A k (e : A) l : SetoidList.InA (@eq_key_elt A) (k, e) l -> List.In (k, e) l.
  Admitted.

  Lemma Permutation_NoDupA A l1 l2 : Permutation l1 l2 -> SetoidList.NoDupA (eq_key (elt:=A)) l1 -> SetoidList.NoDupA (eq_key (elt:=A)) l2.
  Admitted.
  
  Theorem sched_sim
    p_src p_tgt
    st ths_src ths_tgt tid (itr : thread R)
    (THREADS : Permutation (elements ths_src) ths_tgt)
    (TID : forall itr0, ~ List.In (tid, itr0) ths_tgt)
    : gsim nat_wf nat_wf eq p_src p_tgt (interp_all st ths_src tid itr) (interp_all_fifo st ths_tgt tid itr).
  Proof.
    unfold interp_all, interp_all_fifo, gsim. intro m_tgt.

    remember (fun (i : (sum_tid _Ident).(id)) =>
                match i with
                | inl x => List.length ths_tgt
                | inr x => m_tgt (inr x)
                end) as m_src.
    assert (M_SRC0 : m_src (inl tid) > List.length ths_tgt) by admit.
    assert (M_SRC1 : forall i tid t, nth_error ths_tgt i = Some (tid, t) -> m_src (inl tid) > i) by admit.
    assert (M_SRC2 : (forall i, m_src (inr i) = m_tgt (inr i))) by admit.
    clear Heqm_src.
    exists m_src.

    revert p_src p_tgt st ths_src ths_tgt tid itr m_tgt m_src THREADS TID M_SRC0 M_SRC1 M_SRC2.
    pcofix CIH1.
    intros.
    
    rewrite unfold_interp_sched.
    rewrite unfold_interp_fifosched.
    revert st p_src p_tgt m_src m_tgt itr M_SRC0 M_SRC1 M_SRC2.
    pcofix CIH2.
    intros.

    destruct_itree itr.
    - (* Ret case *)
      clear CIH2.
      rewrite interp_thread_ret.
      rewrite 2 bind_ret_l.
      rewrite pick_thread_nondet_terminate.
      rewrite pick_thread_fifo_terminate.
      destruct ths_tgt.
      + (* ths is empty *)
        replace (is_empty ths_src) with true.
        2: { unfold is_empty, Raw.is_empty.
             symmetry in THREADS.
             eapply Permutation_nil in THREADS.
             unfold elements, Raw.elements in THREADS.
             rewrite THREADS.
             ss.
        }
        rewrite 2 bind_ret_l.
        rewrite interp_state_ret.
        pfold; econs; eauto.
      + replace (is_empty ths_src) with false.
        2: { unfold is_empty, Raw.is_empty.
             unfold elements, Raw.elements in THREADS.
             destruct (this ths_src); eauto.
             exfalso.
             eapply Permutation_nil_cons; eauto.
        }
        destruct p as [tid' itr'].
        rewrite bind_vis.
        rewrite interp_state_vis.
        rewrite bind_ret_l.
        rewrite <- bind_trigger.
        pfold.
        eapply sim_chooseL.
        exists tid'.
        econs.
        unfold th_pop.
        erewrite find_1.
        2: {
          eapply In_MapsTo.
          eapply Permutation_in.
          - symmetry.
            eapply THREADS.
          - econs. reflexivity.
        }
        rewrite bind_vis.
        rewrite interp_state_vis.
        rewrite <- bind_trigger.
        rewrite bind_ret_l.
        rewrite 2 interp_state_tau.
        eapply sim_fairL.
        exists (fun i => match i with
                 | inl x => if Nat.eqb x tid'
                           then List.length ths_tgt + 1
                           else m_src (inl x) - 1
                 | inr x => m_src (inr x)
                 end).
        splits. {
          unfold fair_update. i.
          destruct i as [tid''|]; ss.
          - unfold tids_fmap.
            des_if; eauto.
            replace (tid'' =? tid')%nat with false
              by (symmetry; eapply Nat.eqb_neq; eauto).
            des_if.
            + eapply In_th_proj1 in i.
              destruct i.
              eapply remove_3 in H.
              eapply elements_1 in H.
              unfold elements, Raw.elements in H.
              eapply setoid_in_in in H.
              eapply Permutation_in in H.
              2: eapply THREADS.
              eapply In_nth_error in H.
              destruct H as [i H].
              enough (m_src (inl tid'') > i) by lia.
              eapply M_SRC1.
              eauto.
            + unfold le, lt. ss. lia.
          - left. eauto.
        }
        do 4 econs; eauto.
        right.
        eapply CIH1.
        * eapply Permutation_remove. eauto.
        * intros itr0 H.
          pose proof (elements_3w ths_src).
          eapply (Permutation_NoDupA _ _ _ THREADS) in H0.
          inversion H0; subst.
          eapply H3.
          eapply SetoidList.InA_eqA; [eauto| |].
          instantiate (1 := (tid', itr0)); ss.
          eapply SetoidList.In_InA; [eauto|].
          assumption.
        * rewrite Nat.eqb_refl. lia.
        * i.
          (* tid0 can not be equal to tid', but it's easy to show [length ths_tgt + 1 > i] *)
          des_if.
          -- assert (List.length ths_tgt > i \/ List.length ths_tgt <= i) by lia.
             destruct H0; [| eapply nth_error_None in H0; rewrite H in H0; ss].
             lia.
          -- match goal with
             | [ |- ?x - 1 > i ] => enough (x > 1 + i) by lia
             end.
             eapply M_SRC1.
             eauto.
        * eauto.
    - (* Tau case *)
      rewrite interp_thread_tau.
      rewrite 2 bind_tau.
      rewrite 2 interp_state_tau.
      pfold; do 3 econs; eauto.
    - (* Vis case *)
      destruct e as [[|]|].
      + (* eventE *)
        rewrite interp_thread_vis_eventE.
        rewrite 2 bind_vis.
        rewrite 2 interp_state_vis.
        rewrite <- 2 bind_trigger.
        destruct e.
        * pfold.
          eapply sim_chooseR. intros.
          eapply sim_chooseL. exists x.
          rewrite 2 bind_tau.
          rewrite 2 interp_state_tau.
          do 5 econs; eauto.
        * pfold.
          eapply sim_fairR. intros.
          eapply sim_fairL.
          exists (fun i => match i with
                   | inl x => m_src (inl x)
                   | inr x => m_tgt0 (inr x)
                   end).
          splits. {
            unfold fair_update. i.
            destruct i; ss.
            - left. eauto.
            - rewrite M_SRC2.
              unfold fair_update in FAIR.
              specialize FAIR with (inr i).
              ss.
          }
          econs. econs.
          rewrite 2 bind_tau.
          rewrite 2 interp_state_tau.
          do 3 econs; eauto.
        * rewrite 2 bind_trigger.
          simpl embed_eventE.
          pfold. econs. intros. subst. left.
          rewrite 2 bind_tau.
          rewrite 2 interp_state_tau.
          pfold; do 5 econs; eauto.
        * pfold; eapply sim_ub.
      + (* cE *)
        destruct c.
        * (* Yield *)
          rewrite interp_thread_vis_yield.
          rewrite 2 bind_ret_l.
          rewrite pick_thread_nondet_yield.
          rewrite pick_thread_fifo_yield.
          rewrite bind_vis.
          rewrite interp_state_vis.
          rewrite <- bind_trigger.
          match goal with
          | [ |- paco9 _ _ _ _ _ _ _ _ _ _ (interp_state (_, _ <- match ?x with
                                                                | [] => _
                                                                | t' :: ts' => _
                                                                end;;
                                                            _))] => destruct x as [|[tid' itr'] ths_tgt'] eqn: E_ths_tgt
          end.
          { eapply app_eq_nil in E_ths_tgt.
            destruct E_ths_tgt.
            discriminate.
          }
          rewrite bind_ret_l.
          rewrite interp_state_tau.
          pfold. econs. eapply sim_chooseL. exists tid'. econs.
          unfold th_pop.
          replace (find tid' (add tid (k ()) ths_src)) with (Some itr').
          2: {
            symmetry. eapply find_1.
            destruct ths_tgt.
            - ss. inversion E_ths_tgt; subst.
              eapply add_1; eauto.
            - destruct p.
              inversion E_ths_tgt; subst.
              assert (tid' <> tid).
              { pose proof (TID itr').
                intro H1. eapply H. left. subst. ss.
              }
              eapply add_2; eauto.
              eapply In_MapsTo.
              rewrite THREADS.
              left. ss.
          }
          rewrite bind_vis.
          rewrite interp_state_vis.
          rewrite <- bind_trigger.
          eapply sim_fairL.
          exists (fun i => match i with
                   | inl x => if Nat.eqb x tid'
                             then List.length ths_tgt'
                             else m_src (inl x) - 1
                   | inr x => m_src (inr x)
                   end).
          splits.
          { unfold fair_update. i. destruct i; ss.
            - unfold tids_fmap.
              des_if; eauto.
              replace (Nat.eqb i tid') with false
                by (symmetry; eapply Nat.eqb_neq; eauto).
              des_if.
              +
                eapply In_th_proj1 in i0.
                destruct i0.
                eapply remove_3 in H.
                assert (i = tid \/ i <> tid) by lia.
                destruct H0.
                * subst i. unfold key in *. lia.
                * eapply add_3 in H; eauto.
                  eapply elements_1 in H.
                  unfold elements, Raw.elements in H.
                  eapply setoid_in_in in H.
                  eapply Permutation_in in H.
                  2: eapply THREADS.
                  eapply In_nth_error in H.
                  destruct H as [j H].
                  enough (m_src (inl i) > j) by lia.
                  eapply M_SRC1.
                  eauto.
              + unfold le. ss. lia.
            - left. ss.
          }
          rewrite bind_ret_l.
          rewrite interp_state_tau.
          do 3 econs; eauto. right. eapply CIH1.
          -- admit.
          -- admit.
          -- admit.
          -- admit.
          -- ss.
        * rewrite interp_thread_vis_gettid.
          rewrite 2 bind_tau.
          rewrite 2 interp_state_tau.
          pfold; do 3 econs; eauto.
      + (* sE *)
        rewrite interp_thread_vis.
        rewrite 2 bind_vis.
        destruct s.
        * rewrite 2 interp_state_put_vis.
          rewrite 2 bind_tau.
          rewrite 2 interp_state_tau.
          pfold; do 5 econs; eauto.
        * rewrite 2 interp_state_get_vis.
          rewrite 2 bind_tau.
          rewrite 2 interp_state_tau.
          pfold; do 5 econs; eauto.
  Admitted.

End SIM.
