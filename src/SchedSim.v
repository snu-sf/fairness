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
  symmetry in E;
  apply simpobs in E;
  apply bisim_is_eq in E;
  subst itr.

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

  Lemma Empty_nil s : IdSet.Empty s -> IdSet.elements s = [].
  Proof.
    i. destruct s as [s OK]; ss. destruct s; ss.
    exfalso. eapply H. econs. ss.
  Qed.

  Lemma Empty_nil_neg s : ~ IdSet.Empty s -> IdSet.elements s <> [].
  Proof.
    destruct s as [s SORTED]; ss.
    ii. subst. eapply H. ii. eapply InA_nil; eauto.
  Qed.

  Lemma In_MapsTo A k e (m : Th.t A) : List.In (k, e) (elements m) -> MapsTo k e m.
  Proof.
    unfold MapsTo, Raw.PX.MapsTo, elements, Raw.elements.
    remember (this m) as l. clear m Heql. intros.
    induction l; ss. destruct H.
    - eapply InA_cons_hd. subst. ss.
    - eapply InA_cons_tl. eauto.
  Qed.

  Lemma In_th_proj1 A k (m : Th.t A) : List.In k (th_proj1 m) -> exists e, MapsTo k e m.
  Proof.
    unfold th_proj1, MapsTo, Raw.PX.MapsTo, elements, Raw.elements.
    remember (this m) as l. clear m Heql. intros.
    induction l; ss. destruct H.
    - eexists. eapply InA_cons_hd. subst. ss.
    - eapply IHl in H. destruct H. eexists. eapply InA_cons_tl. eauto.
  Qed.

  Lemma IdSet_Permutation_remove x s l :
    Permutation (IdSet.elements s) (x :: l) -> Permutation (IdSet.elements (IdSet.remove x s)) l.
  Proof.
    destruct s as [s SORTED]. ss.
    revert l. induction s; i.
    - eapply Permutation_length in H. ss.
    - assert (List.In a (x :: l)) by (rewrite <- H; econs; ss).
      destruct H0.
      + subst. eapply Permutation_cons_inv in H. ss.
        Raw.MX.elim_comp_eq a a. ss.
      + eapply Add_inv in H0. des. eapply Permutation_Add in H0.
        rewrite <- H0 in *. clear l H0.
        rewrite perm_swap in H. eapply Permutation_cons_inv in H.
        assert (List.In x s).
        { eapply Permutation_in.
          - symmetry. eapply H.
          - econs; ss.
        }
        eapply IdSet.MSet.Raw.isok_iff in SORTED.
        epose proof (Sorted_extends _ SORTED).
        eapply Forall_forall in H1; eauto.
        ss. Raw.MX.elim_comp_gt x a.
        econs. eapply IHs; eauto.
        eapply IdSet.MSet.Raw.isok_iff.
        inv SORTED; ss.
    Unshelve. compute. lia.
  Qed.

  Lemma IdSet_Permutation_add x s l :
    ~ IdSet.In x s -> Permutation (IdSet.elements s) l -> Permutation (IdSet.elements (IdSet.add x s)) (x :: l).
  Proof.
    destruct s as [s SORTED]. ss. revert l. induction s; intros l H1 H2.
    - rewrite <- H2. ss.
    - ss. assert (x = a \/ x < a \/ x > a) by lia. des.
      + exfalso. eapply H1. econs. ss.
      + Raw.MX.elim_comp_lt x a. econs. ss.
      + Raw.MX.elim_comp_gt x a. rewrite <- H2. rewrite perm_swap. econs.
        eapply IHs; eauto.
        unfold IdSet.In, IdSet.MSet.In in *. ss.
        intro. eapply H1. econs 2. eapply H0.
        Unshelve. clear H1. eapply IdSet.MSet.Raw.isok_iff in SORTED. inv SORTED.
        eapply IdSet.MSet.Raw.isok_iff. ss.
  Qed.

  Lemma Permutation_remove A k e (m : Th.t A) l :
    Permutation (elements m) ((k, e) :: l) -> Permutation (elements (remove k m)) l.
  Proof.
    unfold elements, Raw.elements, remove.
    destruct m as [m SORTED]. ss.
    revert l. induction m; i.
    - eapply Permutation_length in H. ss.
    - assert (List.In a ((k, e) :: l)) by (rewrite <- H; econs; ss).
      destruct H0.
      + inv H0. eapply Permutation_cons_inv in H. ss.
        Raw.MX.elim_comp_eq k k. eauto.
    + eapply Add_inv in H0. destruct H0. eapply Permutation_Add in H0.
      rewrite <- H0 in *. clear l H0.
      rewrite perm_swap in H. eapply Permutation_cons_inv in H.
      assert (List.In (k, e) m).
      { eapply Permutation_in.
        - symmetry; eauto.
        - econs; ss.
      }
      epose proof (Sorted_extends _ SORTED).
      eapply Forall_forall in H1; eauto.
      destruct a. ss. Raw.MX.elim_comp_gt k n.
      inv SORTED.
      econs. eapply IHm; eauto.
    Unshelve. compute. lia.
  Qed.

  Lemma Permutation_add A k e (m : Th.t A) l :
    ~ In k m -> Permutation (elements m) l -> Permutation (elements (add k e m)) ((k, e) :: l).
  Proof.
    unfold elements, Raw.elements, add, In.
    destruct m as [m SORTED]. ss. revert l. induction m; intros l H1 H2.
    - rewrite <- H2. ss.
    - destruct a. ss.
      assert (k = n \/ k < n \/ k > n) by lia.
      destruct H as [|[]].
      + exfalso. eapply H1. exists a. left. ss.
      + Raw.MX.elim_comp_lt k n. econs; eauto.
      + Raw.MX.elim_comp_gt k n.
        rewrite <- H2. rewrite perm_swap. econs.
        inv SORTED. eapply IHm; eauto.
        intro. eapply H1. unfold Raw.PX.In in *.
        destruct H0. eexists. right. eauto.
  Qed.

  Lemma InA_In A x (l : list A) : InA (@eq A) x l -> List.In x l.
  Proof. i. induction H.
         - left; eauto.
         - right; eauto.
  Qed.
    
  Lemma setoid_in_in A k (e : A) l :
    SetoidList.InA (@eq_key_elt A) (k, e) l -> List.In (k, e) l.
  Proof.
    i. induction H.
    - left. destruct H; ss. subst. destruct y; ss.
    - right. eauto.
  Qed.

  Lemma Permutation_NoDupA A l1 l2 :
    Permutation l1 l2 ->
    SetoidList.NoDupA (eq_key (elt:=A)) l1 ->
    SetoidList.NoDupA (eq_key (elt:=A)) l2.
  Proof.
    i.
    eapply PermutationA_preserves_NoDupA; eauto.
    eapply Permutation_PermutationA; eauto.
  Qed.

  Lemma nth_error_Some' A (l : list A) x i : nth_error l i = Some x -> i < List.length l.
  Proof. i. eapply nth_error_Some. intro. rewrite H in H0; ss. Qed.

  Theorem ssim_nondet_fifo
    p_src p_tgt tid ths_src ths_tgt
    (THREADS : Permutation (IdSet.elements ths_src) ths_tgt)
    (TID : ~ IdSet.In tid ths_src)
    : forall m_tgt, exists m_src, @ssim nat_wf nat_wf R R R eq p_src m_src p_tgt m_tgt
                          (schedule_nondet R (tid, ths_src))
                          (schedule_fifo R (tid, ths_tgt)).
  Proof.
    i.

    remember (fun (i : thread_id.(id)) => List.length ths_tgt + 1) as m_src.
    assert (M_SRC0 : m_src tid > List.length ths_tgt) by (subst; lia).
    assert (M_SRC1 : forall i tid, nth_error ths_tgt i = Some tid -> m_src tid > i).
    { subst. i. eapply nth_error_Some' in H. lia. }
    clear Heqm_src.
    exists m_src.

    revert p_src p_tgt m_src m_tgt tid ths_src ths_tgt THREADS TID M_SRC0 M_SRC1.
    pcofix CIH. i.

    rewrite unfold_schedule_nondet.
    rewrite unfold_schedule_fifo.
    rewrite ! bind_trigger.
    pfold. econs. intros [].
    - left.
      destruct (IdSet.is_empty ths_src) eqn: H.
      + eapply IdSet.is_empty_2 in H.
        eapply Empty_nil in H.
        rewrite H in THREADS.
        eapply Permutation_nil in THREADS.
        subst ths_tgt.
        pfold. econs; ss.
      + assert (~ IdSet.Empty ths_src).
        { ii. eapply IdSet.is_empty_1 in H0. rewrite H in H0; ss. }
        clear H. eapply Empty_nil_neg in H0.
        destruct ths_tgt as [| tid' ths_tgt' ].
        { symmetry in THREADS. eapply Permutation_nil in THREADS. ss. }
        pfold. eapply ssim_chooseL. exists tid'. unfold id_pop.
        replace (IdSet.mem tid' ths_src) with true; cycle 1.
        { symmetry. eapply IdSet.mem_1. eapply In_InA; eauto.
          rewrite THREADS. econs; ss.
        }
        rewrite bind_trigger.
        eapply ssim_fairL.
        remember (fun i => if Nat.eqb i tid'
                        then List.length ths_tgt' + 1
                        else m_src i - 1) as m_src'.
        exists m_src'. splits.
        { ii. unfold tids_fmap. des_if; ss. subst.
          replace (i =? tid')%nat with false by (symmetry; eapply Nat.eqb_neq; eauto).
          des_if.
          - assert (List.In i (IdSet.elements ths_src)).
            { eapply InA_In. eapply IdSet.remove_3. eapply In_InA; eauto. eapply i0. }
            rewrite THREADS in H.
            eapply In_nth_error in H. destruct H as [i' H].
            enough (m_src i > i') by lia.
            eapply M_SRC1; eauto.
          - unfold le; ss. lia.
        }
        do 3 econs; eauto. right. eapply CIH.
        * eapply IdSet_Permutation_remove. eapply THREADS.
        * eapply IdSet.remove_1; ss.
        * subst. replace (tid' =? tid')%nat with true by (symmetry; eapply Nat.eqb_refl). lia.
        * subst. i. des_if.
          -- eapply nth_error_Some' in H. lia.
          -- enough (m_src tid0 > 1 + i) by lia. eapply M_SRC1. eauto.
    - left.
      match goal with
      | [ |- paco10 _ _ _ _ _ _ _ _ _ _ _ (match ?x with
                                          | [] => _
                                          | t' :: ts' => _
                                          end)] => destruct x as [| tid' ths_tgt'] eqn: E_ths_tgt
      end.
      { eapply app_eq_nil in E_ths_tgt. des. ss. }
      pfold. eapply ssim_chooseL. exists tid'. unfold id_pop.
      replace (IdSet.mem tid' (IdSet.add tid ths_src)) with true; cycle 1.
      { symmetry. eapply IdSet.mem_1.
        destruct ths_tgt; ss; inversion E_ths_tgt; subst.
        - eapply IdSet.add_1; ss.
        - eapply IdSet.add_2. eapply In_InA; eauto. rewrite THREADS. econs; ss.
      }
      rewrite bind_trigger. eapply ssim_fairL.
      remember (fun i => if Nat.eqb i tid'
                      then List.length ths_tgt' + 1
                      else m_src i - 1) as m_src'.
      exists m_src'. splits.
      { ii. unfold tids_fmap. des_if; ss. subst.
        replace (i =? tid')%nat with false by (symmetry; eapply Nat.eqb_neq; eauto).
        des_if.
        - assert (List.In i (IdSet.elements (IdSet.add tid ths_src))).
          { eapply InA_In. eapply IdSet.remove_3. eapply In_InA; eauto. eapply i0. }
          assert (i = tid \/ i <> tid) by lia.
          destruct H0.
          + subst. lia.
          + assert (List.In i (IdSet.elements ths_src)).
            { eapply InA_In. eapply IdSet.add_3; eauto. eapply In_InA; eauto. }
            rewrite THREADS in H1. eapply In_nth_error in H1. destruct H1 as [i' H1].
            enough (m_src i > i') by lia.
            eapply M_SRC1; eauto.
        - unfold le; ss. lia.
      }
      do 3 econs; ss. right. unfold IdSet.elt in *. eapply CIH.
      + eapply IdSet_Permutation_remove.
        rewrite IdSet_Permutation_add.
        * eapply Permutation_refl' in E_ths_tgt. rewrite Permutation_app_comm in E_ths_tgt. eapply E_ths_tgt.
        * intro H. eapply TID. eapply H.
        * ss.
      + eapply IdSet.remove_1; ss.
      + subst. replace (tid' =? tid')%nat with true by (symmetry; eapply Nat.eqb_refl). lia.
      + subst. i. des_if.
        * eapply nth_error_Some' in H. lia.
        * enough (m_src tid0 > 1 + i) by lia.
          assert (nth_error (ths_tgt ++ [tid]) (1 + i) = Some tid0) by (rewrite E_ths_tgt; ss).
          assert (1 + i < List.length ths_tgt \/ 1 + i >= List.length ths_tgt) by lia.
          destruct H1.
          -- rewrite nth_error_app1 in H0 by ss. eapply M_SRC1; eauto.
          -- rewrite nth_error_app2 in H0 by ss.
             assert (1 + i - List.length ths_tgt = 0)
               by (destruct (1 + i - List.length ths_tgt) as [|[]] in *; ss).
             rewrite H2 in H0. inversion H0. subst. lia.
  Qed.

  Theorem ssim_implies_gsim
    RT R0 R1 RR p_src p_tgt sched_src sched_tgt
    (SSIM : forall m_tgt, exists m_src, @ssim nat_wf nat_wf RT R0 R1 RR p_src m_src p_tgt m_tgt sched_src sched_tgt)
    st (ths : @threads _Ident (sE State) RT)
    : gsim nat_wf nat_wf RR p_src p_tgt
        (interp_state (st, interp_sched (ths, sched_src)))
        (interp_state (st, interp_sched (ths, sched_tgt))).
  Proof.
    unfold gsim. intro gm_tgt.

    remember (gm_tgt ∘ inl) as m_tgt.
    assert (M_TGT : forall i, le nat_wf (gm_tgt (inl i)) (m_tgt i)) by (subst; reflexivity).
    specialize (SSIM m_tgt). des.
    remember (fun (i : (sum_tid _Ident).(id)) =>
                match i with
                | inl i => m_src i
                | inr i => gm_tgt (inr i)
                end) as gm_src.
    assert (M_SRC0 : forall i, gm_src (inl i) = m_src i) by (subst; ss).
    assert (M_SRC1 : forall i, nat_wf.(le) (gm_tgt (inr i)) (gm_src (inr i))) by (subst; reflexivity).
    clear Heqm_tgt Heqgm_src.
    exists gm_src.
 
    revert p_src p_tgt gm_src gm_tgt st ths m_src m_tgt sched_src sched_tgt SSIM M_TGT M_SRC0 M_SRC1.
    ginit. gcofix CIH. i.

    revert gm_src gm_tgt M_TGT M_SRC0 M_SRC1.
    punfold SSIM. induction SSIM using ssim_ind; i.
    - rewrite 2 interp_sched_ret, 2 interp_state_ret.
      guclo sim_indC_spec. econs; eauto.
    - rewrite interp_sched_tau, interp_state_tau.
      guclo sim_indC_spec. econs. eapply IHSSIM; eauto.
    - rewrite interp_sched_tau, interp_state_tau.
      guclo sim_indC_spec. econs. eapply IHSSIM; eauto.
    - pclearbot.
      destruct (Th.find tid ths) as [t|]eqn: H0; cycle 1.
      { rewrite 2 interp_sched_execute_None; eauto.
        rewrite 2 interp_state_vis.
        rewrite <- 2 bind_trigger.
        guclo sim_indC_spec. eapply sim_indC_chooseR. ss.
      }
      
      erewrite 2 interp_sched_execute_Some; eauto.
      rewrite 2 interp_state_bind.
      rewrite unfold_interp_thread.
      rewrite interp_state_aux_map_event.

      remember (interp_state_aux (st, interp_thread_aux (tid, t))) as itr.
      clear Heqitr.

      revert p_src p_tgt gm_src gm_tgt itr M_SRC0 M_SRC1 M_TGT.
      gcofix CIH2; i.
      
      destruct_itree itr.
      + destruct r0 as [st' lr]. rewrite map_event_ret, 2 bind_ret_l. destruct lr; ss.
        * rewrite 2 interp_state_tau.
          gstep. do 3 econs; eauto. gfinal. left. eapply CIH; eauto. eapply ssim_deflag, H.
        * rewrite 2 interp_state_tau.
          gstep. do 3 econs; eauto. gfinal. left. eapply CIH; eauto. eapply ssim_deflag, H.
      + rewrite map_event_tau. grind.
        gstep. do 3 econs; eauto. gfinal. left. eapply CIH2; eauto.
      + rewrite map_event_vis, 2 bind_vis.
        destruct e.
        * rewrite <- 2 bind_trigger.
          gstep. eapply sim_chooseR. i. eapply sim_chooseL. exists x. econs; eauto. gfinal. left. eapply CIH2; eauto.
        * rewrite <- 2 bind_trigger.
          gstep. eapply sim_fairR. intros gm_tgt0 FAIR. eapply sim_fairL.
          remember (fun i => match i with
                          | inl i => gm_src (inl i)
                          | inr i => gm_tgt0 (inr i)
                          end) as gm_src0.
          exists gm_src0. splits.
          { subst. intros []; ss.
            - reflexivity.
            - specialize (FAIR (inr i)). specialize (M_SRC1 i). unfold le in *; ss. destruct (m i); lia.
          }
          econs; eauto. gfinal. left. eapply CIH2.
          -- subst; eauto.
          -- subst; reflexivity.
          -- i. specialize (FAIR (inl i)). specialize (M_TGT i). unfold le in *; ss. lia.
        * gstep. econs. i. subst. gfinal. left. eapply CIH2; eauto.
        * rewrite <- 2 bind_trigger. gstep. eapply sim_ub.
    - rewrite 2 interp_sched_vis, 2 interp_state_vis.
      gstep. econs. i. subst.
      rewrite 2 interp_state_tau.
      gstep. do 5 econs; eauto. pclearbot. gfinal. left. eapply CIH; ss. eapply ssim_deflag. eapply H.
    - des. rewrite interp_sched_vis, interp_state_vis, <- bind_trigger.
      guclo sim_indC_spec. econs. eexists.
      rewrite interp_state_tau.
      do 2 (guclo sim_indC_spec; econs). eapply H0; eauto.
    - rewrite interp_sched_vis, interp_state_vis, <- bind_trigger.
      guclo sim_indC_spec. econs. i.
      rewrite interp_state_tau.
      do 2 (guclo sim_indC_spec; econs). eapply H0; eauto.
    - des. rewrite interp_sched_vis, interp_state_vis, <- bind_trigger.
      guclo sim_indC_spec. econs.
      remember (fun (i : (sum_tid _Ident).(id)) =>
                  match i with
                  | inl i => m_src0 i
                  | inr i => gm_tgt (inr i)
                  end) as gm_src0.
      exists gm_src0. splits.
      { subst. intros []; ss. rewrite M_SRC0. eapply FAIR. }
      rewrite interp_state_tau.
      do 2 (guclo sim_indC_spec; econs). eapply H1; subst; eauto. reflexivity.
    - rewrite interp_sched_vis, interp_state_vis, <- bind_trigger.
      guclo sim_indC_spec. econs. intros gm_tgt0 FAIR.
      rewrite interp_state_tau.
      do 2 (guclo sim_indC_spec; econs). eapply H0. instantiate (1 := fun i => gm_tgt0 (inl i)).
      + ii. specialize (FAIR (inl i)). specialize (M_TGT i). unfold le in *; ss. destruct (f_tgt i); lia.
      + reflexivity.
      + eauto.
      + i. specialize (FAIR (inr i)). specialize (M_SRC1 i). unfold le in *; ss. lia.
    - rewrite interp_sched_vis, interp_state_vis, <- bind_trigger. ss.
      gstep. eapply sim_ub.
    - gstep. econs; eauto. pclearbot. gfinal. left. eapply CIH; eauto.
  Qed.

  Check ssim_nondet_fifo.
  Check ssim_implies_gsim.

  Definition key_set {elt} : Th.t elt -> IdSet.t.
  Proof.
    intros [l SORTED]. unfold Raw.t in *.
    set (l' := List.map fst l).
    econs. instantiate (1 := l').
    unfold Raw.PX.ltk in *.

    assert (Sorted (fun x y => x < y) l').
    { induction SORTED.
      - subst l'. ss.
      - subst l'. ss. econs 2; ss.
        inv H; ss. econs; ss.
    }
    
    eapply IdSet.MSet.Raw.isok_iff. ss.
  Defined.

  Theorem sched_sim p_src p_tgt tid st (ths : @threads _Ident (sE State) R) (TID : ~ IdSet.In tid (key_set ths))
    : gsim nat_wf nat_wf eq p_src p_tgt
        (interp_state (st, interp_sched (ths, schedule_nondet _ (tid, key_set ths))))
        (interp_state (st, interp_sched (ths, schedule_fifo _ (tid, IdSet.elements (key_set ths))))).
  Proof. eapply ssim_implies_gsim. eapply ssim_nondet_fifo; ss. Qed.

End SIM.
