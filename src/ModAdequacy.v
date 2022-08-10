From sflib Require Import sflib.
From ITree Require Export ITree.
From Paco Require Import paco.

Require Export Coq.Strings.String Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Program.
Require Import Permutation.

Export ITreeNotations.

From Fairness Require Import Axioms.
From Fairness Require Export ITreeLib FairBeh FairSim NatStructs.
From Fairness Require Import pind PCM World.
From Fairness Require Export Mod ModSimGStutter Concurrency.
From Fairness Require Import SchedSim Adequacy.
From Fairness Require Import KnotSim LocalAdequacyAux Stutter2Knot Knot2Glob.

Set Implicit Arguments.

Section AUX.

  Lemma list_forall2_implies
        A B (f1 f2: A -> B -> Prop) la lb
        (FA: List.Forall2 f1 la lb)
        (IMP: forall a b, (f1 a b) -> (f2 a b))
    :
    List.Forall2 f2 la lb.
  Proof.
    move FA before B. revert_until FA. induction FA; i; ss.
    econs; eauto.
  Qed.

  Inductive Forall3 (A B C : Type) (R : A -> B -> C -> Prop) : list A -> list B -> list C -> Prop :=
    Forall3_nil : Forall3 R [] [] []
  | Forall3_cons : forall (x : A) (y : B) (z : C) (l1 : list A) (l2 : list B) (l3: list C),
      R x y z -> Forall3 R l1 l2 l3 -> Forall3 R (x :: l1) (y :: l2) (z :: l3).

  Lemma list_forall3_implies_forall2_3
        A B C (f1: A -> B -> C -> Prop) (f2: A -> C -> Prop)
        la lb lc
        (FA: Forall3 f1 la lb lc)
        (IMP: forall a b c, (f1 a b c) -> (f2 a c))
    :
    List.Forall2 f2 la lc.
  Proof.
    move FA before C. revert_until FA. induction FA; i; ss.
    econs; eauto.
  Qed.

  Lemma list_forall3_implies_forall2_2
        A B C (f1: A -> B -> C -> Prop) (f2: A -> B -> Prop)
        la lb lc
        (FA: Forall3 f1 la lb lc)
        (IMP: forall a b c, (f1 a b c) -> (f2 a b))
    :
    List.Forall2 f2 la lb.
  Proof.
    move FA before C. revert_until FA. induction FA; i; ss.
    econs; eauto.
  Qed.

  Import NatMap.
  Import NatMapP.

  Lemma nm_forall3_implies_find_some
        elt1 elt2 elt3 (m1: NatMap.t elt1) (m2: NatMap.t elt2) (m3: NatMap.t elt3)
        P
        (FA: Forall3 (fun '(k1, e1) '(k2, e2) '(k3, e3) => (k1 = k2) /\ (k1 = k3) /\ (P e1 e2 e3 k1))
                     (elements m1) (elements m2) (elements m3))
    :
    forall k e1 e2 e3 (FIND1: find k m1 = Some e1) (FIND2: find k m2 = Some e2) (FIND3: find k m3 = Some e3),
      P e1 e2 e3 k.
  Proof.
    match goal with
    | FA: Forall3 _ ?_ml1 ?_ml2 ?_ml3 |- _ => remember _ml1 as ml1; remember _ml2 as ml2; remember _ml3 as ml3
    end.
    move FA before elt3. revert_until FA. induction FA; i.
    { symmetry in Heqml1; apply elements_Empty in Heqml1.
      symmetry in Heqml2; apply elements_Empty in Heqml2.
      symmetry in Heqml3; apply elements_Empty in Heqml3.
      apply nm_empty_eq in Heqml1, Heqml2, Heqml3. subst. rewrite F.empty_o in FIND1; ss.
    }
    des_ifs. des; clarify. destruct (F.eq_dec k k2); clarify.
    { eapply nm_elements_cons_find_some in Heqml1, Heqml2, Heqml3. clarify. }
    hexploit nm_elements_cons_rm. eapply Heqml1. intro RM1.
    hexploit nm_elements_cons_rm. eapply Heqml2. intro RM2.
    hexploit nm_elements_cons_rm. eapply Heqml3. intro RM3.
    eapply IHFA; eauto. rewrite nm_find_rm_neq; auto. rewrite nm_find_rm_neq; auto. rewrite nm_find_rm_neq; auto.
  Qed.

End AUX.



Section LADEQ.

  Context `{M: URA.t}.

  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable _ident_src: ID.
  Let ident_src := sum_tid _ident_src.
  Variable _ident_tgt: ID.
  Let ident_tgt := sum_tid _ident_tgt.

  Variable wf_src: WF.
  Variable wf_tgt: WF.

  Notation srcE := ((@eventE _ident_src +' cE) +' sE state_src).
  Notation tgtE := ((@eventE _ident_tgt +' cE) +' sE state_tgt).

  Variable wf_stt: WF.

  Let shared := shared state_src state_tgt _ident_src _ident_tgt wf_src wf_tgt wf_stt.

  Notation threads_src1 R0 := (threads _ident_src (sE state_src) R0).
  Notation threads_src2 R0 := (threads2 _ident_src (sE state_src) R0).
  Notation threads_tgt R1 := (threads _ident_tgt (sE state_tgt) R1).

  Variable I: shared -> Prop.

  Variable St: wf_tgt.(T) -> wf_tgt.(T).
  Hypothesis lt_succ_diag_r_t: forall (t: wf_tgt.(T)), wf_tgt.(lt) t (St t).

  Lemma lsim_implies_gsim
        R0 R1 (RR: R0 -> R1 -> Prop)
        (ths_src: threads_src1 R0)
        (ths_tgt: threads_tgt R1)
        (WF: th_wf_pair ths_src ths_tgt)
        tid
        (FINDS: Th.find tid ths_src = None)
        (FINDT: Th.find tid ths_tgt = None)
        src tgt
        (st_src: state_src) (st_tgt: state_tgt)
        ps pt
        (LSIM: forall im_tgt, exists im_src o r_shared rs_ctx,
            (<<RSWF: Th.find tid rs_ctx = None>>) /\
              (<<LSIM:
                forall im_tgt0
                  (FAIR: fair_update im_tgt im_tgt0 (sum_fmap_l (tids_fmap tid (NatSet.add tid (key_set ths_tgt))))),
                exists im_src0,
                  (fair_update im_src im_src0 (sum_fmap_l (tids_fmap tid (NatSet.add tid (key_set ths_src))))) /\
                    (lsim I (local_RR I RR tid) tid ps pt (sum_of_resources rs_ctx)
                          src tgt
                          (NatSet.add tid (key_set ths_src), NatSet.add tid (key_set ths_tgt),
                            im_src0, im_tgt0, st_src, st_tgt, o, r_shared))>>) /\
              (<<LOCAL: forall tid (src: itree srcE R0) (tgt: itree tgtE R1) r_own
                          (OWN: r_own = fst (get_resource tid rs_ctx))
                          (LSRC: Th.find tid ths_src = Some src)
                          (LTGT: Th.find tid ths_tgt = Some tgt),
                  (local_sim_pick I RR src tgt tid r_own)>>))
    :
    gsim wf_src wf_tgt RR
         (interp_all st_src (Th.add tid src ths_src) tid)
         (interp_all st_tgt (Th.add tid tgt ths_tgt) tid).
  Proof.
    remember (Th.map (fun th => (false, th)) ths_src) as ths_src2.
    assert (FINDS2: Th.find tid ths_src2 = None).
    { subst. rewrite NatMapP.F.map_o. rewrite FINDS. ss. }
    assert (WF0: th_wf_pair ths_src2 ths_tgt).
    { subst. unfold th_wf_pair, nm_wf_pair in *. rewrite <- WF. unfold key_set. rewrite nm_map_unit1_map_eq. auto. }
    replace ths_src with (nm_proj_v2 ths_src2).
    2:{ subst. unfold nm_proj_v2. rewrite nm_map_map_eq. ss. apply nm_map_self_eq. }
    eapply ksim_implies_gsim; auto.
    eapply lsim_implies_ksim; eauto.
    i. specialize (LSIM im_tgt). des.
    replace (NatSet.add tid (key_set ths_src2)) with (NatSet.add tid (key_set ths_src)).
    2:{ unfold key_set. clarify. rewrite nm_map_unit1_map_eq. auto. }
    esplits; eauto.
    i. assert (SF: sf = false).
    { clarify. rewrite NatMapP.F.map_o in LSRC.
      destruct (NatMap.find (elt:=thread _ident_src (sE state_src) R0) tid0 ths_src); ss. clarify. }
    subst sf. split; i; ss. eapply LOCAL; auto.
    clarify. rewrite NatMapP.F.map_o in LSRC.
    destruct (NatMap.find (elt:=thread _ident_src (sE state_src) R0) tid0 ths_src); ss. clarify.
    Unshelve. exact true.
  Qed.

  Definition local_sim_threads
             R0 R1 (RR: R0 -> R1 -> Prop)
             (ths_src: threads_src1 R0)
             (ths_tgt: threads_tgt R1)
    :=
    List.Forall2
      (fun '(t1, src) '(t2, tgt) => (t1 = t2) /\ (local_sim I RR src tgt))
      (Th.elements ths_src) (Th.elements ths_tgt).

  Lemma local_sim_threads_local_sim_pick
        R0 R1 (RR: R0 -> R1 -> Prop)
        (ths_src: threads_src1 R0)
        (ths_tgt: threads_tgt R1)
        (LOCAL: local_sim_threads RR ths_src ths_tgt)
        (st_src: state_src) (st_tgt: state_tgt)
        (INV: forall im_tgt, exists im_src o r_shared,
            (I (NatSet.empty, NatSet.empty, im_src, im_tgt, st_src, st_tgt, o, r_shared)) /\
              (URA.wf r_shared))
    :
    forall im_tgt,
    exists (im_src0 : imap ident_src wf_src) (o0 : T wf_stt) r_shared0 (rs_local: local_resources),
      (I (key_set ths_src, key_set ths_tgt, im_src0, im_tgt, st_src, st_tgt, o0, r_shared0)) /\
        (resources_wf r_shared0 rs_local) /\
        (Forall3 (fun '(t1, src) '(t2, tgt) '(t3, r_own) =>
                    (t1 = t2) /\ (t1 = t3) /\ (local_sim_pick I RR src tgt t1 r_own))
                 (Th.elements (elt:=thread _ident_src (sE state_src) R0) ths_src)
                 (Th.elements (elt:=thread _ident_tgt (sE state_tgt) R1) ths_tgt)
                 (Th.elements rs_local)).
  Proof.
    unfold local_sim_threads in LOCAL.
    match goal with
    | FA: List.Forall2 _ ?_ml1 ?_ml2 |- _ => remember _ml1 as tl_src; remember _ml2 as tl_tgt
    end.
    move LOCAL before RR. revert_until LOCAL. induction LOCAL; i.
    { specialize (INV im_tgt). des.
      symmetry in Heqtl_src; apply NatMapP.elements_Empty in Heqtl_src.
      symmetry in Heqtl_tgt; apply NatMapP.elements_Empty in Heqtl_tgt.
      apply nm_empty_eq in Heqtl_src, Heqtl_tgt. clarify.
      esplits; ss; eauto.
      - unfold NatSet.empty in *. rewrite !key_set_empty_empty_eq. eauto.
      - instantiate (1:=@NatMap.empty _). unfold resources_wf. r_wf INV0. rewrite sum_of_resources_empty. r_solve.
      - econs.
    }

    des_ifs. des; clarify. rename k0 into tid1, i into src1, i0 into tgt1.
    hexploit nm_elements_cons_rm. eapply Heqtl_src. intro RESS.
    hexploit nm_elements_cons_rm. eapply Heqtl_tgt. intro REST.
    hexploit IHLOCAL; clear IHLOCAL; eauto. intro IND.
    des. clear INV.
    unfold local_sim in H0.
    specialize (H0 _ _ _ _ _ _ _ _ (sum_of_resources rs_local) IND tid1 (key_set ths_src) (key_set ths_tgt)).
    hexploit H0; clear H0.
    { econs. rewrite key_set_pull_rm_eq. eapply nm_find_rm_eq.
      erewrite <- key_set_pull_add_eq. instantiate (1:=src1).
      rewrite <- nm_find_some_rm_add_eq; auto. eapply nm_elements_cons_find_some; eauto.
    }
    { econs. rewrite key_set_pull_rm_eq. eapply nm_find_rm_eq.
      erewrite <- key_set_pull_add_eq. instantiate (1:=tgt1).
      rewrite <- nm_find_some_rm_add_eq; auto. eapply nm_elements_cons_find_some; eauto.
    }
    { r_wf IND0. }
    instantiate (1:=im_tgt). i; des.
    assert (WFPAIR: nm_wf_pair (NatMap.remove (elt:=thread _ident_src (sE state_src) R0) tid1 ths_src) rs_local).
    { hexploit list_forall3_implies_forall2_3. eauto.
      { i. instantiate (1:=fun '(t1, src) '(t3, r_own) => t1 = t3). ss. des_ifs. des; auto. }
      intros FA2. rewrite RESS in FA2. apply nm_forall2_wf_pair in FA2. auto.
    }
    assert (RSL: NatMap.find (elt:=M) tid1 rs_local = None).
    { eapply nm_wf_pair_find_cases in WFPAIR. des. eapply WFPAIR. apply nm_find_rm_eq. }
    esplits; eauto.
    { instantiate (1:=Th.add tid1 r_own rs_local). unfold resources_wf. rewrite sum_of_resources_add. r_wf VALID. auto. }
    replace (Th.elements (Th.add tid1 r_own rs_local)) with ((tid1, r_own) :: (Th.elements rs_local)).
    { econs; auto. splits; ss. ii.
      specialize (H1 _ _ _ _ _ _ _ _ _ INV0 VALID0 im_tgt1 FAIR). des. esplits; eauto.
    }
    { remember (Th.add tid1 r_own rs_local) as rs_local1.
      assert (REP: rs_local = (NatMap.remove tid1 rs_local1)).
      { rewrite Heqrs_local1. rewrite nm_find_none_rm_add_eq; auto. }
      rewrite REP. rewrite REP in WFPAIR. rewrite RESS in Heqtl_src.
      eapply wf_pair_elements_cons_rm; eauto.
      { eapply nm_wf_pair_rm_inv; eauto.
        - unfold NatMap.In, NatMap.Raw.PX.In. exists src1. unfold NatMap.Raw.PX.MapsTo. ss.
          unfold Th.elements, Th.Raw.elements in Heqtl_src. rewrite <- Heqtl_src. econs 1. ss.
        - rewrite Heqrs_local1. apply NatMapP.F.add_in_iff. auto.
      }
      { rewrite Heqrs_local1. rewrite nm_find_add_eq; auto. }
    }
  Qed.

  Theorem local_sim_implies_gsim
          R0 R1 (RR: R0 -> R1 -> Prop)
          (ths_src: threads_src1 R0)
          (ths_tgt: threads_tgt R1)
          (LOCAL: local_sim_threads RR ths_src ths_tgt)
          (st_src: state_src) (st_tgt: state_tgt)
          (INV: forall im_tgt, exists im_src o r_shared,
              (I (NatSet.empty, NatSet.empty, im_src, im_tgt, st_src, st_tgt, o, r_shared)) /\
                (URA.wf r_shared))
          tid
          (INS: Th.In tid ths_src)
          (INT: Th.In tid ths_tgt)
    :
    gsim wf_src wf_tgt RR
         (interp_all st_src ths_src tid)
         (interp_all st_tgt ths_tgt tid).
  Proof.
    unfold local_sim_threads in LOCAL.
    eapply NatMapP.F.in_find_iff in INS, INT.
    destruct (Th.find tid ths_src) eqn:FINDS.
    2:{ clarify. }
    destruct (Th.find tid ths_tgt) eqn:FINDT.
    2:{ clarify. }
    clear INS INT. rename i into src0, i0 into tgt0.
    remember (Th.remove tid ths_src) as ths_src0.
    remember (Th.remove tid ths_tgt) as ths_tgt0.
    assert (POPS: nm_pop tid ths_src = Some (src0, ths_src0)).
    { unfold nm_pop. rewrite FINDS. rewrite Heqths_src0. auto. }
    assert (POPT: nm_pop tid ths_tgt = Some (tgt0, ths_tgt0)).
    { unfold nm_pop. rewrite FINDT. rewrite Heqths_tgt0. auto. }
    i. replace ths_src with (Th.add tid src0 ths_src0).
    2:{ symmetry; eapply nm_pop_res_is_add_eq; eauto. }
    replace ths_tgt with (Th.add tid tgt0 ths_tgt0).
    2:{ symmetry; eapply nm_pop_res_is_add_eq; eauto. }

    eapply lsim_implies_gsim; auto.
    { subst. eapply nm_wf_pair_rm. eapply nm_forall2_wf_pair.
      eapply list_forall2_implies; eauto. i. des_ifs. des; auto.
    }
    { eapply nm_pop_res_find_none; eauto. }
    { eapply nm_pop_res_find_none; eauto. }

    cut (forall im_tgt0, exists im_src0 o0 r_shared0 rs_ctx0,
            (I (key_set ths_src, key_set ths_tgt, im_src0, im_tgt0, st_src, st_tgt, o0, r_shared0)) /\
              (resources_wf r_shared0 rs_ctx0) /\
              (forall (tid0 : Th.key) (src : thread _ident_src (sE state_src) R0)
                 (tgt : thread _ident_tgt (sE state_tgt) R1) r_own,
                  (r_own = fst (get_resource tid0 rs_ctx0)) ->
                  (Th.find (elt:=thread _ident_src (sE state_src) R0) tid0 ths_src = Some src) ->
                  (Th.find (elt:=thread _ident_tgt (sE state_tgt) R1) tid0 ths_tgt = Some tgt) ->
                  local_sim_pick I RR src tgt tid0 r_own)).
    { i. specialize (H im_tgt). des. exists im_src0, o0, r_shared0, (snd (get_resource tid rs_ctx0)). splits.
      - eapply get_resource_snd_find_eq_none.
      - ii. specialize (H1 tid src0 tgt0 (fst (get_resource tid rs_ctx0))). hexploit H1; clear H1; auto.
        i. unfold local_sim_pick in H1.
        assert (SETS: NatSet.add tid (key_set ths_src0) = key_set ths_src).
        { subst. rewrite key_set_pull_rm_eq. unfold NatSet.add.
          rewrite <- nm_find_some_rm_add_eq; auto. eapply key_set_find_some1; eauto.
        }
        assert (SETT: NatSet.add tid (key_set ths_tgt0) = key_set ths_tgt).
        { subst. rewrite key_set_pull_rm_eq. unfold NatSet.add.
          rewrite <- nm_find_some_rm_add_eq; auto. eapply key_set_find_some1; eauto.
        }
        hexploit H1; clear H1. eapply H.
        { instantiate (1:=sum_of_resources (snd (get_resource tid rs_ctx0))).
          hexploit resources_wf_get_wf. eapply H0.
          2:{ i. des. eapply WF. }
          instantiate (1:=tid). destruct (get_resource tid rs_ctx0); ss.
        }
        { rewrite <- SETT; eauto. }
        rewrite !SETS, !SETT. eauto.
      - i. eapply H1.
        { rewrite OWN. eapply get_resource_rs_neq. destruct (tid_dec tid tid0); auto. clarify.
          rewrite nm_find_rm_eq in LSRC. ss. }
        eapply find_some_aux; eauto. eapply find_some_aux; eauto.
    }

    cut (forall im_tgt, exists (im_src0 : imap ident_src wf_src) (o0 : T wf_stt) r_shared0 rs_ctx0,
            I (key_set ths_src, key_set ths_tgt, im_src0, im_tgt, st_src, st_tgt, o0, r_shared0) /\
              (resources_wf r_shared0 rs_ctx0) /\
              (List.Forall2 (fun '(t1, src) '(t2, tgt) =>
                               (t1 = t2) /\ local_sim_pick I RR src tgt t1 (fst (get_resource t1 rs_ctx0)))
                            (Th.elements (elt:=thread _ident_src (sE state_src) R0) ths_src)
                            (Th.elements (elt:=thread _ident_tgt (sE state_tgt) R1) ths_tgt))).
    { intro FA. i. specialize (FA im_tgt0). des. esplits; eauto. i. subst.
      eapply nm_forall2_implies_find_some in FA1; eauto.
    }

    i. hexploit local_sim_threads_local_sim_pick; eauto. intros FAALL. instantiate (1:=im_tgt) in FAALL.
    clear LOCAL. des.
    exists im_src0, o0, r_shared0, rs_local. splits; auto.
    clear - FAALL1.
    eapply nm_find_some_implies_forall2.
    { hexploit list_forall3_implies_forall2_2. eauto.
      { i. instantiate (1:=fun '(t1, src) '(t2, tgt) => t1 = t2). ss. des_ifs. des; auto. }
      intros FA2. apply nm_forall2_wf_pair; auto.
    }
    { i. hexploit nm_forall3_implies_find_some. eapply FAALL1. all: eauto.
      2:{ ss. eauto. }
      assert (WFPAIR: nm_wf_pair ths_src rs_local).
      { hexploit list_forall3_implies_forall2_3. eauto.
        { i. instantiate (1:=fun '(t1, src) '(t3, r_own) => t1 = t3). ss. des_ifs. des; auto. }
        intros FA2. apply nm_forall2_wf_pair in FA2. auto.
      }
      hexploit nm_wf_pair_find_cases. eapply WFPAIR. i. des. clear H. hexploit H0.
      { ii. rewrite FIND1 in H. ss. }
      i. destruct (NatMap.find k rs_local) eqn:FRS; ss. erewrite get_resource_find_some_fst; eauto.
    }
    Unshelve. all: exact true.
  Qed.

End LADEQ.


Section ADEQ.

  Definition program := list (fname * (list Val))%type.

  Definition fn2th (m: Mod.t) (fn: fname) (args: list Val): @thread (Mod.ident m) (sE (Mod.state m)) Val :=
    match Mod.funs m fn with
    | Some ktr => ktr args
    | None => (Vis (inl1 (inl1 Undefined)) (Empty_set_rect _))
    end.



  (* Definition mod_prog_wf (m: Mod.t) (p: program) := *)
  (*   Forall (fun '(fn, args) => match Mod.funs m fn with Some _ => True | _ => False end) p. *)

  (* Fixpoint mod_prog2ths_ (m: Mod.t) (p: program) (k: Th.key): *)
  (*   option (list (Th.key * @thread (Mod.ident m) (sE (Mod.state m)) Val))%type := *)
  (*   match p with *)
  (*   | (fn, args) :: tl => *)
  (*       match Mod.funs m fn with *)
  (*       | Some ktr => match mod_prog2ths_ m tl (S k) with *)
  (*                    | Some ths => Some ((k, ktr args) :: ths) *)
  (*                    | _ => None *)
  (*                    end *)
  (*       | _ => None *)
  (*       end *)
  (*   | _ => Some [] *)
  (*   end. *)

  (* Definition mod_prog2ths (m: Mod.t) (p: program): option (@threads (Mod.ident m) (sE (Mod.state m)) Val) := *)
  (*   match mod_prog2ths_ m p 0 with *)
  (*   | Some lths => Some (NatMapP.of_list lths) *)
  (*   | _ => None *)
  (*   end. *)

  (* Definition local_sim_threads_list *)
  (*            (m1 m2: Mod.t) *)
  (*            (lths_src: list (Th.key * @thread (Mod.ident m1) (sE (Mod.state m1)) Val)%type)  *)
  (*            (lths_tgt: list (Th.key * @thread (Mod.ident m2) (sE (Mod.state m2)) Val)%type) *)
  (*            (wf_src wf_tgt: WF) *)
  (*            (world: Type) (world_le: world -> world -> Prop) *)
  (*            I *)
  (*   := *)
  (*   List.Forall2 *)
  (*     (fun '(t1, src) '(t2, tgt) => (t1 = t2) /\ (local_sim ( world_le I (@eq Val) src tgt)) *)
  (*     lths_src lths_tgt. *)

  (* Lemma mod_prog_wf_prog_ex_ths_ *)
  (*       m p *)
  (*       (WF: mod_prog_wf m p) *)
  (*       (MS: ModSim.mod_sim *)
  (*   : *)
  (*   forall n, exists ths, (mod_prog2ths_ m p n = Some ths). *)
  (* Proof. *)
  (*   induction WF; i. *)
  (*   { eexists. ss. } *)
  (*   ss. des_ifs. *)
  (*   { eexists. eauto. } *)
  (*   { exfalso. specialize (IHWF (S n)). des. clarify. } *)
  (* Qed. *)

  (* Lemma mod_prog_wf_prog_ex_ths *)
  (*       m p *)
  (*       (WF: mod_prog_wf m p) *)
  (*   : *)
  (*   exists ths, mod_prog2ths m p = Some ths. *)
  (* Proof. *)
  (*   unfold mod_prog2ths. hexploit mod_prog_wf_prog_ex_ths_; eauto. i; des. eexists. rewrite H. eauto. *)
  (* Qed. *)

  (* Definition mod_prog_improves (m_src m_tgt: Mod.t) sched (p: program) := *)
  (*   forall tid, *)
  (*     let oths_src := mod_prog2ths m_src p in *)
  (*     let oths_tgt := mod_prog2ths m_tgt p in *)
  (*     match oths_src, oths_tgt with *)
  (*     | Some ths_src, Some ths_tgt => *)
  (*         improves (interp_mod m_src tid ths_src sched_nondet) (interp_mod m_tgt tid ths_tgt sched) *)
  (*     | _, _ => False *)
  (*     end. *)

  (* Theorem  *)


End ADEQ.
