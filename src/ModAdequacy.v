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
From Fairness Require Export Mod ModSimPico Concurrency.
From Fairness Require Import SchedSim Adequacy.
From Fairness Require Import KnotSim LocalAdequacy0 LocalAdequacy1 LocalAdequacy2.

Set Implicit Arguments.

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

  Let shared := shared state_src state_tgt _ident_src _ident_tgt wf_src wf_tgt.

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
        (* r_own *)
        rs_ctx
        (RSWF: Th.find tid rs_ctx = None)
        src tgt
        (st_src: state_src) (st_tgt: state_tgt)
        ps pt
        (LSIM: forall im_tgt, exists im_src o r_shared,
            (* (<<RSWF: resources_wf r_shared (Th.add tid r_own rs_ctx)>>) /\ *)
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
      (fun '(t1, src) '(t2, tgt) => (t1 = t2) /\ (t1 <> kernel_tid) /\ (local_sim I RR src tgt))
      (Th.elements ths_src) (Th.elements ths_tgt).

  Theorem local_sim_implies_gsim
          R0 R1 (RR: R0 -> R1 -> Prop)
          (ths_src: threads_src1 R0)
          (ths_tgt: threads_tgt R1)
          (LOCAL: local_sim_threads RR ths_src ths_tgt)
          (st_src: state_src) (st_tgt: state_tgt)
          (INV: forall im_tgt, exists im_src o r_shared,
              (I (initial_threads, initial_threads, im_src, im_tgt, st_src, st_tgt, o, r_shared)) /\
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
    remember (Th.map (fun _ => ε) (key_set ths_src)) as rs_init.

    eapply lsim_implies_gsim; auto.
    { subst. eapply nm_wf_pair_rm. eapply nm_forall2_wf_pair.
      eapply list_forall2_implies; eauto. i. des_ifs. des; auto.
    }
    { eapply nm_pop_res_find_none; eauto. }
    { eapply nm_pop_res_find_none; eauto. }
    { instantiate (1:= Th.remove tid rs_init). apply nm_find_rm_eq. }

    cut (forall im_tgt0, exists im_src0 o0 r_shared0,
            (I (Th.add kernel_tid tt (key_set ths_src),
                 Th.add kernel_tid tt (key_set ths_tgt),
                 im_src0, im_tgt0, st_src, st_tgt, o0, r_shared0)) /\ (URA.wf r_shared0) /\
              (forall (tid0 : Th.key) (src : thread _ident_src (sE state_src) R0)
                 (tgt : thread _ident_tgt (sE state_tgt) R1) r_own,
                  (r_own = fst (get_resource tid0 rs_init)) ->
                  (Th.find (elt:=thread _ident_src (sE state_src) R0) tid0 ths_src = Some src) ->
                  (Th.find (elt:=thread _ident_tgt (sE state_tgt) R1) tid0 ths_tgt = Some tgt) ->
                  local_sim_pick I RR src tgt tid0 r_own)).
    { i. specialize (H im_tgt). des. exists im_src0, o0, r_shared0. split.
      - ii. specialize (H1 tid src0 tgt0 ε). hexploit H1; clear H1.
        { admit. }
        { eapply nm_pop_find_some; eauto. }
        { eapply nm_pop_find_some; eauto. }
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
        { instantiate (1:=sum_of_resources (Th.remove tid rs_init)). admit. }
        rewrite <- SETT; eauto.
        rewrite !SETS, !SETT. eauto.
      - red. intros. eapply H1.
        { rewrite OWN. admit. }
        eapply find_some_aux; eauto. eapply find_some_aux; eauto.
    }

    cut (forall im_tgt, exists (im_src0 : imap ident_src wf_src) (o0 : T wf_src) r_shared0,
            I (Th.add kernel_tid tt (key_set ths_src),
                Th.add kernel_tid tt (key_set ths_tgt),
                im_src0, im_tgt, st_src, st_tgt, o0, r_shared0) /\
              (URA.wf r_shared0) /\
              (List.Forall2 (fun '(t1, src) '(t2, tgt) => (t1 = t2) /\ (t1 <> kernel_tid) /\ local_sim_pick I RR src tgt t1 ε)
                            (Th.elements (elt:=thread _ident_src (sE state_src) R0) ths_src)
                            (Th.elements (elt:=thread _ident_tgt (sE state_tgt) R1) ths_tgt))).
    { intro FA. i. specialize (FA im_tgt0). des. esplits; eauto. i.
      eapply nm_forall2_implies_find_some in FA1; eauto. des. replace r_own with ε; auto.
      subst. unfold get_resource. des_ifs; ss. unfold nm_pop in Heq. des_ifs.
      rewrite NatMapP.F.map_o in Heq0. unfold option_map in Heq0. des_ifs.
    }

    (* cut (forall im_tgt, exists (im_src0 : imap ident_src wf_src) (o0 : T wf_src) r_shared0, *)
    (*         I (key_set ths_src, key_set ths_tgt, im_src0, im_tgt, st_src, st_tgt, o0, r_shared0) /\ *)
    (*           (URA.wf r_shared0) /\ *)
    (*           (List.Forall2 (fun '(t1, src) '(t2, tgt) => (t1 = t2) /\ (t1 <> kernel_tid) /\ local_sim_pick I RR src tgt t1 (fst (get_resource t1 rs_init))) *)
    (*                         (Th.elements (elt:=thread _ident_src (sE state_src) R0) ths_src) *)
    (*                         (Th.elements (elt:=thread _ident_tgt (sE state_tgt) R1) ths_tgt))). *)
    (* { intro FA. i. specialize (FA im_tgt0). des. esplits; eauto. i. *)
    (*   eapply nm_forall2_implies_find_some in FA1; eauto. des. rewrite H. auto. *)
    (* } *)

    clear tid src0 ths_src0 tgt0 ths_tgt0 FINDS FINDT Heqths_src0 Heqths_tgt0 POPS POPT.
    clear rs_init Heqrs_init.
    match goal with
    | FA: List.Forall2 _ ?_ml1 ?_ml2 |- _ => remember _ml1 as tl_src; remember _ml2 as tl_tgt
    end.
    move LOCAL before RR. revert_until LOCAL. induction LOCAL; i.
    { specialize (INV im_tgt). des.
      symmetry in Heqtl_src; apply NatMapP.elements_Empty in Heqtl_src.
      symmetry in Heqtl_tgt; apply NatMapP.elements_Empty in Heqtl_tgt.
      apply nm_empty_eq in Heqtl_src, Heqtl_tgt. subst. esplits; ss.
      unfold NatSet.empty in *. rewrite !key_set_empty_empty_eq. eauto.
    }

    des_ifs. des; clarify. rename k0 into tid1, i into src1, i0 into tgt1.
    hexploit nm_elements_cons_rm. eapply Heqtl_src. intro RESS.
    hexploit nm_elements_cons_rm. eapply Heqtl_tgt. intro REST.
    hexploit IHLOCAL; clear IHLOCAL; eauto. intro IND.
    des.
    unfold local_sim in H0.
    specialize (H0 _ _ _ _ _ _ _ _ IND tid1 (key_set ths_src) (key_set ths_tgt)).
    hexploit H0.
    { econs. rewrite key_set_pull_rm_eq. eapply nm_find_rm_eq.
      erewrite <- key_set_pull_add_eq. instantiate (1:=src1).
      rewrite <- nm_find_some_rm_add_eq; auto. eapply nm_elements_cons_find_some; eauto.
    }
    { econs. rewrite key_set_pull_rm_eq. eapply nm_find_rm_eq.
      erewrite <- key_set_pull_add_eq. instantiate (1:=tgt1).
      rewrite <- nm_find_some_rm_add_eq; auto. eapply nm_elements_cons_find_some; eauto.
    }
    instantiate (1:=im_tgt). i; des. esplits; eauto.
    econs; auto.
    { split; ss. ii.
      specialize (H2 _ _ _ _ _ _ _ _ INV1 WORLD0 im_tgt1 FAIR). des. esplits; eauto.
    }
    eapply list_forall2_implies; eauto. i. des_ifs. des; clarify. split; auto.
    eapply local_sim_pick_mon_world; eauto.
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
