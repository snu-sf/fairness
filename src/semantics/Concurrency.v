From sflib Require Import sflib.
From Paco Require Import paco.

Require Export Coq.Strings.String.
From Coq Require Import Program.

From Fairness Require Export ITreeLib EventCategory FairBeh NatStructsLarge.
From Fairness Require Export Mod.

Set Implicit Arguments.

Lemma unfold_iter E A B (f: A -> itree E (A + B)) (x: A)
  :
  ITree.iter f x =
    lr <- f x;;
    match lr with
    | inl l => tau;; ITree.iter f l
    | inr r => Ret r
    end.
Proof.
  apply bisim_is_eq. eapply unfold_iter.
Qed.


Module Th := NatMap.
Notation thread _Id E R := (itree ((((@eventE _Id) +' cE) +' callE) +' E) R).
Notation threads _Id E R := (Th.t (@thread _Id E R)).

Definition fn2th (m: Mod.t) (fn: fname) (args: Any.t): @thread (Mod.ident m) (sE (Mod.state m)) Any.t :=
  match Mod.funs m fn with
  | Some ktr => ktr args
  | None => Vis (inl1 (inl1 (inl1 Undefined))) (Empty_set_rect _)
  end.

Fixpoint _numbering {E} (l: list E) (n: NatMap.key): list (NatMap.key * E) :=
  match l with
  | hd :: tl => (n, hd) :: (_numbering tl (S n))
  | [] => []
  end.

Definition numbering {E} (l: list E): list (NatMap.key * E) := _numbering l O.

Definition prog2ths (m: Mod.t) (p: program): @threads (Mod.ident m) (sE (Mod.state m)) Any.t :=
  let pre_threads := List.map (fun '(fn, args) => fn2th m fn args) p in
  NatMapP.of_list (numbering pre_threads).


Section STATE.

  Variable S: Type.
  Variable E: Type -> Type.

  Let Es := E +' (sE S).

  Definition interp_state_aux {R} :
    (S * (itree Es R)) -> itree E (S * R).
  Proof.
    eapply ITree.iter. intros [state itr]. destruct (observe itr).
    - exact (Ret (inr (state, r))).
    - exact (Ret (inl (state, t))).
    - destruct e.
      + exact (Vis e (fun x => Ret (inl (state, k x)))).
      + destruct s as [f].
        exact (Ret (inl (fst (f state), k (snd (f state))))).
  Defined.

  Definition interp_state {R}:
    (S * (itree Es R)) -> itree E R :=
    fun x => r <- interp_state_aux x;;
          Ret (snd r).

  Lemma interp_state_aux_ret R st (r : R) :
    interp_state_aux (st, Ret r) = Ret (st, r).
  Proof. unfold interp_state_aux. rewrite unfold_iter. grind. Qed.

  Lemma interp_state_aux_vis R st X (e : E X) (ktr : ktree Es X R) :
    interp_state_aux (st, Vis (inl1 e) ktr) = Vis e (fun x => tau;; interp_state_aux (st, ktr x)).
  Proof. unfold interp_state_aux. rewrite unfold_iter. grind.
         apply observe_eta. ss. f_equal. extensionality x. grind.
  Qed.

  Lemma interp_state_aux_state R st X run (ktr : ktree Es X R) :
    interp_state_aux (st, Vis (inr1 (State run)) ktr) =
      tau;; interp_state_aux (fst (run st), ktr (snd (run st))).
  Proof. unfold interp_state_aux. rewrite unfold_iter. grind. Qed.

  Lemma interp_state_aux_tau R st (itr : itree Es R) :
    interp_state_aux (st, Tau itr) = Tau (interp_state_aux (st, itr)).
  Proof. unfold interp_state_aux. rewrite unfold_iter. grind. Qed.

  Lemma interp_state_aux_bind {R1} {R2} st (itr : itree Es R1) (ktr : ktree Es R1 R2) :
    interp_state_aux (st, itr >>= ktr) =
      x <- interp_state_aux (st, itr);;
      interp_state_aux (fst x, ktr (snd x)).
  Proof.
    eapply bisim_is_eq. revert st itr. pcofix CIH. i.
    destruct_itree itr.
    - rewrite interp_state_aux_ret. grind.
      eapply paco2_mon.
      + eapply eq_is_bisim. ss.
      + ss.
    - grind. rewrite 2 interp_state_aux_tau. grind.
      pfold. econs. right. eapply CIH.
    - grind. destruct e.
      + rewrite 2 interp_state_aux_vis. grind.
        pfold. econs. intros. grind. left.
        pfold. econs. right. eapply CIH.
      + destruct s. rewrite ! interp_state_aux_state. grind.
        pfold. econs. right. eapply CIH.
  Qed.

  Lemma unfold_interp_state R st (itr : itree Es R) :
    interp_state (st, itr) = x <- interp_state_aux (st, itr);; Ret (snd x).
  Proof. unfold interp_state. ss. Qed.

  Lemma interp_state_bind R1 R2 st (itr : itree Es R1) (ktr : ktree Es R1 R2) :
    interp_state (st, itr >>= ktr) = x <- interp_state_aux (st, itr);; interp_state (fst x, ktr (snd x)).
  Proof. unfold interp_state. rewrite interp_state_aux_bind. grind. Qed.

  Lemma interp_state_ret
        R (r: R) (state: S)
    :
    interp_state (state, Ret r) = Ret r.
  Proof.
    unfold interp_state, interp_state_aux. rewrite unfold_iter. ss. grind.
  Qed.

  Lemma interp_state_tau
        R (state: S) (itr: itree Es R)
    :
    interp_state (state, tau;; itr) = tau;; interp_state (state, itr).
  Proof.
    unfold interp_state, interp_state_aux. rewrite unfold_iter. ss. grind.
  Qed.

  Lemma interp_state_state_vis
    R st X run (ktr : ktree Es X R)
    : interp_state (st, Vis (|State run)%sum ktr) =
        tau;; interp_state (fst (run st), ktr (snd (run st))).
  Proof. unfold interp_state. rewrite interp_state_aux_state. grind. Qed.

  Lemma interp_state_state
    R st X run (ktr : ktree Es X R)
    : interp_state (st, trigger (State run) >>= ktr) =
        tau;; interp_state (fst (run st), ktr (snd (run st))).
  Proof. rewrite bind_trigger. eapply interp_state_state_vis. Qed.

  Lemma interp_state_get_vis
        R (state: S) (ktr: S -> itree Es R)
    :
    interp_state (state, Vis (inr1 (Get id)) ktr)
    =
      tau;; interp_state (state, ktr state).
  Proof.
    unfold interp_state, interp_state_aux. rewrite Get_State, unfold_iter. ss. grind.
  Qed.

  Lemma interp_state_get
        R (state: S) (ktr: S -> itree Es R)
    :
    interp_state (state, trigger (inr1 (Get id)) >>= ktr)
    =
      tau;; interp_state (state, ktr state).
  Proof.
    rewrite bind_trigger. apply interp_state_get_vis.
  Qed.

  Lemma interp_state_vis
        R (state: S) X (e: E X) (ktr: X -> itree Es R)
    :
    interp_state (state, Vis (inl1 e) ktr)
    =
      Vis e (fun x => tau;; interp_state (state, ktr x)).
  Proof.
    unfold interp_state, interp_state_aux. rewrite unfold_iter. ss. rewrite 2 bind_vis.
    apply observe_eta. ss. f_equal. extensionality x.
    rewrite bind_ret_l. rewrite bind_tau. reflexivity.
  Qed.

  Lemma interp_state_trigger
        R (state: S) X (e: E X) (ktr: X -> itree Es R)
    :
    interp_state (state, trigger (inl1 e) >>= ktr)
    =
      x <- trigger e;; tau;; interp_state (state, ktr x).
  Proof.
    rewrite ! bind_trigger. apply interp_state_vis.
  Qed.

End STATE.
Global Opaque interp_state_aux interp_state.


Section STATE_PROP.

  Variable S : Type.

  Lemma interp_state_aux_map_event E1 E2 R (embed : forall X, E1 X -> E2 X) st (itr : itree (E1 +' sE S) R) :
    interp_state_aux (st, map_event (embed_left embed) itr) = map_event embed (interp_state_aux (st, itr)).
  Proof.
    eapply bisim_is_eq. revert st itr. pcofix CIH. i.
    destruct_itree itr.
    - rewrite map_event_ret.
      rewrite 2 interp_state_aux_ret.
      rewrite map_event_ret.
      pfold. econs. ss.
    - rewrite map_event_tau.
      rewrite 2 interp_state_aux_tau.
      rewrite map_event_tau.
      pfold. econs. right. eapply CIH.
    - rewrite map_event_vis.
      destruct e.
      + ss. rewrite 2 interp_state_aux_vis.
        rewrite map_event_vis.
        pfold. econs. intros. left.
        rewrite map_event_tau.
        pfold. econs. right. eapply CIH.
      + ss. destruct s.
        rewrite ! interp_state_aux_state.
        rewrite ! map_event_tau.
        pfold. econs. right. eapply CIH.
  Qed.

End STATE_PROP.



Section SCHEDULE.

  Variant schedulerE (RT : Type) : Type -> Type :=
  | Execute : thread_id -> schedulerE RT (option RT)
  .

  Let eventE0 := @eventE thread_id.

  Definition scheduler RT R := itree (schedulerE RT +' eventE0) R.

  Context {_Ident: ID}.
  Variable E: Type -> Type.

  Let eventE1 := @eventE _Ident.
  Let eventE2 := @eventE (sum_tid _Ident).
  Let Es0 := ((eventE1 +' cE) +' callE) +' E.
  Let thread R := thread _Ident E R.
  Let threads R := threads _Ident E R.

  Definition interp_thread_aux {R} :
    thread_id * thread R -> itree (eventE1 +' E) (thread R + R).
  Proof.
    eapply ITree.iter.
    intros [tid itr].
    apply observe in itr; destruct itr as [r | itr | X e k].
    - (* Ret *)
      exact (Ret (inr (inr r))).
    - (* Tau *)
      exact (Ret (inl (tid, itr))).
    - (* Vis *)
      destruct e as [[[]|]|].
      + (* eventE *)
        exact (Vis (inl1 e) (fun x => Ret (inl (tid, k x)))).
      + (* cE *)
        destruct c.
        * (* Yield *)
          exact (Ret (inr (inl (k tt)))).
        * (* GetTid *)
          exact (Ret (inl (tid, k tid))).
      + (* callE *)
        exact (Vis (inl1 Undefined) (Empty_set_rect _)).
      + (* E *)
        exact (Vis (inr1 e) (fun x => Ret (inl (tid, k x)))).
  Defined.

  Definition interp_thread {R} :
    thread_id * thread R -> itree (eventE2 +' E) (thread R + R) :=
    fun x => map_event (embed_left (map_prism inrp)) (interp_thread_aux x).

  Definition interp_sched RT R : threads RT * scheduler RT R -> itree (eventE2 +' E) R.
  Proof.
    eapply ITree.iter. intros [ts sch].
    destruct (observe sch) as [r | sch' | X [e|e] ktr].
    - exact (Ret (inr r)).
    - exact (Ret (inl (ts, sch'))).
    - destruct e.
      destruct (Th.find n ts) as [t|].
      * exact (r <- interp_thread (n, t);;
               match r with
               | inl t' => Ret (inl (Th.add n t' ts, ktr None))
               | inr r => Ret (inl (Th.remove n ts, ktr (Some r)))
               end).
      * exact (Vis (inl1 Undefined) (Empty_set_rect _)).
    - exact (Vis (inl1 (map_prism inlp e)) (fun x => Ret (inl (ts, ktr x)))).
  Defined.

  Lemma unfold_interp_thread {R} tid (itr : thread R) :
    interp_thread (tid, itr) = map_event (embed_left (map_prism inrp)) (interp_thread_aux (tid, itr)).
  Proof. ss. Qed.

  Lemma interp_thread_ret {R} tid (r : R) :
    interp_thread (tid, Ret r) = Ret (inr r).
  Proof. unfold interp_thread, interp_thread_aux. rewrite unfold_iter. grind. eapply map_event_ret. Qed.

  Lemma interp_thread_tau R tid (itr : thread R) :
    interp_thread (tid, tau;; itr) = tau;; interp_thread (tid, itr).
  Proof. unfold interp_thread at 1, interp_thread_aux. rewrite unfold_iter. grind. eapply map_event_tau. Qed.

  Lemma interp_thread_vis R tid X (e : E X) (ktr : ktree Es0 X R) :
    interp_thread (tid, Vis (inr1 e) ktr) =
      Vis (inr1 e) (fun x => tau;; interp_thread (tid, ktr x)).
  Proof.
    unfold interp_thread at 1, interp_thread_aux. rewrite unfold_iter. grind. rewrite map_event_vis.
    eapply (f_equal (fun x => Vis (inr1 e) x)). extensionality x. grind. rewrite map_event_tau. grind.
  Qed.

  Lemma interp_thread_trigger R tid X (e : E X) (ktr : ktree Es0 X R) :
    interp_thread (tid, x <- trigger (inr1 e);; ktr x) =
      x <- trigger (inr1 e);; tau;; interp_thread (tid, ktr x).
  Proof. rewrite ! bind_trigger. eapply interp_thread_vis. Qed.

  Lemma interp_thread_vis_eventE R tid X (e : eventE1 X) (ktr : ktree Es0 X R) :
    interp_thread (tid, Vis (inl1 (inl1 (inl1 e))) ktr) =
      Vis (inl1 (map_prism inrp e)) (fun x => tau;; interp_thread (tid, ktr x)).
  Proof.
    unfold interp_thread at 1, interp_thread_aux. rewrite unfold_iter. grind. rewrite map_event_vis.
    eapply (f_equal (fun x => Vis (inl1 (map_prism inrp e)) x)). extensionality x. grind. rewrite map_event_tau. grind.
  Qed.

  Lemma interp_thread_trigger_eventE R tid X (e : eventE1 X) (ktr : ktree Es0 X R) :
    interp_thread (tid, x <- trigger (inl1 (inl1 e));; ktr x) =
      x <- trigger (inl1 (map_prism inrp e));; tau;; interp_thread (tid, ktr x).
  Proof. rewrite ! bind_trigger. eapply interp_thread_vis_eventE. Qed.

  Lemma interp_thread_vis_gettid R tid (ktr : ktree Es0 thread_id R) :
    interp_thread (tid, Vis (inl1 (inl1 (inr1 GetTid))) ktr) =
      tau;; interp_thread (tid, ktr tid).
  Proof.
    unfold interp_thread at 1, interp_thread_aux. rewrite unfold_iter. grind. rewrite map_event_tau. grind.
  Qed.

  Lemma interp_thread_trigger_gettid R tid (ktr : ktree Es0 thread_id R) :
    interp_thread (tid, x <- trigger (inl1 (inr1 GetTid));; ktr x) =
      tau;; interp_thread (tid, ktr tid).
  Proof. rewrite bind_trigger. eapply interp_thread_vis_gettid. Qed.

  Lemma interp_thread_vis_yield R tid (ktr : ktree Es0 () R) :
    interp_thread (tid, Vis (inl1 (inl1 (inr1 Yield))) ktr) =
      Ret (inl (ktr tt)).
  Proof.
    unfold interp_thread at 1, interp_thread_aux. rewrite unfold_iter. grind. rewrite map_event_ret. ss.
  Qed.

  Lemma interp_thread_trigger_yield R tid (ktr : ktree Es0 () R) :
    interp_thread (tid, x <- trigger (inl1 (inr1 Yield));; ktr x) =
      Ret (inl (ktr tt)).
  Proof. rewrite bind_trigger. apply interp_thread_vis_yield. Qed.

  Lemma interp_thread_call R tid fn args (ktr : ktree Es0 Any.t R) :
    interp_thread (tid, trigger (Call fn args) >>= ktr) = Vis (inl1 Undefined) (Empty_set_rect _).
  Proof. unfold interp_thread at 1, interp_thread_aux. rewrite unfold_iter. grind.
         rewrite map_event_vis. eapply observe_eta. ss. f_equal. extensionalities x. ss.
  Qed.

  Lemma interp_sched_ret RT R (ths : threads RT) (r : R) :
    interp_sched (ths, Ret r) = Ret r.
  Proof. unfold interp_sched. rewrite unfold_iter. grind. Qed.

  Lemma interp_sched_tau RT R ths (itr : scheduler RT R) :
    interp_sched (ths, Tau itr) = Tau (interp_sched (ths, itr)).
  Proof. unfold interp_sched. rewrite unfold_iter. grind. Qed.

  Lemma interp_sched_execute_Some RT R ths tid t (ktr : option RT -> scheduler RT R)
    (SOME : Th.find tid ths = Some t)
    : interp_sched (ths, Vis (inl1 (Execute _ tid)) ktr) =
      r <- interp_thread (tid, t);;
      match r with
      | inl t' => tau;; interp_sched (Th.add tid t' ths, ktr None)
      | inr r => tau;; interp_sched (Th.remove tid ths, ktr (Some r))
      end.
  Proof. unfold interp_sched. rewrite unfold_iter. grind. Qed.

  Lemma interp_sched_execute_None RT R ths tid (ktr : option RT -> scheduler RT R)
    (NONE : Th.find tid ths = None)
    : interp_sched (ths, Vis (inl1 (Execute _ tid)) ktr) =
        Vis (inl1 Undefined) (Empty_set_rect _).
  Proof. unfold interp_sched. rewrite unfold_iter. grind.
         eapply observe_eta. ss. f_equal. extensionality x. ss.
  Qed.

  Lemma interp_sched_vis RT R ths X (e : eventE0 X) (ktr : X -> scheduler RT R) :
    interp_sched (ths, Vis (inr1 e) ktr) =
      Vis (inl1 (map_prism inlp e)) (fun x => tau;; interp_sched (ths, ktr x)).
  Proof. unfold interp_sched. rewrite unfold_iter. grind.
         eapply observe_eta. ss. f_equal. extensionality x. grind.
  Qed.

End SCHEDULE.
Global Opaque interp_thread_aux interp_thread interp_sched.



Notation schedulerT R := ((thread_id * TIdSet.t) -> scheduler R R).
Section SCHEDULE_NONDET.

  Definition sched_nondet_body {R} q tid r : scheduler R (thread_id * TIdSet.t + R) :=
    match r with
    | None =>
        tid' <- ITree.trigger (inr1 (Choose thread_id));;
        match nm_pop tid' (NatSet.add tid q) with
        | None => Vis (inr1 (Choose void)) (Empty_set_rect _)
        | Some (_, q') =>
            ITree.trigger (inr1 (Fair (tids_fmap tid' q')));;;
            Ret (inl (tid', q'))
        end
    | Some r =>
        if NatMap.is_empty q
        then Ret (inr r)
        else
          tid' <- ITree.trigger (inr1 (Choose thread_id));;
          match nm_pop tid' q with
          | None => Vis (inr1 (Choose void)) (Empty_set_rect _)
          | Some (_, q') =>
              ITree.trigger (inr1 (Fair (tids_fmap tid' q')));;;
              Ret (inl (tid', q'))
          end
    end.

  Definition sched_nondet R0 : schedulerT R0 :=
    ITree.iter (fun '(tid, q) =>
                  r <- ITree.trigger (inl1 (Execute _ tid));;
                  sched_nondet_body q tid r).

  Lemma unfold_sched_nondet R0 tid q :
    sched_nondet R0 (tid, q) =
      r <- ITree.trigger (inl1 (Execute _ tid));;
      match r with
      | None =>
          tid' <- ITree.trigger (inr1 (Choose thread_id));;
          match nm_pop tid' (NatSet.add tid q) with
          | None => Vis (inr1 (Choose void)) (Empty_set_rect _)
          | Some (_, q') =>
              ITree.trigger (inr1 (Fair (tids_fmap tid' q')));;;
              tau;; sched_nondet _ (tid', q')
          end
      | Some r =>
          if NatMap.is_empty q
          then Ret r
          else
            tid' <- ITree.trigger (inr1 (Choose thread_id));;
            match nm_pop tid' q with
            | None => Vis (inr1 (Choose void)) (Empty_set_rect _)
            | Some (_, q') =>
                ITree.trigger (inr1 (Fair (tids_fmap tid' q')));;;
                tau;; sched_nondet _ (tid', q')
            end
      end.
  Proof.
    unfold sched_nondet at 1, sched_nondet_body.
    rewrite unfold_iter.
    grind.
    - eapply observe_eta. ss. f_equal. extensionality x0. ss.
    - eapply observe_eta. ss. f_equal. extensionality x0. ss.
  Qed.


  Context {_Ident : ID}.
  Variable E: Type -> Type.

  Let eventE1 := @eventE _Ident.
  Let eventE2 := @eventE (sum_tid _Ident).
  Let Es0 := (eventE1 +' cE) +' E.
  Let thread R := thread _Ident E R.
  Let threads R := threads _Ident E R.

  Lemma unfold_interp_sched_nondet_Some R tid t (ths : threads R) q :
    Th.find tid ths = Some t ->
    interp_sched (ths, sched_nondet R (tid, q)) =
      r <- interp_thread (tid, t);;
      match r with
      | inl t' => Tau (interp_sched (Th.add tid t' ths,
                                     tid' <- ITree.trigger (inr1 (Choose thread_id));;
                                     match nm_pop tid' (NatSet.add tid q) with
                                     | None => Vis (inr1 (Choose void)) (Empty_set_rect _)
                                     | Some (_, q') =>
                                         ITree.trigger (inr1 (Fair (tids_fmap tid' q')));;;
                                         tau;; sched_nondet _ (tid', q')
                                     end))
      | inr r => Tau (interp_sched (Th.remove tid ths,
                                    if NatMap.is_empty q
                                    then Ret r
                                    else
                                      tid' <- ITree.trigger (inr1 (Choose thread_id));;
                                      match nm_pop tid' q with
                                      | None => Vis (inr1 (Choose void)) (Empty_set_rect _)
                                      | Some (_, q') =>
                                          ITree.trigger (inr1 (Fair (tids_fmap tid' q')));;;
                                          tau;; sched_nondet _ (tid', q')
                                      end))
      end.
  Proof.
    rewrite unfold_sched_nondet at 1.
    rewrite bind_trigger.
    eapply interp_sched_execute_Some.
  Qed.

  Lemma unfold_interp_sched_nondet_None R tid (ths : threads R) q :
    Th.find tid ths = None ->
    interp_sched (ths, sched_nondet R (tid, q)) =
      Vis (inl1 Undefined) (Empty_set_rect _).
  Proof.
    rewrite unfold_sched_nondet at 1.
    rewrite bind_trigger.
    eapply interp_sched_execute_None.
  Qed.

End SCHEDULE_NONDET.
Global Opaque sched_nondet_body sched_nondet.



Section INTERPC.

  Variable State: Type.
  Variable _Ident: ID.
  Variable R: Type.

  Definition interp_concurrency
             (ths: @threads _Ident (sE State) R) (sch: schedulerT R) st :
    itree (@eventE (sum_tid _Ident)) R :=
    interp_state (st, interp_sched (ths, sch (0, NatSet.remove 0 (key_set ths)))).

End INTERPC.


Section INTERP.

  Variable S : Type.
  Variable _Ident: ID.
  Variable R: Type.

  Definition interp_all
    st (ths: @threads _Ident (sE S) R) tid : itree (@eventE (sum_tid _Ident)) R :=
    interp_state (st, interp_sched (ths, sched_nondet _ (tid, NatSet.remove tid (key_set ths)))).

  Lemma interp_all_tau
        st (ths: @threads _Ident (sE S) R) tid
        itr
    :
    (interp_all st (Th.add tid (Tau itr) ths) tid) = (Tau (interp_all st (Th.add tid itr ths) tid)).
  Proof.
    unfold interp_all. erewrite ! unfold_interp_sched_nondet_Some; eauto using nm_find_add_eq.
    rewrite interp_thread_tau. rewrite bind_tau. rewrite interp_state_tau.
    do 5 f_equal. extensionality x. destruct x.
    - rewrite ! nm_add_add_eq. rewrite ! key_set_pull_add_eq. auto.
    - erewrite 1 nm_rm_add_eq. rewrite ! key_set_pull_add_eq. eauto.
  Qed.

  Lemma interp_all_vis
        st (ths: @threads _Ident (sE S) R) tid
        X (e: @eventE _Ident X) ktr
    :
    (interp_all st (Th.add tid (Vis (((e|)|)|)%sum ktr) ths) tid) =
      (Vis (map_prism inrp e) (fun x => tau;; tau;; interp_all st (Th.add tid (ktr x) ths) tid)).
  Proof.
    unfold interp_all. erewrite ! unfold_interp_sched_nondet_Some; eauto using nm_find_add_eq.
    rewrite interp_thread_vis_eventE. rewrite bind_vis. rewrite interp_state_vis.
    do 2 f_equal. extensionality x. rewrite bind_tau. rewrite interp_state_tau.
    erewrite 1 unfold_interp_sched_nondet_Some; eauto using nm_find_add_eq.
    do 7 f_equal. extensionality r.
    destruct r.
    - rewrite ! nm_add_add_eq. rewrite ! key_set_pull_add_eq. auto.
    - erewrite 1 nm_rm_add_eq. rewrite ! key_set_pull_add_eq. eauto.
  Qed.

  Lemma interp_all_state
    st (ths : @threads _Ident (sE S) R) tid
    X run ktr
    : interp_all st (Th.add tid (Vis (|State run)%sum ktr) ths) tid =
        tau;; tau;; interp_all (fst (run st)) (Th.add tid (ktr (snd (run st) : X)) ths) tid .
  Proof.
    unfold interp_all. erewrite ! unfold_interp_sched_nondet_Some; eauto using nm_find_add_eq.
    rewrite interp_thread_vis. rewrite bind_vis. rewrite interp_state_state_vis.
    rewrite bind_tau. rewrite interp_state_tau.
    repeat f_equal. extensionalities x.
    destruct x.
    - rewrite ! nm_add_add_eq. rewrite ! key_set_pull_add_eq. auto.
    - erewrite 1 nm_rm_add_eq. rewrite ! key_set_pull_add_eq. eauto.
  Qed.

  Lemma interp_all_get
        st (ths: @threads _Ident (sE S) R) tid
        ktr
    :
    (interp_all st (Th.add tid (Vis (|Get id)%sum ktr) ths) tid) =
      (tau;; tau;; interp_all st (Th.add tid (ktr st) ths) tid).
  Proof.
    unfold interp_all. erewrite ! unfold_interp_sched_nondet_Some; eauto using nm_find_add_eq.
    rewrite interp_thread_vis. rewrite bind_vis. rewrite interp_state_get_vis. rewrite bind_tau. rewrite interp_state_tau.
    repeat f_equal. extensionality x.
    destruct x.
    - rewrite ! nm_add_add_eq. rewrite ! key_set_pull_add_eq. auto.
    - erewrite 1 nm_rm_add_eq. rewrite ! key_set_pull_add_eq. eauto.
  Qed.

  Lemma interp_all_tid
        st (ths: @threads _Ident (sE S) R) tid
        ktr
    :
    (interp_all st (Th.add tid (Vis (((|GetTid)|)|)%sum ktr) ths) tid) =
      (tau;; interp_all st (Th.add tid (ktr tid) ths) tid).
  Proof.
    unfold interp_all. erewrite ! unfold_interp_sched_nondet_Some; eauto using nm_find_add_eq.
    rewrite interp_thread_vis_gettid. rewrite bind_tau. rewrite interp_state_tau.
    repeat f_equal. extensionality x.
    destruct x.
    - rewrite ! nm_add_add_eq. rewrite ! key_set_pull_add_eq. auto.
    - erewrite 1 nm_rm_add_eq. rewrite ! key_set_pull_add_eq. eauto.
  Qed.

  Lemma interp_all_call
    st (ths: @threads _Ident (sE S) R) tid
    fn args ktr
    : interp_all st (Th.add tid (trigger (Call fn args) >>= ktr) ths) tid = trigger Undefined >>= Empty_set_rect _.
  Proof.
    unfold interp_all. erewrite ! unfold_interp_sched_nondet_Some; eauto using nm_find_add_eq.
    rewrite interp_thread_call. rewrite bind_vis. rewrite interp_state_vis. rewrite ! bind_trigger.
    eapply observe_eta. ss. f_equal. extensionalities s. ss.
  Qed.

End INTERP.

Section MOD.

  Variable mod : Mod.t.
  Let st := (Mod.st_init mod).
  Let Ident := (Mod.ident mod).
  Let main := ((Mod.funs mod) "main").

  Definition interp_mod
             (tid: thread_id)
             (ths: @threads (Mod.ident mod) (sE (Mod.state mod)) Val)
             (sched: forall R, (thread_id * TIdSet.t)%type -> (scheduler R R)):
    itree (@eventE (sum_tid Ident)) Val :=
    interp_state (st, interp_sched (ths, sched _ (tid, NatSet.remove tid (key_set ths)))).

End MOD.
