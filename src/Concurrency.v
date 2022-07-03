From sflib Require Import sflib.
From ITree Require Export ITree.
From Paco Require Import paco.

Require Export Coq.Strings.String.
Require Import Program.
Require Import Permutation.

Export ITreeNotations.

From Fairness Require Export ITreeLib FairBeh.
From Fairness Require Import Mod.

Require Import Coq.FSets.FMaps Coq.Structures.OrderedTypeEx.
Module Th := FMapList.Make(Nat_as_OT).

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

Ltac destruct_itree itr :=
  let E := fresh "E" in
  destruct (observe itr) eqn: E;
  let H := fresh "H" in
  pose proof (H := itree_eta_ itr);
  rewrite E in H;
  clear E;
  subst itr.

Section EMBED_EVENT.

  CoFixpoint map_event {E1 E2} (embed : forall X, E1 X -> E2 X) R : itree E1 R -> itree E2 R :=
    fun itr =>
      match observe itr with
      | RetF r => Ret r
      | TauF itr => Tau (map_event embed itr)
      | VisF e ktr => Vis (embed _ e) (fun x => map_event embed (ktr x))
      end.

  Lemma map_event_ret E1 E2 (embed : forall X, E1 X -> E2 X) R (r : R) :
    map_event embed (Ret r) = Ret r.
  Proof. eapply observe_eta. ss. Qed.

  Lemma map_event_tau E1 E2 (embed : forall X, E1 X -> E2 X) R (itr : itree E1 R) :
    map_event embed (Tau itr) = Tau (map_event embed itr).
  Proof. eapply observe_eta. ss. Qed.

  Lemma map_event_vis E1 E2 (embed : forall X, E1 X -> E2 X) R X (e : E1 X) (ktr : ktree E1 X R) :
    map_event embed (Vis e ktr) = Vis (embed _ e) (fun x => map_event embed (ktr x)).
  Proof. eapply observe_eta. ss. Qed.

  Definition embed_left {E1 E2} (embed : forall X, E1 X -> E2 X) {E} X (e : (E1 +' E) X) : (E2 +' E) X :=
    match e with
    | inl1 e => inl1 (embed _ e)
    | inr1 e => inr1 e
    end.

End EMBED_EVENT.

Section STATE.

  Variable State: Type.
  Variable E: Type -> Type.

  Let Es := E +' (sE State).

  Definition interp_state_aux {R} :
    (State * (itree Es R)) -> itree E (State * R).
  Proof.
    eapply ITree.iter. intros [state itr]. destruct (observe itr).
    - exact (Ret (inr (state, r))).
    - exact (Ret (inl (state, t))).
    - destruct e.
      + exact (Vis e (fun x => Ret (inl (state, k x)))).
      + destruct s.
        * exact (Ret (inl (st, k tt))).
        * exact (Ret (inl (state, k state))).
  Defined.

  Definition interp_state {R}:
    (State * (itree Es R)) -> itree E R :=
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

  Lemma interp_state_aux_put R st st' (ktr : ktree Es unit R) :
    interp_state_aux (st, Vis (inr1 (Put st')) ktr) = tau;; interp_state_aux (st', ktr tt).
  Proof. unfold interp_state_aux. rewrite unfold_iter. grind. Qed.

  Lemma interp_state_aux_get R st (ktr : ktree Es State R) :
    interp_state_aux (st, Vis (inr1 (Get _)) ktr) = tau;; interp_state_aux (st, ktr st).
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
      + destruct s.
        * rewrite 2 interp_state_aux_put. grind.
          pfold. econs. right. eapply CIH.
        * rewrite 2 interp_state_aux_get. grind.
          pfold. econs. right. eapply CIH.
  Qed.

  Lemma unfold_interp_state R st (itr : itree Es R) :
    interp_state (st, itr) = x <- interp_state_aux (st, itr);; Ret (snd x).
  Proof. unfold interp_state. ss. Qed.

  Lemma interp_state_bind R1 R2 st (itr : itree Es R1) (ktr : ktree Es R1 R2) :
    interp_state (st, itr >>= ktr) = x <- interp_state_aux (st, itr);; interp_state (fst x, ktr (snd x)).
  Proof. unfold interp_state. rewrite interp_state_aux_bind. grind. Qed.

  Lemma interp_state_ret
        R (r: R) (state: State)
    :
    interp_state (state, Ret r) = Ret r.
  Proof.
    unfold interp_state, interp_state_aux. rewrite unfold_iter. ss. grind.
  Qed.

  Lemma interp_state_tau
        R (state: State) (itr: itree Es R)
    :
    interp_state (state, tau;; itr) = tau;; interp_state (state, itr).
  Proof.
    unfold interp_state, interp_state_aux. rewrite unfold_iter. ss. grind.
  Qed.

  Lemma interp_state_put_vis
        R (state0 state1: State) (ktr: unit -> itree Es R)
    :
    interp_state (state0, Vis (inr1 (Put state1)) ktr)
    =
      tau;; interp_state (state1, ktr tt).
  Proof.
    unfold interp_state, interp_state_aux. rewrite unfold_iter. ss. grind.
  Qed.

  Lemma interp_state_put
        R (state0 state1: State) (ktr: unit -> itree Es R)
    :
    interp_state (state0, trigger (inr1 (Put state1)) >>= ktr)
    =
      tau;; interp_state (state1, ktr tt).
  Proof.
    rewrite bind_trigger. apply interp_state_put_vis.
  Qed.

  Lemma interp_state_get_vis
        R (state: State) (ktr: State -> itree Es R)
    :
    interp_state (state, Vis (inr1 (@Get _)) ktr)
    =
      tau;; interp_state (state, ktr state).
  Proof.
    unfold interp_state, interp_state_aux. rewrite unfold_iter. ss. grind.
  Qed.

  Lemma interp_state_get
        R (state: State) (ktr: State -> itree Es R)
    :
    interp_state (state, trigger (inr1 (@Get _)) >>= ktr)
    =
      tau;; interp_state (state, ktr state).
  Proof.
    rewrite bind_trigger. apply interp_state_get_vis.
  Qed.

  Lemma interp_state_vis
        R (state: State) X (e: E X) (ktr: X -> itree Es R)
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
        R (state: State) X (e: E X) (ktr: X -> itree Es R)
    :
    interp_state (state, trigger (inl1 e) >>= ktr)
    =
      x <- trigger e;; tau;; interp_state (state, ktr x).
  Proof.
    rewrite ! bind_trigger. apply interp_state_vis.
  Qed.

End STATE.

Global Opaque
  interp_state_aux
  interp_state.

Section STATE_PROP.

  Variable State: Type.

  Lemma interp_state_aux_map_event E1 E2 R (embed : forall X, E1 X -> E2 X) st (itr : itree (E1 +' sE State) R) :
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
        * rewrite 2 interp_state_aux_put.
          rewrite map_event_tau.
          pfold. econs. right. eapply CIH.
        * rewrite 2 interp_state_aux_get.
          rewrite map_event_tau.
          pfold. econs. right. eapply CIH.
  Qed.

End STATE_PROP.



Notation thread _Id E R := (itree (((@eventE _Id) +' cE) +' E) R).
Notation threads _Id E R := (Th.t (@thread _Id E R)).

Definition th_proj1 elt (m: Th.t elt): list Th.key := List.map fst (Th.elements m).
Definition th_proj2 elt (m: Th.t elt): list elt := List.map snd (Th.elements m).

Definition th_proj_v1 V1 V2 (m: Th.t (prod V1 V2)): Th.t V1 := Th.map fst m.
Definition th_proj_v2 V1 V2 (m: Th.t (prod V1 V2)): Th.t V2 := Th.map snd m.

Definition th_pop (elt: Type) : Th.key -> Th.t elt -> option (prod elt (Th.t elt)) :=
  fun k m => match Th.find k m with
          | None => None
          | Some e => Some (e, Th.remove k m)
          end.

Section SCHEDULE.

  Context {_Ident: ID}.
  Variable E: Type -> Type.

  Let eventE1 := @eventE _Ident.
  Let eventE2 := @eventE (sum_tid _Ident).

  Definition embed_eventE X (e: eventE1 X): eventE2 X.
  Proof.
    destruct e. exact (Choose X). exact (Fair (sum_fmap_r m)). exact (Observe fn args). exact Undefined.
  Defined.

  Let Es0 := (eventE1 +' cE) +' E.

  Let thread R := thread _Ident E R.
  Let threads R := threads _Ident E R.

  Definition interp_thread_aux {R} :
    thread_id.(id) * thread R -> itree (eventE1 +' E) (thread R + R).
  Proof.
    eapply ITree.iter.
    intros [tid itr].
    apply observe in itr; destruct itr as [r | itr | X e k].
    - (* Ret *)
      exact (Ret (inr (inr r))).
    - (* Tau *)
      exact (Ret (inl (tid, itr))).
    - (* Vis *)
      destruct e as [[]|].
      + (* eventE *)
        exact (Vis (inl1 e) (fun x => Ret (inl (tid, k x)))).
      + (* cE *)
        destruct c.
        * (* Yield *)
          exact (Ret (inr (inl (k tt)))).
        * (* GetTid *)
          exact (Ret (inl (tid, k tid))).
      + (* E *)
        exact (Vis (inr1 e) (fun x => Ret (inl (tid, k x)))).
  Defined.

  Definition interp_thread {R} :
    thread_id.(id) * thread R -> itree (eventE2 +' E) (thread R + R) :=
    fun x => map_event (embed_left embed_eventE) (interp_thread_aux x).

  Definition interp_sched_aux
    (pick_thread : forall {R}, thread_id.(id) * (thread R + R) -> threads R ->
                          itree (eventE2 +' E) (thread_id.(id) * thread R * threads R + R))
    {R}
    :
    thread_id.(id) * thread R * threads R -> itree (eventE2 +' E) R :=
    ITree.iter (fun '(t, ts) =>
                  res <- interp_thread t;;
                  pick_thread (fst t, res) ts
      ).

  (* NB for invalid tid *)
  Definition pick_thread_nondet {R} :
    thread_id.(id) * (thread R + R) -> threads R ->
    itree (eventE2 +' E) (thread_id.(id) * thread R * threads R + R) :=
    fun '(tid, res) ts =>
      match res with
      | inl t =>
          Vis (inl1 (Choose thread_id.(id)))
              (fun tid' =>
                 match th_pop tid' (Th.add tid t ts) with
                 | None => Vis (inl1 (Choose void)) (Empty_set_rect _)
                 | Some (t', ts') =>
                     Vis (inl1 (Fair (sum_fmap_l (tids_fmap tid' (th_proj1 ts')))))
                         (fun _ => Ret (inl (tid', t', ts')))
                 end)
      | inr r =>
          if Th.is_empty ts then Ret (inr r)
          else Vis (inl1 (Choose thread_id.(id)))
                   (fun tid' =>
                      match th_pop tid' ts with
                      | None => Vis (inl1 (Choose void)) (Empty_set_rect _)
                      | Some (t', ts') =>
                          Vis (inl1 (Fair (sum_fmap_l (tids_fmap tid' (th_proj1 ts')))))
                              (fun _ => Ret (inl (tid', t', ts')))
                      end)
      end.

  Definition interp_sched {R} :
    thread_id.(id) * thread R * threads R -> itree (eventE2 +' E) R :=
    @interp_sched_aux (@pick_thread_nondet) R.

  (* Lemmas for interp_thread *)
  Lemma unfold_interp_thread {R} tid (itr : thread R) :
    interp_thread (tid, itr) = map_event (embed_left embed_eventE) (interp_thread_aux (tid, itr)).
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
    interp_thread (tid, Vis (inl1 (inl1 e)) ktr) =
      Vis (inl1 (embed_eventE e)) (fun x => tau;; interp_thread (tid, ktr x)).
  Proof.
    unfold interp_thread at 1, interp_thread_aux. rewrite unfold_iter. grind. rewrite map_event_vis.
    eapply (f_equal (fun x => Vis (inl1 (embed_eventE e)) x)). extensionality x. grind. rewrite map_event_tau. grind.
  Qed.

  Lemma interp_thread_trigger_eventE R tid X (e : eventE1 X) (ktr : ktree Es0 X R) :
    interp_thread (tid, x <- trigger (inl1 (inl1 e));; ktr x) =
      x <- trigger (inl1 (embed_eventE e));; tau;; interp_thread (tid, ktr x).
  Proof. rewrite ! bind_trigger. eapply interp_thread_vis_eventE. Qed.

  Lemma interp_thread_vis_gettid R tid (ktr : ktree Es0 thread_id.(id) R) :
    interp_thread (tid, Vis (inl1 (inr1 GetTid)) ktr) =
      tau;; interp_thread (tid, ktr tid).
  Proof.
    unfold interp_thread at 1, interp_thread_aux. rewrite unfold_iter. grind. rewrite map_event_tau. grind.
  Qed.

  Lemma interp_thread_trigger_gettid R tid (ktr : ktree Es0 thread_id.(id) R) :
    interp_thread (tid, x <- trigger (inl1 (inr1 GetTid));; ktr x) =
      tau;; interp_thread (tid, ktr tid).
  Proof. rewrite bind_trigger. eapply interp_thread_vis_gettid. Qed.

  Lemma interp_thread_vis_yield R tid (ktr : ktree Es0 () R) :
    interp_thread (tid, Vis (inl1 (inr1 Yield)) ktr) =
      Ret (inl (ktr tt)).
  Proof.
    unfold interp_thread at 1, interp_thread_aux. rewrite unfold_iter. grind. rewrite map_event_ret. ss.
  Qed.

  Lemma interp_thread_trigger_yield R tid (ktr : ktree Es0 () R) :
    interp_thread (tid, x <- trigger (inl1 (inr1 Yield));; ktr x) =
      Ret (inl (ktr tt)).
  Proof. rewrite bind_trigger. apply interp_thread_vis_yield. Qed.

  (* Lemmas for pick_thread_nondet *)
  Lemma pick_thread_nondet_yield {R} tid (t : thread R) ts :
    pick_thread_nondet (tid, (inl t)) ts =
      Vis (inl1 (Choose thread_id.(id)))
        (fun tid' =>
           match th_pop tid' (Th.add tid t ts) with
           | None => Vis (inl1 (Choose void)) (Empty_set_rect _)
           | Some (t', ts') => Vis (inl1 (Fair (sum_fmap_l (tids_fmap tid' (th_proj1 ts')))))
                                (fun _ => Ret (inl (tid', t', ts')))
           end).
  Proof. ss. Qed.

  Lemma pick_thread_nondet_terminate {R} tid (r : R) ts :
    pick_thread_nondet (tid, (inr r)) ts =
      if Th.is_empty ts then Ret (inr r)
      else Vis (inl1 (Choose thread_id.(id)))
               (fun tid' =>
                  match th_pop tid' ts with
                  | None => Vis (inl1 (Choose void)) (Empty_set_rect _)
                  | Some (t', ts') => Vis (inl1 (Fair (sum_fmap_l (tids_fmap tid' (th_proj1 ts')))))
                                         (fun _ => Ret (inl (tid', t', ts')))
                  end).
  Proof. ss. Qed.

  (* Lemmas for interp_sched *)
  Lemma unfold_interp_sched_aux {R} pick_thread tid (t : thread R) ts :
    interp_sched_aux pick_thread (tid, t, ts) =
      res <- interp_thread (tid, t);;
      x <- pick_thread R (tid, res) ts;;
      match x with
      | inl tts => tau;; interp_sched_aux pick_thread tts
      | inr r => Ret r
      end.
  Proof. unfold interp_sched_aux at 1. rewrite unfold_iter. rewrite bind_bind. ss. Qed.

  Lemma unfold_interp_sched {R} tid (t : thread R) ts :
    interp_sched (tid, t, ts) =
      res <- interp_thread (tid, t);;
      x <- pick_thread_nondet (tid, res) ts;;
      match x with
      | inl tts => tau;; interp_sched tts
      | inr r => Ret r
      end.
  Proof. eapply unfold_interp_sched_aux. Qed.

End SCHEDULE.

Global Opaque
  interp_thread
  pick_thread_nondet
  interp_sched_aux
  interp_sched.



Section INTERP.

  Variable State: Type.
  Variable _Ident: ID.

  Definition interp_all
             {R}
             (st: State) (ths: @threads _Ident (sE State) R)
             tid (itr: @thread _Ident (sE State) R) :
    itree (@eventE (sum_tid _Ident)) R :=
    interp_state (st, interp_sched (tid, itr, ths)).

End INTERP.


Section MOD.

  Variable mod: Mod.t.
  Let st := (Mod.st_init mod).
  Let Ident := (Mod.ident mod).
  Let main := ((Mod.funs mod) "main").

  Definition interp_mod (ths: @threads (Mod.ident mod) (sE (Mod.state mod)) Val):
    itree (@eventE (sum_tid Ident)) Val :=
    interp_all st ths tid_main (main []).

End MOD.
