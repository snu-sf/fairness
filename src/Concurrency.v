From sflib Require Import sflib.
From ITree Require Export ITree.
From Paco Require Import paco.

Require Export Coq.Strings.String.
Require Import Permutation.
Require Import Program.

Export ITreeNotations.

From Fairness Require Export ITreeLib FairBeh.
From Fairness Require Import Mod.

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



Section STATE.

  Variable State: Type.
  Variable E: Type -> Type.

  Let Es := E +' (stateE State).

  Definition interp_state {R}:
    (State * (itree Es R)) -> itree E R.
  Proof.
    eapply ITree.iter. intros [state itr]. destruct (observe itr).
    - exact (Ret (inr r)).
    - exact (Ret (inl (state, t))).
    - destruct e.
      + exact (Vis e (fun x => Ret (inl (state, k x)))).
      + destruct s.
        * exact (Ret (inl (st, k tt))).
        * exact (Ret (inl (state, k state))).
  Defined.

  Lemma interp_state_ret
        R (r: R) (state: State)
    :
    interp_state (state, Ret r) = Ret r.
  Proof.
    unfold interp_state. rewrite unfold_iter. ss. grind.
  Qed.

  Lemma interp_state_tau
        R (state: State) (itr: itree Es R)
    :
    interp_state (state, tau;; itr) = tau;; interp_state (state, itr).
  Proof.
    unfold interp_state. rewrite unfold_iter. ss. grind.
  Qed.

  Lemma interp_state_put_vis
        R (state0 state1: State) (ktr: unit -> itree Es R)
    :
    interp_state (state0, Vis (inr1 (Put state1)) ktr)
    =
      tau;; interp_state (state1, ktr tt).
  Proof.
    unfold interp_state. rewrite unfold_iter. ss. grind.
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
    unfold interp_state. rewrite unfold_iter. ss. grind.
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
    unfold interp_state. rewrite unfold_iter. ss. rewrite bind_vis.
    apply observe_eta. ss. f_equal. extensionality x.
    rewrite bind_ret_l. reflexivity.
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



Section SCHEDULE.

  Context {Ident: ID}.
  (* Variable State: Type. *)

  (* Variant cE: Type -> Type := *)
  (*   | Yield (st: State): cE State *)
  (* . *)

  (* Definition Es := cE +' eventE. *)
  Let eventE2 := @eventE (id_sum tids Ident).
  Let Es := eventE2 +' cE.

  (* Definition thread {R} := stateT State (itree Es) R. *)
  Definition thread {R} := itree Es R.
  Definition threads {R} := tids.(id) -> @thread R.

  Definition update_threads {R} (tid: tids.(id)) (th: thread) (ths: threads) : @threads R :=
    fun t => if (tid_dec tid t) then th else (ths t).

  Definition interp_sched {R}:
    ((@threads R) * (tids.(id) * itree Es R)) -> itree eventE2 R.
  Proof.
    eapply ITree.iter. intros [threads [tid itr]].
    destruct (observe itr).
    - exact (Ret (inr r)).
    - exact (Ret (inl (threads, (tid, t)))).
    - destruct e.
      + exact (Vis e (fun x => Ret (inl (threads, (tid, k x))))).
      + destruct c.
        * exact (Vis (Choose tids.(id))
                     (fun t => Vis (Fair (sum_fmap_l (thread_fmap t)))
                                (fun _ => Ret (inl (update_threads tid (k tt) threads, (t, threads t)))))).
        * exact (Ret (inl (threads, (tid, k tid)))).
  Defined.

  (* Definition interp_yield {R}: *)
  (*   (alist Tid (stateT State (itree Es) R) * ((Tid * itree Es (State * R)) + State)) -> itree eventE void. *)
  (* Proof. *)
  (*   eapply ITree.iter. intros [threads [[tid itr]|]]. *)
  (*   - destruct (observe itr). *)
  (*     + exact (Ret (inl (threads, inr (fst r)))). *)
  (*     + exact (Ret (inl (threads, inl (tid, t)))). *)
  (*     + destruct e. *)
  (*       * destruct c. exact (Ret (inl (alist_add tid k threads, inr st))). *)
  (*       * exact (Vis e (fun x => Ret (inl (threads, inl (tid, k x))))). *)
  (*   - exact (Vis (Choose Tid) (fun tid => *)
  (*                                '(itr, threads) <- unwrapN (alist_pop tid threads);; *)
  (*                                Ret (inl (threads, inl (tid, itr s))))). *)
  (* Defined. *)


  Lemma interp_sched_ret
        R (threads: @threads R) tid r
    :
    interp_sched (threads, (tid, Ret r)) = Ret r.
  Proof.
    unfold interp_sched. rewrite unfold_iter. ss. grind.
  Qed.

  Lemma interp_sched_tau
        R (threads: @threads R) tid itr
    :
    interp_sched (threads, (tid, tau;; itr)) = tau;; interp_sched (threads, (tid, itr)).
  Proof.
    unfold interp_sched. rewrite unfold_iter. ss. grind.
  Qed.

  Lemma interp_sched_vis
        R (threads: @threads R) tid X (e: eventE2 X) ktr
    :
    interp_sched (threads, (tid, Vis (inl1 e) ktr))
    =
      Vis e (fun x => tau;; interp_sched (threads, (tid, ktr x))).
  Proof.
    unfold interp_sched. rewrite unfold_iter. ss. rewrite bind_vis.
    apply observe_eta. ss. f_equal. extensionality x.
    rewrite bind_ret_l. reflexivity.
  Qed.

  Lemma interp_sched_trigger
        R (threads: @threads R) tid X (e: eventE2 X) ktr
    :
    interp_sched (threads, (tid, trigger (inl1 e) >>= ktr))
    =
      x <- trigger e;; tau;; interp_sched (threads, (tid, ktr x)).
  Proof.
    rewrite ! bind_trigger. apply interp_sched_vis.
  Qed.

  Lemma interp_sched_yield_vis
        R (threads: @threads R) tid ktr
    :
    interp_sched (threads, (tid, Vis (inr1 Yield) ktr))
    =
      Vis (Choose tids.(id))
          (fun t => Vis (Fair (sum_fmap_l (thread_fmap t)))
                     (fun _ => tau;; interp_sched (update_threads tid (ktr tt) threads, (t, threads t)))).
  Proof.
    unfold interp_sched. rewrite unfold_iter. ss. grind.
    eapply observe_eta. ss. f_equal. extensionality t. ss. grind.
  Qed.

  Lemma interp_sched_yield
        R (threads: @threads R) tid ktr
    :
    interp_sched (threads, (tid, trigger (inr1 Yield) >>= ktr))
    =
      Vis (Choose tids.(id))
          (fun t => Vis (Fair (sum_fmap_l (thread_fmap t)))
                     (fun _ => tau;; interp_sched (update_threads tid (ktr tt) threads, (t, threads t)))).
  Proof.
    rewrite bind_trigger. apply interp_sched_yield_vis.
  Qed.

  Lemma interp_sched_gettid_vis
        R (threads: @threads R) tid ktr
    :
    interp_sched (threads, (tid, Vis (inr1 GetTid) ktr))
    =
      tau;; interp_sched (threads, (tid, ktr tid)).
  Proof.
    unfold interp_sched. rewrite unfold_iter. ss. grind.
  Qed.

  Lemma interp_sched_gettid
        R (threads: @threads R) tid ktr
    :
    interp_sched (threads, (tid, trigger (inr1 GetTid) >>= ktr))
    =
      tau;; interp_sched (threads, (tid, ktr tid)).
  Proof.
    rewrite bind_trigger. apply interp_sched_gettid_vis.
  Qed.


  (* Lemma interp_yield_bind R (threads: alist Tid (stateT State (itree Es) R)) tid A (itr: itree Es A) ktr *)
  (*   : *)
  (*     interp_yield (threads, inl (tid, itr >>= ktr)) *)
  (*     = *)
  (*     ?? *)
  (* . *)

  (* Lemma interp_yield_ret R (threads: @threads R) tid st r *)
  (*   : *)
  (*   interp_yield (threads, inl (tid, Ret (st, r))) = tau;; interp_yield (threads, inr st). *)
  (* Proof. *)
  (*   unfold interp_yield. rewrite unfold_iter. ss. grind. *)
  (* Qed. *)

  (* Lemma interp_yield_tau R (threads: @threads R) tid itr *)
  (*   : *)
  (*   interp_yield (threads, inl (tid, tau;; itr)) = tau;; interp_yield (threads, inl (tid, itr)). *)
  (* Proof. *)
  (*   unfold interp_yield. rewrite unfold_iter. ss. grind. *)
  (* Qed. *)

  (* Lemma interp_yield_yield_vis R (threads: @threads R) tid st k *)
  (*   : *)
  (*   interp_yield (threads, inl (tid, Vis (Yield st|)%sum k)) *)
  (*   = *)
  (*     tau;; interp_yield (update_threads tid k threads, inr st). *)
  (* Proof. *)
  (*   unfold interp_yield. rewrite unfold_iter. ss. grind. *)
  (* Qed. *)

  (* Lemma interp_yield_yield R (threads: @threads R) tid st k *)
  (*   : *)
  (*   interp_yield (threads, inl (tid, trigger (Yield st|)%sum >>= k)) *)
  (*   = *)
  (*     tau;; interp_yield (update_threads tid k threads, inr st). *)
  (* Proof. *)
  (*   rewrite bind_trigger. apply interp_yield_yield_vis. *)
  (* Qed. *)

  (* Lemma interp_yield_vis R (threads: @threads R) tid X (e: eventE X) k *)
  (*   : *)
  (*   interp_yield (threads, inl (tid, Vis (|e)%sum k)) *)
  (*   = *)
  (*     Vis e (fun x => tau;; interp_yield (threads, inl (tid, k x))). *)
  (* Proof. *)
  (*   unfold interp_yield. rewrite unfold_iter. ss. rewrite bind_vis. *)
  (*   apply observe_eta. ss. f_equal. extensionality x. *)
  (*   rewrite bind_ret_l. reflexivity. *)
  (* Qed. *)

  (* Lemma interp_yield_trigger R (threads: @threads R) tid X (e: eventE X) k *)
  (*   : *)
  (*   interp_yield (threads, inl (tid, trigger (|e)%sum >>= k)) *)
  (*   = *)
  (*     x <- trigger e;; tau;; interp_yield (threads, inl (tid, k x)). *)
  (* Proof. *)
  (*   rewrite ! bind_trigger. apply interp_yield_vis. *)
  (* Qed. *)

  (* Lemma interp_yield_pick_vis R (threads: @threads R) st *)
  (*   : *)
  (*   interp_yield (threads, inr st) *)
  (*   = *)
  (*     Vis (Choose id) (fun tid => tau;; interp_yield (threads, inl (tid, (threads tid st)))). *)
  (* (* Vis (Choose _ Tid) (fun tid => *) *)
  (* (*                     '(itr, threads) <- unwrapN (alist_pop tid threads);; *) *)
  (* (*                     tau;; interp_yield (threads, inl (tid, itr st))). *) *)
  (* Proof. *)
  (*   unfold interp_yield. rewrite unfold_iter. rewrite bind_vis. *)
  (*   apply observe_eta. ss. f_equal. extensionality x. *)
  (*   grind. *)
  (*   (* rewrite bind_bind. f_equal. extensionality r. destruct r; ss. *) *)
  (*   (* rewrite bind_ret_l. refl. *) *)
  (* Qed. *)

  (* Lemma interp_yield_pick R (threads: @threads R) st *)
  (*   : *)
  (*   interp_yield (threads, inr st) *)
  (*   = *)
  (*     tid <- trigger (Choose id);; *)
  (*     tau;; interp_yield (threads, inl (tid, threads tid st)). *)
  (* (* '(itr, threads) <- unwrapN (alist_pop tid threads);; *) *)
  (* (* tau;; interp_yield (threads, inl (tid, itr st)). *) *)
  (* Proof. *)
  (*   rewrite bind_trigger. apply interp_yield_pick_vis. *)
  (* Qed. *)

  (* (* Lemma interp_yield_bind R (threads: alist Tid (stateT State (itree Es) R)) tid A (itr: itree Es A) ktr *) *)
  (* (*   : *) *)
  (* (*     interp_yield (threads, inl (tid, itr >>= ktr)) *) *)
  (* (*     = *) *)
  (* (*     ?? *) *)
  (* (* . *) *)

End SCHEDULE.



Section INTERP.

  Variable mod: Mod.t.
  Let st := (Mod.st_init mod).
  Let Ident := (Mod.ident mod).
  Let main := ((Mod.funs mod) "main").

  Definition tid_main: tids.(id) := 0.

  Definition interp_mod (ths: @threads (Mod._ident mod) Val): itree (@eventE Ident) Val :=
    interp_sched (ths, (tid_main, interp_state (st, main []))).

End INTERP.
