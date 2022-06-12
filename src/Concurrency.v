From sflib Require Import sflib.
From ITree Require Export ITree.
From Paco Require Import paco.

Require Export Coq.Strings.String.
Require Import Program.

From ExtLib Require Import FMapAList.

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

  Let Es := E +' (sE State).

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
  Variable E: Type -> Type.
  (* Variable State: Type. *)

  (* Variant cE: Type -> Type := *)
  (*   | Yield (st: State): cE State *)
  (* . *)

  (* Definition Es := cE +' eventE. *)
  Let eventE2 := @eventE (id_sum tids Ident).
  Let Es := (eventE2 +' cE) +' E.
  (* Let Es := (eventE2 +' cE) +' (sE State). *)

  (* Definition thread {R} := stateT State (itree Es) R. *)
  Definition thread {R} := itree Es R.
  Definition threads {R} := alist tids.(id) (@thread R).

  Definition threads_add := alist_add (RelDec.RelDec_from_dec eq tid_dec).
  Definition threads_find := alist_find (RelDec.RelDec_from_dec eq tid_dec).
  Definition threads_remove := alist_remove (RelDec.RelDec_from_dec eq tid_dec).

  Definition update_threads {R} (tid: tids.(id)) (th: thread) (ths: threads): @threads R :=
    threads_add tid th ths.
  (* fun t => if (tid_dec tid t) then th else (ths t). *)

  Definition threads_pop {R} (tid: tids.(id)) (ths: threads): option (prod (@thread R) threads) :=
    match threads_find tid ths with
    | None => None
    | Some th => Some (th, threads_remove tid ths)
    end.

  Definition interp_sched {R}:
    ((@threads R) * ((tids.(id) * itree Es R) + (unit))) -> itree (eventE2 +' E) R.
  Proof.
    eapply ITree.iter. intros [threads [[tid itr]|]].
    - destruct (observe itr).
      + exact (Ret (inl (threads, inr tt))).
      + exact (Ret (inl (threads, inl (tid, t)))).
      + destruct e.
        * destruct s.
          { exact (Vis (inl1 e) (fun x => Ret (inl (threads, inl (tid, k x))))). }
          { destruct c.
            { exact (Ret (inl (update_threads tid (k tt) threads, inr tt))). }
            { exact (Ret (inl (threads, inl (tid, k tid)))). }
          }
        * exact (Vis (inr1 e) (fun x => Ret (inl (threads, inl (tid, k x))))).
    - exact (Vis (inl1 (Choose tids.(id)))
                 (fun t => match threads_pop t threads with
                        | None => Vis (inl1 Undefined) (fun _ => Ret (inl (threads, inr tt)))
                        | Some (th, ths) =>
                            Vis (inl1 (Fair (sum_fmap_l (thread_fmap t))))
                                (fun _ => Ret (inl (ths, inl (t, th))))
                        end)).
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
    interp_sched (threads, inl (tid, Ret r)) = tau;; interp_sched (threads, inr tt).
  Proof.
    unfold interp_sched. rewrite unfold_iter. ss. grind.
  Qed.

  Lemma interp_sched_tau
        R (threads: @threads R) tid itr
    :
    interp_sched (threads, inl (tid, tau;; itr)) = tau;; interp_sched (threads, inl (tid, itr)).
  Proof.
    unfold interp_sched. rewrite unfold_iter. ss. grind.
  Qed.

  Lemma interp_sched_vis
        R (threads: @threads R) tid X (e: E X) ktr
    :
    interp_sched (threads, inl (tid, Vis (inr1 e) ktr))
    =
      Vis (inr1 e) (fun x => tau;; interp_sched (threads, inl (tid, ktr x))).
  Proof.
    unfold interp_sched. rewrite unfold_iter. ss. rewrite bind_vis.
    apply observe_eta. ss. f_equal. extensionality x.
    rewrite bind_ret_l. reflexivity.
  Qed.

  Lemma interp_sched_trigger
        R (threads: @threads R) tid X (e: E X) ktr
    :
    interp_sched (threads, inl (tid, trigger (inr1 e) >>= ktr))
    =
      x <- trigger (inr1 e);; tau;; interp_sched (threads, inl (tid, ktr x)).
  Proof.
    rewrite ! bind_trigger. apply interp_sched_vis.
  Qed.

  Lemma interp_sched_eventE_vis
        R (threads: @threads R) tid X (e: eventE2 X) ktr
    :
    interp_sched (threads, inl (tid, Vis (inl1 (inl1 e)) ktr))
    =
      Vis (inl1 e) (fun x => tau;; interp_sched (threads, inl (tid, ktr x))).
  Proof.
    unfold interp_sched. rewrite unfold_iter. ss. rewrite bind_vis.
    apply observe_eta. ss. f_equal. extensionality x.
    rewrite bind_ret_l. reflexivity.
  Qed.

  Lemma interp_sched_eventE_trigger
        R (threads: @threads R) tid X (e: eventE2 X) ktr
    :
    interp_sched (threads, inl (tid, trigger (inl1 (inl1 e)) >>= ktr))
    =
      x <- trigger (inl1 e);; tau;; interp_sched (threads, inl (tid, ktr x)).
  Proof.
    rewrite ! bind_trigger. apply interp_sched_eventE_vis.
  Qed.

  Lemma interp_sched_gettid_vis
        R (threads: @threads R) tid ktr
    :
    interp_sched (threads, inl (tid, Vis (inl1 (inr1 GetTid)) ktr))
    =
      tau;; interp_sched (threads, inl (tid, ktr tid)).
  Proof.
    unfold interp_sched. rewrite unfold_iter. ss. grind.
  Qed.

  Lemma interp_sched_gettid
        R (threads: @threads R) tid ktr
    :
    interp_sched (threads, inl (tid, trigger (inl1 (inr1 GetTid)) >>= ktr))
    =
      tau;; interp_sched (threads, inl (tid, ktr tid)).
  Proof.
    rewrite bind_trigger. apply interp_sched_gettid_vis.
  Qed.

  Lemma interp_sched_yield_vis
        R (threads: @threads R) tid ktr
    :
    interp_sched (threads, inl (tid, Vis (inl1 (inr1 Yield)) ktr))
    =
      tau;; interp_sched (update_threads tid (ktr tt) threads, inr tt).
  Proof.
    unfold interp_sched. rewrite unfold_iter. ss. grind.
  Qed.

  Lemma interp_sched_yield
        R (threads: @threads R) tid ktr
    :
    interp_sched (threads, inl (tid, trigger (inl1 (inr1 Yield)) >>= ktr))
    =
      tau;; interp_sched (update_threads tid (ktr tt) threads, inr tt).
  Proof.
    rewrite bind_trigger. apply interp_sched_yield_vis.
  Qed.

  Lemma interp_sched_pick_vis
        R (threads: @threads R)
    :
    interp_sched (threads, inr tt)
    =
      Vis (inl1 (Choose tids.(id)))
          (fun t => match threads_pop t threads with
                 | None => Vis (inl1 Undefined) (fun _ => tau;; interp_sched (threads, inr tt))
                 | Some (th, ths) =>
                     Vis (inl1 (Fair (sum_fmap_l (thread_fmap t))))
                         (fun _ => tau;; interp_sched (ths, inl (t, th)))
                 end).
  Proof.
    unfold interp_sched at 1. rewrite unfold_iter. rewrite bind_vis.
    apply observe_eta. ss. f_equal. extensionality t. grind.
  Qed.

  Lemma interp_sched_pick
        R (threads: @threads R)
    :
    interp_sched (threads, inr tt)
    =
      t <- trigger (inl1 (Choose tids.(id)));;
      match threads_pop t threads with
      | None => x <- trigger (inl1 Undefined);; tau;; interp_sched (threads, inr tt)
      | Some (th, ths) =>
          x <- trigger (inl1 (Fair (sum_fmap_l (thread_fmap t))));;
          tau;; interp_sched (ths, inl (t, th))
      end.
  Proof.
    rewrite interp_sched_pick_vis at 1. rewrite bind_trigger.
    apply observe_eta. ss. f_equal. extensionality t. des_ifs.
    - rewrite bind_trigger. reflexivity.
    - rewrite bind_trigger. reflexivity.
  Qed.


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

  Variable State: Type.
  Variable _Ident: ID.

  Definition interp_all
             {R}
             (st: State) (ths: @threads _Ident (sE State) R)
             tid (itr: itree ((_ +' cE) +' (sE State)) R) :
    itree (@eventE (id_sum tids _Ident)) R :=
    interp_state (st, interp_sched (ths, inl (tid, itr))).

End INTERP.


Section MOD.

  Variable mod: Mod.t.
  Let st := (Mod.st_init mod).
  Let Ident := (Mod.ident mod).
  Let main := ((Mod.funs mod) "main").


  Definition interp_mod (ths: @threads (Mod._ident mod) (sE (Mod.state mod)) Val):
    itree (@eventE Ident) Val :=
    interp_all st ths tid_main (main []).

End MOD.
