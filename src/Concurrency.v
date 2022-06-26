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



Definition alist_pop (K : Type) (R : K -> K -> Prop) (DEC: RelDec.RelDec R) (V: Type)
  : K -> alist K V -> option (prod V (alist K V)) :=
  fun k l => match alist_find DEC k l with
          | None => None
          | Some v => Some (v, alist_remove DEC k l)
          end.

Section SCHEDULE.

  Context {_Ident: ID}.
  Variable E: Type -> Type.

  Let eventE2 := @eventE (sum_tids _Ident).
  Let Es := (eventE2 +' cE) +' E.

  Definition thread R := itree Es R.
  Definition threads R := alist tids.(id) (@thread R).

  Definition threads_add := alist_add (RelDec.RelDec_from_dec eq tid_dec).
  Definition threads_find := alist_find (RelDec.RelDec_from_dec eq tid_dec).
  Definition threads_remove := alist_remove (RelDec.RelDec_from_dec eq tid_dec).
  Definition threads_pop := alist_pop (RelDec.RelDec_from_dec eq tid_dec).

  Definition interp_thread {R} :
    tids.(id) * thread R -> itree (eventE2 +' E) (thread R + R).
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
      + (* eventE2 *)
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

  Definition interp_sched_aux
    (pick_thread : forall {R}, tids.(id) * (thread R + R) -> threads R ->
                          itree (eventE2 +' E) (tids.(id) * thread R * threads R + R))
    {R}
    :
    tids.(id) * thread R * threads R -> itree (eventE2 +' E) R :=
    ITree.iter (fun '(t, ts) =>
                  res <- interp_thread t;;
                  pick_thread (fst t, res) ts
      ).

  (* NB for invalid tid *)
  Definition pick_thread_nondet {R} :
    tids.(id) * (thread R + R) -> threads R ->
    itree (eventE2 +' E) (tids.(id) * thread R * threads R + R) :=
    fun '(tid, res) ts =>
      match res with
      | inl t => Vis (inl1 (Choose tids.(id)))
                  (fun tid' =>
                     match threads_pop tid' (threads_add tid t ts) with
                     | None => Vis (inl1 (Choose void)) (Empty_set_rect _)
                     | Some (t', ts') => Vis (inl1 (Fair (sum_fmap_l (thread_fmap tid'))))
                                          (fun _ => Ret (inl (tid', t', ts')))
                     end)
      | inr r => match ts with
                | [] => Ret (inr r)
                | _ => Vis (inl1 (Choose tids.(id)))
                        (fun tid' =>
                           match threads_pop tid' ts with
                           | None => Vis (inl1 (Choose void)) (Empty_set_rect _)
                           | Some (t', ts') => Vis (inl1 (Fair (sum_fmap_l (thread_fmap tid'))))
                                                (fun _ => Ret (inl (tid', t', ts')))
                           end)
                end
      end.

  Definition interp_sched {R} :
    tids.(id) * thread R * threads R -> itree (eventE2 +' E) R :=
    @interp_sched_aux (@pick_thread_nondet) R.

  (* Lemmas for interp_thread *)
  Lemma interp_thread_ret {R} tid (r : R) :
    interp_thread (tid, Ret r) = Ret (inr r).
  Proof. unfold interp_thread. rewrite unfold_iter. ss. rewrite bind_ret_l. ss. Qed.

  Lemma interp_thread_tau R tid (itr : thread R) :
    interp_thread (tid, tau;; itr) = tau;; interp_thread (tid, itr).
  Proof. unfold interp_thread at 1. rewrite unfold_iter. ss. rewrite bind_ret_l. ss. Qed.

  Lemma interp_thread_vis R tid X (e : E X) (ktr : ktree Es X R) :
    interp_thread (tid, Vis (inr1 e) ktr) =
      Vis (inr1 e) (fun x => tau;; interp_thread (tid, ktr x)).
  Proof.
    unfold interp_thread at 1. rewrite unfold_iter. ss. rewrite bind_vis.
    eapply (f_equal (fun x => Vis (inr1 e) x)). extensionality x.
    rewrite bind_ret_l. ss.
  Qed.

  Lemma interp_thread_trigger R tid X (e : E X) (ktr : ktree Es X R) :
    interp_thread (tid, x <- trigger (inr1 e);; ktr x) =
      x <- trigger (inr1 e);; tau;; interp_thread (tid, ktr x).
  Proof. rewrite ! bind_trigger. eapply interp_thread_vis. Qed.

  Lemma interp_thread_vis_eventE R tid X (e : eventE2 X) (ktr : ktree Es X R) :
    interp_thread (tid, Vis (inl1 (inl1 e)) ktr) =
      Vis (inl1 e) (fun x => tau;; interp_thread (tid, ktr x)).
  Proof.
    unfold interp_thread at 1. rewrite unfold_iter. ss. rewrite bind_vis.
    eapply (f_equal (fun x => Vis (inl1 e) x)). extensionality x.
    rewrite bind_ret_l. ss.
  Qed.

  Lemma interp_thread_trigger_eventE R tid X (e : eventE2 X) (ktr : ktree Es X R) :
    interp_thread (tid, x <- trigger (inl1 (inl1 e));; ktr x) =
      x <- trigger (inl1 e);; tau;; interp_thread (tid, ktr x).
  Proof. rewrite ! bind_trigger. eapply interp_thread_vis_eventE. Qed.

  Lemma interp_thread_vis_gettid R tid (ktr : ktree Es tids.(id) R) :
    interp_thread (tid, Vis (inl1 (inr1 GetTid)) ktr) =
      tau;; interp_thread (tid, ktr tid).
  Proof.
    unfold interp_thread at 1. rewrite unfold_iter. ss. rewrite bind_ret_l. ss.
  Qed.

  Lemma interp_thread_trigger_gettid R tid (ktr : ktree Es tids.(id) R) :
    interp_thread (tid, x <- trigger (inl1 (inr1 GetTid));; ktr x) =
      tau;; interp_thread (tid, ktr tid).
  Proof. rewrite bind_trigger. eapply interp_thread_vis_gettid. Qed.

  Lemma interp_thread_vis_yield R tid (ktr : ktree Es () R) :
    interp_thread (tid, Vis (inl1 (inr1 Yield)) ktr) =
      Ret (inl (ktr tt)).
  Proof.
    unfold interp_thread at 1. rewrite unfold_iter. ss. rewrite bind_ret_l. ss.
  Qed.

  Lemma interp_thread_trigger_yield R tid (ktr : ktree Es () R) :
    interp_thread (tid, x <- trigger (inl1 (inr1 Yield));; ktr x) =
      Ret (inl (ktr tt)).
  Proof. rewrite bind_trigger. apply interp_thread_vis_yield. Qed.

  (* Lemmas for pick_thread_nondet *)
  Lemma pick_thread_nondet_yield {R} tid (t : thread R) ts :
    pick_thread_nondet (tid, (inl t)) ts =
      Vis (inl1 (Choose tids.(id)))
        (fun tid' =>
           match threads_pop tid' (threads_add tid t ts) with
           | None => Vis (inl1 (Choose void)) (Empty_set_rect _)
           | Some (t', ts') => Vis (inl1 (Fair (sum_fmap_l (thread_fmap tid'))))
                                (fun _ => Ret (inl (tid', t', ts')))
           end).
  Proof. ss. Qed.

  Lemma pick_thread_nondet_terminate {R} tid (r : R) ts :
    pick_thread_nondet (tid, (inr r)) ts =
      match ts with
      | [] => Ret (inr r)
      | _ => Vis (inl1 (Choose tids.(id)))
              (fun tid' =>
                 match threads_pop tid' ts with
                 | None => Vis (inl1 (Choose void)) (Empty_set_rect _)
                 | Some (t', ts') => Vis (inl1 (Fair (sum_fmap_l (thread_fmap tid'))))
                                      (fun _ => Ret (inl (tid', t', ts')))
                 end)
      end.
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

Section INTERP.

  Variable State: Type.
  Variable _Ident: ID.

  Definition interp_all
             {R}
             (st: State) (ths: @threads _Ident (sE State) R)
             tid (itr: @thread _Ident (sE State) R) :
    itree (@eventE (sum_tids _Ident)) R :=
    interp_state (st, interp_sched (tid, itr, ths)).

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
