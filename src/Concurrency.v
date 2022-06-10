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

Section YIELD.

  Variable State: Type.

  Variant cE: Type -> Type :=
    | Yield (st: State): cE State
  .

  Definition Es := cE+'eventE.

  Definition thread {R} := stateT State (itree Es) R.
  Definition threads {R} := id -> @thread R.

  Definition update_threads {R} (tid: id) (k: thread) (ts: threads) : @threads R :=
    fun t => if (Tid_eq_dec tid t) then k else (ts t).

  Definition interp_yield {R}:
    ((@threads R) * ((id * itree Es (State * R)) + State)) -> itree eventE void.
  Proof.
    eapply ITree.iter. intros [threads [[tid itr]|]].
    - destruct (observe itr).
      + exact (Ret (inl (threads, inr (fst r)))).
      + exact (Ret (inl (threads, inl (tid, t)))).
      + destruct e.
        * destruct c. exact (Ret (inl (update_threads tid k threads, inr st))).
        * exact (Vis e (fun x => Ret (inl (threads, inl (tid, k x))))).
    - exact (Vis (Choose id) (fun tid => Ret (inl (threads, inl (tid, (threads tid s)))))).
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

  Lemma interp_yield_ret R (threads: @threads R) tid st r
    :
    interp_yield (threads, inl (tid, Ret (st, r))) = tau;; interp_yield (threads, inr st).
  Proof.
    unfold interp_yield. rewrite unfold_iter. ss. grind.
  Qed.

  Lemma interp_yield_tau R (threads: @threads R) tid itr
    :
    interp_yield (threads, inl (tid, tau;; itr)) = tau;; interp_yield (threads, inl (tid, itr)).
  Proof.
    unfold interp_yield. rewrite unfold_iter. ss. grind.
  Qed.

  Lemma interp_yield_yield_vis R (threads: @threads R) tid st k
    :
    interp_yield (threads, inl (tid, Vis (Yield st|)%sum k))
    =
      tau;; interp_yield (update_threads tid k threads, inr st).
  Proof.
    unfold interp_yield. rewrite unfold_iter. ss. grind.
  Qed.

  Lemma interp_yield_yield R (threads: @threads R) tid st k
    :
    interp_yield (threads, inl (tid, trigger (Yield st|)%sum >>= k))
    =
      tau;; interp_yield (update_threads tid k threads, inr st).
  Proof.
    rewrite bind_trigger. apply interp_yield_yield_vis.
  Qed.

  Lemma interp_yield_vis R (threads: @threads R) tid X (e: eventE X) k
    :
    interp_yield (threads, inl (tid, Vis (|e)%sum k))
    =
      Vis e (fun x => tau;; interp_yield (threads, inl (tid, k x))).
  Proof.
    unfold interp_yield. rewrite unfold_iter. ss. rewrite bind_vis.
    apply observe_eta. ss. f_equal. extensionality x.
    rewrite bind_ret_l. reflexivity.
  Qed.

  Lemma interp_yield_trigger R (threads: @threads R) tid X (e: eventE X) k
    :
    interp_yield (threads, inl (tid, trigger (|e)%sum >>= k))
    =
      x <- trigger e;; tau;; interp_yield (threads, inl (tid, k x)).
  Proof.
    rewrite ! bind_trigger. apply interp_yield_vis.
  Qed.

  Lemma interp_yield_pick_vis R (threads: @threads R) st
    :
    interp_yield (threads, inr st)
    =
      Vis (Choose id) (fun tid => tau;; interp_yield (threads, inl (tid, (threads tid st)))).
  (* Vis (Choose _ Tid) (fun tid => *)
  (*                     '(itr, threads) <- unwrapN (alist_pop tid threads);; *)
  (*                     tau;; interp_yield (threads, inl (tid, itr st))). *)
  Proof.
    unfold interp_yield. rewrite unfold_iter. rewrite bind_vis.
    apply observe_eta. ss. f_equal. extensionality x.
    grind.
    (* rewrite bind_bind. f_equal. extensionality r. destruct r; ss. *)
    (* rewrite bind_ret_l. refl. *)
  Qed.

  Lemma interp_yield_pick R (threads: @threads R) st
    :
    interp_yield (threads, inr st)
    =
      tid <- trigger (Choose id);;
      tau;; interp_yield (threads, inl (tid, threads tid st)).
  (* '(itr, threads) <- unwrapN (alist_pop tid threads);; *)
  (* tau;; interp_yield (threads, inl (tid, itr st)). *)
  Proof.
    rewrite bind_trigger. apply interp_yield_pick_vis.
  Qed.

  (* Lemma interp_yield_bind R (threads: alist Tid (stateT State (itree Es) R)) tid A (itr: itree Es A) ktr *)
  (*   : *)
  (*     interp_yield (threads, inl (tid, itr >>= ktr)) *)
  (*     = *)
  (*     ?? *)
  (* . *)
End YIELD.
