From sflib Require Import sflib.
Require Import Program.
From ExtLib Require Import FMapAList.
From Fairness Require Import
  Mod
  Concurrency.
Import List.
Import ListNotations.
Set Implicit Arguments.

Section SCHEDULE.

  Context {_Ident : ID}.
  Variable E : Type -> Type.

  Let eventE2 := @eventE (sum_tids _Ident).
  Let Es := (eventE2 +' cE) +' E.

  Definition interp_thread_nonpreemtive {R} :
    tids.(id) * itree Es R -> itree (eventE2 +' E) (itree Es R + R).
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
  
  Definition pick_thread_fifo {R} :
    tids.(id) * (itree Es R + R) ->
    alist tids.(id) (itree Es R) ->
    itree (eventE2 +' E) (tids.(id) * itree Es R * alist tids.(id) (itree Es R) + R) :=
    fun '(tid, res) ts =>
      match res with
      | inl t => match (ts ++ [(tid, t)]) with
                | [] => Vis (inl1 (Choose void)) (Empty_set_rect _)
                | t' :: ts' => Ret (inl (t', ts'))
                end
      | inr r => match ts with
                | [] => Ret (inr r)
                | t' :: ts' => Ret (inl (t', ts'))
                end
      end.

  Definition interp_fifosched {R} :
    tids.(id) * itree Es R * alist tids.(id) (itree Es R) -> itree (eventE2 +' E) R :=
    ITree.iter (fun '(t,ts) =>
                  res <- interp_thread_nonpreemtive t;;
                  pick_thread_fifo (fst t, res) ts
      ).

  Lemma unfold_interp_fifosched {R} tid (t : itree Es R) ts :
    interp_fifosched (tid, t, ts) =
      res <- interp_thread_nonpreemtive (tid, t);;
      yr <- pick_thread_fifo (tid, res) ts;;
      match yr with
      | inl y => tau;; interp_fifosched y
      | inr r => Ret r
      end.
  Proof.
    unfold interp_fifosched at 1, curry.
    rewrite unfold_iter at 1. rewrite bind_bind.
    reflexivity.
  Qed.

  Lemma interp_thread_nonpreemtive_ret {R} tid (r : R) :
    interp_thread_nonpreemtive (tid, Ret r) = Ret (inr r).
  Proof. unfold interp_thread_nonpreemtive. rewrite unfold_iter. ss. rewrite bind_ret_l. ss. Qed.

  Lemma interp_thread_nonpreemtive_tau R tid (itr : itree Es R) :
    interp_thread_nonpreemtive (tid, tau;; itr) = tau;; interp_thread_nonpreemtive (tid, itr).
  Proof. unfold interp_thread_nonpreemtive at 1. rewrite unfold_iter. ss. rewrite bind_ret_l. ss. Qed.

  Lemma interp_thread_nonpreemtive_vis R tid X (e : E X) (ktr : ktree Es X R) :
    interp_thread_nonpreemtive (tid, Vis (inr1 e) ktr) =
      Vis (inr1 e) (fun x => tau;; interp_thread_nonpreemtive (tid, ktr x)).
  Proof.
    unfold interp_thread_nonpreemtive at 1. rewrite unfold_iter. ss. rewrite bind_vis.
    eapply (f_equal (fun x => Vis (inr1 e) x)). extensionality x.
    rewrite bind_ret_l. ss.
  Qed.

  Lemma interp_thread_nonpreemtive_trigger R tid X (e : E X) (ktr : ktree Es X R) :
    interp_thread_nonpreemtive (tid, x <- trigger (inr1 e);; ktr x) =
      x <- trigger (inr1 e);; tau;; interp_thread_nonpreemtive (tid, ktr x).
  Proof. rewrite ! bind_trigger. eapply interp_thread_nonpreemtive_vis. Qed.

  Lemma interp_thread_nonpreemtive_vis_eventE R tid X (e : eventE2 X) (ktr : ktree Es X R) :
    interp_thread_nonpreemtive (tid, Vis (inl1 (inl1 e)) ktr) =
      Vis (inl1 e) (fun x => tau;; interp_thread_nonpreemtive (tid, ktr x)).
  Proof.
    unfold interp_thread_nonpreemtive at 1. rewrite unfold_iter. ss. rewrite bind_vis.
    eapply (f_equal (fun x => Vis (inl1 e) x)). extensionality x.
    rewrite bind_ret_l. ss.
  Qed.

  Lemma interp_thread_nonpreemtive_trigger_eventE R tid X (e : eventE2 X) (ktr : ktree Es X R) :
    interp_thread_nonpreemtive (tid, x <- trigger (inl1 (inl1 e));; ktr x) =
      x <- trigger (inl1 e);; tau;; interp_thread_nonpreemtive (tid, ktr x).
  Proof. rewrite ! bind_trigger. eapply interp_thread_nonpreemtive_vis_eventE. Qed.

  Lemma interp_thread_nonpreemtive_vis_gettid R tid (ktr : ktree Es tids.(id) R) :
    interp_thread_nonpreemtive (tid, Vis (inl1 (inr1 GetTid)) ktr) =
      tau;; interp_thread_nonpreemtive (tid, ktr tid).
  Proof.
    unfold interp_thread_nonpreemtive at 1. rewrite unfold_iter. ss. rewrite bind_ret_l. ss.
  Qed.

  Lemma interp_thread_nonpreemtive_trigger_gettid R tid (ktr : ktree Es tids.(id) R) :
    interp_thread_nonpreemtive (tid, x <- trigger (inl1 (inr1 GetTid));; ktr x) =
      tau;; interp_thread_nonpreemtive (tid, ktr tid).
  Proof. rewrite bind_trigger. eapply interp_thread_nonpreemtive_vis_gettid. Qed.

  Lemma interp_thread_nonpreemtive_vis_yield R tid (ktr : ktree Es () R) :
    interp_thread_nonpreemtive (tid, Vis (inl1 (inr1 Yield)) ktr) =
      Ret (inl (ktr tt)).
  Proof.
    unfold interp_thread_nonpreemtive at 1. rewrite unfold_iter. ss. rewrite bind_ret_l. ss.
  Qed.

  Lemma interp_thread_nonpreemtive_trigger_yield R tid (ktr : ktree Es () R) :
    interp_thread_nonpreemtive (tid, x <- trigger (inl1 (inr1 Yield));; ktr x) =
      Ret (inl (ktr tt)).
  Proof. rewrite bind_trigger. apply interp_thread_nonpreemtive_vis_yield. Qed.

End SCHEDULE.
