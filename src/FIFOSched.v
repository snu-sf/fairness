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

  Definition pick_thread_fifo {R} :
    tids.(id) * (thread E R + R) -> threads E R ->
    itree (eventE2 +' E) (tids.(id) * thread E R * threads E R + R) :=
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

  Definition interp_fifosched {R} := @interp_sched_aux _ E (@pick_thread_fifo) R.

  Lemma pick_thread_fifo_yield {R} tid (t : thread E R) ts :
    pick_thread_fifo (tid, inl t) ts =
      match (ts ++ [(tid, t)]) with
      | [] => Vis (inl1 (Choose void)) (Empty_set_rect _)
      | t' :: ts' => Ret (inl (t', ts'))
      end.
  Proof. ss. Qed.

  Lemma pick_thread_fifo_terminate {R} tid (r : R) ts :
    pick_thread_fifo (tid, inr r) ts =
      match ts with
      | [] => Ret (inr r)
      | t' :: ts' => Ret (inl (t', ts'))
      end.
  Proof. ss. Qed.

  Lemma unfold_interp_fifosched {R} tid (t : itree Es R) ts :
    interp_fifosched (tid, t, ts) =
      res <- interp_thread (tid, t);;
      yr <- pick_thread_fifo (tid, res) ts;;
      match yr with
      | inl y => tau;; interp_fifosched y
      | inr r => Ret r
      end.
  Proof. apply unfold_interp_sched_aux. Qed.

End SCHEDULE.
