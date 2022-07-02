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

  Let eventE1 := @eventE _Ident.
  Let eventE2 := @eventE (sum_tid _Ident).
  Let Es := (eventE1 +' cE) +' E.

  Let thread R := thread _Ident E R.
  Let threads R := list (thread_id.(id) * thread R).
  
  Definition pick_thread_fifo {R} :
    thread_id.(id) * (thread R + R) -> threads R ->
    itree (eventE2 +' E) (thread_id.(id) * thread R * threads R + R) :=
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

  Definition interp_fifosched {R} : thread_id.(id) * thread R * threads R -> itree (eventE2 +' E) R :=
    ITree.iter (fun '(t, ts) =>
                  res <- interp_thread t;;
                  pick_thread_fifo (fst t, res) ts
      ).

  Lemma pick_thread_fifo_yield {R} tid (t : thread R) ts :
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
  Proof. unfold interp_fifosched at 1. rewrite unfold_iter, bind_bind. ss. Qed.

End SCHEDULE.

Global Opaque
  pick_thread_fifo.

Section INTERP.

  Variable State : Type.
  Variable _Ident : ID.
  Let eventE2 := @eventE (sum_tid _Ident).

  Definition interp_all_fifo
    {R}
    (st : State) (ths : list (thread_id.(id) * thread _Ident (sE State) R))
    tid (itr : @thread _Ident (sE State) R) :
    itree eventE2 R :=
    interp_state (st, interp_fifosched (tid, itr, ths)).

End INTERP.
