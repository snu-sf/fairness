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
  Let threads R := list (thread_id * thread R).
  
  Definition sched_fifo R0 : thread_id * list thread_id -> scheduler R0 R0 :=
    ITree.iter (fun '(tid, q) =>
                  r <- ITree.trigger (inl1 (Execute _ tid));;
                  match r with
                  | None =>
                      match q ++ [tid] with
                      | [] => Vis (inr1 (Choose void)) (Empty_set_rect _)
                      | tid' :: q' => Ret (inl (tid', q'))
                      end
                  | Some r =>
                      match q with
                      | [] => Ret (inr r)
                      | tid' :: q' => Ret (inl (tid', q'))
                      end
                  end).

  Lemma unfold_sched_fifo R0 tid q :
    sched_fifo _ (tid, q) =
      r <- ITree.trigger (inl1 (Execute _ tid));;
      match r with
      | None =>
          match q ++ [tid] with
          | [] => Vis (inr1 (Choose void)) (Empty_set_rect _)
          | tid' :: q' => tau;; sched_fifo R0 (tid', q')
          end
      | Some r =>
          match q with
          | [] => Ret r
          | tid' :: q' => tau;; sched_fifo R0 (tid', q')
          end
      end.
  Proof.
    unfold sched_fifo at 1.
    rewrite unfold_iter.
    grind.
    eapply observe_eta. ss. f_equal. extensionality x. ss.
  Qed.

End SCHEDULE.

Section INTERP.

  Variable State : Type.
  Variable _Ident : ID.
  Let eventE2 := @eventE (sum_tid _Ident).

  Definition interp_all_fifo
    {R} st (ths: @threads _Ident (sE State) R) tid : itree (@eventE (sum_tid _Ident)) R :=
    interp_state (st, interp_sched (ths, sched_fifo _ (tid, TIdSet.elements (TIdSet.remove tid (key_set ths))))).

End INTERP.
