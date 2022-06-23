Require Import Program.
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
  
  Definition interp_fifosched {R} :
    @threads _ E R -> itree (eventE2 +' E) ().
  Proof.
    eapply ITree.iter.
    intros [| [tid t] ts].
    - (* No thread to execute *)
      exact (Ret (inr tt)).
    - eapply ITree.bind.
      + eapply (interp_thread_nonpreemtive (tid, t)).
      + intros [t' | r].
        * (* thread t yielded *)
          exact (Ret (inl (ts ++ [(tid, t')]))).
        * (* thread t terminated with r *)
          exact (Ret (inl ts)).
  Defined.

End SCHEDULE.
