From sflib Require Import sflib.
From ITree Require Export ITree.
From Paco Require Import paco.

Require Export Coq.Strings.String.
Require Import Program.
Require Import Permutation.

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



Section ALISTAUX.

  Definition alist_pop (K : Type) (R : K -> K -> Prop) (DEC: RelDec.RelDec R) (V: Type)
    : K -> alist K V -> option (prod V (alist K V)) :=
    fun k l => match alist_find DEC k l with
            | None => None
            | Some v => Some (v, alist_remove DEC k l)
            end.

  Definition alist_proj1 K V (a: alist K V): list K := List.map fst a.
  Definition alist_proj2 K V (a: alist K V): list V := List.map snd a.

  Definition alist_proj_v1 K V1 V2 (a: alist K (prod V1 V2)): alist K V1 := List.map (fun '(k, (v1, v2)) => (k, v1)) a.
  Definition alist_proj_v2 K V1 V2 (a: alist K (prod V1 V2)): alist K V2 := List.map (fun '(k, (v1, v2)) => (k, v2)) a.

  Definition alist_wf (K : Type) (V: Type) : alist K V -> Prop :=
    fun l => List.NoDup (alist_proj1 l).


  Lemma alist_pop_find_none
        K V R (DEC: RelDec.RelDec R)
        (CORRECT: RelDec.RelDec_Correct DEC)
        (a a0: alist K V) k v
        (POP: alist_pop DEC k a = Some (v, a0))
    :
    alist_find DEC k a0 = None.
  Proof.
    unfold alist_pop in POP. des_ifs. eapply remove_eq_alist. auto.
  Qed.

  Lemma alist_pop_find_some
        K V R (DEC: RelDec.RelDec R)
        (a a0: alist K V) k v
        (POP: alist_pop DEC k a = Some (v, a0))
    :
    alist_find DEC k a = Some v.
  Proof.
    unfold alist_pop in POP. des_ifs.
  Qed.


  Lemma alist_wf_perm_pop_cases
        K V R (DEC: RelDec.RelDec R)
        (CORRECT: RelDec.RelDec_Correct DEC)
        (a0 a1: alist K V)
        (PERM: Permutation a0 a1)
        (WF0: alist_wf a0)
    :
    forall k, ((alist_pop DEC k a0 = None) /\ (alist_pop DEC k a1 = None)) \/
           (exists v a2 a3, (alist_pop DEC k a0 = Some (v, a2)) /\
                         (alist_pop DEC k a1 = Some (v, a3)) /\
                         (Permutation a2 a3) /\ (alist_wf a2)).
  Proof.
    i. revert_until PERM. induction PERM; i; ss.
    { left. ss. }
    { inv WF0. specialize (IHPERM H2 k). des.
      { destruct x as [k0 v0]. destruct (RelDec.rel_dec k k0) eqn:EQ.
        { right. unfold alist_pop. ss. rewrite RelDec.rel_dec_eq_true; auto.
          2: apply RelDec.rel_dec_correct; auto. ss. esplits; eauto.
          admit.
          unfold alist_wf. admit.
        }
        { left. unfold alist_pop. ss. rewrite RelDec.rel_dec_neq_false; auto.
          2: apply RelDec.neg_rel_dec_correct; auto. ss.
          unfold alist_pop in *. des_ifs; ss.
        }
      }
      { destruct x as [k0 v0]. destruct (RelDec.rel_dec k k0) eqn:EQ.
        { right. unfold alist_pop. ss. rewrite RelDec.rel_dec_eq_true; auto.
          2: apply RelDec.rel_dec_correct; auto. ss. esplits; eauto.
          admit.
          unfold alist_wf. admit.
        }
        { right. unfold alist_pop. ss. rewrite ! RelDec.rel_dec_neq_false; auto.
          2: apply RelDec.neg_rel_dec_correct; auto. ss.
          unfold alist_pop in *. des_ifs; ss.
          esplits; eauto. unfold alist_wf. ss.
          eapply List.NoDup_cons.
          - ii. apply H1; clear H1. admit.
          - admit.
        }
      }
    }
    { admit. }
    { assert (WF1: alist_wf l').
      { admit. }
      specialize (IHPERM1 WF0 k). specialize (IHPERM2 WF1 k). des; clarify; eauto.
      right. esplits; eauto. eapply perm_trans; eauto.
    }
  Admitted.

End ALISTAUX.


Notation thread _Id E R := (itree (((@eventE _Id) +' cE) +' E) R).
Notation threads _Id E R := ((alist tids.(id) (@thread _Id E R))).

Definition threads_add := alist_add (RelDec.RelDec_from_dec eq tid_dec).
Definition threads_find := alist_find (RelDec.RelDec_from_dec eq tid_dec).
Definition threads_remove := alist_remove (RelDec.RelDec_from_dec eq tid_dec).
Definition threads_pop := alist_pop (RelDec.RelDec_from_dec eq tid_dec).
Definition threads_ids := @alist_proj1 tids.(id).
Definition threads_wf := @alist_wf tids.(id).


Section SCHEDULE.

  Context {_Ident: ID}.
  Variable E: Type -> Type.

  Let eventE1 := @eventE _Ident.
  Let eventE2 := @eventE (sum_tids _Ident).

  Definition embed_eventE X (e: eventE1 X): eventE2 X.
  Proof.
    destruct e. exact (Choose X). exact (Fair (sum_fmap_r m)). exact (Observe fn args). exact Undefined.
  Defined.

  Let Es0 := (eventE1 +' cE) +' E.

  Let thread R := thread _Ident E R.
  Let threads R := threads _Ident E R.

  (* Definition thread R := (itree Es0 R). *)
  (* Definition threads R := (alist tids.(id) (@thread R)). *)

  (* Definition threads_add := alist_add (RelDec.RelDec_from_dec eq tid_dec). *)
  (* Definition threads_find := alist_find (RelDec.RelDec_from_dec eq tid_dec). *)
  (* Definition threads_remove := alist_remove (RelDec.RelDec_from_dec eq tid_dec). *)
  (* Definition threads_pop := alist_pop (RelDec.RelDec_from_dec eq tid_dec). *)
  (* Definition threads_ids := @alist_proj1 tids.(id). *)
  (* Definition threads_wf := @alist_wf tids.(id). *)

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
        exact (Vis (inl1 (embed_eventE e)) (fun x => Ret (inl (tid, k x)))).
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

  Lemma interp_thread_vis R tid X (e : E X) (ktr : ktree Es0 X R) :
    interp_thread (tid, Vis (inr1 e) ktr) =
      Vis (inr1 e) (fun x => tau;; interp_thread (tid, ktr x)).
  Proof.
    unfold interp_thread at 1. rewrite unfold_iter. ss. rewrite bind_vis.
    eapply (f_equal (fun x => Vis (inr1 e) x)). extensionality x.
    rewrite bind_ret_l. ss.
  Qed.

  Lemma interp_thread_trigger R tid X (e : E X) (ktr : ktree Es0 X R) :
    interp_thread (tid, x <- trigger (inr1 e);; ktr x) =
      x <- trigger (inr1 e);; tau;; interp_thread (tid, ktr x).
  Proof. rewrite ! bind_trigger. eapply interp_thread_vis. Qed.

  Lemma interp_thread_vis_eventE R tid X (e : eventE1 X) (ktr : ktree Es0 X R) :
    interp_thread (tid, Vis (inl1 (inl1 e)) ktr) =
      Vis (inl1 (embed_eventE e)) (fun x => tau;; interp_thread (tid, ktr x)).
  Proof.
    unfold interp_thread at 1. rewrite unfold_iter. ss. rewrite bind_vis.
    eapply (f_equal (fun x => Vis (inl1 (embed_eventE e)) x)). extensionality x.
    rewrite bind_ret_l. ss.
  Qed.

  Lemma interp_thread_trigger_eventE R tid X (e : eventE1 X) (ktr : ktree Es0 X R) :
    interp_thread (tid, x <- trigger (inl1 (inl1 e));; ktr x) =
      x <- trigger (inl1 (embed_eventE e));; tau;; interp_thread (tid, ktr x).
  Proof. rewrite ! bind_trigger. eapply interp_thread_vis_eventE. Qed.

  Lemma interp_thread_vis_gettid R tid (ktr : ktree Es0 tids.(id) R) :
    interp_thread (tid, Vis (inl1 (inr1 GetTid)) ktr) =
      tau;; interp_thread (tid, ktr tid).
  Proof.
    unfold interp_thread at 1. rewrite unfold_iter. ss. rewrite bind_ret_l. ss.
  Qed.

  Lemma interp_thread_trigger_gettid R tid (ktr : ktree Es0 tids.(id) R) :
    interp_thread (tid, x <- trigger (inl1 (inr1 GetTid));; ktr x) =
      tau;; interp_thread (tid, ktr tid).
  Proof. rewrite bind_trigger. eapply interp_thread_vis_gettid. Qed.

  Lemma interp_thread_vis_yield R tid (ktr : ktree Es0 () R) :
    interp_thread (tid, Vis (inl1 (inr1 Yield)) ktr) =
      Ret (inl (ktr tt)).
  Proof.
    unfold interp_thread at 1. rewrite unfold_iter. ss. rewrite bind_ret_l. ss.
  Qed.

  Lemma interp_thread_trigger_yield R tid (ktr : ktree Es0 () R) :
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



Section SCHEDAUX.

  Context {_Ident: ID}.
  Variable E: Type -> Type.

  Lemma ths_find_none_tid_add
        R (ths: threads _Ident E R) tid
        (NONE: threads_find tid ths = None)
    :
    tid_list_add (alist_proj1 ths) tid (tid :: (alist_proj1 ths)).
  Proof.
    revert_until ths. induction ths; i; ss.
    { econs; ss. }
    des_ifs. ss. destruct (tid_dec tid n) eqn:TID.
    { clarify. eapply RelDec.neg_rel_dec_correct in Heq. ss. }
    eapply IHths in NONE. inv NONE. econs; ss.
    eapply List.not_in_cons. split; auto.
  Qed.

  Lemma ths_pop_find_none
        R (ths ths0: threads _Ident E R) th tid
        (POP: threads_pop tid ths = Some (th, ths0))
    :
    threads_find tid ths0 = None.
  Proof. eapply alist_pop_find_none; eauto. eapply reldec_correct_tid_dec. Qed.

  Lemma ths_pop_find_some
        R (ths ths0: threads _Ident E R) th tid
        (POP: threads_pop tid ths = Some (th, ths0))
    :
    threads_find tid ths = Some th.
  Proof. eapply alist_pop_find_some; eauto. Qed.

  Lemma ths_find_some_tid_in
        R (ths: threads _Ident E R) tid th
        (FIND: threads_find tid ths = Some th)
    :
    tid_list_in tid (alist_proj1 ths).
  Proof.
    revert_until ths. induction ths; i; ss. des_ifs; ss.
    - left. symmetry. eapply RelDec.rel_dec_correct. eauto.
    - right. eapply IHths. eauto.
      Unshelve. eapply reldec_correct_tid_dec.
  Qed.

  Lemma ths_wf_perm_pop_cases
        R (ths0 ths1: threads _Ident E R)
        (PERM: Permutation ths0 ths1)
        (WF0: threads_wf ths0)
    :
    forall x, ((threads_pop x ths0 = None) /\ (threads_pop x ths1 = None)) \/
           (exists th ths2 ths3, (threads_pop x ths0 = Some (th, ths2)) /\
                              (threads_pop x ths1 = Some (th, ths3)) /\
                              (Permutation ths2 ths3) /\ (threads_wf ths2)).
  Proof. eapply alist_wf_perm_pop_cases; eauto. eapply reldec_correct_tid_dec. Qed.


  Ltac gfold := gfinal; right; pfold.

  Lemma interp_all_perm_equiv
        R tid th (ths0 ths1: @threads _Ident E R)
        (PERM: Permutation ths0 ths1)
        (WF: threads_wf ths0)
    :
    eq_itree (@eq R) (interp_sched (tid, th, ths0)) (interp_sched (tid, th, ths1)).
  Proof.
    ginit. revert_until R. gcofix CIH. i.
    rewrite ! unfold_interp_sched.
    destruct (observe th) eqn:T; (symmetry in T; eapply simpobs in T; eapply bisim_is_eq in T); clarify.
    { rewrite ! interp_thread_ret. rewrite ! bind_ret_l.
      rewrite ! pick_thread_nondet_terminate. destruct ths0.
      { hexploit Permutation_nil; eauto. i; clarify. ired. gfold. econs; eauto. }
      destruct ths1.
      { eapply Permutation_sym in PERM. hexploit Permutation_nil; eauto. i; clarify. }
      ired. rewrite <- ! bind_trigger. guclo eqit_clo_bind. econs. reflexivity. i; clarify.
      hexploit (ths_wf_perm_pop_cases PERM WF u2). i; des.
      { ss. rewrite H, H0. clear H H0. ired. guclo eqit_clo_bind. econs. reflexivity. i. destruct u1. }
      ss. rewrite H, H0. ired.
      rewrite <- ! bind_trigger. guclo eqit_clo_bind. econs. reflexivity. i; clarify. destruct u0; ss.
      gfold. econs 2. right. eapply CIH; eauto.
    }
    { rewrite ! interp_thread_tau. rewrite ! bind_tau. gfold. econs 2. right.
      rewrite <- ! unfold_interp_sched. eauto.
    }
    { destruct e as [[eev | cev] | ev].
      { rewrite interp_thread_vis_eventE. rewrite ! bind_vis.
        rewrite <- ! bind_trigger. guclo eqit_clo_bind. econs. reflexivity. i; clarify.
        rewrite ! bind_tau. gfold. econs 2. right.
        rewrite <- ! unfold_interp_sched. eauto.
      }
      2:{ rewrite interp_thread_vis. rewrite ! bind_vis.
          rewrite <- ! bind_trigger. guclo eqit_clo_bind. econs. reflexivity. i; clarify.
          rewrite ! bind_tau. gfold. econs 2. right.
          rewrite <- ! unfold_interp_sched. eauto.
      }
      destruct cev.
      { rewrite interp_thread_vis_yield. rewrite ! bind_ret_l.
        rewrite ! pick_thread_nondet_yield. rewrite <- ! bind_trigger. rewrite ! bind_bind.
        guclo eqit_clo_bind. econs. reflexivity. i; clarify.
        assert (PERM0: Permutation (threads_add tid (k ()) ths0) (threads_add tid (k ()) ths1)).
        { admit. }
        assert (WF0: threads_wf (threads_add tid (k ()) ths0)).
        { admit. }
        hexploit (ths_wf_perm_pop_cases PERM0 WF0 u2). i; des.
        { ss. rewrite H, H0. clear H H0. ired. guclo eqit_clo_bind. econs. reflexivity. i. destruct u1. }
        ss. rewrite H, H0. ired.
        rewrite <- ! bind_trigger. guclo eqit_clo_bind. econs. reflexivity. i; clarify. destruct u0; ss.
        gfold. econs 2. right. eapply CIH; eauto.
      }
      { rewrite interp_thread_vis_gettid. rewrite ! bind_tau. gfold. econs 2. right.
        rewrite <- ! unfold_interp_sched. eauto.
      }
    }
  Admitted.

End SCHEDAUX.


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

  Definition interp_mod (ths: @threads (Mod.ident mod) (sE (Mod.state mod)) Val):
    itree (@eventE (sum_tids Ident)) Val :=
    interp_all st ths tid_main (main []).

End MOD.
