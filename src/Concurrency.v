From sflib Require Import sflib.
From ITree Require Export ITree.
From Paco Require Import paco.

Require Export Coq.Strings.String.
Require Import Program.
Require Import Permutation.

Export ITreeNotations.

From Fairness Require Export ITreeLib FairBeh.
From Fairness Require Import Mod.

(* From ExtLib Require Import FMapAList. *)
(* Require Import FSets.FMapList. *)
Require Import Coq.FSets.FMaps Coq.Structures.OrderedTypeEx.
Module Th := FMapList.Make(Nat_as_OT).

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

Ltac destruct_itree itr :=
  let E := fresh "E" in
  destruct (observe itr) eqn: E;
  let H := fresh "H" in
  pose proof (H := itree_eta_ itr);
  rewrite E in H;
  clear E;
  subst itr.

Section STATE.

  Variable State: Type.
  Variable E: Type -> Type.

  Let Es := E +' (sE State).

  Definition interp_state_aux {R} :
    (State * (itree Es R)) -> itree E (State * R).
  Proof.
    eapply ITree.iter. intros [state itr]. destruct (observe itr).
    - exact (Ret (inr (state, r))).
    - exact (Ret (inl (state, t))).
    - destruct e.
      + exact (Vis e (fun x => Ret (inl (state, k x)))).
      + destruct s.
        * exact (Ret (inl (st, k tt))).
        * exact (Ret (inl (state, k state))).
  Defined.

  Definition interp_state {R}:
    (State * (itree Es R)) -> itree E R :=
    fun x => r <- interp_state_aux x;;
          Ret (snd r).

  Lemma interp_state_aux_ret R st (r : R) :
    interp_state_aux (st, Ret r) = Ret (st, r).
  Proof. unfold interp_state_aux. rewrite unfold_iter. grind. Qed.

  Lemma interp_state_aux_vis R st X (e : E X) (ktr : ktree Es X R) :
    interp_state_aux (st, Vis (inl1 e) ktr) = Vis e (fun x => tau;; interp_state_aux (st, ktr x)).
  Proof. unfold interp_state_aux. rewrite unfold_iter. grind.
         apply observe_eta. ss. f_equal. extensionality x. grind.
  Qed.

  Lemma interp_state_aux_put R st st' (ktr : ktree Es unit R) :
    interp_state_aux (st, Vis (inr1 (Put st')) ktr) = tau;; interp_state_aux (st', ktr tt).
  Proof. unfold interp_state_aux. rewrite unfold_iter. grind. Qed.

  Lemma interp_state_aux_get R st (ktr : ktree Es State R) :
    interp_state_aux (st, Vis (inr1 (Get _)) ktr) = tau;; interp_state_aux (st, ktr st).
  Proof. unfold interp_state_aux. rewrite unfold_iter. grind. Qed.

  Lemma interp_state_aux_tau R st (itr : itree Es R) :
    interp_state_aux (st, Tau itr) = Tau (interp_state_aux (st, itr)).
  Proof. unfold interp_state_aux. rewrite unfold_iter. grind. Qed.

  Lemma interp_state_bind {R1} {R2} st (itr : itree Es R1) (ktr : ktree Es R1 R2) :
    interp_state_aux (st, itr >>= ktr) =
      x <- interp_state_aux (st, itr);;
      interp_state_aux (fst x, ktr (snd x)).
  Proof.
    eapply bisim_is_eq. revert st itr. pcofix CIH. i.
    destruct_itree itr.
    - rewrite interp_state_aux_ret. grind.
      eapply paco2_mon.
      + eapply eq_is_bisim. ss.
      + ss.
    - grind. rewrite 2 interp_state_aux_tau. grind.
      pfold. econs. right. eapply CIH.
    - grind. destruct e.
      + rewrite 2 interp_state_aux_vis. grind.
        pfold. econs. intros. grind. left.
        pfold. econs. right. eapply CIH.
      + destruct s.
        * rewrite 2 interp_state_aux_put. grind.
          pfold. econs. right. eapply CIH.
        * rewrite 2 interp_state_aux_get. grind.
          pfold. econs. right. eapply CIH.
  Qed.
 
  Lemma interp_state_ret
        R (r: R) (state: State)
    :
    interp_state (state, Ret r) = Ret r.
  Proof.
    unfold interp_state, interp_state_aux. rewrite unfold_iter. ss. grind.
  Qed.

  Lemma interp_state_tau
        R (state: State) (itr: itree Es R)
    :
    interp_state (state, tau;; itr) = tau;; interp_state (state, itr).
  Proof.
    unfold interp_state, interp_state_aux. rewrite unfold_iter. ss. grind.
  Qed.

  Lemma interp_state_put_vis
        R (state0 state1: State) (ktr: unit -> itree Es R)
    :
    interp_state (state0, Vis (inr1 (Put state1)) ktr)
    =
      tau;; interp_state (state1, ktr tt).
  Proof.
    unfold interp_state, interp_state_aux. rewrite unfold_iter. ss. grind.
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
    unfold interp_state, interp_state_aux. rewrite unfold_iter. ss. grind.
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
    unfold interp_state, interp_state_aux. rewrite unfold_iter. ss. rewrite 2 bind_vis.
    apply observe_eta. ss. f_equal. extensionality x.
    rewrite bind_ret_l. rewrite bind_tau. reflexivity.
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



(* Section ALISTAUX. *)

(*   Definition alist_pop (K : Type) (R : K -> K -> Prop) (DEC: RelDec.RelDec R) (V: Type) *)
(*     : K -> alist K V -> option (prod V (alist K V)) := *)
(*     fun k l => match alist_find DEC k l with *)
(*             | None => None *)
(*             | Some v => Some (v, alist_remove DEC k l) *)
(*             end. *)

(*   Definition alist_proj1 K V (a: alist K V): list K := List.map fst a. *)
(*   Definition alist_proj2 K V (a: alist K V): list V := List.map snd a. *)

(*   Definition alist_proj_v1 K V1 V2 (a: alist K (prod V1 V2)): alist K V1 := List.map (fun '(k, (v1, v2)) => (k, v1)) a. *)
(*   Definition alist_proj_v2 K V1 V2 (a: alist K (prod V1 V2)): alist K V2 := List.map (fun '(k, (v1, v2)) => (k, v2)) a. *)

(*   Definition alist_wf (K : Type) (V: Type) : alist K V -> Prop := *)
(*     fun l => List.NoDup (alist_proj1 l). *)

(*   Definition alist_wf_pair (K : Type) (V1 V2: Type) : alist K V1 -> alist K V2 -> Prop := *)
(*     fun a1 a2 => (<<WF: alist_wf a1>>) /\ (<<PERM: Permutation (alist_proj1 a1) (alist_proj1 a2)>>). *)


(*   Lemma alist_proj1_preserves_perm *)
(*         K V (a0 a1: alist K V) *)
(*         (PERM: Permutation a0 a1) *)
(*     : *)
(*     Permutation (alist_proj1 a0) (alist_proj1 a1). *)
(*   Proof. *)
(*     induction PERM; ss; eauto. *)
(*     - econs; eauto. *)
(*     - econs 4; eauto. *)
(*   Qed. *)

(*   Lemma alist_pop_find_none *)
(*         K V R (DEC: RelDec.RelDec R) *)
(*         (CORRECT: RelDec.RelDec_Correct DEC) *)
(*         (a a0: alist K V) k v *)
(*         (POP: alist_pop DEC k a = Some (v, a0)) *)
(*     : *)
(*     alist_find DEC k a0 = None. *)
(*   Proof. *)
(*     unfold alist_pop in POP. des_ifs. eapply remove_eq_alist. auto. *)
(*   Qed. *)

(*   Lemma alist_pop_find_some *)
(*         K V R (DEC: RelDec.RelDec R) *)
(*         (a a0: alist K V) k v *)
(*         (POP: alist_pop DEC k a = Some (v, a0)) *)
(*     : *)
(*     alist_find DEC k a = Some v. *)
(*   Proof. *)
(*     unfold alist_pop in POP. des_ifs. *)
(*   Qed. *)


(*   Lemma alist_wf_perm_pop_cases *)
(*         K V R (DEC: RelDec.RelDec R) *)
(*         (CORRECT: RelDec.RelDec_Correct DEC) *)
(*         (a0 a1: alist K V) *)
(*         (PERM: Permutation a0 a1) *)
(*         (WF0: alist_wf a0) *)
(*     : *)
(*     forall k, ((alist_pop DEC k a0 = None) /\ (alist_pop DEC k a1 = None)) \/ *)
(*            (exists v a2 a3, (alist_pop DEC k a0 = Some (v, a2)) /\ *)
(*                          (alist_pop DEC k a1 = Some (v, a3)) /\ *)
(*                          (Permutation a2 a3) /\ (alist_wf a2)). *)
(*   Proof. *)
(*     i. revert_until PERM. induction PERM; i; ss. *)
(*     { left. ss. } *)
(*     { inv WF0. specialize (IHPERM H2 k). des. *)
(*       { destruct x as [k0 v0]. destruct (RelDec.rel_dec k k0) eqn:EQ. *)
(*         { right. unfold alist_pop. ss. rewrite RelDec.rel_dec_eq_true; auto. *)
(*           2: apply RelDec.rel_dec_correct; auto. ss. esplits; eauto. *)
(*           admit. *)
(*           unfold alist_wf. admit. *)
(*         } *)
(*         { left. unfold alist_pop. ss. rewrite RelDec.rel_dec_neq_false; auto. *)
(*           2: apply RelDec.neg_rel_dec_correct; auto. ss. *)
(*           unfold alist_pop in *. des_ifs; ss. *)
(*         } *)
(*       } *)
(*       { destruct x as [k0 v0]. destruct (RelDec.rel_dec k k0) eqn:EQ. *)
(*         { right. unfold alist_pop. ss. rewrite RelDec.rel_dec_eq_true; auto. *)
(*           2: apply RelDec.rel_dec_correct; auto. ss. esplits; eauto. *)
(*           admit. *)
(*           unfold alist_wf. admit. *)
(*         } *)
(*         { right. unfold alist_pop. ss. rewrite ! RelDec.rel_dec_neq_false; auto. *)
(*           2: apply RelDec.neg_rel_dec_correct; auto. ss. *)
(*           unfold alist_pop in *. des_ifs; ss. *)
(*           esplits; eauto. unfold alist_wf. ss. *)
(*           eapply List.NoDup_cons. *)
(*           - ii. apply H1; clear H1. admit. *)
(*           - admit. *)
(*         } *)
(*       } *)
(*     } *)
(*     { admit. } *)
(*     { assert (WF1: alist_wf l'). *)
(*       { admit. } *)
(*       specialize (IHPERM1 WF0 k). specialize (IHPERM2 WF1 k). des; clarify; eauto. *)
(*       right. esplits; eauto. eapply perm_trans; eauto. *)
(*     } *)
(*   Admitted. *)

(* End ALISTAUX. *)


Notation thread _Id E R := (itree (((@eventE _Id) +' cE) +' E) R).
Notation threads _Id E R := (Th.t (@thread _Id E R)).

Definition th_proj1 elt (m: Th.t elt): list Th.key := List.map fst (Th.elements m).
Definition th_proj2 elt (m: Th.t elt): list elt := List.map snd (Th.elements m).

Definition th_proj_v1 V1 V2 (m: Th.t (prod V1 V2)): Th.t V1 := Th.map fst m.
Definition th_proj_v2 V1 V2 (m: Th.t (prod V1 V2)): Th.t V2 := Th.map snd m.

Definition th_pop (elt: Type) : Th.key -> Th.t elt -> option (prod elt (Th.t elt)) :=
  fun k m => match Th.find k m with
          | None => None
          | Some e => Some (e, Th.remove k m)
          end.

Section SCHEDULE.

  Context {_Ident: ID}.
  Variable E: Type -> Type.

  Let eventE1 := @eventE _Ident.
  Let eventE2 := @eventE (sum_tid _Ident).

  Definition embed_eventE X (e: eventE1 X): eventE2 X.
  Proof.
    destruct e. exact (Choose X). exact (Fair (sum_fmap_r m)). exact (Observe fn args). exact Undefined.
  Defined.

  Let Es0 := (eventE1 +' cE) +' E.

  Let thread R := thread _Ident E R.
  Let threads R := threads _Ident E R.

  Definition interp_thread {R} :
    thread_id.(id) * thread R -> itree (eventE2 +' E) (thread R + R).
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
    (pick_thread : forall {R}, thread_id.(id) * (thread R + R) -> threads R ->
                          itree (eventE2 +' E) (thread_id.(id) * thread R * threads R + R))
    {R}
    :
    thread_id.(id) * thread R * threads R -> itree (eventE2 +' E) R :=
    ITree.iter (fun '(t, ts) =>
                  res <- interp_thread t;;
                  pick_thread (fst t, res) ts
      ).

  (* NB for invalid tid *)
  Definition pick_thread_nondet {R} :
    thread_id.(id) * (thread R + R) -> threads R ->
    itree (eventE2 +' E) (thread_id.(id) * thread R * threads R + R) :=
    fun '(tid, res) ts =>
      match res with
      | inl t =>
          Vis (inl1 (Choose thread_id.(id)))
              (fun tid' =>
                 match th_pop tid' (Th.add tid t ts) with
                 | None => Vis (inl1 (Choose void)) (Empty_set_rect _)
                 | Some (t', ts') =>
                     Vis (inl1 (Fair (sum_fmap_l (tids_fmap tid' (th_proj1 ts')))))
                         (fun _ => Ret (inl (tid', t', ts')))
                 end)
      | inr r =>
          if Th.is_empty ts then Ret (inr r)
          else Vis (inl1 (Choose thread_id.(id)))
                   (fun tid' =>
                      match th_pop tid' ts with
                      | None => Vis (inl1 (Choose void)) (Empty_set_rect _)
                      | Some (t', ts') =>
                          Vis (inl1 (Fair (sum_fmap_l (tids_fmap tid' (th_proj1 ts')))))
                              (fun _ => Ret (inl (tid', t', ts')))
                      end)
      end.

  Definition interp_sched {R} :
    thread_id.(id) * thread R * threads R -> itree (eventE2 +' E) R :=
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

  Lemma interp_thread_vis_gettid R tid (ktr : ktree Es0 thread_id.(id) R) :
    interp_thread (tid, Vis (inl1 (inr1 GetTid)) ktr) =
      tau;; interp_thread (tid, ktr tid).
  Proof.
    unfold interp_thread at 1. rewrite unfold_iter. ss. rewrite bind_ret_l. ss.
  Qed.

  Lemma interp_thread_trigger_gettid R tid (ktr : ktree Es0 thread_id.(id) R) :
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
      Vis (inl1 (Choose thread_id.(id)))
        (fun tid' =>
           match th_pop tid' (Th.add tid t ts) with
           | None => Vis (inl1 (Choose void)) (Empty_set_rect _)
           | Some (t', ts') => Vis (inl1 (Fair (sum_fmap_l (tids_fmap tid' (th_proj1 ts')))))
                                (fun _ => Ret (inl (tid', t', ts')))
           end).
  Proof. ss. Qed.

  Lemma pick_thread_nondet_terminate {R} tid (r : R) ts :
    pick_thread_nondet (tid, (inr r)) ts =
      if Th.is_empty ts then Ret (inr r)
      else Vis (inl1 (Choose thread_id.(id)))
               (fun tid' =>
                  match th_pop tid' ts with
                  | None => Vis (inl1 (Choose void)) (Empty_set_rect _)
                  | Some (t', ts') => Vis (inl1 (Fair (sum_fmap_l (tids_fmap tid' (th_proj1 ts')))))
                                         (fun _ => Ret (inl (tid', t', ts')))
                  end).
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



(* Section SCHEDAUX. *)

(*   Context {_Ident: ID}. *)
(*   Variable E: Type -> Type. *)

(*   Lemma ths_find_none_tid_add *)
(*         R (ths: threads _Ident E R) tid *)
(*         (NONE: threads_find tid ths = None) *)
(*     : *)
(*     tid_list_add (alist_proj1 ths) tid (tid :: (alist_proj1 ths)). *)
(*   Proof. *)
(*     revert_until ths. induction ths; i; ss. *)
(*     { econs; ss. } *)
(*     des_ifs. ss. destruct (tid_dec tid n) eqn:TID. *)
(*     { clarify. eapply RelDec.neg_rel_dec_correct in Heq. ss. } *)
(*     eapply IHths in NONE. inv NONE. econs; ss. *)
(*     eapply List.not_in_cons. split; auto. *)
(*   Qed. *)

(*   Lemma ths_pop_find_none *)
(*         R (ths ths0: threads _Ident E R) th tid *)
(*         (POP: threads_pop tid ths = Some (th, ths0)) *)
(*     : *)
(*     threads_find tid ths0 = None. *)
(*   Proof. eapply alist_pop_find_none; eauto. eapply reldec_correct_tid_dec. Qed. *)

(*   Lemma ths_pop_find_some *)
(*         R (ths ths0: threads _Ident E R) th tid *)
(*         (POP: threads_pop tid ths = Some (th, ths0)) *)
(*     : *)
(*     threads_find tid ths = Some th. *)
(*   Proof. eapply alist_pop_find_some; eauto. Qed. *)

(*   Lemma ths_find_some_tid_in *)
(*         R (ths: threads _Ident E R) tid th *)
(*         (FIND: threads_find tid ths = Some th) *)
(*     : *)
(*     tid_list_in tid (alist_proj1 ths). *)
(*   Proof. *)
(*     revert_until ths. induction ths; i; ss. des_ifs; ss. *)
(*     - left. symmetry. eapply RelDec.rel_dec_correct. eauto. *)
(*     - right. eapply IHths. eauto. *)
(*       Unshelve. eapply reldec_correct_tid_dec. *)
(*   Qed. *)

(*   Lemma ths_wf_perm_pop_cases *)
(*         R (ths0 ths1: threads _Ident E R) *)
(*         (PERM: Permutation ths0 ths1) *)
(*         (WF0: threads_wf ths0) *)
(*     : *)
(*     forall x, ((threads_pop x ths0 = None) /\ (threads_pop x ths1 = None)) \/ *)
(*            (exists th ths2 ths3, (threads_pop x ths0 = Some (th, ths2)) /\ *)
(*                               (threads_pop x ths1 = Some (th, ths3)) /\ *)
(*                               (Permutation ths2 ths3) /\ (threads_wf ths2)). *)
(*   Proof. eapply alist_wf_perm_pop_cases; eauto. eapply reldec_correct_tid_dec. Qed. *)


(*   Lemma tids_fmap_perm_eq *)
(*         tid ts0 ts1 *)
(*         (PERM: Permutation ts0 ts1) *)
(*     : *)
(*     tids_fmap tid ts0 = tids_fmap tid ts1. *)
(*   Proof. *)
(*     extensionality t. unfold tids_fmap. des_ifs. *)
(*     { hexploit Permutation_in; eauto. i. clarify. } *)
(*     { eapply Permutation_sym in PERM. hexploit Permutation_in; eauto. i. clarify. } *)
(*   Qed. *)

(*   Ltac gfold := gfinal; right; pfold. *)

(*   Lemma interp_all_perm_equiv *)
(*         R tid th (ths0 ths1: @threads _Ident E R) *)
(*         (PERM: Permutation ths0 ths1) *)
(*         (WF: threads_wf ths0) *)
(*     : *)
(*     eq_itree (@eq R) (interp_sched (tid, th, ths0)) (interp_sched (tid, th, ths1)). *)
(*   Proof. *)
(*     ginit. revert_until R. gcofix CIH. i. *)
(*     rewrite ! unfold_interp_sched. *)
(*     destruct (observe th) eqn:T; (symmetry in T; eapply simpobs in T; eapply bisim_is_eq in T); clarify. *)
(*     { rewrite ! interp_thread_ret. rewrite ! bind_ret_l. *)
(*       rewrite ! pick_thread_nondet_terminate. destruct ths0. *)
(*       { hexploit Permutation_nil; eauto. i; clarify. ired. gfold. econs; eauto. } *)
(*       destruct ths1. *)
(*       { eapply Permutation_sym in PERM. hexploit Permutation_nil; eauto. i; clarify. } *)
(*       ired. rewrite <- ! bind_trigger. guclo eqit_clo_bind. econs. reflexivity. i; clarify. *)
(*       hexploit (ths_wf_perm_pop_cases PERM WF u2). i; des. *)
(*       { ss. rewrite H, H0. clear H H0. ired. guclo eqit_clo_bind. econs. reflexivity. i. destruct u1. } *)
(*       ss. rewrite H, H0. ired. *)
(*       erewrite tids_fmap_perm_eq. 2: eapply alist_proj1_preserves_perm; eauto. *)
(*       rewrite <- ! bind_trigger. guclo eqit_clo_bind. econs. reflexivity. i; clarify. destruct u0; ss. *)
(*       gfold. econs 2. right. eapply CIH; eauto. *)
(*     } *)
(*     { rewrite ! interp_thread_tau. rewrite ! bind_tau. gfold. econs 2. right. *)
(*       rewrite <- ! unfold_interp_sched. eauto. *)
(*     } *)
(*     { destruct e as [[eev | cev] | ev]. *)
(*       { rewrite interp_thread_vis_eventE. rewrite ! bind_vis. *)
(*         rewrite <- ! bind_trigger. guclo eqit_clo_bind. econs. reflexivity. i; clarify. *)
(*         rewrite ! bind_tau. gfold. econs 2. right. *)
(*         rewrite <- ! unfold_interp_sched. eauto. *)
(*       } *)
(*       2:{ rewrite interp_thread_vis. rewrite ! bind_vis. *)
(*           rewrite <- ! bind_trigger. guclo eqit_clo_bind. econs. reflexivity. i; clarify. *)
(*           rewrite ! bind_tau. gfold. econs 2. right. *)
(*           rewrite <- ! unfold_interp_sched. eauto. *)
(*       } *)
(*       destruct cev. *)
(*       { rewrite interp_thread_vis_yield. rewrite ! bind_ret_l. *)
(*         rewrite ! pick_thread_nondet_yield. rewrite <- ! bind_trigger. rewrite ! bind_bind. *)
(*         guclo eqit_clo_bind. econs. reflexivity. i; clarify. *)
(*         assert (PERM0: Permutation (threads_add tid (k ()) ths0) (threads_add tid (k ()) ths1)). *)
(*         { admit. } *)
(*         assert (WF0: threads_wf (threads_add tid (k ()) ths0)). *)
(*         { admit. } *)
(*         hexploit (ths_wf_perm_pop_cases PERM0 WF0 u2). i; des. *)
(*         { ss. rewrite H, H0. clear H H0. ired. guclo eqit_clo_bind. econs. reflexivity. i. destruct u1. } *)
(*         ss. rewrite H, H0. ired. *)
(*         erewrite tids_fmap_perm_eq. 2: eapply alist_proj1_preserves_perm; eauto. *)
(*         rewrite <- ! bind_trigger. guclo eqit_clo_bind. econs. reflexivity. i; clarify. destruct u0; ss. *)
(*         gfold. econs 2. right. eapply CIH; eauto. *)
(*       } *)
(*       { rewrite interp_thread_vis_gettid. rewrite ! bind_tau. gfold. econs 2. right. *)
(*         rewrite <- ! unfold_interp_sched. eauto. *)
(*       } *)
(*     } *)
(*   Admitted. *)

(* End SCHEDAUX. *)


Section INTERP.

  Variable State: Type.
  Variable _Ident: ID.

  Definition interp_all
             {R}
             (st: State) (ths: @threads _Ident (sE State) R)
             tid (itr: @thread _Ident (sE State) R) :
    itree (@eventE (sum_tid _Ident)) R :=
    interp_state (st, interp_sched (tid, itr, ths)).

End INTERP.


Section MOD.

  Variable mod: Mod.t.
  Let st := (Mod.st_init mod).
  Let Ident := (Mod.ident mod).
  Let main := ((Mod.funs mod) "main").

  Definition interp_mod (ths: @threads (Mod.ident mod) (sE (Mod.state mod)) Val):
    itree (@eventE (sum_tid Ident)) Val :=
    interp_all st ths tid_main (main []).

End MOD.
