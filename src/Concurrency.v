From sflib Require Import sflib.
From ITree Require Export ITree.
From Paco Require Import paco.

Require Export Coq.Strings.String.
From Coq Require Import
  Program
  Permutation
  SetoidList
  SetoidPermutation
  Lists.List
  Lia.

Export ITreeNotations.

From Fairness Require Export ITreeLib FairBeh.
From Fairness Require Import Mod.

(* From ExtLib Require Import FMapAList. *)
(* Require Import FSets.FMapList. *)
Require Import Coq.FSets.FSets Coq.FSets.FMaps Coq.Structures.OrderedTypeEx.
Module Th := FMapList.Make(Nat_as_OT).
Module IdSet := FSetList.Make(Nat_as_OT).

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

Section EMBED_EVENT.

  CoFixpoint map_event {E1 E2} (embed : forall X, E1 X -> E2 X) R : itree E1 R -> itree E2 R :=
    fun itr =>
      match observe itr with
      | RetF r => Ret r
      | TauF itr => Tau (map_event embed itr)
      | VisF e ktr => Vis (embed _ e) (fun x => map_event embed (ktr x))
      end.

  Lemma map_event_ret E1 E2 (embed : forall X, E1 X -> E2 X) R (r : R) :
    map_event embed (Ret r) = Ret r.
  Proof. eapply observe_eta. ss. Qed.

  Lemma map_event_tau E1 E2 (embed : forall X, E1 X -> E2 X) R (itr : itree E1 R) :
    map_event embed (Tau itr) = Tau (map_event embed itr).
  Proof. eapply observe_eta. ss. Qed.

  Lemma map_event_vis E1 E2 (embed : forall X, E1 X -> E2 X) R X (e : E1 X) (ktr : ktree E1 X R) :
    map_event embed (Vis e ktr) = Vis (embed _ e) (fun x => map_event embed (ktr x)).
  Proof. eapply observe_eta. ss. Qed.

  Definition embed_left {E1 E2} (embed : forall X, E1 X -> E2 X) {E} X (e : (E1 +' E) X) : (E2 +' E) X :=
    match e with
    | inl1 e => inl1 (embed _ e)
    | inr1 e => inr1 e
    end.

End EMBED_EVENT.

Global Opaque map_event.

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

  Lemma interp_state_aux_bind {R1} {R2} st (itr : itree Es R1) (ktr : ktree Es R1 R2) :
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

  Lemma unfold_interp_state R st (itr : itree Es R) :
    interp_state (st, itr) = x <- interp_state_aux (st, itr);; Ret (snd x).
  Proof. unfold interp_state. ss. Qed.

  Lemma interp_state_bind R1 R2 st (itr : itree Es R1) (ktr : ktree Es R1 R2) :
    interp_state (st, itr >>= ktr) = x <- interp_state_aux (st, itr);; interp_state (fst x, ktr (snd x)).
  Proof. unfold interp_state. rewrite interp_state_aux_bind. grind. Qed.

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

Global Opaque
  interp_state_aux
  interp_state.

Section STATE_PROP.

  Variable State: Type.

  Lemma interp_state_aux_map_event E1 E2 R (embed : forall X, E1 X -> E2 X) st (itr : itree (E1 +' sE State) R) :
    interp_state_aux (st, map_event (embed_left embed) itr) = map_event embed (interp_state_aux (st, itr)).
  Proof.
    eapply bisim_is_eq. revert st itr. pcofix CIH. i.
    destruct_itree itr.
    - rewrite map_event_ret.
      rewrite 2 interp_state_aux_ret.
      rewrite map_event_ret.
      pfold. econs. ss.
    - rewrite map_event_tau.
      rewrite 2 interp_state_aux_tau.
      rewrite map_event_tau.
      pfold. econs. right. eapply CIH.
    - rewrite map_event_vis.
      destruct e.
      + ss. rewrite 2 interp_state_aux_vis.
        rewrite map_event_vis.
        pfold. econs. intros. left.
        rewrite map_event_tau.
        pfold. econs. right. eapply CIH.
      + ss. destruct s.
        * rewrite 2 interp_state_aux_put.
          rewrite map_event_tau.
          pfold. econs. right. eapply CIH.
        * rewrite 2 interp_state_aux_get.
          rewrite map_event_tau.
          pfold. econs. right. eapply CIH.
  Qed.

End STATE_PROP.

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

Definition id_pop : IdSet.elt -> IdSet.t -> option IdSet.t :=
  fun x s => if IdSet.mem x s
          then Some (IdSet.remove x s)
          else None.

Section THREADS.

  Import Th.
  
  (* IdSet *)
  Lemma Empty_nil s : IdSet.Empty s -> IdSet.elements s = [].
  Proof.
    i. destruct s as [s OK]; ss. destruct s; ss.
    exfalso. eapply H. econs. ss.
  Qed.

  Lemma Empty_nil_neg s : ~ IdSet.Empty s -> IdSet.elements s <> [].
  Proof.
    destruct s as [s SORTED]; ss.
    ii. subst. eapply H. ii. eapply InA_nil; eauto.
  Qed.

  Lemma IdSet_Permutation_remove x s l :
    Permutation (IdSet.elements s) (x :: l) -> Permutation (IdSet.elements (IdSet.remove x s)) l.
  Proof.
    destruct s as [s SORTED]. ss.
    revert l. induction s; i.
    - eapply Permutation_length in H. ss.
    - assert (List.In a (x :: l)) by (rewrite <- H; econs; ss).
      destruct H0.
      + subst. eapply Permutation_cons_inv in H. ss.
        Raw.MX.elim_comp_eq a a. ss.
      + eapply Add_inv in H0. des. eapply Permutation_Add in H0.
        rewrite <- H0 in *. clear l H0.
        rewrite perm_swap in H. eapply Permutation_cons_inv in H.
        assert (List.In x s).
        { eapply Permutation_in.
          - symmetry. eapply H.
          - econs; ss.
        }
        eapply IdSet.MSet.Raw.isok_iff in SORTED.
        epose proof (Sorted_extends _ SORTED).
        eapply Forall_forall in H1; eauto.
        ss. Raw.MX.elim_comp_gt x a.
        econs. eapply IHs; eauto.
        eapply IdSet.MSet.Raw.isok_iff.
        inv SORTED; ss.
    Unshelve. compute. lia.
  Qed.

  Lemma IdSet_Permutation_add x s l :
    ~ IdSet.In x s -> Permutation (IdSet.elements s) l -> Permutation (IdSet.elements (IdSet.add x s)) (x :: l).
  Proof.
    destruct s as [s SORTED]. ss. revert l. induction s; intros l H1 H2.
    - rewrite <- H2. ss.
    - ss. assert (x = a \/ x < a \/ x > a) by lia. des.
      + exfalso. eapply H1. econs. ss.
      + Raw.MX.elim_comp_lt x a. econs. ss.
      + Raw.MX.elim_comp_gt x a. rewrite <- H2. rewrite perm_swap. econs.
        eapply IHs; eauto.
        unfold IdSet.In, IdSet.MSet.In in *. ss.
        intro. eapply H1. econs 2. eapply H0.
        Unshelve. clear H1. eapply IdSet.MSet.Raw.isok_iff in SORTED. inv SORTED.
        eapply IdSet.MSet.Raw.isok_iff. ss.
  Qed.

  (* Th *)
  Lemma In_MapsTo A k e (m : Th.t A) : List.In (k, e) (elements m) -> MapsTo k e m.
  Proof.
    unfold MapsTo, Raw.PX.MapsTo, elements, Raw.elements.
    remember (this m) as l. clear m Heql. intros.
    induction l; ss. destruct H.
    - eapply InA_cons_hd. subst. ss.
    - eapply InA_cons_tl. eauto.
  Qed.

  Lemma In_th_proj1 A k (m : Th.t A) : List.In k (th_proj1 m) -> exists e, MapsTo k e m.
  Proof.
    unfold th_proj1, MapsTo, Raw.PX.MapsTo, elements, Raw.elements.
    remember (this m) as l. clear m Heql. intros.
    induction l; ss. destruct H.
    - eexists. eapply InA_cons_hd. subst. ss.
    - eapply IHl in H. destruct H. eexists. eapply InA_cons_tl. eauto.
  Qed.

  Lemma Permutation_remove A k e (m : Th.t A) l :
    Permutation (elements m) ((k, e) :: l) -> Permutation (elements (Th.remove k m)) l.
  Proof.
    unfold elements, Raw.elements, remove.
    destruct m as [m SORTED]. ss.
    revert l. induction m; i.
    - eapply Permutation_length in H. ss.
    - assert (List.In a ((k, e) :: l)) by (rewrite <- H; econs; ss).
      destruct H0.
      + inv H0. eapply Permutation_cons_inv in H. ss.
        Raw.MX.elim_comp_eq k k. eauto.
    + eapply Add_inv in H0. destruct H0. eapply Permutation_Add in H0.
      rewrite <- H0 in *. clear l H0.
      rewrite perm_swap in H. eapply Permutation_cons_inv in H.
      assert (List.In (k, e) m).
      { eapply Permutation_in.
        - symmetry; eauto.
        - econs; ss.
      }
      epose proof (Sorted_extends _ SORTED).
      eapply Forall_forall in H1; eauto.
      destruct a. ss. Raw.MX.elim_comp_gt k n.
      inv SORTED.
      econs. eapply IHm; eauto.
    Unshelve. compute. lia.
  Qed.

  Lemma Permutation_add A k e (m : Th.t A) l :
    ~ Th.In k m -> Permutation (elements m) l -> Permutation (elements (add k e m)) ((k, e) :: l).
  Proof.
    unfold elements, Raw.elements, add, In.
    destruct m as [m SORTED]. ss. revert l. induction m; intros l H1 H2.
    - rewrite <- H2. ss.
    - destruct a. ss.
      assert (k = n \/ k < n \/ k > n) by lia.
      destruct H as [|[]].
      + exfalso. eapply H1. exists a. left. ss.
      + Raw.MX.elim_comp_lt k n. econs; eauto.
      + Raw.MX.elim_comp_gt k n.
        rewrite <- H2. rewrite perm_swap. econs. 
        inv SORTED. eapply IHm; eauto.
        intro. eapply H1. unfold Raw.PX.In in *.
        destruct H0. eexists. right. eauto.
  Qed.

  Lemma InA_In A x (l : list A) : InA (@eq A) x l -> List.In x l.
  Proof. i. induction H.
         - left; eauto.
         - right; eauto.
  Qed.
    
  Lemma InA_In' A k (e : A) l :
    SetoidList.InA (@eq_key_elt A) (k, e) l -> List.In (k, e) l.
  Proof.
    i. induction H.
    - left. destruct H; ss. subst. destruct y; ss.
    - right. eauto.
  Qed.

  Lemma Permutation_NoDupA A l1 l2 :
    Permutation l1 l2 ->
    SetoidList.NoDupA (eq_key (elt:=A)) l1 ->
    SetoidList.NoDupA (eq_key (elt:=A)) l2.
  Proof.
    i.
    eapply PermutationA_preserves_NoDupA; eauto.
    eapply Permutation_PermutationA; eauto.
  Qed.
  
End THREADS.

Section SCHEDULE.

  Variant schedulerE (RT : Type) : Type -> Type :=
  | Execute : thread_id.(id) -> schedulerE RT (option RT)
  .

  Let eventE0 := @eventE thread_id.

  Definition scheduler RT R := itree (schedulerE RT +' eventE0) R.

  Context {_Ident: ID}.
  Variable E: Type -> Type.

  Let eventE1 := @eventE _Ident.
  Let eventE2 := @eventE (sum_tid _Ident).
  Let Es0 := (eventE1 +' cE) +' E.
  Let thread R := thread _Ident E R.
  Let threads R := threads _Ident E R.

  Definition embed_eventE0 X (e: eventE0 X) : eventE2 X.
  Proof.
    destruct e. exact (Choose X). exact (Fair (sum_fmap_l m)). exact (Observe fn args). exact Undefined.
  Defined.

  Definition embed_eventE X (e: eventE1 X): eventE2 X.
  Proof.
    destruct e. exact (Choose X). exact (Fair (sum_fmap_r m)). exact (Observe fn args). exact Undefined.
  Defined.

  Definition interp_thread_aux {R} :
    thread_id.(id) * thread R -> itree (eventE1 +' E) (thread R + R).
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
      + (* eventE *)
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

  Definition interp_thread {R} :
    thread_id.(id) * thread R -> itree (eventE2 +' E) (thread R + R) :=
    fun x => map_event (embed_left embed_eventE) (interp_thread_aux x).

  Definition interp_sched RT R : threads RT * scheduler RT R -> itree (eventE2 +' E) R.
  Proof.
    eapply ITree.iter. intros [ts sch].
    destruct (observe sch) as [r | sch' | X [e|e] ktr].
    - exact (Ret (inr r)).
    - exact (Ret (inl (ts, sch'))).
    - destruct e.
      destruct (Th.find i ts) as [t|].
      * exact (r <- interp_thread (i, t);;
               match r with
               | inl t' => Ret (inl (Th.add i t' ts, ktr None))
               | inr r => Ret (inl (Th.remove i ts, ktr (Some r)))
               end).
      * exact (Vis (inl1 (Choose void)) (Empty_set_rect _)).
    - exact (Vis (inl1 (embed_eventE0 e)) (fun x => Ret (inl (ts, ktr x)))).
  Defined.

  Lemma unfold_interp_thread {R} tid (itr : thread R) :
    interp_thread (tid, itr) = map_event (embed_left embed_eventE) (interp_thread_aux (tid, itr)).
  Proof. ss. Qed.

  Lemma interp_thread_ret {R} tid (r : R) :
    interp_thread (tid, Ret r) = Ret (inr r).
  Proof. unfold interp_thread, interp_thread_aux. rewrite unfold_iter. grind. eapply map_event_ret. Qed.

  Lemma interp_thread_tau R tid (itr : thread R) :
    interp_thread (tid, tau;; itr) = tau;; interp_thread (tid, itr).
  Proof. unfold interp_thread at 1, interp_thread_aux. rewrite unfold_iter. grind. eapply map_event_tau. Qed.

  Lemma interp_thread_vis R tid X (e : E X) (ktr : ktree Es0 X R) :
    interp_thread (tid, Vis (inr1 e) ktr) =
      Vis (inr1 e) (fun x => tau;; interp_thread (tid, ktr x)).
  Proof.
    unfold interp_thread at 1, interp_thread_aux. rewrite unfold_iter. grind. rewrite map_event_vis.
    eapply (f_equal (fun x => Vis (inr1 e) x)). extensionality x. grind. rewrite map_event_tau. grind.
  Qed.

  Lemma interp_thread_trigger R tid X (e : E X) (ktr : ktree Es0 X R) :
    interp_thread (tid, x <- trigger (inr1 e);; ktr x) =
      x <- trigger (inr1 e);; tau;; interp_thread (tid, ktr x).
  Proof. rewrite ! bind_trigger. eapply interp_thread_vis. Qed.

  Lemma interp_thread_vis_eventE R tid X (e : eventE1 X) (ktr : ktree Es0 X R) :
    interp_thread (tid, Vis (inl1 (inl1 e)) ktr) =
      Vis (inl1 (embed_eventE e)) (fun x => tau;; interp_thread (tid, ktr x)).
  Proof.
    unfold interp_thread at 1, interp_thread_aux. rewrite unfold_iter. grind. rewrite map_event_vis.
    eapply (f_equal (fun x => Vis (inl1 (embed_eventE e)) x)). extensionality x. grind. rewrite map_event_tau. grind.
  Qed.

  Lemma interp_thread_trigger_eventE R tid X (e : eventE1 X) (ktr : ktree Es0 X R) :
    interp_thread (tid, x <- trigger (inl1 (inl1 e));; ktr x) =
      x <- trigger (inl1 (embed_eventE e));; tau;; interp_thread (tid, ktr x).
  Proof. rewrite ! bind_trigger. eapply interp_thread_vis_eventE. Qed.

  Lemma interp_thread_vis_gettid R tid (ktr : ktree Es0 thread_id.(id) R) :
    interp_thread (tid, Vis (inl1 (inr1 GetTid)) ktr) =
      tau;; interp_thread (tid, ktr tid).
  Proof.
    unfold interp_thread at 1, interp_thread_aux. rewrite unfold_iter. grind. rewrite map_event_tau. grind.
  Qed.

  Lemma interp_thread_trigger_gettid R tid (ktr : ktree Es0 thread_id.(id) R) :
    interp_thread (tid, x <- trigger (inl1 (inr1 GetTid));; ktr x) =
      tau;; interp_thread (tid, ktr tid).
  Proof. rewrite bind_trigger. eapply interp_thread_vis_gettid. Qed.

  Lemma interp_thread_vis_yield R tid (ktr : ktree Es0 () R) :
    interp_thread (tid, Vis (inl1 (inr1 Yield)) ktr) =
      Ret (inl (ktr tt)).
  Proof.
    unfold interp_thread at 1, interp_thread_aux. rewrite unfold_iter. grind. rewrite map_event_ret. ss.
  Qed.

  Lemma interp_thread_trigger_yield R tid (ktr : ktree Es0 () R) :
    interp_thread (tid, x <- trigger (inl1 (inr1 Yield));; ktr x) =
      Ret (inl (ktr tt)).
  Proof. rewrite bind_trigger. apply interp_thread_vis_yield. Qed.

  Lemma interp_sched_ret RT R (ths : threads RT) (r : R) :
    interp_sched (ths, Ret r) = Ret r.
  Proof. unfold interp_sched. rewrite unfold_iter. grind. Qed.

  Lemma interp_sched_tau RT R ths (itr : scheduler RT R) :
    interp_sched (ths, Tau itr) = Tau (interp_sched (ths, itr)).
  Proof. unfold interp_sched. rewrite unfold_iter. grind. Qed.

  Lemma interp_sched_execute_Some RT R ths tid t (ktr : option RT -> scheduler RT R)
    (SOME : Th.find tid ths = Some t)
    : interp_sched (ths, Vis (inl1 (Execute _ tid)) ktr) =
      r <- interp_thread (tid, t);;
      match r with
      | inl t' => tau;; interp_sched (Th.add tid t' ths, ktr None)
      | inr r => tau;; interp_sched (Th.remove tid ths, ktr (Some r))
      end.
  Proof. unfold interp_sched. rewrite unfold_iter. grind. Qed.
  
  Lemma interp_sched_execute_None RT R ths tid (ktr : option RT -> scheduler RT R)
    (NONE : Th.find tid ths = None)
    : interp_sched (ths, Vis (inl1 (Execute _ tid)) ktr) =
        Vis (inl1 (Choose void)) (Empty_set_rect _).
  Proof. unfold interp_sched. rewrite unfold_iter. grind.
         eapply observe_eta. ss. f_equal. extensionality x. ss.
  Qed.

  Lemma interp_sched_vis RT R ths X (e : eventE0 X) (ktr : X -> scheduler RT R) :
    interp_sched (ths, Vis (inr1 e) ktr) =
      Vis (inl1 (embed_eventE0 e)) (fun x => tau;; interp_sched (ths, ktr x)).
  Proof. unfold interp_sched. rewrite unfold_iter. grind.
         eapply observe_eta. ss. f_equal. extensionality x. grind.
  Qed.

End SCHEDULE.

Global Opaque
  interp_thread_aux
  interp_thread
  interp_sched.

Section SCHEDULE_NONDET.

  Definition sched_nondet_body {R} q tid r : scheduler R (thread_id.(id) * IdSet.t + R) :=
    match r with
    | None =>
        tid' <- ITree.trigger (inr1 (Choose thread_id.(id)));;
        match id_pop tid' (IdSet.add tid q) with
        | None => Vis (inr1 (Choose void)) (Empty_set_rect _)
        | Some q' =>
            ITree.trigger (inr1 (Fair (tids_fmap tid' (IdSet.elements q'))));;
            Ret (inl (tid', q'))
        end
    | Some r =>
        if IdSet.is_empty q
        then Ret (inr r)
        else
          tid' <- ITree.trigger (inr1 (Choose thread_id.(id)));;
          match id_pop tid' q with
          | None => Vis (inr1 (Choose void)) (Empty_set_rect _)
          | Some q' =>
              ITree.trigger (inr1 (Fair (tids_fmap tid' (IdSet.elements q'))));;
              Ret (inl (tid', q'))
          end
    end.
  
  Definition sched_nondet R0 : thread_id.(id) * IdSet.t -> scheduler R0 R0 :=
    ITree.iter (fun '(tid, q) =>
                  r <- ITree.trigger (inl1 (Execute _ tid));;
                  sched_nondet_body q tid r).

  Lemma unfold_sched_nondet R0 tid q :
    sched_nondet R0 (tid, q) =
      r <- ITree.trigger (inl1 (Execute _ tid));;
      match r with
      | None =>
          tid' <- ITree.trigger (inr1 (Choose thread_id.(id)));;
          match id_pop tid' (IdSet.add tid q) with
          | None => Vis (inr1 (Choose void)) (Empty_set_rect _)
          | Some q' =>
              ITree.trigger (inr1 (Fair (tids_fmap tid' (IdSet.elements q'))));;
              tau;; sched_nondet _ (tid', q')
          end
      | Some r =>
          if IdSet.is_empty q
          then Ret r
          else
            tid' <- ITree.trigger (inr1 (Choose thread_id.(id)));;
            match id_pop tid' q with
            | None => Vis (inr1 (Choose void)) (Empty_set_rect _)
            | Some q' =>
                ITree.trigger (inr1 (Fair (tids_fmap tid' (IdSet.elements q'))));;
                tau;; sched_nondet _ (tid', q')
            end
      end.
  Proof.
    unfold sched_nondet at 1, sched_nondet_body.
    rewrite unfold_iter.
    grind.
    - eapply observe_eta. ss. f_equal. extensionality x0. ss.
    - eapply observe_eta. ss. f_equal. extensionality x0. ss.
  Qed.

  (*
  Lemma unfold_sched_nondet R0 tid q :
    sched_nondet R0 (tid, q) =
      r <- ITree.trigger (inl1 (Execute _ tid));;
      lr <- sched_nondet_body q tid r;;
      match lr with
      | inl (tid', q') => tau;; sched_nondet _ (tid', q')
      | inr r => Ret r
      end.
  Proof. unfold sched_nondet at 1. rewrite unfold_iter. grind. Qed.
   *)

  Context {_Ident : ID}.
  Variable E: Type -> Type.

  Let eventE1 := @eventE _Ident.
  Let eventE2 := @eventE (sum_tid _Ident).
  Let Es0 := (eventE1 +' cE) +' E.
  Let thread R := thread _Ident E R.
  Let threads R := threads _Ident E R.

  Lemma unfold_interp_sched_nondet_Some R tid t (ths : threads R) q :
    Th.find tid ths = Some t ->
    interp_sched (ths, sched_nondet R (tid, q)) =
      r <- interp_thread (tid, t);;
      match r with
      | inl t' => Tau (interp_sched (Th.add tid t' ths,
                          tid' <- ITree.trigger (inr1 (Choose thread_id.(id)));;
                          match id_pop tid' (IdSet.add tid q) with
                          | None => Vis (inr1 (Choose void)) (Empty_set_rect _)
                          | Some q' =>
                              ITree.trigger (inr1 (Fair (tids_fmap tid' (IdSet.elements q'))));;
                              tau;; sched_nondet _ (tid', q')
                          end))
      | inr r => Tau (interp_sched (Th.remove tid ths,
                         if IdSet.is_empty q
                         then Ret r
                         else
                           tid' <- ITree.trigger (inr1 (Choose thread_id.(id)));;
                           match id_pop tid' q with
                           | None => Vis (inr1 (Choose void)) (Empty_set_rect _)
                           | Some q' =>
                               ITree.trigger (inr1 (Fair (tids_fmap tid' (IdSet.elements q'))));;
                               tau;; sched_nondet _ (tid', q')
                           end))
      end.
  Proof.
    rewrite unfold_sched_nondet at 1.
    rewrite bind_trigger.
    eapply interp_sched_execute_Some.
  Qed.

  Lemma unfold_interp_sched_nondet_None R tid (ths : threads R) q :
    Th.find tid ths = None ->
    interp_sched (ths, sched_nondet R (tid, q)) =
      Vis (inl1 (Choose void)) (Empty_set_rect _).
  Proof.
    rewrite unfold_sched_nondet at 1.
    rewrite bind_trigger.
    eapply interp_sched_execute_None.
  Qed.

End SCHEDULE_NONDET.

Global Opaque
  sched_nondet_body
  sched_nondet.

(* section SCHEDAUX. *)

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

  Definition key_set {elt} : Th.t elt -> IdSet.t.
  Proof.
    Import Th.
    intros [l SORTED]. unfold Raw.t in *.
    set (l' := List.map fst l).
    econs. instantiate (1 := l').
    unfold Raw.PX.ltk in *.

    assert (Sorted (fun x y => x < y) l').
    { induction SORTED.
      - subst l'. ss.
      - subst l'. ss. econs 2; ss.
        inv H; ss. econs; ss.
    }

    eapply IdSet.MSet.Raw.isok_iff. ss.
  Defined.

  Definition interp_all
    {R} st (ths: @threads _Ident (sE State) R) tid : itree (@eventE (sum_tid _Ident)) R :=
    interp_state (st, interp_sched (ths, sched_nondet _ (tid, IdSet.remove tid (key_set ths)))).

End INTERP.


Section MOD.

  Variable mod : Mod.t.
  Let st := (Mod.st_init mod).
  Let Ident := (Mod.ident mod).
  Let main := ((Mod.funs mod) "main").

  Definition interp_mod (ths: @threads (Mod.ident mod) (sE (Mod.state mod)) Val):
    itree (@eventE (sum_tid Ident)) Val :=
    interp_all st ths tid_main.

End MOD.
