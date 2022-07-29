From sflib Require Import sflib.
From Paco Require Import paco.

Require Export Coq.Strings.String.
From Coq Require Import Program.

From Fairness Require Export ITreeLib WFLib FairBeh NatStructs.

Set Implicit Arguments.

Module TIdSet := NatSet.


Notation thread_id := nat.
Section TID.

  Definition nat_wf: WF := mk_wf Wf_nat.lt_wf.

  Definition tid_dec := PeanoNat.Nat.eq_dec.

  Lemma reldec_correct_tid_dec: RelDec.RelDec_Correct (RelDec.RelDec_from_dec eq tid_dec).
  Proof. eapply RelDec.RelDec_Correct_eq_typ. Qed.

  Definition tid_dec_bool :=
    fun t1 t2 => if (tid_dec t1 t2) then true else false.


  Definition sum_tid (_id: ID) := id_sum thread_id _id.

  Definition tids_fmap (tid: thread_id) (tidf: TIdSet.t): @fmap thread_id :=
    fun t => if (PeanoNat.Nat.eq_dec t tid) then Flag.success
          else if (NatMapP.F.In_dec tidf t) then Flag.fail
               else Flag.emp.

  Definition tids_fmap_all (tidf: TIdSet.t): @fmap thread_id :=
    fun t => if (NatMapP.F.In_dec tidf t) then Flag.fail
             else Flag.emp.

  Lemma tids_fmap_rm_same_eq
        tid tset
    :
    tids_fmap tid tset = tids_fmap tid (NatMap.remove tid tset).
  Proof.
    extensionality t. unfold tids_fmap. des_ifs.
    - exfalso. apply n0; clear n0. rewrite NatMapP.F.remove_neq_in_iff; eauto.
    - exfalso. apply n0; clear n0. rewrite <- NatMapP.F.remove_neq_in_iff; eauto.
  Qed.

  Lemma tids_fmap_add_same_eq
        tid tset
    :
    tids_fmap tid tset = tids_fmap tid (NatMap.add tid () tset).
  Proof.
    extensionality t. unfold tids_fmap. des_ifs.
    - exfalso. apply n0; clear n0. rewrite NatMapP.F.add_neq_in_iff; eauto.
    - exfalso. apply n0; clear n0. rewrite <- NatMapP.F.add_neq_in_iff; eauto.
  Qed.

  Definition kernel_tid: thread_id := 0.

  Definition kernel_success_fmap: @fmap thread_id :=
    fun t => if (tid_dec t kernel_tid)
             then Flag.success else Flag.emp.

  Definition initial_threads := TIdSet.add kernel_tid NatSet.empty.
End TID.


Notation fname := string (only parsing).
Definition Val := nat.

Variant cE: Type -> Type :=
| Yield: cE unit
| GetTid: cE thread_id
(* | Spawn (fn: fname) (args: list Val): cE unit *)
.

Variant sE (State: Type): Type -> Type :=
| Put (st: State): sE State unit
| Get: sE State State
.

Module Mod.
  Record t: Type :=
    mk {
        state: Type;
        ident: ID;
        st_init: state;
        funs: fname -> option (ktree (((@eventE ident) +' cE) +' sE state) (list Val) Val);
      }.
End Mod.

Definition update_fst {A B}: A * B -> A -> A * B :=
  fun '(_, b) a => (a, b).

Definition update_snd {A B}: A * B -> B -> A * B :=
  fun '(a, _) b => (a, b).

Section LENS.
  Variable S: Type.
  Variable V: Type.
  Variable E: Type -> Type.

  Variable get: S -> V.
  Variable put: S -> V -> S.

  Definition embed_state:
    forall R (itr: itree (E +' sE V) R),
      itree (E +' sE S) R.
    cofix embed_itree.
    intros R itr.
    destruct (observe itr) as [r|itr0|? [e|[v|]] ktr].
    { exact (Ret r). }
    { exact (Tau (embed_itree _ itr0)). }
    { exact (Vis (inl1 e) (fun x => embed_itree _ (ktr x))). }
    { exact (Vis (inr1 (@Get _)) (fun s => Vis (inr1 (Put (put s v))) (fun _ => embed_itree _ (ktr tt)))). }
    { exact (Vis (inr1 (@Get _)) (fun s => embed_itree _ (ktr (get s)))). }
  Defined.

  Lemma embed_state_ret R (r : R) :
    embed_state (Ret r) = Ret r.
  Proof. eapply observe_eta. ss. Qed.

  Lemma embed_state_tau R (itr : itree (E +'sE V) R) :
    embed_state (Tau itr) = Tau (embed_state itr).
  Proof. eapply observe_eta. ss. Qed.

  Lemma embed_state_vis R X e (ktr : ktree (E +' sE V) X R) :
    embed_state (Vis (inl1 e) ktr) = Vis (inl1 e) (fun x => embed_state (ktr x)).
  Proof. eapply observe_eta. ss. Qed.

  Lemma embed_state_get R (ktr : ktree (E +' sE V) V R) :
    embed_state (Vis (inr1 (Get _)) ktr) = Vis (inr1 (Get _)) (fun s => embed_state (ktr (get s))).
  Proof. eapply observe_eta. ss. Qed.

  Lemma embed_state_put R v (ktr : ktree (E +' sE V) unit R) :
    embed_state (Vis (inr1 (Put v)) ktr) =
      Vis (inr1 (Get _)) (fun s => Vis (inr1 (Put (put s v))) (fun _ => embed_state (ktr tt))).
  Proof. eapply observe_eta. ss. Qed.

End LENS.

Global Opaque embed_state.

Section ADD.

  Import Mod.
  Variable M1 M2 : Mod.t.

  Definition embed_l (fn_body : ktree ((eventE +' cE) +' sE _) (list Val) Val) args :=
    map_event (embed_left (embed_left (@embed_event_l M1.(ident) M2.(ident))))
      (embed_state (@fst M1.(state) M2.(state)) update_fst (fn_body args)).

  Definition embed_r (fn_body : ktree ((eventE +' cE) +' sE _) (list Val) Val) args :=
    map_event (embed_left (embed_left (@embed_event_r M1.(ident) M2.(ident))))
      (embed_state (@snd M1.(state) M2.(state)) update_snd (fn_body args)).

  Definition add_funs : fname -> option (ktree _ (list Val) Val) :=
    fun fn =>
      match M1.(funs) fn, M2.(funs) fn with
      | Some fn_body, None => Some (embed_l fn_body)
      | None, Some fn_body => Some (embed_r fn_body)
      | Some _, Some _ => Some (fun args => Vis (inl1 (inl1 Undefined)) (Empty_set_rect _))
      | None , None => None
      end.

  Definition ModAdd : Mod.t :=
    {|
      state := state M1 * state M2;
      ident := id_sum (ident M1) (ident M2);
      st_init := (st_init M1, st_init M2);
      funs := add_funs;
    |}.

End ADD.

(*   Definition add_fun_right *)
(*              (ktr: ktree (BehE +' cE state1) (Val * state1) (Val * state1)): *)
(*     ktree (BehE +' cE add_state) (Val * add_state) (Val * add_state) := *)
(*     embed_fun snd update_snd ktr. *)

(*   Definition add_funs *)
(*              (funs0: fname -> ktree (BehE +' cE state0) (Val * state0) (Val * state0)) *)
(*              (funs1: fname -> ktree (BehE +' cE state1) (Val * state1) (Val * state1)) *)
(*     : *)
(*     fname -> ktree (BehE +' cE add_state) (Val * add_state) (Val * add_state) := *)
(*     fun fn => *)
(*       match fname_parse fn with *)
(*       | Some (true, fn) => add_fun_left (funs0 fn) *)
(*       | Some (false, fn) => add_fun_right (funs1 fn) *)
(*       | None => fun _ => trigger UB >>= Empty_set_rect _ *)
(*       end. *)
(* End ADD. *)

(* Definition add (md0 md1: t): t := *)
(*   @mk *)
(*     (add_state md0.(state) md1.(state)) *)
(*     (add_st_init md0.(st_init) md1.(st_init)) *)
(*     (add_funs md0.(funs) md1.(funs)). *)
(* End Mod. *)


(* Module ModSim. *)
(*   Definition sim: Mod.t -> Mod.t -> Prop. *)
(*   Admitted. *)

(*   Lemma sim_id (md: Mod.t) *)
(*     : *)
(*     sim md md. *)
(*   Admitted. *)

(*   Lemma sim_horizontal *)
(*         (md_src0 md_src1 md_tgt0 md_tgt1: Mod.t) *)
(*         (SIM0: sim md_src0 md_tgt0) *)
(*         (SIM1: sim md_src1 md_tgt1) *)
(*     : *)
(*     sim (Mod.add md_src0 md_tgt0) (Mod.add md_src1 md_tgt1). *)
(*   Admitted. *)
(* End ModSim. *)

(* Variant callE: Type -> Type := *)
(* | Call (fn: fname) (arg: Val): callE Val *)
(* . *)

(* Module OMod. *)
(*   Record t: Type := *)
(*     mk { *)
(*         state: Type; *)
(*         st_init: state; *)
(*         funs: fname -> ktree (BehE +' cE state +' callE state) (Val * state) (Val * state); *)
(*       }. *)

(*   Section LINK. *)
(*     Variable omd: t. *)
(*     Variable md: Mod.t. *)

(*     Definition link_state: Type := omd.(state) * md.(Mod.state). *)

(*     Definition link_st_init: link_state := (omd.(st_init), md.(Mod.st_init)). *)

(*     Definition link_itree: *)
(*       forall (s: link_state) R, *)
(*         itree (BehE +' callE omd.(state) +' cE omd.(state)) R -> itree (BehE +' callE link_state +' cE link_state) (link_state * R). *)
(*     Proof. *)
(*     Admitted. *)
(*   End LINK. *)
(* End OMod. *)
