From sflib Require Import sflib.
From Paco Require Import paco.

Require Export Coq.Strings.String.
From Coq Require Import Program.

From Fairness Require Export ITreeLib WFLib FairBeh NatStructs Any.

Set Implicit Arguments.

Module TIdSet := NatSet.


Notation thread_id := nat (only parsing).
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
        funs: fname -> option (ktree (((@eventE ident) +' cE) +' sE state) Any.t Any.t);
      }.

  Program Definition wrap_fun {ident} {E} `{@eventE ident -< E} A R
          (f: ktree E A R):
    ktree E Any.t Any.t :=
    fun arg =>
      match (arg↓) with
      | Some arg => ret <- f arg;; Ret ret↑
      | None => UB
      end.

  Fixpoint get_funs {ident} {E} `{@eventE ident -< E}
           (funs: list (fname * (ktree E Any.t Any.t)))
           (fn: fname):
    option (ktree E Any.t Any.t) :=
    match funs with
    | [] => None
    | (fn_hd, body_hd)::tl =>
        if string_dec fn fn_hd then Some body_hd else get_funs tl fn
    end.
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

  Lemma embed_state_trigger E' `[E' -< E] R X (e : E' X) (ktr : ktree (E +' sE V) X R) :
    embed_state (x <- trigger e;; ktr x) = x <- trigger e;; embed_state (ktr x).
  Proof.
    rewrite 2 bind_trigger. apply embed_state_vis.
  Qed.

  Lemma embed_state_get' R (ktr : ktree (E +' sE V) V R) :
    embed_state (x <- trigger (Get _);; ktr x) = x <- trigger (Get _);; (embed_state (ktr (get x))).
  Proof. rewrite 2 bind_trigger. eapply embed_state_get. Qed.

  Lemma embed_state_put' R v (ktr : ktree (E +' sE V) unit R) :
    embed_state (x <- trigger (Put v);; ktr x) = s <- trigger (Get _);; _ <- trigger (Put (put s v));; (embed_state (ktr tt)).
  Proof.
    rewrite 2 bind_trigger.
    match goal with [ |- embed_state (go (VisF ?e _)) = _ ] => replace e with (@inr1 E _ _ (Put v)) by ss end.
    rewrite embed_state_put. f_equal. f_equal. extensionalities s.
    rewrite bind_trigger. ss.
  Qed.

End LENS.

Global Opaque embed_state.

Section ADD.

  Import Mod.
  Variable M1 M2 : Mod.t.

  Definition embed_l {R} (itr : itree ((eventE +' cE) +' sE _) R) :=
    map_event (embed_left (embed_left (@embed_event_l M1.(ident) M2.(ident))))
      (embed_state (@fst M1.(state) M2.(state)) update_fst itr).

  Definition embed_r {R} (itr : itree ((eventE +' cE) +' sE _) R) :=
    map_event (embed_left (embed_left (@embed_event_r M1.(ident) M2.(ident))))
      (embed_state (@snd M1.(state) M2.(state)) update_snd itr).

  Definition add_funs : fname -> option (ktree _ Any.t Any.t) :=
    fun fn =>
      match M1.(funs) fn, M2.(funs) fn with
      | Some fn_body, None => Some (fun args => embed_l (fn_body args))
      | None, Some fn_body => Some (fun args => embed_r (fn_body args))
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
