From sflib Require Import sflib.
From Paco Require Import paco.

Require Export Coq.Strings.String.
From Coq Require Import Program.

From Fairness Require Export ITreeLib EventCategory WFLib FairBeh NatStructs Any Lens.

Set Implicit Arguments.

Module TIdSet := NatSet.

Notation fname := string (only parsing).
Notation thread_id := nat (only parsing).

Definition program := list (fname * Any.t)%type.

Definition Val := nat.

Section EVENTS.

  Variant cE: Type -> Type :=
  | Yield: cE unit
  | GetTid: cE thread_id
  (* | Spawn (fn: fname) (args: list Val): cE unit *)
  .

  (* sE is just state monad *)
  Variant sE (S : Type) (X : Type) : Type :=
  | Rmw (rmw : S -> S * X) : sE S X
  .

  Variant callE: Type -> Type :=
  | Call (fn: fname) (arg: Any.t): callE Any.t
  .

  Definition Get {S} {X} (p : S -> X) : sE S X := Rmw (fun x => (x, p x)).
  Definition Put {S} (x' : S) : sE S () := Rmw (fun x => (x', tt)).
  Definition Modify {S} (f : S -> S) : sE S () := Rmw (fun x => (f x, tt)).

  Lemma get_rmw {S X} (p : S -> X) : Get p = Rmw (fun x => (x, p x)).
  Proof. reflexivity. Qed.

  Lemma put_rmw {S} (x' : S) : Put x' = Rmw (fun x => (x', tt)).
  Proof. reflexivity. Qed.

  Lemma modify_rmw {S} (f : S -> S) : Modify f = Rmw (fun x => (f x, tt)).
  Proof. reflexivity. Qed.

End EVENTS.

Global Opaque Get.
Global Opaque Put.
Global Opaque Modify.

Notation programE ident State :=
  ((((@eventE ident) +' cE) +' callE) +' sE State).

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


Module Mod.
  Record t: Type :=
    mk {
        state: Type;
        ident: ID;
        st_init: state;
        funs: fname -> option (ktree (programE ident state) Any.t Any.t);
      }.


  Program Definition wrap_fun {ident} {E} `{@eventE ident -< E} A R
          (f: ktree E A R):
    ktree E Any.t Any.t :=
    fun arg =>
      arg <- unwrap (arg↓);;
      ret <- f arg;; Ret ret↑
  .

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

Section LENS.

  Variable S: Type.
  Variable V: Type.

  Variable l : Lens.t S V.

  Definition apply_lens X : (V -> V * X) -> (S -> S * X) :=
    fun rmw s =>
      (Lens.set l (fst (rmw (Lens.view l s))) s, snd (rmw (Lens.view l s))).

  Definition embed_lens X (se : sE V X) : sE S X :=
    match se with
    | Rmw state => Rmw (apply_lens state)
    end.

  Definition map_lens {E R} : itree (E +' sE V) R -> itree (E +' sE S) R :=
    map_event (embed_right embed_lens).

End LENS.

Section ADD.

  Import Mod.
  Variable M1 M2 : Mod.t.

  Definition embed_l {R} (itr : itree (programE _ _) R) : itree (programE _ _) R :=
    map_event (embed_left (embed_left (embed_left (@embed_event_l M1.(ident) M2.(ident)))))
      (map_event (embed_right (embed_lens (@fstl M1.(state) M2.(state)))) itr).

  Definition embed_r {R} (itr : itree (programE _ _) R) : itree (programE _ _) R :=
    map_event (embed_left (embed_left (embed_left (@embed_event_r M1.(ident) M2.(ident)))))
      (map_event (embed_right (embed_lens (@sndl M1.(state) M2.(state)))) itr).

  Definition add_funs : fname -> option (ktree _ Any.t Any.t) :=
    fun fn =>
      match M1.(funs) fn, M2.(funs) fn with
      | Some fn_body, None => Some (fun args => embed_l (fn_body args))
      | None, Some fn_body => Some (fun args => embed_r (fn_body args))
      | Some _, Some _ => Some (fun args => Vis (inl1 (inl1 (inl1 Undefined))) (Empty_set_rect _))
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
