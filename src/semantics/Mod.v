From sflib Require Import sflib.
From Paco Require Import paco.

Require Export Coq.Strings.String.
From Coq Require Import Program.

From Fairness Require Export ITreeLib WFLib FairBeh NatStructs Any.

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

  Variant sE (State: Type): Type -> Type :=
  | Put (st: State): sE State unit
  | Get: sE State State
  .

  Variant callE: Type -> Type :=
  | Call (fn: fname) (arg: Any.t): callE Any.t
  .

End EVENTS.

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

  Lemma embed_state_tau2 R (itr : itree (E +'sE V) R) :
    embed_state (tau;; itr) = tau;; (embed_state itr).
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

  Lemma embed_state_bind
        A B (itr: itree _ A) (ktr: ktree _ A B)
    :
    @embed_state B (itr >>= ktr) =
      (@embed_state A itr) >>= (fun a => @embed_state B (ktr a)).
  Proof.
    eapply bisim_is_eq. revert itr ktr. ginit. gcofix CIH; i.
    ides itr; grind.
    { rewrite embed_state_ret. ired.
      gfinal. right. eapply paco2_mon.
      2:{ instantiate (1:=bot2). ss. }
      eapply eq_is_bisim. auto.
    }
    { rewrite ! embed_state_tau. rewrite bind_tau.
      gstep. eapply EqTau. gbase. eauto.
    }
    { revert k. destruct e as [|[|]]; i.
      { rewrite ! embed_state_vis.
        ired. gstep. eapply EqVis.
        i. gbase. eauto.
      }
      { rewrite ! embed_state_put.
        ired. gstep. eapply EqVis. i. ss.
        ired. gstep. eapply EqVis. i. ss.
        i. gbase. eauto.
      }
      { rewrite ! embed_state_get.
        ired. gstep. eapply EqVis. i. ss.
        i. gbase. eauto.
      }
    }
  Qed.

  Lemma embed_state_trigger_eventE2
        E' `[E' -< E] X (e : E' X):
    @embed_state X (trigger e) = trigger e >>= (fun r => Ret r).
  Proof.
    rewrite (bind_ret_r_rev (trigger e)).
    setoid_rewrite embed_state_trigger. f_equal. extensionality x.
    apply embed_state_ret.
  Qed.

  Lemma embed_state_trigger_put2
        st
    :
    @embed_state _ (trigger (Put st)) =
      trigger (Get _) >>= (fun s => trigger (Put (put s st)) >>= (fun r => Ret r)).
  Proof.
    rewrite (bind_ret_r_rev (trigger (Put st))).
    setoid_rewrite embed_state_put'. grind.
    rewrite (bind_ret_r_rev (trigger (Put (put x st)))) at 2.
    f_equal. extensionality t. destruct t. apply embed_state_ret.
  Qed.

  Lemma embed_state_trigger_get2
    :
    @embed_state _ (trigger (Get _)) =
      trigger (Get _) >>= (fun s => Ret (get s)).
  Proof.
    rewrite (bind_ret_r_rev (trigger (Get _))).
    setoid_rewrite embed_state_get'. grind. apply embed_state_ret.
  Qed.

  Lemma embed_state_UB
        {ID} `{(@eventE ID) -< E} R:
    @embed_state R UB = UB.
  Proof.
    unfold UB. rewrite embed_state_bind. rewrite embed_state_trigger_eventE2. grind.
  Qed.

  Lemma embed_state_unwrap
        {ID} `{(@eventE ID) -< E}
        X x
    :
    @embed_state X (unwrap x) = unwrap x.
  Proof.
    unfold unwrap. des_ifs.
    { eapply embed_state_ret. }
    { eapply embed_state_UB. }
  Qed.

  Lemma embed_state_ext
        R (itr0 itr1: itree _ R)
    :
    itr0 = itr1 -> embed_state itr0 = embed_state itr1
  .
  Proof. i; subst; reflexivity. Qed.

End LENS.

Global Opaque embed_state.

Section ADD.

  Import Mod.
  Variable M1 M2 : Mod.t.

  Definition embed_l {R} (itr : itree (programE _ _) R) : itree (programE _ _) R :=
    map_event (embed_left (embed_left (embed_left (@embed_event_l M1.(ident) M2.(ident)))))
      (embed_state (@fst M1.(state) M2.(state)) update_fst itr).

  Definition embed_r {R} (itr : itree (programE _ _) R) : itree (programE _ _) R :=
    map_event (embed_left (embed_left (embed_left (@embed_event_r M1.(ident) M2.(ident)))))
      (embed_state (@snd M1.(state) M2.(state)) update_snd itr).

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

Section EMBEDS.

  Import Mod.
  Variable M1 M2 : Mod.t.

  Lemma embed_l_ret R (r : R) :
    embed_l M1 M2 (Ret r) = Ret r.
  Proof. eapply observe_eta. ss. Qed.

  Lemma embed_l_tau R (itr : itree _ R) :
    embed_l M1 M2 (tau;; itr) = tau;; (embed_l M1 M2 itr).
  Proof. eapply observe_eta. ss. Qed.

  Lemma embed_l_vis_eventE R X (e : eventE X) (ktr : ktree _ X R) :
    embed_l M1 M2 (Vis (inl1 (inl1 (inl1 e))) ktr) =
      Vis (inl1 (inl1 (inl1 (@embed_event_l M1.(ident) M2.(ident) _ e)))) (fun x => embed_l M1 M2 (ktr x)).
  Proof. eapply observe_eta. ss. Qed.

  Lemma embed_l_vis_cE R X (e : cE X) (ktr : ktree _ X R) :
    embed_l M1 M2 (Vis (inl1 (inl1 (inr1 e))) ktr) =
      Vis (inl1 (inl1 (inr1 e))) (fun x => embed_l M1 M2 (ktr x)).
  Proof. eapply observe_eta. ss. Qed.

  Lemma embed_l_vis_callE R X (e : callE X) (ktr : ktree _ X R) :
    embed_l M1 M2 (Vis (inl1 (inr1 e)) ktr) =
      Vis (inl1 (inr1 e)) (fun x => embed_l M1 M2 (ktr x)).
  Proof. eapply observe_eta. ss. Qed.

  Lemma embed_l_vis_getE R (ktr : ktree _ _ R) :
    embed_l M1 M2 (Vis (inr1 (Get _)) ktr) =
      Vis (inr1 (Get _)) (fun s => embed_l M1 M2 (ktr (fst s))).
  Proof. eapply observe_eta. ss. Qed.

  Lemma embed_l_vis_putE R v (ktr : ktree _ _ R) :
    embed_l M1 M2 (Vis (inr1 (Put v)) ktr) =
      Vis (inr1 (Get _)) (fun s => Vis (inr1 (Put (update_fst s v))) (fun _ => embed_l M1 M2 (ktr tt))).
  Proof.
    unfold embed_l at 1. rewrite embed_state_put. rewrite map_event_vis. ss.
    eapply observe_eta. ss. f_equal. extensionality x. rewrite map_event_vis. ss.
  Qed.

  Lemma embed_l_bind
        A B (itr: itree _ A) (ktr: ktree _ A B)
    :
    @embed_l M1 M2 B (itr >>= ktr) =
      (@embed_l M1 M2 A itr) >>= (fun a => @embed_l M1 M2 B (ktr a)).
  Proof.
    eapply bisim_is_eq. revert itr ktr. ginit. gcofix CIH; i.
    ides itr; grind.
    { rewrite embed_l_ret. ired.
      gfinal. right. eapply paco2_mon.
      2:{ instantiate (1:=bot2). ss. }
      eapply eq_is_bisim. auto.
    }
    { rewrite ! embed_l_tau. rewrite bind_tau.
      gstep. eapply EqTau. gbase. eauto.
    }
    { revert k. destruct e as [[[]|]|[|]]; i.
      { rewrite ! embed_l_vis_eventE.
        ired. gstep. eapply EqVis.
        i. gbase. eauto.
      }
      { rewrite ! embed_l_vis_cE.
        ired. gstep. eapply EqVis.
        i. gbase. eauto.
      }
      { rewrite ! embed_l_vis_callE.
        ired. gstep. eapply EqVis.
        i. gbase. eauto.
      }
      { rewrite ! embed_l_vis_putE.
        ired. gstep. eapply EqVis. i. ss.
        ired. gstep. eapply EqVis. i. ss.
        i. gbase. eauto.
      }
      { rewrite ! embed_l_vis_getE.
        ired. gstep. eapply EqVis. i. ss.
        i. gbase. eauto.
      }
    }
  Qed.

  Lemma embed_l_trigger_eventE
        R X (e: eventE X) (ktr : ktree _ X R) :
    embed_l M1 M2 (x <- trigger e;; ktr x) =
      x <- trigger (embed_event_l e);; embed_l M1 M2 (ktr x).
  Proof. rewrite 2 bind_trigger. eapply embed_l_vis_eventE. Qed.

  Lemma embed_l_trigger_cE
        R X (e: cE X) (ktr : ktree _ X R) :
    embed_l M1 M2 (x <- trigger e;; ktr x) =
      x <- trigger (e);; embed_l M1 M2 (ktr x).
  Proof. rewrite 2 bind_trigger. eapply embed_l_vis_cE. Qed.

  Lemma embed_l_trigger_getE
        R (ktr : ktree _ _ R) :
    embed_l M1 M2 (x <- trigger (Get _);; ktr x) =
      x <- trigger (Get _);; (embed_l M1 M2 (ktr (fst x))).
  Proof. rewrite 2 bind_trigger. eapply embed_l_vis_getE. Qed.

  Lemma embed_l_trigger_putE
        R v (ktr : ktree _ _ R) :
    embed_l M1 M2 (x <- trigger (Put v);; ktr x) =
      x <- trigger (Get _);; (x <- trigger (Put (update_fst x v));; (embed_l M1 M2 (ktr x))).
  Proof.
    rewrite bind_trigger. setoid_rewrite embed_l_vis_putE.
    rewrite bind_trigger. repeat f_equal. extensionality s. rewrite bind_trigger.
    repeat f_equal. extensionality x. destruct x; ss.
  Qed.

  Lemma embed_l_trigger_eventE2
        X (e: eventE X)
    :
    embed_l M1 M2 (trigger e) = trigger (embed_event_l e) >>= (fun r => Ret r).
  Proof.
    rewrite (bind_ret_r_rev (trigger e)).
    rewrite embed_l_trigger_eventE. f_equal. extensionality x.
    apply embed_l_ret.
  Qed.

  Lemma embed_l_trigger_cE2
        X (e: cE X) :
    embed_l M1 M2 (trigger e) = trigger e >>= (fun r => Ret r).
  Proof.
    rewrite (bind_ret_r_rev (trigger e)).
    rewrite embed_l_trigger_cE. f_equal. extensionality x.
    apply embed_l_ret.
  Qed.

  Lemma embed_l_trigger_getE2
    :
    embed_l M1 M2 (trigger (Get _)) = trigger (Get _) >>= (fun r => Ret (fst r)).
  Proof.
    rewrite (bind_ret_r_rev (trigger _)).
    rewrite embed_l_trigger_getE. f_equal. extensionality x.
    apply embed_l_ret.
  Qed.

  Lemma embed_l_trigger_putE2
        v:
    embed_l M1 M2 (trigger (Put v)) =
      trigger (Get _) >>= (fun x => x <- trigger (Put (update_fst x v));; Ret x).
  Proof.
    rewrite (bind_ret_r_rev (trigger _)).
    rewrite embed_l_trigger_putE. f_equal. extensionality x.
    f_equal. extensionality s.
    apply embed_l_ret.
  Qed.

  Lemma embed_l_UB
        R:
    @embed_l M1 M2 R UB = UB.
  Proof.
    unfold UB. rewrite embed_l_bind. rewrite embed_l_trigger_eventE2. grind.
  Qed.

  Lemma embed_l_unwrap
        X x
    :
    @embed_l M1 M2 X (unwrap x) = unwrap x.
  Proof.
    unfold unwrap. des_ifs.
    { eapply embed_l_ret. }
    { eapply embed_l_UB. }
  Qed.

  Lemma embed_l_ext
        R (itr0 itr1: itree _ R)
    :
    itr0 = itr1 -> embed_l M1 M2 itr0 = embed_l M1 M2 itr1
  .
  Proof. i; subst; reflexivity. Qed.



  Lemma embed_r_ret R (r : R) :
    embed_r M1 M2 (Ret r) = Ret r.
  Proof. eapply observe_eta. ss. Qed.

  Lemma embed_r_tau R (itr : itree _ R) :
    embed_r M1 M2 (tau;; itr) = tau;; (embed_r M1 M2 itr).
  Proof. eapply observe_eta. ss. Qed.

  Lemma embed_r_vis_eventE R X (e : eventE X) (ktr : ktree _ X R) :
    embed_r M1 M2 (Vis (inl1 (inl1 (inl1 e))) ktr) =
      Vis (inl1 (inl1 (inl1 (@embed_event_r M1.(ident) M2.(ident) _ e)))) (fun x => embed_r M1 M2 (ktr x)).
  Proof. eapply observe_eta. ss. Qed.

  Lemma embed_r_vis_cE R X (e : cE X) (ktr : ktree _ X R) :
    embed_r M1 M2 (Vis (inl1 (inl1 (inr1 e))) ktr) =
      Vis (inl1 (inl1 (inr1 e))) (fun x => embed_r M1 M2 (ktr x)).
  Proof. eapply observe_eta. ss. Qed.

  Lemma embed_r_vis_callE R X (e : callE X) (ktr : ktree _ X R) :
    embed_r M1 M2 (Vis (inl1 (inr1 e)) ktr) =
      Vis (inl1 (inr1 e)) (fun x => embed_r M1 M2 (ktr x)).
  Proof. eapply observe_eta. ss. Qed.

  Lemma embed_r_vis_getE R (ktr : ktree _ _ R) :
    embed_r M1 M2 (Vis (inr1 (Get _)) ktr) =
      Vis (inr1 (Get _)) (fun s => embed_r M1 M2 (ktr (snd s))).
  Proof. eapply observe_eta. ss. Qed.

  Lemma embed_r_vis_putE R v (ktr : ktree _ _ R) :
    embed_r M1 M2 (Vis (inr1 (Put v)) ktr) =
      Vis (inr1 (Get _)) (fun s => Vis (inr1 (Put (update_snd s v))) (fun _ => embed_r M1 M2 (ktr tt))).
  Proof.
    unfold embed_r at 1. rewrite embed_state_put. rewrite map_event_vis. ss.
    eapply observe_eta. ss. f_equal. extensionality x. rewrite map_event_vis. ss.
  Qed.

  Lemma embed_r_bind
        A B (itr: itree _ A) (ktr: ktree _ A B)
    :
    @embed_r M1 M2 B (itr >>= ktr) =
      (@embed_r M1 M2 A itr) >>= (fun a => @embed_r M1 M2 B (ktr a)).
  Proof.
    eapply bisim_is_eq. revert itr ktr. ginit. gcofix CIH; i.
    ides itr; grind.
    { rewrite embed_r_ret. ired.
      gfinal. right. eapply paco2_mon.
      2:{ instantiate (1:=bot2). ss. }
      eapply eq_is_bisim. auto.
    }
    { rewrite ! embed_r_tau. rewrite bind_tau.
      gstep. eapply EqTau. gbase. eauto.
    }
    { revert k. destruct e as [[[]|]|[|]]; i.
      { rewrite ! embed_r_vis_eventE.
        ired. gstep. eapply EqVis.
        i. gbase. eauto.
      }
      { rewrite ! embed_r_vis_cE.
        ired. gstep. eapply EqVis.
        i. gbase. eauto.
      }
      { rewrite ! embed_r_vis_callE.
        ired. gstep. eapply EqVis.
        i. gbase. eauto.
      }
      { rewrite ! embed_r_vis_putE.
        ired. gstep. eapply EqVis. i. ss.
        ired. gstep. eapply EqVis. i. ss.
        i. gbase. eauto.
      }
      { rewrite ! embed_r_vis_getE.
        ired. gstep. eapply EqVis. i. ss.
        i. gbase. eauto.
      }
    }
  Qed.

  Lemma embed_r_trigger_eventE
        R X (e: eventE X) (ktr : ktree _ X R) :
    embed_r M1 M2 (x <- trigger e;; ktr x) =
      x <- trigger (embed_event_r e);; embed_r M1 M2 (ktr x).
  Proof. rewrite 2 bind_trigger. eapply embed_r_vis_eventE. Qed.

  Lemma embed_r_trigger_cE
        R X (e: cE X) (ktr : ktree _ X R) :
    embed_r M1 M2 (x <- trigger e;; ktr x) =
      x <- trigger (e);; embed_r M1 M2 (ktr x).
  Proof. rewrite 2 bind_trigger. eapply embed_r_vis_cE. Qed.

  Lemma embed_r_trigger_getE
        R (ktr : ktree _ _ R) :
    embed_r M1 M2 (x <- trigger (Get _);; ktr x) =
      x <- trigger (Get _);; (embed_r M1 M2 (ktr (snd x))).
  Proof. rewrite 2 bind_trigger. eapply embed_r_vis_getE. Qed.

  Lemma embed_r_trigger_putE
        R v (ktr : ktree _ _ R) :
    embed_r M1 M2 (x <- trigger (Put v);; ktr x) =
      x <- trigger (Get _);; (x <- trigger (Put (update_snd x v));; (embed_r M1 M2 (ktr x))).
  Proof.
    rewrite bind_trigger. setoid_rewrite embed_r_vis_putE.
    rewrite bind_trigger. repeat f_equal. extensionality s. rewrite bind_trigger.
    repeat f_equal. extensionality x. destruct x; ss.
  Qed.

  Lemma embed_r_trigger_eventE2
        X (e: eventE X)
    :
    embed_r M1 M2 (trigger e) = trigger (embed_event_r e) >>= (fun r => Ret r).
  Proof.
    rewrite (bind_ret_r_rev (trigger e)).
    rewrite embed_r_trigger_eventE. f_equal. extensionality x.
    apply embed_r_ret.
  Qed.

  Lemma embed_r_trigger_cE2
        X (e: cE X) :
    embed_r M1 M2 (trigger e) = trigger e >>= (fun r => Ret r).
  Proof.
    rewrite (bind_ret_r_rev (trigger e)).
    rewrite embed_r_trigger_cE. f_equal. extensionality x.
    apply embed_r_ret.
  Qed.

  Lemma embed_r_trigger_getE2
    :
    embed_r M1 M2 (trigger (Get _)) = trigger (Get _) >>= (fun r => Ret (snd r)).
  Proof.
    rewrite (bind_ret_r_rev (trigger _)).
    rewrite embed_r_trigger_getE. f_equal. extensionality x.
    apply embed_r_ret.
  Qed.

  Lemma embed_r_trigger_putE2
        v:
    embed_r M1 M2 (trigger (Put v)) =
      trigger (Get _) >>= (fun x => x <- trigger (Put (update_snd x v));; Ret x).
  Proof.
    rewrite (bind_ret_r_rev (trigger _)).
    rewrite embed_r_trigger_putE. f_equal. extensionality x.
    f_equal. extensionality s.
    apply embed_r_ret.
  Qed.

  Lemma embed_r_UB
        R:
    @embed_r M1 M2 R UB = UB.
  Proof.
    unfold UB. rewrite embed_r_bind. rewrite embed_r_trigger_eventE2. grind.
  Qed.

  Lemma embed_r_unwrap
        X x
    :
    @embed_r M1 M2 X (unwrap x) = unwrap x.
  Proof.
    unfold unwrap. des_ifs.
    { eapply embed_r_ret. }
    { eapply embed_r_UB. }
  Qed.

  Lemma embed_r_ext
        R (itr0 itr1: itree _ R)
    :
    itr0 = itr1 -> embed_r M1 M2 itr0 = embed_r M1 M2 itr1
  .
  Proof. i; subst; reflexivity. Qed.

End EMBEDS.

From Fairness Require Export Red IRed.
Global Program Instance embed_state_rdb: red_database (mk_box (@embed_state)) :=
  mk_rdb
    0
    (mk_box embed_state_bind)
    (mk_box embed_state_tau2)
    (mk_box embed_state_ret)
    (mk_box embed_state_trigger_eventE2)
    (mk_box embed_state_trigger_put2)
    (mk_box embed_state_trigger_get2)
    (mk_box embed_state_trigger_eventE2)
    (mk_box embed_state_UB)
    (mk_box embed_state_UB)
    (mk_box embed_state_unwrap)
    (mk_box embed_state_UB)
    (mk_box embed_state_UB)
    (mk_box embed_state_UB)
    (mk_box embed_state_ext)
.

Global Program Instance embed_l_rdb: red_database (mk_box (@embed_l)) :=
  mk_rdb
    0
    (mk_box embed_l_bind)
    (mk_box embed_l_tau)
    (mk_box embed_l_ret)
    (mk_box embed_l_trigger_eventE2)
    (mk_box embed_l_trigger_cE2)
    (mk_box embed_l_trigger_putE2)
    (mk_box embed_l_trigger_getE2)
    (mk_box embed_l_UB)
    (mk_box embed_l_UB)
    (mk_box embed_l_unwrap)
    (mk_box embed_l_UB)
    (mk_box embed_l_UB)
    (mk_box embed_l_UB)
    (mk_box embed_l_ext)
.

Global Program Instance embed_r_rdb: red_database (mk_box (@embed_r)) :=
  mk_rdb
    0
    (mk_box embed_r_bind)
    (mk_box embed_r_tau)
    (mk_box embed_r_ret)
    (mk_box embed_r_trigger_eventE2)
    (mk_box embed_r_trigger_cE2)
    (mk_box embed_r_trigger_putE2)
    (mk_box embed_r_trigger_getE2)
    (mk_box embed_r_UB)
    (mk_box embed_r_UB)
    (mk_box embed_r_unwrap)
    (mk_box embed_r_UB)
    (mk_box embed_r_UB)
    (mk_box embed_r_UB)
    (mk_box embed_r_ext)
.
