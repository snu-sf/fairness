From sflib Require Import sflib.
From ITree Require Export ITree.
From Paco Require Import paco.

Require Export Coq.Strings.String.
From Coq Require Import Program.

From Fairness Require Export ITreeLib EventCategory FairBeh NatStructs Optics.
From Fairness Require Export Mod.

Set Implicit Arguments.

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
Module OMod.

  Section CLOSED.
    Variable omd: Mod.t.
    Variable md: Mod.t.

    Definition closed_state: Type := omd.(Mod.state) * md.(Mod.state).
    Definition closed_ident: ID := id_sum omd.(Mod.ident) md.(Mod.ident).
    Definition closed_st_init: closed_state := (omd.(Mod.st_init), md.(Mod.st_init)).

    Definition embed_callee X
      : programE md.(Mod.ident) md.(Mod.state) X ->
        programE closed_ident closed_state X.
    Proof.
      intro e. destruct e as [[[e|e]|e]|e].
      - exact (((embed_event_r e|)|)|)%sum.
      - exact (((|e)|)|)%sum.
      - exact ((|e)|)%sum.
      - exact (|embed_lens sndl e)%sum.
    Defined.

    Definition embed_itree {R}:
      (itree (programE (Mod.ident md) (Mod.state md)) R) ->
      (itree (programE closed_ident closed_state) R) :=
      map_event embed_callee.

    Definition close_itree {R}:
      (itree (programE omd.(Mod.ident) omd.(Mod.state)) R) ->
      (itree (programE closed_ident closed_state) R).
    Proof.
      (*ub for undefined fn call*)
      eapply ITree.iter. intros itr. destruct (observe itr).
      - exact (Ret (inr r)).
      - exact (Ret (inl t)).
      - destruct e as [[[eE|cE]|caE]|stE].
        + exact (Vis (((embed_event_l eE|)|)|)%sum (fun x => Ret (inl (k x)))).
        + exact (Vis (((|cE)|)|)%sum (fun x => Ret (inl (k x)))).
        + destruct caE.
          destruct (md.(Mod.funs) fn) eqn:FUN.
          { clear FUN. specialize (k0 arg). eapply ITree.bind.
            exact (Vis (((|Yield)|)|)%sum (fun _ => embed_itree k0)).
            intros rv. exact (Ret (inl (k rv))). }
          { exact (Vis (((embed_event_l Undefined|)|)|)%sum (Empty_set_rect _)). }
        + eapply (map_event (embed_right (embed_lens fstl))).
          exact (Vis (|stE)%sum (fun x => Ret (inl (k x)))).
    Defined.

    Definition closed_funs: fname -> option (ktree _ Any.t Any.t) :=
      fun fn =>
        match (omd.(Mod.funs) fn) with
        | None => None
        | Some body => Some (fun args => close_itree (body args))
        end.

  End CLOSED.

  Definition close (om: Mod.t) (m: Mod.t): Mod.t :=
    @Mod.mk
      (closed_state om m)
      (closed_ident om m)
      (closed_st_init om m)
      (closed_funs om m).

  Definition call {R} {ID E} `{@eventE ID -< E} `{callE -< E} {A} (fn: string) (arg: A): itree E R :=
    r <- trigger (Call fn arg↑);;
    unwrap (r↓)
  .

  Definition callR R {ID E} `{@eventE ID -< E} `{callE -< E} {A} (fn: string) (arg: A): itree E R :=
    r <- trigger (Call fn arg↑);;
    unwrap (r↓)
  .
End OMod.

Section RED.

  Import OMod.

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

  Lemma embed_itree_ext
        omd md R (itr0 itr1: itree _ R)
    :
    itr0 = itr1 -> OMod.embed_itree omd md itr0 = OMod.embed_itree omd md itr1
  .
  Proof. i; subst; reflexivity. Qed.

  Lemma embed_itree_ret
        omd md
        R
        (r: R)
    :
    @embed_itree omd md R (Ret r) = Ret r.
  Proof. unfold embed_itree. eapply map_event_ret. Qed. 

  Lemma embed_itree_tau
        omd md
        R
        itr
    :
    @embed_itree omd md R (tau;; itr) = tau;; @embed_itree omd md R itr.
  Proof. unfold embed_itree. eapply map_event_tau. Qed.

  Lemma embed_itree_vis_eventE
        omd md
        R
        X (ee: @eventE _ X) ktr
    :
    @embed_itree omd md R (Vis (((ee|)|)|)%sum ktr) =
      Vis (((embed_event_r ee|)|)|)%sum (fun x => embed_itree omd md (ktr x)).
  Proof. unfold embed_itree. eapply map_event_vis. Qed.

  Lemma embed_itree_trigger_eventE
        omd md
        R
        X (ee: @eventE _ X) ktr
    :
    @embed_itree omd md R (trigger ee >>= ktr) =
      x <- trigger (embed_event_r ee);; (embed_itree omd md (ktr x)).
  Proof. unfold embed_itree. eapply map_event_trigger. Qed.

  Lemma embed_itree_vis_cE
        omd md
        R
        X (ce: @cE X) ktr
    :
    @embed_itree omd md R (Vis (((|ce)|)|)%sum ktr) =
      Vis (((|ce)|)|)%sum (fun x => embed_itree omd md (ktr x)).
  Proof. unfold embed_itree. eapply map_event_vis. Qed.

  Lemma embed_itree_trigger_cE
        omd md
        R
        X (ce: @cE X) ktr
    :
    @embed_itree omd md R (trigger ce >>= ktr) =
      x <- trigger ce;; (embed_itree omd md (ktr x)).
  Proof. unfold embed_itree. eapply map_event_trigger. Qed.

  Lemma embed_itree_vis_callE
    omd md
    R
    X (cae : callE X) ktr
    : @embed_itree omd md R (Vis ((|cae)|)%sum ktr) =
        Vis ((|cae)|)%sum (fun x => embed_itree omd md (ktr x)).
  Proof. unfold embed_itree. eapply map_event_vis. Qed.

  Lemma embed_itree_trigger_callE
    omd md
    R X (cae : callE X) ktr
    :
    @embed_itree omd md R (trigger cae >>= ktr) = x <- trigger cae;; embed_itree omd md (ktr x).
  Proof. unfold embed_itree. eapply map_event_trigger. Qed.

  Lemma embed_itree_vis_sE
        omd md
        R
        X (se: @sE md.(Mod.state) X) ktr
    :
    @embed_itree omd md R (Vis (|se)%sum ktr) =
      Vis (|embed_lens sndl se)%sum (fun x => embed_itree omd md (ktr x)).
  Proof. unfold embed_itree. eapply map_event_vis. Qed.

  Lemma embed_itree_vis_rmw
    omd md R X (rmw : md.(Mod.state) -> md.(Mod.state) * X) ktr
    : @embed_itree omd md R (Vis (inr1 (Rmw rmw)) ktr) =
        Vis (inr1 (Rmw (apply_lens sndl rmw))) (fun x => embed_itree omd md (ktr x)).
  Proof. unfold embed_itree. eapply map_event_vis. Qed.

  Lemma embed_itree_trigger_rmw
    omd md R X (state : md.(Mod.state) -> md.(Mod.state) * X) ktr
    : @embed_itree omd md R (trigger (Rmw state) >>= ktr) =
        x <- trigger (Rmw (apply_lens sndl state));; embed_itree omd md (ktr x).
  Proof. unfold embed_itree. eapply map_event_trigger. Qed.

  Lemma embed_itree_bind
        omd md
        A B (itr: itree _ A) (ktr: ktree _ A B)
    :
    @embed_itree omd md B (itr >>= ktr) =
      (@embed_itree omd md A itr) >>= (fun a => @embed_itree omd md B (ktr a)).
  Proof. unfold embed_itree. eapply map_event_bind. Qed.

  Lemma embed_itree_trigger_eventE2
        omd md
        X ee
    :
    @embed_itree omd md X (trigger ee) =
      trigger (embed_event_r ee).
  Proof.
    unfold trigger. setoid_rewrite embed_itree_vis_eventE.
    eapply observe_eta. ss. f_equal. extensionalities x. eapply embed_itree_ret.
  Qed.

  Lemma embed_itree_trigger_cE2
        omd md
        X (ce: @cE X)
    :
    @embed_itree omd md X (trigger ce) = trigger ce.
  Proof.
    unfold trigger. setoid_rewrite embed_itree_vis_cE.
    eapply observe_eta. ss. f_equal. extensionalities x. eapply embed_itree_ret.
  Qed.

  Lemma embed_itree_UB
        omd md
        R
    :
    @embed_itree omd md R UB = UB.
  Proof.
    unfold UB. rewrite embed_itree_bind. rewrite embed_itree_trigger_eventE2. grind.
  Qed.

  Lemma embed_itree_unwrap
        omd md
        X x
    :
    @embed_itree omd md X (unwrap x) = unwrap x.
  Proof.
    unfold unwrap. des_ifs.
    { eapply embed_itree_ret. }
    { eapply embed_itree_UB. }
  Qed.

  Local Opaque embed_itree.

  Lemma close_itree_ext
        omd md R (itr0 itr1: itree _ R)
    :
    itr0 = itr1 -> OMod.close_itree omd md itr0 = OMod.close_itree omd md itr1
  .
  Proof. i; subst; reflexivity. Qed.

  Lemma close_itree_ret
        omd md
        R r
    :
    @close_itree omd md R (Ret r) = Ret r.
  Proof. unfold close_itree. rewrite unfold_iter. grind. Qed.

  Lemma close_itree_tau
        omd md
        R itr
    :
    @close_itree omd md R (Tau itr) = Tau (@close_itree omd md R itr).
  Proof. unfold close_itree. rewrite unfold_iter. grind. Qed.

  Lemma close_itree_vis_eventE
        omd md
        R
        X (ee: @eventE _ X) ktr
    :
    @close_itree omd md R (Vis (((ee|)|)|)%sum ktr) =
      Vis (((embed_event_l ee|)|)|)%sum (fun x => tau;; close_itree omd md (ktr x)).
  Proof.
    unfold close_itree at 1. rewrite unfold_iter. grind.
    apply observe_eta. ss. f_equal. extensionality x. grind.
  Qed.

  Lemma close_itree_trigger_eventE
        omd md
        R
        X (ee: @eventE _ X) ktr
    :
    @close_itree omd md R (trigger ee >>= ktr) =
      x <- trigger (embed_event_l ee);; tau;; (close_itree omd md (ktr x)).
  Proof. rewrite ! bind_trigger. apply close_itree_vis_eventE. Qed.

  Lemma close_itree_vis_cE
        omd md
        R
        X (ce: @cE X) ktr
    :
    @close_itree omd md R (Vis (((|ce)|)|)%sum ktr) =
      Vis (((|ce)|)|)%sum (fun x => tau;; close_itree omd md (ktr x)).
  Proof.
    unfold close_itree at 1. rewrite unfold_iter. grind.
    apply observe_eta. ss. f_equal. extensionality x. grind.
  Qed.

  Lemma close_itree_trigger_cE
        omd md
        R
        X (ce: @cE X) ktr
    :
    @close_itree omd md R (trigger ce >>= ktr) =
      x <- trigger ce;; tau;; (close_itree omd md (ktr x)).
  Proof. rewrite ! bind_trigger. apply close_itree_vis_cE. Qed.

  Lemma close_itree_vis_sE
        omd md
        R
        X (se: @sE omd.(Mod.state) X) ktr
    :
    @close_itree omd md R (Vis (|se)%sum ktr) =
      Vis (inr1 (embed_lens fstl se)) (fun x => tau;; close_itree omd md (ktr x)).
  Proof.
    unfold close_itree at 1. rewrite unfold_iter. grind.
    rewrite map_event_vis. grind.
    apply observe_eta. ss. f_equal. extensionalities x. rewrite map_event_ret. grind.
  Qed.

  Lemma close_itree_vis_rmw
        omd md
        R
        X (rmw: omd.(Mod.state) -> omd.(Mod.state) * X) ktr
    :
    @close_itree omd md R (Vis (|Rmw rmw)%sum ktr) =
      Vis (inr1 (Rmw (apply_lens fstl rmw))) (fun x => tau;; close_itree omd md (ktr x)).
  Proof. eapply close_itree_vis_sE. Qed.

  Lemma close_itree_trigger_rmw
        omd md
        R
        X (rmw : omd.(Mod.state) -> omd.(Mod.state) * X) ktr
    :
    @close_itree omd md R (trigger (Rmw rmw) >>= ktr) =
      x <- trigger (Rmw (apply_lens fstl rmw));; tau;; close_itree omd md (ktr x).
  Proof.
    rewrite ! bind_trigger. eapply close_itree_vis_rmw.
  Qed.

  Lemma close_itree_vis_call
        omd md
        R
        fn args ktr
    :
    @close_itree omd md R (Vis ((|Call fn args)|)%sum ktr) =
      match (md.(Mod.funs) fn) with
      | Some body =>
          Vis (((|Yield)|)|)%sum (fun _ => rv <- embed_itree omd md (body args);; tau;; close_itree omd md (ktr rv))
      | None => Vis (((embed_event_l Undefined|)|)|)%sum (Empty_set_rect _)
      end.
  Proof.
    unfold close_itree. rewrite unfold_iter. grind.
    eapply observe_eta. ss. f_equal. extensionality x. grind.
    eapply observe_eta. ss. f_equal. extensionality x. destruct x.
  Qed.

  Lemma close_itree_trigger_call
        omd md
        R
        fn args ktr
    :
    @close_itree omd md R (trigger (|Call fn args)%sum >>= ktr) =
      match (md.(Mod.funs) fn) with
      | Some body =>
          _ <- trigger (Yield);; rv <- embed_itree omd md (body args);; tau;; close_itree omd md (ktr rv)
      | None => trigger (embed_event_l Undefined) >>= (Empty_set_rect _)
      end.
  Proof.
    rewrite bind_trigger. setoid_rewrite close_itree_vis_call. des_ifs.
    - rewrite bind_trigger. auto.
    - rewrite bind_trigger. auto.
  Qed.

  Lemma close_itree_bind
        omd md
        A B (itr: itree _ A) (ktr: ktree _ A B)
    :
    @close_itree omd md B (itr >>= ktr) =
      (@close_itree omd md A itr) >>= (fun a => @close_itree omd md B (ktr a)).
  Proof.
    eapply bisim_is_eq. revert itr ktr. ginit. gcofix CIH; i.
    ides itr; grind.
    { rewrite close_itree_ret. ired.
      gfinal. right. eapply paco2_mon.
      2:{ instantiate (1:=bot2). ss. }
      eapply eq_is_bisim. auto.
    }
    { rewrite ! close_itree_tau. rewrite bind_tau.
      gstep. eapply EqTau. gbase. eauto.
    }
    { revert k. destruct e as [[[|]|[]]|[]]; i.
      { rewrite ! close_itree_vis_eventE.
        ired. gstep. eapply EqVis. i. ss.
        ired. gstep. eapply EqTau.
        gbase. eauto.
      }
      { rewrite ! close_itree_vis_cE.
        ired. gstep. eapply EqVis. i. ss.
        ired. gstep. eapply EqTau.
        gbase. eauto.
      }
      { rewrite ! close_itree_vis_call. des_ifs.
        { ired. gstep. eapply EqVis. i. ss.
          guclo eqit_clo_bind. econs.
          { eapply eq_is_bisim. eauto. }
          { i. subst. ired. gstep. eapply EqTau. gbase. eauto. }
        }
        { ired. gstep. eapply EqVis. i. ss. }
      }
      { rewrite ! close_itree_vis_rmw.
        ired. gstep. econs. i.
        ired. gstep. econs.
        gbase. eapply CIH.
      }
    }
  Qed.

  Lemma close_itree_trigger_eventE2
        omd md
        X ee
    :
    @close_itree omd md X (trigger ee) =
      trigger (embed_event_l ee) >>= (fun r => tau;; Ret r).
  Proof.
    rewrite (bind_ret_r_rev (trigger ee)).
    setoid_rewrite close_itree_trigger_eventE. grind. apply close_itree_ret.
  Qed.

  Lemma close_itree_trigger_cE2
        omd md
        X (ce: @cE _)
    :
    @close_itree omd md X (trigger ce) =
      trigger (ce) >>= (fun r => tau;; Ret r).
  Proof.
    rewrite (bind_ret_r_rev (trigger ce)).
    setoid_rewrite close_itree_trigger_cE. grind. apply close_itree_ret.
  Qed.

  Lemma close_itree_trigger_call2
        omd md
        fn args
    :
    @close_itree omd md _ (trigger (Call fn args)) =
      match (md.(Mod.funs) fn) with
      | Some body =>
          trigger (Yield) >>= (fun _ => embed_itree omd md (body args) >>= (fun rv => tau;; Ret rv))
      | None => UB
      end.
  Proof.
    rewrite (bind_ret_r_rev (trigger (Call _ _))).
    setoid_rewrite close_itree_trigger_call. grind.
    { apply close_itree_ret. }
  Qed.

  Lemma close_itree_UB
        omd md
        R
    :
    @close_itree omd md R UB = UB.
  Proof.
    unfold UB. rewrite close_itree_bind. rewrite close_itree_trigger_eventE2. grind.
  Qed.

  Lemma close_itree_unwrap
        omd md
        X x
    :
    @close_itree omd md X (unwrap x) = unwrap x.
  Proof.
    unfold unwrap. des_ifs.
    { eapply close_itree_ret. }
    { eapply close_itree_UB. }
  Qed.

  Lemma close_itree_call
        omd md
        A R
        fn (arg: A)
    :
    @close_itree omd md R (call fn arg) =
      match (md.(Mod.funs) fn) with
      | Some body =>
          trigger (Yield) >>= (fun _ => embed_itree omd md (body (arg↑)) >>= (fun rv => tau;; unwrap (rv↓)))
      | None => UB
      end.
  Proof.
    unfold call. rewrite close_itree_bind. rewrite close_itree_trigger_call2. grind.
    { apply close_itree_unwrap. }
    { unfold UB. grind. }
  Qed.

  Lemma close_itree_callR
        omd md
        A R
        fn (arg: A)
    :
    @close_itree omd md R (callR R fn arg) =
      match (md.(Mod.funs) fn) with
      | Some body =>
          trigger (Yield) >>= (fun _ => embed_itree omd md (body (arg↑)) >>= (fun rv => tau;; unwrap (rv↓)))
      | None => UB
      end.
  Proof.
    unfold callR. rewrite close_itree_bind. rewrite close_itree_trigger_call2. grind.
    { apply close_itree_unwrap. }
    { unfold UB. grind. }
  Qed.
End RED.
Global Opaque OMod.embed_itree.
Global Opaque OMod.close_itree.

From Fairness Require Export Red IRed.
Global Program Instance embed_itree_rdb: red_database (mk_box (@OMod.embed_itree)) :=
  mk_rdb
    0
    (mk_box embed_itree_bind)
    (mk_box embed_itree_tau)
    (mk_box embed_itree_ret)
    (mk_box embed_itree_trigger_eventE2)
    (mk_box embed_itree_trigger_cE2)
    (mk_box embed_itree_trigger_rmw)
    (mk_box embed_itree_trigger_rmw)
    (mk_box embed_itree_UB)
    (mk_box embed_itree_UB)
    (mk_box embed_itree_unwrap)
    (mk_box embed_itree_UB)
    (mk_box embed_itree_UB)
    (mk_box embed_itree_UB)
    (mk_box embed_itree_ext)
.

Global Program Instance close_itree_rdb: red_database (mk_box (@OMod.close_itree)) :=
  mk_rdb
    0
    (mk_box close_itree_bind)
    (mk_box close_itree_tau)
    (mk_box close_itree_ret)
    (mk_box close_itree_trigger_eventE2)
    (mk_box close_itree_trigger_cE2)
    (mk_box close_itree_trigger_rmw)
    (mk_box close_itree_trigger_rmw)
    (mk_box close_itree_UB)
    (mk_box close_itree_UB)
    (mk_box close_itree_unwrap)
    (mk_box close_itree_UB)
    (mk_box close_itree_UB)
    (mk_box close_itree_UB)
    (mk_box close_itree_ext)
.
(* close_itree_trigger_call2 *)
(* close_itree_call *)
(* close_itree_callR *)
