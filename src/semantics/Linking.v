From sflib Require Import sflib.
From ITree Require Export ITree.
From Paco Require Import paco.

Require Export Coq.Strings.String.
From Coq Require Import Program.

From Fairness Require Export ITreeLib EventCategory FairBeh NatStructs Optics.
From Fairness Require Export Mod.

Set Implicit Arguments.

Section ADD.

  Import Mod.
  Variable M1 M2 : Mod.t.

  Definition emb_l
    : forall X, threadE (ident M1) (state M1) X -> threadE (ident M1 + ident M2)%type (state M1 * state M2) X :=
    plmap inlp fstl.

  Definition emb_r
    : forall X, threadE (ident M2) (state M2) X -> threadE (ident M1 + ident M2)%type (state M1 * state M2) X :=
    plmap inrp sndl.

  Definition add_funs : fname -> option (ktree _ Any.t Any.t) :=
    fun fn =>
      match M1.(funs) fn, M2.(funs) fn with
      | Some fn_body, None => Some (fun args => map_event emb_l (fn_body args))
      | None, Some fn_body => Some (fun args => map_event emb_r (fn_body args))
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

    Definition emb_callee
      : forall X, threadE (Mod.ident md) (Mod.state md) X -> threadE closed_ident closed_state X :=
      plmap inrp sndl.

    Definition close_itree {R}:
      (itree (threadE omd.(Mod.ident) omd.(Mod.state)) R) ->
      (itree (threadE closed_ident closed_state) R).
    Proof.
      (*ub for undefined fn call*)
      eapply ITree.iter. intros itr. destruct (observe itr).
      - exact (Ret (inr r)).
      - exact (Ret (inl t)).
      - destruct e as [[[eE|cE]|caE]|stE].
        + exact (Vis (((map_prism inlp eE|)|)|)%sum (fun x => Ret (inl (k x)))).
        + exact (Vis (((|cE)|)|)%sum (fun x => Ret (inl (k x)))).
        + destruct caE.
          destruct (md.(Mod.funs) fn) eqn:FUN.
          { clear FUN. specialize (k0 arg). eapply ITree.bind.
            exact (Vis (((|Yield)|)|)%sum (fun _ => map_event emb_callee k0)).
            intros rv. exact (Ret (inl (k rv))). }
          { exact (Vis (((Undefined|)|)|)%sum (Empty_set_rect _)). }
        + eapply (map_event (embed_right (map_lens fstl))).
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
      Vis (((map_prism inlp ee|)|)|)%sum (fun x => tau;; close_itree omd md (ktr x)).
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
      x <- trigger (map_prism inlp ee);; tau;; (close_itree omd md (ktr x)).
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
      Vis (inr1 (map_lens fstl se)) (fun x => tau;; close_itree omd md (ktr x)).
  Proof.
    unfold close_itree at 1. rewrite unfold_iter. grind.
    rewrite map_event_vis. grind.
    apply observe_eta. ss. f_equal. extensionalities x. rewrite map_event_ret. grind.
  Qed.

  Lemma close_itree_vis_state
        omd md
        R
        X (run: omd.(Mod.state) -> omd.(Mod.state) * X) ktr
    :
    @close_itree omd md R (Vis (|State run)%sum ktr) =
      Vis (inr1 (State (lens_state fstl run))) (fun x => tau;; close_itree omd md (ktr x)).
  Proof. eapply close_itree_vis_sE. Qed.

  Lemma close_itree_vis_get
    omd md
    R
    X (p : omd.(Mod.state) -> X) ktr
    :
    @close_itree omd md R (Vis (|Get p)%sum ktr) =
      Vis (|Get (p ∘ Lens.view fstl))%sum (fun x => tau;; close_itree omd md (ktr x)).
  Proof. rewrite close_itree_vis_sE. rewrite map_lens_Get. ss. Qed.

  Lemma close_itree_trigger_state
        omd md
        R
        X (run : omd.(Mod.state) -> omd.(Mod.state) * X) ktr
    :
    @close_itree omd md R (trigger (State run) >>= ktr) =
      x <- trigger (State (lens_state fstl run));; tau;; close_itree omd md (ktr x).
  Proof.
    rewrite ! bind_trigger. eapply close_itree_vis_state.
  Qed.

  Lemma close_itree_trigger_get
    omd md
    R
    X (p : omd.(Mod.state) -> X) ktr
    :
    @close_itree omd md R (trigger (Get p) >>= ktr) =
      x <- trigger (Get (p ∘ Lens.view fstl));; tau;; close_itree omd md (ktr x).
  Proof. rewrite ! bind_trigger. eapply close_itree_vis_get. Qed.

  Lemma close_itree_trigger_sE
        omd md
        R
        X (se: @sE omd.(Mod.state) X) ktr
    :
    @close_itree omd md R (trigger se >>= ktr) =
      x <- trigger (map_lens fstl se);; tau;; close_itree omd md (ktr x).
  Proof.
    destruct se. rewrite close_itree_trigger_state. ss.
  Qed.

  Lemma close_itree_vis_call
        omd md
        R
        fn args ktr
    :
    @close_itree omd md R (Vis ((|Call fn args)|)%sum ktr) =
      match (md.(Mod.funs) fn) with
      | Some body =>
          Vis (((|Yield)|)|)%sum (fun _ => rv <- map_event (OMod.emb_callee omd md) (body args);; tau;; close_itree omd md (ktr rv))
      | None => Vis (((Undefined|)|)|)%sum (Empty_set_rect _)
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
          _ <- trigger (Yield);; rv <- map_event (OMod.emb_callee omd md) (body args);; tau;; close_itree omd md (ktr rv)
      | None => trigger (Undefined) >>= (Empty_set_rect _)
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
      { rewrite ! close_itree_vis_state.
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
      trigger (map_prism inlp ee) >>= (fun r => tau;; Ret r).
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
          trigger (Yield) >>= (fun _ => map_event (OMod.emb_callee omd md) (body args) >>= (fun rv => tau;; Ret rv))
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
          trigger (Yield) >>= (fun _ => map_event (OMod.emb_callee omd md) (body (arg↑)) >>= (fun rv => tau;; unwrap (rv↓)))
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
          trigger (Yield) >>= (fun _ => map_event (OMod.emb_callee omd md) (body (arg↑)) >>= (fun rv => tau;; unwrap (rv↓)))
      | None => UB
      end.
  Proof.
    unfold callR. rewrite close_itree_bind. rewrite close_itree_trigger_call2. grind.
    { apply close_itree_unwrap. }
    { unfold UB. grind. }
  Qed.
End RED.
Global Opaque OMod.close_itree.

Section MAP_EVENT_RED.

  Variable ident ident' : Type.
  Variable state state' : Type.
  Variable p : Prism.t ident' ident.
  Variable l : Lens.t state' state.

  Lemma map_event_plmap_eventE_nocont
    X (e : @eventE ident X)
    : map_event (plmap p l) (trigger e) = trigger (map_prism p e).
  Proof.
    unfold trigger. rewrite map_event_vis.
    eapply observe_eta; ss. f_equal. extensionalities x.
    eapply map_event_ret.
  Qed.

  Lemma map_event_plmap_cE_nocont
    X (e : cE X)
    : map_event (plmap p l) (trigger e) = trigger e.
  Proof.
    unfold trigger. rewrite map_event_vis.
    eapply observe_eta; ss. f_equal. extensionalities x.
    eapply map_event_ret.
  Qed.

  Lemma map_event_plmap_state_nocont
    X (run : state -> state * X)
    : map_event (plmap p l) (trigger (State run)) = trigger (State (lens_state l run)).
  Proof.
    unfold trigger. rewrite map_event_vis.
    eapply observe_eta; ss. f_equal. extensionalities x.
    eapply map_event_ret.
  Qed.

  Lemma map_event_plmap_get_nocont
    X (pr : state -> X)
    : map_event (plmap p l) (trigger (Get pr)) = trigger (Get (pr ∘ Lens.view l)).
  Proof.
    unfold trigger. rewrite map_event_vis. rewrite <- map_lens_Get.
    eapply observe_eta; ss. f_equal. extensionalities x.
    eapply map_event_ret.
  Qed.

  Lemma map_event_plmap_modify_nocont
    (f : state -> state)
    : map_event (plmap p l) (trigger (Modify f)) = trigger (Modify (Lens.modify l f)).
  Proof.
    unfold trigger. rewrite map_event_vis. rewrite <- map_lens_Modify.
    eapply observe_eta; ss. f_equal. extensionalities x.
    eapply map_event_ret.
  Qed.

  Lemma map_event_plmap_callE_nocont
        X (e : callE X)
    : map_event (plmap p l) (trigger e) = trigger (e).
  Proof.
    unfold trigger. rewrite map_event_vis.
    eapply observe_eta; ss. f_equal. extensionalities x.
    eapply map_event_ret.
  Qed.

  Lemma map_event_plmap_UB
    R :  map_event (plmap p l) (UB : itree _ R) = UB.
  Proof.
    unfold UB. rewrite ! bind_trigger. rewrite map_event_vis.
    eapply observe_eta; ss. f_equal. extensionalities x. ss.
  Qed.

  Lemma map_event_plmap_unwrap
    R (x : option R)
    : map_event (plmap p l) (unwrap x) = unwrap x.
  Proof.
    unfold unwrap. destruct x.
    - eapply map_event_ret.
    - eapply map_event_plmap_UB.
  Qed.

  Lemma map_event_plmap_ext
    R (itr0 itr1 : itree _ R)
    : itr0 = itr1 -> map_event (plmap p l) itr0 = map_event (plmap p l) itr1.
  Proof. i. subst. ss. Qed.

End MAP_EVENT_RED.

From Fairness Require Export Red IRed.

Global Program Instance close_itree_rdb: red_database (mk_box (@OMod.close_itree)) :=
  mk_rdb
    0
    (mk_box close_itree_bind)
    (mk_box close_itree_tau)
    (mk_box close_itree_ret)
    (mk_box close_itree_trigger_eventE2)
    (mk_box close_itree_trigger_cE2)
    (mk_box close_itree_trigger_state)
    (mk_box close_itree_trigger_get)
    (mk_box close_itree_trigger_call2)
    (mk_box close_itree_call)
    (mk_box close_itree_callR)
    (mk_box close_itree_UB)
    (mk_box close_itree_UB)
    (mk_box close_itree_unwrap)
    (mk_box close_itree_UB)
    (mk_box close_itree_UB)
    (mk_box close_itree_UB)
    (mk_box close_itree_ext)
.

Global Program Instance map_event_plmap_rdb: red_database (mk_box (@map_event)) :=
  mk_rdb
    0
    (mk_box map_event_bind)
    (mk_box map_event_tau)
    (mk_box map_event_ret)
    (mk_box map_event_plmap_eventE_nocont)
    (mk_box map_event_plmap_cE_nocont)
    (mk_box map_event_plmap_state_nocont)
    (mk_box map_event_plmap_get_nocont)
    (mk_box map_event_plmap_modify_nocont)
    (mk_box map_event_plmap_callE_nocont)
    (mk_box map_event_plmap_UB)
    (mk_box map_event_plmap_UB)
    (mk_box map_event_plmap_UB)
    (mk_box map_event_plmap_unwrap)
    (mk_box map_event_plmap_UB)
    (mk_box map_event_plmap_UB)
    (mk_box map_event_plmap_UB)
    (mk_box map_event_plmap_ext)
.
