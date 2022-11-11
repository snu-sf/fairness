From sflib Require Import sflib.
From ITree Require Export ITree.
From Paco Require Import paco.

Require Export Coq.Strings.String.
From Coq Require Import Program.

From Fairness Require Export ITreeLib FairBeh NatStructs.
From Fairness Require Export Mod.

Set Implicit Arguments.

Variant callE: Type -> Type :=
  | Call (fn: fname) (arg: Any.t): callE Any.t
.

Module OMod.
  Record t: Type :=
    mk {
        state: Type;
        ident: ID;
        st_init: state;
        funs: fname ->
              option (ktree ((((@eventE ident) +' cE) +' (sE state)) +' callE) Any.t Any.t);
      }.

  Section CLOSED.
    Variable omd: t.
    Variable md: Mod.t.

    Definition closed_state: Type := omd.(state) * md.(Mod.state).
    Definition closed_ident: ID := id_sum omd.(ident) md.(Mod.ident).
    Definition closed_st_init: closed_state := (omd.(st_init), md.(Mod.st_init)).

    Definition embed_itree {R}:
      (itree (((@eventE md.(Mod.ident)) +' cE) +' sE (Mod.state md)) R) ->
      (itree (((@eventE closed_ident) +' cE) +' sE closed_state) R).
    Proof.
      eapply ITree.iter. intros body. destruct (observe body).
      - exact (Ret (inr r)).
      - exact (Ret (inl t0)).
      - destruct e as [[eE|cE]|stE].
        + exact (Vis ((embed_event_r eE|)|)%sum (fun x => Ret (inl (k x)))).
        + exact (Vis ((|cE)|)%sum (fun x => Ret (inl (k x)))).
        + eapply embed_state. instantiate (1:=md.(Mod.state)). exact snd. exact update_snd.
          exact (Vis (|stE)%sum (fun x => Ret (inl (k x)))).
    Defined.

    Definition close_itree {R}:
      (itree ((((@eventE omd.(ident)) +' cE) +' (sE omd.(state))) +' callE) R) ->
      (itree ((((@eventE closed_ident) +' cE) +' (sE closed_state))) R).
    Proof.
      (*ub for undefined fn call*)
      eapply ITree.iter. intros itr. destruct (observe itr).
      - exact (Ret (inr r)).
      - exact (Ret (inl t0)).
      - destruct e as [[[eE|cE]|stE]|caE].
        + exact (Vis ((embed_event_l eE|)|)%sum (fun x => Ret (inl (k x)))).
        + exact (Vis ((|cE)|)%sum (fun x => Ret (inl (k x)))).
        + eapply embed_state. instantiate (1:=omd.(state)). exact fst. exact update_fst.
          exact (Vis (|stE)%sum (fun x => Ret (inl (k x)))).
        + destruct caE.
          destruct (md.(Mod.funs) fn) eqn:FUN.
          { clear FUN. specialize (k0 arg). eapply ITree.bind.
            exact (Vis ((|Yield)|)%sum (fun _ => embed_itree k0)).
            intros rv. exact (Ret (inl (k rv))). }
          { exact (Vis ((embed_event_l Undefined|)|)%sum (Empty_set_rect _)). }
    Defined.

    Definition closed_funs: fname -> option (ktree _ Any.t Any.t) :=
      fun fn =>
        match (omd.(funs) fn) with
        | None => None
        | Some body => Some (fun args => close_itree (body args))
        end.

  End CLOSED.

  Definition close (om: t) (m: Mod.t): Mod.t :=
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
  Proof. unfold embed_itree. rewrite unfold_iter. grind. Qed.

  Lemma embed_itree_tau
        omd md
        R
        itr
    :
    @embed_itree omd md R (tau;; itr) = tau;; @embed_itree omd md R itr.
  Proof. unfold embed_itree. rewrite unfold_iter. grind. Qed.

  Lemma embed_itree_vis_eventE
        omd md
        R
        X (ee: @eventE _ X) ktr
    :
    @embed_itree omd md R (Vis ((ee|)|)%sum ktr) =
      Vis ((embed_event_r ee|)|)%sum (fun x => tau;; embed_itree omd md (ktr x)).
  Proof.
    unfold embed_itree at 1. rewrite unfold_iter. grind.
    apply observe_eta. ss. f_equal. extensionality x. grind.
  Qed.

  Lemma embed_itree_trigger_eventE
        omd md
        R
        X (ee: @eventE _ X) ktr
    :
    @embed_itree omd md R (trigger ee >>= ktr) =
      x <- trigger (embed_event_r ee);; tau;; (embed_itree omd md (ktr x)).
  Proof. rewrite ! bind_trigger. apply embed_itree_vis_eventE. Qed.

  Lemma embed_itree_vis_cE
        omd md
        R
        X (ce: @cE X) ktr
    :
    @embed_itree omd md R (Vis ((|ce)|)%sum ktr) =
      Vis ((|ce)|)%sum (fun x => tau;; embed_itree omd md (ktr x)).
  Proof.
    unfold embed_itree at 1. rewrite unfold_iter. grind.
    apply observe_eta. ss. f_equal. extensionality x. grind.
  Qed.

  Lemma embed_itree_trigger_cE
        omd md
        R
        X (ce: @cE X) ktr
    :
    @embed_itree omd md R (trigger ce >>= ktr) =
      x <- trigger ce;; tau;; (embed_itree omd md (ktr x)).
  Proof. rewrite ! bind_trigger. apply embed_itree_vis_cE. Qed.

  Lemma embed_itree_vis_sE
        omd md
        R
        X (se: @sE md.(Mod.state) X) ktr
    :
    @embed_itree omd md R (Vis (|se)%sum ktr) =
      lr <- embed_state snd update_snd (Vis (|se)%sum (fun x => Ret (inl (ktr x))));;
      match lr with
      | inl l => tau;; embed_itree omd md l
      | inr r0 => Ret r0
      end.
  Proof.
    unfold embed_itree at 1. rewrite unfold_iter. grind.
  Qed.

  Lemma embed_itree_vis_put
        omd md
        R
        st ktr
    :
    @embed_itree omd md R (Vis (|Put st)%sum ktr) =
      Vis (inr1 (Get _)) (fun s => Vis (inr1 (Put (update_snd s st))) (fun _ => tau;; embed_itree omd md (ktr tt))).
  Proof.
    rewrite embed_itree_vis_sE. rewrite embed_state_put. grind.
    apply observe_eta. ss. f_equal. extensionality x. grind.
    apply observe_eta. ss. f_equal. extensionality u.
    rewrite embed_state_ret. grind.
  Qed.

  Lemma embed_itree_trigger_put
        omd md
        R
        st ktr
    :
    @embed_itree omd md R (trigger (Put st) >>= ktr) =
      s <- trigger (Get _);; u <- trigger (Put (update_snd s st));; tau;; embed_itree omd md (ktr tt).
  Proof.
    rewrite ! bind_trigger. setoid_rewrite embed_itree_vis_put.
    apply observe_eta. ss. f_equal. extensionality x.
    rewrite ! bind_trigger. ss.
  Qed.

  Lemma embed_itree_vis_get
        omd md
        R
        ktr
    :
    @embed_itree omd md R (Vis (|Get _)%sum ktr) =
      Vis (inr1 (Get _)) (fun s => tau;; embed_itree omd md (ktr (snd s))).
  Proof.
    rewrite embed_itree_vis_sE. rewrite embed_state_get. grind.
    apply observe_eta. ss. f_equal. extensionality x.
    rewrite embed_state_ret. grind.
  Qed.

  Lemma embed_itree_trigger_get
        omd md
        R
        ktr
    :
    @embed_itree omd md R (trigger (Get _) >>= ktr) =
      s <- trigger (Get _);; tau;; embed_itree omd md (ktr (snd s)).
  Proof.
    rewrite ! bind_trigger. setoid_rewrite embed_itree_vis_get. ss.
  Qed.

  Lemma embed_itree_bind
        omd md
        A B (itr: itree _ A) (ktr: ktree _ A B)
    :
    @embed_itree omd md B (itr >>= ktr) =
      (@embed_itree omd md A itr) >>= (fun a => @embed_itree omd md B (ktr a)).
  Proof.
    eapply bisim_is_eq. revert itr ktr. ginit. gcofix CIH; i.
    ides itr; grind.
    { rewrite embed_itree_ret. ired.
      gfinal. right. eapply paco2_mon.
      2:{ instantiate (1:=bot2). ss. }
      eapply eq_is_bisim. auto.
    }
    { rewrite ! embed_itree_tau. rewrite bind_tau.
      gstep. eapply EqTau. gbase. eauto.
    }
    { revert k. destruct e as [[|]|[]]; i.
      { rewrite ! embed_itree_vis_eventE.
        ired. gstep. eapply EqVis. i. ss.
        ired. gstep. eapply EqTau.
        gbase. eauto.
      }
      { rewrite ! embed_itree_vis_cE.
        ired. gstep. eapply EqVis. i. ss.
        ired. gstep. eapply EqTau.
        gbase. eauto.
      }
      { rewrite ! embed_itree_vis_put.
        ired. gstep. eapply EqVis. i. ss.
        ired. gstep. eapply EqVis. i. ss.
        ired. gstep. eapply EqTau.
        gbase. eauto.
      }
      { rewrite ! embed_itree_vis_get.
        ired. gstep. eapply EqVis. i. ss.
        ired. gstep. eapply EqTau.
        gbase. eauto.
      }
    }
  Qed.

  Lemma embed_itree_trigger_eventE2
        omd md
        X ee
    :
    @embed_itree omd md X (trigger ee) =
      trigger (embed_event_r ee) >>= (fun r => tau;; Ret r).
  Proof.
    rewrite (bind_ret_r_rev (trigger ee)).
    setoid_rewrite embed_itree_trigger_eventE. grind. apply embed_itree_ret.
  Qed.

  Lemma embed_itree_trigger_cE2
        omd md
        X (ce: @cE X)
    :
    @embed_itree omd md X (trigger ce) =
      trigger (ce) >>= (fun r => tau;; Ret r).
  Proof.
    rewrite (bind_ret_r_rev (trigger ce)).
    setoid_rewrite embed_itree_trigger_cE. grind. apply embed_itree_ret.
  Qed.

  Lemma embed_itree_trigger_put2
        omd md
        st
    :
    @embed_itree omd md _ (trigger (Put st)) =
      trigger (Get _) >>= (fun s => trigger (Put (update_snd s st)) >>= (fun r => tau;; Ret r)).
  Proof.
    rewrite (bind_ret_r_rev (trigger (Put st))).
    setoid_rewrite embed_itree_trigger_put. grind. destruct x0. apply embed_itree_ret.
  Qed.

  Lemma embed_itree_trigger_get2
        omd md
    :
    @embed_itree omd md _ (trigger (Get _)) =
      trigger (Get _) >>= (fun s => tau;; Ret (snd s)).
  Proof.
    rewrite (bind_ret_r_rev (trigger (Get _))).
    setoid_rewrite embed_itree_trigger_get. grind. apply embed_itree_ret.
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
      Vis ((embed_event_l ee|)|)%sum (fun x => tau;; close_itree omd md (ktr x)).
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
      Vis ((|ce)|)%sum (fun x => tau;; close_itree omd md (ktr x)).
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
        X (se: @sE omd.(OMod.state) X) ktr
    :
    @close_itree omd md R (Vis ((|se)|)%sum ktr) =
      lr <- embed_state fst update_fst (Vis (|se)%sum (fun x => Ret (inl (ktr x))));;
      match lr with
      | inl l => tau;; close_itree omd md l
      | inr r0 => Ret r0
      end.
  Proof.
    unfold close_itree at 1. rewrite unfold_iter. grind.
  Qed.

  Lemma close_itree_vis_put
        omd md
        R
        st ktr
    :
    @close_itree omd md R (Vis ((|Put st)|)%sum ktr) =
      Vis (inr1 (Get _)) (fun s => Vis (inr1 (Put (update_fst s st))) (fun _ => tau;; close_itree omd md (ktr tt))).
  Proof.
    rewrite close_itree_vis_sE. rewrite embed_state_put. grind.
    apply observe_eta. ss. f_equal. extensionality x. grind.
    apply observe_eta. ss. f_equal. extensionality u.
    rewrite embed_state_ret. grind.
  Qed.

  Lemma close_itree_trigger_put
        omd md
        R
        st ktr
    :
    @close_itree omd md R (trigger (Put st) >>= ktr) =
      s <- trigger (Get _);; u <- trigger (inr1 (Put (update_fst s st)));; tau;; close_itree omd md (ktr tt).
  Proof.
    rewrite ! bind_trigger. setoid_rewrite close_itree_vis_put.
    apply observe_eta. ss. f_equal. extensionality x.
    rewrite ! bind_trigger. ss.
  Qed.

  Lemma close_itree_vis_get
        omd md
        R
        ktr
    :
    @close_itree omd md R (Vis ((|Get _)|)%sum ktr) =
      Vis (inr1 (Get _)) (fun s => tau;; close_itree omd md (ktr (fst s))).
  Proof.
    rewrite close_itree_vis_sE. rewrite embed_state_get. grind.
    apply observe_eta. ss. f_equal. extensionality x.
    rewrite embed_state_ret. grind.
  Qed.

  Lemma close_itree_trigger_get
        omd md
        R
        ktr
    :
    @close_itree omd md R (trigger (Get _) >>= ktr) =
      s <- trigger (Get _);; tau;; close_itree omd md (ktr (fst s)).
  Proof.
    rewrite ! bind_trigger. setoid_rewrite close_itree_vis_get. ss.
  Qed.

  Lemma close_itree_vis_call
        omd md
        R
        fn args ktr
    :
    @close_itree omd md R (Vis (|Call fn args)%sum ktr) =
      match (md.(Mod.funs) fn) with
      | Some body =>
          Vis ((|Yield)|)%sum (fun _ => rv <- embed_itree omd md (body args);; tau;; close_itree omd md (ktr rv))
      | None => Vis ((embed_event_l Undefined|)|)%sum (Empty_set_rect _)
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
          trigger (Yield);; rv <- embed_itree omd md (body args);; tau;; close_itree omd md (ktr rv)
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
      { rewrite ! close_itree_vis_put.
        ired. gstep. eapply EqVis. i. ss.
        ired. gstep. eapply EqVis. i. ss.
        ired. gstep. eapply EqTau.
        gbase. eauto.
      }
      { rewrite ! close_itree_vis_get.
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

  Lemma close_itree_trigger_put2
        omd md
        st
    :
    @close_itree omd md _ (trigger (Put st)) =
      trigger (Get _) >>= (fun s => trigger (Put (update_fst s st)) >>= (fun r => tau;; Ret r)).
  Proof.
    rewrite (bind_ret_r_rev (trigger (Put st))).
    setoid_rewrite close_itree_trigger_put. grind. destruct x0. apply close_itree_ret.
  Qed.

  Lemma close_itree_trigger_get2
        omd md
    :
    @close_itree omd md _ (trigger (Get _)) =
      trigger (Get _) >>= (fun s => tau;; Ret (fst s)).
  Proof.
    rewrite (bind_ret_r_rev (trigger (Get _))).
    setoid_rewrite close_itree_trigger_get. grind. apply close_itree_ret.
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
    { unfold UB. rewrite bind_trigger. grind. }
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
    (mk_box embed_itree_trigger_put2)
    (mk_box embed_itree_trigger_get2)
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
    (mk_box close_itree_trigger_put2)
    (mk_box close_itree_trigger_get2)
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
