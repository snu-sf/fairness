From sflib Require Import sflib.
From ITree Require Export ITree.
From Paco Require Import paco.

Require Export Coq.Strings.String.
From Coq Require Import Program.

From Fairness Require Export ITreeLib FairBeh NatStructs.
From Fairness Require Export Mod.

Set Implicit Arguments.

Variant callE: Type -> Type :=
  | Call (fn: fname) (arg: list Val): callE Val
.

Module OMod.
  Record t: Type :=
    mk {
        state: Type;
        ident: ID;
        st_init: state;
        funs: fname ->
              option (ktree ((((@eventE ident) +' cE) +' (sE state)) +' callE) (list Val) Val);
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

    Definition closed_funs: fname -> option (ktree _ (list Val) Val) :=
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

  Lemma embed_itree_ret
        omd md
        R
        (r: R)
    :
    @embed_itree omd md R (Ret r) = Ret r.
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
    @embed_itree omd md R (trigger ((ee|)|)%sum >>= ktr) =
      x <- trigger ((embed_event_r ee|)|)%sum;; tau;; (embed_itree omd md (ktr x)).
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
    @embed_itree omd md R (trigger ((|ce)|)%sum >>= ktr) =
      x <- trigger ((|ce)|)%sum;; tau;; (embed_itree omd md (ktr x)).
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
    @embed_itree omd md R (trigger (|Put st)%sum >>= ktr) =
      s <- trigger (inr1 (Get _));; u <- trigger (inr1 (Put (update_snd s st)));; tau;; embed_itree omd md (ktr tt).
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
    @embed_itree omd md R (trigger (|Get _)%sum >>= ktr) =
      s <- trigger (inr1 (Get _));; tau;; embed_itree omd md (ktr (snd s)).
  Proof.
    rewrite ! bind_trigger. setoid_rewrite embed_itree_vis_get. ss.
  Qed.

  Local Opaque embed_itree.

  Lemma close_itree_ret
        omd md
        R r
    :
    @close_itree omd md R (Ret r) = Ret r.
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
    @close_itree omd md R (trigger (((ee|)|)|)%sum >>= ktr) =
      x <- trigger ((embed_event_l ee|)|)%sum;; tau;; (close_itree omd md (ktr x)).
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
    @close_itree omd md R (trigger (((|ce)|)|)%sum >>= ktr) =
      x <- trigger ((|ce)|)%sum;; tau;; (close_itree omd md (ktr x)).
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
    @close_itree omd md R (trigger ((|Put st)|)%sum >>= ktr) =
      s <- trigger (inr1 (Get _));; u <- trigger (inr1 (Put (update_fst s st)));; tau;; close_itree omd md (ktr tt).
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
    @close_itree omd md R (trigger ((|Get _)|)%sum >>= ktr) =
      s <- trigger (inr1 (Get _));; tau;; close_itree omd md (ktr (fst s)).
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
          trigger ((|Yield)|)%sum;;; rv <- embed_itree omd md (body args);; tau;; close_itree omd md (ktr rv)
      | None => Vis ((embed_event_l Undefined|)|)%sum (Empty_set_rect _)
      end.
  Proof.
    rewrite bind_trigger. setoid_rewrite close_itree_vis_call. des_ifs.
    rewrite bind_trigger. auto.
  Qed.

End RED.
Global Opaque OMod.embed_itree.
Global Opaque OMod.close_itree.
