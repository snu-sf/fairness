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

    Definition closed_ktree {A R}:
      (ktree ((((@eventE omd.(ident)) +' cE) +' (sE omd.(state))) +' callE) (list A) R) ->
      (ktree ((((@eventE closed_ident) +' cE) +' (sE closed_state))) (list A) R).
    Proof.
      (*ub for undefined fn call*)
      ii. specialize (X X0); clear X0 A. revert X.
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
          { clear FUN. specialize (k0 arg).
            revert k0. eapply ITree.iter. intros body. destruct (observe body).
            - exact (Ret (inr (inl (k r)))).
            - exact (Ret (inl t0)).
            - destruct e as [[eE|cE]|stE].
              + exact (Vis ((embed_event_r eE|)|)%sum (fun x => Ret (inl (k0 x)))).
              + exact (Vis ((|cE)|)%sum (fun x => Ret (inl (k0 x)))).
              + eapply embed_state. instantiate (1:=md.(Mod.state)). exact snd. exact update_snd.
                exact (Vis (|stE)%sum (fun x => Ret (inl (k0 x)))).
          }
          { exact (Vis ((embed_event_l Undefined|)|)%sum (Empty_set_rect _)). }
    Qed.

    Definition closed_funs: fname -> option (ktree _ (list Val) Val) :=
      fun fn =>
        match (omd.(funs) fn) with
        | None => None
        | Some body => Some (closed_ktree body)
        end.

  End CLOSED.

  Definition close (om: t) (m: Mod.t): Mod.t :=
    @Mod.mk
      (closed_state om m)
      (closed_ident om m)
      (closed_st_init om m)
      (closed_funs om m).

End OMod.
