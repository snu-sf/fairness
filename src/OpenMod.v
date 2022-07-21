From sflib Require Import sflib.
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

    Definition closed_itree {A R}:
      (ktree ((((@eventE omd.(ident)) +' cE) +' (sE omd.(state))) +' callE) (list A) R) ->
      (ktree ((((@eventE closed_ident) +' cE) +' (sE closed_state)) +' callE) (list A) R).
    Proof.
      
      

    Definition closed_itree:
      forall (s: closed_state) R,
        itree (BehE +' callE omd.(state) +' cE omd.(state)) R -> itree (BehE +' callE closed_state +' cE closed_state) (closed_state * R).
    Proof.
    Admitted.
  End CLOSED.
End OMod.
