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
        funs: fname -> option (ktree ((((@eventE ident) +' cE) +' (sE state)) +' callE) (list Val) Val);
      }.

  Section LINK.
    Variable omd: t.
    Variable md: Mod.t.

    Definition link_state: Type := omd.(state) * md.(Mod.state).

    Definition link_st_init: link_state := (omd.(st_init), md.(Mod.st_init)).

    Definition link_itree:
      forall (s: link_state) R,
        itree (BehE +' callE omd.(state) +' cE omd.(state)) R -> itree (BehE +' callE link_state +' cE link_state) (link_state * R).
    Proof.
    Admitted.
  End LINK.
End OMod.


Section CALL.

  Variant callE


End CALL.


