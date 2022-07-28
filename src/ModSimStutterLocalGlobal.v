From sflib Require Import sflib.
From Paco Require Import paco.
Require Export Coq.Strings.String.

From Fairness Require Export ITreeLib FairBeh Mod.
From Fairness Require Import pind8.

Set Implicit Arguments.

From Fairness Require Import ModSimGStutter ModSimStutter.

Section PRIMIVIESIM.
  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable _ident_src: ID.
  Definition ident_src := sum_tid _ident_src.
  Variable _ident_tgt: ID.
  Definition ident_tgt := sum_tid _ident_tgt.

  Variable wf_src: WF.
  Variable wf_tgt: WF.

  Let srcE := ((@eventE _ident_src +' cE) +' sE state_src).
  Let tgtE := ((@eventE _ident_tgt +' cE) +' sE state_tgt).

  Variable world: Type.
  Variable world_le: world -> world -> Prop.

  Definition shared :=
    (TIdSet.t *
       (@imap ident_src wf_src) *
       (@imap ident_tgt wf_tgt) *
       state_src *
       state_tgt *
       world)%type.

  Let shared_rel: Type := shared -> Prop.
End PRIMIVIESIM.
