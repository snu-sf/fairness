From sflib Require Import sflib.
From Paco Require Import paco.
Require Export Coq.Strings.String.
Require Import Coq.Classes.RelationClasses.

From Fairness Require Export ITreeLib FairBeh Mod.
From Fairness Require Import pind PCM WFLib.
From Fairness Require Import ModSim ModSimYOrd GenYOrd.

Set Implicit Arguments.

Section PROOF.
  Context `{M: URA.t}.

  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable ident_src: ID.
  Variable _ident_tgt: ID.
  Let ident_tgt := @ident_tgt _ident_tgt.

  Variable wf_src: WF.
  Variable wf_tgt: WF.

  Let srcE := ((@eventE ident_src +' cE) +' sE state_src).
  Let tgtE := ((@eventE _ident_tgt +' cE) +' sE state_tgt).

  Let shared := shared state_src state_tgt ident_src _ident_tgt wf_src wf_tgt.
  Let shared_rel: Type := shared -> Prop.
  Variable I: shared_rel.

  Definition lift_wf (wf: WF): WF := sum_WF wf (option_WF wf).

  Definition mk_o (wf: WF) R (o: wf.(T)) (ps: bool) (itr_src: itree srcE R): (lift_wf wf).(T) :=
    if ps
    then match (observe itr_src) with
         | VisF ((|Yield)|)%sum _ => (inr (Some o))
         | _ => (inr None)
         end
    else match (observe itr_src) with
         | VisF ((|Yield)|)%sum _ => (inl o)
         | _ => (inr None)
         end.

  Let A R0 R1 := (bool * bool * URA.car * (itree srcE R0) * (itree tgtE R1) * shared)%type.
  Let wf_ot R0 R1 := @ord_tree_WF (A R0 R1).
  Let wf_stt R0 R1 := lift_wf (@wf_ot R0 R1).



End PROOF.
