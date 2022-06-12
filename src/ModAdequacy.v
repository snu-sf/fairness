From sflib Require Import sflib.
From ITree Require Export ITree.
From Paco Require Import paco.

Require Export Coq.Strings.String.
Require Import Program.

From ExtLib Require Import FMapAList.

Export ITreeNotations.

From Fairness Require Import pind8.
From Fairness Require Export ITreeLib FairBeh FairSim.
From Fairness Require Export Mod ModSimPico Concurrency.

Set Implicit Arguments.



Section ADEQ.

  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable _ident_src: ID.
  Definition ident_src := id_sum tids _ident_src.
  Variable _ident_tgt: ID.
  Definition ident_tgt := id_sum tids _ident_tgt.

  Variable wf_src: WF.
  Variable wf_tgt: WF.

  Let srcE := ((@eventE ident_src +' cE) +' sE state_src).
  Let tgtE := ((@eventE ident_tgt +' cE) +' sE state_tgt).

  Variable world: Type.
  Variable world_le: world -> world -> Prop.

  Variable I: (@shared state_src state_tgt ident_src ident_tgt wf_src wf_tgt world) -> Prop.

  Theorem local_adequacy
          R
          (ths_src: @threads _ident_src (sE state_src) R)
          (ths_tgt: @threads _ident_tgt (sE state_tgt) R)
          (LSIM: forall tid0 (src0: itree srcE R) (tgt0: itree tgtE R)
                   (LSRC: Some src0 = threads_find tid0 ths_src)
                   (LTGT: Some tgt0 = threads_find tid0 ths_tgt),
              local_sim world_le I src0 tgt0)
          tid src tgt (st_src: state_src) (st_tgt: state_tgt)
          (SRC: Some src = threads_find tid ths_src)
          (TGT: Some tgt = threads_find tid ths_tgt)
    :
    gsim wf_src wf_tgt (@eq R) false false
         (interp_all st_src ths_src tid src)
         (interp_all st_tgt ths_tgt tid tgt).
  Proof.

  Abort.

End ADEQ.
