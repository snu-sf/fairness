From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Export ITreeLib WFLib FairBeh NatStructs Mod pind Wrapper.
From Fairness Require Export Red IRed Wrapper.
From Fairness Require Import IProp IPM Weakest.
From Fairness Require Import ModSim PCM MonotonePCM ThreadsRA StateRA FairRA.

Set Implicit Arguments.


Section WRAPPER.
  Context `{Σ: GRA.t}.

  Variable state_tgt: Type.
  Variable wmod: WMod.t.
  Let state_src := WMod.interp_state wmod.

  Definition WrapSt_src: wmod.(WMod.state) -> iProp. Admitted.
  Definition

  Definition WrapSt_src: wmod.(WMod.state) -> iProp. Admitted.

  Variable state_src: Type.
  Definition St_src: state_src -> iProp. Admitted.

  Variable ident_src: ID.
  Variable ident_tgt: ID.

  Let srcE := ((@eventE ident_src +' cE) +' sE state_src).
  Let tgtE := ((@eventE ident_tgt +' cE) +' sE state_tgt).

  Variable I: iProp.

  Let rel := (forall R_src R_tgt (Q: R_src -> R_tgt -> list nat -> iProp), itree srcE R_src -> itree tgtE R_tgt -> list nat -> iProp).

  Variable tid: thread_id.

  Definition fsim: rel -> rel -> rel. Admitted.

  Lemma fsim_base r g R_src R_tgt
        (Q: R_src -> R_tgt -> list nat -> iProp)
        os itr_src itr_tgt
    :
    (@r _ _ Q itr_src itr_tgt os)
      -∗
      (fsim r g Q itr_src itr_tgt os)
  .
  Admitted.

  Lemma fsim_mono_knowledge (r0 g0 r1 g1: rel) R_src R_tgt
        (Q: R_src -> R_tgt -> list nat -> iProp)
        os itr_src itr_tgt
        (MON0: forall R_src R_tgt (Q: R_src -> R_tgt -> list nat -> iProp)
                      os itr_src itr_tgt,
            (@r0 _ _ Q itr_src itr_tgt os)
              -∗
              (#=> (@r1 _ _ Q itr_src itr_tgt os)))
        (MON1: forall R_src R_tgt (Q: R_src -> R_tgt -> list nat -> iProp)
                      os itr_src itr_tgt,
            (@g0 _ _ Q itr_src itr_tgt os)
              -∗
              (#=> (@g1 _ _ Q itr_src itr_tgt os)))
    :
    bi_entails
      (fsim r0 g0 Q os itr_src itr_tgt)
      (fsim r1 g1 Q os itr_src itr_tgt)
  .
  Proof.
  Admitted.

  Lemma fsim_coind A
        (R_src: forall (a: A), Prop)
        (R_tgt: forall (a: A), Prop)
        (Q: forall (a: A), R_src a -> R_tgt a -> list nat -> iProp)
        (o : forall (a: A), list nat)
        (itr_src : forall (a: A), itree srcE (R_src a))
        (itr_tgt : forall (a: A), itree tgtE (R_tgt a))
        (P: forall (a: A), iProp)
        (r g0: rel)
        (COIND: forall (g1: rel) a,
            (□((∀ R_src R_tgt (Q: R_src -> R_tgt -> list nat -> iProp)
                  os itr_src itr_tgt,
                   @g0 R_src R_tgt Q itr_src itr_tgt os -* @g1 R_src R_tgt Q itr_src itr_tgt os)
                 **
                 (∀ a, P a -* @g1 (R_src a) (R_tgt a) (Q a) (itr_src a) (itr_tgt a) (o a))))
              -∗
              (P a)
              -∗
              (fsim r g1 (Q a) (itr_src a) (itr_tgt a) (o a)))
    :
    (forall a, bi_entails (P a) (fsim r g0 (Q a) (itr_src a) (itr_tgt a) (o a))).
  Proof.
  Admitted.
