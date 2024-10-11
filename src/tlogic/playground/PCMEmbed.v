From sflib Require Import sflib.
Require Export ZArith.
(* Require Export Znumtheory. *)
Require Import List.
Require Import String.
Require Import ClassicalChoice ChoiceFacts.
Require Import Coq.Classes.RelationClasses.
Require Import Lia.
Require Import Program.
From stdpp Require coPset gmap.
From Fairness Require Import Axioms.

Set Implicit Arguments.

From iris.bi Require Import derived_connectives updates.
From iris.prelude Require Import options.

(* TODO: make lemmas for RA and turn it into URA at the last *)

From Fairness Require PCM.
From Fairness Require Import PCMForSyntax.

Section TO_LARGE.

  Global Program Definition  (M: ucmra): PCM.ucmra :=
    @PCM.URA.mk M.(URA.car) M.(URA.unit) M.(URA._add) M.(URA._wf) M.(URA._add_comm) M.(URA._add_assoc) _ _ _ M.(URA.core) _ _ _.
  Next Obligation.
    i. PCM.unseal "ra".
    hexploit URA.unit_id. i. ur in H. eauto.
  Qed.
  Next Obligation.
    i. PCM.unseal "ra".
    hexploit URA.wf_unit. i. ur in H. eauto.
  Qed.
  Next Obligation.
    i. PCM.unseal "ra".
    hexploit URA.wf_mon.
    { ur. eauto. }
    i. ur in H0. eauto.
  Qed.
  Next Obligation.
    i. PCM.unseal "ra".
    hexploit URA.core_id. i. ur in H. eauto.
  Qed.
  Next Obligation.
    i. PCM.unseal "ra".
    hexploit URA.core_idem. i. ur in H. eauto.
  Qed.
  Next Obligation.
    i. PCM.unseal "ra".
    hexploit URA.core_mono. i. ur in H. eauto.
  Qed.

  Global Coercion : ucmra >-> PCM.ucmra.

  Definition to_LGRA (Σ: GRA.t): PCM.GRA.t :=
    fun n =>  (Σ n).

  Global Coercion to_LGRA: GRA.t >-> PCM.GRA.t.

  Global Program Definition to_LGRA_inG
          {RA: ucmra} {Σ: GRA.t} (IN: @GRA.inG RA Σ): @PCM.GRA.inG ( RA) (to_LGRA Σ) :=
    @PCM.GRA.InG RA Σ IN.(GRA.inG_id) _.
  Next Obligation.
    i. destruct IN. subst RA. ss.
  Qed.

End TO_LARGE.
