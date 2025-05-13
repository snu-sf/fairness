From sflib Require Import sflib.
From iris.algebra Require Import cmra.
Require Import Coq.Logic.PropExtensionality.

Require Import Program.

Set Implicit Arguments.

Module Collection.
  Section Collection.
    Context {A: Type}.

    Definition t : Type := A -> Prop.

    Definition unit: t := fun _ => True.

    Definition add: t -> t -> t :=
      fun s0 s1 => (fun a => s0 a /\ s1 a).

    Definition wf: t -> Prop :=
      fun _ => True.

    Definition core: t -> option t := Some.

    Canonical Structure O := leibnizO t.

    Local Instance valid_instance : Valid t := wf.
    Local Instance pcore_instance : PCore t := core.
    Local Instance op_instance : Op t := add.
    Local Instance unit_instance : Unit t := unit.

    Lemma valid_unfold : valid = wf.
    Proof. done. Qed.
    Lemma op_unfold : (⋅) = add.
    Proof. done. Qed.
    Lemma pcore_unfold : pcore = core.
    Proof. done. Qed.
    Lemma unit_unfold : ε = unit.
    Proof. done. Qed.

    Definition mixin : RAMixin t.
    Proof.
      apply ra_total_mixin; try done.
      all: fold_leibniz.
      all: try apply _; try done.
      - intros ???. fold_leibniz.
        rewrite !op_unfold /add. f_equal.
        extensionality a0.
        eapply propositional_extensionality. split; i; des; ss; des; ss.
      - intros ??. fold_leibniz.
        rewrite !op_unfold /add. f_equal.
        extensionality a0.
        eapply propositional_extensionality. split; i; des; ss; des; ss.
      - intros ?. fold_leibniz.
        rewrite /cmra.core !pcore_unfold /core op_unfold /add /=.
        extensionality a0.
        eapply propositional_extensionality. split; i; des; ss; des; ss.
    Qed.

    Canonical Structure R := discreteR t mixin.

    Global Instance discrete : CmraDiscrete R.
    Proof. apply discrete_cmra_discrete. Qed.

    Lemma ucmra_mixin : UcmraMixin t.
    Proof.
      split; try apply _; try done.
      intros m.
      fold_leibniz.
      rewrite op_unfold /add unit_unfold /unit.
      extensionality a0.
      eapply propositional_extensionality. split; i; des; ss; des; ss.
    Qed.
    Canonical Structure UR := Ucmra t ucmra_mixin.

    Definition into_t (a : A -> Prop) : t := a.
  End Collection.
End Collection.
Global Arguments Collection.t _ : clear implicits.
