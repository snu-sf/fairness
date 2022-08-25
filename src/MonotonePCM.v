From sflib Require Import sflib.
From Fairness Require Import PCM IProp IPM.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.PropExtensionality.
From Fairness Require Import Axioms.
Require Import Program.

Set Implicit Arguments.


Module Collection.
  Section Collection.
    Variable A: Type.

    Definition car: Type := A -> Prop.

    Definition unit: car := fun _ => True.

    Definition add: car -> car -> car :=
      fun s0 s1 a => s0 a /\ s1 a.

    Definition wf: car -> Prop :=
      fun _ => True.

    Definition core: car -> car :=
      fun s => s.

    Program Instance t: URA.t := {
        car := car;
        unit := unit;
        _add := add;
        _wf := wf;
        core := core;
      }
    .
    Next Obligation.
    Proof.
      unfold add. extensionality a0.
      eapply propositional_extensionality. split; i; des; ss.
    Qed.
    Next Obligation.
    Proof.
      unfold add. extensionality a0.
      eapply propositional_extensionality. split; i; des; ss.
    Qed.
    Next Obligation.
    Proof.
      unseal "ra". unfold add. extensionality a0.
      eapply propositional_extensionality. split; i; des; ss.
    Qed.
    Next Obligation.
    Proof.
      unseal "ra". ss.
    Qed.
    Next Obligation.
    Proof.
      unseal "ra". ss.
    Qed.
    Next Obligation.
    Proof.
      unseal "ra". unfold add, core. extensionality a0.
      eapply propositional_extensionality. split; i; des; ss.
    Qed.
    Next Obligation.
    Proof.
      unseal "ra".
      unfold add, core. esplits; eauto.
    Qed.
  End Collection.
End Collection.

Section Monotone.
  Variable W: Type.
  Variable le: W -> W -> Prop.
  Hypothesis le_PreOrder: PreOrder le.

  Let leR (w: W): Collection.t W := le w.

  Lemma white_idempotent w0 w1
        (LE: le w0 w1)
    :
    Auth.white (leR w0) ⋅ Auth.white (leR w1) = Auth.white (leR w1).
  Proof.
    unfold Auth.white.
    unfold URA.add. unseal "ra". ss.
    unfold URA.add. unseal "ra". ss.
    unfold Collection.add. f_equal. extensionality a.
    eapply propositional_extensionality. split; i; des; ss.
    split; auto. rr. etrans; eauto.
  Qed.

  Lemma embed_core_commute `{@GRA.inG M Σ}
        (r: M)
    :
    GRA.embed (URA.core r) = URA.core (GRA.embed r).
  Proof.
    Local Transparent GRA.to_URA URA.unit.
    dependent destruction H. subst.
    extensionality n. ss. unfold URA.core at 2. ss.
    unfold GRA.embed. destruct (PeanoNat.Nat.eq_dec GRA.inG_id n) eqn:EQ; ss.
    { subst. ss. }
    { des_ifs. ss. transitivity (add (core unit) unit); auto. }
  Qed.

  Lemma own_persistent `{@GRA.inG M Σ}
        (r: M)
    :
    (OwnM r) -∗ (□ OwnM (URA.core r)).
  Proof.
    rr. autorewrite with iprop. i.
    rr. autorewrite with iprop. split.
    { rr. autorewrite with iprop. auto. }
    { rr. autorewrite with iprop.
      rr in H0. autorewrite with iprop in H0.
      rr. autorewrite with iprop.
      eapply URA.extends_core in H0.
      rewrite embed_core_commute. auto.
    }
  Qed.

  Definition monoRA: URA.t := Auth.t (Collection.t W).

  Context `{@GRA.inG monoRA Σ}.

  Definition monoBlack (w: W): iProp :=
    OwnM (Auth.black (leR w) ⋅ Auth.white (leR w)).

  Definition monoWhiteExact (w: W): iProp :=
    OwnM (Auth.white (leR w)).

  Definition monoWhite (w0: W): iProp :=
    ∃ w1, monoWhiteExact w1 ∧ ⌜le w0 w1⌝.

  Lemma black_persistent_white_exact w
    :
    (monoBlack w) -∗ (□ monoWhiteExact w).
  Proof.
    unfold monoBlack, monoWhiteExact.
    iIntros "[_ H]". iPoseProof (own_persistent with "H") as "H". ss.
  Qed.

  Lemma black_persistent_white w
    :
    (monoBlack w) -∗ (□ monoWhite w).
  Proof.
    unfold monoWhite. iIntros "H".
    iPoseProof (black_persistent_white_exact with "H") as "# H0".
    iClear "∗". iModIntro.
    iExists _. iSplit; eauto.
  Qed.

  Lemma white_exact_persistent w
    :
    (monoWhiteExact w) -∗ (□ monoWhiteExact w).
  Proof.
    unfold monoBlack, monoWhiteExact.
    iIntros "H". iPoseProof (own_persistent with "H") as "H". ss.
  Qed.

  Lemma white_mon w0 w1
    :
    (monoWhite w1) -∗ ⌜le w0 w1⌝ -∗ (monoWhite w0).
  Proof.
    unfold monoWhite. iIntros "H %".
    iDestruct "H" as (w) "[H %]".
    iExists _. iSplit; eauto. iPureIntro. etrans; eauto.
  Qed.

  Lemma white_persistent w
    :
    (monoWhite w) -∗ (□ monoWhite w).
  Proof.
    unfold monoWhite. iIntros "H".
    iDestruct "H" as (w1) "[H %]".
    iPoseProof (white_exact_persistent with "H") as "# H0".
    iClear "∗". iModIntro.
    iExists _. iSplit; eauto.
  Qed.

  Lemma black_updatable w0 w1
    :
    (monoBlack w0) -∗ ⌜le w0 w1⌝ -∗ (#=> monoBlack w1).
  Proof.
    iIntros "H %". iApply (OwnM_Upd with "H").
    eapply Auth.auth_update.
    rr. i. des. splits; auto.
    { rr. unseal "ra". ss. }
    { unfold URA.add in *. unseal "ra". ss.
      unfold Collection.add in *.
      extensionality w. eapply equal_f with (x:=w) in FRAME.
      eapply prop_ext_rev in FRAME. des.
      eapply propositional_extensionality. split; i; des; ss.
      split; eauto. eapply FRAME. etrans; eauto.
    }
  Qed.

  Lemma black_white_exact_compare w0 w1
    :
    (monoWhiteExact w0) -∗ (monoBlack w1) -∗ ⌜le w0 w1⌝.
  Proof.
    iIntros "H0 [H1 H2]".
    iCombine "H1 H0" as "H". iOwnWf "H".
    iPureIntro. eapply Auth.auth_included in H0.
    rr in H0. des. unfold URA.add in H0. unseal "ra".
    ss. unfold Collection.add in H0.
    eapply equal_f in H0. eapply prop_ext_rev in H0. des.
    eapply H1. reflexivity.
  Qed.

  Lemma black_white_compare w0 w1
    :
    (monoWhite w0) -∗ (monoBlack w1) -∗ ⌜le w0 w1⌝.
  Proof.
    unfold monoWhite.
    iIntros "H0 H1". iDestruct "H0" as (w) "[H0 %]".
    iPoseProof (black_white_exact_compare with "H0 H1") as "%".
    iPureIntro. etrans; eauto.
  Qed.
End Monotone.
