From sflib Require Import sflib.
Require Import Program.
From Fairness Require Import PCM IPM.
From Fairness Require Import Axioms.

From iris.algebra Require Import cmra lib.excl_auth functions.
Set Implicit Arguments.

Section AUX.
  Fixpoint sep_conjs `{Σ: GRA.t} (Ps : nat -> iProp Σ) (n : nat) : iProp Σ :=
    match n with
    | O => True
    | S m => (sep_conjs Ps m) ∗ (Ps m)
    end.

  Lemma own_persistent `{@GRA.inG M Σ}
        (r: M)
    :
    (OwnM r) -∗ (□ OwnM (core r)).
  Proof.
    iIntros "H".
    iDestruct (OwnM_persistently with "H") as "#?".
    iModIntro. done.
  Qed.

  Lemma OwnM_ura_unit `{@GRA.inG M Σ}
    :
    ⊢ OwnM ((ε : M)).
  Proof. apply OwnM_unit. Qed.

End AUX.

Definition maps_to {Σ} {A: Type} {M: ucmra} `{ING: @GRA.inG (A -d> M) Σ}
           (a: A) (m: M): iProp Σ :=
  OwnM (maps_to_res a m).

Section UPD.
  Variable A: Type.
  Context `{IN: @GRA.inG (excl_authUR $ leibnizO A) Σ}.

  Lemma black_white_update (a0 a' a1 : A)
    :
    (OwnM (●E (a0 : leibnizO A)))
      -∗
      (OwnM (◯E (a' : leibnizO A)))
      -∗
      #=> (OwnM (●E (a1 : leibnizO A))) ∗ OwnM (◯E (a1 : leibnizO A)).
  Proof.
    iIntros "H0 H1". iCombine "H0 H1" as "H".
    iPoseProof (OwnM_Upd with "H") as "> [H0 H1]".
    { apply (excl_auth_update _ _ (a1 : leibnizO A)). }
    iModIntro. iFrame.
  Qed.

  Lemma black_white_equal (a a' : A)
    :
    (OwnM (●E (a : leibnizO A)))
      -∗
      (OwnM (◯E (a' : leibnizO A)))
      -∗
      ⌜a = a'⌝.
  Proof.
    iIntros "H0 H1". iCombine "H0 H1" as "H".
    iOwnWf "H". iPureIntro. by apply excl_auth_agree_L in H.
  Qed.

  Lemma white_white_excl a a'
    :
    (OwnM (excl_auth_frag a))
      -∗
      (OwnM (excl_auth_frag a' ))
      -∗
      ⌜False⌝.
  Proof.
    iIntros "H0 H1". iCombine "H0 H1" as "H".
    iOwnWf "H". by apply excl_auth_frag_op_valid in H.
  Qed.

End UPD.

Section OWNS.

  Variable (Id: Type).
  Context `{R: ucmra}.
  Context `{IN1: @GRA.inG R Σ}.
  Context `{IN2: @GRA.inG (Id -d> R) Σ}.
  Notation iProp := (iProp Σ).

  Definition OwnMs (s: Id -> Prop) (u: R): iProp :=
    (OwnM ((fun i =>
              if (excluded_middle_informative (s i))
              then u
              else ε): (Id -d> R))).

  Lemma OwnMs_impl (s0 s1: Id -> Prop) u
        (IMPL: forall i (IN: s0 i), s1 i)
    :
    (OwnMs s1 u)
      -∗
      (OwnMs s0 u).
  Proof.
    iIntros "OWNMS".
    iApply (OwnM_extends with "OWNMS"). apply discrete_fun_included_spec_2.
    i. des_ifs; try by reflexivity.
    exfalso. eauto.
  Qed.

  Lemma OwnMs_empty s u
        (EMPTY: forall i, ~ s i)
    :
    ⊢ OwnMs s u.
  Proof.
    iIntros. iApply (OwnM_extends with "[]").
    2:{ iApply (@OwnM_ura_unit (Id -d> R)). }
    apply discrete_fun_included_spec_2. i. des_ifs.
    { exfalso. eapply EMPTY; eauto. }
  Qed.

  Lemma OwnMs_fold (s0 s1: Id -> Prop) i u
        (IMPL: forall j (IN: s0 j), s1 j \/ j = i)
    :
    ((OwnMs s1 u) ∗ (maps_to i u))
      -∗
      (OwnMs s0 u).
  Proof.
    iIntros "[OWNMS OWN]".
    iCombine "OWNMS OWN" as "OWNMS".
    iApply (OwnM_extends with "OWNMS"). apply discrete_fun_included_spec_2.
    i. rewrite discrete_fun_lookup_op.
    des_ifs; ss; repeat rewrite right_id; repeat rewrite left_id; ss; try by reflexivity.
    hexploit IMPL; eauto. i. des; ss. subst.
    by rewrite discrete_fun_lookup_singleton.
  Qed.

  Definition OwnMs_unfold (s0 s1: Id -> Prop) i u
             (IMPL: forall j (IN: s0 j \/ j = i), s1 j)
             (NIN: ~ s0 i)
    :
    (OwnMs s1 u)
      -∗
      (OwnMs s0 u ∗ maps_to i u).
  Proof.
    iIntros "OWNMS".
    iPoseProof (OwnM_extends with "OWNMS") as "[$ $]".
    rewrite !discrete_fun_op.
    apply discrete_fun_included_spec_2=> a.
    destruct (excluded_middle_informative (i = a)) as [->|];
      rewrite ?discrete_fun_lookup_singleton ?discrete_fun_lookup_singleton_ne //;
    des_ifs; ss; repeat rewrite right_id; repeat rewrite left_id; ss; try by reflexivity.
    { exfalso. eapply n0. auto. }
    { exfalso. eapply n0. auto. }
  Qed.

  Definition OwnMs_combine (s0 s1: Id -> Prop) u
    :
    (OwnMs s0 u ∗ OwnMs s1 u)
      -∗
      (OwnMs (fun i => s0 i \/ s1 i) u).
  Proof.
    iIntros "[OWNMS0 OWNMS1]".
    iCombine "OWNMS0 OWNMS1" as "OWNMS".
    iApply (OwnM_extends with "OWNMS"). apply discrete_fun_included_spec_2.
    i. rewrite discrete_fun_lookup_op.
    des_ifs; ss; repeat rewrite right_id; repeat rewrite left_id; ss; try by reflexivity.
    des; ss.
  Qed.

  Definition OwnMs_split (s0 s1: Id -> Prop) u
             (DISJOINT: forall i (IN0: s0 i) (IN1: s1 i), False)
    :
    (OwnMs (fun i => s0 i \/ s1 i) u)
      -∗
      (OwnMs s0 u ∗ OwnMs s1 u).
  Proof.
    iIntros "OWNMS".
    iPoseProof (OwnM_extends with "OWNMS") as "[$ $]".
    apply discrete_fun_included_spec_2.
    i. rewrite discrete_fun_lookup_op.
    des_ifs; ss; repeat rewrite right_id; repeat rewrite left_id; ss; try by reflexivity.
    { exfalso. eapply DISJOINT; eauto. }
    { exfalso. eapply n; eauto. }
    { exfalso. eapply n0; eauto. }
    { exfalso. eapply n0; eauto. }
  Qed.

End OWNS.
