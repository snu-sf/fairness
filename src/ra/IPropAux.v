From sflib Require Import sflib.
Require Import Program.
From Fairness Require Import PCM IPM.
From Fairness Require Import Axioms.

From iris.algebra Require Import cmra lib.excl_auth functions.
Set Implicit Arguments.

(* Section AUX.

  Lemma own_persistent `{@GRA.inG M Σ}
        (r: M)
    :
    (own γ r) -∗ (□ own γ (core r)).
  Proof.
    iIntros "H".
    iDestruct (own γ_persistently with "H") as "#?".
    iModIntro. done.
  Qed.

  Lemma OwnM_ura_unit `{@GRA.inG M Σ}
    :
    ⊢ own γ ((ε : M)).
  Proof. apply own γ_unit. Qed.

End AUX. *)

(* Definition maps_to {Σ} {A: Type} {M: ucmra} `{ING: @GRA.inG (A ==> M)%ra Σ}
           (a: A) (m: M): iProp Σ :=
  OwnM (maps_to_res a m). *)

Section UPD.
  Variable A: Type.
  Context `{IN: !inG Σ (excl_authUR $ leibnizO A)}.
  Implicit Types (a b : A).

  Lemma black_white_update {γ} a0 a' a1
    :
    own γ (●E (a0 : leibnizO A))
      -∗
      own γ (◯E (a' : leibnizO A))
      -∗
      #=> own γ (●E (a1 : leibnizO A)) ∗ own γ (◯E (a1 : leibnizO A)).
  Proof.
    iIntros "B W".
    iMod (own_update_2 with "B W") as "[$ $]"; [|done].
    apply excl_auth_update.
  Qed.

  Lemma black_white_equal {γ} (a a' : A)
    :
    own γ (●E (a : leibnizO A))
      -∗
      own γ (◯E (a' : leibnizO A))
      -∗
      ⌜a = a'⌝.
  Proof. iIntros "B W". by iCombine "B W" gives %H%excl_auth_agree_L. Qed.

  Lemma white_white_excl {γ} a a'
    :
    own γ (◯E (a : leibnizO _))
      -∗
      own γ (◯E (a' : leibnizO _))
      -∗
      ⌜False⌝.
  Proof. iIntros "W W'". by iCombine "W W'" gives %H%excl_auth_frag_op_valid. Qed.

End UPD.

(* Section OWNS.

  Context (Id: Type).
  Context `{R: ucmra}.
  Context `{!inG Σ R, !inG Σ (Id -d> R)}.
  Notation iProp := (iProp Σ).

  (* This works thanks to the explicit type annotation. *)
  Definition OwnMs γ (s: Id -> Prop) (u: R): iProp :=
    own γ ((λ i, if excluded_middle_informative (s i) then u else ε) : Id -d> R).

  Lemma OwnMs_impl {γ} (s0 s1: Id -> Prop) u
        (IMPL: forall i (IN: s0 i), s1 i)
    :
    OwnMs γ s1 u -∗ OwnMs γ s0 u.
  Proof.
    iIntros "OWNMS".
    iApply (own_mono with "OWNMS"). apply included_discrete_fun.
    i. des_ifs; try by reflexivity.
    exfalso. eauto.
  Qed.

  Lemma OwnMs_empty {γ} s u
        (EMPTY: forall i, ¬ s i)
    :
    ⊢ #=> OwnMs γ s u.
  Proof.
    iMod own_unit. iApply (own_mono with "[$]").
    apply included_discrete_fun. i. des_ifs.
    exfalso. eapply EMPTY. eauto.
  Qed.

  Lemma OwnMs_fold {γs} (s0 s1: Id -> Prop) i u
        (IMPL: forall j (IN: s0 j), s1 j ∨ j = i)
    :
    (OwnMs γs s1 u ∗ own γs (discrete_fun_singleton i u))
      -∗
      OwnMs γs s0 u.
  Proof.
    iIntros "[own γS OWN]".
    iCombine "own γS OWN" as "own γS".
    iApply (own γ_extends with "own γS"). apply pointwise_extends.
    i. rewrite discrete_fun_lookup_op /maps_to_res.
    des_ifs; ss; repeat rewrite right_id; repeat rewrite left_id; ss; try by reflexivity.
    hexploit IMPL; eauto. i. des; ss.
  Qed.

  Definition own γs_unfold (s0 s1: Id -> Prop) i u
             (IMPL: forall j (IN: s0 j \/ j = i), s1 j)
             (NIN: ~ s0 i)
    :
    (own γs s1 u)
      -∗
      (own γs s0 u ∗ maps_to i u).
  Proof.
    iIntros "own γS".
    iPoseProof (own γ_extends with "own γS") as "[own γS0 own γS1]".
    { instantiate (1:=maps_to_res i (u: R): (Id ==> R)%ra).
      instantiate (1:=(fun i =>
                         if (excluded_middle_informative (s0 i))
                         then u
                         else ε)).
      erewrite ! (@unfold_pointwise_add Id R). unfold maps_to_res.
      apply pointwise_extends. i.
      des_ifs; ss; repeat rewrite right_id; repeat rewrite left_id; ss; try by reflexivity.
      { exfalso. eapply n0. auto. }
      { exfalso. eapply n0. auto. }
    }
    iFrame.
  Qed.

  Definition own γs_combine (s0 s1: Id -> Prop) u
    :
    (own γs s0 u ∗ own γs s1 u)
      -∗
      (own γs (fun i => s0 i \/ s1 i) u).
  Proof.
    iIntros "[own γS0 own γS1]".
    iCombine "own γS0 own γS1" as "own γS".
    iApply (own γ_extends with "own γS"). apply pointwise_extends.
    i. rewrite discrete_fun_lookup_op.
    des_ifs; ss; repeat rewrite right_id; repeat rewrite left_id; ss; try by reflexivity.
    des; ss.
  Qed.

  Definition own γs_split (s0 s1: Id -> Prop) u
             (DISJOINT: forall i (IN0: s0 i) (IN1: s1 i), False)
    :
    (own γs (fun i => s0 i \/ s1 i) u)
      -∗
      (own γs s0 u ∗ own γs s1 u).
  Proof.
    iIntros "own γS".
    iPoseProof (own γ_extends with "own γS") as "[own γS0 own γS1]".
    2:{ iSplitL "own γS0"; [iExact "own γS0"|iExact "own γS1"]. }
    { apply pointwise_extends.
      i. rewrite discrete_fun_lookup_op.
      des_ifs; ss; repeat rewrite right_id; repeat rewrite left_id; ss; try by reflexivity.
      { exfalso. eapply DISJOINT; eauto. }
      { exfalso. eapply n; eauto. }
      { exfalso. eapply n0; eauto. }
      { exfalso. eapply n0; eauto. }
    }
  Qed.

End OWNS. *)
