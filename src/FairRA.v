From sflib Require Import sflib.
From Fairness Require Import PCM IProp IPM.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.PropExtensionality.
From Fairness Require Import Axioms MonotonePCM.
Require Import Program.

Set Implicit Arguments.


Module NatRA.
  Global Program Instance t: URA.t := {
      car := nat;
      unit := 0;
      _add := Nat.add;
      _wf := fun _ => True;
      core := fun _ => 0;
    }
  .
  Next Obligation.
    lia.
  Qed.
  Next Obligation.
    lia.
  Qed.
  Next Obligation.
    unseal "ra". lia.
  Qed.
  Next Obligation.
    unseal "ra". auto.
  Qed.
  Next Obligation.
    unseal "ra". auto.
  Qed.
  Next Obligation.
    unseal "ra". lia.
  Qed.
  Next Obligation.
    unseal "ra". exists 0. lia.
  Qed.
End NatRA.


Module FairTgtRA.
  Section FAIRTGT.
    Definition t: URA.t := Auth.t NatRA.t.

    Context `{ING: @GRA.inG t Σ}.

    Definition curr (n: nat): iProp :=
      OwnM (Auth.black (n: NatRA.t)).

    Definition decr (n: nat): iProp :=
      OwnM (Auth.white (n: NatRA.t)).

    Lemma decr_sum (n0 n1: nat)
      :
      (decr n0)
        -∗
        (decr n1)
        -∗
        (decr (n0 + n1)).
    Proof.
      iIntros "H0 H1". iCombine "H0 H1" as "H".
      ur. ur. auto.
    Qed.

    Lemma decr_split (n0 n1: nat)
      :
      (decr (n0 + n1))
        -∗
        (decr n0 ** decr n1).
    Proof.
      iIntros "H". unfold decr.
      replace (Auth.white (n0 + n1: NatRA.t)) with (Auth.white (n0: NatRA.t) ⋅ Auth.white (n1: NatRA.t)).
      { iDestruct "H" as "[H0 H1]". iFrame. }
      repeat ur. auto.
    Qed.

    Lemma decr_0 (n0 n1: nat)
      :
      ⊢
        (decr 0).
    Proof.
      iIntros "". iApply (@OwnM_unit _ _ ING).
    Qed.

    Lemma decr_mon (n0 n1: nat)
          (LE: n0 <= n1)
      :
      (decr n1)
        -∗
        (decr n0).
    Proof.
      assert (exists n, n0 + n = n1).
      { exists (n1 - n0). lia. }
      des. subst. iIntros "H".
      iPoseProof (decr_split with "H") as "[H0 H1]". iFrame.
    Qed.

    Lemma curr_mon (n0 n1: nat)
          (LE: n0 <= n1)
      :
      (curr n0)
        -∗
        (#=> curr n1).
    Proof.
      iIntros "H". iPoseProof (OwnM_Upd with "H") as "> H".
      { instantiate (1:=Auth.black (n1: NatRA.t)).
        ii. repeat ur in H. des_ifs. des.
        rr in H. des. repeat ur in H.
        repeat ur. splits; auto. exists (n1 - e + ctx).
        repeat ur. lia.
      }
      iModIntro. eauto.
    Qed.

    Lemma success_update n2 n0 n1
      :
      (decr n0)
        -∗
        (curr n1)
        -∗
        (#=> (decr n2 ** ∃ n, curr n)).
    Proof.
      iIntros "H0 H1".
      iCombine "H1 H0" as "H".
      iPoseProof (OwnM_Upd_set with "H") as "> H".
      { instantiate (1:= fun r => exists ctx, r = Auth.black (n2 + ctx: NatRA.t) ⋅ Auth.white (n2: NatRA.t)).
        ii. ur in WF. des_ifs. des.
        exists (Auth.black (n2 + f0: NatRA.t) ⋅ Auth.white (n2: NatRA.t)).
        esplits; eauto. repeat ur. split; auto.
        exists 0. repeat ur. auto.
      }
      iDestruct "H" as "[% [% H]]". des. subst.
      iDestruct "H" as "[H0 H1]". iModIntro.
      iFrame. iExists _. eauto.
    Qed.

    Lemma fail_update n0 n1
          (LT: n0 < n1)
      :
      (decr n1)
        -∗
        (decr n0 ** decr 1).
    Proof.
      assert (exists n, n1 = n + n0 + 1).
      { exists (n1 - n0 - 1). lia. }
      des. subst.
      iIntros "H".
      iPoseProof (decr_split with "H") as "[H0 H1]".
      iPoseProof (decr_split with "H0") as "[H0 H2]".
      iFrame.
    Qed.

    Lemma decr_update_gen n0 n1
      :
      (curr n0)
        -∗
        (decr n1)
        -∗
        (#=> (∃ n, ⌜(n0 = n + n1)%nat⌝ ** curr n)).
    Proof.
      iIntros "H0 H1".
      iCombine "H1 H0" as "H".
      iOwnWf "H". repeat ur in H. des. rr in H. des.
      ur in H. ss.
      iPoseProof (OwnM_Upd with "H") as "> H".
      { instantiate (1:=Auth.black ctx). ii.
        repeat ur in H1. des_ifs. des.
        rr in H1. des. repeat ur in H1.
        repeat ur. splits; auto. exists ctx0.
        repeat ur. change (@URA.unit NatRA.t) with 0 in *. lia.
      }
      iModIntro. iExists _. iSplit; eauto.
      iPureIntro. change (@URA.unit NatRA.t) with 0 in *. lia.
    Qed.

    Lemma decr_update n1
      :
      (curr n1)
        -∗
        (decr 1)
        -∗
        (#=> (∃ n0, ⌜n0 < n1⌝ ** curr n0)).
    Proof.
      iIntros "H0 H1".
      iPoseProof (decr_update_gen with "H0 H1") as "> [% [% H]]".
      iModIntro. iExists _. iSplit; eauto. iPureIntro. lia.
    Qed.
  End FAIRTGT.
End FairTgtRA.
