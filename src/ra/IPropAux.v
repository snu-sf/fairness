From sflib Require Import sflib.
Require Import Program.
From Fairness Require Import PCM IProp IPM.
From Fairness Require Import Axioms.

Set Implicit Arguments.

Section AUX.

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

  Lemma OwnM_ura_unit `{@GRA.inG M Σ}
    :
    ⊢ OwnM (@URA.unit M).
  Proof.
    rr. autorewrite with iprop. i.
    rr. autorewrite with iprop.
    exists r.
    Local Transparent GRA.to_URA URA.unit.
    replace (GRA.embed ε) with (@URA.unit Σ).
    { rewrite URA.unit_idl. auto. }
    unfold GRA.embed. extensionality n. des_ifs. ss.
    destruct H. ss. destruct inG_prf. ss.
  Qed.

End AUX.

Definition maps_to {Σ} {A: Type} {M: URA.t} `{ING: @GRA.inG (A ==> M)%ra Σ}
           (a: A) (m: M): iProp :=
  OwnM (maps_to_res a m).

Section UPD.
  Variable A: Type.
  Context `{IN: @GRA.inG (Auth.t (Excl.t A)) Σ}.

  Lemma black_white_update a0 a' a1
    :
    (OwnM (Auth.black (Excl.just a0: @Excl.t A)))
      -∗
      (OwnM (Auth.white (Excl.just a': @Excl.t A)))
      -∗
      #=> (OwnM (Auth.black (Excl.just a1: @Excl.t A)) ** OwnM (Auth.white (Excl.just a1: @Excl.t A))).
  Proof.
    iIntros "H0 H1". iCombine "H0 H1" as "H".
    iPoseProof (OwnM_Upd with "H") as "> [H0 H1]".
    { apply Auth.auth_update.
      instantiate (1:=Excl.just a1). instantiate (1:=Excl.just a1).
      ii. des. ur in FRAME. des_ifs. split.
      { ur. ss. }
      { ur. ss. }
    }
    iModIntro. iFrame.
  Qed.

  Lemma black_white_equal a a'
    :
    (OwnM (Auth.black (Excl.just a: @Excl.t A)))
      -∗
      (OwnM (Auth.white (Excl.just a': @Excl.t A)))
      -∗
      ⌜a = a'⌝.
  Proof.
    iIntros "H0 H1". iCombine "H0 H1" as "H".
    iOwnWf "H". ur in H. des.
    rr in H. des. ur in H. des_ifs.
  Qed.

  Lemma white_white_excl a a'
    :
    (OwnM (Auth.white (Excl.just a: @Excl.t A)))
      -∗
      (OwnM (Auth.white (Excl.just a': @Excl.t A)))
      -∗
      ⌜False⌝.
  Proof.
    iIntros "H0 H1". iCombine "H0 H1" as "H".
    iOwnWf "H". ur in H. ur in H. auto.
  Qed.

End UPD.

Section OWNS.

  Variable (Id: Type).
  Context `{R: URA.t}.
  Context `{IN1: @GRA.inG R Σ}.
  Context `{IN2: @GRA.inG (Id ==> R)%ra Σ}.

  Definition OwnMs (s: Id -> Prop) (u: R): iProp :=
    (OwnM ((fun i =>
              if (excluded_middle_informative (s i))
              then u
              else ε): (Id ==> R)%ra)).

  Lemma OwnMs_impl (s0 s1: Id -> Prop) u
        (IMPL: forall i (IN: s0 i), s1 i)
    :
    (OwnMs s1 u)
      -∗
      (OwnMs s0 u).
  Proof.
    iIntros "OWNMS".
    iApply (OwnM_extends with "OWNMS"). apply pointwise_extends.
    i. des_ifs; try by reflexivity.
    { exfalso. eauto. }
    { eexists _. rewrite URA.unit_idl. ss. }
  Qed.

  Lemma OwnMs_empty s u
        (EMPTY: forall i, ~ s i)
    :
    ⊢ OwnMs s u.
  Proof.
    iIntros. iApply (OwnM_extends with "[]").
    2:{ iApply (@OwnM_ura_unit (Id ==> R)%ra). }
    apply pointwise_extends. i. des_ifs.
    { exfalso. eapply EMPTY; eauto. }
    eexists _. rewrite URA.unit_idl. eauto.
  Qed.

  Lemma OwnMs_fold (s0 s1: Id -> Prop) i u
        (IMPL: forall j (IN: s0 j), s1 j \/ j = i)
    :
    ((OwnMs s1 u) ** (maps_to i u))
      -∗
      (OwnMs s0 u).
  Proof.
    iIntros "[OWNMS OWN]".
    iCombine "OWNMS OWN" as "OWNMS".
    iApply (OwnM_extends with "OWNMS"). apply pointwise_extends.
    i. erewrite ! (@unfold_pointwise_add Id R). unfold maps_to_res.
    des_ifs; ss; repeat rewrite URA.unit_id; repeat rewrite URA.unit_idl; ss; try by reflexivity.
    { eexists. apply URA.add_comm. }
    { hexploit IMPL; eauto. i. des; ss. }
    { eexists. rewrite URA.unit_idl. ss. }
    { eexists. rewrite URA.unit_idl. ss. }
    { eexists. rewrite URA.unit_idl. ss. }
  Qed.

  Definition OwnMs_unfold (s0 s1: Id -> Prop) i u
             (IMPL: forall j (IN: s0 j \/ j = i), s1 j)
             (NIN: ~ s0 i)
    :
    (OwnMs s1 u)
      -∗
      (OwnMs s0 u ** maps_to i u).
  Proof.
    iIntros "OWNMS".
    iPoseProof (OwnM_extends with "OWNMS") as "[OWNMS0 OWNMS1]".
    { instantiate (1:=maps_to_res i (u: R): (Id ==> R)%ra).
      instantiate (1:=(fun i =>
                         if (excluded_middle_informative (s0 i))
                         then u
                         else ε)).
      erewrite ! (@unfold_pointwise_add Id R). unfold maps_to_res.
      apply pointwise_extends. i.
      des_ifs; ss; repeat rewrite URA.unit_id; repeat rewrite URA.unit_idl; ss; try by reflexivity.
      { exfalso. eapply n0. auto. }
      { exfalso. eapply n0. auto. }
      { eexists. rewrite URA.unit_idl. ss. }
    }
    iFrame.
  Qed.

  Definition OwnMs_combine (s0 s1: Id -> Prop) u
    :
    (OwnMs s0 u ** OwnMs s1 u)
      -∗
      (OwnMs (fun i => s0 i \/ s1 i) u).
  Proof.
    iIntros "[OWNMS0 OWNMS1]".
    iCombine "OWNMS0 OWNMS1" as "OWNMS".
    iApply (OwnM_extends with "OWNMS"). apply pointwise_extends.
    i. erewrite ! (@unfold_pointwise_add Id R).
    des_ifs; ss; repeat rewrite URA.unit_id; repeat rewrite URA.unit_idl; ss; try by reflexivity.
    { eexists. eauto. }
    { des; ss. }
    { eexists. rewrite URA.unit_idl. ss. }
    { eexists. rewrite URA.unit_idl. ss. }
    { eexists. rewrite URA.unit_idl. ss. }
  Qed.

  Definition OwnMs_split (s0 s1: Id -> Prop) u
             (DISJOINT: forall i (IN0: s0 i) (IN1: s1 i), False)
    :
    (OwnMs (fun i => s0 i \/ s1 i) u)
      -∗
      (OwnMs s0 u ** OwnMs s1 u).
  Proof.
    iIntros "OWNMS".
    iPoseProof (OwnM_extends with "OWNMS") as "[OWNMS0 OWNMS1]".
    2:{ iSplitL "OWNMS0"; [iExact "OWNMS0"|iExact "OWNMS1"]. }
    { apply pointwise_extends.
      i. erewrite ! (@unfold_pointwise_add Id R).
      des_ifs; ss; repeat rewrite URA.unit_id; repeat rewrite URA.unit_idl; ss; try by reflexivity.
      { exfalso. eapply DISJOINT; eauto. }
      { exfalso. eapply n; eauto. }
      { exfalso. eapply n0; eauto. }
      { exfalso. eapply n0; eauto. }
      { des; ss. }
    }
  Qed.

End OWNS.
