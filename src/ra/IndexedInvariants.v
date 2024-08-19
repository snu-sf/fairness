From stdpp Require Import coPset gmap namespaces.
From sflib Require Import sflib.

From iris.algebra Require Import gmap_view agree coPset gset functions.
From iris.bi Require Import big_op.
From iris.base_logic Require lib.invariants.
From Fairness.base_logic Require Import base_logic lib.own.

From Fairness Require Import IPM SRA.

From iris.prelude Require Import options.

Local Notation index := nat.

Section INDEXED_INVARIANT_SET.

  Context `{Σ : gFunctors}.
  Notation iProp := (iProp Σ).

  Class IInvSet (Vars : index -> Type) :=
    { prop : forall (i : index), (Vars i) -> iProp }.

  Definition InvSetRA (Vars : index -> Type) (n : index) : ofe :=
    (gmap_viewO positive (agreeR $ leibnizO (Vars n))).

  Definition IInvSetRA (Vars : index -> Type) : ucmra :=
    discrete_fun (InvSetRA Vars).

End INDEXED_INVARIANT_SET.
Global Arguments IInvSet _ _ : clear implicits.

(** [w]orld [sat]isfaction [G]functor pre [S]ingleton *)
(* The [S] denotes the fact that this is unique. *)
(* This is not a real [gFunctor] but an [cmra]. See [own.v] for more information. *)
Class wsatGpreS (Σ : gFunctors) : Set := WsatGpreS {
  (* wsatGpreS_inv : inG Σ (IInvSetRA Vars); *)
  wsatGpreS_enabled : inG Σ coPset_disjR;
  wsatGpreS_disabled : inG Σ (gset_disjR positive);
}.

Class wsatGS (Σ : gFunctors) : Set := WsatGS {
  wsat_inG : wsatGpreS Σ;
  (* invariant_name : gname; *)
  enabled_name : gname;
  disabled_name : gname;
}.

Global Arguments WsatGS Σ {_} _ _.
(* Global Arguments invariant_name {Σ Vars _} : assert. *)
Global Arguments enabled_name {Σ _} : assert.
Global Arguments disabled_name {Σ _} : assert.


Definition wsatΣ : gFunctors :=
  #[GFunctor coPset_disjR;
    GFunctor (gset_disjR positive)].

Global Instance subG_wsatΣ {Σ} : subG wsatΣ Σ → wsatGpreS Σ.
Proof. solve_inG. Qed.

Global Instance sra_subG_wsatGS {Γ Σ} : @SRA.subG Γ Σ → wsatGS (SRA.to_gf Γ) → wsatGS Σ.
Proof.
  intros SUB [[] γe γd].
  split; [split; apply _|exact γe|exact γd].
Defined.

Local Existing Instances wsat_inG wsatGpreS_enabled wsatGpreS_disabled.

Class invGpreS (Σ : gFunctors) (Vars : index → Type) : Set := InvGpreS {
  invGpreS_inv : inG Σ (IInvSetRA Vars);
}.

Class invGS (Σ : gFunctors) (Vars : index → Type) := InvG {
  invGS_inv : invGpreS Σ Vars;
  invariant_name : gname;
}.

Global Hint Mode invGS - - : typeclass_instances.
Global Hint Mode invGpreS - - : typeclass_instances.
Global Existing Instances invGpreS_inv invGS_inv.

Definition invΣ Vars : gFunctors :=
  #[GFunctor (IInvSetRA Vars)].
Global Instance subG_invΣ {Σ Vars} : subG (invΣ Vars) Σ → invGpreS Σ Vars.
Proof. solve_inG. Qed.

(* Global Instance sra_subG_invGS {Γ Σ Vars} : @SRA.subG Γ Σ → invGS (SRA.to_gf Γ) Vars → invGS Σ Vars.
Proof.
  intros SUB [[] γi].
  split; [split; apply _|exact γi].
Qed. *)

Section PCM_OWN.
  Definition OwnE `{!wsatGS Σ} (E : coPset) : iProp Σ := own enabled_name (CoPset E).

  Definition OwnD `{!wsatGS Σ} (D : gset positive) := own disabled_name (GSet D).

  Definition OwnI_white {Vars} (n : index) (i : positive) (p : Vars n) : IInvSetRA Vars :=
    discrete_fun_singleton n (gmap_view_frag i DfracDiscarded (to_agree (p : leibnizO (Vars n)))).

  Definition OwnI `{!invGS Σ Vars} (n : index) (i : positive) (p : Vars n) :=
    own invariant_name (OwnI_white n i p).

  Lemma OwnE_exploit `{!wsatGS Σ} (E1 E2 : coPset) :
    OwnE E1 ∗ OwnE E2 ⊢ ⌜E1 ## E2⌝.
  Proof.
    iIntros "[H1 H2]". iCombine "H1 H2" as "H". iOwnWf "H" as WF.
    iPureIntro. by apply coPset_disj_valid_op.
  Qed.

  Lemma OwnE_union `{!wsatGS Σ} (E1 E2 : coPset) :
    OwnE E1 ∗ OwnE E2 ⊢ OwnE (E1 ∪ E2).
  Proof.
    iIntros "H". iDestruct (OwnE_exploit with "H") as %D.
    rewrite -own_op coPset_disj_union //.
  Qed.

  Lemma OwnE_disjoint `{!wsatGS Σ} (E1 E2 : coPset) :
    E1 ## E2 -> OwnE (E1 ∪ E2) ⊢ OwnE E1 ∗ OwnE E2.
  Proof.
    iIntros (D) "H".
    rewrite /OwnE -own_op coPset_disj_union //.
  Qed.

  Lemma OwnE_add `{!wsatGS Σ} (E1 E2 : coPset) :
    E1 ## E2 -> OwnE (E1 ∪ E2) ⊣⊢ OwnE E1 ∗ OwnE E2.
  Proof.
    i. iSplit.
    - iApply OwnE_disjoint. done.
    - iApply OwnE_union.
  Qed.
  Lemma OwnE_is_disjoint `{!wsatGS Σ} E1 E2 : OwnE E1 ∗ OwnE E2 ⊢ ⌜E1 ## E2⌝.
  Proof. apply OwnE_exploit. Qed.
  Lemma OwnE_add' `{!wsatGS Σ} E1 E2 : ⌜E1 ## E2⌝ ∧ OwnE (E1 ∪ E2) ⊣⊢ OwnE E1 ∗ OwnE E2.
  Proof.
    iSplit; [iIntros "[% ?]"; by iApply OwnE_add|].
    iIntros "HE". iDestruct (OwnE_is_disjoint with "HE") as %?.
    iSplit; first done. iApply OwnE_add; by try iFrame.
  Qed.
  Lemma OwnE_singleton_twice `{!wsatGS Σ} i : OwnE {[i]} ∗ OwnE {[i]} ⊢ False.
  Proof. rewrite OwnE_is_disjoint. iIntros (?); set_solver. Qed.

  Lemma OwnE_subset `{!wsatGS Σ} (E1 E2 : coPset) :
    E1 ⊆ E2 -> OwnE E2 ⊢ OwnE E1 ∗ (OwnE E1 -∗ OwnE E2).
  Proof.
    iIntros (SUB) "E".
    assert (E2 = E1 ∪ E2 ∖ E1) as EQ.
    { eapply union_difference_L. ss. }
    rewrite EQ.
    iPoseProof (OwnE_disjoint with "E") as "[E1 E2]"; [set_solver|].
    iFrame. iIntros "E1".
    iApply OwnE_union. iFrame.
  Qed.

  Global Instance OwnI_persistent `{!invGS Σ Vars}
    n i p : Persistent (OwnI n i p).
  Proof. apply _. Qed.
End PCM_OWN.

Section WORLD_SATISFACTION.
  Context `{!wsatGS Σ, !invGS Σ Vars, INV : !IInvSet Σ Vars}.

  Notation iProp := (iProp Σ).

  Variable n : index.
  Local Notation Var := (Vars n).

  Definition inv_auth_black (I : gmap positive Var) : IInvSetRA Vars :=
    discrete_fun_singleton n (gmap_view_auth (DfracOwn 1) (to_agree (A:= leibnizO _) <$> I)).

  Definition inv_auth (I : gmap positive Var) := own invariant_name (inv_auth_black I).

  Definition inv_satall (I : gmap positive Var) :=
    ([∗ map] i ↦ p ∈ I, (prop n p) ∗ OwnD {[i]} ∨ OwnE {[i]})%I.

  Definition wsat : iProp := (∃ I, inv_auth I ∗ inv_satall I)%I.


  Lemma alloc_name φ
    (INF : forall (E : gset positive), exists i, i ∉ E /\ φ i)
    : ⊢ |==> ∃ i, ⌜φ i⌝ ∧ OwnD {[i]}.
  Proof.
    assert ((GSet (∅ : gset positive)) ~~>: (fun r => exists i, r = GSet {[i]} /\ φ i)) as UPD.
    { clear - INF. apply gset_disj_alloc_empty_updateP_strong'. done. }
    iMod own_unit as "H".
    iMod (own_updateP _ _ _ UPD with "H") as "[% [% DIS]]".
    iModIntro. des. subst. iExists i. eauto.
  Qed.

  Lemma wsat_OwnI_alloc_gen p φ
        (INF : forall (E : gset positive), exists i, i ∉ E /\ φ i)
    : wsat ⊢ |==> (∃ i, ⌜φ i⌝ ∧ OwnI n i p) ∗ (prop n p -∗ wsat).
  Proof.
    iIntros "[% [AUTH SAT]]".
    iMod (alloc_name (fun i => i ∉ dom I /\ φ i)) as "[% [%Hi D]]".
    { i. specialize (INF (E ∪ dom I)). des. eapply not_elem_of_union in INF. des. esplits; eauto. }
    destruct Hi as [iI iφ].
    pose (<[i:=p]> I) as I'.

    assert (inv_auth_black I ~~> inv_auth_black I' ⋅ OwnI_white n i p) as UPD.
    { unfold inv_auth_black, OwnI_white.
      rewrite discrete_fun_singleton_op /I' fmap_insert.
      apply discrete_fun_singleton_update,gmap_view_alloc; [|done..].
      apply not_elem_of_dom_1.
      by rewrite dom_fmap.
    }
    unfold inv_auth, inv_satall.
    iMod (own_update _ _ _ UPD with "AUTH") as "[AUTH NEW]". iModIntro.

    iSplit.
    - iExists i. iFrame. ss.
    - iIntros "P". unfold wsat. iExists I'. iFrame.
      unfold inv_satall. subst I'.
      iApply big_sepM_insert.
      { apply not_elem_of_dom_1; ss. }
      iSplitL "P D"; ss. iLeft. iFrame.
  Qed.

  Lemma wsat_OwnI_alloc p φ
        (INF : forall (E : gset positive), exists i, i ∉ E /\ φ i)
    : wsat ∗ prop n p ⊢ |==> (∃ i, ⌜φ i⌝ ∧ OwnI n i p) ∗ wsat.
  Proof.
    iIntros "[W P]".
    iMod (wsat_OwnI_alloc_gen with "W") as "[I W]"; [eauto|].
    iFrame. iModIntro. iApply "W". iFrame.
  Qed.

  Lemma wsat_OwnI_open i p :
    OwnI n i p ∗ wsat ∗ OwnE {[i]} ⊢ |==> prop n p ∗ wsat ∗ OwnD {[i]}.
  Proof.
    iIntros "(I & [% [AUTH SAT]] & EN)". iModIntro.
    unfold OwnI, inv_auth, inv_satall.
    iCombine "AUTH I" gives %WF.
    assert (Hip : I !! i = Some p).
    { rewrite /inv_auth_black /OwnI_white discrete_fun_singleton_op in WF.
      specialize (WF n).
      rewrite discrete_fun_lookup_singleton in WF.
      apply gmap_view_both_dfrac_valid_discrete_total in WF. des.
      (* TODO: slightly ackward proof to dance around agree limitations. *)
      rewrite lookup_fmap in WF1.
      have [p' Hv'] : (is_Some (I !! i)).
      { rewrite -fmap_is_Some. eauto. }
      rewrite Hv' /= in WF1. clarify.
      apply to_agree_included_L in WF3. by subst.
    }
    clear WF.
    iPoseProof (big_sepM_delete _ _ _ _ Hip with "SAT") as "[[[H1 H2]|H1] SAT]".
    2: { iCombine "EN H1" gives %WF%coPset_disj_valid_op. set_solver. }
    iFrame "H1 H2". unfold wsat. iExists I. iFrame. unfold inv_satall.
    iApply (big_sepM_delete _ _ _ _ Hip). iFrame.
  Qed.

  Lemma wsat_OwnI_close i p :
    OwnI n i p ∗ wsat ∗ prop n p ∗ OwnD {[i]} ⊢ |==> wsat ∗ OwnE {[i]}.
  Proof.
    iIntros "(I & [% [AUTH SAT]] & P & DIS)". iModIntro.
    unfold OwnI, inv_auth, inv_satall.
    iCombine "AUTH I" gives %WF.
    assert (Hip : I !! i = Some p).
    { rewrite /inv_auth_black /OwnI_white discrete_fun_singleton_op in WF.
      specialize (WF n).
      rewrite discrete_fun_lookup_singleton in WF.
      apply gmap_view_both_dfrac_valid_discrete_total in WF. des.
      (* TODO: slightly ackward proof to dance around agree limitations. *)
      rewrite lookup_fmap in WF1.
      have [p' Hv'] : (is_Some (I !! i)).
      { rewrite -fmap_is_Some. eauto. }
      rewrite Hv' /= in WF1. clarify.
      apply to_agree_included_L in WF3. by subst.
    }
    clear WF.
    iPoseProof (big_sepM_delete _ _ _ _ Hip with "SAT") as "[[[H1 H2]|H1] SAT]".
    { iCombine "DIS H2" gives %WF%gset_disj_valid_op. set_solver. }
    iFrame "H1". unfold wsat. iExists I. iFrame. unfold inv_satall.
    iApply (big_sepM_delete _ _ _ _ Hip). iFrame. iLeft. iFrame.
  Qed.

  Lemma wsat_init :
    own invariant_name (inv_auth_black ∅)
      ⊢ wsat.
  Proof.
    iIntros "H". iExists ∅. iFrame.
    unfold inv_satall. iApply big_sepM_empty. ss.
  Qed.

End WORLD_SATISFACTION.

Section WSATS.
  Context `{!wsatGS Σ, !invGS Σ Vars, INV : !IInvSet Σ Vars}.
  Notation iProp := (iProp Σ).

  Definition wsat_auth_black (x : index) : IInvSetRA Vars :=
    λ n,
      if decide (n < x) then ε
      else (gmap_view_auth (DfracOwn 1) ∅).

  Definition wsat_auth (x : index) := own invariant_name (wsat_auth_black x).

  (* wsat n for all n < x *)
  Definition wsats (x : index) := sep_conjs wsat x.

  Definition wsats_l (x : index) := ([∗ list] n ∈ (seq 0 x), wsat n)%I.

  Lemma unfold_wsats x :
    wsats (S x) = (wsats x ∗ wsat x)%I.
  Proof. ss. Qed.

  Lemma eq_wsats_l x :
    wsats_l (S x) ⊣⊢ (wsats_l x ∗ wsat x)%I.
  Proof. rewrite /wsats_l seq_S big_sepL_snoc //=. Qed.

  Lemma unfold_wsats_l x :
    wsats_l (S x) ⊢ wsats_l x ∗ wsat x.
  Proof. by rewrite eq_wsats_l. Qed.

  Lemma fold_wsats_l x :
    wsats_l x ∗ wsat x ⊢ wsats_l (S x).
  Proof. by rewrite eq_wsats_l. Qed.

  Lemma wsats_equiv_l x :
    wsats x ⊣⊢ wsats_l x.
  Proof. induction x as [|x IH]; [done|]. rewrite eq_wsats_l -IH //. Qed.

  Lemma wsats_init_zero :
    own invariant_name (wsat_auth_black 0) ⊢ wsat_auth 0 ∗ wsats 0.
  Proof. iIntros "$". Qed.

  Lemma wsat_auth_nin (x n : index) (NIN : x ≤ n)
    : wsat_auth x ⊢ wsat_auth n ∗ ([∗ list] m ∈ (seq x (n - x)), wsat m).
  Proof.
    induction NIN.
    - iIntros "AUTH". rename x into n. remember (S n) as x.
      assert (wsat_auth_black n ≡
                wsat_auth_black x
                   ⋅
                   discrete_fun_singleton n (gmap_view_auth (DfracOwn 1) ∅)).
      { subst. intros a. rewrite /wsat_auth_black discrete_fun_lookup_op.
        destruct (decide (n = a)); des_ifs; try lia.
        - rewrite discrete_fun_lookup_singleton left_id //.
        - rewrite discrete_fun_lookup_singleton_ne // left_id.
        - rewrite discrete_fun_lookup_singleton_ne // left_id.
      }
      rewrite Nat.sub_diag. simpl. iFrame.
    - iIntros "AUTH". iPoseProof (IHNIN with "AUTH") as "[AUTH SAT]".
      clear IHNIN. remember (S m) as y.
      assert (wsat_auth_black m ≡
                wsat_auth_black y
                   ⋅
                   discrete_fun_singleton m (gmap_view_auth (DfracOwn 1) ∅)) as EQ.
      { subst. intros a. rewrite /wsat_auth_black discrete_fun_lookup_op.
        destruct (decide (m = a)).
        all: des_ifs; try lia.
        - rewrite discrete_fun_lookup_singleton left_id //.
        - rewrite discrete_fun_lookup_singleton_ne // left_id.
        - rewrite discrete_fun_lookup_singleton_ne // left_id.
      }
      rewrite /wsat_auth EQ. iDestruct "AUTH" as "[AUTH NEW]".
      iPoseProof (wsat_init with "NEW") as "NEW".
      subst y. iFrame.
      replace (S m - x) with ((m - x) + 1) by lia. rewrite seq_app.
      iApply big_sepL_app. iFrame.
      replace (x + (m - x)) with m by lia. ss. iFrame.
  Qed.

  Lemma wsats_nin (x n : index) (NIN : x ≤ n)
    : wsats x ∗ ([∗ list] m ∈ (seq x (n - x)), wsat m) ⊢ wsats n.
  Proof.
    rewrite ! wsats_equiv_l.
    iIntros "[SALL WSAT]". unfold wsats_l.
    replace n with (x + (n - x)) by lia. rewrite seq_app. iFrame.
    replace (x + (n - x) - x) with (n - x) by lia. iFrame.
  Qed.

  Lemma wsats_in (x0 x1 : index) :
    x0 ≤ x1 -> wsats x1 ⊢ wsats x0 ∗ ([∗ list] n ∈ (seq x0 (x1 - x0)), wsat n).
  Proof.
    rewrite ! wsats_equiv_l.
    iIntros (LE) "SAT". unfold wsats_l.
    replace x1 with (x0 + (x1 - x0)) by lia. rewrite (seq_app _ _ 0).
    iPoseProof (big_sepL_app with "SAT") as "[SAT K]". iFrame.
    ss. replace (x0 + (x1 - x0) - x0) with (x1 - x0) by lia. iFrame.
  Qed.

  Lemma wsats_drop_keep (x : index) :
    wsats (S x) ⊢ wsats x ∗ wsat x.
  Proof.
    iIntros "WS". iPoseProof (wsats_in x with "WS") as "[WS W]"; [auto|].
    iFrame. replace (S x - x) with (S O) by lia. rewrite seq_S.
    simpl. replace (x + 0) with x by lia. iDestruct "W" as "[W _]". iFrame.
  Qed.

  Lemma wsats_allocs x1 x2 :
    x1 ≤ x2 -> wsat_auth x1 ∗ wsats x1 ⊢ (wsat_auth x2 ∗ wsats x2).
  Proof.
    iIntros (LE) "[AUTH SAT]".
    iDestruct ((wsat_auth_nin _ _ LE) with "AUTH") as "[$ NEW]".
    iDestruct ((wsats_nin _ _ LE) with "[$SAT $NEW]") as "$".
  Qed.


  Lemma wsats_OwnI_alloc_lt_gen x n (LT : n < x) p φ
        (INF : forall (E : gset positive), exists i, i ∉ E /\ φ i)
    : wsats x ⊢ |==> (∃ i, ⌜φ i⌝ ∧ OwnI n i p) ∗ (prop n p -∗ wsats x).
  Proof.
    rewrite ! wsats_equiv_l.
    iIntros "SALL".
    iPoseProof (big_sepL_lookup_acc with "SALL") as "[WSAT K]".
    { apply lookup_seq_lt; eauto. }
    iPoseProof (wsat_OwnI_alloc_gen with "WSAT") as ">[RES WSAT]"; [apply INF|]. iFrame.
    iModIntro. iIntros "P". iFrame. iPoseProof ("WSAT" with "P") as "WSAT".
    iPoseProof ("K" with "WSAT") as "SALL". iFrame.
  Qed.

  Lemma wsats_OwnI_alloc_lt x n (LT : n < x) p φ
        (INF : forall (E : gset positive), exists i, i ∉ E /\ φ i)
    : wsats x ∗ prop n p ⊢ |==> (∃ i, ⌜φ i⌝ ∧ OwnI n i p) ∗ wsats x.
  Proof.
    iIntros "[W P]". iMod (wsats_OwnI_alloc_lt_gen with "W") as "[I W]". 1,2: eauto.
    iModIntro. iFrame. iApply "W". iFrame.
  Qed.

  Lemma wsats_OwnI_alloc_ge_gen x n (GE : x <= n) p φ
        (INF : forall (E : gset positive), exists i, i ∉ E /\ φ i)
    : wsat_auth x ∗ wsats x ⊢
                |==> (∃ i, ⌜φ i⌝ ∧ OwnI n i p) ∗ wsat_auth (S n) ∗ (prop n p -∗ wsats (S n)).
  Proof.
    iIntros "(AUTH & WSAT)".
    iPoseProof ((wsats_allocs x (S n)) with "[$AUTH $WSAT]") as "[AUTH WSAT]"; [lia|].
    iMod ((wsats_OwnI_alloc_lt_gen (S n) n) with "WSAT") as "[RES WSAT]"; [eauto..|].
    iFrame. done.
  Qed.

  Lemma wsats_OwnI_alloc_ge x n (GE : x <= n) p φ
        (INF : forall (E : gset positive), exists i, i ∉ E /\ φ i)
    : wsat_auth x ∗ wsats x ∗ prop n p ⊢ |==> (∃ i, ⌜φ i⌝ ∧ OwnI n i p) ∗ wsat_auth (S n) ∗ wsats (S n).
  Proof.
    iIntros "(A & W & P)". iMod (wsats_OwnI_alloc_ge_gen with "[$A $W]") as "($ & $ & W)"; [auto..|].
    iModIntro. iApply "W". iFrame.
  Qed.

  Lemma wsat_auth_OwnI_le x n i p :
    OwnI n i p ∗ wsat_auth x ⊢ ⌜n < x⌝.
  Proof.
    iIntros "(I & AUTH)".
    unfold OwnI, wsat_auth.
    iCombine "AUTH I" gives %WF.
    specialize (WF n).
    rewrite /wsat_auth_black /OwnI_white
      discrete_fun_lookup_op discrete_fun_lookup_singleton in WF.
    des_ifs. exfalso.
    apply gmap_view_both_dfrac_valid_discrete_total in WF. des.
    rewrite lookup_empty in WF1. clarify.
  Qed.

  Lemma wsats_OwnI_open x n i p :
    n < x -> OwnI n i p ∗ wsats x ∗ OwnE {[i]} ⊢ |==> prop n p ∗ wsats x ∗ OwnD {[i]}.
  Proof.
    rewrite ! wsats_equiv_l.
    iIntros (LT) "(I & SAT & EN)".
    unfold OwnI, wsats.
    iPoseProof (big_sepL_lookup_acc with "SAT") as "[WSAT K]".
    { apply lookup_seq_lt; eauto. }
    ss. iMod (wsat_OwnI_open with "[$I $WSAT $EN]") as "[P [WSAT DN]]".
    iPoseProof ("K" with "WSAT") as "SAT".
    iModIntro. iFrame.
  Qed.

  Lemma wsats_OwnI_close x n i p :
    n < x -> OwnI n i p ∗ wsats x ∗ prop n p ∗ OwnD {[i]} ⊢ |==> wsats x ∗ OwnE {[i]}.
  Proof.
    rewrite ! wsats_equiv_l.
    iIntros (LT) "(I & SAT & P & DIS)".
    iPoseProof (big_sepL_lookup_acc with "SAT") as "[WSAT K]".
    { apply lookup_seq_lt; eauto. }
    iMod (wsat_OwnI_close with "[$I $WSAT $P $DIS]") as "[WSAT EN]".
    iPoseProof ("K" with "WSAT") as "SAT".
    iModIntro. iFrame.
  Qed.

End WSATS.

(* Lemma gen_heap_init_names `{Countable L, !gen_heapGpreS L V Σ} σ :
  ⊢ |==> ∃ γh γm : gname,
    let hG := GenHeapGS L V Σ γh γm in
    gen_heap_interp σ ∗ ([∗ map] l ↦ v ∈ σ, l ↦ v) ∗ ([∗ map] l ↦ _ ∈ σ, meta_token l ⊤).
Proof. *)

Lemma wsat_alloc x `{!wsatGpreS Σ, !invGpreS Σ Vars, !IInvSet Σ Vars} :
  (* wsatGS *)
  ⊢ #=> ∃ (_ : wsatGS Σ) (_ : invGS Σ Vars),
        wsat_auth x ∗ wsats x ∗ OwnE ⊤.
Proof.
  iIntros.
  iMod (own_alloc (wsat_auth_black 0)) as (γI) "HIA".
  { rewrite /wsat_auth_black => n. des_ifs; [apply ucmra_unit_valid|].
    apply gmap_view_auth_valid.
  }
  iMod (own_alloc (CoPset ⊤)) as (γE) "HE"; first done.
  iMod (own_alloc (GSet ∅)) as (γD) "HD"; first done.
  set (WSAT := WsatGS _ γE γD).
  set (INV := InvG _ _ _ γI).
  iModIntro; iExists WSAT,INV. iFrame.
  iAssert (wsats 0)%I as "HIF"; ss.
  iDestruct (wsats_allocs with "[$HIA $HIF]") as "($ & $)". lia.
Qed.

Section FANCY_UPDATE.
  Context `{!wsatGS Σ, !invGS Σ Vars, INV : !IInvSet Σ Vars}.
  Notation iProp := (iProp Σ).

  Definition inv (n : index) (N : namespace) p :=
    (∃ i, ⌜i ∈ (↑N : coPset)⌝ ∧ OwnI n i p)%I.

  Local Definition FUpd_def x (A : iProp) (E1 E2 : coPset) (P : iProp) : iProp :=
    A ∗ wsats x ∗ OwnE E1 -∗ #=> (A ∗ wsats x ∗ OwnE E2 ∗ P).
  Local Definition FUpd_aux : seal (@FUpd_def). Proof. by eexists. Qed.
  Definition FUpd := FUpd_aux.(unseal).
  Lemma FUpd_unseal' x A: @fupd _ (FUpd x A) = (FUpd_def x A).
  Proof. rewrite -FUpd_aux.(seal_eq) //. Qed.

  Lemma wsats_inv_gen x A E n N p :
    n < x ->
    ⊢ A ∗ wsats x ∗ OwnE E -∗ #=> (A ∗ (prop n p -∗ wsats x) ∗ OwnE E ∗ (inv n N p)).
  Proof.
    iIntros (LT) "(A & WSAT & EN)".
    iMod (wsats_OwnI_alloc_lt_gen _ _ LT p (fun i => i ∈ ↑N) with "WSAT") as "[I WSAT]".
    - i. des_ifs. apply invariants.fresh_inv_name.
    - iFrame. done.
  Qed.

  (* BiFUpd instance. Due to it depending on x and A, this needs to be given explicitly.
     Most of the time, the `=|x|=(A)={E1,E2}=>` notation does it, but for some typeclasses instances explicit
     annotations may be required.

     The same goes for BiBUpd instance for IUpd, but that does not need to be typed out a lot.
  *)
  Lemma FUpd_fupd_mixin x A : BiFUpdMixin iProp (FUpd x A).
  Proof.
    split.
    - rewrite FUpd_unseal'. solve_proper.
    - intros E1 E2 (E1''&->&?)%subseteq_disjoint_union_L.
      rewrite FUpd_unseal' /FUpd_def OwnE_add //.
      by iIntros "($ & $ & $ & HE) !> ($ & $ & $) !>".
    - rewrite FUpd_unseal' /FUpd_def.
      iIntros (E1 E2 P) ">H [Hw HE]". iApply "H"; by iFrame.
    - rewrite FUpd_unseal' /FUpd_def.
      iIntros (E1 E2 P Q HPQ) "HP HwE". rewrite -HPQ. by iApply "HP".
    - rewrite FUpd_unseal' /FUpd_def. iIntros (E1 E2 E3 P) "HP HwE".
      iMod ("HP" with "HwE") as "(HA & Hw & HE & HP)". iApply "HP"; by iFrame.
    - intros E1 E2 Ef P HE1Ef. rewrite FUpd_unseal' /FUpd_def OwnE_add //.
      iIntros "Hvs (HA & Hw & HE1 &HEf)".
      iMod ("Hvs" with "[HA Hw HE1]") as "($ & $ & HE2 & HP)"; first by iFrame.
      iDestruct (OwnE_add' with "[HE2 HEf]") as "[? $]"; first by iFrame.
      iIntros "!>". by iApply "HP".
    - rewrite FUpd_unseal' /FUpd_def. by iIntros (????) "[HwP $]".
  Qed.
  Global Instance iProp_bi_fupd_FUpd x A : BiFUpd iProp :=
    {| bi_fupd_mixin := (FUpd_fupd_mixin x A) |}.
  Global Instance iProp_bi_BUpd_FUpd x A : @BiBUpdFUpd iProp (uPred_bi_bupd (iResUR Σ)) (iProp_bi_fupd_FUpd x A).
  Proof. rewrite /BiBUpdFUpd FUpd_unseal'. by iIntros (??) ">$ $". Qed.
  Global Instance iProp_bi_IUpd_FUpd x A : @BiBUpdFUpd iProp (iProp_bi_bupd_IUpd A) (iProp_bi_fupd_FUpd x A).
  Proof.
    rewrite /BiBUpdFUpd FUpd_unseal'.
    iIntros (??) "P [A [$ $]]". rewrite IUpd_eq.
    by iMod ("P" with "A") as "[$ $]".
  Qed.

End FANCY_UPDATE.

(** Give explicit [BiFUpd] typeclass instance for [FUpd] since inference fails.
    When editing this, make sure that the notation works correctly. *)
Notation fupd_ex x A :=
  (@fupd (bi_car _) (@bi_fupd_fupd _ (iProp_bi_fupd_FUpd x A))) (only parsing).

Notation "'=|' x '|=(' A ')={' E1 ',' E2 '}=>' P" := (fupd_ex x A E1 E2 P) (at level 90).
Notation "'=|' x '|={' E1 ',' E2 '}=>' P" := (=|x|=( ⌜True⌝%I )={ E1, E2}=> P) (at level 90).
Notation "P =| x |=( A )={ E1 , E2 }=∗ Q" := (P -∗ =|x|=(A)={E1,E2}=> Q)%I (at level 90).
Notation "P =| x |={ E1 , E2 }=∗ Q" := (P -∗ =|x|={E1,E2}=> Q)%I (at level 90).

Notation "'=|' x '|=(' A ')={' E '}=>' P" := (=|x|=( A )={E, E}=> P) (at level 90).
Notation "'=|' x '|={' E '}=>' P" := (=|x|=( ⌜True⌝%I )={ E }=> P) (at level 90).
Notation "P =| x |=( A )={ E }=∗ Q" := (P -∗ =|x|=(A)={E}=> Q)%I (at level 90).
Notation "P =| x |={ E }=∗ Q" := (P -∗ =|x|={E}=> Q)%I (at level 90).

Section LEMMAS.

  Context `{!wsatGS Σ, !invGS Σ Vars, INV : !IInvSet Σ Vars}.
  Notation iProp := (iProp Σ).

  Lemma FUpd_unseal x A E1 E2 P :
    (=|x|=(A)={E1,E2}=> P) ⊣⊢ (A ∗ wsats x ∗ OwnE E1 -∗ #=> (A ∗ wsats x ∗ OwnE E2 ∗ P)).
  Proof. rewrite FUpd_unseal' //. Qed.

  Lemma FUpd_mono x0 x1 A Es1 Es2 P :
    (x0 ≤ x1) -> =|x0|=(A)={Es1,Es2}=> P ⊢ =|x1|=(A)={Es1,Es2}=> P.
  Proof.
    rewrite !FUpd_unseal /FUpd_def.
    iIntros (LE) "FUPD (A & SAT & EN)".
    iPoseProof ((wsats_in _ _ LE) with "SAT") as "[SAT K]".
    iMod ("FUPD" with "[$A $SAT $EN]") as "($ & SAT & $ & $)".
    iModIntro. iApply (wsats_nin with "[$]"). apply LE.
  Qed.

  Lemma FUpd_alloc_gen x A E n N p :
    n < x -> (inv n N p -∗ prop n p) ⊢ =|x|=(A)={E}=> (inv n N p).
  Proof.
    rewrite !FUpd_unseal /FUpd_def.
    iIntros (LT) "P (A & WSAT & EN)".
    iMod (wsats_inv_gen _ A with "[$A $WSAT $EN]") as "($ & W & $ & #$)"; [done|].
    iModIntro. iApply "W". iApply "P". done.
  Qed.

  Lemma FUpd_alloc x A E n N p :
    n < x -> prop n p ⊢ =|x|=(A)={E}=> (inv n N p).
  Proof.
    iIntros (LT) "P". iApply FUpd_alloc_gen; [auto|]. iIntros. iFrame.
  Qed.

  Lemma FUpd_open x A E n N (LT : n < x) (IN : ↑N ⊆ E) p :
    inv n N p ⊢
        =|x|=(A)={E,(E∖↑N)}=>
        ((prop n p) ∗ ((prop n p) -∗ =|x|=(A)={(E∖↑N),E}=> emp)).
  Proof.
    rewrite !FUpd_unseal /FUpd_def.
    iIntros "[% (%iN & #HI)] (A & WSAT & EN)".
    iAssert (OwnE (E ∖ ↑N) ∗ OwnE (↑N ∖ {[i]}) ∗ OwnE {[i]})%I with "[EN]" as "(EN1 & EN2 & EN3)".
    { iApply bi.sep_mono_r. { apply OwnE_disjoint. set_solver. }
      iApply OwnE_disjoint. { set_solver. }
      replace (E ∖ ↑N ∪ (↑N ∖ {[i]} ∪ {[i]})) with E.
      - ss.
      - transitivity ({[i]} ∪ ↑N ∖ {[i]} ∪ E ∖ ↑N).
        + rewrite <- union_difference_singleton_L; ss. eapply union_difference_L; ss.
        + rewrite union_comm_L. f_equal. rewrite union_comm_L. ss.
    }
    iMod (wsats_OwnI_open x n i p LT with "[HI WSAT EN3]") as "(P & WSAT & DIS)".
    { iFrame. auto. }
    iModIntro. iFrame. iIntros "P (A & WSAT & EN1)".
    iMod (wsats_OwnI_close x n i p LT with "[HI WSAT P DIS]") as "(WSAT & EN3)".
    { iFrame. auto. }
    iModIntro. iFrame. iSplitL; [|done].
    (* Frame in this order so that union_difference_singleton_L likes it. *)
    iPoseProof (OwnE_union with "[$EN3 $EN2]") as "EN2".
    rewrite -union_difference_singleton_L //.
    iPoseProof (OwnE_union with "[$EN2 $EN1]") as "ENS".
    rewrite -union_difference_L //.
  Qed.

  Global Instance from_modal_FUpd_general x A E1 E2 P :
    FromModal (E2 ⊆ E1) modality_id P (=|x|=(A)={E1,E2}=> P) P.
  Proof.
    rewrite /FromModal !FUpd_unseal /FUpd_def. ss.
    iIntros (HE) "$ ($ & $ & EN)".
    replace E1 with (E2 ∪ E1 ∖ E2).
    - iDestruct (OwnE_disjoint with "EN") as "[$ _]"; [set_solver|]. done.
    - symmetry. by apply union_difference_L.
  Qed.

  Global Instance elim_modal_FUpd_FUpd_simple p n x A E1 E2 E3 P Q :
    ElimModal (n <= x) p false (=|n|={E1,E2}=> P) P (=|x|=(A)={E1,E3}=> Q) (=|x|=(A)={E2,E3}=> Q).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim.
    iIntros (LE) "[P K]".
    iPoseProof (FUpd_mono n x with "P") as "P"; [done|].
    rewrite !FUpd_unseal /FUpd_def.
    iIntros "[A I]".
    iMod ("P" with "[$I]") as "(_ & WSAT & EN & P)".
    iApply ("K" with "P [$]").
  Qed.

  Global Instance into_acc_FUpd_inv x A E n N p :
    IntoAcc (inv n N p) (n < x /\ (↑N ⊆ E)) True
            (fupd_ex x A E (E ∖ ↑N))
            (fupd_ex x A (E ∖ ↑N) E)
            (fun _ : () => prop n p) (fun _ : () => prop n p) (fun _ : () => None).
  Proof.
    rewrite /IntoAcc /accessor bi.exist_unit.
    iIntros ((?&?)) "#INV _". by iApply FUpd_open.
  Qed.

  Global Instance elim_modal_FUpd_FUpd p n x A E1 E2 E3 P Q :
    ElimModal (n <= x) p false (=|n|=(A)={E1,E2}=> P) P (=|x|=(A)={E1,E3}=> Q) (=|x|=(A)={E2,E3}=> Q).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim.
    iIntros (LE) "[P K]".
    iDestruct (FUpd_mono n x with "P") as "P"; [done|].
    iMod "P". iApply ("K" with "P").
  Qed.

  Global Instance elim_modal_FUpd_FUpd_simple_general p x A E0 E1 E2 E3 P Q :
    ElimModal (E0 ⊆ E2) p false
              (=|x|={E0,E1}=> P)
              P
              (=|x|=(A)={E2,E3}=> Q)
              (=|x|=(A)={(E1 ∪ (E2 ∖ E0)),E3}=> Q) | 10.
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim. ss.
    iIntros (HE) "[M K]".
    iDestruct (fupd_mask_frame_r _ _ (E2 ∖ E0) with "M") as "M".
    { set_solver. }
    replace (E0 ∪ E2 ∖ E0) with E2 by (eapply union_difference_L; ss).
    iMod "M". iApply ("K" with "M").
  Qed.

  Global Instance elim_modal_FUpd_FUpd_general p x A E0 E1 E2 E3 P Q :
    ElimModal (E0 ⊆ E2) p false
              (=|x|=(A)={E0,E1}=> P)
              P
              (=|x|=(A)={E2,E3}=> Q)
              (=|x|=(A)={(E1 ∪ (E2 ∖ E0)),E3}=> Q) | 10.
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim. ss.
    iIntros (HE) "[M K]".
    iDestruct (fupd_mask_frame_r _ _ (E2 ∖ E0) with "M") as "M".
    { set_solver. }
    replace (E0 ∪ E2 ∖ E0) with E2 by (eapply union_difference_L; ss).
    iMod "M". iApply ("K" with "M").
  Qed.

End LEMMAS.

Lemma fupd_soundness `{!wsatGpreS Σ, !invGpreS Σ Vars, !IInvSet Σ Vars} x E1 E2 (P : iProp Σ) `{!Plain P} :
  (∀ `{Hwsat : wsatGS Σ} `{Hinv : invGS Σ Vars}, ⊢ =|x|={E1,E2}=> P) → ⊢ P.
Proof.
  intros Hfupd. apply bupd_soundness; first done.
  iIntros.
  iMod (wsat_alloc x) as (Hw Hi) "(HwA & HwF & HE)".
  iAssert (=|x|={⊤,E2}=> P)%I as "H".
  { iMod (fupd_mask_subseteq E1) as "_"; first done. by iApply (Hfupd Hw Hi). }
  rewrite FUpd_unseal.
  by iMod ("H" with "[$HwF $HE]") as "(_ & _ & _ & $)".
Qed.
