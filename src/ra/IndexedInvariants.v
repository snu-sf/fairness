From sflib Require Import sflib.
From stdpp Require Import coPset gmap namespaces.
From iris Require Import bi.big_op.
From iris.algebra Require Import auth agree coPset gset functions.
From Fairness Require Import PCM IPM IUpd IPropAux.

Local Notation index := nat.

Section INDEXED_INVARIANT_SET.

  Context `{Σ : GRA.t}.
  Notation iProp := (iProp Σ).

  Class IInvSet (Vars : index -> Type) :=
    { prop : forall (i : index), (Vars i) -> iProp }.

  Definition InvSetRA (Vars : index -> Type) (n : index) : ucmra :=
    authUR (positive -d> optionUR (agreeR $ leibnizO (Vars n))).

  Definition IInvSetRA (Vars : index -> Type) : ucmra :=
    discrete_funUR (InvSetRA Vars).

  Definition OwnERA : ucmra := coPset_disjUR.
  Definition OwnDRA : ucmra := gset_disjUR positive.

End INDEXED_INVARIANT_SET.

Section PCM_OWN.

  Context `{Σ : GRA.t}.
  Notation iProp := (iProp Σ).
  Definition OwnE `{GRA.inG OwnERA Σ} (E : coPset) : iProp := OwnM (CoPset E).

  Definition OwnD `{GRA.inG OwnDRA Σ} (D : gset positive) := OwnM (GSet D).

  Definition OwnI_white {Vars} (n : index) (i : positive) (p : Vars n) : IInvSetRA Vars :=
    discrete_fun_singleton n
      (◯ (discrete_fun_singleton i
            (Some $ to_agree (p : leibnizO _)))).

  Definition OwnI {Vars} `{GRA.inG (IInvSetRA Vars) Σ} (n : index) (i : positive) (p : Vars n) :=
    OwnM (OwnI_white n i p).

  Lemma OwnE_exploit `{GRA.inG OwnERA Σ} (E1 E2 : coPset) :
    OwnE E1 ∗ OwnE E2 ⊢ ⌜E1 ## E2⌝.
  Proof.
    iIntros "[H1 H2]".
    by iCombine "H1 H2" gives %WF%coPset_disj_valid_op.
  Qed.

  Lemma OwnE_union `{@GRA.inG OwnERA Σ} (E1 E2 : coPset) :
    OwnE E1 ∗ OwnE E2 ⊢ OwnE (E1 ∪ E2).
  Proof.
    iIntros "H". iDestruct (OwnE_exploit with "H") as %D.
    rewrite -OwnM_op coPset_disj_union //.
  Qed.

  Lemma OwnE_disjoint `{@GRA.inG OwnERA Σ} (E1 E2 : coPset) :
    E1 ## E2 -> OwnE (E1 ∪ E2) ⊢ OwnE E1 ∗ OwnE E2.
  Proof.
    iIntros (D) "H".
    rewrite /OwnE -OwnM_op coPset_disj_union //.
  Qed.

  Lemma OwnE_add `{@GRA.inG OwnERA Σ} (E1 E2 : coPset) :
    E1 ## E2 -> OwnE (E1 ∪ E2) ⊣⊢ OwnE E1 ∗ OwnE E2.
  Proof.
    i. iSplit.
    - iApply OwnE_disjoint. done.
    - iApply OwnE_union.
  Qed.
  Lemma OwnE_is_disjoint `{@GRA.inG OwnERA Σ} E1 E2 : OwnE E1 ∗ OwnE E2 ⊢ ⌜E1 ## E2⌝.
  Proof. apply OwnE_exploit. Qed.
  Lemma OwnE_add' `{@GRA.inG OwnERA Σ} E1 E2 : ⌜E1 ## E2⌝ ∧ OwnE (E1 ∪ E2) ⊣⊢ OwnE E1 ∗ OwnE E2.
  Proof.
    iSplit; [iIntros "[% ?]"; by iApply OwnE_add|].
    iIntros "HE". iDestruct (OwnE_is_disjoint with "HE") as %?.
    iSplit; first done. iApply OwnE_add; by try iFrame.
  Qed.
  Lemma OwnE_singleton_twice `{@GRA.inG OwnERA Σ} i : OwnE {[i]} ∗ OwnE {[i]} ⊢ False.
  Proof. rewrite OwnE_is_disjoint. iIntros (?); set_solver. Qed.

  Lemma OwnE_subset `{@GRA.inG OwnERA Σ} (E1 E2 : coPset) :
    E1 ⊆ E2 -> OwnE E2 ⊢ OwnE E1 ∗ (OwnE E1 -∗ OwnE E2).
  Proof.
    iIntros (SUB) "E".
    rewrite (union_difference_L E1 E2) //.
    iPoseProof (OwnE_disjoint with "E") as "[E1 E2]"; [set_solver|].
    iFrame. iIntros "E1".
    iApply OwnE_union. iFrame.
  Qed.

  Global Instance OwnI_persistent {Vars} `{@GRA.inG (IInvSetRA Vars) Σ}
    n i p : Persistent (OwnI n i p).
  Proof. apply _. Qed.

End PCM_OWN.

Section WORLD_SATISFACTION.

  Context `{Σ : GRA.t}.
  Context `{Vars : index -> Type}.
  Context `{@IInvSet Σ Vars}.
  Context `{@GRA.inG OwnERA Σ}.
  Context `{@GRA.inG OwnDRA Σ}.
  Context `{@GRA.inG (IInvSetRA Vars) Σ}.
  Notation iProp := (iProp Σ).

  Variable n : index.
  Local Notation Var := (Vars n).

  Definition inv_auth_black (I : gmap positive Var) : IInvSetRA Vars :=
    discrete_fun_singleton n
      (● ((λ i, to_agree <$> (I !! i : option (leibnizO _))) : discrete_fun _)).

  Definition inv_auth (I : gmap positive Var) := OwnM (inv_auth_black I).

  Definition inv_satall (I : gmap positive Var) : iProp :=
    [∗ map] i ↦ p ∈ I, (prop n p) ∗ OwnD {[i]} ∨ OwnE {[i]}.

  Definition wsat : iProp := ∃ I, inv_auth I ∗ inv_satall I.


  Lemma alloc_name φ
    (INF : ∀ (E : gset positive), ∃ i, i ∉ E ∧ φ i)
    : ⊢ |==> ∃ i, ⌜φ i⌝ ∧ OwnD {[i]}.
  Proof.
    iDestruct (@OwnM_unit _ OwnDRA) as "H".
    iMod (OwnM_Upd_set with "H") as (?) "[% ?]".
    { apply gset_disj_alloc_empty_updateP_strong', INF. }
    ss. des. subst. by iFrame "∗%".
  Qed.

  Lemma wsat_OwnI_alloc_gen p φ
        (INF : forall (E : gset positive), exists i, i ∉ E /\ φ i)
    : wsat ⊢ |==> (∃ i, ⌜φ i⌝ ∧ OwnI n i p) ∗ (prop n p -∗ wsat).
  Proof.
    iIntros "[% [AUTH SAT]]".

    iMod (alloc_name (λ i, i ∉ dom I ∧ φ i)) as (i [HIi%not_elem_of_dom_1 Hiφ]) "D".
    { by setoid_rewrite (assoc (∧)); setoid_rewrite <- not_elem_of_union. }

    pose (<[i:=p]> I) as I'.

    assert (inv_auth_black I ~~> inv_auth_black I' ⋅ OwnI_white n i p) as UPD.
    { rewrite /I' discrete_fun_singleton_op.
      apply discrete_fun_singleton_update, auth_update_alloc,
        local_update_unital_discrete.
      setoid_rewrite (left_id ε (⋅)).

      intros mz WF <-. split=>i'.
      { by destruct (decide (i' = i)) as [->|NE];
          rewrite ?lookup_insert ?lookup_insert_ne.
      }

      rewrite discrete_fun_lookup_op.
      destruct (decide (i = i')) as [->|]; last first.
      - rewrite discrete_fun_lookup_singleton_ne // lookup_insert_ne
          // left_id //.
      - rewrite discrete_fun_lookup_singleton lookup_insert HIi //.
    }
    unfold inv_auth, inv_satall.
    iMod (OwnM_Upd _ _ UPD with "AUTH") as "[AUTH NEW]". iModIntro.

    iSplit.
    - iExists i. iFrame. ss.
    - iIntros "P". unfold wsat. iExists I'. iFrame.
      rewrite /inv_satall /I'.
      iApply big_sepM_insert; [done|].
      iSplitL "P D"; ss. iLeft. iFrame.
  Qed.

  Lemma wsat_OwnI_alloc p φ
        (INF : forall (E : gset positive), exists i, i ∉ E /\ φ i)
    : wsat ∗ prop n p ⊢ |==> (∃ i, ⌜φ i⌝ ∧ OwnI n i p) ∗ wsat.
  Proof.
    iIntros "[W P]".
    iMod (wsat_OwnI_alloc_gen with "W") as "[I W]". eauto.
    iFrame. iModIntro. iApply "W". iFrame.
  Qed.

  Lemma inv_auth_lookup I i p :
    ✓ (inv_auth_black I ⋅ OwnI_white n i p) → I !! i = Some p.
  Proof.
    rewrite discrete_fun_singleton_op discrete_fun_singleton_valid
        auth_both_valid_discrete.
    intros [Hip%(discrete_fun_included_spec_1 _ _ i) _].
    rewrite discrete_fun_lookup_singleton in Hip.
    destruct (I !! i) eqn: E; simpl in *; clarify.
    - f_equal. rewrite Some_included_total to_agree_included_L // in Hip.
    - by apply Some_included_is_Some, is_Some_None in Hip.
  Qed.

  Lemma wsat_OwnI_open i p :
    OwnI n i p ∗ wsat ∗ OwnE {[i]} ⊢ prop n p ∗ wsat ∗ OwnD {[i]}.
  Proof.
    iIntros "(#I & [% [AUTH SAT]] & EN)".
    iCombine "AUTH I" gives %Hip%inv_auth_lookup. iFrame "AUTH".
    iDestruct (big_sepM_delete with "SAT") as "[[[$ $]|EN'] SAT]"; [exact Hip| |].
    2:{ by iDestruct (OwnE_singleton_twice with "[$EN $EN']") as %[]. }
    by iApply (big_sepM_delete with "[$]").
  Qed.

  Lemma wsat_OwnI_close i p :
    OwnI n i p ∗ wsat ∗ prop n p ∗ OwnD {[i]} ⊢ wsat ∗ OwnE {[i]}.
  Proof.
    iIntros "(#I & [% [AUTH SAT]] & P & DIS)".
    iCombine "AUTH I" gives %Hip%inv_auth_lookup. iFrame "AUTH".
    iDestruct (big_sepM_delete with "SAT") as "[[[_ DIS']|$] SAT]".
    { exact Hip. }
    { iCombine "DIS DIS'" gives %?%gset_disj_valid_op.
      exfalso. set_solver.
    }
    iApply big_sepM_delete; [exact Hip|]. iFrame. iLeft. iFrame.
  Qed.

  Lemma wsat_init :
    OwnM (discrete_fun_singleton n (● ((λ _, None) : discrete_fun _)))
      ⊢ wsat.
  Proof.
    iIntros "H". iExists ∅. iFrame.
    unfold inv_satall. iApply big_sepM_empty. ss.
  Qed.

End WORLD_SATISFACTION.

Section WSATS.

  Context `{Σ : GRA.t}.
  Context `{Vars : index -> Type}.
  Context `{@IInvSet Σ Vars}.
  Context `{@GRA.inG OwnERA Σ}.
  Context `{@GRA.inG OwnDRA Σ}.
  Context `{@GRA.inG (IInvSetRA Vars) Σ}.

  Notation iProp := (iProp Σ).

  Definition wsat_auth_black (x : index) : IInvSetRA Vars :=
    λ n, if (lt_dec n x)
          then ε
          else ● ((λ _, None) : discrete_fun _).

  Definition wsat_auth (x : index) := OwnM (wsat_auth_black x).

  (* wsat n for all n < x *)
  Definition wsats (x : index) := sep_conjs wsat x.

  Definition wsats_l (x : index) : iProp := [∗ list] n ∈ (seq 0 x), wsat n.

  Lemma unfold_wsats x :
    wsats (S x) ⊣⊢ wsats x ∗ wsat x.
  Proof. ss. Qed.

  Lemma eq_wsats_l x :
    wsats_l (S x) ⊣⊢ wsats_l x ∗ wsat x.
  Proof. rewrite /wsats_l seq_S big_sepL_snoc //. Qed.

  Lemma unfold_wsats_l x :
    wsats_l (S x) ⊢ wsats_l x ∗ wsat x.
  Proof. rewrite eq_wsats_l //. Qed.

  Lemma fold_wsats_l x :
    wsats_l x ∗ wsat x ⊢ wsats_l (S x).
  Proof. rewrite eq_wsats_l //. Qed.

  Lemma wsats_equiv_l x :
    wsats x ⊣⊢ wsats_l x.
  Proof.
    iInduction x as [|x] "IH"; iSplit; iIntros "W"; ss.
    - rewrite eq_wsats_l.
      iDestruct (unfold_wsats with "W") as "[WS $]".
      iApply "IH"; auto.
    - iDestruct (unfold_wsats_l with "W") as "[WS $]".
      iApply "IH"; auto.
  Qed.

  Lemma wsats_init_zero :
    OwnM (λ _, ● ((λ _, None) : discrete_fun _))
         ⊢ wsat_auth 0 ∗ wsats 0.
  Proof. iIntros "$". Qed.

  Lemma wsat_auth_nin (x n : index) (NIN : x ≤ n)
    : wsat_auth x ⊢ wsat_auth n ∗ ([∗ list] m ∈ (seq x (n - x)), wsat m).
  Proof.
    induction NIN.
    - rewrite Nat.sub_diag /= right_id //.
    - iIntros "AUTH". iPoseProof (IHNIN with "AUTH") as "[AUTH SAT]".
      clear IHNIN. remember (S m) as y.
      assert (wsat_auth_black m ≡
                wsat_auth_black y
                   ⋅
                   discrete_fun_singleton m (● ((λ _, None) : discrete_fun _))) as Hwsat.
      { subst. intros a. rewrite /wsat_auth_black discrete_fun_lookup_op.
        destruct (decide (a = m)) as [->|];
        rewrite ?discrete_fun_lookup_singleton ?discrete_fun_lookup_singleton_ne //.
        all: des_ifs; try lia.
      }
      rewrite /wsat_auth {}Hwsat. iDestruct "AUTH" as "[$ NEW]".
      iPoseProof (wsat_init with "NEW") as "NEW".
      subst y.
      rewrite Nat.sub_succ_l // seq_S big_sepL_snoc.
      iFrame.
      replace (x + (m - x)) with m by lia. ss.
  Qed.

  Lemma wsats_eq (x n : index) (NIN : x ≤ n)
    : wsats x ∗ ([∗ list] m ∈ (seq x (n - x)), wsat m) ⊣⊢ wsats n.
  Proof.
    rewrite ! wsats_equiv_l /wsats_l -big_sepL_app -seq_app.
    by replace (x + (n - x)) with n by lia.
  Qed.

  Lemma wsats_nin (x n : index) (NIN : x ≤ n)
    : wsats x ∗ ([∗ list] m ∈ (seq x (n - x)), wsat m) ⊢ wsats n.
  Proof. rewrite wsats_eq //. Qed.

  Lemma wsats_in (x0 x1 : index) :
    x0 ≤ x1 -> wsats x1 ⊢ wsats x0 ∗ ([∗ list] n ∈ (seq x0 (x1 - x0)), wsat n).
  Proof. intros. rewrite -wsats_eq //. Qed.

  Lemma wsats_drop_keep (x : index) :
    wsats (S x) ⊢ wsats x ∗ wsat x.
  Proof.
    rewrite (wsats_in x); [|auto].
    rewrite Nat.sub_succ_l // Nat.sub_diag /= right_id //.
  Qed.

  Lemma wsats_allocs x1 x2 :
    x1 ≤ x2 -> wsat_auth x1 ∗ wsats x1 ⊢ (wsat_auth x2 ∗ wsats x2).
  Proof.
    iIntros (LE) "[AUTH SAT]". iPoseProof ((wsat_auth_nin _ _ LE) with "AUTH") as "[$ NEW]".
    iPoseProof ((wsats_nin _ _ LE) with "[$SAT $NEW]") as "$".
  Qed.


  Lemma wsats_OwnI_alloc_lt_gen x n (LT : n < x) p φ
        (INF : forall (E : gset positive), exists i, i ∉ E /\ φ i)
    : wsats x ⊢ |==> (∃ i, ⌜φ i⌝ ∧ OwnI n i p) ∗ (prop n p -∗ wsats x).
  Proof.
    rewrite ! wsats_equiv_l.
    iIntros "SALL".
    iPoseProof (big_sepL_lookup_acc with "SALL") as "[WSAT K]".
    apply lookup_seq_lt; eauto.
    iMod (wsat_OwnI_alloc_gen with "WSAT") as "[$ WSAT]"; [done|].
    iIntros "!> P".
    iApply "K". iApply "WSAT". done.
  Qed.

  Lemma wsats_OwnI_alloc_lt x n (LT : n < x) p φ
        (INF : forall (E : gset positive), exists i, i ∉ E /\ φ i)
    : wsats x ∗ prop n p ⊢ |==> (∃ i, ⌜φ i⌝ ∧ OwnI n i p) ∗ wsats x.
  Proof.
    iIntros "[W P]". iMod (wsats_OwnI_alloc_lt_gen with "W") as "[$ W]". 1,2: eauto.
    iModIntro. iApply "W". iFrame.
  Qed.

  Lemma wsats_OwnI_alloc_ge_gen x n (GE : x <= n) p φ
        (INF : forall (E : gset positive), exists i, i ∉ E /\ φ i)
    : wsat_auth x ∗ wsats x ⊢
                |==> (∃ i, ⌜φ i⌝ ∧ OwnI n i p) ∗ wsat_auth (S n) ∗ (prop n p -∗ wsats (S n)).
  Proof.
    iIntros "(AUTH & WSAT)".
    iPoseProof (wsats_allocs with "[$AUTH $WSAT]") as "[$ WSAT]"; [lia|].
    iMod (wsats_OwnI_alloc_lt_gen with "WSAT") as "[$ $]"; auto.
  Qed.

  Lemma wsats_OwnI_alloc_ge x n (GE : x <= n) p φ
        (INF : forall (E : gset positive), exists i, i ∉ E /\ φ i)
    : wsat_auth x ∗ wsats x ∗ prop n p ⊢ |==> (∃ i, ⌜φ i⌝ ∧ OwnI n i p) ∗ wsat_auth (S n) ∗ wsats (S n).
  Proof.
    iIntros "(A & W & P)".
    iMod (wsats_OwnI_alloc_ge_gen with "[$A $W]") as "($ & $ & W)"; [done..|].
    iModIntro. iApply "W". iFrame.
  Qed.

  Lemma wsat_auth_OwnI_le x n i p :
    OwnI n i p ∗ wsat_auth x ⊢ ⌜n < x⌝.
  Proof.
    iIntros "(#I & AUTH)". iCombine "AUTH I" gives %WF.

    specialize (WF n).
    rewrite /wsat_auth_black /OwnI_white discrete_fun_lookup_op
      discrete_fun_lookup_singleton in WF.
    des_ifs.

    exfalso.
    apply auth_both_valid_discrete in WF as
      [EXTENDS%(discrete_fun_included_spec_1 _ _ i) _].

    rewrite discrete_fun_lookup_singleton in EXTENDS.
    by apply Some_included_is_Some, is_Some_None in EXTENDS.
  Qed.

  Lemma wsats_OwnI_open x n i p :
    n < x -> OwnI n i p ∗ wsats x ∗ OwnE {[i]} ⊢ prop n p ∗ wsats x ∗ OwnD {[i]}.
  Proof.
    rewrite ! wsats_equiv_l.
    iIntros (LT) "(#I & SAT & EN)".
    unfold OwnI, wsats.
    iPoseProof (big_sepL_lookup_acc with "SAT") as "[WSAT K]".
    apply lookup_seq_lt; eauto.
    ss. iDestruct (wsat_OwnI_open with "[$I $WSAT $EN]") as "[$ [WSAT $]]".
    iPoseProof ("K" with "WSAT") as "$".
  Qed.

  Lemma wsats_OwnI_close x n i p :
    n < x -> OwnI n i p ∗ wsats x ∗ prop n p ∗ OwnD {[i]} ⊢ wsats x ∗ OwnE {[i]}.
  Proof.
    rewrite ! wsats_equiv_l.
    iIntros (LT) "(#I & SAT & P & DIS)".
    iPoseProof (big_sepL_lookup_acc with "SAT") as "[WSAT K]".
    apply lookup_seq_lt; eauto.
    iDestruct (wsat_OwnI_close with "[$I $WSAT $P $DIS]") as "[WSAT $]".
    iPoseProof ("K" with "WSAT") as "$".
  Qed.

End WSATS.

From iris Require base_logic.lib.invariants.

Section FANCY_UPDATE.

  Context `{Σ : GRA.t}.
  Context `{Vars : index -> Type}.
  Context `{Invs : @IInvSet Σ Vars}.
  Context `{@GRA.inG OwnERA Σ}.
  Context `{@GRA.inG OwnDRA Σ}.
  Context `{@GRA.inG (IInvSetRA Vars) Σ}.

  Notation iProp := (iProp Σ).

  Definition inv (n : index) (N : namespace) p :=
    (∃ i, ⌜i ∈ (↑N : coPset)⌝ ∧ OwnI n i p)%I.

  Local Definition FUpd_def x (A : iProp) (E1 E2 : coPset) (P : iProp) : iProp :=
    A ∗ wsats x ∗ OwnE E1 -∗ #=> (A ∗ wsats x ∗ OwnE E2 ∗ P).
  Local Definition FUpd_aux : seal (@FUpd_def). Proof. by eexists. Qed.
  Definition FUpd := FUpd_aux.(unseal).
  Lemma FUpd_unseal' x A : @fupd _ (FUpd x A) = (FUpd_def x A).
  Proof. rewrite -FUpd_aux.(seal_eq) //. Qed.

  Lemma wsats_inv_gen x A E n N p :
    n < x ->
    ⊢ A ∗ wsats x ∗ OwnE E -∗ #=> (A ∗ (prop n p -∗ wsats x) ∗ OwnE E ∗ (inv n N p)).
  Proof.
    iIntros (LT) "($ & WSAT & $)".
    iMod (wsats_OwnI_alloc_lt_gen with "WSAT") as "[$ $]"; auto.
    i. apply iris.base_logic.lib.invariants.fresh_inv_name.
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
  Global Instance iProp_bi_BUpd_FUpd x A : @BiBUpdFUpd iProp iProp_bi_bupd (iProp_bi_fupd_FUpd x A).
  Proof. rewrite /BiBUpdFUpd FUpd_unseal'. by iIntros (??) ">$ $". Qed.
  Global Instance iProp_bi_IUpd_FUpd x A : @BiBUpdFUpd iProp (iProp_bi_bupd_IUpd A) (iProp_bi_fupd_FUpd x A).
  Proof.
    rewrite /BiBUpdFUpd FUpd_unseal'.
    iIntros (??) "P [A [$ $]]". rewrite IUpd_eq.
    by iMod ("P" with "A") as "[$ $]".
  Qed.

End FANCY_UPDATE.

(* Give explicit [BiFUpd] typeclass instance for [FUpd] since inference fails. *)
(* Explictly spelling out the coercion [bi_car iProp] ensures the below notations are used. Else it will be ``inserted'' ruining the notation. *)
Notation fupd_ex x A :=
  (@fupd (bi_car (iProp _)) (@bi_fupd_fupd _ (iProp_bi_fupd_FUpd x A))) (only parsing).

Notation "'=|' x '|=(' A ')={' E1 ',' E2 '}=>' P" := (fupd_ex x A E1 E2 P) (at level 90).
Notation "'=|' x '|={' E1 ',' E2 '}=>' P" := (=|x|=( ⌜True⌝%I )={ E1, E2}=> P) (at level 90).
Notation "P =| x |=( A )={ E1 , E2 }=∗ Q" := (P -∗ =|x|=(A)={E1,E2}=> Q)%I (at level 90).
Notation "P =| x |={ E1 , E2 }=∗ Q" := (P -∗ =|x|={E1,E2}=> Q)%I (at level 90).

Notation "'=|' x '|=(' A ')={' E '}=>' P" := (=|x|=( A )={E, E}=> P) (at level 90).
Notation "'=|' x '|={' E '}=>' P" := (=|x|=( ⌜True⌝%I )={ E }=> P) (at level 90).
Notation "P =| x |=( A )={ E }=∗ Q" := (P -∗ =|x|=(A)={E}=> Q)%I (at level 90).
Notation "P =| x |={ E }=∗ Q" := (P -∗ =|x|={E}=> Q)%I (at level 90).

Section LEMMAS.

Context `{Σ : GRA.t}.
Context `{Vars : index -> Type}.
Context `{Invs : IInvSet Σ Vars}.
Context `{GRA.inG OwnERA Σ}.
Context `{GRA.inG OwnDRA Σ}.
Context `{GRA.inG (IInvSetRA Vars) Σ}.

Notation iProp := (iProp Σ).

  Lemma FUpd_unseal x A E1 E2 P :
    (=|x|=(A)={E1,E2}=> P) ⊣⊢ (A ∗ wsats x ∗ OwnE E1 -∗ #=> (A ∗ wsats x ∗ OwnE E2 ∗ P)).
  Proof. rewrite FUpd_unseal' //. Qed.

  Lemma FUpd_mono x0 x1 A Es1 Es2 P :
    (x0 ≤ x1) -> =|x0|=(A)={Es1,Es2}=> P ⊢ =|x1|=(A)={Es1,Es2}=> P.
  Proof.
    rewrite !FUpd_unseal.
    iIntros (LE) "FUPD (A & SAT & EN)".
    iPoseProof ((wsats_in _ _ LE) with "SAT") as "[SAT K]".
    iMod ("FUPD" with "[$A $SAT $EN]") as "($ & SAT & $ & $)".
    iModIntro. iApply wsats_nin; [exact LE|]. iFrame.
  Qed.

  Lemma FUpd_alloc_gen x A E n N p :
    n < x -> (inv n N p -∗ prop n p) ⊢ =|x|=(A)={E}=> (inv n N p).
  Proof.
    rewrite !FUpd_unseal.
    iIntros (LT) "P (A & WSAT & EN)".
    iMod (wsats_inv_gen _ A with "[$A $WSAT $EN]") as "($ & W & $ & #$)"; [done|].
    iModIntro. iApply "W". iApply "P". done.
  Qed.

  Lemma FUpd_alloc x A E n N p :
    n < x -> prop n p ⊢ =|x|=(A)={E}=> (inv n N p).
  Proof.
    iIntros (LT) "P". iApply FUpd_alloc_gen. auto. iIntros. iFrame.
  Qed.

  Lemma FUpd_open x A E n N (LT : n < x) (IN : ↑N ⊆ E) p :
    inv n N p ⊢
        =|x|=(A)={E,(E∖↑N)}=>
        (prop n p ∗ (prop n p -∗ =|x|=(A)={(E∖↑N),E}=> emp)).
  Proof.
    rewrite !FUpd_unseal.
    iIntros "[% (%iN & #HI)] ($ & WSAT & EN)".
    iAssert (OwnE (E ∖ ↑N) ∗ OwnE {[i]} ∗ OwnE (↑N ∖ {[i]}))%I with "[EN]" as "($ & EN3 & EN2)".
    { rewrite -!OwnE_disjoint; [|set_solver..].
      rewrite -union_difference_singleton_L //
        union_comm_L -union_difference_L //.
    }
    iDestruct (wsats_OwnI_open x n i p LT with "[$HI $WSAT $EN3]") as "($ & $ & DIS)".
    iIntros "!> P ($ & WSAT & EN1)".
    iDestruct (wsats_OwnI_close x n i p LT with "[$HI $WSAT $P $DIS]") as "($ & EN3)".
    iPoseProof (OwnE_union with "[$EN3 $EN2]") as "EN2".
    iPoseProof (OwnE_union with "[$EN2 $EN1]") as "EN".
    rewrite right_id -union_difference_singleton_L //
      -union_difference_L //.
  Qed.

  Global Instance from_modal_FUpd_general x A E1 E2 P :
    FromModal (E2 ⊆ E1) modality_id P (=|x|=(A)={E1,E2}=> P) P.
  Proof. apply: fupd_mask_intro_discard. Qed.

  Global Instance elim_modal_FUpd_FUpd_simple p n x A E1 E2 E3 P Q :
    ElimModal (n ≤ x) p false (=|n|={E1,E2}=> P) P (=|x|=(A)={E1,E3}=> Q) (=|x|=(A)={E2,E3}=> Q).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim /= => ?.
    rewrite (FUpd_mono n x) // !FUpd_unseal !left_id.
    iIntros "[P K] [A I]".
    iMod ("P" with "[$I]") as "(WSAT & EN & P)".
    iApply ("K" with "P [$]").
  Qed.

  Global Instance into_acc_FUpd_inv x A E n N p :
    IntoAcc (X := unit) (inv n N p) (n < x ∧ (↑N ⊆ E)) True
            (fupd_ex x A E (E ∖ ↑N))
            (fupd_ex x A (E ∖ ↑N) E)
            (λ _, prop n p) (λ _, prop n p) (λ _, None).
  Proof.
    rewrite /IntoAcc /accessor bi.exist_unit.
    iIntros ([? ?]) "#INV _". by iApply FUpd_open.
  Qed.

  Global Instance elim_modal_FUpd_FUpd p n x A E1 E2 E3 P Q :
    ElimModal (n ≤ x) p false (=|n|=(A)={E1,E2}=> P) P (=|x|=(A)={E1,E3}=> Q) (=|x|=(A)={E2,E3}=> Q).
  Proof. intros ?. rewrite (FUpd_mono n x) //. by apply: elim_modal. Qed.

  Global Instance elim_modal_FUpd_FUpd_simple_general p x A E0 E1 E2 E3 P Q :
    ElimModal (E0 ⊆ E2) p false
              (=|x|={E0,E1}=> P)
              P
              (=|x|=(A)={E2,E3}=> Q)
              (=|x|=(A)={(E1 ∪ (E2 ∖ E0)),E3}=> Q) | 10.
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim /=.
    iIntros (HE) "[M K]".
    iApply fupd_mask_frame; [exact HE|].
    iMod "M". iApply ("K" with "M").
  Qed.

  Global Instance elim_modal_FUpd_FUpd_general p x A E0 E1 E2 E3 P Q :
    ElimModal (E0 ⊆ E2) p false
              (=|x|=(A)={E0,E1}=> P)
              P
              (=|x|=(A)={E2,E3}=> Q)
              (=|x|=(A)={(E1 ∪ (E2 ∖ E0)),E3}=> Q) | 10.
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim /=.
    iIntros (HE) "[M K]".
    iApply fupd_mask_frame; [exact HE|].
    iMod "M". iApply ("K" with "M").
  Qed.

End LEMMAS.
