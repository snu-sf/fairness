From stdpp Require Import coPset gmap.
From sflib Require Import sflib.
From Fairness Require Import PCM IProp IPM.
From iris Require Import bi.big_op.

Section INTERPRETATION.

  Class Interp `(Σ : GRA.t) :=
    { Var : Type
    ; prop : Var -> iProp
    }.

End INTERPRETATION.

Section PCM_OWN.

  Context `{Σ : GRA.t}.

  Definition OwnE `{@GRA.inG CoPset.t Σ} (E : coPset) := OwnM (Some E).
  Definition OwnD `{@GRA.inG Gset.t Σ} (D : gset positive) := OwnM (Some D).
  Definition inv `{Interp} `{@GRA.inG (Auth.t (positive ==> URA.agree Var)%ra) Σ}
    (i : positive) (x : Var) :=
    OwnM (Auth.white (@maps_to_res positive (URA.agree Var) i (Some (Some x)))).

  Lemma OwnE_disjoint `{@GRA.inG CoPset.t Σ} (E1 E2 : coPset) :
    E1 ## E2 -> OwnE (E1 ∪ E2) ⊣⊢ OwnE E1 ∗ OwnE E2.
  Proof.
    i. unfold OwnE. iSplit.
    - iApply into_sep. eapply into_sep_ownM.
      unfold IsOp, URA.add. unseal "ra". ss. des_ifs.
    - iApply from_sep. eapply from_sep_ownM.
      unfold IsOp, URA.add. unseal "ra". ss. des_ifs.
  Qed.

  Lemma OwnE_not_disjoint `{@GRA.inG CoPset.t Σ} (E1 E2 : coPset) :
    ¬ E1 ## E2 -> OwnE E1 ∗ OwnE E2 ⊢ False.
  Proof.
    i. iIntros "H". iAssert (OwnM (None : CoPset.t)) with "[H]" as "H".
    - iRevert "H". iApply from_sep. eapply from_sep_ownM.
      unfold IsOp. unfold URA.add. unseal "ra". ss. des_ifs.
    - iPoseProof (OwnM_valid with "H") as "H".
      iRevert "H". iPureIntro. unfold URA.wf. unseal "ra". ss.
  Qed.

  Global Instance inv_persistent `{Interp} `{@GRA.inG (Auth.t (positive ==> URA.agree Var)%ra) Σ}
    i p : Persistent (inv i p).
  Admitted.

End PCM_OWN.

Section WORLD_SATISFACTION.

  Context `{Σ : GRA.t}.
  Context `{@Interp Σ}.
  Context `{@GRA.inG CoPset.t Σ}.
  Context `{@GRA.inG Gset.t Σ}.
  Context `{@GRA.inG (Auth.t (positive ==> URA.agree Var)%ra) Σ}.

  Definition inv_auth (I : gmap positive Var) :=
    OwnM (@Auth.black
            (positive ==> URA.agree Var)%ra
            (fun (i : positive) => Some <$> (I !! i))).

  Definition inv_satall (I : gmap positive Var) :=
    ([∗ map] i ↦ p ∈ I, prop p ∗ OwnD {[i]} ∨ OwnE {[i]})%I.

  Definition wsat : iProp := (∃ I, inv_auth I ∗ inv_satall I)%I.

  Lemma wsat_inv_alloc p :
    wsat ∗ prop p ⊢ |==> ∃ i, inv i p ∗ wsat.
  Admitted.

  Lemma wsat_inv_open i p :
    inv i p ∗ wsat ∗ OwnE {[i]} ⊢ |==> prop p ∗ wsat ∗ OwnD {[i]}.
  Proof.
    iIntros "(I & [% [AUTH SAT]] & EN)".
    unfold inv, inv_auth, inv_satall.
    Search Auth.white.
    Search OwnM.
  Admitted.

  Lemma wsat_inv_close i p :
    inv i p ∗ wsat ∗ prop p ∗ OwnD {[i]} ⊢ |==> wsat ∗ OwnE {[i]}.
  Admitted.

End WORLD_SATISFACTION.

Section FANCY_UPDATE.

  Context `{Σ : GRA.t}.
  Context `{@Interp Σ}.
  Context `{@GRA.inG CoPset.t Σ}.
  Context `{@GRA.inG Gset.t Σ}.
  Context `{@GRA.inG (Auth.t (positive ==> URA.agree Var)%ra) Σ}.

  Definition FUpd (E1 E2 : coPset) (P : iProp) : iProp :=
    wsat ∗ OwnE E1 -∗ #=> (wsat ∗ OwnE E2 ∗ P).

  Lemma FUpd_open E i p (IN : i ∈ E) :
    inv i p ⊢ FUpd E (E∖{[i]}) (prop p ∗ (prop p -∗ FUpd (E∖{[i]}) E True)).
  Proof.
    iIntros "#H [WSAT EN]".
    iAssert (OwnE (E ∖ {[i]}) ∗ OwnE {[i]})%I with "[EN]" as "[EN1 EN2]".
    { iApply OwnE_disjoint. { set_solver. }
      iRevert "EN". replace E with ((E ∖ {[i]}) ∪ {[i]}) at 1. eauto.
      eapply leibniz_equiv. symmetry. transitivity ({[i]} ∪ E ∖ {[i]}).
      - apply union_difference; set_solver.
      - eapply union_comm.
    }
    iMod (wsat_inv_open i p with "[H WSAT EN2]") as "(P & WSAT & DIS)". { iFrame. iApply "H". }
    iModIntro. iFrame. iIntros "P [WSAT EN1]".
    iMod (wsat_inv_close i p with "[H WSAT P  DIS]") as "(WSAT & EN2)". { iFrame. iApply "H". }
    iModIntro. iFrame. iSplit; eauto.
    iAssert (OwnE (E∖{[i]} ∪ {[i]}))%I with "[EN1 EN2]" as "EN".
    { iApply OwnE_disjoint. set_solver. iFrame. }
    replace (E ∖ {[i]} ∪ {[i]}) with E. eauto.
    eapply leibniz_equiv. transitivity ({[i]} ∪ E ∖ {[i]}).
    - apply union_difference; set_solver.
    - eapply union_comm.
  Qed.

End FANCY_UPDATE.
