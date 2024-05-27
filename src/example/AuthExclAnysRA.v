From sflib Require Import sflib.
From Fairness Require Import Any PCM IProp IPM IPropAux.


Section AEAPROP.

  Definition AuthExclAnysRA : URA.t := (nat ==> (Auth.t (Excl.t Any.t)))%ra.

  Context `{Σ : GRA.t}.
  (* Map from nat to Auth Excl Any. *)
  Context {AuthExclAnys : @GRA.inG AuthExclAnysRA Σ}.

  Definition AuExAnyB_ra (r : nat) {T : Type} (t : T) : AuthExclAnysRA :=
    ((maps_to_res r (Auth.black ((Some (t ↑)) : Excl.t Any.t))) : AuthExclAnysRA).
  Definition AuExAnyW_ra (r : nat) {T : Type} (t : T) : AuthExclAnysRA :=
    ((maps_to_res r (Auth.white ((Some (t ↑)) : Excl.t Any.t))) : AuthExclAnysRA).

  Definition AuExAnyB (r : nat) {T : Type} (t : T) : iProp := OwnM (AuExAnyB_ra r t).
  Definition AuExAnyW (r : nat) {T : Type} (t : T) : iProp := OwnM (AuExAnyW_ra r t).

  Definition AuExAny : iProp :=
    (∃ (U : nat), OwnM ((fun k => if (lt_dec k U)
                             then ε
                             else (Auth.black (Some (tt ↑) : Excl.t Any.t) ⋅ Auth.white (Some (tt ↑) : Excl.t Any.t)))
                       : AuthExclAnysRA)).

  (** Properties. *)

  Lemma auexa_b_w_eq r T (tb tw : T) :
    ⊢ AuExAnyB r tb -∗ AuExAnyW r tw -∗ ⌜tb = tw⌝.
  Proof.
    iIntros "B W". iCombine "B W" as "BW". iPoseProof (OwnM_valid with "BW") as "%WF".
    iPureIntro. unfold AuExAnyB_ra, AuExAnyW_ra in WF. setoid_rewrite maps_to_res_add in WF.
    unfold maps_to_res in WF. ur in WF. specialize (WF r). des_ifs. rewrite URA.unit_idl in WF.
    ur in WF. des. unfold URA.extends in WF. des. ur in WF. des_ifs.
    apply Any.upcast_inj in H0. des. rewrite EQ0. auto.
  Qed.

  Lemma auexa_b_b_false r T (t1 t2 : T) :
    ⊢ AuExAnyB r t1 -∗ AuExAnyB r t2 -∗ False.
  Proof.
    iIntros "A B". iCombine "A B" as "C". iPoseProof (OwnM_valid with "C") as "%WF".
    iPureIntro. unfold AuExAnyB_ra, AuExAnyW_ra in WF. setoid_rewrite maps_to_res_add in WF.
    unfold maps_to_res in WF. ur in WF. specialize (WF r). des_ifs. ur in WF. auto.
  Qed.

  Lemma auexa_w_w_false r T (t1 t2 : T) :
    ⊢ AuExAnyW r t1 -∗ AuExAnyW r t2 -∗ False.
  Proof.
    iIntros "A B". iCombine "A B" as "C". iPoseProof (OwnM_valid with "C") as "%WF".
    iPureIntro. unfold AuExAnyB_ra, AuExAnyW_ra in WF. setoid_rewrite maps_to_res_add in WF.
    unfold maps_to_res in WF. ur in WF. specialize (WF r). des_ifs. ur in WF. ur in WF. auto.
  Qed.

  Lemma auexa_b_w_update r T (t1 t2 : T) S (s : S) :
    ⊢ AuExAnyB r t1 -∗ AuExAnyW r t2 ==∗ (AuExAnyB r s ∗ AuExAnyW r s).
  Proof.
    iIntros "B W".
    assert (URA.updatable (AuExAnyB_ra r t1 ⋅ AuExAnyW_ra r t2)
                          (AuExAnyB_ra r s ⋅ AuExAnyW_ra r s)).
    { unfold AuExAnyB_ra, AuExAnyW_ra. setoid_rewrite maps_to_res_add. apply maps_to_updatable, Auth.auth_update.
      ii. des. split.
      - ur. ss.
      - ur in FRAME. ur. des_ifs.
    }
    iCombine "B W" as "BW". iMod (OwnM_Upd with "BW") as "BW". eauto.
    iDestruct "BW" as "[B W]". iModIntro. iFrame.
  Qed.

  Lemma auexa_alloc T (t : T) :
    ⊢ AuExAny -∗ |==> (AuExAny ∗ ∃ r, AuExAnyB r t ∗ AuExAnyW r t).
  Proof.
    iIntros "[%U A]".
    assert (URA.updatable
              ((λ k : nat, if lt_dec k U
                         then ε
                         else(Auth.black (Some (tt ↑) : Excl.t Any.t) ⋅ Auth.white (Some (tt ↑) : Excl.t Any.t))) : AuthExclAnysRA)
              (((λ k : nat, if lt_dec k (S U)
                          then ε
                          else(Auth.black (Some (tt ↑) : Excl.t Any.t) ⋅ Auth.white (Some (tt ↑) : Excl.t Any.t))) : AuthExclAnysRA)
                 ⋅
                 (AuExAnyB_ra U tt ⋅ AuExAnyW_ra U tt))).
    { unfold AuExAnyB_ra, AuExAnyW_ra. setoid_rewrite maps_to_res_add. unfold maps_to_res. setoid_rewrite unfold_pointwise_add.
      apply pointwise_updatable. i. des_ifs; try lia.
      - rewrite URA.unit_id. reflexivity.
      - rewrite URA.unit_idl. reflexivity.
      - rewrite URA.unit_id. reflexivity.
    }
    iMod (OwnM_Upd with "A") as "[A [B W]]". eauto.
    iMod (auexa_b_w_update with "B W") as "BW".
    iModIntro. iSplitL "A".
    - iExists (S U). iFrame.
    - iExists U. iFrame.
  Qed.

End AEAPROP.
