From sflib Require Import sflib.
From Fairness Require Import Any PCM IProp IPM IPropAux.
From Fairness Require Import TemporalLogic.


Module AuthExcls.

  Definition t (A : Type) : URA.t := (nat ==> (Auth.t (Excl.t A)))%ra.

  Section RA.

    Context `{Σ : GRA.t}.
    (* Map from nat to Auth Excl A. *)
    Context `{AuthExclAnys : @GRA.inG (t A) Σ}.

    Definition black_ra (r : nat) a : t A :=
      (maps_to_res r (Auth.black ((Some a) : Excl.t A))).
    Definition white_ra (r : nat) a : t A :=
      (maps_to_res r (Auth.white ((Some a) : Excl.t A))).

    Definition black (r : nat) a : iProp := OwnM (black_ra r a).
    Definition white (r : nat) a : iProp := OwnM (white_ra r a).

    Definition rest_ra {D : nat -> Prop} (DEC : forall i, Decision (D i)) a :=
      ((fun k => if (DEC k)
              then ε
              else (Auth.black (Some a : Excl.t A) ⋅ Auth.white (Some a : Excl.t A)))
        : t A).

    Definition rest {D : nat -> Prop} (DEC : forall i, Decision (D i)) a : iProp :=
      OwnM (rest_ra DEC a).

    (** Properties. *)

    Lemma b_w_eq r (b w : A) :
      ⊢ black r b -∗ white r w -∗ ⌜b = w⌝.
    Proof.
      iIntros "B W". iCombine "B W" as "BW". iPoseProof (OwnM_valid with "BW") as "%WF".
      iPureIntro. unfold black_ra, white_ra in WF. setoid_rewrite maps_to_res_add in WF.
      unfold maps_to_res in WF. ur in WF. specialize (WF r). des_ifs. rewrite URA.unit_idl in WF.
      ur in WF. des. unfold URA.extends in WF. des. ur in WF. des_ifs.
    Qed.

    Lemma b_b_false r (t1 t2 : A) :
      ⊢ black r t1 -∗ black r t2 -∗ False.
    Proof.
      iIntros "A B". iCombine "A B" as "C". iPoseProof (OwnM_valid with "C") as "%WF".
      iPureIntro. unfold black_ra, white_ra in WF. setoid_rewrite maps_to_res_add in WF.
      unfold maps_to_res in WF. ur in WF. specialize (WF r). des_ifs. ur in WF. auto.
    Qed.

    Lemma w_w_false r (t1 t2 : A) :
      ⊢ white r t1 -∗ white r t2 -∗ False.
    Proof.
      iIntros "A B". iCombine "A B" as "C". iPoseProof (OwnM_valid with "C") as "%WF".
      iPureIntro. unfold black_ra, white_ra in WF. setoid_rewrite maps_to_res_add in WF.
      unfold maps_to_res in WF. ur in WF. specialize (WF r). des_ifs. ur in WF. ur in WF. auto.
    Qed.

    Lemma b_w_update r (t1 t2 s : A) :
      ⊢ black r t1 -∗ white r t2 ==∗ (black r s ∗ white r s).
    Proof.
      iIntros "B W".
      assert (URA.updatable (black_ra r t1 ⋅ white_ra r t2)
                            (black_ra r s ⋅ white_ra r s)).
      { unfold black_ra, white_ra. setoid_rewrite maps_to_res_add. apply maps_to_updatable, Auth.auth_update.
        ii. des. split.
        - ur. ss.
        - ur in FRAME. ur. des_ifs.
      }
      iCombine "B W" as "BW". iMod (OwnM_Upd with "BW") as "BW". eauto.
      iDestruct "BW" as "[B W]". iModIntro. iFrame.
    Qed.

    Lemma alloc_gen
          {D1 D2 : nat -> Prop}
          (DEC1 : forall a, Decision (D1 a))
          (DEC2 : forall a, Decision (D2 a))
          (SUB : forall n, match DEC1 n, DEC2 n with
                      | left _, right _ => False
                      | _, _ => True
                      end)
          a
      :
      ⊢ (rest DEC1 a) -∗
        |==> ((rest DEC2 a)
                ∗ (OwnM ((fun k => if (DEC1 k)
                                then ε
                                else if (DEC2 k)
                                     then (Auth.black (Some a : Excl.t A) ⋅ Auth.white (Some a : Excl.t A))
                                     else ε
                         ) : t A))).
    Proof.
      iIntros "A".
      assert (URA.updatable
                ((λ k : nat, if DEC1 k
                           then ε
                           else(Auth.black (Some a : Excl.t A) ⋅ Auth.white (Some a : Excl.t A))) : t A)
                (((λ k : nat, if DEC2 k
                            then ε
                            else(Auth.black (Some a : Excl.t A) ⋅ Auth.white (Some a : Excl.t A))) : t A)
                   ⋅
                   ((fun k => if (DEC1 k)
                           then ε
                           else if (DEC2 k)
                                then (Auth.black (Some a : Excl.t A) ⋅ Auth.white (Some a : Excl.t A))
                                else ε
                    ) : t A))).
      { setoid_rewrite unfold_pointwise_add. apply pointwise_updatable. i. specialize (SUB a0). des_ifs.
        - rewrite URA.unit_id. reflexivity.
        - rewrite URA.unit_idl. reflexivity.
        - rewrite URA.unit_id. reflexivity.
      }
      iMod (OwnM_Upd with "A") as "[A B]". eauto.
      iModIntro. iFrame.
    Qed.

    Lemma alloc_one
          {D1 D2 : nat -> Prop}
          (DEC1 : forall a, Decision (D1 a))
          (DEC2 : forall a, Decision (D2 a))
          a0 a
          (ONE : exists m, forall n,
              (n <> m -> match DEC1 n, DEC2 n with | left _, left _ | right _, right _ => True | _, _ => False end)
              /\ (match DEC1 m, DEC2 m with | right _, left _ => True | _, _ => False end))
      :
      ⊢ (rest DEC1 a0) -∗ |==> ((rest DEC2 a0) ∗ ∃ r, black r a ∗ white r a).
    Proof.
      iIntros "A". des.
      iMod (alloc_gen with "A") as "[A G]".
      2:{ iFrame. assert (
            ((λ k : nat,
                 if DEC1 k then ε else if DEC2 k then Auth.black (Some a0 : Excl.t A) ⋅ Auth.white (Some a0 : Excl.t A) else ε) : t A)
            =
              (black_ra m a0 ⋅ white_ra m a0)).
          { unfold black_ra, white_ra. setoid_rewrite maps_to_res_add. unfold maps_to_res. extensionalities k.
            specialize (ONE k). des. des_ifs.
          }
          rewrite H. iDestruct "G" as "[B W]". iExists m. iMod (b_w_update with "B W") as "BW". iModIntro. iFrame.
      }
      i. specialize (ONE n). des. des_ifs. apply ONE. intros EQ. subst. clarify.
    Qed.

    Definition rest_gt a : iProp := (∃ U, rest (gt_dec U) a).

    Lemma alloc_gt a0 a :
      ⊢ rest_gt a0 -∗ |==> (rest_gt a0 ∗ ∃ r, black r a ∗ white r a).
    Proof.
      iIntros "[%U A]".
      iMod (alloc_one (gt_dec U) (gt_dec (S U)) with "A") as "(A & RES)".
      2:{ iModIntro. iSplitL "A". iExists _. iFrame. iFrame. }
      exists U. i. split.
      { i. des_ifs; try lia. }
      { des_ifs; try lia. }
    Qed.

  End RA.

End AuthExcls.

Module SAuthExcls.

  Section SPROP.

    Context {STT : StateTypes}.
    Context `{sub : @SRA.subG Γ Σ}.
    Context {TLRASs : TLRAs_small STT Γ}.
    Context {TLRAS : TLRAs STT Γ Σ}.

    Context `{HasAuthExcls : @GRA.inG (AuthExcls.t A) Γ}.

    Import AuthExcls.

    Definition s_black {n} (r : nat) a : sProp n := (➢(black_ra r a))%S.

    Lemma red_s_black n r a :
      ⟦s_black r a, n⟧ = black r a.
    Proof.
      unfold s_black. red_tl. ss.
    Qed.

    Definition s_white {n} (r : nat) a : sProp n := (➢(white_ra r a))%S.

    Lemma red_s_white n r a :
      ⟦s_white r a, n⟧ = white r a.
    Proof.
      unfold s_white. red_tl. ss.
    Qed.

    Definition s_rest {n} {D : nat -> Prop} (DEC : forall i, Decision (D i)) a : sProp n :=
      (➢ (rest_ra DEC a))%S.

    Lemma red_s_rest n D (DEC : forall i, Decision (D i)) a :
      ⟦s_rest DEC a, n⟧ = rest DEC a.
    Proof.
      unfold s_rest. red_tl. ss.
    Qed.

  End SPROP.

End SAuthExcls.

Ltac red_tl_authexcls := (try rewrite ! @SAuthExcls.red_s_black;
                          try rewrite ! @SAuthExcls.red_s_white;
                          try rewrite ! @SAuthExcls.red_s_rest
                         ).

Notation "'●' γ a" := (AuthExcls.black γ a) (at level 90, γ, a at level 1) : bi_scope.
Notation "'●' γ a" := (SAuthExcls.s_black γ a) (at level 90, γ, a at level 1) : sProp_scope.
Notation "'○' γ a" := (AuthExcls.white γ a) (at level 90, γ, a at level 1) : bi_scope.
Notation "'○' γ a" := (SAuthExcls.s_white γ a) (at level 90, γ, a at level 1) : sProp_scope.
