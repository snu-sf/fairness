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

  Definition AuExAny_ra {D : nat -> Prop} (DEC : forall a, Decision (D a)) :=
    ((fun k => if (DEC k)
            then ε
            else (Auth.black (Some (tt ↑) : Excl.t Any.t) ⋅ Auth.white (Some (tt ↑) : Excl.t Any.t)))
      : AuthExclAnysRA).

  Definition AuExAny {D : nat -> Prop} (DEC : forall a, Decision (D a)) : iProp :=
    OwnM (AuExAny_ra DEC).

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

  Lemma auexa_alloc_gen
        {D1 D2 : nat -> Prop}
        (DEC1 : forall a, Decision (D1 a))
        (DEC2 : forall a, Decision (D2 a))
        (SUB : forall n, match DEC1 n, DEC2 n with
                    | left _, right _ => False
                    | _, _ => True
                    end)
    :
    ⊢ (AuExAny DEC1) -∗
      |==> ((AuExAny DEC2)
              ∗ (OwnM ((fun k => if (DEC1 k)
                              then ε
                              else if (DEC2 k)
                                   then (Auth.black (Some (tt ↑) : Excl.t Any.t) ⋅ Auth.white (Some (tt ↑) : Excl.t Any.t))
                                   else ε
                       ) : AuthExclAnysRA))).
  Proof.
    iIntros "A".
    assert (URA.updatable
              ((λ k : nat, if DEC1 k
                         then ε
                         else(Auth.black (Some (tt ↑) : Excl.t Any.t) ⋅ Auth.white (Some (tt ↑) : Excl.t Any.t))) : AuthExclAnysRA)
              (((λ k : nat, if DEC2 k
                          then ε
                          else(Auth.black (Some (tt ↑) : Excl.t Any.t) ⋅ Auth.white (Some (tt ↑) : Excl.t Any.t))) : AuthExclAnysRA)
                 ⋅
                 ((fun k => if (DEC1 k)
                         then ε
                         else if (DEC2 k)
                              then (Auth.black (Some (tt ↑) : Excl.t Any.t) ⋅ Auth.white (Some (tt ↑) : Excl.t Any.t))
                              else ε
                  ) : AuthExclAnysRA))).
    { setoid_rewrite unfold_pointwise_add. apply pointwise_updatable. i. specialize (SUB a). des_ifs.
      - rewrite URA.unit_id. reflexivity.
      - rewrite URA.unit_idl. reflexivity.
      - rewrite URA.unit_id. reflexivity.
    }
    iMod (OwnM_Upd with "A") as "[A B]". eauto.
    iModIntro. iFrame.
  Qed.

  Lemma auexa_alloc_one
        {D1 D2 : nat -> Prop}
        (DEC1 : forall a, Decision (D1 a))
        (DEC2 : forall a, Decision (D2 a))
        T (t : T)
        (ONE : exists m, forall n,
            (n <> m -> match DEC1 n, DEC2 n with | left _, left _ | right _, right _ => True | _, _ => False end)
            /\ (match DEC1 m, DEC2 m with | right _, left _ => True | _, _ => False end))
    :
    ⊢ (AuExAny DEC1) -∗ |==> ((AuExAny DEC2) ∗ ∃ r, AuExAnyB r t ∗ AuExAnyW r t).
  Proof.
    iIntros "A". des.
    iMod (auexa_alloc_gen with "A") as "[A G]".
    2:{ iFrame. assert (
          ((λ k : nat,
               if DEC1 k then ε else if DEC2 k then Auth.black (Some (tt↑) : Excl.t Any.t) ⋅ Auth.white (Some (tt↑) : Excl.t Any.t) else ε) : AuthExclAnysRA)
          =
            (AuExAnyB_ra m tt ⋅ AuExAnyW_ra m tt)).
        { unfold AuExAnyB_ra, AuExAnyW_ra. setoid_rewrite maps_to_res_add. unfold maps_to_res. extensionalities k.
          specialize (ONE k). des. des_ifs.
        }
        rewrite H. iDestruct "G" as "[B W]". iExists m. iMod (auexa_b_w_update with "B W") as "BW". iModIntro. iFrame.
    }
    i. specialize (ONE n). des. des_ifs. apply ONE. intros EQ. subst. clarify.
  Qed.

  Definition AuExAny_gt : iProp := (∃ U, AuExAny (gt_dec U)).

  Lemma auexa_alloc_gt T (t : T) :
    ⊢ AuExAny_gt -∗ |==> (AuExAny_gt ∗ ∃ r, AuExAnyB r t ∗ AuExAnyW r t).
  Proof.
    iIntros "[%U A]".
    iMod (auexa_alloc_one (gt_dec U) (gt_dec (S U)) with "A") as "(A & RES)".
    2:{ iModIntro. iSplitL "A". iExists _. iFrame. iFrame. }
    exists U. i. split.
    { i. des_ifs; try lia. }
    { des_ifs; try lia. }
  Qed.

End AEAPROP.
