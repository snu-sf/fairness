From iris.algebra Require Import cmra updates lib.excl_auth.
From sflib Require Import sflib.
From Fairness Require Import Any PCM IPM IPropAux.
From Fairness Require Import TemporalLogic AuthExclsRA.


Section AEAPROP.

  Definition AuthExclAnysRA : ucmra := AuthExcls.t Any.t.

  Context `{Σ : GRA.t}.
  Notation iProp := (iProp Σ) (only parsing).
  (* Map from nat to Auth Excl Any. *)
  Context {AuthExclAnys : @GRA.inG AuthExclAnysRA Σ}.

  Definition AuExAnyB_ra (r : nat) {T : Type} (t : T) : AuthExclAnysRA :=
    AuthExcls.black_ra r (t ↑ :Any.t).
  Definition AuExAnyW_ra (r : nat) {T : Type} (t : T) : AuthExclAnysRA :=
    AuthExcls.white_ra r (t ↑ :Any.t).
  Definition AuExAnyB (r : nat) {T : Type} (t : T) : iProp :=
    ●G r (t ↑ :Any.t).
  Definition AuExAnyW (r : nat) {T : Type} (t : T) : iProp :=
    ○G r (t ↑ :Any.t).

  Definition AuExAny_ra {D : nat -> Prop} (DEC : forall a, Decision (D a)) : AuthExclAnysRA :=
    AuthExcls.rest_ra DEC (tt ↑ : Any.t).
  Definition AuExAny {D : nat -> Prop} (DEC : forall a, Decision (D a)) : iProp :=
    AuthExcls.rest DEC (tt ↑ : Any.t).


  (** Properties. *)

  Lemma auexa_b_w_eq r T (tb tw : T) :
    ⊢ AuExAnyB r tb -∗ AuExAnyW r tw -∗ ⌜tb = tw⌝.
  Proof.
    iIntros "B W".
    iDestruct (AuthExcls.b_w_eq with "B W") as %?%Any.upcast_inj.
    iPureIntro. des. rewrite EQ0. auto.
  Qed.

  Lemma auexa_b_b_false r T (t1 t2 : T) :
    ⊢ AuExAnyB r t1 -∗ AuExAnyB r t2 -∗ False.
  Proof. iApply AuthExcls.b_b_false. Qed.

  Lemma auexa_w_w_false r T (t1 t2 : T) :
    ⊢ AuExAnyW r t1 -∗ AuExAnyW r t2 -∗ False.
  Proof. iApply AuthExcls.w_w_false. Qed.

  Lemma auexa_b_w_update r T (t1 t2 : T) S (s : S) :
    ⊢ AuExAnyB r t1 -∗ AuExAnyW r t2 ==∗ (AuExAnyB r s ∗ AuExAnyW r s).
  Proof. iApply AuthExcls.b_w_update. Qed.

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
                                   then (●E (tt ↑ : leibnizO Any.t)) ⋅ ◯E (tt ↑ : leibnizO  Any.t)
                                   else ε
                       ) : AuthExclAnysRA))).
  Proof. by iApply AuthExcls.alloc_gen. Qed.

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
  Proof.  by iApply AuthExcls.alloc_one. Qed.

  Definition AuExAny_gt : iProp := (∃ U, AuExAny (gt_dec U)).

  Lemma auexa_alloc_gt T (t : T) :
    ⊢ AuExAny_gt -∗ |==> (AuExAny_gt ∗ ∃ r, AuExAnyB r t ∗ AuExAnyW r t).
  Proof. iApply AuthExcls.alloc_gt. Qed.
End AEAPROP.

Section SPROP.

  Context {STT : StateTypes}.
  Context `{sub : @SRA.subG Γ Σ}.
  Context {TLRASs : TLRAs_small STT Γ}.
  Context {TLRAS : TLRAs STT Γ Σ}.

  Context {HasAuthExclAnys : @GRA.inG AuthExclAnysRA Γ}.

  Definition s_AuExAnyB {n} (r : nat) {T : Type} (t : T) : sProp n := (➢(AuExAnyB_ra r t))%S.

  Lemma red_s_AuExAnyB n r T (t : T) :
    ⟦s_AuExAnyB r t, n⟧ = AuExAnyB r t.
  Proof.
    unfold s_AuExAnyB. red_tl. ss.
  Qed.

  Definition s_AuExAnyW {n} (r : nat) {T : Type} (t : T) : sProp n := (➢(AuExAnyW_ra r t))%S.

  Lemma red_s_AuExAnyW n r T (t : T) :
    ⟦s_AuExAnyW r t, n⟧ = AuExAnyW r t.
  Proof.
    unfold s_AuExAnyW. red_tl. ss.
  Qed.

  Definition s_AuExAny {n} {D : nat -> Prop} (DEC : forall a, Decision (D a)) : sProp n :=
    (➢ (AuExAny_ra DEC))%S.

  Lemma red_s_AuExAny n D (DEC : forall a, Decision (D a)) :
    ⟦s_AuExAny DEC, n⟧ = AuExAny DEC.
  Proof.
    unfold s_AuExAny. red_tl. ss.
  Qed.

End SPROP.

Ltac red_tl_auexa := (try rewrite ! red_s_AuExAnyB;
                               try rewrite ! red_s_AuExAnyW;
                               try rewrite ! red_s_AuExAny
                              ).
Ltac red_tl_auexa_s := (try setoid_rewrite red_s_AuExAnyB;
                                 try setoid_rewrite red_s_AuExAnyW;
                                 try setoid_rewrite red_s_AuExAny
                                ).

Notation "'●AG' γ t" := (AuExAnyB γ t) (at level 90, γ, t at level 1) : bi_scope.
Notation "'●AG' γ t" := (s_AuExAnyB γ t) (at level 90, γ, t at level 1) : sProp_scope.
Notation "'○AG' γ t" := (AuExAnyW γ t) (at level 90, γ, t at level 1) : bi_scope.
Notation "'○AG' γ t" := (s_AuExAnyW γ t) (at level 90, γ, t at level 1) : sProp_scope.
