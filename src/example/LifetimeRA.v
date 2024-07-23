From sflib Require Import sflib.
From Fairness Require Import Any PCM IProp IPM IPropAux.
From Fairness Require Import MonotoneRA.
From Fairness Require Import TemporalLogic.

Module Lifetime.

  Definition t : ucmra := @FiniteMap.t (URA.prod (URA.agree Any.t) (OneShot.t unit)).

  Section RA.

    Context `{Σ : GRA.t}.
    Context `{@GRA.inG t Σ}.

    Definition pending (k: nat) {T : Type} (t : T) (q: Qp): iProp :=
      OwnM (FiniteMap.singleton
              k ((Some (Some (t↑)) : URA.agree Any.t, OneShot.pending _ q : OneShot.t unit)
                  : URA.prod (URA.agree Any.t) (OneShot.t unit))).

    Definition shot (k: nat) {T : Type} (t : T) : iProp :=
      OwnM (FiniteMap.singleton
              k ((Some (Some (t↑)) : URA.agree Any.t, OneShot.shot tt: OneShot.t unit):
                  URA.prod (URA.agree Any.t) (OneShot.t unit))).

    Lemma shot_persistent k {T} (t : T)
      :
      shot k t -∗ □ shot k t.
    Proof.
      iIntros "H". iPoseProof (own_persistent with "H") as "H".
      rewrite FiniteMap.singleton_core. auto.
    Qed.

    Global Program Instance Persistent_shot k {T} (t: T) : Persistent (shot k t).
    Next Obligation.
    Proof.
      i. iIntros "POS". iPoseProof (shot_persistent with "POS") as "POS". auto.
    Qed.

    Lemma pending_shot k {T} (t : T)
      :
      (pending k t 1)
        -∗
        #=> (shot k t).
    Proof.
      iApply OwnM_Upd. eapply FiniteMap.singleton_updatable.
      { apply URA.prod_updatable. reflexivity. apply OneShot.pending_shot. }
    Qed.

    Lemma pending_not_shot k q {T1 T2} (t1 : T1) (t2 : T2)
      :
      (pending k t1 q)
        -∗
        (shot k t2)
        -∗
        False.
    Proof.
      iIntros "H0 H1". iCombine "H0 H1" as "H".
      iOwnWf "H". rewrite FiniteMap.singleton_add in H0.
      rewrite FiniteMap.singleton_wf in H0. ur in H0. des. ur in H1. exfalso. auto.
    Qed.

    Lemma pending_wf k q {T} (t : T)
      :
      (pending k t q)
        -∗
        (⌜(q ≤ 1)%Qp⌝).
    Proof.
      iIntros "H". iOwnWf "H".
      rewrite FiniteMap.singleton_wf in H0. ur in H0. des. ur in H1. auto.
    Qed.

    Lemma pending_merge k q0 q1 {T} (t : T)
      :
      (pending k t q0)
        -∗
        (pending k t q1)
        -∗
        (pending k t (q0 + q1)%Qp).
    Proof.
      iIntros "H0 H1". iCombine "H0 H1" as "H".
      rewrite FiniteMap.singleton_add. ur. ur. des_ifs.
    Qed.

    Lemma pending_split k q0 q1 {T} (t : T)
      :
      (pending k t (q0 + q1)%Qp)
        -∗
        (pending k t q0 ∗ pending k t q1).
    Proof.
      iIntros "H".
      iPoseProof (OwnM_extends with "H") as "[H0 H1]"; [|iSplitL "H0"; [iApply "H0"|iApply "H1"]].
      { rewrite FiniteMap.singleton_add. rewrite OneShot.pending_sum. ur. ur. des_ifs. reflexivity. }
    Qed.

    Lemma alloc {T} (t : T)
      :
      ⊢ #=> (∃ k, pending k t 1).
    Proof.
      iPoseProof (@OwnM_unit _ _ H) as "H".
      iPoseProof (OwnM_Upd_set with "H") as "> H0".
      { eapply FiniteMap.singleton_alloc. instantiate (1:=(Some (Some (t↑)), OneShot.pending unit 1)).
        (* repeat rewrite unfold_prod_add. repeat rewrite URA.unit_idl. repeat rewrite URA.unit_id. *)
        rewrite unfold_prod_wf. ss. split.
        { ur. ss. }
        { apply OneShot.pending_one_wf. }
      }
      iDestruct "H0" as "[% [% H0]]".
      des. subst. iModIntro. iExists _. iFrame.
    Qed.

  End RA.

End Lifetime.

Section SPROP.

  Context {STT : StateTypes}.
  Context `{sub : @SRA.subG Γ Σ}.
  Context {TLRASs : TLRAs_small STT Γ}.
  Context {TLRAS : TLRAs STT Γ Σ}.

  Context {HasLifetime : @GRA.inG Lifetime.t Γ}.

  Definition s_lft_pending {n} (k: nat) {T : Type} (t : T) (q: Qp) : sProp n :=
    (➢(FiniteMap.singleton
         k ((Some (Some (t↑)) : URA.agree Any.t, OneShot.pending _ q : OneShot.t unit)
             : URA.prod (URA.agree Any.t) (OneShot.t unit))))%S.

  Lemma red_s_lft_pending n k T (t : T) q :
    ⟦s_lft_pending k t q, n⟧ = Lifetime.pending k t q.
  Proof.
    unfold s_lft_pending. red_tl. ss.
  Qed.

  Definition s_lft_shot {n} (k: nat) {T : Type} (t : T) : sProp n :=
    (➢(FiniteMap.singleton
         k ((Some (Some (t↑)) : URA.agree Any.t, OneShot.shot tt: OneShot.t unit):
             URA.prod (URA.agree Any.t) (OneShot.t unit))))%S.

  Lemma red_s_lft_shot n k T (t : T) :
    ⟦s_lft_shot k t, n⟧ = Lifetime.shot k t.
  Proof.
    unfold s_lft_shot. red_tl. ss.
  Qed.

End SPROP.

Ltac red_tl_lifetime := (try rewrite ! red_s_lft_pending;
                         try rewrite ! red_s_lft_shot
                        ).
Ltac red_tl_lifetime_s := (try setoid_rewrite red_s_lft_pending;
                           try setoid_rewrite red_s_lft_shot
                          ).

Notation "'live' γ t q" := (Lifetime.pending γ t q) (at level 90, γ, t, q at level 1) : bi_scope.
Notation "'live' γ t q" := (s_lft_pending γ t q) (at level 90, γ, t, q at level 1) : sProp_scope.
Notation "'dead' γ t" := (Lifetime.shot γ t) (at level 90, γ, t at level 1) : bi_scope.
Notation "'dead' γ t" := (s_lft_shot γ t) (at level 90, γ, t at level 1) : sProp_scope.
