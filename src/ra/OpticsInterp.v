From sflib Require Import sflib.
From Paco Require Import paco.
From Fairness Require Import Optics  IPM PCM.
From stdpp Require Import coPset gmap namespaces.
From iris.algebra Require Import cmra updates lib.excl_auth coPset gset.
From Fairness Require Export IndexedInvariants.

Set Implicit Arguments.

Require Import Program.

Section STATE.

  Context `{Σ: GRA.t}.
  Notation iProp := (iProp Σ).

  Class ViewInterp {S V} (l : Lens.t S V) (SI : S -> iProp) (VI : V -> iProp) := {
      view_interp : forall s, (SI s) ⊢ (VI (Lens.view l s) ∗ ∀ x, VI x -∗ SI (Lens.set l x s))
    }.

  Definition interp_prod {A B} (SA: A -> iProp) (SB: B -> iProp):
    (A * B -> iProp) :=
    fun '(sa, sb) => (SA sa ∗ SB sb)%I.

  Global Program Instance ViewInterp_fstl {A B}
         (SA: A -> iProp) (SB: B -> iProp)
    : ViewInterp fstl (interp_prod SA SB) SA.
  Next Obligation.
  Proof. iIntros "[$ $]" (?) "$". Qed.

  Global Program Instance ViewInterp_sndl {A B}
         (SA: A -> iProp) (SB: B -> iProp)
    : ViewInterp sndl (interp_prod SA SB) SB.
  Next Obligation.
  Proof. iIntros "[$ $]" (?) "$". Qed.

  Global Program Instance ViewInterp_id {S} (SI: S -> iProp): ViewInterp Lens.id SI SI.
  Next Obligation.
  Proof. iIntros "$" (?) "$". Qed.

  Global Program Instance ViewInterp_compose {A B C}
         {lab: Lens.t A B}
         {lbc: Lens.t B C}
         (SA: A -> iProp) (SB: B -> iProp) (SC: C -> iProp)
         `{VAB: ViewInterp _ _ lab SA SB}
         `{VBC: ViewInterp _ _ lbc SB SC}
    :
    ViewInterp (Lens.compose lab lbc) SA SC.
  Next Obligation.
  Proof.
    iIntros "H".
    iDestruct (view_interp with "H") as "[H K0]".
    iDestruct (view_interp with "H") as "[$ K1]".
    iIntros (?) "H".
    iApply "K0". iApply "K1". iApply "H".
  Qed.

  Definition N_state_src := (nroot .@ "_state_src").
  Definition E_state_src: coPset := ↑ N_state_src.
  Definition N_state_tgt := (nroot .@ "_state_tgt").
  Definition E_state_tgt: coPset := ↑ N_state_tgt.

  Variable state_src: Type.
  Variable state_tgt: Type.

  Local Notation stateSrcRA := (excl_authUR (leibnizO (option state_src)) : ucmra).
  Local Notation stateTgtRA := (excl_authUR (leibnizO (option state_tgt)) : ucmra).

  Local Notation index := nat.
  Context `{Vars : index -> Type}.
  Context `{Invs : @IInvSet Σ Vars}.

  Context `{STATESRC: @GRA.inG (stateSrcRA) Σ}.
  Context `{STATETGT: @GRA.inG (stateTgtRA) Σ}.
  Context `{COPSETRA : @PCM.GRA.inG coPset_disjUR Σ}.
  Context `{GSETRA : @PCM.GRA.inG (gset_disjUR positive) Σ}.
  Context `{INVSETRA : @GRA.inG (IInvSetRA Vars) Σ}.

  Definition St_src (st_src: state_src): iProp :=
    OwnM (◯E (Some st_src : leibnizO (option state_src))).

  Definition Vw_src (st: state_src) {V} (l : Lens.t state_src V) (v : V) : iProp :=
    St_src (Lens.set l v st).

  Definition src_interp_as n {V} (l: Lens.t state_src V) (VI: V -> Vars n) :=
    (∃ (SI : state_src -> Vars n) (p : Vars n),
        (⌜prop _ p = (∃ st, St_src st ∗ prop _ (SI st))%I⌝)
          ∗ (inv n N_state_src p) ∗ ⌜ViewInterp l (fun s => prop _ (SI s)) (fun v => prop _ (VI v))⌝)%I.

  Global Program Instance src_interp_as_persistent n {V} (l: Lens.t state_src V) (VI: V -> Vars n) :
    Persistent (src_interp_as l VI).

  Global Program Instance src_interp_as_acc x A E n {V} (l: Lens.t state_src V) (VI: V -> Vars n):
    IntoAcc
      (src_interp_as l VI)
      (n < x /\ ((↑N_state_src) ⊆ E)) True
      (fupd_ex x A E (E ∖ E_state_src))
      (fupd_ex x A (E ∖ E_state_src) E)
      (fun (st: state_src) => ∃ vw, Vw_src st l vw ∗ prop _ (VI vw))%I
      (fun (st: state_src) => ∃ vw, Vw_src st l vw ∗ prop _ (VI vw))%I
      (fun _ => None).
  Next Obligation.
  Proof.
    iIntros "[% [% [%PIS [INV %]]]] _".
    iInv "INV" as "INTERP" "K".
    rewrite ! PIS. iDestruct "INTERP" as "[% [ST INTERP]]".
    iModIntro. iPoseProof ((view_interp (SI:=λ s : state_src, prop n (SI s))) with "INTERP") as "[INTERP SET]".
    iExists _. iSplitL "ST INTERP".
    { iExists _. iFrame "INTERP". unfold Vw_src. iEval (erewrite Lens.set_view). iFrame. }
    iIntros "[% [ST INTERP]]".
    iPoseProof ("SET" with "INTERP") as "INTERP".
    iApply ("K" with "[ST INTERP]"). iExists _. iFrame.
  Qed.

  Lemma src_interp_as_id x A E n (LT: n < x) (SI: state_src -> Vars n)
        p (IN : prop n p = (∃ st, St_src st ∗ prop _ (SI st))%I):
    (∃ st, St_src st ∗ prop _ (SI st)) ⊢ =|x|=(A)={E}=> (src_interp_as Lens.id SI).
  Proof.
    iIntros "H". rewrite <- IN. iMod (FUpd_alloc with "H") as "H". auto.
    iModIntro. iExists _, p. iSplit. auto. iSplit. auto.
    iPureIntro. typeclasses eauto.
  Qed.

  Lemma src_interp_as_compose n A B
        {la: Lens.t state_src A}
        {lb: Lens.t A B}
        (SA: A -> Vars n)
        (SB: B -> Vars n)
        `{VAB: ViewInterp _ _ lb (fun a => prop _ (SA a)) (fun b => prop _ (SB b))}
    :
    src_interp_as la SA ⊢ src_interp_as (Lens.compose la lb) SB.
  Proof.
    iIntros "[% [% [% [H %]]]]". iExists _, p. iSplit; [eauto|]. iSplit; [eauto|].
    iPureIntro. typeclasses eauto.
  Qed.

  Lemma src_interp_as_equiv n A
        {la: Lens.t state_src A}
        (SA: A -> Vars n)
        (SA2: A -> Vars n)
    :
    (∀ a, prop _ (SA a) ⊣⊢ prop _ (SA2 a))
    ->
      src_interp_as la SA ⊢ src_interp_as la SA2.
  Proof.
    iIntros (IMPL) "[% [% [% [H %]]]]". iExists SI, p. do 2 (iSplit; [auto|]).
    iPureIntro. econs. iIntros (?) "P".
    iPoseProof (view_interp with "[P]") as "[P1 K]". iFrame.
    iPoseProof (IMPL with "P1") as "P2".
    iFrame. iIntros (?) "P2". iApply "K". iApply IMPL. iFrame.
  Qed.



  Definition St_tgt (st_tgt: state_tgt): iProp :=
    OwnM (◯E (Some st_tgt : leibnizO (option state_tgt))).

  Definition Vw_tgt (st: state_tgt) {V} (l : Lens.t state_tgt V) (v : V) : iProp :=
    St_tgt (Lens.set l v st).

  Definition tgt_interp_as n {V} (l: Lens.t state_tgt V) (VI: V -> Vars n) :=
    (∃ (SI : _ -> Vars n) (p : Vars n),
        (⌜prop _ p = (∃ st, St_tgt st ∗ prop _ (SI st))%I⌝)
          ∗ (inv n N_state_tgt p) ∗ ⌜ViewInterp l (fun s => prop _ (SI s)) (fun v => prop _ (VI v))⌝)%I.

  Global Program Instance tgt_interp_as_persistent n {V} (l: Lens.t state_tgt V) (VI: V -> Vars n) :
    Persistent (tgt_interp_as l VI).

  Global Program Instance tgt_interp_as_acc x A E n {V} (l: Lens.t state_tgt V) (VI: V -> Vars n):
    IntoAcc
      (tgt_interp_as l VI)
      (n < x /\ ((↑N_state_tgt) ⊆ E)) True
      (fupd_ex x A E (E ∖ E_state_tgt))
      (fupd_ex x A (E ∖ E_state_tgt) E)
      (fun (st: state_tgt) => ∃ vw, Vw_tgt st l vw ∗ prop _ (VI vw))%I
      (fun (st: state_tgt) => ∃ vw, Vw_tgt st l vw ∗ prop _ (VI vw))%I
      (fun _ => None).
  Next Obligation.
  Proof.
    iIntros "[% [% [%PIS [INV %]]]] _".
    iInv "INV" as "INTERP" "K".
    rewrite ! PIS. iDestruct "INTERP" as "[% [ST INTERP]]".
    iModIntro. iPoseProof (view_interp (SI:=fun s => prop _ (SI s)) with "INTERP") as "[INTERP SET]".
    iExists _. iSplitL "ST INTERP".
    { iExists _. iFrame "INTERP". unfold Vw_tgt. iEval (erewrite Lens.set_view). iFrame. }
    iIntros "[% [ST INTERP]]".
    iPoseProof ("SET" with "INTERP") as "INTERP".
    iApply ("K" with "[ST INTERP]"). iExists _. iFrame.
  Qed.

  Lemma tgt_interp_as_id x A E n (LT: n < x) (SI: state_tgt -> Vars n)
        p (IN : prop n p = (∃ st, St_tgt st ∗ prop _ (SI st))%I):
    (∃ st, St_tgt st ∗ prop _ (SI st)) ⊢ =|x|=(A)={E}=> (tgt_interp_as Lens.id (SI)).
  Proof.
    iIntros "H". rewrite <- IN. iMod (FUpd_alloc with "H") as "H". auto.
    iModIntro. iExists _, p. iSplit. auto. iSplit. auto.
    iPureIntro. typeclasses eauto.
  Qed.

  Lemma tgt_interp_as_compose n A B
        {la: Lens.t state_tgt A}
        {lb: Lens.t A B}
        (SA: A -> Vars n)
        (SB: B -> Vars n)
        `{VAB: ViewInterp _ _ lb (fun a => prop _ (SA a)) (fun b => prop _ (SB b)) }
    :
    tgt_interp_as la SA ⊢ tgt_interp_as (Lens.compose la lb) SB.
  Proof.
    iIntros "[% [% [% [H %]]]]". iExists _, p. iSplit; [eauto|]. iSplit; [eauto|].
    iPureIntro. typeclasses eauto.
  Qed.

  Lemma tgt_interp_as_equiv n A
        {la: Lens.t state_tgt A}
        (SA: A -> Vars n)
        (SA2: A -> Vars n)
    :
    (∀ a, prop _ (SA a) ⊣⊢ prop _ (SA2 a))
    ->
      tgt_interp_as la SA ⊢ tgt_interp_as la SA2.
  Proof.
    iIntros (IMPL) "[% [% [% [H %]]]]". iExists SI, p. do 2 (iSplit; [auto|]).
    iPureIntro. econs. iIntros (?) "P".
    iPoseProof (view_interp with "[P]") as "[P1 K]". iFrame.
    iPoseProof (IMPL with "P1") as "P2".
    iFrame. iIntros (?) "P2". iApply "K". iApply IMPL. iFrame.
  Qed.

End STATE.
