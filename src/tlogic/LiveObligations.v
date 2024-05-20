From sflib Require Import sflib.
From Fairness Require Import WFLibLarge Mod Optics.
From Fairness Require Import PCM IProp IPM IPropAux.
From Fairness Require Import NatMapRALarge MonotoneRA RegionRA.
Require Import Coq.Classes.RelationClasses.
From Fairness Require Import Axioms.
Require Import Program.
From Fairness Require Import FairnessRA IndexedInvariants.
From Fairness Require Export ObligationRA SimDefaultRA.

Notation "'ω'" := Ord.omega.
(* Notation "'ω'" := Ord.omega : ord_scope. *)

Section LAYER.

  Import Jacobsthal Hessenberg.

  Fixpoint _layer (l : nat) : Ord.t :=
    match l with
    | O => Ord.one
    | S m => (_layer m × ω)%ord
    end.

  Lemma _layer_S_eq l :
    _layer (S l) = (_layer l × ω)%ord.
  Proof. ss. Qed.

  Lemma _layer_zero :
    _layer O = 1%ord.
  Proof. ss. Qed.

  Lemma zero_lt_omega : (Ord.O < ω)%ord.
  Proof.
    eapply Ord.le_lt_lt; [| eapply Ord.omega_upperbound].
    eapply Ord.O_bot.
    Unshelve. exact 0.
  Qed.

  Lemma _layer_lowerbound l :
    (0 < _layer l)%ord.
  Proof.
    induction l. ss. apply Ord.S_pos.
    ss. eapply Ord.le_lt_lt.
    2:{ eapply Jacobsthal.lt_mult_r. apply zero_lt_omega. auto. }
    { rewrite Jacobsthal.mult_O_r. reflexivity. }
  Qed.

  Lemma _layer_S_lt l :
    (_layer l < _layer (S l))%ord.
  Proof.
    ss. remember (_layer l × ω)%ord as a. rewrite <- mult_1_r. subst.
    apply lt_mult_r. setoid_rewrite <- Ord.from_nat_1. apply Ord.omega_upperbound.
    apply _layer_lowerbound.
  Qed.

  Lemma _layer_lt l1 l2 :
    l1 < l2 -> (_layer l1 < _layer l2)%ord.
  Proof.
    intro LT. induction LT.
    { apply _layer_S_lt. }
    etransitivity. eauto. apply _layer_S_lt.
  Qed.

  Lemma _layer_le l1 l2 :
    l1 <= l2 -> (_layer l1 <= _layer l2)%ord.
  Proof.
    intro LE. inv LE. reflexivity.
    apply Ord.lt_le. apply _layer_lt. lia.
  Qed.

  Lemma _layer_S_decr l :
    forall (a : nat), ((_layer l × a) < _layer (S l))%ord.
  Proof.
    i. ss. apply lt_mult_r. apply Ord.omega_upperbound. apply _layer_lowerbound.
  Qed.

  Lemma _layer_decr :
    forall l m (a : nat), (l < m) -> ((_layer l × a) < _layer m)%ord.
  Proof.
    i. induction H.
    { apply _layer_S_decr. }
    etransitivity. eauto. apply _layer_S_lt.
  Qed.

  Lemma _layer_S_eq_l l :
    (_layer (S l) == (ω × _layer l))%ord.
  Proof.
    induction l.
    { ss. rewrite mult_1_l. rewrite mult_1_r. reflexivity. }
    ss. rewrite IHl. rewrite ClassicJacobsthal.mult_assoc.
    apply eq_mult_r. auto.
  Qed.

  Lemma _layer_sep :
    forall l m, (_layer (l + m) == (_layer l × _layer m))%ord.
  Proof.
    induction l; i.
    { ss. rewrite mult_1_l. reflexivity. }
    replace (S l + m) with (l + (S m)) by ss.
    rewrite IHl. rewrite (_layer_S_eq l). rewrite ClassicJacobsthal.mult_assoc.
    apply eq_mult_r. apply _layer_S_eq_l.
  Qed.

  Definition layer (l a : nat) : Ord.t := (_layer l × a)%ord.

  Lemma layer_zero1 a :
    (layer 0 a == a)%ord.
  Proof.
    unfold layer. ss. rewrite mult_1_l. reflexivity.
  Qed.

  Lemma layer_zero2 l :
    (layer l 0 == 0)%ord.
  Proof.
    unfold layer. rewrite mult_O_r. reflexivity.
  Qed.

  Lemma layer_one_one :
    (layer 1 1 == ω)%ord.
  Proof.
    unfold layer. ss. rewrite mult_1_l. rewrite mult_1_r. reflexivity.
  Qed.

  Lemma layer_S_decr_one l :
    forall a, (layer l a < layer (S l) 1)%ord.
  Proof.
    i. unfold layer. eapply Ord.lt_le_lt. apply _layer_S_decr.
    rewrite mult_1_r. reflexivity.
  Qed.

  Lemma layer_S_decr l :
    forall a b, (0 < b) -> (layer l a < layer (S l) b)%ord.
  Proof.
    i. unfold layer. eapply Ord.lt_le_lt. apply _layer_S_decr.
    etransitivity. rewrite <- mult_1_r. reflexivity.
    apply le_mult_r. setoid_rewrite <- Ord.from_nat_1. apply OrdArith.le_from_nat. auto.
  Qed.

  Lemma layer_decr :
    forall l m (LT : l < m) a b, (0 < b) -> (layer l a < layer m b)%ord.
  Proof.
    intros l m LT. induction LT; i.
    { apply layer_S_decr. auto. }
    etransitivity. eapply IHLT; eauto.
    apply layer_S_decr. auto.
  Qed.

  Lemma layer_decr_eq :
    forall l m (LE : l <= m) a, (0 < a) -> (layer l a <= layer m a)%ord.
  Proof.
    intros. inv LE.
    { reflexivity. }
    apply Ord.lt_le. apply layer_decr; lia.
  Qed.

  Lemma layer_split l :
    forall a b, (layer l (a + b) == (layer l a ⊕ layer l b))%ord.
  Proof.
    i. unfold layer. rewrite <- ClassicJacobsthal.mult_dist.
    apply eq_mult_r. rewrite <- add_from_nat. reflexivity.
  Qed.

  Lemma layer_split_le l :
    forall a b c, (a + b <= c) -> ((layer l a ⊕ layer l b) <= layer l c)%ord.
  Proof.
    i. unfold layer. rewrite <- ClassicJacobsthal.mult_dist.
    apply le_mult_r. rewrite <- add_from_nat. apply OrdArith.le_from_nat. auto.
  Qed.

  Lemma layer_sep :
    forall l m a, (layer (l + m) a == (layer l 1 × layer m a))%ord.
  Proof.
    i. unfold layer. rewrite _layer_sep. rewrite mult_1_r.
    apply ClassicJacobsthal.mult_assoc.
  Qed.

End LAYER.
Global Opaque _layer.
Global Opaque layer.

Section RULES.

  Variable ident_tgt: ID.
  Local Notation identTgtRA := (identTgtRA ident_tgt).
  (* Local Notation index := nat. *)
  Context `{Vars : nat -> Type}.
  Local Notation ArrowRA := (@ArrowRA ident_tgt Vars).

  Context `{Σ : GRA.t}.
  Context `{Invs : @IInvSet Σ Vars}.
  Context `{IDENTTGT: @GRA.inG identTgtRA Σ}.
  Context `{OBLGRA: @GRA.inG ObligationRA.t Σ}.
  Context `{EDGERA: @GRA.inG EdgeRA Σ}.
  Context `{ONESHOTRA: @GRA.inG ArrowShotRA Σ}.
  Context `{ARROWRA: @GRA.inG ArrowRA Σ}.

  Import ObligationRA.

  (** Definitions and Rules for liveness obligations. *)

  Definition liveness_obligation (k : nat) (l : nat) (o : Ord.t) :=
    (⌜(o <= layer l 1)%ord⌝ ∗ black k o)%I.

  Definition progress_credit (k : nat) (l a : nat) :=
    white k (layer l a).

  Definition live (k : nat) (q : Qp) := pending k q.

  Definition dead (k : nat) := shot k.

  Global Program Instance Persistent_liveness_obligation k l o :
    Persistent (liveness_obligation k l o).

  Global Program Instance Persistent_dead k :
    Persistent (dead k).

  Lemma pc_mon k l1 l2 a1 a2 :
    (layer l1 a1 <= layer l2 a2)%ord ->
    progress_credit k l2 a2 ⊢ |==> progress_credit k l1 a1.
  Proof.
    iIntros (LE) "PC". iPoseProof (white_mon with "PC") as "PC". eauto. iFrame.
  Qed.

  Lemma pc_split k l a b :
    progress_credit k l (a + b) ⊢ progress_credit k l a ∗ progress_credit k l b.
  Proof.
    iIntros "PC". iPoseProof (white_eq with "PC") as "PC". apply layer_split.
    iPoseProof (white_split_eq with "PC") as "[A B]". iFrame.
  Qed.

  Lemma pc_split_le k l a b c :
    (a + b <= c) ->
    progress_credit k l c ⊢ |==> progress_credit k l a ∗ progress_credit k l b.
  Proof.
    iIntros (LE) "PC".
    iMod (white_split with "PC") as "[A B]".
    { apply layer_split_le. eauto. }
    iModIntro. iFrame.
  Qed.

  Lemma pc_merge k l a b :
    (progress_credit k l a ∗ progress_credit k l b) ⊢ progress_credit k l (a + b).
  Proof.
    iIntros "[A B]". unfold progress_credit. iPoseProof (white_merge with "A B") as "W".
    iPoseProof (white_eq with "W") as "W". symmetry; apply layer_split. iFrame.
  Qed.

  Lemma lo_pc_decr k l o m a :
    (0 < a) ->
    (liveness_obligation k l o ∗ progress_credit k m a)
      ⊢ |==> ∃ o', (liveness_obligation k l o') ∗ ⌜(o' < o)%ord⌝.
  Proof.
    iIntros (LT) "[[% #LO] PC]".
    iMod (pc_mon _ 0 _ 1 _ with "PC") as "PC".
    { destruct (le_lt_eq_dec 0 m). lia.
      - apply Ord.lt_le. apply layer_decr; auto.
      - subst. rewrite ! layer_zero1. apply OrdArith.le_from_nat. lia.
    }
    iMod (black_white_decr_one with "LO [PC]") as "[% [LO2 %]]".
    { unfold progress_credit, white_one.
      iPoseProof (white_eq with "PC") as "PC".
      { apply layer_zero1. }
      iFrame.
    }
    iModIntro. iExists o0. iFrame. iSplit; auto.
    iPureIntro. etransitivity. 2: eauto. apply Ord.lt_le. auto.
  Qed.

  Lemma kill k :
    live k 1 ⊢ |==> dead k.
  Proof.
    apply pending_shot.
  Qed.

  Lemma not_dead k q :
    (live k q ∗ dead k) ⊢ ⌜False⌝.
  Proof.
    iIntros "[L D]". iApply (pending_not_shot with "L D").
  Qed.

  Lemma alloc_obligation l :
    ⊢ |==> (∃ k o, liveness_obligation k l o ∗ progress_credit k l 1 ∗ live k 1).
  Proof.
    iMod (alloc (layer l 1)) as "[% [B [W P]]]".
    iExists k. iFrame. iModIntro. iExists (layer l 1). iFrame.
    auto.
  Qed.

  (** Definitions and rules for obligation links. *)

  Definition link k0 k1 l := amplifier k0 k1 (layer l 1).

  Global Program Instance Persistent_link k0 k1 l :
    Persistent (link k0 k1 l).

  Lemma link_new k0 k1 l m o :
    (liveness_obligation k0 l o ∗ progress_credit k1 (m + l) 1)
      ⊢ #=(edges_sat)=> link k0 k1 m.
  Proof.
    iIntros "[[% LD] PC]".
    iPoseProof (white_eq with "PC") as "PC".
    { apply layer_sep. }
    iPoseProof (black_mon with "LD") as "LD".
    { apply H. }
    iMod (amplifier_intro with "LD PC") as "AMP".
    iModIntro. iFrame.
  Qed.

  Lemma link_amplify k0 k1 l m a :
    (progress_credit k0 l a ∗ link k0 k1 m)
      ⊢ #=(edges_sat)=> progress_credit k1 (m + l) a.
  Proof.
    iIntros "[PC #LINK]".
    iMod (amplifier_amplify with "LINK PC") as "PC".
    iPoseProof (white_eq with "PC") as "PC".
    { symmetry. apply layer_sep. }
    iModIntro. iFrame.
  Qed.

  Lemma link_mon k0 k1 l0 l1 :
    (l0 <= l1) ->
    link k0 k1 l1 ⊢ link k0 k1 l0.
  Proof.
    iIntros (LE) "L". iApply amplifier_mon.
    2:{ unfold link. iFrame. }
    apply layer_decr_eq; auto.
  Qed.

  Lemma link_trans k0 k1 k2 l0 l1 :
    (link k0 k1 l0 ∗ link k1 k2 l1) ⊢ link k0 k2 (l1 + l0).
  Proof.
    iIntros "[L1 L2]". unfold link. iApply amplifier_mon.
    { rewrite layer_sep. reflexivity. }
    iApply (amplifier_trans with "L1"). iFrame.
  Qed.

  (** Definitions and rules for obligation duties. *)

  Definition duty {Id} v (p : Prism.t _ Id) (i : Id) ds : iProp :=
    duty v p i (map (fun '(k, l, f) => (k, layer l 1, f)) ds).

  Definition fairness_credit {Id} (p : Prism.t _ Id) (i : Id) : iProp := FairRA.white p i 1.

  Definition promise {Id} v (p : Prism.t _ Id) (i : Id) k l f : iProp :=
    correl v p i k (layer l 1) f.

  Global Program Instance Persistent_promise {Id} v p (i : Id) k l f :
    Persistent (promise v p i k l f).

  Lemma promise_progress {Id} v (p : Prism.t _ Id) (i : Id) k l f :
    (promise v p i k l f ∗ fairness_credit p i)
      ⊢ #=(arrows_sat v)=> progress_credit k l 1 ∨ (dead k ∗ □ (prop v f)).
  Proof.
    iIntros "[#PR FC]". iPoseProof (correl_correlate with "PR FC") as "RES". iFrame.
  Qed.

  Lemma duty_add {Id} v (p : Prism.t _ Id) (i : Id) ds k l f :
    (duty v p i ds ∗ progress_credit k (l + 1) 1)
      ⊢ (□ (prop v f -∗ □ prop v f)) =(arrows_sat v)=∗ duty v p i ((k, l, f) :: ds).
  Proof.
    iIntros "[D PC] #F". iMod (duty_alloc with "D [PC] [F]") as "D".
    { unfold progress_credit. iPoseProof (white_eq with "PC") as "PC".
      { rewrite layer_sep. rewrite layer_one_one. reflexivity. }
      iFrame.
    }
    { eauto. }
    iModIntro. iFrame.
  Qed.

  Lemma duty_promise {Id} v (p : Prism.t _ Id) (i : Id) ds k l f :
    In (k, l, f) ds ->
    duty v p i ds ⊢ promise v p i k l f.
  Proof.
    iIntros (IN) "D". iApply duty_correl. 2: iFrame.
    apply (in_map (fun '(k0, l0, f0) => (k0, layer l0 1, f0))) in IN. auto.
  Qed.

  Lemma duty_fulfill {Id} v (p : Prism.t _ Id) (i : Id) ds k l f :
    (duty v p i ((k, l, f) :: ds) ∗ dead k ∗ prop v f)
      ⊢ #=(arrows_sat v)=> duty v p i ds.
  Proof.
    iIntros "(DUTY & DEAD & F)".
    iMod (duty_done with "DUTY DEAD F") as "D". iModIntro. iFrame.
  Qed.

  Lemma duty_permutation {Id} v (p : Prism.t _ Id) (i : Id) ds0 ds1 :
    (ds0 ≡ₚ ds1) -> duty v p i ds0 ⊢ duty v p i ds1.
  Proof.
    iIntros (P) "D". iApply duty_permutation. 2: iFrame.
    apply Permutation_map. auto.
  Qed.

  (** Obligation duties specialized for thread fairness. *)

  Definition thread_credit : iProp := FairRA.white_thread (S:=_).

  Definition thread_promise v k l f : iProp := correl_thread v k (layer l 1) f.

  Global Program Instance Persistent_thread_promise v k l f :
    Persistent (thread_promise v k l f).

  Lemma thread_promise_progress v k l f :
    (thread_promise v k l f ∗ thread_credit)
      ⊢ #=(arrows_sat v)=> progress_credit k l 1 ∨ (dead k ∗ □ (prop v f)).
  Proof.
    iIntros "[#PR FC]". iPoseProof (correl_thread_correlate with "PR FC") as "RES". iFrame.
  Qed.

  Lemma duty_thread_promise v i ds k l f :
    In (k, l, f) ds ->
    duty v inlp i ds ⊢ thread_promise v k l f.
  Proof.
    iIntros (IN) "D". iApply duty_correl_thread. 2: iFrame.
    apply (in_map (fun '(k0, l0, f0) => (k0, layer l0 1, f0))) in IN. auto.
  Qed.

  (** Additional definitions and rules. *)

  Definition progress_credits (l : list (nat * nat)) m a :=
    taxes (map (fun '(k, n) => (k, layer n 1)) l) (layer m a).

  Lemma pp_nil m a : ⊢ progress_credits [] m a.
  Proof. iApply taxes_nil. Qed.

  Lemma pp_perm l0 l1 m a :
    (l0 ≡ₚ l1) -> progress_credits l0 m a ⊢ progress_credits l1 m a.
  Proof.
    iIntros. iApply taxes_perm. 2: iFrame.
    apply Permutation_map; auto.
  Qed.

  Lemma pp_combine l0 l1 m a :
    progress_credits l0 m a ∗ progress_credits l1 m a ⊢ progress_credits (l0 ++ l1) m a.
  Proof.
    iIntros "[A B]". unfold progress_credits. rewrite map_app.
    iApply taxes_combine. iFrame.
  Qed.

  Lemma pp_split l0 l1 m a :
    progress_credits (l0 ++ l1) m a ⊢ progress_credits l0 m a ∗ progress_credits l1 m a.
  Proof.
    iIntros "A". unfold progress_credits. rewrite map_app.
    iApply taxes_split. iFrame.
  Qed.

  Lemma pp_cons_unfold k l tl m a :
    progress_credits ((k, l) :: tl) m a ⊢ progress_credit k (1 + l + m) a ∗ progress_credits tl m a.
  Proof.
    unfold progress_credits. iIntros "P". ss. unfold progress_credit.
    iPoseProof (taxes_cons_unfold with "P") as "[W T]". iFrame.
    iApply white_eq. 2: iFrame.
    replace (S (l + m)) with (l + 1 + m) by lia.
    rewrite ! layer_sep. rewrite layer_one_one. reflexivity.
  Qed.

  Lemma pp_cons_fold k l tl m a :
    progress_credit k (1 + l + m) a ∗ progress_credits tl m a ⊢ progress_credits ((k, l) :: tl) m a.
  Proof.
    unfold progress_credits. iIntros "[PC PP]". ss. unfold progress_credit.
    iPoseProof (taxes_cons_fold with "[PC PP]") as "W". 2: iFrame.
    iFrame. iApply white_eq. 2: iFrame.
    replace (S (l + m)) with (l + 1 + m) by lia.
    rewrite ! layer_sep. rewrite layer_one_one. reflexivity.
  Qed.

  Lemma pp_decr l m :
    forall a b c, (a + b <= c) ->
             progress_credits l m c ⊢ |==> progress_credits l m a ∗ progress_credits l m b.
  Proof.
    intros. iIntros "PP". iMod (taxes_ord_split with "PP") as "[T1 T2]".
    2: iModIntro; iFrame.
    apply layer_split_le. lia.
  Qed.

  Lemma pp_merge l m :
    forall a b, progress_credits l m a ∗ progress_credits l m b ⊢ |==> progress_credits l m (a + b).
  Proof.
    intros. iIntros "PP". iPoseProof (taxes_ord_merge with "PP") as "PP".
    iApply taxes_ord_mon. 2: iFrame. rewrite layer_split. reflexivity.
  Qed.

  (** Additional definitions and rules. *)

  Definition collection_credits k o (ps : list (nat * nat)) l :=
    collection_taxes k o (map (fun '(k, l) => (k, layer l 1)) ps) (layer l 1).

  Lemma collection_credits_decr k o ps l :
    forall m a, (0 < a) ->
           (collection_credits k o ps l ∗ progress_credit k m a)
             ⊢ #=> (∃ o', collection_credits k o' ps l ∗ ⌜(o' < o)%ord⌝ ∗ progress_credits ps l 1).
  Proof.
    intros. iIntros "[COL PC]". 
    iMod (pc_mon _ 0 _ 1 _ with "PC") as "PC".
    { destruct (le_lt_eq_dec 0 m). lia.
      - apply Ord.lt_le. apply layer_decr; auto.
      - subst. rewrite ! layer_zero1. apply OrdArith.le_from_nat. lia.
    }
    iMod (collection_taxes_decr_one with "COL [PC]") as "[% (COL & % & TAX)]".
    { iApply white_eq. 2: iFrame. rewrite layer_zero1. reflexivity. }
    iExists o'. iFrame.
    iPureIntro. auto.
  Qed.

  Lemma collection_credits_make k l o ps m :
    (liveness_obligation k l o ∗ progress_credits ps (m + l) 1) ⊢ |==> collection_credits k o ps m.
  Proof.
    iIntros "[[% B] T]". iMod (taxes_ord_mon with "T") as "T".
    { rewrite layer_sep. eapply Jacobsthal.le_mult_r. eauto. }
    iPoseProof (collection_taxes_make with "[B T]") as "CT". iFrame.
    iModIntro. iFrame.
  Qed.

  (** Additional definitions and rules. *)

  Definition until_promise {Id} v (p : Prism.t _ Id) (i : Id) k l f (P : iProp) (r : Qp) :=
    (promise v p i k l f ∗ ((P ∗ live k r) ∨ (dead k ∗ □ (prop v f))))%I.

  Lemma until_promise_progress {Id} v (p : Prism.t _ Id) (i : Id) k l f (P : iProp) (r : Qp) :
    (until_promise v p i k l f P r ∗ fairness_credit p i)
      ⊢ #=(arrows_sat v)=> ((P ∗ live k r ∗ progress_credit k l 1) ∨ (dead k ∗ □ (prop v f))).
  Proof.
    iIntros "[[PR A] FC]". iMod (promise_progress with "[PR FC]") as "B". iFrame.
    iModIntro. iDestruct "A" as "[[P L] | [A2 AP]]"; iDestruct "B" as "[B1 | [D F]]".
    { iLeft. iFrame. }
    { iPoseProof (not_dead with "[L D]") as "%". iFrame. inv H. }
    { iRight. iFrame. }
    { iRight. iFrame. }
  Qed.

  Lemma until_promise_live {Id} v (p : Prism.t _ Id) (i : Id) k l f (P : iProp) (r : Qp) :
    (promise v p i k l f ∗ P ∗ live k r) ⊢ until_promise v p i k l f P r.
  Proof.
    iIntros "(A & B & C)". unfold until_promise. iFrame. iLeft. iFrame.
  Qed.

  Lemma until_promise_dead {Id} v (p : Prism.t _ Id) (i : Id) k l f (P : iProp) (r : Qp) :
    (promise v p i k l f ∗ dead k ∗ □ (prop v f)) ⊢ until_promise v p i k l f P r.
  Proof.
    iIntros "(A & B & C)". unfold until_promise. iFrame. iRight. iFrame.
  Qed.

  Definition until_thread_promise v k l f (P : iProp) (r : Qp) :=
    (thread_promise v k l f ∗ ((P ∗ live k r) ∨ (dead k ∗ □ (prop v f))))%I.

  Lemma until_thread_promise_progress v k l f (P : iProp) (r : Qp) :
    (until_thread_promise v k l f P r ∗ thread_credit)
      ⊢ #=(arrows_sat v)=> ((P ∗ live k r ∗ progress_credit k l 1) ∨ (dead k ∗ □ (prop v f))).
  Proof.
    iIntros "[[PR A] FC]". iMod (thread_promise_progress with "[PR FC]") as "B". iFrame.
    iModIntro. iDestruct "A" as "[[P L] | [A2 AP]]"; iDestruct "B" as "[B1 | [D F]]".
    { iLeft. iFrame. }
    { iPoseProof (not_dead with "[L D]") as "%". iFrame. inv H. }
    { iRight. iFrame. }
    { iRight. iFrame. }
  Qed.

  Lemma until_thread_promise_live v k l f (P : iProp) (r : Qp) :
    (thread_promise v k l f ∗ P ∗ live k r) ⊢ until_thread_promise v k l f P r.
  Proof.
    iIntros "(A & B & C)". unfold until_thread_promise. iFrame. iLeft. iFrame.
  Qed.

  Lemma until_thread_promise_dead v k l f (P : iProp) (r : Qp) :
    (thread_promise v k l f ∗ dead k ∗ □ (prop v f)) ⊢ until_thread_promise v k l f P r.
  Proof.
    iIntros "(A & B & C)". unfold until_thread_promise. iFrame. iRight. iFrame.
  Qed.

  (** Induction rules. *)

  Lemma lo_ind k l o (P : iProp) :
    (liveness_obligation k l o)
      ⊢ (□ (∃ m a, (⌜(0 < a)⌝ -∗ progress_credit k m a ==∗ P) ==∗ P)) ==∗ P.
  Proof.
    pattern o. revert o. apply (well_founded_ind Ord.lt_well_founded). intros.
    iIntros "#LO #(% & % & IND)". iApply "IND". iIntros "% PC".
    iMod (lo_pc_decr with "[LO PC]") as "[% [#LO2 %]]". apply H0. iFrame. eauto.
    iClear "LO". iPoseProof (H with "LO2 [IND]") as "P". auto.
    2: iApply "P".
    { iExists m, a. auto. }
  Qed.

  Lemma promise_ind {Id} v (p : Prism.t _ Id) (i : Id) k l o m f (R : iProp) :
    (liveness_obligation k l o ∗ promise v p i k m f)
      ⊢ ((□ ((fairness_credit p i =(arrows_sat v)=∗ R) ==∗ R))
           ∗ (□ ((dead k ∗ □ prop _ f) ==∗ R)))
      ==∗ R.
  Proof.
    iIntros "[#LO #PR] [#IND #RES]".
    iApply "IND". iIntros "FC". iMod (promise_progress with "[PR FC]") as "[PC | [#D #P]]".
    { iFrame. eauto. }
    { iMod (lo_ind with "LO [PC]") as "R". 2: iModIntro; iApply "R".
      iModIntro. iExists m, 1.  iIntros "IND2". iApply "IND".
      iIntros "FC". iMod (promise_progress with "[LO FC]") as "[PC | [#D #P]]".
      { iFrame. eauto. }
      { iMod ("IND2" with "[] [PC]") as "R". auto. iFrame. iModIntro. iFrame. }
      { iMod ("RES" with "[D P]") as "R". auto. iModIntro. iFrame. }
    }
    { iMod ("RES" with "[D P]") as "R". auto. iModIntro. iFrame. }
  Qed.

  Lemma thread_promise_ind v k l o m f (R : iProp) :
    (liveness_obligation k l o ∗ thread_promise v k m f)
      ⊢ ((□ ((thread_credit =(arrows_sat v)=∗ R) ==∗ R))
           ∗ (□ ((dead k ∗ □ prop _ f) ==∗ R)))
      ==∗ R.
  Proof.
    iIntros "[#LO #PR] [#IND #RES]".
    iApply "IND". iIntros "FC". iMod (thread_promise_progress with "[PR FC]") as "[PC | [#D #P]]".
    { iFrame. eauto. }
    { iMod (lo_ind with "LO [PC]") as "R". 2: iModIntro; iApply "R".
      iModIntro. iExists m, 1.  iIntros "IND2". iApply "IND".
      iIntros "FC". iMod (thread_promise_progress with "[LO FC]") as "[PC | [#D #P]]".
      { iFrame. eauto. }
      { iMod ("IND2" with "[] [PC]") as "R". auto. iFrame. iModIntro. iFrame. }
      { iMod ("RES" with "[D P]") as "R". auto. iModIntro. iFrame. }
    }
    { iMod ("RES" with "[D P]") as "R". auto. iModIntro. iFrame. }
  Qed.

  Lemma cc_ind k o ps l (P : iProp) :
    (collection_credits k o ps l)
      ⊢ (□ (∃ m a, (⌜(0 < a)⌝ -∗ progress_credit k m a ==∗ (progress_credits ps l 1 ∗ P)) ==∗ P))
      ==∗ P.
  Proof.
    pattern o. revert o. apply (well_founded_ind Ord.lt_well_founded). intros.
    iIntros "CC #(% & % & IND)". iApply "IND". iIntros "% PC".
    iMod (collection_credits_decr with "[CC PC]") as "[% [CC2 [% PC2]]]". apply H0. iFrame.
    iPoseProof (H with "CC2 [IND]") as ">P". auto.
    2: iModIntro; iFrame.
    { iExists m, a. auto. }
  Qed.

  Lemma cc_promise_ind {Id} v (p : Prism.t _ Id) (i : Id) k o ps l m f (R : iProp) :
    (collection_credits k o ps l ∗ promise v p i k m f)
      ⊢ (□ ((fairness_credit p i =(arrows_sat v)=∗ ((progress_credits ps l 1 ∗ R) ∨ (dead k ∗ □ prop _ f))) ==∗ R))
      ==∗ R.
  Proof.
    iIntros "[CC #PR] #IND". iMod (cc_ind with "CC []") as "R". 2: iModIntro; iApply "R".
    iExists m, 1. iModIntro.  iIntros "IND2". iApply "IND". iIntros "FC".
    iMod (promise_progress with "[PR FC]") as "[PC | [#D #P]]".
    { iFrame. eauto. }
    { iMod ("IND2" with "[] [PC]") as "R". auto. iFrame. iModIntro. iFrame. }
    { iModIntro. iRight. auto. }
  Qed.

  Lemma cc_thread_promise_ind v k o ps l m f (R : iProp) :
    (collection_credits k o ps l ∗ thread_promise v k m f)
      ⊢ (□ ((thread_credit =(arrows_sat v)=∗ ((progress_credits ps l 1 ∗ R) ∨ (dead k ∗ □ prop _ f))) ==∗ R))
      ==∗ R.
  Proof.
    iIntros "[CC #PR] #IND". iMod (cc_ind with "CC []") as "R". 2: iModIntro; iApply "R".
    iExists m, 1. iModIntro.  iIntros "IND2". iApply "IND". iIntros "FC".
    iMod (thread_promise_progress with "[PR FC]") as "[PC | [#D #P]]".
    { iFrame. eauto. }
    { iMod ("IND2" with "[] [PC]") as "R". auto. iFrame. iModIntro. iFrame. }
    { iModIntro. iRight. auto. }
  Qed.

End RULES.


  Definition liveness_obligation (k : nat) (l : nat) (o : Ord.t) :=
    (⌜(o <= layer l 1)%ord⌝ ∗ black k o)%I.

  Definition progress_credit (k : nat) (l a : nat) :=
    white k (layer l a).

  Definition live (k : nat) (q : Qp) := pending k q.

  Definition dead (k : nat) := shot k.
  Definition link k0 k1 l := amplifier k0 k1 (layer l 1).
  Definition duty {Id} v (p : Prism.t _ Id) (i : Id) ds : iProp :=
    duty v p i (map (fun '(k, l, f) => (k, layer l 1, f)) ds).

  Definition fairness_credit {Id} (p : Prism.t _ Id) (i : Id) : iProp := FairRA.white p i 1.
  Definition promise {Id} v (p : Prism.t _ Id) (i : Id) k l f : iProp :=
    correl v p i k (layer l 1) f.
  Definition thread_credit : iProp := FairRA.white_thread (S:=_).
  Definition thread_promise v k l f : iProp := correl_thread v k (layer l 1) f.
  Definition progress_credits (l : list (nat * nat)) m a :=
    taxes (map (fun '(k, n) => (k, layer n 1)) l) (layer m a).
  Definition collection_credits k o (ps : list (nat * nat)) l :=
    collection_taxes k o (map (fun '(k, l) => (k, layer l 1)) ps) (layer l 1).
  Definition until_promise {Id} v (p : Prism.t _ Id) (i : Id) k l f (P : iProp) (r : Qp) :=
    (promise v p i k l f ∗ ((P ∗ live k r) ∨ (dead k ∗ □ (prop v f))))%I.
  Definition until_thread_promise v k l f (P : iProp) (r : Qp) :=
    (thread_promise v k l f ∗ ((P ∗ live k r) ∨ (dead k ∗ □ (prop v f))))%I.
