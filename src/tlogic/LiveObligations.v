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

  Lemma _layer_S_drop l :
    forall (a : nat), ((_layer l × a) < _layer (S l))%ord.
  Proof.
    i. ss. apply lt_mult_r. apply Ord.omega_upperbound. apply _layer_lowerbound.
  Qed.

  Lemma _layer_drop :
    forall l m (a : nat), (l < m) -> ((_layer l × a) < _layer m)%ord.
  Proof.
    i. induction H.
    { apply _layer_S_drop. }
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

  Lemma layer_S_drop_one l :
    forall a, (layer l a < layer (S l) 1)%ord.
  Proof.
    i. unfold layer. eapply Ord.lt_le_lt. apply _layer_S_drop.
    rewrite mult_1_r. reflexivity.
  Qed.

  Lemma layer_S_drop l :
    forall a b, (0 < b) -> (layer l a < layer (S l) b)%ord.
  Proof.
    i. unfold layer. eapply Ord.lt_le_lt. apply _layer_S_drop.
    etransitivity. rewrite <- mult_1_r. reflexivity.
    apply le_mult_r. setoid_rewrite <- Ord.from_nat_1. apply OrdArith.le_from_nat. auto.
  Qed.

  Lemma layer_drop :
    forall l m (LT : l < m) a b, (0 < b) -> (layer l a < layer m b)%ord.
  Proof.
    intros l m LT. induction LT; i.
    { apply layer_S_drop. auto. }
    etransitivity. eapply IHLT; eauto.
    apply layer_S_drop. auto.
  Qed.

  Lemma layer_drop_eq :
    forall l m (LE : l <= m) a, (0 < a) -> (layer l a <= layer m a)%ord.
  Proof.
    intros. inv LE.
    { reflexivity. }
    apply Ord.lt_le. apply layer_drop; lia.
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

  (* Variable ident_tgt : ID. *)
  Context {ident_tgt : ID}.
  Local Notation identTgtRA := (identTgtRA ident_tgt).
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

  Definition _liveness_obligation (k : nat) (l a : nat) (o : Ord.t) :=
    (⌜(o <= layer l a)%ord⌝ ∗ black k o)%I.

  Definition liveness_obligation (k : nat) (l : nat) :=
    (∃ (a : nat) (o : Ord.t), _liveness_obligation k l a o)%I.

  Definition progress_credit (k : nat) (l a : nat) :=
    white k (layer l a).

  Global Program Instance Persistent_liveness_obligation k l :
    Persistent (liveness_obligation k l).

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
    progress_credit k l c ⊢ progress_credit k l a ∗ progress_credit k l b.
  Proof.
    iIntros (LE) "PC".
    exploit PeanoNat.Nat.le_exists_sub. apply LE. i. des. subst c.
    iPoseProof (pc_split with "PC") as "[A B]".
    iPoseProof (pc_split with "B") as "[B C]".
    iFrame.
  Qed.

  Lemma pc_merge k l a b :
    (progress_credit k l a ∗ progress_credit k l b) ⊢ progress_credit k l (a + b).
  Proof.
    iIntros "[A B]". unfold progress_credit. iPoseProof (white_merge with "A B") as "W".
    iPoseProof (white_eq with "W") as "W". symmetry; apply layer_split. iFrame.
  Qed.

  Lemma pc_drop k l m (LE : l < m) :
    forall a b, (0 < b) ->
           progress_credit k m b ⊢ |==> progress_credit k l a.
  Proof.
    iIntros (? ? LT) "PC". iApply (pc_mon with "PC"). apply Ord.lt_le. apply layer_drop; auto.
  Qed.

  Lemma lo_pc_decr k l c o m a :
    (0 < a) ->
    (_liveness_obligation k l c o ∗ progress_credit k m a)
      ⊢ |==> ∃ o', (_liveness_obligation k l c o') ∗ ⌜(o' < o)%ord⌝.
  Proof.
    iIntros (LT) "[[% #LO] PC]".
    iMod (pc_mon _ 0 _ 1 _ with "PC") as "PC".
    { destruct (le_lt_eq_dec 0 m). lia.
      - apply Ord.lt_le. apply layer_drop; auto.
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

  Lemma alloc_obligation l a :
    ⊢ |==> (∃ k, liveness_obligation k l ∗ progress_credit k l a).
  Proof.
    iMod (alloc (layer l a)) as "[% [B W]]".
    iExists k. iFrame. iModIntro. iExists a, (layer l a). iFrame.
    auto.
  Qed.

  (** Definitions and rules for obligation links. *)

  Definition link k0 k1 l := amplifier k0 k1 (layer l 1).

  Global Program Instance Persistent_link k0 k1 l :
    Persistent (link k0 k1 l).

  Lemma link_new k0 k1 l m c :
    (liveness_obligation k0 l ∗ progress_credit k1 (1 + m + l) 1)
      ⊢ #=(edges_sat)=> (link k0 k1 m ∗ progress_credit k1 (m + l) c).
  Proof.
    iIntros "[(% & % & % & LD) PC]".
    iMod (white_mon with "PC") as "PC".
    { apply Ord.lt_le. apply (layer_drop (m+l) _). lia. auto. Unshelve. exact (a+c). }
    iPoseProof (white_eq with "PC") as "PC".
    { apply layer_split. }
    iPoseProof (white_split_eq with "PC") as "[PC RES]". iFrame.
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
    apply layer_drop_eq; auto.
  Qed.

  Lemma link_trans k0 k1 k2 l0 l1 :
    (link k0 k1 l0 ∗ link k1 k2 l1) ⊢ link k0 k2 (l1 + l0).
  Proof.
    iIntros "[L1 L2]". unfold link. iApply amplifier_mon.
    { rewrite layer_sep. reflexivity. }
    iApply (amplifier_trans with "L1"). iFrame.
  Qed.

  (** Definitions and rules for obligation duties. *)

  Definition duty {Id} {v} (p : Prism.t _ Id) (i : Id) ds : iProp :=
    duty v p i (map (fun '(k, l, f) => (k, layer l 1, f)) ds).

  Definition fairness_credit {Id} (p : Prism.t _ Id) (i : Id) : iProp := FairRA.white p i 1.

  Definition promise {Id} {v} (p : Prism.t _ Id) (i : Id) k l f : iProp :=
    correl v p i k (layer l 1) f.

  Global Program Instance Persistent_promise {Id} {v} p (i : Id) k l f :
    Persistent (promise (v:=v) p i k l f).

  Lemma promise_progress {Id} {v} (p : Prism.t _ Id) (i : Id) k l f :
    (promise p i k l f ∗ fairness_credit p i)
      ⊢ #=(arrows_sat v)=> progress_credit k l 1 ∨ (□ (prop v f)).
  Proof.
    iIntros "[#PR FC]". iPoseProof (correl_correlate with "PR FC") as "RES". iFrame.
  Qed.

  Lemma duty_add {Id} {v} (p : Prism.t _ Id) (i : Id) ds k l f :
    (duty p i ds ∗ progress_credit k (1 + l) 1)
      ⊢ (□ (prop v f -∗ □ prop v f)) =(arrows_sat v)=∗ duty p i ((k, l, f) :: ds).
  Proof.
    iIntros "[D PC] #F". iMod (duty_alloc with "D [PC] [F]") as "D".
    { unfold progress_credit. iPoseProof (white_eq with "PC") as "PC".
      { replace (1+l) with (l+1) by lia. rewrite layer_sep. rewrite layer_one_one. reflexivity. }
      iFrame.
    }
    { eauto. }
    iModIntro. iFrame.
  Qed.

  Lemma duty_promise {Id} {v} (p : Prism.t _ Id) (i : Id) ds k l (f : Vars v) :
    In (k, l, f) ds ->
    duty p i ds ⊢ promise p i k l f.
  Proof.
    iIntros (IN) "D". iApply duty_correl. 2: iFrame.
    apply (in_map (fun '(k0, l0, f0) => (k0, layer l0 1, f0))) in IN. auto.
  Qed.

  Lemma duty_fulfill {Id} {v} (p : Prism.t _ Id) (i : Id) ds k l f :
    (duty p i ((k, l, f) :: ds) ∗ prop v f)
      ⊢ #=(arrows_sat v)=> duty p i ds.
  Proof.
    iIntros "(DUTY & F)".
    iMod (duty_done with "DUTY F") as "D". iModIntro. iFrame.
  Qed.

  Lemma duty_permutation {Id} {v} (p : Prism.t _ Id) (i : Id) ds0 ds1 :
    (ds0 ≡ₚ ds1) -> duty (v:=v) p i ds0 ⊢ duty p i ds1.
  Proof.
    iIntros (P) "D". iApply duty_permutation. 2: iFrame.
    apply Permutation_map. auto.
  Qed.

  (** Obligation duties specialized for thread fairness. *)

  Definition thread_credit : iProp := FairRA.white_thread (S:=_).

  Definition thread_promise {v} k l f : iProp := correl_thread v k (layer l 1) f.

  Global Program Instance Persistent_thread_promise {v} k l f :
    Persistent (thread_promise (v:=v) k l f).

  Lemma tpromise_progress {v} k l f :
    (thread_promise k l f ∗ thread_credit)
      ⊢ #=(arrows_sat v)=> progress_credit k l 1 ∨ (□ (prop v f)).
  Proof.
    iIntros "[#PR FC]". iPoseProof (correl_thread_correlate with "PR FC") as "RES". iFrame.
  Qed.

  Lemma duty_tpromise {v} i ds k l (f : Vars v) :
    In (k, l, f) ds ->
    duty inlp i ds ⊢ thread_promise k l f.
  Proof.
    iIntros (IN) "D". iApply duty_correl_thread. 2: iFrame.
    apply (in_map (fun '(k0, l0, f0) => (k0, layer l0 1, f0))) in IN. auto.
  Qed.

  (** Additional definitions and rules. *)

  Definition progress_credits (l : list (nat * nat)) m a :=
    taxes (map (fun '(k, n) => (k, layer n 1)) l) (layer m a).

  Lemma pcs_nil m a : ⊢ progress_credits [] m a.
  Proof. iApply taxes_nil. Qed.

  Lemma pcs_perm l0 l1 m a :
    (l0 ≡ₚ l1) -> progress_credits l0 m a ⊢ progress_credits l1 m a.
  Proof.
    iIntros. iApply taxes_perm. 2: iFrame.
    apply Permutation_map; auto.
  Qed.

  Lemma pcs_merge_list l0 l1 m a :
    progress_credits l0 m a ∗ progress_credits l1 m a ⊢ progress_credits (l0 ++ l1) m a.
  Proof.
    iIntros "[A B]". unfold progress_credits. rewrite map_app.
    iApply taxes_combine. iFrame.
  Qed.

  Lemma pcs_split_list l0 l1 m a :
    progress_credits (l0 ++ l1) m a ⊢ progress_credits l0 m a ∗ progress_credits l1 m a.
  Proof.
    iIntros "A". unfold progress_credits. rewrite map_app.
    iApply taxes_split. iFrame.
  Qed.

  Lemma pcs_cons_unfold k l tl m a :
    progress_credits ((k, l) :: tl) m a ⊢ progress_credit k (l + m) a ∗ progress_credits tl m a.
  Proof.
    unfold progress_credits. iIntros "P". ss. unfold progress_credit.
    iPoseProof (taxes_cons_unfold with "P") as "[W T]". iFrame.
    iApply white_eq. 2: iFrame.
    rewrite ! layer_sep. reflexivity.
  Qed.

  Lemma pcs_cons_fold k l tl m a :
    progress_credit k (l + m) a ∗ progress_credits tl m a ⊢ progress_credits ((k, l) :: tl) m a.
  Proof.
    unfold progress_credits. iIntros "[PC PP]". ss. unfold progress_credit.
    iPoseProof (taxes_cons_fold with "[PC PP]") as "W". 2: iFrame.
    iFrame. iApply white_eq. 2: iFrame.
    rewrite ! layer_sep. reflexivity.
  Qed.

  Lemma pcs_decr l m :
    forall a b c, (a + b <= c) ->
             progress_credits l m c ⊢ |==> progress_credits l m a ∗ progress_credits l m b.
  Proof.
    intros. iIntros "PP". iMod (taxes_ord_split with "PP") as "[T1 T2]".
    2: iModIntro; iFrame.
    apply layer_split_le. lia.
  Qed.

  Lemma pcs_add l m :
    forall a b, progress_credits l m a ∗ progress_credits l m b ⊢ |==> progress_credits l m (a + b).
  Proof.
    intros. iIntros "PP". iPoseProof (taxes_ord_merge with "PP") as "PP".
    iApply taxes_ord_mon. 2: iFrame. rewrite layer_split. reflexivity.
  Qed.

  Lemma pcs_drop l m a (LT : 0 < a) :
    forall n b, (n < m) ->
           progress_credits l m a ⊢ |==> progress_credits l n b.
  Proof.
    iIntros (? ? LE) "PCS". iApply taxes_ord_mon. 2: iFrame.
    apply Ord.lt_le. apply layer_drop; auto.
  Qed.

  Lemma pcs_drop_le l m a (LT : 0 < a) :
    forall n, (n <= m) ->
         progress_credits l m a ⊢ |==> progress_credits l n a.
  Proof.
    iIntros (? LE) "PCS". iApply taxes_ord_mon. 2: iFrame.
    apply layer_drop_eq; auto.
  Qed.

  (** Additional definitions and rules. *)

  Definition _collection_credits k o (ps : list (nat * nat)) l :=
    collection_taxes k o (map (fun '(k, l) => (k, layer l 1)) ps) (layer l 1).

  Definition collection_credits k (ps : list (nat * nat)) l :=
    (∃ (o : Ord.t), _collection_credits k o ps l)%I.

  Lemma ccs_decr k o ps l :
    forall m a, (0 < a) ->
           (_collection_credits k o ps l ∗ progress_credit k m a)
             ⊢ #=> (∃ o', _collection_credits k o' ps l ∗ ⌜(o' < o)%ord⌝ ∗ progress_credits ps l 1).
  Proof.
    intros. iIntros "[COL PC]". 
    iMod (pc_mon _ 0 _ 1 _ with "PC") as "PC".
    { destruct (le_lt_eq_dec 0 m). lia.
      - apply Ord.lt_le. apply layer_drop; auto.
      - subst. rewrite ! layer_zero1. apply OrdArith.le_from_nat. lia.
    }
    iMod (collection_taxes_decr_one with "COL [PC]") as "[% (COL & % & TAX)]".
    { iApply white_eq. 2: iFrame. rewrite layer_zero1. reflexivity. }
    iExists o'. iFrame.
    iPureIntro. auto.
  Qed.

  Lemma ccs_make k l ps m c :
    (liveness_obligation k l ∗ progress_credits ps (1 + m + l) 1)
      ⊢ |==> (collection_credits k ps m ∗ progress_credits ps (m + l) c).
  Proof.
    iIntros "[(% & % & % & B) T]". iMod (pcs_drop _ _ _ _ (m+l) (a+c) with "T") as "T". lia.
    iMod (pcs_decr _ _ a c with "T") as "[T RES]". lia.
    iFrame. iMod (taxes_ord_mon with "T") as "T".
    { rewrite layer_sep. eapply Jacobsthal.le_mult_r. eapply H. }
    iPoseProof (collection_taxes_make with "[B T]") as "CT". iFrame.
    iModIntro. iExists _. iFrame.
    Unshelve. auto.
  Qed.

  (** Induction rules. *)

  Lemma lo_ind_gen k l (P : iProp) :
    (liveness_obligation k l)
      ⊢ (□ (∃ m a, (⌜(0 < a)⌝ -∗ progress_credit k m a ==∗ P) ==∗ P)) ==∗ P.
  Proof.
    iIntros "(%c & %o & LO)". iStopProof.
    pattern o. revert o. apply (well_founded_ind Ord.lt_well_founded). intros.
    iIntros "#LO #(% & % & IND)". iApply "IND". iIntros "% PC".
    iMod (lo_pc_decr with "[LO PC]") as "[% [#LO2 %]]". apply H0. iFrame. eauto.
    iClear "LO". iPoseProof (H with "LO2 [IND]") as "P". auto.
    2: iApply "P".
    { iExists m, a. auto. }
  Qed.

  Lemma lo_ind k l (P : iProp) :
    (liveness_obligation k l)
      ⊢ (□ (∃ m, (progress_credit k m 1 ==∗ P) ==∗ P)) ==∗ P.
  Proof.
    iIntros "#LO #[% IND]". iApply lo_ind_gen. eauto.
    iModIntro. iExists m, 1. iIntros "A". iApply "IND". iApply "A". auto.
  Qed.

  Lemma promise_ind {Id} {v} (p : Prism.t _ Id) (i : Id) k l m f (R : iProp) :
    (liveness_obligation k l ∗ promise p i k m f)
      ⊢ (□ ((fairness_credit p i =(arrows_sat v)=∗ (R ∨ (□ prop v f))) ==∗ R))
      ==∗ R.
  Proof.
    iIntros "[#LO #PR] #IND".
    iMod (lo_ind with "LO []") as "R". 2: iModIntro; iApply "R".
    iExists m. iModIntro. iIntros "IND2". iApply "IND". iIntros "FC".
    iMod (promise_progress with "[PR FC]") as "[PC | #P]".
    { iFrame. eauto. }
    { iMod ("IND2" with "PC") as "R". iModIntro. iFrame. }
    { iModIntro. iRight. auto. }
  Qed.

  Lemma promise_ind2 {Id} {v} (p : Prism.t _ Id) (i : Id) k l m f (R : iProp) :
    (liveness_obligation k l ∗ promise p i k m f)
      ⊢ ((□ ((fairness_credit p i =(arrows_sat v)=∗ R) ==∗ R))
           ∗ (□ ((□ prop v f) ==∗ R)))
      ==∗ R.
  Proof.
    iIntros "[#LO #PR] [#IND #BASE]".
    iApply promise_ind. eauto. iModIntro. iIntros "IH". iApply "IND". iIntros "FC".
    iMod ("IH" with "FC") as "[CASE | CASE]". iModIntro. iFrame.
    iMod ("BASE" with "CASE") as "RES". iModIntro. iFrame.
  Qed.

  Lemma tpromise_ind {v} k l m f (R : iProp) :
    (liveness_obligation k l ∗ thread_promise k m f)
      ⊢ (□ ((thread_credit =(arrows_sat v)=∗ (R ∨ (□ prop v f))) ==∗ R))
      ==∗ R.
  Proof.
    iIntros "[#LO #PR] #IND".
    iMod (lo_ind with "LO []") as "R". 2: iModIntro; iApply "R".
    iExists m. iModIntro. iIntros "IND2". iApply "IND". iIntros "FC".
    iMod (tpromise_progress with "[PR FC]") as "[PC | #P]".
    { iFrame. eauto. }
    { iMod ("IND2" with "PC") as "R". iModIntro. iFrame. }
    { iModIntro. iRight. auto. }
  Qed.

  Lemma tpromise_ind2 {v} k l m f (R : iProp) :
    (liveness_obligation k l ∗ thread_promise k m f)
      ⊢ ((□ ((thread_credit =(arrows_sat v)=∗ R) ==∗ R))
           ∗ (□ ((□ prop v f) ==∗ R)))
      ==∗ R.
  Proof.
    iIntros "[#LO #PR] [#IND #BASE]".
    iApply tpromise_ind. eauto. iModIntro. iIntros "IH". iApply "IND". iIntros "FC".
    iMod ("IH" with "FC") as "[CASE | CASE]". iModIntro. iFrame.
    iMod ("BASE" with "CASE") as "RES". iModIntro. iFrame.
  Qed.

  Lemma ccs_ind_gen k ps l (P : iProp) :
    (collection_credits k ps l)
      ⊢ (□ (∃ m a, (⌜(0 < a)⌝ -∗ progress_credit k m a ==∗ (progress_credits ps l 1 ∗ P)) ==∗ P))
      ==∗ P.
  Proof.
    iIntros "[%o CCS]". iStopProof.
    pattern o. revert o. apply (well_founded_ind Ord.lt_well_founded). intros.
    iIntros "CC #(% & % & IND)". iApply "IND". iIntros "% PC".
    iMod (ccs_decr with "[CC PC]") as "[% [CC2 [% PC2]]]". apply H0. iFrame.
    iPoseProof (H with "CC2 [IND]") as ">P". auto.
    2: iModIntro; iFrame.
    { iExists m, a. auto. }
  Qed.

  Lemma ccs_ind k ps l (P : iProp) :
    (collection_credits k ps l)
      ⊢ (□ (∃ m, (progress_credit k m 1 ==∗ (progress_credits ps l 1 ∗ P)) ==∗ P))
      ==∗ P.
  Proof.
    iIntros "CCS #[% IND]". iApply (ccs_ind_gen with "CCS").
    iModIntro. iExists m, 1. iIntros "A". iApply "IND". iApply "A". auto.
  Qed.

  Lemma ccs_ind2 k ps l (P : iProp) :
    (collection_credits k ps l)
      ⊢ (□ (∃ m, (progress_credit k m 1 ==∗ P) ==∗ (progress_credits ps l 1 -∗ P)))
      ==∗ (progress_credits ps l 1 -∗ P).
  Proof.
    iIntros "CCS #[% IND]". iMod (ccs_ind with "CCS []") as "RES".
    2:{ iModIntro. iApply "RES". }
    iModIntro. iExists m. iIntros "IND2". iApply "IND". iIntros "PC".
    iMod ("IND2" with "PC") as "[A B]". iModIntro. iApply ("B" with "A").
  Qed.

  Lemma ccs_promise_ind {Id} {v} (p : Prism.t _ Id) (i : Id) k ps l m f (R : iProp) :
    (collection_credits k ps l ∗ promise p i k m f)
      ⊢ (□ ((fairness_credit p i =(arrows_sat v)=∗ ((progress_credits ps l 1 ∗ R) ∨ (□ prop v f))) ==∗ R))
      ==∗ R.
  Proof.
    iIntros "[CC #PR] #IND". iMod (ccs_ind with "CC []") as "R". 2: iModIntro; iApply "R".
    iExists m. iModIntro. iIntros "IND2". iApply "IND". iIntros "FC".
    iMod (promise_progress with "[PR FC]") as "[PC | #P]".
    { iFrame. eauto. }
    { iMod ("IND2" with "PC") as "R". iModIntro. iFrame. }
    { iModIntro. iRight. auto. }
  Qed.

  Lemma ccs_promise_ind2 {Id} {v} (p : Prism.t _ Id) (i : Id) k ps l m f (R : iProp) :
    (collection_credits k ps l ∗ promise p i k m f)
      ⊢ (□ ((fairness_credit p i =(arrows_sat v)=∗ (R ∨ (□ prop v f))) ==∗ (progress_credits ps l 1 -∗ R)))
      ==∗ (progress_credits ps l 1 -∗ R).
  Proof.
    iIntros "[CC #PR] #IND". iMod (ccs_ind2 with "CC []") as "R". 2: iModIntro; iApply "R".
    iExists m. iModIntro. iIntros "IND2". iApply "IND". iIntros "FC".
    iMod (promise_progress with "[PR FC]") as "[PC | #P]".
    { iFrame. eauto. }
    { iMod ("IND2" with "PC") as "R". iModIntro. iFrame. }
    { iModIntro. iRight. auto. }
  Qed.

  Lemma ccs_tpromise_ind {v} k ps l m f (R : iProp) :
    (collection_credits k ps l ∗ thread_promise k m f)
      ⊢ (□ ((thread_credit =(arrows_sat v)=∗ ((progress_credits ps l 1 ∗ R) ∨ (□ prop v f))) ==∗ R))
      ==∗ R.
  Proof.
    iIntros "[CC #PR] #IND". iMod (ccs_ind with "CC []") as "R". 2: iModIntro; iApply "R".
    iExists m. iModIntro.  iIntros "IND2". iApply "IND". iIntros "FC".
    iMod (tpromise_progress with "[PR FC]") as "[PC | #P]".
    { iFrame. eauto. }
    { iMod ("IND2" with "PC") as "R". iModIntro. iFrame. }
    { iModIntro. iRight. auto. }
  Qed.

  Lemma ccs_tpromise_ind2 {v} k ps l m f (R : iProp) :
    (collection_credits k ps l ∗ thread_promise k m f)
      ⊢ (□ ((thread_credit =(arrows_sat v)=∗ (R ∨ (□ prop v f))) ==∗ (progress_credits ps l 1 -∗ R)))
      ==∗ (progress_credits ps l 1 -∗ R).
  Proof.
    iIntros "[CC #PR] #IND". iMod (ccs_ind2 with "CC []") as "R". 2: iModIntro; iApply "R".
    iExists m. iModIntro.  iIntros "IND2". iApply "IND". iIntros "FC".
    iMod (tpromise_progress with "[PR FC]") as "[PC | #P]".
    { iFrame. eauto. }
    { iMod ("IND2" with "PC") as "R". iModIntro. iFrame. }
    { iModIntro. iRight. auto. }
  Qed.

  (** Additional definitions and rules. *)

  Definition until_promise {Id} {v} (p : Prism.t _ Id) (i : Id) k l (f P : Vars v) :=
    (promise p i k l f ∗ ((prop v P) ∨ (□ (prop v f))))%I.

  Lemma until_promise_ind {Id} {v} (p : Prism.t _ Id) (i : Id) k l m f P (R : iProp) :
    (liveness_obligation k l ∗ until_promise p i k m f P)
      ⊢ (
        (□ (((fairness_credit p i ∗ until_promise p i k m f P) =(arrows_sat v)=∗ R) ==∗ ((prop v P) -∗ R)))
          ∗
        (□ ((□ prop v f) -∗ R))
      )
      ==∗ R.
  Proof.
    iIntros "[#LO [#PR C]] [#IND #BASE]". iDestruct "C" as "[P | #F]".
    { iPoseProof (promise_ind with "[] []") as "#IND2". eauto.
      2:{ iMod "IND2". iModIntro. iRevert "P". iApply "IND2". }
      iModIntro. iIntros "IND2". iApply "IND". iIntros "[FC [_ [P | #F]]]".
      { iMod ("IND2" with "FC") as "[A | B]".
        - iModIntro. iApply ("A" with "P").
        - iModIntro. iApply "BASE". auto.
      }
      { iModIntro. iApply "BASE". auto. }
    }
    { iModIntro. iApply "BASE". auto. }
  Qed.

  Lemma ccs_until_promise_ind {Id} {v} (p : Prism.t _ Id) (i : Id) k ps l m f P (R : iProp) :
    (collection_credits k ps l ∗ until_promise p i k m f P)
      ⊢ (
        (□ (((fairness_credit p i ∗ until_promise p i k m f P) =(arrows_sat v)=∗ R) ==∗ (progress_credits ps l 1 -∗ (prop v P) -∗ R)))
          ∗
        (□ ((□ prop v f) -∗ R))
      )
      ==∗ (progress_credits ps l 1 -∗ R).
  Proof.
    iIntros "[CC [#PR C]] [#IND #BASE]". iDestruct "C" as "[P | #F]".
    { iPoseProof (ccs_promise_ind2 with "[CC] []") as "IND2". iFrame; eauto.
      2:{ iMod "IND2". iModIntro. iIntros "PC". iRevert "PC P". iApply "IND2". }
      iModIntro. iIntros "IND2". iApply "IND". iIntros "[FC [_ [P | #F]]]".
      { iMod ("IND2" with "FC") as "[A | B]".
        - iModIntro. iApply ("A" with "P").
        - iModIntro. iApply "BASE". auto.
      }
      { iModIntro. iApply "BASE". auto. }
    }
    { iModIntro. iIntros. iApply "BASE". auto. }
  Qed.

  Lemma until_promise_make1 {Id} {v} (p : Prism.t _ Id) (i : Id) k l f P :
    (promise (v:=v) p i k l f ∗ prop v P) ⊢ until_promise p i k l f P.
  Proof.
    iIntros "(A & B)". unfold until_promise. iFrame.
  Qed.

  Lemma until_promise_make2 {Id} {v} (p : Prism.t _ Id) (i : Id) k l f P :
    (promise p i k l f ∗ □ (prop v f)) ⊢ until_promise p i k l f P.
  Proof.
    iIntros "(A & B)". unfold until_promise. iFrame.
  Qed.

  Lemma until_promise_get_promise {Id} {v} (p : Prism.t _ Id) (i : Id) k l f (P : Vars v) :
    until_promise p i k l f P ⊢ promise p i k l f.
  Proof.
    iIntros "(A & B)". iFrame.
  Qed.


  Definition until_thread_promise {v} k l (f P : Vars v) :=
    (thread_promise k l f ∗ ((prop v P) ∨ (□ (prop v f))))%I.

  Lemma until_tpromise_ind {v} k l m f P (R : iProp) :
    (liveness_obligation k l ∗ until_thread_promise k m f P)
      ⊢ (
        (□ (((thread_credit ∗ until_thread_promise k m f P) =(arrows_sat v)=∗ R) ==∗ ((prop v P) -∗ R)))
          ∗
        (□ ((□ prop v f) -∗ R))
      )
      ==∗ R.
  Proof.
    iIntros "[#LO [#PR C]] [#IND #BASE]". iDestruct "C" as "[P | #F]".
    { iPoseProof (tpromise_ind with "[] []") as "#IND2". eauto.
      2:{ iMod "IND2". iModIntro. iRevert "P". iApply "IND2". }
      iModIntro. iIntros "IND2". iApply "IND". iIntros "[FC [_ [P | #F]]]".
      { iMod ("IND2" with "FC") as "[A | B]".
        - iModIntro. iApply ("A" with "P").
        - iModIntro. iApply "BASE". auto.
      }
      { iModIntro. iApply "BASE". auto. }
    }
    { iModIntro. iApply "BASE". auto. }
  Qed.

  Lemma ccs_until_tpromise_ind {v} k ps l m f P (R : iProp) :
    (collection_credits k ps l ∗ until_thread_promise k m f P)
      ⊢ (
        (□ (((thread_credit ∗ until_thread_promise k m f P) =(arrows_sat v)=∗ R) ==∗ (progress_credits ps l 1 -∗ (prop v P) -∗ R)))
          ∗
        (□ ((□ prop v f) -∗ R))
      )
      ==∗ (progress_credits ps l 1 -∗ R).
  Proof.
    iIntros "[CC [#PR C]] [#IND #BASE]". iDestruct "C" as "[P | #F]".
    { iPoseProof (ccs_tpromise_ind2 with "[CC] []") as "IND2". iFrame; eauto.
      2:{ iMod "IND2". iModIntro. iIntros "PC". iRevert "PC P". iApply "IND2". }
      iModIntro. iIntros "IND2". iApply "IND". iIntros "[FC [_ [P | #F]]]".
      { iMod ("IND2" with "FC") as "[A | B]".
        - iModIntro. iApply ("A" with "P").
        - iModIntro. iApply "BASE". auto.
      }
      { iModIntro. iApply "BASE". auto. }
    }
    { iModIntro. iIntros. iApply "BASE". auto. }
  Qed.

  Lemma until_tpromise_make1 {v} k l f P :
    (thread_promise (v:=v) k l f ∗ prop v P) ⊢ until_thread_promise k l f P.
  Proof.
    iIntros "(A & B)". unfold until_thread_promise. iFrame.
  Qed.

  Lemma until_tpromise_make2 {v} k l f P :
    (thread_promise k l f ∗ □ (prop v f)) ⊢ until_thread_promise k l f P.
  Proof.
    iIntros "(A & B)". unfold until_thread_promise. iFrame.
  Qed.

  Lemma until_tpromise_get_tpromise {v} k l f (P : Vars v) :
    until_thread_promise k l f P ⊢ (thread_promise k l f).
  Proof.
    iIntros "(A & B)". iFrame.
  Qed.

End RULES.
Global Opaque link.

(** Notations. *)

Notation "'◆' [ k , l ]" :=
  (liveness_obligation k l) (at level 50, k, l at level 1, format "◆ [ k ,  l ]") : bi_scope.
Notation "'◇' [ k ]( l , a )" :=
  (progress_credit k l a) (at level 50, k, l, a at level 1, format "◇ [ k ]( l ,  a )") : bi_scope.
Notation "s '-(' l ')-' '◇' t" :=
  (link s t l) (at level 50, l, t at level 1, format "s  -( l )- ◇  t") : bi_scope.
Notation "'Duty' ( p ◬ i ) ds" :=
  (duty p i ds) (at level 50, p, i, ds at level 1, format "Duty ( p  ◬  i )  ds") : bi_scope.
Notation "'Duty' ( tid ) ds" :=
  (duty inlp tid ds) (at level 50, tid, ds at level 1, format "Duty ( tid )  ds") : bi_scope.
Notation "'€' ( p ◬ i )" :=
  (fairness_credit p i) (format "€ ( p  ◬  i )") : bi_scope.
Notation "'-(' p ◬ i ')-[' k '](' l ')-' '◇' f" :=
  (promise p i k l f) (at level 50, k, l, p, i at level 1, format "-( p  ◬  i )-[ k ]( l )- ◇  f") : bi_scope.
Notation "'€'" :=
  (thread_credit) : bi_scope.
Notation "'-[' k '](' l ')-' '◇' f" :=
  (thread_promise k l f) (at level 50, k, l at level 1, format "-[ k ]( l )- ◇  f") : bi_scope.
Notation "'◇' { ps }( m , a )" :=
  (progress_credits ps m a) (at level 50, ps, m, a at level 1, format "◇ { ps }( m ,  a )") : bi_scope.
Notation "⦃ '◆' [ k ] & '◇' { ps }( l )⦄"
  := (collection_credits k ps l) (at level 50, k, ps, l at level 1, format "⦃ ◆ [ k ]  &  ◇ { ps }( l )⦄") : bi_scope.
Notation "P '-U-(' p ◬ i ')-[' k '](' l ')-' '◇' f" :=
  (until_promise p i k l f P) (at level 50, k, l, p, i at level 1, format "P  -U-( p  ◬  i )-[ k ]( l )- ◇  f") : bi_scope.
Notation "P '-U-[' k '](' l ')-' '◇' f" :=
  (until_thread_promise k l f P) (at level 50, k, l at level 1, format "P  -U-[ k ]( l )- ◇  f") : bi_scope.



Section ELI.
  (** Environment Liveness Invariants *)

  Context {ident_tgt : ID}.
  Local Notation identTgtRA := (identTgtRA ident_tgt).
  Context `{Vars : nat -> Type}.
  Local Notation ArrowRA := (@ArrowRA ident_tgt Vars).

  Context `{Σ : GRA.t}.
  Context `{Invs : @IInvSet Σ Vars}.
  Context `{OWNERA : @GRA.inG OwnERA Σ}.
  Context `{OWNDRA : @GRA.inG OwnDRA Σ}.
  Context `{IINVSETRA : @GRA.inG (IInvSetRA Vars) Σ}.
  Context `{IDENTTGT : @GRA.inG identTgtRA Σ}.
  Context `{OBLGRA : @GRA.inG ObligationRA.t Σ}.
  Context `{EDGERA : @GRA.inG EdgeRA Σ}.
  Context `{ARROWSHOTRA : @GRA.inG ArrowShotRA Σ}.
  Context `{ARROWRA : @GRA.inG ArrowRA Σ}.

  (* Assumes one linearization point. *)
  Fixpoint env_live_inv (n : nat) (x : nat) E (k : nat) {v} (A T : Vars v) : iProp :=
    match n with
    | O => ⌜False⌝%I
    | S m =>
        □(∃ (P : Vars v),
             (prop _ P)
               ∗
               ((prop _ P ∗ €)
                  -∗ (prop _ A)
                  =| x |=( fairI (ident_tgt:=ident_tgt) x )={ E }=∗ ((prop _ A ∗ ◇[k](0, 1)) ∨ (prop _ A ∗ @env_live_inv m x E k v A T) ∨ (prop _ T))))%I
    end.

  Lemma eli_lo_ind k l n x E v (A T : Vars v) (Q : iProp) :
    (v <= x) ->
    (◆[k, l])
      ⊢
      (□((€ -∗ (prop _ A) =|x|=(fairI (ident_tgt:=ident_tgt) x)={E}=∗ Q) -∗ (prop _ A) =|x|=(fairI (ident_tgt:=ident_tgt) x)={E}=∗ Q))
      -∗
      ((prop _ T) =|x|=(fairI (ident_tgt:=ident_tgt) x)={E}=∗ Q)
      -∗
      ((prop _ A ∗ @env_live_inv n x E k v A T) =|x|=(fairI (ident_tgt:=ident_tgt) x)={E}=∗ Q)
  .
  Proof.
    (* Outer induction. *)
    iIntros (LT). pattern n. induction n.
    { iIntros "_ _ TERM [_ F]". ss. }
    iIntros "(%c & %o & #LO)".
    (* Inner induction. *)
    iStopProof. pattern o. revert o. apply (well_founded_ind Ord.lt_well_founded). intros o IHo.
    iIntros "#LO #IH TERM [AP ELI]".
    iEval (simpl) in "ELI". iPoseProof "ELI" as "(%P & #PP & #ELI)".
    iApply ("IH" with "[TERM] AP"). iIntros "FC AP".
    iMod ("ELI" with "[FC] AP") as "[(PA & PCk) | [(PA & ELI2) | PT]]".
    { iFrame. eauto. }
    { (* Prove with the inner induction. *)
      iMod (lo_pc_decr with "[PCk]") as "(%o' & #LO' & %LTo)".
      2:{ iSplitR; iFrame. eauto. }
      lia.
      specialize (IHo o' LTo).
      iApply (IHo with "LO' IH TERM [-]"). iFrame. iEval simpl.
      iModIntro. iExists P. iSplitL; eauto.
    }
    { (* Prove with the outer induction. *)
      iPoseProof (IHn with "[] IH TERM") as "IHn".
      { iExists _, _. eauto. }
      iSpecialize ("IHn" with "[PA ELI2]").
      iFrame. iFrame.
    }
    { (* Reached the target state T. *)
      iApply ("TERM" with "PT").
    }
  Qed.

  Lemma ELI_persistent n x E k v (A T : Vars v) :
    (@env_live_inv n x E k v A T) -∗ □(@env_live_inv n x E k v A T).
  Proof.
    destruct n; simpl; eauto.
  Qed.

  Global Program Instance Persistent_ELI n x E k v (A T : Vars v) :
    Persistent (@env_live_inv n x E k v A T).
  Next Obligation.
    iIntros "ELI". iPoseProof (ELI_persistent with "ELI") as "ELI". auto.
  Qed.

End ELI.
