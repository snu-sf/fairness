From sflib Require Import sflib.
From Fairness Require Import WFLibLarge Mod Optics.
From Fairness Require Import PCM IPM IPropAux.
From Fairness Require Import RegionRA.
Require Import Coq.Classes.RelationClasses.
From Fairness Require Import Axioms.
Require Import Program.
From Fairness Require Import FairnessRA IndexedInvariants.
From Fairness Require Export ObligationRA SimDefaultRA.
Require Export Nat.

Local Instance frame_exist_instantiate_disabled :
FrameInstantiateExistDisabled := {}.

Notation "'ω'" := Ord.omega.

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
    forall l m (LE : l <= m) a, (layer l a <= layer m a)%ord.
  Proof.
    intros. destruct a.
    { rewrite ! layer_zero2. reflexivity. }
    inv LE.
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
  Notation iProp := (iProp Σ) (only parsing).

  Import ObligationRA.

  (** Definitions and Rules for liveness obligations. *)

  Definition _liveness_obligation (k : nat) (l a : nat) (o : Ord.t) :=
    (⌜(o <= layer l a)%ord⌝ ∗ black k o)%I.

  Definition liveness_obligation_fine (k : nat) (l a : nat) :=
    (∃ (o : Ord.t), _liveness_obligation k l a o)%I.

  Definition liveness_obligation (k : nat) (l : nat) :=
    (∃ (a : nat), liveness_obligation_fine k l a)%I.

  Definition progress_credit (k : nat) (l a : nat) :=
    white k (layer l a).

  Definition pending_obligation (k : nat) (q : Qp) :=
    pending k q.

  Definition active_obligation (k : nat) :=
    shot k.

  Global Instance Persistent_liveness_obligation_fine k l a :
    Persistent (liveness_obligation_fine k l a).
  Proof. apply _. Qed.

  Global Instance Persistent_liveness_obligation k l :
    Persistent (liveness_obligation k l).
  Proof. apply _. Qed.

  Global Instance Persistent_active_obligation k :
    Persistent (active_obligation k).
  Proof. apply _. Qed.

  Lemma pending_active k
    :
    (pending_obligation k 1)
      -∗
      #=> (active_obligation k).
  Proof.
    apply pending_shot.
  Qed.

  Lemma pending_not_active k q
    :
    (pending_obligation k q)
      -∗
      (active_obligation k)
      -∗
      False.
  Proof.
    apply pending_not_shot.
  Qed.

  Lemma pending_sum k q0 q1
    :
    (pending_obligation k q0)
      -∗
      (pending_obligation k q1)
      -∗
      (pending_obligation k (q0 + q1)%Qp).
  Proof.
    apply pending_sum.
  Qed.

  Lemma pending_wf k q
    :
    (pending_obligation k q)
      -∗
      (⌜(q ≤ 1)%Qp⌝).
  Proof.
    apply pending_wf.
  Qed.

  Lemma pending_split k q0 q1
    :
    (pending_obligation k (q0 + q1)%Qp)
      -∗
      (pending_obligation k q0 ∗ pending_obligation k q1).
  Proof.
    apply pending_split.
  Qed.

  Lemma lo_mon k l1 l2 :
    (l1 <= l2) ->
    liveness_obligation k l1 ⊢ liveness_obligation k l2.
  Proof.
    unfold liveness_obligation. iIntros (LAY) "(% & % & %LE1 & OB)".
    iExists a, o. iSplit.
    { iPureIntro. etransitivity. eauto. apply layer_drop_eq. auto. }
    iFrame.
  Qed.

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

  Lemma alloc_obligation_fine l a :
    ⊢ |==> (∃ k, liveness_obligation_fine k l a ∗ progress_credit k l a ∗ pending_obligation k 1).
  Proof.
    iMod (alloc (layer l a)) as "[% (B & W & P)]".
    iExists k. iFrame. iModIntro. iExists (layer l a). iFrame.
    auto.
  Qed.

  Lemma alloc_obligation l a :
    ⊢ |==> (∃ k, liveness_obligation k l ∗ progress_credit k l a ∗ pending_obligation k 1).
  Proof.
    iMod (alloc_obligation_fine l a) as "(% & LO & PC & PO)". iExists k. iModIntro. iFrame.
    iExists a. iFrame.
  Qed.

  (** Definitions and rules for obligation links. *)

  Definition link k0 k1 l := amplifier k0 k1 (layer l 1).

  Global Instance Persistent_link k0 k1 l :
    Persistent (link k0 k1 l).
  Proof. apply _. Qed.

  Lemma link_new_fine k0 k1 l a m :
    (liveness_obligation_fine k0 l a ∗ progress_credit k1 (m + l) a)
      ⊢ #=(edges_sat)=> (link k0 k1 m).
  Proof.
    iIntros "[(% & % & LD) PC]".
    iPoseProof (white_eq with "PC") as "PC".
    { apply layer_sep. }
    iPoseProof (black_mon with "LD") as "LD".
    { apply H. }
    iMod (amplifier_intro with "LD PC") as "AMP".
    iModIntro. iFrame.
  Qed.

  Lemma link_new k0 k1 l m c :
    (liveness_obligation k0 l ∗ progress_credit k1 (1 + m + l) 1)
      ⊢ #=(edges_sat)=> (link k0 k1 m ∗ progress_credit k1 (m + l) c).
  Proof.
    iIntros "[(% & LD) PC]".
    iMod (white_mon with "PC") as "PC".
    { apply Ord.lt_le. apply (layer_drop (m+l) _). lia. auto. Unshelve. exact (a+c). }
    iPoseProof (white_eq with "PC") as "PC".
    { apply layer_split. }
    iPoseProof (white_split_eq with "PC") as "[PC RES]". iFrame.
    iApply (link_new_fine with "[LD PC]"). iFrame.
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

  Definition delayed_promise {Id} {v} (p : Prism.t _ Id) (i : Id) k l f : iProp :=
    delay v p i k (layer l 1) f.

  Definition promise {Id} {v} (p : Prism.t _ Id) (i : Id) k l f : iProp :=
    correl v p i k (layer l 1) f.

  Global Instance Persistent_delayed_promise {Id} {v} p (i : Id) k l f :
    Persistent (delayed_promise (v:=v) p i k l f).
  Proof. apply _. Qed.

  Global Instance Persistent_promise {Id} {v} p (i : Id) k l f :
    Persistent (promise (v:=v) p i k l f).
  Proof. apply _. Qed.

  Lemma activate_promise {Id} {v} (p : Prism.t _ Id) (i : Id) k c (F : Vars v)
    :
    (delayed_promise p i k c F)
      -∗
      (pending_obligation k (1/2))
      -∗
      (#=(arrows_sat v)=> (promise p i k c F) ∗ (active_obligation k)).
  Proof.
    iIntros "#DP PO". iMod (delay_shot with "DP PO") as "[_ #S]".
    iPoseProof (delay_to_correl with "DP S") as "P". iModIntro. auto.
  Qed.

  Lemma unfold_promise {Id} {v} (p : Prism.t _ Id) (i : Id) k c (F : Vars v)
    :
    (promise p i k c F)
      -∗
      (delayed_promise p i k c F ∗ active_obligation k).
  Proof.
    iIntros "P". iPoseProof (unfold_correl with "P") as "A". iFrame.
  Qed.

  Lemma promise_progress {Id} {v} (p : Prism.t _ Id) (i : Id) k l f :
    (promise p i k l f ∗ fairness_credit p i)
      ⊢ #=(arrows_sat v)=> progress_credit k l 1 ∨ (□ (prop v f)).
  Proof.
    iIntros "[#PR FC]". iPoseProof (correl_correlate with "PR FC") as "RES". iFrame.
  Qed.

  Lemma duty_add {Id} {v} (p : Prism.t _ Id) (i : Id) ds k l f :
    (duty p i ds ∗ progress_credit k (1 + l) 1 ∗ pending_obligation k (1/2))
      ⊢ (□ (prop v f -∗ □ prop v f)) =(arrows_sat v)=∗ duty p i ((k, l, f) :: ds).
  Proof.
    iIntros "[D [PC PO]] #F". iMod (duty_alloc with "D [PC] PO [F]") as "D".
    { unfold progress_credit. iPoseProof (white_eq with "PC") as "PC".
      { replace (1+l) with (l+1) by lia. rewrite layer_sep. rewrite layer_one_one. reflexivity. }
      iFrame.
    }
    { eauto. }
    iModIntro. iFrame.
  Qed.

  Lemma duty_delayed_promise {Id} {v} (p : Prism.t _ Id) (i : Id) ds k l (f : Vars v) :
    In (k, l, f) ds ->
    duty p i ds ⊢ delayed_promise p i k l f.
  Proof.
    iIntros (IN) "D". iApply duty_delay. 2: iFrame.
    apply (in_map (fun '(k0, l0, f0) => (k0, layer l0 1, f0))) in IN. auto.
  Qed.

  Lemma duty_promise {Id} {v} (p : Prism.t _ Id) (i : Id) ds k l (f : Vars v) :
    In (k, l, f) ds ->
    duty p i ds ⊢ active_obligation k -∗ promise p i k l f.
  Proof.
    iIntros (IN) "D". iApply duty_correl. 2: iFrame.
    apply (in_map (fun '(k0, l0, f0) => (k0, layer l0 1, f0))) in IN. auto.
  Qed.

  Lemma duty_fulfill {Id} {v} (p : Prism.t _ Id) (i : Id) ds k l f :
    (duty p i ((k, l, f) :: ds) ∗ prop v f ∗ active_obligation k)
      ⊢ #=(arrows_sat v)=> duty p i ds.
  Proof.
    iIntros "(DUTY & F & S)".
    iMod (duty_done with "DUTY S F") as "D". iModIntro. iFrame.
  Qed.

  Lemma duty_permutation {Id} {v} (p : Prism.t _ Id) (i : Id) ds0 ds1 :
    (ds0 ≡ₚ ds1) -> duty (v:=v) p i ds0 ⊢ duty p i ds1.
  Proof.
    iIntros (P) "D". iApply duty_permutation. 2: iFrame.
    apply Permutation_map. auto.
  Qed.

  (** Obligation duties specialized for thread fairness. *)

  Definition thread_credit : iProp := FairRA.white_thread (S:=_).

  Definition thread_delayed_promise {v} k l f : iProp := delay_thread v k (layer l 1) f.

  Definition thread_promise {v} k l f : iProp := correl_thread v k (layer l 1) f.

  Global Instance Persistent_thread_delayed_promise {v} k l f :
    Persistent (thread_delayed_promise (v:=v) k l f).
  Proof. apply _. Qed.

  Global Instance Persistent_thread_promise {v} k l f :
    Persistent (thread_promise (v:=v) k l f).
  Proof. apply _. Qed.

  Lemma activate_tpromise {v} k c (F : Vars v)
    :
    (thread_delayed_promise k c F)
      -∗
      (pending_obligation k (1/2))
      -∗
      (#=(arrows_sat v)=> (thread_promise k c F) ∗ (active_obligation k)).
  Proof.
    iIntros "#DP PO". iMod (delay_thread_shot with "DP PO") as "[_ #S]".
    iPoseProof (delay_to_correl_thread with "DP S") as "P". iModIntro. auto.
  Qed.

  Lemma unfold_tpromise {v} k c (F : Vars v)
    :
    (thread_promise k c F)
      -∗
      (thread_delayed_promise k c F ∗ active_obligation k).
  Proof.
    iIntros "P". iPoseProof (unfold_correl_thread with "P") as "A". iFrame.
  Qed.

  Lemma tpromise_progress {v} k l f :
    (thread_promise k l f ∗ thread_credit)
      ⊢ #=(arrows_sat v)=> progress_credit k l 1 ∨ (□ (prop v f)).
  Proof.
    iIntros "[#PR FC]". iPoseProof (correl_thread_correlate with "PR FC") as "RES". iFrame.
  Qed.

  Lemma duty_delayed_tpromise {v} i ds k l (f : Vars v) :
    In (k, l, f) ds ->
    duty inlp i ds ⊢ thread_delayed_promise k l f.
  Proof.
    iIntros (IN) "D". iApply duty_delay_thread. 2: iFrame.
    apply (in_map (fun '(k0, l0, f0) => (k0, layer l0 1, f0))) in IN. auto.
  Qed.

  Lemma duty_tpromise {v} i ds k l (f : Vars v) :
    In (k, l, f) ds ->
    duty inlp i ds ⊢ active_obligation k -∗ thread_promise k l f.
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

  Lemma pcs_decr {l m} :
    forall {c} a b, (a + b <= c) ->
             progress_credits l m c ⊢ |==> progress_credits l m a ∗ progress_credits l m b.
  Proof.
    intros. iIntros "PP". iMod (taxes_ord_split with "PP") as "[T1 T2]".
    2: iModIntro; iFrame.
    apply layer_split_le. lia.
  Qed.

  Lemma pcs_add {l m} :
    forall a b, progress_credits l m a ∗ progress_credits l m b ⊢ |==> progress_credits l m (a + b).
  Proof.
    intros. iIntros "PP". iPoseProof (taxes_ord_merge with "PP") as "PP".
    iApply taxes_ord_mon. 2: iFrame. rewrite layer_split. reflexivity.
  Qed.

  Lemma pcs_drop {l m a} :
    forall n b, (0 < a) → (n < m) ->
           progress_credits l m a ⊢ |==> progress_credits l n b.
  Proof.
    iIntros (? ? LT LE) "PCS". iApply taxes_ord_mon. 2: iFrame.
    apply Ord.lt_le. apply layer_drop; auto.
  Qed.

  Lemma pcs_drop_le {l m a} :
    forall n, (0 < a) → (n <= m) ->
         progress_credits l m a ⊢ |==> progress_credits l n a.
  Proof.
    iIntros (? LT LE) "PCS". iApply taxes_ord_mon. 2: iFrame.
    apply layer_drop_eq; auto.
  Qed.

  Definition progress_pendings (l : list (nat * Qp)) := pends l.

  Lemma pps_nil : ⊢ progress_pendings [].
  Proof. iApply pends_nil. Qed.

  Lemma pps_perm l0 l1 :
    (l0 ≡ₚ l1) -> progress_pendings l0 ⊢ progress_pendings l1.
  Proof.
    iIntros. iApply pends_perm. 2: iFrame. auto.
  Qed.

  Lemma pps_merge_list l0 l1 :
    progress_pendings l0 ∗ progress_pendings l1 ⊢ progress_pendings (l0 ++ l1).
  Proof.
    iIntros "[A B]". unfold progress_pendings. iApply pends_combine. iFrame.
  Qed.

  Lemma pps_split_list l0 l1 :
    progress_pendings (l0 ++ l1) ⊢ progress_pendings l0 ∗ progress_pendings l1.
  Proof.
    iIntros "A". unfold progress_pendings. iApply pends_split. iFrame.
  Qed.

  Lemma pps_cons_unfold k q tl :
    progress_pendings ((k, q) :: tl) ⊢ pending_obligation k q ∗ progress_pendings tl.
  Proof.
    unfold progress_pendings. iIntros "P". ss.
  Qed.

  Lemma pps_cons_fold k q tl :
    pending_obligation k q ∗ progress_pendings tl ⊢ progress_pendings ((k, q) :: tl).
  Proof.
    unfold progress_pendings. iIntros "[PC PP]".
    iPoseProof (pends_cons_fold with "[PC PP]") as "W". 2: iFrame. iFrame.
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

  Lemma ccs_make_fine k l a ps m :
    (liveness_obligation_fine k l a ∗ progress_credits ps (m + l) a)
      ⊢ |==> (collection_credits k ps m).
  Proof.
    iIntros "[(% & % & B) T]".
    iMod (taxes_ord_mon with "T") as "T".
    { rewrite layer_sep. eapply Jacobsthal.le_mult_r. eapply H. }
    iPoseProof (collection_taxes_make with "[B T]") as "CT". iFrame.
    iModIntro. iExists _. iFrame.
  Qed.

  Lemma ccs_make k l ps m c :
    (liveness_obligation k l ∗ progress_credits ps (1 + m + l) 1)
      ⊢ |==> (collection_credits k ps m ∗ progress_credits ps (m + l) c).
  Proof.
    iIntros "[(% & B) T]". iMod (pcs_drop (m+l) (a+c) with "T") as "T"; [lia..|].
    iMod (pcs_decr a c with "T") as "[T RES]". lia. iFrame.
    iApply (ccs_make_fine with "[B T]"). iFrame.
  Qed.

  (** Induction rules. *)

  Lemma lo_ind_gen_fine k l c (P : iProp) :
    (liveness_obligation_fine k l c)
      ⊢ (□ (∃ m a, (⌜(0 < a)⌝ -∗ progress_credit k m a ==∗ P) ==∗ P)) ==∗ P.
  Proof.
    iIntros "(%o & #LO) #(% & % & IND)".
    iInduction (o) as [o] "IH" using (well_founded_ind Ord.lt_well_founded).
    iApply "IND". iIntros "% PC".
    iMod (lo_pc_decr with "[LO PC]") as "[% [#LO2 %]]". apply H. iFrame. eauto.
    iClear "LO". by iApply ("IH" with "[%] LO2").
  Qed.

  Lemma lo_ind_fine k l c (P : iProp) :
    (liveness_obligation_fine k l c)
      ⊢ (□ (∃ m, (progress_credit k m 1 ==∗ P) ==∗ P)) ==∗ P.
  Proof.
    iIntros "#LO #[% IND]". iApply lo_ind_gen_fine. eauto.
    iModIntro. iExists m, 1. iIntros "A". iApply "IND". iApply "A". auto.
  Qed.

  Lemma lo_ind_gen k l (P : iProp) :
    (liveness_obligation k l)
      ⊢ (□ (∃ m a, (⌜(0 < a)⌝ -∗ progress_credit k m a ==∗ P) ==∗ P)) ==∗ P.
  Proof.
    iIntros "(%c & %o & LO)". iApply lo_ind_gen_fine. iExists _. iFrame.
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
    iIntros "[%o CC] #(% & % & IND)".
    iInduction (o) as [o] "IH" using (well_founded_ind Ord.lt_well_founded).
    iApply "IND". iIntros "% PC".
    iMod (ccs_decr with "[CC PC]") as "[% [CC2 [% $]]]". apply H. iFrame.
    by iApply ("IH" with "[%] CC2").
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
Notation "'◆' [ k , l , n ]" :=
  (liveness_obligation_fine k l n) (at level 50, k, l, n at level 1, format "◆ [ k ,  l ,  n ]") : bi_scope.
Notation "'◇' [ k ]( l , a )" :=
  (progress_credit k l a) (at level 50, k, l, a at level 1, format "◇ [ k ]( l ,  a )") : bi_scope.
Notation "'⧖' [ k , q ]" :=
  (pending_obligation k q) (at level 50, k, q at level 1, format "⧖ [ k ,  q ]") : bi_scope.
Notation "'⋈' [ k ]" :=
  (active_obligation k) (at level 50, k at level 1, format "⋈ [ k ]") : bi_scope.
Notation "s '-(' l ')-' '◇' t" :=
  (link s t l) (at level 50, l, t at level 1, format "s  -( l )- ◇  t") : bi_scope.
Notation "'Duty' ( p ◬ i ) ds" :=
  (duty p i ds) (at level 50, p, i, ds at level 1, format "Duty ( p  ◬  i )  ds") : bi_scope.
Notation "'Duty' ( tid ) ds" :=
  (duty inlp tid ds) (at level 50, tid, ds at level 1, format "Duty ( tid )  ds") : bi_scope.
Notation "'€' ( p ◬ i )" :=
  (fairness_credit p i) (format "€ ( p  ◬  i )") : bi_scope.
Notation "'-(' p ◬ i ')-[' k '](' l ')-' '⧖' f" :=
  (delayed_promise p i k l f) (at level 50, k, l, p, i at level 1, format "-( p  ◬  i )-[ k ]( l )- ⧖  f") : bi_scope.
Notation "'-(' p ◬ i ')-[' k '](' l ')-' '◇' f" :=
  (promise p i k l f) (at level 50, k, l, p, i at level 1, format "-( p  ◬  i )-[ k ]( l )- ◇  f") : bi_scope.
Notation "'€'" :=
  (thread_credit) : bi_scope.
Notation "'-[' k '](' l ')-' '⧖' f" :=
  (thread_delayed_promise k l f) (at level 50, k, l at level 1, format "-[ k ]( l )- ⧖  f") : bi_scope.
Notation "'-[' k '](' l ')-' '◇' f" :=
  (thread_promise k l f) (at level 50, k, l at level 1, format "-[ k ]( l )- ◇  f") : bi_scope.
Notation "'◇' { ps }( m , a )" :=
  (progress_credits ps m a) (at level 50, ps, m, a at level 1, format "◇ { ps }( m ,  a )") : bi_scope.
Notation "'⧖' { ps }" :=
  (progress_pendings ps) (at level 50, ps at level 1, format "⧖ { ps }") : bi_scope.
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
  Notation iProp := (iProp Σ) (only parsing).

  Definition env_live_chain0 (x : nat) E (k : nat) {v} (A T : Vars v) : iProp :=
    □(€ -∗ prop _ A
          =|x|=(fairI (ident_tgt:=ident_tgt) x)={E}=∗ ((prop _ A ∗ ◇[k](0, 1))
                                                       ∨ (prop _ T))
     ).

  Fixpoint env_live_chain (n : nat) (x : nat) E (k l : nat) {v} (A T : Vars v) : iProp :=
    match n with
    | O => env_live_chain0 x E k A T
    | S m =>
      □(€ -∗ prop _ A
        =|x|=(fairI (ident_tgt:=ident_tgt) x)={E}=∗
        ((prop _ A ∗ ◇[k](0, 1))
          ∨ prop _ T
          ∨ (prop _ A
              ∗ (∃ k' l' B,
                  ◆[k', l']
                  ∗ ⌜l' <= l⌝
                  ∗ (□ (prop _ B
                        =|x|=(fairI (ident_tgt:=ident_tgt) x)={E}=∗
                        (prop _ A ∗ (=|x|=(fairI (ident_tgt:=ident_tgt) x)={E}=> (prop _ A =|x|=(fairI (ident_tgt:=ident_tgt) x)={E}=∗ prop _ B)))))
                  ∗ @env_live_chain0 x E k' v A B
                  ∗ @env_live_chain m x E k l v B T)))
       )
    end.

  Global Instance Persistent_ELC0 x E k v (A T : Vars v) :
    Persistent (@env_live_chain0 x E k v A T).
  Proof. apply _. Qed.

  Lemma ELC_persistent n x E k l v (A T : Vars v) :
    (@env_live_chain n x E k l v A T) -∗ □(@env_live_chain n x E k l v A T).
  Proof.
    destruct n; simpl; eauto.
  Qed.

  Local Hint Extern 100 (Persistent (match ?x with _ => _ end)) => destruct x: typeclass_instances.

  Global Instance Persistent_ELC n x E k l v (A T : Vars v) :
    Persistent (@env_live_chain n x E k l v A T).
  Proof. induction n; apply _. Qed.

  Lemma elc0_lo_ind k l x E v (A T : Vars v) (Q : iProp) :
    v <= x ->
    ◆[k, l]
      ⊢
      (□((€ -∗ prop _ A =|x|=(fairI (ident_tgt:=ident_tgt) x)={E}=∗ Q) -∗ prop _ A =|x|=(fairI (ident_tgt:=ident_tgt) x)={E}=∗ Q))
      -∗
      (prop _ T =|x|=(fairI (ident_tgt:=ident_tgt) x)={E}=∗ Q)
      -∗
      (prop _ A ∗ @env_live_chain0 x E k v A T) =|x|=(fairI (ident_tgt:=ident_tgt) x)={E}=∗ Q
  .
  Proof.
    intros. iIntros "(%c & %o & #LO) #IH TERM [PA #ELI]".
    (* Induction. *)
    iInduction (o) as [o] "IHo" using (well_founded_ind Ord.lt_well_founded).
    iApply ("IH" with "[TERM] PA"). iIntros "FC PA".
    iMod ("ELI" with "FC PA") as "[(PA & PCk) | PT]".
    { (* Prove with the induction. *)
      iMod (lo_pc_decr with "[$PCk //]") as "(%o' & #LO' & %LTo)"; [lia|].
      by iApply ("IHo" with "[%] LO' TERM PA").
    }
    { (* Reached the target state T. *)
      iApply ("TERM" with "PT").
    }
  Qed.

  Lemma elc_lo_ind n k l x E v (A T : Vars v) (Q : iProp) :
    (v <= x) ->
    (◆[k, l])
      ⊢
      (□((€ -∗ (prop _ A) =|x|=(fairI (ident_tgt:=ident_tgt) x)={E}=∗ Q) -∗ (prop _ A) =|x|=(fairI (ident_tgt:=ident_tgt) x)={E}=∗ Q))
      -∗
      ((prop _ T) =|x|=(fairI (ident_tgt:=ident_tgt) x)={E}=∗ Q)
      -∗
      ((prop _ A ∗ @env_live_chain n x E k l v A T) =|x|=(fairI (ident_tgt:=ident_tgt) x)={E}=∗ Q)
  .
  Proof.
    iIntros (LE) "(%c & %o & #LO) #IH TERM [PA #ELI]".
    iInduction (n) as [|n] "IHn" forall (A) "IH".
    { iSimpl. iApply (elc0_lo_ind with "[#] IH TERM"); auto. iExists _,_. iFrame "LO". }
    (* Inner induction. *)
    iInduction (o) as [o] "IHo" using (well_founded_ind Ord.lt_well_founded).
    iApply ("IH" with "[TERM] PA"). iIntros "FC PA".
    iMod ("ELI" with "FC PA") as "[(PA & PCk) | [PT | (PA & % & % & % & #LO' & %LAY & #KNOW1 & #ELI' & #ELI2)]]".
    { (* Prove with the inner induction. *)
      iMod (lo_pc_decr with "[$PCk //]") as "(%o' & #LO' & %LTo)"; [lia|].
      by iApply ("IHo" with "[%] LO' TERM PA").
    }
    { (* Reached the target state T. *)
      iApply ("TERM" with "PT").
    }
    { (* Prove with the outer induction. *)
      iApply (elc0_lo_ind with "LO' IH [TERM] [$PA //]"). auto.
      iIntros "PB".
      iApply ("IHn" with "[] TERM PB").
      { eauto. }
      { iModIntro. iIntros "IH2 PB". iMod ("KNOW1" with "PB") as "(PA & >KNOW2)".
        iApply ("IH" with "[IH2 KNOW2] PA").
        iIntros "FC PA". iMod ("KNOW2" with "PA") as "PB". iMod ("IH2" with "FC PB") as "RES". iModIntro. iFrame.
      }
    }
  Qed.

  Lemma elc0_ccs_ind k ps l1 l2 x E v (A T : Vars v) (Q : iProp) :
    (v <= x) ->
    (◆[k, l1] ∗ ◇{ps}((1 + l2 + l1), 1) ∗ ◇{ps}(l2, 1))
      ⊢
      (□((€ -∗ (prop _ A) =|x|=(fairI (ident_tgt:=ident_tgt) x)={E}=∗ Q) -∗ (prop _ A) =|x|=(fairI (ident_tgt:=ident_tgt) x)={E}=∗ (◇{ps}(l2, 1) -∗ Q)))
      -∗
      ((prop _ T) =|x|=(fairI (ident_tgt:=ident_tgt) x)={E}=∗ Q)
      -∗
      ((prop _ A ∗ @env_live_chain0 x E k v A T)
         =|x|=(fairI (ident_tgt:=ident_tgt) x)={E}=∗ (◇{ps}(l2, 1) -∗ Q))
  .
  Proof.
    intros. iIntros "(#LO & PCSh & PCS) #IH TERM [PA #ELI]".
    iMod (ccs_make with "[LO PCSh]") as "[CCS _]". iFrame. eauto.
    Unshelve. 2: auto.
    iDestruct "CCS" as "[%o CCS]".
    (* Induction. *)
    iInduction o as [o] "IHo" using (well_founded_ind Ord.lt_well_founded) forall "CCS".
    iApply ("IH" with "[CCS PCS TERM] PA"). iIntros "FC PA".
    iMod ("ELI" with "FC PA") as "[(PA & PCk) | PT]".
    { (* Prove with the induction. *)
      iMod (ccs_decr with "[$CCS $PCk]") as (o') "(CCS & %LTo & PCk)"; [lia|].
      by iApply ("IHo" with "[%] PCk TERM PA CCS PCS").
    }
    { (* Reached the target state T. *)
      iApply ("TERM" with "PT").
    }
  Qed.

  Lemma elc_ccs_ind k ps l1 l2 n x E v (A T : Vars v) (Q : iProp) :
    (v <= x) ->
    (◆[k, l1] ∗ ◇{ps}((1 + l2 + l1), (1 + n)^2) ∗ ◇{ps}(l2, (1 + n)^2))
      ⊢
      (□((€ -∗ (prop _ A) =|x|=(fairI (ident_tgt:=ident_tgt) x)={E}=∗ Q) -∗ (prop _ A) =|x|=(fairI (ident_tgt:=ident_tgt) x)={E}=∗ (◇{ps}(l2, 1) -∗ Q)))
      -∗
      ((prop _ T) =|x|=(fairI (ident_tgt:=ident_tgt) x)={E}=∗ Q)
      -∗
      ((prop _ A ∗ @env_live_chain n x E k l1 v A T)
         =|x|=(fairI (ident_tgt:=ident_tgt) x)={E}=∗ (◇{ps}(l2, 1) -∗ Q))
  .
  Proof.
    (* Outer induction. *)
    iIntros (LE) "(#LO & PCSh & PCSn) #IH TERM [PA #ELI]".
    iInduction (n) as [|n] "IHn" forall (A) "IH".
    { iSimpl. iApply (elc0_ccs_ind with "[$PCSh $PCSn] IH TERM"); auto. }
    iMod (pcs_decr ((1+n)^2) (2*n + 3) with "PCSh") as "[PCSh PCSh1]"; [simpl;lia|].
    iMod (pcs_decr 1 2 with "PCSh1") as "[PCSh1 PCSh2]"; [lia|].
    iMod (ccs_make _ _ _ _ 0 with "[LO PCSh1]") as "[CCS _]". iFrame. eauto.
    iDestruct "CCS" as "[%o CCS]".
    (* Inner induction. *)
    iInduction o as [o] "IHo" using (well_founded_ind Ord.lt_well_founded) forall "CCS".
    iApply ("IH" with "[CCS PCSn TERM PCSh PCSh2] PA"). iIntros "FC PA".
    iMod ("ELI" with "FC PA") as "[(PA & PCk) | [PT | (PA & % & % & % & #LO' & %LAY & #KNOW1 & #ELI' & #ELI2)]]".
    { (* Prove with the inner induction. *)
      iMod (ccs_decr with "[$CCS $PCk]") as "(%o' & CCS & %LTo & PCk)"; [lia|].
      by iApply ("IHo" with "[%] PCSn TERM PA PCSh PCSh2 CCS").
    }
    { (* Reached the target state T. *)
      iApply ("TERM" with "PT").
    }
    { (* Prove with the outer induction. *)
      iMod (pcs_decr ((1+n)^2) (2*n + 3) with "PCSn") as "[PCSn PCSn0]".
      { simpl. lia. }
      iMod (pcs_decr 1 2 with "PCSn0") as "[PCSn1 PCSn2]".
      { lia. }
      iMod (pcs_decr 1 1 with "PCSn2") as "[PCSn2 PCSn3]".
      { lia. }
      iMod (pcs_decr 1 1 with "PCSh2") as "[PCSh1 PCSh2]".
      { lia. }
      iMod (pcs_drop_le (1+l2+l') with "PCSh1") as "PCSh1"; [lia..|].
      iMod (elc0_ccs_ind with "[$LO' $PCSh1 $PCSn1] IH [TERM PCSh PCSn PCSn3 PCSh2] [$PA //]") as "RES".
      auto.
      2:{ iModIntro. iApply ("RES" with "PCSn2"). }
      iIntros "PB".
      iApply ("IHn" with "[//] PCSh PCSn TERM PB [] [- //]").
      { iModIntro. iIntros "IH2 PB". iMod ("KNOW1" with "PB") as "(PA & >KNOW2)".
        iApply ("IH" with "[IH2 KNOW2] PA").
        iIntros "FC PA". iMod ("KNOW2" with "PA") as "PB". iApply ("IH2" with "FC PB").
      }
    }
  Qed.

End ELI.

Notation "A '~{' x , E , k '}~◇' T" :=
  (env_live_chain0 x E k A T) (at level 50, x, E, k, T at level 1, format "A  ~{ x ,  E ,  k  }~◇  T") : bi_scope.

Notation "A '~{' n , x , E , k , l '}~◇' T" :=
  (env_live_chain n x E k l A T) (at level 50, n, x, E, k, l, T at level 1, format "A  ~{ n ,  x ,  E ,  k ,  l }~◇  T") : bi_scope.
