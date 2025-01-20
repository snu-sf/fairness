From sflib Require Import sflib.

From iris.bi Require Import big_op.
From Fairness Require Import PCM IPM IUpd.

Set Implicit Arguments.

Lemma nth_error_lookup {A} (l: list A) k :
  nth_error (A:=A) l k = l !! k.
Proof. revert k. induction l=> -[|k]; ss. Qed.

Lemma In_elem_of_list {A} (l: list A) v :
  In v l ↔ v ∈ l.
Proof.
  revert v. induction l as [|v' l IH]=> v; ss.
  { rewrite elem_of_nil //. }
  rewrite elem_of_cons IH (comm _ v) //.
Qed.

Section SUM.
  Context `{Σ: GRA.t}.
  Notation iProp := (iProp Σ) (only parsing).

  Fixpoint list_prop_sum A (P: A -> iProp) (l: list A): iProp :=
    match l with
    | [] => True
    | hd::tl => P hd ∗ list_prop_sum P tl
    end.

  Lemma list_prop_sum_big_op A (P: A -> iProp) l
    :
    list_prop_sum P l ⊣⊢ ([∗ list] a ∈ l, P a).
  Proof. induction l as [|a l IH]; ss. rewrite IH //. Qed.

  Lemma list_prop_sum_wand (A: Type) (P0 P1 : A → iProp)
        (l: list A)
    :
    (list_prop_sum P0 l)
      -∗
      (list_prop_sum (fun a => P0 a -∗ P1 a) l)
      -∗
      (list_prop_sum P1 l).
  Proof. rewrite !list_prop_sum_big_op. apply big_sepL_wand. Qed.

  Lemma list_prop_sum_perm A P (l0 l1: list A)
        (PERM: Permutation l0 l1)
    :
    list_prop_sum P l0 ⊢ list_prop_sum P l1.
  Proof. rewrite !list_prop_sum_big_op PERM //. Qed.

  Lemma list_prop_sum_nil A (P: A -> iProp)
    :
    ⊢ list_prop_sum P [].
  Proof. ss. Qed.

  Lemma list_prop_sum_cons_fold A (P: A -> iProp) hd tl
    :
    (P hd ∗ list_prop_sum P tl)
      ⊢
      (list_prop_sum P (hd::tl)).
  Proof. ss. Qed.

  Lemma list_prop_sum_cons_unfold A (P: A -> iProp) hd tl
    :
    (list_prop_sum P (hd::tl))
      ⊢
      (P hd ∗ list_prop_sum P tl).
  Proof. ss. Qed.

  Lemma list_prop_sum_split A (P: A -> iProp) l0 l1
    :
    (list_prop_sum P (l0 ++ l1))
      ⊢
      (list_prop_sum P l0 ∗ list_prop_sum P l1).
  Proof. rewrite !list_prop_sum_big_op big_sepL_app //. Qed.

  Lemma list_prop_sum_combine A (P: A -> iProp) l0 l1
    :
    (list_prop_sum P l0 ∗ list_prop_sum P l1)
      ⊢
      (list_prop_sum P (l0 ++ l1)).
  Proof. rewrite !list_prop_sum_big_op big_sepL_app //. Qed.

  Lemma list_prop_sum_add A (P: A -> iProp) l a
    :
    (P a ∗ list_prop_sum P l)
      ⊢
      (list_prop_sum P (l++[a])).
  Proof. rewrite !list_prop_sum_big_op big_sepL_snoc (comm (∗)%I) //. Qed.

  Lemma list_prop_sum_impl A (P0 P1: A -> iProp) l
        (IMPL: forall a, P0 a ⊢ P1 a)
    :
    (list_prop_sum P0 l)
      ⊢
      (list_prop_sum P1 l).
  Proof. rewrite !list_prop_sum_big_op. by setoid_rewrite IMPL. Qed.

  Lemma list_prop_sum_impl_in A (P0 P1: A -> iProp) l
        (IMPL: forall a (IN: In a l), P0 a ⊢ P1 a)
    :
    (list_prop_sum P0 l)
      ⊢
      (list_prop_sum P1 l).
  Proof.
    rewrite !list_prop_sum_big_op. apply big_sepL_mono.
    ii. by eapply IMPL, In_elem_of_list, elem_of_list_lookup_2.
  Qed.

  Lemma list_prop_sum_sepconj A (P0 P1: A -> iProp) l
    :
    ((list_prop_sum P0 l) ∗ (list_prop_sum P1 l))
      ⊢
      list_prop_sum (fun a => (P0 a) ∗ (P1 a)) l.
  Proof. rewrite !list_prop_sum_big_op big_sepL_sep //. Qed.

  Lemma list_prop_sepconj_sum A (P0 P1: A -> iProp) l
    :
    (list_prop_sum (fun a => (P0 a) ∗ (P1 a)) l)
      ⊢
      ((list_prop_sum P0 l) ∗ (list_prop_sum P1 l)).
  Proof. rewrite !list_prop_sum_big_op big_sepL_sep //. Qed.

  Lemma list_prop_sum_impl2 A (P0 P1 Q: A -> iProp) l
        (IMPL: forall a, (P0 a ∗ P1 a) -∗ Q a)
    :
    ((list_prop_sum P0 l) ∗ (list_prop_sum P1 l))
      -∗
      list_prop_sum Q l.
  Proof.
    rewrite !list_prop_sum_big_op -big_sepL_sep.
    iApply big_sepL_mono. ii. iApply IMPL.
  Qed.

  Lemma list_prop_sum_persistent A (P: A -> iProp) l
        (PERSIST: forall a, Persistent (P a))
    :
    (list_prop_sum P l) -∗ (□ list_prop_sum P l).
  Proof. rewrite !list_prop_sum_big_op. iIntros "#$". Qed.

  Global Instance Persistent_list_prop_sum
         A (P: A -> iProp) l (PERSIST: forall a, Persistent (P a)) : Persistent (list_prop_sum P l).
  Proof. rewrite !list_prop_sum_big_op. apply _. Qed.

  Lemma list_map_forall2 A B (f: A -> B)
        l
    :
    List.Forall2 (fun a b => b = f a) l (List.map f l).
  Proof.
    induction l; ss. econs; eauto.
  Qed.

  Lemma list_prop_sum_forall2 A B
        (R: A -> B -> Prop)
        (P: A -> iProp) (Q: B -> iProp)
        la lb
        (FORALL: List.Forall2 R la lb)
        (IMPL: forall a b (INA: List.In a la) (INB: List.In b lb),
            R a b -> P a ⊢ Q b)
    :
    (list_prop_sum P la)
      ⊢
      (list_prop_sum Q lb).
  Proof.
    rewrite !list_prop_sum_big_op -(big_sepL_fmap _ (λ _ x, x) la)
      -(big_sepL_fmap _ (λ _ x, x) lb).
    apply big_sepL_id_mono', Forall2_fmap_2, Forall2_same_length_lookup_2.
    { eapply Forall2_length, FORALL. }
    ii. apply IMPL.
    1,2: by eapply In_elem_of_list, elem_of_list_lookup_2.
    eapply Forall2_lookup_lr; done.
  Qed.

  Lemma list_prop_sum_or_cases_l
        A (P0 P1: A -> iProp) l
    :
    (list_prop_sum (fun a => (P0 a ∨ P1 a)) l)
      -∗
      ((list_prop_sum P0 l) ∨ (∃ a, (⌜List.In a l⌝) ∗ (P1 a))).
  Proof.
    induction l.
    { iIntros "_". iLeft. ss. }
    ss. iIntros "[[C0|C1] SUM]".
    - iPoseProof (IHl with "SUM") as "[S0|S1]". iLeft; iFrame.
      iRight. iDestruct "S1" as "[% [%IN P1]]". iExists a0. iFrame. iPureIntro. auto.
    - iRight. iExists a. iFrame. iPureIntro. auto.
  Qed.

  Lemma list_prop_sum_or_cases_r
        A (P0 P1: A -> iProp) l
    :
    (list_prop_sum (fun a => (P0 a ∨ P1 a)) l)
      -∗
      ((list_prop_sum P1 l) ∨ (∃ a, (⌜List.In a l⌝) ∗ (P0 a))).
  Proof.
    iIntros "SUM". iApply list_prop_sum_or_cases_l.
    rewrite !list_prop_sum_big_op. by iEval (setoid_rewrite (comm (∨)%I)).
  Qed.

  Lemma list_prop_sum_pull_bupd
        Q
        A (P: A -> iProp) l
    :
    (list_prop_sum (fun a => #=( Q )=> P a) l)
      -∗
      #=( Q )=>(list_prop_sum P l).
  Proof. rewrite !list_prop_sum_big_op !big_sepL_bupd. iIntros "$". Qed.

  Lemma list_prop_sum_pull_bupd_default
        A (P: A -> iProp) l
    :
    (list_prop_sum (fun a => #=> P a) l)
      -∗
      #=>(list_prop_sum P l).
  Proof. rewrite !list_prop_sum_big_op !big_sepL_bupd. iIntros "$". Qed.

  Lemma list_prop_sum_in_split
        A (P: A -> iProp) l a
        (IN: In a l)
    :
    (list_prop_sum (fun a => P a) l)
      -∗ ((P a) ∗ ((P a) -∗ (list_prop_sum (fun a => P a) l))).
  Proof.
    apply In_elem_of_list, elem_of_list_lookup_1 in IN as [k In].
    rewrite !list_prop_sum_big_op.
    by iApply big_sepL_lookup_acc.
  Qed.

  Lemma list_prop_sum_map
        A (P0: A -> iProp)
        B (P1: B -> iProp)
        l (f: A -> B)
        (MAP: forall a, (P0 a) -∗ (P1 (f a)))
    :
    (list_prop_sum P0 l)
      ⊢
      (list_prop_sum P1 (List.map f l)).
  Proof.
    rewrite !list_prop_sum_big_op big_sepL_fmap.
    apply big_sepL_mono.
    ii. iApply MAP.
  Qed.

  Lemma list_prop_sum_map_inv
        A (P0: A -> iProp)
        B (P1: B -> iProp)
        l (f: A -> B)
        (MAP: forall a, (P1 (f a)) -∗ (P0 a))
    :
    (list_prop_sum P1 (List.map f l))
      ⊢
    (list_prop_sum P0 l).
  Proof.
    rewrite !list_prop_sum_big_op big_sepL_fmap.
    apply big_sepL_mono.
    ii. iApply MAP.
  Qed.
End SUM.
