From sflib Require Import sflib.

From Fairness Require Import PCM IPM IUpd.

Set Implicit Arguments.

Section SUM.
  Context `{Σ: GRA.t}.
  Notation iProp := (iProp Σ).

  Fixpoint list_prop_sum A (P: A -> iProp) (l: list A): iProp :=
    match l with
    | [] => True
    | hd::tl => P hd ∗ list_prop_sum P tl
    end.

  Lemma list_prop_sum_wand (A: Type) (P0 P1 : A → iProp)
        (l: list A)
    :
    (list_prop_sum P0 l)
      -∗
      (list_prop_sum (fun a => P0 a -∗ P1 a) l)
      -∗
      (list_prop_sum P1 l).
  Proof.
    induction l; ss.
    { iIntros. auto. }
    iIntros "[HD0 TL0] [HD1 TL1]". iSplitL "HD0 HD1".
    { iApply ("HD1" with "HD0"). }
    { iApply (IHl with "TL0 TL1"). }
  Qed.

  Lemma list_prop_sum_perm A P (l0 l1: list A)
        (PERM: Permutation l0 l1)
    :
    list_prop_sum P l0 ⊢ list_prop_sum P l1.
  Proof.
    induction PERM; ss.
    { iIntros "[H0 H1]". iFrame. iApply IHPERM. auto. }
    { iIntros "[H0 [H1 H2]]". iFrame. }
    { etrans; eauto. }
  Qed.

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
  Proof.
    induction l0; ss.
    { iIntros "SAT". iFrame. }
    { iIntros "[INTERP SAT]". iFrame. iApply IHl0; auto. }
  Qed.

  Lemma list_prop_sum_combine A (P: A -> iProp) l0 l1
    :
    (list_prop_sum P l0 ∗ list_prop_sum P l1)
      ⊢
      (list_prop_sum P (l0 ++ l1)).
  Proof.
    induction l0; ss.
    { iIntros "[_ SAT]". auto. }
    { iIntros "[[INTERP SAT0] SAT1]". iFrame.
      iApply IHl0. iFrame.
    }
  Qed.

  Lemma list_prop_sum_add A (P: A -> iProp) l a
    :
    (P a ∗ list_prop_sum P l)
      ⊢
      (list_prop_sum P (l++[a])).
  Proof.
    iIntros "[NEW SAT]". iApply list_prop_sum_combine. iFrame.
  Qed.

  Lemma list_prop_sum_impl A (P0 P1: A -> iProp) l
        (IMPL: forall a, P0 a ⊢ P1 a)
    :
    (list_prop_sum P0 l)
      ⊢
      (list_prop_sum P1 l).
  Proof.
    induction l; ss.
    iIntros "[HD TL]". iSplitL "HD".
    { iApply (IMPL with "HD"). }
    { iApply (IHl with "TL"). }
  Qed.

  Lemma list_prop_sum_impl_in A (P0 P1: A -> iProp) l
        (IMPL: forall a (IN: In a l), P0 a ⊢ P1 a)
    :
    (list_prop_sum P0 l)
      ⊢
      (list_prop_sum P1 l).
  Proof.
    induction l; ss.
    iIntros "[HD TL]".
    iSplitL "HD".
    { iApply (IMPL with "HD"). auto. }
    { iApply (IHl with "TL"). eauto. }
  Qed.

  Lemma list_prop_sum_sepconj A (P0 P1: A -> iProp) l
    :
    ((list_prop_sum P0 l) ∗ (list_prop_sum P1 l))
      ⊢
      list_prop_sum (fun a => (P0 a) ∗ (P1 a)) l.
  Proof.
    induction l; ss; auto.
    iIntros "[[HD1 TL1] [HD2 TL2]]". iFrame. iApply IHl. iFrame.
  Qed.

  Lemma list_prop_sepconj_sum A (P0 P1: A -> iProp) l
    :
    (list_prop_sum (fun a => (P0 a) ∗ (P1 a)) l)
      ⊢
      ((list_prop_sum P0 l) ∗ (list_prop_sum P1 l)).
  Proof.
    induction l; ss; auto.
    iIntros "[[HD1 HD2] TL]". iFrame. iApply IHl. iFrame.
  Qed.

  Lemma list_prop_sum_impl2 A (P0 P1 Q: A -> iProp) l
        (IMPL: forall a, (P0 a ∗ P1 a) -∗ Q a)
    :
    ((list_prop_sum P0 l) ∗ (list_prop_sum P1 l))
      -∗
      list_prop_sum Q l.
  Proof.
    iIntros "SUMs". iApply list_prop_sum_impl. 2: iApply list_prop_sum_sepconj; iFrame.
    i. ss. iApply IMPL.
  Qed.

  Lemma list_prop_sum_persistent A (P: A -> iProp) l
        (PERSIST: forall a, Persistent (P a))
    :
    (list_prop_sum P l) -∗ (□ list_prop_sum P l).
  Proof.
    induction l.
    { iIntros "_". ss. }
    ss. iIntros "[#$ Ps]".
    iApply IHl; iFrame.
  Qed.

  Global Program Instance Persistent_list_prop_sum
         A (P: A -> iProp) l (PERSIST: forall a, Persistent (P a)) : Persistent (list_prop_sum P l).
  Next Obligation.
  Proof.
    intros. iIntros "Ps". iPoseProof (list_prop_sum_persistent with "Ps") as "Ps". auto.
  Qed.

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
    revert IMPL. induction FORALL; i; ss.
    iIntros "[HD TL]". iSplitL "HD".
    { iApply (IMPL with "HD"); auto. }
    { iApply (IHFORALL with "TL"). auto. }
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
    iIntros "SUM". iApply list_prop_sum_or_cases_l. iApply list_prop_sum_impl. 2: iFrame.
    i. iIntros "[C0|C1]"; iFrame.
  Qed.

  Lemma list_prop_sum_pull_bupd
        Q
        A (P: A -> iProp) l
    :
    (list_prop_sum (fun a => #=( Q )=> P a) l)
      -∗
      #=( Q )=>(list_prop_sum P l).
  Proof.
    induction l.
    { iIntros "_". ss. }
    ss. iIntros "[PA SUM]". iSplitL "PA"; iFrame. iApply IHl. iFrame.
  Qed.

  Lemma list_prop_sum_pull_bupd_default
        A (P: A -> iProp) l
    :
    (list_prop_sum (fun a => #=> P a) l)
      -∗
      #=>(list_prop_sum P l).
  Proof.
    induction l.
    { iIntros "_". ss. }
    ss. iIntros "[PA SUM]". iSplitL "PA"; iFrame. iApply IHl. iFrame.
  Qed.

  Lemma list_prop_sum_in_split
        A (P: A -> iProp) l a
        (IN: In a l)
    :
    (list_prop_sum (fun a => P a) l)
      -∗ ((P a) ∗ ((P a) -∗ (list_prop_sum (fun a => P a) l))).
  Proof.
    iIntros "SUM". apply in_split in IN. des. rewrite cons_middle in IN. clarify.
    iPoseProof (list_prop_sum_split with "SUM") as "[SL SR]".
    iPoseProof (list_prop_sum_split with "SR") as "[SM SR]".
    iSplitL "SM". ss. iDestruct "SM" as "[PA _]". iFrame.
    iIntros "PA".
    iAssert (list_prop_sum (fun a0 => P a0) (a :: (l1 ++ l2)))%I with "[SL SR PA]" as "SP".
    { ss. iFrame. iApply list_prop_sum_combine. iFrame. }
    iApply (list_prop_sum_perm with "SP"). rewrite app_assoc. rewrite app_comm_cons.
    apply Permutation_app_tail. apply Permutation_cons_append.
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
    induction l; ss.
    iIntros "[HD TL]". iSplitL "HD".
    { iApply (MAP with "HD"). }
    { iApply (IHl with "TL"). }
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
    induction l; ss.
    iIntros "[HD TL]". iSplitL "HD".
    { iApply (MAP with "HD"). }
    { iApply (IHl with "TL"). }
  Qed.
End SUM.
