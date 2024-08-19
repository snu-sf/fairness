From iris.algebra Require Import cmra updates functions.
From sflib Require Import sflib.
From Fairness Require Import PCM IPM IPropAux SRA.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.PropExtensionality.
From Fairness Require Import Axioms.

From iris.bi Require Import derived_laws. Import bi.
Require Export Coq.Sorting.Mergesort. Import NatSort.

From Fairness Require Import MonotoneRA.
Require Import Program.

Set Implicit Arguments.

Class regionG (Σ : gFunctors) (A : Type) : Set := RegionGS {
  regionG_inG : inG Σ (nat -d> (OneShot.t A));
}.

Definition regionΣ A : gFunctors :=
  #[GFunctor (nat -d> (OneShot.t A))].

Global Instance subG_regionΣ {Σ A} : subG (regionΣ A) Σ → regionG Σ A.
Proof. solve_inG. Qed.

Local Existing Instances regionG_inG.

Global Instance sra_subG_regionG {Γ Σ A} :
  @SRA.subG Γ Σ → regionG (SRA.to_gf Γ) A → regionG Σ A.
Proof.
  intros ? [].
  split; apply _.
Defined.

Module Region.
  Definition t A : ucmra := nat -d> (OneShot.t A).

  Section REGION.
    Context (γ : gname).
    Context {A: Type}.
    Notation t := (t A).
    Context `{!regionG Σ A}.
    Notation iProp := (iProp Σ).

    Definition to_black (l : list A) : t :=
      (fun n =>
      match nth_error l n with
      | Some a => OneShot.shot a
      | _ => OneShot.pending A 1%Qp
      end): (nat ==> OneShot.t A)%ra.

    Definition black (l: list A): iProp :=
      own γ (to_black l).

    Definition to_white (k : nat) (a : A) : t :=
      (fun n =>
        if Nat.eq_dec n k then OneShot.shot a else ε
      ) : (nat ==> OneShot.t A)%ra.
    Definition white (k: nat) (a: A): iProp :=
      own γ (to_white k a).

    Global Instance Persistent_white k a: Persistent (white k a).
    Proof.
      apply own_core_persistent,core_id_total.
      intros n. rewrite /to_white discrete_fun_lookup_core. des_ifs.
    Qed.

    Lemma black_white_in k a l
      :
      (black l)
        -∗
        (white k a)
        -∗
        ⌜nth_error l k = Some a⌝.
    Proof.
      iIntros "BLACK #WHITE". iCombine "BLACK WHITE" gives %WF.
      iPureIntro. specialize (WF k).
      rewrite discrete_fun_lookup_op /to_black /to_white in WF.
      des_ifs; ss. f_equal.
      apply OneShot.shot_agree in WF. auto.
    Qed.

    Lemma white_agree k a0 a1
      :
        (white k a0)
        -∗
        (white k a1)
        -∗
        ⌜a0 = a1⌝.
    Proof.
      iIntros "W0 W1". iCombine "W0 W1" gives %WF.
      iPureIntro. specialize (WF k).
      rewrite discrete_fun_lookup_op /to_black /to_white in WF.
      des_ifs; ss.
      apply OneShot.shot_agree in WF. auto.
    Qed.

    Lemma black_alloc l a
      :
      (black l)
        -∗
        #=> (black (l++[a]) ∗ white (length l) a).
    Proof.
      iIntros "H". iMod (own_update with "H") as "[BLACK WHITE]".
      2:{ iModIntro. iSplitL "BLACK"; [iApply "BLACK"|iApply "WHITE"]. }
      eapply cmra_update_discrete_fun. i.
      rewrite /to_black /to_white discrete_fun_lookup_op.
      destruct (nth_error l a0) eqn:EQ.
      { rewrite nth_error_app1.
        2:{ apply nth_error_Some; auto. rewrite EQ; auto. }
        rewrite EQ. des_ifs; ss.
        { exploit nth_error_Some.
          erewrite EQ. i. des. hexploit x0; auto. i. lia.
        }
      }
      { dup EQ. eapply nth_error_None in EQ. rewrite nth_error_app2; auto.
        destruct (Nat.eq_dec a0 (length l)).
        { subst. replace (length l - length l) with 0 by lia. ss. etrans.
          { eapply OneShot.pending_shot. }
          { instantiate (1:=a). rewrite -OneShot.shot_dup. done. }
        }
        { hexploit nth_error_None. i. des.
          hexploit H0.
          2:{ i. erewrite H1. rewrite right_id. reflexivity. }
          { ss. lia. }
        }
      }
    Qed.

    Variable interp: A -> iProp.

    Definition sat_list (l: list A) := fold_right (fun a P => (interp a ∗ P)%I) True%I l.

    Lemma sat_list_nil
      :
      ⊢ sat_list [].
    Proof.
      unfold sat_list. ss.
    Qed.

    Lemma sat_list_cons_fold hd tl
      :
      (interp hd ∗ sat_list tl)
        ⊢
        (sat_list (hd::tl)).
    Proof.
      unfold sat_list. ss.
    Qed.

    Lemma sat_list_cons_unfold hd tl
      :
      (sat_list (hd::tl))
        ⊢
        (interp hd ∗ sat_list tl).
    Proof.
      unfold sat_list. ss.
    Qed.

    Lemma sat_list_split l0 l1
      :
      (sat_list (l0 ++ l1))
        -∗
        (sat_list l0 ∗ sat_list l1).
    Proof.
      induction l0; ss.
      { iIntros "SAT". iFrame. }
      { iIntros "[INTERP SAT]". iFrame. iApply IHl0; auto. }
    Qed.

    Lemma sat_list_combine l0 l1
      :
      (sat_list l0 ∗ sat_list l1)
        -∗
        (sat_list (l0 ++ l1)).
    Proof.
      induction l0; ss.
      { iIntros "[_ SAT]". auto. }
      { iIntros "[[INTERP SAT0] SAT1]". iFrame.
        iApply IHl0. iFrame.
      }
    Qed.

    Lemma sat_list_add l a
      :
      (interp a ∗ sat_list l)
        -∗
        (sat_list (l++[a])).
    Proof.
      iIntros "[NEW SAT]". iApply sat_list_combine. iFrame.
    Qed.

    Lemma sat_list_permutation l0 l1
          (PERM: Permutation l0 l1)
      :
      sat_list l0 ⊢ sat_list l1.
    Proof.
      induction PERM.
      { auto. }
      { iIntros "H". iApply sat_list_cons_fold.
        iPoseProof (sat_list_cons_unfold with "H") as "[HD TL]".
        iFrame. iApply IHPERM; auto.
      }
      { iIntros "H". iApply sat_list_cons_fold.
        iPoseProof (sat_list_cons_unfold with "H") as "[HD0 TL]".
        iPoseProof (sat_list_cons_unfold with "TL") as "[HD1 TL]".
        iSplitL "HD1"; auto. iApply sat_list_cons_fold. iFrame.
      }
      { etrans; eauto. }
    Qed.

    Lemma sat_list_update l k a
          (FIND: nth_error l k = Some a)
      :
      sat_list l ⊢ interp a ∗ (interp a -∗ sat_list l).
    Proof.
      hexploit nth_error_split; eauto. i. des. subst.
      iIntros "SAT". iPoseProof (sat_list_split with "SAT") as "[SAT0 SAT1]".
      iPoseProof (sat_list_cons_unfold with "SAT1") as "[OLD SAT1]".
      iFrame. iIntros "NEW". iApply sat_list_combine. iFrame.
    Qed.

    Lemma sat_list_nth_sub l k a
          (FIND: nth_error l k = Some a)
      :
      ⊢ SubIProp (interp a) (sat_list l).
    Proof.
      iIntros "H". iPoseProof (sat_list_update with "H") as "[H0 H1]"; eauto.
      iFrame. iModIntro. iIntros "H". iModIntro. iApply ("H1" with "H").
    Qed.

    Lemma sat_list_sub_update l0 l1
          (SUB: list_sub l0 l1)
      :
      sat_list l1 ⊢ sat_list l0 ∗ (sat_list l0 -∗ sat_list l1).
    Proof.
      rr in SUB. des.
      iIntros "H". iPoseProof (sat_list_permutation with "H") as "H".
      { symmetry. eassumption. }
      iPoseProof (sat_list_split with "H") as "[H0 H1]". iFrame.
      iIntros "H1". iPoseProof (sat_list_combine with "[H0 H1]") as "H".
      { iSplitL "H0"; eauto. }
      iApply (sat_list_permutation with "H"). auto.
    Qed.

    Lemma sat_list_sub_sub l0 l1
          (SUB: list_sub l0 l1)
      :
      ⊢ SubIProp (sat_list l0) (sat_list l1).
    Proof.
      iIntros "H". iPoseProof (sat_list_sub_update with "H") as "[H0 H1]"; eauto.
      iFrame. iModIntro. iIntros "H". iModIntro. iApply ("H1" with "H").
    Qed.

    Definition sat: iProp := ∃ l, black l ∗ sat_list l.

    Lemma white_agree_sat k a0 a1
      :
      (white k a0)
        -∗
        (white k a1)
        -∗
        (⌜a0 = a1⌝).
    Proof.
      iIntros "WHITE0 WHITE1".
      iPoseProof (white_agree with "WHITE0 WHITE1") as "%".
      subst. auto.
    Qed.

    Lemma sat_update k a
      :
      (white k a)
        -∗
        (sat)
        -∗
        (interp a ∗ (interp a -∗ sat)).
    Proof.
      iIntros "WHITE [% [BLACK SAT]]".
      iPoseProof (black_white_in with "BLACK WHITE") as "%".
      iPoseProof (sat_list_update with "SAT") as "[INTERP H0]"; eauto.
      iFrame. iIntros "H1". iExists _. iFrame. iApply ("H0" with "H1").
    Qed.

    Lemma sat_white_sub k a
      :
      white k a ⊢ SubIProp (interp a) sat.
    Proof.
      iIntros "H0 H1". iPoseProof (sat_update with "H0 H1") as "[H0 H1]".
      iFrame. iModIntro. iIntros "H". iModIntro. iApply ("H1" with "H").
    Qed.

    Lemma black_whites_in l ks
          (ND: List.NoDup (List.map fst ks))
      :
      (black l)
        -∗
        (∀ k a (IN: List.In (k, a) ks), white k a)
        -∗
        ⌜list_sub (List.map snd ks) l⌝.
    Proof.
      iIntros "BLACK WHITES".
      iAssert (⌜forall k a (IN: List.In (k, a) ks), nth_error l k = Some a⌝)%I as "%INS".
      { clear ND. iRevert "BLACK WHITES". iInduction ks as [|a ks] "IH".
        { iIntros "BLACK WHITES". ss. }
        { destruct a as [k a]. iIntros "BLACK ALL % % %".
          des; clarify.
          { iApply (black_white_in with "BLACK [ALL]"); eauto. iApply "ALL". auto. }
        }
      }
      iPureIntro.
      remember (length ks) as n. revert ks l Heqn ND INS.
      induction n; ss.
      { i. destruct ks; ss. exists l. rewrite app_nil_r. ss. }
      i. destruct ks as [|[k0 a0] tl]; ss. inv Heqn. inv ND.
      hexploit (INS k0 a0); eauto. i.
      hexploit nth_error_split; eauto. i. des. subst.
      hexploit (IHn (List.map (fun ka => (if le_lt_dec (fst ka) (length l1) then (fst ka) else (fst ka - 1), snd ka)) tl) (l1++l2)).
      { rewrite map_length. auto. }
      { rewrite map_map. ss.
        match goal with
        | |- _ (map ?f tl) => replace (map f tl) with (map (fun k => (if le_lt_dec k (length l1) then k else (k - 1))) (map fst tl))
        end.
        { eapply injective_map_NoDup_strong; auto. i. des_ifs.
          { exfalso. eapply H1. replace (length l1) with (a2 - 1) by lia; ss. }
          { exfalso. eapply H1. replace (length l1) with (a1 - 1) by lia; ss. }
          { lia. }
        }
        rewrite map_map. auto.
      }
      { i. apply in_map_iff in IN. des.
        destruct x as [k1 a1]. ss. clarify. des_ifs.
        { assert (k1 = length l1 \/ k1 < length l1) by lia. des.
          { subst. eapply in_map with (f:=fst)in IN0. ss. }
          rewrite nth_error_app1; auto.
          hexploit (INS k1 a); auto. i. rewrite nth_error_app1 in H3; auto.
        }
        rewrite nth_error_app2; [|lia].
        hexploit (INS k1 a); auto. i.
        rewrite nth_error_app2 in H0; [|lia].
        replace (k1 - length l1) with (S (k1 - 1 - length l1)) in H0 by lia. ss.
      }
      i. rewrite map_map in H0. ss.
      r in H0. des. exists s.
      rewrite <- Permutation_middle. rewrite <- Permutation_middle.
      econs. auto.
    Qed.

    Lemma sat_sub_update (l: list (nat * A))
          (ND: List.NoDup (List.map fst l))
      :
      (∀ k a (IN: List.In (k, a) l), white k a)
        -∗
        (sat)
        -∗
        (sat_list (List.map snd l)) ∗ ((sat_list (List.map snd l)) -∗ sat).
    Proof.
      iIntros "H0 [% [H1 H2]]".
      iPoseProof (black_whites_in with "H1 H0") as "%"; auto.
      iPoseProof (sat_list_sub_update with "H2") as "[H2 H3]".
      { eauto. }
      iFrame. iIntros "H". iPoseProof ("H3" with "H") as "H".
      iExists _. iFrame.
    Qed.

    Lemma sat_whites_sub (l: list (nat * A))
          (ND: List.NoDup (List.map fst l))
      :
      (∀ k a (IN: List.In (k, a) l), white k a)
        ⊢ SubIProp (sat_list (List.map snd l)) sat.
    Proof.
      iIntros "H0 H1". iPoseProof (sat_sub_update with "H0 H1") as "[H0 H1]".
      { auto. }
      iFrame. iModIntro. iIntros "H". iModIntro. iApply ("H1" with "H").
    Qed.

    Lemma sat_alloc a
      :
      sat
        -∗
        (interp a)
        -∗
        ∃ k, (#=> (sat ∗ white k a)).
    Proof.
      iIntros "[% [BLACK SAT]] INTERP".
      iPoseProof (sat_list_add with "[SAT INTERP]") as "SAT".
      { iFrame. }
      iExists _.
      iPoseProof (black_alloc with "BLACK") as "> [BLACK WHITE]".
      iModIntro. iSplitR "WHITE"; auto.
      iExists _. iFrame.
    Qed.

    Lemma update k a P
      :
      (white k a)
        -∗
        (#=(interp a)=> P)
        -∗
        (#=(sat)=> P).
    Proof.
      iIntros "H0 H1".
      iPoseProof (sat_white_sub with "H0") as "H0".
      iApply (IUpd_sub_mon with "H0 H1").
    Qed.

    Lemma updates (l: list (nat * A)) P
          (ND: List.NoDup (List.map fst l))
      :
      (∀ k a (IN: List.In (k, a) l), white k a)
        -∗
        (#=(sat_list (List.map snd l))=> P)
        -∗
        (#=(sat)=> P).
    Proof.
      iIntros "H0 H1".
      iPoseProof (sat_whites_sub with "H0") as "H0"; auto.
      iApply (IUpd_sub_mon with "H0 H1").
    Qed.

    Lemma sat_updating (l: list (nat * A)) P Q R
          (ND: List.NoDup (List.map fst l))
      :
      (∀ k a (IN: List.In (k, a) l), white k a)
        -∗
        (updating (sat_list (List.map snd l)) P Q R)
        -∗
        (updating sat P Q R).
    Proof.
      iIntros "H0 H1".
      iPoseProof (sat_whites_sub with "H0") as "H0"; auto.
      iApply (updating_sub_mon with "H0 H1").
    Qed.

    Lemma alloc a
      :
      (interp a)
        -∗
        (#=(sat)=> ∃ k, white k a).
    Proof.
      rewrite IUpd_eq.
      iIntros "H0 H1".
      iPoseProof (sat_alloc with "H1 H0") as "[% > [H0 H1]]".
      iModIntro. iFrame.
    Qed.
  End REGION.

  Lemma black_new `{!regionG Σ A} l :
    ⊢ #=> ∃ γ, black γ l.
  Proof.
    iMod (own_alloc (to_black l)) as (γ) "B".
    { rewrite /to_black =>n. des_ifs.
      - apply OneShot.shot_wf.
      - apply OneShot.pending_one_wf.
    }
    iModIntro. iFrame.
  Qed.

  Global Typeclasses Opaque white to_white black to_black.
End Region.


Class regionsG (Σ : gFunctors) (X : Type) (As : X → Type) : Set := RegionsGS {
  regionsG_inG : inG Σ (discrete_funUR (λ x : X, nat -d> (OneShot.t (As x))));
}.

Definition regionsΣ (X : Type) (As : X → Type) : gFunctors :=
  #[GFunctor (discrete_funUR (λ x : X, nat -d> (OneShot.t (As x))))].

Global Instance subG_regionsΣ {Σ X} {As : X → Type} : subG (regionsΣ As) Σ → regionsG Σ As.
Proof. solve_inG. Qed.

Local Existing Instances regionsG_inG.

Global Instance sra_subG_regionsG {Γ Σ X} {As : X → Type} :
  @SRA.subG Γ Σ → regionsG (SRA.to_gf Γ) As → regionsG Σ As.
Proof.
  intros ? [].
  split; apply _.
Defined.

Module Regions.

  Definition _t (X : Type) (As : X → Type) (x: X): ucmra := nat -d> (OneShot.t (As x)).
  Definition t (X : Type) (As : X → Type) : ucmra := discrete_funUR (_t As).

  Section REGION.

    Context `{!EqDecision X}.
    Context `{As: X -> Type}.

    Notation t := (t As).

    Context `{!regionsG Σ As}.
    Notation iProp := (iProp Σ).

    Section SINGLE.

      Variable x : X.
      Variable γ : gname.
      Local Notation A := (As x).

      Definition to_black (l: list A) : t :=
        discrete_fun_singleton
        x
        ((fun n =>
            match nth_error l n with
            | Some a => OneShot.shot a
            | _ => OneShot.pending A 1%Qp
            end): nat -d> OneShot.t A).

      Definition black (l: list A): iProp :=
        own γ (to_black l).

      Definition to_white (k : nat) (a : A) : t :=
        discrete_fun_singleton
        x
        ((fun n =>
            if Nat.eq_dec n k
            then OneShot.shot a
            else ε): nat -d> OneShot.t A).
      Definition white (k: nat) (a: A): iProp :=
        own γ (to_white k a).

      Global Instance Persistent_white k a: Persistent (white k a).
      Proof.
        apply own_core_persistent,core_id_total.
        intros y. rewrite /to_white discrete_fun_lookup_core.
        destruct (decide (x = y)); subst; ss.
        - rewrite discrete_fun_lookup_singleton => n.
          rewrite discrete_fun_lookup_core. des_ifs.
        - rewrite discrete_fun_lookup_singleton_ne //.
      Qed.

      Lemma black_white_in k a l
        :
        (black l)
          -∗
          (white k a)
          -∗
          ⌜nth_error l k = Some a⌝.
      Proof.
        iIntros "BLACK WHITE". iCombine "BLACK WHITE" gives %WF.
        iPureIntro. specialize (WF x).
        rewrite /to_black /to_white discrete_fun_lookup_op
          !discrete_fun_lookup_singleton in WF.
        specialize (WF k). rewrite discrete_fun_lookup_op in WF.
        des_ifs. apply OneShot.shot_agree in WF. subst. auto.
      Qed.

      Lemma white_agree k a0 a1
        :
        (white k a0)
          -∗
          (white k a1)
          -∗
          ⌜a0 = a1⌝.
      Proof.
        iIntros "WHITE0 WHITE1". iCombine "WHITE0 WHITE1" gives %WF.
        iPureIntro. specialize (WF x).
        rewrite /to_white discrete_fun_lookup_op
          !discrete_fun_lookup_singleton in WF.
        specialize (WF k). rewrite discrete_fun_lookup_op in WF.
        des_ifs. apply OneShot.shot_agree in WF. subst. auto.
      Qed.

      Lemma black_alloc l a
        :
        (black l)
          -∗
          #=> (black (l++[a]) ∗ white (length l) a).
      Proof.
        iIntros "H". iMod (own_update with "H") as "[BLACK WHITE]".
        2:{ iModIntro. iSplitL "BLACK"; [iApply "BLACK"|iApply "WHITE"]. }
        rewrite discrete_fun_singleton_op. apply discrete_fun_singleton_update.
        apply cmra_update_discrete_fun. i.
        rewrite discrete_fun_lookup_op.
        destruct (nth_error l a0) eqn:EQ.
        { rewrite nth_error_app1.
          2:{ apply nth_error_Some; auto. rewrite EQ; auto. }
          rewrite EQ. des_ifs; ss.
          { exploit nth_error_Some. erewrite EQ. i. des. hexploit x1; auto. i. lia. }
        }
        { dup EQ. eapply nth_error_None in EQ. rewrite nth_error_app2; auto.
          destruct (Nat.eq_dec a0 (length l)).
          { subst. replace (length l - length l) with 0 by lia. ss. etrans.
            { eapply OneShot.pending_shot. }
            { instantiate (1:=a). rewrite -OneShot.shot_dup. done. }
          }
          { hexploit nth_error_None. i. des.
            hexploit H0.
            2:{ i. erewrite H1. rewrite right_id. reflexivity. }
            { ss. lia. }
          }
        }
      Qed.

      Variable interp: A -> iProp.

      Definition sat_list (l: list A) := fold_right (fun a P => (interp a ∗ P)%I) True%I l.

      Lemma sat_list_nil
        :
        ⊢ sat_list [].
      Proof.
        unfold sat_list. ss.
      Qed.

      Lemma sat_list_cons_fold hd tl
        :
        (interp hd ∗ sat_list tl)
          ⊢
          (sat_list (hd::tl)).
      Proof.
        unfold sat_list. ss.
      Qed.

      Lemma sat_list_cons_unfold hd tl
        :
        (sat_list (hd::tl))
          ⊢
          (interp hd ∗ sat_list tl).
      Proof.
        unfold sat_list. ss.
      Qed.

      Lemma sat_list_split l0 l1
        :
        (sat_list (l0 ++ l1))
          -∗
          (sat_list l0 ∗ sat_list l1).
      Proof.
        induction l0; ss.
        { iIntros "SAT". iFrame. }
        { iIntros "[INTERP SAT]". iFrame. iApply IHl0; auto. }
      Qed.

      Lemma sat_list_combine l0 l1
        :
        (sat_list l0 ∗ sat_list l1)
          -∗
          (sat_list (l0 ++ l1)).
      Proof.
        induction l0; ss.
        { iIntros "[_ SAT]". auto. }
        { iIntros "[[INTERP SAT0] SAT1]". iFrame.
          iApply IHl0. iFrame.
        }
      Qed.

      Lemma sat_list_add l a
        :
        (interp a ∗ sat_list l)
          -∗
          (sat_list (l++[a])).
      Proof.
        iIntros "[NEW SAT]". iApply sat_list_combine. iFrame.
      Qed.

      Lemma sat_list_permutation l0 l1
            (PERM: Permutation l0 l1)
        :
        sat_list l0 ⊢ sat_list l1.
      Proof.
        induction PERM.
        { auto. }
        { iIntros "H". iApply sat_list_cons_fold.
          iPoseProof (sat_list_cons_unfold with "H") as "[HD TL]".
          iFrame. iApply IHPERM; auto.
        }
        { iIntros "H". iApply sat_list_cons_fold.
          iPoseProof (sat_list_cons_unfold with "H") as "[HD0 TL]".
          iPoseProof (sat_list_cons_unfold with "TL") as "[HD1 TL]".
          iSplitL "HD1"; auto. iApply sat_list_cons_fold. iFrame.
        }
        { etrans; eauto. }
      Qed.

      Lemma sat_list_update l k a
            (FIND: nth_error l k = Some a)
        :
        sat_list l ⊢ interp a ∗ (interp a -∗ sat_list l).
      Proof.
        hexploit nth_error_split; eauto. i. des. subst.
        iIntros "SAT". iPoseProof (sat_list_split with "SAT") as "[SAT0 SAT1]".
        iPoseProof (sat_list_cons_unfold with "SAT1") as "[OLD SAT1]".
        iFrame. iIntros "NEW". iApply sat_list_combine. iFrame.
      Qed.

      Lemma sat_list_nth_sub l k a
            (FIND: nth_error l k = Some a)
        :
        ⊢ SubIProp (interp a) (sat_list l).
      Proof.
        iIntros "H". iPoseProof (sat_list_update with "H") as "[H0 H1]"; eauto.
        iFrame. iModIntro. iIntros "H". iModIntro. iApply ("H1" with "H").
      Qed.

      Lemma sat_list_sub_update l0 l1
            (SUB: list_sub l0 l1)
        :
        sat_list l1 ⊢ sat_list l0 ∗ (sat_list l0 -∗ sat_list l1).
      Proof.
        rr in SUB. des.
        iIntros "H". iPoseProof (sat_list_permutation with "H") as "H".
        { symmetry. eassumption. }
        iPoseProof (sat_list_split with "H") as "[H0 H1]". iFrame.
        iIntros "H1". iPoseProof (sat_list_combine with "[H0 H1]") as "H".
        { iSplitL "H0"; eauto. }
        iApply (sat_list_permutation with "H"). auto.
      Qed.

      Lemma sat_list_sub_sub l0 l1
            (SUB: list_sub l0 l1)
        :
        ⊢ SubIProp (sat_list l0) (sat_list l1).
      Proof.
        iIntros "H". iPoseProof (sat_list_sub_update with "H") as "[H0 H1]"; eauto.
        iFrame. iModIntro. iIntros "H". iModIntro. iApply ("H1" with "H").
      Qed.

      Definition sat: iProp := ∃ l, black l ∗ sat_list l.

      Lemma white_agree_sat k a0 a1
        :
        (white k a0)
          -∗
          (white k a1)
          -∗
          (⌜a0 = a1⌝).
      Proof.
        iIntros "WHITE0 WHITE1".
        iPoseProof (white_agree with "WHITE0 WHITE1") as "%".
        subst. auto.
      Qed.

      Lemma sat_update k a
        :
        (white k a)
          -∗
          (sat)
          -∗
          (interp a ∗ (interp a -∗ sat)).
      Proof.
        iIntros "WHITE [% [BLACK SAT]]".
        iPoseProof (black_white_in with "BLACK WHITE") as "%".
        iPoseProof (sat_list_update with "SAT") as "[INTERP H0]"; eauto.
        iFrame. iIntros "H1". iExists _. iFrame. iApply ("H0" with "H1").
      Qed.

      Lemma sat_white_sub k a
        :
        white k a ⊢ SubIProp (interp a) sat.
      Proof.
        iIntros "H0 H1". iPoseProof (sat_update with "H0 H1") as "[H0 H1]".
        iFrame. iModIntro. iIntros "H". iModIntro. iApply ("H1" with "H").
      Qed.

      Lemma black_whites_in l ks
            (ND: List.NoDup (List.map fst ks))
        :
        (black l)
          -∗
          (∀ k a (IN: List.In (k, a) ks), white k a)
          -∗
          ⌜list_sub (List.map snd ks) l⌝.
      Proof.
        iIntros "BLACK WHITES".
        iAssert (⌜forall k a (IN: List.In (k, a) ks), nth_error l k = Some a⌝)%I as "%INS".
        { clear ND. iInduction ks as [|[k a] ks] "IH"; ss.
          iIntros "% % %".
          des; clarify.
          { iApply (black_white_in with "BLACK [WHITES]"); eauto. iApply "WHITES". auto. }
          { iDestruct ("IH" with "BLACK [WHITES]") as %IH.
            { iIntros. iApply "WHITES". auto. }
            iPureIntro. eauto.
          }
        }
        iPureIntro.
        remember (length ks) as n. revert ks l Heqn ND INS.
        induction n; ss.
        { i. destruct ks; ss. exists l. rewrite app_nil_r. ss. }
        i. destruct ks as [|[k0 a0] tl]; ss. inv Heqn. inv ND.
        hexploit (INS k0 a0); eauto. i.
        hexploit nth_error_split; eauto. i. des. subst.
        hexploit (IHn (List.map (fun ka => (if le_lt_dec (fst ka) (length l1) then (fst ka) else (fst ka - 1), snd ka)) tl) (l1++l2)).
        { rewrite map_length. auto. }
        { rewrite map_map. ss.
          match goal with
          | |- _ (map ?f tl) => replace (map f tl) with (map (fun k => (if le_lt_dec k (length l1) then k else (k - 1))) (map fst tl))
          end.
          { eapply injective_map_NoDup_strong; auto. i. des_ifs.
            { exfalso. eapply H1. replace (length l1) with (a2 - 1) by lia; ss. }
            { exfalso. eapply H1. replace (length l1) with (a1 - 1) by lia; ss. }
            { lia. }
          }
          rewrite map_map. auto.
        }
        { i. apply in_map_iff in IN. des.
          destruct x0 as [k1 a1]. ss. clarify. des_ifs.
          { assert (k1 = length l1 \/ k1 < length l1) by lia. des.
            { subst. eapply in_map with (f:=fst)in IN0. ss. }
            rewrite nth_error_app1; auto.
            hexploit (INS k1 a); auto. i. rewrite nth_error_app1 in H3; auto.
          }
          rewrite nth_error_app2; [|lia].
          hexploit (INS k1 a); auto. i.
          rewrite nth_error_app2 in H0; [|lia].
          replace (k1 - length l1) with (S (k1 - 1 - length l1)) in H0 by lia. ss.
        }
        i. rewrite map_map in H0. ss.
        r in H0. des. exists s.
        rewrite <- Permutation_middle. rewrite <- Permutation_middle.
        econs. auto.
      Qed.

      Lemma sat_sub_update (l: list (nat * A))
            (ND: List.NoDup (List.map fst l))
        :
        (∀ k a (IN: List.In (k, a) l), white k a)
          -∗
          (sat)
          -∗
          (sat_list (List.map snd l)) ∗ ((sat_list (List.map snd l)) -∗ sat).
      Proof.
        iIntros "H0 [% [H1 H2]]".
        iPoseProof (black_whites_in with "H1 H0") as "%"; auto.
        iPoseProof (sat_list_sub_update with "H2") as "[H2 H3]".
        { eauto. }
        iFrame. iIntros "H". iPoseProof ("H3" with "H") as "H".
        iExists _. iFrame.
      Qed.

      Lemma sat_whites_sub (l: list (nat * A))
            (ND: List.NoDup (List.map fst l))
        :
        (∀ k a (IN: List.In (k, a) l), white k a)
          ⊢ SubIProp (sat_list (List.map snd l)) sat.
      Proof.
        iIntros "H0 H1". iPoseProof (sat_sub_update with "H0 H1") as "[H0 H1]".
        { auto. }
        iFrame. iModIntro. iIntros "H". iModIntro. iApply ("H1" with "H").
      Qed.

      Lemma sat_alloc a
        :
        sat
          -∗
          (interp a)
          -∗
          ∃ k, (#=> (sat ∗ white k a)).
      Proof.
        iIntros "[% [BLACK SAT]] INTERP".
        iPoseProof (sat_list_add with "[SAT INTERP]") as "SAT".
        { iFrame. }
        iExists _.
        iPoseProof (black_alloc with "BLACK") as "> [BLACK WHITE]".
        iModIntro. iSplitR "WHITE"; auto.
        iExists _. iFrame.
      Qed.

      Lemma update k a P
        :
        (white k a)
          -∗
          (#=(interp a)=> P)
          -∗
          (#=(sat)=> P).
      Proof.
        iIntros "H0 H1".
        iPoseProof (sat_white_sub with "H0") as "H0".
        iApply (IUpd_sub_mon with "H0 H1").
      Qed.

      Lemma updates (l: list (nat * A)) P
            (ND: List.NoDup (List.map fst l))
        :
        (∀ k a (IN: List.In (k, a) l), white k a)
          -∗
          (#=(sat_list (List.map snd l))=> P)
          -∗
          (#=(sat)=> P).
      Proof.
        iIntros "H0 H1".
        iPoseProof (sat_whites_sub with "H0") as "H0"; auto.
        iApply (IUpd_sub_mon with "H0 H1").
      Qed.

      Lemma sat_updating (l: list (nat * A)) P Q R
            (ND: List.NoDup (List.map fst l))
        :
        (∀ k a (IN: List.In (k, a) l), white k a)
          -∗
          (updating (sat_list (List.map snd l)) P Q R)
          -∗
          (updating sat P Q R).
      Proof.
        iIntros "H0 H1".
        iPoseProof (sat_whites_sub with "H0") as "H0"; auto.
        iApply (updating_sub_mon with "H0 H1").
      Qed.

      Lemma alloc a
        :
        (interp a)
          -∗
          (#=(sat)=> ∃ k, white k a).
      Proof.
        rewrite IUpd_eq. iIntros "H0 H1".
        iPoseProof (sat_alloc with "H1 H0") as "[% > [H0 H1]]".
        iModIntro. iFrame.
      Qed.

    End SINGLE.

  End REGION.

  Section NATKEY.

    Variable As : nat -> Type.
    Context `{Σ: gFunctors}.
    Context `{!regionsG Σ As}.
    Notation iProp := (iProp Σ).

    Variable γ: gname.
    Variable interps : forall i, As i -> iProp.

    Definition nauth_ra (j : nat): @t nat As :=
      fun i => if (lt_dec i j)
            then ε
            else ((fun _ => OneShot.pending (As i) 1%Qp) : (@_t nat As i)).

    Definition nauth (j : nat) : iProp := own γ (nauth_ra j).

    Definition nsats (j : nat) := sep_conjs (fun i => sat i γ (interps (i:=i))) j.

    Definition nsats_l (j : nat) : iProp := [∗ list] i ∈ (seq 0 j), sat i γ (interps (i:=i)).

    Lemma unfold_nsats x :
      nsats (S x) = (nsats x ∗ sat x γ (interps (i:=x)))%I.
    Proof. ss. Qed.

    Lemma eq_nsats_l x :
      nsats_l (S x) ⊣⊢ nsats_l x ∗ sat x γ (interps (i:=x)).
    Proof.
      rewrite /nsats_l seq_S big_sepL_app big_sepL_singleton //.
    Qed.

    Lemma unfold_nsats_l x :
      nsats_l (S x) ⊢ nsats_l x ∗ sat x γ (interps (i:=x)).
    Proof. rewrite eq_nsats_l //. Qed.

    Lemma fold_nsats_l x :
      nsats_l x ∗ sat x γ (interps (i:=x)) ⊢ nsats_l (S x).
    Proof. rewrite eq_nsats_l //. Qed.

    Lemma nsats_equiv_l x :
      nsats x ⊣⊢ nsats_l x.
    Proof.
      induction x as [|x IH]; ss.
      rewrite unfold_nsats eq_nsats_l -IH //.
    Qed.

    Lemma nauth_init_zero :
      own γ ((fun i => ((fun _ => OneShot.pending (As i) 1%Qp) : (_t As i))) : t As)
           ⊢ nauth 0.
    Proof.
      iIntros "OWN". iFrame.
    Qed.

    Lemma nsat_alloc i :
      own γ (discrete_fun_singleton i ((λ _ : nat, OneShot.pending (As i) 1%Qp) : @_t nat As i) : @t nat As)
           ⊢ sat i γ (interps (i:=i)).
    Proof.
      iIntros "OWN". iExists []. ss. unfold black,to_black,sat_list.
      iSplitL; [|done]. iApply (own_proper with "OWN").
      f_equiv.
      intros n. hexploit (nth_error_None (A := As i) [] n). intros. des. rewrite H0. ss. simpl. lia.
    Qed.

    Lemma nauth_nin i j (NIN : i < j) :
      nauth i ⊢ nauth j ∗ ([∗ list] n ∈ (seq i (j - i)), sat n γ (interps (i:=n))).
    Proof.
      induction NIN.
      - iIntros "AUTH". remember (S i) as j.
        assert ((nauth_ra i) ≡
                  ((nauth_ra j)
                     ⋅
                     (discrete_fun_singleton i ((fun (n : nat) => OneShot.pending (As i) 1%Qp) : (_t As i))))) as H.
        { subst. intros a. rewrite /nauth_ra discrete_fun_lookup_op.
            destruct (decide (i = a)).
          - subst a. rewrite discrete_fun_lookup_singleton. des_ifs; try lia.
          - rewrite discrete_fun_lookup_singleton_ne //.
            destruct (le_dec a (S i)).
            { des_ifs; try lia. }
            { des_ifs; try lia. }
        }
        unfold nauth. rewrite H. iDestruct "AUTH" as "[AUTH NEW]".
        iPoseProof (nsat_alloc with "NEW") as "NEW".
        subst j. replace (S i - i) with 1 by lia. ss. iFrame.
      - iIntros "AUTH". iPoseProof (IHNIN with "AUTH") as "[AUTH SAT]".
        clear IHNIN. remember (S m) as y.
        assert ((nauth_ra m) ≡
                  ((nauth_ra y)
                     ⋅
                     (discrete_fun_singleton m ((fun (n : nat) => OneShot.pending (As m) 1%Qp) : (_t As m))))) as H.
        { subst. intros a.
          rewrite /nauth_ra discrete_fun_lookup_op.
          destruct (decide (m = a)).
          - subst a. rewrite discrete_fun_lookup_singleton. des_ifs; try lia.
          - rewrite discrete_fun_lookup_singleton_ne //.
            destruct (le_dec a (S m)).
            { des_ifs; try lia. }
            { des_ifs; try lia. }
        }
        unfold nauth. rewrite H. iDestruct "AUTH" as "[AUTH NEW]".
        iPoseProof (nsat_alloc with "NEW") as "NEW".
        subst y. iFrame.
        replace (S m - i) with ((m - i) + 1) by lia. rewrite seq_app.
        iApply big_sepL_app. iFrame.
        replace (i + (m - i)) with m by lia. ss. iFrame.
    Qed.

    Lemma nsats_nin (x n : nat) (NIN : x < n)
      : nsats x ∗ ([∗ list] m ∈ (seq x (n - x)), sat m γ (interps (i:=m))) ⊢ nsats n.
    Proof.
      rewrite ! nsats_equiv_l.
      iIntros "[SALL SAT]". unfold nsats_l.
      replace n with (x + (n - x)) by lia. rewrite seq_app. iFrame.
      replace (x + (n - x) - x) with (n - x) by lia. iFrame.
    Qed.

    Lemma nsats_in (x0 x1 : nat) :
      x0 < x1 -> nsats x1 ⊢ nsats x0 ∗ ([∗ list] n ∈ (seq x0 (x1 - x0)), sat n γ (interps (i:=n))).
    Proof.
      rewrite ! nsats_equiv_l.
      iIntros (LT) "SAT". unfold nsats_l.
      replace x1 with (x0 + (x1 - x0)) by lia. rewrite (seq_app _ _ 0).
      iPoseProof (big_sepL_app with "SAT") as "[SAT K]". iFrame.
      ss. replace (x0 + (x1 - x0) - x0) with (x1 - x0) by lia. iFrame.
    Qed.

    Lemma nsats_allocs x1 x2 :
      x1 < x2 -> nauth x1 ∗ nsats x1 ⊢ (nauth x2 ∗ nsats x2).
    Proof.
      iIntros (LT) "[AUTH SAT]". iPoseProof ((nauth_nin LT) with "AUTH") as "[AUTH NEW]".
      iPoseProof ((nsats_nin LT) with "[SAT NEW]") as "SAT". iFrame. iFrame.
    Qed.

    Lemma nsats_sat_sub i j :
      i < j -> ⊢ SubIProp (sat i γ (interps (i:=i))) (nsats j).
    Proof.
      iIntros (LT) "SATS". rewrite ! nsats_equiv_l.
      iPoseProof (big_sepL_lookup_acc _ _ i with "SATS") as "[SAT K]".
      { apply lookup_seq_lt. auto. }
      ss. iFrame. iModIntro. iIntros "SAT".
      iApply "K". iModIntro. iFrame.
    Qed.

  End NATKEY.

  Lemma nsats_alloc `{!regionsG Σ As} interps n :
    ⊢ #=> ∃ γ, nsats γ interps n ∗ nauth γ n.
  Proof.
    rewrite /nsats /nauth /sat /black.
    setoid_rewrite sep_conjs_eq.

    iMod (own_alloc (([^op list] i ↦ _ ∈ seq 0 n, to_black i []) ⋅ nauth_ra As n)) as (γ) "[S A]".
    { rewrite /to_black /nauth_ra.
      induction n as [|n IH].
      { ss. rewrite left_id. intros k k'. apply OneShot.pending_one_wf. }

      (* Dance around rewrites to make sure it works. *)
      rewrite seq_S /= big_opL_snoc seq_length.
      intros k k'. rewrite !discrete_fun_lookup_op.
      specialize (IH k k'). rewrite !discrete_fun_lookup_op in IH.

      destruct (lt_dec k n).
      - rewrite right_id in IH. des_ifs; [|lia].
        rewrite right_id.

        destruct (decide (n = k)); [lia|].
        rewrite discrete_fun_lookup_singleton_ne; [|lia].
        rewrite right_id. done.
      - destruct (lt_dec k (S n)).
        { rewrite right_id. destruct (decide (k = n)); try lia; subst.
          rewrite discrete_fun_lookup_singleton.
          des_ifs.
          apply nth_error_In in Heq. inv Heq.
        }
        destruct (decide (k = n)); try lia; subst.
        rewrite discrete_fun_lookup_singleton_ne; last lia.
        (* FIXME: setoid_rewrite left_id (ε k')) leads to all kinds of incorrect behavior. *)
        rewrite ucmra_unit_right_id //.
    }

    iModIntro. iFrame "A".
    rewrite big_opL_own_1. iApply (big_sepL_mono with "S").

    iIntros (x y Hxy) "OWN".
    iExists []. iFrame.
  Qed.

  Global Typeclasses Opaque white to_white black to_black.
End Regions.
Global Arguments Regions.t _ _ : clear implicits.
Global Arguments Regions.t {_} _.
