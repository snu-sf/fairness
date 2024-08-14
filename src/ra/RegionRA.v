From iris.algebra Require Import cmra updates.
From sflib Require Import sflib.
From Fairness Require Import PCM IPM IPropAux.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.PropExtensionality.
From Fairness Require Import Axioms.

From iris.bi Require Import derived_laws. Import bi.
Require Export Coq.Sorting.Mergesort. Import NatSort.

From Fairness Require Import MonotoneRA.
Require Import Program.

Set Implicit Arguments.

Module Region.
  Definition t A : ucmra := pointwise nat (OneShot.t A).

  Section REGION.
    Context {A: Type}.
    Notation t := (t A).
    Context `{@GRA.inG t Σ}.
    Notation iProp := (iProp Σ).

    Definition to_black (l : list A) : t :=
      (fun n =>
      match nth_error l n with
      | Some a => OneShot.shot a
      | _ => OneShot.pending A 1%Qp
      end): (nat ==> OneShot.t A)%ra.
    Definition black (l: list A): iProp :=
      OwnM (to_black l).

    Definition to_white (k : nat) (a : A) : t :=
      (fun n =>
        if Nat.eq_dec n k then OneShot.shot a else ε
      ) : (nat ==> OneShot.t A)%ra.
    Definition white (k: nat) (a: A): iProp :=
      OwnM (to_white k a).

    Global Instance Persistent_white k a: Persistent (white k a).
    Proof.
      rewrite /Persistent.
      iIntros "H". iPoseProof (own_persistent with "H") as "#HP".
      iApply (OwnM_proper with "HP").
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
      iIntros "BLACK #WHITE".
      iCombine "BLACK WHITE" as "OWN". iOwnWf "OWN". iPureIntro.
      specialize (H0 k). rewrite discrete_fun_lookup_op /to_black /to_white in H0.
      des_ifs; ss. f_equal.
      apply OneShot.shot_agree in H0. auto.
    Qed.

    Lemma white_agree k a0 a1
      :
        (white k a0)
        -∗
        (white k a1)
        -∗
        ⌜a0 = a1⌝.
    Proof.
      iIntros "WHITE0 WHITE1".
      iCombine "WHITE0 WHITE1" as "OWN". iOwnWf "OWN". iPureIntro.
      specialize (H0 k). rewrite discrete_fun_lookup_op /to_black /to_white in H0.
      des_ifs; ss.
      apply OneShot.shot_agree in H0. auto.
    Qed.

    Lemma black_alloc l a
      :
      (black l)
        -∗
        #=> (black (l++[a]) ∗ white (length l) a).
    Proof.
      iIntros "H". iPoseProof (OwnM_Upd with "H") as "> [BLACK WHITE]".
      2:{ iModIntro. iSplitL "BLACK"; [iApply "BLACK"|iApply "WHITE"]. }
      eapply pointwise_updatable. i.
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
          hexploit H1.
          2:{ i. erewrite H2. rewrite right_id. reflexivity. }
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
          { exfalso. eapply H2. replace (length l1) with (a2 - 1) by lia; ss. }
          { exfalso. eapply H2. replace (length l1) with (a1 - 1) by lia; ss. }
          { lia. }
        }
        rewrite map_map. auto.
      }
      { i. apply in_map_iff in IN. des.
        destruct x as [k1 a1]. ss. clarify. des_ifs.
        { assert (k1 = length l1 \/ k1 < length l1) by lia. des.
          { subst. eapply in_map with (f:=fst)in IN0. ss. }
          rewrite nth_error_app1; auto.
          hexploit (INS k1 a); auto. i. rewrite nth_error_app1 in H4; auto.
        }
        rewrite nth_error_app2; [|lia].
        hexploit (INS k1 a); auto. i.
        rewrite nth_error_app2 in H1; [|lia].
        replace (k1 - length l1) with (S (k1 - 1 - length l1)) in H1 by lia. ss.
      }
      i. rewrite map_map in H1. ss.
      r in H1. des. exists s.
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

  Global Typeclasses Opaque white to_white black to_black.
  Global Opaque white to_white black to_black.
End Region.

Module Regions.

  Definition _t (X : Type) (As : X → Type) (x: X): ucmra := pointwise nat (OneShot.t (As x)).
  Definition t (X : Type) (As : X → Type) : ucmra := pointwise_dep (_t As).

  Section REGION.

    Context `{X: Type}.
    Context `{As: X -> Type}.

    Notation t := (t As).

    Context `{@GRA.inG t Σ}.
    Notation iProp := (iProp Σ).

    Section SINGLE.

      Variable x : X.
      Local Notation A := (As x).

      Definition to_black (l: list A) : t :=
        maps_to_res_dep
        x
        ((fun n =>
            match nth_error l n with
            | Some a => OneShot.shot a
            | _ => OneShot.pending A 1%Qp
            end): (nat ==> OneShot.t A)%ra).

      Definition black (l: list A): iProp :=
        OwnM (to_black l).

      Definition to_white (k : nat) (a : A) : t :=
        maps_to_res_dep
        x
        ((fun n =>
            if Nat.eq_dec n k
            then OneShot.shot a
            else ε): (nat ==> OneShot.t A)%ra).
      Definition white (k: nat) (a: A): iProp :=
        OwnM (to_white k a).

      Global Instance Persistent_white k a: Persistent (white k a).
      Proof.
        rewrite /Persistent.
        iIntros "H".
        iPoseProof ((@OwnM_persistently _ _ H _) with "H") as "#X".
        assert (EQ:
          (core
             (maps_to_res_dep
                x
                ((fun n =>
                    if Nat.eq_dec n k then OneShot.shot a else ε): (nat ==> OneShot.t A)%ra)): t)
          ≡
          (maps_to_res_dep
             x
             ((fun n =>
                 if Nat.eq_dec n k then OneShot.shot a else ε): (nat ==> OneShot.t A)%ra): t)).
        { unfold maps_to_res_dep. intros y. rewrite discrete_fun_lookup_core. des_ifs.
          unfold eq_rect_r. ss. intros n. rewrite discrete_fun_lookup_core. des_ifs.
        }
        ss. rewrite EQ. iApply "X".
      Qed.

      Lemma black_white_in k a l
        :
        (black l)
          -∗
          (white k a)
          -∗
          ⌜nth_error l k = Some a⌝.
      Proof.
        iIntros "BLACK WHITE".
        iCombine "BLACK WHITE" as "OWN". iOwnWf "OWN". iPureIntro.
        unfold to_black,to_white,maps_to_res_dep in H0. specialize (H0 x).
        rewrite discrete_fun_lookup_op in H0. des_ifs.
        unfold eq_rect_r in H0. rewrite <- ! Eqdep.EqdepTheory.eq_rect_eq in H0.
        specialize (H0 k). rewrite discrete_fun_lookup_op in H0.
        destruct (Nat.eq_dec k k); ss.
        des_ifs.
        apply OneShot.shot_agree in H0. subst. auto.
      Qed.

      Lemma white_agree k a0 a1
        :
        (white k a0)
          -∗
          (white k a1)
          -∗
          ⌜a0 = a1⌝.
      Proof.
        iIntros "WHITE0 WHITE1".
        iCombine "WHITE0 WHITE1" as "OWN". iOwnWf "OWN". iPureIntro.
        unfold to_white,to_black,maps_to_res_dep in H0. specialize (H0 x). des_ifs.
        unfold eq_rect_r in H0.
        rewrite discrete_fun_lookup_op in H0. des_ifs.
        specialize (H0 k).
        rewrite discrete_fun_lookup_op -!Eqdep.EqdepTheory.eq_rect_eq in H0.
        des_ifs.
        apply OneShot.shot_agree in H0. auto.
      Qed.

      Lemma black_alloc l a
        :
        (black l)
          -∗
          #=> (black (l++[a]) ∗ white (length l) a).
      Proof.
        iIntros "H". iPoseProof (OwnM_Upd with "H") as "> [BLACK WHITE]".
        2:{ iModIntro. iSplitL "BLACK"; [iApply "BLACK"|iApply "WHITE"]. }
        setoid_rewrite maps_to_res_dep_add. apply maps_to_res_dep_updatable.
        eapply pointwise_updatable. i.
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
            hexploit H1.
            2:{ i. erewrite H2. rewrite right_id. reflexivity. }
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
            { exfalso. eapply H2. replace (length l1) with (a2 - 1) by lia; ss. }
            { exfalso. eapply H2. replace (length l1) with (a1 - 1) by lia; ss. }
            { lia. }
          }
          rewrite map_map. auto.
        }
        { i. apply in_map_iff in IN. des.
          destruct x0 as [k1 a1]. ss. clarify. des_ifs.
          { assert (k1 = length l1 \/ k1 < length l1) by lia. des.
            { subst. eapply in_map with (f:=fst)in IN0. ss. }
            rewrite nth_error_app1; auto.
            hexploit (INS k1 a); auto. i. rewrite nth_error_app1 in H4; auto.
          }
          rewrite nth_error_app2; [|lia].
          hexploit (INS k1 a); auto. i.
          rewrite nth_error_app2 in H1; [|lia].
          replace (k1 - length l1) with (S (k1 - 1 - length l1)) in H1 by lia. ss.
        }
        i. rewrite map_map in H1. ss.
        r in H1. des. exists s.
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
    Context `{Σ: GRA.t}.
    Context `{@GRA.inG (@t nat As) Σ}.
    Notation iProp := (iProp Σ).

    Variable interps : forall i, As i -> iProp.

    Definition nauth_ra (j : nat): @t nat As :=
      fun i => if (lt_dec i j)
            then ε
            else ((fun _ => OneShot.pending (As i) 1%Qp) : (@_t nat As i)).

    Definition nauth (j : nat) := OwnM (nauth_ra j).

    Definition nsats (j : nat) := sep_conjs (fun i => @sat nat As _ _ i (@interps i)) j.

    Definition nsats_l (j : nat) := ([∗ list] i ∈ (seq 0 j), @sat nat As _ _ i (@interps i))%I.

    Lemma unfold_nsats x :
      nsats (S x) = (nsats x ∗ sat x (interps (i:=x)))%I.
    Proof. ss. Qed.

    Lemma unfold_nsats_l x :
      nsats_l (S x) ⊢ (nsats_l x ∗ sat x (interps (i:=x)))%I.
    Proof.
      iIntros "A". unfold nsats_l. replace (seq 0 (S x)) with (seq 0 x ++ [x]).
      2:{ rewrite seq_S. ss. }
      iDestruct (big_sepL_app with "A") as "[A B]". ss. iFrame.
      iDestruct "B" as "[$ _]".
    Qed.

    Lemma fold_nsats_l x :
      (nsats_l x ∗ sat x (interps (i:=x)))%I ⊢ nsats_l (S x).
    Proof.
      iIntros "A". unfold nsats_l. replace (seq 0 (S x)) with (seq 0 x ++ [x]).
      2:{ rewrite seq_S. ss. }
      iApply big_sepL_app. ss. iDestruct "A" as "[A B]". iFrame.
    Qed.

    Lemma nsats_equiv_l x :
      nsats x ⊣⊢ nsats_l x.
    Proof.
      iSplit; iIntros "W".
      - iInduction x as [|x] "IH"; ss.
        iEval (rewrite unfold_nsats) in "W". iDestruct "W" as "[WS W]".
        iApply fold_nsats_l. iFrame. iApply "IH"; auto.
      - iInduction x as [|x] "IH"; ss.
        iEval (rewrite unfold_nsats_l) in "W". iDestruct "W" as "[WS W]".
        rewrite unfold_nsats. iFrame. iApply "IH"; auto.
    Qed.


    Lemma nauth_init_zero :
      OwnM ((fun i => ((fun _ => OneShot.pending (As i) 1%Qp) : (@_t nat As i))) : @t nat As)
           ⊢ nauth 0.
    Proof.
      iIntros "OWN". iFrame.
    Qed.

    Lemma nsat_alloc i :
      OwnM (maps_to_res_dep i ((λ _ : nat, OneShot.pending (As i) 1%Qp) : @_t nat As i) : @t nat As)
           ⊢ sat i (interps (i:=i)).
    Proof.
      iIntros "OWN". iExists []. ss. unfold black,to_black.
      replace ((fun n => match nth_error [] n with
                      | Some a => OneShot.shot a
                      | None => OneShot.pending (As i) 1%Qp
                      end) : @_t nat As i)
        with
        ((fun _ => OneShot.pending (As i) 1%Qp) : @_t nat As i).
      { iFrame. }
      { extensionalities n. exploit nth_error_None. intros. des. erewrite x1; ss. lia. }
    Qed.

    Lemma nauth_nin i j (NIN : i < j) :
      nauth i ⊢ nauth j ∗ ([∗ list] n ∈ (seq i (j - i)), @sat nat As _ _ n (@interps n)).
    Proof.
      induction NIN.
      - iIntros "AUTH". remember (S i) as j.
        assert ((nauth_ra i) =
                  ((nauth_ra j)
                     ⋅
                     (maps_to_res_dep i ((fun (n : nat) => OneShot.pending (As i) 1%Qp) : (@_t nat As i))))).
        { subst. extensionalities a. unfold nauth_ra, maps_to_res_dep.
          rewrite discrete_fun_lookup_op.
          destruct (excluded_middle_informative (a = i)).
          - subst a. des_ifs; try lia.
          - destruct (le_dec a (S i)).
            { des_ifs; try lia. }
            { des_ifs; try lia. }
        }
        unfold nauth. rewrite H0. iDestruct "AUTH" as "[AUTH NEW]".
        iPoseProof (nsat_alloc with "NEW") as "NEW".
        subst j. replace (S i - i) with 1 by lia. ss. iFrame.
      - iIntros "AUTH". iPoseProof (IHNIN with "AUTH") as "[AUTH SAT]".
        clear IHNIN. remember (S m) as y.
        assert ((nauth_ra m) =
                  ((nauth_ra y)
                     ⋅
                     (maps_to_res_dep m ((fun (n : nat) => OneShot.pending (As m) 1%Qp) : (@_t nat As m))))).
        { subst. extensionalities a. unfold nauth_ra, maps_to_res_dep.
          rewrite discrete_fun_lookup_op.
          destruct (excluded_middle_informative (a = m)).
          - subst a. des_ifs; try lia.
          - destruct (le_dec a (S m)).
            { des_ifs; try lia.
            }
            { des_ifs; try lia.
            }
        }
        unfold nauth. rewrite H0. iDestruct "AUTH" as "[AUTH NEW]".
        iPoseProof (nsat_alloc with "NEW") as "NEW".
        subst y. iFrame.
        replace (S m - i) with ((m - i) + 1) by lia. rewrite seq_app.
        iApply big_sepL_app. iFrame.
        replace (i + (m - i)) with m by lia. ss. iFrame.
    Qed.

    Lemma nsats_nin (x n : nat) (NIN : x < n)
      : nsats x ∗ ([∗ list] m ∈ (seq x (n - x)), @sat nat As _ _ m (@interps m)) ⊢ nsats n.
    Proof.
      rewrite ! nsats_equiv_l.
      iIntros "[SALL SAT]". unfold nsats_l.
      replace n with (x + (n - x)) by lia. rewrite seq_app. iFrame.
      replace (x + (n - x) - x) with (n - x) by lia. iFrame.
    Qed.

    Lemma nsats_in (x0 x1 : nat) :
      x0 < x1 -> nsats x1 ⊢ nsats x0 ∗ ([∗ list] n ∈ (seq x0 (x1 - x0)), sat n (interps (i:=n))).
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
      i < j -> ⊢ SubIProp (sat i (interps (i:=i))) (nsats j).
    Proof.
      iIntros (LT) "SATS". rewrite ! nsats_equiv_l.
      iPoseProof (big_sepL_lookup_acc _ _ i with "SATS") as "[SAT K]".
      { apply lookup_seq_lt. auto. }
      ss. iFrame. iModIntro. iIntros "SAT".
      iApply "K". iModIntro. iFrame.
    Qed.

  End NATKEY.

  Global Typeclasses Opaque white to_white black to_black.
  Global Opaque white to_white black to_black.
End Regions.
Global Arguments Regions.t _ _ : clear implicits.
Global Arguments Regions.t {_} _.
