From sflib Require Import sflib.

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.PropExtensionality.
From Fairness Require Import Axioms.

From iris.algebra Require Import cmra updates functions.
From iris.bi Require Import derived_laws. Import bi.
From Fairness Require Import PCM IPM IPropAux IUpd OneShotRA.
Require Export Coq.Sorting.Mergesort. Import NatSort.

Require Import Program.

Set Implicit Arguments.

Section LISTSUB.

  Definition list_sub {A} (s0 s1: list A): Prop :=
    exists s, Permutation (s ++ s0) s1.

  Global Program Instance list_sub_PreOrder A: PreOrder (@list_sub A).
  Next Obligation.
  Proof.
    ii. exists []. ss.
  Qed.
  Next Obligation.
  Proof.
    intros x y z SUB1 SUB2. unfold list_sub in *. des.
    rewrite <- SUB1 in SUB2. exists (s ++ s0).
    rewrite <- app_assoc. auto.
  Qed.

  Global Instance permutation_list_sub_proper S :
    Proper ((≡ₚ) ==> (≡ₚ) ==> (↔)) (@list_sub S).
  Proof.
    intros ?? P1 ?? P2. unfold list_sub. split.
    { intros P3. des. exists s. rewrite <-P1. rewrite P3. auto. }
    { intros P3. des. exists s. rewrite P2. rewrite <-P3. rewrite P1. auto. }
    Qed.

End LISTSUB.

(* TODO: move somewhere else *)
Local Lemma injective_map_NoDup_strong S B (f: S -> B) (l: list S)
  (INJ: forall a0 a1 (IN0: List.In a0 l) (IN1: List.In a1 l)
              (EQ: f a0 = f a1), a0 = a1)
  (ND: List.NoDup l)
  :
  List.NoDup (List.map f l).
  Proof.
  revert INJ ND. induction l.
  { i. s. econs. }
  i. inv ND. ss. econs; eauto.
  intros IN. rewrite in_map_iff in IN. des.
  hexploit (INJ x a); eauto. i. subst. ss.
Qed.

Module Region.
  Definition t A : ucmra := nat -d> (OneShot.t A).

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
      end): (nat -d> OneShot.t A).
    Definition black (l: list A): iProp :=
      OwnM (to_black l).

    Definition to_white (k : nat) (a : A) : t :=
      discrete_fun_singleton k (OneShot.shot a).
    Definition white (k: nat) (a: A): iProp :=
      OwnM (to_white k a).

    Global Instance Persistent_white k a: Persistent (white k a).
    Proof. apply _. Qed.

    Lemma black_white_in k a l
      :
      (black l)
        -∗
        (white k a)
        -∗
        ⌜nth_error l k = Some a⌝.
    Proof.
      iIntros "BLACK #WHITE".
      iCombine "BLACK WHITE" gives %H0.
      iPureIntro.
      specialize (H0 k). rewrite discrete_fun_lookup_op /to_black /to_white discrete_fun_lookup_singleton in H0.
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
      iCombine "WHITE0 WHITE1" gives %WF.
      iPureIntro.
      rewrite discrete_fun_singleton_op discrete_fun_singleton_valid in WF.
      apply OneShot.shot_agree in WF. auto.
    Qed.

    Lemma black_alloc l a
      :
      (black l)
        -∗
        #=> (black (l++[a]) ∗ white (length l) a).
    Proof.
      iIntros "H". iMod (OwnM_Upd with "H") as "[$ $]"; [|done].
      eapply discrete_fun_update. i.
      rewrite /to_black /to_white discrete_fun_lookup_op.
      destruct (nth_error l a0) eqn:EQ.
      { rewrite nth_error_app1.
        2:{ apply nth_error_Some; auto. rewrite EQ; auto. }
        rewrite EQ.
        destruct (decide (length l = a0)) as [<-|];
        rewrite ?discrete_fun_lookup_singleton ?discrete_fun_lookup_singleton_ne //.
        { exploit nth_error_Some.
          erewrite EQ. i. des. hexploit x0; auto. i. lia.
        }
      }
      { dup EQ. eapply nth_error_None in EQ. rewrite nth_error_app2; auto.
        destruct (Nat.eq_dec a0 (length l)).
        { subst. replace (length l - length l) with 0 by lia.
          rewrite discrete_fun_lookup_singleton. ss. etrans.
          { eapply OneShot.pending_shot. }
          { instantiate (1:=a). rewrite -OneShot.shot_dup. done. }
        }
        { rewrite discrete_fun_lookup_singleton_ne //.
          hexploit nth_error_None. i. des.
          hexploit H1.
          2:{ i. erewrite H2. rewrite right_id. reflexivity. }
          { ss. lia. }
        }
      }
    Qed.

    Variable interp: A -> iProp.
    (* TODO: Duplication duplication. *)
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

  Global Opaque white to_white black to_black.
End Region.

Module Regions.

  Definition _t (X : Type) (As : X → Type) (x: X): ucmra := nat -d> (OneShot.t (As x)).
  Definition t (X : Type) (As : X → Type) : ucmra := discrete_funUR (_t As).

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
        maps_to_res x
          ((λ n,
              match nth_error l n with
              | Some a => OneShot.shot a
              | _ => OneShot.pending A 1
              end) : discrete_fun _).

      Definition black (l: list A): iProp :=
        OwnM (to_black l).

      Definition to_white (k : nat) (a : A) : t :=
        maps_to_res x
          (discrete_fun_singleton k (OneShot.shot a)).
      Definition white (k: nat) (a: A): iProp :=
        OwnM (to_white k a).

      Global Instance Persistent_white k a: Persistent (white k a).
      Proof. apply _. Qed.

      Lemma black_white_in k a l
        :
        (black l)
          -∗
          (white k a)
          -∗
          ⌜nth_error l k = Some a⌝.
      Proof.
        iIntros "BLACK WHITE". iCombine "BLACK WHITE" gives %WF.
        iPureIntro.
        rewrite discrete_fun_singleton_op discrete_fun_singleton_valid in WF.
        specialize (WF k).
        rewrite discrete_fun_lookup_op discrete_fun_lookup_singleton in WF.
        des_ifs.
        apply OneShot.shot_agree in WF. subst. auto.
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
        iPureIntro.
        rewrite !discrete_fun_singleton_op !discrete_fun_singleton_valid in WF.
        by apply OneShot.shot_agree in WF.
      Qed.

      Lemma black_alloc l a
        :
        (black l)
          -∗
          #=> (black (l++[a]) ∗ white (length l) a).
      Proof.
        iIntros "H". iMod (OwnM_Upd with "H") as "[$ $]"; [|done].
        rewrite discrete_fun_singleton_op.
        apply discrete_fun_singleton_update, discrete_fun_update => a0.
        rewrite discrete_fun_lookup_op /=.
        destruct (nth_error l a0) eqn:EQ.
        { rewrite nth_error_app1.
          2:{ apply nth_error_Some; auto. rewrite EQ; auto. }
          rewrite EQ.
          destruct (decide (length l = a0)) as [<-|];
          rewrite ?discrete_fun_lookup_singleton ?discrete_fun_lookup_singleton_ne //.
          exploit nth_error_Some. erewrite EQ. i. des. hexploit x1; auto. i. lia.
        }
        { dup EQ. eapply nth_error_None in EQ. rewrite nth_error_app2; auto.
          destruct (decide (length l = a0)) as [<-|];
            rewrite ?discrete_fun_lookup_singleton ?discrete_fun_lookup_singleton_ne //.
          { rewrite Nat.sub_diag. ss. etrans.
            { eapply OneShot.pending_shot. }
            { rewrite -OneShot.shot_dup //. }
          }
          { hexploit nth_error_None. i. des.
            hexploit H1.
            2:{ i. erewrite H2. rewrite right_id. reflexivity. }
            { ss. lia. }
          }
        }
      Qed.

      Variable interp: A -> iProp.

      (* FIXME: LOL this is dupe of ListIProp *)
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
    (* The first is an maps_to_res so that they are actually the same instance of discrete_fun_singleton *)
      OwnM (maps_to_res i ((λ _ : nat, OneShot.pending (As i) 1%Qp) : @_t nat As i) : @t nat As)
           ⊢ sat i (interps (i:=i)).
    Proof.
      iIntros "OWN". iExists []. ss. rewrite right_id /black /to_black.
      iApply (OwnM_proper with "OWN").
      f_equiv.
      intros n. exploit nth_error_None. intros. des. erewrite x1; ss. lia.
    Qed.

    Lemma nauth_nin i j (NIN : i < j) :
      nauth i ⊢ nauth j ∗ ([∗ list] n ∈ (seq i (j - i)), @sat nat As _ _ n (@interps n)).
    Proof.
      induction NIN.
      - iIntros "AUTH". remember (S i) as j.
        assert (nauth_ra i ≡
                  nauth_ra j
                    ⋅
                    maps_to_res i ((λ _, OneShot.pending (As i) 1) : discrete_fun _)).
        { subst. intros a. unfold nauth_ra.
          rewrite discrete_fun_lookup_op.
          destruct (decide (i = a)) as [->|]; rewrite ?discrete_fun_lookup_singleton ?discrete_fun_lookup_singleton_ne //.
          - des_ifs; lia.
          - repeat des_ifs; lia.
        }
        unfold nauth. rewrite H0. iDestruct "AUTH" as "[AUTH NEW]".
        iPoseProof (nsat_alloc with "NEW") as "NEW".
        subst j. replace (S i - i) with 1 by lia. ss. iFrame.
      - iIntros "AUTH". iPoseProof (IHNIN with "AUTH") as "[AUTH SAT]".
        clear IHNIN. remember (S m) as y.
        assert (nauth_ra m ≡
                  nauth_ra y
                     ⋅
                     maps_to_res m ((λ _, OneShot.pending (As m) 1) : discrete_fun _)).
        { subst. intros a. unfold nauth_ra.
          rewrite discrete_fun_lookup_op.
          destruct (decide (m = a)) as [->|];
            rewrite ?discrete_fun_lookup_singleton ?discrete_fun_lookup_singleton_ne //.
          - des_ifs; lia.
          - repeat des_ifs; lia.
        }
        unfold nauth. rewrite H0. iDestruct "AUTH" as "[AUTH NEW]".
        iPoseProof (nsat_alloc with "NEW") as "NEW".
        subst y. iFrame.
        replace (S m - i) with ((m - i) + 1) by lia. rewrite seq_app.
        iApply big_sepL_app. iFrame.
        replace (i + (m - i)) with m by lia. ss. iFrame.
    Qed.

    (* TODO: repetition with stuff in wsats *)
    Lemma nsats_nin (x n : nat) (NIN : x < n)
      : nsats x ∗ ([∗ list] m ∈ (seq x (n - x)), @sat nat As _ _ m (@interps m)) ⊢ nsats n.
    Proof.
      rewrite ! nsats_equiv_l /nsats_l -big_sepL_app -seq_app.
      replace (x + (n - x)) with n by lia. done.
    Qed.

    Lemma nsats_in (x0 x1 : nat) :
      x0 < x1 -> nsats x1 ⊢ nsats x0 ∗ ([∗ list] n ∈ (seq x0 (x1 - x0)), sat n (interps (i:=n))).
    Proof.
      rewrite ! nsats_equiv_l /nsats_l -big_sepL_app -seq_app => ?.
      replace (x0 + (x1 - x0)) with x1 by lia. done.
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

End Regions.
Global Arguments Regions.t _ _ : clear implicits.
Global Arguments Regions.t {_} _.
