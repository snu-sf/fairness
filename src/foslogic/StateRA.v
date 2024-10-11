From sflib Require Import sflib.
From Paco Require Import paco.
From Fairness Require Import PCM ITreeLib pind.
Require Import Program.
From Fairness Require Import IPropFOS IPMFOS.
From Fairness Require Import PCMFOS MonotonePCM NatMapRAFOS Mod FairBeh.
From Fairness Require Import Axioms.

Set Implicit Arguments.

Section UPD.
  Variable A: Type.
  Context `{IN: @GRA.inG (Auth.t (Excl.t A)) Σ}.

  Lemma black_white_update a0 a' a1
    :
    (OwnM (Auth.black (Excl.just a0: @Excl.t A)))
      -∗
      (OwnM (Auth.white (Excl.just a': @Excl.t A)))
      -∗
      #=> (OwnM (Auth.black (Excl.just a1: @Excl.t A)) ** OwnM (Auth.white (Excl.just a1: @Excl.t A))).
  Proof.
    iIntros "H0 H1". iCombine "H0 H1" as "H".
    iPoseProof (OwnM_Upd with "H") as "> [H0 H1]".
    { apply Auth.auth_update.
      instantiate (1:=Excl.just a1). instantiate (1:=Excl.just a1).
      ii. des. ur in FRAME. des_ifs. split.
      { ur. ss. }
      { ur. ss. }
    }
    iModIntro. iFrame.
  Qed.

  Lemma black_white_equal a a'
    :
    (OwnM (Auth.black (Excl.just a: @Excl.t A)))
      -∗
      (OwnM (Auth.white (Excl.just a': @Excl.t A)))
      -∗
      ⌜a = a'⌝.
  Proof.
    iIntros "H0 H1". iCombine "H0 H1" as "H".
    iOwnWf "H". ur in H. des.
    rr in H. des. ur in H. des_ifs.
  Qed.

  Lemma white_white_excl a a'
    :
    (OwnM (Auth.white (Excl.just a: @Excl.t A)))
      -∗
      (OwnM (Auth.white (Excl.just a': @Excl.t A)))
      -∗
      ⌜False⌝.
  Proof.
    iIntros "H0 H1". iCombine "H0 H1" as "H".
    iOwnWf "H". ur in H. ur in H. auto.
  Qed.

End UPD.

Section OWNS.

  Variable (Id: Type).
  Context `{R: URA.t}.
  Context `{IN1: @GRA.inG R Σ}.
  Context `{IN2: @GRA.inG (Id ==> R)%ra Σ}.
  (* Context `{IN: @GRA.inG (Id ==> (Auth.t (Excl.t A)))%ra Σ}. *)

  Definition OwnMs (s: Id -> Prop) (u: R): iProp :=
    (OwnM ((fun i =>
              if (excluded_middle_informative (s i))
              then u
              else ε): (Id ==> R)%ra)).

  (* Definition OwnMs (s: Id -> Prop) (u: Id -> R): iProp := *)
  (*   (OwnM ((fun i => *)
  (*             if (excluded_middle_informative (s i)) *)
  (*             then (u i) *)
  (*             else ε): (Id ==> R)%ra)). *)

(* End OWNS. *)

(* Section TEST. *)

(*   Variable (Id: Type). *)
(*   Variable A: Type. *)
(*   Context `{IN: @GRA.inG (Id ==> (Auth.t (Excl.t (Id * A))))%ra Σ}. *)

(*   Definition owns_auth (s: Id -> Prop) (a: A): iProp := *)
(*     OwnMs *)
(*       s *)
(*       (fun i => (Auth.black (Excl.just (i, a): Excl.t (Id * A))) *)
(*                ⋅ (Auth.white (Excl.just (i, a): Excl.t (Id * A)))). *)

(*   Definition owns (s: Id -> Prop) (u: A): iProp := *)
(*     (OwnM ((fun i => *)
(*               if (excluded_middle_informative (s i)) *)
(*               then ((Auth.black (Excl.just u: Excl.t A)) ⋅ (Auth.white (Excl.just u: Excl.t A))) *)
(*               else ε): (Id ==> (Auth.t (Excl.t A)))%ra)). *)

(* End TEST. *)

  Lemma OwnMs_impl (s0 s1: Id -> Prop) u
        (IMPL: forall i (IN: s0 i), s1 i)
    :
    (OwnMs s1 u)
      -∗
      (OwnMs s0 u).
  Proof.
    iIntros "OWNMS".
    iApply (OwnM_extends with "OWNMS"). apply pointwise_extends.
    i. des_ifs; try by reflexivity.
    { exfalso. eauto. }
    { eexists _. rewrite URA.unit_idl. ss. }
  Qed.

  Lemma OwnMs_empty s u
        (EMPTY: forall i, ~ s i)
    :
    ⊢ OwnMs s u.
  Proof.
    iIntros. iApply (OwnM_extends with "[]").
    2:{ iApply (@OwnM_unit (Id ==> R)%ra). }
    apply pointwise_extends. i. des_ifs.
    { exfalso. eapply EMPTY; eauto. }
    eexists _. rewrite URA.unit_idl. eauto.
  Qed.

  Lemma OwnMs_fold (s0 s1: Id -> Prop) i u
        (IMPL: forall j (IN: s0 j), s1 j \/ j = i)
    :
    ((OwnMs s1 u) ** (maps_to i u))
      -∗
      (OwnMs s0 u).
  Proof.
    iIntros "[OWNMS OWN]".
    iCombine "OWNMS OWN" as "OWNMS".
    iApply (OwnM_extends with "OWNMS"). apply pointwise_extends.
    i. erewrite ! (@unfold_pointwise_add Id R). unfold maps_to_res.
    des_ifs; ss; repeat rewrite URA.unit_id; repeat rewrite URA.unit_idl; ss; try by reflexivity.
    { eexists. apply URA.add_comm. }
    { hexploit IMPL; eauto. i. des; ss. }
    { eexists. rewrite URA.unit_idl. ss. }
    { eexists. rewrite URA.unit_idl. ss. }
    { eexists. rewrite URA.unit_idl. ss. }
  Qed.

  Definition OwnMs_unfold (s0 s1: Id -> Prop) i u
             (IMPL: forall j (IN: s0 j \/ j = i), s1 j)
             (NIN: ~ s0 i)
    :
    (OwnMs s1 u)
      -∗
      (OwnMs s0 u ** maps_to i u).
  Proof.
    iIntros "OWNMS".
    iPoseProof (OwnM_extends with "OWNMS") as "[OWNMS0 OWNMS1]".
    { instantiate (1:=maps_to_res i (u: R): (Id ==> R)%ra).
      instantiate (1:=(fun i =>
                         if (excluded_middle_informative (s0 i))
                         then u
                         else ε)).
      erewrite ! (@unfold_pointwise_add Id R). unfold maps_to_res.
      apply pointwise_extends. i.
      des_ifs; ss; repeat rewrite URA.unit_id; repeat rewrite URA.unit_idl; ss; try by reflexivity.
      { exfalso. eapply n0. auto. }
      { exfalso. eapply n0. auto. }
      { eexists. rewrite URA.unit_idl. ss. }
    }
    iFrame.
  Qed.

  Definition OwnMs_combine (s0 s1: Id -> Prop) u
    :
    (OwnMs s0 u ** OwnMs s1 u)
      -∗
      (OwnMs (fun i => s0 i \/ s1 i) u).
  Proof.
    iIntros "[OWNMS0 OWNMS1]".
    iCombine "OWNMS0 OWNMS1" as "OWNMS".
    iApply (OwnM_extends with "OWNMS"). apply pointwise_extends.
    i. erewrite ! (@unfold_pointwise_add Id R).
    des_ifs; ss; repeat rewrite URA.unit_id; repeat rewrite URA.unit_idl; ss; try by reflexivity.
    { eexists. eauto. }
    { des; ss. }
    { eexists. rewrite URA.unit_idl. ss. }
    { eexists. rewrite URA.unit_idl. ss. }
    { eexists. rewrite URA.unit_idl. ss. }
  Qed.

  Definition OwnMs_split (s0 s1: Id -> Prop) u
             (DISJOINT: forall i (IN0: s0 i) (IN1: s1 i), False)
    :
    (OwnMs (fun i => s0 i \/ s1 i) u)
      -∗
      (OwnMs s0 u ** OwnMs s1 u).
  Proof.
    iIntros "OWNMS".
    iPoseProof (OwnM_extends with "OWNMS") as "[OWNMS0 OWNMS1]".
    2:{ iSplitL "OWNMS0"; [iExact "OWNMS0"|iExact "OWNMS1"]. }
    { apply pointwise_extends.
      i. erewrite ! (@unfold_pointwise_add Id R).
      des_ifs; ss; repeat rewrite URA.unit_id; repeat rewrite URA.unit_idl; ss; try by reflexivity.
      { exfalso. eapply DISJOINT; eauto. }
      { exfalso. eapply n; eauto. }
      { exfalso. eapply n0; eauto. }
      { exfalso. eapply n0; eauto. }
      { des; ss. }
    }
  Qed.

End OWNS.


Section UPDNATMAP.
  Variable A: Type.
  Context `{NATMAPRA: @GRA.inG (Auth.t (NatMapRAFOS.t A)) Σ}.

  Lemma NatMapRA_find_some m k a
    :
    (OwnM (Auth.black (Some m: NatMapRAFOS.t A)))
      -∗
      (OwnM (Auth.white (NatMapRAFOS.singleton k a: NatMapRAFOS.t A)))
      -∗
      (⌜NatMap.find k m = Some a⌝).
  Proof.
    iIntros "B W". iCombine "B W" as "BW". iOwnWf "BW".
    eapply Auth.auth_included in H. eapply NatMapRAFOS.extends_singleton_iff in H. auto.
  Qed.

  Lemma NatMapRA_singleton_unique k0 k1 a0 a1
    :
    (OwnM (Auth.white (NatMapRAFOS.singleton k0 a0: NatMapRAFOS.t A)))
      -∗
      (OwnM (Auth.white (NatMapRAFOS.singleton k1 a1: NatMapRAFOS.t A)))
      -∗
      (⌜k0 <> k1⌝).
  Proof.
    iIntros "W0 W1". iCombine "W0 W1" as "W". iOwnWf "W".
    ur in H. eapply NatMapRAFOS.singleton_unique in H. auto.
  Qed.

  Lemma NatMapRA_remove m k a
    :
    (OwnM (Auth.black (Some m: NatMapRAFOS.t A)))
      -∗
      (OwnM (Auth.white (NatMapRAFOS.singleton k a: NatMapRAFOS.t A)))
      -∗
      #=>(OwnM (Auth.black (Some (NatMap.remove k m): NatMapRAFOS.t A))).
  Proof.
    iIntros "B W". iCombine "B W" as "BW". iApply OwnM_Upd. 2: iFrame.
    eapply Auth.auth_dealloc. eapply NatMapRAFOS.remove_local_update.
  Qed.

  Lemma NatMapRA_add m k a
        (NONE: NatMap.find k m = None)
    :
    (OwnM (Auth.black (Some m: NatMapRAFOS.t A)))
      -∗
      #=>((OwnM (Auth.black (Some (NatMap.add k a m): NatMapRAFOS.t A)
                            ⋅ Auth.white (NatMapRAFOS.singleton k a: NatMapRAFOS.t A)))
         ).
  Proof.
    iIntros "B". iApply OwnM_Upd. 2: iFrame.
    eapply Auth.auth_alloc. eapply NatMapRAFOS.add_local_update. auto.
  Qed.

End UPDNATMAP.


Section PAIR.
  Variable A: Type.
  Variable B: Type.

  Context `{IN: @GRA.inG (Auth.t (Excl.t (A * B))) Σ}.
  Context `{INA: @GRA.inG (Auth.t (Excl.t A)) Σ}.
  Context `{INB: @GRA.inG (Auth.t (Excl.t B)) Σ}.

  Definition pair_sat: iProp :=
    ∃ a b,
      (OwnM (Auth.white (Excl.just (a, b): @Excl.t (A * B))))
        **
        (OwnM (Auth.black (Excl.just a: @Excl.t A)))
        **
        (OwnM (Auth.black (Excl.just b: @Excl.t B)))
  .

  Lemma pair_access_fst a
    :
    (OwnM (Auth.white (Excl.just a: @Excl.t A)))
      -∗
      (pair_sat)
      -∗
      (∃ b, (OwnM (Auth.white (Excl.just (a, b): @Excl.t (A * B))))
              **
              (∀ a,
                  ((OwnM (Auth.white (Excl.just (a, b): @Excl.t (A * B))))
                     -*
                     #=> ((OwnM (Auth.white (Excl.just a: @Excl.t A))) ** (pair_sat))))).
  Proof.
    iIntros "H [% [% [[H0 H1] H2]]]".
    iPoseProof (black_white_equal with "H1 H") as "%". subst.
    iExists _. iFrame. iIntros (?) "H0".
    iPoseProof (black_white_update with "H1 H") as "> [H1 H]".
    iModIntro. iFrame. iExists _, _. iFrame.
  Qed.

  Lemma pair_access_snd b
    :
    (OwnM (Auth.white (Excl.just b: @Excl.t B)))
      -∗
      (pair_sat)
      -∗
      (∃ a, (OwnM (Auth.white (Excl.just (a, b): @Excl.t (A * B))))
              **
              (∀ b,
                  ((OwnM (Auth.white (Excl.just (a, b): @Excl.t (A * B))))
                     -*
                     #=> ((OwnM (Auth.white (Excl.just b: @Excl.t B))) ** (pair_sat))))).
  Proof.
    iIntros "H [% [% [[H0 H1] H2]]]".
    iPoseProof (black_white_equal with "H2 H") as "%". subst.
    iExists _. iFrame. iIntros (?) "H0".
    iPoseProof (black_white_update with "H2 H") as "> [H2 H]".
    iModIntro. iFrame. iExists _, _. iFrame.
  Qed.
End PAIR.


From Fairness Require Import FairRA.

Section INVARIANT.
  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable ident_src: ID.
  Variable ident_tgt: ID.

  Definition stateSrcRA: URA.t := Auth.t (Excl.t (option state_src)).
  Definition stateTgtRA: URA.t := Auth.t (Excl.t (option state_tgt)).
  Definition identSrcRA: URA.t := FairRA.srct ident_src.
  Definition identTgtRA: URA.t := FairRA.tgtt ident_tgt.
  Definition ThreadRA: URA.t := Auth.t (NatMapRAFOS.t unit).
  Definition ArrowRA: URA.t :=
    Region.t ((sum_tid ident_tgt) * nat * Ord.t * Qp * nat).
  Definition EdgeRA: URA.t :=
    Region.t (nat * nat * Ord.t).

  Context `{MONORA: @GRA.inG monoRA Σ}.
  Context `{THDRA: @GRA.inG ThreadRA Σ}.
  Context `{STATESRC: @GRA.inG stateSrcRA Σ}.
  Context `{STATETGT: @GRA.inG stateTgtRA Σ}.
  Context `{IDENTSRC: @GRA.inG identSrcRA Σ}.
  Context `{IDENTTGT: @GRA.inG identTgtRA Σ}.
  Context `{OBLGRA: @GRA.inG ObligationRA.t Σ}.
  Context `{ARROWRA: @GRA.inG ArrowRA Σ}.
  Context `{EDGERA: @GRA.inG EdgeRA Σ}.
  Context `{ONESHOTRA: @GRA.inG (@FiniteMap.t (OneShot.t unit)) Σ}.

  Definition fairI: iProp :=
    (ObligationRA.edges_sat)
      **
      (ObligationRA.arrows_sat (S := sum_tid ident_tgt)).

  Definition default_I: TIdSet.t -> (@imap ident_src owf) -> (@imap (sum_tid ident_tgt) nat_wf) -> state_src -> state_tgt -> iProp :=
    fun ths im_src im_tgt st_src st_tgt =>
      (OwnM (Auth.black (Some ths: (NatMapRAFOS.t unit)): ThreadRA))
        **
        (OwnM (Auth.black (Excl.just (Some st_src): @Excl.t (option state_src)): stateSrcRA))
        **
        (OwnM (Auth.black (Excl.just (Some st_tgt): @Excl.t (option state_tgt)): stateTgtRA))
        **
        (FairRA.sat_source im_src)
        **
        (FairRA.sat_target im_tgt ths)
        **
        (ObligationRA.edges_sat)
        **
        (ObligationRA.arrows_sat (S := sum_tid ident_tgt))
  .

  Definition default_I_past (tid: thread_id): TIdSet.t -> (@imap ident_src owf) -> (@imap (sum_tid ident_tgt) nat_wf) -> state_src -> state_tgt -> iProp :=
    fun ths im_src im_tgt st_src st_tgt =>
      (∃ im_tgt0,
          (⌜fair_update im_tgt0 im_tgt (prism_fmap inlp (tids_fmap tid ths))⌝)
            ** (default_I ths im_src im_tgt0 st_src st_tgt))%I.

  Definition own_thread (tid: thread_id): iProp :=
    (OwnM (Auth.white (NatMapRAFOS.singleton tid tt: NatMapRAFOS.t unit): ThreadRA)).

  Lemma own_thread_unique tid0 tid1
    :
    (own_thread tid0)
      -∗
      (own_thread tid1)
      -∗
      ⌜tid0 <> tid1⌝.
  Proof.
    iIntros "OWN0 OWN1". iCombine "OWN0 OWN1" as "OWN".
    iOwnWf "OWN". ur in H. apply NatMapRAFOS.singleton_unique in H.
    iPureIntro. auto.
  Qed.

  Lemma default_I_update_st_src ths im_src im_tgt st_src0 st_tgt st_src' st_src1
    :
    (default_I ths im_src im_tgt st_src0 st_tgt)
      -∗
      (OwnM (Auth.white (Excl.just (Some st_src'): @Excl.t (option state_src)): stateSrcRA))
      -∗
      #=> (OwnM (Auth.white (Excl.just (Some st_src1): @Excl.t (option state_src))) ** default_I ths im_src im_tgt st_src1 st_tgt).
  Proof.
    unfold default_I. iIntros "[[[[[[A B] C] D] E] F] G] OWN".
    iPoseProof (black_white_update with "B OWN") as "> [B OWN]".
    iModIntro. iFrame.
  Qed.

  Lemma default_I_update_st_tgt ths im_src im_tgt st_src st_tgt0 st_tgt' st_tgt1
    :
    (default_I ths im_src im_tgt st_src st_tgt0)
      -∗
      (OwnM (Auth.white (Excl.just (Some st_tgt'): @Excl.t (option state_tgt)): stateTgtRA))
      -∗
      #=> (OwnM (Auth.white (Excl.just (Some st_tgt1): @Excl.t (option state_tgt))) ** default_I ths im_src im_tgt st_src st_tgt1).
  Proof.
    unfold default_I. iIntros "[[[[[[A B] C] D] E] F] G] OWN".
    iPoseProof (black_white_update with "C OWN") as "> [C OWN]".
    iModIntro. iFrame.
  Qed.

  Lemma default_I_get_st_src ths im_src im_tgt st_src st_tgt st
    :
    (default_I ths im_src im_tgt st_src st_tgt)
      -∗
      (OwnM (Auth.white (Excl.just (Some st): @Excl.t (option state_src)): stateSrcRA))
      -∗
      ⌜st_src = st⌝.
  Proof.
    unfold default_I. iIntros "[[[[[[A B] C] D] E] F] G] OWN".
    iPoseProof (black_white_equal with "B OWN") as "%". clarify.
  Qed.

  Lemma default_I_get_st_tgt ths im_src im_tgt st_src st_tgt st
    :
    (default_I ths im_src im_tgt st_src st_tgt)
      -∗
      (OwnM (Auth.white (Excl.just (Some st): @Excl.t (option state_tgt)): stateTgtRA))
      -∗
      ⌜st_tgt = st⌝.
  Proof.
    unfold default_I. iIntros "[[[[[[A B] C] D] E] F] G] OWN".
    iPoseProof (black_white_equal with "C OWN") as "%". clarify.
  Qed.

  Lemma default_I_thread_alloc ths0 im_src im_tgt0 st_src st_tgt
        tid ths1 im_tgt1
        (THS: TIdSet.add_new tid ths0 ths1)
        (TID_TGT : fair_update im_tgt0 im_tgt1 (prism_fmap inlp (fun i => if tid_dec i tid then Flag.success else Flag.emp)))
    :
    (default_I ths0 im_src im_tgt0 st_src st_tgt)
      -∗
      #=> (own_thread tid ** ObligationRA.duty inlp tid [] ** default_I ths1 im_src im_tgt1 st_src st_tgt).
  Proof.
    unfold default_I. iIntros "[[[[[[A B] C] D] E] F] G]".
    iPoseProof (OwnM_Upd with "A") as "> [A TH]".
    { apply Auth.auth_alloc.
      eapply (@NatMapRAFOS.add_local_update unit ths0 tid tt). inv THS. auto.
    }
    iPoseProof (FairRA.target_add_thread with "E") as "> [E BLACK]"; [eauto|eauto|].
    iModIntro. inv THS. iFrame.
    unfold ObligationRA.duty. iExists [], 1%Qp. iFrame. ss.
  Qed.

  Lemma default_I_update_ident_thread ths im_src im_tgt0 st_src st_tgt
        tid im_tgt1 l
        (UPD: fair_update im_tgt0 im_tgt1 (prism_fmap inlp (tids_fmap tid ths)))
    :
    (default_I ths im_src im_tgt0 st_src st_tgt)
      -∗
      (ObligationRA.duty inlp tid l ** ObligationRA.tax l)
      -∗
      #=> (ObligationRA.duty inlp tid l ** FairRA.white_thread (S:=_) ** default_I ths im_src im_tgt1 st_src st_tgt).
  Proof.
    unfold default_I. iIntros "[[[[[[A B] C] D] E] F] G] DUTY".
    iPoseProof (ObligationRA.target_update_thread with "E DUTY G") as "> [G [[E BLACK] WHITE]]"; [eauto|].
    iModIntro. iFrame.
  Qed.

  Lemma default_I_update_ident_target A lf ls
        (p: Prism.t ident_tgt A)
        ths im_src im_tgt0 st_src st_tgt
        fm im_tgt1
        (UPD: fair_update im_tgt0 im_tgt1 (prism_fmap (inrp ⋅ p)%prism fm))
        (SUCCESS: forall i (IN: fm i = Flag.success), List.In i (List.map fst ls))
        (FAIL: forall i (IN: List.In i lf), fm i = Flag.fail)
        (NODUP: List.NoDup lf)
    :
    (default_I ths im_src im_tgt0 st_src st_tgt)
      -∗
      (list_prop_sum (fun '(i, l) => ObligationRA.duty (inrp ⋅ p)%prism i l ** ObligationRA.tax l) ls)
      -∗
      #=> ((list_prop_sum (fun '(i, l) => ObligationRA.duty (inrp ⋅ p)%prism i l) ls)
             **
             (list_prop_sum (fun i => FairRA.white (Id:=_) (inrp ⋅ p)%prism i 1) lf)
             **
             default_I ths im_src im_tgt1 st_src st_tgt).
  Proof.
    unfold default_I. iIntros "[[[[[[A B] C] D] E] F] G] DUTY".
    iPoseProof (ObligationRA.target_update with "E DUTY G") as "> [G [[E BLACK] WHITE]]".
    { eauto. }
    { eauto. }
    { eauto. }
    { eauto. }
    iModIntro. iFrame.
  Qed.

  Lemma default_I_update_ident_source lf ls o
        ths im_src0 im_tgt st_src st_tgt
        fm
        (FAIL: forall i (IN: fm i = Flag.fail), List.In i lf)
        (SUCCESS: forall i (IN: List.In i ls), fm i = Flag.success)
    :
    (default_I ths im_src0 im_tgt st_src st_tgt)
      -∗
      (list_prop_sum (fun i => FairRA.white Prism.id i Ord.one) lf)
      -∗
      #=> (∃ im_src1,
              (⌜fair_update im_src0 im_src1 fm⌝)
                **
                (list_prop_sum (fun i => FairRA.white Prism.id i o) ls)
                **
                default_I ths im_src1 im_tgt st_src st_tgt).
  Proof.
    unfold default_I. iIntros "[[[[[[A B] C] D] E] F] G] WHITES".
    iPoseProof (FairRA.source_update with "D WHITES") as "> [% [[% D] WHITE]]".
    { eauto. }
    { eauto. }
    iModIntro. iExists _. iFrame. auto.
  Qed.

  Lemma arrows_sat_sub ths im_src im_tgt st_src st_tgt
    :
    ⊢ SubIProp (ObligationRA.arrows_sat (S := sum_tid ident_tgt)) (default_I ths im_src im_tgt st_src st_tgt).
  Proof.
    iIntros "[[[[[[A B] C] D] E] F] G]". iModIntro. iFrame. auto.
  Qed.

  Lemma edges_sat_sub ths im_src im_tgt st_src st_tgt
    :
    ⊢ SubIProp (ObligationRA.edges_sat) (default_I ths im_src im_tgt st_src st_tgt).
  Proof.
    iIntros "[[[[[[A B] C] D] E] F] G]". iModIntro. iFrame. auto.
  Qed.

  Lemma default_I_past_update_st_src tid ths im_src im_tgt st_src0 st_tgt st_src' st_src1
    :
    (default_I_past tid ths im_src im_tgt st_src0 st_tgt)
      -∗
      (OwnM (Auth.white (Excl.just (Some st_src'): @Excl.t (option state_src)): stateSrcRA))
      -∗
      #=> (OwnM (Auth.white (Excl.just (Some st_src1): @Excl.t (option state_src))) ** default_I_past tid ths im_src im_tgt st_src1 st_tgt).
  Proof.
    iIntros "[% [% D]] H".
    iPoseProof (default_I_update_st_src with "D H") as "> [H D]".
    iModIntro. iSplitL "H"; auto. unfold default_I_past. eauto.
  Qed.

  Lemma default_I_past_update_st_tgt tid ths im_src im_tgt st_src st_tgt0 st_tgt' st_tgt1
    :
    (default_I_past tid ths im_src im_tgt st_src st_tgt0)
      -∗
      (OwnM (Auth.white (Excl.just (Some st_tgt'): @Excl.t (option state_tgt)): stateTgtRA))
      -∗
      #=> (OwnM (Auth.white (Excl.just (Some st_tgt1): @Excl.t (option state_tgt))) ** default_I_past tid ths im_src im_tgt st_src st_tgt1).
  Proof.
    iIntros "[% [% D]] H".
    iPoseProof (default_I_update_st_tgt with "D H") as "> [H D]".
    iModIntro. iSplitL "H"; auto. unfold default_I_past. eauto.
  Qed.

  Lemma default_I_past_get_st_src tid ths im_src im_tgt st_src st_tgt st
    :
    (default_I_past tid ths im_src im_tgt st_src st_tgt)
      -∗
      (OwnM (Auth.white (Excl.just (Some st): @Excl.t (option state_src)): stateSrcRA))
      -∗
      ⌜st_src = st⌝.
  Proof.
    iIntros "[% [% D]] H".
    iApply (default_I_get_st_src with "D H").
  Qed.

  Lemma default_I_past_get_st_tgt tid ths im_src im_tgt st_src st_tgt st
    :
    (default_I_past tid ths im_src im_tgt st_src st_tgt)
      -∗
      (OwnM (Auth.white (Excl.just (Some st): @Excl.t (option state_tgt)): stateTgtRA))
      -∗
      ⌜st_tgt = st⌝.
  Proof.
    iIntros "[% [% D]] H".
    iApply (default_I_get_st_tgt with "D H").
  Qed.

  Lemma default_I_past_update_ident_thread ths im_src im_tgt st_src st_tgt
        tid l
    :
    (default_I_past tid ths im_src im_tgt st_src st_tgt)
      -∗
      (ObligationRA.duty inlp tid l ** ObligationRA.tax l)
      -∗
      #=> (ObligationRA.duty inlp tid l ** FairRA.white_thread (S:=_) ** default_I ths im_src im_tgt st_src st_tgt).
  Proof.
    iIntros "[% [% D]] H".
    iApply (default_I_update_ident_thread with "D H"); auto.
  Qed.

  Lemma default_I_past_update_ident_target A tid lf ls
        (p: Prism.t ident_tgt A)
        ths im_src im_tgt0 st_src st_tgt
        fm im_tgt1
        (UPD: fair_update im_tgt0 im_tgt1 (prism_fmap (inrp ⋅ p)%prism fm))
        (SUCCESS: forall i (IN: fm i = Flag.success), List.In i (List.map fst ls))
        (FAIL: forall i (IN: List.In i lf), fm i = Flag.fail)
        (NODUP: List.NoDup lf)
    :
    (default_I_past tid ths im_src im_tgt0 st_src st_tgt)
      -∗
      (list_prop_sum (fun '(i, l) => ObligationRA.duty (inrp ⋅ p)%prism i l ** ObligationRA.tax l) ls)
      -∗
      #=> ((list_prop_sum (fun '(i, l) => ObligationRA.duty (inrp ⋅ p)%prism i l) ls)
             **
             (list_prop_sum (fun i => FairRA.white (Id:=_) (inrp ⋅ p)%prism i 1) lf)
             **
             default_I_past tid ths im_src im_tgt1 st_src st_tgt).
  Proof.
    iIntros "[% [% D]] H".
    iPoseProof (default_I_update_ident_target with "D H") as "> [[H0 H1] D]"; [eauto|eauto|eauto|eauto|..].
    { instantiate (1:=(fun i =>
                         match i with
                         | inl i => im_tgt2 (inl i)
                         | inr i => im_tgt1 (inr i)
                         end)).
      ii. specialize (UPD i). specialize (H i).
      unfold prism_fmap, tids_fmap in *; ss. unfold is_inl, is_inr in *; ss. des_ifs.
      { rewrite <- H. auto. }
      { rewrite UPD. auto. }
      { etrans; eauto. }
    }
    iModIntro. iFrame.
    unfold default_I_past. iExists _. iSplit; eauto. iPureIntro.
    ii. specialize (UPD i). specialize (H i).
    unfold prism_fmap, tids_fmap in *; ss. unfold is_inl in *; ss. des_ifs.
    { rewrite UPD. auto. }
    { rewrite <- H. auto. }
  Qed.

  Lemma default_I_past_update_ident_source tid lf ls o
        ths im_src0 im_tgt st_src st_tgt
        fm
        (FAIL: forall i (IN: fm i = Flag.fail), List.In i lf)
        (SUCCESS: forall i (IN: List.In i ls), fm i = Flag.success)
    :
    (default_I_past tid ths im_src0 im_tgt st_src st_tgt)
      -∗
      (list_prop_sum (fun i => FairRA.white Prism.id i Ord.one) lf)
      -∗
      #=> (∃ im_src1,
              (⌜fair_update im_src0 im_src1 fm⌝)
                **
                (list_prop_sum (fun i => FairRA.white Prism.id i o) ls)
                **
                default_I_past tid ths im_src1 im_tgt st_src st_tgt).
  Proof.
    iIntros "[% [% D]] H".
    iPoseProof (default_I_update_ident_source with "D H") as "> [% [[% H] D]]"; [eauto|eauto|..].
    iModIntro. unfold default_I_past. iExists _. iSplitL "H"; auto.
  Qed.

  Lemma default_I_past_update_ident_source_prism A tid lf ls o
        (p: Prism.t ident_src A)
        ths im_src0 im_tgt st_src st_tgt
        fm
        (FAIL: forall i (IN: fm i = Flag.fail), List.In i lf)
        (SUCCESS: forall i (IN: List.In i ls), fm i = Flag.success)
    :
    (default_I_past tid ths im_src0 im_tgt st_src st_tgt)
      -∗
      (list_prop_sum (fun i => FairRA.white p i Ord.one) lf)
      -∗
      #=> (∃ im_src1,
              (⌜fair_update im_src0 im_src1 (prism_fmap p fm)⌝)
                **
                (list_prop_sum (fun i => FairRA.white p i o) ls)
                **
                default_I_past tid ths im_src1 im_tgt st_src st_tgt).
  Proof.
    iIntros "D H".
    iPoseProof (default_I_past_update_ident_source with "D [H]") as "> [% [[% H] D]]".
    { instantiate (1:=List.map (Prism.review p) lf). instantiate (1:=prism_fmap p fm).
      i. unfold prism_fmap in IN. des_ifs.
      eapply Prism.review_preview in Heq. subst.
      eapply in_map. auto.
    }
    { instantiate (1:=List.map (Prism.review p) ls).
      i. eapply in_map_iff in IN. des. subst.
      unfold prism_fmap. rewrite Prism.preview_review. auto.
    }
    { iApply (list_prop_sum_map with "H"). i.
      iIntros "H". iApply (FairRA.white_prism_id with "H").
    }
    iModIntro. iExists _. iFrame. iSplit; auto.
    iApply (list_prop_sum_map_inv with "H"). i.
    iIntros "H". iApply (FairRA.white_prism_id_rev with "H").
  Qed.

  Lemma default_I_past_final ths0 im_src im_tgt st_src st_tgt
        tid
    :
    (default_I_past tid ths0 im_src im_tgt st_src st_tgt)
      -∗
      (own_thread tid ** ObligationRA.duty inlp tid [])
      -∗
      #=> (∃ ths1,
              (⌜NatMap.remove tid ths0 = ths1⌝)
                **
                (default_I ths1 im_src im_tgt st_src st_tgt)).
  Proof.
    iIntros "[% [% D]] [OWN DUTY]".
    iPoseProof (default_I_update_ident_thread with "D [DUTY]") as "> [[DUTY _] D]".
    { eauto. }
    { iSplitL; eauto. }
    unfold default_I. iPoseProof "D" as "[[[[[[A B] C] D] E] F] G]".
    iCombine "A OWN" as "A".
    iPoseProof (OwnM_Upd with "A") as "> X".
    { apply Auth.auth_dealloc.
      eapply (@NatMapRAFOS.remove_local_update unit ths0 _ _).
    }
    iPoseProof (FairRA.target_remove_thread with "E [DUTY]") as "> E".
    { iPoseProof "DUTY" as "[% [% [[A [B %]] %]]]". destruct rs; ss.
      subst. iFrame.
    }
    iModIntro. iExists _. iFrame. auto.
  Qed.
End INVARIANT.
