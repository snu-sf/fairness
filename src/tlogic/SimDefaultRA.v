From iris.algebra Require Import cmra updates lib.excl_auth coPset.
From sflib Require Import sflib.
From Paco Require Import paco.
From Fairness Require Import ITreeLib pind.
Require Import Program.
From Fairness Require Import PCM IProp IPM IPropAux.
From Fairness Require Import Mod FairBeh.
From Fairness Require Import Axioms.
From Fairness Require Import NatMapRA MonotoneRA RegionRA FairnessRA IndexedInvariants ObligationRA OpticsInterp.

Set Implicit Arguments.

(* Section PAIR.
  Context {A B: Type}.

  Context `{IN: @GRA.inG (excl_authUR $ leibnizO (A * B)) Σ}.
  Context `{INA: @GRA.inG (excl_authUR $ leibnizO A) Σ}.
  Context `{INB: @GRA.inG (excl_authUR $ leibnizO B) Σ}.
  Notation iProp := (iProp Σ).

  Definition Own_pair (a : A) (b : B) : iProp :=
    OwnM (●E ((a, b) : leibnizO (A * B))).

  Definition Own_fst (a : A) (b : B) : iProp :=
    OwnM (●E ((a, b) : leibnizO (A * B))).

  Definition pair_sat: iProp :=
    ∃ (a : A) (b : B),
      (OwnM (●E ((a, b) : leibnizO (A * B))))
        ∗
        (OwnM (●E (a : leibnizO A)))
        ∗
        (OwnM (●E (b  : leibnizO B)))
  .

  Lemma pair_access_fst (a : A)
    :
    (OwnM (◯E (a: @Excl.t A)))
      -∗
      (pair_sat)
      -∗
      (∃ b, (OwnM (◯E ((a, b): @Excl.t (A * B))))
              ∗
              (∀ a,
                  ((OwnM (◯E ((a, b): @Excl.t (A * B))))
                     -∗
                     #=> ((OwnM (◯E (a: @Excl.t A))) ∗ (pair_sat))))).
  Proof.
    iIntros "H [% [% [H0 [H1 H2]]]]".
    iPoseProof (black_white_equal with "H1 H") as "%". subst.
    iExists _. iFrame. iIntros (?) "H0".
    iPoseProof (black_white_update with "H1 H") as "> [H1 H]".
    iModIntro. iFrame. iExists _, _. iFrame.
  Qed.

  Lemma pair_access_snd b
    :
    (OwnM (◯E (b: @Excl.t B)))
      -∗
      (pair_sat)
      -∗
      (∃ a, (OwnM (◯E ((a, b): @Excl.t (A * B))))
              ∗
              (∀ b,
                  ((OwnM (◯E ((a, b): @Excl.t (A * B))))
                     -∗
                     #=> ((OwnM (◯E (b: @Excl.t B))) ∗ (pair_sat))))).
  Proof.
    iIntros "H [% [% [H0 [H1 H2]]]]".
    iPoseProof (black_white_equal with "H2 H") as "%". subst.
    iExists _. iFrame. iIntros (?) "H0".
    iPoseProof (black_white_update with "H2 H") as "> [H2 H]".
    iModIntro. iFrame. iExists _, _. iFrame.
  Qed.
End PAIR. *)



Section INVARIANT.
  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable ident_src: ID.
  Variable ident_tgt: ID.

  Definition stateSrcRA: ucmra := excl_authUR $ leibnizO (option state_src).
  Definition stateTgtRA: ucmra := excl_authUR $ leibnizO (option state_tgt).
  Definition identSrcRA: ucmra := FairRA.srct ident_src.
  Definition identTgtRA: ucmra := FairRA.tgtt ident_tgt.
  Definition ThreadRA: ucmra := authUR (NatMapRA.t unit).
  Definition EdgeRA: ucmra := Region.t (nat * nat * Ord.t).
  Definition ArrowShotRA: ucmra := @FiniteMap.t (OneShot.t ObligationRA._unit).

  Local Notation index := nat.
  Context `{Vars : index -> Type}.

  Definition ArrowRA: ucmra :=
    Regions.t (fun x => ((sum_tid ident_tgt) * nat * Ord.t * Qp * nat * (Vars x))%type).

  Context `{Σ : GRA.t}.
  Context `{Invs : @IInvSet Σ Vars}.

  Context `{THDRA: @GRA.inG ThreadRA Σ}.
  Context `{STATESRC: @GRA.inG stateSrcRA Σ}.
  Context `{STATETGT: @GRA.inG stateTgtRA Σ}.
  Context `{IDENTSRC: @GRA.inG identSrcRA Σ}.
  Context `{IDENTTGT: @GRA.inG identTgtRA Σ}.
  Context `{OBLGRA: @GRA.inG ObligationRA.t Σ}.
  Context `{EDGERA: @GRA.inG EdgeRA Σ}.
  Context `{ONESHOTRA: @GRA.inG ArrowShotRA Σ}.
  Context `{ARROWRA: @GRA.inG ArrowRA Σ}.
  Notation iProp := (iProp Σ).

  (* Works for formulas with index < x. *)
  Definition fairI x : iProp :=
    (ObligationRA.edges_sat)
      ∗
      (ObligationRA.arrows_sats (S := sum_tid ident_tgt) x).

  Definition default_I x :
    TIdSet.t -> (@imap ident_src owf) -> (@imap (sum_tid ident_tgt) nat_wf) -> state_src -> state_tgt -> iProp :=
    fun ths im_src im_tgt st_src st_tgt =>
      ((OwnM (● (NatMapRA.to_Map ths) : ThreadRA))
         ∗
         (OwnM (●E (Some st_src: leibnizO (option state_src)): stateSrcRA))
         ∗
         (OwnM (●E (Some st_tgt: leibnizO (option state_tgt)): stateTgtRA))
         ∗
         (FairRA.sat_source im_src)
         ∗
         (FairRA.sat_target im_tgt ths)
         ∗
         (ObligationRA.edges_sat)
         ∗
         (ObligationRA.arrows_sats (S := sum_tid ident_tgt) x)
         ∗
         (ObligationRA.arrows_auth (S := sum_tid ident_tgt) x)
      )%I
  .

  Definition default_I_past (tid: thread_id) x
    : TIdSet.t -> (@imap ident_src owf) -> (@imap (sum_tid ident_tgt) nat_wf) -> state_src -> state_tgt -> iProp :=
    fun ths im_src im_tgt st_src st_tgt =>
      (∃ im_tgt0,
          (⌜fair_update im_tgt0 im_tgt (prism_fmap inlp (tids_fmap tid ths))⌝)
            ∗ (default_I x ths im_src im_tgt0 st_src st_tgt))%I.

  Definition own_thread (tid: thread_id): iProp :=
    (OwnM (◯ (NatMapRA.singleton tid tt: NatMapRA.t unit): ThreadRA)).

  Lemma own_thread_unique tid0 tid1
    :
    ⊢ (own_thread tid0)
      -∗
      (own_thread tid1)
      -∗
      ⌜tid0 <> tid1⌝.
  Proof.
    iIntros "OWN0 OWN1". iCombine "OWN0 OWN1" as "OWN".
    iOwnWf "OWN". apply auth_frag_valid,NatMapRA.singleton_unique in H.
    iPureIntro. auto.
  Qed.

  Lemma default_I_update_st_src x ths im_src im_tgt st_src0 st_tgt st_src' st_src1
    :
    ⊢ (default_I x ths im_src im_tgt st_src0 st_tgt)
      -∗
      (OwnM (◯E (Some st_src': leibnizO (option state_src)): stateSrcRA))
      -∗
      #=> (OwnM (◯E (Some st_src1: leibnizO (option state_src)))
                ∗ default_I x ths im_src im_tgt st_src1 st_tgt).
  Proof.
    unfold default_I. iIntros "[A [B [C [D [E [F G]]]]]] OWN".
    iPoseProof (black_white_update with "B OWN") as "> [B OWN]".
    iModIntro. iFrame.
  Qed.

  Lemma default_I_update_st_tgt x ths im_src im_tgt st_src st_tgt0 st_tgt' st_tgt1
    :
    ⊢ (default_I x ths im_src im_tgt st_src st_tgt0)
      -∗
      (OwnM (◯E (Some st_tgt': leibnizO (option state_tgt)): stateTgtRA))
      -∗
      #=> (OwnM (◯E (Some st_tgt1 : leibnizO (option state_tgt)))
                ∗ default_I x ths im_src im_tgt st_src st_tgt1).
  Proof.
    unfold default_I. iIntros "[A [B [C [D [E [F G]]]]]] OWN".
    iPoseProof (black_white_update with "C OWN") as "> [C OWN]".
    iModIntro. iFrame.
  Qed.

  Lemma default_I_get_st_src x ths im_src im_tgt st_src st_tgt st
    :
    ⊢ (default_I x ths im_src im_tgt st_src st_tgt)
      -∗
      (OwnM (◯E (Some st: leibnizO (option state_src)): stateSrcRA))
      -∗
      ⌜st_src = st⌝.
  Proof.
    unfold default_I. iIntros "[A [B [C [D [E [F G]]]]]] OWN".
    iPoseProof (black_white_equal with "B OWN") as "%". clarify.
  Qed.

  Lemma default_I_get_st_tgt x ths im_src im_tgt st_src st_tgt st
    :
    ⊢ (default_I x ths im_src im_tgt st_src st_tgt)
      -∗
      (OwnM (◯E (Some st: leibnizO (option state_tgt)): stateTgtRA))
      -∗
      ⌜st_tgt = st⌝.
  Proof.
    unfold default_I. iIntros "[A [B [C [D [E [F G]]]]]] OWN".
    iPoseProof (black_white_equal with "C OWN") as "%". clarify.
  Qed.

  Lemma default_I_thread_alloc x n ths0 im_src im_tgt0 st_src st_tgt
        tid ths1 im_tgt1
        (THS: TIdSet.add_new tid ths0 ths1)
        (TID_TGT : fair_update im_tgt0 im_tgt1 (prism_fmap inlp (fun i => if tid_dec i tid then Flag.success else Flag.emp)))
    :
    ⊢
      (default_I x ths0 im_src im_tgt0 st_src st_tgt)
      -∗
      #=> (own_thread tid ∗ ObligationRA.duty n inlp tid [] ∗ default_I x ths1 im_src im_tgt1 st_src st_tgt).
  Proof.
    unfold default_I. iIntros "[A [B [C [D [E [F G]]]]]]".
    iPoseProof (OwnM_Upd with "A") as "> [A TH]".
    { apply auth_update_alloc.
      eapply (@NatMapRA.add_local_update unit ths0 tid tt). inv THS. auto.
    }
    iPoseProof (FairRA.target_add_thread with "E") as "> [E BLACK]"; [eauto|eauto|].
    iModIntro. inv THS. iFrame.
    iApply ObligationRA.black_to_duty. iFrame.
  Qed.

  Lemma default_I_update_ident_thread_pending x n ths im_src im_tgt0 st_src st_tgt
        tid im_tgt1 l
        (UPD: fair_update im_tgt0 im_tgt1 (prism_fmap inlp (tids_fmap tid ths)))
        l1 l2 ps
        (OBLIGS : l = l1 ++ l2)
        (PENDS : Forall2 (fun '(k1, _, _) '(k2, _) => k1 = k2) l1 ps)
    :
    (n < x) ->
    ⊢
      (default_I x ths im_src im_tgt0 st_src st_tgt)
      -∗
      ((ObligationRA.duty n inlp tid l)
         ∗ (ObligationRA.pends ps)
         ∗ (ObligationRA.taxes (List.map fst l2) Ord.omega)
      )
      -∗
      #=> ((ObligationRA.duty n inlp tid l)
             ∗ (FairRA.white_thread (S:=_))
             ∗ (default_I x ths im_src im_tgt1 st_src st_tgt)
             ∗ (ObligationRA.pends ps)
          ).
  Proof.
    unfold default_I. iIntros (LT) "[A [B [C [D [E [F [G H]]]]]]] DUTY".
    iPoseProof (ObligationRA.target_update_thread_pending with "E [DUTY]") as "RES". eauto.
    2:{ iDestruct "DUTY" as "(DUTY & PENDS & TAXES)". iFrame.
        iApply (ObligationRA.pends_taxes_to_ptaxes with "PENDS TAXES").
    }
    { subst. apply Forall2_app.
      - clear - PENDS. rewrite Forall2_fmap_r. eapply Forall2_impl. eauto. i. des_ifs.
      - clear. rewrite List.map_map. rewrite Forall2_fmap_r. apply Reflexive_instance_0.
        ii. des_ifs.
    }
    iMod (Regions.nsats_sat_sub with "G") as "[ARROW K]". apply LT.
    iMod ("RES" with "ARROW") as "[ARROW [E [DUTY [WHITE OPENDS]]]]".
    iPoseProof (ObligationRA.opends_to_pends2 with "OPENDS") as "PENDS".
    iFrame. iApply "K". iFrame.
    Local Transparent ObligationRA.arrows_sat ObligationRA.arrow ObligationRA.arrows.
    Local Typeclasses Transparent ObligationRA.arrows_sat ObligationRA.arrow ObligationRA.arrows.
    iFrame "ARROW".
    Local Typeclasses Opaque ObligationRA.arrows_sat ObligationRA.arrow ObligationRA.arrows.
    Local Opaque ObligationRA.arrows_sat ObligationRA.arrow ObligationRA.arrows.
  Qed.

  Lemma default_I_update_ident_thread x n ths im_src im_tgt0 st_src st_tgt
        tid im_tgt1 l
        (UPD: fair_update im_tgt0 im_tgt1 (prism_fmap inlp (tids_fmap tid ths)))
    :
    (n < x) ->
    ⊢
      (default_I x ths im_src im_tgt0 st_src st_tgt)
      -∗
      (ObligationRA.duty n inlp tid l ∗ ObligationRA.taxes (List.map fst l) Ord.omega)
      -∗
      #=> (ObligationRA.duty n inlp tid l ∗ FairRA.white_thread (S:=_) ∗ default_I x ths im_src im_tgt1 st_src st_tgt).
  Proof.
    iIntros (LT) "DEF [DUTY TAX]".
    iMod (default_I_update_ident_thread_pending with "DEF [DUTY TAX]") as "RES".
    5:{ iFrame. iApply ObligationRA.pends_nil. }
    5:{ iDestruct "RES" as "(A & B & C & _)". iModIntro. iFrame. }
    all: eauto. ss.
  Qed.

  Lemma default_I_update_ident_target x n A lf ls
        (p: Prism.t ident_tgt A)
        ths im_src im_tgt0 st_src st_tgt
        fm im_tgt1
        (UPD: fair_update im_tgt0 im_tgt1 (prism_fmap (inrp ⋅ p)%prism fm))
        (SUCCESS: forall i (IN: fm i = Flag.success), List.In i (List.map fst ls))
        (FAIL: forall i (IN: List.In i lf), fm i = Flag.fail)
        (NODUP: List.NoDup lf)
    :
    (n < x) ->
    ⊢
      (default_I x ths im_src im_tgt0 st_src st_tgt)
      -∗
      (list_prop_sum (fun '(i, l) => ObligationRA.duty n (inrp ⋅ p)%prism i l ∗ ObligationRA.taxes (List.map fst l) Ord.omega) ls)
      -∗
      #=> ((list_prop_sum (fun '(i, l) => ObligationRA.duty n (inrp ⋅ p)%prism i l) ls)
             ∗
             (list_prop_sum (fun i => FairRA.white (Id:=_) (inrp ⋅ p)%prism i 1) lf)
             ∗
             default_I x ths im_src im_tgt1 st_src st_tgt).
  Proof.
    unfold default_I. iIntros (LT) "[A [B [C [D [E [F [G H]]]]]]] DUTY".
    iPoseProof (ObligationRA.target_update with "E DUTY") as "RES". 1,2,3,4: eauto.
    iMod (Regions.nsats_sat_sub with "G") as "[ARROW K]". apply LT.
    iMod ("RES" with "ARROW") as "[ARROW [E [DUTY WHITE]]]". iFrame.
    iApply "K".
    Local Transparent ObligationRA.arrows_sat ObligationRA.arrow ObligationRA.arrows.
    Local Typeclasses Transparent ObligationRA.arrows_sat ObligationRA.arrow ObligationRA.arrows.
    iFrame "ARROW".
    Local Typeclasses Opaque ObligationRA.arrows_sat ObligationRA.arrow ObligationRA.arrows.
    Local Opaque ObligationRA.arrows_sat ObligationRA.arrow ObligationRA.arrows.
  Qed.

  Lemma default_I_update_ident_source x lf ls o
        ths im_src0 im_tgt st_src st_tgt
        fm
        (FAIL: forall i (IN: fm i = Flag.fail), List.In i lf)
        (SUCCESS: forall i (IN: List.In i ls), fm i = Flag.success)
    :
    ⊢
      (default_I x ths im_src0 im_tgt st_src st_tgt)
      -∗
      (list_prop_sum (fun i => FairRA.white Prism.id i Ord.one) lf)
      -∗
      #=> (∃ im_src1,
              (⌜fair_update im_src0 im_src1 fm⌝)
                ∗
                (list_prop_sum (fun i => FairRA.white Prism.id i o) ls)
                ∗
                default_I x ths im_src1 im_tgt st_src st_tgt).
  Proof.
    unfold default_I. iIntros "[A [B [C [D [E [F G]]]]]] WHITES".
    iPoseProof (FairRA.source_update with "D WHITES") as "> [% [% [D WHITE]]]".
    { eauto. }
    { eauto. }
    iModIntro. iExists _. iFrame. auto.
  Qed.

  Lemma arrows_sat_sub x n ths im_src im_tgt st_src st_tgt
    :
    (n < x) ->
    ⊢ SubIProp (ObligationRA.arrows_sat n (S := sum_tid ident_tgt)) (default_I x ths im_src im_tgt st_src st_tgt).
  Proof.
    iIntros (LT) "[A [B [C [D [E [F [G H]]]]]]]".
    iMod (Regions.nsats_sat_sub with "G") as "[ARROW K]". apply LT.
    iFrame. iModIntro. iFrame.
    Local Transparent ObligationRA.arrows_sat ObligationRA.arrow ObligationRA.arrows.
    Local Typeclasses Transparent ObligationRA.arrows_sat ObligationRA.arrow ObligationRA.arrows.
    iFrame.
    Local Typeclasses Opaque ObligationRA.arrows_sat ObligationRA.arrow ObligationRA.arrows.
    Local Opaque ObligationRA.arrows_sat ObligationRA.arrow ObligationRA.arrows.
  Qed.

  Lemma edges_sat_sub x ths im_src im_tgt st_src st_tgt
    :
    ⊢ SubIProp (ObligationRA.edges_sat) (default_I x ths im_src im_tgt st_src st_tgt).
  Proof.
    iIntros "[A [B [C [D [E [F G]]]]]]". iModIntro. iFrame. auto.
  Qed.

  Lemma default_I_past_update_st_src tid x ths im_src im_tgt st_src0 st_tgt st_src' st_src1
    :
    ⊢
      (default_I_past tid x ths im_src im_tgt st_src0 st_tgt)
      -∗
      (OwnM (◯E (Some st_src': leibnizO (option state_src)): stateSrcRA))
      -∗
      #=> (OwnM (◯E (Some st_src1: leibnizO (option state_src)))
                ∗ default_I_past tid x ths im_src im_tgt st_src1 st_tgt).
  Proof.
    iIntros "[% [% D]] H".
    iPoseProof (default_I_update_st_src with "D H") as "> [H D]".
    iModIntro. iSplitL "H"; auto. unfold default_I_past. eauto.
  Qed.

  Lemma default_I_past_update_st_tgt x tid ths im_src im_tgt st_src st_tgt0 st_tgt' st_tgt1
    :
    ⊢
      (default_I_past tid x ths im_src im_tgt st_src st_tgt0)
      -∗
      (OwnM (◯E (Some st_tgt': leibnizO (option state_tgt)): stateTgtRA))
      -∗
      #=> (OwnM (◯E (Some st_tgt1: leibnizO (option state_tgt)))
                ∗ default_I_past tid x ths im_src im_tgt st_src st_tgt1).
  Proof.
    iIntros "[% [% D]] H".
    iPoseProof (default_I_update_st_tgt with "D H") as "> [H D]".
    iModIntro. iSplitL "H"; auto. unfold default_I_past. eauto.
  Qed.

  Lemma default_I_past_get_st_src x tid ths im_src im_tgt st_src st_tgt st
    :
    ⊢
      (default_I_past tid x ths im_src im_tgt st_src st_tgt)
      -∗
      (OwnM (◯E (Some st: leibnizO (option state_src)): stateSrcRA))
      -∗
      ⌜st_src = st⌝.
  Proof.
    iIntros "[% [% D]] H". iApply (default_I_get_st_src with "D H").
  Qed.

  Lemma default_I_past_get_st_tgt x tid ths im_src im_tgt st_src st_tgt st
    :
    ⊢
      (default_I_past tid x ths im_src im_tgt st_src st_tgt)
      -∗
      (OwnM (◯E (Some st: leibnizO (option state_tgt)): stateTgtRA))
      -∗
      ⌜st_tgt = st⌝.
  Proof.
    iIntros "[% [% D]] H". iApply (default_I_get_st_tgt with "D H").
  Qed.

  Lemma default_I_past_update_ident_thread_pending x n ths im_src im_tgt st_src st_tgt
        tid l
        l1 l2 ps
        (OBLIGS : l = l1 ++ l2)
        (PENDS : Forall2 (fun '(k1, _, _) '(k2, _) => k1 = k2) l1 ps)
    :
    (n < x) ->
    ⊢
      (default_I_past tid x ths im_src im_tgt st_src st_tgt)
      -∗
      (ObligationRA.duty n inlp tid l ∗ ObligationRA.pends ps ∗ ObligationRA.taxes (List.map fst l2) Ord.omega)
      -∗
      #=> (ObligationRA.duty n inlp tid l ∗ FairRA.white_thread (S:=_) ∗ default_I x ths im_src im_tgt st_src st_tgt ∗ ObligationRA.pends ps).
  Proof.
    iIntros (LT) "[% [% D]] H".
    iApply (default_I_update_ident_thread_pending with "D H"). all: eauto.
  Qed.

  Lemma default_I_past_update_ident_thread x n ths im_src im_tgt st_src st_tgt
        tid l
    :
    (n < x) ->
    ⊢
      (default_I_past tid x ths im_src im_tgt st_src st_tgt)
      -∗
      (ObligationRA.duty n inlp tid l ∗ ObligationRA.taxes (List.map fst l) Ord.omega)
      -∗
      #=> (ObligationRA.duty n inlp tid l ∗ FairRA.white_thread (S:=_) ∗ default_I x ths im_src im_tgt st_src st_tgt).
  Proof.
    iIntros (LT) "[% [% D]] H". iApply (default_I_update_ident_thread with "D H"). all: eauto.
  Qed.

  Lemma default_I_past_update_ident_target A tid x n lf ls
        (p: Prism.t ident_tgt A)
        ths im_src im_tgt0 st_src st_tgt
        fm im_tgt1
        (UPD: fair_update im_tgt0 im_tgt1 (prism_fmap (inrp ⋅ p)%prism fm))
        (SUCCESS: forall i (IN: fm i = Flag.success), List.In i (List.map fst ls))
        (FAIL: forall i (IN: List.In i lf), fm i = Flag.fail)
        (NODUP: List.NoDup lf)
    :
    (n < x) ->
    ⊢
      (default_I_past tid x ths im_src im_tgt0 st_src st_tgt)
      -∗
      (list_prop_sum (fun '(i, l) => ObligationRA.duty n (inrp ⋅ p)%prism i l ∗ ObligationRA.taxes (List.map fst l) Ord.omega) ls)
      -∗
      #=> ((list_prop_sum (fun '(i, l) => ObligationRA.duty n (inrp ⋅ p)%prism i l) ls)
             ∗
             (list_prop_sum (fun i => FairRA.white (Id:=_) (inrp ⋅ p)%prism i 1) lf)
             ∗
             default_I_past tid x ths im_src im_tgt1 st_src st_tgt).
  Proof.
    iIntros (LT) "[% [% D]] H".
    iPoseProof (default_I_update_ident_target with "D H") as "> [H0 [H1 D]]". 1,2,3,4,5: eauto.
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

  Lemma default_I_past_update_ident_source tid x lf ls o
        ths im_src0 im_tgt st_src st_tgt
        fm
        (FAIL: forall i (IN: fm i = Flag.fail), List.In i lf)
        (SUCCESS: forall i (IN: List.In i ls), fm i = Flag.success)
    :
    ⊢
      (default_I_past tid x ths im_src0 im_tgt st_src st_tgt)
      -∗
      (list_prop_sum (fun i => FairRA.white Prism.id i Ord.one) lf)
      -∗
      #=> (∃ im_src1,
              (⌜fair_update im_src0 im_src1 fm⌝)
                ∗
                (list_prop_sum (fun i => FairRA.white Prism.id i o) ls)
                ∗
                default_I_past tid x ths im_src1 im_tgt st_src st_tgt).
  Proof.
    iIntros "[% [% D]] H".
    iPoseProof (default_I_update_ident_source with "D H") as "> [% [% [H D]]]"; [eauto|eauto|..].
    iModIntro. unfold default_I_past. iExists _. iSplitR. eauto. iFrame. iExists _. iFrame. auto.
  Qed.

  Lemma default_I_past_update_ident_source_prism A tid x lf ls o
        (p: Prism.t ident_src A)
        ths im_src0 im_tgt st_src st_tgt
        fm
        (FAIL: forall i (IN: fm i = Flag.fail), List.In i lf)
        (SUCCESS: forall i (IN: List.In i ls), fm i = Flag.success)
    :
    ⊢
      (default_I_past tid x ths im_src0 im_tgt st_src st_tgt)
      -∗
      (list_prop_sum (fun i => FairRA.white p i Ord.one) lf)
      -∗
      #=> (∃ im_src1,
              (⌜fair_update im_src0 im_src1 (prism_fmap p fm)⌝)
                ∗
                (list_prop_sum (fun i => FairRA.white p i o) ls)
                ∗
                default_I_past tid x ths im_src1 im_tgt st_src st_tgt).
  Proof.
    iIntros "D H".
    iPoseProof (default_I_past_update_ident_source with "D [H]") as "> [% [% [H D]]]".
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
        tid x n
    :
    (n < x) ->
    ⊢
      (default_I_past tid x ths0 im_src im_tgt st_src st_tgt)
      -∗
      (own_thread tid ∗ ObligationRA.duty n inlp tid [])
      -∗
      #=> (∃ ths1,
              (⌜NatMap.remove tid ths0 = ths1⌝)
                ∗
                (default_I x ths1 im_src im_tgt st_src st_tgt)).
  Proof.
    iIntros (LT) "[% [% D]] [OWN DUTY]".
    iPoseProof (default_I_update_ident_thread with "D [DUTY]") as "> [DUTY [_ D]]".
    { eauto. }
    { eauto. }
    { iSplitL; eauto. }
    unfold default_I. iPoseProof "D" as "[A [B [C [D [E [F G]]]]]]".
    iCombine "A OWN" as "A".
    iPoseProof (OwnM_Upd with "A") as "> X".
    { apply auth_update_dealloc. eapply (@NatMapRA.remove_local_update unit ths0 _ _). }
    iPoseProof (FairRA.target_remove_thread with "E [DUTY]") as "> E".
    { iPoseProof "DUTY" as "[% [% [A [[B %] %]]]]". destruct rs; ss. subst. iFrame. }
    iModIntro. iExists _. iSplitR; [iPureIntro;auto|].
    iFrame.
  Qed.

End INVARIANT.

Section INIT.

  Context `{Σ: GRA.t}.

  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable ident_src: ID.
  Variable ident_tgt: ID.

  Local Notation index := nat.
  Context `{Vars : index -> Type}.
  Context `{Invs : @IInvSet Σ Vars}.

  (* Invariant related default RAs *)
  Context `{OWNERA : @GRA.inG OwnERA Σ}.
  Context `{OWNDRA : @GRA.inG OwnDRA Σ}.
  Context `{IINVSETRA : @GRA.inG (IInvSetRA Vars) Σ}.
  (* State related default RAs *)
  Context `{THDRA: @GRA.inG ThreadRA Σ}.
  Context `{STATESRC: @GRA.inG (stateSrcRA state_src) Σ}.
  Context `{STATETGT: @GRA.inG (stateTgtRA state_tgt) Σ}.
  Context `{IDENTSRC: @GRA.inG (identSrcRA ident_src) Σ}.
  Context `{IDENTTGT: @GRA.inG (identTgtRA ident_tgt) Σ}.
  (* Liveness logic related default RAs *)
  Context `{OBLGRA: @GRA.inG ObligationRA.t Σ}.
  Context `{EDGERA: @GRA.inG EdgeRA Σ}.
  Context `{ARROWSHOTRA: @GRA.inG ArrowShotRA Σ}.
  Context `{ARROWRA: @GRA.inG (@ArrowRA ident_tgt Vars) Σ}.


  Definition default_initial_res
    : Σ :=
    (@GRA.embed _ _ OWNERA (CoPset ⊤))
      ⋅
      (@GRA.embed _ _ IINVSETRA ((fun n => ●  ((fun _ => None) : (positive ==> optionUR (agreeR $ leibnizO (Vars n)))%ra)) : IInvSetRA Vars))
      ⋅
      (@GRA.embed _ _ THDRA (● (NatMapRA.to_Map (NatMap.empty unit): NatMapRA.t unit)))
      ⋅
      (@GRA.embed _ _ STATESRC ((●E (None : leibnizO (option state_src))) ⋅ (◯E (None : leibnizO (option state_src))) : stateSrcRA state_src))
      ⋅
      (@GRA.embed _ _ STATETGT ((●E (None : leibnizO (option state_tgt))) ⋅ (◯E (None : leibnizO (option state_tgt))): stateTgtRA state_tgt))
      ⋅
      (@GRA.embed _ _ IDENTSRC (@FairRA.source_init_resource ident_src))
      ⋅
      (@GRA.embed _ _ IDENTTGT ((fun _ => Fuel.black 0 1%Qp): identTgtRA ident_tgt))
      ⋅
      (@GRA.embed _ _ EDGERA ((fun _ => OneShot.pending _ 1%Qp): EdgeRA))
      ⋅
      (@GRA.embed _ _ ARROWRA ((@Regions.nauth_ra _ 0): @ArrowRA ident_tgt Vars))
  .

  Lemma own_threads_init ths
    :
    (OwnM (● (NatMapRA.to_Map (NatMap.empty unit): NatMapRA.t unit)))
      -∗
      (#=>
         ((OwnM (● (NatMapRA.to_Map ths: NatMapRA.t unit)))
            ∗
            (natmap_prop_sum ths (fun tid _ => own_thread tid)))).
  Proof.
    pattern ths. revert ths. eapply nm_ind.
    { iIntros "OWN". iModIntro. iFrame. }
    i. iIntros "OWN".
    iPoseProof (IH with "OWN") as "> [OWN SUM]".
    iPoseProof (OwnM_Upd with "OWN") as "> [OWN0 OWN1]".
    { eapply auth_update_alloc. eapply (@NatMapRA.add_local_update unit m k v); eauto. }
    iModIntro. iFrame. destruct v. iApply (natmap_prop_sum_add with "SUM OWN1").
  Qed.

  Lemma default_initial_res_init x n (LT : n < x)
    :
    (Own (default_initial_res))
      ⊢
      (∀ ths (st_src : state_src) (st_tgt : state_tgt) im_tgt o,
          #=> (∃ im_src,
                  (default_I x ths im_src im_tgt st_src st_tgt)
                    ∗
                    (natmap_prop_sum ths (fun tid _ => ObligationRA.duty n inlp tid []))
                    ∗
                    (natmap_prop_sum ths (fun tid _ => own_thread tid))
                    ∗
                    (FairRA.whites Prism.id (fun _ => True: Prop) o)
                    ∗
                    (FairRA.blacks Prism.id (fun i => match i with | inr _ => True | _ => False end: Prop))
                    ∗
                    (St_src st_src)
                    ∗
                    (St_tgt st_tgt)
                    ∗
                    wsat_auth x
                    ∗
                    wsats x
                    ∗
                    OwnE ⊤
      )).
  Proof.
    iIntros "OWN" (? ? ? ? ?).
    unfold default_initial_res. rewrite !Own_op.
    iDestruct "OWN" as "[[[[[[[[ENS WSATS] OWN0] [OWN1 OWN2]] [OWN3 OWN4]] OWN5] OWN6] OWN7] OWN8]".
    iPoseProof (black_white_update with "OWN1 OWN2") as "> [OWN1 OWN2]".
    iPoseProof (black_white_update with "OWN3 OWN4") as "> [OWN3 OWN4]".
    iPoseProof (OwnM_Upd with "OWN6") as "> OWN6".
    { instantiate (1:=FairRA.target_init_resource im_tgt).
      unfold FairRA.target_init_resource.
      erewrite ! (@unfold_pointwise_add (id_sum nat ident_tgt) (Fuel.t nat)).
      apply pointwise_updatable. i.
      rewrite (comm cmra.op). exact (@Fuel.success_update nat _ 0 (im_tgt a)).
    }
    iPoseProof (FairRA.target_init with "OWN6") as "[H0 [H1 H2]]".
    iPoseProof (FairRA.source_init with "OWN5") as "> [% [H3 H4]]".
    iExists f. unfold default_I.

    iPoseProof (wsats_init_zero with "WSATS") as "W".
    iPoseProof ((wsats_allocs _ x) with "W") as "[WA WS]". lia.
    iPoseProof (own_threads_init with "OWN0") as "> [OWN0 H]".

    iModIntro.
    iSplitL "OWN0 OWN1 OWN3 H3 H0 OWN7 OWN8".
    { iFrame "OWN0 OWN1 OWN3 H3 H0".
      iSplitL "OWN7".
      { iExists []. iSplitL; [|auto].
        iApply (OwnM_extends with "OWN7").
        apply pointwise_extends. i. destruct a; ss; reflexivity.
      }
      { iAssert (ObligationRA.arrows_sats 0)%I as "INIT".
        { unfold ObligationRA.arrows_sats, Regions.nsats. ss. }
        iPoseProof (Regions.nsats_allocs _ (x1:=0) (x2:=x) with "[OWN8]") as "[A S]". lia.
        { iFrame. }
        iFrame.
      }
    }
    iFrame "ENS WA WS H4 H OWN2 OWN4".
    iSplitR "H2".
    { iApply natmap_prop_sum_impl; [|eauto]. i. ss.
      iApply ObligationRA.black_to_duty.
    }
    { iPoseProof (FairRA.blacks_prism_id with "H2") as "H".
      iDestruct (FairRA.blacks_impl with "H") as "$".
      i. simpl in *. des_ifs. esplits; eauto.
    }
  Qed.

End INIT.

Section SHAREDUTY.

  Variable ident_tgt: ID.

  Local Notation index := nat.
  Context `{Vars : index -> Type}.

  Definition _ShareDutyRA n : ucmra := ((nat + ident_tgt) ==> (excl_authUR $ leibnizO (list (nat * nat * Vars n))))%ra.
  Definition ShareDutyRA : ucmra := pointwise_dep _ShareDutyRA.

  Context `{Σ : GRA.t}.
  Context `{SHAREDUTY : @GRA.inG ShareDutyRA Σ}.
  Notation iProp := (iProp Σ).

  Definition _ShareDutyRA_init n : (excl_authUR $ leibnizO (list (nat * nat * Vars n))) :=
    ●E ([] : leibnizO _) ⋅ ◯E ([] : leibnizO _).

  Definition ShareDuty_init : iProp :=
    OwnM ((fun n => (fun _ => _ShareDutyRA_init n)) : ShareDutyRA).

  Definition ShareDuty_init_inl : iProp :=
    OwnM ((fun n => (fun k => match k with
                        | inl _ => _ShareDutyRA_init n
                        | inr _ => ε
                        end)) : ShareDutyRA).

  Definition ShareDuty_init_inr : iProp :=
    OwnM ((fun n => (fun k => match k with
                        | inl _ => ε
                        | inr _ => _ShareDutyRA_init n
                        end)) : ShareDutyRA).

  Definition _ShareDutyRA_black
             n {Id : Type} (p : Prism.t (nat + ident_tgt) Id) (i : Id) (l : list (nat * nat * Vars n)) : ShareDutyRA :=
    maps_to_res_dep n (maps_to_res (Prism.review p i) (●E (l : leibnizO _))) : ShareDutyRA.
  Definition ShareDuty_black
             n {Id : Type} (p : Prism.t (nat + ident_tgt) Id) (i : Id) (l : list (nat * nat * Vars n)) : iProp :=
    OwnM (_ShareDutyRA_black p i l).

  Definition _ShareDutyRA_white
             n {Id : Type} (p : Prism.t (nat + ident_tgt) Id) (i : Id) (l : list (nat * nat * Vars n)) : ShareDutyRA :=
    maps_to_res_dep n (maps_to_res (Prism.review p i) (◯E (l : leibnizO _))) : ShareDutyRA.
  Definition ShareDuty_white
             n {Id : Type} (p : Prism.t (nat + ident_tgt) Id) (i : Id) (l : list (nat * nat * Vars n)) : iProp :=
    OwnM (_ShareDutyRA_white p i l).


  Lemma ShareDuty_init_div0 :
    ShareDuty_init
      ⊢ |==>(ShareDuty_init_inl ∗ ShareDuty_init_inr).
  Proof.
    iIntros "I". unfold ShareDuty_init.
    assert (((fun n => (fun _ => _ShareDutyRA_init n)) : ShareDutyRA) ~~>
              (((fun n => (fun k => match k with
                       | inl _ => _ShareDutyRA_init n
                       | inr _ => ε
                       end)) : ShareDutyRA)
                 ⋅
                 ((fun n => (fun k => match k with
                         | inl _ => ε
                         | inr _ => _ShareDutyRA_init n
                         end)) : ShareDutyRA))).
    { apply pointwise_dep_updatable. i.
      setoid_rewrite unfold_pointwise_add. apply pointwise_updatable. i. destruct a0.
      - rewrite right_id. reflexivity.
      - rewrite left_id. reflexivity.
    }
    iMod (OwnM_Upd with "I") as "[I I0]". eauto. iModIntro. iFrame.
  Qed.

  Lemma ShareDuty_init_div1 (ths : TIdSet.t) :
    ShareDuty_init
      ⊢
      |==> (
        OwnM ((fun n => (fun k => match k with
                            | inl t => match NatMap.find t ths with
                                      | Some _ => _ShareDutyRA_init n
                                      | None => ε
                                      end
                            | inr _ => ε
                            end)) : ShareDutyRA)
             ∗
             OwnM ((fun n => (fun k => match k with
                                 | inl t => match NatMap.find t ths with
                                           | Some _ => ε
                                           | None => _ShareDutyRA_init n
                                           end
                                 | inr _ => ε
                                 end)) : ShareDutyRA)
             ∗
             ShareDuty_init_inr).
  Proof.
    iIntros "I". iMod (ShareDuty_init_div0 with "I") as "[I R]". iFrame.
    assert (((fun n => (fun k => match k with
                             | inl _ => _ShareDutyRA_init n
                             | inr _ => ε
                             end)) : ShareDutyRA)
              ~~> (((fun n => (fun k => match k with
                              | inl t => match NatMap.find t ths with
                                        | Some _ => _ShareDutyRA_init n
                                        | None => ε
                                        end
                              | inr _ => ε
                              end)) : ShareDutyRA)
                 ⋅
                 ((fun n => (fun k => match k with
                                | inl t => match NatMap.find t ths with
                                          | Some _ => ε
                                          | None => _ShareDutyRA_init n
                                          end
                                | inr _ => ε
                                end)) : ShareDutyRA))).
    { apply pointwise_dep_updatable. i.
      setoid_rewrite unfold_pointwise_add. apply pointwise_updatable. i. destruct a0.
      - des_ifs.
      - rewrite left_id. reflexivity.
    }
    iPoseProof (OwnM_Upd with "I") as "> [OWN0 OWN1]". eapply H. iModIntro. iFrame.
  Qed.

  Lemma ShareDuty_init_div n (ths : TIdSet.t) :
    ShareDuty_init
      ⊢
      |==> (
        (natmap_prop_sum ths (fun tid _ => (ShareDuty_black (n:=n) inlp tid [] ∗ ShareDuty_white (n:=n) inlp tid [])%I))
          ∗
          OwnM ((fun n' => (fun k => match k with
                               | inl t => match NatMap.find t ths with
                                         | Some _ => if Nat.eq_dec n n' then ε else _ShareDutyRA_init n'
                                         | None => ε
                                         end
                               | inr _ => ε
                               end)) : ShareDutyRA)
          ∗
          OwnM ((fun n' => (fun k => match k with
                               | inl t => match NatMap.find t ths with
                                         | Some _ => ε
                                         | None => if Nat.eq_dec n n' then _ShareDutyRA_init n' else ε
                                         end
                               | inr _ => ε
                               end)) : ShareDutyRA)
          ∗
          OwnM ((fun n' => (fun k => match k with
                               | inl t => match NatMap.find t ths with
                                         | Some _ => ε
                                         | None => if Nat.eq_dec n n' then ε else _ShareDutyRA_init n'
                                         end
                               | inr _ => ε
                               end)) : ShareDutyRA)
          ∗
          ShareDuty_init_inr).
  Proof.
    iIntros "I". iMod (ShareDuty_init_div1 with "I") as "[I [R $]]".
    assert (((fun n0 => (λ k0 : index + ident_tgt,
                           match k0 with
                           | inl t => match NatMap.find t ths with
                                     | Some _ => _ShareDutyRA_init n0
                                     | None => ε
                                     end
                           | inr _ => ε
                           end)) : ShareDutyRA)
              ~~>
              (((fun n0 => (λ k0 : index + ident_tgt,
                            match k0 with
                            | inl t => match NatMap.find t ths with
                                      | Some _ => if Nat.eq_dec n n0 then ε else _ShareDutyRA_init n0
                                      | None => ε
                                      end
                            | inr _ => ε
                            end)) : ShareDutyRA)
                 ⋅
                 ((fun n0 => (λ k0 : index + ident_tgt,
                              match k0 with
                              | inl t => match NatMap.find t ths with
                                        | Some _ => if Nat.eq_dec n n0 then _ShareDutyRA_init n0 else ε
                                        | None => ε
                                        end
                              | inr _ => ε
                              end)) : ShareDutyRA))).
    { apply pointwise_dep_updatable. i.
      setoid_rewrite unfold_pointwise_add. apply pointwise_updatable. i. destruct a0.
      { des_ifs. }
      rewrite right_id. reflexivity.
    }
    iPoseProof (OwnM_Upd with "I") as "> [$ I1]". eapply H. clear H.
    assert (((fun n0 => (λ k0 : index + ident_tgt,
                           match k0 with
                           | inl t => match NatMap.find t ths with
                                     | Some _ => ε
                                     | None => _ShareDutyRA_init n0
                                     end
                           | inr _ => ε
                           end)) : ShareDutyRA)
              ~~>
              (((fun n0 => (λ k0 : index + ident_tgt,
                            match k0 with
                            | inl t => match NatMap.find t ths with
                                      | Some _ => ε
                                      | None => if Nat.eq_dec n n0 then ε else _ShareDutyRA_init n0
                                      end
                            | inr _ => ε
                            end)) : ShareDutyRA)
                 ⋅
                 ((fun n0 => (λ k0 : index + ident_tgt,
                              match k0 with
                              | inl t => match NatMap.find t ths with
                                        | Some _ => ε
                                        | None => if Nat.eq_dec n n0 then _ShareDutyRA_init n0 else ε
                                        end
                              | inr _ => ε
                              end)) : ShareDutyRA))).
    { apply pointwise_dep_updatable. i.
      setoid_rewrite unfold_pointwise_add. apply pointwise_updatable. i. destruct a0.
      { des_ifs. }
      rewrite right_id. reflexivity.
    }
    iPoseProof (OwnM_Upd with "R") as "> [R0 R1]". eapply H. clear H.
    assert ((((fun n0 => (λ k0 : index + ident_tgt,
                            match k0 with
                            | inl t => match NatMap.find t ths with
                                      | Some _ => if Nat.eq_dec n n0 then _ShareDutyRA_init n0 else ε
                                      | None => ε
                                      end
                            | inr _ => ε
                            end)) : ShareDutyRA)
                 ⋅
                 ((fun n0 => (λ k0 : index + ident_tgt,
                              match k0 with
                              | inl t => match NatMap.find t ths with
                                        | Some _ => ε
                                        | None => if Nat.eq_dec n n0 then _ShareDutyRA_init n0 else ε
                                        end
                              | inr _ => ε
                              end)) : ShareDutyRA))
              ~~>
              ((fun n0 => (λ k0 : index + ident_tgt,
                           match k0 with
                           | inl t => if Nat.eq_dec n n0 then _ShareDutyRA_init n0 else ε
                           | inr _ => ε
                           end)) : ShareDutyRA)
           ).
    { apply pointwise_dep_updatable. i.
      setoid_rewrite unfold_pointwise_add. apply pointwise_updatable. i. destruct a0.
      { des_ifs. }
        rewrite left_id. reflexivity.
    }
    iCombine "I1 R1" as "OWN". iPoseProof (OwnM_Upd with "OWN") as "> OWN". eapply H. clear H. iFrame.
    iStopProof.
    pattern ths. revert ths. eapply nm_ind.
    { iIntros "OWN". iModIntro. iFrame. iApply natmap_prop_sum_empty. }
    i. iIntros "OWN". clear STRONG.
    iPoseProof (IH with "OWN") as "> [SUM OWN]".
    assert (((fun n0 => (λ k0 : index + ident_tgt,
               match k0 with
               | inl t => match NatMap.find (elt:=()) t m with
                          | Some _ => ε
                          | None => if Nat.eq_dec n n0 then _ShareDutyRA_init n0 else ε
                          end
               | inr _ => ε
               end)) : ShareDutyRA)
            ~~>
            (((fun n0 => (λ k0 : index + ident_tgt,
               match k0 with
               | inl t => match NatMap.find t (NatMap.add k v m) with
                          | Some _ => ε
                          | None => if Nat.eq_dec n n0 then _ShareDutyRA_init n0 else ε
                          end
               | inr _ => ε
               end)) : ShareDutyRA)
               ⋅
               (_ShareDutyRA_black (n:=n) inlp k [] ⋅ _ShareDutyRA_white (n:=n) inlp k []))).
    { unfold _ShareDutyRA_black, _ShareDutyRA_white.
      rewrite maps_to_res_dep_add. unfold maps_to_res_dep.
      apply pointwise_dep_updatable. intros n0.
      rewrite !discrete_fun_lookup_op.
      unfold eq_rect_r. destruct (Nat.eq_dec n n0).
      2:{ des_ifs. rewrite right_id. apply pointwise_updatable. i. des_ifs. }
      des_ifs. rewrite <- eq_rect_eq.
      setoid_rewrite unfold_pointwise_add. apply pointwise_updatable. i.
      rewrite !discrete_fun_lookup_op.
      unfold maps_to_res. destruct a.
      2:{ des_ifs. }
      destruct (Nat.eq_dec n k).
      - subst n. rewrite nm_find_add_eq. rewrite left_id. des_ifs.
      - rewrite nm_find_add_neq; auto. unfold Prism.review. ss. des_ifs. all: try (do 2 rewrite right_id; reflexivity).
    }
    iPoseProof (OwnM_Upd with "OWN") as "> [OWN0 [OWN1 OWN2]]". eapply H.
    iModIntro. iFrame. iApply (natmap_prop_sum_add with "SUM [-]"). iFrame.
  Qed.

  Lemma ShareDuty_init_wf: ✓ ((fun n => (fun _ => _ShareDutyRA_init n)) : ShareDutyRA).
  Proof.
    intros ??. apply excl_auth_valid.
  Qed.

  Lemma Shareduty_black_white n tid l l' :
    ShareDuty_black (n:=n) inlp tid l ∗ ShareDuty_white (n:=n) inlp tid l'
      ⊢ ⌜l = l'⌝.
  Proof.
    iIntros "[B W]". unfold ShareDuty_black, ShareDuty_white. unfold _ShareDutyRA_black, _ShareDutyRA_white.
    iCombine "B" "W" as "BW". iPoseProof (OwnM_valid with "BW") as "%BW".
    rewrite maps_to_res_dep_add in BW.
    specialize (BW n). rewrite maps_to_res_dep_eq in BW.
    specialize (BW (inl tid)).
    rewrite discrete_fun_lookup_op /maps_to_res in BW.
    des_ifs. by apply excl_auth_agree_L in BW.
  Qed.

End SHAREDUTY.
