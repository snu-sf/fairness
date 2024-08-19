From iris.algebra Require Import cmra updates auth lib.excl_auth coPset.
From sflib Require Import sflib.
From Paco Require Import paco.
From Fairness Require Import ITreeLib pind.
Require Import Program.
From Fairness Require Import PCM IPM IPropAux SRA.
From Fairness Require Import Mod FairBeh.
From Fairness Require Import Axioms.
From Fairness Require Import NatMapRALarge MonotoneRA RegionRA FairnessRA IndexedInvariants ObligationRA OpticsInterp.

Local Instance frame_exist_instantiate_disabled :
FrameInstantiateExistDisabled := {}.

Set Implicit Arguments.

(* Section PAIR.
  Context {A B: Type}.

  Context `{IN: @GRA.inG (excl_authUR $ leibnizO (A * B)) Σ}.
  Context `{INA: @GRA.inG (excl_authUR $ leibnizO A) Σ}.
  Context `{INB: @GRA.inG (excl_authUR $ leibnizO B) Σ}.
  Notation iProp := (iProp Σ).

  Definition Own_pair (a : A) (b : B) : iProp :=
    own sduty_name (●E ((a, b) : leibnizO (A * B))).

  Definition Own_fst (a : A) (b : B) : iProp :=
    own sduty_name (●E ((a, b) : leibnizO (A * B))).

  Definition pair_sat: iProp :=
    ∃ (a : A) (b : B),
      (own sduty_name (●E ((a, b) : leibnizO (A * B))))
        ∗
        (own sduty_name (●E (a : leibnizO A)))
        ∗
        (own sduty_name (●E (b  : leibnizO B)))
  .

  Lemma pair_access_fst (a : A)
    :
    (own sduty_name (◯E (a: @Excl.t A)))
      -∗
      (pair_sat)
      -∗
      (∃ b, (own sduty_name (◯E ((a, b): @Excl.t (A * B))))
              ∗
              (∀ a,
                  ((own sduty_name (◯E ((a, b): @Excl.t (A * B))))
                     -∗
                     #=> ((own sduty_name (◯E (a: @Excl.t A))) ∗ (pair_sat))))).
  Proof.
    iIntros "H [% [% [H0 [H1 H2]]]]".
    iPoseProof (black_white_equal with "H1 H") as "%". subst.
    iExists _. iFrame. iIntros (?) "H0".
    iPoseProof (black_white_update with "H1 H") as "> [H1 H]".
    iModIntro. iFrame. iExists _, _. iFrame.
  Qed.

  Lemma pair_access_snd b
    :
    (own sduty_name (◯E (b: @Excl.t B)))
      -∗
      (pair_sat)
      -∗
      (∃ a, (own sduty_name (◯E ((a, b): @Excl.t (A * B))))
              ∗
              (∀ b,
                  ((own sduty_name (◯E ((a, b): @Excl.t (A * B))))
                     -∗
                     #=> ((own sduty_name (◯E (b: @Excl.t B))) ∗ (pair_sat))))).
  Proof.
    iIntros "H [% [% [H0 [H1 H2]]]]".
    iPoseProof (black_white_equal with "H2 H") as "%". subst.
    iExists _. iFrame. iIntros (?) "H0".
    iPoseProof (black_white_update with "H2 H") as "> [H2 H]".
    iModIntro. iFrame. iExists _, _. iFrame.
  Qed.
End PAIR. *)

(* Anything other than this goes in small. *)
(* Class TLRAs (STT : StateTypes) (Γ : SRA.t) (Σ : GRA.t) :=
{
  (* Invariant related default RAs *)
  _IINVSETRA : @GRA.inG (IInvSetRA sProp) Σ;
  (* Liveness logic related default RAs *)
  _ARROWRA: @GRA.inG (@ArrowRA id_tgt_type sProp) Σ;
  _SHAREDUTY: @GRA.inG (@ShareDutyRA id_tgt_type sProp) Σ;
}. *)

Class sim_defaultGpreS (Σ : gFunctors) (state_src state_tgt : Type) (ident_src ident_tgt : ID) := Sim_defaultGpreS {
  (* Invariant related default RAs *)
  sim_defaultGpreS_wsat : wsatGpreS Σ;
  (* State related default RAs *)
  sim_defaultGpreS_th : inG Σ (authR (NatMapRALarge.t ()));
  sim_defaultGpreS_state: stateGpreS state_src state_tgt Σ;
  sim_defaultGpreS_id_src : FairRA.srcG Σ ident_src;
  sim_defaultGpreS_id_tgt : FairRA.tgtG Σ ident_tgt;
  (* Liveness logic related default RAs *)
  sim_defaultGpreS_obligation : obligationG Σ;
  sim_defaultGpreS_edge : ObligationRA.edgeGpreS Σ;
  sim_defaultGpreS_oneshot : ObligationRA.oneshotG Σ;
}.

Class sim_defaultGS (Σ : gFunctors) (state_src state_tgt : Type) (ident_src ident_tgt : ID) := Sim_defaultGS {
  #[global] sim_defaultGS_wsat :: wsatGS Σ;
  #[global] sim_defaultGS_th :: inG Σ (authR (NatMapRALarge.t unit));
  #[global] sim_defaultGS_state :: stateGS state_src state_tgt Σ;
  #[global] sim_defaultGS_id_src :: FairRA.srcG Σ ident_src;
  #[global] sim_defaultGS_id_tgt :: FairRA.tgtG Σ ident_tgt;
  #[global] sim_defaultGS_obligation :: obligationG Σ;
  #[global] sim_defaultGS_edge :: ObligationRA.edgeGS Σ;
  #[global] sim_defaultGS_oneshot :: ObligationRA.oneshotG Σ;
  fsrc_name : gname;
  ftgt_name : gname;
  th_name : gname;
}.

Definition sim_defaultΣ (state_src state_tgt : Type) (ident_src ident_tgt : ID) : gFunctors :=
  #[wsatΣ;
    GFunctor (authR (NatMapRALarge.t unit));
    stateΣ state_src state_tgt;
    FairRA.srcΣ ident_src;
    FairRA.tgtΣ ident_tgt;
    obligationΣ;
    ObligationRA.edgeΣ;
    ObligationRA.oneshotΣ
  ].

Global Instance subG_sim_defaultGpreS {Σ} {state_src state_tgt : Type} {ident_src ident_tgt : ID} :
  subG (sim_defaultΣ state_src state_tgt ident_src ident_tgt) Σ →
  sim_defaultGpreS Σ state_src state_tgt ident_src ident_tgt.
Proof. solve_inG. Qed.

Local Existing Instances
  sim_defaultGpreS_wsat
  sim_defaultGpreS_th
  sim_defaultGpreS_state
  sim_defaultGpreS_id_src sim_defaultGpreS_id_tgt
  sim_defaultGpreS_obligation
  sim_defaultGpreS_edge
  sim_defaultGpreS_oneshot
  .

Global Instance sra_subG_sim_defaultGS {Γ Σ} {state_src state_tgt : Type} {ident_src ident_tgt : ID} :
  SRA.subG Γ Σ →
  sim_defaultGS (SRA.to_gf Γ) state_src state_tgt ident_src ident_tgt →
  sim_defaultGS Σ state_src state_tgt ident_src ident_tgt.
Proof.
  intros SUB [].
  split; try apply _.
  - exact fsrc_name0.
  - exact ftgt_name0.
  - exact th_name0.
Defined.

Global Arguments fsrc_name {_} {_} {_} {_} {_} {_}.
Global Arguments ftgt_name {_} {_} {_} {_} {_} {_}.
Global Arguments th_name {_} {_} {_} {_} {_} {_}.

Section INVARIANT.
  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable ident_src: ID.
  Variable ident_tgt: ID.
  Context `{!EqDecision ident_tgt, !EqDecision ident_src}.


  Local Notation index := nat.

  Context `{SIM: !sim_defaultGS Σ state_src state_tgt ident_src ident_tgt,
            ARR: !ObligationRA.arrow_thGS Σ ident_tgt Vars,
            INV: !IInvSet Σ Vars}.

  Notation iProp := (iProp Σ).

  (* Works for formulas with index < x. *)
  Definition fairI x : iProp :=
    (ObligationRA.edges_sat)
      ∗
      (ObligationRA.arrows_sats ftgt_name (S := sum_tid ident_tgt) x).

  Definition default_I x :
    TIdSet.t -> (@imap ident_src owf) -> (@imap (sum_tid ident_tgt) nat_wf) -> state_src -> state_tgt -> iProp :=
    λ ths im_src im_tgt st_src st_tgt,
      (own th_name (● (NatMapRALarge.to_Map ths))
         ∗
         St_src_inv st_src
         ∗
         St_tgt_inv st_tgt
         ∗
         FairRA.sat_source fsrc_name im_src
         ∗
         FairRA.sat_target ftgt_name im_tgt ths
         ∗
         ObligationRA.edges_sat
         ∗
         ObligationRA.arrows_sats ftgt_name (S := sum_tid ident_tgt) x
         ∗
         ObligationRA.arrows_auth (S := sum_tid ident_tgt) x
      )%I
  .

  Definition default_I_past (tid: thread_id) x
    : TIdSet.t -> (@imap ident_src owf) -> (@imap (sum_tid ident_tgt) nat_wf) -> state_src -> state_tgt -> iProp :=
    λ ths im_src im_tgt st_src st_tgt,
      (∃ im_tgt0,
          (⌜fair_update im_tgt0 im_tgt (prism_fmap inlp (tids_fmap tid ths))⌝)
            ∗ (default_I x ths im_src im_tgt0 st_src st_tgt))%I.

  Definition own_thread (tid: thread_id): iProp :=
    own th_name (◯ NatMapRALarge.singleton tid tt).

  Lemma own_thread_unique tid0 tid1
    :
    ⊢ (own_thread tid0)
      -∗
      (own_thread tid1)
      -∗
      ⌜tid0 <> tid1⌝.
  Proof.
    iIntros "OWN0 OWN1".
    by iCombine "OWN0 OWN1" gives
      %WF%auth_frag_valid%NatMapRALarge.singleton_unique.
  Qed.

  Lemma default_I_update_st_src x ths im_src im_tgt st_src0 st_tgt st_src' st_src1
    :
    ⊢ (default_I x ths im_src im_tgt st_src0 st_tgt)
      -∗
      (St_src st_src')
      -∗
      #=> (St_src st_src1)
                ∗ default_I x ths im_src im_tgt st_src1 st_tgt.
  Proof.
    unfold default_I. iIntros "[A [B [C [D [E [F G]]]]]] OWN".
    iPoseProof (black_white_update with "B OWN") as "> [B OWN]".
    iModIntro. iFrame.
  Qed.

  Lemma default_I_update_st_tgt x ths im_src im_tgt st_src st_tgt0 st_tgt' st_tgt1
    :
    ⊢ (default_I x ths im_src im_tgt st_src st_tgt0)
      -∗
      (St_tgt st_tgt')
      -∗
      #=> (St_tgt st_tgt1)
                ∗ default_I x ths im_src im_tgt st_src st_tgt1.
  Proof.
    unfold default_I. iIntros "[A [B [C [D [E [F G]]]]]] OWN".
    iPoseProof (black_white_update with "C OWN") as "> [C OWN]".
    iModIntro. iFrame.
  Qed.

  Lemma default_I_get_st_src x ths im_src im_tgt st_src st_tgt st
    :
    ⊢ (default_I x ths im_src im_tgt st_src st_tgt)
      -∗
      (St_src st)
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
      (St_tgt st)
      -∗
      ⌜st_tgt = st⌝.
  Proof.
    unfold default_I. iIntros "[A [B [C [D [E [F G]]]]]] OWN".
    iPoseProof (black_white_equal with "C OWN") as "%". clarify.
  Qed.

  Lemma default_I_thread_alloc x n ths0 im_src im_tgt0 st_src st_tgt
        tid ths1 im_tgt1
        (THS: TIdSet.add_new tid ths0 ths1)
        (TID_TGT : fair_update im_tgt0 im_tgt1 (prism_fmap inlp (λ i, if tid_dec i tid then Flag.success else Flag.emp)))
    :
    ⊢
      (default_I x ths0 im_src im_tgt0 st_src st_tgt)
      -∗
      #=> (own_thread tid ∗ ObligationRA.duty n inlp ftgt_name tid [] ∗ default_I x ths1 im_src im_tgt1 st_src st_tgt).
  Proof.
    unfold default_I. iIntros "[A [B [C [D [E [F G]]]]]]".
    iMod (own_update with "A") as "[A TH]".
    { apply auth_update_alloc,NatMapRALarge.add_local_update.
      inv THS. apply NEW.
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
        (PENDS : Forall2 (λ '(k1, _, _) '(k2, _), k1 = k2) l1 ps)
    :
    (n < x) ->
    ⊢
      (default_I x ths im_src im_tgt0 st_src st_tgt)
      -∗
      ((ObligationRA.duty n inlp ftgt_name tid l)
         ∗ (ObligationRA.pends ps)
         ∗ (ObligationRA.taxes (List.map fst l2) Ord.omega)
      )
      -∗
      #=> ((ObligationRA.duty n inlp ftgt_name tid l)
             ∗ (FairRA.white_thread ftgt_name)
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
    rewrite IUpd_eq.
    iMod ("RES" with "ARROW") as "[ARROW [E [DUTY [WHITE OPENDS]]]]".
    iPoseProof (ObligationRA.opends_to_pends2 with "OPENDS") as "PENDS".
    iFrame. iApply "K". iFrame.
  Qed.

  Lemma default_I_update_ident_thread x n ths im_src im_tgt0 st_src st_tgt
        tid im_tgt1 l
        (UPD: fair_update im_tgt0 im_tgt1 (prism_fmap inlp (tids_fmap tid ths)))
    :
    (n < x) ->
    ⊢
      (default_I x ths im_src im_tgt0 st_src st_tgt)
      -∗
      (ObligationRA.duty n inlp ftgt_name tid l ∗ ObligationRA.taxes (List.map fst l) Ord.omega)
      -∗
      #=> (ObligationRA.duty n inlp ftgt_name tid l ∗ FairRA.white_thread ftgt_name ∗ default_I x ths im_src im_tgt1 st_src st_tgt).
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
      (list_prop_sum (λ '(i, l), ObligationRA.duty n (inrp ⋅ p)%prism ftgt_name i l ∗ ObligationRA.taxes (List.map fst l) Ord.omega) ls)
      -∗
      #=> ((list_prop_sum (λ '(i, l), ObligationRA.duty n (inrp ⋅ p)%prism ftgt_name i l) ls)
             ∗
             (list_prop_sum (λ i, FairRA.white (Id:=_) (inrp ⋅ p)%prism ftgt_name i 1) lf)
             ∗
             default_I x ths im_src im_tgt1 st_src st_tgt).
  Proof.
    unfold default_I. iIntros (LT) "[A [B [C [D [E [F [G H]]]]]]] DUTY".
    iPoseProof (ObligationRA.target_update with "E DUTY") as "RES". 1,2,3,4: eauto.
    iMod (Regions.nsats_sat_sub with "G") as "[ARROW K]". apply LT.
    rewrite IUpd_eq.
    iMod ("RES" with "ARROW") as "[ARROW [E [DUTY WHITE]]]". iFrame.
    iApply "K". iFrame.
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
      (list_prop_sum (λ i, FairRA.white Prism.id fsrc_name i Ord.one) lf)
      -∗
      #=> (∃ im_src1,
              (⌜fair_update im_src0 im_src1 fm⌝)
                ∗
                (list_prop_sum (λ i, FairRA.white Prism.id fsrc_name i o) ls)
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
    ⊢ SubIProp (ObligationRA.arrows_sat n ftgt_name (S := sum_tid ident_tgt)) (default_I x ths im_src im_tgt st_src st_tgt).
  Proof.
    iIntros (LT) "[A [B [C [D [E [F [G H]]]]]]]".
    iMod (Regions.nsats_sat_sub with "G") as "[ARROW K]". apply LT.
    iFrame. iModIntro. iFrame.
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
      (St_src st_src')
      -∗
      #=> (St_src st_src1
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
      (St_tgt st_tgt')
      -∗
      #=> (St_tgt st_tgt1)
                ∗ default_I_past tid x ths im_src im_tgt st_src st_tgt1.
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
      St_src st
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
      St_tgt st
      -∗
      ⌜st_tgt = st⌝.
  Proof.
    iIntros "[% [% D]] H". iApply (default_I_get_st_tgt with "D H").
  Qed.

  Lemma default_I_past_update_ident_thread_pending x n ths im_src im_tgt st_src st_tgt
        tid l
        l1 l2 ps
        (OBLIGS : l = l1 ++ l2)
        (PENDS : Forall2 (λ '(k1, _, _) '(k2, _), k1 = k2) l1 ps)
    :
    (n < x) ->
    ⊢
      (default_I_past tid x ths im_src im_tgt st_src st_tgt)
      -∗
      (ObligationRA.duty n inlp ftgt_name tid l ∗ ObligationRA.pends ps ∗ ObligationRA.taxes (List.map fst l2) Ord.omega)
      -∗
      #=> (ObligationRA.duty n inlp ftgt_name tid l ∗ FairRA.white_thread ftgt_name ∗ default_I x ths im_src im_tgt st_src st_tgt ∗ ObligationRA.pends ps).
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
      (ObligationRA.duty n inlp ftgt_name tid l ∗ ObligationRA.taxes (List.map fst l) Ord.omega)
      -∗
      #=> (ObligationRA.duty n inlp ftgt_name tid l ∗ FairRA.white_thread ftgt_name ∗ default_I x ths im_src im_tgt st_src st_tgt).
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
      (list_prop_sum (λ '(i, l), ObligationRA.duty n (inrp ⋅ p)%prism ftgt_name  i l ∗ ObligationRA.taxes (List.map fst l) Ord.omega) ls)
      -∗
      #=> ((list_prop_sum (λ '(i, l), ObligationRA.duty n (inrp ⋅ p)%prism ftgt_name i l) ls)
             ∗
             (list_prop_sum (λ i, FairRA.white (inrp ⋅ p)%prism ftgt_name i 1) lf)
             ∗
             default_I_past tid x ths im_src im_tgt1 st_src st_tgt).
  Proof.
    iIntros (LT) "[% [% D]] H".
    iPoseProof (default_I_update_ident_target with "D H") as "> [H0 [H1 D]]". 1,2,3,4,5: eauto.
    { instantiate (1:=(λ i,
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
      (list_prop_sum (λ i, FairRA.white Prism.id fsrc_name i Ord.one) lf)
      -∗
      #=> (∃ im_src1,
              (⌜fair_update im_src0 im_src1 fm⌝)
                ∗
                (list_prop_sum (λ i, FairRA.white Prism.id fsrc_name i o) ls)
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
      (list_prop_sum (λ i, FairRA.white p fsrc_name i Ord.one) lf)
      -∗
      #=> (∃ im_src1,
              (⌜fair_update im_src0 im_src1 (prism_fmap p fm)⌝)
                ∗
                (list_prop_sum (λ i, FairRA.white p fsrc_name i o) ls)
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
      (own_thread tid ∗ ObligationRA.duty n inlp ftgt_name tid [])
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
    iPoseProof (own_update with "A") as "> X".
    { apply auth_update_dealloc. eapply (@NatMapRALarge.remove_local_update unit ths0 _ _). }
    iPoseProof (FairRA.target_remove_thread with "E [DUTY]") as "> E".
    { iPoseProof "DUTY" as "[% [% [A [[B %] %]]]]". destruct rs; ss. subst. iFrame. }
    iModIntro. iExists _. iSplitR; [iPureIntro;auto|].
    iFrame.
  Qed.

End INVARIANT.

Section INIT.

  Context `{Σ: gFunctors}.

  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable ident_src: ID.
  Variable ident_tgt: ID.
  Context `{!EqDecision ident_tgt (*, !EqDecision ident_src *) }.

  Local Notation index := nat.
  Context `{Vars : index -> Type}.
  Context `{Invs : IInvSet Σ Vars}.

  (* TODO: this is nessecary to make some inference work. *)

  Definition default_initial_res
    : Σ :=
    (@GRA.embed _ _ OWNERA (CoPset ⊤))
      ⋅
      (@GRA.embed _ _ IINVSETRA ((λ n, ●  ((λ _ => None) : (positive ==> optionUR (agreeR $ leibnizO (Vars n)))%ra)) : IInvSetRA Vars))
      ⋅
      (@GRA.embed _ _ THDRA (● (NatMapRALarge.to_Map (NatMap.empty unit): NatMapRALarge.t unit)))
      ⋅
      (@GRA.embed _ _ STATESRC ((●E (None : leibnizO (option state_src))) ⋅ (◯E (None : leibnizO (option state_src))) : stateSrcRA state_src))
      ⋅
      (@GRA.embed _ _ STATETGT ((●E (None : leibnizO (option state_tgt))) ⋅ (◯E (None : leibnizO (option state_tgt))): stateTgtRA state_tgt))
      ⋅
      (@GRA.embed _ _ IDENTSRC (@FairRA.source_init_resource ident_src))
      ⋅
      (@GRA.embed _ _ IDENTTGT ((λ _ => Fuel.black 0 1%Qp): identTgtRA ident_tgt))
      ⋅
      (@GRA.embed _ _ EDGERA ((λ _ => OneShot.pending _ 1%Qp): EdgeRA))
      ⋅
      (@GRA.embed _ _ ARROWRA ((@Regions.nauth_ra _ 0): @ArrowRA ident_tgt Vars))
  .

  Lemma own_threads_init `{!sim_defaultGS Σ state_src state_tgt ident_src ident_tgt} ths
    :
    (own th_name (● (NatMapRALarge.to_Map (NatMap.empty unit))))
      -∗
      (#=>
         ((own th_name ((● (NatMapRALarge.to_Map ths))))
            ) ∗
            (natmap_prop_sum ths (λ tid _, own_thread tid))).
  Proof.
    pattern ths. revert ths. eapply nm_ind.
    { iIntros "OWN". iModIntro. iFrame. }
    i. iIntros "OWN".
    iPoseProof (IH with "OWN") as "> [OWN SUM]".
    iPoseProof (own_update with "OWN") as "> [OWN0 OWN1]".
    { eapply auth_update_alloc. eapply (@NatMapRALarge.add_local_update unit m k v); eauto. }
    iModIntro. iFrame. destruct v. iApply (natmap_prop_sum_add with "SUM OWN1").
  Qed.

  Lemma default_initial_res_init `{SIM: !sim_defaultGpreS Σ state_src state_tgt ident_src ident_tgt, ARR: !ObligationRA.arrow_thGpreS Σ ident_tgt Vars, IRA : invGpreS Σ Vars, INV: !IInvSet Σ Vars} x n (LT : n < x)
    :
    ⊢
      (∀ ths (st_src : state_src) (st_tgt : state_tgt) im_tgt o,
          #=>
          (∃ (_ : sim_defaultGS Σ state_src state_tgt ident_src ident_tgt)
            (_ : ObligationRA.arrow_thGpreS Σ ident_tgt Vars)
            (_ : invGS Σ Vars)
            im_src,
                  (default_I x ths im_src im_tgt st_src st_tgt)
                    ∗
                    (natmap_prop_sum ths (λ tid _, ObligationRA.duty n inlp ftgt_name tid []))
                    ∗
                    (natmap_prop_sum ths (λ tid _, own_thread tid))
                    ∗
                    (FairRA.whites Prism.id fsrc_name (λ _, True: Prop) o)
                    ∗
                    (FairRA.blacks Prism.id ftgt_name (λ i, match i with | inr _ => True | _ => False end: Prop))
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
    iIntros (? ? ? ? ?).
    iMod (wsat_alloc x) as (WsatGS InvGS) "(IA & IW & IE)".
    iMod (FairRA.source_alloc o) as (γfs f) "[FsS FsW]".
    iMod FairRA.target_alloc as (γft) "(FtS & FtBex & FtB)".
    iMod state_alloc as (StateGS) "(StS & StSI & StT & StTI)".
    unfold default_I.

    iMod (own_alloc (● (NatMapRALarge.to_Map (NatMap.empty ())))) as (γt) "ThI"; first by apply auth_auth_valid.
    iMod (ObligationRA.arrows_sats_alloc x γft) as (ArrGS) "[AS AA]".
    iMod ObligationRA.edges_alloc as (EdgeGS) "ES".

    set (Hsim := Sim_defaultGS _ _ _ _ _ _ _ _ γfs γft γt).
    iMod (own_threads_init with "[ThI]") as "[ThI H]".
    { subst Hsim. iFrame. }
    subst Hsim.

    iModIntro.
    iExists (Sim_defaultGS _ _ _ _ _ _ _ _ γfs γft γt), ArrGS, InvGS, f.
    iFrame.
    iSplitR "FtB".
    { iApply natmap_prop_sum_impl; [|eauto]. i. ss.
      iApply ObligationRA.black_to_duty.
    }
    { iPoseProof (FairRA.blacks_prism_id with "FtB") as "H".
      iDestruct (FairRA.blacks_impl with "H") as "$".
      i. simpl in *. des_ifs. esplits; eauto.
    }
  Qed.

End INIT.

Definition _ShareDutyRA (ident_tgt : ID) (Vars : nat → Type) n : ofe :=
    (nat + ident_tgt) -d> (excl_authUR $ leibnizO (list (nat * nat * Vars n))).
Definition ShareDutyRA (ident_tgt : ID) (Vars : nat → Type) : ucmra :=
    discrete_funUR (_ShareDutyRA ident_tgt Vars).

Class share_dutyGpreS (Σ : gFunctors) (ident_tgt : ID) (Vars : nat → Type) := {
  share_dutyGpreS_fun : inG Σ (ShareDutyRA ident_tgt Vars);
}.

Class share_dutyGS (Σ : gFunctors) (ident_tgt : ID) (Vars : nat → Type) := Share_dutyGS {
  share_dutyGS_inG : share_dutyGpreS Σ ident_tgt Vars;
  sduty_name : gname;
}.

Local Existing Instances share_dutyGS_inG share_dutyGpreS_fun.

Definition share_dutyΣ (ident_tgt : ID) (Vars : nat → Type) :=
  #[ GFunctor (ShareDutyRA ident_tgt Vars) ].

Global Instance share_duty_subG {Σ ident_tgt Vars} :
  subG (share_dutyΣ (ident_tgt : ID) (Vars : nat → Type)) Σ → share_dutyGpreS Σ ident_tgt Vars.
Proof. solve_inG. Qed.

From iris.algebra Require Import functions.

Section SHAREDUTY.
  Variable ident_tgt: ID.

  Local Notation index := nat.
  Context `{Vars : index -> Type}.

  Notation _ShareDutyRA := (_ShareDutyRA ident_tgt Vars).
  Notation ShareDutyRA := (ShareDutyRA ident_tgt Vars).

  Context `{SHAREDUTY : !share_dutyGS Σ ident_tgt Vars}.
  Notation iProp := (iProp Σ).

  Definition _ShareDutyRA_init n : (excl_authUR $ leibnizO (list (nat * nat * Vars n))) :=
    ●E ([] : leibnizO _) ⋅ ◯E ([] : leibnizO _).

  Definition ShareDuty_init : iProp :=
    own sduty_name ((λ n, (λ _, _ShareDutyRA_init n)) : ShareDutyRA).

  Definition ShareDuty_init_inl : iProp :=
    own sduty_name ((λ n, (λ k, match k with
                        | inl _ => _ShareDutyRA_init n
                        | inr _ => ε
                        end)) : ShareDutyRA).

  Definition ShareDuty_init_inr : iProp :=
    own sduty_name ((λ n, (λ k, match k with
                        | inl _ => ε
                        | inr _ => _ShareDutyRA_init n
                        end)) : ShareDutyRA).

  Definition _ShareDutyRA_black
             n {Id : Type} (p : Prism.t (nat + ident_tgt) Id) (i : Id) (l : list (nat * nat * Vars n)) : ShareDutyRA :=
    discrete_fun_singleton n (maps_to_res (Prism.review p i) (●E (l : leibnizO _))) : ShareDutyRA.

  Definition ShareDuty_black
             n {Id : Type} (p : Prism.t (nat + ident_tgt) Id) (i : Id) (l : list (nat * nat * Vars n)) : iProp :=
    own sduty_name  (_ShareDutyRA_black p i l).

  Definition _ShareDutyRA_white
             n {Id : Type} (p : Prism.t (nat + ident_tgt) Id) (i : Id) (l : list (nat * nat * Vars n)) : ShareDutyRA :=
    discrete_fun_singleton n (maps_to_res (Prism.review p i) (◯E (l : leibnizO _))) : ShareDutyRA.
  Definition ShareDuty_white
             n {Id : Type} (p : Prism.t (nat + ident_tgt) Id) (i : Id) (l : list (nat * nat * Vars n)) : iProp :=
    own sduty_name (_ShareDutyRA_white p i l).

  Lemma ShareDuty_init_div0 :
    ShareDuty_init
      ⊢ |==> (ShareDuty_init_inl ∗ ShareDuty_init_inr).
  Proof.
    iIntros "I". unfold ShareDuty_init.
    iMod (own_update with "I") as "[$ $]"; [|done].
    apply pointwise_dep_updatable. i.
    setoid_rewrite unfold_pointwise_add. apply pointwise_updatable. i. destruct a0.
    - rewrite right_id. reflexivity.
    - rewrite left_id. reflexivity.
  Qed.

  Lemma ShareDuty_init_div1 (ths : TIdSet.t) :
    ShareDuty_init
      ⊢
      |==> (
        own sduty_name ((λ n, (λ k, match k with
                            | inl t => match NatMap.find t ths with
                                      | Some _ => _ShareDutyRA_init n
                                      | None => ε
                                      end
                            | inr _ => ε
                            end)) : ShareDutyRA)
             ∗
             own sduty_name ((λ n, (λ k, match k with
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
    iMod (own_update with "I") as "[$ $]"; [|done].
    apply pointwise_dep_updatable. i.
    setoid_rewrite unfold_pointwise_add. apply pointwise_updatable. i. destruct a0.
    - des_ifs.
    - rewrite left_id. reflexivity.
  Qed.

  Lemma ShareDuty_init_div n (ths : TIdSet.t) :
    ShareDuty_init
      ⊢
      |==> (
        (natmap_prop_sum ths (λ tid _, (ShareDuty_black (n:=n) inlp tid [] ∗ ShareDuty_white (n:=n) inlp tid [])%I))
          ∗
          own sduty_name ((λ n', (λ k, match k with
                               | inl t => match NatMap.find t ths with
                                         | Some _ => if Nat.eq_dec n n' then ε else _ShareDutyRA_init n'
                                         | None => ε
                                         end
                               | inr _ => ε
                               end)) : ShareDutyRA)
          ∗
          own sduty_name ((λ n', (λ k, match k with
                               | inl t => match NatMap.find t ths with
                                         | Some _ => ε
                                         | None => if Nat.eq_dec n n' then _ShareDutyRA_init n' else ε
                                         end
                               | inr _ => ε
                               end)) : ShareDutyRA)
          ∗
          own sduty_name ((λ n', (λ k, match k with
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
    assert (((λ n0, (λ k0 : index + ident_tgt,
                           match k0 with
                           | inl t => match NatMap.find t ths with
                                     | Some _ => _ShareDutyRA_init n0
                                     | None => ε
                                     end
                           | inr _ => ε
                           end)) : ShareDutyRA)
              ~~>
              (((λ n0, (λ k0 : index + ident_tgt,
                            match k0 with
                            | inl t => match NatMap.find t ths with
                                      | Some _ => if Nat.eq_dec n n0 then ε else _ShareDutyRA_init n0
                                      | None => ε
                                      end
                            | inr _ => ε
                            end)) : ShareDutyRA)
                 ⋅
                 ((λ n0, (λ k0 : index + ident_tgt,
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
    iPoseProof (own_update with "I") as "> [$ I1]". eapply H. clear H.
    assert (((λ n0, (λ k0 : index + ident_tgt,
                           match k0 with
                           | inl t => match NatMap.find t ths with
                                     | Some _ => ε
                                     | None => _ShareDutyRA_init n0
                                     end
                           | inr _ => ε
                           end)) : ShareDutyRA)
              ~~>
              (((λ n0, (λ k0 : index + ident_tgt,
                            match k0 with
                            | inl t => match NatMap.find t ths with
                                      | Some _ => ε
                                      | None => if Nat.eq_dec n n0 then ε else _ShareDutyRA_init n0
                                      end
                            | inr _ => ε
                            end)) : ShareDutyRA)
                 ⋅
                 ((λ n0, (λ k0 : index + ident_tgt,
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
    iPoseProof (own_update with "R") as "> [R0 R1]". eapply H. clear H.
    assert ((((λ n0, (λ k0 : index + ident_tgt,
                            match k0 with
                            | inl t => match NatMap.find t ths with
                                      | Some _ => if Nat.eq_dec n n0 then _ShareDutyRA_init n0 else ε
                                      | None => ε
                                      end
                            | inr _ => ε
                            end)) : ShareDutyRA)
                 ⋅
                 ((λ n0, (λ k0 : index + ident_tgt,
                              match k0 with
                              | inl t => match NatMap.find t ths with
                                        | Some _ => ε
                                        | None => if Nat.eq_dec n n0 then _ShareDutyRA_init n0 else ε
                                        end
                              | inr _ => ε
                              end)) : ShareDutyRA))
              ~~>
              ((λ n0, (λ k0 : index + ident_tgt,
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
    iCombine "I1 R1" as "OWN". iPoseProof (own_update with "OWN") as "> OWN". eapply H. clear H. iFrame.
    iStopProof.
    pattern ths. revert ths. eapply nm_ind.
    { iIntros "OWN". iModIntro. iFrame. iApply natmap_prop_sum_empty. }
    i. iIntros "OWN". clear STRONG.
    iPoseProof (IH with "OWN") as "> [SUM OWN]".
    assert (((λ n0, (λ k0 : index + ident_tgt,
               match k0 with
               | inl t => match NatMap.find (elt:=()) t m with
                          | Some _ => ε
                          | None => if Nat.eq_dec n n0 then _ShareDutyRA_init n0 else ε
                          end
               | inr _ => ε
               end)) : ShareDutyRA)
            ~~>
            (((λ n0, (λ k0 : index + ident_tgt,
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
      rewrite discrete_fun_singleton_op.
      apply pointwise_dep_updatable => n0.
      rewrite !discrete_fun_lookup_op.
      destruct (Nat.eq_dec n n0).
      2:{ rewrite discrete_fun_lookup_singleton_ne // right_id.
          apply pointwise_updatable. i. des_ifs. }
      des_ifs.
      rewrite discrete_fun_lookup_singleton.
      setoid_rewrite unfold_pointwise_add. apply pointwise_updatable. i.
      rewrite !discrete_fun_lookup_op.
      unfold maps_to_res. destruct a.
      2:{ des_ifs. }
      destruct (Nat.eq_dec n k).
      - subst n. rewrite nm_find_add_eq. rewrite left_id. des_ifs.
      - rewrite nm_find_add_neq; auto. unfold Prism.review. ss. des_ifs. all: try (do 2 rewrite right_id; reflexivity).
    }
    iPoseProof (own_update with "OWN") as "> [OWN0 [OWN1 OWN2]]". eapply H.
    iModIntro. iFrame. iApply (natmap_prop_sum_add with "SUM [-]"). iFrame.
  Qed.

  Lemma ShareDuty_init_wf: ✓ ((λ n, (λ _, _ShareDutyRA_init n)) : ShareDutyRA).
  Proof.
    intros ??. apply excl_auth_valid.
  Qed.

  Lemma Shareduty_black_white n tid l l' :
    ShareDuty_black (n:=n) inlp tid l ∗ ShareDuty_white (n:=n) inlp tid l'
      ⊢ ⌜l = l'⌝.
  Proof.
    iIntros "[B W]". unfold ShareDuty_black, ShareDuty_white. unfold _ShareDutyRA_black, _ShareDutyRA_white.
    iCombine "B" "W" gives %BW.
    specialize (BW n).
    rewrite discrete_fun_lookup_op
      !discrete_fun_lookup_singleton in BW.
    specialize (BW (inl tid)).
    rewrite discrete_fun_lookup_op /maps_to_res in BW.
    des_ifs. by apply excl_auth_agree_L in BW.
  Qed.

End SHAREDUTY.
Global Arguments ShareDuty_init _ _ {_} {_}.

Lemma shared_duty_alloc `{!share_dutyGpreS Σ ident_tgt Vars} :
  ⊢ |==> ∃ _ : share_dutyGS Σ ident_tgt Vars,
          ShareDuty_init ident_tgt Vars.
Proof.
  iMod (own_alloc ((λ n, (λ _, _ShareDutyRA_init n)) : ShareDutyRA ident_tgt Vars )) as (γ) "H".
  { apply ShareDuty_init_wf. }
  iModIntro. iExists (Share_dutyGS _ γ). iFrame.
Qed.
