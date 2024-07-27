From sflib Require Import sflib.
From Paco Require Import paco.
From Fairness Require Import ITreeLib ModSim ModSimNat.
From Fairness Require PCM.
From Fairness Require Import PCM IProp IPM IPropAux.
From Fairness Require Import ISim.

From stdpp Require Import coPset gmap namespaces.
From Fairness Require Export IndexedInvariants NatMapRA MonotoneRA RegionRA FairnessRA ObligationRA OpticsInterp.
From Fairness Require Export SimDefaultRA LiveObligations.
From Fairness Require Import FairBeh.
Require Import Coq.Sorting.Mergesort.

Require Import Program.

Set Implicit Arguments.

Section STATE.

  Context `{Σ: GRA.t}.
  Notation iProp := (iProp Σ).

  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable ident_src: ID.
  Variable ident_tgt: ID.

  Let srcE := threadE ident_src state_src.
  Let tgtE := threadE ident_tgt state_tgt.

  Let shared_rel := TIdSet.t -> (@imap ident_src owf) -> (@imap (sum_tid ident_tgt) nat_wf) -> state_src -> state_tgt -> iProp.

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
  Context `{ONESHOTRA: @GRA.inG ArrowShotRA Σ}.
  Context `{ARROWRA: @GRA.inG (@ArrowRA ident_tgt Vars) Σ}.

  Variable x : index.
  Variable tid: thread_id.

  Let rel := (forall R_src R_tgt (Q: R_src -> R_tgt -> iProp), bool -> bool -> itree srcE R_src -> itree tgtE R_tgt -> iProp).

  Let unlift_rel
      (r: forall R_src R_tgt (Q: R_src -> R_tgt -> shared_rel), bool -> bool -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel): rel :=
        fun R_src R_tgt Q ps pt itr_src itr_tgt =>
          (∀ ths im_src im_tgt st_src st_tgt,
              (default_I_past tid x ths im_src im_tgt st_src st_tgt ∗ (wsat_auth x ∗ wsats x ∗ OwnE ⊤))
                -∗
                (@r R_src R_tgt (fun r_src r_tgt ths im_src im_tgt st_src st_tgt => (default_I_past tid x ths im_src im_tgt st_src st_tgt ∗ (wsat_auth x ∗ wsats x ∗ OwnE ⊤)) ∗ Q r_src r_tgt) ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt))%I.

  Let lift_rel (rr: rel):
    forall R_src R_tgt (QQ: R_src -> R_tgt -> shared_rel), bool -> bool -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel :=
        fun R_src R_tgt QQ ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt =>
          (∃ (Q: R_src -> R_tgt -> iProp)
             (EQ: QQ = (fun r_src r_tgt ths im_src im_tgt st_src st_tgt =>
                          (default_I_past tid x ths im_src im_tgt st_src st_tgt ∗ (wsat_auth x ∗ wsats x ∗ OwnE ⊤)) ∗ Q r_src r_tgt)),
              rr R_src R_tgt Q ps pt itr_src itr_tgt ∗
                 (default_I_past tid x ths im_src im_tgt st_src st_tgt ∗ (wsat_auth x ∗ wsats x ∗ OwnE ⊤)))%I.

  Let unlift_rel_base r
    :
    forall R_src R_tgt Q ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt,
      (r R_src R_tgt Q ps pt itr_src itr_tgt)
        -∗
        (default_I_past tid x ths im_src im_tgt st_src st_tgt ∗ (wsat_auth x ∗ wsats x ∗ OwnE ⊤))
        -∗
        (lift_rel
           r
           (fun r_src r_tgt ths im_src im_tgt st_src st_tgt => (default_I_past tid x ths im_src im_tgt st_src st_tgt ∗ (wsat_auth x ∗ wsats x ∗ OwnE ⊤)) ∗ Q r_src r_tgt)
           ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt).
  Proof.
    unfold lift_rel. i.
    iIntros "H D". iExists _, _. Unshelve.
    { iFrame. }
    { auto. }
  Qed.

  Let unlift_lift r
    :
    forall R_src R_tgt Q ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt,
      (lift_rel (unlift_rel r) Q ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
        ⊢ (r R_src R_tgt Q ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt).
  Proof.
    unfold lift_rel, unlift_rel. i.
    iIntros "[% [% [H D]]]". subst.
    iApply ("H" with "D").
  Qed.

  Let lift_unlift (r0: rel) (r1: forall R_src R_tgt (Q: R_src -> R_tgt -> shared_rel), bool -> bool -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel)
    :
    (∀ R_src R_tgt (Q: R_src -> R_tgt -> shared_rel) ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt,
        @lift_rel r0 R_src R_tgt Q ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt
                  -∗ r1 R_src R_tgt Q ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
      ⊢
      (∀ R_src R_tgt Q ps pt itr_src itr_tgt,
          r0 R_src R_tgt Q ps pt itr_src itr_tgt -∗ unlift_rel r1 Q ps pt itr_src itr_tgt).
  Proof.
    unfold lift_rel, unlift_rel.
    iIntros "IMPL" (? ? ? ? ? ? ?) "H". iIntros (? ? ? ? ?) "D".
    iApply "IMPL". iExists _, _. Unshelve.
    { iFrame. }
    { auto. }
  Qed.

  Let lift_rel_mon (rr0 rr1: rel)
      (MON: forall R_src R_tgt Q ps pt itr_src itr_tgt,
          (* bi_entails *)
          (rr0 R_src R_tgt Q ps pt itr_src itr_tgt)
            ⊢
            (#=> rr1 R_src R_tgt Q ps pt itr_src itr_tgt))
    :
    forall R_src R_tgt (QQ: R_src -> R_tgt -> shared_rel) ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt,
      (lift_rel rr0 QQ ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
        ⊢
        (#=> lift_rel rr1 QQ ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt).
  Proof.
    unfold lift_rel. i.
    iIntros "[% [% [H D]]]". subst.
    iPoseProof (MON with "H") as "> H".
    iModIntro. iExists _, _. Unshelve.
    { iFrame. }
    { auto. }
  Qed.

  Let I: shared_rel :=
        fun ths im_src im_tgt st_src st_tgt =>
          (default_I x ths im_src im_tgt st_src st_tgt ∗ (wsat_auth x ∗ wsats x ∗ OwnE ⊤))%I.

  Definition wpsim (E : coPset) : rel -> rel -> rel :=
    fun r g
      R_src R_tgt Q ps pt itr_src itr_tgt =>
      (∀ ths im_src im_tgt st_src st_tgt,
          (default_I_past tid x ths im_src im_tgt st_src st_tgt ∗ (wsat_auth x ∗ wsats x ∗ OwnE E))
            -∗
            (isim
               tid
               I
               (lift_rel r)
               (lift_rel g)
               (fun r_src r_tgt ths im_src im_tgt st_src st_tgt => (default_I_past tid x ths im_src im_tgt st_src st_tgt ∗ (wsat_auth x ∗ wsats x ∗ OwnE ⊤)) ∗ Q r_src r_tgt)
               ps pt itr_src itr_tgt
               ths im_src im_tgt st_src st_tgt))%I
  .

  Definition ibot5 { T0 T1 T2 T3 T4} (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) (x4: T4 x0 x1 x2 x3): iProp := False.
  Definition ibot7 { T0 T1 T2 T3 T4 T5 T6} (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) (x4: T4 x0 x1 x2 x3) (x5: T5 x0 x1 x2 x3 x4) (x6: T6 x0 x1 x2 x3 x4 x5): iProp := False.

  Definition isim_simple {Form : Type} {intpF : Form -> iProp}
             (I0 : TIdSet.t -> (@imap ident_src owf) -> (@imap (sum_tid ident_tgt) nat_wf) -> state_src -> state_tgt -> Form)
             (I1 : TIdSet.t -> (@imap ident_src owf) -> (@imap (sum_tid ident_tgt) nat_wf) -> state_src -> state_tgt -> Form) :
    forall R_src R_tgt (Q: R_src -> R_tgt -> Form), bool -> bool -> itree srcE R_src -> itree tgtE R_tgt -> TIdSet.t -> (@imap ident_src owf) -> (@imap (sum_tid ident_tgt) nat_wf) -> state_src -> state_tgt -> iProp
    :=
    fun R_src R_tgt Q ps pt itr_src itr_tgt ths ims imt sts stt =>
      let INV :=
        (fun ths ims imt sts stt => intpF (I0 ths ims imt sts stt))
      in
      let INV1 :=
        (fun ths ims imt sts stt => intpF (I1 ths ims imt sts stt))
      in
      let FIN :=
        (fun r_src r_tgt ths ims imt sts stt => ((INV1 ths ims imt sts stt) ∗ (intpF (Q r_src r_tgt)))%I)
      in
      let LIFTBOT :=
        (fun R_src R_tgt QQ ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt =>
           (∃ (Q: R_src -> R_tgt -> iProp)
              (EQ: QQ = (fun r_src r_tgt ths im_src im_tgt st_src st_tgt =>
                           (INV1 ths im_src im_tgt st_src st_tgt) ∗ (Q r_src r_tgt))),
               (* (ibot7 R_src R_tgt Q ps pt itr_src itr_tgt) *)
               (False)
                 ∗
                 (INV1 ths im_src im_tgt st_src st_tgt))%I)
      in
      (isim
         tid
         INV
         LIFTBOT
         LIFTBOT
         FIN
         ps pt itr_src itr_tgt
         ths ims imt sts stt)%I.


  (* Lemmas for wpsim. *)

  Record mytype
         (A: Type) :=
    mk_mytype {
        comp_a: A;
        comp_ths: TIdSet.t;
        comp_im_src: imap ident_src owf;
        comp_im_tgt: imap (sum_tid ident_tgt) nat_wf;
        comp_st_src: state_src;
        comp_st_tgt: state_tgt;
      }.

  Lemma wpsim_upd E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt itr_src itr_tgt
    :
    (#=> (wpsim E r g Q ps pt itr_src itr_tgt))
      -∗
      (wpsim E r g Q ps pt itr_src itr_tgt)
  .
  Proof.
    unfold wpsim. iIntros "H" (? ? ? ? ?) "D". iMod "H".
    iApply "H". auto.
  Qed.

  Lemma wpsim_discard E0 E1 r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt itr_src itr_tgt
        (TOP: E0 ⊆ E1)
    :
    (wpsim E0 r g Q ps pt itr_src itr_tgt)
      -∗
      (wpsim E1 r g Q ps pt itr_src itr_tgt)
  .
  Proof.
    unfold wpsim. iIntros "H" (? ? ? ? ?) "(D & WA & WS & E)".
    iApply "H". iFrame. iPoseProof (OwnE_subset with "E") as "[E0 _]"; [eapply TOP|].
    iFrame.
  Qed.

  Lemma wpsim_base E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt itr_src itr_tgt
        (TOP: ⊤ ⊆ E)
    :
    (@r _ _ Q ps pt itr_src itr_tgt)
      -∗
      (wpsim E r g Q ps pt itr_src itr_tgt)
  .
  Proof.
    rewrite <- wpsim_discard; [|eassumption].
    unfold wpsim. iIntros "H" (? ? ? ? ?) "D".
    iApply isim_base.
    iApply (unlift_rel_base with "H D").
  Qed.

  Lemma wpsim_mono_knowledge E (r0 g0 r1 g1: rel) R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt itr_src itr_tgt
        (MON0: forall R_src R_tgt (Q: R_src -> R_tgt -> iProp)
                 ps pt itr_src itr_tgt,
            (@r0 _ _ Q ps pt itr_src itr_tgt)
              -∗
              (#=> (@r1 _ _ Q ps pt itr_src itr_tgt)))
        (MON1: forall R_src R_tgt (Q: R_src -> R_tgt -> iProp)
                 ps pt itr_src itr_tgt,
            (@g0 _ _ Q ps pt itr_src itr_tgt)
              -∗
              (#=> (@g1 _ _ Q ps pt itr_src itr_tgt)))
    :
    (wpsim E r0 g0 Q ps pt itr_src itr_tgt)
      ⊢
      (wpsim E r1 g1 Q ps pt itr_src itr_tgt)
  .
  Proof.
    unfold wpsim. iIntros "H" (? ? ? ? ?) "D".
    iApply isim_mono_knowledge.
    { eapply lift_rel_mon. eauto. }
    { eapply lift_rel_mon. eauto. }
    iApply ("H" with "D").
  Qed.

  Lemma wpsim_coind E A
        (R_src: forall (a: A), Type)
        (R_tgt: forall (a: A), Type)
        (Q: forall (a: A), R_src a -> R_tgt a -> iProp)
        (ps pt: forall (a: A), bool)
        (itr_src : forall (a: A), itree srcE (R_src a))
        (itr_tgt : forall (a: A), itree tgtE (R_tgt a))
        (P: forall (a: A), iProp)
        (r g0: rel)
        (TOP: ⊤ ⊆ E)
        (COIND: forall (g1: rel) a,
            (□((∀ R_src R_tgt (Q: R_src -> R_tgt -> iProp)
                  ps pt itr_src itr_tgt,
                   @g0 R_src R_tgt Q ps pt itr_src itr_tgt -∗
                       @g1 R_src R_tgt Q ps pt itr_src itr_tgt)
                 ∗
                 (∀ a, P a -∗ @g1 (R_src a) (R_tgt a) (Q a) (ps a) (pt a) (itr_src a) (itr_tgt a))))
              -∗
              (P a)
              -∗
              (wpsim ⊤ r g1 (Q a) (ps a) (pt a) (itr_src a) (itr_tgt a)))
    :
    (forall a, (P a) ⊢ (wpsim E r g0 (Q a) (ps a) (pt a) (itr_src a) (itr_tgt a))).
  Proof.
    cut (forall (m: mytype A),
            bi_entails
              ((fun m => (P m.(comp_a) ∗ (default_I_past tid x m.(comp_ths) m.(comp_im_src) m.(comp_im_tgt) m.(comp_st_src) m.(comp_st_tgt) ∗ (wsat_auth x ∗ wsats x ∗ OwnE ⊤)))%I) m)
              (isim tid I (lift_rel r) (lift_rel g0) ((fun m => fun r_src r_tgt ths im_src im_tgt st_src st_tgt => ((default_I_past tid x ths im_src im_tgt st_src st_tgt ∗ (wsat_auth x ∗ wsats x ∗ OwnE ⊤)) ∗ Q m.(comp_a) r_src r_tgt)%I) m)
                    ((fun m => ps m.(comp_a)) m) ((fun m => pt m.(comp_a)) m) ((fun m => itr_src m.(comp_a)) m) ((fun m => itr_tgt m.(comp_a)) m) (comp_ths m) (comp_im_src m) (comp_im_tgt m) (comp_st_src m) (comp_st_tgt m))).
    { ss. i. rewrite <- wpsim_discard; [|eassumption].
      unfold wpsim. iIntros "H" (? ? ? ? ?) "D".
      specialize (H (mk_mytype a ths im_src im_tgt st_src st_tgt)). ss.
      iApply H. iFrame.
    }
    eapply isim_coind. i. iIntros "[# CIH [H D]]".
    unfold wpsim in COIND.
    iAssert (□((∀ R_src R_tgt (Q: R_src -> R_tgt -> iProp)
                  ps pt itr_src itr_tgt,
                   @g0 R_src R_tgt Q ps pt itr_src itr_tgt -∗ @unlift_rel g1 R_src R_tgt Q ps pt itr_src itr_tgt)
                 ∗
                 (∀ a, P a -∗ @unlift_rel g1 (R_src a) (R_tgt a) (Q a) (ps a) (pt a) (itr_src a) (itr_tgt a))))%I with "[CIH]" as "CIH'".
    { iPoseProof "CIH" as "# [CIH0 CIH1]". iModIntro. iSplitL.
      { iApply (lift_unlift with "CIH0"). }
      { iIntros. unfold unlift_rel.
        iIntros (?????) "?".
        iSpecialize ("CIH1" $! (mk_mytype _ _ _ _ _ _)). ss.
        iApply "CIH1". iFrame.
      }
    }
    iPoseProof (COIND with "CIH' H D") as "H".
    iApply (isim_mono_knowledge with "H").
    { auto. }
    { i. iIntros "H". iModIntro. iApply unlift_lift. auto. }
  Qed.

  Lemma wpsim_coind2 E A
        (R_src: forall (a: A), Type)
        (R_tgt: forall (a: A), Type)
        (Q: forall (a: A), R_src a -> R_tgt a -> iProp)
        (ps pt: forall (a: A), bool)
        (itr_src : forall (a: A), itree srcE (R_src a))
        (itr_tgt : forall (a: A), itree tgtE (R_tgt a))
        (P: forall (a: A), iProp)
        (TOP: ⊤ ⊆ E)
    :
    ⊢
      ∀ (r g0 : rel),
        ⌜(∀ (g1: rel) (a : A),
            (□((∀ R_src R_tgt (Q: R_src -> R_tgt -> iProp)
                  ps pt itr_src itr_tgt,
                   @g0 R_src R_tgt Q ps pt itr_src itr_tgt -∗
                       @g1 R_src R_tgt Q ps pt itr_src itr_tgt)
                 ∗
                 (∀ a, P a -∗ @g1 (R_src a) (R_tgt a) (Q a) (ps a) (pt a) (itr_src a) (itr_tgt a))))
              -∗
              (P a)
              -∗
              (wpsim ⊤ r g1 (Q a) (ps a) (pt a) (itr_src a) (itr_tgt a)))⌝
          -∗
          (∀ a, (P a) -∗ (wpsim E r g0 (Q a) (ps a) (pt a) (itr_src a) (itr_tgt a))).
  Proof.
    iIntros "% % %CIH". iIntros "% PA".
    iApply wpsim_coind. auto. 2: iApply "PA".
    intros. specialize (CIH g1 a0). apply CIH.
  Qed.


  Global Instance wpsim_elim_upd
         E r g R_src R_tgt
         (Q: R_src -> R_tgt -> iProp)
         ps pt itr_src itr_tgt p
         P
    :
    ElimModal True p false (#=> P) P (wpsim E r g Q ps pt itr_src itr_tgt) (wpsim E r g Q ps pt itr_src itr_tgt).
  Proof.
    typeclasses eauto.
  Qed.

  Lemma wpsim_FUpd E0 E1 n r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt itr_src itr_tgt
    :
    (n <= x) ->
    (=|n|=(fairI (ident_tgt:=ident_tgt) x)={E0,E1}=> (wpsim E1 r g Q ps pt itr_src itr_tgt))
      ⊢
      (wpsim E0 r g Q ps pt itr_src itr_tgt)
  .
  Proof.
    Local Transparent FUpd.
    intros LE. iIntros "H" (? ? ? ? ?) "[[% [% (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8)]] (WAUTH & WSAT & E)]".
    iAssert (=|x|=(fairI (ident_tgt:=ident_tgt) x)={E0,E1}=> (wpsim E1 r g Q ps pt itr_src itr_tgt)) with "[H]" as "H".
    { inv LE. iFrame. iApply FUpd_mono. 2: iFrame. lia. }
    iAssert (fairI (ident_tgt:=ident_tgt) x ∗ (wsats x ∗ OwnE E0))%I with "[D6 D7 WSAT E]" as "C".
    { iFrame. }
    unfold FUpd. iMod ("H" with "C") as "(F & WSAT & E & H)".
    iApply "H". iFrame. iExists _. iFrame. auto.
    Local Opaque FUpd.
  Qed.

  Lemma wpsim_FUpd_simple E0 E1 n r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt itr_src itr_tgt
    :
    (n <= x) ->
    (=|n|={E0,E1}=> (wpsim E1 r g Q ps pt itr_src itr_tgt))
      ⊢
      (wpsim E0 r g Q ps pt itr_src itr_tgt)
  .
  Proof.
    Local Transparent FUpd.
    intros LE. iIntros "H" (? ? ? ? ?) "[[% [% (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8)]] (WAUTH & WSAT & E)]".
    iAssert (=|x|={E0,E1}=> (wpsim E1 r g Q ps pt itr_src itr_tgt)) with "[H]" as "H".
    { inv LE. iFrame. iApply FUpd_mono. 2: iFrame. lia. }
    iAssert (wsats x ∗ OwnE E0)%I with "[WSAT E]" as "C".
    { iFrame. }
    rewrite /fupd /bi_fupd_fupd /= /FUpd.
    iMod ("H" with "[C]") as "(_ & WSAT & E & H)". iFrame.
    iApply "H". iFrame. iExists _. iFrame. auto.
    Local Opaque FUpd.
  Qed.

  Lemma wpsim_FUpd_weaken y r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt itr_src itr_tgt
        E0 E1
        (SUB: E0 ⊆ E1)
    :
    (y <= x) ->
    (=|y|=(fairI (ident_tgt:=ident_tgt) x)={E0}=> (wpsim E1 r g Q ps pt itr_src itr_tgt))
      ⊢
      (wpsim E1 r g Q ps pt itr_src itr_tgt)
  .
  Proof.
    iIntros (LE) "H". iApply wpsim_FUpd. eauto. iApply fupd_mask_mono; eauto.
  Qed.

  Global Instance wpsim_elim_FUpd_gen
         E0 E1 E2 y
         r g R_src R_tgt
         (Q: R_src -> R_tgt -> iProp)
         ps pt itr_src itr_tgt p
         P
    :
    ElimModal (y <= x /\ E0 ⊆ E2) p false
              (=|y|=(fairI (ident_tgt:=ident_tgt) x)={E0,E1}=> P)
              P
              (wpsim E2 r g Q ps pt itr_src itr_tgt)
              (wpsim (E1 ∪ (E2 ∖ E0)) r g Q ps pt itr_src itr_tgt).
  Proof.
    unfold ElimModal. rewrite bi.intuitionistically_if_elim.
    intros (LE & SUB). iIntros "[H0 H1]".
    iApply wpsim_FUpd. apply LE.
    iMod "H0". iPoseProof ("H1" with "H0") as "H".
    iModIntro. iFrame.
  Qed.

  Global Instance wpsim_elim_FUpd_eq
         E1 E2 y
         r g R_src R_tgt
         (Q: R_src -> R_tgt -> iProp)
         ps pt itr_src itr_tgt p
         P
    :
    ElimModal (y <= x /\ E1 ⊆ E2) p false
              (=|y|=(fairI (ident_tgt:=ident_tgt) x)={E1}=> P)
              P
              (wpsim E2 r g Q ps pt itr_src itr_tgt)
              (wpsim E2 r g Q ps pt itr_src itr_tgt).
  Proof.
    unfold ElimModal. rewrite bi.intuitionistically_if_elim.
    intros (LE & SUB). iIntros "[H0 H1]".
    iApply wpsim_FUpd_weaken. apply SUB. apply LE.
    iMod "H0". iModIntro. iApply ("H1" with "H0").
  Qed.

  Global Instance wpsim_elim_FUpd
         E0 E1 y
         r g R_src R_tgt
         (Q: R_src -> R_tgt -> iProp)
         ps pt itr_src itr_tgt p
         P
    :
    ElimModal (y <= x) p false
              (=|y|=(fairI (ident_tgt:=ident_tgt) x)={E0,E1}=> P)
              P
              (wpsim E0 r g Q ps pt itr_src itr_tgt)
              (wpsim E1 r g Q ps pt itr_src itr_tgt).
  Proof.
    unfold ElimModal. rewrite bi.intuitionistically_if_elim.
    intros LE. iIntros "[H0 H1]".
    iApply wpsim_FUpd. apply LE. iMod "H0".
    iModIntro. iApply ("H1" with "H0").
  Qed.

  Global Instance wpsim_elim_FUpd_simple
         E0 E1 y
         r g R_src R_tgt
         (Q: R_src -> R_tgt -> iProp)
         ps pt itr_src itr_tgt p
         P
    :
    ElimModal (y <= x) p false
              (=|y|={E0,E1}=> P)
              P
              (wpsim E0 r g Q ps pt itr_src itr_tgt)
              (wpsim E1 r g Q ps pt itr_src itr_tgt).
  Proof.
    unfold ElimModal. rewrite bi.intuitionistically_if_elim.
    intros LE. iIntros "[H0 H1]".
    iApply wpsim_FUpd_simple. apply LE. iMod "H0".
    iModIntro. iApply ("H1" with "H0").
  Qed.

  Global Instance wpsim_add_modal_FUpd
         E y (LE: y <= x)
         r g R_src R_tgt
         (Q: R_src -> R_tgt -> iProp)
         ps pt itr_src itr_tgt
         P
    :
    AddModal (=|y|=(fairI (ident_tgt:=ident_tgt) x)={E}=> P)
             P
             (wpsim E r g Q ps pt itr_src itr_tgt).
  Proof.
    unfold AddModal. iIntros "[> H0 H1]". iApply ("H1" with "H0").
  Qed.

  Global Instance wpsim_elim_iupd_edge
         E r g R_src R_tgt
         (Q: R_src -> R_tgt -> iProp)
         ps pt itr_src itr_tgt p
         P
    :
    ElimModal True p false
              (#=(ObligationRA.edges_sat)=> P)
              P
              (wpsim E r g Q ps pt itr_src itr_tgt)
              (wpsim E r g Q ps pt itr_src itr_tgt).
  Proof.
    unfold ElimModal. rewrite bi.intuitionistically_if_elim.
    intros _. iIntros "[H0 H1]" (? ? ? ? ?) "[[% [% D]] W]".
    iPoseProof (IUpd_sub_mon with "[] H0 D") as "> [D P]".
    { iApply edges_sat_sub. }
    iApply ("H1" with "P"). iFrame. iExists _. eauto.
  Qed.

  Global Instance wpsim_elim_iupd_arrow
         E y
         r g R_src R_tgt
         (Q: R_src -> R_tgt -> iProp)
         ps pt itr_src itr_tgt p
         P
    :
    ElimModal (y < x) p false
              (#=(ObligationRA.arrows_sat (S:=sum_tid ident_tgt) y)=> P)
              P
              (wpsim E r g Q ps pt itr_src itr_tgt)
              (wpsim E r g Q ps pt itr_src itr_tgt).
  Proof.
    unfold ElimModal. rewrite bi.intuitionistically_if_elim.
    intros LE. iIntros "[H0 H1]" (? ? ? ? ?) "[[% [% D]] W]".
    iPoseProof (IUpd_sub_mon with "[] H0 D") as "> [D P]".
    { iApply arrows_sat_sub. apply LE. }
    iApply ("H1" with "P"). iFrame. iExists _. eauto.
  Qed.

  Global Instance fupd_elim_iupd_edge
         a b P Q E1 E2 p
    :
    ElimModal True p false
              (#=(ObligationRA.edges_sat)=> P)
              P
              (=|a|=(fairI (ident_tgt:=ident_tgt) b)={E1,E2}=> Q)
              (=|a|=(fairI (ident_tgt:=ident_tgt) b)={E1,E2}=> Q).
  Proof.
    unfold ElimModal. rewrite bi.intuitionistically_if_elim.
    intros _. iIntros "[H0 H1]".
    iPoseProof (IUpd_sub_mon with "[] H0") as "H0".
    { iApply SubIProp_sep_l. }
    iMod "H0". iApply ("H1" with "H0").
  Qed.

  Global Instance fupd_elim_iupd_arrow
         a b c P Q E1 E2 p
    :
    ElimModal (a < b) p false
              (#=(ObligationRA.arrows_sat (S:=sum_tid ident_tgt) a)=> P)
              P
              (=|c|=(fairI (ident_tgt:=ident_tgt) b)={E1,E2}=> Q)
              (=|c|=(fairI (ident_tgt:=ident_tgt) b)={E1,E2}=> Q).
  Proof.
    unfold ElimModal. rewrite bi.intuitionistically_if_elim.
    intros LT. iIntros "[H0 H1]".
    Local Transparent ObligationRA.edges_sat ObligationRA.arrows_sats.
    Local Typeclasses Transparent ObligationRA.edges_sat ObligationRA.arrows_sats.
    iPoseProof (IUpd_sub_mon with "[] H0") as "H0".
    { iApply SubIProp_trans. iApply Regions.nsats_sat_sub. apply LT. iApply SubIProp_sep_r. }
    assert (Regions.nsats (ObligationRA.arrow (S:=sum_tid ident_tgt)) b = (ObligationRA.arrows_sats b)) as ->; [done|].
    iMod "H0". iApply ("H1" with "H0").
    Local Typeclasses Opaque ObligationRA.edges_sat ObligationRA.arrows_sats.
    Local Opaque ObligationRA.edges_sat ObligationRA.arrows_sats.
  Qed.

  Lemma wpsim_wand E r g R_src R_tgt
        (Q0 Q1: R_src -> R_tgt -> iProp)
        ps pt itr_src itr_tgt
    :
    (wpsim E r g Q0 ps pt itr_src itr_tgt)
      -∗
      (∀ r_src r_tgt,
          ((Q0 r_src r_tgt) -∗ #=> (Q1 r_src r_tgt)))
      -∗
      (wpsim E r g Q1 ps pt itr_src itr_tgt)
  .
  Proof.
    unfold wpsim. iIntros "H0 H1" (? ? ? ? ?) "D".
    iApply isim_wand.
    iPoseProof ("H0" $! _ _ _ _ _ with "D") as "H0".
    iSplitR "H0"; [|auto]. iIntros (? ? ? ? ? ? ?) "[D H0]".
    iPoseProof ("H1" $! _ _ with "H0") as "> H0". iModIntro. iFrame.
  Qed.

  Lemma wpsim_mono E r g R_src R_tgt
        (Q0 Q1: R_src -> R_tgt -> iProp)
        (MONO: forall r_src r_tgt,
            (Q0 r_src r_tgt)
              -∗
              (#=> (Q1 r_src r_tgt)))
        ps pt itr_src itr_tgt
    :
    (wpsim E r g Q0 ps pt itr_src itr_tgt)
      -∗
      (wpsim E r g Q1 ps pt itr_src itr_tgt)
  .
  Proof.
    iIntros "H". iApply (wpsim_wand with "H").
    iIntros. iApply MONO. auto.
  Qed.

  Lemma wpsim_frame E r g R_src R_tgt
        P (Q: R_src -> R_tgt -> iProp)
        ps pt itr_src itr_tgt
    :
    (wpsim E r g Q ps pt itr_src itr_tgt)
      -∗
      P
      -∗
      (wpsim E r g (fun r_src r_tgt => P ∗ Q r_src r_tgt) ps pt itr_src itr_tgt)
  .
  Proof.
    iIntros "H0 H1". iApply (wpsim_wand with "H0").
    iIntros. iModIntro. iFrame.
  Qed.

  Lemma wpsim_bind_top E r g R_src R_tgt S_src S_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt (itr_src: itree srcE S_src) (itr_tgt: itree tgtE S_tgt)
        ktr_src ktr_tgt
    :
    (wpsim E r g (fun s_src s_tgt => wpsim ⊤ r g Q false false (ktr_src s_src) (ktr_tgt s_tgt)) ps pt itr_src itr_tgt)
      -∗
      (wpsim E r g Q ps pt (itr_src >>= ktr_src) (itr_tgt >>= ktr_tgt))
  .
  Proof.
    unfold wpsim. iIntros "H" (? ? ? ? ?) "D".
    iPoseProof ("H" $! _ _ _ _ _ with "D") as "H".
    iApply isim_bind. iApply (isim_mono with "H").
    iIntros (? ? ? ? ? ? ?) "[[D I] H]".
    iApply ("H" $! _ _ _ _ _ with "[D I]"). iFrame.
  Qed.

  (* Simulation rules. *)

  Lemma wpsim_ret
        E y (LE : y <= x)
        r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt r_src r_tgt
    :
    (=|y|=(fairI (ident_tgt:=ident_tgt) x)={E,⊤}=> (Q r_src r_tgt))
      -∗
      (wpsim E r g Q ps pt (Ret r_src) (Ret r_tgt))
  .
  Proof.
    iIntros "> H".
    unfold wpsim. iIntros (? ? ? ? ?) "D".
    iApply isim_ret. iFrame.
  Qed.

  Lemma wpsim_tauL E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt itr_src itr_tgt
    :
    (wpsim E r g Q true pt itr_src itr_tgt)
      -∗
      (wpsim E r g Q ps pt (Tau itr_src) itr_tgt)
  .
  Proof.
    unfold wpsim. iIntros "H" (? ? ? ? ?) "D".
    iPoseProof ("H" $! _ _ _ _ _ with "D") as "H".
    iApply isim_tauL. iFrame.
  Qed.

  Lemma wpsim_tauR E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt itr_src itr_tgt
    :
    (wpsim E r g Q ps true itr_src itr_tgt)
      -∗
      (wpsim E r g Q ps pt itr_src (Tau itr_tgt))
  .
  Proof.
    unfold wpsim. iIntros "H" (? ? ? ? ?) "D".
    iPoseProof ("H" $! _ _ _ _ _ with "D") as "H".
    iApply isim_tauR. iFrame.
  Qed.

  Lemma wpsim_chooseL E X r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src itr_tgt
    :
    (∃ x, wpsim E r g Q true pt (ktr_src x) itr_tgt)
      -∗
      (wpsim E r g Q ps pt (trigger (Choose X) >>= ktr_src) itr_tgt)
  .
  Proof.
    unfold wpsim. iIntros "[% H]" (? ? ? ? ?) "D".
    iPoseProof ("H" $! _ _ _ _ _ with "D") as "H".
    iApply isim_chooseL. iExists _. iFrame.
  Qed.

  Lemma wpsim_chooseR E X r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt itr_src ktr_tgt
    :
    (∀ x, wpsim E r g Q ps true itr_src (ktr_tgt x))
      -∗
      (wpsim E r g Q ps pt itr_src (trigger (Choose X) >>= ktr_tgt))
  .
  Proof.
    unfold wpsim. iIntros "H" (? ? ? ? ?) "D".
    iApply isim_chooseR. iIntros (?).
    iPoseProof ("H" $! _ _ _ _ _ _ with "D") as "H". iFrame.
  Qed.

  Lemma wpsim_stateL E X run r g R_src R_tgt
        (Q : R_src -> R_tgt -> iProp)
        ps pt ktr_src itr_tgt st_src
    :
    (St_src st_src)
      -∗ (St_src (fst (run st_src))
                 -∗ wpsim E r g Q true pt (ktr_src (snd (run st_src) : X)) itr_tgt)
      -∗ wpsim E r g Q ps pt (trigger (State run) >>= ktr_src) itr_tgt.
  Proof.
    unfold wpsim. iIntros "H0 H1" (? ? ? ? ?) "(D & W)". iApply isim_stateL.
    iAssert (⌜st_src0 = st_src⌝)%I as "%".
    { iApply (default_I_past_get_st_src with "D H0"); eauto. }
    subst.
    iPoseProof (default_I_past_update_st_src with "D H0") as "> [H0 D]".
    iApply ("H1" with "H0 [D W]"). iFrame.
  Qed.

  Lemma wpsim_lens_stateL E V (l : Lens.t _ V) X run r g R_src R_tgt
        (Q : R_src -> R_tgt -> iProp)
        ps pt ktr_src itr_tgt st v
    :
    (Vw_src st l v)
      -∗ (Vw_src st l (fst (run v))
                 -∗ wpsim E r g Q true pt (ktr_src (snd (run v) : X)) itr_tgt)
      -∗ wpsim E r g Q ps pt (trigger (map_lens l (State run)) >>= ktr_src) itr_tgt.
  Proof.
    iIntros "S H". rewrite map_lens_State. iApply (wpsim_stateL with "S").
    iIntros "S". ss. unfold Vw_src.
    rewrite Lens.view_set. rewrite Lens.set_set.
    iApply ("H" with "S").
  Qed.

  Lemma wpsim_stateR E X run r g R_src R_tgt
        (Q : R_src -> R_tgt -> iProp)
        ps pt itr_src ktr_tgt st_tgt
    :
    (St_tgt st_tgt)
      -∗ (St_tgt (fst (run st_tgt))
                 -∗ wpsim E r g Q ps true itr_src (ktr_tgt (snd (run st_tgt) : X)))
      -∗ wpsim E r g Q ps pt itr_src (trigger (State run) >>= ktr_tgt).
  Proof.
    unfold wpsim. iIntros "H0 H1" (? ? ? ? ?) "(D & W)". iApply isim_stateR.
    iAssert (⌜st_tgt0 = st_tgt⌝)%I as "%".
    { iApply (default_I_past_get_st_tgt with "D H0"); eauto. }
    subst.
    iPoseProof (default_I_past_update_st_tgt with "D H0") as "> [H0 D]".
    iApply ("H1" with "H0 [D W]"). iFrame.
  Qed.

  Lemma wpsim_lens_stateR E V (l : Lens.t _ V) X run r g R_src R_tgt
        (Q : R_src -> R_tgt -> iProp)
        ps pt itr_src ktr_tgt st v
    :
    (Vw_tgt st l v)
      -∗ (Vw_tgt st l (fst (run v))
                 -∗ wpsim E r g Q ps true itr_src (ktr_tgt (snd (run v) : X)))
      -∗ wpsim E r g Q ps pt itr_src (trigger (map_lens l (State run)) >>= ktr_tgt).
  Proof.
    iIntros "S H". rewrite map_lens_State. iApply (wpsim_stateR with "S").
    iIntros "S". ss. unfold Vw_tgt.
    rewrite Lens.view_set. rewrite Lens.set_set.
    iApply ("H" with "S").
  Qed.

  Lemma wpsim_lens_getL V (l : Lens.t _ V) X (p : V -> X) E st v r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src itr_tgt
    :
    ((Vw_src st l v) ∧ (wpsim E r g Q true pt (ktr_src (p v)) itr_tgt))
      -∗
      (wpsim E r g Q ps pt (trigger (map_lens l (Get p)) >>= ktr_src) itr_tgt)
  .
  Proof.
    unfold wpsim. iIntros "H" (? ? ? ? ?) "[D C]".
    rewrite map_lens_Get. rewrite Get_State. iApply isim_stateL. ss.
    iAssert (⌜Lens.view l st_src = v⌝)%I as "%".
    { iDestruct "H" as "[H1 _]".
      iPoseProof (default_I_past_get_st_src with "D H1") as "%H". subst.
      rewrite Lens.view_set. auto.
    }
    rewrite H. iDestruct "H" as "[_ H]". iApply ("H" with "[D C]"). iFrame.
  Qed.

  Lemma wpsim_getL X (p : state_src -> X) E st r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src itr_tgt
    :
    ((St_src st) ∧ (wpsim E r g Q true pt (ktr_src (p st)) itr_tgt))
      -∗
      (wpsim E r g Q ps pt (trigger (Get p) >>= ktr_src) itr_tgt)
  .
  Proof.
    iIntros "H". replace (Get p) with (map_lens Lens.id (Get p)) by ss.
    iApply wpsim_lens_getL. iSplit.
    - iDestruct "H" as "[H _]". iApply "H".
    - iDestruct "H" as "[_ H]". ss.
      Unshelve. all: eauto.
  Qed.

  Lemma wpsim_lens_getR V (l : Lens.t _ V) X (p : V -> X) E st v r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt itr_src ktr_tgt
    :
    ((Vw_tgt st l v) ∧ (wpsim E r g Q ps true itr_src (ktr_tgt (p v))))
      -∗
      (wpsim E r g Q ps pt itr_src (trigger (map_lens l (Get p)) >>= ktr_tgt))
  .
  Proof.
    unfold wpsim. iIntros "H" (? ? ? ? ?) "[D C]".
    rewrite map_lens_Get. rewrite Get_State. iApply isim_stateR. ss.
    iAssert (⌜Lens.view l st_tgt = v⌝)%I as "%".
    { iDestruct "H" as "[H1 _]". subst.
      iPoseProof (default_I_past_get_st_tgt with "D H1") as "%H". subst.
      rewrite Lens.view_set. auto.
    }
    rewrite H. iDestruct "H" as "[_ H]". iApply ("H" with "[D C]"). iFrame.
  Qed.

  Lemma wpsim_getR X (p : state_tgt -> X) E st r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt itr_src ktr_tgt
    :
    ((St_tgt st) ∧ (wpsim E r g Q ps true itr_src (ktr_tgt (p st))))
      -∗
      (wpsim E r g Q ps pt itr_src (trigger (Get p) >>= ktr_tgt))
  .
  Proof.
    iIntros "H". replace (Get p) with (map_lens Lens.id (Get p)) by ss.
    iApply wpsim_lens_getR. iSplit.
    - iDestruct "H" as "[H _]". iApply "H".
    - iDestruct "H" as "[_ H]". ss.
      Unshelve. all: eauto.
  Qed.

  Lemma wpsim_modifyL E f r g R_src R_tgt
        (Q : R_src -> R_tgt -> iProp)
        ps pt ktr_src itr_tgt st_src
    :
    (St_src st_src)
      -∗ (St_src (f st_src) -∗ wpsim E r g Q true pt (ktr_src tt) itr_tgt)
      -∗ wpsim E r g Q ps pt (trigger (Modify f) >>= ktr_src) itr_tgt.
  Proof.
    rewrite Modify_State. iIntros "H1 H2". iApply (wpsim_stateL with "H1"). simpl. iFrame.
  Qed.

  Lemma wpsim_lens_modifyL E V (l : Lens.t _ V) f r g R_src R_tgt
        (Q : R_src -> R_tgt -> iProp)
        ps pt ktr_src itr_tgt st v
    :
    (Vw_src st l v)
      -∗ (Vw_src st l (f v) -∗ wpsim E r g Q true pt (ktr_src tt) itr_tgt)
      -∗ wpsim E r g Q ps pt (trigger (map_lens l (Modify f)) >>= ktr_src) itr_tgt.
  Proof.
    rewrite map_lens_Modify.
    iIntros "H1 H2". iApply (wpsim_modifyL with "H1").
    iIntros "H". iApply "H2".
    unfold Lens.modify. rewrite Lens.view_set. rewrite Lens.set_set. iApply "H".
  Qed.

  Lemma wpsim_modifyR E f r g R_src R_tgt
        (Q : R_src -> R_tgt -> iProp)
        ps pt itr_src ktr_tgt st_tgt
    :
    (St_tgt st_tgt)
      -∗ (St_tgt (f st_tgt) -∗ wpsim E r g Q ps true itr_src (ktr_tgt tt))
      -∗ wpsim E r g Q ps pt itr_src (trigger (Modify f) >>= ktr_tgt).
  Proof.
    rewrite Modify_State. iIntros "H1 H2". iApply (wpsim_stateR with "H1"). simpl. iFrame.
  Qed.

  Lemma wpsim_lens_modifyR E V (l : Lens.t _ V) f r g R_src R_tgt
        (Q : R_src -> R_tgt -> iProp)
        ps pt itr_src ktr_tgt st v
    :
    (Vw_tgt st l v)
      -∗ (Vw_tgt st l (f v) -∗ wpsim E r g Q ps true itr_src (ktr_tgt tt))
      -∗ wpsim E r g Q ps pt itr_src (trigger (map_lens l (Modify f)) >>= ktr_tgt).
  Proof.
    rewrite map_lens_Modify.
    iIntros "H1 H2". iApply (wpsim_modifyR with "H1").
    iIntros "H". iApply "H2".
    unfold Lens.modify. rewrite Lens.view_set. rewrite Lens.set_set. iApply "H".
  Qed.

  Lemma wpsim_tidL E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src itr_tgt
    :
    (wpsim E r g Q true pt (ktr_src tid) itr_tgt)
      -∗
      (wpsim E r g Q ps pt (trigger GetTid >>= ktr_src) itr_tgt)
  .
  Proof.
    unfold wpsim. iIntros "H" (? ? ? ? ?) "D".
    iApply isim_tidL. iApply ("H" with "D").
  Qed.

  Lemma wpsim_tidR E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt itr_src ktr_tgt
    :
    (wpsim E r g Q ps true itr_src (ktr_tgt tid))
      -∗
      (wpsim E r g Q ps pt itr_src (trigger GetTid >>= ktr_tgt))
  .
  Proof.
    unfold wpsim. iIntros "H" (? ? ? ? ?) "D".
    iApply isim_tidR. iApply ("H" with "D").
  Qed.

  Lemma wpsim_fairL_prism o
        A lf ls
        (p : Prism.t _ A)
        E fm r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src itr_tgt
        (FAIL: forall i (IN: fm i = Flag.fail), List.In i lf)
        (SUCCESS: forall i (IN: List.In i ls), fm i = Flag.success)
    :
    (list_prop_sum (fun i => FairRA.white p i Ord.one) lf)
      -∗
      ((list_prop_sum (fun i => FairRA.white p i o) ls)
         -∗ (wpsim E r g Q true pt (ktr_src tt) itr_tgt))
      -∗
      (wpsim E r g Q ps pt (trigger (Fair (prism_fmap p fm)) >>= ktr_src) itr_tgt).
  Proof.
    unfold wpsim. iIntros "OWN H" (? ? ? ? ?) "(D & W)".
    iPoseProof (default_I_past_update_ident_source_prism with "D OWN") as ">[% [% [WHITES D]]]".
    { eauto. }
    { eauto. }
    iPoseProof ("H" with "WHITES [D W]") as "H".
    { iFrame "D W". }
    iApply isim_fairL. iExists _. iSplit; eauto.
  Qed.

  Lemma wpsim_fairL o lf ls
        E fm r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src itr_tgt
        (FAIL: forall i (IN: fm i = Flag.fail), List.In i lf)
        (SUCCESS: forall i (IN: List.In i ls), fm i = Flag.success)
    :
    (list_prop_sum (fun i => FairRA.white Prism.id i Ord.one) lf)
      -∗
      ((list_prop_sum (fun i => FairRA.white Prism.id i o) ls)
         -∗ (wpsim E r g Q true pt (ktr_src tt) itr_tgt))
      -∗
      (wpsim E r g Q ps pt (trigger (Fair fm) >>= ktr_src) itr_tgt).
  Proof.
    iIntros "WHITES K". rewrite <- (prism_fmap_id fm).
    iApply (wpsim_fairL_prism with "WHITES K"); eauto.
  Qed.

  Lemma wpsim_fairR_prism_step
        y (LT : y < x)
        A lf ls
        (p : Prism.t _ A)
        E fm r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt itr_src ktr_tgt
        (SUCCESS: forall i (IN: fm i = Flag.success), List.In i (List.map fst ls))
        (FAIL: forall i (IN: List.In i lf), fm i = Flag.fail)
        (NODUP: List.NoDup lf)
    :
    (list_prop_sum
       (fun '(i, l) =>
          ObligationRA.duty y (Prism.compose inrp p) i l ∗ ObligationRA.taxes (List.map fst l) Ord.omega)
       ls)%I
      -∗
      ((list_prop_sum (fun '(i, l) => ObligationRA.duty y (Prism.compose inrp p) i l) ls)
         -∗
         (list_prop_sum (fun i => FairRA.white (Prism.compose inrp p) i 1) lf)
         -∗
         wpsim E r g Q ps true itr_src (ktr_tgt tt))
      -∗
      (wpsim E r g Q ps pt itr_src (trigger (Fair (prism_fmap p fm)) >>= ktr_tgt))
  .
  Proof.
    unfold wpsim. iIntros "OWN H"  (? ? ? ? ?) "(D & W)".
    iApply isim_fairR. iIntros (?) "%".
    iPoseProof (default_I_past_update_ident_target with "D OWN") as "> [DUTY [WHITE D]]".
    { rewrite prism_fmap_compose. eauto. }
    { eauto. }
    { eauto. }
    { eauto. }
    { eauto. }
    iApply ("H" with "DUTY WHITE"). iFrame.
  Qed.

  Lemma wpsim_fairR_prism
        y (LT : y < x)
        A lf
        (ls : list (A * list (nat * nat * Vars y)))
        (p : Prism.t _ A)
        E fm r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt itr_src ktr_tgt
        (SUCCESS: forall i (IN: fm i = Flag.success), List.In i (List.map fst ls))
        (FAIL: forall i (IN: List.In i lf), fm i = Flag.fail)
        (NODUP: List.NoDup lf)
    :
    (list_prop_sum (fun '(i, l) => Duty((inrp ⋅ p)%prism ◬ i) l ∗ ◇{List.map fst l}(1, 1)) ls)
      -∗
      ((list_prop_sum (fun '(i, l) => Duty((inrp ⋅ p)%prism ◬ i) l) ls)
         -∗
         (list_prop_sum (fun i => €((Prism.compose inrp p) ◬ i)) lf)
         -∗
         wpsim E r g Q ps true itr_src (ktr_tgt tt))
      -∗
      (wpsim E r g Q ps pt itr_src (trigger (Fair (prism_fmap p fm)) >>= ktr_tgt))
  .
  Proof.
    iIntros "DUTY K".
    iAssert
      (#=>list_prop_sum (λ '(i, l), (ObligationRA.duty y (inrp ⋅ p)%prism i l ∗ ObligationRA.taxes (List.map fst l) Ord.omega)%I)
          (List.map (λ '(i, l), (i, List.map (λ '(a, b, f), (a, layer b 1, f)) l)) ls))
      with "[DUTY]" as "DUTY".
    { iApply list_prop_sum_pull_bupd_default. iApply list_prop_sum_map. 2: iFrame.
      iIntros ([? ?]) "[D T]". iFrame.
      unfold progress_credits.
      replace (List.map (λ '(k, n), (k, layer n 1)) (List.map fst l))
        with
        (List.map fst (List.map (λ '(a, b, f), (a, layer b 1, f)) l)).
      2:{ rewrite ! List.map_map. f_equal. extensionalities. des_ifs. }
      iMod (ObligationRA.taxes_ord_mon with "T") as "T".
      2:{ iModIntro. iFrame. }
      { rewrite layer_one_one. reflexivity. }
    }
    iMod "DUTY".
    iApply (wpsim_fairR_prism_step with "[DUTY]"). 1,2,3,4,5: eauto.
    2:{ iIntros "A B".
        iAssert (#=> list_prop_sum (λ '(i, l), duty (inrp ⋅ p)%prism i l) ls)
          with "[A]" as "A".
        { iApply list_prop_sum_pull_bupd_default.
          iPoseProof (list_prop_sum_map_inv with "A") as "A". 2: iFrame.
          iIntros ([? ?]) "D". iModIntro. iFrame.
        }
        iMod "A". iApply ("K" with "[A]"); iFrame.
    }
    { i. specialize (SUCCESS i IN). rewrite in_map_iff in SUCCESS. des. destruct x0. ss.
      subst. rewrite List.map_map. rewrite in_map_iff. esplits. 2: eauto. des_ifs.
    }
  Qed.

  Lemma wpsim_fairR_step
        y (LT : y < x)
        lf ls
        E fm r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt itr_src ktr_tgt
        (SUCCESS: forall i (IN: fm i = Flag.success), List.In i (List.map fst ls))
        (FAIL: forall i (IN: List.In i lf), fm i = Flag.fail)
        (NODUP: List.NoDup lf)
    :
    (list_prop_sum
       (fun '(i, l) => ObligationRA.duty y inrp i l ∗ ObligationRA.taxes (List.map fst l) Ord.omega) ls)
      -∗
      ((list_prop_sum (fun '(i, l) => ObligationRA.duty y inrp i l) ls)
         -∗
         (list_prop_sum (fun i => FairRA.white inrp i 1) lf)
         -∗
         wpsim E r g Q ps true itr_src (ktr_tgt tt))
      -∗
      (wpsim E r g Q ps pt itr_src (trigger (Fair fm) >>= ktr_tgt))
  .
  Proof.
    iIntros "DUTY K". rewrite <- (prism_fmap_id fm).
    iApply (wpsim_fairR_prism_step with "[DUTY] [K]").
    5:{ iFrame "DUTY". }
    5:{ iFrame "K". }
    all: eauto.
  Qed.

  Lemma wpsim_fairR
        y (LT : y < x)
        lf
        (ls : list (ident_tgt * list (nat * nat * Vars y)))
        E fm r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt itr_src ktr_tgt
        (SUCCESS: forall i (IN: fm i = Flag.success), List.In i (List.map fst ls))
        (FAIL: forall i (IN: List.In i lf), fm i = Flag.fail)
        (NODUP: List.NoDup lf)
    :
    (list_prop_sum (fun '(i, l) => Duty(inrp ◬ i) l ∗ ◇{List.map fst l}(1, 1)) ls)
      -∗
      ((list_prop_sum (fun '(i, l) => Duty(inrp ◬ i) l) ls)
         -∗
         (list_prop_sum (fun i => €(inrp ◬ i)) lf)
         -∗
         wpsim E r g Q ps true itr_src (ktr_tgt tt))
      -∗
      (wpsim E r g Q ps pt itr_src (trigger (Fair fm) >>= ktr_tgt))
  .
  Proof.
    iIntros "DUTY K".
    iAssert
      (#=>list_prop_sum (λ '(i, l), (ObligationRA.duty y inrp i l ∗ ObligationRA.taxes (List.map fst l) Ord.omega)%I)
          (List.map (λ '(i, l), (i, List.map (λ '(a, b, f), (a, layer b 1, f)) l)) ls))
      with "[DUTY]" as "DUTY".
    { iApply list_prop_sum_pull_bupd_default. iApply list_prop_sum_map. 2: iFrame.
      iIntros ([? ?]) "[D T]". iFrame.
      unfold progress_credits.
      replace (List.map (λ '(k, n), (k, layer n 1)) (List.map fst l))
        with
        (List.map fst (List.map (λ '(a, b, f), (a, layer b 1, f)) l)).
      2:{ rewrite ! List.map_map. f_equal. extensionalities. des_ifs. }
      iMod (ObligationRA.taxes_ord_mon with "T") as "T".
      2:{ iModIntro. iFrame. }
      { rewrite layer_one_one. reflexivity. }
    }
    iMod "DUTY".
    iApply (wpsim_fairR_step with "[DUTY]"). 1,2,3,4,5: eauto.
    2:{ iIntros "A B".
        iAssert (#=> list_prop_sum (λ '(i, l), duty inrp i l) ls)
          with "[A]" as "A".
        { iApply list_prop_sum_pull_bupd_default.
          iPoseProof (list_prop_sum_map_inv with "A") as "A". 2: iFrame.
          iIntros ([? ?]) "D". iModIntro. iFrame.
        }
        iMod "A". iApply ("K" with "[A]"); iFrame.
    }
    { i. specialize (SUCCESS i IN). rewrite in_map_iff in SUCCESS. des. destruct x0. ss.
      subst. rewrite List.map_map. rewrite in_map_iff. esplits. 2: eauto. des_ifs.
    }
  Qed.

  Lemma wpsim_fairR_simple
        y (LT : y < x)
        lf ls
        E fm r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt itr_src ktr_tgt
        (SUCCESS: forall i (IN: fm i = Flag.success), List.In i ls)
        (FAIL: forall i (IN: List.In i lf), fm i = Flag.fail)
        (NODUP: List.NoDup lf)
    :
    (list_prop_sum (fun i => FairRA.black_ex inrp i 1) ls)
      -∗
      ((list_prop_sum (fun i => FairRA.black_ex inrp i 1) ls)
         -∗
         (list_prop_sum (fun i => FairRA.white inrp i 1) lf)
         -∗
         wpsim E r g Q ps true itr_src (ktr_tgt tt))
      -∗
      (wpsim E r g Q ps pt itr_src (trigger (Fair fm) >>= ktr_tgt))
  .
  Proof.
    iIntros "A B". iApply (wpsim_fairR with "[A]").
    1,3,4:eauto.
    { instantiate (1:= List.map (fun i => (i, [])) ls).
      i. specialize (SUCCESS _ IN). rewrite List.map_map. ss.
      replace (List.map (λ x : ident_tgt, x) ls) with ls; auto.
      clear. induction ls; ss; eauto. f_equal. auto.
    }
    { iApply list_prop_sum_map. 2: iFrame.
      i. ss. iIntros "BLK". iSplitL; auto. iApply ObligationRA.black_to_duty. auto.
    }
    { iIntros "S F". iApply ("B" with "[S]"). 2: iFrame.
      iApply list_prop_sum_map_inv. 2: iFrame.
      i; ss. iIntros "D". iApply ObligationRA.duty_to_black. iFrame.
    }
  Qed.

  Lemma wpsim_UB E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src itr_tgt
    :
    ⊢ (wpsim E r g Q ps pt (trigger Undefined >>= ktr_src) itr_tgt)
  .
  Proof.
    unfold wpsim. iIntros (? ? ? ? ?) "D". iApply isim_UB. auto.
  Qed.

  Lemma wpsim_observe E fn args r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src ktr_tgt
    :
    (∀ ret, wpsim E g g Q true true (ktr_src ret) (ktr_tgt ret))
      -∗
      (wpsim E r g Q ps pt (trigger (Observe fn args) >>= ktr_src) (trigger (Observe fn args) >>= ktr_tgt))
  .
  Proof.
    unfold wpsim. iIntros "H" (? ? ? ? ?) "D".
    iApply isim_observe. iIntros (?). iApply ("H" with "D").
  Qed.

  Lemma wpsim_yieldL E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src ktr_tgt
    :
    (wpsim E r g Q true pt (ktr_src tt) (trigger (Yield) >>= ktr_tgt))
      -∗
      (wpsim E r g Q ps pt (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt))
  .
  Proof.
    unfold wpsim. iIntros "H" (? ? ? ? ?) "D".
    iApply isim_yieldL. iApply ("H" with "D").
  Qed.

  Lemma wpsim_yieldR_strong_pending
        y (LT: y < x)
        E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src ktr_tgt l
        l1 l2 pps
        (OBLIGS : l = l1 ++ l2)
        (PENDS : Forall2 (fun '(k1, _, _) '(k2, _) => k1 = k2) l1 pps)
    :
    (ObligationRA.duty y inlp tid l ∗ ObligationRA.pends pps ∗ ObligationRA.taxes (List.map fst l2) Ord.omega)
      -∗
      ((ObligationRA.duty y inlp tid l)
         -∗
         (FairRA.white_thread (S:=_))
         -∗
         (ObligationRA.pends pps)
         -∗
         (=|x|=(fairI (ident_tgt:=ident_tgt) x)={E,⊤}=> (wpsim ⊤ r g Q ps true (trigger (Yield) >>= ktr_src) (ktr_tgt tt))))
      -∗
      (wpsim E r g Q ps pt (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt))
  .
  Proof.
    iIntros "H K". unfold wpsim. iIntros (? ? ? ? ?) "(D & [WA WS])".
    iMod (default_I_past_update_ident_thread_pending with "D H") as "[B [W ([D0 [D1 [D2 [D3 [D4 [D5 [D6 D7]]]]]]] & PPS)]]".
    1,2,3: eauto.
    iAssert ((fairI (ident_tgt:=ident_tgt) x) ∗ (wsats x ∗ OwnE E))%I with "[WS D5 D6]" as "C".
    { iFrame. }
    Local Transparent FUpd.
    iPoseProof ("K" with "B W PPS C") as ">[D5 [D6 [E K]]]".
    iApply isim_yieldR. unfold I, fairI. iFrame. iFrame.
    iIntros (? ? ? ? ? ?) "(D & WAS) %".
    iApply ("K" with "[D WAS]"). iFrame. iExists _. eauto.
    Local Opaque FUpd.
  Qed.

  Lemma wpsim_yieldR_strong
        y (LT: y < x)
        E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src ktr_tgt l
    :
    (ObligationRA.duty y inlp tid l ∗ ObligationRA.taxes (List.map fst l) Ord.omega)
      -∗
      ((ObligationRA.duty y inlp tid l)
         -∗
         (FairRA.white_thread (S:=_))
         -∗
         (=|x|=(fairI (ident_tgt:=ident_tgt) x)={E,⊤}=> (wpsim ⊤ r g Q ps true (trigger (Yield) >>= ktr_src) (ktr_tgt tt))))
      -∗
      (wpsim E r g Q ps pt (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt))
  .
  Proof.
    iIntros "H K". unfold wpsim. iIntros (? ? ? ? ?) "(D & [WA WS])".
    iMod (default_I_past_update_ident_thread with "D H") as "[B [W [D0 [D1 [D2 [D3 [D4 [D5 [D6 D7]]]]]]]]]". auto.
    iAssert ((fairI (ident_tgt:=ident_tgt) x) ∗ (wsats x ∗ OwnE E))%I with "[WS D5 D6]" as "C".
    { iFrame. }
    Local Transparent FUpd.
    iPoseProof ("K" with "B W C") as ">[D5 [D6 [E K]]]".
    iApply isim_yieldR. unfold I, fairI. iFrame. iFrame.
    iIntros (? ? ? ? ? ?) "(D & WAS) %".
    iApply ("K" with "[D WAS]"). iFrame. iExists _. eauto.
    Local Opaque FUpd.
  Qed.

  Lemma wpsim_yieldR_gen_pending
        y (LT: y < x)
        E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src ktr_tgt
        (l : list (nat * nat * Vars y))
        l1 l2 pps
        (OBLIGS : l = l1 ++ l2)
        (PENDS : Forall2 (fun '(k1, _, _) '(k2, _) => k1 = k2) l1 pps)
        a (MANY : 1 <= a)
    :
    (Duty(tid) l)
      -∗ (⧖{pps})
      -∗ (◇{List.map fst l2}(1, a))
      -∗
      ((Duty(tid) l)
         -∗
         €
         -∗
         ⧖{pps}
         -∗
         ◇{List.map fst l2}(1, a - 1)
         -∗
         (=|x|=(fairI (ident_tgt:=ident_tgt) x)={E, ⊤}=>
            (wpsim ⊤ r g Q ps true (trigger (Yield) >>= ktr_src) (ktr_tgt tt))))
      -∗
      (wpsim E r g Q ps pt (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt))
  .
  Proof.
    iIntros "D P T H".
    iMod (pcs_decr _ _ (a-1) 1 a _ with "T") as "[REST T]".
    Unshelve. 2: lia.
    iAssert (#=> ObligationRA.taxes (List.map fst (List.map (λ '(k, l0, f), (k, layer l0 1, f)) l2)) Ord.omega) with "[T]" as "T".
    { unfold progress_credits.
      replace (List.map fst (List.map (λ '(k, l0, f), (k, layer l0 1, f)) l2))
        with (List.map (λ '(k, n), (k, layer n 1)) (List.map fst l2)).
      { iMod (ObligationRA.taxes_ord_mon with "T") as "T".
        2:{ iModIntro. iFrame. }
        rewrite layer_one_one. reflexivity.
      }
      { rewrite ! List.map_map. f_equal. extensionalities. des_ifs. ss. des_ifs. }
    }
    iMod "T". iApply (wpsim_yieldR_strong_pending with "[D P T]").
    5:{ iIntros "D W P". iApply ("H" with "D W P REST"). }
    4: iFrame.
    auto.
    { subst. apply List.map_app. }
    { apply Forall2_fmap_l. eapply Forall2_impl. eauto. ss. i. des_ifs. }
  Qed.

  Lemma wpsim_yieldR_gen
        y (LT: y < x)
        E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src ktr_tgt
        (l : list (nat * nat * Vars y))
    :
    (Duty(tid) l ∗ ◇{List.map fst l}(1, 1))
      -∗
      ((Duty(tid) l)
         -∗
         €
         -∗
         (=|x|=(fairI (ident_tgt:=ident_tgt) x)={E, ⊤}=>
            (wpsim ⊤ r g Q ps true (trigger (Yield) >>= ktr_src) (ktr_tgt tt))))
      -∗
      (wpsim E r g Q ps pt (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt))
  .
  Proof.
    iIntros "[D T] H".
    iAssert (#=> ObligationRA.taxes (List.map fst (List.map (λ '(k, l0, f), (k, layer l0 1, f)) l)) Ord.omega) with "[T]" as "T".
    { unfold progress_credits.
      replace (List.map fst (List.map (λ '(k, l0, f), (k, layer l0 1, f)) l))
        with (List.map (λ '(k, n), (k, layer n 1)) (List.map fst l)).
      { iMod (ObligationRA.taxes_ord_mon with "T") as "T".
        2:{ iModIntro. iFrame. }
        rewrite layer_one_one. reflexivity.
      }
      { rewrite ! List.map_map. f_equal. extensionalities. des_ifs. ss. des_ifs. }
    }
    iMod "T". iApply (wpsim_yieldR_strong with "[D T]"). eauto. iFrame.
    iApply "H".
  Qed.

  Lemma wpsim_yieldR_gen2
        y (LT: y < x)
        E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src ktr_tgt
        (l : list (nat * nat * Vars y))
        a (MANY : 1 <= a)
    :
    (Duty(tid) l ∗ ◇{List.map fst l}(1, a))
      -∗
      ((Duty(tid) l)
         -∗
         €
         -∗
         ◇{List.map fst l}(1, a - 1)
         -∗
         (=|x|=(fairI (ident_tgt:=ident_tgt) x)={E, ⊤}=>
            (wpsim ⊤ r g Q ps true (trigger (Yield) >>= ktr_src) (ktr_tgt tt))))
      -∗
      (wpsim E r g Q ps pt (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt))
  .
  Proof.
    iIntros "[D T] H".
    iMod (pcs_decr _ _ (a-1) 1 a _ with "T") as "[REST T]".
    Unshelve. 2: lia.
    iApply (wpsim_yieldR_gen with "[D T] [-]"). 2: iFrame. auto. iIntros "D FC". iApply ("H" with "D FC REST").
  Qed.

  Lemma wpsim_yieldR
        y (LT: y < x)
        r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src ktr_tgt
        (l : list (nat * nat * Vars y))
    :
    (Duty(tid) l ∗ ◇{List.map fst l}(1, 1))
      -∗
      ((Duty(tid) l)
         -∗
         €
         -∗
         (wpsim ⊤ r g Q ps true (trigger (Yield) >>= ktr_src) (ktr_tgt tt)))
      -∗
      (wpsim ⊤ r g Q ps pt (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt))
  .
  Proof.
    iIntros "[D T] H". iApply wpsim_discard. eauto.
    iApply (wpsim_yieldR_gen with "[D T]"). eauto. iFrame.
    iIntros "D F". iModIntro. iApply ("H" with "D F").
  Qed.

  Lemma wpsim_yieldR2
        y (LT: y < x)
        r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src ktr_tgt
        (l : list (nat * nat * Vars y))
        a (MANY : 1 <= a)
    :
    (Duty(tid) l ∗ ◇{List.map fst l}(1, a))
      -∗
      ((Duty(tid) l)
         -∗
         €
         -∗
         ◇{List.map fst l}(1, a - 1)
         -∗
         (wpsim ⊤ r g Q ps true (trigger (Yield) >>= ktr_src) (ktr_tgt tt)))
      -∗
      (wpsim ⊤ r g Q ps pt (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt))
  .
  Proof.
    iIntros "[D T] H". iApply wpsim_discard. eauto.
    iApply (wpsim_yieldR_gen2 with "[D T]"). 1,2: eauto. iFrame.
    iIntros "D F C". iModIntro. iApply ("H" with "D F C").
  Qed.

  Lemma wpsim_sync_strong_pending
        y (LT: y < x)
        E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src ktr_tgt l
        l1 l2 pps
        (OBLIGS : l = l1 ++ l2)
        (PENDS : Forall2 (fun '(k1, _, _) '(k2, _) => k1 = k2) l1 pps)
    :
    (ObligationRA.duty y inlp tid l ∗ ObligationRA.pends pps ∗ ObligationRA.taxes (List.map fst l2) Ord.omega)
      -∗
      ((ObligationRA.duty y inlp tid l)
         -∗
         (FairRA.white_thread (S:=_))
         -∗
         (ObligationRA.pends pps)
         -∗
         (=|x|=(fairI (ident_tgt:=ident_tgt) x)={E,⊤}=>
               (wpsim ⊤ g g Q true true (ktr_src tt) (ktr_tgt tt))))
      -∗
      (wpsim E r g Q ps pt (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt)).
  Proof.
    iIntros "H K". unfold wpsim. iIntros (? ? ? ? ?) "(D & [WA WS])".
    iMod (default_I_past_update_ident_thread_pending with "D H") as "[B [W ([D0 [D1 [D2 [D3 [D4 [D5 [D6 D7]]]]]]] & PPS)]]".
    1,2,3: eauto.
    iAssert ((fairI (ident_tgt:=ident_tgt) x) ∗ (wsats x ∗ OwnE E))%I with "[WS D5 D6]" as "C".
    { iFrame. }
    Local Transparent FUpd.
    iPoseProof ("K" with "B W PPS C") as ">[D5 [D6 [E K]]]".
    iApply isim_sync. unfold I, fairI. iFrame. iFrame.
    iIntros (? ? ? ? ? ?) "(D & WAS) %".
    iApply ("K" with "[D WAS]"). iFrame. iExists _. eauto.
    Local Opaque FUpd.
  Qed.

  Lemma wpsim_sync_strong
        y (LT: y < x)
        E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src ktr_tgt l
    :
    (ObligationRA.duty y inlp tid l ∗ ObligationRA.taxes (List.map fst l) Ord.omega)
      -∗
      ((ObligationRA.duty y inlp tid l)
         -∗
         (FairRA.white_thread (S:=_))
         -∗
         (=|x|=(fairI (ident_tgt:=ident_tgt) x)={E,⊤}=> (wpsim ⊤ g g Q true true (ktr_src tt) (ktr_tgt tt))))
      -∗
      (wpsim E r g Q ps pt (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt)).
  Proof.
    iIntros "H K". unfold wpsim. iIntros (? ? ? ? ?) "(D & WA & WS)".
    iPoseProof (default_I_past_update_ident_thread with "D H") as "> [B [W [D0 [D1 [D2 [D3 [D4 [D5 [D6 D7]]]]]]]]]". auto.
    iAssert ((fairI (ident_tgt:=ident_tgt) x) ∗ (wsats x ∗ OwnE E))%I with "[WS D5 D6]" as "C".
    { iFrame. }
    Local Transparent FUpd.
    iPoseProof ("K" with "B W C") as "> (D5 & C & E & K)".
    iApply isim_sync. unfold I. iFrame. iFrame.
    iIntros (? ? ? ? ? ?) "(D & C & E) %".
    iApply ("K" with "[D C E]"). iFrame. iExists _. eauto.
    Local Opaque FUpd.
  Qed.

  Lemma wpsim_sync_gen_pending
        y (LT: y < x)
        E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src ktr_tgt
        (l : list (nat * nat * Vars y))
        l1 l2 pps
        (OBLIGS : l = l1 ++ l2)
        (PENDS : Forall2 (fun '(k1, _, _) '(k2, _) => k1 = k2) l1 pps)
        a (MANY : 1 <= a)
    :
    (Duty(tid) l)
      -∗ (⧖{pps})
      -∗ (◇{List.map fst l2}(1, a))
      -∗
      ((Duty(tid) l)
         -∗
         €
         -∗
         ⧖{pps}
         -∗
         ◇{List.map fst l2}(1, a - 1)
         -∗
         (=|x|=(fairI (ident_tgt:=ident_tgt) x)={E, ⊤}=>
            (wpsim ⊤ g g Q true true (ktr_src tt) (ktr_tgt tt))))
      -∗
      (wpsim E r g Q ps pt (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt)).
  Proof.
    iIntros "D P T H".
    iMod (pcs_decr _ _ (a-1) 1 a _ with "T") as "[REST T]".
    Unshelve. 2: lia.
    iAssert (#=> ObligationRA.taxes (List.map fst (List.map (λ '(k, l0, f), (k, layer l0 1, f)) l2)) Ord.omega) with "[T]" as "T".
    { unfold progress_credits.
      replace (List.map fst (List.map (λ '(k, l0, f), (k, layer l0 1, f)) l2))
        with (List.map (λ '(k, n), (k, layer n 1)) (List.map fst l2)).
      { iMod (ObligationRA.taxes_ord_mon with "T") as "T".
        2:{ iModIntro. iFrame. }
        rewrite layer_one_one. reflexivity.
      }
      { rewrite ! List.map_map. f_equal. extensionalities. des_ifs. ss. des_ifs. }
    }
    iMod "T". iApply (wpsim_sync_strong_pending with "[D P T]").
    5:{ iIntros "D W P". iApply ("H" with "D W P REST"). }
    4: iFrame.
    auto.
    { subst. apply List.map_app. }
    { apply Forall2_fmap_l. eapply Forall2_impl. eauto. ss. i. des_ifs. }
  Qed.

  Lemma wpsim_sync_gen
        y (LT: y < x)
        E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src ktr_tgt
        (l : list (nat * nat * Vars y))
    :
    (Duty(tid) l ∗ ◇{List.map fst l}(1, 1))
      -∗
      ((Duty(tid) l)
         -∗
         €
         -∗
         (=|x|=(fairI (ident_tgt:=ident_tgt) x)={E, ⊤}=>
            (wpsim ⊤ g g Q true true (ktr_src tt) (ktr_tgt tt))))
      -∗
      (wpsim E r g Q ps pt (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt)).
  Proof.
    iIntros "[D T] H".
    iAssert (#=> ObligationRA.taxes (List.map fst (List.map (λ '(k, l0, f), (k, layer l0 1, f)) l)) Ord.omega) with "[T]" as "T".
    { unfold progress_credits.
      replace (List.map fst (List.map (λ '(k, l0, f), (k, layer l0 1, f)) l))
        with (List.map (λ '(k, n), (k, layer n 1)) (List.map fst l)).
      { iMod (ObligationRA.taxes_ord_mon with "T") as "T".
        2:{ iModIntro. iFrame. }
        rewrite layer_one_one. reflexivity.
      }
      { rewrite ! List.map_map. f_equal. extensionalities. des_ifs. ss. des_ifs. }
    }
    iMod "T". iApply (wpsim_sync_strong with "[D T]"). eauto. iFrame.
    iApply "H".
  Qed.

  Lemma wpsim_sync_gen2
        y (LT: y < x)
        E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src ktr_tgt
        (l : list (nat * nat * Vars y))
        a (MANY : 1 <= a)
    :
    (Duty(tid) l ∗ ◇{List.map fst l}(1, a))
      -∗
      ((Duty(tid) l)
         -∗
         €
         -∗
         ◇{List.map fst l}(1, a - 1)
         -∗
         (=|x|=(fairI (ident_tgt:=ident_tgt) x)={E, ⊤}=>
            (wpsim ⊤ g g Q true true (ktr_src tt) (ktr_tgt tt))))
      -∗
      (wpsim E r g Q ps pt (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt)).
  Proof.
    iIntros "[D T] H".
    iMod (pcs_decr _ _ (a-1) 1 a _ with "T") as "[REST T]".
    Unshelve. 2: lia.
    iApply (wpsim_sync_gen with "[D T] [-]"). 2: iFrame. auto. iIntros "D FC". iApply ("H" with "D FC REST").
  Qed.

  Lemma wpsim_sync
        y (LT: y < x)
        r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src ktr_tgt
        (l : list (nat * nat * Vars y))
    :
    (Duty(tid) l ∗ ◇{List.map fst l}(1, 1))
      -∗
      ((Duty(tid) l)
         -∗
         €
         -∗
         (wpsim ⊤ g g Q true true (ktr_src tt) (ktr_tgt tt)))
      -∗
      (wpsim ⊤ r g Q ps pt (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt)).
  Proof.
    iIntros "[D T] H". iApply wpsim_discard. eauto.
    iApply (wpsim_sync_gen with "[D T]"). eauto. iFrame.
    iIntros "D F". iModIntro. iApply ("H" with "D F").
  Qed.

  Lemma wpsim_sync2
        y (LT: y < x)
        r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src ktr_tgt
        (l : list (nat * nat * Vars y))
        a (MANY : 1 <= a)
    :
    (Duty(tid) l ∗ ◇{List.map fst l}(1, a))
      -∗
      ((Duty(tid) l)
         -∗
         €
         -∗
         ◇{List.map fst l}(1, a - 1)
         -∗
         (wpsim ⊤ g g Q true true (ktr_src tt) (ktr_tgt tt)))
      -∗
      (wpsim ⊤ r g Q ps pt (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt)).
  Proof.
    iIntros "[D T] H". iApply wpsim_discard. eauto.
    iApply (wpsim_sync_gen2 with "[D T]"). 1,2: eauto. iFrame.
    iIntros "D F C". iModIntro. iApply ("H" with "D F C").
  Qed.

  Lemma wpsim_yieldR_weak
        y (LT: y < x)
        E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src ktr_tgt l
        (TOP: ⊤ ⊆ E)
    :
    (ObligationRA.duty y inlp tid l ∗ ObligationRA.taxes (List.map fst l) Ord.omega)
      -∗
      ((ObligationRA.duty y inlp tid l)
         -∗
         (FairRA.white_thread (S:=_))
         -∗
         wpsim ⊤ r g Q ps true (trigger (Yield) >>= ktr_src) (ktr_tgt tt))
      -∗
      (wpsim E r g Q ps pt (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt))
  .
  Proof.
    iIntros "H K". iApply wpsim_discard; [eassumption|].
    iApply (wpsim_yieldR_strong with "H"). auto. iIntros "DUTY WHITE".
    iModIntro. iApply ("K" with "DUTY WHITE").
  Qed.

  Lemma wpsim_sync_weak
        y (LT: y < x)
        E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src ktr_tgt l
        (TOP: ⊤ ⊆ E)
    :
    (ObligationRA.duty y inlp tid l ∗ ObligationRA.taxes (List.map fst l) Ord.omega)
      -∗
      ((ObligationRA.duty y inlp tid l)
         -∗
         (FairRA.white_thread (S:=_))
         -∗
         wpsim ⊤ g g Q true true (ktr_src tt) (ktr_tgt tt))
      -∗
      (wpsim E r g Q ps pt (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt)).
  Proof.
    iIntros "H K". iApply wpsim_discard; [eassumption|].
    iApply (wpsim_sync_strong with "H"). auto. iIntros "DUTY WHITE".
    iModIntro. iApply ("K" with "DUTY WHITE").
  Qed.

  Lemma wpsim_yieldR_simple
        y (LT: y < x)
        r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src ktr_tgt
    :
    =|x|=(fairI (ident_tgt:=ident_tgt) x)={⊤}=>
         ((FairRA.black_ex inlp tid 1)
            ∗
            ((FairRA.black_ex inlp tid 1)
               -∗
               (FairRA.white_thread (S:=_))
               -∗
               wpsim ⊤ r g Q ps true (trigger (Yield) >>= ktr_src) (ktr_tgt tt)))
         -∗
         (wpsim ⊤ r g Q ps pt (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt))
  .
  Proof.
    iIntros "> [H K]". iApply (wpsim_yieldR_weak with "[H]").
    { eauto. }
    { ss. }
    { iPoseProof (ObligationRA.black_to_duty with "H") as "H". iFrame. }
    iIntros "B W". iApply ("K" with "[B] [W]"); ss.
    { iApply ObligationRA.duty_to_black. auto. }
  Qed.

  Lemma wpsim_sync_simple
        y (LT: y < x)
        r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src ktr_tgt
    :
    =|x|=(fairI (ident_tgt:=ident_tgt) x)={⊤}=>
         ((FairRA.black_ex inlp tid 1)
            ∗
            ((FairRA.black_ex inlp tid 1)
               -∗
               (FairRA.white_thread (S:=_))
               -∗
               wpsim ⊤ g g Q true true (ktr_src tt) (ktr_tgt tt)))
         -∗
         (wpsim ⊤ r g Q ps pt (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt)).
  Proof.
    iIntros "> [H K]". iApply (wpsim_sync_weak with "[H]").
    { eauto. }
    { ss. }
    { iPoseProof (ObligationRA.black_to_duty with "H") as "H". iFrame. }
    iIntros "B W". iApply ("K" with "[B] [W]"); ss.
    { iApply ObligationRA.duty_to_black. auto. }
  Qed.

  Lemma wpsim_reset E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt itr_src itr_tgt
    :
    (wpsim E r g Q false false itr_src itr_tgt)
      -∗
      (wpsim E r g Q ps pt itr_src itr_tgt)
  .
  Proof.
    unfold wpsim. iIntros "H" (? ? ? ? ?) "D".
    iApply isim_reset. iApply ("H" with "D").
  Qed.

  Lemma wpsim_stutter_mon E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt itr_src itr_tgt
        ps' pt'
        (MONS: ps' = true -> ps = true)
        (MONT: pt' = true -> pt = true)
    :
    (wpsim E r g Q ps' pt' itr_src itr_tgt)
      -∗
      (wpsim E r g Q ps pt itr_src itr_tgt)
  .
  Proof.
    unfold wpsim. iIntros "H" (? ? ? ? ?) "D".
    iApply isim_stutter_mon; eauto. iApply ("H" with "D").
  Qed.

  Lemma wpsim_progress E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        itr_src itr_tgt
    :
    (wpsim E g g Q false false itr_src itr_tgt)
      -∗
      (wpsim E r g Q true true itr_src itr_tgt)
  .
  Proof.
    unfold wpsim. iIntros "H" (? ? ? ? ?) "D".
    iApply isim_progress. iApply ("H" with "D").
  Qed.

End STATE.

Section STATETYPES.

  Class StateTypes :=
    { st_src_type : Type ;
      st_tgt_type : Type ;
      id_src_type : ID ;
      id_tgt_type : ID
    }.

End STATETYPES.

Section TRIPLES.

  Context `{Σ: GRA.t}.

  Context {STT : StateTypes}.
  Local Notation state_src := (@st_src_type STT).
  Local Notation state_tgt := (@st_tgt_type STT).
  Local Notation ident_src := (@id_src_type STT).
  Local Notation ident_tgt := (@id_tgt_type STT).

  Let srcE := threadE ident_src state_src.
  Let tgtE := threadE ident_tgt state_tgt.

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
  Context `{ONESHOTRA: @GRA.inG ArrowShotRA Σ}.
  Context `{ARROWRA: @GRA.inG (@ArrowRA ident_tgt Vars) Σ}.
  Notation iProp := (iProp Σ).


  (** Formats for triples-like specs. *)

  Definition term_cond m tid (R_term : Type) :=
    (fun (rs rt : R_term) => (own_thread tid ∗ ObligationRA.duty m inlp tid []) ∗ ⌜rs = rt⌝)%I.

  Definition triple_gen
             n m
             tid (P : iProp) {RV} (Q : RV -> iProp) (E1 E2 : coPset)
             {R_term : Type}
             (* {R_src R_tgt : Type} (TERM : R_src -> R_tgt -> Vars m) *)
             ps pt
             (itr_src : itree srcE R_term) (code : itree tgtE RV) (ktr_tgt : ktree tgtE RV R_term)
    : iProp
    :=
    (∀ rr gr,
        (P)
          -∗
          (∀ (rv : RV),
              (Q rv) -∗ wpsim n tid E2 rr gr (@term_cond m tid R_term) ps true itr_src (ktr_tgt rv))
          -∗
          wpsim n tid E1 rr gr (@term_cond m tid R_term) ps pt itr_src (code >>= ktr_tgt))%I.
          (* wpsim n tid E1 rr gr (fun rs rt => prop m (TERM rs rt)) ps pt itr_src (code >>= ktr_tgt))%I. *)

  Definition atomic_triple
             tid n m (E : coPset) (P : iProp) {RV} (code : itree tgtE RV) (Q : RV -> iProp)
    : iProp
    :=
    (* (∀ R_src R_tgt (TERM : R_src -> R_tgt -> Vars n) ps pt *)
    (∀ R_term ps pt
       (itr_src : itree srcE R_term)
       (ktr_tgt : RV -> itree tgtE R_term),
        triple_gen n m tid P Q E E ps pt itr_src code ktr_tgt)%I.
  (* (P) *)
  (*   -∗ *)
  (*   (∀ (rv : RV), *)
  (*       (Q rv) -∗ wpsim n tid E rr gr TERM ps true itr_src (ktr_tgt rv)) *)
  (*   -∗ *)
  (*   wpsim n tid E rr gr TERM ps pt itr_src (code >>= ktr_tgt))%I. *)

  Definition non_atomic_triple
             tid n m (E : coPset) (P : iProp) {RV} (code : itree tgtE RV) (Q : RV -> iProp)
    : iProp
    :=
    (* (∀ R_src R_tgt (TERM : R_src -> R_tgt -> Vars n) ps pt *)
    (∀ R_term ps pt
       (itr_src : itree srcE R_term)
       (ktr_tgt : RV -> itree tgtE R_term),
        triple_gen n m tid P Q E ⊤ ps pt (trigger Yield;;; itr_src) code ktr_tgt)%I.
        (* triple_gen (S n) (m:=n) tid P Q E ⊤ TERM ps pt (trigger Yield;;; itr_src) code ktr_tgt)%I. *)
      (* (P) *)
      (*   -∗ *)
      (*   (∀ (rv : RV), *)
      (*       (Q rv) -∗ wpsim n tid ⊤ rr gr TERM ps true (trigger Yield;;; itr_src) (ktr_tgt rv)) *)
      (*   -∗ *)
      (*   wpsim n tid E rr gr TERM ps pt (trigger Yield;;; itr_src) (code >>= ktr_tgt))%I. *)

  (* For syntactic encoding. *)
  Definition triple_format {Form : Type} {intpF : Form -> iProp}
             tid
             (I0 : TIdSet.t -> (@imap ident_src owf) -> (@imap (sum_tid ident_tgt) nat_wf) -> state_src -> state_tgt -> Form)
             (I1 : TIdSet.t -> (@imap ident_src owf) -> (@imap (sum_tid ident_tgt) nat_wf) -> state_src -> state_tgt -> Form)
             (I2 : TIdSet.t -> (@imap ident_src owf) -> (@imap (sum_tid ident_tgt) nat_wf) -> state_src -> state_tgt -> coPset -> Form)
             (P : Form)
             {RV : Type}
             (Q : RV -> Form)
             (E1 E2 : coPset)
    :
    forall R_src R_tgt (TERM: R_src -> R_tgt -> Form), bool -> bool -> itree srcE R_src -> itree tgtE RV -> (ktree tgtE RV R_tgt) -> iProp
    :=
    fun R_src R_tgt TERM ps pt itr_src code ktr_tgt =>
      (* (∀ (rr gr : rel), *)
      (∀ rr gr,
          let INV :=
            (fun ths ims imt sts stt => intpF (I0 ths ims imt sts stt))
          in
          let INV1 :=
            (fun ths ims imt sts stt => intpF (I1 ths ims imt sts stt))
          in
          let FIN :=
            (fun r_src r_tgt ths ims imt sts stt => ((INV1 ths ims imt sts stt) ∗ (intpF (TERM r_src r_tgt)))%I)
          in
          let LIFT1 :=
            (fun R_src R_tgt QQ ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt =>
               (∃ (Q: R_src -> R_tgt -> iProp)
                  (EQ: QQ = (fun r_src r_tgt ths im_src im_tgt st_src st_tgt =>
                               (INV1 ths im_src im_tgt st_src st_tgt) ∗ (Q r_src r_tgt))),
                   (rr R_src R_tgt Q ps pt itr_src itr_tgt)
                     ∗
                     (INV1 ths im_src im_tgt st_src st_tgt))%I)
          in
          let LIFT2 :=
            (fun R_src R_tgt QQ ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt =>
               (∃ (Q: R_src -> R_tgt -> iProp)
                  (EQ: QQ = (fun r_src r_tgt ths im_src im_tgt st_src st_tgt =>
                               (INV1 ths im_src im_tgt st_src st_tgt) ∗ (Q r_src r_tgt))),
                   (gr R_src R_tgt Q ps pt itr_src itr_tgt)
                     ∗
                     (INV1 ths im_src im_tgt st_src st_tgt))%I)
          in
          (intpF P)
            -∗
            (∀ (rv : RV),
                (intpF (Q rv))
                  -∗
                  (∀ ths im_src im_tgt st_src st_tgt,
                      (intpF (I2 ths im_src im_tgt st_src st_tgt E2))
                        -∗
                        isim
                        tid INV LIFT1 LIFT2 FIN
                        ps true itr_src (ktr_tgt rv) ths im_src im_tgt st_src st_tgt))
            -∗
            (∀ ths im_src im_tgt st_src st_tgt,
                (intpF (I2 ths im_src im_tgt st_src st_tgt E1))
                  -∗
                  isim
                  tid INV LIFT1 LIFT2 FIN
                  ps pt itr_src (code >>= ktr_tgt) ths im_src im_tgt st_src st_tgt)
      )%I.

  (** LAT. *)
  Section atomic_update_def.
  (* TODO: ideally should be [tele] *)
  Context {TA TB : Type}.
  Implicit Types
    (Eo Ei : coPset) (* outer/inner masks *)
    (α : TA → iProp) (* atomic pre-condition *)
    (β : TA → TB → iProp) (* atomic post-condition *)
    (POST : TA → TB → iProp) (* post-condition *)
  .

  (* TODO: Reuse the following from [iris.bi.lib.atomic] with all the
    sweet typeclass instances, tactics, and abort for free.
    Probably requires adding [atomic_update] as an atom to the syntax,
    or implementing fixpoints in the syntax level, which is not ideal.
  *)
  (* Definition atomic_update n Eo Ei α β POST : iProp :=
    @atomic_update
      iProp (iProp_bi_fupd_FUpd (S n) True) TA TB
      Eo Ei α β POST. *)
  (** atomic_update without abort, so no need for fixpoint *)
  Definition atomic_update n Eo Ei α β POST : iProp :=
    =|S n|={Eo, Ei}=> ∃ x, α x ∗
          (∀ y, β x y =|S n|={Ei, Eo}=∗ POST x y).
  (* TODO: Seal? *)
  End atomic_update_def.

  (* TODO: make masks fully generic *)
  Definition LAT_ind {TA TB TP}
            tid n (E : coPset)
            {RV}
            (α: TA → iProp) (* atomic pre-condition *)
            (β: TA → TB → iProp) (* atomic post-condition *)
            (POST: TA → TB → TP → iProp) (* post-condition *)
            (f: TA → TB → TP → RV) (* Turn the return data into the return value *)
            (code : itree tgtE RV)
    : iProp
    :=
    ∀ R_term ps pt
       (itr_src : itree srcE R_term)
       (ktr_tgt : RV -> itree tgtE R_term),
      atomic_update n (⊤∖E) ∅ α β
        (λ x y, ∀ z, POST x y z -∗
          wpsim (S n) tid ⊤ ibot7 ibot7 (@term_cond n tid R_term) ps true (trigger Yield;;; itr_src) (ktr_tgt (f x y z))
        )
       -∗
       wpsim (S n) tid ⊤ ibot7 ibot7 (@term_cond n tid R_term) ps pt (trigger Yield;;; itr_src) (code >>= ktr_tgt).

End TRIPLES.

(** For triples. *)
Ltac iStartTriple := iIntros (? ? ? ? ? ? ?).
(* Ltac iStartLAT := iIntros (? ? ? ? ?). *)

Notation "'[@' tid , n , E '@]' { P } code { v , Q }" :=
  (atomic_triple tid (S n) n E P code (fun v => Q))
    (at level 200, tid, n, E, P, code, v, Q at level 1,
      format "[@  tid ,  n ,  E  @] { P }  code  { v ,  Q }") : bi_scope.

Notation "'[@' tid , n , δ , E '@]' { P } code { v , Q }" :=
  (atomic_triple tid (S (δ + n)) n E P code (fun v => Q))
    (at level 200, tid, n, δ, E, P, code, v, Q at level 1,
      format "[@  tid ,  n ,  δ ,  E  @] { P }  code  { v ,  Q }") : bi_scope.

Notation "'[@' tid , n , E '@]' ⧼ P ⧽ code ⧼ v , Q ⧽" :=
  (non_atomic_triple tid (S n) n E P code (fun v => Q))
    (at level 200, tid, n, E, P, code, v, Q at level 1,
      format "[@  tid ,  n ,  E  @] ⧼ P ⧽  code  ⧼ v ,  Q ⧽") : bi_scope.

Notation "'[@' tid , n , δ , E '@]' ⧼ P ⧽ code ⧼ v , Q ⧽" :=
  (non_atomic_triple tid (S (δ + n)) n E P code (fun v => Q))
    (at level 200, tid, n, δ, E, P, code, v, Q at level 1,
      format "[@  tid ,  n ,  δ ,  E  @] ⧼ P ⧽  code  ⧼ v ,  Q ⧽") : bi_scope.


(** Notation: Atomic updates *)
(** We avoid '<<'/'>>' since those can also reasonably be infix operators
(and in fact Autosubst uses the latter). *)
Notation "'AU' '<{' ∃∃ x , α '}>' @ n , Eo , Ei '<{' ∀∀ y , β , 'COMM' POST '}>'" :=
  (* The way to read the [tele_app foo] here is that they convert the n-ary
  function [foo] into a unary function taking a telescope as the argument. *)
    (atomic_update n Eo Ei
                   (λ x, α%I)
                   (λ x y, β%I)
                   (λ x y, POST%I)
    )
    (at level 20, Eo, Ei, α, β, POST at level 200, x binder, y binder,
     format "'[hv   ' 'AU'  '<{'  '[' ∃∃  x ,  '/' α  ']' '}>'  '/' @  '[' n ,  '/' Eo ,  '/' Ei ']'  '/' '<{'  '[' ∀∀  y ,  '/' β ,  '/' COMM  POST  ']' '}>' ']'") : bi_scope.

(* The way to read the [tele_app foo] here is that they convert the n-ary
function [foo] into a unary function taking a telescope as the argument. *)
Notation "'<<{' ∀∀ x , α '}>>' e @ tid , n , E '<<{' ∃∃ y , β '|' z , 'RET' v ; POST '}>>'" :=
  (LAT_ind tid n E
          (λ x, α%I)
          (λ x y, β%I)
          (λ x y z, POST%I)
          (λ x y z, v)
          e
  )
  (at level 20, E, β, α, v, POST at level 200, x binder, y binder, z binder,
   format "'[hv' '<<{'  '[' ∀∀  x ,  '/' α  ']' '}>>'  '/  ' e  @  tid , n , E  '/' '<<{'  '[' ∃∃  y ,  '/' β  '|'  '/' z ,  RET  v ;  '/' POST  ']' '}>>' ']'")
  : bi_scope.

(** Simulation tactics. *)

From Fairness Require Export Red IRed.

Ltac lred := repeat (prw _red_gen 1 2 0).
Ltac rred := repeat (prw _red_gen 1 1 0).

From Fairness Require Export LinkingRed.

Ltac lred2 := (prw ltac:(red_tac itree_class) 1 2 0).
Ltac rred2 := (prw ltac:(red_tac itree_class) 1 1 0).
Ltac lred2r := repeat lred2.
Ltac rred2r := repeat rred2.
