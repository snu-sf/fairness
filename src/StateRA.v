From sflib Require Import sflib.
From Paco Require Import paco.
From Fairness Require Import PCM ITreeLib pind.
Require Import Program.
From Fairness Require Import IProp IPM.
From Fairness Require Import PCM MonotonePCM ThreadsRA ModSim FairBeh.

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
End UPD.


Section INVARIANT.
  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable ident_src: ID.
  Variable ident_tgt: ID.
  Variable wf_src: WF.

  Definition stateSrcRA: URA.t := Auth.t (Excl.t state_src).
  Definition stateTgtRA: URA.t := Auth.t (Excl.t state_tgt).
  Definition identSrcRA: URA.t := Auth.t (Excl.t (imap ident_src wf_src)).
  Definition identTgtRA: URA.t := Auth.t (Excl.t (imap ident_tgt nat_wf)).
  Definition identThsRA: URA.t := Auth.t (Excl.t (imap thread_id nat_wf)).

  Context `{MONORA: @GRA.inG monoRA Σ}.
  Context `{THSRA: @GRA.inG ths_RA Σ}.
  Context `{STATESRC: @GRA.inG stateSrcRA Σ}.
  Context `{STATETGT: @GRA.inG stateTgtRA Σ}.
  Context `{IDENTSRC: @GRA.inG identSrcRA Σ}.
  Context `{IDENTTGT: @GRA.inG identTgtRA Σ}.
  Context `{IDENTTHS: @GRA.inG identThsRA Σ}.

  Definition default_I: TIdSet.t -> (@imap ident_src wf_src) -> (@imap (sum_tid ident_tgt) nat_wf) -> state_src -> state_tgt -> iProp :=
    fun ths im_src im_tgt st_src st_tgt =>
      (own_threads_black ths)
        **
        (OwnM (Auth.black (Excl.just st_src: @Excl.t state_src): stateSrcRA))
        **
        (OwnM (Auth.black (Excl.just st_tgt: @Excl.t state_tgt): stateTgtRA))
        **
        (OwnM (Auth.black (Excl.just im_src: @Excl.t (imap ident_src wf_src)): identSrcRA))
        **
        (OwnM (Auth.black (Excl.just (snd (imap_proj_id im_tgt)): @Excl.t (imap ident_tgt nat_wf)): identTgtRA))
        **
        (OwnM (Auth.black (Excl.just (fst (imap_proj_id im_tgt)): @Excl.t (imap thread_id nat_wf)): identThsRA))
  .

  Lemma default_I_update_st_src ths im_src im_tgt st_src0 st_tgt st_src' st_src1
    :
    (default_I ths im_src im_tgt st_src0 st_tgt)
      -∗
      (OwnM (Auth.white (Excl.just st_src': @Excl.t state_src): stateSrcRA))
      -∗
      #=> (OwnM (Auth.white (Excl.just st_src1: @Excl.t state_src)) ** default_I ths im_src im_tgt st_src1 st_tgt).
  Proof.
    unfold default_I. iIntros "[[[[[H0 H1] H2] H3] H4] H5] OWN".
    iPoseProof (black_white_update with "H1 OWN") as "> [H1 OWN]".
    iModIntro. iFrame.
  Qed.

  Lemma default_I_update_st_tgt ths im_src im_tgt st_src st_tgt0 st_tgt' st_tgt1
    :
    (default_I ths im_src im_tgt st_src st_tgt0)
      -∗
      (OwnM (Auth.white (Excl.just st_tgt': @Excl.t state_tgt): stateTgtRA))
      -∗
      #=> (OwnM (Auth.white (Excl.just st_tgt1: @Excl.t state_tgt)) ** default_I ths im_src im_tgt st_src st_tgt1).
  Proof.
    unfold default_I. iIntros "[[[[[H0 H1] H2] H3] H4] H5] OWN".
    iPoseProof (black_white_update with "H2 OWN") as "> [H2 OWN]".
    iModIntro. iFrame.
  Qed.

  Lemma default_I_update_ident_src ths im_src0 im_tgt st_src st_tgt im_src' im_src1
    :
    (default_I ths im_src0 im_tgt st_src st_tgt)
      -∗
      (OwnM (Auth.white (Excl.just im_src': @Excl.t (imap ident_src wf_src)): identSrcRA))
      -∗
      #=> (OwnM (Auth.white (Excl.just im_src1: @Excl.t (imap ident_src wf_src))) ** default_I ths im_src1 im_tgt st_src st_tgt).
  Proof.
    unfold default_I. iIntros "[[[[[H0 H1] H2] H3] H4] H5] OWN".
    iPoseProof (black_white_update with "H3 OWN") as "> [H3 OWN]".
    iModIntro. iFrame.
  Qed.

  Lemma default_I_update_ident_tgt ths im_src im_tgt0 st_src st_tgt im_tgt' im_tgt1
    :
    (default_I ths im_src im_tgt0 st_src st_tgt)
      -∗
      (OwnM (Auth.white (Excl.just im_tgt': @Excl.t (imap ident_tgt nat_wf)): identTgtRA))
      -∗
      #=> (OwnM (Auth.white (Excl.just im_tgt1: @Excl.t (imap ident_tgt nat_wf))) ** default_I ths im_src (imap_sum_id (fst (imap_proj_id im_tgt0), im_tgt1)) st_src st_tgt).
  Proof.
    unfold default_I. iIntros "[[[[[H0 H1] H2] H3] H4] H5] OWN".
    iPoseProof (black_white_update with "H4 OWN") as "> [H4 OWN]".
    ss. iModIntro. iFrame.
  Qed.

  Lemma default_I_update_ident_ths ths im_src im_tgt0 st_src st_tgt im_tgt' im_tgt1
    :
    (default_I ths im_src im_tgt0 st_src st_tgt)
      -∗
      (OwnM (Auth.white (Excl.just im_tgt': @Excl.t (imap thread_id nat_wf)): identThsRA))
      -∗
      #=> (OwnM (Auth.white (Excl.just im_tgt1: @Excl.t (imap thread_id nat_wf))) ** default_I ths im_src (imap_sum_id (im_tgt1, snd (imap_proj_id im_tgt0))) st_src st_tgt).
  Proof.
    unfold default_I. iIntros "[[[[[H0 H1] H2] H3] H4] H5] OWN".
    iPoseProof (black_white_update with "H5 OWN") as "> [H5 OWN]".
    ss. iModIntro. iFrame.
  Qed.

  Lemma default_I_get_st_src ths im_src im_tgt st_src st_tgt st_src'
    :
    (default_I ths im_src im_tgt st_src st_tgt)
      -∗
      (OwnM (Auth.white (Excl.just st_src': @Excl.t state_src): stateSrcRA))
      -∗
      ⌜st_src = st_src'⌝.
  Proof.
    unfold default_I. iIntros "[[[[[H0 H1] H2] H3] H4] H5] OWN".
    iApply (black_white_equal with "H1 OWN").
  Qed.

  Lemma default_I_get_st_tgt ths im_src im_tgt st_src st_tgt st_tgt'
    :
    (default_I ths im_src im_tgt st_src st_tgt)
      -∗
      (OwnM (Auth.white (Excl.just st_tgt': @Excl.t state_tgt): stateTgtRA))
      -∗
      ⌜st_tgt = st_tgt'⌝.
  Proof.
    unfold default_I. iIntros "[[[[[H0 H1] H2] H3] H4] H5] OWN".
    iApply (black_white_equal with "H2 OWN").
  Qed.

  Lemma default_I_get_ident_src ths im_src im_tgt st_src st_tgt im_src'
    :
    (default_I ths im_src im_tgt st_src st_tgt)
      -∗
      (OwnM (Auth.white (Excl.just im_src': @Excl.t (imap ident_src wf_src)): identSrcRA))
      -∗
      ⌜im_src = im_src'⌝.
  Proof.
    unfold default_I. iIntros "[[[[[H0 H1] H2] H3] H4] H5] OWN".
    iApply (black_white_equal with "H3 OWN").
  Qed.

  Lemma default_I_get_ident_tgt ths im_src im_tgt st_src st_tgt im_tgt'
    :
    (default_I ths im_src im_tgt st_src st_tgt)
      -∗
      (OwnM (Auth.white (Excl.just im_tgt': @Excl.t (imap ident_tgt nat_wf)): identTgtRA))
      -∗
      ⌜snd (imap_proj_id im_tgt) = im_tgt'⌝.
  Proof.
    unfold default_I. iIntros "[[[[[H0 H1] H2] H3] H4] H5] OWN".
    iApply (black_white_equal with "H4 OWN").
  Qed.

  Lemma default_I_get_ident_ths ths im_src im_tgt st_src st_tgt im_tgt'
    :
    (default_I ths im_src im_tgt st_src st_tgt)
      -∗
      (OwnM (Auth.white (Excl.just im_tgt': @Excl.t (imap thread_id nat_wf)): identThsRA))
      -∗
      ⌜fst (imap_proj_id im_tgt) = im_tgt'⌝.
  Proof.
    unfold default_I. iIntros "[[[[[H0 H1] H2] H3] H4] H5] OWN".
    iApply (black_white_equal with "H5 OWN").
  Qed.

  Lemma default_I_thread_alloc ths0 im_src im_tgt st_src st_tgt ths'
        tid ths1
        (THS: TIdSet.add_new tid ths0 ths1)
    :
    (default_I ths' im_src im_tgt st_src st_tgt)
      -∗
      (own_threads_white ths0)
      -∗
      #=> (own_thread tid ** own_threads_white ths1 ** default_I ths1 im_src im_tgt st_src st_tgt).
  Proof.
    unfold default_I. iIntros "[[[[[H0 H1] H2] H3] H4] H5] H6".
    iPoseProof (threads_alloc with "H0 H6") as "> [[BLACK WHITE] TH]".
    { eauto. }
    iModIntro. iFrame.
  Qed.

  Lemma default_I_thread_dealloc ths0 im_src im_tgt st_src st_tgt ths'
        tid
    :
    (default_I ths' im_src im_tgt st_src st_tgt)
      -∗
      (own_threads_white ths0)
      -∗
      (own_thread tid)
      -∗
      ∃ ths1, ⌜NatMap.remove tid ths0 = ths1⌝ ** #=> (own_threads_white ths1 ** default_I ths1 im_src im_tgt st_src st_tgt).
  Proof.
    unfold default_I. iIntros "[[[[[H0 H1] H2] H3] H4] H5] THS TH".
    iPoseProof (threads_dealloc with "H0 THS TH") as (ths1) "[% H0]".
    iExists _. iSplit; eauto. iMod "H0". iModIntro.
    iDestruct "H0" as "[H0 H6]". iFrame.
  Qed.

  Lemma default_I_ths_eq ths im_src im_tgt st_src st_tgt ths'
    :
    (default_I ths im_src im_tgt st_src st_tgt)
      -∗
      (own_threads_white ths')
      -∗
      ⌜ths = ths'⌝.
  Proof.
    unfold default_I. iIntros "[[[[[H0 H1] H2] H3] H4] H5] THS".
    iApply (threads_eq with "H0 THS").
  Qed.

End INVARIANT.
