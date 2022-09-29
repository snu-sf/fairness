From sflib Require Import sflib.
From Paco Require Import paco.
From Fairness Require Import PCM ITreeLib pind.
Require Import Program.
From Fairness Require Import IProp IPM.
From Fairness Require Import PCM MonotonePCM ThreadsRA ModSim FairBeh.

Set Implicit Arguments.

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
      (own_threads ths)
        **
        (OwnM (Auth.black (Excl.just st_src: @Excl.t state_src): stateSrcRA))
        **
        (OwnM (Auth.black (Excl.just st_tgt: @Excl.t state_tgt): stateTgtRA))
        **
        (OwnM (Auth.black (Excl.just im_src: @Excl.t (imap ident_src wf_src)): identSrcRA))
        **
        (OwnM (Auth.black (Excl.just (imap_proj_id2 im_tgt): @Excl.t (imap ident_tgt nat_wf)): identTgtRA))
        **
        (OwnM (Auth.black (Excl.just (imap_proj_id1 im_tgt): @Excl.t (imap thread_id nat_wf)): identThsRA))
  .
End INVARIANT.
