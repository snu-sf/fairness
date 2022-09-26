From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Export ITreeLib WFLib FairBeh NatStructs Mod pind.

Set Implicit Arguments.


Section MOD.
  Definition example_fun:
    itree (((@eventE void) +' cE) +' sE (bool * bool)) Any.t :=
    '(l0, f0) <- trigger (@Get _);;
    if (l0: bool)
    then
      ITree.iter
        (fun (_: unit) =>
           trigger Yield;;;
           trigger Yield;;;
           '(l, f) <- trigger (Get _);;
           if (f: bool)
           then
             trigger Yield;;;
             trigger Yield;;;
             Ret (inr tt)
           else
             trigger Yield;;;
             trigger Yield;;;
             Ret (inl tt)) tt;;;
      trigger Yield;;;
      Ret 0↑
    else
      trigger (Put (true, f0));;;
      trigger Yield;;;
      trigger Yield;;;
      '(l1, _) <- trigger (@Get _);;
      trigger Yield;;;
      trigger Yield;;;
      trigger (Put (l1, true));;;
      trigger Yield;;;
      trigger Yield;;;
      Ret 0↑
  .

  Definition example_mod: Mod.t :=
    Mod.mk
      (false, false)
      (fun _ => Some (fun _ => example_fun))
  .

  Definition example_fun_spec:
    itree (((@eventE void) +' cE) +' sE unit) Any.t :=
    trigger Yield;;;
    Ret 0↑
  .

  Definition example_mod_spec: Mod.t :=
    Mod.mk
      tt
      (fun _ => Some (fun _ => example_fun_spec))
  .
End MOD.

From Fairness Require Import IProp IPM Weakest.
From Fairness Require Import ModSim PCM MonotonePCM ThreadsRA.

Section SIM.
  Context `{Σ: GRA.t}.
  Context `{MONORA: @GRA.inG monoRA Σ}.
  Context `{THSRA: @GRA.inG ths_RA Σ}.
  Context `{EXCL: @GRA.inG (Excl.t unit) Σ}.

  Variant W: Type :=
    | W_bot
    | W_own (th: thread_id) (k: nat) (o: nat) (i: nat)
    | W_top
  .

  Variant W_le: W -> W -> Prop :=
    | W_le_bot
        w
      :
      W_le W_bot w
    | W_le_th
        th k i0 i1 o0 o1
        (LE: o0 < o1 \/ o0 <= o1 /\ i0 <= i1)
      :
      W_le (W_own k th o1 i1) (W_own k th o0 i0)
    | W_le_top
        w
      :
      W_le w W_top
  .

  Global Program Instance ge_PreOrder: PreOrder ge.
  Next Obligation.
  Proof.
    ii. lia.
  Qed.
  Next Obligation.
  Proof.
    ii. lia.
  Qed.

  Program Instance W_le_PreOrder: PreOrder W_le.
  Next Obligation.
  Proof.
    ii. destruct x; econs. lia.
  Qed.
  Next Obligation.
  Proof.
    ii. inv H; inv H0; try econs; eauto. lia.
  Qed.

  Let I_aux (w: W): (@imap void nat_wf) -> (@imap (sum_tid void) nat_wf) -> unit -> (bool * bool) -> iProp :=
        fun im_src im_tgt st_src '(l, f) =>
          (match w with
           | W_bot => ⌜l = false⌝ ** (OwnM (Excl.just tt: @URA.car (Excl.t unit)))
           | W_own th k o i => ⌜l = true /\ im_tgt (inl th) <= i⌝ ** own_thread th ** monoWhite k ge_PreOrder o
           | W_top => ⌜l = true /\ f = true⌝ ** (OwnM (Excl.just tt: @URA.car (Excl.t unit)))
           end).

  Lemma I_aux_fair_update w
        im_src im_tgt0 im_tgt1 tid ths st_src st_tgt
        (UPD: fair_update im_tgt0 im_tgt1 (sum_fmap_l (tids_fmap tid ths)))
    :
    (own_thread tid)
      -∗
      (I_aux w im_src im_tgt0 st_src st_tgt)
      -∗
      (own_thread tid ∗ I_aux w im_src im_tgt1 st_src st_tgt).
  Proof.
    iIntros "OWN INV". destruct w; try by iFrame.
    unfold I_aux. des_ifs. iDestruct "INV" as "[[% INV] ORD]".
    iPoseProof (thread_disjoint with "OWN INV") as "%".
    des. subst. iFrame. iPureIntro. split; auto.
    specialize (UPD (inl th)). unfold sum_fmap_l, tids_fmap in UPD.
    des_ifs; ss; lia.
  Qed.

  Let I: TIdSet.t -> (@imap void nat_wf) -> (@imap (sum_tid void) nat_wf) -> unit -> (bool * bool) -> iProp :=
        fun ths im_src im_tgt st_src st_tgt =>
          (own_threads ths)
            **
            ∃ w,
              (monoBlack 0 W_le_PreOrder w)
                **
                I_aux w im_src im_tgt st_src st_tgt.

  Lemma I_fair_update
        im_src im_tgt0 im_tgt1 tid ths st_src st_tgt
        (UPD: fair_update im_tgt0 im_tgt1 (sum_fmap_l (tids_fmap tid ths)))
    :
    (own_thread tid)
      -∗
      (I ths im_src im_tgt0 st_src st_tgt)
      -∗
      (own_thread tid ∗ I ths im_src im_tgt1 st_src st_tgt).
  Proof.
    unfold I.
    iIntros "OWN [THS INV]". iDestruct "INV" as (w) "[MONO INV]".
    iPoseProof (I_aux_fair_update with "OWN INV") as "[OWN INV]".
    { eauto. }
    iFrame. iExists _. iFrame.
  Qed.

  Lemma I_own_fair_update
        im_src im_tgt0 im_tgt1 tid ths st_src st_tgt
        (UPD: fair_update im_tgt0 im_tgt1 (sum_fmap_l (tids_fmap tid ths)))
        th k o0 i0
    :
    monoWhite 0 W_le_PreOrder (W_own th k o0 i0)
              -∗
              (own_thread tid)
              -∗
              (I ths im_src im_tgt0 st_src st_tgt)
              -∗
              #=> (∃ o1 i1, monoWhite 0 W_le_PreOrder (W_own th k o1 i1) ∗ ⌜prod_lt Peano.lt Peano.lt (o1, i1) (o0, i0)⌝ ∗ own_thread tid ∗ I ths im_src im_tgt1 st_src st_tgt).
  Proof.
    unfold I.
    iIntros "WHITE OWN [THS INV]". iDestruct "INV" as (w) "[MONO INV]".
    iPoseProof (black_white_compare with "WHITE MONO") as "%". inv H; ss.
    { guardH LE. destruct st_tgt. ss.
      iDestruct "INV" as "[[% INV] ORD]". des. subst.
      iPoseProof (thread_disjoint with "OWN INV") as "%".
      iPoseProof (threads_in with "THS OWN") as "%".
      admit.
    }
  Admitted.

  Lemma locked_after_own
        ths im_src im_tgt st_src st_tgt
        tid k o i
    :
    monoWhite 0 W_le_PreOrder (W_own tid k o i)
              -∗
              I ths im_src im_tgt st_src st_tgt
              -∗
              ⌜fst st_tgt = true⌝.
  Proof.
    destruct st_tgt. iIntros "WHITE INV".
    iEval (unfold I) in "INV". iDestruct "INV" as "[THS INV]".
    iDestruct "INV" as (w) "[MONO INV]".
    iPoseProof (black_white_compare with "WHITE MONO") as "%". inv H; ss.
    { iDestruct "INV" as "[[% ?] ?]". des; auto. }
    { iDestruct "INV" as "[[% ?] ?]". des; auto. }
  Qed.

  Lemma locked_after_top
        ths im_src im_tgt st_src st_tgt
    :
    monoWhite 0 W_le_PreOrder W_top
              -∗
              I ths im_src im_tgt st_src st_tgt
              -∗
              ⌜fst st_tgt = true /\ snd st_tgt = true⌝.
  Proof.
    destruct st_tgt. iIntros "WHITE INV".
    iEval (unfold I) in "INV". iDestruct "INV" as "[THS INV]".
    iDestruct "INV" as (w) "[MONO INV]".
    iPoseProof (black_white_compare with "WHITE MONO") as "%". inv H; ss.
    iDestruct "INV" as "[% _]". auto.
  Qed.

  Lemma I_stutter
        tid i ths
        im_src im_tgt0 im_tgt1 st_src st_tgt
        n n0 n1 k
        (LT: n1 < n0)
    :
    monoWhite 0 W_le_PreOrder (W_own tid k n i)
              -∗
              (OwnM (Excl.just tt: @URA.car (Excl.t unit)))
              -∗
              I ths im_src im_tgt0 st_src st_tgt
              -∗
              monoBlack k ge_PreOrder n0
              -∗
              #=>
              (OwnM (Excl.just tt: @URA.car (Excl.t unit))
                    **
                    I ths im_src im_tgt1 st_src st_tgt
                    **
                    monoBlack k ge_PreOrder n1).
  Proof.
    iIntros "WHITE OWN [THS [%w [MONO INV]]] ORD".
    iPoseProof (black_white_compare with "WHITE MONO") as "%".
    unfold I_aux. inv H; des_ifs.
    { iDestruct "INV" as "[[% TID] WHITE0]".
      iPoseProof (black_white_compare with "WHITE0 ORD") as "%".
      iPoseProof (black_updatable with "ORD") as "> ORD".
      { instantiate (1:=n1). lia. }
      iPoseProof (black_persistent_white with "ORD") as "# ORDWHITE".
      iPoseProof (black_updatable with "MONO") as "> MONO".
      { instantiate (1:=(W_own tid k n1 (im_tgt1 (inl tid)))).
        econs; eauto. left. lia.
      }
      iModIntro. unfold I. iFrame. iExists _. iFrame. iSplit; auto.
      iPureIntro. des; split; auto.
    }
    { iDestruct "INV" as "[% INV]".
        iCombine "OWN INV" as "OWN". iOwnWf "OWN". ur in H0. ss.
    }
  Qed.

  Lemma I_finish
        tid k n i
        ths im_src0 im_tgt0 st_src0 st_tgt0
        im_src1 im_tgt1 st_src1
    :
    (monoWhite 0 W_le_PreOrder (W_own tid k n i))
      -∗
      OwnM (Excl.just tt: @URA.car (Excl.t unit))
      -∗
      I ths im_src0 im_tgt0 st_src0 st_tgt0
      -∗
      #=>
      (I ths im_src1 im_tgt1 st_src1 (true, true)
         **
         own_thread tid
         **
         monoWhite 0 W_le_PreOrder W_top).
  Proof.
    iIntros "WHITE OWN [THS [%w [MONO INV]]]".
    iPoseProof (black_white_compare with "WHITE MONO") as "%".
    destruct st_tgt0. inv H; ss.
    { iClear "WHITE". iDestruct "INV" as "[[% TID] _]".
      iPoseProof (black_updatable with "MONO") as "> MONO".
      { instantiate (1:=W_top). econs. }
      iPoseProof (black_persistent_white with "MONO") as "#WHITE".
      iModIntro. iSplitL; auto. unfold I. iFrame.
      iExists W_top. ss. iFrame. auto.
    }
    { iDestruct "INV" as "[% INV]".
      iCombine "OWN INV" as "OWN". iOwnWf "OWN". ur in H0. ss.
    }
  Qed.

  Let srcE := ((@eventE void +' cE) +' sE unit).
  Let tgtE := ((@eventE void +' cE) +' sE (bool * bool)).

  Definition itop10 { T0 T1 T2 T3 T4 T5 T6 T7 T8 T9} (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) (x4: T4 x0 x1 x2 x3) (x5: T5 x0 x1 x2 x3 x4) (x6: T6 x0 x1 x2 x3 x4 x5) (x7: T7 x0 x1 x2 x3 x4 x5 x6) (x8: T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: T9 x0 x1 x2 x3 x4 x5 x6 x7 x8): iProp := True%I.

  Definition isim_gen tid r g R_src R_tgt Q (itr_src: itree srcE R_src) (itr_tgt: itree tgtE R_tgt): iProp :=
    ∀ ths im_src im_tgt0 st_src st_tgt im_tgt1,
      I ths im_src im_tgt0 st_src st_tgt
        -*
        ⌜fair_update im_tgt0 im_tgt1 (sum_fmap_l (tids_fmap tid ths))⌝
        -*
        isim tid I r g Q itr_src itr_tgt ths im_src im_tgt1 st_src st_tgt.

  Lemma sim: ModSim.mod_sim example_mod_spec example_mod.
  Proof.
    refine (@ModSim.mk _ _ nat_wf nat_wf _ _ Σ _ _ _).
    { econs. exact 0. }
    { i. exists (S o0). ss. }
    { instantiate (1:=liftI I). admit. }
    i. ss.

    cut (forall tid,
            own_thread tid ⊢ @isim_gen tid itop10 itop10 _ _ (fun r_src r_tgt ths im_src im_tgt st_src st_tgt =>
                                                                I ths im_src im_tgt st_src st_tgt
                                                                  ** own_thread tid
                                                                  ** ⌜r_src = r_tgt⌝)%I example_fun_spec example_fun).
    { admit. }

    unfold example_fun_spec, example_fun.
    unfold isim_gen. i. iIntros "TID".
    iIntros (ths im_src im_tgt0 st_src st_tgt im_tgt1) "INV %".
    iDestruct "INV" as "[THS INV]". iDestruct "INV" as (w) "[MONO INV]".
    destruct w.

    3:{
      unfold I_aux. des_ifs.
      iPoseProof (black_persistent_white with "MONO") as "#WHITE".
      iDestruct "INV" as "[% OWN]". des. subst.
      iApply isim_getR.
      ired. rewrite unfold_iter_eq. ired.

      admit.

      (* iApply isim_yieldR. iFrame. *)
      (* iIntros (? ? ? ? ? ?) "INV %". *)
      (* iPoseProof (I_fair_update with "TID INV") as "[TID INV]"; eauto. *)


      (* iApply isim_getR. ired. iApply isim_sync. *)
      (* iSplitR "TID". *)
      (* { unfold I. iFrame. iExists W_top. iFrame. auto. } *)
      (* iIntros (ths1 im_src1 im_tgt2 st_src1 st_tgt1 im_tgt3) "INV". *)
      (* iIntros. iApply isim_ret. *)
      (* iPoseProof (I_fair_update with "TID INV") as "[TID INV]"; eauto. *)
      (* iFrame. auto. *)
    }

    1:{
      iPoseProof (black_persistent_white with "MONO") as "#WHITE".
      unfold I_aux. des_ifs. iDestruct "INV" as "[% OWN]". subst.
      iApply isim_getR.

      iDestruct (monoBlack_alloc ge_PreOrder 6) as "-# > [%k ORD]".
      iPoseProof (black_updatable with "MONO") as "> MONO".
      { instantiate (1:=W_own tid k 6 (im_tgt1 (inl tid))). econs. }
      iClear "WHITE".
      iPoseProof (black_persistent_white with "MONO") as "#WHITE".

      iApply isim_putR.

      iApply isim_yieldR.
      iPoseProof (black_persistent_white with "ORD") as "# -# ORDWHITE".
      iSplitR "OWN ORD".
      { unfold I. iFrame. iExists (W_own _ _ _ _). iFrame.
        iSplit; auto.
      }
      iIntros (? ? ? ? ? ?) "INV %".

      iPoseProof (I_stutter with "WHITE OWN INV ORD") as "> [[OWN INV] ORD]".
      { eapply Nat.lt_succ_diag_r. }
      iApply isim_yieldR. iFrame.
      iIntros (? ? ? ? ? ?) "INV %".

      iPoseProof (locked_after_own with "WHITE INV") as "%".
      destruct st_tgt0. ss. subst.
      iApply isim_getR.

      iPoseProof (I_stutter with "WHITE OWN INV ORD") as "> [[OWN INV] ORD]".
      { eapply Nat.lt_succ_diag_r. }
      iApply isim_yieldR. iFrame.
      iIntros (? ? ? ? ? ?) "INV %".

      iPoseProof (I_stutter with "WHITE OWN INV ORD") as "> [[OWN INV] ORD]".
      { eapply Nat.lt_succ_diag_r. }
      iApply isim_yieldR. iFrame.
      iIntros (? ? ? ? ? ?) "INV %".

      iApply isim_putR.
      iPoseProof (I_finish with "WHITE OWN INV") as "> [[INV TID] TOP]".

      iApply isim_yieldR. iFrame.
      iIntros (? ? ? ? ? ?) "INV %".
      iPoseProof (I_fair_update with "TID INV") as "[TID INV]"; eauto.

      iApply isim_sync. iFrame.
      iIntros (? ? ? ? ? ?) "INV %".
      iPoseProof (I_fair_update with "TID INV") as "[TID INV]"; eauto.

      iApply isim_ret. iFrame. auto.
    }

    {
      iPoseProof (black_persistent_white with "MONO") as "#WHITE".
      unfold I_aux. des_ifs. iDestruct "INV" as "[[% OWN] MONOWHITE]". des. subst.
      iApply isim_getR.

      iStopProof.
      revert ths im_src st_src im_tgt0 im_tgt1 b0 th H1 H.
      pattern o, i. match goal with | |- ?f o i => change (f (fst (o, i)) (snd (o, i))) end.
      generalize (o, i) as oi. clear o i. intros oi.

      induction (prod_lt_well_founded Nat.lt_wf_0 Nat.lt_wf_0 oi). clear H. rename H0 into IH.
      i. destruct x as [o i]. subst.
      iIntros "[WHITE [TID [THS [MONO [OWN MONOWHITE]]]]]".

      iPoseProof (thread_disjoint with "TID OWN") as "%".
      iPoseProof (black_updatable with "MONO") as "> MONO".
      { ss. instantiate (1:= W_own th k o (im_tgt1 (inl th))). econs.
        specialize (H (inl th)).
        unfold sum_fmap_l, tids_fmap in H. des_ifs.
        { ss. lia. }
        { lia. }
      }
      iClear "WHITE".
      iPoseProof (black_persistent_white with "MONO") as "#WHITE".

      rewrite unfold_iter_eq. ired.

      admit.

      (* iApply isim_getR. destruct b0. *)
      (* { ired. *)
      (*   iApply isim_sync. *)
      (*   iSplitR "TID". *)
      (*   { unfold I. iFrame. iExists (W_own _ _ _ _). iFrame. iPureIntro. auto. } *)
      (*   iIntros (ths1 im_src1 im_tgt2 st_src1 st_tgt1 im_tgt3) "INV". *)
      (*   iIntros. iApply isim_ret. iSplitL; auto. *)
      (*   iPoseProof (I_fair_update with "TID INV") as "[TID INV]"; eauto. *)
      (*   iFrame. *)
      (* } *)
      (* { ired. iPoseProof (threads_in with "THS OWN") as "%". *)
      (*   iApply isim_yieldR. *)
      (*   { iSplitR "TID". *)
      (*     { unfold I. iFrame. iExists (W_own _ _ _ _). iFrame. iPureIntro. auto. } *)
      (*     iIntros (ths1 im_src1 im_tgt2 st_src1 st_tgt1 im_tgt3) "INV". *)
      (*     iIntros. iApply isim_tauR. *)
      (*     iDestruct "INV" as "[THS INV]". iDestruct "INV" as (w) "[MONO INV]". *)
      (*     destruct st_tgt1 as [l f]. ss. *)
      (*     iPoseProof (black_white_compare with "WHITE MONO") as "%". *)
      (*     inv H4. *)
      (*     { guardH LE. iDestruct "INV" as "[[% OWN] MONOWHITE]". des. subst. *)
      (*       iPoseProof (threads_in with "THS OWN") as "%". *)
      (*       iApply IH. *)
      (*       3:{ eauto. } *)
      (*       2:{ instantiate (1:=(o0, _)). simpl. eauto. } *)
      (*       { inv LE. *)
      (*         { left. auto. } *)
      (*         { des. right. *)
      (*           { lia. } *)
      (*           { cut (im_tgt1 (inl th) < im_tgt0 (inl th)). *)
      (*             { lia. } *)
      (*             specialize (H (inl th)). unfold sum_fmap_l, tids_fmap in H. *)
      (*             des_ifs. *)
      (*           } *)
      (*         } *)
      (*       } *)
      (*       iClear "WHITE". *)
      (*       iPoseProof (black_persistent_white with "MONO") as "#WHITE". *)
      (*       iFrame. auto. *)
      (*     } *)
      (*     { iDestruct "INV" as "[% INV]". des. subst. *)
      (*       rewrite unfold_iter_eq. ired. *)
      (*       iApply isim_getR. ired. *)
      (*       iApply isim_sync. iSplitR "TID". *)
      (*       { unfold I. iFrame. iExists W_top. iFrame. auto. } *)
      (*       { iIntros (? ? ? ? ? ?) "INV %". *)
      (*         iApply isim_ret. *)
      (*         iPoseProof (I_fair_update with "TID INV") as "[TID INV]"; eauto. *)
      (*         iFrame. auto. *)
      (*       } *)
      (*     } *)
      (*   } *)
      (* } *)
    }
  Admitted.
End SIM.
