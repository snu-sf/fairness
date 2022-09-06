From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Export ITreeLib WFLib FairBeh NatStructs Mod pind.

Set Implicit Arguments.

(* TODO: move it to ITreeLib *)
Lemma unfold_iter_eq A E B
  : forall (f : A -> itree E (A + B)) (x : A),
    ITree.iter f x = lr <- f x;; match lr with
                                 | inl l => Tau (ITree.iter f l)
                                 | inr r0 => Ret r0
                                 end.
Proof.
  i. eapply bisim_is_eq. eapply unfold_iter.
Qed.


Section MOD.
  Definition example_fun:
    itree (((@eventE void) +' cE) +' sE (bool * bool)) Val :=
    '(l0, f0) <- trigger (@Get _);;
    if (l0: bool)
    then
      ITree.iter
        (fun (_: unit) =>
           '(l, f) <- trigger (Get _);;
           if (f: bool)
           then
             Ret (inr tt)
           else
             trigger Yield;;;
             Ret (inl tt)) tt;;;
      trigger Yield;;;
      Ret 0
    else
      trigger (Put (true, f0));;;
      trigger Yield;;;
      '(l1, _) <- trigger (@Get _);;
      trigger (Put (l1, true));;;
      Ret 0
  .

  Definition example_mod: Mod.t :=
    Mod.mk
      (false, false)
      (fun _ => Some (fun _ => example_fun))
  .

  Definition example_fun_spec:
    itree (((@eventE void) +' cE) +' sE unit) Val :=
    trigger Yield;;;
    Ret 0
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
    | W_own (th: thread_id) (i: nat)
    | W_top
  .

  Variant W_le: W -> W -> Prop :=
    | W_le_bot
        w
      :
      W_le W_bot w
    | W_le_th
        th i0 i1
        (LE: i0 <= i1)
      :
      W_le (W_own th i1) (W_own th i0)
    | W_le_top
        w
      :
      W_le w W_top
  .

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
           | W_own th i => ⌜l = true /\ im_tgt (inl th) <= i⌝ ** own_thread th
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
    unfold I_aux. des_ifs. iDestruct "INV" as "[% INV]".
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
      iApply isim_getR. ired. iApply isim_sync.
      iSplitR "TID".
      { unfold I. iFrame. iExists W_top. iFrame. auto. }
      iIntros (ths1 im_src1 im_tgt2 st_src1 st_tgt1 im_tgt3) "INV".
      iIntros. iApply isim_ret.
      iPoseProof (I_fair_update with "TID INV") as "[TID INV]"; eauto.
      iFrame. auto.
    }

    1:{
      iPoseProof (black_persistent_white with "MONO") as "#WHITE".
      unfold I_aux. des_ifs. iDestruct "INV" as "[% OWN]". subst.
      iApply isim_getR. iApply isim_putR.
      iPoseProof (black_updatable with "MONO") as "> MONO".
      { instantiate (1:=W_own tid (im_tgt1 (inl tid))). econs. }
      iClear "WHITE".
      iPoseProof (black_persistent_white with "MONO") as "#WHITE".
      iApply isim_sync. iSplitR "OWN".
      { unfold I. iFrame. iExists (W_own tid _). iFrame. auto. }
      iIntros (ths1 im_src1 im_tgt2 st_src1 st_tgt1 im_tgt3) "INV %".
      iEval (unfold I) in "INV". iDestruct "INV" as "[THS INV]".
      iDestruct "INV" as (w) "[MONO INV]".
      iPoseProof (black_white_compare with "WHITE MONO") as "%". inv H1.
      { iApply isim_getR. des_ifs. iApply isim_putR.
        iPoseProof (black_updatable with "MONO") as "> MONO".
        { instantiate (1:=W_top). econs. }
        iApply isim_ret. iFrame. iSplitL; auto.
        iDestruct "INV" as "[% TID]". des.
        iFrame. iExists W_top. iFrame. auto.
      }
      { unfold I_aux. des_ifs. iDestruct "INV" as "[% INV]".
        iCombine "OWN INV" as "OWN". iOwnWf "OWN". ur in H2. ss.
      }
    }

    {
      iPoseProof (black_persistent_white with "MONO") as "#WHITE".
      unfold I_aux. des_ifs. iDestruct "INV" as "[% OWN]". des. subst.
      iApply isim_getR.

      iStopProof.
      revert ths im_src st_src im_tgt0 im_tgt1 b0 th H1 H.
      induction (Nat.lt_wf_0 i). clear H. rename H0 into IH.
      i. subst.
      iIntros "[WHITE [TID [THS [MONO OWN]]]]".

      iPoseProof (thread_disjoint with "TID OWN") as "%".
      iPoseProof (black_updatable with "MONO") as "> MONO".
      { instantiate (1:= W_own th (im_tgt1 (inl th))). econs.
        specialize (H (inl th)).
        unfold sum_fmap_l, tids_fmap in H. des_ifs.
        { ss. lia. }
        { lia. }
      }
      iClear "WHITE".
      iPoseProof (black_persistent_white with "MONO") as "#WHITE".

      rewrite unfold_iter_eq. ired.
      iApply isim_getR. destruct b0.
      { ired.
        iApply isim_sync.
        iSplitR "TID".
        { unfold I. iFrame. iExists (W_own _ _). iFrame. iPureIntro. auto. }
        iIntros (ths1 im_src1 im_tgt2 st_src1 st_tgt1 im_tgt3) "INV".
        iIntros. iApply isim_ret. iSplitL; auto.
        iPoseProof (I_fair_update with "TID INV") as "[TID INV]"; eauto.
        iFrame.
      }
      { ired. iPoseProof (threads_in with "THS OWN") as "%".
        iApply isim_yieldR.
        { iSplitR "TID".
          { unfold I. iFrame. iExists (W_own _ _). iFrame. iPureIntro. auto. }
          iIntros (ths1 im_src1 im_tgt2 st_src1 st_tgt1 im_tgt3) "INV".
          iIntros. iApply isim_tauR.
          iDestruct "INV" as "[THS INV]". iDestruct "INV" as (w) "[MONO INV]".
          destruct st_tgt1 as [l f]. ss.
          iPoseProof (black_white_compare with "WHITE MONO") as "%".
          inv H4.
          { iDestruct "INV" as "[% OWN]". des. subst.
            iPoseProof (threads_in with "THS OWN") as "%".
            iApply IH.
            3:{ eauto. }
            2:{ eauto. }
            { cut (im_tgt1 (inl th) < im_tgt0 (inl th)).
              { lia. }
              specialize (H (inl th)). unfold sum_fmap_l, tids_fmap in H.
              des_ifs.
            }
            iClear "WHITE".
            iPoseProof (black_persistent_white with "MONO") as "#WHITE".
            iFrame. auto.
          }
          { iDestruct "INV" as "[% INV]". des. subst.
            rewrite unfold_iter_eq. ired.
            iApply isim_getR. ired.
            iApply isim_sync. iSplitR "TID".
            { unfold I. iFrame. iExists W_top. iFrame. auto. }
            { iIntros (? ? ? ? ? ?) "INV %".
              iApply isim_ret.
              iPoseProof (I_fair_update with "TID INV") as "[TID INV]"; eauto.
              iFrame. auto.
            }
          }
        }
      }
    }
  Admitted.
End SIM.
