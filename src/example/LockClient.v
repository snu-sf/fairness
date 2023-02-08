From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
Unset Universe Checking.
From Fairness Require Export
     ITreeLib WFLib FairBeh NatStructs Mod pind Axioms
     OpenMod WMM Red IRed Wrapper WeakestAdequacy FairLock Concurrency.
From PromisingLib Require Import Loc Event.
From PromisingSEQ Require Import TView.
From Ordinal Require Export ClassicalHessenberg.
Require Import Coq.Numbers.BinNums.


Set Implicit Arguments.

Section INIT.

  Definition loc_X: Loc.t := Loc.of_nat 2.

  Definition const_0: Const.t := Const.of_Z (BinIntDef.Z.of_nat 0).
  Definition const_42: Const.t := Const.of_Z (BinIntDef.Z.of_nat 42).

End INIT.

Module ClientImpl.

  Definition thread1:
    ktree ((((@eventE void) +' cE) +' (sE unit)) +' OpenMod.callE) unit unit
    :=
    fun _ =>
      let tvw := TView.bot in
      tvw <- (OMod.call "lock" (tvw: TView.t));;
      tvw <- (OMod.call "store" (tvw: TView.t, loc_X, const_42, Ordering.plain));;
      `tvw: TView.t <- (OMod.call "unlock" (tvw: TView.t));;
      _ <- trigger Yield;;
      Ret tt.

  Definition thread2:
    ktree ((((@eventE void) +' cE) +' (sE unit)) +' OpenMod.callE) unit unit
    :=
    fun _ =>
      let tvw := TView.bot in
      val_x <- ITree.iter
                (fun (tvw: TView.t) =>
                   tvw <- (OMod.call "lock" (tvw: TView.t));;
                   '(tvw, x) <- (OMod.call "load" (tvw: TView.t, loc_X, Ordering.plain));;
                   `tvw: TView.t <- (OMod.call "unlock" (tvw: TView.t));;
                         b <- unwrap (Const.eqb const_0 x);;
                         if (b: bool) then Ret (inl tvw) else Ret (inr x)) tvw;;
      b <- unwrap (Const.eqb const_42 val_x);;
      if (b: bool) then
        _ <- trigger Yield;;
        _ <- trigger (Observe 0 [42]);;
        _ <- trigger Yield;;
        Ret tt
      else UB.

  Definition omod: OMod.t :=
    OMod.mk
      tt
      (Mod.get_funs [("thread1", Mod.wrap_fun thread1);
                     ("thread2", Mod.wrap_fun thread2)])
  .

  Definition mod: Mod.t :=
    OMod.close
      (omod)
      (ModAdd WMem.mod AbsLockW.mod)
  .

End ClientImpl.

Module ClientSpec.
  Definition thread1:
    ktree ((((@eventE void) +' cE) +' (sE unit))) unit unit
    :=
    fun _ =>
      _ <- trigger Yield;; Ret tt.

  Definition thread2:
    ktree ((((@eventE void) +' cE) +' (sE unit))) unit unit
    :=
    fun _ =>
      _ <- trigger Yield;;
      _ <- trigger (Observe 0 [42]);;
      _ <- trigger Yield;;
      Ret tt.

  Definition mod: Mod.t :=
    Mod.mk
      tt
      (Mod.get_funs [("thread1", Mod.wrap_fun thread1);
                     ("thread2", Mod.wrap_fun thread2)])
  .

End ClientSpec.



From Fairness Require Import
     IProp IPM Weakest ModSim PCM MonotonePCM StateRA FairRA.

Section LEMMA.

  Context `{Σ: GRA.t}.
  Variable A: Type.
  Context `{EXCL: @GRA.inG (Excl.t A) Σ}.

  Lemma excl_unique
        a0 a1
    :
    (OwnM (Excl.just a0: Excl.t A))
      -∗
      (OwnM (Excl.just a1: Excl.t A))
      -∗
      ⌜False⌝%I.
  Proof.
    iIntros "I1 I2". iCombine "I1 I2" as "C". iPoseProof (OwnM_valid with "C") as "%C". exfalso. ur in C. ss.
  Qed.

End LEMMA.

Section SIM.

  Context `{Σ: GRA.t}.

  Context `{MONORA: @GRA.inG monoRA Σ}.
  Context `{THDRA: @GRA.inG ThreadRA Σ}.
  Context `{STATESRC: @GRA.inG (stateSrcRA (unit)) Σ}.
  Context `{STATETGT: @GRA.inG (stateTgtRA ((OMod.closed_state ClientImpl.omod (ModAdd (WMem.mod) AbsLockW.mod)))) Σ}.
  Context `{IDENTSRC: @GRA.inG (identSrcRA (void)) Σ}.
  Context `{IDENTTGT: @GRA.inG (identTgtRA (OMod.closed_ident ClientImpl.omod (ModAdd (WMem.mod) AbsLockW.mod))%type) Σ}.

  Context `{OBLGRA: @GRA.inG ObligationRA.t Σ}.
  Context `{ARROWRA: @GRA.inG (ArrowRA (OMod.closed_ident ClientImpl.omod (ModAdd (WMem.mod) AbsLockW.mod))%type) Σ}.
  Context `{EDGERA: @GRA.inG EdgeRA Σ}.
  Context `{ONESHOTSRA: @GRA.inG (@FiniteMap.t (OneShot.t unit)) Σ}.

  Context `{WMEMRA: @GRA.inG wmemRA Σ}.

  Context `{EXCL: @GRA.inG (Excl.t unit) Σ}.
  Context `{EXCL2: @GRA.inG (Excl.t (unit * unit)) Σ}.
  Context `{ONESHOTRA: @GRA.inG (OneShot.t nat) Σ}.
  Context `{REGIONRA: @GRA.inG (Region.t (thread_id * nat)) Σ}.
  Context `{CONSENTRA: @GRA.inG (@FiniteMap.t (Consent.t nat)) Σ}.
  Context `{AUTHNRA: @GRA.inG (Auth.t (Excl.t nat)) Σ}.
  Context `{AUTHVWRA: @GRA.inG (Auth.t (Excl.t TView.t)) Σ}.
  Context `{AUTHVWRA2: @GRA.inG (Auth.t (Excl.t (TView.t * unit))) Σ}.
  Context `{AUTHNMNRA: @GRA.inG (Auth.t (NatMapRA.t nat)) Σ}.

  Definition thread1_will_write (tvw: TView.t) : iProp :=
    ∃ k, (∃ n, ObligationRA.black k n)
           ∗
           (ObligationRA.correl_thread k 1%ord)
           ∗
           (OwnM (OneShot.shot k))
           ∗
           ((ObligationRA.pending k (/2)%Qp ∗ wpoints_to loc_X const_0 tvw)
            ∨
              (ObligationRA.shot k ∗ wpoints_to loc_X const_42 tvw)).

  Definition o_w_cor: Ord.t := (Ord.omega × Ord.omega)%ord.

  Definition lock_will_unlock : iProp :=
    ∃ (own: bool) (tvw: TView.t) (ing: bool) (mem: WMem.t) (wobl: NatMap.t nat) (j: nat),
      (OwnM (Auth.black (Some wobl: NatMapRA.t nat)))
        ∗
        ((OwnM (Auth.black (Excl.just j: Excl.t nat)))
        ∗ (OwnM (Auth.black (Excl.just (tvw, tt): Excl.t (TView.t * unit)%type))))
        ∗
        (wmemory_black mem)
        ∗
        (St_tgt (tt, (mem, (((own, tvw), ing), key_set wobl))))
        ∗
        (FairRA.blacks (fun id => exists t, (id = (inr (inr (inr t)))) /\ (~ NatMap.In t wobl)))
        ∗
        (natmap_prop_sum wobl
                         (fun tid idx =>
                            (own_thread tid)
                              ∗
                              (ObligationRA.correl (inr (inr (inr tid))) idx o_w_cor)
                              ∗
                              (ObligationRA.pending idx 1)
                              ∗
                              (ObligationRA.duty (inr (inr (inr tid))) [(idx, o_w_cor)])
        ))
        ∗
        (
          ((⌜own = false⌝)
             ∗ (OwnM (Auth.white (Excl.just j: Excl.t nat)))
             (* points_to view *)
             ∗ (OwnM (Auth.white (Excl.just tvw: Excl.t TView.t)))
             (* argument-passing view *)
             ∗ (OwnM (Auth.white (Excl.just (tvw, tt): Excl.t (TView.t * unit)%type)))
             ∗ (OwnM (Excl.just tt: Excl.t unit))
          )
          ∨
            ((⌜own = true⌝)
               ∗ (ObligationRA.pending j 1)
               ∗ (ObligationRA.black j o_w_cor)
               ∗ (ObligationRA.correl_thread j 1%ord)
               ∗ (natmap_prop_sum wobl (fun _ idx => ObligationRA.amplifier j idx 1%ord))
            )
        )
        ∗
        (
          ((⌜ing = false⌝)
             ∗ (OwnM (Excl.just (tt, tt): Excl.t (unit * unit)%type))
          )
          ∨
            ((⌜ing = true⌝)
               ∗ (OwnM (Excl.just tt: Excl.t unit))
            (* ∗ (OwnM (Auth.white (Excl.just j: Excl.t nat))) *)
            (* ∗ (∃ tvw', (OwnM (Auth.white (Excl.just tvw': Excl.t TView.t))) ∗ (⌜TView.le tvw tvw'⌝)) *)
            )
        )
  .

  Let I: list iProp :=
        [(∃ tvw, (OwnM (Auth.black (Excl.just tvw: Excl.t TView.t)))
                   ∗ (thread1_will_write tvw))%I;
         lock_will_unlock].

  Lemma AbsLock_lock
        R_src R_tgt tid
        (src: thread void (sE unit) R_src)
        tgt
        r g
        (Q: R_src -> R_tgt -> iProp)
        (l: list (nat * Ord.t)%type)
        (num_line: nat)
        (tvw0: TView.t)
    :
    ((own_thread tid)
       ∗
       (ObligationRA.duty (inl tid) l)
       ∗
       (ObligationRA.taxes
          l ((((Ord.omega × Ord.omega) × Ord.omega)
                ⊕
                ((Ord.S Ord.O) × (o_w_cor)))
               ⊕ 9)%ord))
      ∗
      (∀ tvw1,
          ((⌜TView.le tvw0 tvw1⌝)
             ∗
             (own_thread tid)
             ∗
             (∃ j, (ObligationRA.duty (inl tid) ((j, Ord.S Ord.O) :: l))
                     ∗
                     (ObligationRA.white j (Ord.omega × (Ord.from_nat num_line))%ord)
                     ∗
                     (OwnM (Auth.white (Excl.just j: Excl.t nat)))
             )
             ∗
             (∃ tvw,
                 (OwnM (Auth.white (Excl.just tvw: Excl.t TView.t)))
                   ∗ (OwnM (Auth.white (Excl.just (tvw, tt): Excl.t (TView.t * unit))))
                   ∗ (⌜(TView.le tvw tvw1)⌝)
             )
             ∗
             (OwnM (Excl.just tt: Excl.t unit))
          )
            -∗
            (stsim I tid (topset I) r g Q
                   false false
                   (trigger Yield;;; src)
                   (tgt tvw1)))
      ⊢
      (stsim I tid (topset I) r g Q
             false false
             (trigger Yield;;; src)
             (tvw' <- (OMod.close_itree ClientImpl.omod (ModAdd (WMem.mod) AbsLockW.mod) (R:=TView.t) (OMod.call "lock" tvw0));; (tgt tvw'))).
  Proof.
    iIntros "[[TH [DUTY TAXES]] SIM]".
    rewrite close_itree_call. ss. rred.
    iPoseProof (ObligationRA.taxes_ord_split_one with "TAXES") as "TAXES".
    { eapply Hessenberg.lt_add_r. apply OrdArith.lt_from_nat. instantiate (1:=8). auto. }
    iMod "TAXES". iDestruct "TAXES" as "[TAXES TAX]".

    iApply (stsim_yieldR with "[DUTY TAX]"). msubtac. iFrame.
    iIntros "DUTY _". rred.
    unfold AbsLockW.lock_fun, Mod.wrap_fun. rred.
    iPoseProof (ObligationRA.taxes_ord_split_one with "TAXES") as "TAXES".
    { eapply Hessenberg.lt_add_r. apply OrdArith.lt_from_nat. instantiate (1:=7). auto. }
    iMod "TAXES". iDestruct "TAXES" as "[TAXES TAX]".

    iApply (stsim_yieldR with "[DUTY TAX]"). msubtac. iFrame.
    iIntros "DUTY _". rred.
    iApply stsim_tauR. rred.
    iApply stsim_tidR. rred. iApply stsim_tauR. rred.
    iopen 1 "I1" "K1". do 6 (iDestruct "I1" as "[% I1]").
    iDestruct "I1" as "[B1 [B2 [MEM [STGT I1]]]]".
    iApply stsim_getR. iSplit. iFrame. rred.
    iApply stsim_tauR. rred.
    iApply stsim_getR. iSplit. iFrame. rred.
    iApply stsim_tauR. rred.
    iApply stsim_getR. iSplit. iFrame. rred.
    iApply (stsim_putR with "STGT"). iIntros "STGT". rred.
    iApply stsim_tauR. rred.

    iPoseProof (ObligationRA.alloc
                  (((Ord.omega × Ord.omega) × Ord.omega)
                     ⊕ ((Ord.S Ord.O) × (o_w_cor)))%ord) as "A".
    iMod "A" as "[% [[MYB MYW] PEND]]".
    iPoseProof (ObligationRA.white_split_eq with "MYW") as "[MYW YOUW]".
    iDestruct "I1" as "[BLKS [SUM [CASES INGS]]]".

    iAssert (⌜~ NatMap.In tid wobl⌝)%I as "%".
    { iAssert (⌜(NatMap.In tid wobl)⌝ ∨ ⌜(~ NatMap.In tid wobl)⌝)%I as "%".
      { iPureIntro. pose NatMapP.F.In_dec. specialize (s _ wobl tid). destruct s; auto. }
      destruct H as [IN | NI].
      2: auto.
      iPoseProof (natmap_prop_sum_impl with "SUM") as "SUM".
      { instantiate (1:= fun tid0 idx => own_thread tid0). i. iIntros "[F1 F2]". iFrame. }
      apply NatMapP.F.in_find_iff in IN.
      destruct (NatMap.find tid wobl) eqn:FIND; ss.
      iPoseProof (natmap_prop_sum_in with "SUM") as "TH2". eauto.
      iPoseProof (own_thread_unique with "TH TH2") as "F". iPure "F" as F. ss.
    }

    (* update ObligationRA.duty: get [] by black_to_duty, update with MYW; then correl *)
    set (blks2 := 
           (λ id : nat + (OMod.ident ClientImpl.omod + (Mod.ident (WMem.mod) + NatMap.key)),
               (∃ t : NatMap.key, id = inr (inr (inr t)) ∧ ¬ NatMap.In (elt:=nat) t (NatMap.add tid k wobl))%type)).
    iPoseProof (FairRA.blacks_unfold with "BLKS") as "[BLKS MYDUTY]".
    { instantiate (1:=inr (inr (inr tid))). instantiate (1:=blks2). i. des.
      { subst blks2. ss. des. esplits; eauto. ii; apply IN0. apply NatMapP.F.add_in_iff; auto. }
      { subst blks2. ss. esplits; eauto. }
    }
    { subst blks2. ss. ii. des. clarify. apply H1. apply NatMapP.F.add_in_iff. auto. }
    iPoseProof (black_to_duty with "MYDUTY") as "MYDUTY".
    iPoseProof (ObligationRA.duty_alloc with "MYDUTY") as "MYDUTY".
    iPoseProof ("MYDUTY" with "MYW") as "> MYDUTY".
    iPoseProof (ObligationRA.duty_correl with "MYDUTY") as "# MYCOR".
    { ss. left; eauto. }

    (* make (Auth.white singleton tid k) and update wobl *)
    iPoseProof (OwnM_Upd with "B1") as "OWN1".
    { eapply Auth.auth_alloc. instantiate (1:=NatMapRA.singleton tid k).
      instantiate (1:=Some (NatMap.add tid k wobl)). eapply NatMapRA.add_local_update.
      eapply NatMapP.F.not_find_in_iff; auto.
    }
    iMod "OWN1" as "[OWNB1 MYSING]".

    (* need to make amp; need ObligationRA.black j *)
    iAssert (
        (
  (⌜own = false⌝ **
               (OwnM (Auth.white (Excl.just j: Excl.t nat))
                     ** (OwnM (Auth.white (Excl.just tvw: Excl.t TView.t))
                     ** (OwnM (Auth.white (Excl.just (tvw, tt): Excl.t (TView.t * unit))) ** OwnM (Excl.just tt: Excl.t unit)))
  ))
   ∨ (⌜own = true⌝ **
               (ObligationRA.pending j 1 **
                (ObligationRA.black j o_w_cor **
                 (ObligationRA.correl_thread j 1 **
            natmap_prop_sum wobl (λ _ idx : nat, ObligationRA.amplifier j idx 1))))))
    ∗
    #=( ObligationRA.edges_sat )=>((⌜own = true⌝) -∗ (ObligationRA.amplifier j k 1))
      )%I
      with "[CASES YOUW]" as "[CASES AMP]".
    { iDestruct "CASES" as "[OWNF | [OT [PEND [JBLK [JCOR ALLAMP]]]]]".
      { iDestruct "OWNF" as "[% OW]". iSplitL "OW". iLeft. iFrame. auto.
        iModIntro. iIntros "OT". iPure "OT" as OT. clarify.
      }
      iPoseProof ("JBLK") as "# JBLK". iSplitR "YOUW".
      { iRight. iFrame. auto. }
      iPoseProof (ObligationRA.amplifier_intro with "JBLK") as "AMP".
      iPoseProof ("AMP" with "YOUW") as "AMP2". iMod "AMP2". iModIntro.
      iIntros "OT". iFrame.
    }
    iMod "AMP".

    (* now close invariant *)
    iMod ("K1" with "[TH OWNB1 B2 MEM SUM CASES INGS STGT PEND BLKS MYDUTY MYCOR AMP]") as "_".
    { unfold lock_will_unlock. iExists own, tvw, ing, mem, (NatMap.add tid k wobl), j. iFrame.
      rewrite key_set_pull_add_eq. iFrame. iSplitL "SUM TH MYDUTY MYCOR PEND".
      { iApply (natmap_prop_sum_add with "SUM"). iFrame. auto. }
      iDestruct "CASES" as "[OWNF | [OT [PEND [JBLK [JCOR ALLAMP]]]]]". iFrame.
      iRight. iPure "OT" as OT. iFrame. iSplit; auto.
      iApply (natmap_prop_sum_add with "ALLAMP"). iApply "AMP". auto.
    }
    { msubtac. }

    (* induction *)
    rred. iApply stsim_discard.
    { instantiate (1:=topset I). msubtac. }
    remember (((Ord.omega × Ord.omega) × Ord.omega)
                ⊕ Ord.S Ord.O × o_w_cor)%ord as wd.
    iPoseProof (ObligationRA.taxes_ord_split_one with "TAXES") as "> [TAXES TAXKEEP]".
    { instantiate (1:= (wd ⊕ 6)%ord). apply Hessenberg.lt_add_r.
      apply OrdArith.lt_from_nat. lia.
    }
    remember (wd ⊕ 6)%ord as credit.
    assert (RICH: (wd < credit)%ord).
    { subst; apply Hessenberg.add_lt_l. rewrite <- Ord.from_nat_O.
      apply OrdArith.lt_from_nat. lia.
    }
    clear Heqwd Heqcredit.
    clear own mem blks2 j H wobl. iClear "MYCOR".
    iStopProof. revert l k credit RICH. pattern wd. revert wd.
    apply (well_founded_induction Ord.lt_well_founded). intros wd IH. intros l k credit RICH.
    iIntros "[SIM [DUTY [MYB [MYW [TAXES TAXKEEP]]]]]".
    rewrite OpenMod.unfold_iter. rred.

    iPoseProof (ObligationRA.taxes_ord_split_one with "TAXES") as "> [TAXES TAX]". eauto.
    iApply (stsim_yieldR with "[DUTY TAX]"). msubtac. iFrame.
    iIntros "DUTY WTH". rred.
    iApply stsim_tauR. rred.
    iopen 1 "I1" "K1". do 6 (iDestruct "I1" as "[% I1]").
    iDestruct "I1" as "[B1 [B2 [MEM [STGT I1]]]]".
    iApply stsim_getR. iSplit. iFrame. rred.
    iApply stsim_tauR. rred. destruct own.

    (* someone is holding the lock *)
    { rred. iApply stsim_tauR. rred.

      iAssert (⌜NatMap.find tid wobl = Some k⌝)%I as "%".
      { iPoseProof (OwnM_valid with "[MYW B1]") as "%".
        { instantiate (1:= (Auth.black (Some wobl: NatMapRA.t nat)) ⋅ (Auth.white (NatMapRA.singleton tid k: NatMapRA.t nat))). iSplitL "B1"; iFrame. }
        eapply Auth.auth_included in H. eapply NatMapRA.extends_singleton_iff in H.
        auto.
      }
      rename H into FIND.

      iDestruct "I1" as "[BLKS [SUM [CASES INGS]]]".
      iDestruct "CASES" as "[[%OWNF [LOCK EXCL]] | [%OWNT [JPEND [JBLK [#JCOR AMPs]]]]]".
      { inversion OWNF. }

      (* induction *)
      { iAssert (ObligationRA.amplifier j k 1)%I with "[AMPs]" as "#AMP".
        { iPoseProof (natmap_prop_remove_find with "AMPs") as "[# AMP AMPs]".
          { eapply FIND. }
          auto.
        }
        iPoseProof (ObligationRA.correl_thread_correlate with "JCOR WTH") as "> DEC".
        iDestruct "DEC" as "[DEC | DONE]"; cycle 1.
        { iPoseProof (ObligationRA.pending_not_shot with "JPEND DONE") as "CONTRA". auto. }
        { iPoseProof (ObligationRA.amplifier_amplify with "AMP DEC") as "> DEC".
          iPoseProof (ObligationRA.black_white_decr with "MYB DEC") as "> [% [MYB %]]".
          assert (RENEW: (o2 < wd)%ord).
          { eapply Ord.lt_le_lt. 2: eauto. apply Hessenberg.add_lt_l.
            rewrite <- Ord.from_nat_O. rewrite <- Jacobsthal.mult_from_nat.
            apply OrdArith.lt_from_nat. ss.
          }
          iMod ("K1" with "[B1 B2 MEM STGT BLKS SUM JPEND JBLK AMPs INGS]") as "_".
          { unfold lock_will_unlock. iExists true, tvw1, ing0, mem, wobl, j. iFrame.
            iRight. iFrame. iSplit; auto.
          }
          { msubtac. }
          iApply IH. eapply RENEW. eapply RENEW.
          iFrame.
        }
      }
    }

    (* no one is holding the lock *)
    { rred.
      iClear "TAXES". clear IH credit RICH.
      iApply stsim_getR. iSplit. iFrame. rred.
      iApply stsim_tauR. rred.
      iDestruct "I1" as "[BLKS [SUM [[[%VW [LOCK EXCL]] | [%CONTRA _]] INGS]]]".
      2:{ inversion CONTRA. }
      inv VW.
      iDestruct "INGS" as "[[%INGF INGEX] | [_ CONTRA]]".
      2:{ iDestruct "EXCL" as "[_ [_ EXCL]]". iPoseProof (excl_unique with "EXCL CONTRA") as "%C". inv C. }
      subst. rred.

      iApply stsim_chooseR. iIntros "%". destruct x. rename x into tvw'. rred.
      iApply stsim_tauR. rred.
      iApply stsim_getR. iSplit. iFrame. rred.
      iApply stsim_tauR. rred.
      iApply stsim_getR. iSplit. iFrame. rred.
      iApply (stsim_putR with "STGT"). iIntros "STGT". rred.
      iApply stsim_tauR. rred.

      iAssert (⌜NatMap.find tid wobl = Some k⌝)%I as "%".
      { iPoseProof (OwnM_valid with "[MYW B1]") as "%".
        { instantiate (1:= (Auth.black (Some wobl: NatMapRA.t nat)) ⋅ (Auth.white (NatMapRA.singleton tid k: NatMapRA.t nat))). iSplitL "B1"; iFrame. }
        eapply Auth.auth_included in H. eapply NatMapRA.extends_singleton_iff in H.
        auto.
      }
      rename H into FIND.

      iPoseProof (natmap_prop_remove_find with "SUM") as "[[MYTH [_ [MYPEND MYDUTY]]] SUM]".
      eapply FIND. iPoseProof (ObligationRA.pending_shot with "MYPEND") as "> MYDONE".
      iPoseProof (ObligationRA.duty_done with "MYDUTY MYDONE") as "> MYDUTY".
      iApply (stsim_fairR with "[MYDUTY]").
      4:{ instantiate (1:=[(inr (inr tid), [])]). ss. iFrame. }
      { clear. i. unfold sum_fmap_r in *. des_ifs. ss. auto. }
      { instantiate (1:= List.map (fun '(j, _) => inr (inr j)) (NatMap.elements (NatMap.remove tid (key_set wobl)))). clear. i. unfold sum_fmap_r.
        assert (A: exists j, (i = inr (inr j)) /\ (NatMap.In j (NatMap.remove tid (key_set wobl)))).
        { apply in_map_iff in IN. des. des_ifs. destruct u. esplits; eauto.
          remember (NatMap.remove tid (key_set wobl)) as M. clear HeqM.
          apply NatMapP.F.elements_in_iff. exists (). apply SetoidList.InA_alt.
          exists (k, ()). ss.
        }
        des. subst. des_ifs. apply in_map_iff in IN. des. des_ifs. destruct u.
        eapply SetoidList.In_InA in IN0. eapply NatMap.elements_2 in IN0.
        apply NatMapP.F.remove_mapsto_iff in IN0. des; ss.
        apply NatMapP.eqke_equiv.
      }
      { eapply FinFun.Injective_map_NoDup.
        { unfold FinFun.Injective. i. des_ifs. destruct u, u0. ss. }
        apply NoDupA_NoDup. apply NatMap.elements_3w.
      }
      iIntros "MYDUTY WHITES". rred.
      iApply stsim_tauR. rred.

      (* close invariant *)
      iPoseProof (OwnM_Upd with "[B1 MYW]") as "> B1".
      2:{ instantiate (1:= (Auth.black (Some wobl: NatMapRA.t nat)) ⋅ (Auth.white (NatMapRA.singleton tid k: NatMapRA.t nat))). iSplitL "B1"; iFrame. }
      { eapply Auth.auth_dealloc. eapply NatMapRA.remove_local_update. }
      rewrite <- key_set_pull_rm_eq in *. remember (NatMap.remove tid wobl) as new_wobl.

      iPoseProof (list_prop_sum_cons_unfold with "MYDUTY") as "[MYDUTY _]".
      iPoseProof (duty_to_black with "MYDUTY") as "MYBEX".
      iPoseProof (FairRA.blacks_fold with "[BLKS MYBEX]") as "BLKS".
      2:{ iFrame. }
      { instantiate (1:=
         (λ id : nat + (OMod.ident ClientImpl.omod + (Mod.ident (WMem.mod) + NatMap.key)),
             ∃ t : NatMap.key, id = inr (inr (inr t)) ∧ ¬ NatMap.In (elt:=nat) t new_wobl)).
        i. ss. des. destruct (tid_dec t tid) eqn:DEC.
        - clarify. auto.
        - left. esplits; eauto. ii. apply IN0. subst. apply NatMapP.F.remove_in_iff.
          split; auto.
      }

      iClear "MYB".
      clear Heqnew_wobl FIND wd k wobl.
      iDestruct "B2" as "[B2 B3]".
      iPoseProof (ObligationRA.alloc o_w_cor) as "> [% [[NEWB NEWW] NEWP]]".
      iPoseProof (OwnM_Upd with "[B2 LOCK]") as "> B2".
      2:{ instantiate (1:= (Auth.black (Excl.just j: Excl.t nat)) ⋅ (Auth.white (Excl.just j: Excl.t nat))). iSplitL "B2"; iFrame. }
      { eapply Auth.auth_update. do 2 instantiate (1:=Excl.just k).
        clear. ii. des. split.
        - ur. ss.
        - ur. ur in FRAME. des_ifs.
      }
      iDestruct "B2" as "[B2 LOCK]". clear j.

      iAssert (natmap_prop_sum new_wobl (fun tid0 idx => ObligationRA.correl (inr (inr (inr tid0))) idx (Ord.omega × Ord.omega)%ord)) with "[SUM]" as "#CORs".
      { iApply natmap_prop_sum_impl. 2: iFrame.
        i. iIntros "[_ [CORS _]]".  iFrame.
      }
      iPoseProof (ObligationRA.white_mon with "NEWW") as "> NEWW".
      { unfold o_w_cor. instantiate (1:= (Ord.omega × (Ord.S (Ord.S num_line)))%ord).
        apply Ord.lt_le. apply Jacobsthal.lt_mult_r.
        rewrite <- Ord.from_nat_S. rewrite <- Ord.from_nat_S. apply Ord.omega_upperbound.
        rewrite <- Ord.from_nat_O. apply Ord.omega_upperbound.
      }
      iPoseProof (ObligationRA.white_eq with "NEWW") as "NEWW".
      { apply Jacobsthal.mult_S. }
      iPoseProof (ObligationRA.white_split_eq with "NEWW") as "[NEWW1 NEWW2]".
      iPoseProof (ObligationRA.white_eq with "NEWW2") as "NEWW2".
      { apply Jacobsthal.mult_S. }
      iPoseProof (ObligationRA.white_split_eq with "NEWW2") as "[NEWWTAX NEWW2]".
      iPoseProof (ObligationRA.white_eq with "NEWW1") as "NEWW1".
      { symmetry. apply Jacobsthal.mult_1_l. }
      iPoseProof (ObligationRA.duty_alloc with "DUTY NEWW1") as "> DUTY".
      iPoseProof (ObligationRA.duty_correl_thread with "DUTY") as "#NEWCORTH".
      { ss. left; eauto. }

      (* need amps == need pendings; *)
      iAssert (natmap_prop_sum new_wobl (fun k _ => FairRA.white (inr (inr (inr k))) 1))%I with "[WHITES]" as "WHITES".
      { unfold key_set. rewrite <- list_map_elements_nm_map. unfold natmap_prop_sum.
        remember (NatMap.elements new_wobl) as ml. clear Heqml. rewrite List.map_map.
        iClear "CORs NEWCORTH". clear. iStopProof. induction ml.
        { iIntros "SUM". ss. }
        ss. des_ifs. iIntros "[WH SUM]". iFrame. iApply IHml. auto.
      }
      iPoseProof (natmap_prop_sum_impl2 with "[WHITES]") as "CASES".
      2:{ iSplitR "WHITES". iApply "CORs". iApply "WHITES". }
      { i. ss. iIntros "[COR WH]". iApply (ObligationRA.correl_correlate with "COR WH"). }
      Unshelve. 2,3: auto.
      iPoseProof (natmap_prop_sum_pull_bupd with "CASES") as "CASES". iMod "CASES".
      iPoseProof (natmap_prop_sum_or_cases_l with "CASES") as "[WHITEs|SHOT]"; cycle 1.
      { iDestruct "SHOT" as "[% [% [%FIND SHOT]]]".
        iPoseProof (natmap_prop_sum_in with "SUM") as "[_ [_ [PEND _]]]". eapply FIND.
        iPoseProof (ObligationRA.pending_not_shot with "PEND SHOT") as "FALSE". ss.
      }
      iPoseProof "NEWB" as "#NEWB".
      iPoseProof (natmap_prop_sum_sepconj with "[WHITEs]") as "WHITEs".
      { iSplitR "WHITEs". 2: iApply "WHITEs".
        instantiate (1:=fun _ _ => ObligationRA.black k o_w_cor).
        iClear "CORs NEWCORTH". unfold natmap_prop_sum. remember (NatMap.elements new_wobl) as ml.
        clear. iStopProof. induction ml; ss. auto.
        iIntros "#BLK". des_ifs. iSplit; auto. iApply IHml. auto.
      }
      iPoseProof (natmap_prop_sum_impl with "WHITEs") as "AMPs".
      { i. ss. iIntros "[BLK WHI]".
        iPoseProof (ObligationRA.white_eq with "WHI") as "WHI".
        { symmetry. apply Jacobsthal.mult_1_l. }
        iPoseProof (ObligationRA.amplifier_intro with "BLK WHI") as "AMP". iApply "AMP".
      }
      iPoseProof (natmap_prop_sum_pull_bupd with "AMPs") as "> AMPs".

      iDestruct "EXCL" as "[EXCL [EXCL2 EXCL3]]".
      iPoseProof (black_white_update with "B3 EXCL2") as ">[B3 EXCL2]".
      instantiate (1:= (tvw1, tt)).

      iMod ("K1" with "[B1 B2 B3 MEM STGT BLKS SUM NEWP AMPs INGEX]") as "_".
      { unfold lock_will_unlock. iExists true, tvw1, false, mem, new_wobl, k. iFrame. iSplitR "INGEX".
        - iRight. iFrame. auto.
        - iLeft. iFrame. auto.
      }
      { msubtac. }
      iApply stsim_discard. instantiate (1:=topset I). msubtac.

      iApply (stsim_yieldR with "[DUTY TAXKEEP NEWWTAX]"). msubtac.
      { iSplitL "DUTY". iFrame. iFrame. iApply ObligationRA.white_eq.
        { symmetry. apply Jacobsthal.mult_1_l. }
        iFrame.
      }
      iIntros "DUTY _". rred.
      iApply stsim_tauR. rred. iApply stsim_tauR. rred.

      (* iopen 0 "I0" "K0". iDestruct "I0" as "[% [I0B I0]]". *)
      (* iDestruct "I0" as "[% I0]". iDestruct "I0" as "[I01 [I02 [I03 I04]]]". *)
      (* iPoseProof (black_white_equal with "I0B EXCL") as "%". subst. *)
      (* iAssert ( *)
      (*     ((ObligationRA.pending k0 (/ 2) ** wpoints_to loc_X const_0 tvw1) *)
      (*      ∨ (ObligationRA.shot k0 ** wpoints_to loc_X const_42 tvw1)) *)
      (*       -∗ *)
      (*       ((ObligationRA.pending k0 (/ 2) ** wpoints_to loc_X const_0 tvw') *)
      (*        ∨ (ObligationRA.shot k0 ** wpoints_to loc_X const_42 tvw')) *)
      (*   )%I with "[]" as "I04a". *)
      (* { iIntros "I". iDestruct "I" as "[[A B] | [A B]]". *)
      (*   - iLeft. iFrame. iApply wpoints_to_view_mon. 2: iFrame. *)
      (*     etrans. 2: eapply l0. apply TView.join_r. *)
      (*   - iRight. iFrame. iApply wpoints_to_view_mon. 2: iFrame. *)
      (*     etrans. 2: eapply l0. apply TView.join_r. *)
      (* } *)
      (* iPoseProof ("I04a" with "I04") as "I04". *)
      (* iPoseProof (black_white_update with "I0B EXCL") as ">[I0B EXCL]". *)
      (* instantiate (1:= tvw1). *)
      (* iMod ("K0" with "[I0B I01 I02 I03 I04]") as "_". *)
      (* { iExists tvw1. iFrame. unfold thread1_will_write. iExists k0. iFrame. } *)
      (* msubtac. *)

      iPoseProof ("SIM" with "[MYTH DUTY NEWW2 EXCL EXCL2 EXCL3 LOCK]") as "SIM".
      { instantiate (1:= tvw'). iFrame. iSplit.
        { iPureIntro. etrans. 2: eapply l0. apply TView.join_l. }
        iSplitL "DUTY NEWW2 LOCK". iExists k. iFrame.
        iExists _. iFrame. iPureIntro.
        etrans. 2: eapply l0. apply TView.join_r.
      }
      iApply stsim_reset. iFrame.
    }

  Qed.

  Lemma AbsLock_unlock
        R_src R_tgt tid
        (src: thread void (sE unit) R_src)
        tgt
        r g
        (Q: R_src -> R_tgt -> iProp)
        l
        (tvw0 lvw: TView.t)
    :
    ((OwnM (Excl.just tt: Excl.t unit))
       ∗
       (OwnM (Auth.white (Excl.just tvw0: Excl.t TView.t)))
       ∗
       ((OwnM (Auth.white (Excl.just (lvw, tt): Excl.t (TView.t * unit)))) ∗ (⌜TView.le lvw tvw0⌝))
       ∗
       (∃ k, (ObligationRA.duty (inl tid) ((k, Ord.S Ord.O) :: l))
               ∗ (OwnM (Auth.white (Excl.just k: Excl.t nat)))
               ∗ (ObligationRA.taxes ((k, Ord.S Ord.O) :: l) 4%ord))
    )
      ∗
      (∀ tvw1,
          ((ObligationRA.duty (inl tid) l)
             ∗ (⌜TView.le tvw0 tvw1⌝)
          )
            -∗
            (stsim I tid (topset I) r g Q
                   false false
                   (trigger Yield;;; src)
                   (tgt tvw1)))
      ⊢
      (stsim I tid (topset I) r g Q
             false false
             (trigger Yield;;; src)
             (tvw' <- OMod.close_itree ClientImpl.omod (ModAdd (WMem.mod) AbsLockW.mod) (R:=TView.t) (OMod.call "unlock" tvw0);; (tgt tvw'))).
  Proof.
    iIntros "[[EXCLTT [EXCL [[EXCL2 %LVW] [% [DUTY [LOCK TAXES]]]]]] SIM]".
    iPoseProof (ObligationRA.taxes_ord_split_one with "TAXES") as "> [TAXES TAX]".
    { instantiate (1:= 3%ord). apply OrdArith.lt_from_nat. lia. }
    iPoseProof (ObligationRA.taxes_ord_split_one with "TAXES") as "> [TAXES TAX1]".
    { instantiate (1:= 2%ord). apply OrdArith.lt_from_nat. lia. }
    iPoseProof (ObligationRA.taxes_ord_split_one with "TAXES") as "> [TAXES TAX2]".
    { instantiate (1:= 1%ord). apply OrdArith.lt_from_nat. lia. }
    iPoseProof (ObligationRA.taxes_single_is_tax with "TAXES") as "TAX3".

    rewrite close_itree_call. ss. rred.
    iApply (stsim_yieldR with "[DUTY TAX]"). msubtac. iFrame.
    iIntros "DUTY _". rred.
    unfold AbsLockW.unlock_fun, Mod.wrap_fun. rred.
    iApply (stsim_yieldR with "[DUTY TAX1]"). msubtac. iFrame.
    iIntros "DUTY _". rred.
    iApply stsim_tauR. rred.
    iopen 1 "I1" "K1". do 6 (iDestruct "I1" as "[% I1]").
    iDestruct "I1" as "[B1 [B2 [MEM [STGT [BLKS [SUM [[CONTRA | CASE] INGS]]]]]]]".
    { iDestruct "CONTRA" as "[_ [_ [EXCL3 _]]]".
      iPoseProof (white_white_excl with "EXCL EXCL3") as "%FF". inversion FF.
    }
    iDestruct "CASE" as "[% [JPEND [JBLK [JCOR AMPs]]]]". subst own.
    iApply stsim_getR. iSplit. iFrame. rred.
    iApply stsim_tauR. rred.

    iDestruct "B2" as "[B2 B3]".
    iPoseProof (black_white_equal with "B3 EXCL2") as "%EQ". inv EQ.
    destruct (excluded_middle_informative (TView.le lvw tvw0)).
    2:{ rred. exfalso. clarify. }

    rred. iDestruct "INGS" as "[[%INGF INGEXCL] | [_ CONTRA]]".
    2:{ iPoseProof (excl_unique with "EXCLTT CONTRA") as "%FF". inv FF. }
    subst ing. rred.
    iApply stsim_getR. iSplit. iFrame. rred.
    iApply stsim_tauR. rred.
    iApply stsim_getR. iSplit. iFrame. rred.
    iApply (stsim_putR with "STGT"). iIntros "STGT". rred.
    iApply stsim_tauR. rred.

    iPoseProof (black_white_equal with "B2 LOCK") as "%EQ". subst k.
    iMod ("K1" with "[EXCLTT B1 B2 B3 MEM BLKS SUM STGT JPEND JBLK JCOR AMPs]") as "_".
    { unfold lock_will_unlock. iExists true, lvw, true, mem, wobl, j. iFrame. iSplitR "EXCLTT".
      - iRight. iSplit. auto. iFrame.
      - iRight. iSplit. auto. iFrame.
    }
    msubtac.
    iApply (stsim_yieldR with "[DUTY TAX2]"). msubtac. iFrame.
    iIntros "DUTY _". rred.

    iApply stsim_tauR. rred.
    iopen 1 "I1" "K1". do 6 (iDestruct "I1" as "[% I1]").
    iDestruct "I1" as "[B1 [B2 [MEM [STGT [BLKS [SUM [[CONTRA | CASE] INGS]]]]]]]".
    { iDestruct "CONTRA" as "[_ [_ [_ [CONTRA _]]]]".
      iPoseProof (white_white_excl with "EXCL2 CONTRA") as "%FF". inversion FF.
    }
    iDestruct "CASE" as "[% [JPEND [JBLK [JCOR AMPs]]]]". subst own.

    iDestruct "B2" as "[B2 B3]".
    iPoseProof (black_white_equal with "B3 EXCL2") as "%EQ". inv EQ.
    iDestruct "INGS" as "[[_ CONTRA] | [%INGT EXCLTT]]".
    { iPoseProof (excl_unique with "INGEXCL CONTRA") as "%FF". inv FF. }
    subst ing. rred.

    iApply stsim_getR. iSplit. iFrame. rred.
    iApply stsim_tauR. rred.
    iApply stsim_chooseR. iIntros "%". rename x into tvw_V. rred.
    iApply stsim_tauR. rred.
    iApply stsim_getR. iSplit. iFrame. rred.
    iApply stsim_tauR. rred.
    iApply stsim_getR. iSplit. iFrame. rred.
    iApply (stsim_putR with "STGT"). iIntros "STGT". rred.
    iApply stsim_tauR. rred.

    iApply stsim_chooseR. iIntros "%". destruct x. rename x into tvw'. rred.
    iApply stsim_tauR. rred.

    iPoseProof (black_white_equal with "B2 LOCK") as "%". subst.
    iPoseProof (black_white_update with "B3 EXCL2") as ">[B3 EXCL2]".
    instantiate (1:= (tvw', tt)).
    iopen 0 "I0" "K0". iDestruct "I0" as "[% [I0B I0]]".
    iDestruct "I0" as "[% I0]". iDestruct "I0" as "[I01 [I02 [I03 I04]]]".
    iPoseProof (black_white_equal with "I0B EXCL") as "%". subst.
    iAssert (
  ((ObligationRA.pending k (/ 2) ** wpoints_to loc_X const_0 tvw0)
   ∨ (ObligationRA.shot k ** wpoints_to loc_X const_42 tvw0))
    -∗
  ((ObligationRA.pending k (/ 2) ** wpoints_to loc_X const_0 tvw')
   ∨ (ObligationRA.shot k ** wpoints_to loc_X const_42 tvw'))
      )%I with "[]" as "I04a".
    { iIntros "I". iDestruct "I" as "[[A B] | [A B]]".
      - iLeft. iFrame. iApply wpoints_to_view_mon. 2: iFrame. etrans. 2:eauto. apply TView.join_l.
      - iRight. iFrame. iApply wpoints_to_view_mon. 2: iFrame. etrans. 2:eauto. apply TView.join_l.
    }
    iPoseProof ("I04a" with "I04") as "I04".
    iPoseProof (black_white_update with "I0B EXCL") as ">[I0B EXCL]".
    instantiate (1:= tvw').

    iMod ("K0" with "[I0B I01 I02 I03 I04]") as "_".
    { iExists tvw'. iFrame. unfold thread1_will_write. iExists k. iFrame. }
    iMod ("K1" with "[INGEXCL EXCLTT EXCL EXCL2 LOCK B1 B2 B3 MEM BLKS SUM STGT]") as "_".
    { unfold lock_will_unlock. iExists false, tvw_V, false, mem0, wobl0, j. iFrame. iSplitR "INGEXCL".
      - iLeft. iSplit. auto. iFrame.
      - iLeft. iSplit. auto. iFrame.
    }
    { msubtac. }
    iPoseProof (ObligationRA.pending_shot with "JPEND") as "> SHOT".
    iPoseProof (ObligationRA.duty_done with "DUTY SHOT") as "> DUTY".

    (* iApply stsim_chooseR. iIntros "%". destruct x. rename x into tvw''. rred. *)
    (* iApply stsim_tauR. rred. *)

    iApply (stsim_yieldR with "[DUTY TAX3]"). msubtac.
    { iSplitL "DUTY". iFrame.
      iPoseProof (ObligationRA.tax_cons_unfold with "TAX3") as "[_ TAX2]". iFrame.
    }
    iIntros "DUTY _". rred.
    iApply stsim_tauR. rred. iApply stsim_tauR. rred.
    iApply stsim_reset. iApply "SIM". iFrame.
    iPureIntro. etrans. 2: eapply l1. reflexivity.

  Qed.

  Lemma correct_thread1 tid:
    (∃ k, (own_thread tid)
            ∗ (ObligationRA.duty (inl tid) [(k, Ord.from_nat 1)])
            ∗ (ObligationRA.taxes
                 [(k, Ord.from_nat 1)]
                 ((((Ord.omega × Ord.omega) × Ord.omega) ⊕ ((Ord.S Ord.O) × (o_w_cor))) ⊕ 10)%ord
              )
            ∗ (OwnM (OneShot.shot k))
            ∗ (ObligationRA.pending k (/ 2))
    )
      ⊢
      (stsim I tid (topset I) ibot7 ibot7
             (fun r_src r_tgt => own_thread tid ** ObligationRA.duty (inl tid) [] ** ⌜r_src = r_tgt⌝)
             false false
             (ClientSpec.thread1 tt)
             (OMod.close_itree ClientImpl.omod (ModAdd (WMem.mod) AbsLockW.mod) (ClientImpl.thread1 tt))).
  Proof.
    iIntros "[% [TH [DUTY [TAXES [#KSHOT KPENDh]]]]]".
    unfold ClientSpec.thread1, ClientImpl.thread1. rred.
    iPoseProof (ObligationRA.taxes_ord_split_one with "TAXES") as "> [TAXES TAX]".
    { apply Hessenberg.lt_add_r. instantiate (1:=9). apply OrdArith.lt_from_nat. auto. }
    iApply AbsLock_lock. iFrame.
    iIntros "% [%VW0 [MYTH [SUM1 [SUM2 EXCLTT]]]]".
    iDestruct "SUM1" as "[% [DUTY [WHI LOCK]]]". iDestruct "SUM2" as "[% [EXCL [EXCL2 %VW1]]]".
    instantiate (1:=9). rred.
    rewrite close_itree_call. ss. rred.
    iPoseProof (ObligationRA.white_eq with "WHI") as "WHI".
    { rewrite Ord.from_nat_S. rewrite Jacobsthal.mult_S. reflexivity. }
    iPoseProof (ObligationRA.white_split_eq with "WHI") as "[WHI1 WHI2]".
    iApply (stsim_yieldR with "[DUTY WHI1 TAX]"). msubtac.
    { iSplitL "DUTY". iFrame.
      iApply ObligationRA.tax_cons_fold. iSplitL "WHI1"; auto.
      iApply ObligationRA.white_eq. 2: iFrame. symmetry; apply Jacobsthal.mult_1_l.
    }
    iIntros "DUTY _". rred. unfold WMem.store_fun, Mod.wrap_fun. rred.

    iopen 0 "I0" "K0".
    iDestruct "I0" as "[% [EXCLB I0]]".
    iPoseProof (black_white_equal with "EXCLB EXCL") as "%EQ". subst tvw0.

    iDestruct "I0" as "[% [i0BLK [i0KCOR [#i0KSHOT [i0PEND | i0SHOT]]]]]".
    2:{ iDestruct "i0SHOT" as "[i0SHOT PTR]".
        iPoseProof (OwnM_valid with "[KSHOT i0KSHOT]") as "%AGR".
        { instantiate (1:= (OneShot.shot k) ⋅ (OneShot.shot k0)). iSplitL "KSHOT"; auto. }
        apply OneShot.shot_agree in AGR. subst k0.
        iPoseProof (ObligationRA.pending_not_shot with "KPENDh i0SHOT") as "FALSE". ss.
    }
    iDestruct "i0PEND" as "[i0PENDh i0PTR]".
    iPoseProof (OwnM_valid with "[KSHOT i0KSHOT]") as "%AGR".
    { instantiate (1:= (OneShot.shot k) ⋅ (OneShot.shot k0)). iSplitL "KSHOT"; auto. }
    apply OneShot.shot_agree in AGR. subst k0.
    iPoseProof (ObligationRA.pending_sum with "KPENDh i0PENDh") as "KPEND".

    iopen 1 "I1" "K1". do 6 (iDestruct "I1" as "[% I1]").
    iDestruct "I1" as "[i1B1 [i1B2 [i1MEM [i1STGT I1]]]]".

    iApply stsim_getR. iSplit. iFrame. rred. iApply stsim_tauR. rred.
    iApply stsim_chooseR. iIntros "%". rred.
    iApply stsim_tauR. rred.
    destruct x. destruct x as [[[lc1 to] sc1] mem1]. des. rename y into WRITE.
    iPoseProof (wpoints_to_view_mon with "i0PTR") as "i0PTR". eapply VW1.
    iPoseProof (wmemory_ra_store with "i1MEM i0PTR") as "[%VW2 >[i1MEM i0PTR]]".
    eapply WRITE. eauto. eauto. eauto.

    iPoseProof (black_white_update with "EXCLB EXCL") as ">[EXCLB EXCL]".
    instantiate (1:= Local.Local.tview lc1). destruct lc1. ss. rred.
    iApply stsim_fairR.
    { i. instantiate (1:= []). ss. clear - IN.
      unfold sum_fmap_r, sum_fmap_l, WMem.missed in IN. des_ifs.
    }
    { i. instantiate (1:=[]) in IN. inv IN. }
      (* instantiate (1:= [inr (inl (loc_X, to))]) in IN. *)
    (* inv IN; ss. des_ifs. *)
    { econs. }
    { auto. }
    iIntros "_ _". rred.
    iApply stsim_tauR. rred.
    iApply stsim_getR. iSplit. iFrame. rred. iApply stsim_tauR. rred.
    iApply stsim_getR. iSplit. iFrame. rred.
    iApply (stsim_putR with "i1STGT"). iIntros "i1STGT". rred. iApply stsim_tauR. rred.
    iApply stsim_tauR. rred.

    rewrite Qp_inv_half_half.
    iPoseProof (ObligationRA.pending_shot with "KPEND") as "> #OBLKSHOT".

    iMod ("K0" with "[EXCLB i0BLK i0KCOR i0PTR]") as "_".
    { iExists tview. iFrame.
      unfold thread1_will_write. iExists k. iFrame. iSplitR; auto. }

    iMod ("K1" with "[i1B1 i1B2 i1MEM i1STGT I1]") as "_".
    { unfold lock_will_unlock. iExists own, tvw0, ing, _, wobl, j0. iFrame. }
    msubtac.

    iPoseProof (ObligationRA.white_mon with "WHI2") as ">WHI2".
    { instantiate (1:= (Ord.omega × 4)%ord). apply Jacobsthal.le_mult_r. apply OrdArith.le_from_nat. lia. }

    iPoseProof (ObligationRA.duty_permutation with "DUTY") as "DUTY".
    { eapply perm_swap. }
    iPoseProof (ObligationRA.duty_done with "DUTY OBLKSHOT") as "> DUTY".
    iApply stsim_reset. iApply AbsLock_unlock. iSplitL "EXCL EXCL2 EXCLTT LOCK WHI2 DUTY".
    { iSplitL "EXCLTT". iFrame. iSplitL "EXCL". iFrame. iSplitL "EXCL2".
      { iFrame. iPureIntro. etrans. eapply VW1. auto. }
      iExists j. iFrame. iApply ObligationRA.taxes_cons_fold. iSplitL; auto.
      iApply ObligationRA.white_eq. 2: iFrame.
      rewrite Jacobsthal.mult_1_l. reflexivity.
    }
    iIntros "% [DUTY %VW3]". rred.
    iApply (stsim_sync with "[DUTY]"). msubtac. iFrame.
    iIntros "DUTY _". rred. iApply stsim_tauR. rred.
    iApply stsim_ret. iApply MUpd_intro. iFrame. auto.

  Qed.

  Lemma correct_thread2 tid:
    ((own_thread tid)
       ∗ (ObligationRA.duty (inl tid) [])
    )
      ⊢
      (stsim I tid (topset I) ibot7 ibot7
             (fun r_src r_tgt => own_thread tid ** ObligationRA.duty (inl tid) [] ** ⌜r_src = r_tgt⌝)
             false false
             (ClientSpec.thread2 tt)
             (OMod.close_itree ClientImpl.omod (ModAdd (WMem.mod) AbsLockW.mod) (ClientImpl.thread2 tt))).
  Proof.
    iIntros "[MYTH DUTY]".
    unfold ClientSpec.thread2, ClientImpl.thread2. rred.
    iopen 0 "I0" "K0".
    iDestruct "I0" as "[% [EXCLB I0]]". iDestruct "I0" as "[% [[% #KBLK] [#KCOR [#KSHOT I0]]]]".
    iMod ("K0" with "[EXCLB I0]") as "_".
    { iExists tvw. iFrame. unfold thread1_will_write. iExists k. iFrame. auto. }
    { msubtac. }

    (* induction *)
    rred. iApply stsim_discard.
    { instantiate (1:=topset I). msubtac. }
    remember TView.bot as tvw_base. clear tvw Heqtvw_base.
    iStopProof. revert tid k tvw_base. pattern n. revert n.
    apply (well_founded_induction Ord.lt_well_founded). intros n IH. intros.
    iIntros "[#[KBLK [KCOR KSHOT]] [MYTH DUTY]]".
    rewrite OpenMod.unfold_iter. rred.
    iApply AbsLock_lock. iSplitL "MYTH DUTY".
    { iFrame. }
    iIntros "% [%VW0 [MYTH [SUM1 [SUM2 EXCLTT]]]]".
    iDestruct "SUM1" as "[% [DUTY [WHI LOCK]]]". iDestruct "SUM2" as "[% [EXCL [EXCL2 %VW1]]]".
    instantiate (1:= 9). rred.

    rewrite close_itree_call. ss. rred.
    iPoseProof (ObligationRA.white_eq with "WHI") as "WHI".
    { rewrite Ord.from_nat_S. rewrite Jacobsthal.mult_S. reflexivity. }
    iPoseProof (ObligationRA.white_split_eq with "WHI") as "[WHI1 WHI2]".
    iApply (stsim_yieldR with "[DUTY WHI1]"). msubtac.
    { iSplitL "DUTY". iFrame.
      iApply ObligationRA.tax_cons_fold. iSplitL "WHI1"; auto.
      iApply ObligationRA.white_eq. 2: iFrame. symmetry; apply Jacobsthal.mult_1_l.
    }
    iIntros "DUTY OWHTH". rred. unfold WMem.load_fun, Mod.wrap_fun. rred.

    iopen 0 "I0" "K0". iDestruct "I0" as "[% [EXCLB I0]]".
    iPoseProof (black_white_equal with "EXCLB EXCL") as "%EQ". subst tvw0.
    iDestruct "I0" as "[% [i0BLK [i0KCOR [#i0KSHOT [i0PEND | i0SHOT]]]]]".

    (* iterate case *)
    { iDestruct "i0PEND" as "[i0PENDh i0PTR]".
      iPoseProof (OwnM_valid with "[KSHOT i0KSHOT]") as "%AGR".
      { instantiate (1:= (OneShot.shot k) ⋅ (OneShot.shot k0)). iSplitL "KSHOT"; auto. }
      apply OneShot.shot_agree in AGR. subst k0.

      iopen 1 "I1" "K1". do 6 (iDestruct "I1" as "[% I1]").
      iDestruct "I1" as "[i1B1 [i1B2 [i1MEM [i1STGT I1]]]]".
      iApply stsim_getR. iSplit. iFrame. rred. iApply stsim_tauR. rred.
      iApply stsim_chooseR. iIntros "%".
      destruct x. destruct x as [[lc1 val] to]. des. rename y into READ. rred.
      iPoseProof (wpoints_to_view_mon with "i0PTR") as "i0PTR". eapply VW1.
      iPoseProof (wmemory_ra_load with "i1MEM i0PTR") as "[i1MEM [%VW2 >i0PTR]]".
      eapply READ. eauto. eauto. des. subst val.
      iApply stsim_tauR. rred.

      iPoseProof (black_white_update with "EXCLB EXCL") as ">[EXCLB EXCL]".
      instantiate (1:= Local.Local.tview lc1). destruct lc1. ss. rred.
      iApply stsim_fairR.
      { i. instantiate (1:= []). ss. clear - IN.
        unfold sum_fmap_r, sum_fmap_l, WMem.missed in IN. des_ifs.
      }
      { i. instantiate (1:=[]) in IN. inv IN. }
      { econs. }
      { auto. }
      iIntros "_ _". rred.
      iApply stsim_tauR. rred. iApply stsim_tauR. rred.

      iMod ("K0" with "[EXCLB i0BLK i0KCOR i0PTR i0PENDh]") as "_".
      { iExists tview. iFrame. unfold thread1_will_write. iExists k. iFrame. iSplitR; auto. iLeft; iFrame. }
      iMod ("K1" with "[i1B1 i1B2 i1MEM i1STGT I1]") as "_".
      { unfold lock_will_unlock. iExists own, tvw0, ing, mem, wobl, j0. iFrame. }
      msubtac.
      clear own mem wobl j0 released READ.
      iPoseProof (ObligationRA.white_mon with "WHI2") as ">WHI2".
      { instantiate (1:= (Ord.omega × 4)%ord). apply Jacobsthal.le_mult_r. apply OrdArith.le_from_nat. lia. }
      iApply stsim_reset. iApply AbsLock_unlock. iSplitL "LOCK EXCLTT EXCL EXCL2 WHI2 DUTY".
      { iSplitL "EXCLTT". iFrame. iSplitL "EXCL". iFrame. iSplitL "EXCL2".
        { iFrame. iPureIntro. etrans. 2: eauto. auto. }
        iFrame. iExists j. iFrame. iApply ObligationRA.taxes_cons_fold. iSplitL; auto.
        iApply ObligationRA.white_eq. 2: iFrame.
        rewrite Jacobsthal.mult_1_l. reflexivity.
      }
      iIntros "% [DUTY %VW3]". rred. iApply stsim_tauR. rred.
      iClear "i0KSHOT".
      iPoseProof (ObligationRA.correl_thread_correlate with "KCOR OWHTH") as "> [KWHI|#KDONE]".
      (* thread 1 not done; induction *)
      { iPoseProof (ObligationRA.black_white_decr_one with "KBLK KWHI") as "> [% [#KBLK2 %DECR]]".
        iClear "KBLK". iApply stsim_reset. iApply IH. apply DECR. iFrame. eauto.
      }

      (* thread 1 done; exit *)
      { iClear "KBLK KCOR". clear_upto I.
        rewrite OpenMod.unfold_iter. rred.
        iApply stsim_reset. iApply AbsLock_lock. iSplitL "MYTH DUTY".
        { iFrame. }
        iIntros "% [%VW0 [MYTH [SUM1 [SUM2 EXCLTT]]]]".
        iDestruct "SUM1" as "[% [DUTY [WHI LOCK]]]". iDestruct "SUM2" as "[% [EXCL [EXCL2 %VW1]]]".
        instantiate (1:= 9). rred.

        iopen 0 "I0" "K0". iDestruct "I0" as "[% [EXCLB I0]]".
        iDestruct "I0" as "[% [i0BLK [i0KCOR [#i0KSHOT [i0PEND | i0SHOT]]]]]".
        { iDestruct "i0PEND" as "[i0PENDh i0PTR]".
          iPoseProof (OwnM_valid with "[KSHOT i0KSHOT]") as "%AGR".
          { instantiate (1:= (OneShot.shot k) ⋅ (OneShot.shot k0)). iSplitL "KSHOT"; auto. }
          apply OneShot.shot_agree in AGR. subst k0.
          iPoseProof (ObligationRA.pending_not_shot with "i0PENDh KDONE") as "FALSE". ss.
        }
        iDestruct "i0SHOT" as "[_ i0PTR]".
        iPoseProof (OwnM_valid with "[KSHOT i0KSHOT]") as "%AGR".
        { instantiate (1:= (OneShot.shot k) ⋅ (OneShot.shot k0)). iSplitL "KSHOT"; auto. }
        apply OneShot.shot_agree in AGR. subst k0.

        rewrite close_itree_call. ss. rred.
        iMod ("K0" with "[EXCLB i0BLK i0KCOR i0PTR]") as "_".
        { iExists _. iFrame. unfold thread1_will_write. iExists _. iFrame. iSplitR; auto. }
        msubtac.
        iPoseProof (ObligationRA.white_eq with "WHI") as "WHI".
        { rewrite Ord.from_nat_S. rewrite Jacobsthal.mult_S. reflexivity. }
        iPoseProof (ObligationRA.white_split_eq with "WHI") as "[WHI1 WHI2]".
        iApply (stsim_yieldR with "[DUTY WHI1]"). msubtac.
        { iSplitL "DUTY". iFrame.
          iApply ObligationRA.tax_cons_fold. iSplitL "WHI1"; auto.
          iApply ObligationRA.white_eq. 2: iFrame. symmetry; apply Jacobsthal.mult_1_l.
        }
        iIntros "DUTY _". rred. unfold WMem.load_fun, Mod.wrap_fun. rred.
        iopen 1 "I1" "K1". do 6 (iDestruct "I1" as "[% I1]").
        iDestruct "I1" as "[i1B1 [i1B2 [i1MEM [i1STGT I1]]]]".
        iApply stsim_getR. iSplit. iFrame. rred. iApply stsim_tauR. rred.
        iClear "i0KSHOT". iopen 0 "I0" "K0". iDestruct "I0" as "[% [EXCLB I0]]".
        iDestruct "I0" as "[% [i0BLK [i0KCOR [#i0KSHOT [i0PEND | i0SHOT]]]]]".
        { iDestruct "i0PEND" as "[i0PENDh i0PTR]".
          iPoseProof (OwnM_valid with "[KSHOT i0KSHOT]") as "%AGR".
          { instantiate (1:= (OneShot.shot k) ⋅ (OneShot.shot k0)). iSplitL "KSHOT"; auto. }
          apply OneShot.shot_agree in AGR. subst k0.
          iPoseProof (ObligationRA.pending_not_shot with "i0PENDh KDONE") as "FALSE". ss.
        }
        iDestruct "i0SHOT" as "[_ i0PTR]".
        iPoseProof (OwnM_valid with "[KSHOT i0KSHOT]") as "%AGR".
        { instantiate (1:= (OneShot.shot k) ⋅ (OneShot.shot k0)). iSplitL "KSHOT"; auto. }
        apply OneShot.shot_agree in AGR. subst k0.
        iPoseProof (black_white_equal with "EXCLB EXCL") as "%EQ". subst tvw4.

        iApply stsim_chooseR. iIntros "%".
        destruct x. destruct x as [[lc1 val] to]. des. rename y into READ. rred.
        iPoseProof (wpoints_to_view_mon with "i0PTR") as "i0PTR". eapply VW1.
        iPoseProof (wmemory_ra_load with "i1MEM i0PTR") as "[i1MEM [%VW3 >i0PTR]]".
        eapply READ. eauto. eauto. des. subst val.
        iApply stsim_tauR. rred.
        iPoseProof (black_white_update with "EXCLB EXCL") as ">[EXCLB EXCL]".
        instantiate (1:= Local.Local.tview lc1). destruct lc1. ss. rred.
        iApply stsim_fairR.
        { i. instantiate (1:= []). ss. clear - IN.
          unfold sum_fmap_r, sum_fmap_l, WMem.missed in IN. des_ifs.
        }
        { i. instantiate (1:=[]) in IN. inv IN. }
        { econs. }
        { auto. }
        iIntros "_ _". rred.
        iApply stsim_tauR. rred. iApply stsim_tauR. rred.

        iMod ("K0" with "[EXCLB i0BLK i0KCOR i0PTR]") as "_".
        { iExists _. iFrame. unfold thread1_will_write. iExists _. iFrame. iSplitR; auto. }
        iMod ("K1" with "[i1B1 i1B2 i1MEM i1STGT I1]") as "_".
        { unfold lock_will_unlock. iExists own, tvw3, ing, mem, wobl, j0. iFrame. }
        msubtac.
        clear own mem wobl j0 promises to released READ.
        iPoseProof (ObligationRA.white_mon with "WHI2") as ">WHI2".
        { instantiate (1:= (Ord.omega × 4)%ord). apply Jacobsthal.le_mult_r. apply OrdArith.le_from_nat. lia. }
        iApply stsim_reset. iApply AbsLock_unlock. iSplitL "LOCK EXCLTT EXCL EXCL2 WHI2 DUTY".
        { iSplitL "EXCLTT". iFrame. iSplitL "EXCL". iFrame. iSplitL "EXCL2".
          { iFrame. iPureIntro. etrans. 2: eauto. auto. }
          iFrame. iExists j. iFrame. iApply ObligationRA.taxes_cons_fold. iSplitL; auto.
          iApply ObligationRA.white_eq. 2: iFrame.
          rewrite Jacobsthal.mult_1_l. reflexivity.
        }
        iIntros "% [DUTY %VW4]". rred.

        iApply (stsim_sync with "[DUTY]"). msubtac. iFrame.
        iIntros "DUTY _". rred. iApply stsim_tauR. rred.
        iApply stsim_observe. iIntros. rred.
        iApply stsim_tauR. rred.
        iApply (stsim_sync with "[DUTY]"). msubtac. iFrame.
        iIntros "DUTY _". rred.
        iApply stsim_tauR. rred.
        iApply stsim_ret.
        iApply MUpd_intro. iFrame. auto.
      }
    }

    { iDestruct "i0SHOT" as "[#KDONE i0PTR]".
      iPoseProof (OwnM_valid with "[KSHOT i0KSHOT]") as "%AGR".
      { instantiate (1:= (OneShot.shot k) ⋅ (OneShot.shot k0)). iSplitL "KSHOT"; auto. }
      apply OneShot.shot_agree in AGR. subst k0.

      iopen 1 "I1" "K1". do 6 (iDestruct "I1" as "[% I1]").
      iDestruct "I1" as "[i1B1 [i1B2 [i1MEM [i1STGT I1]]]]".
      iApply stsim_getR. iSplit. iFrame. rred. iApply stsim_tauR. rred.
      iApply stsim_chooseR. iIntros "%".
      destruct x. destruct x as [[lc1 val] to]. des. rename y into READ. rred.
      iPoseProof (wpoints_to_view_mon with "i0PTR") as "i0PTR". eapply VW1.
      iPoseProof (wmemory_ra_load with "i1MEM i0PTR") as "[i1MEM [%VW3 >i0PTR]]".
      eapply READ. eauto. eauto. des. subst val.
      iApply stsim_tauR. rred.
      iPoseProof (black_white_update with "EXCLB EXCL") as ">[EXCLB EXCL]".
      instantiate (1:= Local.Local.tview lc1). destruct lc1. ss. rred.
      iApply stsim_fairR.
      { i. instantiate (1:= []). ss. clear - IN.
        unfold sum_fmap_r, sum_fmap_l, WMem.missed in IN. des_ifs.
      }
      { i. instantiate (1:=[]) in IN. inv IN. }
      { econs. }
      { auto. }
      iIntros "_ _". rred.
      iApply stsim_tauR. rred. iApply stsim_tauR. rred.

      iMod ("K0" with "[EXCLB i0BLK i0KCOR i0PTR]") as "_".
      { iExists _. iFrame. unfold thread1_will_write. iExists _. iFrame. iSplitR; auto. }
      iMod ("K1" with "[i1B1 i1B2 i1MEM i1STGT I1]") as "_".
      { unfold lock_will_unlock. iExists own, tvw0, ing, mem, wobl, j0. iFrame. }
      msubtac.
      clear own mem wobl j0 promises to released READ.
      iPoseProof (ObligationRA.white_mon with "WHI2") as ">WHI2".
      { instantiate (1:= (Ord.omega × 4)%ord). apply Jacobsthal.le_mult_r. apply OrdArith.le_from_nat. lia. }
      iApply stsim_reset. iApply AbsLock_unlock. iSplitL "LOCK EXCLTT EXCL EXCL2 WHI2 DUTY".
      { iSplitL "EXCLTT". iFrame. iSplitL "EXCL". iFrame. iSplitL "EXCL2".
        { iFrame. iPureIntro. etrans. 2: eauto. auto. }
        iFrame. iExists j. iFrame. iApply ObligationRA.taxes_cons_fold. iSplitL; auto.
        iApply ObligationRA.white_eq. 2: iFrame.
        rewrite Jacobsthal.mult_1_l. reflexivity.
      }
      iIntros "% [DUTY %VW4]". rred.

      iApply (stsim_sync with "[DUTY]"). msubtac. iFrame.
      iIntros "DUTY _". rred. iApply stsim_tauR. rred.
      iApply stsim_observe. iIntros. rred.
      iApply stsim_tauR. rred.
      iApply (stsim_sync with "[DUTY]"). msubtac. iFrame.
      iIntros "DUTY _". rred.
      iApply stsim_tauR. rred.
      iApply stsim_ret.
      iApply MUpd_intro. iFrame. auto.
    }

  Qed.





  Let config := [("thread1", tt↑); ("thread2", tt↑)].

  Lemma client_correct:
    UserSim.sim ClientSpec.mod ClientImpl.mod (prog2ths ClientSpec.mod config) (prog2ths ClientImpl.mod config).
  Admitted.
End SIM.
