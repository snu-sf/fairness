From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
Unset Universe Checking.

From Fairness Require Export
     ITreeLib WFLib FairBeh NatStructs Mod pind Axioms
     OpenMod SCM Red IRed Wrapper WeakestAdequacy FairLock Concurrency.
From Ordinal Require Export ClassicalHessenberg.

Set Implicit Arguments.

Definition ord_wf: WF := mk_wf (@Ord.lt_well_founded).

Section INIT.

  Definition gvs : list nat := [1].

  Definition loc_X := SCMem.val_ptr (0, 0).

  Definition const_0 := SCMem.val_nat 0.
  Definition const_42 := SCMem.val_nat 42.

End INIT.

Module ClientImpl.

  Definition thread1:
    ktree ((((@eventE void) +' cE) +' (sE unit)) +' OpenMod.callE) unit unit
    :=
    fun _ =>
      `_: unit <- (OMod.call "lock" tt);;
      `_: unit <- (OMod.call "store" (loc_X, const_42));;
      `_: unit <- (OMod.call "unlock" tt);;
      _ <- trigger Yield;;
      Ret tt.

  Definition thread2:
    ktree ((((@eventE void) +' cE) +' (sE unit)) +' OpenMod.callE) unit unit
    :=
    fun _ =>
      _ <- ITree.iter
            (fun (_: unit) =>
               `_: unit <- (OMod.call "lock" tt);;
               x <- (OMod.call "load" loc_X);;
               `_: unit <- (OMod.call "unlock" tt);;
               b <- OMod.call "compare" (x: SCMem.val, SCMem.val_nat 0);;
               if (b: bool) then Ret (inl tt) else Ret (inr tt)) tt;;
      x <- (OMod.call "load" loc_X);;
      match x with
      | SCMem.val_nat n => _ <- trigger (Observe 0 [n]);; Ret tt
      | _ => UB
      end.

  Definition omod: OMod.t :=
    OMod.mk
      tt
      (Mod.get_funs [("thread1", Mod.wrap_fun thread1);
                     ("thread2", Mod.wrap_fun thread2)])
  .

  Definition mod: Mod.t :=
    OMod.close
      (omod)
      (ModAdd (SCMem.mod gvs) ABSLock.mod)
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

Section SIM.

  Context `{Σ: GRA.t}.

  Context `{MONORA: @GRA.inG monoRA Σ}.
  Context `{THDRA: @GRA.inG ThreadRA Σ}.
  Context `{STATESRC: @GRA.inG (stateSrcRA (unit)) Σ}.
  (* Context `{STATETGT: @GRA.inG (stateTgtRA (unit * (SCMem.t * (bool * NatMap.t unit)))) Σ}. *)
  Context `{STATETGT: @GRA.inG (stateTgtRA ((OMod.closed_state ClientImpl.omod (ModAdd (SCMem.mod gvs) ABSLock.mod)))) Σ}.
  Context `{IDENTSRC: @GRA.inG (identSrcRA (void)) Σ}.
  (* Context `{IDENTTGT: @GRA.inG (identTgtRA (void + (SCMem.val + thread_id))%type) Σ}. *)
  Context `{IDENTTGT: @GRA.inG (identTgtRA (OMod.closed_ident ClientImpl.omod (ModAdd (SCMem.mod gvs) ABSLock.mod))%type) Σ}.

  Context `{OBLGRA: @GRA.inG ObligationRA.t Σ}.
  (* Context `{ARROWRA: @GRA.inG (ArrowRA (void + (SCMem.val + thread_id))%type) Σ}. *)
  Context `{ARROWRA: @GRA.inG (ArrowRA (OMod.closed_ident ClientImpl.omod (ModAdd (SCMem.mod gvs) ABSLock.mod))%type) Σ}.
  Context `{EDGERA: @GRA.inG EdgeRA Σ}.
  Context `{ONESHOTSRA: @GRA.inG (@FiniteMap.t (OneShot.t unit)) Σ}.

  Context `{MEMRA: @GRA.inG memRA Σ}.

  Context `{EXCL: @GRA.inG (Excl.t unit) Σ}.
  Context `{ONESHOTRA: @GRA.inG (OneShot.t nat) Σ}.
  Context `{REGIONRA: @GRA.inG (Region.t (thread_id * nat)) Σ}.
  Context `{CONSENTRA: @GRA.inG (@FiniteMap.t (Consent.t nat)) Σ}.
  Context `{AUTHNRA: @GRA.inG (Auth.t (Excl.t nat)) Σ}.
  (* Context `{AUTHUNITRA: @GRA.inG (Auth.t (Excl.t unit)) Σ}. *)
  (* Context `{AUTHNMRA: @GRA.inG (Auth.t (NatMapRA.t unit)) Σ}. *)
  Context `{AUTHNMNRA: @GRA.inG (Auth.t (NatMapRA.t nat)) Σ}.
  (* Context `{AUTHNMNN: @GRA.inG (Auth.t (NatMapRA.t (nat * nat))) Σ}. *)

  Definition thread1_will_write : iProp :=
    ∃ k, (∃ n, ObligationRA.black k n)
           ∗
           (ObligationRA.correl_thread k 1%ord)
           ∗
           (OwnM (OneShot.shot k))
           ∗
           ((ObligationRA.pending k (/2)%Qp ∗ points_to loc_X const_0)
            ∨
              (ObligationRA.shot k ∗ points_to loc_X const_42)).

  Definition o_w_cor: Ord.t := (Ord.omega × Ord.omega)%ord.

  Definition lock_will_unlock : iProp :=
    ∃ (own: bool) (mem: SCMem.t) (wobl: NatMap.t nat) (j: nat),
      (OwnM (Auth.black (Some wobl: NatMapRA.t nat)))
        ∗
        (OwnM (Auth.black (Excl.just j: Excl.t nat)))
        ∗
        (memory_black mem)
        ∗
        (St_tgt (tt, (mem, (own, key_set wobl))))
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
  .

  Let I: list iProp := [thread1_will_write; lock_will_unlock].

  Lemma ABSLock_lock
        R_src R_tgt tid
        (src: thread void (sE unit) R_src)
        tgt
        r g
        (Q: R_src -> R_tgt -> iProp)
        (l: list (nat * Ord.t)%type)
        (num_line: nat)
    :
    ((own_thread tid)
       ∗
       (ObligationRA.duty (inl tid) l)
       ∗
       (ObligationRA.taxes
          l ((((Ord.omega × Ord.omega) × Ord.omega)
                ⊕
                ((Ord.S Ord.O) × (o_w_cor)))
               ⊕ 2)%ord))
      ∗
      (((own_thread tid)
          ∗
          (∃ j, (ObligationRA.duty (inl tid) ((j, Ord.S Ord.O) :: l))
                  ∗
                  (ObligationRA.white j (Ord.omega × (Ord.from_nat num_line))%ord)
                  ∗
                  (OwnM (Auth.white (Excl.just j: Excl.t nat)))
          )
          ∗
          (OwnM (Excl.just tt: Excl.t unit)))
         -∗
         (stsim I tid (topset I) r g Q
                (trigger Yield;;; src)
                (tgt)))
      ⊢
      (stsim I tid (topset I) r g Q
             (trigger Yield;;; src)
             ((OMod.close_itree ClientImpl.omod (ModAdd (SCMem.mod gvs) ABSLock.mod) (R:=unit) (OMod.call "lock" ()));;; tgt)).
  Proof.
    iIntros "[[TH [DUTY TAXES]] SIM]".
    rewrite close_itree_call. ss. rred.
    iPoseProof (ObligationRA.taxes_ord_split_one with "TAXES") as "TAXES".
    { eapply Hessenberg.lt_add_r. apply OrdArith.lt_from_nat. instantiate (1:=1). auto. }
    iMod "TAXES". iDestruct "TAXES" as "[TAXES TAX]".

    iApply (stsim_yieldR with "[DUTY TAX]"). msubtac. iFrame.
    iIntros "DUTY _". rred.
    unfold ABSLock.lock_fun, Mod.wrap_fun. rred.
    iApply stsim_tidR. rred. iApply stsim_tauR. rred.
    iopen 1 "I1" "K1". do 4 (iDestruct "I1" as "[% I1]").
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
    iDestruct "I1" as "[BLKS [SUM CASES]]".

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
           (λ id : nat + (OMod.ident ClientImpl.omod + (Mod.ident (SCMem.mod gvs) + NatMap.key)),
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
  ((⌜own = false⌝ ∗
   (OwnM (Auth.white (Excl.just j: Excl.t nat)) ** OwnM (Excl.just (): Excl.t unit)))
   ∨ (⌜own = true⌝ **
               (ObligationRA.pending j 1 **
                (ObligationRA.black j o_w_cor **
                 (ObligationRA.correl_thread j 1 **
            natmap_prop_sum wobl (λ _ idx : nat, ObligationRA.amplifier j idx 1))))))
    ∗
    #=( ObligationRA.edges_sat )=>((⌜own = true⌝) -∗ (ObligationRA.amplifier j k 1)))%I
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
    iMod ("K1" with "[TH OWNB1 B2 MEM SUM CASES STGT PEND BLKS MYDUTY MYCOR AMP]") as "_".
    { unfold lock_will_unlock. iExists own, mem, (NatMap.add tid k wobl), j. iFrame.
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
    remember (wd ⊕ 1)%ord as credit.
    assert (RICH: (wd < credit)%ord).
    { subst; apply Hessenberg.add_lt_l. rewrite <- Ord.from_nat_O.
      apply OrdArith.lt_from_nat. auto.
    }
    clear Heqwd Heqcredit.
    clear own mem blks2 j H wobl. iClear "MYCOR".
    iStopProof. revert l k credit RICH. pattern wd. revert wd.
    apply (well_founded_induction Ord.lt_well_founded). intros wd IH. intros l k credit RICH.
    iIntros "[SIM [TAXES [DUTY [MYB MYW]]]]".
    rewrite OpenMod.unfold_iter. rred.
    iopen 1 "I1" "K1". do 4 (iDestruct "I1" as "[% I1]").
    iDestruct "I1" as "[B1 [B2 [MEM [STGT I1]]]]".
    iApply stsim_getR. iSplit. iFrame. rred.
    iApply stsim_tauR. rred. destruct own.

    (* someone is holding the lock *)
    { rred. iMod ("K1" with "[B1 B2 MEM STGT I1]") as "_".
      { unfold lock_will_unlock. do 4 (iExists _). iFrame. }
      { msubtac. }
      iPoseProof (ObligationRA.taxes_ord_split_one with "TAXES") as "> [TAXES TAX]". eauto.
      iApply (stsim_yieldR with "[DUTY TAX]"). msubtac. iFrame.
      iIntros "DUTY WTH". rred.
      iApply stsim_tauR. rred. iApply stsim_tauR. rred.

      clear mem wobl j.
      iopen 1 "I1" "K1". do 4 (iDestruct "I1" as "[% I1]").
      iDestruct "I1" as "[B1 [B2 [MEM [STGT [BLKS [SUM CASES]]]]]]".

      iAssert (⌜NatMap.find tid wobl = Some k⌝)%I as "%".
      { iPoseProof (OwnM_valid with "[MYW B1]") as "%".
        { instantiate (1:= (Auth.black (Some wobl: NatMapRA.t nat)) ⋅ (Auth.white (NatMapRA.singleton tid k: NatMapRA.t nat))). iSplitL "B1"; iFrame. }
        eapply Auth.auth_included in H. eapply NatMapRA.extends_singleton_iff in H.
        auto.
      }
      rename H into FIND.

      iDestruct "CASES" as "[[%OWNF [LOCK EXCL]] | [%OWNT [JPEND [JBLK [#JCOR AMPs]]]]]"; cycle 1.

      (* own = true, induction *)
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
          iMod ("K1" with "[B1 B2 MEM STGT BLKS SUM JPEND JBLK AMPs]") as "_".
          { unfold lock_will_unlock. do 4 (iExists _). iFrame.
            iRight. iFrame. iSplit; auto.
          }
          { msubtac. }
          iApply IH. eapply RENEW. eapply RENEW.
          iFrame.
        }
      }

      (* own = false, exit *)
      clear IH credit RICH.
      rewrite OpenMod.unfold_iter. rred.
      iApply stsim_getR. iSplit. iFrame. rred.
      iApply stsim_tauR. rred.
      subst own. rred.
      iApply stsim_getR. iSplit. iFrame. rred.
      iApply stsim_tauR. rred.
      iApply stsim_getR. iSplit. iFrame. rred.
      iApply stsim_tauR. rred.
      iApply stsim_getR. iSplit. iFrame. rred.
      iApply (stsim_putR with "STGT"). iIntros "STGT". rred.
      iApply stsim_tauR. rred.

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
         (λ id : nat + (OMod.ident ClientImpl.omod + (Mod.ident (SCMem.mod gvs) + NatMap.key)),
             ∃ t : NatMap.key, id = inr (inr (inr t)) ∧ ¬ NatMap.In (elt:=nat) t new_wobl)).
        i. ss. des. destruct (tid_dec t tid) eqn:DEC.
        - clarify. auto.
        - left. esplits; eauto. ii. apply IN0. subst. apply NatMapP.F.remove_in_iff.
          split; auto.
      }

      iClear "MYB TAXES". clear Heqnew_wobl FIND wd k wobl.
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
      { unfold o_w_cor. instantiate (1:= (Ord.omega × (Ord.S num_line))%ord). apply Ord.lt_le.
        apply Jacobsthal.lt_mult_r. rewrite <- Ord.from_nat_S. apply Ord.omega_upperbound.
        rewrite <- Ord.from_nat_O. apply Ord.omega_upperbound.
      }
      iPoseProof (ObligationRA.white_eq with "NEWW") as "NEWW".
      { apply Jacobsthal.mult_S. }
      iPoseProof (ObligationRA.white_split_eq with "NEWW") as "[NEWW1 NEWW2]".
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

      iMod ("K1" with "[B1 B2 MEM STGT BLKS SUM NEWP AMPs]") as "_".
      { unfold lock_will_unlock. iExists true, mem, new_wobl, k. iFrame. iRight. iFrame. auto. }
      { msubtac. }
      iApply stsim_discard. instantiate (1:=topset I). msubtac.
      iPoseProof ("SIM" with "[MYTH DUTY NEWW2 EXCL LOCK]") as "SIM".
      iFrame. iExists k. iFrame.
      iFrame.
    }

    { rred. iClear "TAXES".
      clear IH credit RICH.
      iApply stsim_getR. iSplit. iFrame. rred.
      iApply stsim_tauR. rred.
      iApply stsim_getR. iSplit. iFrame. rred.
      iApply stsim_tauR. rred.
      iApply stsim_getR. iSplit. iFrame. rred.
      iApply (stsim_putR with "STGT"). iIntros "STGT". rred.
      iApply stsim_tauR. rred.

      iDestruct "I1" as "[BLKS [SUM [[_ [LOCK EXCL]] | [%CONTRA _]]]]".
      2:{ inversion CONTRA. }
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
         (λ id : nat + (OMod.ident ClientImpl.omod + (Mod.ident (SCMem.mod gvs) + NatMap.key)),
             ∃ t : NatMap.key, id = inr (inr (inr t)) ∧ ¬ NatMap.In (elt:=nat) t new_wobl)).
        i. ss. des. destruct (tid_dec t tid) eqn:DEC.
        - clarify. auto.
        - left. esplits; eauto. ii. apply IN0. subst. apply NatMapP.F.remove_in_iff.
          split; auto.
      }

      iClear "MYB". clear Heqnew_wobl FIND wd k wobl.
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
      { unfold o_w_cor. instantiate (1:= (Ord.omega × (Ord.S num_line))%ord). apply Ord.lt_le.
        apply Jacobsthal.lt_mult_r. rewrite <- Ord.from_nat_S. apply Ord.omega_upperbound.
        rewrite <- Ord.from_nat_O. apply Ord.omega_upperbound.
      }
      iPoseProof (ObligationRA.white_eq with "NEWW") as "NEWW".
      { apply Jacobsthal.mult_S. }
      iPoseProof (ObligationRA.white_split_eq with "NEWW") as "[NEWW1 NEWW2]".
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

      iMod ("K1" with "[B1 B2 MEM STGT BLKS SUM NEWP AMPs]") as "_".
      { unfold lock_will_unlock. iExists true, mem, new_wobl, k. iFrame. iRight. iFrame. auto. }
      { msubtac. }
      iApply stsim_discard. instantiate (1:=topset I). msubtac.
      iPoseProof ("SIM" with "[MYTH DUTY NEWW2 EXCL LOCK]") as "SIM".
      iFrame. iExists k. iFrame.
      iFrame.
    }
  Qed.

  Lemma ABSLock_unlock
        R_src R_tgt tid
        (src: thread void (sE unit) R_src)
        tgt
        r g
        (Q: R_src -> R_tgt -> iProp)
        l
    :
    ((OwnM (Excl.just tt: Excl.t unit))
       ∗
       (∃ k, (ObligationRA.duty (inl tid) ((k, Ord.S Ord.O) :: l))
               ∗ (OwnM (Auth.white (Excl.just k: Excl.t nat)))
               ∗ (ObligationRA.tax ((k, Ord.S Ord.O) :: l)))
    )
      ∗
      ((ObligationRA.duty (inl tid) l)
         -∗
         (stsim I tid (topset I) r g Q
                (trigger Yield;;; src)
                (tgt)))
      ⊢
      (stsim I tid (topset I) r g Q
             (trigger Yield;;; src)
             (OMod.close_itree ClientImpl.omod (ModAdd (SCMem.mod gvs) ABSLock.mod) (R:=unit) (OMod.call "unlock" ());;; tgt)).
  Proof.
    iIntros "[[EXCL [% [DUTY [LOCK TAX]]]] SIM]".
    rewrite close_itree_call. ss. rred.
    iApply (stsim_yieldR with "[DUTY TAX]"). msubtac. iFrame.
    iIntros "DUTY _". rred.
    unfold ABSLock.unlock_fun, Mod.wrap_fun. rred.
    iopen 1 "I1" "K1". do 4 (iDestruct "I1" as "[% I1]").
    iDestruct "I1" as "[B1 [B2 [MEM [STGT [BLKS [SUM [CONTRA | CASE]]]]]]]".
    { iDestruct "CONTRA" as "[_ [_ EXCL2]]". iPoseProof (OwnM_valid with "[EXCL EXCL2]") as "%".
      { instantiate (1:= (Excl.just (): Excl.t unit) ⋅ (Excl.just (): Excl.t unit)).
        iSplitL "EXCL". all: iFrame. }
      eapply Excl.wf in H. inversion H.
    }
    iDestruct "CASE" as "[% [JPEND [JBLK [JCOR AMPs]]]]". subst own.
    iApply stsim_getR. iSplit. iFrame. rred.
    iApply stsim_tauR. rred.
    iApply stsim_getR. iSplit. iFrame. rred.
    iApply stsim_tauR. rred.
    iApply stsim_getR. iSplit. iFrame. rred.
    iApply (stsim_putR with "STGT"). iIntros "STGT". rred.
    iApply stsim_tauR. rred.
    iApply stsim_tauR. rred.

    iPoseProof (black_white_equal with "B2 LOCK") as "%". subst.
    iMod ("K1" with "[EXCL LOCK B1 B2 MEM BLKS SUM STGT]") as "_".
    { unfold lock_will_unlock. iExists false, mem, wobl, k. iFrame.
      iLeft. iFrame. auto.
    }
    { msubtac. }
    iPoseProof (ObligationRA.pending_shot with "JPEND") as "> SHOT".
    iPoseProof (ObligationRA.duty_done with "DUTY SHOT") as "> DUTY".
    iApply "SIM". iFrame.
  Qed.

  Lemma correct_thread1 tid:
    (∃ k, (own_thread tid)
            ∗ (ObligationRA.duty (inl tid) [(k, Ord.from_nat 1)])
            ∗ (ObligationRA.taxes
                 [(k, Ord.from_nat 1)]
                 ((((Ord.omega × Ord.omega) × Ord.omega) ⊕ ((Ord.S Ord.O) × (o_w_cor))) ⊕ 3)%ord
              )
            ∗ (OwnM (OneShot.shot k))
            ∗ (ObligationRA.pending k (/ 2))
    )
      ⊢
      (stsim I tid (topset I) ibot5 ibot5
             (fun r_src r_tgt => own_thread tid ** ObligationRA.duty (inl tid) [] ** ⌜r_src = r_tgt⌝)
             (ClientSpec.thread1 tt)
             (OMod.close_itree ClientImpl.omod (ModAdd (SCMem.mod gvs) ABSLock.mod) (ClientImpl.thread1 tt))).
  Proof.
    iIntros "[% [TH [DUTY [TAXES [#KSHOT KPENDh]]]]]".
    unfold ClientSpec.thread1, ClientImpl.thread1. rred.
    iPoseProof (ObligationRA.taxes_ord_split_one with "TAXES") as "> [TAXES TAX]".
    { apply Hessenberg.lt_add_r. instantiate (1:=2). apply OrdArith.lt_from_nat. auto. }
    iApply ABSLock_lock. iFrame. iIntros "[MYTH [[% [DUTY [WHI LOCK]]] EXCL]]".
    instantiate (1:=2). rred.
    rewrite close_itree_call. ss. rred.
    iPoseProof (ObligationRA.white_eq with "WHI") as "WHI".
    { rewrite Ord.from_nat_S. rewrite Jacobsthal.mult_S. reflexivity. }
    iPoseProof (ObligationRA.white_split_eq with "WHI") as "[WHI1 WHI2]".
    iApply (stsim_yieldR with "[DUTY WHI1 TAX]"). msubtac.
    { iSplitL "DUTY". iFrame.
      iApply ObligationRA.tax_cons_fold. iSplitL "WHI1"; auto.
      iApply ObligationRA.white_eq. 2: iFrame. symmetry; apply Jacobsthal.mult_1_l.
    }
    iIntros "DUTY _". rred. unfold SCMem.store_fun, Mod.wrap_fun. rred.

    iopen 0 "I0" "K0". iDestruct "I0" as "[% [i0BLK [i0KCOR [#i0KSHOT [i0PEND | i0SHOT]]]]]".
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

    iopen 1 "I1" "K1". do 4 (iDestruct "I1" as "[% I1]").
    iDestruct "I1" as "[i1B1 [i1B2 [i1MEM [i1STGT I1]]]]".

    iApply stsim_getR. iSplit. iFrame. rred. iApply stsim_tauR. rred.
    iPoseProof (memory_ra_store with "i1MEM i0PTR") as "[% [%STORE > [i1MEM i0PTR]]]".
    rewrite STORE. rred.
    iApply stsim_getR. iSplit. iFrame. rred. iApply stsim_tauR. rred.
    iApply stsim_getR. iSplit. iFrame. rred.
    iApply (stsim_putR with "i1STGT"). iIntros "i1STGT". rred. iApply stsim_tauR. rred.
    iApply stsim_tauR. rred.

    rewrite Qp_inv_half_half.
    iPoseProof (ObligationRA.pending_shot with "KPEND") as "> #OBLKSHOT".

    iMod ("K0" with "[i0BLK i0KCOR i0PTR]") as "_".
    { unfold thread1_will_write. iExists _. iFrame. iSplitR; auto. }

    iMod ("K1" with "[i1B1 i1B2 i1MEM i1STGT I1]") as "_".
    { unfold lock_will_unlock. iExists own, m1, wobl, j0. iFrame. }
    msubtac.

    iPoseProof (ObligationRA.duty_permutation with "DUTY") as "DUTY".
    { eapply perm_swap. }
    iPoseProof (ObligationRA.duty_done with "DUTY OBLKSHOT") as "> DUTY".
    iApply ABSLock_unlock. iSplitL "LOCK EXCL WHI2 DUTY".
    { iFrame. iExists j. iFrame. iApply ObligationRA.tax_cons_fold. iSplitL; auto.
      iApply ObligationRA.white_eq. 2: iFrame.
      rewrite Jacobsthal.mult_1_l. rewrite Ord.from_nat_1. rewrite Jacobsthal.mult_1_r.
      reflexivity.
    }
    iIntros "DUTY". rred.
    iApply (stsim_sync with "[DUTY]"). msubtac. iFrame.
    iIntros "DUTY _". rred. iApply stsim_tauR. rred.
    iApply stsim_ret. iApply MUpd_intro. iFrame. auto.
  Qed.

  Lemma correct_thread2 tid:
    ((own_thread tid)
       ∗ (ObligationRA.duty (inl tid) [])
    )
      ⊢
      (stsim I tid (topset I) ibot5 ibot5
             (fun r_src r_tgt => own_thread tid ** ObligationRA.duty (inl tid) [] ** ⌜r_src = r_tgt⌝)
             (ClientSpec.thread2 tt)
             (OMod.close_itree ClientImpl.omod (ModAdd (SCMem.mod gvs) ABSLock.mod) (ClientImpl.thread2 tt))).
  Proof.
    iIntros "[MYTH DUTY]".
    unfold ClientSpec.thread2, ClientImpl.thread2. rred.
    iopen 0 "I0" "K0". iDestruct "I0" as "[% [[% #KBLK] [#KCOR [#KSHOT I0]]]]".
    iMod ("K0" with "[I0]") as "_".
    { unfold thread1_will_write. iExists k. iFrame. auto. }
    { msubtac. }

    (* induction *)
    iStopProof. revert tid k. pattern n. revert n.
    apply (well_founded_induction Ord.lt_well_founded). intros n IH. intros.
    iIntros "[#[KBLK [KCOR KSHOT]] [MYTH DUTY]]".
    rewrite OpenMod.unfold_iter. rred.
    iApply ABSLock_lock. iSplitL "MYTH DUTY".
    { iFrame. }
    iIntros "[MYTH [[% [DUTY [WHI LOCK]]] EXCL]]". instantiate (1:= 2). rred.

    rewrite close_itree_call. ss. rred.
    iPoseProof (ObligationRA.white_eq with "WHI") as "WHI".
    { rewrite Ord.from_nat_S. rewrite Jacobsthal.mult_S. reflexivity. }
    iPoseProof (ObligationRA.white_split_eq with "WHI") as "[WHI1 WHI2]".
    iApply (stsim_yieldR with "[DUTY WHI1]"). msubtac.
    { iSplitL "DUTY". iFrame.
      iApply ObligationRA.tax_cons_fold. iSplitL "WHI1"; auto.
      iApply ObligationRA.white_eq. 2: iFrame. symmetry; apply Jacobsthal.mult_1_l.
    }
    iIntros "DUTY _". rred. unfold SCMem.load_fun, Mod.wrap_fun. rred.

    iopen 0 "I0" "K0". iDestruct "I0" as "[% [i0BLK [i0KCOR [#i0KSHOT [i0PEND | i0SHOT]]]]]".
    { (* loop case *)
      iDestruct "i0PEND" as "[i0PENDh i0PTR]".
      iPoseProof (OwnM_valid with "[KSHOT i0KSHOT]") as "%AGR".
      { instantiate (1:= (OneShot.shot k) ⋅ (OneShot.shot k0)). iSplitL "KSHOT"; auto. }
      apply OneShot.shot_agree in AGR. subst k0.

      iopen 1 "I1" "K1". do 4 (iDestruct "I1" as "[% I1]").
      iDestruct "I1" as "[i1B1 [i1B2 [i1MEM [i1STGT I1]]]]".
      iApply stsim_getR. iSplit. iFrame. rred. iApply stsim_tauR. rred.
      iPoseProof (memory_ra_load with "i1MEM i0PTR") as "[%LOAD %PERM]".
      rewrite LOAD. rred. iApply stsim_tauR. rred.

      iMod ("K0" with "[i0BLK i0KCOR i0PTR i0PENDh]") as "_".
      { unfold thread1_will_write. iExists _. iFrame. iSplitR; auto. iLeft; iFrame. }
      iMod ("K1" with "[i1B1 i1B2 i1MEM i1STGT I1]") as "_".
      { unfold lock_will_unlock. iExists own, mem, wobl, j0. iFrame. }
      msubtac.
      iApply ABSLock_unlock. iSplitL "LOCK EXCL WHI2 DUTY".
      { iFrame. iExists j. iFrame. iApply ObligationRA.tax_cons_fold. iSplitL; auto.
        iApply ObligationRA.white_eq. 2: iFrame.
        rewrite Jacobsthal.mult_1_l. rewrite Ord.from_nat_1. rewrite Jacobsthal.mult_1_r.
        reflexivity.
      }
      iIntros "DUTY". rred.

      rewrite close_itree_call. ss. rred.
      iApply (stsim_yieldR with "[DUTY]"). msubtac. iFrame. iIntros "DUTY OWHTH". rred.
      unfold Mod.wrap_fun, SCMem.compare_fun. rred.

      iApply stsim_getR. iSplit. iFrame. rred. iApply stsim_tauR. rred.
      iApply stsim_getR. iSplit. iFrame. rred.
      iApply (stsim_putR with "i1STGT"). iIntros "i1STGT". rred. iApply stsim_tauR. rred.
      iApply stsim_tauR. rred.
      
      
    

  (* TODO *)

  Let config := [("thread1", tt↑); ("thread2", tt↑)].

  Lemma client_correct:
    UserSim.sim ClientSpec.mod ClientImpl.mod
                (prog2ths ClientSpec.mod config)
                (prog2ths ClientImpl.mod config).
  Proof.
    refine (@UserSim.mk _ _ _ _ ord_wf nat_wf _ _ Σ _ _).
    { econs. exact 0. }
    { i. exists (S o0). ss. }
    ss.
    cut (forall tid,
            (own_thread tid ** ObligationRA.duty (inl tid) []) ⊢ stsim I tid [0; 1] ibot5 ibot5 (fun r_src r_tgt => own_thread tid ** ObligationRA.duty (inl tid) [] ** ⌜r_src = r_tgt⌝) (example_spec_fun tt) (OMod.close_itree (example_omod) (SCMem.mod [1; 1]) (example_fun tt))).
    { admit. }
    iIntros (?) "[TH DUTY]". unfold example_spec_fun, example_fun.
    lred. rred. rewrite close_itree_call. ss. rred.
    iApply (stsim_yieldR with "[DUTY]"); [msubtac|iFrame|]. iIntros "DUTY _".
    rred. unfold SCMem.cas_fun, Mod.wrap_fun. rred.
    iopen 0 "[% [MEM ST]]" "K0".
    iApply stsim_getR. iSplit.
    { iFrame. }
    rred. iApply stsim_tauR. rred.
    unfold SCMem.cas.
    iopen 1 "[[[POINTL POINTF] PEND]|[% H]]" "K1".
  Abort.

End SIM.
