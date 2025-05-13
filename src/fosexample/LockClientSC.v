From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.

From Fairness Require Export
     ITreeLib WFLibLarge FairBeh Mod pind Axioms
     Linking SCM Red IRed WeakestAdequacy FairLock Concurrency.
From Ordinal Require Export ClassicalHessenberg.
From Fairness Require Import NatStructs.

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
    ktree (threadE void unit) unit unit
    :=
    fun _ =>
      `_: unit <- (OMod.call "lock" tt);;
      `_: unit <- (OMod.call "store" (loc_X, const_42));;
      `_: unit <- (OMod.call "unlock" tt);;
      _ <- trigger Yield;;
      Ret tt.

  Definition thread2:
    ktree (threadE void unit) unit unit
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
      | SCMem.val_nat n => _ <- trigger (Observe 0 [n]);;
                          _ <- trigger Yield;;
                          Ret tt
      | _ => UB
      end.

  Definition omod: Mod.t :=
    Mod.mk
      tt
      (Mod.get_funs [("thread1", Mod.wrap_fun thread1);
                     ("thread2", Mod.wrap_fun thread2)])
  .

  Definition mod: Mod.t :=
    OMod.close
      (omod)
      (ModAdd (SCMem.mod gvs) AbsLock.mod)
  .

End ClientImpl.


Module ClientSpec.
  Definition thread1:
    ktree (threadE void unit) unit unit
    :=
    fun _ =>
      _ <- trigger Yield;; Ret tt.

  Definition thread2:
    ktree (threadE void unit) unit unit
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
      IPMFOS Weakest ModSim PCMFOS MonotonePCM StateRA FairRA NatMapRAFOS.

Import NatStructs.

Section SIM.

  Context `{Σ: GRA.t}.

  Context `{MONORA: @GRA.inG monoRA Σ}.
  Context `{THDRA: @GRA.inG ThreadRA Σ}.
  Context `{STATESRC: @GRA.inG (stateSrcRA (unit)) Σ}.
  (* Context `{STATETGT: @GRA.inG (stateTgtRA (unit * (SCMem.t * (bool * NatMap.t unit)))) Σ}. *)
  Context `{STATETGT: @GRA.inG (stateTgtRA ((OMod.closed_state ClientImpl.omod (ModAdd (SCMem.mod gvs) AbsLock.mod)))) Σ}.
  Context `{IDENTSRC: @GRA.inG (identSrcRA (void)) Σ}.
  (* Context `{IDENTTGT: @GRA.inG (identTgtRA (void + (SCMem.val + thread_id))%type) Σ}. *)
  Context `{IDENTTGT: @GRA.inG (identTgtRA (OMod.closed_ident ClientImpl.omod (ModAdd (SCMem.mod gvs) AbsLock.mod))%type) Σ}.

  Context `{OBLGRA: @GRA.inG ObligationRA.t Σ}.
  (* Context `{ARROWRA: @GRA.inG (ArrowRA (void + (SCMem.val + thread_id))%type) Σ}. *)
  Context `{ARROWRA: @GRA.inG (ArrowRA (OMod.closed_ident ClientImpl.omod (ModAdd (SCMem.mod gvs) AbsLock.mod))%type) Σ}.
  Context `{EDGERA: @GRA.inG EdgeRA Σ}.
  Context `{ONESHOTSRA: @GRA.inG (@FiniteMap.t (OneShot.t unit)) Σ}.

  Context `{MEMRA: @GRA.inG memRA Σ}.

  Context `{EXCL: @GRA.inG (Excl.t unit) Σ}.
  Context `{ONESHOTRA: @GRA.inG (OneShot.t nat) Σ}.
  Context `{REGIONRA: @GRA.inG (Region.t (thread_id * nat)) Σ}.
  Context `{CONSENTRA: @GRA.inG (@FiniteMap.t (Consent.t nat)) Σ}.
  Context `{AUTHNRA: @GRA.inG (Auth.t (Excl.t nat)) Σ}.
  (* Context `{AUTHUNITRA: @GRA.inG (Auth.t (Excl.t unit)) Σ}. *)
  (* Context `{AUTHNMRA: @GRA.inG (Auth.t (NatMapRAFOS.t unit)) Σ}. *)
  Context `{AUTHNMNRA: @GRA.inG (Auth.t (NatMapRAFOS.t nat)) Σ}.
  (* Context `{AUTHNMNN: @GRA.inG (Auth.t (NatMapRAFOS.t (nat * nat))) Σ}. *)

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
    ∃ (own: bool) (mem: SCMem.t) (wobl: NatStructs.NatMap.t nat) (j: nat),
      (OwnM (Auth.black (Some wobl: NatMapRAFOS.NatMapRAFOS.t nat)))
        ∗
        (OwnM (Auth.black (Excl.just j: Excl.t nat)))
        ∗
        (memory_black mem)
        ∗
        (St_tgt (tt, (mem, (own, key_set wobl))))
        ∗
        (FairRA.blacks (inrp ⋅ (inrp ⋅ inrp))%prism (fun id => (~ NatMap.In id wobl)))
        ∗
        (natmap_prop_sum wobl
                         (fun tid idx =>
                            (own_thread tid)
                              ∗
                              (ObligationRA.correl (inrp ⋅ (inrp ⋅ inrp))%prism tid idx o_w_cor)
                              ∗
                              (ObligationRA.pending idx 1)
                              ∗
                              (ObligationRA.duty (inrp ⋅ (inrp ⋅ inrp))%prism tid [(idx, o_w_cor)])
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


  Variable Invs : @InvSet Σ.
  Context `{COPSETRA : @GRA.inG CoPset.t Σ}.
  Context `{GSETRA : @GRA.inG Gset.t Σ}.
  Context `{INVSETRA : @GRA.inG (InvSetRA Var) Σ}.


  Variable N_lock : stdpp.namespaces.namespace.
  (* Let I: list iProp := [thread1_will_write; lock_will_unlock]. *)

    (* (inv N ticket_lock_inv) ∗ *)


  Lemma AbsLock_lock
        R_src R_tgt tid
        (src: thread void (sE unit) R_src)
        tgt
        r g
        (Q: R_src -> R_tgt -> iProp)
        (l: list (nat * Ord.t)%type)
        (num_line: nat)
    :
    ((inv N_lock lock_will_unlock)
       ∗
       (own_thread tid)
       ∗
       (ObligationRA.duty inlp tid l)
       ∗
       (ObligationRA.taxes
          l ((((Ord.omega × Ord.omega) × Ord.omega)
                ⊕
                ((Ord.S Ord.O) × (o_w_cor)))
               ⊕ 9)%ord))
      ∗
      (((own_thread tid)
          ∗
          (∃ j, (ObligationRA.duty inlp tid ((j, Ord.S Ord.O) :: l))
                  ∗
                  (ObligationRA.white j (Ord.omega × (Ord.from_nat num_line))%ord)
                  ∗
                  (OwnM (Auth.white (Excl.just j: Excl.t nat)))
          )
          ∗
          (OwnM (Excl.just tt: Excl.t unit)))
         -∗
         (stsim tid ⊤ r g Q
                false false
                (trigger Yield;;; src)
                (tgt)))
      ⊢
      (stsim tid ⊤ r g Q
             false false
             (trigger Yield;;; src)
             ((OMod.close_itree ClientImpl.omod (ModAdd (SCMem.mod gvs) AbsLock.mod) (R:=unit) (OMod.call "lock" ()));;; tgt)).
  Proof.
    Opaque key_set.
    iIntros "[[# LOCK_INV [TH [DUTY TAXES]]] SIM]".
    rewrite close_itree_call. ss. unfold OMod.emb_callee, emb_r. rewrite <- map_event_compose. rewrite <- plmap_compose. rred.
    iPoseProof (ObligationRA.taxes_ord_split_one with "TAXES") as "TAXES".
    { eapply Hessenberg.lt_add_r. apply OrdArith.lt_from_nat. instantiate (1:=8). auto. }
    iMod "TAXES". iDestruct "TAXES" as "[TAXES TAX]".

    iApply (stsim_yieldR with "[DUTY TAX]"). ss. iFrame.
    iIntros "DUTY _". rred.
    unfold AbsLock.lock_fun, Mod.wrap_fun. rred.
    iPoseProof (ObligationRA.taxes_ord_split_one with "TAXES") as "TAXES".
    { eapply Hessenberg.lt_add_r. apply OrdArith.lt_from_nat. instantiate (1:=7). auto. }
    iMod "TAXES". iDestruct "TAXES" as "[TAXES TAX]".

    iApply (stsim_yieldR with "[DUTY TAX]"). ss. iFrame.
    iIntros "DUTY _". rred.
    iApply stsim_tidR. rred.

    iInv "LOCK_INV" as "I1" "K1". do 4 (iDestruct "I1" as "[% I1]").
    iDestruct "I1" as "[B1 [B2 [MEM [STGT I1]]]]".
    iApply stsim_getR. iSplit. iFrame. rred.
    iApply (stsim_modifyR with "STGT"). iIntros "STGT". rred.

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
    set (blks2 := fun id => ¬ NatMap.In id (NatMap.add tid k wobl)).
    iPoseProof (FairRA.blacks_unfold with "BLKS") as "[BLKS MYDUTY]".
    { instantiate (1:=tid). instantiate (1:=blks2). i. des; subst.
      { subst blks2. ss. ii; apply IN. apply NatMapP.F.add_in_iff; auto. }
      { subst blks2. ss. }
    }
    { subst blks2. ss. ii. eapply H0. apply NatMapP.F.add_in_iff. auto. }
    iPoseProof (ObligationRA.black_to_duty with "MYDUTY") as "MYDUTY".
    iPoseProof (ObligationRA.duty_alloc with "MYDUTY") as "MYDUTY".
    iPoseProof ("MYDUTY" with "MYW") as "> MYDUTY".
    iPoseProof (ObligationRA.duty_correl with "MYDUTY") as "# MYCOR".
    { ss. left; eauto. }

    (* make (Auth.white singleton tid k) and update wobl *)
    iPoseProof (OwnM_Upd with "B1") as "OWN1".
    { eapply Auth.auth_alloc. instantiate (1:=NatMapRAFOS.singleton tid k).
      instantiate (1:=Some (NatMap.add tid k wobl)). eapply NatMapRAFOS.add_local_update.
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

    (* induction *)
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
    iIntros "[# LOCK_INV [SIM [DUTY [MYB [MYW [TAXES TAXKEEP]]]]]]".
    rewrite unfold_iter_eq. rred.

    iPoseProof (ObligationRA.taxes_ord_split_one with "TAXES") as "> [TAXES TAX]". eauto.
    iApply (stsim_yieldR with "[DUTY TAX]"). ss. iFrame.
    iIntros "DUTY WTH". rred.
    iInv "LOCK_INV" as "I1" "K1". do 4 (iDestruct "I1" as "[% I1]").
    iDestruct "I1" as "[B1 [B2 [MEM [STGT I1]]]]".
    iApply stsim_getR. iSplit. iFrame. rred.
    destruct own.

    (* someone is holding the lock *)
    { rred.
      iApply stsim_tauR. rred.

      iAssert (⌜NatMap.find tid wobl = Some k⌝)%I as "%".
      { iPoseProof (OwnM_valid with "[MYW B1]") as "%".
        { instantiate (1:= (Auth.black (Some wobl: NatMapRAFOS.t nat)) ⋅ (Auth.white (NatMapRAFOS.singleton tid k: NatMapRAFOS.t nat))). iSplitL "B1"; iFrame. }
        eapply Auth.auth_included in H. eapply NatMapRAFOS.extends_singleton_iff in H.
        auto.
      }
      rename H into FIND.

      iDestruct "I1" as "[BLKS [SUM CASES]]".
      iDestruct "CASES" as "[[%OWNF [LOCK EXCL]] | [%OWNT [JPEND [JBLK [#JCOR AMPs]]]]]".
      { inversion OWNF. }

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
          { unfold lock_will_unlock. iExists true, mem, wobl, j. iFrame.
            iRight. iFrame. iSplit; auto.
          }
          iApply IH. eapply RENEW. eapply RENEW.
          iFrame. auto.
        }
      }
    }

    (* no one is holding the lock *)
    { rred.
      iClear "TAXES". clear IH credit RICH.
      iApply stsim_getR. iSplit. iFrame. rred.
      iApply (stsim_modifyR with "STGT"). iIntros "STGT". rred.

      iDestruct "I1" as "[BLKS [SUM [[_ [LOCK EXCL]] | [%CONTRA _]]]]".
      2:{ inversion CONTRA. }
      iAssert (⌜NatMap.find tid wobl = Some k⌝)%I as "%".
      { iPoseProof (OwnM_valid with "[MYW B1]") as "%".
        { instantiate (1:= (Auth.black (Some wobl: NatMapRAFOS.t nat)) ⋅ (Auth.white (NatMapRAFOS.singleton tid k: NatMapRAFOS.t nat))). iSplitL "B1"; iFrame. }
        eapply Auth.auth_included in H. eapply NatMapRAFOS.extends_singleton_iff in H.
        auto.
      }
      rename H into FIND.

      iPoseProof (natmap_prop_remove_find with "SUM") as "[[MYTH [_ [MYPEND MYDUTY]]] SUM]".
      eapply FIND. iPoseProof (ObligationRA.pending_shot with "MYPEND") as "> MYDONE".
      iPoseProof (ObligationRA.duty_done with "MYDUTY MYDONE") as "> MYDUTY".
      iApply (stsim_fairR_prism with "[MYDUTY]").
      4:{ instantiate (1:=[(tid, [])]). ss. iFrame. }
      { clear. i. ss. des_ifs. auto. }
      { instantiate (1:= List.map fst (NatMap.elements (NatMap.remove tid (key_set wobl)))). clear. i. unfold prism_fmap.
        assert (A: (NatMap.In i (NatMap.remove tid (key_set wobl)))).
        { apply in_map_iff in IN. des. subst. destruct x. destruct u.
          remember (NatMap.remove tid (key_set wobl)) as M. clear HeqM.
          apply NatMapP.F.elements_in_iff. exists (). apply SetoidList.InA_alt.
          exists (k, tt). ss.
        }
        des. subst. unfold Prism.preview; ss. des_ifs.
        exfalso. eapply NatMap.remove_1. ss. eapply A.
      }
      { eapply FinFun.Injective_map_NoDup.
        { unfold FinFun.Injective. i. destruct x, y. destruct u, u0. ss. subst. auto. }
        apply NoDupA_NoDup. apply NatMap.elements_3w.
      }
      iIntros "MYDUTY WHITES". rred.

      (* close invariant *)
      iPoseProof (OwnM_Upd with "[B1 MYW]") as "> B1".
      2:{ instantiate (1:= (Auth.black (Some wobl: NatMapRAFOS.t nat)) ⋅ (Auth.white (NatMapRAFOS.singleton tid k: NatMapRAFOS.t nat))). iSplitL "B1"; iFrame. }
      { eapply Auth.auth_dealloc. eapply NatMapRAFOS.remove_local_update. }
      rewrite <- key_set_pull_rm_eq in *. remember (NatMap.remove tid wobl) as new_wobl.

      iPoseProof (MonotonePCM.list_prop_sum_cons_unfold with "MYDUTY") as "[MYDUTY _]".
      iPoseProof (ObligationRA.duty_to_black with "MYDUTY") as "MYBEX".
      iPoseProof (FairRA.blacks_fold with "[BLKS MYBEX]") as "BLKS".
      2:{ iFrame. }
      { instantiate (1:=fun id => ¬ NatMap.In (elt:=nat) id new_wobl).
        i. ss. des. destruct (tid_dec j0 tid) eqn:DEC.
        - clarify. auto.
        - left. esplits; eauto. ii. apply IN. subst. apply NatMapP.F.remove_in_iff.
          split; auto.
      }

      ss. repeat (unfold Lens.modify, Lens.set; ss). iClear "MYB".
      clear Heqnew_wobl FIND wd k wobl.
      iPoseProof (ObligationRA.alloc o_w_cor) as "> [% [[NEWB NEWW] NEWP]]".
      iPoseProof (OwnM_Upd with "[B2 LOCK]") as "> B2".
      2:{ instantiate (1:= (Auth.black (Excl.just j: Excl.t nat)) ⋅ (Auth.white (Excl.just j: Excl.t nat))). iSplitL "B2"; iFrame. }
      { eapply Auth.auth_update. do 2 instantiate (1:=Excl.just k).
        clear. ii. des. split.
        - ur. ss.
        - ur. ur in FRAME. des_ifs.
      }
      iDestruct "B2" as "[B2 LOCK]". clear j.

      iAssert (natmap_prop_sum new_wobl (fun tid0 idx => ObligationRA.correl (inrp ⋅ (inrp ⋅ inrp))%prism tid0 idx (Ord.omega × Ord.omega)%ord)) with "[SUM]" as "#CORs".
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
      iAssert (natmap_prop_sum new_wobl (fun k _ => FairRA.white (inrp ⋅ (inrp ⋅ inrp))%prism k 1))%I with "[WHITES]" as "WHITES".
      { Transparent key_set. unfold key_set. rewrite <- list_map_elements_nm_map. unfold natmap_prop_sum.
        remember (NatMap.elements new_wobl) as ml. clear Heqml. rewrite List.map_map.
        iClear "CORs NEWCORTH". clear. iStopProof. induction ml.
        { iIntros "SUM". ss. }
        ss. des_ifs. iIntros "[# LOCK_INV [WH SUM]]". iFrame. iApply IHml. auto.
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
        iIntros "# [LOCK_INV BLK]". des_ifs. iSplit; auto. iApply IHml. auto.
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

      iApply (stsim_yieldR with "[DUTY TAXKEEP NEWWTAX]"). ss.
      { iSplitL "DUTY". iFrame. iFrame. iApply ObligationRA.white_eq.
        { symmetry. apply Jacobsthal.mult_1_l. }
        iFrame.
      }
      iIntros "DUTY _". rred.
      iApply stsim_tauR. rred.
      iPoseProof ("SIM" with "[MYTH DUTY NEWW2 EXCL LOCK]") as "SIM".
      iFrame. iExists k. iFrame.
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
    :
    ((inv N_lock lock_will_unlock)
       ∗
       (OwnM (Excl.just tt: Excl.t unit))
       ∗
       (∃ k, (ObligationRA.duty inlp tid ((k, Ord.S Ord.O) :: l))
               ∗ (OwnM (Auth.white (Excl.just k: Excl.t nat)))
               ∗ (ObligationRA.taxes ((k, Ord.S Ord.O) :: l) 3%ord))
    )
      ∗
      ((ObligationRA.duty inlp tid l)
         -∗
         (stsim tid ⊤ r g Q
                false false
                (trigger Yield;;; src)
                (tgt)))
      ⊢
      (stsim tid ⊤ r g Q
             false false
             (trigger Yield;;; src)
             (OMod.close_itree ClientImpl.omod (ModAdd (SCMem.mod gvs) AbsLock.mod) (R:=unit) (OMod.call "unlock" ());;; tgt)).
  Proof.
    iIntros "[[# LOCK_INV [EXCL [% [DUTY [LOCK TAXES]]]]] SIM]".
    iPoseProof (ObligationRA.taxes_ord_split_one with "TAXES") as "> [TAXES TAX]".
    { instantiate (1:= 2%ord). apply OrdArith.lt_from_nat. lia. }
    iPoseProof (ObligationRA.taxes_ord_split_one with "TAXES") as "> [TAXES TAX1]".
    { instantiate (1:= 1%ord). apply OrdArith.lt_from_nat. lia. }
    iPoseProof (ObligationRA.taxes_single_is_tax with "TAXES") as "TAX2".

    rewrite close_itree_call. ss. unfold OMod.emb_callee, emb_r. rewrite <- map_event_compose. rewrite <- plmap_compose. rred.
    iApply (stsim_yieldR with "[DUTY TAX]"). ss. iFrame.
    iIntros "DUTY _". rred.
    unfold AbsLock.unlock_fun, Mod.wrap_fun. rred.
    iApply (stsim_yieldR with "[DUTY TAX1]"). ss. iFrame.
    iIntros "DUTY _". rred.


    iInv "LOCK_INV" as "I1" "K1". do 4 (iDestruct "I1" as "[% I1]").
    iDestruct "I1" as "[B1 [B2 [MEM [STGT [BLKS [SUM [CONTRA | CASE]]]]]]]".
    { iDestruct "CONTRA" as "[_ [_ EXCL2]]". iPoseProof (OwnM_valid with "[EXCL EXCL2]") as "%".
      { instantiate (1:= (Excl.just (): Excl.t unit) ⋅ (Excl.just (): Excl.t unit)).
        iSplitL "EXCL". all: iFrame. }
      eapply Excl.wf in H. inversion H.
    }
    iDestruct "CASE" as "[% [JPEND [JBLK [JCOR AMPs]]]]". subst own.
    iApply stsim_getR. iSplit. iFrame. rred.
    iApply (stsim_modifyR with "STGT"). iIntros "STGT". rred.

    iPoseProof (black_white_equal with "B2 LOCK") as "%". subst.
    iMod ("K1" with "[EXCL LOCK B1 B2 MEM BLKS SUM STGT]") as "_".
    { unfold lock_will_unlock. iExists false, mem, wobl, k. iFrame.
      iLeft. iFrame. auto.
    }
    iPoseProof (ObligationRA.pending_shot with "JPEND") as "> SHOT".
    iPoseProof (ObligationRA.duty_done with "DUTY SHOT") as "> DUTY".

    iApply (stsim_yieldR with "[DUTY TAX2]"). ss.
    { iSplitL "DUTY". iFrame.
      iPoseProof (ObligationRA.tax_cons_unfold with "TAX2") as "[_ TAX2]". iFrame.
    }
    iIntros "DUTY _". rred.
    iApply stsim_tauR. rred.
    iApply stsim_reset. iApply "SIM". iFrame.

  Qed.

  Variable N_user : stdpp.namespaces.namespace.
  Variable N_user_N_lock_disjoint: N_user ## N_lock.

  Lemma correct_thread1 tid:
    (inv N_lock lock_will_unlock) **
    (inv N_user thread1_will_write) **
    (∃ k, (own_thread tid)
            ∗ (ObligationRA.duty inlp tid [(k, Ord.from_nat 1)])
            ∗ (ObligationRA.taxes
                 [(k, Ord.from_nat 1)]
                 ((((Ord.omega × Ord.omega) × Ord.omega) ⊕ ((Ord.S Ord.O) × (o_w_cor))) ⊕ 10)%ord
              )
            ∗ (OwnM (OneShot.shot k))
            ∗ (ObligationRA.pending k (/ 2))
    )
      ⊢
      (stsim tid ⊤ ibot7 ibot7
             (fun r_src r_tgt => own_thread tid ** ObligationRA.duty inlp tid [] ** ⌜r_src = r_tgt⌝)
             false false
             (ClientSpec.thread1 tt)
             (OMod.close_itree ClientImpl.omod (ModAdd (SCMem.mod gvs) AbsLock.mod) (ClientImpl.thread1 tt))).
  Proof.
    iIntros "[# [LOCK_INV WILL_WRITE] [% [TH [DUTY [TAXES [#KSHOT KPENDh]]]]]]".
    unfold ClientSpec.thread1, ClientImpl.thread1. rred.
    iPoseProof (ObligationRA.taxes_ord_split_one with "TAXES") as "> [TAXES TAX]".
    { apply Hessenberg.lt_add_r. instantiate (1:=9). apply OrdArith.lt_from_nat. auto. }
    iApply AbsLock_lock. iFrame. iSplit.
    { auto. }
    iIntros "[MYTH [[% [DUTY [WHI LOCK]]] EXCL]]".
    instantiate (1:=4). rred.
    rewrite close_itree_call. ss. unfold OMod.emb_callee, emb_l. rewrite <- map_event_compose. rewrite <- plmap_compose. rred.
    iPoseProof (ObligationRA.white_eq with "WHI") as "WHI".
    { rewrite Ord.from_nat_S. rewrite Jacobsthal.mult_S. reflexivity. }
    iPoseProof (ObligationRA.white_split_eq with "WHI") as "[WHI1 WHI2]".
    iApply (stsim_yieldR with "[DUTY WHI1 TAX]"). ss.
    { iSplitL "DUTY". iFrame.
      iApply ObligationRA.tax_cons_fold. iSplitL "WHI1"; auto.
      iApply ObligationRA.white_eq. 2: iFrame. symmetry; apply Jacobsthal.mult_1_l.
    }
    iIntros "DUTY _". rred. unfold SCMem.store_fun, Mod.wrap_fun. rred.

    iInv "WILL_WRITE" as "I0" "K0". iDestruct "I0" as "[% [i0BLK [i0KCOR [#i0KSHOT [i0PEND | i0SHOT]]]]]".
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

    iInv "LOCK_INV" as "I1" "K1".
    do 4 (iDestruct "I1" as "[% I1]").
    iDestruct "I1" as "[i1B1 [i1B2 [i1MEM [i1STGT I1]]]]".

    iApply stsim_getR. iSplit. iFrame. rred.
    iPoseProof (memory_ra_store with "i1MEM i0PTR") as "[% [%STORE > [i1MEM i0PTR]]]".
    rewrite STORE. rred.
    iApply (stsim_modifyR with "i1STGT"). iIntros "i1STGT". rred. iApply stsim_tauR. rred.

    rewrite Qp.inv_half_half.
    iPoseProof (ObligationRA.pending_shot with "KPEND") as "> #OBLKSHOT".

    iMod ("K1" with "[i1B1 i1B2 i1MEM i1STGT I1]") as "_".
    { unfold lock_will_unlock. iExists own, m1, wobl, j0. iFrame. }

    iMod ("K0" with "[i0BLK i0KCOR i0PTR]") as "_".
    { unfold thread1_will_write. iExists _. iFrame. iSplitR; auto. }

    iPoseProof (ObligationRA.duty_permutation with "DUTY") as "DUTY".
    { eapply perm_swap. }
    iPoseProof (ObligationRA.duty_done with "DUTY OBLKSHOT") as "> DUTY".
    iApply stsim_reset. iApply AbsLock_unlock. iSplitL "LOCK EXCL WHI2 DUTY".
    { iFrame. iSplit; [auto|].
      iExists j. iFrame. iApply ObligationRA.taxes_cons_fold. iSplitL; auto.
      iApply ObligationRA.white_eq. 2: iFrame.
      rewrite Jacobsthal.mult_1_l. reflexivity.
    }
    iIntros "DUTY". rred.
    iApply (stsim_sync with "[DUTY]"). ss. iFrame.
    iIntros "DUTY _". rred. iApply stsim_tauR. rred.
    iApply stsim_ret. iModIntro. iFrame. auto.

  Qed.

  Lemma correct_thread2 tid:
    (inv N_lock lock_will_unlock) **
    (inv N_user thread1_will_write) **
    ((own_thread tid)
       ∗ (ObligationRA.duty inlp tid [])
    )
      ⊢
      (stsim tid ⊤ ibot7 ibot7
             (fun r_src r_tgt => own_thread tid ** ObligationRA.duty inlp tid [] ** ⌜r_src = r_tgt⌝)
             false false
             (ClientSpec.thread2 tt)
             (OMod.close_itree ClientImpl.omod (ModAdd (SCMem.mod gvs) AbsLock.mod) (ClientImpl.thread2 tt))).
  Proof.
    iIntros "[# [LOCK_INV WILL_WRITE] [MYTH DUTY]]".
    unfold ClientSpec.thread2, ClientImpl.thread2. rred.
    iInv "WILL_WRITE" as "I0" "K0". iDestruct "I0" as "[% [[% #KBLK] [#KCOR [#KSHOT I0]]]]".
    iMod ("K0" with "[I0]") as "_".
    { unfold thread1_will_write. iExists k. iFrame. auto. }

    (* induction *)
    iStopProof. revert tid k. pattern n. revert n.
    apply (well_founded_induction Ord.lt_well_founded). intros n IH. intros.
    iIntros "[# [LOCK_INV [WILL_WRITE [KBLK [KCOR KSHOT]]]] [MYTH DUTY]]".
    rewrite unfold_iter_eq. rred.
    iApply AbsLock_lock. iSplitL "MYTH DUTY".
    { iFrame. auto. }
    iIntros "[MYTH [[% [DUTY [WHI LOCK]]] EXCL]]". instantiate (1:= 4). rred.

    rewrite close_itree_call. ss. unfold OMod.emb_callee, emb_l. rewrite <- map_event_compose. rewrite <- plmap_compose. rred.
    iPoseProof (ObligationRA.white_eq with "WHI") as "WHI".
    { rewrite Ord.from_nat_S. rewrite Jacobsthal.mult_S. reflexivity. }
    iPoseProof (ObligationRA.white_split_eq with "WHI") as "[WHI1 WHI2]".
    iApply (stsim_yieldR with "[DUTY WHI1]"). ss.
    { iSplitL "DUTY". iFrame.
      iApply ObligationRA.tax_cons_fold. iSplitL "WHI1"; auto.
      iApply ObligationRA.white_eq. 2: iFrame. symmetry; apply Jacobsthal.mult_1_l.
    }
    iIntros "DUTY _". rred. unfold SCMem.load_fun, Mod.wrap_fun. rred.

    iInv "WILL_WRITE" as "I0" "K0". iDestruct "I0" as "[% [i0BLK [i0KCOR [#i0KSHOT [i0PEND | i0SHOT]]]]]".
    (* iterate case *)
    { iDestruct "i0PEND" as "[i0PENDh i0PTR]".
      iPoseProof (OwnM_valid with "[KSHOT i0KSHOT]") as "%AGR".
      { instantiate (1:= (OneShot.shot k) ⋅ (OneShot.shot k0)). iSplitL "KSHOT"; auto. }
      apply OneShot.shot_agree in AGR. subst k0.

      iInv "LOCK_INV" as "I1" "K1". do 4 (iDestruct "I1" as "[% I1]").
      iDestruct "I1" as "[i1B1 [i1B2 [i1MEM [i1STGT I1]]]]".
      iApply stsim_getR. iSplit. iFrame. rred.
      iPoseProof (memory_ra_load with "i1MEM i0PTR") as "[%LOAD %PERM]".
      rewrite LOAD. rred. iApply stsim_tauR. rred.

      iMod ("K1" with "[i1B1 i1B2 i1MEM i1STGT I1]") as "_".
      { unfold lock_will_unlock. iExists own, mem, wobl, j0. iFrame. }
      iMod ("K0" with "[i0BLK i0KCOR i0PTR i0PENDh]") as "_".
      { unfold thread1_will_write. iExists _. iFrame. iSplitR; auto. iLeft; iFrame. }
      clear own mem wobl j0 LOAD PERM.
      iApply stsim_reset. iApply AbsLock_unlock. iSplitL "LOCK EXCL WHI2 DUTY".
      { iFrame. iSplit; [auto|]. iExists j. iFrame. iApply ObligationRA.taxes_cons_fold. iSplitL; auto.
        iApply ObligationRA.white_eq. 2: iFrame.
        rewrite Jacobsthal.mult_1_l. reflexivity.
      }
      iIntros "DUTY". rred.

      rewrite close_itree_call. ss. unfold OMod.emb_callee, emb_l. rewrite <- map_event_compose. rewrite <- plmap_compose. rred.
      iApply (stsim_yieldR with "[DUTY]"). ss. iFrame. iIntros "DUTY OWHTH". rred.
      unfold Mod.wrap_fun, SCMem.compare_fun. rred.
      iInv "LOCK_INV" as "I1" "K1". do 4 (iDestruct "I1" as "[% I1]").
      iDestruct "I1" as "[i1B1 [i1B2 [i1MEM [i1STGT I1]]]]".
      iApply stsim_getR. iSplit. iFrame. rred. iApply stsim_tauR. rred.
      iApply stsim_tauR. rred.
      iMod ("K1" with "[i1B1 i1B2 i1MEM i1STGT I1]") as "_".
      { unfold lock_will_unlock. iExists _, _, _, _. iFrame. }
      ss.
      iClear "i0KSHOT".
      iPoseProof (ObligationRA.correl_thread_correlate with "KCOR OWHTH") as "> [KWHI|#KDONE]".
      (* thread 1 not done; induction *)
      { iPoseProof (ObligationRA.black_white_decr_one with "KBLK KWHI") as "> [% [#KBLK2 %DECR]]".
        iClear "KBLK". iApply stsim_reset. iApply IH. apply DECR. iFrame. iModIntro. eauto.
      }

      (* thread 1 done; exit *)
      { iClear "KBLK KCOR". clear n j own mem wobl j0 IH.
        rewrite unfold_iter_eq. rred.
        iApply stsim_reset. iApply AbsLock_lock. iSplitL "MYTH DUTY".
        { iFrame. auto. }
        iIntros "[MYTH [[% [DUTY [WHI LOCK]]] EXCL]]". instantiate (1:= 4). rred.

        iInv "WILL_WRITE" as "I0" "K0". iDestruct "I0" as "[% [i0BLK [i0KCOR [#i0KSHOT [i0PEND | i0SHOT]]]]]".
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

        rewrite close_itree_call. ss. unfold OMod.emb_callee, emb_l. rewrite <- map_event_compose. rewrite <- plmap_compose. rred.
        iMod ("K0" with "[i0BLK i0KCOR i0PTR]") as "_".
        { unfold thread1_will_write. iExists _. iFrame. iSplitR; auto. }
        ss.
        iPoseProof (ObligationRA.white_eq with "WHI") as "WHI".
        { rewrite Ord.from_nat_S. rewrite Jacobsthal.mult_S. reflexivity. }
        iPoseProof (ObligationRA.white_split_eq with "WHI") as "[WHI1 WHI2]".
        iApply (stsim_yieldR with "[DUTY WHI1]"). ss.
        { iSplitL "DUTY". iFrame.
          iApply ObligationRA.tax_cons_fold. iSplitL "WHI1"; auto.
          iApply ObligationRA.white_eq. 2: iFrame. symmetry; apply Jacobsthal.mult_1_l.
        }
        iIntros "DUTY _". rred. unfold SCMem.load_fun, Mod.wrap_fun. rred.
        iInv "LOCK_INV" as "I1" "K1". do 4 (iDestruct "I1" as "[% I1]").
        iDestruct "I1" as "[i1B1 [i1B2 [i1MEM [i1STGT I1]]]]".
        iApply stsim_getR. iSplit. iFrame. rred.
        iInv "WILL_WRITE" as "I0" "K0". iClear "i0KSHOT".
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
        iPoseProof (memory_ra_load with "i1MEM i0PTR") as "[%LOAD %PERM]".
        rewrite LOAD. rred. iApply stsim_tauR. rred.

        iMod ("K0" with "[i0BLK i0KCOR i0PTR]") as "_".
        { unfold thread1_will_write. iExists _. iFrame. iSplitR; auto. }
        iMod ("K1" with "[i1B1 i1B2 i1MEM i1STGT I1]") as "_".
        { unfold lock_will_unlock. iExists own, mem, wobl, j0. iFrame. }
        ss.
        clear own mem wobl j0 LOAD PERM.
        iApply stsim_reset. iApply AbsLock_unlock. iSplitL "LOCK EXCL WHI2 DUTY".
        { iFrame. iSplit; [auto|]. iExists j. iFrame. iApply ObligationRA.taxes_cons_fold. iSplitL; auto.
          iApply ObligationRA.white_eq. 2: iFrame.
          rewrite Jacobsthal.mult_1_l. reflexivity.
        }
        iIntros "DUTY". rred.

        rewrite close_itree_call. ss. unfold OMod.emb_callee, emb_l. rewrite <- map_event_compose. rewrite <- plmap_compose. rred.
        iApply (stsim_yieldR with "[DUTY]"). ss. iFrame. iIntros "DUTY _". rred.
        unfold Mod.wrap_fun, SCMem.compare_fun. rred.
        iInv "LOCK_INV" as "I1" "K1". do 4 (iDestruct "I1" as "[% I1]").
        iDestruct "I1" as "[i1B1 [i1B2 [i1MEM [i1STGT I1]]]]".
        iApply stsim_getR. iSplit. iFrame. rred. iApply stsim_tauR. rred.

        rewrite close_itree_call. ss. unfold OMod.emb_callee, emb_l. rewrite <- map_event_compose. rewrite <- plmap_compose. rred.
        iMod ("K1" with "[i1B1 i1B2 i1MEM i1STGT I1]") as "_".
        { unfold lock_will_unlock. iExists own, mem, wobl, j0. iFrame. }
        iApply (stsim_sync with "[DUTY]"). ss.
        { iFrame. }
        iIntros "DUTY _". rred. unfold SCMem.load_fun, Mod.wrap_fun. rred.
        iInv "LOCK_INV" as "I1" "K1". do 4 (iDestruct "I1" as "[% I1]").
        iDestruct "I1" as "[i1B1 [i1B2 [i1MEM [i1STGT I1]]]]".
        iApply stsim_getR. iSplit. iFrame. rred.
        iInv "WILL_WRITE" as "I0" "K0". iClear "i0KSHOT".
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
        iPoseProof (memory_ra_load with "i1MEM i0PTR") as "[%LOAD %PERM]".
        rewrite LOAD. rred. iApply stsim_tauR. rred.

        iApply stsim_observe. iIntros. rred.
        iApply stsim_tauR. rred.
        iMod ("K0" with "[i0BLK i0KCOR i0PTR]") as "_".
        { unfold thread1_will_write. iExists _. iFrame. iSplitR; auto. }
        iMod ("K1" with "[i1B1 i1B2 i1MEM i1STGT I1]") as "_".
        { unfold lock_will_unlock. do 4 iExists _. iFrame. }
        ss.
        iApply (stsim_sync with "[DUTY]"). ss. iFrame.
        iIntros "DUTY _". rred.
        iApply stsim_tauR. rred.
        iApply stsim_ret. iModIntro. iFrame. auto.
      }
    }

    { iDestruct "i0SHOT" as "[#KDONE i0PTR]".
      iPoseProof (OwnM_valid with "[KSHOT i0KSHOT]") as "%AGR".
      { instantiate (1:= (OneShot.shot k) ⋅ (OneShot.shot k0)). iSplitL "KSHOT"; auto. }
      apply OneShot.shot_agree in AGR. subst k0.

      iInv "LOCK_INV" as "I1" "K1". do 4 (iDestruct "I1" as "[% I1]").
      iDestruct "I1" as "[i1B1 [i1B2 [i1MEM [i1STGT I1]]]]".
      iApply stsim_getR. iSplit. iFrame. rred.
      iPoseProof (memory_ra_load with "i1MEM i0PTR") as "[%LOAD %PERM]".
      rewrite LOAD. rred. iApply stsim_tauR. rred.

      iMod ("K1" with "[i1B1 i1B2 i1MEM i1STGT I1]") as "_".
      { unfold lock_will_unlock. do 4 iExists _. iFrame. }
      iMod ("K0" with "[i0BLK i0KCOR i0PTR]") as "_".
      { unfold thread1_will_write. iExists _. iFrame. iSplitR; auto. }
      ss.
      clear own mem wobl j0 LOAD PERM.
      iApply stsim_reset. iApply AbsLock_unlock. iSplitL "LOCK EXCL WHI2 DUTY".
      { iFrame. iSplit; [auto|]. iExists j. iFrame. iApply ObligationRA.taxes_cons_fold. iSplitL; auto.
        iApply ObligationRA.white_eq. 2: iFrame.
        rewrite Jacobsthal.mult_1_l. reflexivity.
      }
      iIntros "DUTY". rred.

      rewrite close_itree_call. ss. unfold OMod.emb_callee, emb_l. rewrite <- map_event_compose. rewrite <- plmap_compose. rred.
      iApply (stsim_yieldR with "[DUTY]"). ss. iFrame. iIntros "DUTY _". rred.
      unfold Mod.wrap_fun, SCMem.compare_fun. rred.
      iInv "LOCK_INV" as "I1" "K1". do 4 (iDestruct "I1" as "[% I1]").
      iDestruct "I1" as "[i1B1 [i1B2 [i1MEM [i1STGT I1]]]]".
      iApply stsim_getR. iSplit. iFrame. rred. iApply stsim_tauR. rred.

      rewrite close_itree_call. ss. unfold OMod.emb_callee, emb_l. rewrite <- map_event_compose. rewrite <- plmap_compose. rred.
      iMod ("K1" with "[i1B1 i1B2 i1MEM i1STGT I1]") as "_".
      { unfold lock_will_unlock. iExists own, mem, wobl, j0. iFrame. }
      ss.
      iApply (stsim_sync with "[DUTY]"). ss.
      { iFrame. }
      iIntros "DUTY _". rred. unfold SCMem.load_fun, Mod.wrap_fun. rred.
      iInv "LOCK_INV" as "I1" "K1". do 4 (iDestruct "I1" as "[% I1]").
      iDestruct "I1" as "[i1B1 [i1B2 [i1MEM [i1STGT I1]]]]".
      iApply stsim_getR. iSplit. iFrame. rred.
      iInv "WILL_WRITE" as "I0" "K0". iClear "i0KSHOT".
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
      iPoseProof (memory_ra_load with "i1MEM i0PTR") as "[%LOAD %PERM]".
      rewrite LOAD. rred. iApply stsim_tauR. rred.

      iApply stsim_observe. iIntros. rred.
      iApply stsim_tauR. rred.
      iMod ("K0" with "[i0BLK i0KCOR i0PTR]") as "_".
      { unfold thread1_will_write. iExists _. iFrame. iSplitR; auto. }
      iMod ("K1" with "[i1B1 i1B2 i1MEM i1STGT I1]") as "_".
      { unfold lock_will_unlock. do 4 iExists _. iFrame. }
      ss.
      iApply (stsim_sync with "[DUTY]"). ss. iFrame.
      iIntros "DUTY _". rred.
      iApply stsim_tauR. rred.
      iApply stsim_ret. iModIntro. iFrame. auto.
    }

  Qed.


  Let config := [("thread1", tt↑); ("thread2", tt↑)].
End SIM.
