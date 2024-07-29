From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Export
     ITreeLib WFLibLarge FairBeh NatStructsLarge Mod pind Axioms
     Linking WMMSpec Red IRed SimWeakestAdequacy FairLock Concurrency.
From PromisingLib Require Import Loc Event.
From PromisingSEQ Require Import View.
From Ordinal Require Export ClassicalHessenberg.
Require Import Coq.Numbers.BinNums.


Set Implicit Arguments.

Section INIT.

  Definition loc_X: Loc.t := Loc.of_nat 2.

  Definition const_0: Const.t := Const.of_Z (BinIntDef.Z.of_nat 0).
  Definition const_42: Const.t := Const.of_Z (BinIntDef.Z.of_nat 42).

End INIT.

Module ClientCode.

  Definition thread1:
    ktree (threadE void unit) unit unit
    :=
    fun _ =>
      let tvw := View.bot in
      tvw <- (OMod.call "lock" (tvw: View.t));;
      tvw <- (OMod.call "store" (tvw: View.t, loc_X, const_42, Ordering.plain));;
      `tvw: View.t <- (OMod.call "unlock" (tvw: View.t));;
      _ <- trigger Yield;;
      Ret tt.

  Definition thread2:
    ktree (threadE void unit) unit unit
    :=
    fun _ =>
      let tvw := View.bot in
      val_x <- ITree.iter
                (fun (tvw: View.t) =>
                   tvw <- (OMod.call "lock" (tvw: View.t));;
                   '(tvw, x) <- (OMod.call "load" (tvw: View.t, loc_X, Ordering.plain));;
                   `tvw: View.t <- (OMod.call "unlock" (tvw: View.t));;
                         b <- unwrap (Const.eqb const_0 x);;
                         if (b: bool) then Ret (inl tvw) else Ret (inr x)) tvw;;
      b <- unwrap (Const.eqb const_42 val_x);;
      if (b: bool) then
        _ <- trigger Yield;;
        _ <- trigger (Observe 0 [42]);;
        _ <- trigger Yield;;
        Ret tt
      else UB.

  Definition omod: Mod.t :=
    Mod.mk
      tt
      (Mod.get_funs [("thread1", Mod.wrap_fun thread1);
                     ("thread2", Mod.wrap_fun thread2)])
  .

  Definition mod: Mod.t :=
    OMod.close
      (omod)
      (ModAdd WMem.mod AbsLockW.mod)
  .

End ClientCode.

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


From iris.algebra Require Import auth excl_auth cmra updates local_updates.
From Fairness Require Import
     IPM SimWeakest ModSim PCM MonotoneRA FairnessRA
     TemporalLogic OneShotsRA AuthExclsRA ExclsRA.
From Fairness Require Import NatStructs NatMapRA.

Section SIM.

  Notation src_state := (Mod.state ClientSpec.mod).
  Notation src_ident := (Mod.ident ClientSpec.mod).
  Notation tgt_state := (Mod.state ClientCode.mod).
  Notation tgt_ident := (Mod.ident ClientCode.mod).

  Local Instance STT : StateTypes := Build_StateTypes src_state tgt_state src_ident tgt_ident.
  Context `{sub : @SRA.subG Γ Σ}
          {TLRASs : TLRAs_small STT Γ}
          {TLRAS : TLRAs STT Γ Σ}
          {HASONESHOTS : @GRA.inG (OneShots.t unit) Γ}
          {HASWMEM : @GRA.inG wmemRA Γ}
          {AUTHNMNRA: @GRA.inG (authUR (NatMapRA.t nat)) Γ}
          {HASLOCKTOKENRA: @GRA.inG (AuthExcls.t (nat * nat * View.t)) Γ} (* obligation id * ghost loc * svw *)
          {HASVIEWTOKENRA: @GRA.inG (AuthExcls.t View.t) Γ}
          {HASINGTOKENRA: @GRA.inG (Excls.t unit) Γ}.
  Notation iProp := (iProp Σ).

  Ltac desas H name := iEval (red_tl; simpl) in H; iDestruct H as (name) H.

  (** Invariants. *)
  (* Namespace for Client invariants. *)
  Definition N_Client : namespace := (nroot .@ "Client").
  Definition N_AbsLock : namespace := (nroot .@ "AbsLock").

  Fixpoint list_sprop_sum {n} A (l: list A) (P: A -> sProp n) : sProp n :=
    match l with
    | [] => ⌜True⌝%S
    | hd::tl => (P hd ∗ list_sprop_sum tl P)%S
    end.

  Definition natmap_sprop_sum {n} A (f: NatMap.t A) (P: nat -> A -> sProp n) :=
    list_sprop_sum (NatMap.elements f) (fun '(k, v) => P k v).

  Lemma red_sprop_sum n A (f: NatMap.t A) (P: nat -> A -> sProp n) :
    ⟦natmap_sprop_sum f P, n⟧ = NatMapRA.natmap_prop_sum f (fun t a => ⟦P t a, n⟧).
  Proof.
    unfold natmap_sprop_sum, NatMapRA.natmap_prop_sum.
    induction (NatMap.elements _); ss; red_tl.
    rewrite IHl. des_ifs.
  Qed.

  Lemma natmap_prop_sum_pull_fupd
        Q x E
        A (P: nat -> A -> iProp) m
    :
    (NatMapRA.natmap_prop_sum m (fun k a => =| x |=( Q )={E}=> P k a))
      -∗
      =| x |=( Q )={E}=>(NatMapRA.natmap_prop_sum m P).
  Proof.
    unfold NatMapRA.natmap_prop_sum. iIntros "SUM". iStopProof.
    generalize (NatMap.elements m) as l.
    induction l.
    { iIntros "_". ss. }
    ss. des_ifs. iIntros "[PA SUM]". iMod "PA". iSplitL "PA"; iFrame. iModIntro. done.
    iPoseProof (IHl with "[SUM]") as "SUM". 2:{ done. } done.
  Qed.

  Ltac red_tl_all := red_tl; red_tl_oneshots; red_tl_memra;
    red_tl_authexcls; red_tl_excls; try rewrite ! red_sprop_sum.

  Definition clientInv i κw γs γtv : sProp i :=
    (∃ (tvw: τ{View.t, i}),
      ●G γtv tvw
      ∗ ◆[κw, 6]
      ∗ (-[κw](0)-◇ ▿ γs tt)
      ∗ ((△ γs (1/2) ∗ ({tvw}(loc_X ↦ const_0)))
        ∨ (▿ γs tt ∗ ({tvw}(loc_X ↦ const_42)))))%S.

  Definition lockInv i γtv γsv γl γing : sProp i :=
    (∃ (svw: τ{View.t, i}) (waits: τ{NatMap.t nat, i})
        (mem: τ{WMem.t, i}) (own ing : τ{bool, i}) (κu γs: τ{nat, i}),
      ➢ (● (NatMapRA.to_Map waits))
      ∗ STTGT {(tt, (mem, (((own, svw), ing), key_set waits)))}
      ∗ s_wmemory_black mem
      ∗ SAuthExcls.s_black γsv (κu, γs, svw)
      ∗ natmap_sprop_sum waits
          (fun tid idx =>
            ∃ (γs: τ{nat, i}),
              (-((inrp ⋅ inrp ⋅ inrp)%prism ◬ tid)-[idx](2)-◇ ▿ γs tt)
              ∗ △ γs 1
              ∗ TID(tid)
              ∗ Duty((inrp ⋅ inrp ⋅ inrp)%prism ◬ tid)[(idx, 2, ▿ γs tt)])
      ∗ ⟨Atom.fair_blacks_tgt (inrp ⋅ inrp ⋅ inrp)%prism (fun id => (~ NatMap.In id waits))⟩
      ∗ ((⌜own = false⌝ ∗ ○G γtv svw ∗ ○G γsv (κu, γs, svw) ∗ EX γl tt)
        ∨ (⌜own = true⌝ ∗ ◆[κu, 1] ∗ (-[κu](0)-◇ ▿ γs tt) ∗ △ γs 1
          ∗ natmap_sprop_sum waits (fun _ idx => κu -(0)-◇ idx)))
      ∗ ((⌜ing = false⌝ ∗ EX γing tt) ∨ (⌜ing = true⌝ ∗ EX γl tt))
    )%S.

  Lemma AbsLock_lock_spec
    tid i n
  :
  ⊢ ∀ tvw0 γtv γsv γl γing κw γs (ds : list (nat * nat * sProp i)),
    [@ tid, i, ⊤ @]
      ⧼⟦((syn_inv i N_AbsLock (lockInv i γtv γsv γl γing))
        ∗ (syn_inv i N_Client (clientInv i κw γs γtv))
        ∗ (Duty(tid) ds)
        ∗ ◇{ds@1}(6, 2)
        ∗ TID(tid))%S, i⟧⧽
        (OMod.close_itree ClientCode.omod (ModAdd (WMem.mod) AbsLockW.mod) (R:=View.t) (OMod.call "lock" tvw0))
        ⧼rv, ⟦(∃ (tvw1 tvw2: τ{View.t, i}) (κa γa : τ{nat, i}),
                ⌜rv = tvw2 /\ View.le tvw0 tvw2 /\ View.le tvw1 tvw2⌝
                ∗ ○G γtv tvw1
                ∗ ○G γsv (κa, γa, tvw1)
                ∗ EX γl tt
                ∗ (Duty(tid) ((κa, 0, ▿ γa tt) :: ds))
                ∗ TID(tid)
                ∗ ◇[κa](1, n))%S, i⟧⧽.
  Proof.
    iIntros. iStartTriple. red_tl. rewrite ! red_syn_inv. simpl.
    rewrite close_itree_call. simpl.
    unfold OMod.emb_callee, emb_r. rewrite <- map_event_compose. rewrite <- plmap_compose.

    iIntros "(#LINV & #CINV & DUTY & PCS & TID) SIM".
    iMod (pcs_decr 1 1 with "PCS") as "[PCS1 PCS2]". auto.

    iMod (pcs_drop 2 2 with "PCS2") as "PCS2". Unshelve. all: auto.
    iMod (pcs_decr 1 1  with "PCS2") as "[PCS2 PCS3]". auto.
    iMod (pcs_drop 1 2 with "PCS3") as "PCS3". Unshelve. all: auto.

    rred2r.
    iApply (wpsim_yieldR2 with "[DUTY PCS3]"). auto. 2: iFrame. lia.
    iIntros "DUTY _ PCS3". rred2r.

    iApply (wpsim_yieldR2 with "[DUTY PCS3]"). auto. 2: iFrame. lia.
    iIntros "DUTY _ _". simpl. rred2r.
    iApply wpsim_tidR. rred2r.

    iInv "LINV" as "LI" "LIK". iEval (unfold lockInv; simpl) in "LI".
    desas "LI" svw; desas "LI" waits; desas "LI" mem; desas "LI" own; desas "LI" ing; desas "LI" κu; desas "LI" γu.
    iEval (red_tl_all; simpl) in "LI".
    iDestruct "LI" as "(LI1 & LI2 & LI3 & LI4 & LI5 & LI6 & LI7 & LI8)".
    iApply wpsim_getR. iSplit. auto. rred2r.
    iApply (wpsim_modifyR with "LI2"). iIntros "LI2". rred2r. repeat (unfold Lens.modify, Lens.set; simpl).

    iMod (alloc_obligation 3 2) as "(%κa & #LO & PC & PO)".
    iEval (rewrite <- Qp.half_half) in "PO".
    iPoseProof (pending_split _ (1/2)%Qp with "PO") as "[PO1 PO2]".
    iPoseProof (pc_split _ _ 1 with "PC") as "[PC1 PC2]".
    iMod (pc_drop _ 2 _ _ 1 with "PC2") as "PC2". Unshelve. all: auto.
    iMod (OneShots.alloc) as "[%γa PEND]".

    erewrite <- (key_set_pull_add_eq _ κa).
    remember (NatMap.add tid _ _) as waits'.

    iAssert (⌜~ NatMap.In tid waits⌝)%I as "%".
    { iAssert (⌜(NatMap.In tid waits)⌝ ∨ ⌜(~ NatMap.In tid waits)⌝)%I as "%".
      { iPureIntro. pose NatMapP.F.In_dec. specialize (s _ waits tid). destruct s; auto. }
      destruct H as [IN | NI].
      2: auto.
      iPoseProof (NatMapRA.natmap_prop_sum_impl with "LI5") as "LI5".
      { instantiate (1:= fun tid0 idx => own_thread tid0). i. simpl. iIntros "F".
        red_tl. iDestruct "F" as "[% F]". red_tl. simpl. iDestruct "F" as "[_ [_ [TID _]]]". iFrame.
      }
      apply NatMapP.F.in_find_iff in IN.
      destruct (NatMap.find tid waits) eqn:FIND; ss.
      iPoseProof (NatMapRA.natmap_prop_sum_in with "LI5") as "TH2". eauto.
      iPoseProof (own_thread_unique with "TID TH2") as "F". iPure "F" as F. ss.
    }

    set (blks2 := fun id => ¬ NatMap.In id (waits')%type).
    iPoseProof (FairRA.blacks_unfold with "LI6") as "[LI6 MYDUTY]".
    { instantiate (1:=tid). instantiate (1:=blks2). i. des.
      { subst blks2 waits'. ii. apply IN. apply NatMapP.F.add_in_iff; auto. }
      { subst blks2. subst. auto. }
    }
    { subst blks2 waits'. ss. ii. eapply H0. apply NatMapP.F.add_in_iff. auto. }
    iAssert (Duty((inrp ⋅ inrp ⋅ inrp)%prism ◬ tid) [])%I with "[MYDUTY]" as "MYDUTY".
    { iPoseProof (ObligationRA.black_to_duty with "MYDUTY") as "MYDUTY". done. }
    iPoseProof (duty_add with "[MYDUTY PO2 PC1] []") as "> MYDUTY".
    { iFrame. }
    { instantiate (1:=(▿ γa tt)%S). iModIntro. simpl. red_tl_all. iIntros "#S". iModIntro. done. }
    iPoseProof (duty_delayed_promise with "MYDUTY") as "#DPRM". simpl; left; auto.
    iMod (activate_promise with "DPRM PO1") as "#[PRM AO]". iClear "DPRM AO".

    (* make (Auth.white singleton tid k) and update wobl *)
    iMod (OwnM_Upd with "LI1") as "[LI1 MYLI1]".
    { instantiate (2:= (● (NatMapRA.to_Map (NatMap.add tid κa waits)))).
      eapply auth_update_alloc.
      eapply NatMapRA.add_local_update.
      eapply NatMapP.F.not_find_in_iff; auto.
    }

    iAssert (□ (◇[κa](2, 1) =( ObligationRA.edges_sat )=∗ ((⌜own = true⌝) -∗ (κu -(0)-◇ κa))))%I
      with "[LI7]" as "# LINK".
    { iDestruct "LI7" as "[[%OWNF _] | [_ (#LOu & _)]]".
      { subst. iModIntro. iIntros "_". iModIntro. iIntros "%". inv H0. }
      { iModIntro. iIntros "PC". iMod (link_new with "[LOu PC]") as "[LINK _]". iSplitR. auto.
        instantiate (1:=0). done. iModIntro. iIntros; done.
      }
    }
    iSpecialize ("LINK" with "PC2"). iMod "LINK".

    (* now close invariant *)
    iMod ("LIK" with "[- SIM PCS1 PCS2 DUTY MYLI1]") as "_".
    { iEval (unfold lockInv; red_tl_all; simpl).
      iExists svw; red_tl; iExists waits'; red_tl; iExists mem; red_tl; iExists own; red_tl; iExists ing; red_tl;
        iExists κu; red_tl; iExists γu; red_tl. red_tl_all. simpl. rewrite <- Heqwaits'.
      iSplitL "LI1"; [auto|]. iSplitL "LI2"; [auto|]. iSplitL "LI3"; [auto|]. iSplitL "LI4"; [auto|].
      iSplitL "PEND TID LI5 MYDUTY".
      { subst waits'. iApply (NatMapRA.natmap_prop_sum_add with "LI5"). red_tl. iExists γa.
        red_tl_all. simpl. iFrame. done.
      }
      iSplitL "LI6"; [auto|].
      iSplitL "LI7 LINK".
      iDestruct "LI7" as "[(%OWNF & LI1 & LI2 & LI3) | (%OWNT & LI1 & LI2 & LI3 & LI4)]"; subst own.
      { iLeft. iSplit; auto. iFrame. }
      { iRight. iSplit; auto. iFrame. iSpecialize ("LINK" with "[%]"). done.
        subst. iApply (NatMapRA.natmap_prop_sum_add with "LI4"). red_tl. done.
      }
      iFrame.
    }

    iClear "PRM".
    iMod (ccs_make with "[LO PCS1]") as "[CCS _]". iSplitR. auto. instantiate (1:=2). iFrame.
    iRevert "PCS2 SIM DUTY MYLI1".
    iMod (ccs_ind2 with "CCS [-]") as "IND". 2: iApply "IND".
    iModIntro. iExists 0. iIntros "IH". iModIntro.
    iIntros "PCS SIM DUTY MY".

    rewrite unfold_iter_eq. rred2r.
    iMod (pcs_drop 1 4 with "PCS") as "PCS". Unshelve. all: auto.
    iApply (wpsim_yieldR2 with "[DUTY PCS]"). auto. 2: iFrame. auto.
    iIntros "DUTY CRED PCS". simpl.
    rred2r.

    clear svw waits waits' Heqwaits' H blks2 mem own ing κu γu γa.
    iInv "LINV" as "LI" "LIK". iEval (unfold lockInv; simpl) in "LI".
    desas "LI" svw; desas "LI" waits; desas "LI" mem; desas "LI" own; desas "LI" ing; desas "LI" κu; desas "LI" γu.
    iEval (red_tl_all; simpl) in "LI".
    iDestruct "LI" as "(LI1 & LI2 & LI3 & LI4 & LI5 & LI6 & LI7 & LI8)".
    iDestruct "LI7" as "[(%OWNF & LI9 & LI10 & LI11) | (%OWNT & LI9 & #LI10 & LI11 & LI12)]"; subst own.
    { iClear "IH".
      iDestruct "LI8" as "[[%INGF LI8] | [%INGT LI8]]"; cycle 1; subst ing.
      { iExFalso; iApply (Excls.exclusive with "LI11 LI8"). }
      iApply wpsim_getR. iSplit. auto. simpl. rred2r.
      iApply wpsim_getR. iSplit. auto. simpl. rred2r.

      iAssert (⌜NatMap.find tid waits = Some κa⌝)%I as "%FIND".
      { iPoseProof (OwnM_valid with "[MY LI1]") as "%".
        { instantiate
            (1:= (● (NatMapRA.to_Map waits))
            ⋅ (◯ (NatMapRA.singleton tid κa))).
          iSplitL "LI1"; iFrame.
        }
        eapply auth_both_valid_discrete in H as [H _]. eapply NatMapRA.extends_singleton_iff in H.
        auto.
      }

      iPoseProof (NatMapRA.natmap_prop_remove_find with "LI5") as "[LIMY LI5]". apply FIND.
      remember (NatMap.remove _ _) as waits'.
      desas "LIMY" γa. iEval (red_tl_all) in "LIMY". simpl.
      iDestruct "LIMY" as "(MY1 & MY2 & TID & MY3)".
      iPoseProof (unfold_promise with "MY1") as "[_ AO]".
      iMod (OneShots.pending_shot _ tt with "MY2") as "MY2".
      iMod (duty_fulfill with "[MY3 AO MY2]") as "MY3".
      { iFrame. simpl; red_tl_all. done. }

      iApply wpsim_chooseR. iIntros "%". destruct x. rename x into tvw2. rred2r.
      iApply (wpsim_modifyR with "LI2"). iIntros "LI2". rred2r.
      repeat (unfold Lens.modify, Lens.set; simpl).

      iApply (wpsim_fairR_prism with "[MY3]"). auto.
      4:{ instantiate (1:=[(tid, [])]). ss. iFrame. }
      { clear. i. des_ifs. simpl. auto. }
      { rewrite <- key_set_pull_rm_eq. rewrite <- Heqwaits'.
        instantiate (1:=List.map fst (NatMap.elements (key_set waits'))).
        subst waits'. clear. i.
        assert (A: NatMap.In i (key_set (NatMap.remove tid waits))).
        { apply in_map_iff in IN. des. des_ifs. destruct x. destruct u.
          remember (NatMap.remove tid (key_set waits)) as M. clear HeqM.
          apply NatMapP.F.elements_in_iff. exists (). apply SetoidList.InA_alt.
          exists (k, ()). ss.
        }
        des_ifs. exfalso. eapply NatMap.remove_1. reflexivity.
        rewrite key_set_pull_rm_eq in A. apply A.
      }
      { eapply FinFun.Injective_map_NoDup.
        { unfold FinFun.Injective. i. des_ifs. destruct x, y. destruct u, u0. ss. subst. auto. }
        apply NoDupA_NoDup. apply NatMap.elements_3w.
      }
      iIntros "MY3 WHITES". rred2r.

      iCombine "LI1 MY" as "LI1".
      iPoseProof (OwnM_Upd with "LI1") as "> LI1".
      { eapply auth_update_dealloc. eapply NatMapRA.remove_local_update. }
      rewrite <- Heqwaits'.

      iPoseProof (NatMapRALarge.list_prop_sum_cons_unfold with "MY3") as "[MY3 _]".
      iPoseProof (ObligationRA.duty_to_black with "MY3") as "MY3".
      iPoseProof (FairRA.blacks_fold with "[LI6 MY3]") as "LI6".
      2:{ rewrite Prism.compose_assoc. iFrame. }
      { instantiate (1:=(fun id => ¬ NatMap.In id waits')).
        i. ss. des. destruct (tid_dec j tid) eqn:DEC.
        - clarify. auto.
        - left. esplits; eauto. ii. apply IN. subst. apply NatMapP.F.remove_in_iff. split; auto.
      }

      iMod (alloc_obligation 1 (S (S n))) as "(%κum & #LOm & PCm & POm)".
      iEval (rewrite <- Qp.half_half) in "POm". iPoseProof (pending_split with "POm") as "[POm1 POm2]".
      iPoseProof (pc_split _ _ 1 with "PCm") as "[PCm2 PCm1]".
      iMod (OneShots.alloc) as "(%γum & PENDm)".
      iMod (duty_add with "[DUTY PCm2 POm2] []") as "DUTY".
      { iFrame. }
      { instantiate (1:= (▿ γum tt)%S). iModIntro. simpl. red_tl_all. iIntros "#H"; iModIntro; done. }
      iPoseProof (duty_delayed_tpromise with "DUTY") as "#DPRM".
      { simpl; left; auto. }
      iMod (activate_tpromise with "DPRM POm1") as "[#PRM _]". iClear "DPRM".

      iMod (AuthExcls.b_w_update with "LI4 LI10") as "[LI4 LI10]".
      instantiate (1:=(κum, γum, svw)).

      (* need amps == need pendings; *)
      iAssert (NatMapRA.natmap_prop_sum waits' (fun k _ => €((inrp ⋅ (inrp ⋅ inrp))%prism ◬ k)))%I
        with "[WHITES]" as "WHITES".
      { Transparent key_set. unfold key_set. rewrite <- list_map_elements_nm_map.
        unfold NatMapRA.natmap_prop_sum.
        remember (NatMap.elements waits') as ml. clear Heqml. rewrite List.map_map.
        clear. iStopProof. induction ml.
        { iIntros "SUM". ss. }
        ss. des_ifs. iIntros "[# LOCK_INV [WH SUM]]". iFrame. iApply IHml. iSplit; [auto|]. iFrame.
      }
      iPoseProof (NatMapRA.natmap_prop_sum_impl2 with "[LI5 WHITES]") as "LI5".
      2:{ iSplitR "WHITES". iApply "LI5". iApply (NatMapRA.natmap_prop_sum_impl_ctx with "LOm").
        2: iApply "WHITES". ii. iIntros "H". done. }
      { i. simpl. iIntros "[H1 [H2 H3]]". desas "H1" γst. iEval (red_tl) in "H1". simpl.
        iDestruct "H1" as "(#H1 & H4 & H5 & H6)".
        iPoseProof (promise_progress with "[H1 H3]") as "CASES". iFrame. done.
        instantiate (1:=
          (fun k a =>
            =|S i|=(fairI (S i))={⊤ ∖ ↑N_AbsLock}=>
              ⟦(∃ (γst: τ{nat, i}),
                (-((inrp ⋅ inrp ⋅ inrp)%prism ◬ k)-[a](2)-◇ (▿ γst ()))
                ∗ (△ γst 1)
                ∗ (TID(k))
                ∗ (Duty((inrp ⋅ inrp ⋅ inrp)%prism ◬ k) [(a, 2, (▿ γst ()))])), i⟧
              ∗ κum -(0)-◇ a)%I). simpl.
        iMod "CASES". iDestruct "CASES" as "[PC | #CONTRA]"; cycle 1.
        { red_tl_all. iExFalso. iApply (OneShots.pending_not_shot with "H4 CONTRA"). }
        iMod (link_new with "[H2 PC]") as "[LINK _]". iSplitL "H2". auto. instantiate (1:=0). iFrame.
        iModIntro. red_tl_all. iSplitR "LINK". iExists γst. red_tl_all. simpl. iFrame. auto. auto.
      }
      Unshelve. 2: auto.
      iPoseProof (natmap_prop_sum_pull_fupd with "LI5") as "LI5". iMod "LI5".
      iPoseProof (NatMapRA.natmap_prop_sepconj_sum with "LI5") as "[LI5 LI12]".

      iMod ("LIK" with "[- SIM PCS LI11 TID PCm1 LI10 DUTY LI9]") as "_".
      { iEval (unfold lockInv).
        red_tl. iExists svw. red_tl. iExists waits'. red_tl. iExists mem. red_tl. iExists true.
        red_tl. iExists false. red_tl. iExists κum. red_tl. iExists γum. red_tl_all. simpl.
        iFrame. rewrite <- key_set_pull_rm_eq. rewrite <- Heqwaits'. iFrame.
        rewrite Prism.compose_assoc. iFrame.
        iSplitL "PENDm LI12".
        { iRight. iSplit. auto. iFrame. iSplit; auto. }
        iLeft. iFrame. auto.
      }

      iPoseProof (pc_split _ _ 1 with "PCm1") as "[PCm1 PCm2]".
      iMod (pcs_decr 1 with "PCS") as "[PCS1 PC2]". left.
      iApply (wpsim_yieldR with "[DUTY PCS1 PCm1]"). auto.
      { iSplitL "DUTY". iFrame. iApply (pcs_cons_fold with "[PCS1 PCm1]"). iFrame. }
      iIntros "DUTY CRED".
      rred2r.
      iApply wpsim_tauR. rred2r.
      iApply wpsim_stutter_mon; auto. instantiate (1:=ps). auto.
      iApply ("SIM" with "[LI9 LI10 LI11 DUTY PCm2 TID]").
      do 4 (red_tl; iExists _). red_tl_all. iFrame. iPureIntro. split; auto. split.
      { etrans; eauto. apply View.join_l. }
      { etrans; eauto. apply View.join_r. }
    }
    { iApply (wpsim_getR). iSplit. auto. rred2r.
      iApply wpsim_tauR.

      iMod (tpromise_progress with "[LI10 CRED]") as "[PC | #CONTRA]". iFrame. done.
      2:{ simpl. iExFalso. iEval (red_tl_oneshots) in "CONTRA".
        iApply (OneShots.pending_not_shot with "LI11 CONTRA").
      }

      iAssert (⌜NatMap.find tid waits = Some κa⌝)%I as "%FIND".
      { iCombine "LI1 MY" as "LI1".
        iDestruct (OwnM_valid with "LI1") as %?.
        iPureIntro.
        eapply auth_both_valid_discrete in H as [H _]. eapply NatMapRA.extends_singleton_iff in H.
        auto.
      }
      iPoseProof (NatMapRA.natmap_prop_sum_find_remove with "LI12") as "[LI12 LI13]". eauto.
      iEval (red_tl_all) in "LI12". simpl. iPoseProof "LI12" as "#LI12".
      iMod (link_amplify with "[PC LI12]") as "PC". iFrame. done. simpl.
      iPoseProof ("IH" with "PC") as "> IH".
      iPoseProof ("LI13" with "LI12") as "LI13".

      iMod ("LIK" with "[LI1 LI2 LI3 LI4 LI5 LI6 LI9 LI11 LI8 LI13]") as "_".
      { unfold lockInv. do 7 (red_tl; iExists _). red_tl_all; simpl. iFrame. iRight. iSplit. auto. iFrame. done. }

      rewrite unfold_iter_eq.
      iApply ("IH" with "SIM DUTY MY").
    }
  Qed.

  Lemma AbsLock_unlock_spec
        tid i
  :
  ⊢ ∀ svw tvw γtv γsv γl γing κw γw (ds : list (nat * nat * sProp i)) κa γa,
  [@ tid, i, ⊤ @]
    ⧼⟦((syn_inv i N_AbsLock (lockInv i γtv γsv γl γing))
      ∗ (syn_inv i N_Client (clientInv i κw γw γtv))
      ∗ EX γl tt
      ∗ ⌜View.le svw tvw⌝
      ∗ ○G γtv tvw
      ∗ ○G γsv (κa, γa, svw)
      ∗ (Duty(tid) ((κa, 0, ▿ γa tt) :: ds))
      ∗ ◇{((κa, 0, ▿ γa tt) :: ds)@1}(1, 4))%S, i⟧⧽
    (OMod.close_itree ClientCode.omod (ModAdd (WMem.mod) AbsLockW.mod) (R:=View.t) (OMod.call "unlock" tvw))
    ⧼rv, ⟦(∃ (tvw1 : τ{View.t, i}),
      ⌜rv = tvw1 /\ View.le tvw tvw1⌝
      ∗ (Duty(tid) (ds)))%S, i⟧⧽.
  Proof.
    iIntros. iStartTriple. red_tl_all. simpl. rewrite ! red_syn_inv.
    iIntros "(#LINV & #CINV & MY1 & % & MY2 & MY3 & DUTY & PCS) POST".
    rewrite close_itree_call. simpl. rred2r.
    unfold OMod.emb_callee, emb_r. rewrite <- map_event_compose. rewrite <- plmap_compose.

    iApply (wpsim_yieldR2 with "[DUTY PCS]"). auto. 2: iFrame; done. auto.
    iIntros "DUTY _ PCS". simpl. rred2r.
    iApply (wpsim_yieldR2 with "[DUTY PCS]"). auto. 2: iFrame; done. auto.
    iIntros "DUTY _ PCS". simpl. rred2r.

    iInv "LINV" as "LI" "LI_CLOSE".
    iEval (unfold lockInv; simpl) in "LI".
    desas "LI" svw'; desas "LI" waits; desas "LI" mem; desas "LI" own; desas "LI" ing; desas "LI" κu; desas "LI" γu.
    iEval (red_tl_all; simpl) in "LI".
    iDestruct "LI" as "(LI1 & LI2 & LI3 & LI4 & LI5 & LI6 & LI7 & LI8)".
    iPoseProof (AuthExcls.b_w_eq with "LI4 MY3") as "%EQ". inv EQ.

    iApply (wpsim_getR). iSplit. auto. simpl.
    destruct (excluded_middle_informative (View.le svw tvw)); cycle 1. ss.
    iDestruct "LI7" as "[(%OWNF & LI9 & LI10 & LI11) | (%OWNT & LI9 & LI10 & LI11 & LI12)]"; subst own.
    { iExFalso. iApply (Excls.exclusive with "MY1 LI11"). }
    iDestruct "LI8" as "[[% LI8] | [% LI8]]"; subst ing; cycle 1.
    { iExFalso. iApply (Excls.exclusive with "MY1 LI8"). }
    rred2r.

    iApply (wpsim_modifyR with "LI2"). iIntros "LI2".
    repeat (iEval (unfold Lens.modify, Lens.set; simpl) in "LI2"). rred2r.

    iMod ("LI_CLOSE" with "[- MY2 MY3 POST DUTY PCS LI8]") as "_".
    { iEval (unfold lockInv; red_tl_all; simpl).
      iExists svw; red_tl; iExists waits; red_tl; iExists mem; red_tl; iExists true; red_tl; iExists true; red_tl;
        iExists κa; red_tl; iExists γa; red_tl. red_tl_all. simpl.
      iFrame. iSplitR "MY1".
      { iRight. iSplit; auto. iFrame. }
      iRight. iSplit; auto.
    }

    iApply (wpsim_yieldR2 with "[DUTY PCS]"). auto. 2: iFrame; done. auto.
    iIntros "DUTY _ PCS". simpl. rred2r.

    clear waits mem l. iRename "LI8" into "MY1".
    iInv "LINV" as "LI" "LI_CLOSE".
    iEval (unfold lockInv; simpl) in "LI".
    desas "LI" svw'; desas "LI" waits; desas "LI" mem; desas "LI" own; desas "LI" ing; desas "LI" κu; desas "LI" γu.
    iEval (red_tl_all; simpl) in "LI".
    iDestruct "LI" as "(LI1 & LI2 & LI3 & LI4 & LI5 & LI6 & LI7 & LI8)".
    iPoseProof (AuthExcls.b_w_eq with "LI4 MY3") as "%EQ". inv EQ.

    iDestruct "LI7" as "[(%OWNF & LI9 & LI10 & LI11) | (%OWNT & LI9 & LI10 & LI11 & LI12)]"; subst own.
    { iExFalso. iApply (AuthExcls.w_w_false with "MY2 LI9"). }
    iDestruct "LI8" as "[[% LI8] | [% LI8]]"; subst ing.
    { iExFalso. iApply (Excls.exclusive with "MY1 LI8"). }
    iApply wpsim_getR. iSplit. auto. rred2r.
    iApply wpsim_chooseR. iIntros. destruct x. rename x into tvw1. rred2r.
    iApply (wpsim_modifyR with "LI2"). iIntros "LI2".
    repeat (iEval (unfold Lens.modify, Lens.set; simpl) in "LI2"). rred2r.
    iApply wpsim_chooseR. iIntros. destruct x. rename x into tvw2. rred2r.

    iInv "CINV" as "CI" "CI_CLOSE".
    iEval (unfold clientInv; simpl) in "CI".
    desas "CI" tvw0. iEval (red_tl_all; simpl) in "CI".
    iDestruct "CI" as "(CI1 & CI2 & CI3 & CI4)".
    iPoseProof (AuthExcls.b_w_eq with "CI1 MY2") as "%EQ". inv EQ.
    iAssert ((△ γw (1 / 2)) ∗ ({tvw1}(loc_X ↦ const_0)) ∨ (▿ γw ()) ∗ ({tvw1}(loc_X ↦ const_42)))%I
      with "[CI4]" as "CI4".
    { iDestruct "CI4" as "[[CI4 CI5] | [CI4 CI5]]"; rewrite ! red_s_wpoints_to.
      { iLeft. iFrame. iApply wpoints_to_view_mon; done. }
      { iRight. iFrame. iApply wpoints_to_view_mon; done. }
    }
    iPoseProof (AuthExcls.b_w_update with "CI1 MY2") as "> [CI1 MY2]". instantiate (1:=tvw1).
    iMod ("CI_CLOSE" with "[CI1 CI2 CI3 CI4]") as "_".
    { iEval (unfold clientInv). simpl. red_tl. iExists tvw1. red_tl_all. rewrite ! red_s_wpoints_to. iFrame. }
    iPoseProof (AuthExcls.b_w_update with "LI4 MY3") as "> [LI4 MY3]". instantiate (1:=(κa, γa, tvw1)).
    iMod (OneShots.pending_shot with "LI11") as "#SHOT".
    iPoseProof (unfold_tpromise with "LI10") as "[_ AO]".
    iMod (duty_fulfill with "[DUTY AO]") as "DUTY".
    { iFrame. simpl; red_tl_all; auto. }
    iClear "LI9 LI12".

    iMod ("LI_CLOSE" with "[- POST DUTY PCS]") as "_".
    { iEval (unfold lockInv; simpl; red_tl).
      iExists tvw1; red_tl; iExists waits; red_tl; iExists mem; red_tl;
        iExists false; red_tl; iExists false; red_tl; iExists κa; red_tl; iExists γa; red_tl. red_tl_all. simpl.
      iFrame. iSplitR "MY1".
      { iLeft. iSplit; auto. iFrame. }
      iLeft. iSplit; auto.
    }

    iPoseProof (pcs_cons_unfold with "PCS") as "[_ PCS]".
    iApply (wpsim_yieldR with "[DUTY PCS]"). auto. iFrame.
    iIntros "DUTY _". rred2r. iApply wpsim_tauR. rred2r.
    iApply ("POST" with "[-]").
    { red_tl. iExists _. red_tl_all. simpl; auto. iFrame. iPureIntro. eauto. }
  Qed.

  Lemma Client_thread1_spec
        tid i
  :
  ⊢ ⟦(∀ (γtv γsv γl γing κw γw: τ{nat, 1+i}),
     ((⤉ syn_inv i N_AbsLock (lockInv i γtv γsv γl γing))
        ∗ (⤉ syn_inv i N_Client (clientInv i κw γw γtv))
        ∗ TID(tid)
        ∗ (⤉ Duty(tid) [(κw, 0, ▿ γw tt)])
        ∗ ◇[κw](6, 3)
        ∗ (⤉ △ γw (1/2)))
       -∗
       syn_wpsim (S i) tid ⊤
       (fun rs rt => (⤉(syn_term_cond i tid _ rs rt))%S)
       false false
       (fn2th ClientSpec.mod "thread1" (tt ↑))
       (fn2th ClientCode.mod "thread1" (tt ↑)))%S, 1+i⟧.
  Proof.
    red_tl; iIntros (γtv); red_tl; iIntros (γsv); red_tl; iIntros (γl);
      red_tl; iIntros (γing); red_tl; iIntros (κw); red_tl; iIntros (γw).
    red_tl_all. simpl. rewrite ! red_syn_inv. rewrite ! red_syn_wpsim.

    iIntros "(#LINV & #CINV & TID & DUTY & PC & PEND)".
    unfold fn2th. ss. unfold Mod.wrap_fun, ClientCode.thread1.
    lred2r. rred.

    iPoseProof (pc_split _ _ 1 2 with "PC") as "[PC PC2]".
    iMod (pc_drop _ 1 _ _ 10 with "PC") as "PC". Unshelve. all: try lia.

    iApply (AbsLock_lock_spec _ _ 10 with "[DUTY TID PC2] [-]").
    { red_tl. rewrite ! red_syn_inv. simpl. iFrame. iSplit; auto. iSplit; auto. simpl.
      iApply (pcs_cons_fold with "[PC2]"). iFrame.
    }
    iIntros (rv) "POST".
    desas "POST" tvw1; desas "POST" tvw2; desas "POST" κa; desas "POST" γa. red_tl_all. simpl.
    iDestruct "POST" as "(% & MY1 & MY2 & MY3 & DUTY & TID & PC2)". des. subst rv. rred2r.
    iApply (wpsim_yieldR2 with "[DUTY PC PC2]"). auto.
    2:{ iFrame. simpl. iApply (pcs_cons_fold with "[-]"). iFrame. iApply (pcs_cons_fold with "[PC]"). iFrame. } lia.
    iIntros "DUTY _ PCS". simpl. rred2r.
    rewrite <- map_event_compose. unfold emb_l. rewrite <- plmap_compose.

    iInv "CINV" as "CI" "CI_CLOSE".
    iEval (unfold clientInv; simpl; red_tl_all) in "CI".
    iDestruct "CI" as (tvw1') "CI". red_tl_all; simpl.
    iDestruct "CI" as "(CI1 & CI2 & CI3 & CI4)".
    iPoseProof (AuthExcls.b_w_eq with "CI1 MY1") as "%EQ". inv EQ.
    iDestruct "CI4" as "[[PEND2 CI4] | [CONTRA CI4]]"; cycle 1.
    { iExFalso. iApply (OneShots.pending_not_shot with "PEND CONTRA"). }
    rewrite red_s_wpoints_to.
    iPoseProof (OneShots.pending_merge with "PEND PEND2") as "PEND". rewrite Qp.half_half.
    iMod (OneShots.pending_shot _ tt with "PEND") as "#SHOT".
    iPoseProof (unfold_tpromise with "CI3") as "#[_ AO]".
    iPoseProof (duty_permutation with "[DUTY]") as "DUTY".
    2: iFrame. apply Permutation_swap.
    iMod (duty_fulfill with "[DUTY]") as "DUTY".
    { iFrame. iSplit; simpl; red_tl_all; auto. }

    iInv "LINV" as "LI" "LI_CLOSE".
    iEval (unfold lockInv; simpl) in "LI".
    desas "LI" svw'; desas "LI" waits; desas "LI" mem; desas "LI" own; desas "LI" ing; desas "LI" κu; desas "LI" γu.
    iEval (red_tl_all; simpl) in "LI".
    iDestruct "LI" as "(LI1 & LI2 & LI3 & LI4 & LI5)". rewrite red_s_wmemory_black.
    iPoseProof (AuthExcls.b_w_eq with "LI4 MY2") as "%EQ". inv EQ.

    Local Transparent WMem.store_fun. rred2r.
    iApply wpsim_getR. iSplit. auto. rred2r.
    iApply wpsim_chooseR. iIntros. destruct x. destruct x as [[[lc2 to] sc1] mem1]. des.
    rename y into WRITE. rred2r.

    iPoseProof (wpoints_to_view_mon with "CI4") as "CI4". eapply H1.
    iPoseProof (wmemory_ra_store with "LI3 CI4") as "[%VW2 >[LI3 CI4]]". all: eauto.

    iApply wpsim_fairR_prism. auto.
    { i. instantiate (1:=[]). ss. clear - IN. unfold prism_fmap, WMem.missed in IN. des_ifs. }
    { i. instantiate (1:=[]) in IN. inv IN. }
    econs. ss. iIntros "_ _". rred2r.

    iApply (wpsim_modifyR with "LI2"). iIntros "LI2".
    repeat (iEval (unfold Lens.modify, Lens.set; simpl) in "LI2"). rred2r. iApply wpsim_tauR. rred.
    remember (TView.TView.cur (Local.Local.tview lc2)) as tvw3. clear Heqtvw3.
    iMod (AuthExcls.b_w_update with "CI1 MY1") as "[CI1 MY1]". instantiate (1:=tvw3).

    iMod ("LI_CLOSE" with "[LI1 LI2 LI3 LI4 LI5]") as "_".
    { iEval (unfold lockInv; simpl).
      red_tl; iExists tvw1; red_tl; iExists waits; red_tl; iExists _;
        red_tl; iExists own; red_tl; iExists ing; red_tl; iExists _; red_tl; iExists _; red_tl_all.
      simpl. iFrame. rewrite red_s_wmemory_black. done.
    }
    iMod ("CI_CLOSE" with "[CI1 CI2 CI3 CI4]") as "_".
    { iEval (unfold clientInv; red_tl). iExists _. red_tl_all. simpl; iFrame.
      iRight. iSplit; auto. rewrite red_s_wpoints_to. done.
    }

    iPoseProof (pcs_cons_unfold with "PCS") as "[PC _]". simpl.
    iPoseProof (pc_split _ _ 4 with "PC") as "[PC1 PC2]".
    iApply (AbsLock_unlock_spec with "[DUTY MY1 MY2 MY3 PC1]").
    { red_tl_all. rewrite ! red_syn_inv. simpl. iFrame. iSplit; auto. iSplit; auto. iSplit.
      iPureIntro. etrans; eauto. iApply pcs_cons_fold. iFrame.
    }
    iIntros (rv) "POST". red_tl. iDestruct "POST" as (tvw4) "POST". red_tl.
    iDestruct "POST" as "[% DUTY]". simpl. des; subst. rred2r.

    iApply (wpsim_sync2 with "[DUTY]"). auto. auto. iFrame. iIntros "DUTY _ _". rred2r.
    iApply wpsim_tauR. rred2r. lred2r.
    iApply wpsim_ret. auto. iModIntro. iFrame. auto.
  Qed.

  Lemma Client_thread2_spec
        tid i
  :
  ⊢ ⟦(∀ (γtv γsv γl γing κw γw: τ{nat, 1+i}),
     ((⤉ syn_inv i N_AbsLock (lockInv i γtv γsv γl γing))
        ∗ (⤉ syn_inv i N_Client (clientInv i κw γw γtv))
        ∗ TID(tid)
        ∗ (⤉ Duty(tid) []))
       -∗
       syn_wpsim (S i) tid ⊤
       (fun rs rt => (⤉(syn_term_cond i tid _ rs rt))%S)
       false false
       (fn2th ClientSpec.mod "thread2" (tt ↑))
       (fn2th ClientCode.mod "thread2" (tt ↑)))%S, 1+i⟧.
  Proof.
    red_tl; iIntros (γtv); red_tl; iIntros (γsv); red_tl; iIntros (γl);
      red_tl; iIntros (γing); red_tl; iIntros (κw); red_tl; iIntros (γw).
    red_tl_all. simpl. rewrite ! red_syn_inv. rewrite red_syn_wpsim.
    iIntros "(#LINV & #CINV & TID & DUTY)".
    unfold fn2th. ss. unfold Mod.wrap_fun. lred2r. rred2r.

    iInv "CINV" as "CI" "CI_CLOSE".
    iEval (unfold clientInv; simpl; red_tl_all) in "CI".
    iDestruct "CI" as (tvw) "CI". red_tl_all; simpl.
    iDestruct "CI" as "(CI1 & #CI2 & CI3)".
    iMod ("CI_CLOSE" with "[CI1 CI2 CI3]") as "_".
    { iEval (unfold clientInv; red_tl). iExists _. red_tl_all. simpl; iFrame. done. }
    clear tvw.

    iRevert "TID DUTY". generalize (View.bot). intros tvw0. iRevert (tvw0).
    iPoseProof (lo_ind with "CI2 []") as "> IH". 2: iApply ("IH"). iModIntro.
    iExists 0. iIntros "IH". iModIntro. iIntros (tvw0) "TID DUTY".

    iEval (rewrite unfold_iter_eq). rred.
    iApply (AbsLock_lock_spec _ _ 5 with "[DUTY TID] [-]").
    { red_tl. rewrite ! red_syn_inv. simpl. iFrame. iSplit; auto. }
    iIntros (rv) "POST". desas "POST" tvw1; desas "POST" tvw2; desas "POST" κu; desas "POST" γu.
    iEval (red_tl_all) in "POST". iDestruct "POST" as "(% & MY1 & MY2 & MY3 & DUTY & TID & PC)".
    simpl. des; subst. rred2r.

    iApply (wpsim_yieldR2 with "[DUTY PC]"). auto. 2:{ iFrame. iApply pcs_cons_fold. iFrame. } lia.
    iIntros "DUTY CRED PC". simpl. rred2r.
    unfold emb_l. rewrite <- map_event_compose. rewrite <- plmap_compose.
    Local Transparent WMem.load_fun. rred2r.

    iInv "LINV" as "LI" "LI_CLOSE".
    iEval (unfold lockInv; simpl) in "LI".
    desas "LI" svw; desas "LI" waits; desas "LI" mem;
      desas "LI" own; desas "LI" ing; desas "LI" κu'; desas "LI" γu'.
    iEval (red_tl_all; simpl) in "LI".
    iDestruct "LI" as "(LI1 & LI2 & LI3 & LI4 & LI5)". rewrite red_s_wmemory_black.
    iPoseProof (AuthExcls.b_w_eq with "LI4 MY2") as "%EQ". inv EQ.
    iApply (wpsim_getR). iSplit. auto. rred2r.
    iApply wpsim_chooseR. iIntros. destruct x. destruct x as [[[lc2 to] sc1] mem1]. des.
    rename y into READ. rred2r.

    iApply wpsim_fairR_prism. auto.
    { i. instantiate (1:=[]). ss. clear - IN. unfold prism_fmap, WMem.missed in IN. des_ifs. }
    { i. instantiate (1:=[]) in IN. inv IN. }
    econs. ss. iIntros "_ _". rred2r. iApply wpsim_tauR. rred.

    iInv "CINV" as "CI" "CI_CLOSE".
    iEval (unfold clientInv; simpl; red_tl_all) in "CI".
    iDestruct "CI" as (tvw1') "CI". iEval (red_tl_all; simpl) in "CI".
    iDestruct "CI" as "(CI1 & _ & #CI3 & CI4)".
    iPoseProof (AuthExcls.b_w_eq with "CI1 MY1") as "%EQ". inv EQ.
    iDestruct "CI4" as "[[PEND2 CI4] | [#SHOT CI4]]".
    { rewrite red_s_wpoints_to.
      iMod (tpromise_progress with "[CI3 CRED]") as "[PCw | #SHOT]". iFrame. done.
      2:{ simpl. iExFalso. iEval (red_tl_all) in "SHOT". iApply (OneShots.pending_not_shot with "PEND2 SHOT"). }
      iPoseProof (wpoints_to_view_mon with "CI4") as "CI4". eapply H1.
      iPoseProof (wmemory_ra_load with "LI3 CI4") as "(LI3 & %VW2 & > CI4)". all: eauto.
      simpl. des; subst. ss. remember (TView.TView.cur lc2) as tvw3.
      iPoseProof (AuthExcls.b_w_update with "CI1 MY1") as "> [CI1 MY1]". instantiate (1:=tvw3).

      iMod ("CI_CLOSE" with "[CI1 CI4 PEND2]") as "_".
      { iEval (unfold clientInv; red_tl). iExists _. red_tl_all. simpl; iFrame.
        iSplit. auto. iSplit. auto. iLeft. rewrite red_s_wpoints_to. iFrame.
      }
      iMod ("LI_CLOSE" with "[LI1 LI2 LI3 LI4 LI5]") as "_".
      { iEval (unfold lockInv; simpl).
        red_tl; iExists tvw1; red_tl; iExists waits; red_tl; iExists _;
          red_tl; iExists own; red_tl; iExists ing; red_tl; iExists _; red_tl; iExists _; red_tl_all.
        simpl. iFrame. rewrite red_s_wmemory_black. done.
      }

      iApply (AbsLock_unlock_spec with "[DUTY PC MY1 MY2 MY3]").
      { red_tl_all. rewrite ! red_syn_inv. iSplit. auto. iSplit. auto. simpl. iFrame. iSplit; auto.
        iPureIntro. etrans; eauto.
      }
      iIntros (rv) "POST". iEval (red_tl) in "POST". iDestruct "POST" as (tvw4) "POST".
      iEval (red_tl; simpl) in "POST". iDestruct "POST" as "[% DUTY]". rred2r.
      iApply wpsim_tauR.
      iMod ("IH" with "PCw") as "IH". iApply wpsim_reset. iApply ("IH" with "TID DUTY").
    }
    { iClear "IH". rewrite red_s_wpoints_to.
      iPoseProof (wpoints_to_view_mon with "CI4") as "CI4". eapply H1.
      iPoseProof (wmemory_ra_load with "LI3 CI4") as "(LI3 & %VW2 & > CI4)". all: eauto.
      simpl. des; subst. ss. remember (TView.TView.cur lc2) as tvw3.
      iPoseProof (AuthExcls.b_w_update with "CI1 MY1") as "> [CI1 MY1]". instantiate (1:=tvw3).

      iMod ("CI_CLOSE" with "[CI1 CI4]") as "_".
      { iEval (unfold clientInv; red_tl). iExists _. red_tl_all. simpl; iFrame.
        iSplit. auto. iSplit. auto. iRight. rewrite red_s_wpoints_to. iFrame. done.
      }
      iMod ("LI_CLOSE" with "[LI1 LI2 LI3 LI4 LI5]") as "_".
      { iEval (unfold lockInv; simpl).
        red_tl; iExists tvw1; red_tl; iExists waits; red_tl; iExists _;
          red_tl; iExists own; red_tl; iExists ing; red_tl; iExists _; red_tl; iExists _; red_tl_all.
        simpl. iFrame. rewrite red_s_wmemory_black. done.
      }
      iApply (AbsLock_unlock_spec with "[DUTY MY1 MY2 MY3 PC]").
      { red_tl. rewrite ! red_syn_inv. simpl. iSplit. auto. iSplit. auto.
        red_tl_all. iFrame. iSplit.
        { iPureIntro. etrans; eauto. }
        iFrame.
      }
      iIntros (rv) "POST". iEval (red_tl) in "POST". iDestruct "POST" as (tvw4) "POST".
      iEval (red_tl; simpl) in "POST". iDestruct "POST" as "[% DUTY]". rred2r.
      iApply (wpsim_sync with "[DUTY]"). auto. iFrame. iIntros "DUTY _". rred2r.
      iApply wpsim_tauR. rred2r. lred2r.
      iApply wpsim_observe. iIntros. lred2r. rred2r.
      iApply wpsim_tauR. rred2r.
      iApply (wpsim_sync with "[DUTY]"). auto. iFrame. iIntros "DUTY _". rred2r.
      iApply wpsim_tauR. rred2r. lred2r.
      iApply wpsim_ret. auto. iModIntro. iFrame. auto.
    }
  Qed.

  Section SIM_INIT.

    Variable tid1 tid2 : thread_id.
    Let init_ord := Ord.O.
    Let init_ths :=
          (NatStructsLarge.NatMap.add
             tid1 tt
             (NatStructsLarge.NatMap.add
                tid2 tt
                (NatStructsLarge.NatMap.empty unit))).

    Let idx := 1.

    Lemma init_sat E (H_TID : tid1 <> tid2)
    :
    (OwnM (Σ:=Σ) (wmem_init_res loc_X (Loc.of_nat 210)))
      ∗ ((AuthExcls.rest (Σ:=Σ) (gt_dec 0) (0, 0, View.bot))
        ∗ (AuthExcls.rest (gt_dec 0) View.bot)
        ∗ (OwnM (● (NatMapRA.to_Map (NatMap.empty nat))))
        ∗ (Excls.rest (gt_dec 0) tt))
    ∗
    (WSim.initial_prop
        ClientSpec.mod ClientCode.mod
        (Vars:=@sProp STT Γ) (Σ:=Σ)
        (STATESRC:=@SRA.in_subG Γ Σ sub _ _STATESRC)
        (STATETGT:=@SRA.in_subG Γ Σ sub _ _STATETGT)
        (IDENTSRC:=@SRA.in_subG Γ Σ sub _ _IDENTSRC)
        (IDENTTGT:=@SRA.in_subG Γ Σ sub _ _IDENTTGT)
        (ARROWRA:=@_ARROWRA STT Γ Σ TLRAS)
        idx init_ths init_ord)
    ⊢
      =| 1+idx |=(⟦syn_fairI (1+idx), 1+idx⟧)={E}=>
        (∃ γtv γsv γl γing κw γw,
          (inv idx N_AbsLock (lockInv idx γtv γsv γl γing))
          ∗ (inv idx N_Client (clientInv idx κw γw γtv))
          ∗ (own_thread tid1
            ∗ (⟦Duty(tid1) [(κw, 0, ▿ γw tt : sProp idx)], idx⟧)
            ∗ (◇[κw](6, 3))
            ∗ (△ γw (1/2)%Qp))
          ∗ (own_thread tid2
            ∗ (⟦Duty(tid2) [], idx⟧))).
    Proof.
      iIntros "(MEM & (REST1 & REST2 & REST3 & REST4) & INIT)". rewrite red_syn_fairI.
      iPoseProof (wmem_init_res_prop with "MEM") as "(PT & _ & MEM)".
      iPoseProof (init_points_to_wpoints_to _ View.bot with "PT") as "PT".

      iMod (alloc_obligation 6 4) as "(%κw & #LO & PC & PENDING)".
      iEval (rewrite <- Qp.half_half) in "PENDING".
      iPoseProof (pending_split _ (1/2) (1/2) with "PENDING") as "(PENDING1 & PENDING2)".

      iMod (OneShots.alloc) as "(%γw & LIVE)".
      iEval (rewrite <- Qp.half_half) in "LIVE".
      iPoseProof (OneShots.pending_split _ (1/2) (1/2) with "LIVE") as "(LIVE1 & LIVE2)".
      iMod (AuthExcls.alloc_gt _ (0, 0, View.bot) with "[REST1]") as "[REST1 (%γsv & LB & LW)]".
      { iExists 0. done. }
      iMod (AuthExcls.alloc_gt _ View.bot with "[REST2]") as "[REST2 (%γtv & LB2 & LW2)]".
      { iExists 0. done. }
      iMod (Excls.alloc_gt _ with "[REST4]") as "[REST4 (%γl & EX)]".
      { iExists 0. done. }
      iMod (Excls.alloc_gt _ with "[REST4]") as "[REST4 (%γing & EX2)]".
      { done. }

      unfold WSim.initial_prop.
      iDestruct "INIT" as "(INIT0 & INIT1 & INIT2 & INIT3 & INIT4 & INIT5)".
      (* make thread_own, duty *)
      assert (NatStructsLarge.NatMap.find tid1 init_ths = Some tt).
      { unfold init_ths. apply NatStructsLarge.nm_find_add_eq. }
      iPoseProof (NatMapRALarge.natmap_prop_remove_find _ _ _ H with "INIT2") as "[DU1 INIT2]".
      iPoseProof (NatMapRALarge.natmap_prop_remove_find _ _ _ H with "INIT3") as "[TH1 INIT3]".
      clear H.
      assert (NatStructsLarge.NatMap.find tid2 (NatStructsLarge.NatMap.remove tid1 init_ths) = Some tt).
      { unfold init_ths.
        rewrite NatStructsLarge.NatMapP.F.remove_neq_o; ss.
        rewrite NatStructsLarge.nm_find_add_neq; ss.
        rewrite NatStructsLarge.nm_find_add_eq. ss.
      }
      iPoseProof (NatMapRALarge.natmap_prop_remove_find _ _ _ H with "INIT2") as "[DU2 INIT2]".
      iPoseProof (NatMapRALarge.natmap_prop_remove_find _ _ _ H with "INIT3") as "[TH2 INIT3]".
      clear H.

      iPoseProof (pc_split _ _ 1 with "PC") as "[PC' PC]".
      iMod (pc_drop _ 1 _ _ 1 with "PC'") as "PC'". Unshelve. all: try lia.
      iMod (duty_add with "[DU1 PENDING2 PC'] []") as "DU1".
      { instantiate (4:=[]). iSplitL "DU1". done. instantiate (2:=0). iFrame. }
      { instantiate (1:=(▿ γw tt : @sProp STT Γ idx)%S).
        iModIntro. simpl; red_tl. iIntros "H". red_tl_all.
        iPoseProof "H" as "#H". iModIntro; red_tl_all; auto.
      }
      iPoseProof (duty_delayed_tpromise with "DU1") as "#DPRM".
      { ss. eauto. }
      iMod (activate_tpromise with "DPRM PENDING1") as "[#TPRM _]".

      iMod (FUpd_alloc _ _ _ idx N_AbsLock (lockInv idx γtv γsv γl γing)
        with "[REST3 INIT1 INIT5 MEM LB LW LW2 EX EX2]") as "LI".
      lia.
      { simpl. unfold lockInv.
        red_tl. iExists View.bot. red_tl. iExists (NatMap.empty nat).
        red_tl. iExists (WMem.init). red_tl. iExists false. red_tl. iExists false.
        red_tl. iExists 0. red_tl. iExists 0. red_tl_all. simpl.
        unfold OMod.closed_st_init, Mod.st_init; ss. rewrite key_set_empty_empty_eq.
        rewrite red_s_wmemory_black. iFrame.
        iSplitR. ss.
        iSplitL "INIT1".
        { iApply FairRA.blacks_prism_id_rev.
          iApply FairRA.blacks_impl.
          2: { iFrame. }
          i. des. subst. ss.
        }
        iSplitL "LW LW2 EX". iLeft. iFrame. auto. iLeft. iFrame. auto.
      }
      iMod (FUpd_alloc _ _ _ idx N_Client (clientInv idx κw γw γtv)
        with "[PT LIVE2 LB2]") as "CI".
      lia.
      { simpl. unfold clientInv.
        red_tl. iExists View.bot. red_tl_all. simpl. iFrame.
        repeat iSplit; auto. iLeft. rewrite red_s_wpoints_to. iFrame.
      }

      iModIntro. iExists γtv, γsv, γl, γing, κw, γw.
      red_tl_all; simpl. repeat iSplit; auto.
      iFrame.
    Qed.
  End SIM_INIT.

End SIM.