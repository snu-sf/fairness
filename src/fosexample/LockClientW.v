From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Export
     ITreeLib WFLibLarge FairBeh NatStructs Mod pind Axioms
     Linking WMM Red IRed WeakestAdequacy FairLock Concurrency.
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

Module ClientImpl.

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
     IProp IPMFOS Weakest ModSim PCM MonotonePCM StateRA FairRA NatStructs NatMapRAFOS.

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

  Context `{Invs : @InvSet Σ}.

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

  Context `{COPSETRA : @GRA.inG CoPset.t Σ}.
  Context `{GSETRA : @GRA.inG Gset.t Σ}.
  Context `{INVSETRA : @GRA.inG (InvSetRA Var) Σ}.

  Context `{WMEMRA: @GRA.inG wmemRA Σ}.

  Context `{EXCL: @GRA.inG (Excl.t unit) Σ}.
  Context `{EXCL2: @GRA.inG (Excl.t (unit * unit)) Σ}.
  Context `{ONESHOTRA: @GRA.inG (OneShot.t nat) Σ}.
  Context `{REGIONRA: @GRA.inG (Region.t (thread_id * nat)) Σ}.
  Context `{CONSENTRA: @GRA.inG (@FiniteMap.t (Consent.t nat)) Σ}.
  Context `{AUTHNRA: @GRA.inG (Auth.t (Excl.t nat)) Σ}.
  Context `{AUTHVWRA: @GRA.inG (Auth.t (Excl.t View.t)) Σ}.
  Context `{AUTHVWRA2: @GRA.inG (Auth.t (Excl.t (View.t * unit))) Σ}.
  Context `{AUTHNMNRA: @GRA.inG (Auth.t (NatMapRAFOS.t nat)) Σ}.

  Definition thread1_will_write (tvw: View.t) : iProp :=
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
    ∃ (own: bool) (tvw: View.t) (ing: bool) (mem: WMem.t) (wobl: NatMap.t nat) (j: nat),
      (OwnM (Auth.black (Some wobl: NatMapRAFOS.t nat)))
        ∗
        ((OwnM (Auth.black (Excl.just j: Excl.t nat)))
        ∗ (OwnM (Auth.black (Excl.just (tvw, tt): Excl.t (View.t * unit)%type))))
        ∗
        (wmemory_black mem)
        ∗
        (St_tgt (tt, (mem, (((own, tvw), ing), key_set wobl))))
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
             (* points_to view *)
             ∗ (OwnM (Auth.white (Excl.just tvw: Excl.t View.t)))
             (* argument-passing view *)
             ∗ (OwnM (Auth.white (Excl.just (tvw, tt): Excl.t (View.t * unit)%type)))
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
            (* ∗ (∃ tvw', (OwnM (Auth.white (Excl.just tvw': Excl.t View.t))) ∗ (⌜View.le tvw tvw'⌝)) *)
            )
        )
  .

  Section INITIAL.

    Variable tid1 tid2 : nat.
    Let init_ord := (((((Ord.omega × Ord.omega) × Ord.omega) ⊕ ((Ord.S Ord.O) × (o_w_cor))) ⊕ 10)%ord).
    Let init_ths :=
              (NatStructs.NatMap.add tid1 tt
                 (NatStructs.NatMap.add tid2 tt
                    (NatStructs.NatMap.empty unit))).

    Lemma init_sat E (H_TID : tid1 <> tid2) :
        (
            OwnM (OneShot.pending nat 1)
        ) ∗ (
            OwnM (Auth.black (Some (NatMap.empty nat) : NatMapRAFOS.t nat))
              ∗ OwnM (Auth.black (Excl.just 0 : Excl.t nat))
              ∗ OwnM (Auth.white (Excl.just 0 : Excl.t nat))
              ∗ OwnM (Auth.black (Excl.just View.bot : Excl.t View.t))
              ∗ OwnM (Auth.white (Excl.just View.bot : Excl.t View.t))
              ∗ OwnM (Auth.black (Excl.just (View.bot, ()) : Excl.t (View.t * unit)))
              ∗ OwnM (Auth.white (Excl.just (View.bot, ()) : Excl.t (View.t * unit)))
              ∗ OwnM (Excl.just (tt,tt): Excl.t (unit * unit))
              ∗ OwnM (Excl.just () : Excl.t unit)
              ∗ OwnM (wmem_init_res loc_X (Loc.of_nat 5)))
        ∗
        WSim.initial_prop ClientSpec.mod ClientImpl.mod init_ths init_ord
        ⊢
        FUpd (fairI (ident_tgt:=Mod.ident ClientImpl.mod)) E E (
            (∃ tvw, (OwnM (Auth.black (Excl.just tvw: Excl.t View.t))) ∗ (thread1_will_write tvw))
            ∗
            (lock_will_unlock)
            ∗
            (∃ k, (own_thread tid1)
                    ∗ (ObligationRA.duty inlp tid1 [(k, Ord.from_nat 1)])
                    ∗ (ObligationRA.taxes [(k, Ord.from_nat 1)] init_ord)
                    ∗ (OwnM (OneShot.shot k))
                    ∗ (ObligationRA.pending k (/ 2))
            )
            ∗
            ((own_thread tid2) ∗ (ObligationRA.duty inlp tid2 []))
        ).
    Proof.
      iIntros "(PEND & (B1 & B2 & W2 & B3 & W3 & B4 & W4 & E1 & E2 & E3) & INIT)".
      iPoseProof (wmem_init_res_prop with "E3") as "[[WPOINTS _] MBLACK]".

      iMod (ObligationRA.alloc ((1 × Ord.omega) ⊕ ((1 × Ord.omega) × init_ord))%ord) as "[% [[OBLIG1 OBLIG2] OBLIG3]]".
      iMod (OwnM_Upd (OneShot.pending_shot k) with "PEND") as "#SHOT".
      rewrite <- Qp.inv_half_half.
      iPoseProof (ObligationRA.pending_split _ (/ 2)%Qp (/ 2)%Qp with "OBLIG3") as "[OBPEND1 OBPEND2]".

      unfold WSim.initial_prop.
      iDestruct "INIT" as "[[[[[INIT0 INIT1] INIT2] INIT3] INIT4] INIT5]".
      (* make thread_own, duty *)
      assert (NatStructs.NatMap.find tid1 init_ths = Some tt).
      { unfold init_ths. apply NatStructs.nm_find_add_eq. }
      iPoseProof (MonotonePCM.natmap_prop_remove_find _ _ _ H with "INIT2") as "[DU1 INIT2]".
      iPoseProof (MonotonePCM.natmap_prop_remove_find _ _ _ H with "INIT3") as "[TH1 INIT3]".
      clear H.
      assert (NatStructs.NatMap.find tid2 (NatStructs.NatMap.remove tid1 init_ths) = Some tt).
      { unfold init_ths.
        rewrite NatStructs.NatMapP.F.remove_neq_o; ss.
        rewrite NatStructs.nm_find_add_neq; ss.
        rewrite NatStructs.nm_find_add_eq. ss.
      }
      iPoseProof (MonotonePCM.natmap_prop_remove_find _ _ _ H with "INIT2") as "[DU2 INIT2]".
      iPoseProof (MonotonePCM.natmap_prop_remove_find _ _ _ H with "INIT3") as "[TH2 INIT3]".
      clear H.

      iPoseProof (ObligationRA.white_split_eq with "OBLIG2") as "[O0 O1]".
      iPoseProof (ObligationRA.duty_alloc with "DU1 O0") as "> DU".
      iPoseProof (ObligationRA.duty_correl with "DU") as "#CORREL".
      { ss. eauto. }
      iModIntro.

      iSplitL "B3 OBLIG1 SHOT OBPEND1 WPOINTS".
      { unfold thread1_will_write.
        iExists View.bot. iFrame. iExists k.
        iSplitL "OBLIG1". { iExists _. iFrame. }
        iSplitR. { iExists _.  eauto. }
        iSplitL "SHOT". { iApply "SHOT". }
        iLeft. iFrame. iApply (init_points_to_wpoints_to with "WPOINTS").
      }

      (*
      Check FairRA.blacks_unfold.
      Search FairRA.blacks.
      set (s0 := λ i : nat + OMod.closed_ident ClientImpl.omod (ModAdd WMem.mod AbsLockW.mod),
               match i with
               | inl _ => False%type
               | inr _ => True%type
               end).
      set (s1 := λ i : nat + OMod.closed_ident ClientImpl.omod (ModAdd WMem.mod AbsLockW.mod),
               match i with
               | inl _ => i = inl tid1
               | inr _ => True%type
               end).
      set (s2 := λ i : nat + OMod.closed_ident ClientImpl.omod (ModAdd WMem.mod AbsLockW.mod),
               match i with
               | inl _ => i = inl tid1 \/ i = inl tid2
               | inr _ => True%type
               end).
      Check FairRA.blacks_unfold s1 s0.
       *)
      (* iPoseProof (FairRA.blacks_unfold s1 s0 with "BLACK") as "BLACK". *)

      (* FairRA.blacks_unfold *)
      (* black_to_duty *)

      iSplitL "B1 B2 W2 W3 B4 W4 E1 E2 MBLACK INIT1 INIT5".
      { unfold lock_will_unlock.
        iExists false, View.bot, false, WMem.init, (NatMap.empty nat), 0.
        iFrame.
        iSplitL "INIT5".
        { ss. unfold OMod.closed_st_init, Mod.st_init. ss.
          rewrite key_set_empty_empty_eq. iFrame. }
        iSplitL "INIT1".
        { iApply FairRA.blacks_prism_id_rev.
          iApply FairRA.blacks_impl.
          2: { iFrame. }
          i. des. subst. ss. }
        iSplitR. { ss. }
        iSplitL "W2 W3 W4 E2". { iLeft. iFrame. ss. }
        { iLeft. iFrame. ss. }
      }

      iSplitL "O1 OBPEND2 TH1 DU".
      { iExists k. iSplitL "TH1"; ss. iFrame. auto. }
      iFrame.
    Qed.

      (*
    Definition thread1_will_write (tvw: View.t) : iProp :=
      ∃ k, (∃ n, ObligationRA.black k n)
             ∗
             (ObligationRA.correl_thread k 1%ord)
             ∗
             (OwnM (OneShot.shot k))
             ∗
             ((ObligationRA.pending k (/2)%Qp ∗ wpoints_to loc_X const_0 tvw)
              ∨
                (ObligationRA.shot k ∗ wpoints_to loc_X const_42 tvw)).


    Definition lock_will_unlock : iProp :=
      ∃ (own: bool) (tvw: View.t) (ing: bool) (mem: WMem.t) (wobl: NatMap.t nat) (j: nat),
        (OwnM (Auth.black (Some wobl: NatMapRAFOS.t nat)))
          ∗
          ((OwnM (Auth.black (Excl.just j: Excl.t nat)))
          ∗ (OwnM (Auth.black (Excl.just (tvw, tt): Excl.t (View.t * unit)%type))))
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
               ∗ (OwnM (Auth.white (Excl.just tvw: Excl.t View.t)))
               ∗ (OwnM (Auth.white (Excl.just (tvw, tt): Excl.t (View.t * unit)%type)))
               ∗ (OwnM (Excl.just tt: Excl.t unit))
            )
            ∨
              (* ((⌜own = true⌝) *)
              (*    ∗ (ObligationRA.pending j 1) *)
              (*    ∗ (ObligationRA.black j o_w_cor) *)
              (*    ∗ (ObligationRA.correl_thread j 1%ord) *)
              (*    ∗ (natmap_prop_sum wobl (fun _ idx => ObligationRA.amplifier j idx 1%ord)) *)
              (* ) *)
          )
          ∗
          (
            ((⌜ing = false⌝)
               ∗ (OwnM (Excl.just (tt, tt): Excl.t (unit * unit)%type))
            )
            ∨
              (* ((⌜ing = true⌝) *)
              (*    ∗ (OwnM (Excl.just tt: Excl.t unit)) *)
              (* ) *)
          )
    .
      *)
  End INITIAL.

  Let client_invariant := (∃ tvw, (OwnM (Auth.black (Excl.just tvw: Excl.t View.t))) ∗ (thread1_will_write tvw))%I.

  Variable N : stdpp.namespaces.namespace.

  Variable N_lock : stdpp.namespaces.namespace.
  Variable N_user : stdpp.namespaces.namespace.
  Variable N_user_N_lock_disjoint: N_user ## N_lock.

  Lemma AbsLock_lock
        R_src R_tgt tid
        (src: thread void (sE unit) R_src)
        tgt
        r g
        (Q: R_src -> R_tgt -> iProp)
        (l: list (nat * Ord.t)%type)
        (num_line: nat)
        (tvw0: View.t)
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
      (∀ tvw1,
          ((⌜View.le tvw0 tvw1⌝)
             ∗
             (own_thread tid)
             ∗
             (∃ j, (ObligationRA.duty inlp tid ((j, Ord.S Ord.O) :: l))
                     ∗
                     (ObligationRA.white j (Ord.omega × (Ord.from_nat num_line))%ord)
                     ∗
                     (OwnM (Auth.white (Excl.just j: Excl.t nat)))
             )
             ∗
             (∃ tvw,
                 (OwnM (Auth.white (Excl.just tvw: Excl.t View.t)))
                   ∗ (OwnM (Auth.white (Excl.just (tvw, tt): Excl.t (View.t * unit))))
                   ∗ (⌜(View.le tvw tvw1)⌝)
             )
             ∗
             (OwnM (Excl.just tt: Excl.t unit))
          )
            -∗
            (stsim tid ⊤ r g Q
                   false false
                   (trigger Yield;;; src)
                   (tgt tvw1)))
      ⊢
      (stsim tid ⊤ r g Q
             false false
             (trigger Yield;;; src)
             (tvw' <- (OMod.close_itree ClientImpl.omod (ModAdd (WMem.mod) AbsLockW.mod) (R:=View.t) (OMod.call "lock" tvw0));; (tgt tvw'))).
  Proof.
    Opaque key_set.
    iIntros "[[# LOCK_INV [TH [DUTY TAXES]]] SIM]".
    rewrite close_itree_call. ss. rred. unfold OMod.emb_callee, emb_r. rewrite <- map_event_compose. rewrite <- plmap_compose.
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
    iApply stsim_tidR. rred.
    iInv "LOCK_INV" as "I1" "K1". do 6 (iDestruct "I1" as "[% I1]").
    iDestruct "I1" as "[B1 [B2 [MEM [STGT I1]]]]".
    iApply stsim_getR. iSplit. iFrame. rred.
    iApply (stsim_modifyR with "STGT"). iIntros "STGT". rred.

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
    set (blks2 := fun id => ¬ NatMap.In id (NatMap.add tid k wobl)%type).
    iPoseProof (FairRA.blacks_unfold with "BLKS") as "[BLKS MYDUTY]".
    { instantiate (1:=tid). instantiate (1:=blks2). i. des.
      { subst blks2. ss. des. esplits; eauto. ii. apply IN. apply NatMapP.F.add_in_iff; auto. }
      { subst blks2. subst. auto. }
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
        (
  (⌜own = false⌝ **
               (OwnM (Auth.white (Excl.just j: Excl.t nat))
                     ** (OwnM (Auth.white (Excl.just tvw: Excl.t View.t))
                     ** (OwnM (Auth.white (Excl.just (tvw, tt): Excl.t (View.t * unit))) ** OwnM (Excl.just tt: Excl.t unit)))
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

    (* induction *)
    rred.
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
    iApply (stsim_yieldR with "[DUTY TAX]"). msubtac. iFrame.
    iIntros "DUTY WTH". rred.
    iInv "LOCK_INV" as "I1" "K1". do 6 (iDestruct "I1" as "[% I1]").
    iDestruct "I1" as "[B1 [B2 [MEM [STGT I1]]]]".
    iApply stsim_getR. iSplit. iFrame. rred.
    destruct own.

    (* someone is holding the lock *)
    { rred. iApply stsim_tauR. rred.

      iAssert (⌜NatMap.find tid wobl = Some k⌝)%I as "%".
      { iPoseProof (OwnM_valid with "[MYW B1]") as "%".
        { instantiate (1:= (Auth.black (Some wobl: NatMapRAFOS.t nat)) ⋅ (Auth.white (NatMapRAFOS.singleton tid k: NatMapRAFOS.t nat))). iSplitL "B1"; iFrame. }
        eapply Auth.auth_included in H. eapply NatMapRAFOS.extends_singleton_iff in H.
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
          iApply IH. eapply RENEW. eapply RENEW.
          iFrame. auto.
        }
      }
    }

    (* no one is holding the lock *)
    { rred.
      iClear "TAXES". clear IH credit RICH.
      iApply stsim_getR. iSplit. iFrame. rred.
      iDestruct "I1" as "[BLKS [SUM [[[%VW [LOCK EXCL]] | [%CONTRA _]] INGS]]]".
      2:{ inversion CONTRA. }
      inv VW.
      iDestruct "INGS" as "[[%INGF INGEX] | [_ CONTRA]]".
      2:{ iDestruct "EXCL" as "[_ [_ EXCL]]". iPoseProof (excl_unique with "EXCL CONTRA") as "%C". inv C. }
      subst. rred.

      iApply stsim_chooseR. iIntros "%". destruct x. rename x into tvw'. rred.
      iApply (stsim_modifyR with "STGT"). iIntros "STGT". rred.

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
      { clear. i. des_ifs. ss. auto. }
      { instantiate (1:= List.map fst (NatMap.elements (NatMap.remove tid (key_set wobl)))). clear. i. unfold prism_fmap.
        assert (A: NatMap.In i (NatMap.remove tid (key_set wobl))).
        { apply in_map_iff in IN. des. des_ifs. destruct x. destruct u. esplits; eauto.
          remember (NatMap.remove tid (key_set wobl)) as M. clear HeqM.
          apply NatMapP.F.elements_in_iff. exists (). apply SetoidList.InA_alt.
          exists (k, ()). ss.
        }
        des. subst. unfold Prism.preview; ss. des_ifs.
        exfalso. eapply NatMap.remove_1. reflexivity. eapply A.
      }
      { eapply FinFun.Injective_map_NoDup.
        { unfold FinFun.Injective. i. des_ifs. destruct x, y. destruct u, u0. ss. subst. auto. }
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
      { instantiate (1:=
         (fun id => ¬ NatMap.In id new_wobl)).
        i. ss. des. destruct (tid_dec j0 tid) eqn:DEC.
        - clarify. auto.
        - left. esplits; eauto. ii. apply IN. subst. apply NatMapP.F.remove_in_iff.
          split; auto.
      }

      ss. repeat (unfold Lens.modify, Lens.set; ss).
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
        ss. des_ifs. iIntros "[# LOCK_INV [WH SUM]]". iFrame. iApply IHml. iSplit; [auto|]. iFrame.
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
        iIntros "# [LOCK_INV BLK]". des_ifs. iSplit; auto. iApply IHml. iModIntro. iSplit; auto.
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

      iApply (stsim_yieldR with "[DUTY TAXKEEP NEWWTAX]"). msubtac.
      { iSplitL "DUTY". iFrame. iFrame. iApply ObligationRA.white_eq.
        { symmetry. apply Jacobsthal.mult_1_l. }
        iFrame.
      }
      iIntros "DUTY _". rred.
      iApply stsim_tauR. rred.

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
      (*     etrans. 2: eapply l0. apply View.join_r. *)
      (*   - iRight. iFrame. iApply wpoints_to_view_mon. 2: iFrame. *)
      (*     etrans. 2: eapply l0. apply View.join_r. *)
      (* } *)
      (* iPoseProof ("I04a" with "I04") as "I04". *)
      (* iPoseProof (black_white_update with "I0B EXCL") as ">[I0B EXCL]". *)
      (* instantiate (1:= tvw1). *)
      (* iMod ("K0" with "[I0B I01 I02 I03 I04]") as "_". *)
      (* { iExists tvw1. iFrame. unfold thread1_will_write. iExists k0. iFrame. } *)
      (* msubtac. *)

      iPoseProof ("SIM" with "[MYTH DUTY NEWW2 EXCL EXCL2 EXCL3 LOCK]") as "SIM".
      { instantiate (1:= tvw'). iFrame. iSplit.
        { iPureIntro. etrans. 2: eapply l0. apply View.join_l. }
        iSplitL "DUTY NEWW2 LOCK". iExists k. iFrame.
        iExists _. iFrame. iPureIntro.
        etrans. 2: eapply l0. apply View.join_r.
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
        (tvw0 lvw: View.t)
    :
    ((inv N_lock lock_will_unlock)
       ∗
       (inv N_user client_invariant)
       ∗
       (OwnM (Excl.just tt: Excl.t unit))
       ∗
       (OwnM (Auth.white (Excl.just tvw0: Excl.t View.t)))
       ∗
       ((OwnM (Auth.white (Excl.just (lvw, tt): Excl.t (View.t * unit)))) ∗ (⌜View.le lvw tvw0⌝))
       ∗
       (∃ k, (ObligationRA.duty inlp tid ((k, Ord.S Ord.O) :: l))
               ∗ (OwnM (Auth.white (Excl.just k: Excl.t nat)))
               ∗ (ObligationRA.taxes ((k, Ord.S Ord.O) :: l) 4%ord))
    )
      ∗
      (∀ tvw1,
          ((ObligationRA.duty inlp tid l)
             ∗ (⌜View.le tvw0 tvw1⌝)
          )
            -∗
            (stsim tid ⊤ r g Q
                   false false
                   (trigger Yield;;; src)
                   (tgt tvw1)))
      ⊢
      (stsim tid ⊤ r g Q
             false false
             (trigger Yield;;; src)
             (tvw' <- OMod.close_itree ClientImpl.omod (ModAdd (WMem.mod) AbsLockW.mod) (R:=View.t) (OMod.call "unlock" tvw0);; (tgt tvw'))).
  Proof.
    iIntros "[[# LOCK_INV [# CLIENT_INV [EXCLTT [EXCL [[EXCL2 %LVW] [% [DUTY [LOCK TAXES]]]]]]]] SIM]".
    iPoseProof (ObligationRA.taxes_ord_split_one with "TAXES") as "> [TAXES TAX]".
    { instantiate (1:= 3%ord). apply OrdArith.lt_from_nat. lia. }
    iPoseProof (ObligationRA.taxes_ord_split_one with "TAXES") as "> [TAXES TAX1]".
    { instantiate (1:= 2%ord). apply OrdArith.lt_from_nat. lia. }
    iPoseProof (ObligationRA.taxes_ord_split_one with "TAXES") as "> [TAXES TAX2]".
    { instantiate (1:= 1%ord). apply OrdArith.lt_from_nat. lia. }
    iPoseProof (ObligationRA.taxes_single_is_tax with "TAXES") as "TAX3".

    rewrite close_itree_call. ss. rred. unfold OMod.emb_callee, emb_r. rewrite <- map_event_compose. rewrite <- plmap_compose.
    iApply (stsim_yieldR with "[DUTY TAX]"). msubtac. iFrame.
    iIntros "DUTY _". rred.
    unfold AbsLockW.unlock_fun, Mod.wrap_fun. rred.
    iApply (stsim_yieldR with "[DUTY TAX1]"). msubtac. iFrame.
    iIntros "DUTY _". rred.
    iInv "LOCK_INV" as "I1" "K1". do 6 (iDestruct "I1" as "[% I1]").
    iDestruct "I1" as "[B1 [B2 [MEM [STGT [BLKS [SUM [[CONTRA | CASE] INGS]]]]]]]".
    { iDestruct "CONTRA" as "[_ [_ [EXCL3 _]]]".
      iPoseProof (white_white_excl with "EXCL EXCL3") as "%FF". inversion FF.
    }
    iDestruct "CASE" as "[% [JPEND [JBLK [JCOR AMPs]]]]". subst own.
    iApply stsim_getR. iSplit. iFrame. ss.

    iDestruct "B2" as "[B2 B3]".
    iPoseProof (black_white_equal with "B3 EXCL2") as "%EQ". inv EQ.
    destruct (excluded_middle_informative (View.le lvw tvw0)).
    2:{ rred. exfalso. clarify. }

    rred. iDestruct "INGS" as "[[%INGF INGEXCL] | [_ CONTRA]]".
    2:{ iPoseProof (excl_unique with "EXCLTT CONTRA") as "%FF". inv FF. }
    subst ing. rred. ss.
    iApply (stsim_modifyR with "STGT"). iIntros "STGT". rred. ss. repeat (unfold Lens.set; ss).

    iPoseProof (black_white_equal with "B2 LOCK") as "%EQ". subst k.
    iMod ("K1" with "[EXCLTT B1 B2 B3 MEM BLKS SUM STGT JPEND JBLK JCOR AMPs]") as "_".
    { unfold lock_will_unlock. iExists true, lvw, true, mem, wobl, j. iFrame. iSplitR "EXCLTT".
      - iRight. iSplit. auto. iFrame.
      - iRight. iSplit. auto. iFrame.
    }
    msubtac.
    iApply (stsim_yieldR with "[DUTY TAX2]"). msubtac. iFrame.
    iIntros "DUTY _". rred.

    iInv "LOCK_INV" as "I1" "K1". do 6 (iDestruct "I1" as "[% I1]").
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
    iApply stsim_chooseR. iIntros "%". destruct x. rename x into tvw_V. rred.
    (* iApply stsim_chooseR. iIntros "%". rename x into tvw_V. rred. *)
    iApply (stsim_modifyR with "STGT"). iIntros "STGT". rred.

    iApply stsim_chooseR. iIntros "%". destruct x. rename x into tvw'. rred.

    iPoseProof (black_white_equal with "B2 LOCK") as "%". subst.
    iPoseProof (black_white_update with "B3 EXCL2") as ">[B3 EXCL2]".
    instantiate (1:= (tvw_V, tt)).
    iInv "CLIENT_INV" as "I0" "K0". iDestruct "I0" as "[% [I0B I0]]".
    iDestruct "I0" as "[% I0]". iDestruct "I0" as "[I01 [I02 [I03 I04]]]".
    iPoseProof (black_white_equal with "I0B EXCL") as "%". subst.
    iAssert (
  ((ObligationRA.pending k (/ 2) ** wpoints_to loc_X const_0 tvw0)
   ∨ (ObligationRA.shot k ** wpoints_to loc_X const_42 tvw0))
    -∗
  ((ObligationRA.pending k (/ 2) ** wpoints_to loc_X const_0 tvw_V)
   ∨ (ObligationRA.shot k ** wpoints_to loc_X const_42 tvw_V))
      )%I with "[]" as "I04a".
    { iIntros "I". iDestruct "I" as "[[A B] | [A B]]".
      - iLeft. iFrame. iApply wpoints_to_view_mon. 2: iFrame. auto.
      - iRight. iFrame. iApply wpoints_to_view_mon. 2: iFrame. auto.
    }
    iPoseProof ("I04a" with "I04") as "I04".
    iPoseProof (black_white_update with "I0B EXCL") as ">[I0B EXCL]".
    instantiate (1:= tvw_V).

    iMod ("K0" with "[I0B I01 I02 I03 I04]") as "_".
    { iExists tvw_V. iFrame. unfold thread1_will_write. iExists k. iFrame. }
    iMod ("K1" with "[INGEXCL EXCLTT EXCL EXCL2 LOCK B1 B2 B3 MEM BLKS SUM STGT]") as "_".
    { unfold lock_will_unlock. iExists false, tvw_V, false, mem0, wobl0, j. iFrame. iSplitR "INGEXCL".
      - iLeft. iSplit. auto. iFrame.
      - iLeft. iSplit. auto. iFrame.
    }
    iPoseProof (ObligationRA.pending_shot with "JPEND") as "> SHOT".
    iPoseProof (ObligationRA.duty_done with "DUTY SHOT") as "> DUTY".

    (* iApply stsim_chooseR. iIntros "%". destruct x. rename x into tvw''. rred. *)
    (* iApply stsim_tauR. rred. *)

    iApply (stsim_yieldR with "[DUTY TAX3]"). msubtac.
    { iSplitL "DUTY". iFrame.
      iPoseProof (ObligationRA.tax_cons_unfold with "TAX3") as "[_ TAX2]". iFrame.
    }
    iIntros "DUTY _". rred.
    iApply stsim_tauR. rred.
    iApply stsim_reset. iApply "SIM". iFrame.
    iPureIntro. etrans. 2: eapply l2. auto.

  Qed.

  Lemma correct_thread1 tid:
    (inv N_lock lock_will_unlock)
      -∗
      (inv N_user client_invariant)
      -∗
      (∃ k, (own_thread tid)
              ∗ (ObligationRA.duty inlp tid [(k, Ord.from_nat 1)])
              ∗ (ObligationRA.taxes
                   [(k, Ord.from_nat 1)]
                   ((((Ord.omega × Ord.omega) × Ord.omega) ⊕ ((Ord.S Ord.O) × (o_w_cor))) ⊕ 10)%ord
                )
              ∗ (OwnM (OneShot.shot k))
              ∗ (ObligationRA.pending k (/ 2))
      )
      -∗
      (stsim tid ⊤ ibot7 ibot7
             (fun r_src r_tgt => own_thread tid ** ObligationRA.duty inlp tid [] ** ⌜r_src = r_tgt⌝)
             false false
             (ClientSpec.thread1 tt)
             (OMod.close_itree ClientImpl.omod (ModAdd (WMem.mod) AbsLockW.mod) (ClientImpl.thread1 tt))).
  Proof.
    iIntros "# LOCK_INV # CLIENT_INV [% [TH [DUTY [TAXES [#KSHOT KPENDh]]]]]".
    unfold ClientSpec.thread1, ClientImpl.thread1. rred.
    iPoseProof (ObligationRA.taxes_ord_split_one with "TAXES") as "> [TAXES TAX]".
    { apply Hessenberg.lt_add_r. instantiate (1:=9). apply OrdArith.lt_from_nat. auto. }
    iApply AbsLock_lock. iFrame. iSplit; [auto|].
    iIntros "% [%VW0 [MYTH [SUM1 [SUM2 EXCLTT]]]]".
    iDestruct "SUM1" as "[% [DUTY [WHI LOCK]]]". iDestruct "SUM2" as "[% [EXCL [EXCL2 %VW1]]]".
    instantiate (1:=9). rred.
    rewrite close_itree_call. ss. unfold OMod.emb_callee, emb_l. rewrite <- map_event_compose. rewrite <- plmap_compose. rred.
    iPoseProof (ObligationRA.white_eq with "WHI") as "WHI".
    { rewrite Ord.from_nat_S. rewrite Jacobsthal.mult_S. reflexivity. }
    iPoseProof (ObligationRA.white_split_eq with "WHI") as "[WHI1 WHI2]".
    iApply (stsim_yieldR with "[DUTY WHI1 TAX]"). msubtac.
    { iSplitL "DUTY". iFrame.
      iApply ObligationRA.tax_cons_fold. iSplitL "WHI1"; auto.
      iApply ObligationRA.white_eq. 2: iFrame. symmetry; apply Jacobsthal.mult_1_l.
    }
    iIntros "DUTY _". rred. unfold WMem.store_fun, Mod.wrap_fun. rred.

    iInv "CLIENT_INV" as "I0" "K0".
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

    iInv "LOCK_INV" as "I1" "K1". do 6 (iDestruct "I1" as "[% I1]").
    iDestruct "I1" as "[i1B1 [i1B2 [i1MEM [i1STGT I1]]]]".

    iApply stsim_getR. iSplit. iFrame. rred.
    iApply stsim_chooseR. iIntros "%". rred.
    destruct x. destruct x as [[[lc1 to] sc1] mem1]. des. rename y into WRITE.
    iPoseProof (wpoints_to_view_mon with "i0PTR") as "i0PTR". eapply VW1.
    iPoseProof (wmemory_ra_store with "i1MEM i0PTR") as "[%VW2 >[i1MEM i0PTR]]".
    eapply WRITE. eauto. eauto. eauto. eauto.

    iPoseProof (black_white_update with "EXCLB EXCL") as ">[EXCLB EXCL]".
    instantiate (1:= TView.TView.cur (Local.Local.tview lc1)). destruct lc1. ss. rred.
    iApply stsim_fairR.
    { i. instantiate (1:= []). ss. clear - IN.
      unfold prism_fmap, WMem.missed in IN. des_ifs.
    }
    { i. instantiate (1:=[]) in IN. inv IN. }
      (* instantiate (1:= [inr (inl (loc_X, to))]) in IN. *)
    (* inv IN; ss. des_ifs. *)
    { econs. }
    { auto. }
    iIntros "_ _". rred.
    iApply (stsim_modifyR with "i1STGT"). iIntros "i1STGT". rred. iApply stsim_tauR. rred.

    rewrite Qp.inv_half_half.
    iPoseProof (ObligationRA.pending_shot with "KPEND") as "> #OBLKSHOT".

    iMod ("K1" with "[i1B1 i1B2 i1MEM i1STGT I1]") as "_".
    { unfold lock_will_unlock. iExists own, tvw0, ing, _, wobl, j0. iFrame. }

    iMod ("K0" with "[EXCLB i0BLK i0KCOR i0PTR]") as "_".
    { iExists (TView.TView.cur tview). iFrame.
      unfold thread1_will_write. iExists k. iFrame. iSplitR; auto. }

    iPoseProof (ObligationRA.white_mon with "WHI2") as ">WHI2".
    { instantiate (1:= (Ord.omega × 4)%ord). apply Jacobsthal.le_mult_r. apply OrdArith.le_from_nat. lia. }

    iPoseProof (ObligationRA.duty_permutation with "DUTY") as "DUTY".
    { eapply perm_swap. }
    iPoseProof (ObligationRA.duty_done with "DUTY OBLKSHOT") as "> DUTY".
    iApply stsim_reset. iApply AbsLock_unlock. iSplitL "EXCL EXCL2 EXCLTT LOCK WHI2 DUTY".
    { iSplit; [auto|]. iSplit; [auto|].
      iSplitL "EXCLTT". iFrame. iSplitL "EXCL". iFrame. iSplitL "EXCL2".
      { iFrame. iPureIntro. etrans. eapply VW1. auto. }
      iExists j. iFrame. iApply ObligationRA.taxes_cons_fold. iSplitL; auto.
      iApply ObligationRA.white_eq. 2: iFrame.
      rewrite Jacobsthal.mult_1_l. reflexivity.
    }
    iIntros "% [DUTY %VW3]". rred.
    iApply (stsim_sync with "[DUTY]"). msubtac. iFrame.
    iIntros "DUTY _". rred. iApply stsim_tauR. rred.
    iApply stsim_ret. iModIntro. iFrame. auto.

  Qed.

  Lemma correct_thread2 tid:
    (inv N_lock lock_will_unlock)
      -∗
      (inv N_user client_invariant)
      -∗
      ((own_thread tid)
         ∗ (ObligationRA.duty inlp tid [])
      )
      -∗
      (stsim tid ⊤ ibot7 ibot7
             (fun r_src r_tgt => own_thread tid ** ObligationRA.duty inlp tid [] ** ⌜r_src = r_tgt⌝)
             false false
             (ClientSpec.thread2 tt)
             (OMod.close_itree ClientImpl.omod (ModAdd (WMem.mod) AbsLockW.mod) (ClientImpl.thread2 tt))).
  Proof.
    iIntros "# LOCK_INV # CLIENT_INV [MYTH DUTY]".
    unfold ClientSpec.thread2, ClientImpl.thread2. rred.
    iInv "CLIENT_INV" as "I0" "K0".
    iDestruct "I0" as "[% [EXCLB I0]]". iDestruct "I0" as "[% [[% #KBLK] [#KCOR [#KSHOT I0]]]]".
    iMod ("K0" with "[EXCLB I0]") as "_".
    { iExists tvw. iFrame. unfold thread1_will_write. iExists k. iFrame. auto. }

    (* induction *)
    rred. remember View.bot as tvw_base. clear tvw Heqtvw_base.
    iStopProof. revert tid k tvw_base. pattern n. revert n.
    apply (well_founded_induction Ord.lt_well_founded). intros n IH. intros.
    iIntros "[#[LOCK_INV [CLIENT_INV [KBLK [KCOR KSHOT]]]] [MYTH DUTY]]".
    rewrite unfold_iter_eq. rred.
    iApply AbsLock_lock. iSplitL "MYTH DUTY".
    { iFrame. auto. }
    iIntros "% [%VW0 [MYTH [SUM1 [SUM2 EXCLTT]]]]".
    iDestruct "SUM1" as "[% [DUTY [WHI LOCK]]]". iDestruct "SUM2" as "[% [EXCL [EXCL2 %VW1]]]".
    instantiate (1:= 9). rred.

    rewrite close_itree_call. ss. unfold OMod.emb_callee, emb_l. rewrite <- map_event_compose. rewrite <- plmap_compose. rred.
    iPoseProof (ObligationRA.white_eq with "WHI") as "WHI".
    { rewrite Ord.from_nat_S. rewrite Jacobsthal.mult_S. reflexivity. }
    iPoseProof (ObligationRA.white_split_eq with "WHI") as "[WHI1 WHI2]".
    iApply (stsim_yieldR with "[DUTY WHI1]"). msubtac.
    { iSplitL "DUTY". iFrame.
      iApply ObligationRA.tax_cons_fold. iSplitL "WHI1"; auto.
      iApply ObligationRA.white_eq. 2: iFrame. symmetry; apply Jacobsthal.mult_1_l.
    }
    iIntros "DUTY OWHTH". rred. unfold WMem.load_fun, Mod.wrap_fun. rred.

    iInv "CLIENT_INV" as "I0" "K0". iDestruct "I0" as "[% [EXCLB I0]]".
    iPoseProof (black_white_equal with "EXCLB EXCL") as "%EQ". subst tvw0.
    iDestruct "I0" as "[% [i0BLK [i0KCOR [#i0KSHOT [i0PEND | i0SHOT]]]]]".

    (* iterate case *)
    { iDestruct "i0PEND" as "[i0PENDh i0PTR]".
      iPoseProof (OwnM_valid with "[KSHOT i0KSHOT]") as "%AGR".
      { instantiate (1:= (OneShot.shot k) ⋅ (OneShot.shot k0)). iSplitL "KSHOT"; auto. }
      apply OneShot.shot_agree in AGR. subst k0.

      iInv "LOCK_INV" as "I1" "K1". do 6 (iDestruct "I1" as "[% I1]").
      iDestruct "I1" as "[i1B1 [i1B2 [i1MEM [i1STGT I1]]]]".
      iApply stsim_getR. iSplit. iFrame. rred.
      iApply stsim_chooseR. iIntros "%".
      destruct x. destruct x as [[lc1 val] to]. des. rename y into READ. rred.
      iPoseProof (wpoints_to_view_mon with "i0PTR") as "i0PTR". eapply VW1.
      iPoseProof (wmemory_ra_load with "i1MEM i0PTR") as "[i1MEM [%VW2 >i0PTR]]".
      eapply READ. eauto. eauto. des. subst val.

      iPoseProof (black_white_update with "EXCLB EXCL") as ">[EXCLB EXCL]".
      instantiate (1:= TView.TView.cur (Local.Local.tview lc1)). destruct lc1. ss. rred.
      iApply stsim_fairR.
      { i. instantiate (1:= []). ss. clear - IN.
        unfold prism_fmap, WMem.missed in IN. des_ifs.
      }
      { i. instantiate (1:=[]) in IN. inv IN. }
      { econs. }
      { auto. }
      iIntros "_ _". rred.
      iApply stsim_tauR. rred.

      iMod ("K1" with "[i1B1 i1B2 i1MEM i1STGT I1]") as "_".
      { unfold lock_will_unlock. iExists own, tvw0, ing, mem, wobl, j0. iFrame. }
      iMod ("K0" with "[EXCLB i0BLK i0KCOR i0PTR i0PENDh]") as "_".
      { iExists (TView.TView.cur tview). iFrame. unfold thread1_will_write. iExists k. iFrame. iSplitR; auto. iLeft; iFrame. }
      clear own mem wobl j0 released READ.
      iPoseProof (ObligationRA.white_mon with "WHI2") as ">WHI2".
      { instantiate (1:= (Ord.omega × 4)%ord). apply Jacobsthal.le_mult_r. apply OrdArith.le_from_nat. lia. }
      iApply stsim_reset. iApply AbsLock_unlock. iSplitL "LOCK EXCLTT EXCL EXCL2 WHI2 DUTY".
      { iSplit; [auto|]. iSplit; [auto|].
        iSplitL "EXCLTT". iFrame. iSplitL "EXCL". iFrame. iSplitL "EXCL2".
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
        iClear "KBLK". iApply stsim_reset. iApply IH. apply DECR. iFrame.
        iModIntro. eauto.
      }

      (* thread 1 done; exit *)
      { iClear "KBLK KCOR". clear_upto N_user_N_lock_disjoint.
        rewrite unfold_iter_eq. rred.
        iApply stsim_reset. iApply AbsLock_lock. iSplitL "MYTH DUTY".
        { iFrame. auto. }
        iIntros "% [%VW0 [MYTH [SUM1 [SUM2 EXCLTT]]]]".
        iDestruct "SUM1" as "[% [DUTY [WHI LOCK]]]". iDestruct "SUM2" as "[% [EXCL [EXCL2 %VW1]]]".
        instantiate (1:= 9). rred.

        iInv "CLIENT_INV" as "I0" "K0". iDestruct "I0" as "[% [EXCLB I0]]".
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

        rewrite close_itree_call. ss. unfold OMod.emb_callee, emb_l. rewrite <- map_event_compose. rewrite <- plmap_compose. rred.
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
        iInv "LOCK_INV" as "I1" "K1". do 6 (iDestruct "I1" as "[% I1]").
        iDestruct "I1" as "[i1B1 [i1B2 [i1MEM [i1STGT I1]]]]".
        iApply stsim_getR. iSplit. iFrame. rred.
        iClear "i0KSHOT". iInv "CLIENT_INV" as "I0" "K0".
        iDestruct "I0" as "[% [EXCLB I0]]".
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
        iPoseProof (black_white_update with "EXCLB EXCL") as ">[EXCLB EXCL]".
        instantiate (1:= TView.TView.cur (Local.Local.tview lc1)). destruct lc1. ss. rred.
        iApply stsim_fairR.
        { i. instantiate (1:= []). ss. clear - IN.
          unfold prism_fmap, WMem.missed in IN. des_ifs.
        }
        { i. instantiate (1:=[]) in IN. inv IN. }
        { econs. }
        { auto. }
        iIntros "_ _". rred.
        iApply stsim_tauR. rred.

        iMod ("K0" with "[EXCLB i0BLK i0KCOR i0PTR]") as "_".
        { iExists _. iFrame. unfold thread1_will_write. iExists _. iFrame. iSplitR; auto. }
        iMod ("K1" with "[i1B1 i1B2 i1MEM i1STGT I1]") as "_".
        { unfold lock_will_unlock. iExists own, tvw3, ing, mem, wobl, j0. iFrame. }
        msubtac.
        clear own mem wobl j0 promises to released READ.
        iPoseProof (ObligationRA.white_mon with "WHI2") as ">WHI2".
        { instantiate (1:= (Ord.omega × 4)%ord). apply Jacobsthal.le_mult_r. apply OrdArith.le_from_nat. lia. }
        iApply stsim_reset. iApply AbsLock_unlock. iSplitL "LOCK EXCLTT EXCL EXCL2 WHI2 DUTY".
        { iSplit; [auto|]. iSplit; [auto|].
          iSplitL "EXCLTT". iFrame. iSplitL "EXCL". iFrame. iSplitL "EXCL2".
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
        iApply stsim_ret. iModIntro. iFrame. auto.
      }
    }

    { iDestruct "i0SHOT" as "[#KDONE i0PTR]".
      iPoseProof (OwnM_valid with "[KSHOT i0KSHOT]") as "%AGR".
      { instantiate (1:= (OneShot.shot k) ⋅ (OneShot.shot k0)). iSplitL "KSHOT"; auto. }
      apply OneShot.shot_agree in AGR. subst k0.

      iInv "LOCK_INV" as "I1" "K1". do 6 (iDestruct "I1" as "[% I1]").
      iDestruct "I1" as "[i1B1 [i1B2 [i1MEM [i1STGT I1]]]]".
      iApply stsim_getR. iSplit. iFrame. rred.
      iApply stsim_chooseR. iIntros "%".
      destruct x. destruct x as [[lc1 val] to]. des. rename y into READ. rred.
      iPoseProof (wpoints_to_view_mon with "i0PTR") as "i0PTR". eapply VW1.
      iPoseProof (wmemory_ra_load with "i1MEM i0PTR") as "[i1MEM [%VW3 >i0PTR]]".
      eapply READ. eauto. eauto. des. subst val.
      iPoseProof (black_white_update with "EXCLB EXCL") as ">[EXCLB EXCL]".
      instantiate (1:= TView.TView.cur (Local.Local.tview lc1)). destruct lc1. ss. rred.
      iApply stsim_fairR.
      { i. instantiate (1:= []). ss. clear - IN.
        unfold prism_fmap, WMem.missed in IN. des_ifs.
      }
      { i. instantiate (1:=[]) in IN. inv IN. }
      { econs. }
      { auto. }
      iIntros "_ _". rred.
      iApply stsim_tauR. rred.

      iMod ("K1" with "[i1B1 i1B2 i1MEM i1STGT I1]") as "_".
      { unfold lock_will_unlock. iExists own, tvw0, ing, mem, wobl, j0. iFrame. }
      iMod ("K0" with "[EXCLB i0BLK i0KCOR i0PTR]") as "_".
      { iExists _. iFrame. unfold thread1_will_write. iExists _. iFrame. iSplitR; auto. }
      clear own mem wobl j0 promises to released READ.
      iPoseProof (ObligationRA.white_mon with "WHI2") as ">WHI2".
      { instantiate (1:= (Ord.omega × 4)%ord). apply Jacobsthal.le_mult_r. apply OrdArith.le_from_nat. lia. }
      iApply stsim_reset. iApply AbsLock_unlock. iSplitL "LOCK EXCLTT EXCL EXCL2 WHI2 DUTY".
      { iSplit; [auto|]. iSplit; [auto|].
        iSplitL "EXCLTT". iFrame. iSplitL "EXCL". iFrame. iSplitL "EXCL2".
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
      iModIntro. iFrame. auto.
    }

  Qed.

End SIM.

From Fairness Require Import WeakestAdequacy.

Module LockClientWCorrect.
  Definition config := [("thread1", tt↑); ("thread2", tt↑)].

  Local Instance Σ: GRA.t:=
    GRA.of_list [monoRA;
                 ThreadRA;
                 (stateSrcRA (unit));
                 (stateTgtRA ((OMod.closed_state ClientImpl.omod (ModAdd (WMem.mod) AbsLockW.mod))));
                 (identSrcRA (void));
                 (identTgtRA (OMod.closed_ident ClientImpl.omod (ModAdd (WMem.mod) AbsLockW.mod))%type);
                 ObligationRA.t;
                 (ArrowRA (OMod.closed_ident ClientImpl.omod (ModAdd (WMem.mod) AbsLockW.mod))%type);
                 EdgeRA;
                 (@FiniteMap.t (OneShot.t unit));
                 wmemRA;
                 (Excl.t unit);
                 (Excl.t (unit * unit));
                 (OneShot.t nat);
                 (Region.t (thread_id * nat));
                 (@FiniteMap.t (Consent.t nat));
                 (Auth.t (Excl.t nat));
                 (Auth.t (Excl.t View.t));
                 (Auth.t (Excl.t (View.t * unit)));
                 (Auth.t (NatMapRAFOS.t nat));
                 CoPset.t;
                 Gset.t;
                 InvSetRA (Prop)
                 (* InvSetRA (bool) *)
      ].

  Local Instance MONORA: @GRA.inG monoRA Σ := (@GRA.InG _ _ 0 (@eq_refl _ _)).
  Local Instance THDRA: @GRA.inG ThreadRA Σ := (@GRA.InG _ _ 1 (@eq_refl _ _)).
  Local Instance STATESRC: @GRA.inG (stateSrcRA (unit)) Σ := (@GRA.InG _ _ 2 (@eq_refl _ _)).
  Local Instance STATETGT: @GRA.inG (stateTgtRA ((OMod.closed_state ClientImpl.omod (ModAdd (WMem.mod) AbsLockW.mod)))) Σ := (@GRA.InG _ _ 3 (@eq_refl _ _)).
  Local Instance IDENTSRC: @GRA.inG (identSrcRA (void)) Σ := (@GRA.InG _ _ 4 (@eq_refl _ _)).
  Local Instance IDENTTGT: @GRA.inG (identTgtRA (OMod.closed_ident ClientImpl.omod (ModAdd (WMem.mod) AbsLockW.mod))%type) Σ := (@GRA.InG _ _ 5 (@eq_refl _ _)).
  Local Instance OBLGRA: @GRA.inG ObligationRA.t Σ := (@GRA.InG _ _ 6 (@eq_refl _ _)).
  Local Instance ARROWRA: @GRA.inG (ArrowRA (OMod.closed_ident ClientImpl.omod (ModAdd (WMem.mod) AbsLockW.mod))%type) Σ := (@GRA.InG _ _ 7 (@eq_refl _ _)).
  Local Instance EDGERA: @GRA.inG EdgeRA Σ := (@GRA.InG _ _ 8 (@eq_refl _ _)).
  Local Instance ONESHOTSRA: @GRA.inG (@FiniteMap.t (OneShot.t unit)) Σ := (@GRA.InG _ _ 9 (@eq_refl _ _)).

  Local Instance WMEMRA: @GRA.inG wmemRA Σ := (@GRA.InG _ _ 10 (@eq_refl _ _)).
  Local Instance EXCL: @GRA.inG (Excl.t unit) Σ := (@GRA.InG _ _ 11 (@eq_refl _ _)).
  Local Instance EXCL2: @GRA.inG (Excl.t (unit * unit)) Σ := (@GRA.InG _ _ 12 (@eq_refl _ _)).
  Local Instance ONESHOTRA: @GRA.inG (OneShot.t nat) Σ := (@GRA.InG _ _ 13 (@eq_refl _ _)).
  Local Instance REGIONRA: @GRA.inG (Region.t (thread_id * nat)) Σ := (@GRA.InG _ _ 14 (@eq_refl _ _)).
  Local Instance CONSENTRA: @GRA.inG (@FiniteMap.t (Consent.t nat)) Σ := (@GRA.InG _ _ 15 (@eq_refl _ _)).
  Local Instance AUTHNRA: @GRA.inG (Auth.t (Excl.t nat)) Σ := (@GRA.InG _ _ 16 (@eq_refl _ _)).
  Local Instance AUTHVWRA: @GRA.inG (Auth.t (Excl.t View.t)) Σ := (@GRA.InG _ _ 17 (@eq_refl _ _)).
  Local Instance AUTHVWRA2: @GRA.inG (Auth.t (Excl.t (View.t * unit))) Σ := (@GRA.InG _ _ 18 (@eq_refl _ _)).
  Local Instance AUTHNMNRA: @GRA.inG (Auth.t (NatMapRAFOS.t nat)) Σ := (@GRA.InG _ _ 19 (@eq_refl _ _)).

  Local Instance COPSETRA: @GRA.inG CoPset.t Σ := (@GRA.InG _ _ 20 (@eq_refl _ _)).
  Local Instance GSETRA : @GRA.inG Gset.t Σ := (@GRA.InG _ _ 21 (@eq_refl _ _)).
  Local Instance INVSETRA : @GRA.inG (InvSetRA Prop) Σ := (@GRA.InG _ _ 22 (@eq_refl _ _)).
  (* Local Instance INVSETRA : @GRA.inG (InvSetRA bool) Σ := (@GRA.InG _ _ 22 (@eq_refl _ _)). *)

  Local Instance Invs : @InvSet Σ := {| Var := Prop; prop := fun (b : Prop) => if (excluded_middle_informative b) then lock_will_unlock else (∃ tvw, (OwnM (Auth.black (Excl.just tvw: Excl.t View.t))) ∗ (thread1_will_write tvw))%I |}.
  (* Local Instance Invs : @InvSet Σ := {| Var := bool; prop := fun b => if b then lock_will_unlock else (∃ tvw, (OwnM (Auth.black (Excl.just tvw: Excl.t View.t))) ∗ (thread1_will_write tvw))%I |}. *)
  Import stdpp.namespaces.
  Let lock_namespace := nroot .@ "TicketLock".
  Let client_namespace := nroot .@ "Client".


  Let init_res :=
        (GRA.embed (OneShot.pending nat 1))
          ⋅ GRA.embed (Auth.black (Some (NatMap.empty nat) : NatMapRAFOS.t nat))
          ⋅ GRA.embed (Auth.black (Excl.just 0 : Excl.t nat) ⋅ Auth.white (Excl.just 0 : Excl.t nat))
          ⋅ GRA.embed (Auth.black (Excl.just View.bot : Excl.t View.t) ⋅ Auth.white (Excl.just View.bot : Excl.t View.t))
          ⋅ GRA.embed (Auth.black (Excl.just (View.bot, ()) : Excl.t (View.t * unit))
                                  ⋅ Auth.white (Excl.just (View.bot, ()) : Excl.t (View.t * unit)))
          ⋅ GRA.embed (Excl.just (tt,tt): Excl.t (unit * unit))
          ⋅ GRA.embed (Excl.just () : Excl.t unit)
          ⋅ GRA.embed  (wmem_init_res loc_X (Loc.of_nat 5))
  .

  Arguments stsim_bind_top {_ _ _ _ _ _}.
  Arguments stsim_wand {_ _ _ _ _ _}.
  Arguments stsim_ret {_ _ _ _ _ _}.

  Lemma correct:
    UserSim.sim ClientSpec.mod ClientImpl.mod (prog2ths ClientSpec.mod config) (prog2ths ClientImpl.mod config).
  Proof.
    eapply WSim.whole_sim_implies_usersim. econs.
    { instantiate (1:=init_res). rr. splits.
      { unfold init_res, default_initial_res. disj_tac. }
      { ndtac. }
      { unfold init_res. grawf_tac.
        { ur. auto. }
        { ur. split; auto.
          { eexists. eapply URA.unit_idl. }
          { ur. auto. }
        }
        { ur. split.
          { eexists _. rewrite URA.unit_idl. eapply URA.unit_id. }
          { ur. ss. }
        }
        { ur. split.
          { eexists _. rewrite URA.unit_idl. eapply URA.unit_id. }
          { ur. ss. }
        }
        { ur. split.
          { eexists _. rewrite URA.unit_idl. eapply URA.unit_id. }
          { ur. ss. }
        }
        { ur. ss. }
        { ur. ss. }
        { apply wmem_init_res_wf. ss. }
      }
    }
    unfold init_res. repeat rewrite <- GRA.embed_add.
    eexists _. iIntros "[[[[[[[[A B] [C0 C1]] [D0 D1]] [E0 E1]] F] G] H] INIT]".
    iPoseProof (init_sat with "[A B C0 C1 D0 D1 E0 E1 F G H INIT]") as "> [[% [H0 H1]] [H2 [[% [H3 [H5 [H6 [H7 H8]]]]] H4]]]".
    { instantiate (1:=1). instantiate (1:=0). ss. }
    { iFrame. }
    iMod (FUpd_alloc with "H2") as "# LOCK_INV".
    { econs. instantiate (1:=True). ss. des_ifs. }
    (* { econs. instantiate (1:=true). ss. } *)
    iMod (FUpd_alloc with "[H0 H1]") as "# CLIENT_INV".
    { econs. instantiate (2:=False). ss. }
    (* { econs. instantiate (2:=false). ss. } *)
    { des_ifs. iExists _. iFrame. }
    (* { iExists _. iFrame. } *)
    iModIntro. unfold MonotonePCM.natmap_prop_sum. ss.
    iSplitL "H3 H5 H6 H7 H8".
    { unfold fn2th. ss. unfold Mod.wrap_fun. lred. rred.
      iApply stsim_bind_top. iApply (stsim_wand with "[H3 H5 H6 H7 H8]").
      { iApply correct_thread1.
        { instantiate (1:=lock_namespace). instantiate (1:=client_namespace).
          eapply ndot_ne_disjoint. ss.
        }
        { eauto. }
        { des_ifs. }
        (* { eauto. } *)
        iExists _. iFrame.
      }
      { iIntros (? ?) "[[H0  H1] %]". subst. iModIntro.
        lred. rred. iApply stsim_ret. iModIntro. iFrame. iPureIntro. auto.
      }
    }
    iSplit; [|auto]. iDestruct "H4" as "[H0 H1]".
    { unfold fn2th. ss. unfold Mod.wrap_fun. lred. rred.
      iApply stsim_bind_top. iApply (stsim_wand with "[H0 H1]").
      { iApply correct_thread2.
        { instantiate (1:=lock_namespace). instantiate (1:=client_namespace).
          eapply ndot_ne_disjoint. ss.
        }
        { eauto. }
        { des_ifs. }
        (* { eauto. } *)
        iFrame.
      }
      { iIntros (? ?) "[[H0  H1] %]". subst. iModIntro.
        lred. rred. iApply stsim_ret. iModIntro. iFrame. iPureIntro. auto.
      }
    }
  Qed.

End LockClientWCorrect.
