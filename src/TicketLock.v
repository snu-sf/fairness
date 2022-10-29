From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Export ITreeLib WFLib FairBeh NatStructs Mod pind Axioms OpenMod SCM Red IRed Wrapper.
From Ordinal Require Export ClassicalHessenberg.


Set Implicit Arguments.


Module FairLock.
  Definition lock_fun: WMod.function bool unit void :=
    WMod.mk_fun
      tt
      (fun (_: unit) st next =>
         match st with
         | true => next = WMod.disabled
         | false => next = WMod.normal true tt (sum_fmap_l (fun _ => Flag.fail))
         end).

  Definition unlock_fun: WMod.function bool unit void :=
    WMod.mk_fun
      tt
      (fun (_: unit) st next =>
         match st with
         | false => next = WMod.stuck
         | true => next = WMod.normal false tt (sum_fmap_l (fun _ => Flag.emp))
         end).

  Definition wmod: WMod.t :=
    WMod.mk
      false
      [("lock", lock_fun);
       ("unlock", unlock_fun)
      ].

  Definition mod: Mod.t :=
    WMod.interp_mod wmod.
End FairLock.

Module TicketLock.
  Definition now_serving: SCMem.val := SCMem.val_ptr (0, 0).
  Definition next_ticket: SCMem.val := SCMem.val_ptr (0, 1).

  Definition lock_fun:
    ktree ((((@eventE void) +' cE) +' (sE unit)) +' OpenMod.callE) unit unit :=
    fun _ =>
      myticket <- (OMod.call "faa" (next_ticket, 1));;
      _ <- ITree.iter
             (fun (_: unit) =>
                next <- (OMod.call "load" (now_serving));;
                b <- (OMod.call "compare" (next: SCMem.val, myticket: SCMem.val));;          if (b: bool) then Ret (inr tt) else Ret (inl tt)) tt;;
      trigger Yield
  .

  Definition unlock_fun:
    ktree ((((@eventE void) +' cE) +' (sE unit)) +' OpenMod.callE) unit unit :=
    fun _ =>
      _ <- trigger Yield;;
      v <- (OMod.call "load" now_serving);;
      let v := SCMem.val_add v 1 in
      `_: unit <- (OMod.call "store" (now_serving, v));;
      trigger Yield
  .

  Definition omod: OMod.t :=
    OMod.mk
      tt
      (Mod.get_funs [("lock", Mod.wrap_fun lock_fun);
                     ("unlock", Mod.wrap_fun unlock_fun)])
  .

  Definition mod: Mod.t :=
    OMod.close
      (omod)
      (SCMem.mod [1; 1])
  .
End TicketLock.

From Fairness Require Import IProp IPM Weakest.
From Fairness Require Import ModSim PCM MonotonePCM ThreadsRA StateRA FairRA.


Section SIM.
  Context `{Σ: GRA.t}.


  Fixpoint list_prop_sum A (l: list A) (P: A -> iProp): iProp :=
    match l with
    | [] => True
    | hd::tl => P hd ** list_prop_sum tl P
    end.

  Lemma list_prop_sum_perm A (l0 l1: list A) P
        (PERM: Permutation l0 l1)
    :
    list_prop_sum l0 P ⊢ list_prop_sum l1 P.
  Proof.
    induction PERM; ss.
    { iIntros "[H0 H1]". iFrame. iApply IHPERM. auto. }
    { iIntros "[H0 [H1 H2]]". iFrame. }
    { etrans; eauto. }
  Qed.

  Definition natmap_prop_sum A (f: NatMap.t A) (P: nat -> A -> iProp) :=
    list_prop_sum (NatMap.elements f) (fun '(k, v) => P k v).

  Lemma natmap_prop_sum_empty A P
    :
    ⊢ natmap_prop_sum (NatMap.empty A) P.
  Proof.
    unfold natmap_prop_sum. ss. auto.
  Qed.

  Lemma natmap_prop_remove_find A (f: NatMap.t A) P k v
        (FIND: NatMap.find k f = Some v)
    :
    (natmap_prop_sum f P)
      -∗
      (P k v ** natmap_prop_sum (NatMap.remove k f) P).
  Proof.
    hexploit NatMap.elements_1.
    { eapply NatMap.find_2; eauto. }
    i. eapply SetoidList.InA_split in H. des.
    destruct y. inv H. ss. subst.
    unfold natmap_prop_sum. rewrite H0.
    iIntros "H".
    iPoseProof (list_prop_sum_perm with "H") as "H".
    { instantiate (1:=(k0,a)::(l1 ++ l2)).
      symmetry. apply Permutation_middle.
    }
    iEval (ss) in "H". iDestruct "H" as "[H0 H1]". iFrame.
    iApply (list_prop_sum_perm with "H1").
    symmetry. eapply Permutation_remove.
    rewrite H0. symmetry. apply Permutation_middle.
  Qed.

  Lemma natmap_prop_remove A (f: NatMap.t A) P k
    :
    (natmap_prop_sum f P)
      -∗
      (natmap_prop_sum (NatMap.remove k f) P).
  Proof.
    destruct (NatMap.find k f) eqn:EQ.
    { iIntros "H". iPoseProof (natmap_prop_remove_find with "H") as "[_ H]"; eauto. }
    replace (NatMap.remove k f) with f; auto.
    eapply eq_ext_is_eq. ii.
    rewrite NatMapP.F.remove_mapsto_iff. split.
    { i. split; auto. ii.
      eapply NatMap.find_1 in H. clarify.
    }
    { i. des. auto. }
  Qed.

  Lemma natmap_prop_sum_add A P k v (f: NatMap.t A)
    :
    (natmap_prop_sum f P)
      -∗
      (P k v)
      -∗
      (natmap_prop_sum (NatMap.add k v f) P).
  Proof.
    destruct (NatMapP.F.In_dec f k).
    { rewrite <- nm_add_rm_eq. iIntros "H0 H1".
      unfold natmap_prop_sum.
      iApply list_prop_sum_perm.
      { symmetry. eapply Permutation_add; eauto. apply NatMap.remove_1; auto. }
      iPoseProof (natmap_prop_remove with "H0") as "H0".
      ss. iFrame.
    }
    { unfold natmap_prop_sum. iIntros "H0 H1".
      iApply list_prop_sum_perm.
      { symmetry. eapply Permutation_add; eauto. }
      ss. iFrame.
    }
  Qed.

  Context `{EXCL: @GRA.inG (Excl.t unit) Σ}.
  Context `{MONORA: @GRA.inG monoRA Σ}.
  Context `{THSRA: @GRA.inG ths_RA Σ}.
  Context `{STATESRC: @GRA.inG (stateSrcRA (bool * NatMap.t unit)) Σ}.
  Context `{STATETGT: @GRA.inG (stateTgtRA (unit * SCMem.t)) Σ}.
  Context `{IDENTSRC: @GRA.inG (identSrcRA (id_sum thread_id void) (mk_wf Ord.lt_well_founded)) Σ}.
  Context `{IDENTTGT: @GRA.inG (identTgtRA (id_sum void SCMem.val)) Σ}.
  (* Context `{IDENTTHS: @GRA.inG identThsRA Σ}. *)
  Context `{MEMRA: @GRA.inG memRA Σ}.
  Context `{FAIRSRC: @GRA.inG (@FairRA.t thread_id Ord.t _) Σ}.
  (* Context `{IDENTTGT: @GRA.inG (identTgtRA ident_tgt) Σ}. *)




  Global Program Instance ge_PreOrder: PreOrder ge.
  Next Obligation.
  Proof.
    ii. lia.
  Qed.
  Next Obligation.
  Proof.
    ii. lia.
  Qed.

  Fixpoint waiters now_serving (n: nat) (W: NatMap.t unit): iProp :=
    match n with
    | 0 => True
    | S n' => (∃ i, (monoWhite 1 (@partial_map_PreOrder nat nat) (partial_map_singleton (now_serving + n) i)) ** Pending i ** natmap_prop_sum W (fun k _ => FairRA.white k (Ord.S Ord.O))) ** (waiters now_serving n' W)
    end.

  Let I: iProp :=
        (∃ m,
            (memory_black m)
              **
              (St_tgt (tt, m)))
          **
          (∃ (im: imap thread_id (mk_wf Ord.lt_well_founded)) im_void,
              (FairRA.blacks im)
                **
              (OwnM (Auth.white (Excl.just (imap_sum_id (im, im_void)): @Excl.t _): identSrcRA (id_sum thread_id void) (mk_wf Ord.lt_well_founded))))
          **

          (∃ now_serving n,
              (points_to TicketLock.next_ticket (SCMem.val_nat (now_serving + n)))
                **
                (points_to TicketLock.now_serving (SCMem.val_nat now_serving))
                **
                (monoBlack 0 ge_PreOrder now_serving)
                **
                (∃ f,
                    (monoBlack 1 (@partial_map_PreOrder nat nat) f)
                      **
                      (⌜forall m (LT: now_serving + n < m), f m = None⌝))
                **
                ((⌜n = 0⌝ ** St_src (false, NatMap.empty unit))
                 ∨
                   (∃ n', ⌜n = S n'⌝ ** ∃ W, St_src (false, W) ** waiters now_serving n' W))).

  Definition blacks_success_single (tid: thread_id) (o: Ord.t)
             (f0: imap thread_id (mk_wf Ord.lt_well_founded))
    :
    (FairRA.blacks f0)
      -∗
      (#=>
         (∃ (f1: imap thread_id (mk_wf Ord.lt_well_founded)),
             ((FairRA.blacks f1)
                **
                (FairRA.white tid o)
                **
                ⌜fair_update f0 f1 (fun i => if tid_dec i tid then Flag.success else Flag.emp)⌝))).
  Admitted.

  Definition blacks_fail_single (tid: thread_id)
             (f0: imap thread_id (mk_wf Ord.lt_well_founded))
    :
    (FairRA.blacks f0)
      -∗
      (FairRA.white tid (Ord.S Ord.O))
      -∗
      (#=>
         (∃ (f1: imap thread_id (mk_wf Ord.lt_well_founded)),
             ((FairRA.blacks f1)
                **
                ⌜fair_update f0 f1 (fun i => if tid_dec i tid then Flag.fail else Flag.emp)⌝))).
  Admitted.

  Lemma imap_sum_update_l (A B: ID) (W: WF)
        (im_l0 im_l1: imap A W) (im_r: imap B W) fm
        (UPD: fair_update im_l0 im_l1 fm)
    :
    fair_update
      (imap_sum_id (im_l0, im_r))
      (imap_sum_id (im_l1, im_r))
      (sum_fmap_l fm).
  Proof.
    ii. unfold sum_fmap_l. des_ifs.
    { specialize (UPD a). des_ifs. }
    { specialize (UPD a). des_ifs. }
  Qed.

  Lemma imap_sum_update_r (A B: ID) (W: WF)
        (im_l: imap A W) (im_r0 im_r1: imap B W) fm
        (UPD: fair_update im_r0 im_r1 fm)
    :
    fair_update
      (imap_sum_id (im_l, im_r0))
      (imap_sum_id (im_l, im_r1))
      (sum_fmap_r fm).
  Proof.
    ii. unfold sum_fmap_r. des_ifs.
    { specialize (UPD b). des_ifs. }
    { specialize (UPD b). des_ifs. }
  Qed.

  Lemma fair_white_eq k o0 o1
        (EQ: Ord.eq o0 o1)
    :
    (FairRA.white k o0)
      -∗
      (FairRA.white k o1).
  Proof.
    erewrite FairRA.white_eq; eauto.
  Qed.

  Lemma fair_white_one k o
    :
    (FairRA.white k (Ord.S o))
      -∗
      (FairRA.white k o ** FairRA.white k (Ord.S Ord.O)).
  Proof.
    iIntros "H". iApply FairRA.white_split. ss.
    iApply (fair_white_eq with "H").
    erewrite Hessenberg.add_S_r. rewrite Hessenberg.add_O_r. reflexivity.
  Qed.

  Lemma sim: ModSim.mod_sim TicketLock.mod FairLock.mod.
  Proof.
    refine (@ModSim.mk _ _ (mk_wf Ord.lt_well_founded) nat_wf _ _ Σ _ _ _).
    { econs. exact 0. }
    { i. exists (S o0). ss. }
    { admit. }
    { ii. ss. unfold OMod.closed_funs. ss. des_ifs.
      { cut ((forall tid,
                 (I ** own_thread tid ⊢ fsim I tid itop6 itop6 (fun r_src r_tgt os => I ** own_thread tid ** ⌜r_src = r_tgt /\ os = []⌝) (WMod.interp_fun FairLock.wmod FairLock.lock_fun args) (OMod.close_itree TicketLock.omod (SCMem.mod [1; 1])
                                                                                                                                                                                                                  (Mod.wrap_fun TicketLock.lock_fun args)) []))).
        { admit. }
        i. iIntros "[INV TH]".
        unfold TicketLock.lock_fun, WMod.interp_fun, Mod.wrap_fun. ss.
        destruct (Any.downcast args); ss.
        2:{ unfold UB. lred. iApply fsim_UB. }
        lred. rred. rewrite close_itree_call. ss. rred.
        iApply fsim_sync. instantiate (1:=None). ss. iFrame. iIntros "INV _".
        rred. lred. iApply fsim_tidL. lred.
        iDestruct "INV" as "[[[%m [MEM TGT]] IM] [% [% [[[[NEXT NOW] MONO] MAP] WAIT]]]]".
        unfold Mod.wrap_fun, SCMem.faa_fun.
        rred. iApply fsim_getR. iSplit.
        { iFrame. }
        rred. iApply fsim_tauR.
        iPoseProof (memory_ra_faa with "MEM NEXT") as "[% [% > [MEM NEXT]]]".
        rred. rewrite H.
        rred. iApply fsim_getR. iSplit.
        { iFrame. }
        rred. iApply (fsim_putR with "TGT"). iIntros "TGT".
        rred. iApply fsim_tauR.
        rred. iApply fsim_tauR.
        iPoseProof "IM" as "[% [% [BLACK IM]]]".
        rred. iDestruct "WAIT" as "[[% SRC]|H]".
        { subst. iApply fsim_getL. iSplit.
          { iFrame. }
          lred. iApply (fsim_putL with "SRC"). iIntros "SRC".
          iPoseProof ((@blacks_success_single tid (Ord.S (Ord.S Ord.O))) with "BLACK") as "> [% [[BLACK FUEL] %]]".
          lred. iApply (fsim_fairL with "IM"). iExists _. iSplit.
          { iPureIntro. eapply imap_sum_update_l; eauto. }
          iIntros "IM".
          iPoseProof (fair_white_one with "FUEL") as "[FUEL ONE]".
          iApply fsim_alloc_obligation.
          { instantiate (1:=Ord.S (Ord.S (Ord.O))).
            iIntros "% PENDING NEG # POS".
            iPoseProof "MAP" as "[% [MAP %]]".
            iPoseProof (black_updatable with "MAP") as "> MAP".
            { instantiate (1:=(fun m => if (Nat.eq_dec m (now_serving + 1)) then Some k else f m)).
              ii. des_ifs. exfalso. rewrite H1 in SOME; ss. lia.
            }


tid_dec

            iAssert (#=> (I ** monoBlack 1 (partial_map_PreOrder nat nat) (partial_map_singleton (now_serving + 1))) with "[NOW MONO MAP MEM NEXT TGT SRC BLACK IM FUEL ONE]" as "INV".
            { unfold I. iSplitL "MEM TGT BLACK IM".
              { iModIntro. iSplitL "MEM TGT".
                { iExists _. iFrame. }
                { iExists _, _. iFrame. }
              }
              iExists now_serving, 1. iFrame. iSplitL "NEXT MAP".
              { monoBlack 1 (partial_map_PreOrder nat nat) (partial_map_singleton (now_serving + 1) )

ss.

, _. iFrame.


 red.

          rewrite unfold_iter_eq. lred. iApply fsim_chooseL. iExists true.
          lred.

(inl ).

          rewrite ITree.iter

          iPoseProof ((@blacks_success_single tid (Ord.S (Ord.S Ord.O))) with "IMBLACK") as "> [% [[IMBLACK FUEL] %]]".
          lred. iApply (fsim_fairL with "IM"). iExists _. iSplit.
          { iPureIntro. eapply imap_sum_update_l; eauto. }
          iIntros "IM".



blacks_fail_single
          lred.

          {


          ss.
          { ss. unfold OMod.closed_ident. ss. eapply IDENTTGT.
unfold

s

          iPoseProof (memory_ra_faa with "MEM NEXT") as "[% [% > [MEM NEXT]]]".




iApply fsim_tauR.

iApply (fsim_putR with "ST"). iIntros "ST".

iSplit.
        { iFrame. }


ss. des; clarify.


        rred. iApply fsim_getR. iSplit.
        { iFrame. }
        rred. iApply fsim_tauR.
        iPoseProof (memory_ra_load with "MEM NEXT") as "%". ss. des; clarify.
        rred. ss. rewrite H.

                iPoseProof (memory_ra_load
        rred.

[% [% [% [% H]]]]]".

        iDestruct "INV" as "[[[%m [MEM ST]] IM] [% [% [% [% H]]]]]".


  Let I: iProp :=
        (∃ m,
            (memory_black m)
              **
              (St_tgt (tt, m)))
          **
          (∃ im0 im1,
              (OwnM (Auth.white (Excl.just (imap_sum_id (im0, im1)): @Excl.t _): identSrcRA (id_sum thread_id void) (mk_wf Ord.lt_well_founded)))
                **
                True
          )
          **
          (∃ now_serving n f i,
              (points_to TicketLock.next_ticket (SCMem.val_nat (now_serving + n)))
                **
                (monoBlack 0 ge_PreOrder now_serving)
                **
                (monoBlack 1 (@partial_map_PreOrder nat nat) f)
                **
                (⌜forall m (LT: now_serving + n < m), f m = None⌝)
                **
                (monoWhite 1 (@partial_map_PreOrder nat nat) (partial_map_singleton now_serving i))
                **
                (Eventually i (points_to TicketLock.now_serving (SCMem.val_nat now_serving)))
                **
                (waiters now_serving n))
  .

        iApply fsim_getR. iSplit.
        { iFrame. }
        rred. iApply fsim_tauR. rred.

        unfold SCMem.cas.
        destruct w; ss.
        { iDestruct "H" as "[[POINTL POINTF] EXCL]".
          iPoseProof (memory_ra_load with "MEM POINTL") as "%". ss. des; clarify.
          rewrite H. ss.
          iPoseProof (memory_ra_store with "MEM POINTL") as "[% [% > [MEM POINTL]]]".
          rewrite H1. ss.
          rred. iApply fsim_getR. iSplit.
          { iFrame. }
          rred. iApply (fsim_putR with "ST"). iIntros "ST".
          rred. iApply fsim_tauR.
          rred. iApply fsim_tauR.

          iApply (@fsim_alloc_obligation _ _ _ _ _ _ _ (Ord.large × 10)%ord). iIntros "% ONG NEG # POS".
          iDestruct (monoBlack_alloc le_PreOrder 0) as "-# > [% ORD]".
          iPoseProof (black_updatable with "MONO") as "> MONO".
          { instantiate (1:=W_own k k0). econs. }
          iPoseProof (black_persistent_white with "MONO") as "# MWHITE".
          iPoseProof (Neg_split with "NEG") as "> [FUEL NEG]". { eapply ord_mult_split. }
          rred. iApply (@fsim_yieldR _ _ _ _ _ _ _ None). iSplitR "EXCL NEG".
          { ss. iFrame. iSplit; auto. iSplitL "MEM ST".
            { iExists _. iFrame. }
            iExists _. iFrame. iSplit.
            { iExists _. iFrame. auto. }
            { iClear "POINTF ORD". iModIntro. iExists _. eauto. }
          }
          iIntros "INV _".
          iPoseProof (Neg_split with "NEG") as "> [FUEL NEG]". { eapply ord_mult_split. }
          rred. iApply fsim_tauR.
          rred. iApply (@fsim_yieldR _ _ _ _ _ _ _ None). ss. iFrame.
          iIntros "INV _".
          iPoseProof (Neg_split with "NEG") as "> [FUEL NEG]". { eapply ord_mult_split. }

        rred. iApply fsim_tauR.
        rred. rewrite close_itree_call. ss.
        rred. iApply (@fsim_yieldR _ _ _ _ _ _ _ None). ss. iFrame.
        iIntros "INV _".
        iPoseProof (Neg_split with "NEG") as "> [FUEL NEG]". { eapply ord_mult_split. }

        unfold SCMem.store_fun, Mod.wrap_fun.
        iDestruct "INV" as "[[% [MEM ST]] [% [MONO H]]]".
        rred. iApply fsim_getR. iSplit.
        { iFrame. }
        rred. iApply fsim_tauR. rred.

        iPoseProof (black_white_compare with "MWHITE MONO") as "%". inv H2.
        ss. iDestruct "H" as "[[POINTL [% [[POINTF ORD] %]]] EVT]".

        iPoseProof (memory_ra_store with "MEM POINTF") as "[% [% > [MEM POINTF]]]".
        rewrite H3. ss.
        rred. iApply fsim_getR. iSplit.
        { iFrame. }
        rred. iApply (fsim_putR with "ST"). iIntros "ST".
        rred. iApply fsim_tauR.
        rred. iApply fsim_tauR.
        iPoseProof (eventually_finish with "EVT") as "[# DONE | [ONG EVT]]".
        { iApply (fsim_obligation_not_done with "DONE"). ss. auto. }
        iPoseProof (black_updatable with "ORD") as "> ORD".
        { instantiate (1:=1). lia. }
        iPoseProof (black_persistent_white with "ORD") as "#WHITE".
        iApply (fsim_dealloc_obligation with "ONG").
        { ss. }
        iIntros "# DONE". iPoseProof ("EVT" with "DONE WHITE") as "EVT".

        rred. iApply (@fsim_sync _ _ _ _ _ _ _ None). iSplitR "".
        { ss. unfold I. iSplit; auto. iSplit; auto. iSplitL "MEM ST".
          { iExists _. iFrame. }
          iExists _. iFrame. ss. iFrame.
          iExists _. iFrame. auto.
        }
        iIntros "INV _". iApply fsim_tauR. iApply fsim_ret. auto.
      }

      { iDestruct "H" as "[[POINTL POINTF] EXCL]".
        iPoseProof (memory_ra_load with "MEM POINTL") as "%". des; clarify.
        iPoseProof (eventually_obligation with "EXCL") as "# [% OBL]".
        rewrite H. ss.
        rred. iApply fsim_tauR.
        rred.
        iPoseProof (black_persistent_white with "MONO") as "# WHITE".
        iAssert I with "[MEM ST MONO POINTL POINTF EXCL]" as "INV".
        { unfold I. iSplitL "MEM ST".
          { iExists _. iFrame. }
          iExists (W_own _ _). ss. iFrame.
        }
        iStopProof.
        pattern n. revert n. eapply (well_founded_induction Ord.lt_well_founded). intros o IH.
        iIntros "[# [OBL WHITE] INV]".
        rewrite unfold_iter_eq. rred.
        iApply (@fsim_yieldR _ _ _ _ _ _ _ (Some k)).
        ss. iFrame. iSplitL.
        { iExists _. eauto. }
        iIntros "INV FUEL".
        rred. iApply fsim_tauR.
        rred. rewrite close_itree_call. ss.
        unfold SCMem.load_fun, Mod.wrap_fun. ss.
        rred. iApply (@fsim_yieldR _ _ _ _ _ _ _ None). ss. iFrame. iIntros "INV _".
        iDestruct "INV" as "[[% [MEM ST]] [% [MONO H]]]".
        rred. iApply fsim_getR. iSplit. { iFrame. }
        rred. iApply fsim_tauR. rred.
        iPoseProof (black_white_compare with "WHITE MONO") as "%". inv H1.
        ss. iDestruct "H" as "[[POINTL [% [[POINTF PWHITE] %]]] EVT]".
        iPoseProof (memory_ra_load with "MEM POINTF") as "%".
        destruct H2 as [LOAD _]. rewrite LOAD.
        rred. iApply fsim_tauR.
        rred. des; subst; cycle 1.
        { iApply (@fsim_yieldR _ _ _ _ _ _ _ None). ss. iSplitL.
          { iSplit; auto. iSplit; auto. unfold I. iSplitL "MEM ST".
            { iExists _. iFrame. }
            iExists (W_own _ _). ss. iFrame. iExists _. iFrame. auto.
          }
          iIntros "INV _".
          rred. iApply fsim_tauR.
          rred. rewrite close_itree_call. ss.
          unfold SCMem.compare_fun, Mod.wrap_fun.
          rred. iApply (@fsim_yieldR _ _ _ _ _ _ _ None). ss. iFrame. iIntros "INV _".
          iDestruct "INV" as "[[% [MEM ST]] [% [MONO H]]]".
          rred. iApply fsim_getR. iSplit; [eauto|].
          rred. iApply fsim_tauR.
          rred. iApply fsim_tauR.
          rred. iApply (@fsim_sync _ _ _ _ _ _ _ None). ss. iSplitL.
          { iSplit; auto. iSplit; auto. unfold I. iSplitL "MEM ST".
            { iExists _. iFrame. }
            { iExists _. iFrame. }
          }
          iIntros "INV _". rred. iApply fsim_tauR.
          rred. iApply fsim_ret. auto.
        }
        { iDestruct "FUEL" as "[FUEL|#DONE]"; cycle 1.
          { iDestruct (eventually_done with "DONE EVT") as "[H EVT]".
            iPoseProof (black_white_compare with "H PWHITE") as "%". exfalso. lia.
          }
          rred. iApply (@fsim_yieldR _ _ _ _ _ _ _ None). ss. iSplitR "FUEL".
          { iSplit; auto. iSplit; auto. unfold I. iSplitL "MEM ST".
            { iExists _. iFrame. }
            { iExists _. iFrame. unfold I_aux. iFrame. iExists _. iFrame. auto. }
          }
          iIntros "INV _".
          rred. iApply fsim_tauR.
          rred. rewrite close_itree_call. ss.
          unfold SCMem.compare_fun, Mod.wrap_fun. ss.
          rred. iApply (@fsim_yieldR _ _ _ _ _ _ _ None). ss. iFrame. iIntros "INV _".
          rred. iDestruct "INV" as "[[% [MEM ST]] [% [MONO H]]]".
          iApply fsim_getR. iSplit. { iFrame. }
          rred. iApply fsim_tauR.
          rred. iApply fsim_tauR.
          rred. iApply (@fsim_yieldR _ _ _ _ _ _ _ None). ss. iSplitR "FUEL".
          { iSplit; auto. iSplit; auto. unfold I. iSplitL "MEM ST".
            { iExists _. iFrame. }
            { iExists _. iFrame. }
          }
          iIntros "INV _".
          rred. iApply fsim_tauR.
          rred. iApply fsim_tauR.
          iPoseProof (Pos_Neg_annihilate with "OBL FUEL") as "> [% [H %]]".
          iClear "OBL". iPoseProof (Pos_persistent with "H") as "# OBL".
          iApply IH; eauto. iSplit; auto. iClear "INV H". auto.
        }
      }
    }
  Admitted.
End SIM.
