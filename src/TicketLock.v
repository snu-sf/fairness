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
  Context `{EXCL: @GRA.inG (Excl.t unit) Σ}.
  Context `{MONORA: @GRA.inG monoRA Σ}.
  Context `{THSRA: @GRA.inG ths_RA Σ}.
  (* Context `{STATESRC: @GRA.inG (stateSrcRA unit) Σ}. *)
  Context `{STATETGT: @GRA.inG (stateTgtRA (unit * SCMem.t)) Σ}.
  Context `{IDENTSRC: @GRA.inG (identSrcRA (id_sum thread_id void) (mk_wf Ord.lt_well_founded)) Σ}.
  (* Context `{IDENTTGT: @GRA.inG (identTgtRA (void + SCMem.pointer)%type) Σ}. *)
  (* Context `{IDENTTHS: @GRA.inG identThsRA Σ}. *)
  Context `{MEMRA: @GRA.inG memRA Σ}.

  Global Program Instance ge_PreOrder: PreOrder ge.
  Next Obligation.
  Proof.
    ii. lia.
  Qed.
  Next Obligation.
  Proof.
    ii. lia.
  Qed.


  Definition partial_map_le A B (f0 f1: A -> option B): Prop :=
    forall a b (SOME: f0 a = Some b), f1 a = Some b.

  Global Program Instance partial_map_PreOrder A B: PreOrder (@partial_map_le A B).
  Next Obligation.
  Proof.
    ii. auto.
  Qed.
  Next Obligation.
  Proof.
    ii. eapply H0. eapply H. auto.
  Qed.

  Definition partial_map_empty A B: A -> option B :=
    fun _ => None.

  Definition partial_map_update A B (a: A) (b: B) (f: A -> option B):
    A -> option B :=
    fun a' => if (excluded_middle_informative (a' = a)) then Some b else (f a').

  Definition partial_map_singleton A B (a: A) (b: B): A -> option B :=
    partial_map_update a b (@partial_map_empty A B).

  Definition partial_map_update_le A B (a: A) (b: B) (f: A -> option B)
             (NONE: f a = None)
    :
    partial_map_le f (partial_map_update a b f).
  Proof.
    ii. unfold partial_map_update. des_ifs.
  Qed.

  Definition partial_map_update_le_singleton A B (a: A) (b: B) (f: A -> option B)
             (NONE: f a = None)
    :
    partial_map_le (partial_map_singleton a b) (partial_map_update a b f).
  Proof.
    ii. unfold partial_map_singleton, partial_map_update in *. des_ifs.
  Qed.

  Lemma partial_map_singleton_le_iff A B (a: A) (b: B) f
    :
    partial_map_le (partial_map_singleton a b) f <-> (f a = Some b).
  Proof.
    split.
    { i. eapply H. unfold partial_map_singleton, partial_map_update. des_ifs. }
    { ii. unfold partial_map_singleton, partial_map_update in *. des_ifs. }
  Qed.

  Fixpoint waiters now_serving (n: nat): iProp :=
    match n with
    | 0 => True
    | S n => (∃ i, (monoWhite 1 (@partial_map_PreOrder nat nat) (partial_map_singleton (now_serving + n) i)) ** Pending i) ** (waiters now_serving n)
    end.

  Let I: iProp :=
        (∃ m,
            (memory_black m)
              **
              (St_tgt (tt, m)))
          **
          (∃ im0 im1 (W: NatMap.t unit) (b: bool),
              (OwnM (Auth.white (Excl.just (imap_sum_id (im0, im1)): @Excl.t _): identSrcRA (id_sum thread_id void) (mk_wf Ord.lt_well_founded)))
                **
                (St_src void (W, b)))
          **
          (∃ now_serving n,
              (points_to TicketLock.next_ticket (SCMem.val_nat (now_serving + n)))
                **
                (points_to TicketLock.now_serving (SCMem.val_nat now_serving))
                **
                (monoBlack 0 ge_PreOrder now_serving)
                **
                (waiters now_serving n)
                **
                (∃ f,
                    (monoBlack 1 (@partial_map_PreOrder nat nat) f)
                      **
                      (⌜forall m (LT: now_serving + n < m), f m = None⌝))
                **
                (∃ i,
                    (monoWhite 1 (@partial_map_PreOrder nat nat) (partial_map_singleton now_serving i))
                      **
                      (Eventually i (points_to TicketLock.now_serving (SCMem.val_nat now_serving))))
)
  .



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
        iApply (@fsim_sync _ _ _ _ _ _ _ None). ss. iFrame. iIntros "INV _".
        rred. unfold SCMem.cas_fun, Mod.wrap_fun. rred.
        lred. iApply fsim_tidL. lred.
        iDestruct "INV" as "[[[%m [MEM ST]] SRC] [% [% [% [% [NEXT TK]]]]]]".
        rred. iApply fsim_getR. iSplit.
        { iFrame. }
        rred. iApply fsim_tauR.
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
