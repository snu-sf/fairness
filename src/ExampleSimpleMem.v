From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Export ITreeLib WFLib FairBeh NatStructs Mod pind OpenMod SCM Red IRed.
From Ordinal Require Export ClassicalHessenberg.

Set Implicit Arguments.


Section MOD.
  Definition loc_l: SCMem.val := SCMem.val_ptr (0, 0).
  Definition loc_f: SCMem.val := SCMem.val_ptr (1, 0).

  Definition example_fun:
    ktree ((((@eventE void) +' cE) +' (sE unit)) +' OpenMod.callE) unit unit :=
    fun _ =>
      b <- OMod.call "cas" (loc_l, SCMem.val_nat 0, SCMem.val_nat 1);;
      if (b: bool) then
        _ <- trigger Yield;;
        _ <- trigger Yield;;
        `_: unit <- OMod.call "store" (loc_f, SCMem.val_nat 1);;
        trigger Yield
      else
        ITree.iter
          (fun _ =>
             _ <- trigger Yield;;
             f <- OMod.call "load" loc_f;;
             _ <- trigger Yield;;
             b <- OMod.call "compare" (f: SCMem.val, SCMem.val_nat 1);;
             _ <- trigger Yield;;
             if (b: bool) then Ret (inr tt) else Ret (inl tt)) tt
  .

  Definition example_omod: OMod.t :=
    OMod.mk
      tt
      (Mod.get_funs [("example", Mod.wrap_fun example_fun)])
  .

  Definition example_mod: Mod.t :=
    OMod.close
      (example_omod)
      (SCMem.mod [1; 1])
  .

  Definition example_spec_fun:
    ktree ((((@eventE void) +' cE) +' (sE unit))) unit unit :=
    fun _ =>
      trigger Yield
  .

  Definition example_spec_mod: Mod.t :=
    Mod.mk
      tt
      (Mod.get_funs [("example", Mod.wrap_fun example_spec_fun)])
  .
End MOD.

From Fairness Require Import IProp IPM Weakest.
From Fairness Require Import ModSim PCM MonotonePCM ThreadsRA StateRA.

Section SIM.
  Context `{Σ: GRA.t}.
  Context `{EXCL: @GRA.inG (Excl.t unit) Σ}.
  Context `{MONORA: @GRA.inG monoRA Σ}.
  Context `{THSRA: @GRA.inG ths_RA Σ}.
  Context `{STATESRC: @GRA.inG (stateSrcRA unit) Σ}.
  Context `{STATETGT: @GRA.inG (stateTgtRA (unit * SCMem.t)) Σ}.
  Context `{IDENTSRC: @GRA.inG (identSrcRA void nat_wf) Σ}.
  Context `{IDENTTGT: @GRA.inG (identTgtRA (void + SCMem.pointer)%type) Σ}.
  Context `{IDENTTHS: @GRA.inG identThsRA Σ}.
  Context `{MEMRA: @GRA.inG memRA Σ}.

  Variant W: Type :=
    | W_bot
    | W_own (k: nat) (x: nat)
  .

  Variant W_le: W -> W -> Prop :=
    | W_le_bot
        w
      :
      W_le W_bot w
    | W_le_th
        k x
      :
      W_le (W_own k x) (W_own k x)
  .

  Global Program Instance le_PreOrder: PreOrder Nat.le.

  Program Instance W_le_PreOrder: PreOrder W_le.
  Next Obligation.
  Proof.
    ii. destruct x; econs.
  Qed.
  Next Obligation.
  Proof.
    ii. inv H; inv H0; try econs; eauto.
  Qed.

  Let I_aux (w: W): iProp :=
        (match w with
         | W_bot => points_to loc_l (SCMem.val_nat 0) ** points_to loc_f (SCMem.val_nat 0) ** (OwnM (Excl.just tt: @URA.car (Excl.t unit)))
         | W_own k x =>
             (points_to loc_l (SCMem.val_nat 1))
               **
               (∃ n, points_to loc_f (SCMem.val_nat n) ** monoBlack x le_PreOrder n ** ⌜n = 0 \/ n = 1⌝)
               **
               Eventually k (monoWhite x le_PreOrder 1)
         end)
  .

  Let I: iProp :=
        (∃ m,
            (memory_black m)
              **
              (St_tgt (tt, m)))
          **
          (∃ w,
              (monoBlack 0 W_le_PreOrder w)
                **
                I_aux w).

  (* Lemma I_aux_fair_update w *)
  (*       im_src im_tgt0 im_tgt1 tid ths st_src st_tgt *)
  (*       (UPD: fair_update im_tgt0 im_tgt1 (sum_fmap_l (tids_fmap tid ths))) *)
  (*   : *)
  (*   (own_thread tid) *)
  (*     -∗ *)
  (*     (I_aux w im_src im_tgt0 st_src st_tgt) *)
  (*     -∗ *)
  (*     (own_thread tid ∗ I_aux w im_src im_tgt1 st_src st_tgt). *)
  (* Proof. *)
  (*   iIntros "OWN INV". destruct w; try by iFrame. *)
  (*   unfold I_aux. des_ifs. iDestruct "INV" as "[[% INV] ORD]". *)
  (*   iPoseProof (thread_disjoint with "OWN INV") as "%". *)
  (*   des. subst. iFrame. iPureIntro. split; auto. *)
  (*   specialize (UPD (inl th)). unfold sum_fmap_l, tids_fmap in UPD. *)
  (*   des_ifs; ss; lia. *)
  (* Qed. *)

  (* Lemma I_fair_update *)
  (*       im_src im_tgt0 im_tgt1 tid ths st_src st_tgt *)
  (*       (UPD: fair_update im_tgt0 im_tgt1 (sum_fmap_l (tids_fmap tid ths))) *)
  (*   : *)
  (*   (own_thread tid) *)
  (*     -∗ *)
  (*     (I ths im_src im_tgt0 st_src st_tgt) *)
  (*     -∗ *)
  (*     (own_thread tid ∗ I ths im_src im_tgt1 st_src st_tgt). *)
  (* Proof. *)
  (*   unfold I. *)
  (*   iIntros "OWN [THS INV]". iDestruct "INV" as (w) "[MONO INV]". *)
  (*   iPoseProof (I_aux_fair_update with "OWN INV") as "[OWN INV]". *)
  (*   { eauto. } *)
  (*   iFrame. iExists _. iFrame. *)
  (* Qed. *)

  (* Lemma I_own_fair_update *)
  (*       im_src im_tgt0 im_tgt1 tid ths st_src st_tgt *)
  (*       (UPD: fair_update im_tgt0 im_tgt1 (sum_fmap_l (tids_fmap tid ths))) *)
  (*       th k o0 i0 *)
  (*   : *)
  (*   monoWhite 0 W_le_PreOrder (W_own th k o0 i0) *)
  (*             -∗ *)
  (*             (own_thread tid) *)
  (*             -∗ *)
  (*             (I ths im_src im_tgt0 st_src st_tgt) *)
  (*             -∗ *)
  (*             #=> (∃ o1 i1, monoWhite 0 W_le_PreOrder (W_own th k o1 i1) ∗ ⌜prod_lt Peano.lt Peano.lt (o1, i1) (o0, i0)⌝ ∗ own_thread tid ∗ I ths im_src im_tgt1 st_src st_tgt). *)
  (* Proof. *)
  (*   unfold I. *)
  (*   iIntros "WHITE OWN [THS INV]". iDestruct "INV" as (w) "[MONO INV]". *)
  (*   iPoseProof (black_white_compare with "WHITE MONO") as "%". inv H; ss. *)
  (*   { guardH LE. destruct st_tgt. ss. *)
  (*     iDestruct "INV" as "[[% INV] ORD]". des. subst. *)
  (*     iPoseProof (thread_disjoint with "OWN INV") as "%". *)
  (*     iPoseProof (threads_in with "THS OWN") as "%". *)
  (*     admit. *)
  (*   } *)
  (* Admitted. *)

  (* Lemma locked_after_own *)
  (*       ths im_src im_tgt st_src st_tgt *)
  (*       tid k o i *)
  (*   : *)
  (*   monoWhite 0 W_le_PreOrder (W_own tid k o i) *)
  (*             -∗ *)
  (*             I ths im_src im_tgt st_src st_tgt *)
  (*             -∗ *)
  (*             ⌜fst st_tgt = true⌝. *)
  (* Proof. *)
  (*   destruct st_tgt. iIntros "WHITE INV". *)
  (*   iEval (unfold I) in "INV". iDestruct "INV" as "[THS INV]". *)
  (*   iDestruct "INV" as (w) "[MONO INV]". *)
  (*   iPoseProof (black_white_compare with "WHITE MONO") as "%". inv H; ss. *)
  (*   { iDestruct "INV" as "[[% ?] ?]". des; auto. } *)
  (*   { iDestruct "INV" as "[[% ?] ?]". des; auto. } *)
  (* Qed. *)

  (* Lemma locked_after_top *)
  (*       ths im_src im_tgt st_src st_tgt *)
  (*   : *)
  (*   monoWhite 0 W_le_PreOrder W_top *)
  (*             -∗ *)
  (*             I ths im_src im_tgt st_src st_tgt *)
  (*             -∗ *)
  (*             ⌜fst st_tgt = true /\ snd st_tgt = true⌝. *)
  (* Proof. *)
  (*   destruct st_tgt. iIntros "WHITE INV". *)
  (*   iEval (unfold I) in "INV". iDestruct "INV" as "[THS INV]". *)
  (*   iDestruct "INV" as (w) "[MONO INV]". *)
  (*   iPoseProof (black_white_compare with "WHITE MONO") as "%". inv H; ss. *)
  (*   iDestruct "INV" as "[% _]". auto. *)
  (* Qed. *)

  (* Lemma I_stutter *)
  (*       tid i ths *)
  (*       im_src im_tgt0 im_tgt1 st_src st_tgt *)
  (*       n n0 n1 k *)
  (*       (LT: n1 < n0) *)
  (*   : *)
  (*   monoWhite 0 W_le_PreOrder (W_own tid k n i) *)
  (*             -∗ *)
  (*             (OwnM (Excl.just tt: @URA.car (Excl.t unit))) *)
  (*             -∗ *)
  (*             I ths im_src im_tgt0 st_src st_tgt *)
  (*             -∗ *)
  (*             monoBlack k ge_PreOrder n0 *)
  (*             -∗ *)
  (*             #=> *)
  (*             (OwnM (Excl.just tt: @URA.car (Excl.t unit)) *)
  (*                   ** *)
  (*                   I ths im_src im_tgt1 st_src st_tgt *)
  (*                   ** *)
  (*                   monoBlack k ge_PreOrder n1). *)
  (* Proof. *)
  (*   iIntros "WHITE OWN [THS [%w [MONO INV]]] ORD". *)
  (*   iPoseProof (black_white_compare with "WHITE MONO") as "%". *)
  (*   unfold I_aux. inv H; des_ifs. *)
  (*   { iDestruct "INV" as "[[% TID] WHITE0]". *)
  (*     iPoseProof (black_white_compare with "WHITE0 ORD") as "%". *)
  (*     iPoseProof (black_updatable with "ORD") as "> ORD". *)
  (*     { instantiate (1:=n1). lia. } *)
  (*     iPoseProof (black_persistent_white with "ORD") as "# ORDWHITE". *)
  (*     iPoseProof (black_updatable with "MONO") as "> MONO". *)
  (*     { instantiate (1:=(W_own tid k n1 (im_tgt1 (inl tid)))). *)
  (*       econs; eauto. left. lia. *)
  (*     } *)
  (*     iModIntro. unfold I. iFrame. iExists _. iFrame. iSplit; auto. *)
  (*     iPureIntro. des; split; auto. *)
  (*   } *)
  (*   { iDestruct "INV" as "[% INV]". *)
  (*       iCombine "OWN INV" as "OWN". iOwnWf "OWN". ur in H0. ss. *)
  (*   } *)
  (* Qed. *)

  (* Lemma I_finish *)
  (*       tid k n i *)
  (*       ths im_src0 im_tgt0 st_src0 st_tgt0 *)
  (*       im_src1 im_tgt1 st_src1 *)
  (*   : *)
  (*   (monoWhite 0 W_le_PreOrder (W_own tid k n i)) *)
  (*     -∗ *)
  (*     OwnM (Excl.just tt: @URA.car (Excl.t unit)) *)
  (*     -∗ *)
  (*     I ths im_src0 im_tgt0 st_src0 st_tgt0 *)
  (*     -∗ *)
  (*     #=> *)
  (*     (I ths im_src1 im_tgt1 st_src1 (true, true) *)
  (*        ** *)
  (*        own_thread tid *)
  (*        ** *)
  (*        monoWhite 0 W_le_PreOrder W_top). *)
  (* Proof. *)
  (*   iIntros "WHITE OWN [THS [%w [MONO INV]]]". *)
  (*   iPoseProof (black_white_compare with "WHITE MONO") as "%". *)
  (*   destruct st_tgt0. inv H; ss. *)
  (*   { iClear "WHITE". iDestruct "INV" as "[[% TID] _]". *)
  (*     iPoseProof (black_updatable with "MONO") as "> MONO". *)
  (*     { instantiate (1:=W_top). econs. } *)
  (*     iPoseProof (black_persistent_white with "MONO") as "#WHITE". *)
  (*     iModIntro. iSplitL; auto. unfold I. iFrame. *)
  (*     iExists W_top. ss. iFrame. auto. *)
  (*   } *)
  (*   { iDestruct "INV" as "[% INV]". *)
  (*     iCombine "OWN INV" as "OWN". iOwnWf "OWN". ur in H0. ss. *)
  (*   } *)
  (* Qed. *)

  (* Let srcE := ((@eventE void +' cE) +' sE unit). *)
  (* Let tgtE := ((@eventE void +' cE) +' sE (bool * bool)). *)

  Definition itop5 { T0 T1 T2 T3 T4 } (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) (x4: T4 x0 x1 x2 x3): iProp := True%I.

  Definition itop6 { T0 T1 T2 T3 T4 T5 } (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) (x4: T4 x0 x1 x2 x3) (x5: T5 x0 x1 x2 x3 x4): iProp := True%I.

  Definition itop10 { T0 T1 T2 T3 T4 T5 T6 T7 T8 T9} (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) (x4: T4 x0 x1 x2 x3) (x5: T5 x0 x1 x2 x3 x4) (x6: T6 x0 x1 x2 x3 x4 x5) (x7: T7 x0 x1 x2 x3 x4 x5 x6) (x8: T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: T9 x0 x1 x2 x3 x4 x5 x6 x7 x8): iProp := True%I.

  (* Definition isim_gen tid r g R_src R_tgt Q (itr_src: itree srcE R_src) (itr_tgt: itree tgtE R_tgt): iProp := *)
  (*   ∀ ths im_src im_tgt0 st_src st_tgt im_tgt1, *)
  (*     I ths im_src im_tgt0 st_src st_tgt *)
  (*       -* *)
  (*       ⌜fair_update im_tgt0 im_tgt1 (sum_fmap_l (tids_fmap tid ths))⌝ *)
  (*       -* *)

  (* Ltac _red_close_itree f := *)
  (*   match goal with *)
  (*   | [ |- ITree.bind (OMod.close_itree _ _ ?itr) _ = _ ] => *)
  (*       match itr with *)
  (*       | ITree.bind _ _ => *)
  (*           instantiate (f:=_continue); eapply interp_tgt_bind; fail *)
  (*       | Tau _ => *)
  (*           instantiate (f:=_break); apply interp_tgt_tau; fail *)
  (*       | Ret _ => *)
  (*           instantiate (f:=_continue); apply interp_tgt_ret; fail *)
  (*       | trigger ?e => *)
  (*           instantiate (f:=_break); *)
  (*           match (type of e) with *)
  (*           | context[hCallE] => apply interp_tgt_hcall *)
  (*           | context[eventE] => apply interp_tgt_triggere *)
  (*           | context[pE] => apply interp_tgt_triggerp *)
  (*           | _ => fail 2 *)
  (*           end *)
  (*       | triggerUB => *)
  (*           instantiate (f:=_break); apply interp_tgt_triggerUB; fail *)
  (*       | triggerNB => *)
  (*           instantiate (f:=_break); apply interp_tgt_triggerNB; fail *)
  (*       | unwrapU _ => *)
  (*           instantiate (f:=_break); apply interp_tgt_unwrapU; fail *)
  (*       | unwrapN _ => *)
  (*           instantiate (f:=_break); apply interp_tgt_unwrapN; fail *)
  (*       | assume _ => *)
  (*           instantiate (f:=_break); apply interp_tgt_assume; fail *)
  (*       | guarantee _ => *)
  (*           instantiate (f:=_break); apply interp_tgt_guarantee; fail *)
  (*       | _ => *)
  (*           fail *)
  (*       end *)
  (*   | [ |- interp_hCallE_tgt _ _ _ _ = _] => *)
  (*       instantiate (f:=_continue); apply bind_ret_r_rev; fail *)
  (*   | _ => fail *)
  (*   end. *)

  (* Ltac _red_lsim f := *)
  (*   _red_interp_tgt f || _red_itree f || fail. *)

  (* Ltac ired_l := try (prw _red_lsim 2 1 0). *)
  (* Ltac ired_r := try (prw _red_lsim 1 1 0). *)

  (* Ltac ired_both := ired_l; ired_r. *)

  (*       isim tid I r g Q itr_src itr_tgt ths im_src im_tgt1 st_src st_tgt. *)

  Lemma ord_mult_split (n: nat)
    :
    ((Ord.omega ⊕ Ord.large × n ) <= (Ord.large × (S n)))%ord.
  Proof.
    rewrite Ord.from_nat_S.
    rewrite Jacobsthal.mult_S.
    apply Hessenberg.le_add_l.
    apply Ord.lt_le.
    rewrite Ord.omega_from_peano_lt_set.
    apply Ord.large_lt_from_wf_set.
  Qed.

  Section AUX.
    Lemma embed_itree_ext
          omd md R (itr0 itr1: itree _ R)
      :
      itr0 = itr1 -> OMod.embed_itree omd md itr0 = OMod.embed_itree omd md itr1
    .
    Proof. i; subst; reflexivity. Qed.

    Lemma close_itree_ext
          omd md R (itr0 itr1: itree _ R)
      :
      itr0 = itr1 -> OMod.close_itree omd md itr0 = OMod.close_itree omd md itr1
    .
    Proof. i; subst; reflexivity. Qed.

    Global Program Instance embed_itree_rdb: red_database (mk_box (@OMod.embed_itree)) :=
      mk_rdb
        0
        (mk_box embed_itree_bind)
        (mk_box embed_itree_tau)
        (mk_box embed_itree_ret)
        (mk_box embed_itree_trigger_eventE2)
        (mk_box embed_itree_trigger_cE2)
        (mk_box embed_itree_trigger_put2)
        (mk_box embed_itree_trigger_get2)
        (mk_box embed_itree_UB)
        (mk_box embed_itree_UB)
        (mk_box embed_itree_unwrap)
        (mk_box embed_itree_UB)
        (mk_box embed_itree_UB)
        (mk_box embed_itree_UB)
        (mk_box embed_itree_ext)
    .

    Global Program Instance close_itree_rdb: red_database (mk_box (@OMod.close_itree)) :=
      mk_rdb
        0
        (mk_box close_itree_bind)
        (mk_box close_itree_tau)
        (mk_box close_itree_ret)
        (mk_box close_itree_trigger_eventE2)
        (mk_box close_itree_trigger_cE2)
        (mk_box close_itree_trigger_put2)
        (mk_box close_itree_trigger_get2)
        (mk_box close_itree_UB)
        (mk_box close_itree_UB)
        (mk_box close_itree_unwrap)
        (mk_box close_itree_UB)
        (mk_box close_itree_UB)
        (mk_box close_itree_UB)
        (mk_box close_itree_ext)
    .
(* close_itree_trigger_call2 *)
(* close_itree_call *)
(* close_itree_callR *)
  End AUX.
  Ltac lred := repeat (prw _red_gen 1 3 0).
  Ltac rred := repeat (prw _red_gen 1 2 0).

  Lemma sim: ModSim.mod_sim example_spec_mod example_mod.
  Proof.
    refine (@ModSim.mk _ _ nat_wf nat_wf _ _ Σ _ _ _).
    { econs. exact 0. }
    { i. exists (S o0). ss. }
    { admit. }
    { cut (forall tid,
              I ⊢ fsim I tid itop6 itop6 (fun r_src r_tgt os => I ** ⌜r_src = r_tgt /\ os = []⌝) (example_spec_fun tt) (OMod.close_itree (example_omod) (SCMem.mod [1; 1]) (example_fun tt)) []).
      { admit. }
      i. iIntros "INV". ss. unfold example_spec_fun, example_fun.

      lred. rred. rewrite close_itree_call. ss. rred.
      iApply (@fsim_yieldR _ _ _ _ _ _ _ None). ss. iFrame. iIntros "INV _".
      rred. unfold SCMem.cas_fun, Mod.wrap_fun. rred.
      iDestruct "INV" as "[[%m [MEM ST]] [%w [MONO H]]]".
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
        { iDestruct "FUEL" as "[FUEL|FUEL]"; cycle 1.
          { iPoseProof (Done_persistent with "FUEL") as "# DONE".
            iDestruct (eventually_done with "DONE EVT") as "[H EVT]".
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
