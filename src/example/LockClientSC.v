From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
Unset Universe Checking.

From Fairness Require Export
     ITreeLib WFLib FairBeh NatStructs Mod pind Axioms
     OpenMod SCM Red IRed Wrapper WeakestAdequacy FairLock Concurrency.
From Ordinal Require Export ClassicalHessenberg.

Set Implicit Arguments.

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
      Ret tt.

  Definition thread2:
    ktree ((((@eventE void) +' cE) +' (sE unit))) unit unit
    :=
    fun _ =>
      _ <- trigger (Observe 0 [42]);;
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
  Context `{STATETGT: @GRA.inG (stateTgtRA (unit * SCMem.t * (bool * NatMap.t unit))) Σ}.
  Context `{IDENTSRC: @GRA.inG (identSrcRA (void)) Σ}.
  Context `{IDENTTGT: @GRA.inG (identTgtRA (void + SCMem.val + thread_id)%type) Σ}.

  Context `{OBLGRA: @GRA.inG ObligationRA.t Σ}.
  Context `{ARROWRA: @GRA.inG (ArrowRA (void + SCMem.val + thread_id)%type) Σ}.
  Context `{EDGERA: @GRA.inG EdgeRA Σ}.
  Context `{ONESHOTSRA: @GRA.inG (@FiniteMap.t (OneShot.t unit)) Σ}.

  Context `{MEMRA: @GRA.inG memRA Σ}.

  Context `{EXCL: @GRA.inG (Excl.t unit) Σ}.
  Context `{ONESHOTRA: @GRA.inG (OneShot.t nat) Σ}.
  Context `{REGIONRA: @GRA.inG (Region.t (thread_id * nat)) Σ}.
  Context `{CONSENTRA: @GRA.inG (@FiniteMap.t (Consent.t nat)) Σ}.
  Context `{AUTHNRA: @GRA.inG (Auth.t (Excl.t nat)) Σ}.
  Context `{AUTHNMRA: @GRA.inG (Auth.t (NatMapRA.t unit)) Σ}.
  Context `{AUTHNMNRA: @GRA.inG (Auth.t (NatMapRA.t nat)) Σ}.
  Context `{AUTHNMNN: @GRA.inG (Auth.t (NatMapRA.t (nat * nat))) Σ}.

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

  Definition lock_will_unlock (own: bool) (ths wait: TIdSet.t) : iProp :=
    ∃ (f: NatMap.t nat) (j: nat),
      (OwnM (Auth.black (Some f: NatMapRA.t nat)))
        ∗
        (OwnM (Auth.black (Excl.just j: Excl.t nat)))
        ∗
        (⌜nm_wf_pair f wait⌝)
        ∗
        (natmap_prop_sum ths (fun tid _ => (⌜~ NatMap.In tid wait⌝) -∗ ObligationRA.duty (inr (inr tid)) []))
        ∗
        (natmap_prop_sum f (fun tid idx => (ObligationRA.correl (inr (inr tid)) idx (Ord.omega ^ 2)%ord)
                                          ∗
                                          (ObligationRA.pending idx 1)
                                          ∗
                                          (ObligationRA.duty (inr (inr tid)) [(idx, Ord.omega)])
        ))
        ∗
        ((⌜own = false⌝ ∗ OwnM (Auth.white (Excl.just j: Excl.t nat)))
         ∨
           ((⌜own = true⌝)
              ∗ (ObligationRA.pending j 1)
              ∗ (ObligationRA.correl_thread j 1%ord)
              ∗ (natmap_prop_sum f (fun tid idx => ObligationRA.amplifier j idx 1%ord))
           )
        )
  .

  Definition lock_holding (j: nat) (n: Ord.t) : iProp :=
    (OwnM (Auth.black (Excl.just j: Excl.t nat))) ∗ (ObligationRA.white j n).

  Definition lock_waiting (tid: thread_id) (i: nat) : iProp :=
    ∃ m, (OwnM (Auth.white (NatMapRA.singleton tid i: NatMapRA.t nat)))
           ∗
           (ObligationRA.correl (inr (inr tid)) i (Ord.omega ^ 2)%ord)
           ∗
           (ObligationRA.black i m).

  Let config := [("thread1", tt↑); ("thread2", tt↑)].

  Lemma client_correct:
    UserSim.sim ClientSpec.mod ClientImpl.mod
                (prog2ths ClientSpec.mod config)
                (prog2ths ClientImpl.mod config).
  Proof.
    refine (@ModSim.mk _ _ nat_wf nat_wf _ _ Σ _ _ _).
    { econs. exact 0. }
    { i. exists (S o0). ss. }
    { admit. }
    { cut (forall tid,
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
