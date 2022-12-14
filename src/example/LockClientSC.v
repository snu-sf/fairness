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
  Context `{ONESHOTRA: @GRA.inG (OneShot.t thread_id) Σ}.
  Context `{NATMAPRA: @GRA.inG (Auth.t (NatMapRA.t unit)) Σ}.
  Context `{REGIONRA: @GRA.inG (Region.t (thread_id * nat)) Σ}.
  Context `{CONSENTRA: @GRA.inG (@FiniteMap.t (Consent.t nat)) Σ}.
  Context `{AUTHRA: @GRA.inG (Auth.t (NatMapRA.t (nat * nat))) Σ}.

  Let Is: list iProp := [
      (∃ m own ws,
          (memory_black m)
            ∗
            (St_tgt (tt, m, (own, ws))));
      ()

      ((points_to loc_X const_0 ∗ OwnM (OneShot.pending thread_id 1))

  Let I: list iProp := [
      (∃ m,
          (memory_black m)
            **
            (St_tgt (tt, m)));
      (((points_to loc_l (SCMem.val_nat 0))
          **
          (points_to loc_f (SCMem.val_nat 0))
          **
          (OwnM (OneShot.pending thread_id 1)))
       ∨
         (∃ k,
             (OwnM (OneShot.shot k))
               **
               (ObligationRA.correl_thread k 1%ord)
               **
               (∃ n, ObligationRA.black k n)
               **
               (points_to loc_l (SCMem.val_nat 1))
               **
               ((points_to loc_f (SCMem.val_nat 0) ** ObligationRA.pending k (/2)%Qp)
                ∨
                  (points_to loc_f (SCMem.val_nat 1) ** ObligationRA.shot k))))]%I.

  Definition ticketlock_inv
             (L: bool) (W: NatMap.t unit)
             (reserved: bool)
             (now_serving: nat) (n: nat): iProp :=
    (wait_set_wf W n)
      **
      (regionl ((Nat.b2n reserved) + now_serving + n))
      **
      ((⌜n = 0 /\ L = false /\ reserved = false⌝ ** OwnM (Excl.just tt: Excl.t unit))
       ∨
         ((waiters (S ((Nat.b2n reserved) + now_serving)) n)
            **
            (∃ k j,
                (ConsentP.voted_singleton k j)
                  **
                  (ObligationRA.correl_thread j 1%ord)
                  **
                  (∃ o, ObligationRA.black j o)
                  **
                  (((⌜L = false /\ reserved = true⌝)
                      **
                      (OwnM (Excl.just tt: Excl.t unit))
                      **
                      (waiters_tax (S ((Nat.b2n reserved) + now_serving)) n)
                      **
                      (ObligationRA.pending j (/2)%Qp))
                   ∨
                     ((⌜L = true /\ reserved = false⌝)
                        **
                        (ObligationRA.shot j)))))).

  Definition wait_set_wf (W: NatMap.t unit) (n: nat): iProp :=
    ((natmap_prop_sum W (fun tid _ => own_thread tid))
       **
       (OwnM (Auth.black (Some W: NatMapRA.t unit)))
       **
       (⌜NatMap.cardinal W = n⌝))
  .

  Definition regionl (n: nat): iProp :=
    (∃ l, (Region.black l) ** (⌜List.length l = n⌝)).

  Definition waiters (start n: nat): iProp :=
    (list_prop_sum
       (fun a => (∃ k j tid,
                     (Region.white (start + a) (tid, k))
                       **
                       (OwnM (FiniteMap.singleton k (Consent.vote j (/2)%Qp)))
                       **
                       (ObligationRA.correl_thread j 1%ord)
                       **
                       (ObligationRA.pending j (/2)%Qp)
                       **
                       (∃ o, ObligationRA.black j o)
                       **
                       (FairRA.white (inl tid) (a × Ord.one)%ord)
                       **
                       (OwnM (Auth.white (NatMapRA.singleton tid tt: NatMapRA.t unit)))
       ))
       (seq 0 n))%I.

  Definition waiters_tax start n: iProp :=
    (list_prop_sum
       (fun a => (∃ k tid,
                     (Region.white (start + a) (tid, k))
                       **
                       (FairRA.white (inl tid) Ord.one)))
       (seq 0 n))%I.

  Definition ticketlock_inv
             (L: bool) (W: NatMap.t unit)
             (reserved: bool)
             (now_serving: nat) (n: nat): iProp :=
    (wait_set_wf W n)
      **
      (regionl ((Nat.b2n reserved) + now_serving + n))
      **
      ((⌜n = 0 /\ L = false /\ reserved = false⌝ ** OwnM (Excl.just tt: Excl.t unit))
       ∨
         ((waiters (S ((Nat.b2n reserved) + now_serving)) n)
            **
            (∃ k j,
                (ConsentP.voted_singleton k j)
                  **
                  (ObligationRA.correl_thread j 1%ord)
                  **
                  (∃ o, ObligationRA.black j o)
                  **
                  (((⌜L = false /\ reserved = true⌝)
                      **
                      (OwnM (Excl.just tt: Excl.t unit))
                      **
                      (waiters_tax (S ((Nat.b2n reserved) + now_serving)) n)
                      **
                      (ObligationRA.pending j (/2)%Qp))
                   ∨
                     ((⌜L = true /\ reserved = false⌝)
                        **
                        (ObligationRA.shot j)))))).

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
