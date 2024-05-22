From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Import pind Axioms ITreeLib Red TRed IRed2 WFLibLarge.
From Fairness Require Import FairBeh Mod Linking.
From Fairness Require Import PCM IProp IPM.
From Fairness Require Import IndexedInvariants OpticsInterp SimWeakest.
From Fairness Require Import TemporalLogic TemporalLogicFull SCMemSpec.
(* From Fairness Require Import ModSim. *)
(* Import NatStructs. *)

Module Spinlock.

  Notation unlocked := (SCMem.val_nat 0).
  Notation locked := (SCMem.val_nat 1).

  Definition lock :
    ktree (threadE void unit) SCMem.val unit
    :=
    fun x =>
      ITree.iter
        (fun (_ : unit) =>
           b <- (OMod.call "cas" (x, unlocked, locked));;
           if (b : bool) then Ret (inr tt) else Ret (inl tt)) tt.

  Definition unlock :
    ktree (threadE void unit) SCMem.val unit
    :=
    fun x => (OMod.call "store" (x, unlocked)).

  Definition omod : Mod.t :=
    Mod.mk
      tt
      (Mod.get_funs [("lock", Mod.wrap_fun lock);
                     ("unlock", Mod.wrap_fun unlock)])
  .

  Definition module : Mod.t :=
    OMod.close
      (omod)
      (SCMem.mod [])
  .

End Spinlock.

Section SIM.

  Context {STT : StateTypes}.

  Context `{Σ : GRA.t}.
  (* Invariant related default RAs *)
  Context `{OWNESRA : @GRA.inG OwnEsRA Σ}.
  Context `{OWNDSRA : @GRA.inG OwnDsRA Σ}.
  Context `{IINVSETRA : @GRA.inG (IInvSetRA (@Formula XAtom STT)) Σ}.
  (* State related default RAs *)
  Context `{THDRA: @GRA.inG ThreadRA Σ}.
  Context `{STATESRC: @GRA.inG (stateSrcRA st_src_type) Σ}.
  Context `{STATETGT: @GRA.inG (stateTgtRA st_tgt_type) Σ}.
  Context `{IDENTSRC: @GRA.inG (identSrcRA id_src_type) Σ}.
  Context `{IDENTTGT: @GRA.inG (identTgtRA id_tgt_type) Σ}.
  (* Liveness logic related default RAs *)
  Context `{OBLGRA: @GRA.inG ObligationRA.t Σ}.
  Context `{EDGERA: @GRA.inG EdgeRA Σ}.
  Context `{ONESHOTRA: @GRA.inG ArrowShotRA Σ}.
  Context `{ARROWRA: @GRA.inG (@ArrowRA id_tgt_type (@Formula XAtom STT)) Σ}.
  (* SCMem related RAs *)
  Context `{MEMRA: @GRA.inG memRA Σ}.
  (* Map from nat to Excl unit RA. *)
  Context `{EXCLUNITS: @GRA.inG ExclUnitsRA Σ}.


  Variable p_spinlock : Prism.t id_tgt_type void.
  Variable l_spinlock : Lens.t st_tgt_type unit.
  Let emb_spinlock := plmap p_spinlock l_spinlock.

  Definition spinlock_inv


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


End SIM.
