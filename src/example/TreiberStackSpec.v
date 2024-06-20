From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From iris Require Import bi.big_op.
From Fairness Require Import pind Axioms ITreeLib Red TRed IRed2 WFLibLarge.
From Fairness Require Import FairBeh Mod Linking.
From Fairness Require Import TreiberStack.
From Fairness Require Import PCM IProp IPM IPropAux.
From Fairness Require Import IndexedInvariants OpticsInterp SimWeakest.
From Fairness Require Import TemporalLogic SCMemSpec AuthExclsRA.

Section SPEC.

  Context {src_state : Type}.
  Context {src_ident : Type}.
  Context {Client : Mod.t}.
  Context {gvs : list nat}.
  Context (treiberN : namespace).
  Notation tgt_state := (OMod.closed_state Client (SCMem.mod gvs)).
  Notation tgt_ident := (OMod.closed_ident Client (SCMem.mod gvs)).

  Local Instance STT : StateTypes := Build_StateTypes src_state tgt_state src_ident tgt_ident.
  Context `{sub : @SRA.subG Γ Σ}.
  Context {TLRASs : TLRAs_small STT Γ}.
  Context {TLRAS : TLRAs STT Γ Σ}.

  Context {HasMEMRA: @GRA.inG memRA Γ}.
  Context {HasAuthExclAnys : @GRA.inG (AuthExcls.t (list SCMem.val)) Γ}.

  Ltac red_tl_all := red_tl; red_tl_memra; red_tl_authexcls.

  Inductive mabye_null_ptr : Type :=
  | Null
  | Ptr (p : SCMem.pointer).
  Local Instance mabye_null_ptr_eqdec : EqDecision mabye_null_ptr.
  Proof. solve_decision. Qed.

  Definition to_val (mnp : mabye_null_ptr) : SCMem.val :=
    match mnp with
    | Null => SCMem.val_null
    | Ptr p => SCMem.val_ptr p
    end.

  Fixpoint phys_list n (l : mabye_null_ptr) (L : list SCMem.val) : sProp n := (
    match (l,L) with
    | (Null, []) => emp
    | (Null, _ :: _) => ⌜False⌝
    | (Ptr _, []) => ⌜False⌝
    | (Ptr l, v::tL) => ∃ (r : τ{mabye_null_ptr}), (l ↦∗□ [(to_val r); v]) ∗ (phys_list n r tL)
    end
  )%S.

  Definition TStackLivenessInv (lv k γs : nat) (h : mabye_null_ptr) : sProp (1+lv)  := (
    ∃ (m : τ{ (gmap nat (option mabye_null_ptr)) ,1+lv}),
    [∗ (1+lv) , (option mabye_null_ptr) map] i ↦ op ∈ m, (
      match op with
      | None => emp
      | Some p =>
        if (decide (h=p)) then
          ◇[k](0,1)
        else
          emp
      end
    )
  )%S.

  (* Definition TreiberStackInv (n : nat) (s : SCMem.val) (γs : nat) : sProp n := (
    ∃ (h : τ{option SCMem.pointer}) (L : τ{list SCMem.val}),
      s ↦ (to_val h) ∗ ● γs (L : list SCMem.val) ∗
      phys_list n h L ∗
  )%S.

  Definition IsTreiber n s γs : sProp n := (
    syn_inv n treiberN (TreiberStackInv n s γs)
  )%S.

  Global Instance IsTreiber_persistent n s γs:
    Persistent (⟦ IsTreiber n s γs, n⟧).
  Proof. unfold Persistent,IsTreiber. rewrite red_syn_inv. by iIntros "#?". Qed.

  Lemma Treiber_push_spec {n} (E : coPset) (Q : SCMem.val → sProp n) (P : sProp n) tid (SUBSET : (↑treiberN) ⊆ E) :
    ∀ s γs val L (ds : list (nat * nat * sProp n)),
    ⊢ [@ tid, n, E @]
          ⧼⟦(
            (syn_tgt_interp_as n sndl (fun m => s_memory_black m))
            ∗ (⤉ IsTreiber n s γs)
            ∗ (⤉ Duty(tid) ds)
            ∗ (⤉ P)
            (* TODO: masks? *)
            ∗ (∀ (S : τ{list SCMem.val, 1+n}), (⤉ (● γs (S : list SCMem.val) ∗ P))
                  =|1+n|={E}=∗ (⤉ (● γs (val::S) ∗ Q val))
              )
            (* TODO: Proper ord level. *)
            ∗ ◇{List.map fst ds}(2 + L, 1)
            )%S, 1+n⟧⧽
            (OMod.close_itree Client (SCMem.mod gvs) (TreiberStack.push (s,val)))
          ⧼_, ⟦(
            (⤉ (Q val ∗ Duty(tid) ds))
            )%S, 1+n⟧⧽
  .
  Proof.
  Admitted.
(*
∀ (S : τ{list SCMem.val}), (⤉ (● γs (S : list SCMem.val) ∗ P))
                  =|1+n|={E}=∗
                  (∃ (S' : τ{list SCMem.val}) (ov : τ{option SCMem.val}),
                    (⤉ (● γs (S' : list SCMem.val) ∗ Q (ov : option SCMem.val) ∗ ⌜ov = hd_error S⌝)))
*)
  Lemma Treiber_pop_spec
        {n} (E : coPset) (Q : (option SCMem.val) → sProp n) (P : sProp n) tid
        (SUBSET : (↑treiberN) ⊆ E) :
    ∀ s γs L (ds : list (nat * nat * sProp n)),
    ⊢ [@ tid, n, E @]
          ⧼⟦(
            (syn_tgt_interp_as n sndl (fun m => s_memory_black m))
            ∗ (⤉ IsTreiber n s γs)
            ∗ (⤉ Duty(tid) ds)
            ∗ (⤉ P)
            (* TODO: masks? *)
            ∗ (∀ (S : τ{list SCMem.val, 1+n}), (⤉ (● γs (S : list SCMem.val) ∗ P))
                  =|1+n|={E}=∗
                  match S with
                  | [] => (⤉ (● γs ([] : list SCMem.val) ∗ Q None))
                  | h::t => (⤉ (● γs t ∗ Q (Some h)))
                  end
              )
            (* TODO: Proper ord level. *)
            ∗ ◇{List.map fst ds}(2 + L, 1)
            )%S, 1+n⟧⧽
            (OMod.close_itree Client (SCMem.mod gvs) (TreiberStack.pop s))
          ⧼rv, ⟦(
            (⤉ (Q rv ∗ Duty(tid) ds))
            )%S, 1+n⟧⧽
  .
  Proof.
  Admitted. *)

End SPEC.
Global Opaque TreiberStack.push TreiberStack.pop.
