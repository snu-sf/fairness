From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Import pind Axioms ITreeLib Red TRed IRed2 WFLibLarge.
From Fairness Require Import FairBeh Mod Linking.
From Fairness Require Import PCM IProp IPM IPropAux.
From Fairness Require Import IndexedInvariants OpticsInterp SimWeakest.
From Fairness Require Import TemporalLogic SCMemSpec AuthExclAnysRA.

Module TreiberStack.

  Section TreiberStack.

    Context {state : Type}.
    Context {ident : ID}.

    Definition push_loop :
      (* ktree (threadE void unit) (SCMem.val * SCMem.val) unit *)
      ktree (threadE ident state) (SCMem.val * SCMem.val) unit
      :=
      fun '(s, node) =>
        ITree.iter
          (fun (_ : unit) =>
             head <- (OMod.call (R:=SCMem.val) "load" s);;
             _ <- (OMod.call (R:=unit) "store" (node,head));;
             b <- (OMod.call (R:=bool) "cas" (s, head, node));;
             if b then Ret (inr tt) else Ret (inl tt)) tt.

    Definition push :
      (* ktree (threadE void unit) (SCMem.val * SCMem.val) unit *)
      ktree (threadE ident state) (SCMem.val * SCMem.val) unit
      :=
      fun '(s,val) =>
        node <- (OMod.call (R:=SCMem.val) "alloc" 2);;
        _ <- (OMod.call (R:=unit) "store" (SCMem.val_add node 1, val));;
        _ <- push_loop (s, node);;
        trigger Yield.

    Definition pop :
      (* ktree (threadE void unit) SCMem.val (option (SCMem.val) *)
      ktree (threadE ident state) SCMem.val (option (SCMem.val))
      :=
      fun s =>
        ITree.iter
          (fun (_ : unit) =>
            head <- (OMod.call (R:=SCMem.val) "load" s);;
            is_null <- (OMod.call (R:=bool) "compare" (head, SCMem.val_null));;
            if is_null then Ret (inr None) else (
              next <- (OMod.call (R:=SCMem.val) "load" head);;
              b <- (OMod.call (R:=bool) "cas" (s, head, next));;
              if b then Ret (inr (Some head)) else Ret (inl tt)
            )
          ) tt.

    (** TODO : more rules for module composition. *)
    (* Definition omod : Mod.t := *)
    (*   Mod.mk *)
    (*     (* tt *) *)
    (*     (Mod.st_init Client) *)
    (*     (Mod.get_funs [("push", Mod.wrap_fun push); *)
    (*                    ("pop", Mod.wrap_fun pop)]) *)
    (* . *)

    (* Definition module gvs : Mod.t := *)
    (*   OMod.close *)
    (*     (omod) *)
    (*     (SCMem.mod gvs) *)
    (* . *)

  End TreiberStack.
End TreiberStack.

(* TODO: Write down spec for minimal LAT and TStack. *)
Section SPEC.

  Context {src_state : Type}.
  Context {src_ident : Type}.
  Context {Client : Mod.t}.
  Context {gvs : list nat}.
  Notation tgt_state := (OMod.closed_state Client (SCMem.mod gvs)).
  Notation tgt_ident := (OMod.closed_ident Client (SCMem.mod gvs)).

  Local Instance STT : StateTypes := Build_StateTypes src_state tgt_state src_ident tgt_ident.
  Context `{sub : @SRA.subG Γ Σ}.
  Context {TLRASs : TLRAs_small STT Γ}.
  Context {TLRAS : TLRAs STT Γ Σ}.

  Context {HasMEMRA: @GRA.inG memRA Γ}.
  Context {HasAuthExclAnys : @GRA.inG AuthExclAnysRA Γ}.

  Definition TreiberStackInv (n : nat) (s : SCMem.val) (γs : nat) : sProp n := (⌜True⌝)%S.

  Definition TreiberStack (n : nat) (γs : nat) (L : list SCMem.val) : sProp n := (⌜True⌝)%S.

  (* Namespace for Spinlock invariants. *)
  Definition N_Treiber : namespace := (nroot .@ "Treiber").

  Definition IsTreiber n s γs : sProp n := (∃ (N : τ{namespace, n}),
        (⌜(↑N ⊆ (↑N_Treiber : coPset))⌝) ∗
          syn_inv n N (TreiberStackInv n s γs))%S.

  Global Instance IsTreiber_persistent n s γs:
    Persistent (⟦ IsTreiber n s γs, n⟧).
  Proof.
    unfold Persistent. iIntros "H". unfold IsTreiber. red_tl.
    iDestruct "H" as "[%N H]". iExists N. red_tl. rewrite red_syn_inv.
    iDestruct "H" as "#H". auto.
  Qed.

  Definition mask_has_Treiber (E : coPset) :=
    (↑N_Treiber) ⊆ E.

  Lemma mask_disjoint_Treiber_state_tgt : ↑N_Treiber ## (↑N_state_tgt : coPset).
  Proof. apply ndot_ne_disjoint. ss. Qed.

  Lemma Treiber_push_spec n (Q : SCMem.val → sProp n) (P : sProp n) tid (E : coPset) :
    ∀ s γs val L (ds : list (nat * nat * sProp n)),
    ⊢ [@ tid, n, E @]
          ⧼⟦(
            (syn_tgt_interp_as n sndl (fun m => s_memory_black m))
            ∗ (⤉⤉ IsTreiber n s γs)
            ∗ (⤉⤉ Duty(tid) ds)
            ∗ (⤉⤉ P)
            (* TODO: masks? *)
            ∗ (⤉ ∀ (S : τ{list SCMem.val}), (● γs (S : list SCMem.val)) ∗ (⤉ P)
                  =|n+1|={E}=∗ ((● γs (val::S)) ∗ (⤉ Q val)))
            (* TODO: Proper ord level. *)
            ∗ ◇{List.map fst ds}(2 + L, 1)
            )%S, 2+n⟧⧽
            (OMod.close_itree Client (SCMem.mod gvs) (TreiberStack.push (s,val)))
          ⧼_, ⟦(
            (⤉⤉ Q val) ∗ (⤉⤉ Duty(tid) ds)
            )%S, 2+n⟧⧽
  .
  Proof.
  Admitted.

  Lemma Treiber_pop_spec
        n (Q : (option SCMem.val) → sProp n) (P : sProp n) tid
        (E : coPset)
        (* (MASK_TOP : OwnEs_top Es) *)
        (* (MASK_STTGT : mask_has_st_tgt Es n) *)
    :
    ∀ s γs L (ds : list (nat * nat * sProp n)),
    ⊢ [@ tid, n, E @]
          ⧼⟦(
            (syn_tgt_interp_as n sndl (fun m => s_memory_black m))
            ∗ (⤉ IsTreiber n s γs)
            ∗ (⤉ Duty(tid) ds)
            ∗ (⤉ P)
            (* TODO: masks? *)
            ∗ (⤉ ∀ (S : τ{list SCMem.val}), (● γs (S : list SCMem.val)) ∗ P
                  =|n|={E}=∗ (∃ (S' : τ{list SCMem.val}) (ov : τ{option SCMem.val}),
                    (● γs (S' : list SCMem.val)) ∗ Q ov ∗ ⌜ov = hd_error S⌝)
                    )
            (* TODO: Proper ord level. *)
            ∗ ◇{List.map fst ds}(2 + L, 1)
            )%S, 1+n⟧⧽
            (OMod.close_itree Client (SCMem.mod gvs) (TreiberStack.pop s))
            ⧼rv, ⟦((⤉ Q rv) ∗ (⤉ Duty(tid) ds))%S, 1+n⟧⧽
  .
  Proof.
  Admitted.

End SPEC.
Global Opaque TreiberStack.push TreiberStack.pop.
