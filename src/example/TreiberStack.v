From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Import pind Axioms ITreeLib Red TRed IRed2 WFLibLarge.
From Fairness Require Import FairBeh Mod Linking.
From Fairness Require Import PCM IProp IPM IPropAux.
From Fairness Require Import IndexedInvariants OpticsInterp SimWeakest.
From Fairness Require Import TemporalLogic TemporalLogicFull SCMemSpec.

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
  Context `{Σ : GRA.t}.
  Context {TLRAS : @TLRAs XAtom STT Σ}.
  Context {AUXRAS : AUXRAs Σ}.

  Definition TreiberStackInv (n : nat) (s : SCMem.val) (γs : nat) : Formula n := (⌜True⌝)%F.

  Definition Stack (n : nat) (γs : nat) (L : list SCMem.val) : Formula n := (⌜True⌝)%F.

  (* Namespace for Spinlock invariants. *)
  Definition N_Treiber : namespace := (nroot .@ "Treiber").

  Definition IsTreiber n s γs : Formula n := (∃ (N : τ{namespace, n}),
        (⌜(↑N ⊆ (↑N_Treiber : coPset))⌝) ∗
          syn_inv n N (TreiberStackInv n s γs))%F.

  Global Instance IsTreiber_persistent n s γs:
    Persistent (⟦ IsTreiber n s γs, n⟧).
  Proof.
    unfold Persistent. iIntros "H". unfold IsTreiber. red_tl.
    iDestruct "H" as "[%N H]". iExists N. red_tl. rewrite red_syn_inv.
    iDestruct "H" as "#H". auto.
  Qed.

  Definition mask_has_Treiber (Es : coPsets) n :=
    (match Es !! n with Some E => (↑N_Treiber) ⊆ E | None => True end).

  Lemma mask_disjoint_Treiber_state_tgt : ↑N_Treiber ## (↑N_state_tgt : coPset).
  Proof. apply ndot_ne_disjoint. ss. Qed.

  Lemma Treiber_push_spec
        tid n
        (Es : coPsets)
        (MASK_TOP : OwnEs_top Es)
        (MASK_STTGT : mask_has_st_tgt Es n)
    :
    ⊢ ∀ s γs val L (P : Formula n) (Q : SCMem.val → Formula n) (ds : list (nat * nat * Formula n)),
        [@ tid, n, Es @]
          ⧼⟦(
            (syn_tgt_interp_as n sndl (fun m => (➢ (scm_memory_black m))))
            ∗ (⤉ IsTreiber n s γs)
            ∗ (⤉ Duty(tid) ds)
            ∗ (⤉ P)
            (* TODO: masks? *)
            ∗ (∀ (S : τ{list SCMem.val}), (⤉ Stack n γs S) ∗ (⤉ P)
                  ==∗ ((⤉ Stack n γs (val :: S)) ∗ (⤉ Q val)))
            (* TODO: Proper ord level. *)
            ∗ ◇{List.map fst ds}(2 + L, 1)
            )%F, 1+n⟧⧽
            (OMod.close_itree Client (SCMem.mod gvs) (TreiberStack.push (s,val)))
            ⧼_, ⟦((⤉ Q val) ∗ (⤉ Duty(tid) ds))%F, 1+n⟧⧽
  .
  Proof.
  Admitted.

End SPEC.
Global Opaque TreiberStack.push TreiberStack.pop.
