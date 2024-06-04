From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Import pind Axioms ITreeLib Red TRed IRed2 WFLibLarge.
From Fairness Require Import FairBeh Mod Linking.
From Fairness Require Import PCM IProp IPM IPropAux.
From Fairness Require Import IndexedInvariants OpticsInterp SimWeakest.
From Fairness Require Import TemporalLogic TemporalLogicFull SCMemSpec.

Module TicketLock.

  Section TICKET.

    Context {state : Type}.
    Context {ident : ID}.

    Definition lock_loop :
      ktree (threadE ident state) (SCMem.val * SCMem.val) unit
      :=
      fun x =>
        let '(own_loc, my_tk) := x in
        ITree.iter
          (fun (_: unit) =>
             own <- (OMod.call (R:=SCMem.val) "load" own_loc);;
             b <- (OMod.call (R:=bool) "compare" (own, my_tk));;
             if b then Ret (inr tt) else Ret (inl tt)) tt.

    Definition lock :
      ktree (threadE ident state) (SCMem.val * SCMem.val) unit
      :=
      fun x =>
        let '(own_loc, next_loc) := x in
        my_tk <- (OMod.call (R:=SCMem.val) "faa" (next_loc, 1));;
        _ <- lock_loop (own_loc, my_tk);;
        trigger Yield.

    Definition unlock :
      ktree (threadE ident state) (SCMem.val * SCMem.val) unit
      :=
      fun x =>
        let '(own_loc, next_loc) := x in
        now <- (OMod.call (R:=SCMem.val) "load" own_loc);;
        _ <- (OMod.call (R:=unit) "store" (own_loc, SCMem.val_add now 1));;
        trigger Yield
    .

    (** TODO : more rules for module composition. *)
    (* Definition omod : Mod.t := *)
    (*   Mod.mk *)
    (*     (* tt *) *)
    (*     (Mod.st_init Client) *)
    (*     (Mod.get_funs [("lock", Mod.wrap_fun lock); *)
    (*                    ("unlock", Mod.wrap_fun unlock)]) *)
    (* . *)

    (* Definition module gvs : Mod.t := *)
    (*   OMod.close *)
    (*     (omod) *)
    (*     (SCMem.mod gvs) *)
    (* . *)

  End TICKET.

End TicketLock.

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

  Lemma lock_loop_red own_loc my_tk :
    @TicketLock.lock_loop tgt_state tgt_ident (own_loc, my_tk)
    =
      own <- (OMod.call (R:=SCMem.val) "load" (own_loc));;
      b <- (OMod.call (R:=bool) "compare" (own, my_tk));;
      if b then Ret tt else tau;; TicketLock.lock_loop (own_loc, my_tk).
  Proof.
    unfold TicketLock.lock_loop. etransitivity.
    { apply unfold_iter_eq. }
    grind.
  Qed.

  (* TODO *)

  (** Invariants. *)
  (* Ref: Lecture Notes on Iris. *)
  Definition tklockInv (i : nat) (r : nat) (lo ln : SCMem.val) (P : Formula i) (l : nat)
    : Formula (1+i) :=
    (∃ (o n o_obl : τ{nat, 1+i}) (D : τ{gset nat, 1+i}),
        (lo ↦ o)
          ∗ (ln ↦ n)
          ∗ ➢(tkl_b r o D)
          ∗ (⌜forall tk, (tk < n) <-> (tk ∈ D)⌝)
          ∗ ((➢(tkl_locked r o) ∗ (⤉P) ∗
               ((⌜o = n⌝) ∨ (⌜o < n⌝ ∗ ∃ (tid : τ{nat}) (ds : τ{ listT (nat * nat * Φ)%ftype, 1+i}),
                                      (⤉Duty(tid) ((o_obl, 0, emp) :: ds)) ∗ (⤉ ○Duty(tid) ds) ∗ ◇[o_obl](l, 1))))
             ∨ (∃ (_tid _obl : τ{nat, 1+i}), ➢(tkl_issued r o _tid _obl) ∗ (-[o_obl](l)-◇ emp))
            )
          ∗ ([∗ (1+i) set] tk ∈ D,
              (⌜tk <= o⌝) ∨ (∃ (tid obl : τ{nat}) (ds : τ{ listT (nat * nat * Φ)%ftype, 1+i}),
                               (⤉ Duty(tid) ds)
                                 ∗ (⤉ ○Duty(tid) ds)
                                 ∗ ➢(tkl_wait r tk tid obl)
                                 ∗ (◇[obl](1 + l, tk - o))
                                 ∗ (o_obl -(0)-◇ obl)
                           )
            )
    )%F.

  (* Namespace for TicketLock invariants. *)
  Definition N_TicketLock : namespace := (nroot .@ "TicketLock").

  Definition isTicketLock i (r : nat) (v : SCMem.val * SCMem.val) (P : Formula i) (l : nat)
    : Formula (1+i) :=
    (∃ (lo ln : τ{SCMem.val}) (N : τ{namespace, 1+i}),
        (⌜(↑N ⊆ (↑N_TicketLock : coPset))⌝)
          ∗ (⌜0 < l⌝) ∗ (⌜v = (lo, ln)⌝) ∗ syn_inv (1+i) N (tklockInv i r lo ln P l))%F.

  Global Instance isSpinlock_persistent i r v P l : Persistent (⟦isTicketLock i r v P l, 1+i⟧).
  Proof.
    unfold Persistent. iIntros "H". unfold isTicketLock.
    red_tl. iDestruct "H" as "[%lo H]". iExists lo.
    red_tl. iDestruct "H" as "[%ln H]". iExists ln.
    red_tl. iDestruct "H" as "[%N H]". iExists N.
    red_tl. rewrite red_syn_inv. iDestruct "H" as "#H". auto.
  Qed.

  Definition mask_has_TicketLock (Es : coPsets) n :=
    (match Es !! n with Some E => (↑N_TicketLock) ⊆ E | None => True end).


  Lemma make_isTicketLock
        i lo ln P l (LT : 0 < l)
        Es
    :
    ⊢
      ⟦((lo ↦ 0) ∗ (ln ↦ 0) ∗ (⤉P) ∗ ➢(tkl_auth))%F, 1+i⟧
        -∗
        ⟦(∃ (r : τ{nat, 1+i}), =|1+i|={Es}=> ((isTicketLock i r (lo, ln) P l)))%F, 1+i⟧.
  Proof.
    (* TODO *)
  Admitted.

  Lemma TicketLock_lock_spec
        tid i
        (Es : coPsets)
        (MASK_TOP : OwnEs_top Es)
    :
    ⊢ ∀ r lo ln (P : Formula i) l (ds : list (nat * nat * Formula i)),
        [@ tid, 1+i, Es @]
          ⧼⟦(((syn_tgt_interp_as (1+i) sndl (fun m => (➢ (scm_memory_black m))))
                ∗ (⤉ isTicketLock i r (lo, ln) P l)
                ∗ (⤉ (⤉ Duty(tid) ds))
                ∗ (⤉ (⤉ ○Duty(tid) ds))
                ∗ (⤉ (⤉ ●Duty(tid) ds))
                ∗ ◇{ds@1}(3 + l, 1))%F), 2+i⟧⧽
            (OMod.close_itree Client (SCMem.mod gvs) (TicketLock.lock (lo, ln)))
            ⧼rv, ⟦(∃ (o u : τ{nat, 2+i}),
                      (⤉ (⤉ P))
                        ∗ ➢(tkl_locked r o)
                        ∗ (⤉ (⤉ Duty(tid) ((u, 0, emp) :: ds)))
                        ∗ (⤉ (⤉ ○Duty(tid) ds))
                        ∗ (⤉ (⤉ ●Duty(tid) ds))
                        ∗ live[u] 1 ∗ ◇[u](l, 1))%F, 2+i⟧⧽
  .
  Proof.
  Admitted.

  Lemma TicketLock_unlock_spec
        tid i
        (Es : coPsets)
        (MASK_TOP : OwnEs_top Es)
    :
    ⊢ ∀ r lo ln (P : Formula i) l (ds : list (nat * nat * Formula i)) u o,
        [@ tid, 1+i, Es @]
          ⧼⟦((syn_tgt_interp_as (1+i) sndl (fun m => (➢ (scm_memory_black m))))
               ∗ (⤉ isTicketLock i r (lo, ln) P l)
               ∗ (⤉ (⤉ P))
               ∗ ➢(tkl_locked r o)
               ∗ (⤉ (⤉ Duty(tid) ((u, 0, emp) :: ds)))
               ∗ live[u] 1
               ∗ ◇{((u, 0, emp) :: ds)@1}(1, 3))%F, 2+i⟧⧽
            (OMod.close_itree Client (SCMem.mod gvs) (TicketLock.unlock (lo, ln)))
            ⧼rv, ⟦((⤉ (⤉ Duty(tid) ds))
                     ∗ (⤉ (⤉ ○Duty(tid) ds))
                     ∗ (⤉ (⤉ ●Duty(tid) ds))
                  )%F, 2+i⟧⧽
  .
  Proof.
  Admitted.

End SPEC.
Global Opaque TicketLock.lock TicketLock.unlock.
