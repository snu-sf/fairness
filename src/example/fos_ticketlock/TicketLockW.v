From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From iris.algebra Require Import auth excl_auth cmra updates functions.
From Fairness Require Import pind Axioms ITreeLib Red TRed IRed2 WFLibLarge.
From Fairness Require Import FairBeh Mod Concurrency Linking.
From Fairness Require Import PCM IPM IPropAux OwnGhost.
From Fairness Require Import IndexedInvariants OpticsInterp SimWeakest SimWeakestAdequacy.
From Fairness Require Import TemporalLogic.

From Fairness Require Import WMMSpec.
From PromisingLib Require Import Loc Event.
From PromisingSEQ Require Import View.
From Ordinal Require Export ClassicalHessenberg.
Require Import Coq.Numbers.BinNums.
From Fairness Require Import FairLock.
From Fairness Require Import NatStructs NatMapRA.
From Fairness Require Import MonotoneRA FairnessRA OneShotsRA.

Set Implicit Arguments.

Section INIT.

  Definition nat2c (n: nat): Const.t := Const.of_Z (BinIntDef.Z.of_nat n).

  Definition const_1: Const.t := nat2c 1.

End INIT.

Module TicketLockW.

  Definition tk := nat.

  Definition now_serving: Loc.t := Loc.of_nat 1.
  Definition next_ticket: Loc.t := Loc.of_nat 2.

  Definition lock_loop (myticket: Const.t) (tvw: View.t):
    itree (threadE void unit) View.t
    :=
    ITree.iter
      (fun (tvw: View.t) =>
         '(tvw, now) <- (OMod.call "load" (tvw, now_serving, Ordering.acqrel));;
         b <- unwrap (Const.eqb myticket now);;
         if (b: bool) then Ret (inr tvw) else Ret (inl tvw)) tvw.

  Definition lock_fun:
    ktree (threadE void unit) View.t View.t :=
    fun tvw =>
      '(tvw, myticket) <- (OMod.call "faa" (tvw, next_ticket, const_1, Ordering.plain, Ordering.acqrel));;
      tvw <- lock_loop myticket tvw;;
      _ <- trigger Yield;;
      Ret tvw
  .

  Definition unlock_fun:
    ktree (threadE void unit) View.t View.t :=
    fun tvw =>
      '(tvw, v) <- (OMod.call "load" (tvw, now_serving, Ordering.relaxed));;
      let v := Const.add v const_1 in
      tvw <- (OMod.call "store" (tvw: View.t, now_serving, v, Ordering.acqrel));;
      _ <- trigger Yield;;
      Ret tvw
  .

  Definition omod: Mod.t :=
    Mod.mk
      tt
      (Mod.get_funs [("lock", Mod.wrap_fun lock_fun);
                     ("unlock", Mod.wrap_fun unlock_fun)])
  .

  Definition module : Mod.t :=
    OMod.close
      (omod)
      (WMem.mod)
  .

  Lemma lock_loop_red myticket tvw
    :
    lock_loop myticket tvw
    =
      '(tvw, now) <- (OMod.call "load" (tvw, now_serving, Ordering.acqrel));;
      b <- unwrap (Const.eqb myticket now);;
      if (b: bool)
      then Ret tvw else tau;; lock_loop myticket tvw.
  Proof.
    unfold lock_loop. etransitivity.
    { apply unfold_iter_eq. }
    grind.
  Qed.

End TicketLockW.


Section AUX.

  Variant prod_le
          {A B: Type} {RA: A -> A -> Prop} {RB: B -> B -> Prop}
          (PRA: PartialOrder RA) (PRB: PreOrder RB) :
    (A * B) -> (A * B) -> Prop :=
    | prod_le_l
        a0 a1 b0 b1
        (ORD: RA a0 a1)
        (NEQ: a0 <> a1)
      :
      prod_le PRA PRB (a0, b0) (a1, b1)
    | prod_le_r
        a b0 b1
        (ORD: RB b0 b1)
      :
      prod_le PRA PRB (a, b0) (a, b1)
  .

  Global Program Instance prod_le_PreOrder
         {A B: Type} {RA: A -> A -> Prop} {RB: B -> B -> Prop}
         (PRA: PartialOrder RA) (PRB: PreOrder RB)
    : PreOrder (prod_le PRA PRB).
  Next Obligation.
    ii. destruct x. econs 2. inv PRB. auto.
  Qed.
  Next Obligation.
    ii. destruct x as [a0 b0], y as [a1 b1], z as [a2 b2].
    inv H.
    - inv H0.
      + econs 1; inv PRA.
        * inv partial_order_pre. eapply PreOrder_Transitive; eauto.
        * ii. clarify. apply NEQ0. apply partial_order_anti_symm; auto.
      + econs 1; auto.
    - inv H0.
      + econs 1; auto.
      + econs 2. inv PRB. eapply PreOrder_Transitive; eauto.
  Qed.

End AUX.

Module Tkst.
  Section TKST.

    Definition t X := (nat * X)%type.

    Definition le {X} (s0 s1: @t X): Prop :=
      let '(n0, x0) := s0 in
      let '(n1, x1) := s1 in
      (n0 <= n1) /\ (n0 = n1 -> x0 = x1).

    Global Program Instance le_PreOrder X: PreOrder (@le X).
    Next Obligation.
      ii. unfold le. des_ifs.
    Qed.
    Next Obligation.
      ii. unfold le in *. des_ifs. des; clarify. split; auto; try lia.
      i. clarify. assert (n0 = n1). lia. clarify. rewrite H2; auto.
    Qed.


    Definition a {X} x : t X := (1, x).
    Definition b {X} x : t X := (2, x).
    Definition c {X} x : t X := (3, x).
    Definition d {X} x : t X := (4, x).

  End TKST.
End Tkst.

Section TKQ.

  Inductive tkqueue
            (l: list thread_id) (tks: NatMap.t TicketLockW.tk) (inc exc: TicketLockW.tk)
    : Prop :=
  | tkqueue_nil
      (EMP1: l = [])
      (EMP2: tks = @NatMap.empty _)
      (EQ: inc = exc)
    :
    tkqueue l tks inc exc
  | tkqueue_cons
      hd tl
      (QUEUE: l = hd :: tl)
      (FIND: NatMap.find hd tks = Some inc)
      (TL: tkqueue tl (NatMap.remove hd tks) (S inc) exc)
    :
    tkqueue l tks inc exc
  .

  Lemma tkqueue_enqueue
        l tks inc exc
        (TQ: tkqueue l tks inc exc)
        k
        (FIND: NatMap.find k tks = None)
    :
    tkqueue (l ++ [k]) (NatMap.add k exc tks) inc (S exc).
  Proof.
    revert_until TQ. induction TQ; i; clarify; ss.
    { econs 2. ss. apply nm_find_add_eq. econs 1; auto. rewrite nm_find_none_rm_add_eq; auto. }
    assert (NEQ: hd <> k).
    { ii. clarify. }
    econs 2. instantiate (2:=hd). ss. rewrite nm_find_add_neq; auto.
    erewrite <- nm_find_none_add_rm_is_eq. eapply IHTQ.
    rewrite nm_find_rm_neq; auto. rewrite nm_find_add_neq; auto. apply nm_find_rm_eq.
    instantiate (1:=inc). rewrite nm_add_rm_comm_eq; auto.
    rewrite <- nm_find_some_rm_add_eq; auto. rewrite nm_find_add_neq; auto.
  Qed.

  Lemma tkqueue_dequeue
        l tks inc exc
        (TQ: tkqueue l tks inc exc)
        hd tl
        (HD: l = hd :: tl)
    :
    tkqueue tl (NatMap.remove hd tks) (S inc) exc.
  Proof.
    revert_until TQ. induction TQ; i; clarify; ss.
  Qed.

  Lemma tkqueue_range
        l tks inc exc
        (TQ: tkqueue l tks inc exc)
    :
    inc <= exc.
  Proof.
    induction TQ; i; clarify; ss. lia.
  Qed.

  Lemma tkqueue_val_range_l
        l tks inc exc
        (TQ: tkqueue l tks inc exc)
        t v
        (FIND: NatMap.find t tks = Some v)
    :
    inc <= v.
  Proof.
    revert_until TQ. induction TQ; i; clarify; ss.
    destruct (tid_dec t hd) eqn:DEC; clarify.
    hexploit (IHTQ t v). rewrite nm_find_rm_neq; auto. i. lia.
  Qed.

  Lemma tkqueue_val_range_r
        l tks inc exc
        (TQ: tkqueue l tks inc exc)
        t v
        (FIND: NatMap.find t tks = Some v)
    :
    v < exc.
  Proof.
    revert_until TQ. induction TQ; i; clarify; ss.
    destruct (tid_dec t hd) eqn:DEC; clarify.
    - eapply tkqueue_range in TQ. lia.
    - hexploit (IHTQ t v). rewrite nm_find_rm_neq; auto. i. lia.
  Qed.

  Lemma tkqueue_inv_unique
        l tks inc exc
        (TQ: tkqueue l tks inc exc)
        t0 t1 v
        (FIND0: NatMap.find t0 tks = Some v)
        (FIND1: NatMap.find t1 tks = Some v)
    :
    t0 = t1.
  Proof.
    revert_until TQ. induction TQ; i; clarify; ss.
    destruct (tid_dec t0 hd) eqn:DEC0; clarify; eauto.
    { destruct (tid_dec t1 hd) eqn:DEC1; clarify; eauto.
      hexploit tkqueue_val_range_l. eapply TQ. erewrite nm_find_rm_neq.
      2:{ ii. apply n. symmetry. eapply H. }
      eapply FIND1. i. lia.
    }
    { destruct (tid_dec t1 hd) eqn:DEC1; clarify; eauto.
      { hexploit tkqueue_val_range_l. eapply TQ. erewrite nm_find_rm_neq.
        2:{ ii. apply n. symmetry. eapply H. }
        eapply FIND0. i. lia.
      }
      eapply IHTQ; rewrite nm_find_rm_neq; eauto.
    }
  Qed.

  Lemma tkqueue_inv_hd
        l tks inc exc
        (TQ: tkqueue l tks inc exc)
        t
        (FIND: NatMap.find t tks = Some inc)
    :
    exists tl, l = t :: tl.
  Proof.
    revert_until TQ. induction TQ; i; clarify; ss.
    destruct (tid_dec t hd) eqn:DEC; clarify; eauto.
    hexploit tkqueue_inv_unique. 2: eapply FIND. 2: eapply FIND0.
    { instantiate (1:=exc). instantiate (1:=inc). instantiate (1:=hd :: tl).
      econs 2; eauto.
    }
    i; clarify.
  Qed.

  Lemma tkqueue_find_in
        l tks inc exc
        (TQ: tkqueue l tks inc exc)
        t v
        (FIND: NatMap.find t tks = Some v)
    :
    In t l.
  Proof.
    revert_until TQ. induction TQ; i; clarify; ss.
    destruct (tid_dec t hd) eqn:DEC; clarify; auto.
    right. hexploit (IHTQ t v). rewrite nm_find_rm_neq; auto. i. auto.
  Qed.

  Lemma tkqueue_in_find
        l tks inc exc
        (TQ: tkqueue l tks inc exc)
        t
        (IN: In t l)
    :
    exists v, NatMap.find t tks = Some v.
  Proof.
    revert_until TQ. induction TQ; i; clarify; ss. des; clarify; eauto.
    hexploit (IHTQ t IN). i. des. exists v. rewrite NatMapP.F.remove_o in H. des_ifs.
  Qed.

End TKQ.

Section AUX.

  Definition ord_ge: Ord.t -> Ord.t -> Prop := fun o1 o2 => Ord.le o2 o1.

  Global Program Instance ord_ge_PreOrder: PreOrder ord_ge.
  Next Obligation.
    ii. unfold ord_ge. reflexivity.
  Qed.
  Next Obligation.
    ii. unfold ord_ge in *. etrans; eauto.
  Qed.


End AUX.

(* TODO: Move *)
Section OWNMS_SPROP.

  Context {STT : StateTypes}.
  Context `{sub : @SRA.subG Γ Σ}.
  Context {TLRASs : TLRAs_small STT Γ}.
  Context {TLRAS : TLRAs STT Γ Σ}.
  Context `{IN1: @GRA.inG R Γ}.
  Context `{IN2: @GRA.inG (Id -d> R) Γ}.

  Definition s_OwnMs {n} (s: Id -> Prop) (u: R) : sProp n :=
    (➢((fun i =>
      if (excluded_middle_informative (s i))
      then u
      else ε): discrete_fun _ ))%S.

  Lemma red_s_OwnMs n (s: Id -> Prop) (u: R) :
    ⟦s_OwnMs s u, n⟧ = OwnMs s u.
  Proof.
    unfold s_OwnMs, OwnMs. red_tl. ss.
  Qed.

End OWNMS_SPROP.

Section SIM.

  Notation src_state := (Mod.state AbsLockW.mod).
  Notation src_ident := (Mod.ident AbsLockW.mod).
  Notation tgt_state := (Mod.state TicketLockW.module).
  Notation tgt_ident := (Mod.ident TicketLockW.module).

  Local Instance STT : StateTypes := Build_StateTypes src_state tgt_state src_ident tgt_ident.
  Context `{sub : @SRA.subG Γ Σ}.
  Context {TLRASs : TLRAs_small STT Γ}.
  Context {TLRAS : TLRAs STT Γ Σ}.

  Context {HasMEMRA: @GRA.inG wmemRA Γ}.

  Context `{MONORA: @GRA.inG monoRA Γ}.
  Context `{NATMAPRA: @GRA.inG (authUR (NatMapRA.t TicketLockW.tk)) Γ}. (* waiters natmap ra *)
  Context `{AUTHRA2: @GRA.inG (excl_authUR (leibnizO (((nat * nat) * View.t)))) Γ}. (* token *)
  Context `{IN2: @GRA.inG (thread_id -d> (excl_authUR (leibnizO (list nat)))) Γ}. (* ticket token ra *)
  Context {HasOneShots : @GRA.inG (OneShots.t unit) Γ}.


  Let mypreord := prod_le_PreOrder Nat.le_po (Tkst.le_PreOrder nat).
  Let wmpreord := prod_le_PreOrder Nat.le_po (base.PreOrder_instance_0 nat).
  Let wopreord := prod_le_PreOrder Nat.le_po (ord_ge_PreOrder).


  Section VARIABLES.

  Variable monok: nat.
  Variable tk_mono: nat.
  Variable wm_mono: nat.
  (* Variable wo_mono: nat. *)

  Definition N_Ticketlock_w : namespace := (nroot .@ "Ticketlock_w").
  Lemma mask_disjoint_ticketlock_state_tgt : ↑N_Ticketlock_w ## (↑N_state_tgt : coPset).
  Proof. apply ndot_ne_disjoint. ss. Qed.

  Fixpoint list_sprop_sum {n} A (l: list A) (P: A -> sProp n) : sProp n :=
    match l with
    | [] => ⌜True⌝%S
    | hd::tl => (P hd ∗ list_sprop_sum tl P)%S
    end.

  Definition natmap_sprop_sum {n} A (f: NatMap.t A) (P: nat -> A -> sProp n) :=
    list_sprop_sum (NatMap.elements f) (fun '(k, v) => P k v).

  Lemma red_sprop_sum n A (f: NatMap.t A) (P: nat -> A -> sProp n) :
    ⟦natmap_sprop_sum f P, n⟧ = natmap_prop_sum f (fun t a => ⟦P t a, n⟧).
  Proof.
    unfold natmap_sprop_sum, natmap_prop_sum.
    induction (NatMap.elements _); ss; red_tl.
    rewrite IHl. des_ifs.
  Qed.

  Ltac red_tl_all :=
    red_tl; red_tl_memra; red_tl_monoRA; red_tl_oneshots;
      try rewrite ! red_sprop_sum; try rewrite ! red_s_OwnMs.

  Definition ticket_lock_inv_unlocking
             n (l: list thread_id) (tks: NatMap.t nat) (now next: nat) (myt: thread_id) (κm : nat): sProp n :=
    (TID(myt)
    ∗ ⌜tkqueue l tks (S now) next⌝
    ∗ (natmap_sprop_sum tks
        (fun th tk =>
          ⟨Atom.fair_white_src Prism.id th (Ord.from_nat (tk - (S now)))⟩
          ∗ (∃ κa γs : τ{nat, n},
              ◆[κa, 4 + tk]
              ∗ (-[κa](0)-⧖ ▿ γs tt)
              ∗ ⧖[κa, 1/2]
              ∗ △ γs 1
              ∗ ◇[κa](4 + tk, tk - now)
              ∗ ➢(maps_to_res th (●E ([κa; γs]: leibnizO _)))%I)))
    ∗ s_monoBlack monok mypreord (now, Tkst.c κm))%S.

  Lemma ticket_lock_inv_unlocking_eq n l tks now next myt κm :
    ⟦ ticket_lock_inv_unlocking n l tks now next myt κm, n ⟧ ⊣⊢
    own_thread myt ∗ ⌜tkqueue l tks (S now) next⌝ ∗
      natmap_prop_sum tks
        (λ t a : nat,
           ⟦ ⟨ Atom.fair_white_src Prism.id t (a - S now) ⟩%S ∗
           (∃ κa γs : τ{nat,n}, ◆[κa, (S (S (S (S a))))] ∗ -[κa](0)-⧖ (▿ γs ()) ∗ ⧖[κa,
              (1 / 2)] ∗ (△ γs 1) ∗ ◇[κa]((S (S (S (S a)))), (a - now)) ∗
              ➢ maps_to_res t (●E ([κa; γs]: leibnizO _)))%S, n ⟧) ∗ monoBlack monok mypreord (now, Tkst.c κm).
  Proof. unfold ticket_lock_inv_unlocking. red_tl_all. simpl in *. f_equiv. Qed.

  Definition ticket_lock_inv_unlocked0
             n (l: list thread_id) (tks: NatMap.t nat) (now next : nat)
             (myt: thread_id) (V: View.t) (κm: nat): sProp n :=
    (➢ (◯E ((now, myt, V) : leibnizO _))
    ∗ ⌜(l = []) /\ (tks = @NatMap.empty _) /\ (now = next)⌝
    ∗ s_monoBlack monok mypreord (now, Tkst.a κm))%S.

  Definition ticket_lock_inv_unlocked1
             n (l: list thread_id) (tks: NatMap.t nat) (now next: nat)
             (myt: thread_id) (V: View.t) (κm : nat): sProp n :=
    (∃ (yourt κay : τ{nat, n}) (waits : τ{list nat, n}),
      (➢ (◯E ((now, myt, V): leibnizO _))
      ∗ (⌜(l = yourt :: waits)⌝)
      ∗ (⌜tkqueue l tks now next⌝)
      ∗ (natmap_sprop_sum (NatMap.remove (elt:=nat) yourt tks)
          (fun th tk =>
            (⟨Atom.fair_white_src Prism.id th (Ord.from_nat (tk - now))⟩)
            ∗ (∃ κa γs : τ{nat, n},
              ◆[κa, 4 + tk]
              ∗ (-[κa](0)-⧖ ▿ γs tt)
              ∗ ⧖[κa, 1/2]
              ∗ △ γs 1
              ∗ ◇[κa](4 + tk, tk - now)
              ∗ ➢(maps_to_res th (●E ([κa; γs] : leibnizO _)))%I
              ∗ κay -(0)-◇ κa)))
      ∗ (∃ (γs: τ{nat, n}),
          (s_monoBlack monok mypreord (now, Tkst.b (κm : nat)))
          ∗ (◆[κay, 4 + now])
          ∗ (△ γs 1)
          ∗ (-[κay](0)-◇ ▿ γs tt)
          ∗ (⋈ [κay])
          ∗ (κm -(2)-◇ κay)
          ∗ ➢(maps_to_res yourt (●E ([κay; γs] : leibnizO _)))%I)))%S.

  Definition ticket_lock_inv_locked
             n (l: list thread_id) (tks: NatMap.t nat) (now next: nat)
             (myt: thread_id) (V: View.t) (κm : nat): sProp n :=
    (➢ (◯E ((now, myt, V) : leibnizO _))
    ∗ ⌜tkqueue l tks (S now) next⌝
    ∗ (natmap_sprop_sum tks
        (fun th tk =>
          (⟨Atom.fair_white_src Prism.id th (Ord.from_nat (tk - (S now)))⟩)
          ∗ (∃ κa γs: τ{nat, n},
              ◆[κa, 4 + tk]
              ∗ (-[κa](0)-⧖ ▿ γs tt)
              ∗ ⧖[κa, 1/2]
              ∗ △ γs 1
              ∗ ◇[κa](4 + tk, tk - now)
              ∗ ➢(maps_to_res th (●E ([κa; γs] : leibnizO _)))%I)))
    ∗ (s_monoBlack monok mypreord (now, Tkst.c κm)))%S.

  Definition ticket_lock_inv_tks n (tks: NatMap.t nat) : sProp n :=
    ((➢ (● (NatMapRA.to_Map tks)))
      ∗ ⟨Atom.fair_whites_src Prism.id (fun id => (~ NatMap.In id tks)) Ord.omega⟩
      ∗ (natmap_sprop_sum tks (fun tid tk => TID(tid)))
      ∗ (s_OwnMs (fun id => (~ NatMap.In id tks))
          (●E ([] : leibnizO _)
          ⋅ ◯E ([] : leibnizO _))))%S.

  Definition wP (n: nat): wProp := fun c _ => (exists m, (c = nat2c m) /\ (m < n)).
  Definition wQ (n: nat): wProp := fun c _ => ((c = nat2c n)).

  Definition ticket_lock_inv_mem
             n (V: View.t) (κm: nat) (now next: nat) (myt: thread_id) : sProp n :=
    (TicketLockW.now_serving ↦(n, inrp){full} V κm (wP now) (wQ now)
    ∗ (TicketLockW.next_ticket ↦{faa} (nat2c next))
    ∗ (➢ (●E ((now, myt, V) : leibnizO _)))
    ∗ (s_monoBlack tk_mono Nat.le_preorder now)
    ∗ (s_monoBlack wm_mono wmpreord (now, κm))
    ∗ ◆[κm, 1])%S.

  Definition ticket_lock_inv_state
             n (own': bool) (svw: View.t) (ing: bool) (tks: NatMap.t nat) : sProp n :=
    (STSRC {(own', svw, ing, (key_set tks))})%S
  .

  Definition ticket_lock_inv n : sProp n :=
    (∃ (own' ing: τ{bool, n}) (V: τ{View.t, n}) (κm: τ{nat, n})
      (l: τ{list thread_id, n}) (tks: τ{NatMap.t nat, n}) (now next: τ{nat, n}) (myt: τ{thread_id, n}),
      (ticket_lock_inv_tks n tks)
      ∗ (ticket_lock_inv_mem n V κm now next myt)
      ∗ (ticket_lock_inv_state n own' V ing tks)
      ∗ ((⌜own' = true⌝
          ∗ ((⌜ing = false⌝ ∗ (ticket_lock_inv_locked n l tks now next myt V κm))
            ∨ (⌜ing = true⌝ ∗ (ticket_lock_inv_unlocking n l tks now next myt κm))))
        ∨ (⌜own' = false⌝
          ∗ ⌜ing = false⌝
          ∗ ((ticket_lock_inv_unlocked0 n l tks now next myt V κm)
            ∨ (ticket_lock_inv_unlocked1 n l tks now next myt V κm)))))%S.

  Lemma ticket_lock_inv_eq n :
    ⟦ticket_lock_inv n, n⟧ ⊣⊢
    ∃ (own' ing: bool) (V: View.t) (κm: nat)
      (l: list thread_id) (tks: NatMap.t nat) (now next: nat) (myt: thread_id),
      ⟦ticket_lock_inv_tks n tks, n⟧
      ∗ ⟦ticket_lock_inv_mem n V κm now next myt,n⟧
      ∗ ⟦ticket_lock_inv_state n own' V ing tks,n⟧
      ∗ ((⌜own' = true⌝
          ∗ ((⌜ing = false⌝ ∗ ⟦ticket_lock_inv_locked n l tks now next myt V κm,n⟧)
            ∨ (⌜ing = true⌝ ∗ ⟦ticket_lock_inv_unlocking n l tks now next myt κm,n⟧)))
        ∨ (⌜own' = false⌝
          ∗ ⌜ing = false⌝
          ∗ (⟦ticket_lock_inv_unlocked0 n l tks now next myt V κm,n⟧
            ∨ ⟦ticket_lock_inv_unlocked1 n l tks now next myt V κm,n⟧))).
  Proof. f_equiv. Qed.

  Ltac desas H name := iEval (red_tl; simpl) in H; iDestruct H as (name) H.

  Lemma unlocking_contra
        n tid l tks now next myt κm
        (FIND: NatMap.find tid tks = Some now)
    :
    ⟦ticket_lock_inv_unlocking n l tks now next myt κm, n⟧
      -∗ ⌜False⌝.
  Proof.
    iIntros "I". unfold ticket_lock_inv_unlocking. red_tl_all. ss.
    iDestruct "I" as "[_ [%I2 _]]". exfalso.
    hexploit (tkqueue_val_range_l I2 _ FIND). i. lia.
  Qed.

  Lemma unlocking_myturn
        n tid l tks now next myt κm
        mytk o
        (FIND: NatMap.find tid tks = Some mytk)
    :
    (monoWhite monok mypreord (mytk, o))
      -∗
      ⟦ticket_lock_inv_unlocking n l tks now next myt κm, n⟧
      -∗ ⌜False⌝.
  Proof.
    iIntros "MYT I". rewrite ticket_lock_inv_unlocking_eq.
    iDestruct "I" as "(_ & %I2 & _ & I3)".
    iPoseProof (black_white_compare with "MYT I3") as "%LE". exfalso.
    hexploit (tkqueue_val_range_l I2 _ FIND). i. inv LE; try lia.
  Qed.

  Lemma unlocked0_contra
        n tid l tks now next myt mytk V κm
        (FIND: NatMap.find tid tks = Some mytk)
    :
    ⟦ticket_lock_inv_unlocked0 n l tks now next myt V κm, n⟧ -∗ ⌜False⌝.
  Proof.
    iIntros "I". unfold ticket_lock_inv_unlocked0. red_tl_all; simpl.
    iDestruct "I" as "[_ [%I2 _]]". exfalso. des; clarify.
  Qed.

  Lemma unlocked1_mono
        n l tks now next myt V κm:
    ⟦ticket_lock_inv_unlocked1 n l tks now next myt V κm, n⟧
    -∗ ((⌜tkqueue l tks now next⌝)
        ∗ (monoWhite monok mypreord (now, Tkst.b κm))).
  Proof.
    iIntros "I". unfold ticket_lock_inv_unlocked1. red_tl_all; simpl.
    do 3 (iDestruct "I" as "[% I]"; red_tl_all; simpl).
    iDestruct "I" as "(_ & _ & % & _ & % & I)". red_tl_all; simpl.
    iDestruct "I" as "[MB [OB _]]".
    iSplit. auto. iPoseProof (black_white with "MB") as "#MYTURN". done.
  Qed.

  Lemma unlocked1_myturn
        n tid l tks now next myt V κm
        mytk o
        κa γs
        (FIND: NatMap.find tid tks = Some mytk)
    :
    (OwnM (maps_to_res tid (◯E ([κa; γs] : leibnizO _))))
    -∗ (monoWhite monok mypreord (mytk, o))
    -∗ ⟦ticket_lock_inv_unlocked1 n l tks now next myt V κm, n⟧
    -∗ (⌜now = mytk⌝ ∗ κm -(2)-◇ κa).
  Proof.
    iIntros "MY MONO I".
    unfold ticket_lock_inv_unlocked1.
    desas "I" yourt; desas "I" κay; desas "I" waits. red_tl_all.
    iDestruct "I" as "(_ & % & %I1 & _ & [% I2])". clarify. red_tl_all; simpl.
    iDestruct "I2" as "(MONB & _ & _ & _ & _ & #LINK & MY2)".
    unfold maps_to.
    (* do 2 iDestruct "I" as "[% I]". iDestruct "I" as "[_ [%I1 [%I2 [_ [_ I]]]]]".
    do 3 iDestruct "I" as "[% I]". iDestruct "I" as "[MB _]". *)
    iPoseProof (black_white_compare with "MONO MONB") as "%LE".
    hexploit (tkqueue_val_range_l I1 _ FIND). i. inv LE; auto. lia. iSplit. auto.
    exploit tkqueue_inv_unique. eauto. eauto. inv I1. clarify. apply FIND0. i; clarify.
    iCombine "MY MY2" gives %EQ.
    rewrite discrete_fun_singleton_op discrete_fun_singleton_valid in EQ.
    by apply excl_auth_agree_L in EQ as [= -> ->].
  Qed.

  Lemma locked_contra
        n tid l tks now next myt V κm
        (FIND: NatMap.find tid tks = Some now)
    :
    ⟦ticket_lock_inv_locked n l tks now next myt V κm, n⟧
      -∗ ⌜False⌝.
  Proof.
    unfold ticket_lock_inv_locked. red_tl_all; simpl.
    iIntros "I". iDestruct "I" as "[_ [%I2 _]]". exfalso.
    hexploit (tkqueue_val_range_l I2 _ FIND). clear. i. lia.
  Qed.

  Lemma locked_myturn
        n tid l tks now next myt V κm
        mytk o
        (FIND: NatMap.find tid tks = Some mytk)
    :
    (monoWhite monok mypreord (mytk, o))
    -∗ ⟦ticket_lock_inv_locked n l tks now next myt V κm, n⟧
    -∗ ⌜False⌝.
  Proof.
    iIntros "MYT I". unfold ticket_lock_inv_locked; red_tl_all.
    iDestruct "I" as "(_ & %I2 & _ & I3)".
    iPoseProof (black_white_compare with "MYT I3") as "%LE". exfalso.
    hexploit (tkqueue_val_range_l I2 _ FIND). i. inv LE; try lia.
  Qed.

  Lemma mytk_find_some n tid mytk tks:
    (OwnM (◯ (NatMapRA.singleton tid mytk)))
      ∗ ⟦ticket_lock_inv_tks n tks, n⟧
      -∗ ⌜NatMap.find tid tks = Some mytk⌝.
  Proof.
    unfold ticket_lock_inv_tks. red_tl.
    iIntros "[MYTK TKS]". iDestruct "TKS" as "[TKS0 _]".
    iApply (NatMapRA_find_some with "TKS0 MYTK").
  Qed.

  Lemma yourturn_range i
        tid tks mytk now next own' ing l myt V κm
        (FIND : NatMap.find tid tks = Some mytk)
        (NEQ : mytk ≠ now)
  :
    ⟦(⌜own' = true⌝
        ∗ (⌜ing = false⌝ ∗ (⤉ ticket_lock_inv_locked i l tks now next myt V κm)
          ∨ ⌜ing = true⌝ ∗ (⤉ ticket_lock_inv_unlocking i l tks now next myt κm))
      ∨ ⌜own' = false⌝ ∗ ⌜ing = false⌝
        ∗ ((⤉ ticket_lock_inv_unlocked0 i l tks now next myt V κm)
          ∨ (⤉ ticket_lock_inv_unlocked1 i l tks now next myt V κm)))%S, 1+i⟧
    ⊢
    (⌜now < mytk⌝).
  Proof.
    red_tl_all.
    iIntros "[[%CT [[%IF I] | [%IT I]]] | [%CF [%IF [I | I]]]]".
    { unfold ticket_lock_inv_locked. red_tl_all. iDestruct "I" as "[_ [%I1 _]]".
      hexploit (tkqueue_val_range_l I1 _ FIND). i. iPureIntro. lia. }
    { rewrite ticket_lock_inv_unlocking_eq. iDestruct "I" as "[_ [%I1 _]]".
      hexploit (tkqueue_val_range_l I1 _ FIND). i. iPureIntro. lia. }
    { iPoseProof (unlocked0_contra with "I") as "%FF". eauto. inv FF. }
    { iPoseProof (unlocked1_mono with "I") as "[%I1 _]".
      hexploit (tkqueue_val_range_l I1 _ FIND). i. iPureIntro. lia. }
  Qed.

  Lemma Ticketlock_enqueue_spec i tid tvw
  :
  ⟦((⤉ syn_inv i N_Ticketlock_w (ticket_lock_inv i))
    ∗ (syn_tgt_interp_as i sndl (fun m => (s_wmemory_black_strong inrp m : sProp i)))
    ∗ (⤉ TID(tid))
    ∗ (⤉ Duty(tid) []))%S, 1+i⟧
  ∗ (∀ (Vfaa: View.t) (mytk κa γs: nat),
      ⟦((⤉ Duty(tid)[(κa, 0, ▿ γs tt)])
      ∗ (⤉ ◇[κa](4, 1))
      ∗ (⤉ ◆[κa, 4 + mytk])
      ∗ ⌜View.le tvw Vfaa⌝
      ∗ (⤉ ➢ (maps_to_res tid (◯E ([κa; γs] : leibnizO _))))
      ∗ (⤉ ➢ (◯ (NatMapRA.singleton tid (mytk : nat)))))%S, 1+i⟧
    -∗
      ⟦(syn_wpsim (S i) tid ⊤ (fun rs rt => (⤉ (syn_term_cond i tid _ rs rt))%S) true true
      (ITree.iter
        (λ _ : (),
            trigger Yield;;;
            ` x_ : bool * View.t * bool * NatMap.t () <- trigger (Get id);;
            (let (y, _) := x_ in
            let (y1, _) := y in let (own0, _) := y1 in if own0 then Ret (inl ()) else Ret (inr ()))) ();;;
      ` x_ : bool * View.t * bool * NatMap.t () <- trigger (Get id);;
      (let (y, ts) := x_ in
        let (y0, ing0) := y in
        let (_, tvw_lock) := y0 in
        if ing0
        then ` x : _ <- trigger (Choose void);; Empty_set_rect (λ _ : void, thread nat (sE AbsLockW.st) View.t) x
        else
        ` x_0 : {tvw' : View.t | View.le (View.join tvw tvw_lock) tvw'} <-
        trigger (Choose {tvw' : View.t | View.le (View.join tvw tvw_lock) tvw'});;
        (let (tvw', _) := x_0 in
          trigger (Put (true, tvw_lock, false, NatMap.remove (elt:=()) tid ts));;;
          trigger
            (Fair
              (λ i0 : nat,
                  if tid_dec i0 tid
                  then Flag.success
                  else if NatMapP.F.In_dec (NatMap.remove (elt:=()) tid ts) i0 then Flag.fail else Flag.emp));;;
          trigger Yield;;; Ret tvw')))
      (` a : View.t <- OMod.close_itree TicketLockW.omod WMem.mod (TicketLockW.lock_loop (nat2c mytk) Vfaa);;
      OMod.close_itree TicketLockW.omod WMem.mod (trigger Yield;;; Ret a))), 1 + i⟧)
  -∗
    ⟦syn_wpsim (S i) tid ⊤ (fun rs rt => (⤉ syn_term_cond i tid _ rs rt)%S) false false
      (AbsLockW.lock_fun tvw)
      (OMod.close_itree TicketLockW.omod WMem.mod (TicketLockW.lock_fun tvw)), 1 + i⟧.
  Proof.
    red_tl_all. iEval (rewrite red_syn_inv; rewrite ! red_syn_wpsim; rewrite red_syn_tgt_interp_as). simpl.
    iIntros "((#TINV & #WMEM & TID & DUTY) & SIM)".

    unfold fn2th. simpl. unfold AbsLockW.lock_fun, TicketLockW.lock_fun. rred2r. lred2r.
    iApply (wpsim_sync with "[DUTY]"). auto. iFrame. iIntros "DUTY _". lred. rred2r.

    iApply wpsim_tidL. lred. rred2r.

    iInv "TINV" as "TI" "TI_CLOSE".
    iEval (rewrite /= ticket_lock_inv_eq) in "TI". iDestruct "TI" as (own' ing V κm l tks now next myt) "(TKS & MEM & ST & CASES)".
    iEval (unfold ticket_lock_inv_state; red_tl_all; ss) in "ST". lred2r. rred2r.
    iApply wpsim_getL. iSplit. auto. lred.
    iApply (wpsim_modifyL with "ST"). iIntros "ST".

    iEval (unfold ticket_lock_inv_mem; red_tl_all; ss) in "MEM".
    iDestruct "MEM" as "(MEM1 & MEM2 & MEM3 & MEM4 & MEM5 & #MEM6)".
    iApply (WMem_faa_fun_spec with "[WMEM MEM2] [-]"). auto.
    { solve_ndisj. } ss. iFrame. auto.
    iIntros (rv) "[%Vfaa [% [MEM2 VLE]]]". clarify. rred2r. iApply wpsim_tauR. rred2r.

    iEval (unfold ticket_lock_inv_tks; red_tl_all; simpl) in "TKS".
    iDestruct "TKS" as "[TKS0 [TKS1 [TKS2 TKS3]]]".
    set (tks' := NatMap.add tid next tks).

    iAssert (⌜NatMap.find tid tks = None⌝)%I as "%FINDNONE".
    { destruct (NatMap.find tid tks) eqn:FIND; auto.
      iPoseProof (natmap_prop_sum_in with "TKS2") as "FALSE".
      eauto. red_tl. iPoseProof (own_thread_unique with "TID FALSE") as "%FALSE". auto.
    }

    iPoseProof (NatMapRA_add with "TKS0") as ">[TKS0 MYTK]". eauto. instantiate (1:=next).
    iAssert (St_src (own', V, ing, (key_set tks')))%I with "[ST]" as "ST".
    { subst tks'. rewrite key_set_pull_add_eq. iFrame. }
    iPoseProof ((FairRA.whites_unfold _ (fun id => ~ NatMap.In id tks') _ (i:=tid)) with "TKS1") as "[TKS1 MYTRI]".
    { subst tks'. i. ss. des; clarify.
      - ii. apply IN. destruct (tid_dec j tid); clarify.
        apply NatMapP.F.not_find_in_iff in H; clarify. apply NatMapP.F.add_in_iff; auto.
      - apply NatMapP.F.not_find_in_iff; auto.
    }
    { subst tks'. ii. apply H. apply NatMapP.F.add_in_iff. auto. }

    iPoseProof ((OwnMs_unfold (fun id => ~ NatMap.In id tks') _ (i:=tid)) with "TKS3") as "[TKS3 MYNUM]".
    { subst tks'. i. ss. des; clarify.
      - ii. apply IN. destruct (tid_dec j tid); clarify.
        apply NatMapP.F.not_find_in_iff in H; clarify. apply NatMapP.F.add_in_iff; auto.
      - apply NatMapP.F.not_find_in_iff; auto.
    }
    { subst tks'. ii. apply H. apply NatMapP.F.add_in_iff. auto. }

    iAssert (natmap_prop_sum tks' (λ tid0 _ : nat, own_thread tid0))%I with "[TID TKS2]" as "TKS2".
    { subst tks'. iApply (natmap_prop_sum_add with "TKS2"). iFrame. }

    iMod (alloc_obligation (4 + next) (3 + (next - now))) as "(%κa & #LO & PC & PO)".
    iPoseProof (pc_split _ _ 3 with "PC") as "[PC2 PC1]".
    iPoseProof (pc_split _ _ 1 with "PC2") as "[PC2 PC3]".
    iAssert (#=> ◇[κa](4, 2))%I with "[PC3]" as "> PC3".
    { destruct next; [ auto | ]. iMod (pc_drop _ 4 _ _ 2 with "PC3") as "PC3". auto. auto. }
    iPoseProof (pc_split _ _ 1 with "PC3") as "[PC3 PC4]".
    iEval (rewrite <- Qp.half_half) in "PO".
    iPoseProof (pending_split _ (1/2) (1/2) with "PO") as "[PO1 PO2]".
    iMod (pc_drop _ 1 _ _ 1 with "PC4") as "PC4". auto. Unshelve. all: try lia.
    iMod (OneShots.alloc) as "[%γs PEND]".
    iMod (duty_add with "[DUTY PC4 PO2] []") as "DUTY". iFrame.
    { iModIntro. instantiate (1:=(▿ γs tt)%S). ss. red_tl_all. iIntros "#?". iModIntro; auto. }
    iPoseProof (duty_delayed_tpromise with "DUTY") as "#DPRM". simpl; left; auto.

    iPoseProof (OwnM_Upd with "MYNUM") as "> MYNUM".
    { eapply discrete_fun_singleton_update.
      (* excl_auth_update. *)
      instantiate (1:=(●E ([κa; γs] : leibnizO _) ⋅ _)).
      eapply excl_auth_update.
    }
    rewrite <- discrete_fun_singleton_op. iDestruct "MYNUM" as "[MYNB MYNW]".

    iAssert (=|S i|=(fairI (S i))={⊤ ∖ ↑N_Ticketlock_w}=> (prop i (ticket_lock_inv i)))
      with "[- DUTY TI_CLOSE MYTK PC3 MYNW VLE SIM]" as "> TI".
    { rewrite /= ticket_lock_inv_eq. repeat iExists _.
      unfold ticket_lock_inv_tks, ticket_lock_inv_mem, ticket_lock_inv_state; red_tl_all; simpl.
      iSplitL "TKS0 TKS1 TKS2 TKS3". iFrame. iModIntro; auto.
      iSplitL "MEM1 MEM2 MEM3 MEM4 MEM5 MEM6".
      iFrame "MEM1 MEM3 MEM4 MEM5".
      iModIntro. iSplit; auto.
      { instantiate (1:=(S next)). replace (nat2c (S next)) with (Const.add (nat2c next) const_1).
        ss. unfold nat2c. ss. unfold BinIntDef.Z.of_nat. des_ifs. ss. rewrite Z.add_comm.
        rewrite Pos2Z.add_pos_pos. rewrite Pplus_one_succ_l. econs.
      }
      iSplitL "ST"; [iFrame | ]. iModIntro; auto.
      iDestruct "CASES" as "[[%TRUE [[%IF INV] | [%IT INV]]] | [%FALSE [%IF [INV | INV]]]]"; subst.
      { iPoseProof (FairRA.white_mon with "MYTRI") as ">MYTRI".
        { instantiate (1:=Ord.from_nat (next - (S now))). ss. apply Ord.lt_le. apply Ord.omega_upperbound. }
        iModIntro. iLeft. iSplit; auto. iLeft. iSplit; auto.
        unfold ticket_lock_inv_locked; red_tl_all; simpl.
        iDestruct "INV" as "(INV0 & %INV1 & INV2 & INV3)". iFrame.
        iSplit.
        { iPureIntro. apply tkqueue_enqueue; eauto. }
        iPoseProof (natmap_prop_sum_add with "[INV2]") as "INV2". iFrame.
        iApply "INV2". red_tl_all; ss. iFrame. repeat (iExists _; red_tl). ss. iFrame.
        iSplit; auto. iSplit; red_tl_all; auto.
      }
      { iPoseProof (FairRA.white_mon with "MYTRI") as ">MYTRI".
        { instantiate (1:=Ord.from_nat (next - (S now))). ss. apply Ord.lt_le. apply Ord.omega_upperbound. }
        iModIntro. iLeft. iSplit; auto. iRight. iSplit; auto.
        unfold ticket_lock_inv_unlocking; red_tl_all; simpl.
        iDestruct "INV" as "(INV0 & %INV1 & INV2 & INV3)". iFrame.
        iSplit.
        { iPureIntro. apply tkqueue_enqueue; eauto. }
        iPoseProof (natmap_prop_sum_add with "[INV2]") as "INV2". iFrame.
        iApply "INV2". red_tl_all; ss. iFrame.
        repeat (iExists _; red_tl). red_tl_all. simpl. iFrame "∗#".
      }
      { iPoseProof (FairRA.white_mon with "MYTRI") as ">MYTRI".
        { instantiate (1:=Ord.from_nat (next - now)). ss. apply Ord.lt_le. apply Ord.omega_upperbound. }
        iPoseProof (activate_tpromise with "DPRM PO1") as "> #[PRM AO]".
        unfold ticket_lock_inv_unlocked0, ticket_lock_inv_unlocked1. red_tl_all.
        iDestruct "INV" as "(INV0 & %INV1 & INV2)". des; clarify.
        iPoseProof ((black_updatable _ _ _ (next, Tkst.b κm)) with "INV2") as ">INV2". right. econs; eauto.
        iAssert (#=> ◇[κa](4, 1))%I with "[PC2]" as "> PC2".
        { destruct next. auto. iMod (pc_drop _ 4 _ _ 1 with "PC2") as "PC2". auto. auto. Unshelve. lia. }
        iPoseProof (link_new with "[MEM6 PC2]") as "> [LINK _]".
        { iSplitR. iApply "MEM6". instantiate (1:=2). simpl. done. }
        Unshelve. all: try exact 0.
        iModIntro. iRight. repeat (iSplit; auto). iRight.
        iExists tid; red_tl; iExists κa; red_tl; iExists []; red_tl; iFrame.
        iSplit; auto. iSplit; auto.
        { iPureIntro. apply tkqueue_enqueue; eauto. econs; auto. }
        iSplitR.
        { red_tl_all. subst tks'. rewrite nm_find_none_rm_add_eq. ss. ss. }
        { iExists _; red_tl_all; iFrame. repeat iSplit; auto. }
      }
      { iPoseProof (FairRA.white_mon with "MYTRI") as ">MYTRI".
        { instantiate (1:=Ord.from_nat (next - now)). ss. apply Ord.lt_le. apply Ord.omega_upperbound. }
        unfold ticket_lock_inv_unlocked1.
        desas "INV" yourt; desas "INV" κay; desas "INV" waits; red_tl_all.
        iDestruct "INV" as "(INV0 & %INV1 & %INV2 & INV3 & INV4)".
        iDestruct "INV4" as (?) "INV4". red_tl_all; simpl. iDestruct "INV4" as "(INV4 & #INV5 & INV6)".
        hexploit tkqueue_range; eauto. i.
        iAssert (#=(ObligationRA.edges_sat)=> κay -(0)-◇ κa)%I with "[PC2]" as "> LINK".
        { inv H.
          { inv INV2. clarify. hexploit tkqueue_range; eauto. i; lia. }
          iAssert (#=> ◇[κa](5 + now, 1))%I with "[PC2]" as "> PC2".
          { destruct H0. auto. iMod (pc_drop _ (5 + now) _ _ 1 with "PC2") as "PC2". auto. auto. Unshelve. lia. }
          iPoseProof (link_new with "[PC2]") as "[LINK _]". iSplit. iApply "INV5". instantiate (1:=0). done. iFrame "LINK".
        }
        iModIntro. iRight. repeat (iSplit; auto). iRight.
        iExists yourt; red_tl; iExists κay; red_tl; iExists (waits ++ [tid]). red_tl_all. iFrame.
        iSplit. iPureIntro. clarify.
        iSplit. iPureIntro. apply tkqueue_enqueue; eauto.
        iSplitR "INV4 INV6".
        { subst tks'. rewrite <- nm_add_rm_comm_eq.
          iPoseProof (natmap_prop_sum_add with "[INV3]") as "INV3". iFrame.
          iApply "INV3". red_tl_all; ss. iFrame.
          repeat (iExists _; red_tl). simpl. iFrame. repeat iSplit; auto. red_tl_all. auto.
          ii; clarify. inv INV2. clarify. unfold TicketLockW.tk in *.
          rewrite FINDNONE in FIND; clarify.
        }
        iExists _. red_tl_all. iFrame. simpl. done.
      }
    }

    iMod ("TI_CLOSE" with "TI") as "_".
    iPoseProof ("SIM" $! Vfaa next κa γs with "[DUTY MYTK PC3 MYNW VLE]") as "SIM".
    { red_tl_all. simpl. iFrame. auto. }
    rewrite red_syn_wpsim. done.
    Unshelve. exact 0.
  Qed.

  Lemma lock_yourturn_yield i
        g0 g1
        (ps pt: bool)
        (src: itree (threadE _  (Mod.state AbsLockW.mod)) View.t)
        (tgt: itree (threadE _  (OMod.closed_state TicketLockW.omod (WMem.mod))) View.t)
        (tid mytk now: nat)
        tks next l myt own' V ing
        (NEQ: mytk <> now)
        κa γs κm
    :
  ⟦(⤉ (➢ (◯ (NatMapRA.singleton tid (mytk : nat))))
    ∗ ⤉ (➢ (maps_to_res tid (◯E ([κa; γs] : leibnizO _))))
    ∗ ⤉ (ticket_lock_inv_tks i tks)
    ∗ ⤉ (ticket_lock_inv_mem i V κm now next myt)
    ∗ ⤉ (ticket_lock_inv_state i own' V ing tks)
    ∗ (⤉ Duty(tid) [(κa, 0, (▿ γs ())%S)])
    ∗ (⌜own' = true⌝
      ∗ (⌜ing = false⌝ ∗ (⤉ ticket_lock_inv_locked i l tks now next myt V κm)
        ∨ ⌜ing = true⌝ ∗ (⤉ ticket_lock_inv_unlocking i l tks now next myt κm))
      ∨ ⌜own' = false⌝ ∗ ⌜ing = false⌝
      ∗ ((⤉ ticket_lock_inv_unlocked0 i l tks now next myt V κm)
        ∨ (⤉ ticket_lock_inv_unlocked1 i l tks now next myt V κm)))
    ∗ ((⤉ ticket_lock_inv i) =| S i |={ ⊤ ∖ ↑N_Ticketlock_w, ⊤ }=∗ emp))%S, 1+i⟧
  ∗ (⟦((⤉ Duty(tid) [(κa, 0, (▿ γs ())%S)])
    ∗ ⤉ (➢ (◯ (NatMapRA.singleton tid (mytk : nat) : NatMapRA.t nat)))
    ∗ ⤉ (➢ (maps_to_res tid (◯E ([κa; γs] : leibnizO _))))
    ∗ €)%S, 1+i⟧
    -∗ wpsim (STATESRC:=@SRA.in_subG Γ Σ sub _ _STATESRC) (STATETGT:=@SRA.in_subG Γ Σ sub _ _STATETGT)
      (S i) tid ⊤ g0 g1 (fun rs rt => (⟦⤉ syn_term_cond i tid View.t rs rt, 1+i⟧)%S) ps true
        (trigger Yield;;; src) (tgt))
  ⊢ wpsim (STATESRC:=@SRA.in_subG Γ Σ sub _ _STATESRC) (STATETGT:=@SRA.in_subG Γ Σ sub _ _STATETGT)
    (S i) tid (⊤ ∖ ↑N_Ticketlock_w) g0 g1 (fun rs rt => (⟦⤉ syn_term_cond i tid View.t rs rt, 1+i⟧)%S) ps pt
    (trigger Yield;;; src)
    (trigger Yield;;; tgt).
  Proof.
    red_tl_all. simpl. iIntros "((MY1 & MY2 & TKS & MEM & STATE & DUTY & CASES & TI_CLOSE) & SIM)".
    iPoseProof (mytk_find_some with "[MY1 TKS]") as "%FIND". iFrame.
    iDestruct "CASES" as "[[%TRUE [[%IF INV] | [%IT INV]]] | [%FALSE [%IF [INV | INV]]]]"; subst.
    { iEval (unfold ticket_lock_inv_locked; red_tl_all) in "INV".
      iDestruct "INV" as "(INV1 & INV2 & INV3 & INV4)".

      iPoseProof (natmap_prop_sum_find_remove with "INV3") as "[INV3 CLOSE]". done.
      iEval (red_tl_all; simpl) in "INV3". iDestruct "INV3" as "[INV3 [%κam INV5]]".
      iEval (red_tl) in "INV5". iDestruct "INV5" as "[%γsm INV5]". iEval (red_tl_all) in "INV5". simpl.
      iDestruct "INV5" as "(INV6 & INV7 & INV8 & INV9 & INV10 & INV11)".
      iCombine "INV11 MY2" gives %MY.
      rewrite discrete_fun_singleton_op in MY.
      apply discrete_fun_singleton_valid, excl_auth_agree_L in MY as [= -> ->].

      iApply (wpsim_yieldR_gen_pending with "[DUTY] [INV8]"). auto.
      4: iFrame. 4:{ iApply (pps_cons_fold with "[INV8]"). iSplitL; iFrame. iApply pps_nil. }
      { instantiate (1:=[]). rewrite app_nil_r. done. }
      { eauto using Forall2. }
      auto. auto.
      iIntros "DUTY CRED [PEND _] _".
      iPoseProof ("CLOSE" with "[INV3 INV6 INV7 PEND INV9 INV10 INV11]") as "CLOSE".
      { red_tl_all. simpl. iFrame. iExists _. red_tl. iExists _. red_tl_all. iFrame. }
      iPoseProof ("TI_CLOSE" with "[TKS MEM STATE INV1 INV2 INV4 CLOSE]") as "CLOSE".
      { rewrite ticket_lock_inv_eq. do 9 iExists _. iFrame.
        iLeft. iSplit; auto. iLeft. iSplit; auto.
        unfold ticket_lock_inv_locked. red_tl_all. iFrame.
      }
      rewrite red_syn_fupd. iMod "CLOSE". iModIntro.
      iApply ("SIM" with "[DUTY MY1 MY2 CRED]"). iFrame.
    }
    { iEval (unfold ticket_lock_inv_unlocking; red_tl_all) in "INV".
      iDestruct "INV" as "(INV1 & INV2 & INV3 & INV4)".

      iPoseProof (natmap_prop_sum_find_remove with "INV3") as "[INV3 CLOSE]". done.
      iEval (red_tl_all; simpl) in "INV3". iDestruct "INV3" as "[INV3 [%κam INV5]]".
      iEval (red_tl) in "INV5". iDestruct "INV5" as "[%γsm INV5]". iEval (red_tl_all) in "INV5". simpl.
      iDestruct "INV5" as "(INV6 & INV7 & INV8 & INV9 & INV10 & INV11)".
      iCombine "INV11 MY2" gives %MY.
      rewrite discrete_fun_singleton_op in MY.
      apply discrete_fun_singleton_valid, excl_auth_agree_L in MY as [= -> ->].

      iApply (wpsim_yieldR_gen_pending with "DUTY [INV8]"). auto.
      4:{ iApply (pps_cons_fold with "[$INV8]"). iApply pps_nil. }
      { erewrite app_nil_r. done. }
      { eauto using Forall2. }
      auto. auto.
      iIntros "DUTY CRED [PEND _] _".
      iPoseProof ("CLOSE" with "[INV3 INV6 INV7 PEND INV9 INV10 INV11]") as "CLOSE".
      { red_tl_all. simpl. iFrame. iExists _. red_tl. iExists _. red_tl_all. iFrame. }
      iPoseProof ("TI_CLOSE" with "[TKS MEM STATE INV1 INV2 INV4 CLOSE]") as "CLOSE".
      { rewrite ticket_lock_inv_eq. do 9 iExists _. iFrame.
        iLeft. iSplit; auto. iRight. iSplit; auto.
        unfold ticket_lock_inv_unlocking. red_tl_all. iFrame.
      }
      rewrite red_syn_fupd. iMod "CLOSE". iModIntro.
      iApply ("SIM" with "[DUTY MY1 MY2 CRED]"). iFrame.
    }
    { unfold ticket_lock_inv_unlocked0. red_tl. iDestruct "INV" as "[INV0 [%INV1 INV2]]". exfalso. des; clarify. }
    { iEval (unfold ticket_lock_inv_unlocked1) in "INV".
      desas "INV" yourt. desas "INV" κay. desas "INV" waits. red_tl_all.
      iDestruct "INV" as "(INV1 & %INV2 & %INV3 & INV4 & INV5)".
      hexploit (tkqueue_dequeue INV3). eapply INV2. i.
      assert (NOTMT: tid <> yourt).
      { ii. clarify. inv INV3; ss. clarify. setoid_rewrite FIND in FIND0. inv FIND0. }

      iPoseProof (natmap_prop_sum_find_remove with "INV4") as "[INV4 CLOSE]".
      { rewrite nm_find_rm_neq. done. done. }
      iEval (red_tl_all; simpl) in "INV4". iDestruct "INV4" as "[INV4 [%κam INV3]]".
      iEval (red_tl) in "INV3". iDestruct "INV3" as "[%γsm INV3]". iEval (red_tl_all) in "INV3". simpl.
      iDestruct "INV3" as "(INV6 & INV7 & INV8 & INV9 & INV10 & INV11 & INV12)".
      iCombine "INV11 MY2" gives %MY.
      rewrite discrete_fun_singleton_op in MY.
      apply discrete_fun_singleton_valid, excl_auth_agree_L in MY as [= -> ->].

      iApply (wpsim_yieldR_gen_pending with "DUTY [INV8]"). auto.
      4:{ iApply (pps_cons_fold with "[$INV8]"). iApply pps_nil. }
      { erewrite app_nil_r. done. }
      { eauto using Forall2. }
      auto. auto.
      iIntros "DUTY CRED [PEND _] _".
      iPoseProof ("CLOSE" with "[INV4 INV6 INV7 PEND INV9 INV10 INV11 INV12]") as "CLOSE".
      { red_tl_all. simpl. iFrame. iExists _. red_tl. iExists _. red_tl_all. iFrame. }
      iPoseProof ("TI_CLOSE" with "[TKS MEM STATE INV1 INV5 CLOSE]") as "CLOSE".
      { rewrite ticket_lock_inv_eq. do 9 iExists _. iFrame.
        iRight. iSplit; auto. iSplit; auto. iRight.
        unfold ticket_lock_inv_unlocked1. red_tl_all. do 3 (iExists _; red_tl). red_tl_all. iFrame.
        instantiate (1:=l). iSplit; auto.
      }
      rewrite red_syn_fupd. iMod "CLOSE". iModIntro.
      iApply ("SIM" with "[DUTY MY1 MY2 CRED]"). iFrame.
    }
  Qed.

  Lemma lock_yourturn_acq i
        g0 g1
        (ps pt: bool)
        (src: itree (threadE _  (Mod.state AbsLockW.mod)) View.t)
        tgt
        (tid mytk now: nat)
        next myt V
        tview
        (NEQ: now < mytk)
        κm
  :
  ⟦(⤉ (ticket_lock_inv_mem i V κm now next myt)
    ∗ (syn_tgt_interp_as i sndl (fun m : WMem.t => s_wmemory_black_strong inrp m : sProp i)))%S, 1+i⟧
  ∗ (∀ Vfaa val,
      ((⌜View.le tview Vfaa⌝)
        ∗ (⌜val <> mytk⌝)
        ∗ ⟦(⤉ (ticket_lock_inv_mem i V κm now next myt))%S, 1+i⟧)
      -∗ wpsim (STATESRC:=@SRA.in_subG Γ Σ sub _ _STATESRC)
        (S i) tid (⊤ ∖ ↑N_Ticketlock_w) g0 g1 (fun rs rt => (⟦⤉ syn_term_cond i tid View.t rs rt, 1+i⟧)%S) ps true
        (src) (tgt (Vfaa, nat2c val)))
  ⊢ wpsim (STATESRC:=@SRA.in_subG Γ Σ sub _ _STATESRC)
    (S i) tid (⊤ ∖ ↑N_Ticketlock_w) g0 g1 (fun rs rt => (⟦⤉ syn_term_cond i tid View.t rs rt, 1+i⟧)%S) ps pt
    (src)
    (` r : View.t * Const.t <-
    map_event (OMod.emb_callee TicketLockW.omod WMem.mod)
      (WMem.load_fun (tview, TicketLockW.now_serving, Ordering.acqrel));;
    ` x : Any.t <- map_event (OMod.emb_callee TicketLockW.omod WMem.mod) (Ret (Any.upcast r));;
    ` x0 : View.t * Const.t <- (tau;; unwrap (Any.downcast x));;
    (tgt x0)).
  Proof.
    red_tl. rewrite red_syn_tgt_interp_as. iIntros "((MEM & #WMEM) & SIM)".
    iEval (unfold ticket_lock_inv_mem) in "MEM". red_tl_all.
    iDestruct "MEM" as "(MEM1 & MEM2 & MEM3 & MEM4 & MEM5)".

    iApply (WMem_load_fun_spec with "[MEM1] [-]"). auto.
    { solve_ndisj. }
    iSplit; auto.

    iIntros (rv) "(%V3 & %v & % & MEM1 & POST)". des. clarify.
    iDestruct "POST" as "[[%SUCC _] | [%FAIL %]]".
    { des. rr in SUCC. des. clarify.
      rred2r. iApply wpsim_tauR. rred2r. iApply ("SIM" with "[MEM1 MEM2 MEM3 MEM4 MEM5]").
      iSplit; auto. iSplit; auto. iPureIntro. lia.
      unfold ticket_lock_inv_mem. red_tl_all. iFrame.
    }
    des. rr in FAIL. clarify.
    rred2r. iApply wpsim_tauR. rred2r. iApply ("SIM" with "[MEM1 MEM2 MEM3 MEM4 MEM5]").
    iSplit; auto. iSplit; auto. iPureIntro; lia. unfold ticket_lock_inv_mem. red_tl_all. iFrame.
  Qed.

  Lemma correct_lock n tid
  :
    ⊢ ⟦(∀ (tvw : τ{View.t, 1+n}),
        ((⤉ syn_inv n N_Ticketlock_w (ticket_lock_inv n))
        ∗ (syn_tgt_interp_as n sndl (fun m => ((s_wmemory_black_strong inrp m))))
        ∗ TID(tid)
        ∗ (⤉ Duty(tid) []))
      -∗
      syn_wpsim (S n) tid ⊤
      (fun rs rt => (⤉ (syn_term_cond n tid _ rs rt))%S)
      false false
      (AbsLockW.lock_fun tvw)
      (OMod.close_itree TicketLockW.omod WMem.mod (TicketLockW.lock_fun tvw)))%S, 1+n⟧.
  Proof.
    red_tl_all. iIntros (tvw). red_tl_all; simpl.
    iEval (rewrite red_syn_inv; rewrite red_syn_wpsim; rewrite red_syn_tgt_interp_as).
    iIntros "(#TINV & #WMEM & TID & DUTY)".

    iPoseProof (Ticketlock_enqueue_spec with "[TID DUTY]") as "SIM".
    2:{ rewrite red_syn_wpsim. done. }
    red_tl_all. iEval (rewrite red_syn_inv; rewrite red_syn_tgt_interp_as). simpl.
    iSplitL. iFrame. iSplit; auto.
    iIntros (? ? ? ?) "H". red_tl_all. simpl.
    iDestruct "H" as "(DUTY & PC & #OBL & VLE & MY1 & MY2)".
    rewrite red_syn_wpsim.

    iMod (pc_drop _ 1 _ _ 10 with "PC") as "PC". auto. Unshelve. all: auto.
    lred2r. unfold TicketLockW.lock_loop. iEval (do 2 rewrite unfold_iter_eq). rred2r. lred2r.
    iApply wpsim_reset. iStopProof. depgen Vfaa.
    eapply wpsim_coind. set_solver.
    intros g1 V'.
    iIntros "(#HG1 & #CIH) [(#TINV & #WMEM & #LO) (DUTY & VLE & MY1 & MY2 & PC)]".

    iRevert "DUTY MY1 MY2 PC VLE". iRevert (V'). iMod (lo_ind with "LO []") as "IND".
    2:{ iApply "IND". }
    iModIntro. iExists 0. iIntros "IH". iModIntro. iIntros (V') "DUTY MY1 MY2 PC VLE".

    iInv "TINV" as "TI" "TI_CLOSE".
    iEval (rewrite /= ticket_lock_inv_eq) in "TI". iDestruct "TI" as (own' ing V κm l tks now next myt) "(TKS & MEM & ST & CASES)".

    destruct (Nat.eq_dec mytk now).
    { subst. iClear "HG1 CIH".
      iPoseProof (mytk_find_some with "[MY2 TKS]") as "%FIND". iFrame.
      iDestruct "CASES" as "[[%CT [[% I] | [% I]]] | [%CF [% [I | I]]]]".
      { iPoseProof (locked_contra with "I") as "%F". eauto. inv F. }
      { iPoseProof (unlocking_contra with "I") as "%F". eauto. inv F. }
      { iPoseProof (unlocked0_contra with "I") as "%F". eauto. inv F. }

      subst. iPoseProof (unlocked1_mono with "I") as "[% #MONW]".

      iMod ("TI_CLOSE" with "[- DUTY MY1 MY2 VLE PC IH]") as "_".
      { rewrite /= ticket_lock_inv_eq. repeat iExists _.
        iFrame. iRight. iSplit. auto. iSplit. auto. iRight. auto.
      }

      iApply (wpsim_yieldR2 with "[DUTY PC]"). auto.
      2:{ iFrame. iApply pcs_cons_fold. iFrame. } lia.
      iIntros "DUTY CRED PCS".
      iPoseProof (pcs_cons_unfold with "PCS") as "[PCS _]". simpl.
      rred2r.

      iInv "TINV" as "TI" "TI_CLOSE". simpl.
      iEval (rewrite /= ticket_lock_inv_eq) in "TI". iDestruct "TI" as (own' ing V'' κm2 l2 tks2 now2 next3 myt2) "(TKS & MEM & ST & CASES)".
      clear FIND.
      iPoseProof (mytk_find_some with "[MY2 TKS]") as "%FIND". iFrame.
      iDestruct "CASES" as "[[%CT [[% I] | [% I]]] | [%CF [% [I | I]]]]".
      { iPoseProof (locked_myturn with "MONW I") as "%F". eauto. inv F. }
      { iPoseProof (unlocking_myturn with "MONW I") as "%F". eauto. inv F. }
      { iPoseProof (unlocked0_contra with "I") as "%F". eauto. inv F. }

      iEval (unfold ticket_lock_inv_mem; red_tl_all; ss) in "MEM".
      iDestruct "MEM" as "(MEM1 & MEM2 & MEM3 & MEM4 & MEM5 & MEM6)".
      iApply (WMem_load_fun_spec with "[WMEM MEM1] [-]"). auto.
      { solve_ndisj. } iFrame. auto.
      iIntros (rv) "(%Vload & %v & [% [MEM1 [[%FAIL PCM] | SUCC]]])".
      { iPoseProof (unlocked1_myturn with "MY1 MONW I") as "[%EQ #LINK]". auto. subst.
        iMod (link_amplify with "[$PCM]") as "PC". done. simpl.
        iMod (pc_drop _ 1 _ _ 2 with "PC") as "PC". auto. Unshelve. all: try lia.
        iPoseProof (pc_split _ _ 1 with "PC") as "[PC1 PC2]".
        iMod (pc_drop _ 0 _ _ 1 with "PC2") as "PC2". auto. Unshelve. all: try lia.
        iMod ("IH" with "PC2") as "IH".

        rred2r. iApply wpsim_tauR. des. rr in FAIL. des; clarify. rred2r.
        destruct (BinIntDef.Z.of_nat now =? BinIntDef.Z.of_nat m)%Z eqn:IF.
        { exfalso. clear - IF FAIL1. apply Z.eqb_eq in IF. apply Nat2Z.inj_iff in IF. lia. }
        subst. rred2r. iApply wpsim_tauR.

        iMod ("TI_CLOSE" with "[- DUTY MY1 MY2 VLE PCS PC1 IH]") as "_".
        { rewrite ticket_lock_inv_eq. repeat iExists _.
          unfold ticket_lock_inv_mem; red_tl_all. iFrame.
          iRight. iSplit. auto. iSplit. auto. iRight; auto.
        }

        iApply wpsim_reset. rewrite unfold_iter_eq. rred2r.
        iApply ("IH" with "[DUTY] [MY1] [MY2] [PCS PC1] [VLE]"); iFrame.
        { iPoseProof (pc_merge with "[PCS PC1]") as "PC". iFrame. done. }
        { iPure "VLE" as VLE. iPureIntro. etrans; eauto. }
      }
      { iClear "IH". iDestruct "SUCC" as "[%SUCC %VLE]".
        iPoseProof (unlocked1_myturn with "MY1 MONW I") as "[%EQ #LINK]". auto. subst.
        des. rr in SUCC. subst.
        rred2r. iApply wpsim_tauR. rred2r.

        destruct (BinIntDef.Z.of_nat now =? BinIntDef.Z.of_nat now)%Z eqn:ENOW; cycle 1.
        { apply Z.eqb_neq in ENOW. clarify. }
        clear ENOW. rred2r.
        iApply wpsim_yieldL. lred2r.
        iApply wpsim_getL. iSplit; auto. lred2r.
        iApply wpsim_getL. iSplit; auto. lred2r.
        iPure "VLE" as SVLE.
        assert (SIG: View.le (View.join tvw V'') Vload).
        { apply View.join_spec. etrans. eapply SVLE. auto. auto. }
        iApply wpsim_chooseL. iExists (@exist View.t _ Vload SIG). lred2r.
        iApply (wpsim_modifyL with "ST"). iIntros "ST".

        remember (NatMap.remove tid tks2) as tks2'.
        rewrite <- key_set_pull_rm_eq. rewrite <- Heqtks2'.
        iAssert (⟦ticket_lock_inv_state n true V'' false tks2', n⟧)%I with "[ST]" as "ST". iFrame.
        iAssert (⟦ticket_lock_inv_mem n V'' κm2 now next3 myt2, n⟧)%I
          with "[MEM1 MEM2 MEM3 MEM4 MEM5 MEM6]" as "MEM".
        {  unfold ticket_lock_inv_mem. red_tl_all. simpl. iFrame. }

        iEval (unfold ticket_lock_inv_unlocked1; red_tl_all; simpl) in "I".
        do 3 (iDestruct "I" as "[% I]"; red_tl).
        iDestruct "I" as "(I1 & %I2 & %I3 & I4 & (% & I5))". red_tl_all.
        iDestruct "I5" as "(I5 & I6 & I7 & I8 & #I9 & I10 & I11)". simpl.
        hexploit (tkqueue_inv_hd I3 _ FIND). i. des.
        subst l2. inversion H1. subst x0; subst x2. clear H1.

        iEval (unfold ticket_lock_inv_tks; red_tl_all) in "TKS". iDestruct "TKS" as "[TKS1 TKS2]".
        iPoseProof (NatMapRA_remove with "TKS1 MY2") as "> TKS1". rewrite <- Heqtks2'. simpl.
        iDestruct "TKS2" as "(TKS2 & TKS3 & TKS4)".
        iPoseProof (natmap_prop_remove_find with "TKS3") as "[TID TKS3]". eauto. rewrite <- Heqtks2'.
        iCombine "I11 MY1" as "MY". rewrite discrete_fun_singleton_op.
        iDestruct (OwnM_valid with "MY") as %[= -> ->]%discrete_fun_singleton_valid%excl_auth_agree_L.
        iPoseProof (OwnM_Upd with "MY") as "> MY".
        { eapply discrete_fun_singleton_update, excl_auth_update. }
        iPoseProof (OwnMs_fold with "[TKS4 MY]") as "TKS4".
        2:{ iSplitL "TKS4". iFrame. iFrame. }
        { instantiate (1:= fun id => ~ NatMap.In id tks2'). i. ss. subst tks2'.
          destruct (tid_dec j tid); auto. left. ii. apply IN.
          rewrite NatMapP.F.remove_neq_in_iff; auto.
        }

        iMod (OneShots.pending_shot _ tt with "I7") as "I7".
        iMod (duty_fulfill with "[DUTY I7 I9]") as "DUTY". iFrame. simpl. red_tl_all. iFrame. done.
        iPoseProof (black_updatable with "I5") as ">I5".
        { instantiate (1:=(now, Tkst.c κm2)). econs 2. ss. split; ss. lia. }
        hexploit (tkqueue_dequeue I3).
        { reflexivity. }
        i. rename I3 into I3Old, H1 into I3. unfold TicketLockW.tk in I3. rewrite <- Heqtks2' in I3.

        iAssert (⟦ticket_lock_inv_locked n tl tks2' now next3 myt2 V'' κm2, n⟧
          ∗ (natmap_prop_sum tks2' (fun th tk => FairRA.white Prism.id th (Ord.one))))%I
          with "[I1 I4 I5]" as "I1".
        { unfold ticket_lock_inv_locked. red_tl_all. iFrame.
          iPoseProof (natmap_prop_sepconj_sum with "[I4]") as "[I4 I6]".
          { instantiate (4:=tks2').
            instantiate (2:=(fun k a => FairRA.white Prism.id k Ord.one)%I).
            iApply (natmap_prop_sum_impl with "I4"). ii. iIntros "H". simpl.
            iEval (red_tl_all) in "H". simpl. iDestruct "H" as "[H1 H2]".
            erewrite FairRA.white_eq.
            2:{ instantiate (1:= (OrderedCM.add (Ord.from_nat (a - (S now))) (Ord.one))).
              rewrite <- Ord.from_nat_1. ss. rewrite <- Hessenberg.add_from_nat. rr. ss.
              hexploit (tkqueue_val_range_l I3 _ IN). i. split.
              { apply OrdArith.le_from_nat. lia. }
              { apply OrdArith.le_from_nat. lia. }
            }
            iPoseProof (FairRA.white_split with "H1") as "[H1 H3]". iFrame.
            iCombine "H1" "H2" as "H". iApply "H".
          }
          iFrame. iSplit; auto.
          iApply (natmap_prop_sum_impl). 2: iApply "I6". ii. iIntros "H".
          iDestruct "H" as "[H1 H2]".
          red_tl_all. simpl. iFrame.
          do 2 (iDestruct "H2" as "[% H2]"; red_tl). do 2 (iExists _; red_tl).
          iDestruct "H2" as "(H1 & H2 & H3 & H4 & H5 & H6 & H7)". iFrame.
        }
        iDestruct "I1" as "[I1 I2]". lred2r.
        (* iEval (unfold natmap_prop_sum) in "I2". lred2r. *)

        iApply (wpsim_fairL with "[I2]").
        { i. ss. instantiate (1:= (NatSet.elements (key_set tks2'))). des_ifs.
          eapply NatSetIn_In. auto.
        }
        { instantiate (1:=[tid]). i; ss. des; clarify. des_ifs. }
        { unfold natmap_prop_sum. unfold NatSet.elements. unfold nm_proj1.
          unfold key_set. rewrite <- list_map_elements_nm_map. unfold unit1. rewrite List.map_map.
          iPoseProof (list_prop_sum_map with "I2") as "I2".
          2: iFrame.
          ss. i. destruct a; ss. iIntros "$".
        }
        instantiate (1:=Ord.omega). iIntros "[MYW _]".
        iPoseProof (FairRA.whites_fold with "[TKS2 MYW]") as "TKS2".
        2:{ iSplitL "TKS2". iFrame. iFrame. }
        { instantiate (1:= fun id => ~ NatMap.In id tks2'). ss. i. destruct (tid_dec j tid); auto.
          left. ii. apply IN. subst tks2'. rewrite NatMapP.F.remove_neq_in_iff; auto.
        }

        lred2r.
        iMod ("TI_CLOSE" with "[- DUTY TID]") as "_".
        { rewrite ticket_lock_inv_eq. repeat iExists _.
          iSplitL "TKS1 TKS3 TKS2 TKS4".
          { unfold ticket_lock_inv_tks. red_tl_all; simpl. iFrame. }
          iFrame.
          iLeft. iSplit. auto. iLeft. iSplit. auto. auto.
        }
        iApply (wpsim_sync with "[$DUTY]"). auto. iIntros "DUTY _".
        lred2r. rred2r.
        iApply wpsim_tauR. rred2r. iApply wpsim_ret. auto. iModIntro. iFrame. auto.
      }
    }

    iApply (lock_yourturn_yield with "[-]"). apply n0.
    iSplitR "IH PC VLE".
    { red_tl_all. iFrame. iIntros "I". rewrite red_syn_fupd. iMod ("TI_CLOSE" with "[I]").
      { simpl. done. }
      ss.
    }
    iEval (red_tl_all). iIntros "(DUTY & MY1 & MY2 & CRED)". simpl. rred2r.
    clear own' ing next myt now n0 κm l tks.

    iInv "TINV" as "TI" "TI_CLOSE".
    iEval (rewrite /= ticket_lock_inv_eq) in "TI". iDestruct "TI" as (own2 ing2 V2 κm2 l2 tks2 now2 next2 myt2) "(TKS & MEM & ST & CASES)".

    destruct (Nat.eq_dec mytk now2).
    { subst. iClear "HG1 CIH".
      iPoseProof (mytk_find_some with "[MY1 TKS]") as "%FIND". iFrame.
      iDestruct "CASES" as "[[%CT [[% I] | [% I]]] | [%CF [% [I | I]]]]".
      { iPoseProof (locked_contra with "I") as "%F". eauto. inv F. }
      { iPoseProof (unlocking_contra with "I") as "%F". eauto. inv F. }
      { iPoseProof (unlocked0_contra with "I") as "%F". eauto. inv F. }

      subst. iPoseProof (unlocked1_mono with "I") as "[% #MONW]".

      iEval (unfold ticket_lock_inv_mem; red_tl_all; ss) in "MEM".
      iDestruct "MEM" as "(MEM1 & MEM2 & MEM3 & MEM4 & MEM5 & MEM6)".
      iApply (WMem_load_fun_spec with "[WMEM MEM1] [-]"). auto.
      { pose proof mask_disjoint_ticketlock_state_tgt. set_solver. } iFrame. auto.
      iIntros (rv) "(%Vload & %v & [% [MEM1 [[%FAIL PCM] | SUCC]]])".
      { iPoseProof (unlocked1_myturn with "MY2 MONW I") as "[%EQ #LINK]". auto. subst.
        iMod (link_amplify with "[PCM LINK]") as "PC2". iFrame. done. simpl.
        iMod (pc_drop _ 1 _ _ 2 with "PC2") as "PC2". auto. Unshelve. all: try lia.
        iPoseProof (pc_split _ _ 1 with "PC2") as "[PC1 PC2]".
        iMod (pc_drop _ 0 _ _ 1 with "PC2") as "PC2". auto. Unshelve. all: try lia.
        iMod ("IH" with "PC2") as "IH".

        rred2r. iApply wpsim_tauR. des. rr in FAIL. des; clarify. rred2r.
        destruct (BinIntDef.Z.of_nat now2 =? BinIntDef.Z.of_nat m)%Z eqn:IF.
        { exfalso. clear - IF FAIL1. apply Z.eqb_eq in IF. apply Nat2Z.inj_iff in IF. lia. }
        subst. rred2r. iApply wpsim_tauR.

        iMod ("TI_CLOSE" with "[- DUTY MY1 MY2 VLE PC PC1 IH]") as "_".
        { rewrite ticket_lock_inv_eq. repeat iExists _. iFrame.
          iSplitR "I".
          unfold ticket_lock_inv_mem; red_tl_all. iFrame.
          iRight. iSplit. auto. iSplit. auto. iRight; auto.
        }

        iApply wpsim_reset. rewrite unfold_iter_eq. rred2r.
        iApply ("IH" with "[DUTY] [MY2] [MY1] [PC PC1] [VLE]"); iFrame.
        { iPure "VLE" as VLE. iPureIntro. etrans; eauto. }
      }
      { iClear "IH". iDestruct "SUCC" as "[%SUCC %VLE]".
        iPoseProof (unlocked1_myturn with "MY2 MONW I") as "[%EQ #LINK]". auto. subst.
        des. rr in SUCC. subst.
        rred2r. iApply wpsim_tauR. rred2r.

        destruct (BinIntDef.Z.of_nat now2 =? BinIntDef.Z.of_nat now2)%Z eqn:ENOW; cycle 1.
        { apply Z.eqb_neq in ENOW. clarify. }
        clear ENOW. rred2r.
        iApply wpsim_yieldL. lred2r.
        iApply wpsim_getL. iSplit; auto. lred2r.
        iApply wpsim_getL. iSplit; auto. lred2r.
        iPure "VLE" as SVLE.
        assert (SIG: View.le (View.join tvw V2) Vload).
        { apply View.join_spec. etrans. eapply SVLE. auto. auto. }
        iApply wpsim_chooseL. iExists (@exist View.t _ Vload SIG). lred2r.
        iApply (wpsim_modifyL with "ST"). iIntros "ST".

        remember (NatMap.remove tid tks2) as tks2'.
        rewrite <- key_set_pull_rm_eq. rewrite <- Heqtks2'.
        iAssert (⟦ticket_lock_inv_state n true V2 false tks2', n⟧)%I with "[ST]" as "ST". iFrame.
        iAssert (⟦ticket_lock_inv_mem n V2 κm2 now2 next2 myt2, n⟧)%I
          with "[MEM1 MEM2 MEM3 MEM4 MEM5 MEM6]" as "MEM".
        {  unfold ticket_lock_inv_mem. red_tl_all. simpl. iFrame. }

        iEval (unfold ticket_lock_inv_unlocked1; red_tl_all; simpl) in "I".
        do 3 (iDestruct "I" as "[% I]"; red_tl).
        iDestruct "I" as "(I1 & %I2 & %I3 & I4 & (% & I5))". red_tl_all.
        iDestruct "I5" as "(I5 & I6 & I7 & I8 & #I9 & I10 & I11)". simpl.
        hexploit (tkqueue_inv_hd I3 _ FIND). i. des.
        subst l2. inversion H0. subst x0; subst x2. clear H0.

        iEval (unfold ticket_lock_inv_tks; red_tl_all) in "TKS". iDestruct "TKS" as "[TKS1 TKS2]".
        iPoseProof (NatMapRA_remove with "TKS1 MY1") as "> TKS1". rewrite <- Heqtks2'. simpl.
        iDestruct "TKS2" as "(TKS2 & TKS3 & TKS4)".
        iPoseProof (natmap_prop_remove_find with "TKS3") as "[TID TKS3]". eauto. rewrite <- Heqtks2'.
        iCombine "I11 MY2" as "MY". rewrite discrete_fun_singleton_op.
        iDestruct (OwnM_valid with "MY") as %[= -> ->]%discrete_fun_singleton_valid%excl_auth_agree_L.
        iPoseProof (OwnM_Upd with "MY") as "> MY".
        { apply discrete_fun_singleton_update, excl_auth_update. }
        iPoseProof (OwnMs_fold with "[TKS4 MY]") as "TKS4".
        2:{ iSplitL "TKS4". iFrame. iFrame. }
        { instantiate (1:= fun id => ~ NatMap.In id tks2'). i. ss. subst tks2'.
          destruct (tid_dec j tid); auto. left. ii. apply IN.
          rewrite NatMapP.F.remove_neq_in_iff; auto.
        }

        iMod (OneShots.pending_shot _ tt with "I7") as "I7".
        iMod (duty_fulfill with "[DUTY I7 I9]") as "DUTY". iFrame. simpl. red_tl_all. iFrame. done.
        iPoseProof (black_updatable with "I5") as ">I5".
        { instantiate (1:=(now2, Tkst.c κm2)). econs 2. ss. split; ss. lia. }
        hexploit (tkqueue_dequeue I3).
        { reflexivity. }
        i. rename I3 into I3Old, H0 into I3. unfold TicketLockW.tk in I3. rewrite <- Heqtks2' in I3.

        iAssert (⟦ticket_lock_inv_locked n tl tks2' now2 next2 myt2 V2 κm2, n⟧
          ∗ (natmap_prop_sum tks2' (fun th tk => FairRA.white Prism.id th (Ord.one))))%I
          with "[I1 I4 I5]" as "I1".
        { unfold ticket_lock_inv_locked. red_tl_all. iFrame.
          iPoseProof (natmap_prop_sepconj_sum with "[I4]") as "[I4 I6]".
          { instantiate (4:=tks2').
            instantiate (2:=(fun k a => FairRA.white Prism.id k Ord.one)%I).
            iApply (natmap_prop_sum_impl with "I4"). ii. iIntros "H". simpl.
            iEval (red_tl_all) in "H". simpl. iDestruct "H" as "[H1 H2]".
            erewrite FairRA.white_eq.
            2:{ instantiate (1:= (OrderedCM.add (Ord.from_nat (a - (S now2))) (Ord.one))).
              rewrite <- Ord.from_nat_1. ss. rewrite <- Hessenberg.add_from_nat. rr. ss.
              hexploit (tkqueue_val_range_l I3 _ IN). i. split.
              { apply OrdArith.le_from_nat. lia. }
              { apply OrdArith.le_from_nat. lia. }
            }
            iPoseProof (FairRA.white_split with "H1") as "[H1 H3]". iFrame.
            iCombine "H1" "H2" as "H". iApply "H".
          }
          iFrame. iSplit; auto.
          iApply (natmap_prop_sum_impl). 2: iApply "I6". ii. iIntros "H".
          iDestruct "H" as "[H1 H2]".
          red_tl_all. simpl. iFrame.
          do 2 (iDestruct "H2" as "[% H2]"; red_tl). do 2 (iExists _; red_tl).
          iDestruct "H2" as "(H1 & H2 & H3 & H4 & H5 & H6 & H7)". iFrame.
        }
        iDestruct "I1" as "[I1 I2]". lred2r.

        iApply (wpsim_fairL with "[I2]").
        { i. ss. instantiate (1:= (NatSet.elements (key_set tks2'))). des_ifs.
          eapply NatSetIn_In. auto.
        }
        { instantiate (1:=[tid]). i; ss. des; clarify. des_ifs. }
        { unfold natmap_prop_sum. unfold NatSet.elements. unfold nm_proj1.
          unfold key_set. rewrite <- list_map_elements_nm_map. unfold unit1. rewrite List.map_map.
          iPoseProof (list_prop_sum_map with "I2") as "I2".
          2: iFrame.
          ss. i. destruct a; ss. iIntros "$".
        }
        instantiate (1:=Ord.omega). iIntros "[MYW _]".
        iPoseProof (FairRA.whites_fold with "[TKS2 MYW]") as "TKS2".
        2:{ iSplitL "TKS2". iFrame. iFrame. }
        { instantiate (1:= fun id => ~ NatMap.In id tks2'). ss. i. destruct (tid_dec j tid); auto.
          left. ii. apply IN. subst tks2'. rewrite NatMapP.F.remove_neq_in_iff; auto.
        }

        lred2r.
        iMod ("TI_CLOSE" with "[- DUTY TID]") as "_".
        { rewrite ticket_lock_inv_eq. do 9 iExists _. iFrame.
          iSplitL "TKS1 TKS3 TKS2 TKS4".
          { unfold ticket_lock_inv_tks. red_tl_all; simpl. iFrame. }
          iLeft. iSplit. auto. iLeft. iSplit. auto. auto.
        }
        iApply (wpsim_sync with "[DUTY]"). auto. iFrame. iIntros "DUTY _".
        lred2r. rred2r.
        iApply wpsim_tauR. rred2r. iApply wpsim_ret. auto. iModIntro. iFrame. auto.
      }
    }

    iPoseProof (mytk_find_some with "[MY1 TKS]") as "%FIND". iFrame.
    iPoseProof (yourturn_range with "CASES") as "%LT". done. done.
    iApply (lock_yourturn_acq with "[-]"). done.
    red_tl. rewrite red_syn_tgt_interp_as. iFrame. iSplit; auto.
    iIntros (Vfaa val) "(% & % & MEM)".

    rred2r.
    destruct (BinIntDef.Z.of_nat mytk =? BinIntDef.Z.of_nat val)%Z eqn:IF.
    { exfalso. clear - IF H0. apply Z.eqb_eq in IF. apply Nat2Z.inj_iff in IF. lia. }
    rred2r. iApply wpsim_tauR.
    rewrite unfold_iter_eq. rred2r.

    clear IF.
    iDestruct "CASES" as "[[%TRUE [[%IF INV] | [%IT INV]]] | [%FALSE [%IF [INV | INV]]]]"; subst.
    { subst. iApply (wpsim_yieldL). lred2r.
      iApply wpsim_getL. iSplit. auto. lred2r.
      iApply wpsim_tauL. lred2r. rewrite unfold_iter_eq. lred2r.
      iMod ("TI_CLOSE" with "[TKS ST INV MEM]").
      { rewrite /= ticket_lock_inv_eq. do 9 iExists _. iFrame.
        iLeft. iSplit. auto. iLeft. iSplit. auto. auto.
      }
      iApply wpsim_progress. iApply wpsim_base. set_solver.
      iApply ("CIH" with "[-]").
      { iFrame. iSplit.
        { iModIntro. iSplit; auto. }
        iPure "VLE" as VLE. iPureIntro.
        etrans; eauto.
      }
    }
    { subst. iApply (wpsim_yieldL). lred2r.
      iApply wpsim_getL. iSplit. auto. lred2r.
      iApply wpsim_tauL. lred2r. rewrite unfold_iter_eq. lred2r.
      iMod ("TI_CLOSE" with "[TKS ST INV MEM]").
      { rewrite /= ticket_lock_inv_eq. do 9 iExists _. iFrame.
        iLeft. iSplit. auto. iRight. iSplit. auto. auto.
      }
      iApply wpsim_progress. iApply wpsim_base. set_solver.
      iApply ("CIH" with "[-]").
      { iFrame. iSplit.
        { iModIntro. iSplit; auto. }
        iPure "VLE" as VLE. iPureIntro.
        etrans; eauto.
      }
    }
    { iPoseProof (unlocked0_contra with "INV") as "%FF". eauto. inv FF. }
    { iEval (unfold ticket_lock_inv_unlocked1) in "INV".
      desas "INV" yourt; desas "INV" κay; desas "INV" waits.
      iEval (red_tl_all) in "INV".
      iDestruct "INV" as "(INV1 & %INV2 & %INV3 & INV4 & INV5)".
      iDestruct "INV5" as "(% & INV5)". iEval (red_tl) in "INV5".
      iDestruct "INV5" as "(INV5 & INV6 & INV7 & #INV8 & INV9 & INV10 & INV11)". simpl.
      iMod (tpromise_progress with "[INV8 CRED]") as "[PC2 | #CONTRA]". iFrame. done.
      2:{ iEval (simpl; red_tl_all) in "CONTRA". iExFalso. iApply (OneShots.pending_not_shot with "[INV7 CONTRA]").
        red_tl_all. iFrame. auto.
      }

      hexploit (tkqueue_dequeue INV3). eapply INV2. i.
      assert (NOTMT: tid <> yourt).
      { ii. clarify. inv INV3; ss. clarify. setoid_rewrite FIND in FIND0. inv FIND0. }

      iPoseProof (natmap_prop_sum_find_remove with "INV4") as "[INV4 CLOSE]".
      { rewrite nm_find_rm_neq. done. done. }

      iEval (red_tl) in "INV4". iDestruct "INV4" as "[INV4 [% INV12]]".
      iEval (red_tl) in "INV12". iDestruct "INV12" as "[% INV12]". iEval (red_tl) in "INV12". simpl.
      iDestruct "INV12" as "(INV12 & INV13 & INV14 & INV15 & INV16 & INV17 & #INV18)".

      iMod (link_amplify with "[INV18 PC2]") as "PC2". iFrame. iApply "INV18".
      iCombine "INV17 MY2" gives %MY.
      rewrite discrete_fun_singleton_op in MY.
      apply discrete_fun_singleton_valid, excl_auth_agree_L in MY as [= -> ->].
      iMod ("IH" with "PC2") as "IH".
      iPoseProof ("CLOSE" with "[INV4 INV12 INV13 INV14 INV15 INV16 INV17]") as "CLOSE".
      { red_tl. iFrame. iExists _; red_tl; iExists _; red_tl. iFrame. done. }

      iMod ("TI_CLOSE" with "[- PC VLE DUTY MY1 MY2 IH]").
      { rewrite ticket_lock_inv_eq. repeat iExists _. iFrame.
        iRight. iSplit; auto. iSplit; auto. iRight. unfold ticket_lock_inv_unlocked1.
        red_tl; iExists yourt; red_tl; iExists κay; red_tl; iExists waits. red_tl_all.
        iFrame. iSplit. auto. iSplit. auto.
        red_tl_all. iFrame. iExists x. red_tl_all. simpl. iPoseProof "INV9" as "#INV9". iFrame. iSplit; auto.
      }

      iApply wpsim_reset. iApply ("IH" $! Vfaa with "DUTY MY2 MY1 PC [VLE]").
      iPure "VLE" as VLE. iPureIntro. etrans; eauto.
    }
  Qed.

  (* Simulations *)
  Lemma correct_unlock tid i:
  ⊢ ⟦(∀ (tvw : τ{View.t, 1+i}),
      ((⤉ syn_inv i N_Ticketlock_w (ticket_lock_inv i))
      ∗ (syn_tgt_interp_as i sndl (fun m => ((s_wmemory_black_strong inrp m))))
      ∗ TID(tid)
      ∗ (⤉ Duty(tid) []))
    -∗
      (syn_wpsim (S i) tid ⊤
        (fun rs rt => (⤉ (syn_term_cond i tid _ rs rt))%S)
        false false
        (AbsLockW.unlock_fun tvw)
        (OMod.close_itree TicketLockW.omod WMem.mod (TicketLockW.unlock_fun tvw))))%S, 1+i⟧.
  Proof.
    red_tl. iIntros (V0). red_tl. rewrite red_syn_inv; rewrite red_syn_tgt_interp_as; rewrite red_syn_wpsim. simpl.
    iIntros "(#INV & #WMEM & TID & DUTY)".

    unfold AbsLockW.unlock_fun, TicketLockW.unlock_fun. lred2r. rred2r.
    iApply (wpsim_sync with "[DUTY]"). auto. iFrame. iIntros "DUTY _". lred2r. rred2r.

    iInv "INV" as "TI" "TI_CLOSE".
    iEval (rewrite /= ticket_lock_inv_eq) in "TI". iDestruct "TI" as (own' ing V κm l tks now next myt) "(TKS & MEM & ST & CASES)".

    iDestruct "CASES" as "[[%CT [[% I] | [% I]]] | [%CF [%CF2 [I | I]]]]"; cycle 1.
    { subst. iApply wpsim_getL. iSplit. auto. rred. ss. des_ifs; lred2r; iApply wpsim_UB. }
    { subst. iApply wpsim_getL. iSplit. auto. rred. ss. des_ifs; lred2r; iApply wpsim_UB. }
    { subst. iApply wpsim_getL. iSplit. auto. rred. ss. des_ifs; lred2r; iApply wpsim_UB. }

    subst. iApply wpsim_getL. iSplit. auto. ss.
    destruct (excluded_middle_informative (View.le V V0)).
    2: lred2r; iApply wpsim_UB.
    rename l0 into ARGLE. lred2r. iApply (wpsim_modifyL with "ST"). iIntros "ST". lred2r.

    unfold ticket_lock_inv_mem. red_tl_all. iDestruct "MEM" as "(MEM1 & MEM2 & MEM3 & MEM4 & MEM5 & MEM6)". simpl.
    iApply (WMem_load_fun_spec_rlx with "[WMEM MEM1] [-]"). auto.
    { pose proof mask_disjoint_ticketlock_state_tgt. set_solver. }
    { iFrame. iSplit; auto. }
    iIntros (rv) "(%V2 & %v & (% & PT & %Q))". des. rr in Q. clarify.
    rred2r. iApply wpsim_tauR. rred2r.

    unfold ticket_lock_inv_locked. red_tl_all.
    iDestruct "I" as "(I1 & %I2 & I3 & I4)".
    iCombine "MEM3 I1" as "MEM3".
    iMod (OwnM_Upd with "MEM3") as "MEM3".
    { apply excl_auth_update. }
    instantiate (1:=(now, tid, V)).
    iDestruct "MEM3" as "[MEM3 HOLD]".
    iMod ("TI_CLOSE" with "[- DUTY HOLD]") as "_".
    { rewrite ticket_lock_inv_eq. repeat iExists _. iFrame.
      iSplitL "PT MEM2 MEM3 MEM4 MEM5 MEM6". unfold ticket_lock_inv_mem. red_tl_all. simpl. iFrame "MEM4 ∗".
      iSplitL "ST". auto.
      iLeft. iSplit; auto. iRight. iSplit; auto.
      unfold ticket_lock_inv_unlocking. red_tl_all. iFrame. done.
    }

    iApply (wpsim_sync with "[$DUTY]"). auto. iIntros "DUTY _".

    iInv "INV" as "TI" "TI_CLOSE".
    iEval (rewrite /= ticket_lock_inv_eq) in "TI". iDestruct "TI" as (own2 ing2 V3 κm2 l2 tks2 no2w next2 myt2) "(TKS & MEM & ST & CASES)".

    iDestruct "CASES" as "[[%CT [[% I] | [% I]]] | [%CF [%CF2 [I | I]]]]"; cycle 2.
    { subst. unfold ticket_lock_inv_unlocked0. red_tl_all. iDestruct "I" as "[C I]".
      iCombine "HOLD C" as "F". iOwnWf "F" as F.
      by apply excl_auth_frag_op_valid in F.
    }
    { subst. unfold ticket_lock_inv_unlocked1. desas "I" yourt; desas "I" κay; desas "I" waits.
      red_tl. iDestruct "I" as "[C I]".
      iCombine "HOLD C" as "F". iOwnWf "F" as F.
      by apply excl_auth_frag_op_valid in F.
    }
    { subst. unfold ticket_lock_inv_locked.
      red_tl. iDestruct "I" as "[C I]".
      iCombine "HOLD C" as "F". iOwnWf "F" as F.
      by apply excl_auth_frag_op_valid in F.
    }
    unfold ticket_lock_inv_mem. red_tl_all. iDestruct "MEM" as "[MEM0 [MEM1 [MEM2 [MEM3 [MEM4 MEM5]]]]]".
    iCombine "MEM2 HOLD" as "MEM2".
    iOwnWf "MEM2" as EQ. apply excl_auth_agree_L in EQ. inv EQ.
    iDestruct "MEM2" as "[MEM2 HOLD]".
    lred2r. iApply wpsim_getL. iSplit; auto. lred2r. rred2r.

    iApply (WMem_store_fun_spec with "[MEM0] [-]"). auto.
    { pose proof mask_disjoint_ticketlock_state_tgt; set_solver. }
    { repeat iSplit; auto.
      instantiate (1:=wQ (1+now)). iPureIntro. rr.
      replace (nat2c (1+now)) with (Const.add (nat2c now) const_1). ss.
      clear. unfold nat2c. ss. unfold BinIntDef.Z.of_nat. des_ifs. ss.
      rewrite Z.add_comm. rewrite Pos2Z.add_pos_pos. rewrite Pplus_one_succ_l. ss.
      iPureIntro. etrans; eauto.
    }
    iIntros (rv) "(%V1 & %V' & %k' & (%H & [MEM0 MEM6]))". des; clarify.
    rred2r. iApply wpsim_tauR. rred2r.

    assert (SIG: View.le V0 V').
    { etrans; eauto. }
    iApply wpsim_chooseL.
    iExists (@exist View.t _ V' SIG). lred.
    iApply (wpsim_modifyL with "ST"). iIntros "ST".
    lred2r.

    assert (SIG2: View.le V' V1).
    { eauto. }
    iApply wpsim_chooseL.
    iExists (@exist View.t _ V1 SIG2). lred.
    iCombine "MEM2 HOLD" as "MEM2".
    iMod (OwnM_Upd with "MEM2") as "MEM2".
    { apply excl_auth_update. }
    iDestruct "MEM2" as "[MEM2 HOLD]".
    instantiate (1:=(S now, tid, V')).
    iPoseProof (black_updatable with "MEM3") as ">MEM3".
    { instantiate (1:=S now). lia. }
    iPoseProof (black_updatable with "MEM4") as ">MEM4".
    { instantiate (1:=(S now, k')). econs 1; try lia. }

    unfold ticket_lock_inv_unlocking. red_tl_all. simpl. clear I2.
    iDestruct "I" as "[I1 [%I2 [I3 I4]]]".

    destruct l2 as [ | yourt waits].
    { iPoseProof (black_updatable with "I4") as ">I4".
      { instantiate (1:=(S now, Tkst.a k')). econs 1; try lia. }
      iAssert (⟦ticket_lock_inv_mem i V' k' (S now) next2 tid, i⟧)%I with "[MEM0 MEM1 MEM2 MEM3 MEM4 MEM6]" as "MEM".
      { unfold ticket_lock_inv_mem. red_tl_all. simpl. iFrame.
        iApply wpoints_to_full_impl. iSplit; auto. iPureIntro.
        unfold wimpl. ii. rr in H. rr. des. rr in H. des. exists m; auto. rr in H. exists now. auto.
      }
      iClear "MEM5".
      (* iAssert (ticket_lock_inv_state false V' false tks2)%I with "[ST]" as "ST". iFrame. *)
      iMod ("TI_CLOSE" with "[TKS MEM ST I3 I4 HOLD]") as "_".
      { rewrite ticket_lock_inv_eq. do 9 iExists _. iFrame "∗". iSplitL "ST". auto.
        iRight. iSplit. auto. iSplit. auto. iLeft. unfold ticket_lock_inv_unlocked0. red_tl_all. iFrame.
        iPureIntro. split; eauto. inv I2; ss.
      }
      iApply (wpsim_sync with "[DUTY]"). auto. iFrame. iIntros "DUTY _".
      rred. iApply wpsim_tauR. rred. lred2r.
      iApply wpsim_ret. auto. iModIntro. iFrame. auto.
    }

    exploit tkqueue_in_find; eauto. simpl; left; auto. i. des.
    iPoseProof (natmap_prop_remove_find with "I3") as "[NEXT I3]". done.
    dup I2. inv I2. clarify. simpl.
    iEval (red_tl_all) in "NEXT". iDestruct "NEXT" as "[NEXT1 [%n1 NEXT2]]". red_tl. iDestruct "NEXT2" as "[%n2 NEXT2]".
    red_tl_all. simpl. iDestruct "NEXT2" as "(#NEXT2 & NEXT3 & NEXT4 & NEXT5 & NEXT6 & NEXT7)".
    replace (S now - now) with 1. 2: lia.
    iMod (pc_drop _ 4 _ _ 1 with "NEXT6") as "NEXT6". lia. Unshelve. 2: lia.
    iPoseProof "MEM6" as "#MEM6".
    iMod (link_new with "[MEM6 NEXT6]") as "[NEXT6 _]". iSplitR "NEXT6". auto. instantiate (1:=2). iFrame.
    iMod (activate_tpromise with "NEXT3 NEXT4") as "[NEXT3 NEXT4]".
    Unshelve. 2: exact 0.

    iAssert
      (natmap_prop_sum (NatMap.remove (elt:=nat) hd tks2)
        (λ t a : nat,
          #=(ObligationRA.edges_sat)=> FairRA.white (Id:=nat) Prism.id t (Ord.from_nat (a - S now))
          ∗ ⟦(∃ κa γs : τ{ (⇣ nat)%stype}, ◆[κa, (4 + a)] ∗ -[κa](0)-⧖ (▿ γs ()) ∗ ⧖[κa, (1 / 2)] ∗
              (△ γs 1) ∗ ◇[κa]((4 + a), (a - S now)) ∗ ➢ maps_to_res t _ ∗
              n1 -(0)-◇ κa)%S, i ⟧))%I with "[I3]" as "I3".
    { Unshelve. 2: apply ord_OrderedCM.
      2: { assert (id_src_type = nat). ss. rewrite <- H. apply (@SRA.in_subG Γ Σ sub _ _IDENTSRC). }
      iApply (natmap_prop_sum_impl_ctx with "NEXT2 I3"). ii. red_tl_all. simpl. iIntros "[CTX [H [% H1]]]". red_tl.
      iDestruct "H1" as "[% H1]". red_tl_all. simpl. iDestruct "H1" as "(H1 & H2 & H3 & H4 & H5 & H6)".
      hexploit tkqueue_val_range_l; eauto; i. replace (a - now) with (1 + (a - S now)). 2: lia.
      iPoseProof (pc_split _ _ 1 with "H5") as "[H5 H7]".
      iAssert (#=> ◇[x0](6 + now, 1))%I with "[H5]" as "> H5".
      { inv H. done. iPoseProof (pc_drop _ (6 + now) _ _ 1 with "H5") as "H5". auto. Unshelve. 2: lia. auto. }

      iMod (link_new _ _ _ 0 with "[CTX H5]") as "[H5 _]". iSplit; auto.
      iModIntro. iFrame. iExists _; red_tl; iExists _; red_tl_all. iFrame.
    }
    iPoseProof (natmap_prop_sum_pull_bupd with "I3") as "> I3".

    iPoseProof (black_updatable with "I4") as ">I4".
    { instantiate (1:=(S now, Tkst.b k')). econs 1; try lia. }
    iAssert (⟦ticket_lock_inv_mem i V' k' (S now) next2 tid, i⟧)%I with "[MEM0 MEM1 MEM2 MEM3 MEM4 MEM5 MEM6]" as "MEM".
    { unfold ticket_lock_inv_mem. red_tl_all. simpl. iFrame. iSplit; auto.
      iApply wpoints_to_full_impl. iFrame.
      unfold wimpl, wor. iPureIntro. ss. i. clear - H.
      unfold wP, wQ in *. des; eauto.
    }
    iMod ("TI_CLOSE" with "[- DUTY I1]") as "_".
    { rewrite ticket_lock_inv_eq. do 9 iExists _. red_tl_all. iFrame.
      iSplitL "ST". auto.
      iRight. iSplit. auto. iSplit. auto. iRight. unfold ticket_lock_inv_unlocked1.
      red_tl; iExists hd; red_tl; iExists n1; red_tl; iExists tl. red_tl_all. iFrame. iSplit; auto. iSplit; auto.
      iPoseProof "NEXT4" as "#NEXT4".
      iExists _; red_tl_all. simpl. iFrame. iSplit; auto.
    }
    iApply (wpsim_sync with "[DUTY]"). auto. iFrame. iIntros "DUTY _".
    rred. iApply wpsim_tauR. rred. lred2r.
    iApply wpsim_ret. auto. iFrame. auto.
  Unshelve. exact 0.
  Qed.

  End VARIABLES.

  Section SIM_INITIAL.
    Let init_ord := Ord.omega.
    Let idx := 1.

    Lemma init_sat :
      (OwnM (Σ:=Σ) (wmem_init_res TicketLockW.now_serving TicketLockW.next_ticket)
        ∗ OwnM (◯E ((0, 0, View.bot) : leibnizO _)
          ⋅ ●E ((0, 0, View.bot): leibnizO _))
        ∗ OwnM ((fun _ => (●E ([] : leibnizO _))
          ⋅ (◯E ([] : leibnizO _))): (thread_id -d> (excl_authUR (leibnizO (list nat)))))
        ∗ OwnM (Σ:=Σ) (●{#1} (NatMapRA.to_Map (NatMap.empty nat))))
        ∗ (WSim.initial_prop
          AbsLockW.mod TicketLockW.module
          (Vars:=@sProp STT Γ) (Σ:=Σ)
          (STATESRC:=@SRA.in_subG Γ Σ sub _ _STATESRC)
          (STATETGT:=@SRA.in_subG Γ Σ sub _ _STATETGT)
          (IDENTSRC:=@SRA.in_subG Γ Σ sub _ _IDENTSRC)
          (IDENTTGT:=@SRA.in_subG Γ Σ sub _ _IDENTTGT)
          (ARROWRA:=@_ARROWRA STT Γ Σ TLRAS)
          idx TIdSet.empty init_ord)
        ⊢
        =| 1+idx |=(⟦syn_fairI (1+idx), 1+idx⟧)={ ⊤, ⊤ }=>
          (⟦∃ (monok tk_mono wm_mono: τ{nat, idx}),
            syn_inv idx N_Ticketlock_w (ticket_lock_inv monok tk_mono wm_mono idx), idx⟧)
          ∗ (⟦syn_tgt_interp_as idx sndl (fun m => (s_wmemory_black_strong inrp m)), 1+idx⟧).
    Proof.
    iIntros "[[MEM [[OWN0 OWN1] [OWN2 OWN3]]] INIT]".
    unfold WSim.initial_prop.
    iDestruct "INIT" as "(INIT0 & INIT1 & INIT2 & INIT3 & INIT4 & INIT5)".
    iPoseProof (wmem_init_res_prop with "MEM") as "[NOW [NEXT MBLACK]]".
    iPoseProof (init_points_to_wpoints_to_faa with "NEXT") as "NEXT".
    iPoseProof (init_points_to_wpoints_to_full with "NOW") as "> [% [NOW BLACK]]".
    { instantiate (1:=wQ 0). ss. }
    iPoseProof (@monoBlack_alloc _ _ _ _ mypreord) as "> [%monok MONO0]".
    iPoseProof (@monoBlack_alloc _ _ _ _ Nat.le_preorder 0) as "> [%tk_mono MONO1]".
    iPoseProof (@monoBlack_alloc _ _ _ _ wmpreord (0, _)) as "> [%wm_mono MONO2]".
    iMod (FUpd_alloc _ _ _ idx N_Ticketlock_w (ticket_lock_inv monok tk_mono wm_mono idx)
      with "[- MBLACK INIT1 INIT5]") as "ALLOC". auto.
    { rewrite /= ticket_lock_inv_eq. iExists false,false,View.bot,_,[],(NatMap.empty nat),0,0,0.
      iSplitL "OWN2 OWN3 INIT0".
      { unfold ticket_lock_inv_tks. red_tl. simpl. iFrame. iSplitL "INIT0".
        { iApply (FairRA.whites_impl with "INIT0"). i. ss. }
        iSplitR.
        { rewrite red_sprop_sum. ss. }
        { rewrite red_s_OwnMs. unfold OwnMs. iApply (OwnM_extends with "OWN2").
          eapply discrete_fun_included_spec_2. i. des_ifs.
        }
      }
      iSplitL "MONO2 NEXT NOW OWN1 MONO1 BLACK".
      { unfold ticket_lock_inv_mem. red_tl. simpl. red_tl_memra. iFrame. red_tl_monoRA. iFrame. }
      iSplitL "INIT4".
      { unfold ticket_lock_inv_state. red_tl. rewrite key_set_empty_empty_eq. iFrame. }
      { iRight. iSplit; auto. iSplit; auto. iLeft.
        unfold ticket_lock_inv_unlocked0. red_tl. simpl. red_tl_monoRA. iFrame. iSplitR; [auto|]. iPureIntro; auto.
      }
    }
    iMod (tgt_interp_as_id _ _ (n:=idx) with "[INIT5 INIT1 MBLACK]") as "TGT_ST".
    auto.
    2:{ iExists _. iFrame. instantiate (1:=fun '(_, m) => s_wmemory_black_strong inrp m). simpl.
        red_tl_memra. unfold wmemory_black_strong. iFrame.
        iApply FairRA.blacks_prism_id_rev.
        iApply (FairRA.blacks_impl with "INIT1"). i. des. subst. ss.
    }
    { simpl. instantiate (1:= (∃ (st : τ{st_tgt_type, idx}), ⟨Atom.ow_st_tgt st⟩ ∗ (let '(_, m) := st in s_wmemory_black_strong (n:=idx) inrp m))%S).
      red_tl. f_equal.
    }
    iPoseProof (tgt_interp_as_compose (n:=idx) (la:=Lens.id) (lb:=sndl) with "TGT_ST") as "TGT_ST".
    { ss. econs. iIntros ([x m]) "MEM". unfold Lens.view. ss. iFrame.
      iIntros (m') "MEM". iFrame.
    }
    iEval (rewrite Lens.left_unit) in "TGT_ST".
    iModIntro. rewrite red_syn_tgt_interp_as. iSplit.
    { do 3 (red_tl; iExists _). rewrite red_syn_inv. iApply "ALLOC". } done.
  Qed.
  End SIM_INITIAL.
End SIM.

From Fairness Require Import ModSim.
Import ucmra_list.

Module TicketLockFair.

  Notation src_state := (Mod.state AbsLockW.mod).
  Notation src_ident := (Mod.ident AbsLockW.mod).
  Notation tgt_state := (Mod.state TicketLockW.module).
  Notation tgt_ident := (Mod.ident TicketLockW.module).
  Local Instance STT : StateTypes := Build_StateTypes src_state tgt_state src_ident tgt_ident.

  Local Instance Γ: SRA.t:=
    GRA.of_list [
      (* Default RAs *)
      OwnERA;
      OwnDRA;
      ThreadRA;
      (stateSrcRA st_src_type);
      (stateTgtRA st_tgt_type);
      (identSrcRA id_src_type);
      (identTgtRA id_tgt_type);
      ObligationRA.t;
      EdgeRA;
      ArrowShotRA;
      (* Additional RAs *)
      monoRA;
      (OneShots.t unit);
      wmemRA;
      (authUR (NatMapRA.t TicketLockW.tk));
      (excl_authUR (leibnizO ((nat * nat) * View.t)));
      (thread_id -d> (excl_authUR (leibnizO (list nat))))].

  Local Instance _OWNERA : GRA.inG OwnERA Γ := (@GRA.InG _ Γ 0 (@eq_refl _ _)).
  Local Instance _OWNDRA : GRA.inG OwnDRA Γ := (@GRA.InG _ Γ 1 (@eq_refl _ _)).
  Local Instance _THDRA : GRA.inG ThreadRA Γ := (@GRA.InG _ Γ 2 (@eq_refl _ _)).
  Local Instance _STATESRC : GRA.inG (stateSrcRA st_src_type) Γ := (@GRA.InG _ Γ 3 (@eq_refl _ _)).
  Local Instance _STATETGT : GRA.inG (stateTgtRA st_tgt_type) Γ := (@GRA.InG _ Γ 4 (@eq_refl _ _)).
  Local Instance _IDENTSRC : GRA.inG (identSrcRA id_src_type) Γ := (@GRA.InG _ Γ 5 (@eq_refl _ _)).
  Local Instance _IDENTTGT : GRA.inG (identTgtRA id_tgt_type) Γ := (@GRA.InG _ Γ 6 (@eq_refl _ _)).
  Local Instance _OBLGRA : GRA.inG ObligationRA.t Γ := (@GRA.InG _ Γ 7 (@eq_refl _ _)).
  Local Instance _EDGERA : GRA.inG EdgeRA Γ := (@GRA.InG _ Γ 8 (@eq_refl _ _)).
  Local Instance _ARROWSHOTRA : GRA.inG ArrowShotRA Γ := (@GRA.InG _ Γ 9 (@eq_refl _ _)).

  Local Instance MONORA: @GRA.inG monoRA Γ := (@GRA.InG _ Γ 10 (@eq_refl _ _)).
  Local Instance ONESHOTSRA: @GRA.inG (OneShots.t unit) Γ := (@GRA.InG _ Γ 11 (@eq_refl _ _)).
  Local Instance WMEMRA: @GRA.inG wmemRA Γ := (@GRA.InG _ Γ 12 (@eq_refl _ _)).
  Local Instance NATMAPRA: @GRA.inG (authUR (NatMapRA.t TicketLockW.tk)) Γ := (@GRA.InG _ Γ 13 (@eq_refl _ _)).
  Local Instance AUTHRA2: @GRA.inG (excl_authUR (leibnizO (((nat * nat) * View.t)))) Γ := (@GRA.InG _ Γ 14 (@eq_refl _ _)).
  Local Instance IN2: @GRA.inG (thread_id -d> (excl_authUR (leibnizO (list nat)))) Γ := (@GRA.InG _ Γ 15 (@eq_refl _ _)).

  Local Instance TLRASs : TLRAs_small STT Γ :=
    @Build_TLRAs_small STT Γ _ _ _ _ _ _ _ _ _ _.

  Definition Σ : GRA.t:=
    GRA.of_list [
        (* Default RAs. *)
        OwnERA;
        OwnDRA;
        ThreadRA;
        (stateSrcRA st_src_type);
        (stateTgtRA st_tgt_type);
        (identSrcRA id_src_type);
        (identTgtRA id_tgt_type);
        ObligationRA.t;
        EdgeRA;
        ArrowShotRA;
        (* Additional RAs. *)
        monoRA;
        (OneShots.t unit);
        wmemRA;
        (authUR (NatMapRA.t TicketLockW.tk));
        (excl_authUR (leibnizO (((nat * nat) * View.t))));
        (thread_id -d> (excl_authUR (leibnizO (list nat))));
        (* Maps from empty RAs of Γ. *)
        (optionUR Empty_setR);
        (* Default RAs depending on sProp. *)
        (IInvSetRA sProp);
        (ArrowRA id_tgt_type (Vars:=sProp));
        (ShareDutyRA id_tgt_type (Vars:=sProp))
      ].

  Local Program Instance sub : @SRA.subG Γ Σ :=
    { subG_map := fun i => if (le_lt_dec i 15) then i else 16 }.
  Next Obligation.
    i. ss. unfold Σ, Γ. des_ifs.
  Qed.

  Local Instance _IINVSETRA : GRA.inG (IInvSetRA sProp) Σ := (@GRA.InG _ Σ 17 (@eq_refl _ _)).
  Local Instance _ARROWRA : GRA.inG (ArrowRA id_tgt_type (Vars:=sProp)) Σ := (@GRA.InG _ Σ 18 (@eq_refl _ _)).
  Local Instance _SHAREDUTY : GRA.inG (ShareDutyRA id_tgt_type (Vars:=sProp)) Σ := (@GRA.InG _ Σ 19 (@eq_refl _ _)).

  Local Instance TLRAs : TLRAs STT Γ Σ :=
    @Build_TLRAs STT Γ Σ _ _ _.

  (* Additional initial resources. *)
  Local Definition init_res : Σ :=
    GRA.embed (wmem_init_res TicketLockW.now_serving TicketLockW.next_ticket)
    ⋅ GRA.embed (◯E ((0, 0, View.bot): leibnizO _ )
      ⋅ ●E ((0, 0, View.bot): leibnizO _))
    ⋅ GRA.embed (● (NatMapRA.to_Map (NatStructs.NatMap.empty nat)))
    ⋅ GRA.embed ((fun _ => ●E ([] : leibnizO _)
      ⋅ ◯E ([] : leibnizO _)) : (thread_id -d> (excl_authUR (leibnizO (list nat))))).

  Arguments wpsim_bind_top {_ _ _ _ _ _}.
  Arguments wpsim_wand {_ _ _ _ _ _}.
  Arguments wpsim_ret {_ _ _ _ _ _}.

  Lemma ticketlock_fair:
    ModSim.mod_sim AbsLockW.mod TicketLockW.module.
  Proof.
    eapply WSim.context_sim_implies_modsim. econs.
    { instantiate (1:=init_res). rr. splits.
      { unfold init_res, default_initial_res. disj_tac. }
      { ndtac. }
      { unfold init_res. grawf_tac.
        { apply wmem_init_res_wf. ss. }
        { rewrite comm. apply excl_auth_valid. }
        { apply auth_auth_valid. done. }
        { intros ?. apply excl_auth_valid. }
      }
    }
    unfold init_res. repeat rewrite <- GRA.embed_add.
    exists 2, 1. eexists. lia. exists Ord.omega.
    iIntros "[[[[A0 [A1 A2]] B] C] D]".
    iPoseProof ((init_sat ) with "[A0 A1 A2 B C D]") as "H".
    { iFrame. iSplitL "A1"; auto. }
    simpl. rewrite red_syn_fairI. iMod "H". rewrite red_syn_tgt_interp_as. iDestruct "H" as "[H1 #H2]".
    red_tl; iDestruct "H1" as "[%monok H1]"; red_tl; iDestruct "H1" as "[%tk_mono H1]"; red_tl.
    iDestruct "H1" as "[%wm_mono H1]". rewrite red_syn_inv. iPoseProof "H1" as "#H1".
    iModIntro. iModIntro. iIntros. ss.
    unfold OMod.closed_funs. ss. des_ifs.
    { iIntros (?) "OWN DUTY". unfold Mod.wrap_fun, unwrap. des_ifs.
      2:{ unfold UB. lred. iApply wpsim_UB. }
      lred. rred. iApply wpsim_bind_top.
      iApply (wpsim_wand with "[H1 H2 OWN DUTY]").
      { iPoseProof correct_lock as "SIM". red_tl. iSpecialize ("SIM" $! t).
        red_tl. rewrite red_syn_wpsim. iApply "SIM". iFrame.
        rewrite red_syn_inv; rewrite red_syn_tgt_interp_as. iSplit; done.
      }
      { iIntros (? ?) "H". iModIntro. rred. iApply wpsim_ret. auto. iModIntro.
        red_tl. unfold syn_term_cond. red_tl. simpl. iDestruct "H" as "[[TID DUTY] %H]".
        iFrame. subst. auto.
      }
    }
    { iIntros (?) "OWN DUTY". unfold Mod.wrap_fun, unwrap. des_ifs.
      2:{ unfold UB. lred. iApply wpsim_UB. }
      lred. rred. iApply wpsim_bind_top.
      iApply (wpsim_wand with "[H1 H2 OWN DUTY]").
      { iPoseProof correct_unlock as "SIM". red_tl. iSpecialize ("SIM" $! t).
        red_tl. rewrite red_syn_wpsim. iApply "SIM". iFrame.
        rewrite red_syn_inv; rewrite red_syn_tgt_interp_as. iSplit; done.
      }
      { iIntros (? ?) "H". iModIntro. rred. iApply wpsim_ret. auto. iModIntro.
        red_tl. unfold syn_term_cond. red_tl. simpl. iDestruct "H" as "[[TID DUTY] %H]".
        iFrame. subst. auto.
      }
    }
  Qed.
End TicketLockFair.
