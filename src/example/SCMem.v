From sflib Require Import sflib.
From Paco Require Import paco.
From stdpp Require Import decidable.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Export ITreeLib WFLibLarge FairBeh Mod pind.

Set Implicit Arguments.

Module SCMem.
  Definition pointer := (nat * nat)%type.

  Variant val: Type :=
    | val_nat (n: nat)
    | val_ptr (p: pointer)
  .

  Let ident := val.

  Definition unwrap_ptr (v: val): option pointer :=
    match v with
    | val_nat _ => None
    | val_ptr p => Some p
    end.

  Definition ptr_eq_dec (p0 p1: pointer): {p0 = p1} + {p0 <> p1}.
  Proof.
    destruct p0 as [blk0 ofs0], p1 as [blk1 ofs1].
    destruct (PeanoNat.Nat.eq_dec blk0 blk1).
    - destruct (PeanoNat.Nat.eq_dec ofs0 ofs1).
      + left. f_equal; assumption.
      + right. ii. inject H. apply n. reflexivity.
    - right. ii. inject H. apply n. reflexivity.
  Qed.

  Definition val_null: val := val_nat 0.

  Definition val_eq_dec (v0 v1: val): {v0 = v1} + {v0 <> v1}.
  Proof.
    destruct v0 as [n0|p0], v1 as [n1|p1].
    - destruct (PeanoNat.Nat.eq_dec n0 n1).
      + left. f_equal; assumption.
      + right. ii. inject H. apply n. reflexivity.
    - right. ii. inject H.
    - right. ii. inject H.
    - destruct (ptr_eq_dec p0 p1).
      + left. f_equal; assumption.
      + right. ii. inject H. apply n. reflexivity.
  Qed.

  Global Instance ptr_eq_dec' : EqDecision pointer.
  Proof. intros x y. apply ptr_eq_dec. Defined.
  Global Instance val_eq_dec' : EqDecision val.
  Proof. intros x y. apply val_eq_dec. Defined.

  Definition val_add (v: val) (n: nat): val :=
    match v with
    | val_nat v => val_nat (v + n)
    | val_ptr (blk, ofs) => val_ptr (blk, ofs + n)
    end.

  Definition val_sub (v: val) (n: nat): val :=
    match v with
    | val_nat v => val_nat (v - n)
    | val_ptr (blk, ofs) => val_ptr (blk, ofs - n)
    end.

  Record t :=
    mk
      {
        contents:> nat -> nat -> option val;
        next_block: nat;
      }.

  Definition wf (m: t): Prop :=
    forall blk ofs v (SOME: m.(contents) blk ofs = Some v),
      blk < m.(next_block).

  Definition has_permission (m: t) (ptr: val): bool :=
    match unwrap_ptr ptr with
    | Some (blk, ofs) =>
        if (m.(contents) blk ofs) then true else false
    | None => false
    end.

  Definition val_compare (m: t) (v0 v1: val): option bool :=
    match v0, v1 with
    | val_nat n0, val_nat n1 => Some (if (PeanoNat.Nat.eq_dec n0 n1) then true else false)
    | val_nat n, val_ptr p
    | val_ptr p, val_nat n =>
        if (has_permission m (val_ptr p))
        then Some false else None
    | val_ptr p0, val_ptr p1 =>
        if (has_permission m (val_ptr p0) && has_permission m (val_ptr p1))%bool then
          Some (if (ptr_eq_dec p0 p1) then true else false)
        else None
    end.

  Definition alloc (m: t) (size: nat): t * val :=
    let nb := (m.(next_block)) in
    (mk (fun blk => if (PeanoNat.Nat.eq_dec blk nb)
                    then
                      fun ofs =>
                        if Compare_dec.le_gt_dec size ofs
                        then None
                        else Some (val_nat 0)
                    else m.(contents) blk) (S nb), val_ptr (nb, 0)).

  Definition free (m : t) (ptr : val) : option t :=
    if has_permission m ptr
    then
      match unwrap_ptr ptr with
      | Some (blk, ofs) =>
          Some (mk (fun blk' => if (PeanoNat.Nat.eq_dec blk' blk)
                                then
                                  fun ofs' => if (PeanoNat.Nat.eq_dec ofs' ofs)
                                              then None
                                              else m.(contents) blk' ofs'
                                else
                                  m.(contents) blk') m.(next_block))
      | None => None
      end
    else None.

  Definition mem_update (m: t) (blk: nat) (ofs: nat) (v: val): t :=
    mk (fun blk' => if (PeanoNat.Nat.eq_dec blk' blk)
                    then
                      fun ofs' => if (PeanoNat.Nat.eq_dec ofs' ofs)
                                  then Some v
                                  else m.(contents) blk' ofs'
                    else m.(contents) blk') m.(next_block).

  Definition store (m: t) (ptr: val) (v: val): option t :=
    match unwrap_ptr ptr with
    | Some (blk, ofs) =>
        if (m.(contents) blk ofs)
        then Some (mem_update m blk ofs v)
        else None
    | None => None
    end.

  Definition load (m: t) (ptr: val): option val :=
    match unwrap_ptr ptr with
    | Some (blk, ofs) =>
        m.(contents) blk ofs
    | _ => None
    end.

  Definition compare (m: t) (v0: val) (v1: val): option bool :=
    val_compare m v0 v1.

  Definition faa (m: t) (ptr: val) (addend: nat): option (t * val) :=
    match (load m ptr) with
    | None => None
    | Some v =>
        match (store m ptr (val_add v addend)) with
        | Some m => Some (m, v)
        | None => None
        end
    end.

  Definition cas (m: t) (ptr: val) (v_old: val) (v_new: val):
    option (t + unit) :=
    match (load m ptr) with
    | Some v =>
        match (val_compare m v v_old) with
        | None => None
        | Some true =>
            match store m ptr v_new with
            | Some m_new => Some (inl m_new)
            | None => None
            end
        | Some false =>
            Some (inr tt)
        end
    | None => None
    end.

  Definition alloc_fun:
    ktree (threadE ident t) nat val :=
    fun sz =>
      m <- trigger (Get id);;
      let (m, v) := alloc m sz in
      _ <- trigger (Put m);;
      Ret v
  .

  Definition store_fun:
    ktree (threadE ident t) (val * val) unit :=
    fun '(vptr, v) =>
      m <- trigger (Get id);;
      m <- unwrap (store m vptr v);;
      _ <- trigger (Put m);;
      Ret tt
  .

  Definition free_fun :
    ktree (threadE ident t) val unit :=
    fun ptr =>
      m <- trigger (Get id);;
      m <- unwrap (free m ptr);;
      _ <- trigger (Put m);;
      Ret tt
  .

  Definition load_fun:
    ktree (threadE ident t) val val :=
    fun vptr =>
      m <- trigger (Get id);;
      v <- unwrap (load m vptr);;
      Ret v
  .

  Definition faa_fun:
    ktree (threadE ident  t) (val * nat) val :=
    fun '(vptr, addend) =>
      m <- trigger (Get id);;
      '(m, v) <- unwrap (faa m vptr addend);;
      _ <- trigger (Put m);;
      Ret v
  .

  Definition cas_fun:
    ktree (threadE ident t) (val * val * val) bool :=
    fun '(vptr, v_old, v_new) =>
      m <- trigger (Get id);;
      mb <- unwrap (cas m vptr v_old v_new);;
      match mb with
      | inl m =>
          _ <- trigger (Put m);;
          Ret true
      | inr _ =>
          Ret false
      end
  .

  Definition cas_weak_fun:
    ktree (threadE ident t) (val * val * val) bool :=
    fun '(vptr, v_old, v_new) =>
      m <- trigger (Get id);;
      b <- trigger (Choose bool);;
      if (b: bool)
      then
        mb <- unwrap (cas m vptr v_old v_new);;
        match mb with
        | inl m =>
            _ <- trigger (Put m);;
            Ret true
        | inr _ =>
            Ret false
        end
      else
        if has_permission m vptr
        then
          _ <- trigger (Fair (fun i => if val_eq_dec i vptr then Flag.fail else Flag.success));;
          Ret false
        else UB
  .

  Definition compare_fun:
    ktree (threadE ident t) (val * val) bool :=
    fun '(v0, v1) =>
      m <- trigger (Get id);;
      b <- unwrap (compare m v0 v1);;
      Ret b
  .

  Definition empty: t := mk (fun _ _ => None) 0.

  Fixpoint initialize (m: t) (l: list nat): t * list val :=
    match l with
    | hd::tl =>
        let (m, vs) := initialize m tl in
        let (m, v) := alloc m hd in
        (m, v::vs)
    | [] => (m, [])
    end.

  Definition init_gvars (l: list nat): list val := snd (initialize empty l).

  Definition init_mem (l: list nat): t := fst (initialize empty l).

  Definition mod (gvars: list nat): Mod.t :=
    Mod.mk
      (init_mem gvars)
      (Mod.get_funs [("alloc", Mod.wrap_fun alloc_fun);
                     ("store", Mod.wrap_fun store_fun);
                     ("load", Mod.wrap_fun load_fun);
                     ("faa", Mod.wrap_fun faa_fun);
                     ("cas", Mod.wrap_fun cas_fun);
                     ("cas_weak", Mod.wrap_fun cas_weak_fun);
                     ("compare", Mod.wrap_fun compare_fun)
      ]).

  (* Some lemmas. *)

  Lemma val_compare_Some m v1 v2 b :
    SCMem.val_compare m v1 v2 = Some b ->
    if b then v1 = v2 else v1 <> v2.
  Proof.
    unfold SCMem.val_compare. i. des_ifs; ii; inv H0; congruence.
  Qed.

  Lemma has_permission_store m m' l stv v :
    SCMem.store m l stv = Some m' ->
    has_permission m v = has_permission m' v.
  Proof.
    unfold SCMem.store, SCMem.mem_update, SCMem.unwrap_ptr.
    des_ifs. i. des_ifs. unfold has_permission in *. des_ifs; ss; des_ifs.
  Qed.

  Lemma val_compare_store m m' l stv v0 v1 :
    SCMem.store m l stv = Some m' ->
    val_compare m v0 v1 = val_compare m' v0 v1.
  Proof.
    i. unfold val_compare.
    des_ifs; try (exploit (has_permission_store); eauto; rewrite Heq, Heq0; i; ss).
    all: exfalso; unfold store, mem_update, has_permission, unwrap_ptr in *; des_ifs; ss; des_ifs.
  Qed.

  Lemma has_permission_compare m v0 v1 :
    has_permission m v0 = true -> has_permission m v1 = true -> val_compare m v0 v1 <> None.
  Proof.
    unfold has_permission, val_compare. i. des_ifs.
    exfalso. unfold has_permission, unwrap_ptr in *. des_ifs.
  Qed.

  (* Definition memory_comparable (m : SCMem.t) (v : SCMem.val) : Prop := *)
  (*   match (SCMem.unwrap_ptr v) with *)
  (*   | Some (vb, vo) => *)
  (*       match (SCMem.contents m) vb vo with *)
  (*       | Some vv => True *)
  (*       | None => False *)
  (*       end *)
  (*   | _ => True *)
  (*   end. *)

  (* Lemma memory_comparable_store m m' l stv v : *)
  (*   SCMem.store m l stv = Some m' -> *)
  (*   memory_comparable m v -> memory_comparable m' v. *)
  (* Proof. *)
  (*   unfold SCMem.store, SCMem.mem_update, SCMem.unwrap_ptr. *)
  (*   des_ifs. i. des_ifs. unfold memory_comparable in *. des_ifs. ss. des_ifs.     *)
  (* Qed. *)

  (* Lemma val_compare_None m v1 v2 : *)
  (*   SCMem.val_compare m v1 v2 = None -> *)
  (*   (memory_comparable m v1 /\ memory_comparable m v2) -> False. *)
  (* Proof. *)
  (*   unfold memory_comparable. unfold SCMem.val_compare, SCMem.has_permission. *)
  (*   i. des_ifs; des; clarify. *)
  (* Qed. *)

  (* Lemma has_permission_comparable m v : *)
  (*   has_permission m v = true -> memory_comparable m v. *)
  (* Proof. *)
  (*   unfold has_permission, memory_comparable. i. des_ifs. *)
  (* Qed. *)

End SCMem.

Coercion SCMem.val_nat : nat >-> SCMem.val.
Coercion SCMem.val_ptr : SCMem.pointer >-> SCMem.val.

(** RA for SCMem. *)

From iris.algebra Require Import cmra updates lib.gmap_view.
From Fairness Require Import PCM IPM IPropAux MonotoneRA Axioms.

Section MEMRA.
  Context `{heap_name : nat}.
  Definition memRA: ucmra := (nat ==> nat ==> (gmap_viewUR unit (leibnizO SCMem.val)))%ra.

  Context `{MEMRA: @GRA.inG memRA Σ}.
  Notation iProp := (iProp Σ).

  Definition memory_resource_black (m: SCMem.t): memRA :=
    fun blk ofs =>
      match m.(SCMem.contents) blk ofs with
      | Some v => gmap_view_auth (DfracOwn 1) {[ () := (v : leibnizO _)]}
      | None => gmap_view_auth (DfracOwn 1) {[ () := (0 : SCMem.val) : leibnizO _]} ⋅
                gmap_view_frag () (DfracOwn 1) ((0 : SCMem.val) : leibnizO _)
      end.

  Definition points_to_white (blk ofs: nat) (v: SCMem.val) (dq : dfrac) : memRA :=
    fun blk' ofs' =>
      if (PeanoNat.Nat.eq_dec blk' blk)
      then if (PeanoNat.Nat.eq_dec ofs' ofs)
           then
            gmap_view_frag () dq (v : leibnizO _)
           else ε
      else ε
  .

  Fixpoint points_tos_white (blk ofs: nat) (vs: list SCMem.val) (dq : dfrac) : memRA :=
    match vs with
    | vhd::vtl =>
        points_to_white blk ofs vhd dq ⋅ points_tos_white blk (ofs + 1) vtl dq
    | [] => ε
    end
  .


  Lemma points_tos_white_eq blk ofs vs dq blk' ofs'
    :
    points_tos_white blk ofs vs dq blk' ofs' ≡
      if (PeanoNat.Nat.eq_dec blk' blk)
      then
        if (Compare_dec.le_gt_dec ofs ofs')
        then
          match nth_error vs (ofs' - ofs) with
          | Some v => gmap_view_frag () dq (v : leibnizO _)
          | _ => ε
          end
        else ε
      else ε.
  Proof.
    revert blk ofs blk' ofs'. induction vs; ss; i.
    { des_ifs; destruct (ofs' - ofs); ss. }
    rewrite !discrete_fun_lookup_op IHvs /points_to_white.
    destruct (PeanoNat.Nat.eq_dec blk' blk); ss.
    2:{ r_solve. }
    subst. destruct (PeanoNat.Nat.eq_dec ofs' ofs).
    { subst. des_ifs; try by exfalso; lia.
      all: rewrite PeanoNat.Nat.sub_diag in Heq; ss.
      all: inv Heq; r_solve.
    }
    { des_ifs; try by exfalso; lia.
      all: try (replace (ofs' - ofs) with (S (ofs' - (ofs + 1))) in Heq0 by lia).
      all: ss; clarify; r_solve.
    }
  Qed.

  Definition memory_black (m: SCMem.t): iProp :=
    OwnM (memory_resource_black m) ∧ ⌜SCMem.wf m⌝.

  Definition points_to (p: SCMem.val) (v: SCMem.val) dq: iProp :=
    match p with
    | SCMem.val_ptr (blk, ofs) => OwnM (points_to_white blk ofs v dq)
    | _ => False
    end.

  Fixpoint points_tos (p: SCMem.val) (vs: list SCMem.val) dq: iProp :=
    match vs with
    | vhd::vtl =>
        points_to p vhd dq ∗ points_tos (SCMem.val_add p 1) vtl dq
    | [] => True
    end.

  Lemma points_tos_to_resource blk ofs vs dq
    :
    (OwnM (points_tos_white blk ofs vs dq))
      -∗
      (points_tos (SCMem.val_ptr (blk, ofs)) vs dq).
  Proof.
    revert blk ofs. induction vs; ss; i.
    { iIntros "_". iPureIntro. auto. }
    iIntros "[H0 H1]".
    iPoseProof (IHvs with "H1") as "H1". iFrame.
  Qed.

  Lemma resource_to_points_to blk ofs vs dq
    :
    (points_tos (SCMem.val_ptr (blk, ofs)) vs dq)
      -∗
      (OwnM (points_tos_white blk ofs vs dq)).
  Proof.
    revert blk ofs. induction vs; ss; i.
    { iIntros "_". iPoseProof (@OwnM_unit _ _ MEMRA) as "H". auto. }
    iIntros "[H0 H1]". iSplitL "H0"; auto.
    iApply IHvs. auto.
  Qed.

  Definition memory_empty_resource: memRA :=
    memory_resource_black SCMem.empty.

  Lemma memory_empty_wf: ✓ memory_empty_resource.
  Proof.
    intros blk ofs. rewrite /memory_empty_resource /memory_resource_black.
    simpl. apply gmap_view_both_valid. done.
  Qed.


  Fixpoint init_points_tos_resource (nb: nat) (l: list nat): memRA :=
    match l with
    | [] => ε
    | sz::tl =>
        points_tos_white (nb + length tl) 0 (repeat (SCMem.val_nat 0) sz) (DfracOwn 1) ⋅ init_points_tos_resource nb tl
    end.

  Fixpoint init_points_tos (l: list nat) (vs: list SCMem.val): iProp :=
    match l, vs with
    | sz::tl, vhd::vtl => points_tos vhd (repeat (SCMem.val_nat 0) sz) (DfracOwn 1) ∗ init_points_tos tl vtl
    | [], [] => True
    | _, _ => False
    end.

  Definition memory_init_resource (l: list nat): memRA :=
    memory_resource_black (SCMem.init_mem l) ⋅ init_points_tos_resource 0 l.

  Lemma pointwise_updatabable M K (a b: pointwise K M)
        (POINTWISE: forall k, (a k) ~~> (b k))
    :
    a ~~> b.
  Proof. apply cmra_update_discrete_fun, POINTWISE. Qed.

  Lemma memory_alloc_updatable m0 sz m1 p
        (ALLOC : SCMem.alloc m0 sz = (m1, p))
        (WF : SCMem.wf m0)
    :
      (memory_resource_black m0) ~~>
      (memory_resource_black m1 ⋅ points_tos_white (SCMem.next_block m0) 0 (repeat (SCMem.val_nat 0) sz) (DfracOwn 1)).
  Proof.
    eapply pointwise_updatabable. i.
    eapply pointwise_updatabable. i.
    rewrite !discrete_fun_lookup_op points_tos_white_eq.
    unfold SCMem.alloc in ALLOC. inv ALLOC.
    unfold memory_resource_black. ss. des_ifs; try by exfalso; lia.
    { eapply WF in Heq. lia. }
    { eapply WF in Heq. lia. }
    { rewrite right_id. reflexivity. }
    { eapply WF in Heq. lia. }
    { eapply WF in Heq. lia. }
    { rewrite PeanoNat.Nat.sub_0_r in Heq1.
      hexploit nth_error_repeat; eauto. erewrite Heq1. i. clarify.
    }
    { rewrite PeanoNat.Nat.sub_0_r in Heq1.
      hexploit nth_error_repeat; eauto. erewrite Heq1. i. clarify.
    }
    { rewrite PeanoNat.Nat.sub_0_r in Heq1.
      assert (LT: k0 < length (repeat (SCMem.val_nat 0) sz)).
      { eapply nth_error_Some. rewrite Heq1. ss. }
      rewrite repeat_length in LT. lia.
    }
    { rewrite right_id. reflexivity. }
    { rewrite right_id. reflexivity. }
  Qed.

  Lemma memory_ra_alloc m0 sz m1 p
        (ALLOC: SCMem.alloc m0 sz = (m1, p))
    :
    (memory_black m0)
      -∗
      (#=> (memory_black m1 ∗ points_tos p (repeat (SCMem.val_nat 0) sz) (DfracOwn 1))).
  Proof.
    unfold memory_black. iIntros "[BLACK %WF]".
    iAssert (#=> (OwnM (memory_resource_black m1 ⋅ points_tos_white (m0.(SCMem.next_block)) 0 (repeat (SCMem.val_nat 0) sz) (DfracOwn 1)))) with "[BLACK]" as "> [BLACK WHITE]".
    { iApply (OwnM_Upd with "BLACK").
      eapply memory_alloc_updatable; eauto.
    }
    unfold SCMem.alloc in ALLOC. inv ALLOC.
    iModIntro. iFrame. iSplit.
    { iPureIntro. ii. ss. des_ifs. eapply WF in SOME; eauto. }
    { iApply points_tos_to_resource. ss. }
  Qed.

  Lemma memory_free_updatable m0 m1 p ofs blk v
        (FREE : SCMem.free m0 p = Some m1)
        (WF : SCMem.wf m0)
        (PTR : SCMem.unwrap_ptr p = Some (ofs, blk))
    :
    (memory_resource_black m0 ⋅ points_to_white ofs blk v (DfracOwn 1))
    ~~> (memory_resource_black m1).
  Proof.
    do 2 (eapply pointwise_updatabable; i).
    rewrite !discrete_fun_lookup_op.
    unfold SCMem.free, SCMem.has_permission in FREE. unfold memory_resource_black, points_to_white.
    des_ifs; ss; des_ifs.
    { etrans.
      { apply gmap_view_delete. }
      rewrite delete_singleton. etrans.
      { eapply (gmap_view_alloc _ () (DfracOwn 1)); auto. done. }
      rewrite insert_empty. reflexivity.
    }
    { rewrite right_id. ss. }
    { rewrite right_id. ss. }
    { rewrite right_id. ss. }
    { rewrite right_id. ss. }
  Qed.

  Lemma memory_ra_free m0 p v
    :
    (memory_black m0 ∗ points_to p v (DfracOwn 1))
      -∗
      (∃ m1, ⌜SCMem.free m0 p = Some m1⌝ ∗ #=> memory_black m1).
  Proof.
    iIntros "[[MB %WF] PTS]".
    unfold memory_black, points_to. des_ifs.
    iCombine "MB PTS" as "OWN". iOwnWf "OWN".
    specialize (H n n0).
    unfold memory_resource_black, points_to_white in H.
    rewrite !discrete_fun_lookup_op in H. des_ifs.
    2:{ exfalso. rewrite -(assoc cmra.op) in H.
        apply cmra_valid_op_r,gmap_view_frag_op_valid in H.
        des. done.
    }
    remember (SCMem.free _ _) as m1 eqn:FREE. pose proof FREE as FREE'. revert FREE'.
    unfold SCMem.free, SCMem.has_permission in FREE. ss. des_ifs. remember (SCMem.mk _ _) as m1. i.
    iExists m1. iSplit; eauto.
    iAssert (#=> (OwnM (memory_resource_black m1))) with "[OWN]" as "> RB".
    { iApply (OwnM_Upd with "OWN").
      eapply memory_free_updatable; eauto. }
    iModIntro. iFrame. iPureIntro. ii. unfold SCMem.free in FREE'.
    des_ifs; ss; des_ifs; eapply WF in SOME; eauto.
  Qed.

  Lemma initialize_next_block m0 l m1 vs
        (INIT: SCMem.initialize m0 l = (m1, vs))
    :
    m1.(SCMem.next_block) = m0.(SCMem.next_block) + length l.
  Proof.
    revert m0 m1 vs INIT. induction l; i; ss.
    { clarify. }
    { des_ifs. ss. eapply IHl in Heq. rewrite Heq. auto. }
  Qed.

  Lemma initialize_wf m0 l m1 vs
        (INIT: SCMem.initialize m0 l = (m1, vs))
        (WF: SCMem.wf m0)
    :
    SCMem.wf m1.
  Proof.
    revert m0 m1 vs INIT WF. induction l; i; ss.
    { clarify. }
    { des_ifs. ii. ss. des_ifs. exploit IHl; eauto. }
  Qed.

  Lemma memory_init_iprop l
    :
    OwnM (memory_init_resource l) -∗ (memory_black (SCMem.init_mem l) ∗ init_points_tos l (SCMem.init_gvars l)).
  Proof.
    iIntros "[BLACK WHITE]". unfold memory_black. iFrame. iSplit.
    { iPureIntro. induction l; ss. unfold SCMem.init_mem in *. ii. ss.
      des_ifs. ss. des_ifs. eapply IHl in SOME; eauto.
    }
    unfold SCMem.init_gvars.
    replace 0 with (SCMem.next_block SCMem.empty); [|done].
    move: SCMem.empty => t.
    iInduction (l) as [|i l] "IHl" forall (t); ss.
    des_ifs. ss. inv Heq. iDestruct "WHITE" as "[POINT OWN]".
    change (S (SCMem.next_block t)) with (SCMem.next_block (fst (SCMem.alloc t a))).
    iPoseProof ("IHl" with "OWN") as "OWN". rewrite Heq0. ss. iFrame.
    iPoseProof (points_tos_to_resource with "POINT") as "POINT".
    replace (SCMem.next_block t0) with (SCMem.next_block t + length l); auto.
    eapply initialize_next_block in Heq0. lia.
  Qed.

  Lemma memory_init_resource_wf l
    :
    ✓ (memory_init_resource l).
  Proof.
    assert (memory_empty_resource ~~> (memory_init_resource l)).
    2:{ intros b o. rewrite cmra_discrete_update in H. exploit (H ε).
        - rewrite right_id; auto; eapply memory_empty_wf.
        - rewrite !discrete_fun_lookup_op. rewrite right_id. done.
      }
    unfold memory_init_resource.
    unfold memory_empty_resource. unfold SCMem.init_mem.
    change 0 with (SCMem.next_block SCMem.empty).
    cut (SCMem.wf SCMem.empty).
    2:{ ii. ss. }
    generalize SCMem.empty. induction l; i.
    { ss. rewrite right_id. reflexivity. }
    { etransitivity; eauto. ss. des_ifs; ss.
      rewrite (assoc cmra.op). eapply cmra_update_op; [|reflexivity].
      hexploit memory_alloc_updatable.
      { instantiate (2:=fst (SCMem.alloc _ _)).
        instantiate (1:=snd (SCMem.alloc _ _)). ss.
      }
      { eapply initialize_wf; eauto. }
      i. etrans; eauto. eapply cmra_update_op.
      { unfold SCMem.alloc. ss. reflexivity. }
      { eapply initialize_next_block in Heq. rewrite Heq. reflexivity. }
    }
    Unshelve. all: ss.
  Qed.

  Lemma memory_ra_load m l v dq
    :
    (memory_black m)
      -∗
      (points_to l v dq)
      -∗
      (⌜SCMem.load m l = Some v /\ SCMem.has_permission m l = true⌝).
  Proof.
    iIntros "[BLACK %WF] WHITE".
    unfold memory_black, points_to. des_ifs.
    iCombine "BLACK WHITE" as "OWN". iOwnWf "OWN".
    specialize (H n n0). rewrite !discrete_fun_lookup_op in H.
    unfold memory_resource_black, points_to_white in H. des_ifs.
    { iPureIntro. apply gmap_view_both_valid in H.
      rewrite lookup_singleton in H.
      des. inv H0. rewrite <-H3.
      splits; auto.
      unfold SCMem.has_permission. ss. rewrite Heq. ss.
    }
    { exfalso. rewrite -(assoc cmra.op) in H.
      apply cmra_valid_op_r,gmap_view_frag_op_valid in H.
      des. apply exclusive_l in H; [done|apply _].
    }
  Qed.

  Lemma memory_ra_has_permission m l v dq
    :
    (memory_black m)
      -∗
      (points_to l v dq)
      -∗
      (⌜SCMem.has_permission m l = true⌝).
  Proof.
    iIntros "BLACK WHITE". iPoseProof (memory_ra_load with "BLACK WHITE") as "%".
    des; auto.
  Qed.

  Lemma memory_ra_store m0 l v0 v1
    :
    (memory_black m0)
      -∗
      (points_to l v0 (DfracOwn 1))
      -∗
      ∃ m1,
        ((⌜SCMem.store m0 l v1 = Some m1⌝)
           ∗ #=> (memory_black m1 ∗ points_to l v1 (DfracOwn 1))).
  Proof.
    iIntros "[BLACK %WF] WHITE".
    unfold memory_black, points_to. des_ifs.
    iCombine "BLACK WHITE" as "OWN". iOwnWf "OWN".
    specialize (H n n0). rewrite !discrete_fun_lookup_op in H.
    unfold memory_resource_black, points_to_white in H. des_ifs.
    2:{ exfalso. rewrite -(assoc cmra.op) in H.
        apply cmra_valid_op_r,gmap_view_frag_op_valid in H.
        des. apply exclusive_l in H; [done|apply _].
      }
    unfold SCMem.store. ss. des_ifs. iExists _.
    iSplitR; [iPureIntro; eauto|].
    iAssert (#=> OwnM (memory_resource_black (SCMem.mem_update m0 n n0 v1) ⋅  points_to_white n n0 v1 (DfracOwn 1))) with "[OWN]" as "> [BLACK WHITE]".
    { iApply (OwnM_Upd with "OWN").
      apply pointwise_updatabable. i.
      apply pointwise_updatabable. i.
      rewrite !discrete_fun_lookup_op.
      unfold memory_resource_black, points_to_white. ss. des_ifs.
      etrans.
      { apply gmap_view_delete. }
      rewrite delete_singleton. etrans.
      { eapply (gmap_view_alloc _ () (DfracOwn 1)); auto. done. }
      rewrite insert_empty. reflexivity.
    }
    { ss. iModIntro. iFrame. iPureIntro.
      unfold SCMem.mem_update. ii. ss. des_ifs; eauto.
    }
  Qed.

  Lemma memory_ra_faa m0 l v addend
    :
    (memory_black m0)
      -∗
      (points_to l v (DfracOwn 1))
      -∗
      ∃ m1,
        ((⌜SCMem.faa m0 l addend = Some (m1, v)⌝)
           ∗ #=> (memory_black m1 ∗ points_to l (SCMem.val_add v addend) (DfracOwn 1))).
  Proof.
    iIntros "BLACK POINT". unfold SCMem.faa.
    iPoseProof (memory_ra_load with "BLACK POINT") as "%". des. rewrite H.
    iPoseProof (memory_ra_store with "BLACK POINT") as "[% [% H]]".
    iExists m1. erewrite H1. iFrame. auto.
  Qed.

  Lemma memory_ra_compare_nat m n0 n1
    :
    SCMem.compare m (SCMem.val_nat n0) (SCMem.val_nat n1) = Some (if PeanoNat.Nat.eq_dec n0 n1 then true else false).
  Proof.
    ss.
  Qed.

  Lemma memory_ra_compare_ptr_left m n l v dq
    :
    (memory_black m)
      -∗
      (points_to l v dq)
      -∗
      (⌜SCMem.compare m (SCMem.val_nat n) l = Some false⌝).
  Proof.
    iIntros "BLACK POINT". ss.
    iPoseProof (memory_ra_load with "BLACK POINT") as "%". des.
    unfold SCMem.unwrap_ptr in H. des_ifs.
  Qed.

  Lemma memory_ra_compare_ptr_right m n l v dq
    :
    (memory_black m)
      -∗
      (points_to l v dq)
      -∗
      (⌜SCMem.compare m l (SCMem.val_nat n) = Some false⌝).
  Proof.
    iIntros "BLACK POINT". ss.
    iPoseProof (memory_ra_load with "BLACK POINT") as "%". des.
    unfold SCMem.compare, SCMem.val_compare. des_ifs.
  Qed.

  Lemma memory_ra_compare_ptr_same m l v dq
    :
    (memory_black m)
      -∗
      (points_to l v dq)
      -∗
      (⌜SCMem.compare m l l = Some true⌝).
  Proof.
    iIntros "BLACK POINT". ss.
    iPoseProof (memory_ra_load with "BLACK POINT") as "%". des.
    unfold SCMem.compare, SCMem.val_compare. des_ifs.
  Qed.

  (* Note: can be slightly more general, one of the points-to can be dqistent. *)
  Lemma memory_ra_compare_ptr_both m l0 v0 l1 v1
    :
    (memory_black m)
      -∗
      (points_to l0 v0 (DfracOwn 1))
      -∗
      (points_to l1 v1 (DfracOwn 1))
      -∗
      (⌜SCMem.compare m l0 l1 = Some false⌝).
  Proof.
    iIntros "BLACK POINT0 POINT1". ss.
    iPoseProof (memory_ra_load with "BLACK POINT0") as "%". des.
    iPoseProof (memory_ra_load with "BLACK POINT1") as "%". des.
    unfold SCMem.compare, SCMem.val_compare. des_ifs.
    ss. des_ifs. iCombine "POINT0 POINT1" as "POINT". iOwnWf "POINT".
    specialize (H n n0).
    rewrite !discrete_fun_lookup_op in H.
    unfold points_to_white in H. des_ifs.
    apply gmap_view_frag_op_valid in H. des.
    apply exclusive_l in H; [done|apply _].
  Qed.

  Lemma memory_ra_compare_ptr_both_gen m l0 v0 l1 v1 p1 p2
    :
    (memory_black m)
      -∗
      (points_to l0 v0 p1)
      -∗
      (points_to l1 v1 p2)
      -∗
      (⌜SCMem.compare m l0 l1 = Some (bool_decide (l0=l1))⌝).
  Proof.
    iIntros "BLACK POINT0 POINT1". ss.
    iPoseProof (memory_ra_load with "BLACK POINT0") as "%". des.
    iPoseProof (memory_ra_load with "BLACK POINT1") as "%". des.
    unfold SCMem.compare, SCMem.val_compare. des_ifs. ss. des_ifs.
    { case_bool_decide; done. }
    case_bool_decide as EQ; try done. injection EQ as ->. done.
  Qed.

  Lemma memory_ra_points_to_agree l v0 v1 p1 p2
    :
      (points_to l v0 p1)
      -∗
      (points_to l v1 p2)
      -∗
      (⌜v0 = v1⌝).
  Proof.
    iIntros "POINT0 POINT1". ss.
    destruct l as [n|[b o]]; ss.
    iCombine "POINT0 POINT1" as "POINT". iOwnWf "POINT".
    iPureIntro.
    specialize (H b o). rewrite !discrete_fun_lookup_op in H.
    unfold points_to_white in H. des_ifs; clarify.
    apply gmap_view_frag_op_valid in H. des.
    rewrite H0. done.
  Qed.

  (* Lemma memory_ra_compare_ptr_both_dq_left m l0 v0 l1 v1
    :
    (memory_black m)
      -∗
      (points_to l0 v0 false)
      -∗
      (points_to l1 v1 true)
      -∗
      (⌜SCMem.compare m l0 l1 = Some false⌝).
  Proof.
    iIntros "BLACK POINT0 POINT1". ss.
    iPoseProof (memory_ra_load with "BLACK POINT0") as "%". des.
    iPoseProof (memory_ra_load with "BLACK POINT1") as "%". des.
    unfold SCMem.compare, SCMem.val_compare. des_ifs.
    ss. des_ifs. iCombine "POINT0 POINT1" as "POINT". iOwnWf "POINT".
    ur in H. ur in H. specialize (H n). specialize (H n0). ur in H.
    unfold points_to_white in H. des_ifs. inv Heq1.
    apply dfrac_agree_op_valid in H. des. done.
  Qed. *)

  (* Persistency lemmas *)

  Global Instance points_to_discarded_persistent l v : Persistent (points_to l v DfracDiscarded).
  Proof.
    rewrite /points_to /points_to_white. des_ifs; try apply _.
    rewrite /Persistent. iIntros "H".
    iDestruct (own_persistent with "H") as "#HP".
    iModIntro. iApply (OwnM_proper with "HP").
    intros blk' ofs'. rewrite !discrete_fun_lookup_core.
    des_ifs; rewrite core_id_core //.
  Qed.
  Global Instance points_tos_discarded_persistent l vs : Persistent (points_tos l vs DfracDiscarded).
  Proof. revert l. induction vs; apply _. Qed.

  Lemma points_to_persist l dq v :
    points_to l v dq ==∗ points_to l v DfracDiscarded.
  Proof.
    unfold points_to,points_to_white. des_ifs.
    { by iIntros (?). }
    apply OwnM_Upd,pointwise_updatable=>blk'. apply pointwise_updatabable=>ofs'.
    des_ifs.
    apply gmap_view_frag_persist.
  Qed.
  Lemma points_tos_persist l dq vs :
    points_tos l vs dq ==∗ points_tos l vs DfracDiscarded.
  Proof.
    revert l. induction vs as [|v vs IH]; i; ss.
    { by iIntros (?). }
    iIntros "(l↦ & l↦s)".
    iMod (points_to_persist with "l↦") as "$".
    iMod (IH with "l↦s") as "$".
    done.
  Qed.
End MEMRA.

From Fairness Require Import TemporalLogic.

Section SPROP.

  Context {STT : StateTypes}.
  Context `{sub : @SRA.subG Γ Σ}.
  Context {TLRASs : TLRAs_small STT Γ}.
  Context {TLRAS : TLRAs STT Γ Σ}.

  Context {HasMEMRA: @GRA.inG memRA Γ}.

  Definition s_memory_black {n} (m : SCMem.t) : sProp n :=
    (➢(memory_resource_black m) ∧ ⌜SCMem.wf m⌝)%S.

  Lemma red_s_memory_black n m :
    ⟦s_memory_black m, n⟧ = memory_black m.
  Proof.
    unfold s_memory_black. red_tl. ss.
  Qed.

  Definition s_points_to {n} (p: SCMem.val) (v: SCMem.val) dq : sProp n :=
    match p with
    | SCMem.val_ptr (blk, ofs) => (➢ (points_to_white blk ofs v dq))%S
    | _ => ⌜False⌝%S
    end.

  Lemma red_s_points_to n p v dq :
    ⟦s_points_to p v dq, n⟧ = points_to p v dq.
  Proof.
    unfold s_points_to, points_to. des_ifs. red_tl. ss.
  Qed.

  Fixpoint s_points_tos {n} (p: SCMem.val) (vs: list SCMem.val) dq : sProp n :=
    match vs with
    | vhd::vtl =>
        (s_points_to p vhd dq ∗ s_points_tos (SCMem.val_add p 1) vtl dq)%S
    | [] => ⌜True⌝%S
    end.

  Lemma red_s_points_tos n p vs dq :
    ⟦s_points_tos p vs dq, n⟧ = points_tos p vs dq.
  Proof.
    revert p. induction vs; i; ss. red_tl. erewrite IHvs.
    f_equal. apply red_s_points_to.
  Qed.

End SPROP.

Global Opaque points_to memory_black SCMem.load SCMem.store SCMem.faa SCMem.alloc SCMem.free SCMem.cas.

Ltac red_tl_memra := (try rewrite ! red_s_memory_black;
                      try rewrite ! red_s_points_to;
                      try rewrite ! red_s_points_tos
                     ).
Ltac red_tl_memra_s := (try setoid_rewrite red_s_memory_black;
                        try setoid_rewrite red_s_points_to;
                        try setoid_rewrite red_s_points_tos
                       ).

Notation "l ↦{ dq } v" := (points_to l v dq) (at level 90, v at level 1) : bi_scope.
Notation "l ↦{ dq } v" := (s_points_to l v dq) (at level 90, v at level 1) : sProp_scope.
Notation "l ↦{# q } v" := (points_to l v (DfracOwn q)) (at level 90, v at level 1) : bi_scope.
Notation "l ↦{# q } v" := (s_points_to l v (DfracOwn q)) (at level 90, v at level 1) : sProp_scope.
Notation "l ↦ v" := (points_to l v (DfracOwn 1)) (at level 90, v at level 1) : bi_scope.
Notation "l ↦ v" := (s_points_to l v (DfracOwn 1)) (at level 90, v at level 1) : sProp_scope.
Notation "l ↦□ v" := (points_to l v DfracDiscarded) (at level 90, v at level 1) : bi_scope.
Notation "l ↦□ v" := (s_points_to l v DfracDiscarded) (at level 90, v at level 1) : sProp_scope.

Notation "l ↦∗{ dq } vs" := (points_tos l vs dq) (at level 90, vs at level 1) : bi_scope.
Notation "l ↦∗{ dq } vs" := (s_points_tos l vs dq) (at level 90, vs at level 1) : sProp_scope.
Notation "l ↦*{# q } v" := (points_tos l v (DfracOwn q)) (at level 90, v at level 1) : bi_scope.
Notation "l ↦*{# q } v" := (s_points_tos l v (DfracOwn q)) (at level 90, v at level 1) : sProp_scope.
Notation "l ↦∗ vs" := (points_tos l vs (DfracOwn 1)) (at level 90, vs at level 1) : bi_scope.
Notation "l ↦∗ vs" := (s_points_tos l vs (DfracOwn 1)) (at level 90, vs at level 1) : sProp_scope.
Notation "l ↦∗□ vs" := (points_tos l vs DfracDiscarded) (at level 90, vs at level 1) : bi_scope.
Notation "l ↦∗□ vs" := (s_points_tos l vs DfracDiscarded) (at level 90, vs at level 1) : sProp_scope.
