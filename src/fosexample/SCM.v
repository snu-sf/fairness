From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Export ITreeLib WFLibLarge FairBeh NatStructs Mod pind.

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

  Definition val_add (v: val) (n: nat): val :=
    match v with
    | val_nat v => val_nat (v + n)
    | val_ptr (blk, ofs) => val_ptr (blk, ofs + n)
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
End SCMem.

From Fairness Require Import PCM IProp IPMFOS StateRA MonotonePCM.

Section MEMRA.
  Definition memRA: URA.t := (nat ==> nat ==> (Auth.t (Excl.t SCMem.val)))%ra.

  Context `{MEMRA: @GRA.inG memRA Σ}.

  Definition memory_resource_black (m: SCMem.t): memRA :=
    fun blk ofs =>
      match m.(SCMem.contents) blk ofs with
      | Some v => Auth.black (Excl.just v: Excl.t SCMem.val)
      | None => Auth.black (Excl.just (SCMem.val_nat 0): Excl.t SCMem.val) ⋅ Auth.white (Excl.just (SCMem.val_nat 0): Excl.t SCMem.val)
      end.

  Definition points_to_white (blk ofs: nat) (v: SCMem.val): memRA :=
    fun blk' ofs' =>
      if (PeanoNat.Nat.eq_dec blk' blk)
      then if (PeanoNat.Nat.eq_dec ofs' ofs)
           then Auth.white (Excl.just v: Excl.t SCMem.val)
           else URA.unit
      else URA.unit
  .

  Fixpoint points_tos_white (blk ofs: nat) (vs: list SCMem.val): memRA :=
    match vs with
    | vhd::vtl =>
        points_to_white blk ofs vhd ⋅ points_tos_white blk (ofs + 1) vtl
    | [] => URA.unit
    end
  .

  Lemma points_tos_white_eq blk ofs vs blk' ofs'
    :
    points_tos_white blk ofs vs blk' ofs' =
      if (PeanoNat.Nat.eq_dec blk' blk)
      then
        if (Compare_dec.le_gt_dec ofs ofs')
        then
          match nth_error vs (ofs' - ofs) with
          | Some v => Auth.white (Excl.just v: Excl.t SCMem.val)
          | _ => URA.unit
          end
        else URA.unit
      else URA.unit.
  Proof.
    revert blk ofs blk' ofs'. induction vs; ss; i.
    { des_ifs. destruct (ofs' - ofs); ss. }
    ur. ur. rewrite IHvs. unfold points_to_white.
    destruct (PeanoNat.Nat.eq_dec blk' blk); ss.
    2:{ r_solve. }
    subst. destruct (PeanoNat.Nat.eq_dec ofs' ofs).
    { subst. des_ifs; try by exfalso; lia.
      { rewrite PeanoNat.Nat.sub_diag in Heq. ss. inv Heq. r_solve. }
      { rewrite PeanoNat.Nat.sub_diag in Heq. ss. }
    }
    { des_ifs; try by exfalso; lia.
      { replace (ofs' - ofs) with (S (ofs' - (ofs + 1))) in Heq0 by lia.
        ss. clarify. r_solve.
      }
      { replace (ofs' - ofs) with (S (ofs' - (ofs + 1))) in Heq0 by lia.
        ss. clarify.
      }
      { replace (ofs' - ofs) with (S (ofs' - (ofs + 1))) in Heq0 by lia.
        ss. clarify.
      }
      { replace (ofs' - ofs) with (S (ofs' - (ofs + 1))) in Heq0 by lia.
        ss. clarify. r_solve.
      }
      { r_solve.
      }
    }
  Qed.

  Definition memory_black (m: SCMem.t): iProp :=
    OwnM (memory_resource_black m) ∧ ⌜SCMem.wf m⌝.

  Definition points_to (p: SCMem.val) (v: SCMem.val): iProp :=
    match p with
    | SCMem.val_ptr (blk, ofs) => OwnM (points_to_white blk ofs v)
    | _ => False
    end.

  Fixpoint points_tos (p: SCMem.val) (vs: list SCMem.val): iProp :=
    match vs with
    | vhd::vtl =>
        points_to p vhd ** points_tos (SCMem.val_add p 1) vtl
    | [] => True
    end.

  Lemma points_tos_to_resource blk ofs vs
    :
    (OwnM (points_tos_white blk ofs vs))
      -∗
      (points_tos (SCMem.val_ptr (blk, ofs)) vs).
  Proof.
    revert blk ofs. induction vs; ss; i.
    { auto. }
    iIntros "[H0 H1]".
    iPoseProof (IHvs with "H1") as "H1". iFrame.
  Qed.

  Lemma resource_to_points_to blk ofs vs
    :
    (points_tos (SCMem.val_ptr (blk, ofs)) vs)
      -∗
      (OwnM (points_tos_white blk ofs vs)).
  Proof.
    revert blk ofs. induction vs; ss; i.
    { iIntros "_". iPoseProof (@OwnM_unit _ _ MEMRA) as "H". auto. }
    iIntros "[H0 H1]". iSplitL "H0"; auto.
    iApply IHvs. auto.
  Qed.

  Definition memory_empty_resource: memRA :=
    memory_resource_black SCMem.empty.

  Lemma memory_empty_wf: URA.wf memory_empty_resource.
  Proof.
    ur. i. ur. i. ur. unfold memory_empty_resource.
    ur. split; ss. exists ε. r_solve.
  Qed.


  Fixpoint init_points_tos_resource (nb: nat) (l: list nat): memRA :=
    match l with
    | [] => URA.unit
    | sz::tl =>
        points_tos_white (nb + length tl) 0 (repeat (SCMem.val_nat 0) sz) ⋅ init_points_tos_resource nb tl
    end.

  Fixpoint init_points_tos (l: list nat) (vs: list SCMem.val): iProp :=
    match l, vs with
    | sz::tl, vhd::vtl => points_tos vhd (repeat (SCMem.val_nat 0) sz) ** init_points_tos tl vtl
    | [], [] => True
    | _, _ => False
    end.

  Definition memory_init_resource (l: list nat): memRA :=
    memory_resource_black (SCMem.init_mem l) ⋅ init_points_tos_resource 0 l.

  Lemma pointwise_updatabable M K (a b: URA.pointwise K M)
        (POINTWISE: forall k, URA.updatable (a k) (b k))
    :
    URA.updatable a b.
  Proof.
    ii. ur. ur in H. i. eapply POINTWISE; eauto.
  Qed.

  Lemma memory_alloc_updatable m0 sz m1 p
        (ALLOC : SCMem.alloc m0 sz = (m1, p))
        (WF : SCMem.wf m0)
    :
    URA.updatable (memory_resource_black m0)
                  (memory_resource_black m1 ⋅ points_tos_white (SCMem.next_block m0) 0 (repeat (SCMem.val_nat 0) sz)).
  Proof.
    eapply pointwise_updatabable. i.
    eapply pointwise_updatabable. i.
    ur. ur. rewrite points_tos_white_eq.
    unfold SCMem.alloc in ALLOC. inv ALLOC.
    unfold memory_resource_black. ss. des_ifs; try by exfalso; lia.
    { eapply WF in Heq. lia. }
    { eapply WF in Heq. lia. }
    { rewrite URA.unit_id. reflexivity. }
    { eapply WF in Heq. lia. }
    { eapply WF in Heq. lia. }
    { rewrite PeanoNat.Nat.sub_0_r in Heq1.
      hexploit nth_error_repeat; eauto. rewrite Heq1. i. clarify.
    }
    { rewrite PeanoNat.Nat.sub_0_r in Heq1.
      hexploit nth_error_repeat; eauto. rewrite Heq1. i. clarify.
    }
    { rewrite PeanoNat.Nat.sub_0_r in Heq1.
      assert (LT: k0 < length (repeat (SCMem.val_nat 0) sz)).
      { eapply nth_error_Some. rewrite Heq1. ss. }
      rewrite repeat_length in LT. lia.
    }
    { rewrite URA.unit_id. reflexivity. }
    { rewrite URA.unit_id. reflexivity. }
  Qed.

  Lemma memory_ra_alloc m0 sz m1 p
        (ALLOC: SCMem.alloc m0 sz = (m1, p))
    :
    (memory_black m0)
      -∗
      (#=> (memory_black m1 ** points_tos p (repeat (SCMem.val_nat 0) sz))).
  Proof.
    unfold memory_black. iIntros "[BLACK %WF]".
    iAssert (#=> (OwnM (memory_resource_black m1 ⋅ points_tos_white (m0.(SCMem.next_block)) 0 (repeat (SCMem.val_nat 0) sz)))) with "[BLACK]" as "> [BLACK WHITE]".
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
        (* (VAL : (SCMem.contents m0) ofs blk = Some v) *)
    :
    URA.updatable (memory_resource_black m0 ⋅ points_to_white ofs blk v)
                  (memory_resource_black m1).
  Proof.
    do 2 (eapply pointwise_updatabable; i). ur. ur.
    unfold SCMem.free, SCMem.has_permission in FREE. unfold memory_resource_black, points_to_white.
    des_ifs; ss; des_ifs.
    { eapply Auth.auth_update; ii. des. split; ur; ss. revert FRAME; ur. i; des_ifs. }
    { rewrite URA.unit_id. ss. }
    { rewrite URA.unit_id. ss. }
    { rewrite URA.unit_id. eapply Auth.auth_update; ii. des. split; ur; ss. revert FRAME; ur. i; des_ifs. }
    { rewrite URA.unit_id. eapply Auth.auth_update; ii. des. split; ur; ss. revert FRAME; ur. i; des_ifs. }
  Qed.

  Lemma memory_ra_free m0 p v
    :
    (memory_black m0 ** points_to p v)
      -∗
      (∃ m1, ⌜SCMem.free m0 p = Some m1⌝ ** #=> memory_black m1).
  Proof.
    iIntros "[[MB %WF] PTS]".
    unfold memory_black, points_to. des_ifs.
    iCombine "MB PTS" as "OWN". iOwnWf "OWN".
    ur in H. specialize (H n). ur in H. specialize (H n0).
    unfold memory_resource_black, points_to_white in H. des_ifs.
    2:{ ur in H. des. unfold URA.extends in H. des. ur in H. des_ifs. }
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
    OwnM (memory_init_resource l) -∗ (memory_black (SCMem.init_mem l) ** init_points_tos l (SCMem.init_gvars l)).
  Proof.
    iIntros "[BLACK WHITE]". unfold memory_black. iFrame. iSplit.
    { iPureIntro. induction l; ss. unfold SCMem.init_mem in *. ii. ss.
      des_ifs. ss. des_ifs. eapply IHl in SOME; eauto.
    }
    unfold SCMem.init_gvars.
    iStopProof. change 0 with (SCMem.next_block SCMem.empty).
    generalize (SCMem.empty). induction l; i; ss.
    { auto. }
    des_ifs. ss. inv Heq. iIntros "[POINT OWN]".
    change (S (SCMem.next_block t)) with (SCMem.next_block (fst (SCMem.alloc t a))).
    iPoseProof (IHl with "OWN") as "OWN". rewrite Heq0. ss. iFrame.
    iPoseProof (points_tos_to_resource with "POINT") as "POINT".
    replace (SCMem.next_block t0) with (SCMem.next_block t + length l); auto.
    eapply initialize_next_block in Heq0. lia.
  Qed.

  Lemma memory_init_resource_wf l
    :
    URA.wf (memory_init_resource l).
  Proof.
    assert (URA.updatable memory_empty_resource (memory_init_resource l)).
    2:{ exploit (H URA.unit); rewrite URA.unit_id; auto. eapply memory_empty_wf. }
    unfold memory_init_resource.
    unfold memory_empty_resource. unfold SCMem.init_mem.
    change 0 with (SCMem.next_block SCMem.empty).
    cut (SCMem.wf SCMem.empty).
    2:{ ii. ss. }
    generalize SCMem.empty. induction l; i.
    { ss. rewrite URA.unit_id. reflexivity. }
    { etransitivity; eauto. ss. des_ifs; ss.
      rewrite URA.add_assoc. eapply URA.updatable_add; [|reflexivity].
      hexploit memory_alloc_updatable.
      { instantiate (2:=fst (SCMem.alloc _ _)).
        instantiate (1:=snd (SCMem.alloc _ _)). ss.
      }
      { eapply initialize_wf; eauto. }
      i. etrans; eauto. eapply URA.updatable_add.
      { unfold SCMem.alloc. ss. reflexivity. }
      { eapply initialize_next_block in Heq. rewrite Heq. reflexivity. }
    }
    Unshelve. all: ss.
  Qed.

  Lemma memory_ra_load m l v
    :
    (memory_black m)
      -∗
      (points_to l v)
      -∗
      (⌜SCMem.load m l = Some v /\ SCMem.has_permission m l = true⌝).
  Proof.
    iIntros "[BLACK %WF] WHITE".
    unfold memory_black, points_to. des_ifs.
    iCombine "BLACK WHITE" as "OWN". iOwnWf "OWN".
    ur in H. specialize (H n). ur in H. specialize (H n0).
    unfold memory_resource_black, points_to_white in H. des_ifs.
    { ur in H. des. unfold URA.extends in H. des. ur in H. des_ifs.
      iPureIntro. splits; auto.
      unfold SCMem.has_permission. ss. rewrite Heq. ss.
    }
    { ur in H. des. unfold URA.extends in H. des. ur in H. des_ifs. }
  Qed.

  Lemma memory_ra_store m0 l v0 v1
    :
    (memory_black m0)
      -∗
      (points_to l v0)
      -∗
      ∃ m1,
        ((⌜SCMem.store m0 l v1 = Some m1⌝)
           ** #=> (memory_black m1 ** points_to l v1)).
  Proof.
    iIntros "[BLACK %WF] WHITE".
    unfold memory_black, points_to. des_ifs.
    iCombine "BLACK WHITE" as "OWN". iOwnWf "OWN".
    ur in H. specialize (H n). ur in H. specialize (H n0).
    unfold memory_resource_black, points_to_white in H. des_ifs.
    2:{ ur in H. des. unfold URA.extends in H. des. ur in H. des_ifs. }
    unfold SCMem.store. ss. des_ifs. iExists _.
    iSplit; eauto.
    iAssert (#=> OwnM (memory_resource_black (SCMem.mem_update m0 n n0 v1) ⋅  points_to_white n n0 v1)) with "[OWN]" as "> [BLACK WHITE]".
    { iApply (OwnM_Upd with "OWN").
      apply pointwise_updatabable. i. ur.
      apply pointwise_updatabable. i. ur.
      unfold memory_resource_black, points_to_white. ss. des_ifs.
      eapply Auth.auth_update. ii. des. split; ss.
      { ur. ss. }
      { ur in FRAME. ur. des_ifs. }
    }
    { ss. iModIntro. iFrame. iPureIntro.
      unfold SCMem.mem_update. ii. ss. des_ifs; eauto.
    }
  Qed.

  Lemma memory_ra_faa m0 l v addend
    :
    (memory_black m0)
      -∗
      (points_to l v)
      -∗
      ∃ m1,
        ((⌜SCMem.faa m0 l addend = Some (m1, v)⌝)
           ** #=> (memory_black m1 ** points_to l (SCMem.val_add v addend))).
  Proof.
    iIntros "BLACK POINT". unfold SCMem.faa.
    iPoseProof (memory_ra_load with "BLACK POINT") as "%". des. rewrite H.
    iPoseProof (memory_ra_store with "BLACK POINT") as "[% [% H]]".
    iExists m1. rewrite H1. iFrame. auto.
  Qed.

  Lemma memory_ra_compare_nat m n0 n1
    :
    SCMem.compare m (SCMem.val_nat n0) (SCMem.val_nat n1) = Some (if PeanoNat.Nat.eq_dec n0 n1 then true else false).
  Proof.
    ss.
  Qed.

  Lemma memory_ra_compare_ptr_left m n l v
    :
    (memory_black m)
      -∗
      (points_to l v)
      -∗
      (⌜SCMem.compare m (SCMem.val_nat n) l = Some false⌝).
  Proof.
    iIntros "BLACK POINT". ss.
    iPoseProof (memory_ra_load with "BLACK POINT") as "%". des.
    unfold SCMem.unwrap_ptr in H. des_ifs.
  Qed.

  Lemma memory_ra_compare_ptr_right m n l v
    :
    (memory_black m)
      -∗
      (points_to l v)
      -∗
      (⌜SCMem.compare m l (SCMem.val_nat n) = Some false⌝).
  Proof.
    iIntros "BLACK POINT". ss.
    iPoseProof (memory_ra_load with "BLACK POINT") as "%". des.
    unfold SCMem.compare, SCMem.val_compare. des_ifs.
  Qed.

  Lemma memory_ra_compare_ptr_same m l v
    :
    (memory_black m)
      -∗
      (points_to l v)
      -∗
      (⌜SCMem.compare m l l = Some true⌝).
  Proof.
    iIntros "BLACK POINT". ss.
    iPoseProof (memory_ra_load with "BLACK POINT") as "%". des.
    unfold SCMem.compare, SCMem.val_compare. des_ifs.
  Qed.

  Lemma memory_ra_compare_ptr_both m l0 v0 l1 v1
    :
    (memory_black m)
      -∗
      (points_to l0 v0)
      -∗
      (points_to l1 v1)
      -∗
      (⌜SCMem.compare m l0 l1 = Some false⌝).
  Proof.
    iIntros "BLACK POINT0 POINT1". ss.
    iPoseProof (memory_ra_load with "BLACK POINT0") as "%". des.
    iPoseProof (memory_ra_load with "BLACK POINT1") as "%". des.
    unfold SCMem.compare, SCMem.val_compare. des_ifs.
    ss. des_ifs. iCombine "POINT0 POINT1" as "POINT". iOwnWf "POINT".
    ur in H. ur in H. specialize (H n). specialize (H n0). ur in H.
    unfold points_to_white in H. des_ifs. inv Heq1. ur in H. ss.
  Qed.
End MEMRA.

Global Opaque points_to memory_black SCMem.load SCMem.store SCMem.faa SCMem.alloc.
