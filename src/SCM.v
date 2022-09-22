From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Export ITreeLib WFLib FairBeh NatStructs Mod pind.

Set Implicit Arguments.

Module SCMem.
  Definition pointer := (nat * nat)%type.

  Variant val: Type :=
    | val_nat (n: nat)
    | val_ptr (p: pointer)
  .

  Definition unwrap_ptr (v: val): option pointer :=
    match v with
    | val_nat _ => None
    | val_ptr p => Some p
    end.

  Definition val_null: val := val_nat 0.

  Definition val_eq_dec (v0 v1: val): {v0 = v1} + {v0 <> v1}.
  Proof.
    destruct v0 as [n0|[blk0 ofs0]], v1 as [n1|[blk1 ofs1]].
    - destruct (PeanoNat.Nat.eq_dec n0 n1).
      + left. f_equal; assumption.
      + right. ii. inject H. apply n. reflexivity.
    - right. ii. inject H.
    - right. ii. inject H.
    - destruct (PeanoNat.Nat.eq_dec blk0 blk1).
      + destruct (PeanoNat.Nat.eq_dec ofs0 ofs1).
        * left. f_equal. f_equal; assumption.
        * right. ii. inject H. apply n. reflexivity.
      + right. ii. inject H. apply n. reflexivity.
  Defined.

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

  Definition val_valid (m: t) (v: val): bool :=
    match v with
    | val_nat _ => true
    | val_ptr (blk, ofs) =>
        if (m.(contents) blk ofs) then true else false
    end.

  Definition val_compare (m: t) (v0 v1: val): option bool :=
    match v0, v1 with
    | val_nat n0, val_nat n1 => Some (if (PeanoNat.Nat.eq_dec n0 n1) then true else false)
    | val_nat n, val_ptr (blk, ofs)
    | val_ptr (blk, ofs), val_nat n =>
        if (m.(contents) blk ofs)
        then Some (if (PeanoNat.Nat.eq_dec n 0) then true else false)
        else None
    | val_ptr (blk0, ofs0), val_ptr (blk1, ofs1) =>
        if (m.(contents) blk0 ofs0) then
          if (m.(contents) blk1 ofs1) then
            Some (if (PeanoNat.Nat.eq_dec blk0 blk1)
                  then if (PeanoNat.Nat.eq_dec ofs0 ofs1) then true else false
                  else false)
          else None
        else None
    end.

  Definition init: t := mk (fun _ _ => None) 0.

  Definition alloc (m: t) (size: nat): t * val :=
    let nb := (S m.(next_block)) in
    (mk (fun blk => if (PeanoNat.Nat.eq_dec blk nb)
                    then
                      fun ofs =>
                        if Compare_dec.le_gt_dec size ofs
                        then None
                        else Some (val_nat 0)
                    else m.(contents) blk) nb, val_ptr (nb, 0)).

  Definition mem_update (m: t) (blk: nat) (ofs: nat) (v: val): t :=
    mk (fun blk' => if (PeanoNat.Nat.eq_dec blk' blk)
                    then
                      fun ofs' => if (PeanoNat.Nat.eq_dec ofs' ofs)
                                  then Some v
                                  else m.(contents) blk' ofs'
                    else m.(contents) blk') m.(next_block).

  Definition store (m: t) (ptr: pointer) (v: val): option t :=
    let (blk, ofs) := ptr in
    if (m.(contents) blk ofs)
    then Some (mem_update m blk ofs v)
    else None.

  Definition load (m: t) (ptr: pointer): option val :=
    let (blk, ofs) := ptr in
    m.(contents) blk ofs.

  Definition compare (m: t) (v0: val) (v1: val): option bool :=
    val_compare m v0 v1.

  Definition faa (m: t) (ptr: pointer) (addend: nat): option (t * val) :=
    let (blk, ofs) := ptr in
    match (m.(contents) blk ofs) with
    | Some v => Some (mem_update m blk ofs (val_add v addend), v)
    | None => None
    end.

  Definition cas (m: t) (ptr: pointer) (v_old: val) (v_new: val):
    option (t * bool) :=
    let (blk, ofs) := ptr in
    match (m.(contents) blk ofs) with
    | Some v =>
        match (val_compare m v v_old) with
        | None => None
        | Some true =>
            Some (mem_update m blk ofs v_new, true)
        | Some false =>
            Some (m, false)
        end
    | None => None
    end.

  Definition alloc_fun:
    ktree (((@eventE void) +' cE) +' sE t) nat val :=
    fun sz =>
      m <- trigger (@Get _);;
      let (m, v) := alloc m sz in
      _ <- trigger (Put m);;
      Ret v
  .

  Definition store_fun:
    ktree (((@eventE void) +' cE) +' sE t) (val * val) unit :=
    fun '(vptr, v) =>
      p <- unwrap (unwrap_ptr vptr);;
      m <- trigger (@Get _);;
      m <- unwrap (store m p v);;
      _ <- trigger (Put m);;
      Ret tt
  .

  Definition load_fun:
    ktree (((@eventE void) +' cE) +' sE t) val val :=
    fun vptr =>
      p <- unwrap (unwrap_ptr vptr);;
      m <- trigger (@Get _);;
      v <- unwrap (load m p);;
      Ret v
  .

  Definition faa_fun:
    ktree (((@eventE void) +' cE) +' sE t) (val * nat) val :=
    fun '(vptr, addend) =>
      p <- unwrap (unwrap_ptr vptr);;
      m <- trigger (@Get _);;
      '(m, v) <- unwrap (faa m p addend);;
      _ <- trigger (Put m);;
      Ret v
  .

  Definition cas_fun:
    ktree (((@eventE void) +' cE) +' sE t) (val * val * val) bool :=
    fun '(vptr, v_old, v_new) =>
      p <- unwrap (unwrap_ptr vptr);;
      m <- trigger (@Get _);;
      '(m, b) <- unwrap (cas m p v_old v_new);;
      _ <- trigger (Put m);;
      Ret b
  .

  Definition mod: Mod.t :=
    Mod.mk
      init
      (Mod.get_funs [("alloc", Mod.wrap_fun alloc_fun);
                     ("store", Mod.wrap_fun store_fun);
                     ("load", Mod.wrap_fun load_fun);
                     ("faa", Mod.wrap_fun faa_fun);
                     ("cas", Mod.wrap_fun cas_fun)
      ]).
End SCMem.
