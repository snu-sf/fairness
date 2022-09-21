From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Export ITreeLib WFLib FairBeh NatStructs Mod pind.

Set Implicit Arguments.

Module SCMem.
  Record t :=
    mk
      {
        contents:> nat -> option Val;
        next_block: nat;
      }.

  Definition init: t := mk (fun _ => None) 0.

  Definition alloc (m: t): t * nat :=
    let nb := (S m.(next_block)) in
    (mk (fun k => if (PeanoNat.Nat.eq_dec k nb)
                  then Some 0
                  else m.(contents) k) nb, nb).

  Definition store (m: t) (k: nat) (v: Val): option t :=
    if (m.(contents) k)
    then Some (mk (fun k' => if (PeanoNat.Nat.eq_dec k' k)
                             then Some v
                             else m.(contents) k') m.(next_block))
    else None.

  Definition load (m: t) (k: nat): option Val :=
    m.(contents) k.

  Definition alloc_fun:
    ktree (((@eventE void) +' cE) +' sE t) unit nat :=
    fun _ =>
      m <- trigger (@Get _);;
      let (m, nb) := alloc m in
      _ <- trigger (Put m);;
      Ret nb
  .

  Definition store_fun:
    ktree (((@eventE void) +' cE) +' sE t) (nat * Val) unit :=
    fun '(k, v) =>
      m <- trigger (@Get _);;
      m <- unwrap (store m k v);;
      _ <- trigger (Put m);;
      Ret tt
  .

  Definition load_fun:
    ktree (((@eventE void) +' cE) +' sE t) nat Val :=
    fun k =>
      m <- trigger (@Get _);;
      v <- unwrap (load m k);;
      Ret v
  .

  Definition mod: Mod.t :=
    Mod.mk
      init
      (Mod.get_funs [("alloc", Mod.wrap_fun alloc_fun);
                     ("store", Mod.wrap_fun store_fun);
                     ("load", Mod.wrap_fun load_fun)]).
End SCMem.
