From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Export ITreeLib WFLib FairBeh NatStructs Mod pind.

Set Implicit Arguments.


Module FairLock.
  Definition all_fail (s: TIdSet.t): fmap thread_id :=
    fun id => if (NatMap.mem id s) then Flag.fail else Flag.emp.

  Definition all_success (s: TIdSet.t): fmap thread_id :=
    fun id => if (NatMap.mem id s) then Flag.success else Flag.emp.

  Definition lock_fun:
    ktree (((@eventE thread_id) +' cE) +' sE (TIdSet.t * option thread_id)) unit unit :=
    fun _ =>
      _ <- trigger Yield;;
      tid <- trigger GetTid;;
      '(W, own) <- trigger (@Get _);;
      let W := TIdSet.add tid W in
      _ <- trigger (Put (W, own));;

      _ <- ITree.iter
             (fun (_: unit) =>
                '(W, own) <- trigger (@Get _);;
                match own with
                | Some _ => _ <- trigger Yield;; Ret (inl tt)
                | None => Ret (inr tt)
                end
             ) tt;;

      let W := TIdSet.remove tid W in
      _ <- trigger (Fair (all_fail W));;
      _ <- trigger (Put (W, Some tid));;
      trigger Yield
  .

  Definition unlock_fun:
    ktree (((@eventE thread_id) +' cE) +' sE (TIdSet.t * option thread_id)) unit unit :=
    fun _ =>
      _ <- trigger Yield;;
      tid <- trigger GetTid;;
      '(W, own) <- trigger (@Get _);;
      own <- unwrap own;;
      if (PeanoNat.Nat.eq_dec own tid)
      then
        _ <- trigger (Put (W, None));;
        trigger Yield
      else UB
  .

  Definition example_mod_spec: Mod.t :=
    Mod.mk
      (TIdSet.empty, None)
      (Mod.get_funs [("lock", Mod.wrap_fun lock_fun);
                     ("unlock", Mod.wrap_fun unlock_fun)
      ]).
End FairLock.

From Fairness Require Import OpenMod SCM.

Module TicketLock.
  Definition now_serving: SCMem.val := SCMem.val_ptr (0, 0).
  Definition next_ticket: SCMem.val := SCMem.val_ptr (0, 1).

  Definition lock_fun:
    ktree ((((@eventE void) +' cE) +' (sE unit)) +' OpenMod.callE) unit unit :=
    fun _ =>
      _ <- trigger Yield;;
      myticket <- trigger (OpenMod.Call "faa" (next_ticket, 1)↑);;
      myticket <- unwrap (myticket↓);;
      _ <- trigger Yield;;

      _ <- ITree.iter
             (fun (_: unit) =>
                _ <- trigger Yield;;
                next <- trigger (OpenMod.Call "load" (now_serving)↑);; next <- unwrap (next↓);;
                _ <- trigger Yield;;
                b <- trigger (OpenMod.Call "compare" (next: SCMem.val, myticket: SCMem.val)↑);; b <- unwrap (b↓);;
                _ <- trigger Yield;;
                if (b: bool) then Ret (inr tt) else Ret (inl tt)) tt;;
      trigger Yield
  .

  Definition unlock_fun:
    ktree ((((@eventE void) +' cE) +' (sE unit)) +' OpenMod.callE) unit unit :=
    fun _ =>
      _ <- trigger Yield;;
      _ <- trigger (OpenMod.Call "faa" (now_serving, 1)↑);;
      trigger Yield
  .
End TicketLock.
