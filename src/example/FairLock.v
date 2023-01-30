From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
Unset Universe Checking.
From Fairness Require Export
     ITreeLib WFLib FairBeh NatStructs Mod pind Axioms
     OpenMod SCM Red IRed Wrapper.
From PromisingSEQ Require Import TView.
From Ordinal Require Export ClassicalHessenberg.


Set Implicit Arguments.

Module AbsLock.

  Definition lock_fun
    : ktree (((@eventE thread_id) +' cE) +' (sE (bool * NatMap.t unit)%type)) unit unit :=
    fun _ =>
      _ <- trigger Yield;;
      tid <- trigger (GetTid);;
      '(own, ts) <- trigger (@Get _);;
      let ts := NatMap.add tid tt ts in
      _ <- trigger (Put (own, ts));;
      _ <- (ITree.iter
             (fun (_: unit) =>
                _ <- trigger Yield;;
                '(own, ts) <- trigger (@Get _);;
                if (Bool.eqb own true)
                then Ret (inl tt)
                else Ret (inr tt)) tt);;
      '(_, ts) <- trigger (@Get _);;
      let ts := NatMap.remove tid ts in
      _ <- trigger (Put (true, ts));;
      _ <- trigger (Fair (fun i => if tid_dec i tid then Flag.success
                               else if (NatMapP.F.In_dec ts i) then Flag.fail
                                    else Flag.emp));;
      _ <- trigger Yield;;
      Ret tt.

  Definition unlock_fun
    : ktree (((@eventE thread_id) +' cE) +' (sE (bool * NatMap.t unit)%type)) unit unit :=
    fun _ =>
      _ <- trigger Yield;;
      '(own, ts) <- trigger (@Get _);;
      if (Bool.eqb own true)
      then _ <- trigger (Put (false, ts));; _ <- trigger Yield;; Ret tt
      else UB.

  Definition mod: Mod.t :=
    Mod.mk
      (false, NatMap.empty unit)
      (Mod.get_funs [("lock", Mod.wrap_fun lock_fun);
                     ("unlock", Mod.wrap_fun unlock_fun)]).

End AbsLock.

Module AbsLockW.

  Definition lock_fun
    : ktree (((@eventE thread_id) +' cE) +' (sE ((option TView.t) * NatMap.t unit)%type))
            TView.t TView.t :=
    fun tvw =>
      _ <- trigger Yield;;
      tid <- trigger (GetTid);;
      '(own, ts) <- trigger (@Get _);;
      let ts := NatMap.add tid tt ts in
      _ <- trigger (Put (own, ts));;
      `tvw_lock: TView.t <- (ITree.iter
                              (fun (_: unit) =>
                                 _ <- trigger Yield;;
                                 '(own, ts) <- trigger (@Get _);;
                                 match own with
                                 | None => Ret (inl tt)
                                 | Some tvw_lock => Ret (inr tvw_lock)
                                 end)
                              tt);;
      '(_, ts) <- trigger (@Get _);;
      let ts := NatMap.remove tid ts in
      _ <- trigger (Put (None, ts));;
      _ <- trigger (Fair (fun i => if tid_dec i tid then Flag.success
                               else if (NatMapP.F.In_dec ts i) then Flag.fail
                                    else Flag.emp));;
      _ <- trigger Yield;;
      Ret (TView.join tvw tvw_lock).

  Definition unlock_fun
    : ktree (((@eventE thread_id) +' cE) +' (sE ((option TView.t) * NatMap.t unit)%type))
            TView.t TView.t :=
    fun tvw =>
      _ <- trigger Yield;;
      '(own, ts) <- trigger (@Get _);;
      match own with
      | None => _ <- trigger (Put (Some tvw, ts));; _ <- trigger Yield;; Ret tvw
      | Some _ => UB
      end.

  Definition mod: Mod.t :=
    Mod.mk
      (Some TView.bot, NatMap.empty unit)
      (Mod.get_funs [("lock", Mod.wrap_fun lock_fun);
                     ("unlock", Mod.wrap_fun unlock_fun)]).

End AbsLockW.


Module FairLock.
  Definition lock_fun: WMod.function bool unit void :=
    WMod.mk_fun
      tt
      (fun (_: unit) st next =>
         match st with
         | true => next = WMod.disabled
         | false => next = WMod.normal true tt (sum_fmap_l (fun _ => Flag.fail))
         end).

  Definition unlock_fun: WMod.function bool unit void :=
    WMod.mk_fun
      tt
      (fun (_: unit) st next =>
         match st with
         | false => next = WMod.stuck
         | true => next = WMod.normal false tt (sum_fmap_l (fun _ => Flag.emp))
         end).

  Definition wmod: WMod.t :=
    WMod.mk
      false
      [("lock", lock_fun);
       ("unlock", unlock_fun)
      ].

  Definition mod: Mod.t :=
    WMod.interp_mod wmod.
End FairLock.

From Fairness Require Export WMM.

Module FairLockW.
  Definition lock_fun: WMod.function (option TView.t) unit void :=
    WMod.mk_fun
      tt
      (fun (tvw: TView.t) st next =>
         match st with
         | None => next = WMod.disabled
         | Some tvw_lock =>
             next = WMod.normal None (TView.join tvw tvw_lock) (sum_fmap_l (fun _ => Flag.fail))
         end).

  Definition unlock_fun: WMod.function (option TView.t) unit void :=
    WMod.mk_fun
      tt
      (fun (tvw: TView.t) st next =>
         match st with
         | Some _ => next = WMod.stuck
         | None => next = WMod.normal (Some tvw) tvw (sum_fmap_l (fun _ => Flag.emp))
         end).

  Definition wmod: WMod.t :=
    WMod.mk
      (Some TView.bot)
      [("lock", lock_fun);
       ("unlock", unlock_fun)
      ].

  Definition mod: Mod.t :=
    WMod.interp_mod wmod.
End FairLockW.
