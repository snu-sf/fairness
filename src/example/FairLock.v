From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
Unset Universe Checking.
From Fairness Require Export ITreeLib WFLib FairBeh NatStructs Mod pind Axioms Linking SCM Red IRed Wrapper.
From PromisingSEQ Require Import TView.
From Ordinal Require Export ClassicalHessenberg.


Set Implicit Arguments.


Module FairLock.
  Definition lock_fun: WMod.function bool unit void :=
    WMod.mk_fun
      tt
      (fun (_: unit) st next =>
         match st with
         | true => next = WMod.disabled
         | false => next = WMod.normal true tt (prism_fmap inlp (fun _ => Flag.fail))
         end).

  Definition unlock_fun: WMod.function bool unit void :=
    WMod.mk_fun
      tt
      (fun (_: unit) st next =>
         match st with
         | false => next = WMod.stuck
         | true => next = WMod.normal false tt (prism_fmap inlp (fun _ => Flag.emp))
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
             next = WMod.normal None (TView.join tvw tvw_lock) (prism_fmap inlp (fun _ => Flag.fail))
         end).

  Definition unlock_fun: WMod.function (option TView.t) unit void :=
    WMod.mk_fun
      tt
      (fun (tvw: TView.t) st next =>
         match st with
         | Some _ => next = WMod.stuck
         | None => next = WMod.normal (Some tvw) tvw (prism_fmap inlp (fun _ => Flag.emp))
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
