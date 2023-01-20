From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
Unset Universe Checking.
From Fairness Require Export ITreeLib WFLib FairBeh NatStructs Mod pind Axioms OpenMod WMM Red IRed Wrapper WeakestAdequacy FairLock Concurrency.
From PromisingLib Require Import Loc Event.
From PromisingSEQ Require Import TView.
From Ordinal Require Export ClassicalHessenberg.
Require Import Coq.Numbers.BinNums.


Set Implicit Arguments.


Module ClientImpl.
  Definition loc_X: Loc.t := Loc.of_nat 2.

  Definition const_0: Const.t := Const.of_Z (BinIntDef.Z.of_nat 0).
  Definition const_42: Const.t := Const.of_Z (BinIntDef.Z.of_nat 42).

  Definition thread1:
    ktree (oprogramE void unit) unit unit
    :=
    fun _ =>
      let tvw := TView.bot in
      tvw <- (OMod.call "lock" (tvw: TView.t));;
      tvw <- (OMod.call "store" (tvw: TView.t, loc_X, const_42, Ordering.plain));;
      `tvw: TView.t <- (OMod.call "unlock" (tvw: TView.t));;
      Ret tt.

  Definition thread2:
    ktree (oprogramE void unit) unit unit
    :=
    fun _ =>
      let tvw := TView.bot in
      _ <- ITree.iter
             (fun (tvw: TView.t) =>
                tvw <- (OMod.call "lock" (tvw: TView.t));;
                '(tvw, x) <- (OMod.call "load" (tvw: TView.t, loc_X, Ordering.plain));;
                `tvw: TView.t <- (OMod.call "unlock" (tvw: TView.t));;
                      b <- unwrap (Const.eqb const_0 x);;
                      if (b: bool) then Ret (inl tvw) else Ret (inr tvw)) tvw;;
      _ <- trigger (Observe 0 [42]);;
      Ret tt.

  Definition omod: OMod.t :=
    OMod.mk
      tt
      (Mod.get_funs [("thread1", Mod.wrap_fun thread1);
                     ("thread2", Mod.wrap_fun thread2)])
  .

  Definition mod: Mod.t :=
    OMod.close
      (omod)
      (ModAdd WMem.mod FairLockW.mod)
  .
End ClientImpl.


Module ClientSpec.
  Definition thread1:
    ktree (programE void unit) unit unit
    :=
    fun _ =>
      Ret tt.

  Definition thread2:
    ktree (programE void unit) unit unit
    :=
    fun _ =>
      _ <- trigger (Observe 0 [42]);;
      Ret tt.

  Definition mod: Mod.t :=
    Mod.mk
      tt
      (Mod.get_funs [("thread1", Mod.wrap_fun thread1);
                     ("thread2", Mod.wrap_fun thread2)])
  .
End ClientSpec.


From Fairness Require Import ModSim.

Section SIM.
  Let config := [("thread1", tt↑); ("thread2", tt↑)].

  Lemma client_correct:
    UserSim.sim ClientSpec.mod ClientImpl.mod (prog2ths ClientSpec.mod config) (prog2ths ClientImpl.mod config).
  Admitted.
End SIM.
