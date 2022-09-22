From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Export ITreeLib WFLib FairBeh NatStructs Mod pind.
From PromisingSEQ Require Import Time View Memory Local.

Set Implicit Arguments.

Module WMem.
  Record t :=
    mk
      {
        memory:> Memory.t;
        sc: TimeMap.t;
      }.

  Definition init: t := mk Memory.init TimeMap.bot.
End WMem.
