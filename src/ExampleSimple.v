From sflib Require Import sflib.
From Paco Require Import paco.

Require Export Coq.Strings.String.
From Coq Require Import Program.

From Fairness Require Export ITreeLib WFLib FairBeh NatStructs Mod.

Set Implicit Arguments.

Section MOD.
  Definition example_fun:
    itree (((@eventE void) +' cE) +' sE (bool * bool)) Val :=
    '(l0, f0) <- trigger (@Get _);;
    if (l0: bool)
    then
      ITree.iter
        (fun (_: unit) =>
           '(l, f) <- trigger (Get _);;
           if (f: bool)
           then
             Ret (inr tt)
           else
             trigger Yield;;;
             Ret (inl tt)) tt;;;
      trigger Yield;;;
      Ret 0
    else
      trigger (Put (true, f0));;;
      trigger Yield;;;
      '(l1, _) <- trigger (@Get _);;
      trigger (Put (l1, true));;;
      Ret 0
  .

  Definition example_mod: Mod.t :=
    Mod.mk
      (false, false)
      (fun _ => Some (fun _ => example_fun))
  .

  Definition example_fun_spec:
    itree (((@eventE void) +' cE) +' sE unit) Val :=
    trigger Yield;;;
    Ret 0
  .

  Definition example_mod_spec: Mod.t :=
    Mod.mk
      tt
      (fun _ => Some (fun _ => example_fun_spec))
  .
End MOD.

From Fairness Require Import ModSim PCM.

Section SIM.
  Context `{M: URA.t}.

  Let I:
    shared unit (bool * bool) void void nat_wf nat_wf -> Prop :=
        fun '(ths, im_src, im_tgt, st_src, st_tgt, w) => True.

  Lemma sim: ModSim.mod_sim example_mod_spec example_mod.
  Proof.
    eapply (@ModSim.mk _ _ nat_wf nat_wf _ _ M). instantiate (1:=I).
    { ii. admit. }
    i. ss. ii.
  Admitted.
End SIM.
