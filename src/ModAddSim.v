From sflib Require Import sflib.
From Paco Require Import paco.
From Fairness Require Import
  Mod
  ModSimPico.

Section ADD_MODSIM.

  Lemma ModAdd_comm M1 M2 : ModSim.mod_sim (ModAdd M1 M2) (ModAdd M2 M1).
  Proof.
    econs.
  Admitted.

  Lemma ModAdd_right_cong M1 M2_src M2_tgt :
    ModSim.mod_sim M2_src M2_tgt ->
    ModSim.mod_sim (ModAdd M1 M2_src) (ModAdd M1 M2_tgt).
  Admitted.

End ADD_MODSIM.
