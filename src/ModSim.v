From sflib Require Import sflib.
From Paco Require Import paco.
From Ordinal Require Import Ordinal.
From Fairness Require Export ITreeLib FairBeh Mod.
Require Export Coq.Strings.String.

Set Implicit Arguments.

Section PRIMIVIESIM.
  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable ident_src: Type.
  Variable ident_tgt: Type.

  Variable interpretation:
    list nat -> state_src -> state_tgt ->

  option


  Variant cE: Type -> Type :=
  | Yield: cE unit
  | Spawn (fn: fname) (args: list Val): cE unit
  | GetTid: cE nat
  .

  Variant stateE (State: Type): Type -> Type :=
    | Put (st: State): stateE State unit
    | Get: stateE State State
  .


  Inductive _sim
            (sim: forall R0 R1 (RR: R0 -> R1 -> Prop), bool -> imap -> bool  -> imap -> (@state _ R0) -> (@state _ R1) -> Prop)
            {R0 R1} (RR: R0 -> R1 -> Prop) (p_src: bool) (m_src: imap) (p_tgt: bool) (m_tgt: imap) :
    (@state _ R0) -> (@state _ R1) -> Prop :=
  | sim_ret
      r_src r_tgt
      (SIM: RR r_src r_tgt)
    :
    _sim sim RR p_src m_src p_tgt m_tgt (Ret r_src) (Ret r_tgt)
  | sim_obs
      ktr_src0 ktr_tgt0 fn args
      (SIM: forall r_src r_tgt (EQ: r_src = r_tgt),
          sim _ _ RR true m_src true m_tgt (ktr_src0 r_src) (ktr_tgt0 r_tgt))
    :
    _sim sim RR p_src m_src p_tgt m_tgt (Vis (Observe fn args) ktr_src0) (Vis (Observe fn args) ktr_tgt0)

  | sim_tauL
      itr_src0 itr_tgt0
      (SIM: @_sim sim _ _ RR true m_src p_tgt m_tgt itr_src0 itr_tgt0)
    :
    _sim sim RR p_src m_src p_tgt m_tgt (Tau itr_src0) itr_tgt0
  | sim_tauR
      itr_src0 itr_tgt0
      (SIM: @_sim sim _ _ RR p_src m_src true m_tgt itr_src0 itr_tgt0)
    :
    _sim sim RR p_src m_src p_tgt m_tgt itr_src0 (Tau itr_tgt0)
  | sim_chooseL
      X ktr_src0 itr_tgt0
      (SIM: exists x, _sim sim RR true m_src p_tgt m_tgt (ktr_src0 x) itr_tgt0)
    :
    _sim sim RR p_src m_src p_tgt m_tgt (trigger (Choose X) >>= ktr_src0) itr_tgt0
  | sim_chooseR
      X itr_src0 ktr_tgt0
      (SIM: forall x, _sim sim RR p_src m_src true m_tgt itr_src0 (ktr_tgt0 x))
    :
    _sim sim RR p_src m_src p_tgt m_tgt itr_src0 (trigger (Choose X) >>= ktr_tgt0)

  | sim_fairL
      f_src ktr_src0 itr_tgt0
      (SIM: exists m_src0, (<<FAIR: fair_update m_src m_src0 f_src>>) /\
                        (<<SIM: _sim sim RR true m_src0 p_tgt m_tgt (ktr_src0 tt) itr_tgt0>>))
    :
    _sim sim RR p_src m_src p_tgt m_tgt (trigger (Fair f_src) >>= ktr_src0) itr_tgt0
  | sim_fairR
      f_tgt itr_src0 ktr_tgt0
      (SIM: forall m_tgt0 (FAIR: fair_update m_tgt m_tgt0 f_tgt),
          _sim sim RR p_src m_src true m_tgt0 itr_src0 (ktr_tgt0 tt))
    :
    _sim sim RR p_src m_src p_tgt m_tgt itr_src0 (trigger (Fair f_tgt) >>= ktr_tgt0)

  | sim_ub
      ktr_src0 itr_tgt0
    :
    _sim sim RR p_src m_src p_tgt m_tgt (trigger Undefined >>= ktr_src0) itr_tgt0
  .
