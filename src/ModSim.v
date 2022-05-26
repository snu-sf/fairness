From sflib Require Import sflib.
From Paco Require Import paco.
From Ordinal Require Import Ordinal.
From Fairness Require Export ITreeLib FairBeh Mod.
Require Export Coq.Strings.String.

Set Implicit Arguments.

Section PRIMIVIESIM.
  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable ident_src: ID.
  Variable ident_tgt: ID.

  Let tids: ID := mk_id nat.

  Variable wf_src: WF.
  Variable wf_tgt: WF.

  Let srcE := ((@eventE ident_src +' cE) +' stateE state_src).
  Let tgtE := ((@eventE ident_tgt +' cE) +' stateE state_tgt).

  Variable world: Type.
  Variable world_le: world -> world -> Prop.

  Let shared_rel: Type :=
        @imap ident_src wf_src ->
        @imap ident_tgt wf_tgt ->
        @imap tids wf_src ->
        @imap tids wf_tgt ->
        wf_src.(T) ->
        state_src ->
        state_tgt ->
        world ->
        Prop.

  Definition shared_rel_wf (r: shared_rel): Prop :=
    forall im_src im_tgt th_src0 th_tgt0 o st_src st_tgt w0
           (INV: r im_src im_tgt th_src0 th_tgt0 o st_src st_tgt w0)
           th_tgt1 (TGT: fair_update th_tgt0 th_tgt1 (fun _ => Flag.fail)),
    exists th_src1 w1,
      (<<SRC: fair_update th_src0 th_src1 (fun _ => Flag.fail)>>) /\
        (<<INV: r im_src im_tgt th_src1 th_tgt1 o st_src st_tgt w1>>) /\
        (<<WORLD: world_le w0 w1>>).

  Variable I: shared_rel.

  Definition single_fmap (tid: nat): @fmap tids :=
    fun i => if (PeanoNat.Nat.eq_dec i tid) then Flag.success else Flag.fail.

  Inductive _sim (tid: nat)
            (sim: forall R_src R_tgt (RR: R_src -> R_tgt -> shared_rel),
                bool -> bool -> bool -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel)
            R_src R_tgt (RR: R_src -> R_tgt -> shared_rel)
    :
    bool -> bool -> bool -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel :=
  | sim_ret
      f_src f_tgt
      im_src im_tgt th_src th_tgt o st_src st_tgt w
      r_src r_tgt
      (SIM: RR r_src r_tgt im_src im_tgt th_src th_tgt o st_src st_tgt w)
    :
    _sim tid sim RR false f_src f_tgt (Ret r_src) (Ret r_tgt) im_src im_tgt th_src th_tgt o st_src st_tgt w

  | sim_tauL
      f_src f_tgt
      im_src im_tgt th_src th_tgt o st_src st_tgt w
      itr_src itr_tgt
      (SIM: sim _ _ RR false true f_tgt itr_src itr_tgt im_src im_tgt th_src th_tgt o st_src st_tgt w)
    :
    _sim tid sim RR false f_src f_tgt (Tau itr_src) itr_tgt im_src im_tgt th_src th_tgt o st_src st_tgt w
  | sim_chooseL
      f_src f_tgt
      im_src im_tgt th_src th_tgt o st_src st_tgt w
      X ktr_src itr_tgt
      (SIM: exists x, sim _ _ RR false true f_tgt (ktr_src x) itr_tgt im_src im_tgt th_src th_tgt o st_src st_tgt w)
    :
    _sim tid sim RR false f_src f_tgt (trigger (Choose X) >>= ktr_src) itr_tgt im_src im_tgt th_src th_tgt o st_src st_tgt w
  | sim_putL
      f_src f_tgt
      im_src im_tgt th_src th_tgt o st_src st_tgt w
      st ktr_src itr_tgt
      (SIM: sim _ _ RR false true f_tgt (ktr_src tt) itr_tgt im_src im_tgt th_src th_tgt o st st_tgt w)
    :
    _sim tid sim RR false f_src f_tgt (trigger (Put st) >>= ktr_src) itr_tgt im_src im_tgt th_src th_tgt o st_src st_tgt w
  | sim_getL
      f_src f_tgt
      im_src im_tgt th_src th_tgt o st_src st_tgt w
      ktr_src itr_tgt
      (SIM: sim _ _ RR false true f_tgt (ktr_src st_src) itr_tgt im_src im_tgt th_src th_tgt o st_src st_tgt w)
    :
    _sim tid sim RR false f_src f_tgt (trigger (@Get _) >>= ktr_src) itr_tgt im_src im_tgt th_src th_tgt o st_src st_tgt w
  | sim_tidL
      f_src f_tgt
      im_src im_tgt th_src th_tgt o st_src st_tgt w
      ktr_src itr_tgt
      (SIM: sim _ _ RR false true f_tgt (ktr_src tid) itr_tgt im_src im_tgt th_src th_tgt o st_src st_tgt w)
    :
    _sim tid sim RR false f_src f_tgt (trigger (GetTid) >>= ktr_src) itr_tgt im_src im_tgt th_src th_tgt o st_src st_tgt w
  | sim_UB
      f_src f_tgt
      im_src im_tgt th_src th_tgt o st_src st_tgt w
      ktr_src itr_tgt
    :
    _sim tid sim RR false f_src f_tgt (trigger (Undefined) >>= ktr_src) itr_tgt im_src im_tgt th_src th_tgt o st_src st_tgt w
  | sim_fairL
      f_src f_tgt
      im_src0 im_tgt th_src th_tgt o st_src st_tgt w
      f ktr_src itr_tgt
      (SIM: exists im_src1,
          (<<FAIR: fair_update im_src0 im_src1 f>>) /\
            (<<SIM: sim _ _ RR false true f_tgt (ktr_src tt) itr_tgt im_src1 im_tgt th_src th_tgt o st_src st_tgt w>>))
    :
    _sim tid sim RR false f_src f_tgt (trigger (Fair f) >>= ktr_src) itr_tgt im_src0 im_tgt th_src th_tgt o st_src st_tgt w

  | sim_tauR
      sync f_src f_tgt
      im_src im_tgt th_src th_tgt o st_src st_tgt w
      itr_src itr_tgt
      (SIM: sim _ _ RR sync f_src true itr_src itr_tgt im_src im_tgt th_src th_tgt o st_src st_tgt w)
    :
    _sim tid sim RR sync f_src f_tgt itr_src (Tau itr_tgt) im_src im_tgt th_src th_tgt o st_src st_tgt w
  | sim_chooseR
      sync f_src f_tgt
      im_src im_tgt th_src th_tgt o st_src st_tgt w
      X itr_src ktr_tgt
      (SIM: forall x, sim _ _ RR sync f_src true itr_src (ktr_tgt x) im_src im_tgt th_src th_tgt o st_src st_tgt w)
    :
    _sim tid sim RR sync f_src f_tgt itr_src (trigger (Choose X) >>= ktr_tgt) im_src im_tgt th_src th_tgt o st_src st_tgt w
  | sim_putR
      sync f_src f_tgt
      im_src im_tgt th_src th_tgt o st_src st_tgt w
      st itr_src ktr_tgt
      (SIM: sim _ _ RR sync f_src true itr_src (ktr_tgt tt) im_src im_tgt th_src th_tgt o st_src st w)
    :
    _sim tid sim RR sync f_src f_tgt itr_src (trigger (Put st) >>= ktr_tgt) im_src im_tgt th_src th_tgt o st_src st_tgt w
  | sim_getR
      sync f_src f_tgt
      im_src im_tgt th_src th_tgt o st_src st_tgt w
      itr_src ktr_tgt
      (SIM: sim _ _ RR sync f_src true itr_src (ktr_tgt st_tgt) im_src im_tgt th_src th_tgt o st_src st_tgt w)
    :
    _sim tid sim RR sync f_src f_tgt itr_src (trigger (@Get _) >>= ktr_tgt) im_src im_tgt th_src th_tgt o st_src st_tgt w
  | sim_tidR
      sync f_src f_tgt
      im_src im_tgt th_src th_tgt o st_src st_tgt w
      itr_src ktr_tgt
      (SIM: sim _ _ RR sync f_src true itr_src (ktr_tgt tid) im_src im_tgt th_src th_tgt o st_src st_tgt w)
    :
    _sim tid sim RR sync f_src f_tgt itr_src (trigger (GetTid) >>= ktr_tgt) im_src im_tgt th_src th_tgt o st_src st_tgt w
  | sim_fairR
      sync f_src f_tgt
      im_src im_tgt0 th_src th_tgt o st_src st_tgt w
      f itr_src ktr_tgt
      (SIM: forall im_tgt1
                   (FAIR: fair_update im_tgt0 im_tgt1 f),
          (<<SIM: sim _ _ RR sync f_src true itr_src (ktr_tgt tt) im_src im_tgt1 th_src th_tgt o st_src st_tgt w>>))
    :
    _sim tid sim RR sync f_src f_tgt itr_src (trigger (Fair f) >>= ktr_tgt) im_src im_tgt0 th_src th_tgt o st_src st_tgt w

  | sim_observe
      f_src f_tgt
      im_src im_tgt th_src th_tgt o st_src st_tgt w
      fn args ktr_src ktr_tgt
      (SIM: forall ret,
          sim _ _ RR false true true (ktr_src ret) (ktr_tgt ret) im_src im_tgt th_src th_tgt o st_src st_tgt w)
    :
    _sim tid sim RR false f_src f_tgt (trigger (Observe fn args) >>= ktr_src) (trigger (Observe fn args) >>= ktr_tgt) im_src im_tgt th_src th_tgt o st_src st_tgt w

  | sim_yield
      sync f_src f_tgt
      im_src0 im_tgt0 th_src0 th_tgt0 o st_src0 st_tgt0 w
      o0 w0 ktr_src ktr_tgt
      (INV: I im_src0 im_tgt0 th_src0 th_tgt0 o0 st_src0 st_tgt0 w0)
      (SIM: forall im_src1 im_tgt1 th_src1 th_tgt1 o1 st_src1 st_tgt1 w1
                   (INV: I im_src1 im_tgt1 th_src1 th_tgt1 o1 st_src1 st_tgt1 w1)
                   (WORLD: world_le w0 w1)
                   th_tgt2
                   (TGT: fair_update th_tgt1 th_tgt2 (single_fmap tid)),
          sim _ _ RR true true true (ktr_src tt) (ktr_tgt tt) im_src1 im_tgt1 th_src1 th_tgt2 o1 st_src1 st_tgt1 w1)
    :
    _sim tid sim RR sync f_src f_tgt (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt) im_src0 im_tgt0 th_src0 th_tgt0 o st_src0 st_tgt0 w


  | sim_yieldR
      sync f_src f_tgt
      im_src0 im_tgt0 th_src0 th_tgt0 o st_src0 st_tgt0 w
      o0 w0 itr_src ktr_tgt
      (INV: I im_src0 im_tgt0 th_src0 th_tgt0 o0 st_src0 st_tgt0 w0)
      (STUTTER: wf_src.(lt) o0 o)
      (SIM: forall im_src1 im_tgt1 th_src1 th_tgt1 o1 st_src1 st_tgt1 w1
                   (INV: I im_src1 im_tgt1 th_src1 th_tgt1 o1 st_src1 st_tgt1 w1)
                   (WORLD: world_le w0 w1)
                   th_tgt2
                   (TGT: fair_update th_tgt1 th_tgt2 (single_fmap tid)),
          sim _ _ RR true true true itr_src (ktr_tgt tt) im_src1 im_tgt1 th_src1 th_tgt2 o1 st_src1 st_tgt1 w1)
    :
    _sim tid sim RR sync f_src f_tgt itr_src (trigger (Yield) >>= ktr_tgt) im_src0 im_tgt0 th_src0 th_tgt0 o0 st_src0 st_tgt0 w
  | sim_yieldL
      f_src f_tgt
      im_src im_tgt th_src0 th_tgt o0 st_src st_tgt w
      ktr_src itr_tgt
      (SIM: exists th_src1 o1,
          (<<FAIR: fair_update th_src0 th_src1 (single_fmap tid)>>) /\
            (<<SIM: sim _ _ RR false true f_tgt (ktr_src tt) itr_tgt im_src im_tgt th_src1 th_tgt o1 st_src st_tgt w>>))
    :
    _sim tid sim RR false f_src f_tgt (trigger (Yield) >>= ktr_src) itr_tgt im_src im_tgt th_src0 th_tgt o0 st_src st_tgt w
  | sim_scheduleL
      f_src f_tgt
      im_src im_tgt th_src0 th_tgt o0 st_src st_tgt w
      itr_src itr_tgt
      (SIM: exists th_src1 o1,
          (<<FAIR: fair_update th_src0 th_src1 (single_fmap tid)>>) /\
            (<<SIM: sim _ _ RR false true f_tgt itr_src itr_tgt im_src im_tgt th_src1 th_tgt o1 st_src st_tgt w>>))
    :
    _sim tid sim RR true f_src f_tgt itr_src itr_tgt im_src im_tgt th_src0 th_tgt o0 st_src st_tgt w
  .

  (* TODO: src yield, tgt yield, both yield, progress *)
  _sim sim

End PRIMIVIESIM.
