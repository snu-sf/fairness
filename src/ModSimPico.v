From sflib Require Import sflib.
From Paco Require Import paco.
Require Export Coq.Strings.String.

(* From Ordinal Require Import Ordinal. *)
From Fairness Require Import pind8.

From Fairness Require Export ITreeLib FairBeh Mod.

Set Implicit Arguments.



Section PRIMIVIESIM.
  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable ident_src: ID.
  Variable ident_tgt: ID.

  Variable wf_src: WF.
  Variable wf_tgt: WF.

  Let srcE := ((@eventE ident_src +' cE) +' stateE state_src).
  Let tgtE := ((@eventE ident_tgt +' cE) +' stateE state_tgt).

  Variable world: Type.
  Variable world_le: world -> world -> Prop.

  (* Variable stutter: WF. *)
  Definition shared :=
    (threads *
       (@imap ident_src wf_src) *
       (@imap ident_tgt wf_tgt) *
       (@imap tids wf_src) *
       (@imap tids wf_tgt) *
       wf_src.(T) *
       state_src *
       state_tgt *
       world)%type.

  Let shared_rel: Type := shared -> Prop.

  Definition shared_rel_wf (r: shared_rel): Prop :=
    forall ths im_src im_tgt th_src0 th_tgt0 o st_src st_tgt w0
      (INV: r (ths, im_src, im_tgt, th_src0, th_tgt0, o, st_src, st_tgt, w0))
      th_tgt1 (TGT: fair_update th_tgt0 th_tgt1 (fun _ => Flag.fail)),
    exists th_src1 w1,
      (<<SRC: fair_update th_src0 th_src1 (fun _ => Flag.fail)>>) /\
        (<<INV: r (ths, im_src, im_tgt, th_src1, th_tgt1, o, st_src, st_tgt, w1)>>) /\
        (<<WORLD: world_le w0 w1>>).

  Variable I: shared_rel.

  Variant __lsim (tid: tids.(id))
            (lsim: forall R_src R_tgt (RR: R_src -> R_tgt -> shared_rel),
                bool -> bool -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel)
            (_lsim: forall R_src R_tgt (RR: R_src -> R_tgt -> shared_rel),
                bool -> bool -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel)
            R_src R_tgt (RR: R_src -> R_tgt -> shared_rel)
    :
    bool -> bool -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel :=
  | lsim_ret
      f_src f_tgt
      ths im_src im_tgt th_src th_tgt o st_src st_tgt w
      r_src r_tgt
      (LSIM: RR r_src r_tgt (ths, im_src, im_tgt, th_src, th_tgt, o, st_src, st_tgt, w))
    :
    __lsim tid lsim _lsim RR f_src f_tgt (Ret r_src) (Ret r_tgt) (ths, im_src, im_tgt, th_src, th_tgt, o, st_src, st_tgt, w)

  | lsim_tauL
      f_src f_tgt
      ths im_src im_tgt th_src th_tgt o st_src st_tgt w
      itr_src itr_tgt
      (LSIM: _lsim _ _ RR true f_tgt itr_src itr_tgt (ths, im_src, im_tgt, th_src, th_tgt, o, st_src, st_tgt, w))
    :
    __lsim tid lsim _lsim RR f_src f_tgt (Tau itr_src) itr_tgt (ths, im_src, im_tgt, th_src, th_tgt, o, st_src, st_tgt, w)
  | lsim_chooseL
      f_src f_tgt
      ths im_src im_tgt th_src th_tgt o st_src st_tgt w
      X ktr_src itr_tgt
      (LSIM: exists x, _lsim _ _ RR true f_tgt (ktr_src x) itr_tgt (ths, im_src, im_tgt, th_src, th_tgt, o, st_src, st_tgt, w))
    :
    __lsim tid lsim _lsim RR f_src f_tgt (trigger (Choose X) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, th_src, th_tgt, o, st_src, st_tgt, w)
  | lsim_putL
      f_src f_tgt
      ths im_src im_tgt th_src th_tgt o st_src st_tgt w
      st ktr_src itr_tgt
      (LSIM: _lsim _ _ RR true f_tgt (ktr_src tt) itr_tgt (ths, im_src, im_tgt, th_src, th_tgt, o, st, st_tgt, w))
    :
    __lsim tid lsim _lsim RR f_src f_tgt (trigger (Put st) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, th_src, th_tgt, o, st_src, st_tgt, w)
  | lsim_getL
      f_src f_tgt
      ths im_src im_tgt th_src th_tgt o st_src st_tgt w
      ktr_src itr_tgt
      (LSIM: _lsim _ _ RR true f_tgt (ktr_src st_src) itr_tgt (ths, im_src, im_tgt, th_src, th_tgt, o, st_src, st_tgt, w))
    :
    __lsim tid lsim _lsim RR f_src f_tgt (trigger (@Get _) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, th_src, th_tgt, o, st_src, st_tgt, w)
  | lsim_tidL
      f_src f_tgt
      ths im_src im_tgt th_src th_tgt o st_src st_tgt w
      ktr_src itr_tgt
      (LSIM: _lsim _ _ RR true f_tgt (ktr_src tid) itr_tgt (ths, im_src, im_tgt, th_src, th_tgt, o, st_src, st_tgt, w))
    :
    __lsim tid lsim _lsim RR f_src f_tgt (trigger (GetTid) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, th_src, th_tgt, o, st_src, st_tgt, w)
  | lsim_UB
      f_src f_tgt
      ths im_src im_tgt th_src th_tgt o st_src st_tgt w
      ktr_src itr_tgt
    :
    __lsim tid lsim _lsim RR f_src f_tgt (trigger (Undefined) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, th_src, th_tgt, o, st_src, st_tgt, w)
  | lsim_fairL
      f_src f_tgt
      ths im_src0 im_tgt th_src th_tgt o st_src st_tgt w
      f ktr_src itr_tgt
      (LSIM: exists im_src1,
          (<<FAIR: fair_update im_src0 im_src1 f>>) /\
            (<<LSIM: _lsim _ _ RR true f_tgt (ktr_src tt) itr_tgt (ths, im_src1, im_tgt, th_src, th_tgt, o, st_src, st_tgt, w)>>))
    :
    __lsim tid lsim _lsim RR f_src f_tgt (trigger (Fair f) >>= ktr_src) itr_tgt (ths, im_src0, im_tgt, th_src, th_tgt, o, st_src, st_tgt, w)

  | lsim_tauR
      f_src f_tgt
      ths im_src im_tgt th_src th_tgt o st_src st_tgt w
      itr_src itr_tgt
      (LSIM: _lsim _ _ RR f_src true itr_src itr_tgt (ths, im_src, im_tgt, th_src, th_tgt, o, st_src, st_tgt, w))
    :
    __lsim tid lsim _lsim RR f_src f_tgt itr_src (Tau itr_tgt) (ths, im_src, im_tgt, th_src, th_tgt, o, st_src, st_tgt, w)
  | lsim_chooseR
      f_src f_tgt
      ths im_src im_tgt th_src th_tgt o st_src st_tgt w
      X itr_src ktr_tgt
      (LSIM: forall x, _lsim _ _ RR f_src true itr_src (ktr_tgt x) (ths, im_src, im_tgt, th_src, th_tgt, o, st_src, st_tgt, w))
    :
    __lsim tid lsim _lsim RR f_src f_tgt itr_src (trigger (Choose X) >>= ktr_tgt) (ths, im_src, im_tgt, th_src, th_tgt, o, st_src, st_tgt, w)
  | lsim_putR
      f_src f_tgt
      ths im_src im_tgt th_src th_tgt o st_src st_tgt w
      st itr_src ktr_tgt
      (LSIM: _lsim _ _ RR f_src true itr_src (ktr_tgt tt) (ths, im_src, im_tgt, th_src, th_tgt, o, st_src, st, w))
    :
    __lsim tid lsim _lsim RR f_src f_tgt itr_src (trigger (Put st) >>= ktr_tgt) (ths, im_src, im_tgt, th_src, th_tgt, o, st_src, st_tgt, w)
  | lsim_getR
      f_src f_tgt
      ths im_src im_tgt th_src th_tgt o st_src st_tgt w
      itr_src ktr_tgt
      (LSIM: _lsim _ _ RR f_src true itr_src (ktr_tgt st_tgt) (ths, im_src, im_tgt, th_src, th_tgt, o, st_src, st_tgt, w))
    :
    __lsim tid lsim _lsim RR f_src f_tgt itr_src (trigger (@Get _) >>= ktr_tgt) (ths, im_src, im_tgt, th_src, th_tgt, o, st_src, st_tgt, w)
  | lsim_tidR
      f_src f_tgt
      ths im_src im_tgt th_src th_tgt o st_src st_tgt w
      itr_src ktr_tgt
      (LSIM: _lsim _ _ RR f_src true itr_src (ktr_tgt tid) (ths, im_src, im_tgt, th_src, th_tgt, o, st_src, st_tgt, w))
    :
    __lsim tid lsim _lsim RR f_src f_tgt itr_src (trigger (GetTid) >>= ktr_tgt) (ths, im_src, im_tgt, th_src, th_tgt, o, st_src, st_tgt, w)
  | lsim_fairR
      f_src f_tgt
      ths im_src im_tgt0 th_src th_tgt o st_src st_tgt w
      f itr_src ktr_tgt
      (LSIM: forall im_tgt1
                   (FAIR: fair_update im_tgt0 im_tgt1 f),
          (<<LSIM: _lsim _ _ RR f_src true itr_src (ktr_tgt tt) (ths, im_src, im_tgt1, th_src, th_tgt, o, st_src, st_tgt, w)>>))
    :
    __lsim tid lsim _lsim RR f_src f_tgt itr_src (trigger (Fair f) >>= ktr_tgt) (ths, im_src, im_tgt0, th_src, th_tgt, o, st_src, st_tgt, w)

  | lsim_observe
      f_src f_tgt
      ths im_src im_tgt th_src th_tgt o st_src st_tgt w
      fn args ktr_src ktr_tgt
      (LSIM: forall ret,
          lsim _ _ RR true true (ktr_src ret) (ktr_tgt ret) (ths, im_src, im_tgt, th_src, th_tgt, o, st_src, st_tgt, w))
    :
    __lsim tid lsim _lsim RR f_src f_tgt (trigger (Observe fn args) >>= ktr_src) (trigger (Observe fn args) >>= ktr_tgt) (ths, im_src, im_tgt, th_src, th_tgt, o, st_src, st_tgt, w)

  | lsim_sync
      f_src f_tgt
      ths0 im_src0 im_tgt0 th_src0 th_tgt0 o st_src0 st_tgt0 w
      o0 w0 ktr_src ktr_tgt
      (INV: I (ths0, im_src0, im_tgt0, th_src0, th_tgt0, o0, st_src0, st_tgt0, w0))
      (STUTTER: wf_src.(lt) o0 o)
      (LSIM: forall ths1 im_src1 im_tgt1 th_src1 th_tgt1 o1 st_src1 st_tgt1 w1
                   (INV: I (ths1, im_src1, im_tgt1, th_src1, th_tgt1, o1, st_src1, st_tgt1, w1))
                   (WORLD: world_le w0 w1)
                   th_tgt2
                   (TGT: fair_update th_tgt1 th_tgt2 (thread_fmap tid)),
          lsim _ _ RR true true (trigger (Yield) >>= ktr_src) (ktr_tgt tt) (ths1, im_src1, im_tgt1, th_src1, th_tgt2, o1, st_src1, st_tgt1, w1))
    :
    __lsim tid lsim _lsim RR f_src f_tgt (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt) (ths0, im_src0, im_tgt0, th_src0, th_tgt0, o, st_src0, st_tgt0, w)
  | lsim_yieldL
      f_src f_tgt
      ths im_src im_tgt th_src0 th_tgt o0 st_src st_tgt w
      ktr_src itr_tgt
      (LSIM: exists th_src1 o1,
          (<<FAIR: fair_update th_src0 th_src1 (thread_fmap tid)>>) /\
            (<<LSIM: _lsim _ _ RR true f_tgt (ktr_src tt) itr_tgt (ths, im_src, im_tgt, th_src1, th_tgt, o1, st_src, st_tgt, w)>>))
    :
    __lsim tid lsim _lsim RR f_src f_tgt (trigger (Yield) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, th_src0, th_tgt, o0, st_src, st_tgt, w)

  | lsim_progress
      ths im_src im_tgt th_src th_tgt o st_src st_tgt w
      itr_src itr_tgt
      (LSIM: lsim _ _ RR false false itr_src itr_tgt (ths, im_src, im_tgt, th_src, th_tgt, o, st_src, st_tgt, w))
    :
    __lsim tid lsim _lsim RR true true itr_src itr_tgt (ths, im_src, im_tgt, th_src, th_tgt, o, st_src, st_tgt, w)
  .

  Definition lsim (tid: tids.(id)): forall R_src R_tgt (RR: R_src -> R_tgt -> shared_rel),
      bool -> bool -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel :=
    paco8 (fun r => pind8 (__lsim tid r) top8) bot8.

  Lemma __lsim_mon tid: forall r r' (LE: r <8= r'), (__lsim tid r) <9= (__lsim tid r').
  Proof.
    ii. inv PR; econs; eauto.
  Qed.

  Lemma _lsim_mon tid: forall r, monotone8 (__lsim tid r).
  Proof.
    ii. inv IN; econs; eauto.
    { des. eauto. }
    { des. eauto. }
    { i. eapply LE. eapply LSIM. eauto. }
    { des. esplits; eauto. }
  Qed.

  Lemma lsim_mon tid: forall q, monotone8 (fun r => pind8 (__lsim tid r) q).
  Proof.
    ii. eapply pind8_mon_gen; eauto.
    ii. eapply __lsim_mon; eauto.
  Qed.

End PRIMIVIESIM.
#[export] Hint Constructors __lsim: core.
#[export] Hint Unfold lsim: core.
#[export] Hint Resolve _lsim_mon: paco.
#[export] Hint Resolve lsim_mon: paco.



Module ModSim.
  Section MODSIM.

    Variable md_src: Mod.t.
    Variable md_tgt: Mod.t.

    Record local_sim: Prop :=
      mk {
          wf: WF;
          world: Type;
          world_le: world -> world -> Prop;
          I: (@shared md_src.(Mod.state) md_tgt.(Mod.state) md_src.(Mod.ident) md_tgt.(Mod.ident) wf nat_wf world) -> Prop;

          init: forall im_tgt th_tgt,
          exists im_src th_src o w,
            I ([], im_src, im_tgt, th_src, th_tgt, o, md_src.(Mod.st_init), md_tgt.(Mod.st_init), w);

          funs: forall ths0 im_src0 im_tgt0 th_src0 th_tgt0 o0 st_src0 st_tgt0 w0
                  (INV: I (ths0, im_src0, im_tgt0, th_src0, th_tgt0, o0, st_src0, st_tgt0, w0))
                  fn args tid ths1
                  (THS: threads_add ths0 tid ths1),
            lsim
              world_le
              I
              tid
              (fun r_src r_tgt '(ths2, im_src1, im_tgt1, th_src1, th_tgt1, o1, st_src1, st_tgt1, w1) =>
                 exists ths3 w2,
                   (<<THS: threads_remove ths2 tid ths3>>) /\
                     (<<WORLD: world_le w1 w2>>) /\
                     (<<INV: I (ths3, im_src1, im_tgt1, th_src1, th_tgt1, o1, st_src1, st_tgt1, w2)>>) /\
                     (<<RET: r_src = r_tgt>>))
              false false
              (md_src.(Mod.funs) fn args) (md_tgt.(Mod.funs) fn args)
              (ths1, im_src0, im_tgt0, th_src0, th_tgt0, o0, st_src0, st_tgt0, w0);
        }.

  End MODSIM.
End ModSim.
