From sflib Require Import sflib.
From Paco Require Import paco.
Require Export Coq.Strings.String.

From Fairness Require Export ITreeLib FairBeh Mod.
From Fairness Require Import pind8.

Set Implicit Arguments.

From Fairness Require Import ModSim ModSimStutter.

Section PRIMIVIESIM.
  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable _ident_src: ID.
  Definition ident_src := sum_tid _ident_src.
  Variable _ident_tgt: ID.
  Definition ident_tgt := sum_tid _ident_tgt.

  Variable wf_src: WF.
  Variable wf_tgt: WF.

  Let srcE := ((@eventE _ident_src +' cE) +' sE state_src).
  Let tgtE := ((@eventE _ident_tgt +' cE) +' sE state_tgt).

  Variable world: Type.
  Variable world_le: world -> world -> Prop.

  Definition shared :=
    (TIdSet.t *
       (@imap ident_src wf_src) *
       (@imap ident_tgt wf_tgt) *
       state_src *
       state_tgt *
       world)%type.

  Let shared_rel: Type := shared -> Prop.

  Variable I: shared_rel.

  Variable get_ord:
    forall {R_src R_tgt} (RR: R_src -> R_tgt -> shared_rel), @id thread_id -> bool -> bool -> itree srcE R_src -> itree tgtE R_tgt -> shared -> wf_src.(T).

  (* TODO: Do not work *)
  Hint Resolve ModSimStutter.lsim_mon: paco.
  Hint Resolve cpn8_wcompat: paco.

  Lemma yield_flag_to_stutter R_src R_tgt (RR: R_src -> R_tgt -> shared_rel)
        tid
    :
    forall
      f_src f_tgt src tgt ths im_src im_tgt st_src st_tgt w
      (SIM: ModSim.lsim world_le I tid RR f_src f_tgt src tgt (ths, im_src, im_tgt, st_src, st_tgt, w)),
      ModSimStutter.lsim world_le I tid RR f_src f_tgt (get_ord RR tid f_src f_tgt src tgt (ths, im_src, im_tgt, st_src, st_tgt, w), src) tgt (ths, im_src, im_tgt, st_src, st_tgt, w).
  Proof.
    ginit.
    { i. eapply ModSimStutter.lsim_mon. }
    { i. eapply cpn8_wcompat. eapply ModSimStutter.lsim_mon. }
    i.



eauto with paco. }

 "". eapply _lsim_mon.

gcofix CIH. i. ss.
    intros tid . pcofix CIH.f_src f_tgt src tgt ths im_src im_tgt st_src st_tgt w SIM.
    . pcofix CIH.

    pcofix CIH.
    i. pcofix CIH.
    pcofix CIH.



                 (lsim
                    tid
                    (@local_RR R0 R1 RR tid)
                    fs ft
                    src tgt
                    (ths0, im_src1, im_tgt1, st_src0, st_tgt0, w0)).

    :
    forall R_

  Variant __lsim
          (tid: thread_id.(id))
          (lsim: forall R_src R_tgt (RR: R_src -> R_tgt -> shared_rel), bool -> bool -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel)
          (_lsim: forall R_src R_tgt (RR: R_src -> R_tgt -> shared_rel),bool -> bool -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel)
          R_src R_tgt (RR: R_src -> R_tgt -> shared_rel)
    :
    bool -> bool -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel :=



  Definition

  Let shared_rel: Type := shared -> Prop.
