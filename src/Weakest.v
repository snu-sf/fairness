From sflib Require Import sflib.
From Paco Require Import paco.
From Fairness Require Import PCM ITreeLib IProp IPM ModSim ModSimNat.

Set Implicit Arguments.


Section SIM.
  Context `{Σ: GRA.t}.

  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable ident_src: ID.
  Variable ident_tgt: ID.

  Variable wf_src: WF.

  Let srcE := ((@eventE ident_src +' cE) +' sE state_src).
  Let tgtE := ((@eventE ident_tgt +' cE) +' sE state_tgt).

  Let shared_rel' := TIdSet.t -> (@imap ident_src wf_src) -> (@imap (sum_tid ident_tgt) nat_wf) -> state_src -> state_tgt -> @URA.car Σ -> Prop.
  Let shared_rel := TIdSet.t -> (@imap ident_src wf_src) -> (@imap (sum_tid ident_tgt) nat_wf) -> state_src -> state_tgt -> iProp.

  Let lift (R: shared_rel): (TIdSet.t *
                               (@imap ident_src wf_src) *
                               (@imap (sum_tid ident_tgt) nat_wf) *
                               state_src *
                               state_tgt *
                               @URA.car Σ)%type -> Prop :=
        fun '(ths, im_src, im_tgt, st_src, st_tgt, r_shared) =>
          R ths im_src im_tgt st_src st_tgt r_shared.

  Variable I: shared_rel.

  (* TODO: remove r_shared in ModSim *)
  Definition isim (tid: thread_id) (R_src R_tgt: Type)
             (RR: R_src -> R_tgt -> shared_rel):
    itree srcE R_src -> itree tgtE R_tgt -> shared_rel' :=
    fun itr_src itr_tgt ths im_src im_tgt st_src st_tgt r =>
      forall r_ctx (WF: URA.wf (r ⋅ r_ctx)),
        lsim (lift I) tid (fun r_src r_tgt => lift (RR r_src r_tgt)) false false r_ctx itr_src itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, ε).


  Variant __lsim
          (tid: thread_id)
          (lsim: forall R_src R_tgt (RR: R_src -> R_tgt -> URA.car -> shared_rel), bool -> bool -> URA.car -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel)
          (_lsim: forall R_src R_tgt (RR: R_src -> R_tgt -> URA.car -> shared_rel),bool -> bool -> URA.car -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel)
          R_src R_tgt (RR: R_src -> R_tgt -> URA.car -> shared_rel)
    :
    bool -> bool -> URA.car -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel :=



lsim =
λ (M : URA.t) (state_src state_tgt : Type) (ident_src _ident_tgt : ID)
  (wf_src wf_tgt : WF) (srcE := (eventE +' cE) +' sE state_src)
  (tgtE := (eventE +' cE) +' sE state_tgt) (shared_rel :=
                                            shared state_src state_tgt ident_src
                                              _ident_tgt wf_src wf_tgt → Prop)
  (I : shared_rel) (tid : thread_id) (R_src R_tgt : Type)
  (RR : R_src → R_tgt → M → shared_rel),


lsim



URA.car -> shared_rel):
    bool -> bool -> URA.car -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel :=
    paco9 (fun r => pind9 (__lsim tid r) top9) bot9 R_src R_tgt RR.



  Variable I: shared_rel.


Variant


Definition lsim (tid: thread_id)
           R_src R_tgt (RR: R_src -> R_tgt -> URA.car -> shared_rel):
  bool -> bool -> URA.car -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel :=
  paco9 (fun r => pind9 (__lsim tid r) top9) bot9 R_src R_tgt RR.
