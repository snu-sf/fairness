From sflib Require Import sflib.
From Paco Require Import paco.
Require Export Coq.Strings.String.

From Fairness Require Export ITreeLib FairBeh Mod.
From Fairness Require Import pind5.
(* From Fairness Require Import pind8. *)

Set Implicit Arguments.



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

  (* Variable stutter: WF. *)
  Definition shared :=
    (tid_list *
       tid_list *
       (@imap ident_src wf_src) *
       (@imap ident_tgt wf_tgt) *
       (* (@imap thread_id wf_src) * *)
       (* (@imap thread_id wf_tgt) * *)
       state_src *
       state_tgt *
       wf_src.(T) *
       world)%type.

  Let shared_rel: Type := shared -> Prop.

  Definition shared_rel_wf (r: shared_rel): Prop :=
    forall ths tht im_src0 im_tgt0 st_src st_tgt o w0
      (INV: r (ths, tht, im_src0, im_tgt0, st_src, st_tgt, o, w0))
      im_tgt1 (TGT: fair_update im_tgt0 im_tgt1 (sum_fmap_l (fun _ => Flag.fail))),
    exists im_src1 w1,
      (<<SRC: fair_update im_src0 im_src1 (sum_fmap_l (fun _ => Flag.fail))>>) /\
        (<<INV: r (ths, tht, im_src1, im_tgt1, st_src, st_tgt, o, w1)>>) /\
        (<<WORLD: world_le w0 w1>>).

  Variable I: shared_rel.

  Variant __lsim R_src R_tgt (RR: R_src -> R_tgt -> shared_rel) (tid: thread_id.(id))
            (lsim: bool -> bool -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel)
            (_lsim: bool -> bool -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel)
    :
    bool -> bool -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel :=
  | lsim_ret
      f_src f_tgt
      ths tht im_src im_tgt st_src st_tgt o w
      r_src r_tgt
      (LSIM: RR r_src r_tgt (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w))
    :
    __lsim RR tid lsim _lsim f_src f_tgt (Ret r_src) (Ret r_tgt) (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)

  | lsim_tauL
      f_src f_tgt
      ths tht im_src im_tgt st_src st_tgt o w
      itr_src itr_tgt
      (LSIM: _lsim true f_tgt itr_src itr_tgt (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w))
    :
    __lsim RR tid lsim _lsim f_src f_tgt (Tau itr_src) itr_tgt (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)
  | lsim_chooseL
      f_src f_tgt
      ths tht im_src im_tgt st_src st_tgt o w
      X ktr_src itr_tgt
      (LSIM: exists x, _lsim true f_tgt (ktr_src x) itr_tgt (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w))
    :
    __lsim RR tid lsim _lsim f_src f_tgt (trigger (Choose X) >>= ktr_src) itr_tgt (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)
  | lsim_putL
      f_src f_tgt
      ths tht im_src im_tgt st_src st_tgt o w
      st ktr_src itr_tgt
      (LSIM: _lsim true f_tgt (ktr_src tt) itr_tgt (ths, tht, im_src, im_tgt, st, st_tgt, o, w))
    :
    __lsim RR tid lsim _lsim f_src f_tgt (trigger (Put st) >>= ktr_src) itr_tgt (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)
  | lsim_getL
      f_src f_tgt
      ths tht im_src im_tgt st_src st_tgt o w
      ktr_src itr_tgt
      (LSIM: _lsim true f_tgt (ktr_src st_src) itr_tgt (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w))
    :
    __lsim RR tid lsim _lsim f_src f_tgt (trigger (@Get _) >>= ktr_src) itr_tgt (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)
  | lsim_tidL
      f_src f_tgt
      ths tht im_src im_tgt st_src st_tgt o w
      ktr_src itr_tgt
      (LSIM: _lsim true f_tgt (ktr_src tid) itr_tgt (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w))
    :
    __lsim RR tid lsim _lsim f_src f_tgt (trigger (GetTid) >>= ktr_src) itr_tgt (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)
  | lsim_UB
      f_src f_tgt
      ths tht im_src im_tgt st_src st_tgt o w
      ktr_src itr_tgt
    :
    __lsim RR tid lsim _lsim f_src f_tgt (trigger (Undefined) >>= ktr_src) itr_tgt (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)
  | lsim_fairL
      f_src f_tgt
      ths tht im_src0 im_tgt st_src st_tgt o w
      f ktr_src itr_tgt
      (LSIM: exists im_src1,
          (<<FAIR: fair_update im_src0 im_src1 (sum_fmap_r f)>>) /\
            (<<LSIM: _lsim true f_tgt (ktr_src tt) itr_tgt (ths, tht, im_src1, im_tgt, st_src, st_tgt, o, w)>>))
    :
    __lsim RR tid lsim _lsim f_src f_tgt (trigger (Fair f) >>= ktr_src) itr_tgt (ths, tht, im_src0, im_tgt, st_src, st_tgt, o, w)

  | lsim_tauR
      f_src f_tgt
      ths tht im_src im_tgt st_src st_tgt o w
      itr_src itr_tgt
      (LSIM: _lsim f_src true itr_src itr_tgt (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w))
    :
    __lsim RR tid lsim _lsim f_src f_tgt itr_src (Tau itr_tgt) (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)
  | lsim_chooseR
      f_src f_tgt
      ths tht im_src im_tgt st_src st_tgt o w
      X itr_src ktr_tgt
      (LSIM: forall x, _lsim f_src true itr_src (ktr_tgt x) (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w))
    :
    __lsim RR tid lsim _lsim f_src f_tgt itr_src (trigger (Choose X) >>= ktr_tgt) (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)
  | lsim_putR
      f_src f_tgt
      ths tht im_src im_tgt st_src st_tgt o w
      st itr_src ktr_tgt
      (LSIM: _lsim f_src true itr_src (ktr_tgt tt) (ths, tht, im_src, im_tgt, st_src, st, o, w))
    :
    __lsim RR tid lsim _lsim f_src f_tgt itr_src (trigger (Put st) >>= ktr_tgt) (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)
  | lsim_getR
      f_src f_tgt
      ths tht im_src im_tgt st_src st_tgt o w
      itr_src ktr_tgt
      (LSIM: _lsim f_src true itr_src (ktr_tgt st_tgt) (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w))
    :
    __lsim RR tid lsim _lsim f_src f_tgt itr_src (trigger (@Get _) >>= ktr_tgt) (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)
  | lsim_tidR
      f_src f_tgt
      ths tht im_src im_tgt st_src st_tgt o w
      itr_src ktr_tgt
      (LSIM: _lsim f_src true itr_src (ktr_tgt tid) (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w))
    :
    __lsim RR tid lsim _lsim f_src f_tgt itr_src (trigger (GetTid) >>= ktr_tgt) (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)
  | lsim_fairR
      f_src f_tgt
      ths tht im_src im_tgt0 st_src st_tgt o w
      f itr_src ktr_tgt
      (LSIM: forall im_tgt1
                   (FAIR: fair_update im_tgt0 im_tgt1 (sum_fmap_r f)),
          (<<LSIM: _lsim f_src true itr_src (ktr_tgt tt) (ths, tht, im_src, im_tgt1, st_src, st_tgt, o, w)>>))
    :
    __lsim RR tid lsim _lsim f_src f_tgt itr_src (trigger (Fair f) >>= ktr_tgt) (ths, tht, im_src, im_tgt0, st_src, st_tgt, o, w)

  | lsim_observe
      f_src f_tgt
      ths tht im_src im_tgt st_src st_tgt o w
      fn args ktr_src ktr_tgt
      (LSIM: forall ret,
          lsim true true (ktr_src ret) (ktr_tgt ret) (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w))
    :
    __lsim RR tid lsim _lsim f_src f_tgt (trigger (Observe fn args) >>= ktr_src) (trigger (Observe fn args) >>= ktr_tgt) (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)

  | lsim_sync
      f_src f_tgt
      ths0 tht0 im_src0 im_tgt0 st_src0 st_tgt0 o w
      o0 w0 ktr_src ktr_tgt
      (INV: I (ths0, tht0, im_src0, im_tgt0, st_src0, st_tgt0, o0, w0))
      (WORLD: world_le w w0)
      (STUTTER: wf_src.(lt) o0 o)
      (LSIM: forall ths1 tht1 im_src1 im_tgt1 st_src1 st_tgt1 o1 w1
                   (INV: I (ths1, tht1, im_src1, im_tgt1, st_src1, st_tgt1, o1, w1))
                   (WORLD: world_le w0 w1)
                   im_tgt2
                   (TGT: fair_update im_tgt1 im_tgt2 (sum_fmap_l (tids_fmap tid tht1))),
          lsim true true (trigger (Yield) >>= ktr_src) (ktr_tgt tt) (ths1, tht1, im_src1, im_tgt2, st_src1, st_tgt1, o1, w1))
    :
    __lsim RR tid lsim _lsim f_src f_tgt (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt) (ths0, tht0, im_src0, im_tgt0, st_src0, st_tgt0, o, w)
  | lsim_yieldL
      f_src f_tgt
      ths tht im_src0 im_tgt st_src st_tgt o0 w
      ktr_src itr_tgt
      (LSIM: exists im_src1 o1,
          (<<FAIR: fair_update im_src0 im_src1 (sum_fmap_l (tids_fmap tid ths))>>) /\
            (<<LSIM: _lsim true f_tgt (ktr_src tt) itr_tgt (ths, tht, im_src1, im_tgt, st_src, st_tgt, o1, w)>>))
    :
    __lsim RR tid lsim _lsim f_src f_tgt (trigger (Yield) >>= ktr_src) itr_tgt (ths, tht, im_src0, im_tgt, st_src, st_tgt, o0, w)

  | lsim_progress
      ths tht im_src im_tgt st_src st_tgt o w
      itr_src itr_tgt
      (LSIM: lsim false false itr_src itr_tgt (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w))
    :
    __lsim RR tid lsim _lsim true true itr_src itr_tgt (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)
  .

  Definition lsim R_src R_tgt (RR: R_src -> R_tgt -> shared_rel) (tid: thread_id.(id)):
    bool -> bool -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel :=
    paco5 (fun r => pind5 (__lsim RR tid r) top5) bot5.

  Lemma __lsim_mon R0 R1 (RR: R0 -> R1 -> shared_rel) tid:
    forall r r' (LE: r <5= r'), (__lsim RR tid r) <6= (__lsim RR tid r').
  Proof.
    ii. inv PR; econs; eauto.
  Qed.

  Lemma _lsim_mon R0 R1 (RR: R0 -> R1 -> shared_rel) tid: forall r, monotone5 (__lsim RR tid r).
  Proof.
    ii. inv IN; econs; eauto.
    { des. eauto. }
    { des. eauto. }
    { i. eapply LE. eapply LSIM. eauto. }
    { des. esplits; eauto. }
  Qed.

  Lemma lsim_mon R0 R1 (RR: R0 -> R1 -> shared_rel) tid: forall q, monotone5 (fun r => pind5 (__lsim RR tid r) q).
  Proof.
    ii. eapply pind5_mon_gen; eauto.
    ii. eapply __lsim_mon; eauto.
  Qed.


  Lemma lsim_reset_prog
        R0 R1 (RR: R0 -> R1 -> shared_rel) tid
        src tgt shr
        ps0 pt0 ps1 pt1
        (LSIM: lsim RR tid ps1 pt1 src tgt shr)
        (SRC: ps1 = true -> ps0 = true)
        (TGT: pt1 = true -> pt0 = true)
    :
    lsim RR tid ps0 pt0 src tgt shr.
  Proof.
    revert_until tid. pcofix CIH. i.
    move LSIM before CIH. revert_until LSIM. punfold LSIM.
    2:{ eapply lsim_mon. }
    eapply pind5_acc in LSIM.

    { instantiate (1:= (fun ps1 pt1 src tgt shr =>
                          forall ps0 pt0 : bool,
                            (ps1 = true -> ps0 = true) ->
                            (pt1 = true -> pt0 = true) ->
                            paco5
                              (fun
                                  r0 : rel5 bool (fun _ : bool => bool) (fun _ _ : bool => itree srcE R0)
                                            (fun (_ _ : bool) (_ : itree srcE R0) => itree tgtE R1)
                                            (fun (_ _ : bool) (_ : itree srcE R0) (_ : itree tgtE R1) => shared) =>
                                  pind5 (__lsim RR tid r0) top5) r ps0 pt0 src tgt shr)) in LSIM; auto. }

    ss. clear ps1 pt1 src tgt shr LSIM.
    intros rr DEC IH ps1 pt1 src tgt shr LSIM. clear DEC.
    intros ps0 pt0 SRC TGT.
    eapply pind5_unfold in LSIM.
    2:{ eapply _lsim_mon. }
    inv LSIM.

    { pfold. eapply pind5_fold. econs; eauto. }

    { destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      pfold. eapply pind5_fold. eapply lsim_tauL. split; ss.
      hexploit IH. eauto. all: eauto. i. punfold H. eapply lsim_mon.
    }

    13:{ pfold. eapply pind5_fold. eapply lsim_observe. i. eapply upaco5_mon_bot; eauto. }

    13:{ pfold. eapply pind5_fold. eapply lsim_sync; eauto. i. eapply upaco5_mon_bot; eauto. }

    14:{ pclearbot. hexploit SRC; ss; i. hexploit TGT; ss; i. clarify.
         pfold. eapply pind5_fold. eapply lsim_progress. right. eapply CIH. eauto. all: ss. }

  Admitted.

  Lemma lsim_set_prog
        R0 R1 (RR: R0 -> R1 -> shared_rel) tid
        src tgt shr
        (LSIM: lsim RR tid true true src tgt shr)
    :
    forall ps pt, lsim RR tid ps pt src tgt shr.
  Proof.
    i. revert_until tid. pcofix CIH. i.
    remember true as ps0 in LSIM at 1. remember true as pt0 in LSIM at 1.
    move LSIM before CIH. revert_until LSIM. punfold LSIM.
    2:{ eapply lsim_mon. }
    eapply pind5_acc in LSIM.

    { instantiate (1:= (fun ps0 pt0 src tgt shr =>
                          ps0 = true ->
                          pt0 = true ->
                          forall ps pt : bool,
                            paco5
                              (fun
                                  r0 : rel5 bool (fun _ : bool => bool) (fun _ _ : bool => itree srcE R0)
                                            (fun (_ _ : bool) (_ : itree srcE R0) => itree tgtE R1)
                                            (fun (_ _ : bool) (_ : itree srcE R0) (_ : itree tgtE R1) => shared) =>
                                  pind5 (__lsim RR tid r0) top5) r ps pt src tgt shr)) in LSIM; auto. }

    ss. clear ps0 pt0 src tgt shr LSIM.
    intros rr DEC IH gps gpt src tgt shr LSIM. clear DEC.
    intros Egps Egpt ps pt.
    eapply pind5_unfold in LSIM.
    2:{ eapply _lsim_mon. }
    inv LSIM.

    { pfold. eapply pind5_fold. econs; eauto. }

    { destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      pfold. eapply pind5_fold. eapply lsim_tauL. split; ss.
      hexploit IH. eauto. all: eauto. i. punfold H. eapply lsim_mon.
    }

    13:{ pfold. eapply pind5_fold. eapply lsim_observe. i. eapply upaco5_mon_bot; eauto. }

    13:{ pfold. eapply pind5_fold. eapply lsim_sync; eauto. i. eapply upaco5_mon_bot; eauto. }

    14:{ pclearbot. eapply paco5_mon_bot. eapply lsim_reset_prog. eauto. all: ss. }

  Admitted.


  (* Variant __lsim (tid: thread_id.(id)) *)
  (*           (lsim: forall R_src R_tgt (RR: R_src -> R_tgt -> shared_rel), *)
  (*               bool -> bool -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel) *)
  (*           (_lsim: forall R_src R_tgt (RR: R_src -> R_tgt -> shared_rel), *)
  (*               bool -> bool -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel) *)
  (*           R_src R_tgt (RR: R_src -> R_tgt -> shared_rel) *)
  (*   : *)
  (*   bool -> bool -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel := *)
  (* | lsim_ret *)
  (*     f_src f_tgt *)
  (*     ths tht im_src im_tgt st_src st_tgt o w *)
  (*     r_src r_tgt *)
  (*     (LSIM: RR r_src r_tgt (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)) *)
  (*   : *)
  (*   __lsim tid lsim _lsim RR f_src f_tgt (Ret r_src) (Ret r_tgt) (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w) *)

  (* | lsim_tauL *)
  (*     f_src f_tgt *)
  (*     ths tht im_src im_tgt st_src st_tgt o w *)
  (*     itr_src itr_tgt *)
  (*     (LSIM: _lsim _ _ RR true f_tgt itr_src itr_tgt (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)) *)
  (*   : *)
  (*   __lsim tid lsim _lsim RR f_src f_tgt (Tau itr_src) itr_tgt (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w) *)
  (* | lsim_chooseL *)
  (*     f_src f_tgt *)
  (*     ths tht im_src im_tgt st_src st_tgt o w *)
  (*     X ktr_src itr_tgt *)
  (*     (LSIM: exists x, _lsim _ _ RR true f_tgt (ktr_src x) itr_tgt (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)) *)
  (*   : *)
  (*   __lsim tid lsim _lsim RR f_src f_tgt (trigger (Choose X) >>= ktr_src) itr_tgt (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w) *)
  (* | lsim_putL *)
  (*     f_src f_tgt *)
  (*     ths tht im_src im_tgt st_src st_tgt o w *)
  (*     st ktr_src itr_tgt *)
  (*     (LSIM: _lsim _ _ RR true f_tgt (ktr_src tt) itr_tgt (ths, tht, im_src, im_tgt, st, st_tgt, o, w)) *)
  (*   : *)
  (*   __lsim tid lsim _lsim RR f_src f_tgt (trigger (Put st) >>= ktr_src) itr_tgt (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w) *)
  (* | lsim_getL *)
  (*     f_src f_tgt *)
  (*     ths tht im_src im_tgt st_src st_tgt o w *)
  (*     ktr_src itr_tgt *)
  (*     (LSIM: _lsim _ _ RR true f_tgt (ktr_src st_src) itr_tgt (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)) *)
  (*   : *)
  (*   __lsim tid lsim _lsim RR f_src f_tgt (trigger (@Get _) >>= ktr_src) itr_tgt (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w) *)
  (* | lsim_tidL *)
  (*     f_src f_tgt *)
  (*     ths tht im_src im_tgt st_src st_tgt o w *)
  (*     ktr_src itr_tgt *)
  (*     (LSIM: _lsim _ _ RR true f_tgt (ktr_src tid) itr_tgt (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)) *)
  (*   : *)
  (*   __lsim tid lsim _lsim RR f_src f_tgt (trigger (GetTid) >>= ktr_src) itr_tgt (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w) *)
  (* | lsim_UB *)
  (*     f_src f_tgt *)
  (*     ths tht im_src im_tgt st_src st_tgt o w *)
  (*     ktr_src itr_tgt *)
  (*   : *)
  (*   __lsim tid lsim _lsim RR f_src f_tgt (trigger (Undefined) >>= ktr_src) itr_tgt (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w) *)
  (* | lsim_fairL *)
  (*     f_src f_tgt *)
  (*     ths tht im_src0 im_tgt st_src st_tgt o w *)
  (*     f ktr_src itr_tgt *)
  (*     (LSIM: exists im_src1, *)
  (*         (<<FAIR: fair_update im_src0 im_src1 f>>) /\ *)
  (*           (<<LSIM: _lsim _ _ RR true f_tgt (ktr_src tt) itr_tgt (ths, tht, im_src1, im_tgt, st_src, st_tgt, o, w)>>)) *)
  (*   : *)
  (*   __lsim tid lsim _lsim RR f_src f_tgt (trigger (Fair f) >>= ktr_src) itr_tgt (ths, tht, im_src0, im_tgt, st_src, st_tgt, o, w) *)

  (* | lsim_tauR *)
  (*     f_src f_tgt *)
  (*     ths tht im_src im_tgt st_src st_tgt o w *)
  (*     itr_src itr_tgt *)
  (*     (LSIM: _lsim _ _ RR f_src true itr_src itr_tgt (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)) *)
  (*   : *)
  (*   __lsim tid lsim _lsim RR f_src f_tgt itr_src (Tau itr_tgt) (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w) *)
  (* | lsim_chooseR *)
  (*     f_src f_tgt *)
  (*     ths tht im_src im_tgt st_src st_tgt o w *)
  (*     X itr_src ktr_tgt *)
  (*     (LSIM: forall x, _lsim _ _ RR f_src true itr_src (ktr_tgt x) (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)) *)
  (*   : *)
  (*   __lsim tid lsim _lsim RR f_src f_tgt itr_src (trigger (Choose X) >>= ktr_tgt) (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w) *)
  (* | lsim_putR *)
  (*     f_src f_tgt *)
  (*     ths tht im_src im_tgt st_src st_tgt o w *)
  (*     st itr_src ktr_tgt *)
  (*     (LSIM: _lsim _ _ RR f_src true itr_src (ktr_tgt tt) (ths, tht, im_src, im_tgt, st_src, st, o, w)) *)
  (*   : *)
  (*   __lsim tid lsim _lsim RR f_src f_tgt itr_src (trigger (Put st) >>= ktr_tgt) (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w) *)
  (* | lsim_getR *)
  (*     f_src f_tgt *)
  (*     ths tht im_src im_tgt st_src st_tgt o w *)
  (*     itr_src ktr_tgt *)
  (*     (LSIM: _lsim _ _ RR f_src true itr_src (ktr_tgt st_tgt) (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)) *)
  (*   : *)
  (*   __lsim tid lsim _lsim RR f_src f_tgt itr_src (trigger (@Get _) >>= ktr_tgt) (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w) *)
  (* | lsim_tidR *)
  (*     f_src f_tgt *)
  (*     ths tht im_src im_tgt st_src st_tgt o w *)
  (*     itr_src ktr_tgt *)
  (*     (LSIM: _lsim _ _ RR f_src true itr_src (ktr_tgt tid) (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)) *)
  (*   : *)
  (*   __lsim tid lsim _lsim RR f_src f_tgt itr_src (trigger (GetTid) >>= ktr_tgt) (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w) *)
  (* | lsim_fairR *)
  (*     f_src f_tgt *)
  (*     ths tht im_src im_tgt0 st_src st_tgt o w *)
  (*     f itr_src ktr_tgt *)
  (*     (LSIM: forall im_tgt1 *)
  (*                  (FAIR: fair_update im_tgt0 im_tgt1 f), *)
  (*         (<<LSIM: _lsim _ _ RR f_src true itr_src (ktr_tgt tt) (ths, tht, im_src, im_tgt1, st_src, st_tgt, o, w)>>)) *)
  (*   : *)
  (*   __lsim tid lsim _lsim RR f_src f_tgt itr_src (trigger (Fair f) >>= ktr_tgt) (ths, tht, im_src, im_tgt0, st_src, st_tgt, o, w) *)

  (* | lsim_observe *)
  (*     f_src f_tgt *)
  (*     ths tht im_src im_tgt st_src st_tgt o w *)
  (*     fn args ktr_src ktr_tgt *)
  (*     (LSIM: forall ret, *)
  (*         lsim _ _ RR true true (ktr_src ret) (ktr_tgt ret) (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)) *)
  (*   : *)
  (*   __lsim tid lsim _lsim RR f_src f_tgt (trigger (Observe fn args) >>= ktr_src) (trigger (Observe fn args) >>= ktr_tgt) (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w) *)

  (* | lsim_sync *)
  (*     f_src f_tgt *)
  (*     ths0 tht0 im_src0 im_tgt0 st_src0 st_tgt0 o w *)
  (*     o0 w0 ktr_src ktr_tgt *)
  (*     (INV: I (ths0, tht0, im_src0, im_tgt0, st_src0, st_tgt0, o0, w0)) *)
  (*     (WORLD: world_le w w0) *)
  (*     (STUTTER: wf_src.(lt) o0 o) *)
  (*     (LSIM: forall ths1 tht1 im_src1 im_tgt1 st_src1 st_tgt1 o1 w1 *)
  (*                  (INV: I (ths1, tht1, im_src1, im_tgt1, st_src1, st_tgt1, o1, w1)) *)
  (*                  (WORLD: world_le w0 w1) *)
  (*                  im_tgt2 *)
  (*                  (TGT: fair_update im_tgt1 im_tgt2 (sum_fmap_l (thread_fmap tid))), *)
  (*         lsim _ _ RR true true (trigger (Yield) >>= ktr_src) (ktr_tgt tt) (ths1, tht1, im_src1, im_tgt2, st_src1, st_tgt1, o1, w1)) *)
  (*   : *)
  (*   __lsim tid lsim _lsim RR f_src f_tgt (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt) (ths0, tht0, im_src0, im_tgt0, st_src0, st_tgt0, o, w) *)
  (* | lsim_yieldL *)
  (*     f_src f_tgt *)
  (*     ths tht im_src0 im_tgt st_src st_tgt o0 w *)
  (*     ktr_src itr_tgt *)
  (*     (LSIM: exists im_src1 o1, *)
  (*         (<<FAIR: fair_update im_src0 im_src1 (sum_fmap_l (thread_fmap tid))>>) /\ *)
  (*           (<<LSIM: _lsim _ _ RR true f_tgt (ktr_src tt) itr_tgt (ths, tht, im_src1, im_tgt, st_src, st_tgt, o1, w)>>)) *)
  (*   : *)
  (*   __lsim tid lsim _lsim RR f_src f_tgt (trigger (Yield) >>= ktr_src) itr_tgt (ths, tht, im_src0, im_tgt, st_src, st_tgt, o0, w) *)

  (* | lsim_progress *)
  (*     ths tht im_src im_tgt st_src st_tgt o w *)
  (*     itr_src itr_tgt *)
  (*     (LSIM: lsim _ _ RR false false itr_src itr_tgt (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)) *)
  (*   : *)
  (*   __lsim tid lsim _lsim RR true true itr_src itr_tgt (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w) *)
  (* . *)

  (* Definition lsim (tid: thread_id.(id)): forall R_src R_tgt (RR: R_src -> R_tgt -> shared_rel), *)
  (*     bool -> bool -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel := *)
  (*   paco8 (fun r => pind8 (__lsim tid r) top8) bot8. *)

  (* Lemma __lsim_mon tid: forall r r' (LE: r <8= r'), (__lsim tid r) <9= (__lsim tid r'). *)
  (* Proof. *)
  (*   ii. inv PR; econs; eauto. *)
  (* Qed. *)

  (* Lemma _lsim_mon tid: forall r, monotone8 (__lsim tid r). *)
  (* Proof. *)
  (*   ii. inv IN; econs; eauto. *)
  (*   { des. eauto. } *)
  (*   { des. eauto. } *)
  (*   { i. eapply LE. eapply LSIM. eauto. } *)
  (*   { des. esplits; eauto. } *)
  (* Qed. *)

  (* Lemma lsim_mon tid: forall q, monotone8 (fun r => pind8 (__lsim tid r) q). *)
  (* Proof. *)
  (*   ii. eapply pind8_mon_gen; eauto. *)
  (*   ii. eapply __lsim_mon; eauto. *)
  (* Qed. *)

  Definition local_RR {R0 R1} (RR: R0 -> R1 -> Prop) tid :=
    fun (r_src: R0) (r_tgt: R1) '(ths2, tht2, im_src1, im_tgt1, st_src1, st_tgt1, o1, w1) =>
      (exists ths3 tht3 w2,
          (<<THSR: tid_list_remove ths2 tid ths3>>) /\
            (<<THTR: tid_list_remove tht2 tid tht3>>) /\
            (<<WORLD: world_le w1 w2>>) /\
            (<<INV: I (ths3, tht3, im_src1, im_tgt1, st_src1, st_tgt1, o1, w2)>>) /\
            (<<RET: RR r_src r_tgt>>)).

  Definition local_sim {R0 R1} (RR: R0 -> R1 -> Prop) src tgt :=
    forall ths0 tht0 im_src0 im_tgt0 st_src0 st_tgt0 o0 w0
      (* (INV: I (ths0, tht0, im_src0, im_tgt0, st_src0, st_tgt0, o0, w0)) *)
      (* tid ths1 tht1 *)
      (* (THS: tid_list_add ths0 tid ths1) *)
      (* (THT: tid_list_add tht0 tid tht1) *)
      tid
      (THS: tid_list_in tid ths0)
      (THT: tid_list_in tid tht0)
      (INV: I (ths0, tht0, im_src0, im_tgt0, st_src0, st_tgt0, o0, w0))
      fs ft,
      lsim
        (@local_RR R0 R1 RR tid)
        tid
        fs ft
        src tgt
        (ths0, tht0, im_src0, im_tgt0, st_src0, st_tgt0, o0, w0).

End PRIMIVIESIM.
#[export] Hint Constructors __lsim: core.
#[export] Hint Unfold lsim: core.
#[export] Hint Resolve __lsim_mon: paco.
#[export] Hint Resolve _lsim_mon: paco.
#[export] Hint Resolve lsim_mon: paco.



Module ModSim.
  Section MODSIM.

    Variable md_src: Mod.t.
    Variable md_tgt: Mod.t.

    Record mod_sim: Prop :=
      mk {
          wf: WF;
          world: Type;
          world_le: world -> world -> Prop;
          I: (@shared md_src.(Mod.state) md_tgt.(Mod.state) md_src.(Mod.ident) md_tgt.(Mod.ident) wf nat_wf world) -> Prop;

          init_src_thread_id: tid_list;
          init_tgt_thread_id: tid_list;
          (* INV should hold for all current existing thread_id *)
          init: forall im_tgt, exists im_src o w,
            I (init_src_thread_id, init_tgt_thread_id, im_src, im_tgt, md_src.(Mod.st_init), md_tgt.(Mod.st_init), o, w);

          (* init_thread_id: tid_list; *)
          (* init: forall im_tgt, exists im_src o w, *)
          (*   I (init_thread_id, init_thread_id, im_src, im_tgt, md_src.(Mod.st_init), md_tgt.(Mod.st_init), o, w); *)

          funs: forall fn args, local_sim world_le I (@eq Val) (md_src.(Mod.funs) fn args) (md_tgt.(Mod.funs) fn args);
        }.

    (* Record local_sim: Prop := *)
    (*   mk { *)
    (*       wf: WF; *)
    (*       world: Type; *)
    (*       world_le: world -> world -> Prop; *)
    (*       I: (@shared md_src.(Mod.state) md_tgt.(Mod.state) md_src.(Mod.ident) md_tgt.(Mod.ident) wf nat_wf world) -> Prop; *)

    (*       init: forall im_tgt th_tgt, *)
    (*       exists im_src th_src o w, *)
    (*         I ([], im_src, im_tgt, th_src, th_tgt, o, md_src.(Mod.st_init), md_tgt.(Mod.st_init), w); *)

    (*       funs: forall ths0 im_src0 im_tgt0 th_src0 th_tgt0 o0 st_src0 st_tgt0 w0 *)
    (*               (INV: I (ths0, im_src0, im_tgt0, th_src0, th_tgt0, o0, st_src0, st_tgt0, w0)) *)
    (*               fn args tid ths1 *)
    (*               (THS: tid_list_add ths0 tid ths1), *)
    (*         lsim *)
    (*           world_le *)
    (*           I *)
    (*           tid *)
    (*           (fun r_src r_tgt '(ths2, im_src1, im_tgt1, th_src1, th_tgt1, o1, st_src1, st_tgt1, w1) => *)
    (*              exists ths3 w2, *)
    (*                (<<THS: tid_list_remove ths2 tid ths3>>) /\ *)
    (*                  (<<WORLD: world_le w1 w2>>) /\ *)
    (*                  (<<INV: I (ths3, im_src1, im_tgt1, th_src1, th_tgt1, o1, st_src1, st_tgt1, w2)>>) /\ *)
    (*                  (<<RET: r_src = r_tgt>>)) *)
    (*           false false *)
    (*           (md_src.(Mod.funs) fn args) (md_tgt.(Mod.funs) fn args) *)
    (*           (ths1, im_src0, im_tgt0, th_src0, th_tgt0, o0, st_src0, st_tgt0, w0); *)
    (*     }. *)

  End MODSIM.
End ModSim.
