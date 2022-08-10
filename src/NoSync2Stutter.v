From sflib Require Import sflib.
From ITree Require Export ITree.
From Paco Require Import paco.

Require Import Coq.Classes.RelationClasses.
Require Import Program.
Require Import Permutation.

Export ITreeNotations.

From Fairness Require Import Axioms.
From Fairness Require Export ITreeLib FairBeh FairSim NatStructs.
From Fairness Require Import pind PCM World WFLib.
From Fairness Require Export Mod ModSimNoSync ModSimStutter.

Set Implicit Arguments.

Section GENORDER.
  Context `{M: URA.t}.

  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable _ident_src: ID.
  Let ident_src := @ident_src _ident_src.
  Variable _ident_tgt: ID.
  Let ident_tgt := @ident_tgt _ident_tgt.

  Variable wf_src: WF.
  Variable wf_tgt: WF.

  Let srcE := ((@eventE _ident_src +' cE) +' sE state_src).
  Let tgtE := ((@eventE _ident_tgt +' cE) +' sE state_tgt).

  Let shared :=
    (TIdSet.t *
       (@imap ident_src wf_src) *
       (@imap ident_tgt wf_tgt) *
       state_src *
       state_tgt *
       URA.car)%type.

  Let shared_rel: Type := shared -> Prop.

  Variable I: shared_rel.

  Let A R0 R1 := (bool * bool * URA.car * (itree srcE R0) * (itree tgtE R1) * shared)%type.
  Let wf_stt {R0 R1} := @ord_tree_WF (A R0 R1).

  Variant _geno
          (tid: thread_id) R_src R_tgt
          (geno: forall (RR: R_src -> R_tgt -> URA.car -> shared_rel), bool -> bool -> URA.car -> ((@wf_stt R_src R_tgt).(T) * itree srcE R_src) -> itree tgtE R_tgt -> shared_rel)
          (RR: R_src -> R_tgt -> URA.car -> shared_rel)
    :
    bool -> bool -> URA.car -> ((@wf_stt R_src R_tgt).(T) * itree srcE R_src) -> itree tgtE R_tgt -> shared_rel :=
  | geno_ret
      f_src f_tgt r_ctx o o0
      ths im_src im_tgt st_src st_tgt r_shared
      r_src r_tgt
      (LT: wf_stt.(lt) o0 o)
      (GENO: RR r_src r_tgt r_ctx (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    _geno tid geno RR f_src f_tgt r_ctx (o, Ret r_src) (Ret r_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)

  | geno_tauL
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt r_shared
      itr_src itr_tgt
      (GENO: geno RR true f_tgt r_ctx (o, itr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    _geno tid geno RR f_src f_tgt r_ctx (o, Tau itr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | geno_chooseL
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt r_shared
      X ktr_src itr_tgt
      (GENO: exists x, geno RR true f_tgt r_ctx (o, ktr_src x) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    _geno tid geno RR f_src f_tgt r_ctx (o, trigger (Choose X) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | geno_putL
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt r_shared
      st ktr_src itr_tgt
      (GENO: geno RR true f_tgt r_ctx (o, ktr_src tt) itr_tgt (ths, im_src, im_tgt, st, st_tgt, r_shared))
    :
    _geno tid geno RR f_src f_tgt r_ctx (o, trigger (Put st) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | geno_getL
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt r_shared
      ktr_src itr_tgt
      (GENO: geno RR true f_tgt r_ctx (o, ktr_src st_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    _geno tid geno RR f_src f_tgt r_ctx (o, trigger (@Get _) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | geno_tidL
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt r_shared
      ktr_src itr_tgt
      (GENO: geno RR true f_tgt r_ctx (o, ktr_src tid) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    _geno tid geno RR f_src f_tgt r_ctx (o, trigger (GetTid) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | geno_UB
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt r_shared
      ktr_src itr_tgt
    :
    _geno tid geno RR f_src f_tgt r_ctx (o, trigger (Undefined) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | geno_fairL
      f_src f_tgt r_ctx o
      ths im_src0 im_tgt st_src st_tgt r_shared
      f ktr_src itr_tgt
      (GENO: exists im_src1,
             (<<FAIR: fair_update im_src0 im_src1 (sum_fmap_r f)>>) /\
               (<<GENO: geno RR true f_tgt r_ctx (o, ktr_src tt) itr_tgt (ths, im_src1, im_tgt, st_src, st_tgt, r_shared)>>))
    :
    _geno tid geno RR f_src f_tgt r_ctx (o, trigger (Fair f) >>= ktr_src) itr_tgt (ths, im_src0, im_tgt, st_src, st_tgt, r_shared)

  | geno_tauR
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt r_shared
      itr_src itr_tgt
      (GENO: geno RR f_src true r_ctx (o, itr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    _geno tid geno RR f_src f_tgt r_ctx (o, itr_src) (Tau itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | geno_chooseR
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt r_shared
      X itr_src ktr_tgt
      (GENO: forall x, geno RR f_src true r_ctx (o, itr_src) (ktr_tgt x) (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    _geno tid geno RR f_src f_tgt r_ctx (o, itr_src) (trigger (Choose X) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | geno_putR
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt r_shared
      st itr_src ktr_tgt
      (GENO: geno RR f_src true r_ctx (o, itr_src) (ktr_tgt tt) (ths, im_src, im_tgt, st_src, st, r_shared))
    :
    _geno tid geno RR f_src f_tgt r_ctx (o, itr_src) (trigger (Put st) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | geno_getR
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt r_shared
      itr_src ktr_tgt
      (GENO: geno RR f_src true r_ctx (o, itr_src) (ktr_tgt st_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    _geno tid geno RR f_src f_tgt r_ctx (o, itr_src) (trigger (@Get _) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | geno_tidR
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt r_shared
      itr_src ktr_tgt
      (GENO: geno RR f_src true r_ctx (o, itr_src) (ktr_tgt tid) (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    _geno tid geno RR f_src f_tgt r_ctx (o, itr_src) (trigger (GetTid) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  | geno_fairR
      f_src f_tgt r_ctx o
      ths im_src im_tgt0 st_src st_tgt r_shared
      f itr_src ktr_tgt
      (GENO: forall im_tgt1
                   (FAIR: fair_update im_tgt0 im_tgt1 (sum_fmap_r f)),
          (<<GENO: geno RR f_src true r_ctx (o, itr_src) (ktr_tgt tt) (ths, im_src, im_tgt1, st_src, st_tgt, r_shared)>>))
    :
    _geno tid geno RR f_src f_tgt r_ctx (o, itr_src) (trigger (Fair f) >>= ktr_tgt) (ths, im_src, im_tgt0, st_src, st_tgt, r_shared)

  | geno_observe
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt r_shared
      fn args ktr_src ktr_tgt
      (GENO: forall ret,
             geno RR true true r_ctx (o, ktr_src ret) (ktr_tgt ret) (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    _geno tid geno RR f_src f_tgt r_ctx (o, trigger (Observe fn args) >>= ktr_src) (trigger (Observe fn args) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)

  | geno_yieldR
      f_src f_tgt r_ctx0 o0
      ths0 im_src0 im_tgt0 st_src0 st_tgt0 r_shared0
      r_own r_shared
      ktr_src ktr_tgt
      (INV: I (ths0, im_src0, im_tgt0, st_src0, st_tgt0, r_shared))
      (VALID: URA.wf (r_shared ⋅ r_own ⋅ r_ctx0))
      (GENO: forall ths1 im_src1 im_tgt1 st_src1 st_tgt1 r_shared1 r_ctx1
               (INV: I (ths1, im_src1, im_tgt1, st_src1, st_tgt1, r_shared1))
               (VALID: URA.wf (r_shared1 ⋅ r_own ⋅ r_ctx1))
               im_tgt2
               (TGT: fair_update im_tgt1 im_tgt2 (sum_fmap_l (tids_fmap tid ths1))),
        exists o1,
          (<<GENO: geno RR f_src true r_ctx1 (o1, trigger (Yield) >>= ktr_src) (ktr_tgt tt) (ths1, im_src1, im_tgt2, st_src1, st_tgt1, r_shared1)>>) /\
            (<<STUTTER: wf_stt.(lt) o1 o0>>))
    :
    _geno tid geno RR f_src f_tgt r_ctx0 (o0, trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt) (ths0, im_src0, im_tgt0, st_src0, st_tgt0, r_shared0)

  | geno_yieldL
      f_src f_tgt r_ctx o0
      ths im_src0 im_tgt st_src st_tgt r_shared
      ktr_src itr_tgt
      (GENO: exists im_src1 o1,
          (<<FAIR: fair_update im_src0 im_src1 (sum_fmap_l (tids_fmap tid ths))>>) /\
            (<<GENO: geno RR true f_tgt r_ctx (o1, ktr_src tt) itr_tgt (ths, im_src1, im_tgt, st_src, st_tgt, r_shared)>>))
    :
    _geno tid geno RR f_src f_tgt r_ctx (o0, trigger (Yield) >>= ktr_src) itr_tgt (ths, im_src0, im_tgt, st_src, st_tgt, r_shared)

  | geno_progress
      r_ctx o
      ths im_src im_tgt st_src st_tgt r_shared
      itr_src itr_tgt
      (GENO: ModSimNoSync.lsim I tid RR false false r_ctx itr_src itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared))
    :
    _geno tid geno RR true true r_ctx (o, itr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared)
  .

  Definition geno (tid: thread_id)
             R_src R_tgt (RR: R_src -> R_tgt -> URA.car -> shared_rel):
    bool -> bool -> URA.car -> (wf_stt.(T) * itree srcE R_src) -> itree tgtE R_tgt -> shared_rel :=
    pind7 (@_geno tid R_src R_tgt) top7 RR.

  Lemma geno_mon tid R0 R1: monotone7 (@_geno tid R0 R1).
  Proof.
    ii. inv IN; try (econs; eauto; fail).
    { des. econs; eauto. }
    { des. econs; eauto. }
    { econs; eauto. i. eapply LE. eapply GENO. eauto. }
    { econs; eauto. i. specialize (GENO _ _ _ _ _ _ _ INV0 VALID0 _ TGT). des. esplits; eauto. }
    { des. econs; esplits; eauto. }
  Qed.

  Local Hint Constructors _geno: core.
  Local Hint Unfold geno: core.
  Local Hint Resolve geno_mon: paco.

  Lemma geno_ord_weak
        tid R0 R1 (LRR: R0 -> R1 -> URA.car -> shared_rel)
        ps pt r_ctx src tgt (shr: shared) o0 o1
        (LT: wf_stt.(lt) o0 o1)
        (GENO: geno tid LRR ps pt r_ctx (o0, src) tgt shr)
    :
    geno tid LRR ps pt r_ctx (o1, src) tgt shr.
  Proof.
    remember (o0, src) as osrc.
    move GENO before tid. revert_until GENO.
    pattern LRR, ps, pt, r_ctx, osrc, tgt, shr.
    revert LRR ps pt r_ctx osrc tgt shr GENO. apply pind7_acc.
    intros rr DEC IH. clear DEC. intros LRR ps pt r_ctx osrc tgt shr GENO.
    i; clarify.
    eapply pind7_unfold in GENO; eauto with paco.
    inv GENO.

    { eapply pind7_fold. econs 1; eauto. }
    { eapply pind7_fold. econs 2; eauto.
      destruct GENO0 as [GENO IND]. eapply IH in IND; eauto. split; ss.
    }
    { eapply pind7_fold. econs 3; eauto.
      des. destruct GENO0 as [GENO IND]. eapply IH in IND; eauto. esplits; eauto.
      split; ss; eauto.
    }
    { eapply pind7_fold. econs 4; eauto.
      destruct GENO0 as [GENO IND]. eapply IH in IND; eauto. split; ss.
    }
    { eapply pind7_fold. econs 5; eauto.
      destruct GENO0 as [GENO IND]. eapply IH in IND; eauto. split; ss.
    }
    { eapply pind7_fold. econs 6; eauto.
      destruct GENO0 as [GENO IND]. eapply IH in IND; eauto. split; ss.
    }
    { eapply pind7_fold. econs 7; eauto. }
    { eapply pind7_fold. econs 8; eauto.
      des. destruct GENO as [GENO IND]. eapply IH in IND; eauto. esplits; eauto.
      split; ss; eauto.
    }

    { eapply pind7_fold. econs 9; eauto.
      destruct GENO0 as [GENO IND]. eapply IH in IND; eauto. split; ss.
    }
    { eapply pind7_fold. econs 10; eauto.
      i. specialize (GENO0 x).
      destruct GENO0 as [GENO IND]. eapply IH in IND; eauto. split; ss.
    }
    { eapply pind7_fold. econs 11; eauto.
      destruct GENO0 as [GENO IND]. eapply IH in IND; eauto. split; ss.
    }
    { eapply pind7_fold. econs 12; eauto.
      destruct GENO0 as [GENO IND]. eapply IH in IND; eauto. split; ss.
    }
    { eapply pind7_fold. econs 13; eauto.
      destruct GENO0 as [GENO IND]. eapply IH in IND; eauto. split; ss.
    }
    { eapply pind7_fold. econs 14; eauto.
      i. specialize (GENO0 _ FAIR).
      destruct GENO0 as [GENO IND]. eapply IH in IND; eauto. split; ss.
    }
    { eapply pind7_fold. econs 15; eauto.
      i. specialize (GENO0 ret).
      destruct GENO0 as [GENO IND]. eapply IH in IND; eauto. split; ss.
    }

    { eapply pind7_fold. econs 16; eauto.
      i. specialize (GENO0 _ _ _ _ _ _ _ INV0 VALID0 _ TGT). des. esplits; eauto.
      destruct GENO as [GENO IND]. eapply IH in IND; eauto. split; ss.
    }

    { eapply pind7_fold. econs 17; eauto.
      des. esplits; eauto.
      eapply upind7_mon; eauto. ss.
    }

    { eapply pind7_fold. econs 18; eauto. }

  Qed.

  Lemma nosync_geno
        tid R0 R1 (RR: R0 -> R1 -> URA.car -> shared_rel)
        ps pt r_ctx src tgt shr
        (LSIM: ModSimNoSync.lsim I tid RR ps pt r_ctx src tgt shr)
    :
    exists o, geno tid RR ps pt r_ctx (o, src) tgt shr.
  Proof.
    punfold LSIM.
    pattern R0, R1, RR, ps, pt, r_ctx, src, tgt, shr.
    revert R0 R1 RR ps pt r_ctx src tgt shr LSIM. apply pind9_acc.
    intros rr DEC IH. clear DEC. intros R0 R1 RR ps pt r_ctx src tgt shr LSIM.
    eapply pind9_unfold in LSIM; eauto with paco.
    set (fzero:= fun _: (A R0 R1) => @ord_tree_base (A R0 R1)). set (one:= ord_tree_cons fzero).
    inv LSIM.

    { exists one. eapply pind7_fold. econs 1; eauto.
      instantiate (1:=fzero (ps, pt, r_ctx, Ret r_src, Ret r_tgt, (ths, im_src, im_tgt, st_src, st_tgt, r_shared))); ss.
    }

    { destruct LSIM0 as [LSIM IND]. eapply IH in IND. des.
      exists o. eapply pind7_fold. econs 2; eauto. split; ss.
    }
    { des. destruct LSIM0 as [LSIM IND]. eapply IH in IND. des.
      exists o. eapply pind7_fold. econs 3; eauto. eexists. split; ss. eauto.
    }
    { destruct LSIM0 as [LSIM IND]. eapply IH in IND. des.
      exists o. eapply pind7_fold. econs 4; eauto. split; ss.
    }
    { destruct LSIM0 as [LSIM IND]. eapply IH in IND. des.
      exists o. eapply pind7_fold. econs 5; auto. split; ss.
    }
    { destruct LSIM0 as [LSIM IND]. eapply IH in IND. des.
      exists o. eapply pind7_fold. econs 6; auto. split; ss.
    }
    { exists one. eapply pind7_fold. econs 7; eauto. }
    { des. destruct LSIM as [LSIM IND]. eapply IH in IND. des.
      exists o. eapply pind7_fold. econs 8; eauto. esplits; eauto. split; ss.
    }

    { destruct LSIM0 as [LSIM IND]. eapply IH in IND. des. exists o.
      eapply pind7_fold. econs 9; eauto. ss.
    }

    { hexploit ord_tree_join.
      { instantiate (2:=A R0 R1).
        instantiate (2:= fun '(ps, pt, rs, src, tgt, shr) => @rr R0 R1 RR ps pt rs src tgt shr).
        i. ss. des_ifs. eapply IH in SAT.
        instantiate (1:= fun '(ps, pt, rs, src, tgt, shr) o =>
                           geno tid RR ps pt rs (o, src) tgt shr).
        eauto.
      }
      intro JOIN. des. exists o1.
      eapply pind7_fold. econs 10.
      i. specialize (LSIM0 x). destruct LSIM0 as [LSIM IND].
      specialize (JOIN (ps, true, r_ctx, src, (ktr_tgt x), (ths, im_src, im_tgt, st_src, st_tgt, r_shared))).
      destruct JOIN; auto. des. split; ss.
      eapply geno_ord_weak; eauto.
    }

    { destruct LSIM0 as [LSIM IND]. eapply IH in IND. des. exists o.
      eapply pind7_fold. econs 11; eauto. ss.
    }
    { destruct LSIM0 as [LSIM IND]. eapply IH in IND. des. exists o.
      eapply pind7_fold. econs 12; eauto. ss.
    }
    { destruct LSIM0 as [LSIM IND]. eapply IH in IND. des. exists o.
      eapply pind7_fold. econs 13; eauto. ss.
    }

    { hexploit ord_tree_join.
      { instantiate (2:=A R0 R1).
        instantiate (2:= fun '(ps, pt, rs, src, tgt, shr) => @rr R0 R1 RR ps pt rs src tgt shr).
        i. ss. des_ifs. eapply IH in SAT.
        instantiate (1:= fun '(ps, pt, rs, src, tgt, shr) o =>
                           geno tid RR ps pt rs (o, src) tgt shr).
        eauto.
      }
      intro JOIN. des. exists o1.
      eapply pind7_fold. econs 14.
      i. specialize (LSIM0 _ FAIR). destruct LSIM0 as [LSIM IND].
      specialize (JOIN (ps, true, r_ctx, src, (ktr_tgt ()), (ths, im_src, im_tgt1, st_src, st_tgt, r_shared))).
      destruct JOIN; auto. des. split; ss.
      eapply geno_ord_weak; eauto.
    }

    { hexploit ord_tree_join.
      { instantiate (2:=A R0 R1).
        instantiate (2:= fun '(ps, pt, rs, src, tgt, shr) => @rr R0 R1 RR ps pt rs src tgt shr).
        i. ss. des_ifs. eapply IH in SAT.
        instantiate (1:= fun '(ps, pt, rs, src, tgt, shr) o =>
                           geno tid RR ps pt rs (o, src) tgt shr).
        eauto.
      }
      intro JOIN. des. exists o1.
      eapply pind7_fold. econs 15.
      i. specialize (LSIM0 ret). destruct LSIM0 as [LSIM IND].
      specialize (JOIN (true, true, r_ctx, ktr_src ret, ktr_tgt ret, (ths, im_src, im_tgt, st_src, st_tgt, r_shared))).
      destruct JOIN; auto. des. split; ss.
      eapply geno_ord_weak; eauto.
    }

    { hexploit ord_tree_join.
      { instantiate (2:=A R0 R1).
        instantiate (2:= fun '(ps, pt, rs, src, tgt, shr) => @rr R0 R1 RR ps pt rs src tgt shr).
        i. ss. des_ifs. eapply IH in SAT.
        instantiate (1:= fun '(ps, pt, rs, src, tgt, shr) o =>
                           geno tid RR ps pt rs (o, src) tgt shr).
        eauto.
      }
      intro JOIN. des. exists o1.
      eapply pind7_fold. econs 16.
      1,2: eauto.
      i. specialize (LSIM0 _ _ _ _ _ _ _ INV0 VALID0 _ TGT). destruct LSIM0 as [LSIM IND].
      specialize (JOIN (ps, true, r_ctx1, (x <- trigger Yield;; ktr_src x), ktr_tgt (), (ths1, im_src1, im_tgt2, st_src1, st_tgt1, r_shared1))).
      destruct JOIN; auto. des. esplits; eauto. split; ss.
    }

    { des. destruct LSIM as [LSIM IND]. eapply IH in IND. des. exists o.
      eapply pind7_fold. econs 17; eauto. esplits; eauto.
      split; ss. eauto.
    }

    { exists one. eapply pind7_fold. econs 18. pclearbot. auto. }

  Qed.

End GENORDER.
#[export] Hint Constructors _geno: core.
#[export] Hint Unfold geno: core.
#[export] Hint Resolve geno_mon: paco.

Section PROOF.

  Context `{M: URA.t}.

  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable _ident_src: ID.
  Let ident_src := @ident_src _ident_src.
  Variable _ident_tgt: ID.
  Let ident_tgt := @ident_tgt _ident_tgt.

  Variable wf_src: WF.
  Variable wf_tgt: WF.

  Let srcE := ((@eventE _ident_src +' cE) +' sE state_src).
  Let tgtE := ((@eventE _ident_tgt +' cE) +' sE state_tgt).

  Let shared :=
    (TIdSet.t *
       (@imap ident_src wf_src) *
       (@imap ident_tgt wf_tgt) *
       state_src *
       state_tgt *
       URA.car)%type.

  Let shared_rel: Type := shared -> Prop.

  Variable I: shared_rel.

  Definition lift_wf (wf: WF): WF := sum_WF (sum_WF wf wf) wf.

  Definition mk_o (wf: WF) (w: wf.(T)) R (o: wf.(T)) (ps: bool) (itr_src: itree srcE R):
    (lift_wf wf).(T) :=
    if ps
    then match (observe itr_src) with
         | VisF ((|Yield)|)%sum _ => (inl (inr o))
         | _ => (inr w)
         end
    else match (observe itr_src) with
         | VisF ((|Yield)|)%sum _ => (inl (inl o))
         | _ => (inr w)
         end.

  Let A R0 R1 := (bool * bool * URA.car * (itree srcE R0) * (itree tgtE R1) * shared)%type.
  Let wf_ot R0 R1 := @ord_tree_WF (A R0 R1).
  Let wf_stt R0 R1 := lift_wf (@wf_ot R0 R1).

  Lemma nosync_implies_stutter
        tid
        R0 R1 (LRR: R0 -> R1 -> URA.car -> shared_rel)
        ps pt r_ctx src tgt
        (shr: shared)
        (LSIM: ModSimNoSync.lsim I tid LRR ps pt r_ctx src tgt shr)
    :
    exists (o: (@wf_stt R0 R1).(T)),
      ModSimStutter.lsim (@wf_stt R0 R1) I tid LRR ps pt r_ctx (o, src) tgt shr.
  Proof.
    eapply nosync_geno in LSIM. des.
    exists (mk_o (@wf_ot R0 R1) (@ord_tree_base _) o ps src).
    revert_until R1. ginit. gcofix CIH; i.
    remember (o, src) as osrc.
    move LSIM before CIH. revert_until LSIM.
    pattern LRR, ps, pt, r_ctx, osrc, tgt, shr.
    revert LRR ps pt r_ctx osrc tgt shr LSIM. apply pind7_acc.
    intros rr DEC IH. clear DEC. intros LRR ps pt r_ctx osrc tgt shr LSIM.
    intros src o Eosrc. clarify.
    eapply pind7_unfold in LSIM; eauto with paco.
    inv LSIM.

    { guclo lsim_indC_spec. econs 1; eauto.
      instantiate (1:=inl (inl o1)). ss.
      unfold mk_o. des_ifs. all: econs 3.
    }

    { destruct GENO as [GENO IND]. eapply IH in IND; eauto.
      guclo lsim_indC_spec. econs 2; eauto.
      guclo lsim_ord_weakC_spec. econs; eauto.
      unfold mk_o. des_ifs; try reflexivity.
      - right. ss. econs 3.
      - right. ss. econs 3.
    }
    { des. destruct GENO as [GENO IND]. eapply IH in IND; eauto.
      guclo lsim_indC_spec. econs 3; eauto. exists x.
      guclo lsim_ord_weakC_spec. econs; eauto.
      unfold mk_o. des_ifs; try reflexivity.
      - right. ss. econs 3.
      - right. ss. econs 3.
    }
    { destruct GENO as [GENO IND]. eapply IH in IND; eauto.
      guclo lsim_indC_spec. econs 4; eauto.
      guclo lsim_ord_weakC_spec. econs; eauto.
      unfold mk_o. des_ifs; try reflexivity.
      - right. ss. econs 3.
      - right. ss. econs 3.
    }
    { destruct GENO as [GENO IND]. eapply IH in IND; eauto.
      guclo lsim_indC_spec. econs 5; eauto.
      guclo lsim_ord_weakC_spec. econs; eauto.
      unfold mk_o. des_ifs; try reflexivity.
      - right. ss. econs 3.
      - right. ss. econs 3.
    }
    { destruct GENO as [GENO IND]. eapply IH in IND; eauto.
      guclo lsim_indC_spec. econs 6; eauto.
      guclo lsim_ord_weakC_spec. econs; eauto.
      unfold mk_o. des_ifs; try reflexivity.
      - right. ss. econs 3.
      - right. ss. econs 3.
    }
    { guclo lsim_indC_spec. econs 7; eauto. }
    { des. destruct GENO0 as [GENO IND]. eapply IH in IND; eauto.
      guclo lsim_indC_spec. econs 8; eauto. esplits; eauto.
      guclo lsim_ord_weakC_spec. econs; eauto.
      unfold mk_o. des_ifs; try reflexivity.
      - right. ss. econs 3.
      - right. ss. econs 3.
    }

    { destruct GENO as [GENO IND]. eapply IH in IND; eauto.
      guclo lsim_indC_spec. econs 9; eauto.
    }
    { guclo lsim_indC_spec. econs 10; eauto. i. specialize (GENO x).
      destruct GENO as [GENO IND]. eapply IH in IND; eauto.
    }
    { destruct GENO as [GENO IND]. eapply IH in IND; eauto.
      guclo lsim_indC_spec. econs 11; eauto.
    }
    { destruct GENO as [GENO IND]. eapply IH in IND; eauto.
      guclo lsim_indC_spec. econs 12; eauto.
    }
    { destruct GENO as [GENO IND]. eapply IH in IND; eauto.
      guclo lsim_indC_spec. econs 13; eauto.
    }
    { guclo lsim_indC_spec. econs 14; eauto. i. specialize (GENO _ FAIR).
      destruct GENO as [GENO IND]. eapply IH in IND; eauto.
    }

    { guclo lsim_indC_spec. econs 15; eauto. i. specialize (GENO ret).
      destruct GENO as [GENO IND]. eapply IH in IND; eauto.
      guclo lsim_ord_weakC_spec. econs; eauto.
      unfold mk_o. ss. des_ifs; try reflexivity.
      - right. ss. econs 3.
      - right. ss. econs 3.
    }

    { guclo lsim_indC_spec. econs 16; eauto. i.
      specialize (GENO _ _ _ _ _ _ _ INV0 VALID0 _ TGT). des.
      destruct GENO0 as [GENO IND]. eapply IH in IND; eauto.
      esplits.
      guclo lsim_resetC_spec. econs; eauto.
      unfold mk_o; ss. rewrite !bind_trigger. ss.
      des_ifs.
      - econs 1. econs 2. auto.
      - econs 1. econs 1. auto.
    }

    { des. destruct GENO0 as [GENO IND]. eapply IH in IND; eauto.
      guclo lsim_indC_spec. econs 17; eauto.
    }

    { eapply nosync_geno in GENO. des.
      guclo lsim_ord_weakC_spec. econs.
      instantiate (1:=mk_o (@wf_ot R0 R1) (@ord_tree_base _) o0 false src).
      gfinal. right. pfold. eapply pind9_fold. econs 18. right. eapply CIH. auto.
      ss. des_ifs; try reflexivity. right. ss. econs 1. econs 3.
    }

  Qed.

End PROOF.
