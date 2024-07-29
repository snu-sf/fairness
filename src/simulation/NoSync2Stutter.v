From sflib Require Import sflib.
From Paco Require Import paco.

Require Import Coq.Classes.RelationClasses.
Require Import Program.
From iris.algebra Require Import cmra.

From Fairness Require Import Axioms.
From Fairness Require Export ITreeLib FairBeh FairSim NatStructsLarge.
From Fairness Require Import pind PCM World WFLibLarge.
From Fairness Require Export Mod ModSimNoSync ModSimStutter.

Set Implicit Arguments.

Section GENORDER.
  Context `{M: ucmra}.

  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable _ident_src: ID.
  Let ident_src := @ident_src _ident_src.
  Variable _ident_tgt: ID.
  Let ident_tgt := @ident_tgt _ident_tgt.

  Variable wf_src: WF.
  Variable wf_tgt: WF.

  Let srcE := threadE _ident_src state_src.
  Let tgtE := threadE _ident_tgt state_tgt.

  Let shared := shared state_src state_tgt _ident_src _ident_tgt wf_src wf_tgt.
  Let shared_rel: Type := shared -> Prop.
  Variable I: shared -> (cmra_car M) -> Prop.

  Let A R0 R1 := (bool * bool * (cmra_car M) * (itree srcE R0) * (itree tgtE R1) * shared)%type.
  Let wf_stt {R0 R1} := @ord_tree_WF (A R0 R1).

  Variant _geno
          (tid: thread_id) R_src R_tgt (RR: R_src -> R_tgt -> (cmra_car M) -> shared_rel)
          (geno: bool -> bool -> (cmra_car M) -> ((@wf_stt R_src R_tgt).(T) * itree srcE R_src) -> itree tgtE R_tgt -> shared_rel)
    :
    bool -> bool -> (cmra_car M) -> ((@wf_stt R_src R_tgt).(T) * itree srcE R_src) -> itree tgtE R_tgt -> shared_rel :=
  | geno_ret
      f_src f_tgt r_ctx o o0
      ths im_src im_tgt st_src st_tgt
      r_src r_tgt
      (LT: wf_stt.(lt) o0 o)
      (GENO: RR r_src r_tgt r_ctx (ths, im_src, im_tgt, st_src, st_tgt))
    :
    _geno tid RR geno f_src f_tgt r_ctx (o, Ret r_src) (Ret r_tgt) (ths, im_src, im_tgt, st_src, st_tgt)

  | geno_tauL
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt
      itr_src itr_tgt
      (GENO: geno true f_tgt r_ctx (o, itr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt))
    :
    _geno tid RR geno f_src f_tgt r_ctx (o, Tau itr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt)
  | geno_chooseL
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt
      X ktr_src itr_tgt
      (GENO: exists x, geno true f_tgt r_ctx (o, ktr_src x) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt))
    :
    _geno tid RR geno f_src f_tgt r_ctx (o, trigger (Choose X) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt)
  | geno_stateL
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt
      X run ktr_src itr_tgt
      (GENO: geno true f_tgt r_ctx (o, ktr_src (snd (run st_src) : X)) itr_tgt (ths, im_src, im_tgt, fst (run st_src), st_tgt))
    :
    _geno tid RR geno f_src f_tgt r_ctx (o, trigger (State run) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt)
  | geno_tidL
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt
      ktr_src itr_tgt
      (GENO: geno true f_tgt r_ctx (o, ktr_src tid) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt))
    :
    _geno tid RR geno f_src f_tgt r_ctx (o, trigger (GetTid) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt)
  | geno_UB
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt
      ktr_src itr_tgt
    :
    _geno tid RR geno f_src f_tgt r_ctx (o, trigger (Undefined) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt)
  | geno_fairL
      f_src f_tgt r_ctx o
      ths im_src0 im_tgt st_src st_tgt
      f ktr_src itr_tgt
      (GENO: exists im_src1,
             (<<FAIR: fair_update im_src0 im_src1 (prism_fmap inrp f)>>) /\
               (<<GENO: geno true f_tgt r_ctx (o, ktr_src tt) itr_tgt (ths, im_src1, im_tgt, st_src, st_tgt)>>))
    :
    _geno tid RR geno f_src f_tgt r_ctx (o, trigger (Fair f) >>= ktr_src) itr_tgt (ths, im_src0, im_tgt, st_src, st_tgt)

  | geno_tauR
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt
      itr_src itr_tgt
      (GENO: geno f_src true r_ctx (o, itr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt))
    :
    _geno tid RR geno f_src f_tgt r_ctx (o, itr_src) (Tau itr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)
  | geno_chooseR
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt
      X itr_src ktr_tgt
      (GENO: forall x, geno f_src true r_ctx (o, itr_src) (ktr_tgt x) (ths, im_src, im_tgt, st_src, st_tgt))
    :
    _geno tid RR geno f_src f_tgt r_ctx (o, itr_src) (trigger (Choose X) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)
  | geno_stateR
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt
      X run itr_src ktr_tgt
      (GENO: geno f_src true r_ctx (o, itr_src) (ktr_tgt (snd (run st_tgt) : X)) (ths, im_src, im_tgt, st_src, fst (run st_tgt)))
    :
    _geno tid RR geno f_src f_tgt r_ctx (o, itr_src) (trigger (State run) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)
  | geno_tidR
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt
      itr_src ktr_tgt
      (GENO: geno f_src true r_ctx (o, itr_src) (ktr_tgt tid) (ths, im_src, im_tgt, st_src, st_tgt))
    :
    _geno tid RR geno f_src f_tgt r_ctx (o, itr_src) (trigger (GetTid) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)
  | geno_fairR
      f_src f_tgt r_ctx o
      ths im_src im_tgt0 st_src st_tgt
      f itr_src ktr_tgt
      (GENO: forall im_tgt1 (FAIR: fair_update im_tgt0 im_tgt1 (prism_fmap inrp f)),
          (<<GENO: geno f_src true r_ctx (o, itr_src) (ktr_tgt tt) (ths, im_src, im_tgt1, st_src, st_tgt)>>))
    :
    _geno tid RR geno f_src f_tgt r_ctx (o, itr_src) (trigger (Fair f) >>= ktr_tgt) (ths, im_src, im_tgt0, st_src, st_tgt)

  | geno_observe
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt
      fn args ktr_src ktr_tgt
      (GENO: forall ret,
             geno true true r_ctx (o, ktr_src ret) (ktr_tgt ret) (ths, im_src, im_tgt, st_src, st_tgt))
    :
    _geno tid RR geno f_src f_tgt r_ctx (o, trigger (Observe fn args) >>= ktr_src) (trigger (Observe fn args) >>= ktr_tgt) (ths, im_src, im_tgt, st_src, st_tgt)

  | geno_call
      f_src f_tgt r_ctx o
      ths im_src im_tgt st_src st_tgt
      fn args ktr_src itr_tgt
    :
    _geno tid RR geno f_src f_tgt r_ctx (o, trigger (Call fn args) >>= ktr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt)

  | geno_yieldR
      f_src f_tgt r_ctx0 o0
      ths0 im_src0 im_tgt0 st_src0 st_tgt0
      r_own r_shared
      ktr_src ktr_tgt
      (INV: I (ths0, im_src0, im_tgt0, st_src0, st_tgt0) r_shared)
      (VALID: ✓ (r_shared ⋅ r_own ⋅ r_ctx0))
      o1
      (STUTTER: wf_stt.(lt) o1 o0)
      (GENO: forall ths1 im_src1 im_tgt1 st_src1 st_tgt1 r_shared1 r_ctx1
               (INV: I (ths1, im_src1, im_tgt1, st_src1, st_tgt1) r_shared1)
               (VALID: ✓ (r_shared1 ⋅ r_own ⋅ r_ctx1))
               im_tgt2
               (TGT: fair_update im_tgt1 im_tgt2 (prism_fmap inlp (tids_fmap tid ths1))),
          (<<GENO: geno f_src true r_ctx1 (o1, trigger (Yield) >>= ktr_src) (ktr_tgt tt) (ths1, im_src1, im_tgt2, st_src1, st_tgt1)>>))
    :
    _geno tid RR geno f_src f_tgt r_ctx0 (o0, trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt) (ths0, im_src0, im_tgt0, st_src0, st_tgt0)

  | geno_yieldL
      f_src f_tgt r_ctx o0
      ths im_src0 im_tgt st_src st_tgt
      ktr_src itr_tgt
      (GENO: exists im_src1 o1,
          (<<FAIR: fair_update im_src0 im_src1 (prism_fmap inlp (tids_fmap tid ths))>>) /\
            (<<GENO: geno true f_tgt r_ctx (o1, ktr_src tt) itr_tgt (ths, im_src1, im_tgt, st_src, st_tgt)>>))
    :
    _geno tid RR geno f_src f_tgt r_ctx (o0, trigger (Yield) >>= ktr_src) itr_tgt (ths, im_src0, im_tgt, st_src, st_tgt)

  | geno_progress
      r_ctx o
      ths im_src im_tgt st_src st_tgt
      itr_src itr_tgt
      (GENO: ModSimNoSync.lsim I tid RR false false r_ctx itr_src itr_tgt (ths, im_src, im_tgt, st_src, st_tgt))
    :
    _geno tid RR geno true true r_ctx (o, itr_src) itr_tgt (ths, im_src, im_tgt, st_src, st_tgt)
  .

  Definition geno (tid: thread_id)
             R_src R_tgt (RR: R_src -> R_tgt -> (cmra_car M) -> shared_rel):
    bool -> bool -> (cmra_car M) -> (wf_stt.(T) * itree srcE R_src) -> itree tgtE R_tgt -> shared_rel :=
    pind6 (_geno tid RR) top6.

  Lemma geno_mon tid R0 R1 (RR: R0 -> R1 -> (cmra_car M) -> shared_rel): monotone6 (_geno tid RR).
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
        tid R0 R1 (LRR: R0 -> R1 -> (cmra_car M) -> shared_rel)
        ps pt r_ctx src tgt (shr: shared) o0 o1
        (LT: wf_stt.(lt) o0 o1)
        (GENO: geno tid LRR ps pt r_ctx (o0, src) tgt shr)
    :
    geno tid LRR ps pt r_ctx (o1, src) tgt shr.
  Proof.
    remember (o0, src) as osrc.
    move GENO before tid. revert_until GENO.
    pattern ps, pt, r_ctx, osrc, tgt, shr.
    revert ps pt r_ctx osrc tgt shr GENO. apply pind6_acc.
    intros rr DEC IH. clear DEC. intros ps pt r_ctx osrc tgt shr GENO.
    i; clarify.
    eapply pind6_unfold in GENO; eauto with paco.
    inv GENO.

    { eapply pind6_fold. eapply geno_ret; eauto. }
    { eapply pind6_fold. eapply geno_tauL; eauto.
      destruct GENO0 as [GENO IND]. eapply IH in IND; eauto. split; ss.
    }
    { eapply pind6_fold. eapply geno_chooseL; eauto.
      des. destruct GENO0 as [GENO IND]. eapply IH in IND; eauto. esplits; eauto.
      split; ss; eauto.
    }
    { eapply pind6_fold. eapply geno_stateL; eauto.
      destruct GENO0 as [GENO IND]. eapply IH in IND; eauto. split; ss.
    }
    { eapply pind6_fold. eapply geno_tidL; eauto.
      destruct GENO0 as [GENO IND]. eapply IH in IND; eauto. split; ss.
    }
    { eapply pind6_fold. eapply geno_UB; eauto. }
    { eapply pind6_fold. eapply geno_fairL; eauto.
      des. destruct GENO as [GENO IND]. eapply IH in IND; eauto. esplits; eauto.
      split; ss; eauto.
    }

    { eapply pind6_fold. eapply geno_tauR; eauto.
      destruct GENO0 as [GENO IND]. eapply IH in IND; eauto. split; ss.
    }
    { eapply pind6_fold. eapply geno_chooseR; eauto.
      i. specialize (GENO0 x).
      destruct GENO0 as [GENO IND]. eapply IH in IND; eauto. split; ss.
    }
    { eapply pind6_fold. eapply geno_stateR; eauto.
      destruct GENO0 as [GENO IND]. eapply IH in IND; eauto. split; ss.
    }
    { eapply pind6_fold. eapply geno_tidR; eauto.
      destruct GENO0 as [GENO IND]. eapply IH in IND; eauto. split; ss.
    }
    { eapply pind6_fold. eapply geno_fairR; eauto.
      i. specialize (GENO0 _ FAIR).
      destruct GENO0 as [GENO IND]. eapply IH in IND; eauto. split; ss.
    }
    { eapply pind6_fold. eapply geno_observe; eauto.
      i. specialize (GENO0 ret).
      destruct GENO0 as [GENO IND]. eapply IH in IND; eauto. split; ss.
    }

    { eapply pind6_fold. eapply geno_call; eauto. }

    { eapply pind6_fold. eapply geno_yieldR; eauto.
      i. specialize (GENO0 _ _ _ _ _ _ _ INV0 VALID0 _ TGT). des. esplits; eauto.
      destruct GENO0 as [GENO IND]. eapply IH in IND; eauto. split; ss.
    }

    { eapply pind6_fold. eapply geno_yieldL; eauto.
      des. esplits; eauto.
      eapply upind6_mon; eauto. ss.
    }

    { eapply pind6_fold. eapply geno_progress; eauto. }

  Qed.

  Lemma nosync_geno
        tid R0 R1 (RR: R0 -> R1 -> (cmra_car M) -> shared_rel)
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

    { exists one. eapply pind6_fold. eapply geno_ret; eauto.
      instantiate (1:=fzero (ps, pt, r_ctx, Ret r_src, Ret r_tgt, (ths, im_src, im_tgt, st_src, st_tgt))); ss.
    }

    { destruct LSIM0 as [LSIM IND]. eapply IH in IND. des.
      exists o. eapply pind6_fold. eapply geno_tauL; eauto. split; ss.
    }
    { des. destruct LSIM0 as [LSIM IND]. eapply IH in IND. des.
      exists o. eapply pind6_fold. eapply geno_chooseL; eauto. eexists. split; ss. eauto.
    }
    { destruct LSIM0 as [LSIM IND]. eapply IH in IND. des.
      exists o. eapply pind6_fold. eapply geno_stateL; eauto. split; ss.
    }
    { destruct LSIM0 as [LSIM IND]. eapply IH in IND. des.
      exists o. eapply pind6_fold. eapply geno_tidL; auto. split; ss.
    }
    { exists one. eapply pind6_fold. eapply geno_UB; eauto. }
    { des. destruct LSIM as [LSIM IND]. eapply IH in IND. des.
      exists o. eapply pind6_fold. eapply geno_fairL; eauto. esplits; eauto. split; ss.
    }

    { destruct LSIM0 as [LSIM IND]. eapply IH in IND. des. exists o.
      eapply pind6_fold. eapply geno_tauR; eauto. ss.
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
      eapply pind6_fold. eapply geno_chooseR.
      i. specialize (LSIM0 x). destruct LSIM0 as [LSIM IND].
      specialize (JOIN (ps, true, r_ctx, src, (ktr_tgt x), (ths, im_src, im_tgt, st_src, st_tgt))).
      destruct JOIN; auto. des. split; ss.
      eapply geno_ord_weak; eauto.
    }

    { destruct LSIM0 as [LSIM IND]. eapply IH in IND. des. exists o.
      eapply pind6_fold. eapply geno_stateR; eauto. ss.
    }
    { destruct LSIM0 as [LSIM IND]. eapply IH in IND. des. exists o.
      eapply pind6_fold. eapply geno_tidR; eauto. ss.
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
      eapply pind6_fold. eapply geno_fairR.
      i. specialize (LSIM0 _ FAIR). destruct LSIM0 as [LSIM IND].
      specialize (JOIN (ps, true, r_ctx, src, (ktr_tgt ()), (ths, im_src, im_tgt1, st_src, st_tgt))).
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
      eapply pind6_fold. eapply geno_observe.
      i. specialize (LSIM0 ret). destruct LSIM0 as [LSIM IND].
      specialize (JOIN (true, true, r_ctx, ktr_src ret, ktr_tgt ret, (ths, im_src, im_tgt, st_src, st_tgt))).
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
      intro JOIN. des.
      set (fo1:= fun _: A R0 R1 => o1). exists (ord_tree_cons fo1).
      eapply pind6_fold. eapply geno_call.
    }

    { hexploit ord_tree_join.
      { instantiate (2:=A R0 R1).
        instantiate (2:= fun '(ps, pt, rs, src, tgt, shr) => @rr R0 R1 RR ps pt rs src tgt shr).
        i. ss. des_ifs. eapply IH in SAT.
        instantiate (1:= fun '(ps, pt, rs, src, tgt, shr) o =>
                           geno tid RR ps pt rs (o, src) tgt shr).
        eauto.
      }
      intro JOIN. des.
      set (fo1:= fun _: A R0 R1 => o1). exists (ord_tree_cons fo1).
      eapply pind6_fold. eapply geno_yieldR.
      1,2: eauto.
      { instantiate (1:=fo1 (ps, pt, r_ctx, (x <- trigger Yield;; ktr_src x), (x <- trigger Yield;; ktr_tgt x), (ths0, im_src0, im_tgt0, st_src0, st_tgt0))). ss.
      }
      i. specialize (LSIM0 _ _ _ _ _ _ _ INV0 VALID0 _ TGT). destruct LSIM0 as [LSIM IND].
      specialize (JOIN (ps, true, r_ctx1, (x <- trigger Yield;; ktr_src x), ktr_tgt (), (ths1, im_src1, im_tgt2, st_src1, st_tgt1))).
      destruct JOIN; auto. des. subst fo1. ss. split; ss. eapply geno_ord_weak; eauto.
    }

    { des. destruct LSIM as [LSIM IND]. eapply IH in IND. des. exists o.
      eapply pind6_fold. eapply geno_yieldL; eauto. esplits; eauto.
      split; ss. eauto.
    }

    { exists one. eapply pind6_fold. eapply geno_progress. pclearbot. auto. }

  Qed.

End GENORDER.
#[export] Hint Constructors _geno: core.
#[export] Hint Unfold geno: core.
#[export] Hint Resolve geno_mon: paco.

Section PROOF.

  Context `{M: ucmra}.

  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable _ident_src: ID.
  Let ident_src := @ident_src _ident_src.
  Variable _ident_tgt: ID.
  Let ident_tgt := @ident_tgt _ident_tgt.

  Variable wf_src: WF.
  Variable wf_tgt: WF.

  Let srcE := threadE _ident_src state_src.
  Let tgtE := threadE _ident_tgt state_tgt.

  Let shared :=
    (TIdSet.t *
       (@imap ident_src wf_src) *
       (@imap ident_tgt wf_tgt) *
       state_src *
       state_tgt)%type.

  Let shared_rel: Type := shared -> Prop.

  Variable I: shared -> (cmra_car M) -> Prop.

  Definition lift_wf (wf: WF): WF := sum_WF wf (option_WF wf).

  Definition mk_o (wf: WF) R (o: wf.(T)) (ps: bool) (itr_src: itree srcE R): (lift_wf wf).(T) :=
    if ps
    then match (observe itr_src) with
         | VisF (((|Yield)|)|)%sum _ => (inr (Some o))
         | _ => (inr None)
         end
    else match (observe itr_src) with
         | VisF (((|Yield)|)|)%sum _ => (inl o)
         | _ => (inr None)
         end.

  Let A R0 R1 := (bool * bool * (cmra_car M) * (itree srcE R0) * (itree tgtE R1) * shared)%type.
  Let wf_ot R0 R1 := @ord_tree_WF (A R0 R1).
  Let wf_stt R0 R1 := lift_wf (@wf_ot R0 R1).

  Lemma nosync_implies_stutter
        tid
        R0 R1 (LRR: R0 -> R1 -> (cmra_car M) -> shared_rel)
        ps pt r_ctx src tgt
        (shr: shared)
        (LSIM: ModSimNoSync.lsim I tid LRR ps pt r_ctx src tgt shr)
    :
    exists (o: (@wf_stt R0 R1).(T)),
      ModSimStutter.lsim (wf_stt) I tid LRR ps pt r_ctx (o, src) tgt shr.
  Proof.
    eapply nosync_geno in LSIM. des.
    exists (mk_o (@wf_ot R0 R1) o ps src).
    ginit. eapply cpn6_wcompat. eapply lsim_mon.
    revert_until LRR. gcofix CIH; i.
    remember (o, src) as osrc.
    move LSIM before CIH. revert_until LSIM.
    pattern ps, pt, r_ctx, osrc, tgt, shr.
    revert ps pt r_ctx osrc tgt shr LSIM. apply pind6_acc.
    intros rr DEC IH. clear DEC. intros ps pt r_ctx osrc tgt shr LSIM.
    intros src o Eosrc. clarify.
    eapply pind6_unfold in LSIM; eauto with paco.
    inv LSIM.

    { guclo (@lsim_indC_spec M). econs 1; eauto.
      instantiate (1:=(inl o1)). ss.
      unfold mk_o. des_ifs. all: econs 3.
    }

    { destruct GENO as [GENO IND]. eapply IH in IND; eauto.
      guclo (@lsim_indC_spec M). econs 2; eauto.
      guclo (@lsim_ord_weakC_spec M). econs; eauto.
      unfold mk_o. des_ifs; try reflexivity.
      - right. ss. do 2 econs.
      - right. ss. do 2 econs.
    }
    { des. destruct GENO as [GENO IND]. eapply IH in IND; eauto.
      guclo (@lsim_indC_spec M). econs 3; eauto. exists x.
      guclo (@lsim_ord_weakC_spec M). econs; eauto.
      unfold mk_o. des_ifs; try reflexivity.
      - right. ss. do 2 econs.
      - right. ss. do 2 econs.
    }
    { destruct GENO as [GENO IND]. eapply IH in IND; eauto.
      guclo (@lsim_indC_spec M). econs 4; eauto.
      guclo (@lsim_ord_weakC_spec M). econs; eauto.
      unfold mk_o. des_ifs; try reflexivity.
      - right. ss. do 2 econs.
      - right. ss. do 2 econs.
    }
    { destruct GENO as [GENO IND]. eapply IH in IND; eauto.
      guclo (@lsim_indC_spec M). econs 5; eauto.
      guclo (@lsim_ord_weakC_spec M). econs; eauto.
      unfold mk_o. des_ifs; try reflexivity.
      - right. ss. do 2 econs.
      - right. ss. do 2 econs.
    }
    { guclo (@lsim_indC_spec M). econs 6; eauto. }
    { des. destruct GENO0 as [GENO IND]. eapply IH in IND; eauto.
      guclo (@lsim_indC_spec M). econs 7; eauto. esplits; eauto.
      guclo (@lsim_ord_weakC_spec M). econs; eauto.
      unfold mk_o. des_ifs; try reflexivity.
      - right. ss. do 2 econs.
      - right. ss. do 2 econs.
    }

    { destruct GENO as [GENO IND]. eapply IH in IND; eauto.
      guclo (@lsim_indC_spec M). econs 8; eauto.
    }
    { guclo (@lsim_indC_spec M). econs 9; eauto. i. specialize (GENO x).
      destruct GENO as [GENO IND]. eapply IH in IND; eauto.
    }
    { destruct GENO as [GENO IND]. eapply IH in IND; eauto.
      guclo (@lsim_indC_spec M). econs 10; eauto.
    }
    { destruct GENO as [GENO IND]. eapply IH in IND; eauto.
      guclo (@lsim_indC_spec M). econs 11; eauto.
    }
    { guclo (@lsim_indC_spec M). econs 12; eauto. i. specialize (GENO _ FAIR).
      destruct GENO as [GENO IND]. eapply IH in IND; eauto.
    }

    { guclo (@lsim_indC_spec M). econs 13; eauto. i. specialize (GENO ret).
      destruct GENO as [GENO IND]. eapply IH in IND; eauto.
      guclo (@lsim_ord_weakC_spec M). econs; eauto.
      unfold mk_o. ss. des_ifs; try reflexivity.
      - right. ss. do 2 econs.
      - right. ss. do 2 econs.
    }

    { guclo (@lsim_indC_spec M). econs 14. }

    { guclo (@lsim_indC_spec M). econs 15; eauto.
      2:{ i. specialize (GENO _ _ _ _ _ _ _ INV0 VALID0 _ TGT). des.
          destruct GENO as [GENO IND]. eapply IH in IND; eauto.
          esplits.
          guclo (@lsim_resetC_spec M). econs; eauto.
      }
      unfold mk_o; ss. rewrite !bind_trigger. ss.
      des_ifs.
      - do 2 econs. auto.
      - econs. auto.
    }

    { des. destruct GENO0 as [GENO IND]. eapply IH in IND; eauto.
      guclo (@lsim_indC_spec M). econs 16; eauto.
    }

    { eapply nosync_geno in GENO. des.
      guclo (@lsim_ord_weakC_spec M). econs.
      instantiate (1:=mk_o (@wf_ot R0 R1) o0 false src).
      gfinal. right. pfold. eapply pind6_fold. econs 17. right. eapply CIH. auto.
      ss. des_ifs; try reflexivity. right. ss. do 2 econs.
    }

  Qed.

End PROOF.

Section MODSIM.

  Lemma nosync_implies_stutter_mod
        md_src md_tgt
        (MDSIM: ModSimNoSync.ModSim.mod_sim md_src md_tgt)
    :
    ModSimStutter.ModSim.mod_sim md_src md_tgt.
  Proof.
    inv MDSIM.
    set (_ident_src := Mod.ident md_src). set (_ident_tgt := Mod.ident md_tgt).
    set (state_src := Mod.state md_src). set (state_tgt := Mod.state md_tgt).
    set (srcE := threadE _ident_src state_src).
    set (tgtE := threadE _ident_tgt state_tgt).
    set (ident_src := @ident_src _ident_src).
    set (ident_tgt := @ident_tgt _ident_tgt).
    set (shared := (TIdSet.t * (@imap ident_src wf_src) * (@imap ident_tgt wf_tgt) * state_src * state_tgt)%type).
    set (wf_stt:=fun R0 R1 => lift_wf (@ord_tree_WF (bool * bool * (cmra_car world) * (itree srcE R0) * (itree tgtE R1) * shared)%type)).
    econs; eauto. instantiate (1:=wf_stt).
    i. specialize (init im_tgt). des. rename init0 into funs. exists I. esplits; eauto.
    i. specialize (funs fn args). des_ifs.
    unfold ModSimNoSync.local_sim in funs.
    ii. specialize (funs _ _ _ _ _ _ _ INV tid _ THS VALID _ UPD).
    des. esplits; eauto. instantiate (1:=inr None).
    i. specialize (funs1 _ _ _ _ _ _ _ INV1 VALID1 _ TGT).
    des. esplits; eauto. i. specialize (LSIM fs ft).
    eapply nosync_implies_stutter in LSIM. des.
    eapply stutter_ord_weak. 2: eapply LSIM.
    clear. destruct o.
    { right. econs. }
    destruct t.
    { right. do 2 econs. }
    { left. auto. }
  Qed.

End MODSIM.

Section USERSIM.

  Lemma nosync_implies_stutter_user
        md_src md_tgt p_src p_tgt
        (MDSIM: ModSimNoSync.UserSim.sim md_src md_tgt p_src p_tgt)
    :
    ModSimStutter.UserSim.sim md_src md_tgt p_src p_tgt.
  Proof.
    inv MDSIM.
    set (_ident_src := Mod.ident md_src). set (_ident_tgt := Mod.ident md_tgt).
    set (state_src := Mod.state md_src). set (state_tgt := Mod.state md_tgt).
    set (srcE := threadE _ident_src state_src).
    set (tgtE := threadE _ident_tgt state_tgt).
    set (ident_src := @ident_src _ident_src).
    set (ident_tgt := @ident_tgt _ident_tgt).
    set (shared := (TIdSet.t * (@imap ident_src wf_src) * (@imap ident_tgt wf_tgt) * state_src * state_tgt)%type).
    set (wf_stt:=fun R0 R1 => lift_wf (@ord_tree_WF (bool * bool * (cmra_car world) * (itree srcE R0) * (itree tgtE R1) * shared)%type)).
    econs; eauto. instantiate (2:=world). instantiate (1:=wf_stt).
    i. specialize (funs im_tgt). des. exists I. esplits; eauto.
    instantiate (1:=NatMap.map (fun _ => inr None) p_src).
    eapply nm_find_some_implies_forall4.
    { apply nm_forall2_wf_pair. eapply list_forall3_implies_forall2_2; eauto. clear. i. des. des_ifs. des; clarify. }
    { apply nm_forall2_wf_pair. eapply list_forall3_implies_forall2_3; eauto. clear. i. des. des_ifs. des; clarify. }
    { unfold nm_wf_pair. unfold key_set. rewrite nm_map_unit1_map_eq. ss. }
    i. eapply nm_forall3_implies_find_some in SIM; eauto.
    unfold ModSimNoSync.local_sim_init in SIM. unfold local_sim_init.
    i. specialize (SIM _ _ _ _ _ _ _ INV VALID _ FAIR). des. esplits; eauto.
    i. specialize (SIM0 fs ft). eapply nosync_implies_stutter in SIM0. des.
    rewrite NatMapP.F.map_o in FIND4. unfold option_map in FIND4. des_ifs.
    eapply stutter_ord_weak. 2: eapply SIM0.
    clear. destruct o.
    { right. econs. }
    destruct t.
    { right. do 2 econs. }
    { left. auto. }
  Qed.

End USERSIM.
