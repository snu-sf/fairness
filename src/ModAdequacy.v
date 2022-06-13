From sflib Require Import sflib.
From ITree Require Export ITree.
From Paco Require Import paco.

Require Export Coq.Strings.String.
Require Import Program.

From ExtLib Require Import FMapAList.

Export ITreeNotations.

From Fairness Require Import pind8.
From Fairness Require Export ITreeLib FairBeh FairSim.
From Fairness Require Export Mod ModSimPico Concurrency.

Set Implicit Arguments.



Section AUX.

  Definition alist_proj1 {K} {V} (a: alist K V): list K :=
    List.map fst a.


  Variable E1: Type -> Type.
  Variable E2: Type -> Type.

  Variable _ident_src: ID.
  Variable _ident_tgt: ID.

  Definition wf_ths {R}
             (ths_src: @threads _ident_src E1 R)
             (ths_tgt: @threads _ident_tgt E2 R) :=
    (alist_proj1 ths_src) = (alist_proj1 ths_tgt).

  Lemma ths_find_none_tid_add
        R (ths: @threads _ident_src E1 R) tid
        (NONE: threads_find tid ths = None)
    :
    tid_list_add (alist_proj1 ths) tid (tid :: (alist_proj1 ths)).
  Proof.
    revert_until ths. induction ths; i; ss.
    { econs; ss. }
    des_ifs. ss. destruct (tid_dec tid n) eqn:TID.
    { clarify. eapply RelDec.neg_rel_dec_correct in Heq. ss. }
    eapply IHths in NONE. inv NONE. econs; ss.
    eapply List.not_in_cons. split; auto.
  Qed.

End AUX.



Section ADEQ.

  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable _ident_src: ID.
  Definition ident_src := sum_tids _ident_src.
  Variable _ident_tgt: ID.
  Definition ident_tgt := sum_tids _ident_tgt.

  Variable wf_src: WF.
  Variable wf_tgt: WF.

  Let srcE := ((@eventE ident_src +' cE) +' sE state_src).
  Let tgtE := ((@eventE ident_tgt +' cE) +' sE state_tgt).

  Variable world: Type.
  Variable world_le: world -> world -> Prop.

  Variable I: (@shared state_src state_tgt _ident_src _ident_tgt wf_src wf_tgt world) -> Prop.

  (*invariant for tid_list & threads: tid_list_add threads.proj1 tid tid_list*)
  Theorem local_adequacy
          R
          (LSIM: forall (src0: itree srcE R) (tgt0: itree tgtE R),
              local_sim world_le I src0 tgt0)
          (ths_src: @threads _ident_src (sE state_src) R)
          (ths_tgt: @threads _ident_tgt (sE state_tgt) R)
          tid src tgt (st_src: state_src) (st_tgt: state_tgt)
          (WFTHS: wf_ths ths_src ths_tgt)
          (THSRC: threads_find tid ths_src = None)
          (THTGT: threads_find tid ths_tgt = None)
          (INV: forall im_tgt, exists im_src o w,
              I (alist_proj1 ths_src, im_src, im_tgt, st_src, st_tgt, o, w))
    :
    gsim wf_src wf_tgt (@eq R) false false
         (interp_all st_src ths_src tid src)
         (interp_all st_tgt ths_tgt tid tgt).
  Proof.
    ii. specialize (INV mt). des. rename im_src into ms. exists ms.
    pose proof (ths_find_none_tid_add ths_src tid THSRC) as TADD. 
    unfold local_sim in LSIM. specialize (LSIM src tgt _ _ _ _ _ _ _ INV tid _ TADD).


  Abort.

End ADEQ.
