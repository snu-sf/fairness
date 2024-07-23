From sflib Require Import sflib.
From Paco Require Import paco.
From Coq Require Import Program.

From Fairness Require Export ITreeLib WFLibLarge FairBeh NatStructs Any Event.

Set Implicit Arguments.

Module TIdSet := NatSet.

Definition program := list (fname * Any.t)%type.

Definition Val := nat.

Section TID.

  Definition nat_wf: WF := mk_wf Wf_nat.lt_wf.

  Definition tid_dec := PeanoNat.Nat.eq_dec.

  Lemma reldec_correct_tid_dec: RelDec.RelDec_Correct (RelDec.RelDec_from_dec eq tid_dec).
  Proof. eapply RelDec.RelDec_Correct_eq_typ. Qed.

  Definition tid_dec_bool :=
    fun t1 t2 => if (tid_dec t1 t2) then true else false.


  Definition sum_tid (_id: ID) := id_sum thread_id _id.

  Definition tids_fmap (tid: thread_id) (tidf: TIdSet.t): @fmap thread_id :=
    fun t => if (PeanoNat.Nat.eq_dec t tid) then Flag.success
          else if (NatMapP.F.In_dec tidf t) then Flag.fail
               else Flag.emp.

  Definition tids_fmap_all (tidf: TIdSet.t): @fmap thread_id :=
    fun t => if (NatMapP.F.In_dec tidf t) then Flag.fail
             else Flag.emp.

  Lemma tids_fmap_rm_same_eq
        tid tset
    :
    tids_fmap tid tset = tids_fmap tid (NatMap.remove tid tset).
  Proof.
    extensionality t. unfold tids_fmap. des_ifs.
    - exfalso. apply n0; clear n0. rewrite NatMapP.F.remove_neq_in_iff; eauto.
    - exfalso. apply n0; clear n0. rewrite <- NatMapP.F.remove_neq_in_iff; eauto.
  Qed.

  Lemma tids_fmap_add_same_eq
        tid tset
    :
    tids_fmap tid tset = tids_fmap tid (NatMap.add tid () tset).
  Proof.
    extensionality t. unfold tids_fmap. des_ifs.
    - exfalso. apply n0; clear n0. rewrite NatMapP.F.add_neq_in_iff; eauto.
    - exfalso. apply n0; clear n0. rewrite <- NatMapP.F.add_neq_in_iff; eauto.
  Qed.

  Definition kernel_tid: thread_id := 0.

  Definition kernel_success_fmap: @fmap thread_id :=
    fun t => if (tid_dec t kernel_tid)
             then Flag.success else Flag.emp.

  Definition initial_threads := TIdSet.add kernel_tid NatSet.empty.
End TID.


Module Mod.
  Record t: Type :=
    mk {
        state: Type;
        ident: ID;
        st_init: state;
        funs: fname -> option (ktree (threadE ident state) Any.t Any.t);
      }.


  Program Definition wrap_fun {ident} {E} `{@eventE ident -< E} A R
          (f: ktree E A R):
    ktree E Any.t Any.t :=
    fun arg =>
      arg <- unwrap (arg↓);;
      ret <- f arg;; Ret ret↑
  .

  Fixpoint get_funs {ident} {E} `{@eventE ident -< E}
           (funs: list (fname * (ktree E Any.t Any.t)))
           (fn: fname):
    option (ktree E Any.t Any.t) :=
    match funs with
    | [] => None
    | (fn_hd, body_hd)::tl =>
        if string_dec fn fn_hd then Some body_hd else get_funs tl fn
    end.
End Mod.
