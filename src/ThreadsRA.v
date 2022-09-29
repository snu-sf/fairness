From sflib Require Import sflib.
Require Import Coq.Classes.RelationClasses.
From Fairness Require Import Axioms NatStructs.
From Fairness Require Import PCM World IProp IPM.
From Fairness Require Import Mod.
Require Import String Lia Program.

Set Implicit Arguments.

Section THREADS_RA_DEF.
  Definition ths_RA: URA.t. Admitted.

  Definition ths_RA_black (ths: TIdSet.t): ths_RA.(URA.car). Admitted.

  Definition ths_RA_white (ths: TIdSet.t): ths_RA.(URA.car). Admitted.

  Definition ths_RA_th (th: thread_id): ths_RA.(URA.car). Admitted.

  Context `{@GRA.inG ths_RA Σ}.

  Definition own_threads_black (ths: TIdSet.t): iProp := OwnM (ths_RA_black ths).

  Definition own_threads_white (ths: TIdSet.t): iProp := OwnM (ths_RA_white ths).

  Definition own_thread (th: thread_id): iProp := OwnM (ths_RA_th th).

  Lemma thread_disjoint th0 th1
    :
    (own_thread th0) -∗ (own_thread th1) -∗ ⌜th0 <> th1⌝.
  Admitted.

  Lemma threads_eq ths ths'
    :
    (own_threads_black ths) -∗ (own_threads_white ths') -∗ ⌜ths = ths'⌝.
  Admitted.

  Lemma threads_alloc tid ths0 ths1 ths'
        (THS: TIdSet.add_new tid ths0 ths1)
    :
    own_threads_black ths' -∗ own_threads_white ths0 -∗ #=> (own_threads_black ths1 **own_threads_white ths1 ** own_thread tid).
  Admitted.

  Lemma threads_dealloc tid ths0 ths'
    :
    own_threads_black ths' -∗ own_threads_white ths0 -∗ own_thread tid -∗ ∃ ths1, ⌜NatMap.remove tid ths0 = ths1⌝ ** #=> (own_threads_black ths1 ** own_threads_white ths1).
  Admitted.

  Lemma threads_in tid ths
    :
    own_threads_white ths -∗ own_thread tid -∗ ⌜TIdSet.In tid ths⌝.
  Admitted.
End THREADS_RA_DEF.
