From sflib Require Import sflib.
From iris.algebra Require Import cmra updates gmap.

From iris.prelude Require Import options.

Set Implicit Arguments.

(* TODO: https://mattermost.mpi-sws.org/iris/pl/8cftahufytftmyt4mm5q7m6tyh *)
Module FiniteMap.
  Section FiniteMap.
    Context `{M: cmra}.

    Definition t : ucmra := (gmapUR nat M).

    Definition singleton (k : nat) (m : M) : t := {[ k := m ]}.

    (* TODO: upstream to iris *)
    Global Instance singleton_proper k :
      Proper ((≡)==>(≡)) (singleton k).
    Proof.
      intros x y EQ. unfold singleton.
      intros k'. destruct (decide (k' = k)) as [->|NE].
      - rewrite !lookup_singleton. f_equiv. done.
      - rewrite !lookup_singleton_ne; done.
    Qed.

    Lemma singleton_wf k m
      :
      ✓ (singleton k m) ↔ ✓ m.
    Proof. apply singleton_valid. Qed.

    Lemma singleton_add k m0 m1
      :
      (singleton k m0) ⋅ (singleton k m1)
      ≡
        singleton k (m0 ⋅ m1).
    Proof. by rewrite singleton_op /singleton. Qed.

    Lemma singleton_core k x cx
      :
      pcore x ≡ Some cx → core (singleton k x) ≡ singleton k cx.
    Proof. by apply singleton_core'. Qed.

    Lemma singleton_core_total k m `{CmraTotal M}
      :
      core (singleton k m) ≡ singleton k (core m).
    Proof. by rewrite singleton_core_total. Qed.

    Lemma singleton_updatable k m0 m1
          (UPD: m0 ~~> m1)
      :
      (singleton k m0) ~~> (singleton k m1).
    Proof. by apply singleton_update. Qed.

    Lemma singleton_extends k m0 m1
          (UPD: m0 ≼ m1)
      :
      (singleton k m0) ≼ (singleton k m1).
    Proof. apply singleton_included,Some_included. by right. Qed.

    Lemma singleton_updatable_set k m s
          (UPD: m ~~>: s)
      :
      (singleton k m) ~~>: (fun a => exists m1, s m1 ∧ a = singleton k m1).
    Proof.
      eapply cmra_updateP_weaken.
      { eapply singleton_updateP',UPD. }
      ii. simpl in *. des. eauto.
    Qed.

    Lemma singleton_alloc (m: M)
          (WF: ✓ m)
      :
      ε ~~>: (fun f => exists k, f ≡ singleton k m).
    Proof.
      eapply alloc_updateP.
      { exact WF. }
      intros k _. exists k. set_solver.
    Qed.
  End FiniteMap.
  Global Arguments t : clear implicits.
End FiniteMap.
