From sflib Require Import sflib.
Require Import String.
From iris.algebra Require Import cmra updates.
From Fairness Require Import PCM.
Require Import Coq.Classes.RelationClasses.
Require Import Program.

Set Implicit Arguments.


Create HintDb iprop.
Definition aof_true: Type := True.
Global Opaque aof_true.

Ltac place_bar name :=
  first [ on_last_hyp ltac:(fun H => revert H; place_bar name; intros H) | assert(name: aof_true) by constructor].

Ltac all_once_fast TAC :=
  generalize (I: aof_true);
  let name := fresh "bar" in
  place_bar name; revert_until name;
  repeat
    match goal with
    | [ |- aof_true -> _ ] => fail 1
    | _ => intro; on_last_hyp TAC
    end;
  intro; on_last_hyp ltac:(fun H => clear H);
  clear name.

Ltac uipropall :=
  repeat (autounfold with iprop; autorewrite with iprop;
       all_once_fast ltac:(fun H => autounfold with iprop in H; autorewrite with iprop in H); ss).

Section IPROP.
  Context {Σ: GRA.t}.

  Local Notation iPred := (Σ -> Prop).

  Record iProp' :=
    iProp_intro {
        iProp_pred :> iPred;
        iProp_mono: forall r0 r1 (WF: ✓ r1) (LE: r0 ≼ r1),
          iProp_pred r0 -> iProp_pred r1;
      }.

  Program Definition Sepconj (P Q: iProp'): iProp' :=
    Seal.sealing
      "iProp"
      (iProp_intro (fun r => exists a b, r ≡ a ⋅ b /\ P a /\ Q b) _).
  Next Obligation.
    red in LE. ss. des; subst.
    exists H, (H0 ⋅ z). rewrite (assoc op). splits; auto.
    { rewrite LE H1. done. }
    eapply iProp_mono; [| |exact H3].
    { eapply cmra_valid_op_r. rewrite (assoc op). rewrite LE H1 in WF. apply WF. }
    { exists z. auto. }
  Qed.

  Program Definition Pure (P: Prop): iProp' :=
    Seal.sealing
      "iProp"
      (iProp_intro (fun _ => P) _).

  Program Definition Ex {X: Type} (P: X -> iProp'): iProp' :=
    Seal.sealing
      "iProp"
      (iProp_intro (fun r => exists x, P x r) _).
  Next Obligation.
    esplits. eapply iProp_mono; eauto.
  Qed.

  Program Definition Univ {X: Type} (P: X -> iProp'): iProp' :=
    Seal.sealing
      "iProp"
      (iProp_intro (fun r => forall x, P x r) _).
  Next Obligation.
    eapply iProp_mono; eauto.
  Qed.

  Program Definition Own (r0: Σ): iProp' :=
    Seal.sealing
      "iProp"
      (iProp_intro (fun r1 => r0 ≼ r1) _).
  Next Obligation.
    etransitivity; eauto.
  Qed.

  Program Definition And (P Q: iProp'): iProp' :=
    Seal.sealing
      "iProp"
      (iProp_intro (fun r => P r /\ Q r) _).
  Next Obligation.
    splits; auto; eapply iProp_mono; eauto.
  Qed.

  Program Definition Or (P Q: iProp'): iProp' :=
    Seal.sealing
      "iProp"
      (iProp_intro (fun r => P r \/ Q r) _).
  Next Obligation.
    des.
    { left. eapply iProp_mono; eauto. }
    { right. eapply iProp_mono; eauto. }
  Qed.

  Program Definition Impl (P Q: iProp'): iProp' :=
    Seal.sealing
      "iProp"
      (iProp_intro (fun r0 => forall r1 (WF: ✓ r1) (LE: r0 ≼ r1),
                        ✓ r1 -> P r1 -> Q r1) _).
  Next Obligation.
    eapply H; eauto. etransitivity; eauto.
  Qed.

  Program Definition Wand (P Q: iProp'): iProp' :=
    Seal.sealing
      "iProp"
      (iProp_intro (fun r => forall rp, ✓ (r ⋅ rp) -> P rp -> Q (r ⋅ rp)) _).
  Next Obligation.
    eapply iProp_mono; [..|eapply H]; eauto.
    { eapply cmra_mono_r; auto. }
    { eapply cmra_valid_included; eauto. eapply cmra_mono_r; auto. }
  Qed.

  Program Definition Emp: iProp' :=
    Seal.sealing
      "iProp"
      (iProp_intro (fun _ => True) _).

  Program Definition Persistently (P: iProp'): iProp' :=
    Seal.sealing
      "iProp"
      (iProp_intro (fun r0 => P (core r0)) _).
  Next Obligation.
    eapply iProp_mono; [| |exact H].
    { by apply cmra_core_valid. }
    { eapply cmra_core_mono; eauto. }
  Qed.

  Program Definition Plainly (P: iProp'): iProp' :=
    Seal.sealing
      "iProp"
      (iProp_intro (fun r => P ε) _).

  Program Definition Later (P: iProp'): iProp' :=
    Seal.sealing
      "iProp"
      (iProp_intro P (iProp_mono P)).

  Program Definition Upd (P: iProp'): iProp' :=
    Seal.sealing
      "iProp"
      (iProp_intro (fun r0 => forall ctx, ✓ (r0 ⋅ ctx) -> exists r1, ✓ (r1 ⋅ ctx) /\ P r1) _).
  Next Obligation.
    red in LE. des. rewrite LE in H0. hexploit (H (z ⋅ ctx)).
    { rewrite (assoc op). auto. }
    i. des. esplits; [..|eauto]. eapply cmra_valid_op_l.
    rewrite (assoc op) in H1.
    rewrite -(assoc op) (comm op ctx) (assoc op). done.
  Qed.

  Definition Entails (P Q : iProp') : Prop :=
    Seal.sealing
      "iProp"
      (forall r (WF: ✓ r), P r -> Q r).

  Hint Rewrite (Seal.sealing_eq "iProp"): iprop.
  #[local] Hint Unfold Sepconj Pure Ex Univ Own And Or Impl Wand Emp Persistently Later Upd Entails: iprop.

  (* BI axioms *)
  Global Program Instance PreOrder_Entails: PreOrder Entails.
  Next Obligation.
  Proof.
    ii. uipropall.
  Qed.
  Next Obligation.
  Proof.
    ii. uipropall. ii. exploit (H r); eauto.
  Qed.

  Lemma Pure_intro: forall (φ : Prop) (P : iProp'), φ -> Entails P (Pure φ).
  Proof.
    ii. uipropall.
  Qed.

  Lemma Pure_elim: forall (φ : Prop) (P : iProp'), (φ -> Entails (Pure True) P) -> Entails (Pure φ) P.
  Proof.
    ii. uipropall. ii. eapply H in H0; eauto.
  Qed.

  Lemma And_elim_l: forall P Q : iProp', Entails (And P Q) P.
  Proof.
    ii. uipropall. ii. eapply H.
  Qed.

  Lemma And_elim_r: forall P Q : iProp', Entails (And P Q) Q.
  Proof.
    ii. uipropall. ii. eapply H.
  Qed.

  Lemma And_intro: forall P Q R : iProp', Entails P Q -> Entails P R -> Entails P (And Q R).
  Proof.
    ii. uipropall. ii. split; [eapply H|eapply H0]; eauto.
  Qed.

  Lemma Or_intro_l: forall P Q : iProp', Entails P (Or P Q).
  Proof.
    ii. uipropall. ii. left. ss.
  Qed.

  Lemma Or_intro_r: forall P Q : iProp', Entails Q (Or P Q).
  Proof.
    ii. uipropall. ii. right. ss.
  Qed.

  Lemma Or_elim: forall P Q R : iProp', Entails P R -> Entails Q R -> Entails (Or P Q) R.
  Proof.
    ii. uipropall. ii. inv H1.
    { eapply H; ss. }
    { eapply H0; ss. }
  Qed.

  Lemma Impl_intro_r: forall P Q R : iProp', Entails (And P Q) R -> Entails P (Impl Q R).
  Proof.
    ii. uipropall. ii. eapply H; eauto. splits; auto. eapply iProp_mono; eauto.
  Qed.

  Lemma Impl_elim_l: forall P Q R : iProp', Entails P (Impl Q R) -> Entails (And P Q) R.
  Proof.
    ii. uipropall. ii. inv H0. eapply H; eauto.
  Qed.

  Lemma Univ_intro: forall (A : Type) (P : iProp') (Ψ : A -> iProp'), (forall a : A, Entails P (Ψ a)) -> Entails P (Univ (fun a : A => Ψ a)).
  Proof.
    ii. uipropall. ii. specialize (H x). uipropall. eapply H; eauto.
  Qed.

  Lemma Univ_elim: forall (A : Type) (Ψ : A -> iProp') (a : A), Entails (Univ (fun a0 : A => Ψ a0)) (Ψ a).
  Proof.
    ii. uipropall.
  Qed.

  Lemma Ex_intro: forall (A : Type) (Ψ : A -> iProp') (a : A), Entails (Ψ a) (Ex (fun a0 : A => Ψ a0)).
  Proof.
    ii. uipropall. ii. eexists. eauto.
  Qed.

  Lemma Ex_elim: forall (A : Type) (Φ : A -> iProp') (Q : iProp'), (forall a : A, Entails (Φ a) Q) -> Entails (Ex (fun a : A => Φ a)) Q.
  Proof.
    ii. uipropall. ii. des. specialize (H x). uipropall. eauto.
  Qed.

  Lemma Sepconj_mono: forall P P' Q Q' : iProp', Entails P Q -> Entails P' Q' -> Entails (Sepconj P P') (Sepconj Q Q').
  Proof.
    ii. uipropall. ii. unfold Sepconj in *. des; subst. esplits; eauto.
    { eapply H; eauto. rewrite H1 in WF. eapply cmra_valid_op_l; eauto. }
    { eapply H0; eauto. rewrite H1 in WF. eapply cmra_valid_op_r; eauto. }
  Qed.

  Lemma Emp_Sepconj_l: forall P : iProp', Entails P (Sepconj Emp P).
  Proof.
    ii. uipropall. ii. exists ε, r. splits; ss. rewrite left_id. eauto.
  Qed.

  Lemma Emp_Sepconj_r: forall P : iProp', Entails (Sepconj Emp P) P.
  Proof.
    ii. uipropall. ii. inv H. des; subst. eapply iProp_mono; [| |exact H2]; eauto.
    exists x. rewrite (comm op). done.
  Qed.

  Lemma Sepconj_comm: forall P Q : iProp', Entails (Sepconj P Q) (Sepconj Q P).
  Proof.
    ii. uipropall. ii. unfold Sepconj in *. des. subst. exists b, a. splits; eauto. rewrite (comm op). done.
  Qed.

  Lemma Sepconj_assoc: forall P Q R : iProp', Entails (Sepconj (Sepconj P Q) R) (Sepconj P (Sepconj Q R)).
  Proof.
    ii. uipropall. ii. unfold Sepconj in *. des; subst. esplits; [|apply H2| |apply H3|apply H1]; ss.
    rewrite (assoc op) H H0. ss.
  Qed.

  Lemma Wand_intro_r: forall P Q R : iProp', Entails (Sepconj P Q) R -> Entails P (Wand Q R).
  Proof.
    ii. uipropall. ii. eapply H; eauto.
  Qed.

  Lemma Wand_elim_l: forall P Q R : iProp', Entails P (Wand Q R) -> Entails (Sepconj P Q) R.
  Proof.
    ii. uipropall. ii. unfold Sepconj in *. des.
    assert (R (a ⋅ b)) as HR.
    { rewrite H0 in WF. apply H; auto. eapply cmra_valid_op_l; eauto. }
    eapply iProp_mono; [done| |exact HR].
    exists ε. rewrite right_id. ss.
  Qed.

  Lemma Persistently_mono: forall P Q : iProp', Entails P Q -> Entails (Persistently P) (Persistently Q).
  Proof.
    ii. uipropall. ii. eapply H; eauto. by apply cmra_core_valid.
  Qed.

  Lemma Persistently_idem: forall P : iProp', Entails (Persistently P) (Persistently (Persistently P)).
  Proof.
    ii. uipropall. ii. eapply iProp_mono; [| |exact H].
    - by repeat apply cmra_core_valid.
    - exists ε. rewrite right_id cmra_core_idemp. done.
  Qed.

  Lemma Persistently_emp: Entails Emp (Persistently Emp).
  Proof.
    uipropall.
  Qed.

  Lemma Persistently_univ: forall (A : Type) (Ψ : A -> iProp'), Entails (Univ (fun a => Persistently (Ψ a))) (Persistently (Univ (fun a => Ψ a))).
  Proof.
    ii. uipropall. ii. specialize (H x). uipropall.
  Qed.

  Lemma Persistently_ex: forall (A : Type) (Ψ : A -> iProp'), Entails (Persistently (Ex (fun a => Ψ a))) (Ex (fun a => Persistently (Ψ a))).
  Proof.
    ii. uipropall. ii. des. exists x. uipropall.
  Qed.

  Lemma Persistently_and: forall (P Q : iProp'), Entails (And (Persistently P) (Persistently Q)) (Persistently (And P Q)).
  Proof.
    ii. uipropall.
  Qed.

  Lemma Persistently_sep: forall P Q : iProp', Entails (Sepconj (Persistently P) Q) (Persistently P).
  Proof.
    ii. uipropall. ii. des. subst.
    eapply iProp_mono; [..|eauto].
    { eapply cmra_core_valid; eauto. }
    { eapply cmra_core_mono; eauto. exists b. auto. }
  Qed.

  Lemma Persistently_sep_and: forall P Q : iProp', Entails (And (Persistently P) Q) (Sepconj P Q).
  Proof.
    ii. uipropall. ii. des. esplits; eauto. rewrite cmra_core_l. auto.
  Qed.

  Lemma Upd_intro: forall P : iProp', Entails P (Upd P).
  Proof.
    ii. uipropall. ii. exists r. splits; auto.
  Qed.

  Lemma Upd_mono: forall P Q : iProp', Entails P Q -> Entails (Upd P) (Upd Q).
  Proof.
    ii. uipropall. ii. exploit H0; eauto. i. des.
    exploit (H r1); eauto. eapply cmra_valid_op_l; eauto.
  Qed.

  Lemma Upd_trans: forall P : iProp', Entails (Upd (Upd P)) (Upd P).
  Proof.
    ii. uipropall. ii. exploit H; eauto. i. des. hexploit x0; eauto.
  Qed.

  Lemma Upd_frame_r: forall P R : iProp', Entails (Sepconj (Upd P) R) (Upd (Sepconj P R)).
  Proof.
    ii. uipropall. ii. unfold Sepconj in *. des. subst. exploit (H1 (b ⋅ ctx)); eauto.
    { rewrite (assoc op). rewrite H in H0. eauto. }
    i. des. esplits; [..|eapply x1|eapply H2]; ss.
    rewrite -(assoc op). eauto.
  Qed.

End IPROP.
Hint Rewrite (Seal.sealing_eq "iProp"): iprop.
#[export] Hint Unfold Sepconj Pure Ex Univ Own And Or Impl Wand Emp Persistently Later Upd Entails: iprop.
