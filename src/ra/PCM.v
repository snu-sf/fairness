From sflib Require Import sflib.
Require Export ZArith.
(* Require Export Znumtheory. *)
Require Import String.
Require Import ClassicalChoice ChoiceFacts.
Require Import Coq.Classes.RelationClasses.
Require Import Lia.
Require Import Program.
From stdpp Require coPset gmap.
From Fairness Require Import Axioms.
From Fairness Require Import ucmra_list.
From iris.algebra Require Import cmra updates functions.

From iris.prelude Require Import prelude options.

Set Implicit Arguments.




Require Export String.
Module Type SEAL.
  Parameter sealing: string -> forall X: Type, X -> X.
  Parameter sealing_eq: forall key X (x: X), sealing key x = x.
End SEAL.
Module Seal: SEAL.
  Definition sealing (_: string) X (x: X) := x.
  Lemma sealing_eq key X (x: X): sealing key x = x.
  Proof. reflexivity. Qed.
End Seal.

Ltac seal_with key x :=
  replace x with (Seal.sealing key x); [|eapply Seal.sealing_eq].
Ltac seal x :=
  let key := fresh "key" in
  assert (key:= "_deafult_");
  seal_with key x.
Ltac unseal x :=
  match (type of x) with
  | string => repeat rewrite (@Seal.sealing_eq x) in *; try clear x
  | _ => repeat rewrite (@Seal.sealing_eq _ _ x) in *;
         repeat match goal with
                | [ H: string |- _ ] => try clear H
                end
  end
.


Definition cast A B (LeibEq: A = B) (a: A): B := eq_rect A _ a _ LeibEq.


Module RA.
  (* Class t: Type := mk {
    car:> Type;
    add: car -> car -> car;
    wf: car -> Prop;
    add_comm: forall a b, add a b = add b a;
    add_assoc: forall a b c, add a (add b c) = add (add a b) c;
    wf_mon: forall a b, wf (add a b) -> wf a;
    pcore : car -> option car;
    pcore_id: forall a cx, pcore a = Some cx -> add cx a = a;
    pcore_idem: forall a cx, pcore a = Some cx -> pcore cx = Some cx;
    pcore_mono: forall a b cx,
      pcore a = Some cx -> (exists cy, pcore (add a b) = Some cy /\ (exists c, cy = add cx c));

    extends := fun a b => exists ctx, add a ctx = b;
    updatable := fun a b => (wf a -> wf b) /\ forall ctx, wf (add a ctx) -> wf (add b ctx);
    updatable_set := fun a B =>
                     (forall (WF : wf a),
                         exists b, <<IN: B b>> /\ <<WF: wf b>>) /\
                     forall ctx (WF: wf (add a ctx)),
                         exists b, <<IN: B b>> /\ <<WF: wf (add b ctx)>>;
  }
  . *)

  Lemma extends_updatable
        `{M: cmra}
        (a b : M)
        (EXT: a ≼ b)
    :
      << UPD: b ~~> a >>
  .
  Proof. rewrite /NW. destruct EXT as [c ->]. apply cmra_update_op_l. Qed.

  Lemma updatable_add
        `{M: cmra}
        (a0 a1 : M)
        (b0 b1 : M)
        (UPD0: a0 ~~> a1)
        (UPD1: b0 ~~> b1)
    :
      <<UPD: (a0 ⋅ b0) ~~> (a1 ⋅ b1)>>
  .
  Proof. by apply cmra_update_op. Qed.

  Lemma extends_add
        `{M: cmra}
        (a b delta : M)
        (EXT: a ≼ b)
    :
      <<EXT: (a ⋅ delta) ≼ (b ⋅ delta)>>
  .
  Proof. by apply cmra_mono_r. Qed.

  (* Program Instance extends_Transitive `{M: t}: Transitive extends.
  Next Obligation.
    rr. ii. rr in H. rr in H0. des. rewrite <- H0. rewrite <- H. esplits; eauto. rewrite add_assoc. eauto.
  Qed. *)

  (* Program Instance updatable_PreOrder `{M: t}: PreOrder updatable.
  Next Obligation. ii. ss. Qed.
  Next Obligation. ii. r in H. r in H0. des. split; eauto. Qed. *)

  (* Definition prod (M0 M1 : t) : t := (prodR (fosraR M0) (fosraR M1)).

  Theorem prod_updatable
          M0 M1
          (a0: @car M0) (a1: @car M1)
          (b0: @car M0) (b1: @car M1)
          (UPD0: updatable a0 b0)
          (UPD1: updatable a1 b1)
    :
      <<UPD: @updatable (prod M0 M1) (a0, a1) (b0, b1)>>
  .
  Proof.
    r in UPD0. r in UPD1. des. split.
    { intros [? ?]. split; simpl in *.
      - by apply UPD0.
      - by apply UPD1.
    }
    ii. ss. destruct ctx as [ctx0 ctx1], H as [H0 H1]. simpl in *.
    specialize (UPD3 ctx0 H0). specialize (UPD2 ctx1 H1).
    split; done.
  Qed. *)

  (* Program Instance frac (denom: positive): t := {
    car := positive;
    add := fun a b => (a + b)%positive;
    wf := fun a => (a <= denom)%positive;
  }
  .
  Next Obligation. ss. lia. Qed.
  Next Obligation. ss. lia. Qed.
  Next Obligation. ss. lia. Qed. *)

  (* Theorem frac_updatable
          denom M
          a b
    :
      <<UPD: @updatable (prod (frac denom) M) (denom, a) b>>
  .
  Proof.
    ii. ss. des_ifs. des. lia.
  Qed. *)

  (* Program Instance agree (A: Type): t := {
    car := option A;
    add := fun a0 a1 => if excluded_middle_informative (a0 = a1) then a0 else None;
    wf := fun a => a <> None;
  }
  .
  Next Obligation. i. ss. des_ifs. Qed.
  Next Obligation. i. ss. des_ifs. Qed.
  Next Obligation. i. ss. des_ifs. Qed.

  Theorem agree_unupdatable
          A
          a0 a1
    :
      <<UPD: @updatable (agree A) (Some a0) a1 -> a1 = Some a0>>
  .
  Proof.
    ii. ss. rr in H. specialize (H (Some a0)). ss. des_ifs.
    exfalso. eapply H; eauto.
  Qed. *)

  (* Program Instance excl (A: Type): cmra := excl A. *)

  (* Theorem excl_updatable
          A
          a0 a1
    :
      <<UPD: @updatable (excl A) (Some a0) (Some a1)>>
  .
  Proof. rr. ii. ss. Qed. *)

  (* Let sum_add {M0 M1} := (fun (a b: car M0 + car M1 + unit) =>
                            match a, b with
                            | inl (inl a0), inl (inl b0) => inl (inl (add a0 b0))
                            | inl (inr a1), inl (inr b1) => inl (inr (add a1 b1))
                            | _, _ => inr tt
                            end).
  Let sum_wf {M0 M1} := (fun (a: car M0 + car M1 + unit) =>
                           match a with
                           | inl (inl a0) => wf a0
                           | inl (inr a1) => wf a1
                           | _ => False
                           end).
  Program Instance sum (M0 M1: t): t := {
    car := car M0 + car M1 + unit (* boom *);
    add := sum_add;
    wf := sum_wf;
  }
  .
  Next Obligation. unfold sum_add. esplits; ii; ss; des; des_ifs; do 2 f_equal; apply add_comm. Qed.
  Next Obligation. unfold sum_add. esplits; ii; ss; des; des_ifs; do 2 f_equal; apply add_assoc. Qed.
  Next Obligation. i. unfold sum_wf in *. des_ifs; ss; des_ifs; eapply wf_mon; eauto. Qed. *)

  (* Program Instance pointwise K (M: t): t := {
    car := K -> car;
    add := fun f0 f1 => (fun k => add (f0 k) (f1 k));
    wf := fun f => forall k, wf (f k);
  }
  .
  Next Obligation. i. apply func_ext. ii. rewrite add_comm. ss. Qed.
  Next Obligation. i. apply func_ext. ii. rewrite add_assoc. ss. Qed.
  Next Obligation. ss. i. eapply wf_mon; ss. Qed. *)

  (* Local Program Instance empty: t := {
    car := False;
    add := fun a _ => a;
    wf := fun _ => False;
    pcore := fun _ => None;
  }.
  Next Obligation. ss. Qed.
  Next Obligation. ss. Qed.
  Next Obligation. ss. Qed.
  Next Obligation. ss. Qed.
  Next Obligation. ss. Qed.
  Next Obligation. ss. Qed. *)
End RA.






Local Obligation Tactic := i; unseal "ra"; ss; des_ifs.

(*** PCM == Unital RA ***)
(*** When URA, not RA? (1) Auth algebra (2) global RA construction ***)
(* Module URA.
  (* Class t: Type := mk {
    car:> Type;
    unit: car;
    _add: car -> car -> car;
    _wf: car -> Prop;
    _add_comm: forall a b, _add a b = _add b a;
    _add_assoc: forall a b c, _add a (_add b c) = _add (_add a b) c;
    add: car -> car -> car := Seal.sealing "ra" _add;
    wf: car -> Prop := Seal.sealing "ra" _wf;
    unit_id: forall a, add a unit = a;
    wf_unit: wf unit;
    wf_mon: forall a b, wf (add a b) -> wf a;
    core: car -> car;
    core_id: forall a, add (core a) a = a;
    core_idem: forall a, core (core a) = core a;
    core_mono: forall a b, exists c, core (add a b) = add (core a) c;

    (* extends := fun a b => exists ctx, add a ctx = b; *)
    (* updatable := fun a b => forall ctx, wf (add a ctx) -> wf (add b ctx); *)
    extends := fun a b => exists ctx, add a ctx = b;
    updatable := fun a b => forall ctx, wf (add a ctx) -> wf (add b ctx);
    updatable_set := fun a B => forall ctx (WF: wf (add a ctx)),
                         exists b, <<IN: B b>> /\ <<WF: wf (add b ctx)>>;
  }
  . *)

  Lemma add_comm `{M: cmra} (a b : M) : a ⋅ b ≡ b ⋅ a.
  Proof. by rewrite (comm _). Qed.
  Lemma add_assoc `{M: cmra} (a b c : M) : a ⋅ (b ⋅ c) ≡ (a ⋅ b) ⋅ c.
  Proof. by rewrite (assoc _). Qed.

  Lemma wf_split `{M: cmra} (a b : M) : ✓ (a ⋅ b) → <<WF: ✓ a ∧ ✓ b>>.
  Proof.
    i. split.
    - by eapply cmra_valid_op_l.
    - by eapply cmra_valid_op_r.
  Qed.

  Lemma extends_updatable
        `{M: cmra}
        (a b : M)
        (EXT: a ≼ b)
    :
      <<UPD: b ~~> a>>
  .
  Proof. by apply RA.extends_updatable. Qed.

  Lemma unit_id_ `{M: ucmra} (b : M) (EQ: b ≡ ε) (a : M) : a ⋅ b ≡ a.
  Proof. by rewrite EQ right_id. Qed.

  Lemma unit_idl `{M: ucmra} (a : M) : ε ⋅ a ≡ a.
  Proof. by rewrite left_id. Qed.

  Lemma wf_core `{M: ucmra} (a : M) (WF: ✓ a) : ✓ (core a).
  Proof. by apply cmra_core_valid. Qed.

  Lemma unit_core `{M: ucmra}: core (ε : M) ≡ ε.
  Proof. apply core_id_core. apply _. Qed.

  (*** TODO: remove redundancy with "updatable_horizontal" above ***)
  Lemma updatable_add
        `{M: cmra}
        (a0 a1 : M)
        (b0 b1 : M)
        (UPD0: a0 ~~> a1)
        (UPD1: b0 ~~> b1)
    :
      <<UPD: (a0 ⋅ b0) ~~> (a1 ⋅ b1)>>
  .
  Proof. by apply cmra_update_op. Qed.

  Lemma updatable_unit
        `{M: t}
        a
    :
      <<UPD: updatable a unit>>
  .
  Proof.
    ii. rewrite unit_idl. rewrite add_comm in H. eapply wf_mon; eauto.
  Qed.

  Lemma extends_add
        `{M: t}
        a b delta
        (EXT: extends a b)
    :
      <<EXT: extends (add a delta) (add b delta)>>
  .
  Proof.
    rr in EXT. rr. des. exists ctx. subst. rewrite <- add_assoc. rewrite (add_comm a).
    symmetry. rewrite <- add_assoc. rewrite add_comm. f_equal. rewrite add_comm. ss.
  Qed.

  Lemma wf_extends
        `{M: t}
        a b
        (EXT: extends a b)
        (WF: wf b)
    :
    wf a.
  Proof.
    rr in EXT. des. subst. eapply wf_split in WF. des; auto.
  Qed.

  Lemma extends_core
        `{M: t}
        a b
        (EXT: extends a b)
    :
    extends (core a) (core b).
  Proof.
    rr in EXT. des. subst. hexploit core_mono. i. des.
    eexists. eauto.
  Qed.

  (* Iris ucmra is a URA. *)
  (* TODO:(janggun) Move this to a separate module, if needed *)
  (* Program Instance ucmra_ura (M: ucmra) : t := {
    car := ucmra_car M;
    unit := ε;
    _add := op;
    _wf := valid;
    core := cmra.core;
  }.
  Next Obligation. by rewrite (base.comm op). Qed.
  Next Obligation. by rewrite (base.assoc op). Qed.
  Next Obligation. by apply ucmra_unit_right_id. Qed.
  Next Obligation. by apply ucmra_unit_valid. Qed.
  Next Obligation. by apply (cmra_valid_op_l _ b). Qed.
  Next Obligation. by apply cmra_core_l. Qed.
  Next Obligation. by apply cmra_core_idemp. Qed.
  Next Obligation. by apply cmra_core_mono. Qed. *)

  (* URA is an Iris ucmra. *)
  (* Section fos_ura_to_ucmra.
    Context (M : t).
    Local Instance fos_ura_valid_instance : Valid car := wf.
    Local Instance fos_ura_pcore_instance : PCore car := fun a => Some (core a).
    Local Instance fos_ura_op_instance : Op car := add.
    Local Instance fos_ura_unit_instance : Unit car := unit.

    Lemma fos_ura_valid a : valid a <-> wf a.
    Proof. done. Qed.
    Lemma fos_ura_op a0 a1 : op a0 a1 = add a0 a1.
    Proof. done. Qed.

    Definition fos_ura_ra_mixin : RAMixin car.
    Proof.
      split; try apply _; try done.
      - ii. subst. eauto.
      - ii. apply add_assoc.
      - ii. apply add_comm.
      - intros ???Heq. unfold pcore,fos_ura_pcore_instance in Heq. injection Heq as <-. apply core_id.
      - intros ???Heq. unfold pcore,fos_ura_pcore_instance in *. injection Heq as <-. f_equal. apply core_idem.
      - intros a ? ? [c ->] Heq. unfold pcore,fos_ura_pcore_instance in *. injection Heq as <-. eexists.
        split; [done|]. destruct (core_mono a c) as [cx ?].
        exists cx. done.
      - ii. eapply wf_mon. eauto.
    Qed.
    Canonical Structure fosuraR := discreteR car fos_ura_ra_mixin.

    Lemma fos_ura_ucmra_mixin : UcmraMixin car.
    Proof.
      split.
      - apply wf_unit.
      - ii. rewrite (base.comm op). apply unit_id.
      - unfold pcore,fos_ura_pcore_instance. f_equal. apply unit_core.
    Qed.
    Canonical Structure fosuraUR := Ucmra car fos_ura_ucmra_mixin.

  End fos_ura_to_ucmra. *)

  Program Instance prod (M0 M1: t): t := {
    car := car M0 * car M1;
    unit := (unit, unit);
    _add := fun '(a0, a1) '(b0, b1) => ((add a0 b0), (add a1 b1));
    _wf := fun '(a0, a1) => wf a0 /\ wf a1;
    core := fun '(a0, a1) => (core a0, core a1);
  }
  .
  Next Obligation. f_equal; rewrite add_comm; ss. Qed.
  Next Obligation. f_equal; rewrite add_assoc; ss. Qed.
  Next Obligation. f_equal; rewrite unit_id; ss. Qed.
  Next Obligation. split; eapply wf_unit. Qed.
  Next Obligation. des. split; eapply wf_mon; eauto. Qed.
  Next Obligation. f_equal; rewrite core_id; eauto. Qed.
  Next Obligation. f_equal; rewrite core_idem; eauto. Qed.
  Next Obligation.
    hexploit (core_mono c3 c1). intros [c_aux0 EQ0].
    hexploit (core_mono c4 c2). intros [c_aux1 EQ1].
    exists (c_aux0, c_aux1). rewrite EQ0. rewrite EQ1. auto.
  Qed.

  Theorem prod_updatable
          M0 M1
          (a0: @car M0) (a1: @car M1)
          (b0: @car M0) (b1: @car M1)
          (UPD0: updatable a0 b0)
          (UPD1: updatable a1 b1)
    :
      <<UPD: @updatable (prod M0 M1) (a0, a1) (b0, b1)>>
  .
  Proof.
    ii. unfold wf, add in *. unseal "ra".
    ss. des_ifs. des. esplits; eauto.
  Qed.

  Lemma prod_extends (A B: t)
        (a0 a1: @car A) (b0 b1: @car B)
    :
    @extends (prod A B) (a0, b0) (a1, b1) <-> extends a0 a1 /\ URA.extends b0 b1.
  Proof.
    split.
    { i. r in H. des. unfold add in H. unseal "ra". destruct ctx. ss. clarify.  split.
      { exists c; auto. }
      { exists c0; auto. }
    }
    { i. des. r in H. r in H0. des. subst.
      exists (ctx0, ctx). unfold add. unseal "ra". ss. unfold add. unseal "ra". f_equal.
    }
  Qed.

  Lemma prod_updatable_set (A B: t)
        (a0: @car A) (PA: @car A -> Prop)
        (b0: @car B) (PB: @car B -> Prop)
        (UPD0: URA.updatable_set a0 PA)
        (UPD1: URA.updatable_set b0 PB)
    :
    @updatable_set (prod A B) (a0, b0) (fun '(a1, b1) => PA a1 /\ PB b1).
  Proof.
    ii. destruct ctx.
    unfold wf, add in WF. unseal "ra". ss. des.
    exploit UPD0; eauto. i. des.
    exploit UPD1; eauto. i. des.
    exists (b, b1). ss. splits; ss.
    unfold wf. unseal "ra". ss. des_ifs.
    unfold add in Heq. unseal "ra". ss. clarify.
  Qed.

  Program Definition to_RA (M: t): RA.t := {|
    RA.car := car;
    RA.add := add;
    RA.wf := wf;
    RA.pcore := fun a => Some (core a);
  |}
  .
  Next Obligation. apply add_comm. Qed.
  Next Obligation. apply add_assoc. Qed.
  Next Obligation. eapply wf_mon; eauto. Qed.
  Next Obligation. apply core_id. Qed.
  Next Obligation. by rewrite core_idem. Qed.
  Next Obligation. eexists. split; [done|]. apply core_mono. Qed.

  Global Program Instance extends_PreOrder `{M: t}: PreOrder extends.
  Next Obligation. rr. eexists unit. ss. rewrite unit_id. ss. Qed.
  Next Obligation.
    rr. ii. rr in H. rr in H0. des. rewrite <- H0. rewrite <- H. esplits; eauto. rewrite add_assoc. eauto.
  Qed.

  Program Instance updatable_PreOrder `{M: t}: PreOrder updatable.
  Next Obligation. ii. ss. Qed.
  Next Obligation. ii. r in H. r in H0. eauto. Qed.

  Lemma unfold_add `{M: t}: add = _add. Proof. unfold add. unseal "ra". reflexivity. Qed.
  (* Hint Resolve unfold_add. *)
  Lemma unfold_wf `{M: t}: wf = _wf. Proof. unfold wf. unseal "ra". reflexivity. Qed.
  (* Hint Resolve unfold_wf. *)
  Lemma unfold_wf2 `{M: t}: forall x, wf x <-> _wf x. Proof. unfold wf. unseal "ra". reflexivity. Qed.
  (* Hint Resolve unfold_wf2. *)
  Opaque add wf.









  Program Instance pointwise K (M: t): t := {
    car := K -> car;
    unit := fun _ => unit;
    _add := fun f0 f1 => (fun k => add (f0 k) (f1 k));
    _wf := fun f => forall k, wf (f k);
    core := fun f => (fun k => core (f k));
  }
  .
  Next Obligation. apply func_ext. ii. rewrite add_comm. ss. Qed.
  Next Obligation. apply func_ext. ii. rewrite add_assoc. ss. Qed.
  Next Obligation. apply func_ext. ii. rewrite unit_id. ss. Qed.
  Next Obligation. i. eapply wf_unit; ss. Qed.
  Next Obligation. i. eapply wf_mon; ss. Qed.
  Next Obligation. apply func_ext. ii. rewrite core_id. ss. Qed.
  Next Obligation. apply func_ext. ii. rewrite core_idem. ss. Qed.
  Next Obligation.
    hexploit (choice (fun k c => core (add (a k) (b k)) = add (core (a k)) c)).
    { i. eapply core_mono. }
    intros [f EQ]. exists f. apply func_ext. i. apply EQ.
  Qed.
  *)

  Definition pointwise K (M: ucmra) : ucmra := discrete_funUR (λ k : K, M).

  Definition pointwise_dep K (M: K -> ucmra) : ucmra := discrete_funUR M.

  (* {
    car := forall (k: K), car M k;
    unit := fun _ => unit;
    _add := fun f0 f1 => (fun k => add (f0 k) (f1 k));
    _wf := fun f => forall k, wf (f k);
    core := fun f => (fun k => core (f k));
  }
  .
  Next Obligation. apply func_ext_dep. ii. rewrite add_comm. ss. Qed.
  Next Obligation. apply func_ext_dep. ii. rewrite add_assoc. ss. Qed.
  Next Obligation. apply func_ext_dep. ii. rewrite unit_id. ss. Qed.
  Next Obligation. i. eapply wf_unit; ss. Qed.
  Next Obligation. i. eapply wf_mon; ss. Qed.
  Next Obligation. apply func_ext_dep. ii. rewrite core_id. ss. Qed.
  Next Obligation. apply func_ext_dep. ii. rewrite core_idem. ss. Qed.
  Next Obligation.
    hexploit (non_dep_dep_functional_choice
                choice _
                (fun k c => core (add (a k) (b k)) = add (core (a k)) c)).
    { i. eapply core_mono. }
    intros [f EQ]. exists f. apply func_ext_dep. i. apply EQ.
  Qed. *)

  (*
  Let sum_add {M0 M1} := (fun (a b: car M0 + car M1 + bool) =>
                            match a, b with
                            | inl (inl a0), inl (inl b0) => inl (inl (add a0 b0))
                            | inl (inr a1), inl (inr b1) => inl (inr (add a1 b1))
                            | _, inr false => a
                            | inr false, _ => b
                            | _, _ => inr true
                            end).
  Let sum_wf {M0 M1} := (fun (a: car M0 + car M1 + bool) =>
                           match a with
                           | inl (inl a0) => wf a0
                           | inl (inr a1) => wf a1
                           | inr false => True
                           | inr true => False
                           end).
  Let sum_core {M0 M1} := (fun (a: car M0 + car M1 + bool) =>
                             match a with
                             | inl (inl a0) => inl (inl (core a0))
                             | inl (inr a1) => inl (inr (core a1))
                             | inr false => inr false
                             | inr true => inr true
                             end).

  Program Instance sum (M0 M1: t): t := {
    car := car M0 + car M1 + bool;
    unit := inr false;
    _add := sum_add;
    _wf := sum_wf;
    core := sum_core;
  }
  .
  Next Obligation. unfold sum_add. esplits; ii; ss; des; des_ifs; do 2 f_equal; apply add_comm. Qed.
  Next Obligation. unfold sum_add. esplits; ii; ss; des; des_ifs; do 2 f_equal; apply add_assoc. Qed.
  Next Obligation. unfold sum_add. des_ifs. Qed.
  Next Obligation. unfold sum_wf in *. des_ifs; ss; des_ifs; eapply wf_mon; eauto. Qed.
  Next Obligation. unfold sum_add, sum_core. des_ifs; ss; do 2 f_equal; eapply core_id. Qed.
  Next Obligation. unfold sum_core. des_ifs; ss; do 2 f_equal; eapply core_idem. Qed.
  Next Obligation.
    pose (c := match a, b with
               | inr false, _ => sum_core b
               | _, inr false => inr false
               | inr true, _ => inr true
               | _, inr true => inr true
               | inl (inl _), inl (inr _) => inr true
               | inl (inr _), inl (inl _) => inr true
               | _, _ => inr false
               end: @car M0 + @car M1 + bool).
    destruct a as [[]|[]] eqn:EQA, b as [[]|[]] eqn:EQB; ss;
      try by (exists c; ss).
    { hexploit (@core_mono M0). i. des.
      eexists (inl (inl _)). do 2 f_equal. eauto.
    }
    { hexploit (@core_mono M1). i. des.
      eexists (inl (inr _)). do 2 f_equal. eauto.
    }
  Qed.

  Definition agree_add (A: Type) (a0 a1: option (option A)): option (option A) :=
    match a0, a1 with
    | None, _ => a1
    | _, None => a0
    | _, _ => if excluded_middle_informative (a0 = a1) then a0 else (Some None)
    end.

  Program Instance agree (A: Type): t := {
    car := option (option A);
    unit := None;
    _add := @agree_add A;
    _wf := fun a => a <> Some None;
    core := fun a => a;
  }
  .
  Next Obligation. unfold agree_add. des_ifs. Qed.
  Next Obligation. unfold agree_add. des_ifs. Qed.
  Next Obligation. unfold agree_add. des_ifs. Qed.
  Next Obligation. unfold agree_add in *. des_ifs. Qed.
  Next Obligation. unfold agree_add. des_ifs. Qed.
  Next Obligation. exists b. auto. Qed.
End URA. *)

(* Coercion URA.to_RA: ucmra >-> RA.t. *)
(* Coercion RA.car: RA.t >-> Sortclass.
Coercion cmra_car: ucmra >-> Sortclass. *)

(* Tactic Notation "ur" := try rewrite ! URA.unfold_wf; try rewrite ! URA.unfold_add; cbn.
Tactic Notation "ur" "in" hyp(H)  := try rewrite ! URA.unfold_wf in H; try rewrite ! URA.unfold_add in H; cbn in H.

Notation "'ε'" := URA.unit.
Infix "⋅" := URA.add (at level 50, left associativity).
Notation "(⋅)" := URA.add (only parsing). *)

(* Module of_IrisRA.

Local Open Scope iris_algebra_scope.

(* Iris cmra is a RA. *)
Section IrisCMRAtoRA.
Context (M : cmra).

Inductive car (X: Type) : Type :=
| just (x: X): car X
.

Let wf `{M : cmra}: car M -> Prop := fun a =>
    match a with
    | just a => ✓ a
    end.
Let add `{M : cmra}: car M -> car M -> car M := fun a b =>
    match a,b with
    | just a, just b => just (a ⋅ b)%ia
    end.
Let pcore `{M : cmra}: car M -> option car := fun a =>
    match a with
    | just a => match cmra.pcore a with
                | Some cx => Some (just cx)
                | None => None
                end
    end.
Program Instance t : RA.t := {
  car := car M;
  add := add;
  wf := wf;
  pcore := pcore;
}.
Next Obligation. destruct a,b. unfold add. f_equal. by rewrite (base.comm op). Qed.
Next Obligation. destruct a,b,c. unfold add. f_equal. by rewrite (base.assoc op). Qed.
Next Obligation. destruct a,b. unfold wf,add in *. eapply cmra_valid_op_l. apply H. Qed.
Next Obligation.
  unfold pcore,add in *. ii. des_ifs. f_equal.
  by apply cmra_pcore_l.
Qed.
Next Obligation.
  ii. unfold pcore in *. des_ifs.
  all: apply cmra_pcore_idemp in Heq0; clarify.
Qed.
Next Obligation.
  ii. unfold pcore,add in *. des_ifs.
  all: apply (cmra_pcore_mono x1 (x1 ⋅ x2)%ia) in Heq; [|eexists; done]; des.
  all: rewrite Heq in Heq0.
  - eexists. split; [done|]. injection Heq0 as ->.
    destruct Heq1. exists (just x). clarify.
  - clarify.
Qed.
End IrisCMRAtoRA.

(* RA is an Iris cmra. *)
Section RAtoIrisCMRA.
  Context (M : RA.t).

  Local Instance fos_ra_valid_instance : Valid RA.car := RA.wf.
  Local Instance fos_ra_pcore_instance : PCore RA.car := RA.pcore.
  Local Instance fos_ra_op_instance : Op RA.car := RA.add.


  Lemma fos_ra_valid a : ✓ a <-> RA.wf a.
  Proof. done. Qed.
  Lemma fos_ra_op a0 a1 : (a0 ⋅ a1)%ia = RA.add a0 a1.
  Proof. done. Qed.

  Definition fos_ra_mixin : RAMixin RA.car.
  Proof.
    split; try apply _; try done.
    - intros ??? -> Hy. exists cx. eauto.
    - ii. apply RA.add_assoc.
    - ii. apply RA.add_comm.
    - ii. apply RA.pcore_id. done.
    - ii. eapply RA.pcore_idem. eauto.
    - intros ???[??]. subst. apply RA.pcore_mono.
    - ii. eapply RA.wf_mon. eauto.
  Qed.
  Canonical Structure fos_RAO := discreteR RA.car fos_ra_mixin.
End RAtoIrisCMRA. *)


(* Definition to_ra `{M: cmra} (a: M) : t M := just a.

Lemma to_ra_add `{M: cmra} (a b: M) :
  RA.add (to_ra a) (to_ra b) = to_ra (a ⋅ b)%ia.
Proof. ss. Qed.

Lemma to_ra_wf `{M: cmra} (a: M) :
  RA.wf (to_ra a) <-> ✓ a.
Proof. ss. Qed.

Lemma to_ra_pcore `{M: cmra} (a: M) :
  RA.pcore (to_ra a) = match (cmra.pcore a) with | Some x => Some (to_ra x) | None => None end.
Proof. des_ifs. Qed.

Lemma to_ra_extends `{M : cmra} (a b : M) :
  @RA.extends (t M) (to_ra a) (to_ra b) <-> a ≼ b.
Proof.
  unfold to_ra. split; intros EXT.
  all: rr; rr in EXT; des.
  - destruct ctx. exists x. unfold RA.add in EXT. simpl in *. injection EXT as ->. done.
  - exists (just z). subst. done.
Qed.


Lemma to_ra_updatable `{M: cmra} (a b : M) :
  @RA.updatable (t M) (to_ra a) (to_ra b) <-> a ~~> b.
Proof.
  rewrite cmra_discrete_total_update. split; intros UPD.
  - intros mz V. rr in UPD. des. simpl in *. destruct mz as [mz|].
    + specialize (UPD0 (to_ra mz)). simpl in *. apply UPD0,V.
    + apply UPD,V.
  - rr. split.
    + intros V. unfold to_ra,RA.wf,to_ra in *. simpl in *.
      apply (UPD None V).
    + intros [ctx] V. rr. simpl in *. apply (UPD (Some ctx) V).
Qed.

Lemma to_ra_updatable_set `{M: cmra} (a : M) P :
  @RA.updatable_set (t M) (to_ra a) (fun a => match a with | just a => P a end) <-> a ~~>: P.
Proof.
  rewrite cmra_discrete_total_updateP. split; intros UPD.
  - rr in UPD. des. intros [mz|] V.
    + specialize (UPD0 (to_ra mz) V). destruct UPD0 as [[b] [??]]. exists b. split; ss.
    + specialize (UPD V). destruct UPD as [[b] [??]]. exists b. split; ss.
  - rr. rr in UPD. unfold to_ra in *. simpl in *. split.
    + intros V. specialize (UPD None V). simpl in *. des.
      exists (just y). split; ss.
    + intros [ctx] V. specialize (UPD (Some ctx) V). simpl in *. des.
      exists (just y). split; ss.
  Qed.
End of_IrisRA. *)

(* Module of_RA.
Section of_RA.

Inductive car {X: Type}: Type :=
| just (x: X): car
| unit: car
.

Let wf `{M: RA.t}: car -> Prop := fun a => match a with
                                           | just a => RA.wf a
                                           | _ => True
                                           end.
Let add `{M: RA.t}: car -> car -> car :=
  fun a b =>
    match a, b with
    | just a, just b => just (RA.add a b)
    | unit, _ => b
    | _, unit => a
    end.
Let core `{M: RA.t}: car -> car :=
  fun a =>
    match a with
    | just a =>
      match (RA.pcore a) with
      | Some x => just x
      | _ => unit
      end
    | _ => a
    end.

Program Instance t (RA: RA.t): ucmra := {
  car := car;
  unit := of_RA.unit;
  _wf := wf;
  _add := add;
  core := core;
}.
Next Obligation. unfold add. des_ifs. { rewrite RA.add_comm; ss. } Qed.
Next Obligation. unfold add. des_ifs. { rewrite RA.add_assoc; ss. } Qed.
Next Obligation. unfold add. des_ifs. Qed.
Next Obligation. unfold add in *. des_ifs. eapply RA.wf_mon; eauto. Qed.
Next Obligation. unfold add,core in *. des_ifs. f_equal. by apply RA.pcore_id. Qed.
Next Obligation.
  unfold core. des_ifs.
  - f_equal. apply RA.pcore_idem in Heq1. rewrite Heq1 in Heq0. injection Heq0. done.
  - apply RA.pcore_idem in Heq1. clarify. Qed.
Next Obligation.
  unfold core,add. des_ifs; try by (eexists; ss).
  - apply (RA.pcore_mono x1 x2) in Heq2.
    des. exists (just c0). subst. clarify.
  - exists unit. done.
  - apply (RA.pcore_mono x1 x2) in Heq2. des. clarify.
Qed.

Definition to_ura `{M: RA.t} (a: M) : t M := just a.

Lemma to_ura_add (RA : RA.t)
  (a b : RA.car (t := RA))
  :
  URA.add (to_ura a) (to_ura b) = to_ura (RA.add a b).
Proof. rewrite URA.unfold_add. ss. Qed.

Lemma to_ura_wf (RA : RA.t)
  (a : RA.car (t := RA))
  :
  (✓ (to_ura a)) <-> (RA.wf a).
Proof. rewrite URA.unfold_wf. ss. Qed.

Lemma to_ura_core (RA : RA.t) (a : RA.car (t := RA)) :
  URA.core (to_ura a) = match (RA.pcore a) with | Some x => to_ura x | None => unit end.
Proof. ss. Qed.

Theorem to_ura_updatable (RA : RA.t)
  (a a': RA.car (t := RA))
  :
  URA.updatable (to_ura a) (to_ura a') <-> RA.updatable a a'
.
Proof.
  unfold to_ura. split.
  - intros UPD_URA. unfold RA.updatable. unfold URA.updatable,✓,URA.add in *. unseal "ra". ss. split.
    + ii. specialize (UPD_URA unit). ss. apply UPD_URA; eauto.
    + ii. specialize (UPD_URA (just ctx)). ss. apply UPD_URA; eauto.
  - intros UPD_RA. ii. des. unfold ✓, URA.add in *. unseal "ra".
    ss. unfold wf in *. des_ifs.
    + by apply UPD_RA.
    + rr in UPD_RA. des. by apply UPD_RA.
Qed.

Theorem to_ura_updatable_set (RA : RA.t)
  (a : RA.car (t := RA)) B
  (RA_UPD: RA.updatable_set a B)
  :
  URA.updatable_set (to_ura a) (fun x => match x with | just x => B x | unit => True end).
Proof.
  unfold to_ura. ii. rr in RA_UPD. des. rr in WF. unseal "ra". ss. rr in WF. unseal "ra". ss. destruct ctx as [ctx|].
  - specialize (RA_UPD0 ctx WF). des. exists (just b). split; ss.
    rr. unseal "ra". ss. rr. unseal "ra". ss.
  - specialize (RA_UPD WF). des. exists unit. split; ss.
    rr. unseal "ra". ss. rr. unseal "ra". ss.
Qed.

Lemma to_ura_extends (RA : RA.t)
  (a b: RA.car (t := RA))
  (EXT_RA : RA.extends a b)
  :
  << EXT_URA : URA.extends (to_ura a) (to_ura b) >>.
Proof.
  rr. rr in EXT_RA. des. exists (just ctx).
  rewrite URA.unfold_add. ss. subst. done.
Qed.

End of_RA.
End of_RA.

(* Coercion to_RA: t >-> RA.t. *)
Coercion of_RA.t: RA.t >-> ucmra. *)





Section discrete_fun.

  Lemma included_discrete_fun
      A (Ms : A -> ucmra)
      (f0 f1 : discrete_fun Ms)
      (EXT : ∀ a, (f0 a) ≼ (f1 a))
    :
    f0 ≼ f1.
  Proof.
    set (R := fun (a : A) => (fun (ctx : Ms a) => f1 a ≡ (f0 a) ⋅ ctx)).
    hexploit (dependent_functional_choice _ R).
    { subst R. i. specialize (EXT x). r in EXT. des. eauto. }
    subst R. intros H. des. exists f. intros ?. apply H.
  Qed.

  Lemma cmra_updateP_discrete_fun
      A (Ms : A → ucmra)
      (f : discrete_fun Ms)
      (P : ∀ (a : A), (Ms a) → Prop)
      (UPD: ∀ a, (f a) ~~>: (P a))
    :
    f ~~>: (λ f', forall a, P a (f' a)).
  Proof.
    intros n mz WF; simpl in *.
    set RES := λ a, (match mz with | Some mz => (Some (mz a)) | None => None end).
    set (R := λ (a : A), (λ (m : Ms a), P a m ∧ ✓{n} (m ⋅? (RES a)))).
    hexploit (dependent_functional_choice _ R).
    { subst R. ss. i. eapply (UPD x n (RES x)). subst RES. simpl.
      des_ifs; simpl in *; apply WF.
    }
    subst R RES. ss. i. des. exists f0. splits; auto.
    { i. specialize (H a). des. auto. }
    { intros k. specialize (H k). des. des_ifs; auto. }
  Qed.

  (* Note: this can be proven without axioms. Not sure about the other ones. *)
  Lemma cmra_update_discrete_fun
      A (Ms : A → ucmra)
      (f0 f1 : discrete_fun Ms)
      (UPD: ∀ a, (f0 a) ~~> (f1 a))
    :
    f0 ~~> f1.
  Proof.
    eapply cmra_update_updateP, cmra_updateP_weaken.
    - setoid_rewrite cmra_update_updateP in UPD.
      apply cmra_updateP_discrete_fun,UPD.
    - intros y EQ. simpl in *. by apply func_ext_dep.
  Qed.

End discrete_fun.

(* Module Excl.
Section EXCL.
Context {X: Type}.
Variant car: Type :=
  | just (x: X)
  | unit
  | boom
.

Global Instance excl_equiv : Equiv car := (=).

Lemma equiv_unfold :
  (≡@{car}) = (=@{car}).
Proof. done. Qed.

Global Instance excl_equiv_equivalence : Equivalence (≡@{car}).
Proof. apply _. Qed.

Global Instance proper_just : Proper ((=) ==> (≡)) just.
Proof. solve_proper. Qed.

Definition add := fun x y => match x, y with | _, unit => x | unit, _ => y | _, _ => boom end.
Definition wf := fun a => a ≠ boom.
Definition core  := fun _ : car => Some unit.

Local Instance excl_valid_instance : Valid car := wf.
Local Instance excl_pcore_instance : PCore car := core.
Local Instance excl_op_instance : Op car := add.
Local Instance excl_unit_instance : Unit car := unit.

Canonical Structure ExclO := discreteO car.

Lemma valid_unfold : valid = wf.
Proof. done. Qed.
Lemma op_unfold : (⋅) = add.
Proof. done. Qed.
Lemma pcore_unfold : pcore = core.
Proof. done. Qed.
Lemma unit_unfold : ε = unit.
Proof. done. Qed.

Local Definition excl_unfold :=
  (equiv_unfold, valid_unfold, op_unfold, pcore_unfold, unit_unfold).
Local Ltac excl_unfold_all :=
  rewrite !excl_unfold /=.

Definition mixin : RAMixin car.
Proof.
  split; try apply _; try done.
  all: excl_unfold_all.
  - naive_solver.
  - intros [][][]; done.
  - intros [][]; done.
  - intros [][]; done.
  - intros [][]; done.
  - intros [][][]; eauto; try naive_solver.
    all: intros [[] ?]; try done.
    all: unfold core.
    all: intros _; esplits; try naive_solver.
    all: exists unit; done.
  - intros [][] WF; eauto; simpl in *; try naive_solver; done.
Qed.
Canonical Structure ExclR := discreteR car mixin.

Global Instance discrete : CmraDiscrete ExclR.
Proof. apply discrete_cmra_discrete. Qed.

Lemma ucmra_mixin : UcmraMixin car.
Proof.
  split; try apply _; try done.
  excl_unfold_all.
  intros []; done.
Qed.
Canonical Structure t := Ucmra car ucmra_mixin.

Theorem updatable
        a0 a1
        (WF: ✓ a1)
  :
    <<UPD: (just a0) ~~> a1>>
.
Proof.
  rewrite /NW cmra_discrete_total_update.
  revert WF. excl_unfold_all.
  ii. des_ifs. destruct a1; done.
Qed.

Theorem extends
        a0 a1
        (WF: ✓ a1)
        (EXT: (just a0) ≼ a1)
  :
    <<EQ: a1 = just a0>>
.
Proof.
  revert EXT. unfold included. excl_unfold_all.
  intros [? EQ]. des_ifs.
Qed.

Theorem wf_unit
        a0 a1
        (WF: ✓ ((just a0) ⋅ a1))
  :
    <<EQ: a1 = unit>>
.
Proof. revert WF. excl_unfold_all. ii. des_ifs. Qed.

Definition to_excl (x: X) : t := just x.

End EXCL.
End Excl.

Arguments Excl.t: clear implicits. *)

From iris.algebra Require Import local_updates.
(* Note: not used anymore *)
Module Auth.
Section AUTH.
Context `{M : ucmra, DISC : CmraDiscrete M}.

Inductive car : Type :=
| frag (f: M)
| excl (e: M) (f: M)
| boom
.

Definition add a0 a1 :=
  match a0, a1 with
  | frag f0, frag f1 => frag (f0 ⋅ f1)
  | frag f0, excl e1 f1 => excl e1 (f0 ⋅ f1)
  | excl e0 f0, frag f1 => excl e0 (f0 ⋅ f1)
  | _, _ => boom
  end.

Definition wf a :=
  match a with
  | frag f => ✓ f
  | excl e f => f ≼ e ∧ ✓ e
  | boom => False
  end.

Definition core a :=
  match a with
  | frag f => Some (frag (core f))
  | excl _ f => Some (frag (core f))
  | boom => Some boom
  end.

Definition unit := frag ε.

Definition equiv (a b : car) :=
  match a, b with
  | frag f0, frag f1 => f0 ≡ f1
  | excl e0 f0, excl e1 f1 => e0 ≡ e1 ∧ f0 ≡ f1
  | boom, boom => True
  | _, _ => False
  end.

Global Instance auth_equiv : Equiv car := equiv.

Lemma equiv_unfold :
  (≡) = equiv.
Proof. done. Qed.

Global Instance auth_equiv_equivalence : Equivalence (≡@{car}).
Proof.
  rewrite equiv_unfold /equiv. split.
  - intros ?. des_ifs.
  - intros ?? EQ. des_ifs. des. done.
  - intros ??? EQ1 EQ2. des_ifs; des.
    + by rewrite EQ1 EQ2.
    + by rewrite EQ1 EQ2 EQ3.
Qed.

Global Instance proper_frag : Proper ((≡) ==> (≡)) frag.
Proof. intros x y EQ. done. Qed.

Global Instance proper_excl : Proper ((≡) ==> (≡) ==> (≡)) excl.
Proof. intros x1 x2 EQ1 y1 y2 EQ2. by subst. Qed.

Local Instance auth_valid_instance : Valid car := wf.
Local Instance auth_pcore_instance : PCore car := core.
Local Instance auth_op_instance : Op car := add.
Local Instance auth_unit_instance : Unit car := unit.

Canonical Structure AuthO := discreteO car.

Lemma valid_unfold : valid = wf.
Proof. done. Qed.
Lemma op_unfold : (⋅) = add.
Proof. done. Qed.
Lemma pcore_unfold : pcore = core.
Proof. done. Qed.
Lemma unit_unfold : ε = unit.
Proof. done. Qed.

Definition mixin : RAMixin car.
Proof.
  split; try apply _; try done.
  all: try rewrite equiv_unfold /equiv.
  - intros ??? EQ.
    rewrite op_unfold /add. des_ifs; des.
    all: by rewrite EQ ?EQ0.
  - intros ???. rewrite pcore_unfold /core. intros EQ1 EQ2.
    all: des_ifs; des.
    + esplits; eauto. des_ifs. rewrite EQ1. done.
    + esplits; eauto. des_ifs. rewrite EQ0. done.
    + esplits; eauto.
  - intros ???. rewrite !valid_unfold /wf. des_ifs; des.
    all: by rewrite H ?H0.
  - intros ???. rewrite !op_unfold /add. des_ifs; des.
    all: by rewrite (assoc cmra.op).
  - intros ??. rewrite !op_unfold /add. des_ifs; des.
    all: by rewrite (comm cmra.op).
  - intros ??. rewrite pcore_unfold /core => EQ.
    rewrite !op_unfold /add. des_ifs; des.
    all: by rewrite cmra_core_l.
  - intros ??. rewrite pcore_unfold /core => EQ. des_ifs; des.
    all: by rewrite cmra_core_idemp.
  - intros ???. unfold included.
    rewrite equiv_unfold /equiv op_unfold /add => EQ.
    rewrite pcore_unfold /core => EQ1. repeat des_ifs; des.
    all: eexists.
    all: split; auto.
    all: try (by exists boom).
    all: destruct z; des_ifs; des.
    + hexploit (cmra_core_mono f1 f); [eexists; eauto|].
      intros [? EQ1]; eexists (frag _). done.
    + hexploit (cmra_core_mono f1 f); [eexists; eauto|].
      intros [? EQ1]; eexists (frag _). done.
    + hexploit (cmra_core_mono f1 f); [eexists; eauto|].
      intros [? EQ1]; eexists (frag _). done.
  - intros x y. rewrite !valid_unfold /wf op_unfold /add => WF. des_ifs; des.
    + by apply cmra_valid_op_l in WF.
    + des. destruct WF as [? ->] in WF0.
      do 2 eapply cmra_valid_op_l. done.
    + des. destruct WF as [? ->] in WF0. split; auto.
      eexists (_ ⋅ _). rewrite (assoc cmra.op). done.
Qed.
Canonical Structure AuthR := discreteR car mixin.

Global Instance discrete : CmraDiscrete AuthR.
Proof. apply discrete_cmra_discrete. Qed.

Lemma ucmra_mixin : UcmraMixin car.
Proof.
  split; try apply _; try done.
  + rewrite valid_unfold /wf unit_unfold /unit.
    apply ucmra_unit_valid.
  + rewrite op_unfold /add equiv_unfold /equiv unit_unfold /unit.
    intros []; try rewrite left_id; done.
  + rewrite pcore_unfold /core unit_unfold /unit.
    rewrite core_id_core. done.
Qed.
Canonical Structure t := Ucmra car ucmra_mixin.

Definition black (a: M): t := excl a ε.
Definition white (a: M): t := frag a.

Theorem auth_update
        (a b a' b' : M)
        (UPD: (a,b) ~l~> (a',b'))
  :
    <<UPD: black a ⋅ white b ~~> black a' ⋅ white b'>>
.
Proof using DISC.
  apply cmra_discrete_total_update.
  rewrite /black /white valid_unfold /wf op_unfold /add.
  intros []; auto.
  rewrite local_update_unital_discrete in UPD.
  intros [[z' LE] WF]. rewrite left_id /included.
  rewrite left_id -(assoc cmra.op) in LE.
  specialize (UPD (f ⋅ z') WF LE).
  rewrite (assoc cmra.op) in UPD. des; split; eauto.
Qed.

Theorem auth_dup_black
        (a ca : M)
        (CORE: a ≡ a ⋅ ca)
  :
    <<DUP: black a ~~> black a ⋅ white ca >>
.
Proof.
  rewrite /NW cmra_discrete_total_update.
  rewrite /black /white valid_unfold /wf op_unfold /add.
  intros []; auto.
  rewrite left_id. intros [[z LE] WF].
  rewrite left_id /included. split; auto.
  eexists. rewrite -(assoc cmra.op). erewrite <- LE.
  rewrite (comm cmra.op). done.
Qed.

Theorem auth_dup_white
        (a ca : M)
        (CORE: a ≡ a ⋅ ca)
  :
    <<DUP: white a ~~> white a ⋅ white ca >>
.
Proof.
  rewrite /NW cmra_discrete_total_update.
  rewrite /white valid_unfold /wf op_unfold /add.
  intros []; auto.
  - ss. rewrite -CORE. ss.
  - ss. des. intros; des; esplits; eauto. rewrite -CORE. ss.
Qed.

Theorem auth_alloc
        (a0 a1 b1 : M)
        (UPD: (a0,ε) ~l~> (a1,b1))
  :
    <<UPD: black a0 ~~> black a1 ⋅ white b1 >>
.
Proof using DISC.
  rewrite /NW -(right_id ε cmra.op (black a0)).
  eapply auth_update. ss.
Qed.

Theorem auth_alloc2
        (a0 delta : M)
        (WF: ✓ (a0 ⋅ delta))
  :
    <<UPD: black a0 ~~> black (a0 ⋅ delta) ⋅ white delta>>
.
Proof using DISC.
  eapply auth_alloc.
  rewrite local_update_unital_discrete.
  intros z WF' EQ. split; auto.
  rewrite EQ left_id (comm cmra.op).
  done.
Qed.

Theorem auth_dealloc
        (a0 a1 b0 : M)
        (UPD: (a0,b0) ~l~> (a1,ε))
  :
    <<UPD: black a0 ⋅ white b0 ~~> black a1 >>
.
Proof using DISC.
  rewrite /NW -(right_id ε cmra.op (black a1)).
  eapply auth_update. ss.
Qed.

Theorem auth_included
        (a b : M)
        (WF: ✓ (black a ⋅ white b))
  :
    <<EXT: b ≼ a>>
.
Proof.
  rewrite /NW /included.
  rewrite /black /white valid_unfold /wf op_unfold /add in WF. rewrite left_id /included in WF. des. eauto.
Qed.

Theorem auth_exclusive
        (a b : M)
        (WF: ✓ (black a ⋅ black b))
  :
    False
.
Proof. rewrite /black valid_unfold /wf op_unfold /add // in WF.
Qed.

Lemma black_wf
      (a : M)
      (WF: ✓ (black a))
  :
    <<WF: ✓ a>>
.
Proof. rewrite /black valid_unfold /wf // in WF. by des. Qed.
End AUTH.
Global Arguments t _ : clear implicits.
End Auth.

(**********************************************************************************)
(*** For backward compatibility, I put below definitions "outside" Auth module. ***)
(*** TODO: put it inside ***)






(* Lemma nth_error_nth
      A (l: list A) a d
      (NTH: nth_error l = Some a)
  :
    <<NTH: nth l d = a>>
.
Proof.
  ginduction n; ii; ss; des_ifs. ss. eapply IHn; eauto.
Qed. *)

(* This is gset_disjR for positive *)
(* Module Gset.
  Import gmap.

  Definition add (x y : option (gset positive)) : option (gset positive) :=
    match x, y with
    | Some x, Some y => if decide (x ## y) then Some (x ∪ y) else None
    | _, _ => None
    end.

  Program Instance t : ucmra :=
    {|
      cmra_car := option (gset positive);
      URA.unit := Some ∅;
      URA._wf := fun x => match x with Some _ => True | None => False end;
      URA._add := add;
      URA.core := fun x => Some ∅;
    |}.
  Next Obligation.
    unfold add. intros [] []; des_ifs. f_equal. set_solver.
  Qed.
  Next Obligation.
    unfold add. intros [] [] []; des_ifs.
    { f_equal. set_solver. }
    all: set_solver.
  Qed.
  Next Obligation.
    unseal "ra". unfold add. intros []; des_ifs.
    { f_equal. set_solver. }
    set_solver.
  Qed.
  Next Obligation.
    unseal "ra". ss.
  Qed.
  Next Obligation.
    unseal "ra". ss. intros [] []; ss.
  Qed.
  Next Obligation.
    unseal "ra". ss. intros []; des_ifs.
    { f_equal. set_solver. }
    set_solver.
  Qed.
  Next Obligation.
    intros []; ss.
  Qed.
  Next Obligation.
    unseal "ra". i. exists (Some ∅). ss. des_ifs.
    { f_equal. set_solver. }
    set_solver.
  Qed.

End Gset. *)

(* This is CoPset for positive *)
(* Module CoPset.
  Import coPset.

  Definition add (x y : option coPset) : option coPset :=
    match x, y with
    | Some x, Some y => if decide (x ## y) then Some (x ∪ y) else None
    | _, _ => None
    end.

  Program Instance t : ucmra :=
    {|
      cmra_car := option coPset;
      URA.unit := Some ∅;
      URA._wf := fun x => match x with Some _ => True | None => False end;
      URA._add := add;
      URA.core := fun x => Some ∅;
    |}.
  Next Obligation.
    intros [] []; ss. des_ifs. f_equal. set_solver.
  Qed.
  Next Obligation.
    unfold add. intros [] [] []; des_ifs.
    { f_equal. set_solver. }
    all: set_solver.
  Qed.
  Next Obligation.
    unseal "ra". unfold add. intros []; des_ifs.
    - f_equal. set_solver.
    - set_solver.
  Qed.
  Next Obligation.
    unseal "ra". ss.
  Qed.
  Next Obligation.
    unseal "ra". intros [] []; ss.
  Qed.
  Next Obligation.
    unseal "ra". unfold add. intros []; des_ifs.
    - f_equal. set_solver.
    - set_solver.
  Qed.
  Next Obligation.
    intros []; ss.
  Qed.
  Next Obligation.
    unseal "ra". i. exists (Some ∅). ss. f_equal. set_solver.
  Qed.

End CoPset. *)

(* This is gset_disjR K for positive *)
(* Module GsetK.
  Import gmap.

  Section KEY.

    Context {K : Type}.
    Context {EqDecision0 : EqDecision K}.
    Context {Countable0 : Countable K}.

    Definition add (x y : option (gset K)) : option (gset K) :=
      match x, y with
      | Some x, Some y => if decide (x ## y) then Some (x ∪ y) else None
      | _, _ => None
      end.

    Program Instance t : ucmra :=
      {|
        cmra_car := option (gset K);
        URA.unit := Some (∅);
        URA._wf := fun x => match x with Some _ => True | None => False end;
        URA._add := add;
        URA.core := fun x => Some ∅;
      |}.
    Next Obligation.
      unfold add. intros [] []; des_ifs. f_equal. set_solver.
    Qed.
    Next Obligation.
      unfold add. intros [] [] []; des_ifs.
      { f_equal. set_solver. }
      all: set_solver.
    Qed.
    Next Obligation.
      unseal "ra". unfold add. intros []; des_ifs.
      { f_equal. set_solver. }
      set_solver.
    Qed.
    Next Obligation.
      unseal "ra". ss.
    Qed.
    Next Obligation.
      unseal "ra". ss. intros [] []; ss.
    Qed.
    Next Obligation.
      unseal "ra". ss. intros []; des_ifs.
      { f_equal. set_solver. }
      set_solver.
    Qed.
    Next Obligation.
      intros []; ss.
    Qed.
    Next Obligation.
      unseal "ra". i. exists (Some ∅). ss. des_ifs.
      { f_equal. set_solver. }
      set_solver.
    Qed.

  End KEY.

End GsetK. *)


Module GRA.
  Record t: Type := GRA__INTERNAL {
    gra_map :> (nat → ucmra);
    gra_discrete : ∀ (i : nat), CmraDiscrete (gra_map i);
  }.
  Class inG (RA: ucmra) (Σ: t) := InG {
    inG_id: nat;
    (* inG_prf: Eq (GRA inG_id) RA; *)
    inG_prf: RA = Σ inG_id;
  }
  .
  Class subG (Σ0 Σ1: t) := SubG i : { j | Σ0 i = Σ1 j }.
  (* Class subG (GRA0 GRA1: t) := SubG { subG_prf: forall i, { j | GRA0 i = GRA1 j } }. *)

  Program Definition of_list (RAs: ucmra_list) : t := {| gra_map := λ n, (UList.nth n RAs (optionUR Empty_setR)) |}.
  Next Obligation.
    ii. revert i. induction RAs as [|? ? IH].
    { destruct i; apply _. }
    destruct i.
    { simpl. apply _. }
    simpl. apply IH.
  Qed.

  Definition to_URA (Σ: t): ucmra := discrete_funUR Σ.

  Coercion to_URA: t >-> ucmra.

  Global Instance GRA_discrete `{Σ : t} : CmraDiscrete
  Σ.
  Proof. apply discrete_funR_cmra_discrete, gra_discrete. Qed.

  Global Instance inG_discrete `{Σ : t} `{@inG A Σ} : CmraDiscrete A.
  Proof.
    destruct H as [id Hid].
    specialize (gra_discrete Σ id). by subst.
  Qed.

  Local Definition cast_ra {A B: ucmra} (LeibEq: A = B) (a : A) : B :=
    eq_rect A cmra_car a _ LeibEq.

  (* a: cmra_car =ty= RAs inG_id =ty= RAs n *)
  Definition embed {A Σ} `{@GRA.inG A Σ} (a: A): Σ :=
    fun n => match Nat.eq_dec inG_id n with
             | left H => ((@eq_rect nat inG_id (Σ : (nat → ucmra)) ((cast_ra inG_prf a): Σ inG_id) n H): Σ n)
             | right _ => ε
             end
  .

  Lemma embed_wf
        A Σ
        `{@GRA.inG A Σ}
        (a: A)
        (WF: ✓ (embed a))
    :
      <<WF: ✓ a>>
  .
  Proof.
    rewrite /NW. rewrite /embed in WF.
    specialize (WF inG_id). ss. des_ifs.
    unfold cast_ra in *. unfold eq_rect, eq_sym in *. dependent destruction e. destruct inG_prf. ss.
  Qed.

  Lemma wf_embed
        A Σ
        `{@GRA.inG A Σ}
        (a: A)
        (WF: ✓ a)
    :
      <<WF: ✓ (embed a)>>
  .
  Proof.
    destruct H. subst. rewrite /NW /embed.
    ii. des_ifs. apply ucmra_unit_valid.
  Qed.

  Lemma embed_equiv
        A Σ
        `{@GRA.inG A Σ}
        (a0 a1: A)
        (EQ : a0 ≡ a1)
    :
      (embed a0) ≡ embed (a1)
  .
  Proof.
    rewrite /embed. intros ?. des_ifs. ss.
    unfold cast_ra. destruct inG_prf. done.
  Qed.

  Global Instance embed_proper A Σ `{@GRA.inG A Σ} :
    Proper ((≡) ==> (≡)) (@embed A Σ _).
  Proof. intros a0 a1 EQ. by apply embed_equiv. Qed.

  Lemma embed_add
        A Σ
        `{@GRA.inG A Σ}
        (a0 a1: A)
    :
      (embed a0) ⋅ (embed a1) ≡ embed (a0 ⋅ a1)
  .
  Proof.
    intros ?. rewrite /NW /embed discrete_fun_lookup_op. des_ifs.
    - ss. unfold cast_ra. destruct inG_prf. reflexivity.
    - rewrite right_id //.
  Qed.

  (* (fun f => exists (m1: M), f ≡ maps_to_res a m1 /\ P m1). *)
  Lemma embed_updatable_set
        A Σ
        `{@GRA.inG A Σ}
        (a : A) P
        (UPD: a ~~>: P)
    :
      <<UPD: (GRA.embed a) ~~>: (λ a', ∃ b, a' = GRA.embed b ∧ P b) >>
  .
  Proof.
    rewrite /NW cmra_discrete_total_updateP.
    rewrite cmra_discrete_total_updateP in UPD.
    ss. intros z WF.
    unshelve hexploit UPD.
    { eapply (@eq_rect ucmra (Σ (@GRA.inG_id _ _ H)) cmra_car).
      { eapply (z (@GRA.inG_id _ _ H)). }
      { symmetry. eapply (@GRA.inG_prf _ _ H). }
    }
    { specialize (WF GRA.inG_id). rewrite discrete_fun_lookup_op in WF.
      destruct H. subst. ss.
      unfold GRA.embed in WF. ss.
      replace (Nat.eq_dec inG_id0 inG_id0)
        with (@left (inG_id0 = inG_id0) (inG_id0 <> inG_id0) eq_refl) in WF; ss.
      des_ifs. repeat f_equal. eapply proof_irrelevance.
    }
    i. des. exists (GRA.embed y). esplits; eauto.
    unfold GRA.embed. intros k. rewrite discrete_fun_lookup_op. des_ifs.
    { ss. unfold PCM.GRA.cast_ra. destruct H. subst. ss. }
    { specialize (WF k). rewrite left_id.
      rewrite discrete_fun_lookup_op in WF.
      eapply cmra_valid_op_r,WF.
    }
  Qed.

  Lemma embed_updatable
        A Σ
        `{@GRA.inG A Σ}
        (a0 a1: A)
        (UPD: a0 ~~> a1)
    :
      <<UPD: (GRA.embed a0) ~~> (GRA.embed a1)>>
  .
  Proof.
    rewrite /NW.
    eapply cmra_update_updateP, cmra_updateP_weaken.
    - rewrite cmra_update_updateP in UPD.
      apply embed_updatable_set,UPD.
  - intros y EQ. simpl in *. des. subst. done.
  Qed.

  Lemma embed_core M Σ `{@GRA.inG M Σ} (r : M) : embed (core r) ≡ core (embed r).
  Proof.
    intros i. rewrite /embed /to_URA discrete_fun_lookup_core.
    des_ifs.
    - ss. destruct H. ss. dependent destruction inG_prf0. ss.
    - symmetry. apply core_id_total,_.
  Qed.

  Lemma embed_unit M Σ `{@GRA.inG M Σ} : GRA.embed ε = ε.
  Proof.
    unfold embed. extensionalities n. des_ifs. ss.
    destruct H. ss. dependent destruction inG_prf0.
    ss.
  Qed.

  Section GETSET.
    Variable ra: ucmra.
    Variable gra: t.
    Context `{@inG ra gra}.

    Section GETSET.
    Variable get: cmra_car ra.
    Variable set: (cmra_car ra) -> unit.

    (* own & update can be lifted *)
    (* can we write spec in terms of own & update, not get & set? *)
    (* how about add / sub? *)
    Program Definition get_lifted: cmra_car gra :=
      fun n => if Nat.eq_dec n inG_id then _ else ε.
    Next Obligation.
      i. subst. apply (cast_ra inG_prf get).
    Defined.

    (* Program Definition set_lifted: cmra_car construction gra -> unit := *)
    (*   fun n => if Nat.eq_dec n inG_id then _ else URA.unit. *)
    (* Next Obligation. *)
    (*   apply (ra_transport inG_prf get). *)
    (* Defined. *)
    End GETSET.

    Section HANDLER.
    Variable handler: cmra_car ra -> cmra_car ra.
    Local Obligation Tactic := idtac.
    Program Definition handler_lifted: cmra_car gra -> cmra_car gra :=
      fun st0 => fun n => if Nat.eq_dec n inG_id then _ else st0 n
    .
    Next Obligation.
      i. subst. simpl in st0. specialize (st0 inG_id).
      rewrite /= -inG_prf in st0. specialize (handler st0). rewrite <- inG_prf. apply handler.
    Defined.

    End HANDLER.

  End GETSET.

  Section CONSTRUCTION.
    Variable RAs: ucmra_list.
    Definition GRA: t := of_list RAs.
    (* Theorem construction_adequate: forall RA (IN: UList.nth_error RAs = Some RA),
        inG RA GRA.
    Proof.
      i. unshelve econs; eauto. unfold GRA. symmetry. eapply nth_error_nth; eauto.
    Qed. *)

    (* Let GRA2: RA.t := URA.pointwise_dep GRA. *)
    (* Goal @RA.car GRA2 = forall k, (@RA.car (GRA k)). ss. Qed. *)
  End CONSTRUCTION.

  (* Definition extends (RA0 RA1: ucmra): Prop := *)
  (*   exists c, URA.prod RA0 c = RA1 *)
  (* . *)

  (* Class inG2 (RA GRA: ucmra): Prop := {
    GRA_data: t;
    (* GRA_prf:  *)
    inG2_id: nat;
    inG2_prf: GRA_data inG2_id = RA;
  }
  . *)

  Fixpoint point_wise_wf (Ml: ucmra_list) (x: of_list Ml) (n: nat) :=
  match n with
  | O => True
  | S n' => ✓ (x n') ∧ @point_wise_wf Ml x n'
  end.

  Definition point_wise_wf_lift (Ml: ucmra_list) (x: of_list Ml)
             (POINT: point_wise_wf x (UList.length Ml))
    :
      ✓ x.
  Proof.
    intro i. unfold of_list in *.
    assert (WF: ∀ (n m: nat)
                       (POINT: point_wise_wf x n)
                       (LT: (m < n)%nat),
               ✓ (x m)).
    { induction n.
      { i. inv LT. }
      { i. ss. des. inv LT; auto. }
    }
    destruct (le_lt_dec (UList.length Ml) i).
    { generalize (x i). simpl. rewrite UList.nth_overflow; auto. intros []; done. }
    { eapply WF; eauto. }
  Qed.

  Lemma point_add (G: t) (x0 x1: G) n
    :
      (x0 ⋅ x1) n = x0 n ⋅ x1 n.
  Proof. by rewrite discrete_fun_lookup_op. Qed.
End GRA.
Coercion GRA.to_URA: GRA.t >-> ucmra.

Global Opaque GRA.to_URA.
(* Definition ε `{Σ: GRA.t}: Σ := URA.unit. *)

(***
Choose: non-det
Take: angelic non-det
(*** empty choose : NB ***)
(*** empty take : UB ***)
x <- Choose X ;; guarantee (P x) ;; k x   (~=) x <- Choose { X | P x } ;; k x
x <- Take X   ;; assume (P x)    ;; k x   (~=) x <- Take { X | P x }   ;; k x
guarantee P ;; assume P ;; k              (~=) guarantee P ;; k
x <- Take X ;; pure ;; k x                (>=) pure ;; x <- Take X ;; k x
pure ;; x <- Choose X ;; k x              (>=) x <- Choose X ;; pure ;; k x
______________caller______________    _________________callee_________________   _caller_
x0 <- Choose X ;; guarantee (P x0) ;; (x1 <- Take X ;; assume (P x1) ;; k1 x1) ;; k0 x0
(<=)
x0 <- Choose X ;; x1 <- Take X ;; guarantee (P x0) ;; assume (P x1) ;; k1 x1 ;; k0 x0
(<=)
x <- Choose X ;; guarantee (P x) ;; assume (P x) ;; k1 x ;; k0 x
(<=)
x <- Choose X ;; guarantee (P x) ;; k1 x ;; k0 x
Goal forall X Y (k: X -> Y),
    x <- trigger (EChoose X) ;; Ret (k x) =
    y <- trigger (EChoose {y | exists x, y = k x}) ;; Ret (proj1_sig y)
.
Abort.
***)


Declare Scope ra_scope.
Delimit Scope ra_scope with ra.
Notation " K ==> V' " := (discrete_funUR (fun k : K => V')) (at level 55, right associativity): ra_scope.


(* Section TEST.
  Variable A B: Type.
  Variable C: ofe.
  Let _myRA: ucmra := (A ==> B ==> (optionUR $ exclR $ (agreeR C)))%ra.
  (* Let myRA: ucmra := authUR _myRA. *)
End TEST. *)

Ltac r_first rs :=
  match rs with
  | (?rs0 ⋅ ?rs1) =>
    let tmp0 := r_first rs0 in
    constr:(tmp0)
  | ?r => constr:(r)
  end
.

Ltac r_solve :=
  repeat rewrite (assoc op);
  repeat (try rewrite right_id; try rewrite left_id);
  match goal with
  | [|- ?lhs ≡ (_ ⋅ _) ] =>
    let a := r_first lhs in
    try rewrite <- (comm op a);
    repeat rewrite <- (assoc op);
    try (f_equiv; r_solve)
  | _ => try reflexivity
  end
.

Ltac r_wf H := eapply cmra_valid_proper; [|exact H]; r_solve.

Ltac g_wf_tac :=
  cbn; repeat rewrite right_id; repeat rewrite left_id;
  apply GRA.point_wise_wf_lift; ss; splits; repeat rewrite GRA.point_add; unfold GRA.embed; ss;
  repeat rewrite right_id; repeat rewrite left_id; try apply ucmra_unit_valid.


(* Section UNIT.

  Program Instance Unit : ucmra := {| URA.unit := tt; URA._add := fun _ _ => tt; URA._wf := fun _ => True; URA.core := fun _ => tt; |}.
  Next Obligation. destruct a. ss. Qed.
  Next Obligation. destruct a. ss. Qed.
  Next Obligation. unseal "ra". i. destruct a. ss. Qed.
  Next Obligation. unseal "ra". ss. Qed.
  Next Obligation. unseal "ra". i. ss. Qed.
  Next Obligation. unseal "ra". i. destruct a. ss. Qed.
  Next Obligation. ss. Qed.
  Next Obligation. unseal "ra". i. exists tt. ss. Qed.

  Lemma Unit_wf : forall x, @✓ Unit x.
  Proof. unfold ✓. unseal "ra". ss. Qed.

End UNIT.
Global Opaque Unit. *)

(* Section URA_PROD.

  Lemma unfold_prod_add (M0 M1 : ucmra) : @URA.add (URA.prod M0 M1) = fun '(a0, a1) '(b0, b1) => (a0 ⋅ b0, a1 ⋅ b1).
  Proof. rewrite URA.unfold_add. extensionalities r0 r1. destruct r0, r1. ss. Qed.

  Lemma unfold_prod_wf (M0 M1 : ucmra) : @✓ (URA.prod M0 M1) = fun r => ✓ (fst r) /\ ✓ (snd r).
  Proof. rewrite URA.unfold_wf. extensionalities r. destruct r. ss. Qed.

End URA_PROD. *)

Section POINTWISE.

  Lemma unfold_pointwise_add X (M: ucmra) (f0 f1: (X ==> M)%ra)
    :
    f0 ⋅ f1 ≡ (fun x => f0 x ⋅ f1 x).
  Proof. intros i. by rewrite discrete_fun_lookup_op. Qed.

  Lemma updatable_set_impl (M: ucmra)
        (P0 P1: M -> Prop)
        (IMPL: forall r, P0 r -> P1 r)
        (m: M)
        (UPD: m ~~>: P0)
    :
    m ~~>: P1.
  Proof. apply (cmra_updateP_weaken P0 P1); done. Qed.

  Lemma pointwise_extends A (M: ucmra)
        (f0 f1: (A ==> M)%ra)
        (UPD: ∀ a, (f0 a) ≼ (f1 a))
    :
    f0 ≼ f1.
  Proof. by apply included_discrete_fun. Qed.

  Lemma pointwise_updatable A (M: ucmra)
        (f0 f1: (A ==> M)%ra)
        (UPD: forall a, (f0 a) ~~> (f1 a))
    :
    f0 ~~> f1.
  Proof. by apply cmra_update_discrete_fun. Qed.

  Lemma pointwise_updatable_set A (M: ucmra)
        (f: (A ==> M)%ra)
        (P: A -> M -> Prop)
        (UPD: forall a, (f a) ~~>: (P a))
    :
    f ~~>: (fun f' => forall a, P a (f' a)).
  Proof. by apply cmra_updateP_discrete_fun. Qed.

  Definition maps_to_res {A} {M: ucmra}
             a (m : M) : (A ==> M)%ra :=
    fun a' => if excluded_middle_informative (a' = a)
              then m
              else ε.

  Lemma maps_to_res_add A (M: ucmra)
        (a: A) (m0 m1: M)
    :
    maps_to_res a m0 ⋅ maps_to_res a m1
    ≡
      maps_to_res a (m0 ⋅ m1).
  Proof.
    intros a'. rewrite /maps_to_res discrete_fun_lookup_op. des_ifs.
    by rewrite right_id.
  Qed.

  Lemma maps_to_updatable A (M: ucmra)
        (a: A) (m0 m1: M)
        (UPD: m0 ~~> m1)
    :
    (maps_to_res a m0) ~~> (maps_to_res a m1).
  Proof.
    eapply pointwise_updatable. i.
    unfold maps_to_res. des_ifs.
  Qed.

  Lemma maps_to_updatable_set A (M: ucmra)
        (a: A) (m: M) (P: M -> Prop)
        (UPD: m ~~>: P)
    :
      (maps_to_res a m) ~~>:
      (fun f => exists (m1: M), f ≡ maps_to_res a m1 /\ P m1).
  Proof.
    eapply updatable_set_impl; cycle 1.
    { eapply pointwise_updatable_set.
      instantiate (1:= fun a' m' => (a' = a -> P m') /\ (a' ≠ a -> m' ≡ ε)).
      intros a' n mz WF. unfold maps_to_res in WF. des_ifs.
      { specialize (UPD n mz WF). des. exists y. esplits; eauto. ss. }
      { exists ε. splits; ss. }
    }
    { intros r H. ss. exists (r a). splits; auto.
      { intros a'. unfold maps_to_res. des_ifs.
        specialize (H a'). des. auto.
      }
      { specialize (H a). des. auto. }
    }
  Qed.

  Definition map_update {A} {M: ucmra}
             (f: (A ==> M)%ra) a m :=
    fun a' => if excluded_middle_informative (a' = a)
              then m
              else f a'.

End POINTWISE.

Section PWDEP.

  Lemma pointwise_dep_extends
        A (Ms : A -> ucmra)
        (f0 f1 : @pointwise_dep A Ms)
        (UPD : forall a, (f0 a) ≼ (f1 a))
    :
    f0 ≼ f1.
  Proof. by apply included_discrete_fun. Qed.

  Lemma pointwise_dep_updatable A (Ms: A → ucmra)
        (f0 f1: @pointwise_dep A Ms)
        (UPD: ∀ a, (f0 a) ~~> (f1 a))
    :
    f0 ~~> f1.
  Proof. by apply cmra_update_discrete_fun. Qed.

  Lemma pointwise_dep_updatable_set
        A (Ms : A -> ucmra)
        (f : @pointwise_dep A Ms)
        (P : forall (a : A), (Ms a) -> Prop)
        (UPD: forall a, (f a) ~~>: (P a))
    :
    f ~~>: (fun f' => forall a, P a (f' a)).
  Proof. by apply cmra_updateP_discrete_fun. Qed.

  Program Definition maps_to_res_dep {A : Type} {Ms : A -> ucmra} (a : A) (m : Ms a)
    : @pointwise_dep A Ms.
  Proof.
    intros k. destruct (Axioms.excluded_middle_informative (k = a)).
    - subst k. exact m.
    - exact ε.
  Defined.

  Lemma maps_to_res_dep_eq
        A (Ms : A -> ucmra)
        (a : A)
        (m : Ms a)
    :
    (@maps_to_res_dep A Ms a m) a = m.
  Proof.
    unfold maps_to_res_dep. des_ifs. unfold eq_rect_r.
    rewrite <- Eqdep.EqdepTheory.eq_rect_eq. auto.
  Qed.

  Lemma maps_to_res_dep_neq
        A (Ms : A -> ucmra)
        (a b : A)
        (m : Ms a)
    :
    a ≠ b -> (@maps_to_res_dep A Ms a m) b = ε.
  Proof.
    i. unfold maps_to_res_dep. des_ifs.
  Qed.

  Lemma maps_to_res_dep_add
        A (Ms : A -> ucmra)
        (a : A)
        (m0 m1 : Ms a)
    :
    @maps_to_res_dep _ Ms a m0 ⋅ @maps_to_res_dep _ Ms a m1 ≡ @maps_to_res_dep _ Ms a (m0 ⋅ m1).
  Proof.
    intros a'. ss. rewrite discrete_fun_lookup_op.
    destruct (Axioms.excluded_middle_informative (a' = a)).
    - subst a'. rewrite ! @maps_to_res_dep_eq. auto.
    - rewrite ! @maps_to_res_dep_neq; auto. by rewrite right_id.
  Qed.

  Lemma maps_to_res_dep_updatable
        A (Ms : A -> ucmra)
        (a : A)
        (m0 m1 : Ms a)
        (UPD: m0 ~~> m1)
    :
    (@maps_to_res_dep A Ms a m0) ~~> (@maps_to_res_dep A Ms a m1).
  Proof.
    eapply pointwise_dep_updatable. i. unfold maps_to_res_dep. des_ifs.
  Qed.

  Lemma maps_to_res_dep_updatable_set
        A (Ms : A -> ucmra)
        (a : A)
        (m : Ms a)
        (P : ∀ (a' : A), Ms a' -> Prop)
        (UPD: m ~~>: (P a))
    :
      (@maps_to_res_dep A Ms a m) ~~>:
      (fun f => exists (m1 : Ms a), f = @maps_to_res_dep A Ms a m1 /\ (P a m1)).
  Proof.
    eapply updatable_set_impl; cycle 1.
    { eapply pointwise_dep_updatable_set.
      instantiate (1:= fun a' m' => (a' = a → P a' m') /\ (a' ≠ a → m' = ε)).
      intros a' n mz WF. unfold maps_to_res_dep in WF. des_ifs.
      { exploit (UPD n); eauto. i. des. esplits; eauto. ss. }
      { exists ε. splits; ss. }
    }
    { i. ss. exists (r a). splits; auto.
      { extensionalities a'. unfold maps_to_res_dep. des_ifs.
        specialize (H a'). des. auto.
      }
      { specialize (H a). des. auto. }
    }
  Qed.

  Program Definition maps_to_res_dep_update {A} {Ms: A -> ucmra}
          (f: @pointwise_dep A Ms) a (m : Ms a) : @pointwise_dep A Ms.
  Proof.
    intros k. destruct (excluded_middle_informative (k = a)).
    - subst k. exact m.
    - exact (f k).
  Qed.

End PWDEP.


Tactic Notation "unfold_prod" :=
  try rewrite -!pair_op;
  rewrite pair_valid;
  simpl.

Tactic Notation "unfold_prod" hyp(H) :=
  try rewrite -!pair_op in H;
  rewrite pair_valid in H;
  simpl in H;
  let H1 := fresh H in
  destruct H as [H H1].

Section PWDAUX.

  Context {K: Type} `{M: K -> ucmra}.
  Let RA := @pointwise_dep K M.

  Lemma pwd_extends (f0 f1: forall (k : K), M k) (EXT: (f0 : (@cmra_car RA)) ≼ (f1 : (@cmra_car RA))) : <<EXT: forall k, (f0 k) ≼ (f1 k)>>.
  Proof.
    ii. r in EXT. des. specialize (EXT k).
    rewrite discrete_fun_lookup_op in EXT.  eexists; eauto.
  Qed.

  Lemma pwd_wf: forall (f: forall (k : K), M k) (WF: ✓ (f: @cmra_car RA)), <<WF: forall k, ✓ (f k)>>.
  Proof. ii; ss. eauto. Qed.

  Lemma pwd_add_disj_wf
        (f g: forall (k : K), M k)
        (WF0: ✓ (f: @cmra_car RA))
        (WF1: ✓ (g: @cmra_car RA))
        (DISJ: forall k, <<DISJ: f k ≡ ε \/ g k ≡ ε>>)
    :
      <<WF: ✓ ((f: RA) ⋅ g)>>
  .
  Proof.
    intros k. rewrite discrete_fun_lookup_op. specialize (DISJ k). des; rewrite DISJ.
    - rewrite left_id; eauto.
    - rewrite right_id; eauto.
  Qed.

  (* Lemma pw_insert_wf: forall `{EqDecision K} (f: K -> M) k v (WF: ✓ (f: @cmra_car RA)) (WFV: ✓ v),
      <<WF: ✓ (f: @cmra_car RA)>>.
  Proof. by apply pwd_insert_wf. Qed. *)

  Lemma pwd_lookup_wf: forall (f: @cmra_car RA) k (WF: ✓ f), ✓ (f k).
  Proof. ii; ss. Qed.

End PWDAUX.


Section PWAUX.

  Context {K: Type} `{M: ucmra}.
  Let RA := @pointwise K M.

  Lemma pw_extends (f0 f1 : K -> M) (EXT: (f0 : @cmra_car RA) ≼ (f1  : @cmra_car RA)) : <<EXT: forall k, (f0 k) ≼ (f1 k)>>.
  Proof. by apply pwd_extends. Qed.

  Lemma pw_wf: forall (f: K -> M) (WF: ✓ (f : @cmra_car RA)), <<WF: forall k, ✓ (f k)>>.
  Proof. by apply pwd_wf. Qed.

  Lemma pw_add_disj_wf
        (f g: K -> M)
        (WF0: ✓ (f: @cmra_car RA))
        (WF1: ✓ (g: @cmra_car RA))
        (DISJ: forall k, <<DISJ: f k ≡ ε ∨ g k ≡ ε>>)
    :
      <<WF: ✓ ((f: RA) ⋅ g)>>
  .
  Proof. by apply pwd_add_disj_wf. Qed.

  (* Lemma pw_insert_wf: forall `{EqDecision K} (f: K -> M) k v (WF: ✓ (f: @cmra_car RA)) (WFV: ✓ v),
      <<WF: ✓ (f: @cmra_car RA)>>.
  Proof. by apply pwd_insert_wf. Qed. *)

  Lemma pw_lookup_wf: forall (f: @cmra_car RA) k (WF: ✓ f), ✓ (f k).
  Proof. by apply pwd_lookup_wf. Qed.

End PWAUX.

(* TODO: make lemmas for RA and turn it into URA at the last *)
