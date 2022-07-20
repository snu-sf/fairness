From sflib Require Import sflib.
Require Export ZArith.
(* Require Export Znumtheory. *)
Require Import List.
Require Import String.
Require Import ClassicalChoice ChoiceFacts.
Require Import Coq.Classes.RelationClasses.
Require Import Lia.
Require Import Program.
From Fairness Require Import Axioms.

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
  Class t: Type := mk {
    car:> Type;
    add: car -> car -> car;
    wf: car -> Prop;
    add_comm: forall a b, add a b = add b a;
    add_assoc: forall a b c, add a (add b c) = add (add a b) c;
    wf_mon: forall a b, wf (add a b) -> wf a;

    extends := fun a b => exists ctx, add a ctx = b;
    updatable := fun a b => forall ctx, wf (add a ctx) -> wf (add b ctx);
    updatable_set := fun a B => forall ctx (WF: wf (add a ctx)),
                         exists b, <<IN: B b>> /\ <<WF: wf (add b ctx)>>;
  }
  .

  Lemma extends_updatable
        `{M: t}
        a b
        (EXT: extends a b)
    :
      <<UPD: updatable b a>>
  .
  Proof.
    ii. rr in EXT. des. clarify. eapply wf_mon; eauto.
    rewrite <- add_assoc in H.
    rewrite <- add_assoc. rewrite (add_comm ctx). eauto.
  Qed.

  Lemma updatable_add
        `{M: t}
        a0 a1
        b0 b1
        (UPD0: updatable a0 a1)
        (UPD1: updatable b0 b1)
    :
      <<UPD: updatable (add a0 b0) (add a1 b1)>>
  .
  Proof.
    ii. r in UPD0. r in UPD1.
    specialize (UPD0 (add b0 ctx)). exploit UPD0; eauto. { rewrite add_assoc. ss. } intro A.
    specialize (UPD1 (add a1 ctx)). exploit UPD1; eauto.
    { rewrite add_assoc. rewrite (add_comm b0). rewrite <- add_assoc. ss. }
    intro B.
    rewrite (add_comm a1). rewrite <- add_assoc. ss.
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

  Program Instance extends_Transitive `{M: t}: Transitive extends.
  Next Obligation.
    rr. ii. rr in H. rr in H0. des. rewrite <- H0. rewrite <- H. esplits; eauto. rewrite add_assoc. eauto.
  Qed.

  Program Instance updatable_PreOrder `{M: t}: PreOrder updatable.
  Next Obligation. ii. ss. Qed.
  Next Obligation. ii. r in H. r in H0. eauto. Qed.

  Program Instance prod (M0 M1: t): t := {
    car := car (t:=M0) * car (t:=M1);
    add := fun '(a0, a1) '(b0, b1) => ((add a0 b0), (add a1 b1));
    wf := fun '(a0, a1) => wf a0 /\ wf a1;
  }
  .
  Next Obligation. f_equal; rewrite add_comm; ss. Qed.
  Next Obligation. f_equal; rewrite add_assoc; ss. Qed.
  Next Obligation. split; eapply wf_mon; eauto. Qed.

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
    ii. ss. des_ifs. des. esplits; eauto.
  Qed.

  Program Instance frac (denom: positive): t := {
    car := positive;
    add := fun a b => (a + b)%positive;
    wf := fun a => (a <= denom)%positive;
  }
  .
  Next Obligation. lia. Qed.
  Next Obligation. lia. Qed.
  Next Obligation. lia. Qed.

  Theorem frac_updatable
          denom M
          a b
    :
      <<UPD: @updatable (prod (frac denom) M) (denom, a) b>>
  .
  Proof.
    ii. ss. des_ifs. des. lia.
  Qed.

  Program Instance agree (A: Type): t := {
    car := option A;
    add := fun a0 a1 => if excluded_middle_informative (a0 = a1) then a0 else None;
    wf := fun a => a <> None;
  }
  .
  Next Obligation. des_ifs. Qed.
  Next Obligation. des_ifs. Qed.
  Next Obligation. des_ifs. Qed.

  Theorem agree_unupdatable
          A
          a0 a1
    :
      <<UPD: @updatable (agree A) (Some a0) a1 -> a1 = Some a0>>
  .
  Proof.
    ii. ss. rr in H. specialize (H (Some a0)). ss. des_ifs.
    exfalso. eapply H; eauto. ss.
  Qed.

  Program Instance excl (A: Type): t := {
    car := option A;
    add := fun _ _ => None;
    wf := fun a => a <> None;
  }
  .

  Theorem excl_updatable
          A
          a0 a1
    :
      <<UPD: @updatable (excl A) (Some a0) a1>>
  .
  Proof. rr. ii. ss. Qed.

  Let sum_add {M0 M1} := (fun (a b: car (t:=M0) + car (t:=M1) + unit) =>
                            match a, b with
                            | inl (inl a0), inl (inl b0) => inl (inl (add a0 b0))
                            | inl (inr a1), inl (inr b1) => inl (inr (add a1 b1))
                            | _, _ => inr tt
                            end).
  Let sum_wf {M0 M1} := (fun (a: car (t:=M0) + car (t:=M1) + unit) =>
                           match a with
                           | inl (inl a0) => wf a0
                           | inl (inr a1) => wf a1
                           | _ => False
                           end).
  Program Instance sum (M0 M1: t): t := {
    car := car (t:=M0) + car (t:=M1) + unit (* boom *);
    add := sum_add;
    wf := sum_wf;
  }
  .
  Next Obligation. unfold sum_add. esplits; ii; ss; des; des_ifs; do 2 f_equal; apply add_comm. Qed.
  Next Obligation. unfold sum_add. esplits; ii; ss; des; des_ifs; do 2 f_equal; apply add_assoc. Qed.
  Next Obligation. unfold sum_wf in *. des_ifs; ss; des_ifs; eapply wf_mon; eauto. Qed.

  Program Instance pointwise K (M: t): t := {
    car := K -> car;
    add := fun f0 f1 => (fun k => add (f0 k) (f1 k));
    wf := fun f => forall k, wf (f k);
  }
  .
  Next Obligation. apply func_ext. ii. rewrite add_comm. ss. Qed.
  Next Obligation. apply func_ext. ii. rewrite add_assoc. ss. Qed.
  Next Obligation. eapply wf_mon; ss. Qed.

  Local Program Instance empty: t := {
    car := False;
    add := fun a _ => a;
    wf := fun _ => False;
  }
  .
  Next Obligation. ss. Qed.

End RA.







Local Obligation Tactic := i; unseal "ra"; ss; des_ifs.

(*** PCM == Unital RA ***)
(*** When URA, not RA? (1) Auth algebra (2) global RA construction ***)
Module URA.
  Class t: Type := mk {
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
  .

  Lemma add_comm `{M: t}: forall a b, add a b = add b a. Proof. i. unfold add. unseal "ra". rewrite _add_comm; ss. Qed.
  Lemma add_assoc `{M: t}: forall a b c, add a (add b c) = add (add a b) c. Proof. i. unfold add. unseal "ra". rewrite _add_assoc; ss. Qed.

  Lemma wf_split `{M: t}: forall a b, wf (add a b) -> <<WF: wf a /\ wf b>>.
  Proof. i. split; eapply wf_mon; eauto. rewrite add_comm; eauto. Qed.

  Lemma extends_updatable
        `{M: t}
        a b
        (EXT: extends a b)
    :
      <<UPD: updatable b a>>
  .
  Proof.
    ii. rr in EXT. des. clarify. eapply wf_mon; eauto.
    rewrite <- add_assoc in H.
    rewrite <- add_assoc. rewrite (add_comm ctx). eauto.
  Qed.

  Lemma unit_id_ `{M: t} b (EQ: b = unit): forall a, add a b = a. i. subst. apply unit_id. Qed.

  Lemma unit_idl `{M: t}: forall a, add unit a = a. i. rewrite add_comm. rewrite unit_id; ss. Qed.

  Lemma wf_core `{M: t}: forall a (WF: wf a), wf (core a).
  Proof. i. eapply wf_mon. rewrite core_id. auto. Qed.

  Lemma unit_core `{M: t}: core unit = unit.
  Proof.
    transitivity (add (core unit) unit).
    { symmetry. apply unit_id. }
    { apply core_id. }
  Qed.

  (*** TODO: remove redundancy with "updatable_horizontal" above ***)
  Lemma updatable_add
        `{M: t}
        a0 a1
        b0 b1
        (UPD0: updatable a0 a1)
        (UPD1: updatable b0 b1)
    :
      <<UPD: updatable (add a0 b0) (add a1 b1)>>
  .
  Proof.
    ii. r in UPD0. r in UPD1.
    specialize (UPD0 (add b0 ctx)). exploit UPD0; eauto. { rewrite add_assoc. ss. } intro A.
    specialize (UPD1 (add a1 ctx)). exploit UPD1; eauto.
    { rewrite add_assoc. rewrite (add_comm b0). rewrite <- add_assoc. ss. }
    intro B.
    rewrite (add_comm a1). rewrite <- add_assoc. ss.
  Qed.

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

  Program Instance prod (M0 M1: t): t := {
    car := car (t:=M0) * car (t:=M1);
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

  Program Definition to_RA (M: t): RA.t := {|
    RA.car := car;
    RA.add := add;
    RA.wf := wf;
  |}
  .
  Next Obligation. apply add_comm. Qed.
  Next Obligation. apply add_assoc. Qed.
  Next Obligation. eapply wf_mon; eauto. Qed.

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

  Program Instance pointwise_dep K (M: K -> t): t := {
    car := forall (k: K), car (t:=M k);
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
  Qed.

End URA.

(* Coercion URA.to_RA: URA.t >-> RA.t. *)
Coercion RA.car: RA.t >-> Sortclass.
Coercion URA.car: URA.t >-> Sortclass.

Tactic Notation "ur" := try rewrite ! URA.unfold_wf; try rewrite ! URA.unfold_add; cbn.
Tactic Notation "ur" "in" hyp(H)  := try rewrite ! URA.unfold_wf in H; try rewrite ! URA.unfold_add in H; cbn in H.

Notation "'ε'" := URA.unit.
Infix "⋅" := URA.add (at level 50, left associativity).
Notation "(⋅)" := URA.add (only parsing).














Module of_RA.
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

Program Instance t (RA: RA.t): URA.t := {
  car := car;
  unit := of_RA.unit;
  _wf := wf;
  _add := add;
  core := fun _ => unit;
}.
Next Obligation. unfold add. des_ifs. { rewrite RA.add_comm; ss. } Qed.
Next Obligation. unfold add. des_ifs. { rewrite RA.add_assoc; ss. } Qed.
Next Obligation. unfold add. des_ifs. Qed.
Next Obligation. unfold add in *. des_ifs. eapply RA.wf_mon; eauto. Qed.
Next Obligation. exists unit. ss. Qed.

End of_RA.
End of_RA.

(* Coercion to_RA: t >-> RA.t. *)
Coercion of_RA.t: RA.t >-> URA.t.











Module Excl.
Section EXCL.

Context {X: Type}.
Inductive car: Type :=
| just (x: X)
| unit
| boom
.

Let _add := fun x y => match x, y with | _, unit => x | unit, _ => y | _, _ => boom end.
Let _wf := fun a => a <> boom.

Program Instance t: URA.t := {
  URA.car := car;
  URA._add := _add;
  URA._wf := _wf;
  URA.unit := unit;
  URA.core := fun _ => unit;
}
.
Next Obligation. unfold _wf, _add in *. des_ifs. Qed.
Next Obligation. unfold _wf, _add in *. des_ifs. Qed.
Next Obligation. unfold _wf, _add in *. des_ifs. Qed.
Next Obligation. unfold _wf, _add in *. des_ifs. Qed.
Next Obligation. exists unit. auto. Qed.

Theorem updatable
        a0 a1
        (WF: URA.wf a1)
  :
    <<UPD: URA.updatable (just a0) a1>>
.
Proof. rr. unfold URA.wf, URA.add in *. unseal "ra". ss. ii. des_ifs; ss. unfold _wf, _add in *. des_ifs; ss. Qed.

Theorem extends
        a0 a1
        (WF: URA.wf a1)
        (EXT: URA.extends (just a0) a1)
  :
    <<EQ: a1 = just a0>>
.
Proof. rr. rr in EXT. des; subst. unfold URA.wf, URA.add in *. unseal "ra". ss. des_ifs; ss. Qed.

Theorem wf
        a0 a1
        (WF: URA.wf (URA.add (just a0) a1))
  :
    <<EQ: a1 = unit>>
.
Proof. rr. unfold URA.wf, URA.add in *. unseal "ra". ss. des_ifs; ss. Qed.

Coercion option_coercion (x: option X): car :=
  match x with
  | Some x => just x
  | None => boom
  end
.

End EXCL.
End Excl.

Arguments Excl.t: clear implicits.
Coercion Excl.option_coercion: option >-> Excl.car.


Module Auth.
Section AUTH.

(* Variable (M: URA.t). *)

Inductive car `{M: URA.t}: Type :=
| frag (f: M)
| excl (e: M) (f: M)
| boom
.

Let add `{M: URA.t} := fun a0 a1 => match a0, a1 with
                                    | frag f0, frag f1 => frag (f0 ⋅ f1)
                                    | frag f0, excl e1 f1 => excl e1 (f0 ⋅ f1)
                                    | excl e0 f0, frag f1 => excl e0 (f0 ⋅ f1)
                                    | _, _ => boom
                                    end.
Let wf `{M: URA.t} := fun a =>
                        match a with
                        | frag f => URA.wf f
                        | excl e f => URA.extends f e /\ URA.wf e
                        | boom => False
                        end.

Let core `{M: URA.t} := fun a =>
                          match a with
                          | frag f => frag (URA.core f)
                          | excl _ f => frag (URA.core f)
                          | boom => boom
                          end.

Program Instance t (M: URA.t): URA.t := {
  car := car;
  unit := frag ε;
  _add := add;
  _wf := wf;
  core := core;
}
.
Next Obligation. subst add wf. ss. des_ifs; f_equal; eauto using URA.add_comm. Qed.
Next Obligation. subst add wf. ss. des_ifs; f_equal; eauto using URA.add_assoc. Qed.
Next Obligation. subst add wf. ss. ii; des_ifs; ss; rewrite URA.unit_id; ss. Qed.
Next Obligation. subst add wf. eauto using URA.wf_unit. Qed.
Next Obligation.
  subst add wf. ss.
  des_ifs; des; eauto using URA.wf_mon.
  - rr in H. des. subst. eapply URA.wf_mon. rewrite URA.add_assoc. eauto.
  - esplits; eauto. etransitivity; eauto. rr. ss. esplits; eauto.
Qed.
Next Obligation. subst add core. ss. des_ifs; f_equal; rewrite URA.core_id; ss. Qed.
Next Obligation. subst core. ss. des_ifs; f_equal; rewrite URA.core_idem; ss. Qed.
Next Obligation.
  destruct a.
  - destruct b.
    + hexploit (URA.core_mono f f0). intros [c EQ].
      exists (frag c). ss. f_equal. auto.
    + hexploit (URA.core_mono f f0). intros [c EQ].
      exists (frag c). ss. f_equal. auto.
    + exists boom. ss.
  - destruct b.
    + hexploit (URA.core_mono f f0). intros [c EQ].
      exists (frag c). ss. f_equal. auto.
    + exists boom. ss.
    + exists boom. ss.
  - exists boom. ss.
Qed.

Definition black `{M: URA.t} (a: M): t M := excl a ε.
Definition white `{M: URA.t} (a: M): t M := frag a.

Definition local_update `{M: URA.t} a0 b0 a1 b1: Prop :=
  forall ctx, (<<WF: URA.wf a0>> /\ <<FRAME: a0 = URA.add b0 ctx>>) ->
              (<<WF: URA.wf a1>> /\ <<FRAME: a1 = URA.add b1 ctx>>)
.

Theorem auth_update
        `{M: URA.t}
        a b a' b'
        (UPD: local_update a b a' b')
  :
    <<UPD: URA.updatable ((black a) ⋅ (white b)) ((black a') ⋅ (white b'))>>
.
Proof.
  (* rr. ur. ii; des_ifs. unseal "ra". des. *)
  rr. rewrite URA.unfold_add, URA.unfold_wf in *. ii. unseal "ra". ss. des_ifs. des.
  r in UPD. r in H. des; clarify. r in H. des; clarify.
  rewrite URA.unit_idl in *. ss.
  exploit (UPD (f ⋅ ctx)); eauto.
  { esplits; eauto. rewrite URA.add_assoc. ss. }
  i; des. clarify. esplits; eauto. rr. exists ctx. rewrite URA.add_assoc. ss.
Qed.

Theorem auth_dup_black
        `{M: URA.t}
        a ca
        (CORE: a = a ⋅ ca)
  :
    <<DUP: URA.updatable (t:=t M) (black a) ((black a) ⋅ (white ca))>>
.
Proof.
  (* r. rewrite <- unit_id at 1. *)
  (* eapply auth_update. rr. ii. des. rewrite unit_idl in FRAME. subst. *)
  (* esplits; eauto. rewrite add_comm; ss. *)
  rr. rewrite URA.unfold_add, URA.unfold_wf in *. ii. ss. des_ifs. unseal "ra". ss. des.
  rr in H. des. rewrite URA.unit_idl in *. esplits; eauto.
  rewrite CORE. eexists. rewrite <- URA.add_assoc. rewrite H. rewrite URA.add_comm. eauto.
Qed.

Theorem auth_dup_white
        `{M: URA.t}
        a ca
        (CORE: a = a ⋅ ca)
  :
    <<DUP: URA.updatable (t:=t M) (white a) ((white a) ⋅ (white ca))>>
.
Proof.
  rr. rewrite URA.unfold_add, URA.unfold_wf in *. ii. unseal "ra". ss. des_ifs.
  - ss. rewrite <- CORE. ss.
  - ss. des. esplits; eauto. rewrite <- CORE. ss.
Qed.

Theorem auth_alloc
        `{M: URA.t}
        a0 a1 b1
        (UPD: local_update a0 ε a1 b1)
  :
    <<UPD: URA.updatable (t:=t M) (black a0) ((black a1) ⋅ (white b1))>>
.
Proof.
  r. rewrite <- URA.unit_id at 1. ss. eapply auth_update. ss.
Qed.

Theorem auth_alloc2
        `{M: URA.t}
        a0 delta
        (WF: URA.wf (a0 ⋅ delta))
  :
    <<UPD: URA.updatable (t:=t M) (black a0) ((black (a0 ⋅ delta)) ⋅ (white delta))>>
.
Proof.
  rr. rewrite URA.unfold_add, URA.unfold_wf in *.
  ii. unseal "ra". ss. des_ifs. subst add wf. ss. des.
  esplits; eauto.
  rewrite URA.unit_idl in *.
  rr in H. des. rr. exists ctx; eauto. ss. clarify.
  rewrite URA.add_comm. rewrite (URA.add_comm f). rewrite <- URA.add_assoc. f_equal.
  rewrite URA.add_comm. ss.
Qed.

Theorem auth_dealloc
        `{M: URA.t}
        a0 a1 b0
        (UPD: local_update a0 b0 a1 ε)
  :
    <<UPD: URA.updatable (t:=t M) ((black a0) ⋅ (white b0)) (black a1)>>
.
Proof.
  r. rewrite <- URA.unit_id. ss. eapply auth_update. ss.
Qed.

Theorem auth_included
        `{M: URA.t}
        a b
        (WF: URA.wf ((black a) ⋅ (white b)))
  :
    <<EXT: URA.extends b a>>
.
Proof.
  rewrite URA.unfold_add in WF; rewrite URA.unfold_wf in WF.
  rr in WF. des. rr in WF. rr. des. rewrite URA.unit_idl in WF. subst. esplits; eauto.
Qed.

Theorem auth_exclusive
        `{M: URA.t}
        a b
        (WF: URA.wf ((black a) ⋅ (black b)))
  :
    False
.
Proof. rewrite URA.unfold_add in WF; rewrite URA.unfold_wf in WF. ss. Qed.

Lemma black_wf
      `{M: URA.t}
      a
      (WF: URA.wf (black a))
  :
    <<WF: URA.wf a>>
.
Proof. ur in WF. des; ss. Qed.
End AUTH.
End Auth.

(**********************************************************************************)
(*** For backward compatibility, I put below definitions "outside" Auth module. ***)
(*** TODO: put it inside ***)



































Lemma nth_error_nth
      A (l: list A) n a d
      (NTH: nth_error l n = Some a)
  :
    <<NTH: nth n l d = a>>
.
Proof.
  ginduction n; ii; ss; des_ifs. ss. eapply IHn; eauto.
Qed.





Module GRA.
  Class t: Type := __GRA__INTERNAL__: (nat -> URA.t).
  Class inG (RA: URA.t) (Σ: t) := InG {
    inG_id: nat;
    (* inG_prf: Eq (GRA inG_id) RA; *)
    inG_prf: RA = Σ inG_id;
  }
  .
  Class subG (Σ0 Σ1: t) := SubG i : { j | Σ0 i = Σ1 j }.
  (* Class subG (GRA0 GRA1: t) := SubG { subG_prf: forall i, { j | GRA0 i = GRA1 j } }. *)

  Definition of_list (RAs: list URA.t): t := fun n => List.nth n RAs (of_RA.t RA.empty).

  Definition to_URA (Σ: t): URA.t := URA.pointwise_dep Σ.

  Coercion to_URA: t >-> URA.t.

  Let cast_ra {A B: URA.t} (LeibEq: A = B) (a: URA.car (t:=A)): URA.car (t:=B) :=
    eq_rect A (@URA.car) a _ LeibEq.

  (* a: URA.car =ty= RAs inG_id =ty= RAs n *)
  Definition embed {A Σ} `{@GRA.inG A Σ} (a: URA.car (t:=A)): URA.car (t:=Σ) :=
    fun n => match Nat.eq_dec inG_id n with
             | left H => ((@eq_rect nat inG_id Σ ((cast_ra inG_prf a): Σ inG_id) n H): Σ n)
             | right _ => URA.unit
             end
  .

  Lemma embed_wf
        A Σ
        `{@GRA.inG A Σ}
        (a: A)
        (WF: URA.wf (embed a))
    :
      <<WF: URA.wf a>>
  .
  Proof.
    rewrite URA.unfold_wf in WF.
    r. specialize (WF inG_id). ss. unfold embed in *. des_ifs.
    unfold cast_ra in *. unfold eq_rect, eq_sym in *. dependent destruction e. destruct inG_prf. ss.
  Qed.

  Lemma wf_embed
        A Σ
        `{@GRA.inG A Σ}
        (a: A)
        (WF: URA.wf a)
    :
      <<WF: URA.wf (embed a)>>
  .
  Proof.
    destruct H. subst. rewrite URA.unfold_wf.
    r. ii. unfold embed. des_ifs.
    eapply URA.wf_unit.
  Qed.

  Lemma embed_add
        A Σ
        `{@GRA.inG A Σ}
        (a0 a1: A)
    :
      <<EQ: URA.add (embed a0) (embed a1) = embed (URA.add a0 a1)>>
  .
  Proof.
    rewrite URA.unfold_add in *.
    r. ss. unfold embed. apply func_ext_dep. i. des_ifs.
    - ss. unfold cast_ra. unfold eq_rect, eq_sym. destruct inG_prf. reflexivity.
    - rewrite URA.unit_id. ss.
  Qed.

  Lemma embed_updatable
        A Σ
        `{@GRA.inG A Σ}
        (a0 a1: A)
        (UPD: URA.updatable a0 a1)
    :
      <<UPD: URA.updatable (GRA.embed a0) (GRA.embed a1)>>
  .
  Proof.
    r in UPD. ii. ss.
    rewrite URA.unfold_add in *. rewrite URA.unfold_wf in *. ss. ii.
    rename H0 into WF.
    specialize (WF k).
    unfold embed in *. des_ifs. ss.
    unfold cast_ra in *. unfold eq_rect, eq_sym in *.
    destruct H. ss.
    dependent destruction inG_prf0.
    eapply UPD. ss.
  Qed.

  Section GETSET.
    Variable ra: URA.t.
    Variable gra: t.
    Context `{@inG ra gra}.

    Section GETSET.
    Variable get: URA.car (t:=ra).
    Variable set: URA.car (t:=ra) -> unit.

    (* own & update can be lifted *)
    (* can we write spec in terms of own & update, not get & set? *)
    (* how about add / sub? *)
    Program Definition get_lifted: URA.car (t:=gra) :=
      fun n => if Nat.eq_dec n inG_id then _ else URA.unit.
    Next Obligation.
      apply (cast_ra inG_prf get).
    Defined.

    (* Program Definition set_lifted: URA.car (t:=construction gra) -> unit := *)
    (*   fun n => if Nat.eq_dec n inG_id then _ else URA.unit. *)
    (* Next Obligation. *)
    (*   apply (ra_transport inG_prf get). *)
    (* Defined. *)
    End GETSET.

    Section HANDLER.
    Variable handler: URA.car (t:=ra) -> URA.car (t:=ra).
    Local Obligation Tactic := idtac.
    Program Definition handler_lifted: URA.car (t:=gra) -> URA.car (t:=gra) :=
      fun st0 => fun n => if Nat.eq_dec n inG_id then _ else st0 n
    .
    Next Obligation.
      i. subst. simpl in st0. specialize (st0 inG_id).
      rewrite <- inG_prf in st0. specialize (handler st0). rewrite <- inG_prf. apply handler.
    Defined.

    End HANDLER.

  End GETSET.

  Section CONSTRUCTION.
    Variable RAs: list URA.t.
    Let GRA: t := (fun n => List.nth n RAs RA.empty).
    Theorem construction_adequate: forall n RA (IN: List.nth_error RAs n = Some RA),
        inG RA GRA.
    Proof.
      i. unshelve econs; eauto. unfold GRA. symmetry. eapply nth_error_nth; eauto.
    Qed.

    (* Let GRA2: RA.t := URA.pointwise_dep GRA. *)
    (* Goal @RA.car GRA2 = forall k, (@RA.car (GRA k)). ss. Qed. *)
  End CONSTRUCTION.

  (* Definition extends (RA0 RA1: URA.t): Prop := *)
  (*   exists c, URA.prod RA0 c = RA1 *)
  (* . *)

  Class inG2 (RA GRA: URA.t): Prop := {
    GRA_data: t;
    (* GRA_prf:  *)
    inG2_id: nat;
    inG2_prf: GRA_data inG2_id = RA;
  }
  .

  Fixpoint point_wise_wf (Ml: list URA.t) (x: of_list Ml) (n: nat) :=
  match n with
  | O => True
  | S n' => @URA.wf (of_list Ml n') (x n') /\ @point_wise_wf Ml x n'
  end.

  Definition point_wise_wf_lift (Ml: list URA.t) (x: of_list Ml)
             (POINT: point_wise_wf x (List.length Ml))
    :
      @URA.wf (of_list Ml) x.
  Proof.
    ur. ss. i. unfold of_list in *.
    assert (WF: forall (n m: nat)
                       (POINT: point_wise_wf x n)
                       (LT: (m < n)%nat),
               URA.wf (x m)).
    { induction n.
      { i. inv LT. }
      { i. ss. des. inv LT; auto. }
    }
    destruct (le_lt_dec (List.length Ml) k).
    { generalize (x k). rewrite nth_overflow; auto. i. ur. destruct c; ss. }
    { eapply WF; eauto. }
  Qed.

  Lemma point_add (G: t) (x0 x1: G) n
    :
      (x0 ⋅ x1) n = x0 n ⋅ x1 n.
  Proof.
    ur. ss. ur. auto.
  Qed.
End GRA.
Coercion GRA.to_URA: GRA.t >-> URA.t.

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
Notation " K ==> V' " := (URA.pointwise K V') (at level 80, right associativity): ra_scope.

Section TEST.
  Variable A B C: Type.
  Let _myRA: URA.t := (A ==> B ==> (RA.excl C))%ra.
  Let myRA: URA.t := Auth.t _myRA.
End TEST.

Ltac r_first rs :=
  match rs with
  | (?rs0 ⋅ ?rs1) =>
    let tmp0 := r_first rs0 in
    constr:(tmp0)
  | ?r => constr:(r)
  end
.

Ltac r_solve :=
  repeat rewrite URA.add_assoc;
  repeat (try rewrite URA.unit_id; try rewrite URA.unit_idl);
  match goal with
  | [|- ?lhs = (_ ⋅ _) ] =>
    let a := r_first lhs in
    try rewrite <- (URA.add_comm a);
    repeat rewrite <- URA.add_assoc;
    try (eapply f_equal; r_solve)
  | _ => try reflexivity
  end
.

Lemma prop_ext_rev
      A B
      (EQ: A = B)
  :
    A <-> B
.
Proof. clarify. Qed.

Ltac r_wf H := eapply prop_ext_rev; [eapply f_equal|]; [|eapply H]; r_solve.

Ltac g_wf_tac :=
  cbn; repeat rewrite URA.unit_id; repeat rewrite URA.unit_idl;
  apply GRA.point_wise_wf_lift; ss; splits; repeat rewrite GRA.point_add; unfold GRA.embed; ss;
  repeat rewrite URA.unit_id; repeat rewrite URA.unit_idl; try apply URA.wf_unit.

Global Opaque URA.unit.
