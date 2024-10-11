From stdpp Require Import coPset gmap namespaces.
From sflib Require Import sflib.
From iris Require Import bi.big_op.
From iris Require base_logic.lib.invariants.
From Coq Require Import Program Arith.
Require Import Coqlib PCM PCMAux  IPM.
(* Require Import PropExtensionality. *)

Module HRA.

  Section HRA.

  Class t := __HRA_INTERNAL : GRA.t.

  Class subG (Γ: t) (Σ: GRA.t) : Type := {
    subG_map: nat -> nat;
    subG_prf: forall i, Σ (subG_map i) = Γ i;
  }.

  Coercion subG_map: subG >-> Funclass.

  Context `{Γ: t}.
  Context `{Σ: GRA.t}.
  Context `{sub: @subG Γ Σ}.

  Global Program Instance embed (i:nat) : @GRA.inG (Γ i) Σ := {
      inG_id := sub i;
    }.
  Next Obligation. i. symmetry. apply HRA.subG_prf. Qed.

  Global Program Instance in_subG `{M: ucmra} `{emb: @GRA.inG M Γ} : @GRA.inG M Σ := {
      inG_id := sub.(subG_map) emb.(GRA.inG_id);
      }.
  Next Obligation.
    i. destruct emb. subst. destruct sub. ss.
  Qed.

  (* Definition embed `{Γ: GRA.t} `{Σ: GRA.t} `{m: @subG Γ Σ} (r: Σ) : Γ := *)
  (*   fun i => eq_rect _ (@URA.car) (r (m i)) _ (m.(subG_prf) i). *)

  (* Lemma embed_wf `{Γ: GRA.t} `{Σ: GRA.t} `{m: @subG Γ Σ} (r: Σ) *)
  (*     (WF: URA.wf r): *)
  (*   URA.wf (embed r). *)
  (* Proof. *)
  (*   Local Transparent GRA.to_URA. *)
  (*   revert WF. unfold URA.wf, embed. unseal "ra". ss. *)
  (*   i. specialize (WF (m k)). revert WF. *)
  (*   rewrite <-(m.(subG_prf) k). ss. *)
  (* Qed. *)

  (* Lemma embed_extends `{Γ: GRA.t} `{Σ: GRA.t} `{m: @subG Γ Σ} (r0 r1: Σ) *)
  (*     (EXT: URA.extends r0 r1): *)
  (*   URA.extends (embed r0) (embed r1). *)
  (* Proof. *)
  (*   Local Transparent GRA.to_URA. *)
  (*   rr in EXT. des. subst. exists (embed ctx). extensionality k. *)
  (*   unfold embed, URA.add. unseal "ra". simpl. *)
  (*   rewrite <-(m.(subG_prf) k). ss. *)
  (* Qed. *)

  (* Program Definition lift `{Γ: GRA.t} `{Σ: GRA.t} `{m: @subG Γ Σ} (P: @iProp Γ): @iProp Σ := *)
  (*   iProp_intro (fun r => P (embed r)) _. *)
  (* Next Obligation. *)
  (*   i. ss. eapply iProp_mono; eauto using embed_wf, embed_extends. *)
  (* Qed. *)

  (* Lemma iprop_extensionality `{Σ: GRA.t} (P Q: iProp) *)
  (*     (EQ: iProp_pred P = iProp_pred Q): *)
  (*   P = Q. *)
  (* Proof. *)
  (*   destruct P eqn: EQP. subst. *)
  (*   destruct Q eqn: EQQ. subst. *)
  (*   ss. subst. f_equal. eapply proof_irrelevance. *)
  (* Qed. *)

  (* Lemma lift_ownM `{Γ: GRA.t} `{Σ: GRA.t} `{sub: @subG Γ Σ} {M: ucmra} {emb: @GRA.inG M Γ} (m: M): *)
  (*   lift (@OwnM Γ M emb m) = @OwnM Σ M (in_subG sub emb) m. *)
  (* Proof. *)
  (*   Local Transparent GRA.to_URA. *)
  (*   apply iprop_extensionality. ss. *)
  (*   extensionality i. unfold OwnM, embed, Own, URA.extends. uiprop. *)
  (*   destruct emb, sub. subst. *)
  (*   rename i into r. apply propositional_extensionality. split; i; des. *)
  (*   - exists (fun k => *)
  (*               match Nat.eq_dec (subG_map0 inG_id) k with *)
  (*               | left H => *)
  (*                   eq_rect _ (fun k => @URA.car (Σ k)) *)
  (*                   (eq_rect_r (@URA.car) (ctx inG_id) (subG_prf0 inG_id)) _ H *)
  (*               | _ => r k *)
  (*               end). *)
  (*     extensionality k. ss. *)
  (*     assert (EQ:= equal_f_dep H inG_id). clear H. *)
  (*     unfold URA.add in *. unseal "ra". ss. *)
  (*     unfold GRA.embed in *. ss. des_ifs; r_solve. ss. *)
  (*     unfold URA.add in *. unseal "ra". unfold PCM.GRA.cast_ra. clear Heq. *)
  (*     revert EQ. rewrite (UIP_refl _ _ e). ss. clear e. *)
  (*     rewrite (UIP_refl _ _ e0). ss. clear e0. *)
  (*     generalize (in_subG_obligation_1 Γ Σ (Γ inG_id)  *)
  (*         {| subG_map := subG_map0; subG_prf := subG_prf0 |} *)
  (*         {| GRA.inG_id := inG_id; GRA.inG_prf := eq_refl |}). *)
  (*     generalize (subG_prf0 inG_id). ss. *)
  (*     unfold eq_rect_r. i. rewrite (UIP _ _ _ (eq_sym e) e0). *)
  (*     revert_until r. generalize (subG_map0 inG_id) as j. *)
  (*     intros j. generalize (r j) as r'. clear r. *)
  (*     generalize (Σ j) as A. clear j. clear Σ subG_prf0 subG_map0. *)
  (*     i. subst. rewrite (UIP_refl _ _ e0). ss. *)
  (*   - ss.       *)
  (*     exists (fun k => *)
  (*               match Nat.eq_dec inG_id k with *)
  (*               | left H => eq_rect _ (@URA.car) (ctx (subG_map0 k)) _ (subG_prf0 k)  *)
  (*               | _ => eq_rect _ (@URA.car) (r (subG_map0 k)) _ (subG_prf0 k) *)
  (*               end). *)
  (*     extensionality k. *)
  (*     assert (EQ:= equal_f_dep H (subG_map0 inG_id)). clear H. *)
  (*     unfold URA.add in *. unseal "ra". ss. *)
  (*     unfold GRA.embed in *. ss. des_ifs; r_solve. ss. *)
  (*     unfold URA.add in *. unseal "ra". clear Heq e. *)
  (*     revert EQ. unfold PCM.GRA.cast_ra. *)
  (*     rewrite (UIP_refl _ _ e0). ss. clear e0. *)
  (*     generalize (in_subG_obligation_1 Γ Σ (Γ k) *)
  (*         {| subG_map := subG_map0; subG_prf := subG_prf0 |} *)
  (*         {| GRA.inG_id := k; GRA.inG_prf := eq_refl |}). ss. *)
  (*     generalize (subG_prf0 k). generalize (subG_map0 k). *)
  (*     intros j. generalize (r j) as r'. clear r. revert m. *)
  (*     generalize (ctx j). clear ctx. *)
  (*     generalize (Σ j) as A. clear j. i. subst. *)
  (*     rewrite (UIP_refl _ _ e0). ss. *)
  (* Qed. *)

  End HRA.

End HRA.

Coercion HRA.subG_map: HRA.subG >-> Funclass.

Module sAtom.

  Class t: Type := car : forall (sProp: Type), Type.

End sAtom.

Module sType.

  Class t : Type := mk {
    car: Type;
    interp: car -> forall sProp: Type, Type;
  }.

End sType.

Coercion sType.car: sType.t >-> Sortclass.

Local Notation level := nat.

Module sProp.

  Section SYNTAX.

  Context `{τ: sType.t}.
  Context `{Γ: HRA.t}.
  Context `{A : Type}.

  Inductive t {sProp : Type} : Type :=
  | ownm i (r : Γ i) : t
  | atom (a : A) : t
  | lift (p : sProp) : t
  | pure (P : Prop) : t
  | and (p q : t) : t
  | or  (p q : t) : t
  | impl (p q : t) : t
  | univ (ty : τ) (p: τ.(sType.interp) ty sProp -> t) : t
  | ex   (ty : τ) (p: τ.(sType.interp) ty sProp -> t) : t
  | empty : t
  | sepconj (p q : t) : t
  | wand (p q : t) : t
  | persistently (p : t) : t
  | plainly (p : t) : t
  | upd (p : t) : t
  .

  End SYNTAX.

  Section SPROP.

  Context `{τ: sType.t}.
  Context `{Γ: HRA.t}.
  Context `{As : sAtom.t}.

  Fixpoint _sProp (n : level) : Type :=
    match n with
    | O => Empty_set
    | S m => @t _ _ (As (_sProp m)) (_sProp m)
    end.

  Definition sProp (n : level) : Type := _sProp (S n).

  Fixpoint liftn n {m} (p: sProp m) : sProp (n+m) :=
    match n return sProp (n+m) with
    | 0 => p
    | S n' => lift (liftn n' p)
    end.

  Definition affinely {n} (p : sProp n) : sProp n :=
    and empty p.

  Definition ownM `{IN: @GRA.inG M Γ} {n} (r: M) : sProp n :=
    ownm IN.(GRA.inG_id) (eq_rect _ (@URA.car) r _ IN.(GRA.inG_prf)).

  End SPROP.

End sProp.

Module SAtom.

  Section SATOM.

  Context `{τ: sType.t}.
  Context `{Γ: HRA.t}.
  Context `{As: sAtom.t}.
  Context `{Σ: GRA.t}.

  Class t : Type := interp :
      forall (n:level), As (sProp._sProp n) -> iProp.

  End SATOM.

End SAtom.

Module sPropI.

  Section INTERP.

  Context `{sub: @HRA.subG Γ Σ}.
  Context `{α: SAtom.t (Γ:=Γ) (Σ:=Σ)}.

  Import sProp.

  Fixpoint _interp n : _sProp n -> iProp :=
    match n with
    | O => fun _ => ⌜False⌝%I
    | S m => fix _interp_aux (syn : _sProp (S m)) : iProp :=
      match syn with
      | ownm i a => OwnM a
      | atom a => α m a
      | lift p => _interp m p
      | pure P => Pure P
      | and p q => And (_interp_aux p) (_interp_aux q)
      | or p q => Or (_interp_aux p) (_interp_aux q)
      | impl p q => Impl (_interp_aux p) (_interp_aux q)
      | univ ty p => Univ (fun x => _interp_aux (p x))
      | ex ty p => Ex (fun x => _interp_aux (p x))
      | empty => Emp
      | sepconj p q => Sepconj (_interp_aux p) (_interp_aux q)
      | wand p q => Wand (_interp_aux p) (_interp_aux q)
      | persistently p => Persistently (_interp_aux p)
      | plainly p => .Plainly (_interp_aux p)
      | upd p => Upd (_interp_aux p)
      end
    end.

  Definition interp n : sProp n -> iProp := _interp (S n).

  End INTERP.

End sPropI.

Section RED.

  Context `{sub: @HRA.subG Γ Σ}.
  Context `{α: SAtom.t (Γ:=Γ) (Σ:=Σ)}.

  Import sProp.
  Import sPropI.

  Lemma red_sem_ownm n i a :
    interp n (ownm i a) = OwnM a.
  Proof. reflexivity. Qed.

  Lemma red_sem_ownM `{@GRA.inG M Γ} n (r: M) :
    interp n (ownM r) = OwnM r.
  Proof.
    unfold ownM. rewrite red_sem_ownm.
    destruct sub eqn: EQsub. subst. destruct H. subst. ss.
    f_equal. unfold HRA.in_subG, HRA.embed. ss.
    erewrite (UIP _ _ _ (HRA.embed_obligation_1 inG_id)).
    reflexivity.
  Qed.

  Lemma red_sem_atom n a :
    interp n (atom a) = α n a.
  Proof. reflexivity. Qed.

  Lemma red_sem_lift_0 p :
    interp 0 (lift p) = ⌜False⌝%I.
  Proof. reflexivity. Qed.

  Lemma red_sem_lift n p :
    interp (S n) (lift p) = interp n p.
  Proof. reflexivity. Qed.

  Lemma red_sem_pure n P :
    interp n (pure P) = ⌜P⌝%I.
  Proof. reflexivity. Qed.

  Lemma red_sem_and n p q :
    interp n (and p q) = (interp n p ∧ interp n q)%I.
  Proof. reflexivity. Qed.

  Lemma red_sem_or n p q :
    interp n (or p q) = (interp n p ∨ interp n q)%I.
  Proof. reflexivity. Qed.

  Lemma red_sem_impl n p q :
    interp n (impl p q) = (interp n p → interp n q)%I.
  Proof. reflexivity. Qed.

  Lemma red_sem_univ n ty p :
    interp n (univ ty p) = (∀ x, interp n (p x))%I.
  Proof. reflexivity. Qed.

  Lemma red_sem_ex n ty p :
    interp n (ex ty p) = (∃ x, interp n (p x))%I.
  Proof. reflexivity. Qed.

  Lemma red_sem_empty n :
    interp n empty = emp%I.
  Proof. reflexivity. Qed.

  Lemma red_sem_sepconj n p q :
    interp n (sepconj p q) = (interp n p ∗ interp n q)%I.
  Proof. reflexivity. Qed.

  Lemma red_sem_wand n p q :
    interp n (wand p q) = (interp n p -∗ interp n q)%I.
  Proof. reflexivity. Qed.

  Lemma red_sem_persistently n p :
    interp n (persistently p) = (<pers> interp n p)%I.
  Proof. reflexivity. Qed.

  Lemma red_sem_plainly n p :
    interp n (plainly p) = (.Plainly (interp n p))%I.
  Proof. reflexivity. Qed.

  Lemma red_sem_upd n p :
    interp n (upd p) = (#=> interp n p)%I.
  Proof. reflexivity. Qed.

  Lemma red_sem_affinely n p :
    interp n (affinely p) = (<affine> interp n p)%I.
  Proof. reflexivity. Qed.

  Lemma red_sem_intuitionistically n p :
    interp n (affinely (persistently p)) = (□ interp n p)%I.
  Proof. reflexivity. Qed.

End RED.

Global Opaque sPropI.interp.

(* Simple sProp reduction tactics. *)
Ltac red_sem_binary_once := (try rewrite ! @red_sem_sepconj;
                             try rewrite ! @red_sem_and;
                             try rewrite ! @red_sem_or;
                             try rewrite ! @red_sem_impl;
                             try rewrite ! @red_sem_wand
                            ).

Ltac red_sem_unary_once := (try rewrite ! @red_sem_atom;
                            try rewrite ! @red_sem_ownm;
                            try rewrite ! @red_sem_lift;
                            try rewrite ! @red_sem_pure;
                            try rewrite ! @red_sem_univ;
                            try rewrite ! @red_sem_ex;
                            try rewrite ! @red_sem_empty;
                            try rewrite ! @red_sem_persistently;
                            try rewrite ! @red_sem_plainly;
                            try rewrite ! @red_sem_upd;
                            try rewrite ! @red_sem_affinely;
                            try rewrite ! @red_sem_intuitionistically
                           ).

Ltac red_sem_binary := repeat red_sem_binary_once.
Ltac red_sem_unary := repeat red_sem_unary_once.
Ltac red_sem := repeat (red_sem_binary; red_sem_unary).

Ltac red_sem_binary_once_every := (try rewrite ! @red_sem_sepconj in *;
                                   try rewrite ! @red_sem_and in *;
                                   try rewrite ! @red_sem_or in *;
                                   try rewrite ! @red_sem_impl in *;
                                   try rewrite ! @red_sem_wand in *
                                  ).

Ltac red_sem_unary_once_every := (try rewrite ! @red_sem_atom in *;
                                  try rewrite ! @red_sem_ownm in *;
                                  try rewrite ! @red_sem_lift in *;
                                  try rewrite ! @red_sem_pure in *;
                                  try rewrite ! @red_sem_univ in *;
                                  try rewrite ! @red_sem_ex in *;
                                  try rewrite ! @red_sem_empty in *;
                                  try rewrite ! @red_sem_persistently in *;
                                  try rewrite ! @red_sem_plainly in *;
                                  try rewrite ! @red_sem_upd in *;
                                  try rewrite ! @red_sem_affinely in *;
                                  try rewrite ! @red_sem_intuitionistically in *
                                 ).

Ltac red_sem_binary_every := repeat red_sem_binary_once.
Ltac red_sem_unary_every := repeat red_sem_unary_once.
Ltac red_sem_every := repeat (red_sem_binary_every; red_sem_unary_every).

(** Notations *)

Declare Scope sProp_scope.
Delimit Scope sProp_scope with F.
Bind Scope sProp_scope with sProp.sProp.

Local Open Scope sProp_scope.

Notation "'⌜' P '⌝'" := (sProp.pure P) : sProp_scope.
Notation "'⊤'" := ⌜True⌝ : sProp_scope.
Notation "'⊥'" := ⌜False⌝ : sProp_scope.

Notation "'<ownm>' r" := (sProp.ownM r) (at level 20) : sProp_scope.
Notation "'⟨' A '⟩'" := (sProp.atom A) : sProp_scope.
Notation "⤉ P" := (sProp.lift P) (at level 20) : sProp_scope.

Notation "'<pers>' P" := (sProp.persistently P) : sProp_scope.
Notation "'<affine>' P" := (sProp.affinely P) : sProp_scope.
Notation "□ P" := (<affine> <pers> P) : sProp_scope.
Notation "■ P" := (sProp.plainly P) : sProp_scope.
Notation "|==> P" := (sProp.upd P) : sProp_scope.
Infix "∧" := (sProp.and) : sProp_scope.
Infix "∨" := (sProp.or) : sProp_scope.
Infix "→" := (sProp.impl) : sProp_scope.
Notation "¬ P" := (P → False) : sProp_scope.
Infix "∗" := (sProp.sepconj) : sProp_scope.
Infix "-∗" := (sProp.wand) : sProp_scope.
Notation "P ==∗ Q" := (P -∗ |==> Q) : sProp_scope.
Notation f_forall A := (sProp.univ A).
Notation "∀'" := (f_forall _) (only parsing) : sProp_scope.
Notation "∀ a .. z , P" := (f_forall _ (λ a, .. (f_forall _ (λ z, P%F)) ..)) : sProp_scope.
Notation f_exist A := (sProp.ex A).
Notation "∃'" := (f_exist _) (only parsing) : sProp_scope.
Notation "∃ a .. z , P" := (f_exist _ (λ a, .. (f_exist _ (λ z, P%F)) ..)) : sProp_scope.
Notation "'emp'" := (sProp.empty) : sProp_scope.

(* Module TestLock. *)

(* Section TESTLOCK. *)

(*   Context `{τ: sType.t}. *)
(*   Context `{Σ : GRA.t}. *)

(*   Variant atm {sProp : Type} : Type := *)
(*     | lock (p: sProp) : atm *)
(*     | unlock (p: sProp) : atm *)
(*   . *)

(*   Instance t : SAtom.t := { *)
(*     car sProp := @atm sProp; *)
(*     interp α n itp p := *)
(*         match p with *)
(*         | lock q => itp q -∗ itp q *)
(*         | unlock q => itp q ∗ itp q *)
(*         end%I *)
(*   }. *)

(* End TESTLOCK. *)

(* End TestLock. *)

(* Require Import RobustIndexedInvariants. *)

(* Module TestOwnI. *)

(* Section TestOwnI. *)

(*   Context `{τ: sType.t}. *)
(*   Context `{Σ: GRA.t}. *)
(*   Context `{@GRA.inG OwnEsRA Σ}. *)
(*   Context `{@GRA.inG (OwnIsRA sProp.sProp) Σ}. *)

(*   Definition xxx (u: positive) (n: nat) (i: positive) : sProp.sProp 0 := *)
(*     (⟨∃ p: iProp, p -∗ OwnI u n i ⟨OwnE u n ∅⟩⟩)%F. *)

(*   Check (sPropSem.interp 0 (xxx 1 0 1)). *)
(*   Check (OwnI 1 0 1 ⟨OwnE 1 0 ∅⟩). *)

(*   Check (∃ p: iProp, p -∗ False)%I. *)

(*   Lemma foo: sPropSem.interp 0 (xxx 1 0 1) = OwnI 1 0 1 ⟨OwnE 1 0 ∅⟩. *)
(*     reflexivity. *)
(*   Qed.   *)


(*   (* Context `{α: GAtom.t}. *) *)

(*   (* Variant atom {sProp : Type} : Type := *) *)
(*   (* | owni (u: positive) (i : positive) (p : sProp.t (sProp:=sProp)) *) *)
(*   (* . *) *)

(*   (* Context `{@GRA.inG (OwnIsRA sProp) Σ}. *) *)

(*   (* Program Instance t : SAtom.t := { *) *)
(*   (*   car sProp := @atom sProp; *) *)
(*   (* }. *) *)
(*   (* Next Obligation. *) *)
(*   (*   intros. destruct X. *) *)
(*   (*   Set Printing All. *) *)
(*   (*   exact (@OwnI _ sProp.sProp _ u n i p). *) *)

(*   (*   interp α n itp p := *) *)
(*   (*     match p with *) *)
(*   (*     | owni u i p => @OwnI _ sProp.sProp _ u _ i p *) *)
(*   (*     end *) *)
(*   (* }. *) *)






(* End TestOwnI. *)

(* End TestOwnI. *)
