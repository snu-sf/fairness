From sflib Require Import sflib.
From Coq Require Import Program.
From Fairness Require Import Axioms.

Set Implicit Arguments.

Tactic Notation "hspecialize" hyp(H) "with" uconstr(x) :=
  apply (fun H => equal_f H x) in H.

Tactic Notation "cong" uconstr(f) "in" hyp(H) :=
  eapply (f_equal f) in H.

Module Store.

  Definition t S A := (S * (S -> A))%type.

  Definition map {S A B} : (A -> B) -> t S A -> t S B :=
    fun ϕ x => (fst x, ϕ ∘ snd x).

  Definition counit {S A} : t S A -> A :=
    fun x => snd x (fst x).

  Definition cojoin {S A} : t S A -> t S (t S A) :=
    fun x => (fst x, fun a' => (a', snd x)).

End Store.

Module Lens.

  (* Lens is just a coalgebra of the Store comonad *)

  Record isLens {S V} (l : S -> Store.t V S) : Prop :=
    { counit : Store.counit ∘ l = id
    ; coaction : Store.map l ∘ l = Store.cojoin ∘ l
    }.

  Definition t S V := {l : S -> Store.t V S | isLens l}.

  Definition view {S V} : t S V -> S -> V := fun l s => fst (`l s).
  Definition set {S V} : t S V -> V -> S -> S := fun l a s => snd (`l s) a.
  Definition modify {S V} : t S V -> (V -> V) -> (S -> S) := fun l f s => Lens.set l (f (Lens.view l s)) s.

  Lemma view_set {S V} (l : t S V) : forall v s, view l (set l v s) = v.
  Proof.
    destruct l as [l [H1 H2]]. unfold view, set; ss.
    i. hspecialize H2 with s. cong snd in H2. hspecialize H2 with v. ss.
    unfold compose in H2. rewrite H2. ss.
  Qed.

  Lemma set_view {S V} (l : t S V) : forall s, set l (view l s) s = s.
  Proof.
    destruct l as [l [H1 H2]]. unfold view, set; ss.
    i. hspecialize H1 with s. ss.
  Qed.

  Lemma set_set {S V} (l : t S V) : forall v v' s, set l v' (set l v s) = set l v' s.
  Proof.
    destruct l as [l [H1 H2]]. unfold view, set; ss.
    i. hspecialize H2 with s. cong snd in H2. hspecialize H2 with v. ss.
    unfold compose in H2. rewrite H2. ss.
  Qed.

  Lemma view_modify {S V} (l : t S V) : forall f s, view l (modify l f s) = f (view l s).
  Proof.
    i. unfold modify. apply view_set.
  Qed.

  Program Definition id {S} : Lens.t S S :=
    exist _ (fun s => (s, fun s' => s')) _.
  Next Obligation.
    constructor; ss.
  Qed.

  Program Definition compose {A B C} (l1: t A B) (l2: t B C): t A C :=
    exist _ (fun a => (view l2 (view l1 a), fun c => set l1 (set l2 c (view l1 a)) a)) _.
  Next Obligation.
    constructor.
    - extensionalities s. cbn. rewrite ! set_view. ss.
    - extensionalities s. unfold Store.map, Store.cojoin, compose; ss. f_equal.
      extensionalities c. f_equal.
      + rewrite ! view_set. ss.
      + extensionalities c'. rewrite view_set, ! set_set. ss.
  Qed.

  Lemma left_unit A B (l : t A B):
    (compose id l) = l.
  Proof.
    eapply eq_sig_hprop.
    - i. eapply proof_irrelevance.
    - ss. extensionality a. eapply injective_projections; ss.
  Qed.

  Lemma right_unit A B (l : t A B):
    (compose l id) = l.
  Proof.
    eapply eq_sig_hprop.
    - i. eapply proof_irrelevance.
    - ss. extensionality a. eapply injective_projections; ss.
  Qed.

  Lemma compose_assoc A B C D (l1 : t A B) (l2 : t B C) (l3 : t C D) :
    (compose (compose l1 l2) l3) = compose l1 (compose l2 l3).
  Proof.
    eapply eq_sig_hprop.
    - i. eapply proof_irrelevance.
    - ss.
  Qed.

  Definition Disjoint {S V1 V2} (l1 : t S V1) (l2 : t S V2) : Prop :=
    forall s v1 v2, set l2 v2 (set l1 v1 s) = set l1 v1 (set l2 v2 s).

End Lens.

Module Prism.

  Set Implicit Arguments.

  Record isPrism {S A} (p : (A -> S) * (S -> option A)) : Prop :=
    { _preview_review : forall a, snd p (fst p a) = Some a
    ; _review_preview : forall s a, snd p s = Some a -> fst p a = s
    }.

  Definition t S A := { p : (A -> S) * (S -> option A) | isPrism p }.

  Definition review {S A} (p : t S A) : A -> S := fst (`p).
  Definition preview {S A} (p : t S A) : S -> option A := snd (`p).

  Lemma preview_review S A (p : t S A) a : preview p (review p a) = Some a.
  Proof. unfold review, preview. eapply _preview_review. destruct p; ss. Qed.

  Lemma review_preview S A (p : t S A) s a : preview p s = Some a -> review p a = s.
  Proof. unfold review, preview. eapply _review_preview. destruct p; ss. Qed.

  Lemma review_inj S A (p : t S A)
        a0 a1 (EQ: review p a0 = review p a1)
    :
    a0 = a1.
  Proof.
    eapply f_equal with (f:=preview p) in EQ.
    rewrite ! preview_review in EQ. clarify.
  Qed.

  Program Definition id {S} : Prism.t S S :=
    exist _ (id, Some) _.
  Next Obligation.
    constructor; ss. i. clarify.
  Qed.

  Program Definition compose {A B C} (p1: t A B) (p2: t B C): t A C :=
    exist _ (review p1 ∘ review p2, (fun a : A =>
                                       match @preview A B p1 a return (option C) with
                                       | Some b => @preview B C p2 b
                                       | None => @None C
                                       end)) _.
  Next Obligation.
    constructor.
    - i. unfold compose; ss. rewrite ! preview_review. ss.
    - i. unfold compose; ss. des_ifs.
      eapply review_preview in Heq. eapply review_preview in H. subst; ss.
  Qed.

  Lemma left_unit A B (p : t A B):
    (compose id p) = p.
  Proof.
    eapply eq_sig_hprop.
    - i. eapply proof_irrelevance.
    - ss. eapply injective_projections; ss.
  Qed.

  Lemma right_unit A B (p : t A B):
    (compose p id) = p.
  Proof.
    eapply eq_sig_hprop.
    - i. eapply proof_irrelevance.
    - ss. eapply injective_projections; ss.
      extensionality a. des_ifs.
  Qed.

  Lemma compose_assoc A B C D (l1 : t A B) (l2 : t B C) (l3 : t C D) :
    (compose (compose l1 l2) l3) = compose l1 (compose l2 l3).
  Proof.
    eapply eq_sig_hprop.
    - i. eapply proof_irrelevance.
    - ss. eapply injective_projections; ss.
      extensionality a. unfold preview. ss. unfold preview.
      des_ifs; ss.
  Qed.

End Prism.

Declare Scope lens_scope.
Declare Scope prism_scope.
Delimit Scope lens_scope with lens.
Delimit Scope prism_scope with prism.
Infix "⋅" := (Lens.compose) (at level 50, left associativity) : lens_scope.
Infix "⋅" := (Prism.compose) (at level 50, left associativity) : prism_scope.

Section DISJOINT_LENS.

  Context {S V1 V2 : Type}.
  Variable (l1 : Lens.t S V1).
  Variable (l2 : Lens.t S V2).

  Program Definition prodl (DISJ: Lens.Disjoint l1 l2): Lens.t S (V1 * V2) :=
    exist _ (fun s => ((Lens.view l1 s, Lens.view l2 s), fun '(v1, v2) => Lens.set l2 v2 (Lens.set l1 v1 s))) _.
  Next Obligation.
    constructor.
    - extensionalities x. unfold compose. ss. rewrite ! Lens.set_view. ss.
    - extensionalities x. unfold Store.map, Store.cojoin, compose. ss. f_equal.
      extensionalities v. destruct v as [v1 v2]. f_equal.
      + rewrite Lens.view_set. rewrite DISJ. rewrite Lens.view_set. ss.
      + extensionalities u. destruct u as [u1 u2].
        rewrite DISJ. rewrite Lens.set_set.
        rewrite DISJ. rewrite Lens.set_set. ss.
  Qed.

End DISJOINT_LENS.

Section PRISM_LENS.

  Program Definition prisml {S A T} (p: Prism.t S A): Lens.t (S -> T) (A -> T) :=
    exist _ (fun f => (fun a => f (Prism.review p a), (fun (g : A -> T) (s : S) =>
                                                         match @Prism.preview S A p s return T with
                                                         | Some a => g a
                                                         | None => f s
                                                         end))) _.
  Next Obligation.
    constructor.
    - unfold Store.counit, compose; ss. extensionalities f s.
      des_ifs. eapply Prism.review_preview in Heq. rewrite Heq. ss.
    - unfold Store.map, Store.cojoin, compose; ss. extensionalities f.
      f_equal. extensionalities g. f_equal.
      + extensionalities a. rewrite Prism.preview_review. ss.
      + extensionalities g' s. des_ifs.
  Qed.

End PRISM_LENS.

Section PRODUCT_LENS.

  Context {A B : Type}.

  Program Definition fstl : Lens.t (A * B) A :=
    exist _ (fun x => (fst x, fun a => (a, snd x))) _.
  Next Obligation.
    constructor.
    - extensionalities x. destruct x; ss.
    - ss.
  Qed.

  Program Definition sndl : Lens.t (A * B) B :=
    exist _ (fun x => (snd x, fun b => (fst x, b))) _.
  Next Obligation.
    constructor.
    - extensionalities x. destruct x; ss.
    - ss.
  Qed.

  Lemma Disjoint_fstl_sndl : Lens.Disjoint fstl sndl.
  Proof. ss. Qed.

End PRODUCT_LENS.

Section SUM_PRISM.

  Context {A B : Type}.

  Definition is_inl : A + B -> option A :=
    fun x =>
      match x with
      | inl a => Some a
      | inr _ => None
      end.

  Definition is_inr : A + B -> option B :=
    fun x =>
      match x with
      | inl _ => None
      | inr b => Some b
      end.

  Program Definition inlp : Prism.t (A + B) A :=
    exist _ (inl, is_inl) _.
  Next Obligation.
    constructor.
    - ss.
    - i. destruct s; ss. inv H; ss.
  Qed.

  Program Definition inrp : Prism.t (A + B) B :=
    exist _ (inr, is_inr) _.
  Next Obligation.
    constructor.
    - ss.
    - i. destruct s; ss. inv H; ss.
  Qed.

End SUM_PRISM.

Section TEST.

  Let lens1 : Lens.t ((nat * nat) * nat) nat := (fstl ⋅ fstl)%lens.
  Let lens2 : Lens.t ((nat * nat) * nat) nat := (fstl ⋅ sndl)%lens.
  Let lens3 : Lens.t ((nat * nat) * nat) nat := sndl.
  Goal Lens.view lens1 (1,2,3) = 1. reflexivity. Qed.
  Goal Lens.view lens2 (1,2,3) = 2. reflexivity. Qed.
  Goal Lens.view lens3 (1,2,3) = 3. reflexivity. Qed.
  Goal Lens.set lens1 4 (1,2,3) = (4,2,3). reflexivity. Qed.
  Goal Lens.set lens2 4 (1,2,3) = (1,4,3). reflexivity. Qed.
  Goal Lens.set lens3 4 (1,2,3) = (1,2,4). reflexivity. Qed.
  Goal Lens.modify lens3 (fun x => x+1) (1,2,3) = (1,2,4). reflexivity. Qed.

End TEST.
