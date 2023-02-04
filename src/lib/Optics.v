From sflib Require Import sflib.
From Coq Require Import Program.

Module Store.

  Definition t S A := (S * (S -> A))%type.

  Definition map {S A B} : (A -> B) -> t S A -> t S B :=
    fun ϕ '(a, f) => (a, ϕ ∘ f).

  Definition counit {S A} : t S A -> A :=
    fun '(a, f) => f a.

  Definition cojoin {S A} : t S A -> t S (t S A) :=
    fun '(a, f) => (a, fun a' => (a', f)).

End Store.

Module Lens.

  Definition t S V := S -> Store.t V S.
  Definition view {S V} : t S V -> S -> V := fun l s => fst (l s).
  Definition set {S V} : t S V -> V -> S -> S := fun l a s => snd (l s) a.

  (* Lens is just a coalgebra of the Store comonad *)
  Record isLens {S V} (l : t S V) : Prop :=
    { counit : Store.counit ∘ l = id
    ; coaction : Store.map l ∘ l = Store.cojoin ∘ l
    }.

  Definition compose {A B C} : t A B -> t B C -> t A C.
  Proof.
    intros l1 l2.
    intro a. split.
    - exact (view l2 (view l1 a)).
    - intro c. exact (set l1 (set l2 c (view l1 a)) a).
  Defined.

  Lemma compose_assoc A B C D (l1 : t A B) (l2 : t B C) (l3 : t C D) :
    (compose (compose l1 l2) l3) = compose l1 (compose l2 l3).
  Proof. reflexivity. Qed.

End Lens.

Module Prism.

  Set Implicit Arguments.

  Record t S A :=
    mkPrism
      { review : A -> S
      ; preview : S -> option A
      }.

  Record isPrism {S A} (p : t S A) : Prop :=
    { preview_review : forall a, preview p (review p a) = Some a
    ; review_preview : forall s a, preview p s = Some a -> review p a = s
    }.

End Prism.

Section PRISM_LENS.

  Definition plens {S A} T : Prism.t S A -> Lens.t (S -> T) (A -> T) :=
    fun p f => (fun a => f (Prism.review p a), fun g s => match Prism.preview p s with
                                           | None => f s
                                           | Some a => g a
                                           end).

  Lemma plens_isLens S A T (p : Prism.t S A) : Prism.isPrism p -> Lens.isLens (plens T p).
  Proof.
    i. inv H. econs.
    - unfold Store.counit, plens, compose. extensionalities f s.
      des_ifs. rewrite (review_preview _ _ Heq). ss.
    - unfold Store.map, Store.cojoin, plens, compose.
      extensionalities f. f_equal. extensionalities g. f_equal.
      + extensionalities a. rewrite preview_review. ss.
      + extensionalities g' s. des_ifs.
  Qed.

End PRISM_LENS.

Declare Scope lens_scope.
Delimit Scope lens_scope with lens.
Infix "⋅" := (Lens.compose) (at level 50, left associativity) : lens_scope.

Section PRODUCT_LENS.

  Context {A B : Type}.

  Definition fstl : Lens.t (A * B) A := fun '(a, b) => (a, fun a' => (a', b)).
  Definition sndl : Lens.t (A * B) B := fun '(a, b) => (b, fun b' => (a, b')).

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

  Definition inlp : Prism.t (A + B) A := {| Prism.review := inl; Prism.preview := is_inl |}.
  Definition inrp : Prism.t (A + B) B := {| Prism.review := inr; Prism.preview := is_inr |}.

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

End TEST.
