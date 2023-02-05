From sflib Require Import sflib.
From Coq Require Import Program.

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

  Definition t S V := S -> Store.t V S.
  Definition view {S V} : t S V -> S -> V := fun l s => fst (l s).
  Definition set {S V} : t S V -> V -> S -> S := fun l a s => snd (l s) a.

  (* Lens is just a coalgebra of the Store comonad *)
  Record isLens {S V} (l : t S V) : Prop :=
    { counit : forall s, Store.counit (l s) = s
    ; coaction : forall s, Store.map l (l s) = Store.cojoin (l s)
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

  Lemma view_set {S V} (l : t S V) (H : isLens l) : forall v s, view l (set l v s) = v.
  Proof.
    destruct H as [_ H]. i. specialize (H s). eapply (f_equal snd) in H. cbn in H.
    unfold view, set. eapply equal_f in H. unfold Basics.compose in H. rewrite H. ss.
  Qed.

  Lemma set_view {S V} (l : t S V) (H : isLens l) : forall s, set l (view l s) s = s.
  Proof. firstorder. Qed.

  Lemma set_set {S V} (l : t S V) (H : isLens l) : forall v v' s, set l v' (set l v s) = set l v' s.
  Proof.
    destruct H as [_ H]. i. specialize (H s). eapply (f_equal snd) in H. cbn in H.
    unfold view, set. eapply equal_f in H. unfold Basics.compose in H. rewrite H. ss.
  Qed.

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

  Definition compose {A B C} : t A B -> t B C -> t A C.
  Proof.
    intros p1 p2. split.
    - exact (review p1 ∘ review p2).
    - exact (fun a => match preview p1 a with
                   | Some b => preview p2 b
                   | None => None
                   end).
  Defined.

End Prism.

Declare Scope lens_scope.
Declare Scope prism_scope.
Delimit Scope lens_scope with lens.
Delimit Scope prism_scope with prism.
Infix "⋅" := (Lens.compose) (at level 50, left associativity) : lens_scope.
Infix "⋅" := (Prism.compose) (at level 50, left associativity) : prism_scope.

Section PRISM_COMPOSE.

  Lemma isPrism_compose A B C (p1 : Prism.t A B) (p2 : Prism.t B C) (H1 : Prism.isPrism p1) (H2 : Prism.isPrism p2)
    : Prism.isPrism (p1 ⋅ p2)%prism.
  Proof.
    econs.
    - i. unfold Prism.review, Prism.preview; ss. unfold Basics.compose; ss.
      rewrite Prism.preview_review; eauto. eapply Prism.preview_review; eauto.
    - i. unfold Prism.review, Prism.preview in *; ss. unfold Basics.compose; des_ifs.
      eapply Prism.review_preview in Heq; eauto. eapply Prism.review_preview in H; eauto. subst; ss.
  Qed.

End PRISM_COMPOSE.

Section PRISM_LENS.

  Definition plens {S A} T : Prism.t S A -> Lens.t (S -> T) (A -> T) :=
    fun p f => (fun a => f (Prism.review p a), fun g s => match Prism.preview p s with
                                           | None => f s
                                           | Some a => g a
                                           end).

  Lemma isLens_plens S A T (p : Prism.t S A) : Prism.isPrism p -> Lens.isLens (plens T p).
  Proof.
    i. inv H. econs.
    - unfold Store.counit, plens. intros f. extensionalities s. ss.
      des_ifs. rewrite (review_preview _ _ Heq). ss.
    - unfold Store.map, Store.cojoin, plens, compose. intros f.
      f_equal. extensionalities g. f_equal.
      + extensionalities a. ss. rewrite preview_review. ss.
      + extensionalities g' s. ss. des_ifs.
  Qed.

End PRISM_LENS.

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

  Lemma isPrism_inlp : Prism.isPrism inlp.
  Proof.
    econs.
    - i. ss.
    - i. destruct s; ss. inv H; ss.
  Qed.

  Lemma isPrism_inrp : Prism.isPrism inrp.
  Proof.
    econs.
    - i. ss.
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

End TEST.
