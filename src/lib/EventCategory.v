From Paco Require Import paco.
From sflib Require Import sflib.
From ITree Require Import ITree.
From Fairness Require Import ITreeLib.
From Coq Require Import Program.

Set Implicit Arguments.

Module Event.

  Definition hom (E1 E2 : Type -> Type) := forall X, E1 X -> E2 X.

  Definition id E : hom E E := fun X e => e.

  Definition compose {E1 E2 E3} : hom E2 E3 -> hom E1 E2 -> hom E1 E3 :=
    fun f g X => f X ∘ g X.

  Lemma identity_l E1 E2 (f : hom E1 E2) : compose (id E2) f = f.
  Proof. reflexivity. Qed.

  Lemma identity_r E1 E2 (f : hom E1 E2) : compose f (id E1) = f.
  Proof. reflexivity. Qed.

  Lemma assoc E1 E2 E3 E4 (f : hom E1 E2) (g : hom E2 E3) (h : hom E3 E4) :
    compose (compose h g) f = compose h (compose g f).
  Proof. reflexivity. Qed.

End Event.

Declare Scope event_scope.
Delimit Scope event_scope with event.
Infix "∘" := (Event.compose) (at level 40, left associativity) : event_scope.

Section SUM.

  Definition embed_left {E1 E2} (embed : forall X, E1 X -> E2 X) {E} X (e : (E1 +' E) X) : (E2 +' E) X :=
    match e with
    | inl1 e => inl1 (embed _ e)
    | inr1 e => inr1 e
    end.

  Definition embed_right {E1 E2} (embed : forall X, E1 X -> E2 X) {E} X (e : (E +' E1) X) : (E +' E2) X :=
    match e with
    | inl1 e => inl1 e
    | inr1 e => inr1 (embed _ e)
    end.

End SUM.

Section MAP_EVENT.

  CoFixpoint map_event {E1 E2} (embed : forall X, E1 X -> E2 X) {R} : itree E1 R -> itree E2 R :=
    fun itr =>
      match observe itr with
      | RetF r => Ret r
      | TauF itr => Tau (map_event embed itr)
      | VisF e ktr => Vis (embed _ e) (fun x => map_event embed (ktr x))
      end.

  Lemma map_event_ret E1 E2 (embed : forall X, E1 X -> E2 X) R (r : R) :
    map_event embed (Ret r) = Ret r.
  Proof. eapply observe_eta. ss. Qed.

  Lemma map_event_tau E1 E2 (embed : forall X, E1 X -> E2 X) R (itr : itree E1 R) :
    map_event embed (Tau itr) = Tau (map_event embed itr).
  Proof. eapply observe_eta. ss. Qed.

  Lemma map_event_vis E1 E2 (embed : forall X, E1 X -> E2 X) R X (e : E1 X) (ktr : ktree E1 X R) :
    map_event embed (Vis e ktr) = Vis (embed _ e) (fun x => map_event embed (ktr x)).
  Proof. eapply observe_eta. ss. Qed.

  Lemma map_event_trigger E1 E2 (embed : forall X, E1 X -> E2 X) E' `[E' -< E1] R X (e : E' X) (ktr : ktree E1 X R) :
    map_event embed (x <- trigger e;; ktr x) = x <- trigger (embed _ (subevent X e));; map_event embed (ktr x).
  Proof. rewrite 2 bind_trigger. apply map_event_vis. Qed.

  Lemma map_event_bind E1 E2 (embed : forall X, E1 X -> E2 X) A B (itr : itree E1 A) (ktr : A -> itree E1 B) :
    map_event embed (itr >>= ktr) = map_event embed itr >>= fun x => map_event embed (ktr x).
  Proof.
    eapply bisim_is_eq.
    revert itr ktr. pcofix CIH. i.
    destruct_itree itr.
    - rewrite ! map_event_ret. grind.
      eapply paco2_mon. eapply eq_is_bisim. reflexivity. ss.
    - grind. rewrite ! map_event_tau. grind.
      pfold. econs. right. eapply CIH.
    - grind. rewrite ! map_event_vis. grind.
      pfold. econs. i. right. eapply CIH.
  Qed.

  Lemma map_event_id E R (itr : itree E R) : map_event (Event.id E) itr = itr.
  Proof.
    eapply bisim_is_eq.
    revert itr. pcofix CIH. i.
    destruct_itree itr.
    - rewrite map_event_ret. pfold. econs. ss.
    - rewrite map_event_tau. pfold. econs. right. eapply CIH.
    - rewrite map_event_vis. pfold. econs. i. right. eapply CIH.
  Qed.

  Lemma map_event_compose
    E1 E2 E3 (f : Event.hom E1 E2) (g : Event.hom E2 E3) R (itr : itree E1 R)
    : map_event (g ∘ f)%event itr = map_event g (map_event f itr).
  Proof.
    eapply bisim_is_eq.
    revert itr. pcofix CIH. i.
    destruct_itree itr.
    - rewrite ! map_event_ret. pfold. econs. ss.
    - rewrite ! map_event_tau. pfold. econs. right. eapply CIH.
    - rewrite ! map_event_vis. pfold. econs. i. right. eapply CIH.
  Qed.

End MAP_EVENT.

Global Opaque map_event.
