From sflib Require Export sflib.
Set Universe Polymorphism.

Section UNIVERSE.
  Universe i j.
  Lemma mp: forall (P: Type@{i}) (Q: Type@{i}), P -> (P -> Q) -> Q.
  Proof. intuition. Defined.

  Lemma mp': forall (P: Type@{i}) (Q: Type@{i}), (P -> Q) -> P -> Q.
  Proof. intuition. Qed.

  Ltac hexploit x := eapply mp; [eapply x|].
  Ltac hexploit' x := let H := fresh in set (H := x); clear H; eapply mp; [eapply x|].
End UNIVERSE.
