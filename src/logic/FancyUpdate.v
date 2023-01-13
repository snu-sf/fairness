From stdpp Require Import coPset gmap.
From sflib Require Import sflib.
From Fairness Require Import PCM IProp IPM.
From iris Require Import bi.big_op.

Section INTERPRETATION.

  Class Interp `(Σ : GRA.t) :=
    { Var : Type
    ; prop : Var -> iProp
    }.

End INTERPRETATION.

Section PCM_OWN.

  Context `{Σ : GRA.t}.

  Definition OwnE `{@GRA.inG CoPset.t Σ} (E : coPset) := OwnM (Some E).
  Definition OwnD `{@GRA.inG Gset.t Σ} (D : gset positive) := OwnM (Some D).
  Definition inv `{Interp} `{@GRA.inG (Auth.t (positive ==> URA.agree Var)%ra) Σ}
    (n : positive) (x : Var) :=
    OwnM (Auth.white (@maps_to_res positive (URA.agree Var) n (Some (Some x)))).

End PCM_OWN.

Section WORLD_SATISFACTION.

  Context `{Σ : GRA.t}.
  Context `{@Interp Σ}.
  Context `{@GRA.inG CoPset.t Σ}.
  Context `{@GRA.inG Gset.t Σ}.
  Context `{@GRA.inG (Auth.t (positive ==> URA.agree Var)%ra) Σ}.

  Definition inv_auth (I : gmap positive Var) :=
    OwnM (@Auth.black
            (positive ==> URA.agree Var)%ra
            (fun (i : positive) =>
               match I !! i return (URA.agree Var) with
               | Some x => Some (Some x)
               | None => None
               end)).

  Definition inv_satall (I : gmap positive Var) :=
    ([∗ map] i ↦ x ∈ I, prop x ∗ OwnD {[i]} ∨ OwnE {[i]})%I.

  Definition wsat : iProp := (∃ I, inv_auth I ∗ inv_satall I)%I.

End WORLD_SATISFACTION.

Section FANCY_UPDATE.

  Context `{Σ : GRA.t}.
  Context `{@Interp Σ}.
  Context `{@GRA.inG CoPset.t Σ}.
  Context `{@GRA.inG Gset.t Σ}.
  Context `{@GRA.inG (Auth.t (positive ==> URA.agree Var)%ra) Σ}.

  Definition FUpd (E1 E2 : coPset) (P : iProp) : iProp :=
    wsat ∗ OwnE E1 -∗ #=> (wsat ∗ OwnE E2 ∗ P).

End FANCY_UPDATE.
