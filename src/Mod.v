From sflib Require Import sflib.
From ITree Require Export ITree.
From Paco Require Import paco.

From ITree Require Export
     ITree
     ITreeFacts
     Events.MapDefault
     Events.State
     Events.StateFacts
     EqAxiom
.

Export ITreeNotations.

Require Import Coq.Classes.RelationClasses.

Set Implicit Arguments.

Variant cE (State: Type): Type -> Type :=
| Yield (st: State): cE State State
.

Variable BehE: Type -> Type.

Variable fname: Type.
Variable fname_eq_dec: forall (f0 f1: fname), {f0 = f1} + {f0 <> f1}.
Variable Val: Type.

Variant callE (State: Type): Type -> Type :=
| Call (arg: Val) (st: State): callE State (Val * State)
.

Module Mod.
  Record t: Type :=
    mk {
        state: Type;
        st_init: state;
        funs: fname -> ktree (BehE +' cE state) (Val * state) (Val * state);
      }.

  Section ADD.
    Variable state0 state1: Type.

    Definition add_state: Type :=
      (state0 * state1)%type.

    Definition add_st_init: state0 -> state1 -> add_state :=
      fun st_init0 st_init1 => (st_init0, st_init1).

    Definition add_cE_left (st1: state1):
      forall X, cE state0 X -> cE add_state (X * state1) :=
      fun X e =>
        match e with
        | Yield st0 => Yield (st0, st1)
        end.

    CoFixpoint add_itree_left:
      forall (st1: state1) R (itr: itree (BehE +' cE state0) R),
        itree (BehE +' cE add_state) (R * state1) :=
      fun st1 R itr =>
        match observe itr with
        | RetF r => Ret (r, st1)
        | TauF itr => Tau (add_itree_left st1 itr)
        | VisF (inl1 e) ktr =>
            Vis (inl1 e) (fun x => add_itree_left st1 (ktr x))
        | VisF (inr1 e) ktr =>
            Vis (inr1 (add_cE_left st1 e)) (fun '(x, st1) => add_itree_left st1 (ktr x))
        end.

    Lemma add_itree_left_ret st1 R (r: R)
      :
      add_itree_left st1 (Ret r) = Ret (r, st1).
    Admitted.

    Lemma add_itree_left_tau st1 R (itr: itree (BehE +' cE state0) R)
      :
      add_itree_left st1 (Tau itr) = Tau (add_itree_left st1 itr).
    Admitted.
  End ADD.

  Definition add: t -> t -> t.
  Admitted.
End Mod.

Module ModSim.
  Definition sim: Mod.t -> Mod.t -> Prop.
  Admitted.

  Lemma sim_id (md: Mod.t)
    :
    sim md md.
  Admitted.

  Lemma sim_horizontal
        (md_src0 md_src1 md_tgt0 md_tgt1: Mod.t)
        (SIM0: sim md_src0 md_tgt0)
        (SIM1: sim md_src1 md_tgt1)
    :
    sim (Mod.add md_src0 md_tgt0) (Mod.add md_src1 md_tgt1).
  Admitted.
End ModSim.

Module OMod.
  Record t: Type :=
    mk {
        state: Type;
        st_init: state;
        funs: fname -> ktree (BehE +' cE state +' callE state) (Val * state) (Val * state);
      }.

  Section LINK.
    Variable omd: t.
    Variable md: Mod.t.

    Definition link_state: Type := omd.(state) * md.(Mod.state).

    Definition link_st_init: link_state := (omd.(st_init), md.(Mod.st_init)).
  End LINK.
End OMod.
