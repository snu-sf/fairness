From sflib Require Import sflib.
From ITree Require Export ITree Subevent.
From Paco Require Import paco.

From ITree Require Export
     ITree
     ITreeFacts
     Events.MapDefault
     Events.State
     Events.StateFacts
     EqAxiom
.

From ExtLib Require Export
     (* Data.String *)
     (* Structures.Monad *)
     (* Structures.Traversable *)
     (* Structures.Foldable *)
     (* Structures.Reducible *)
     (* OptionMonad *)
     Functor FunctorLaws
     Structures.Maps
     (* Data.List *)
.

Export SumNotations.
Export Monads.
Export CatNotations.
Open Scope cat_scope.
Open Scope monad_scope.
Open Scope itree_scope.
Export ITreeNotations.
Export CatNotations.

Require Import Coq.Classes.RelationClasses.

Set Implicit Arguments.

Definition update_fst {A B}: A * B -> A -> A * B :=
  fun '(_, b) a => (a, b).

Definition update_snd {A B}: A * B -> B -> A * B :=
  fun '(a, _) b => (a, b).

Variant cE (State: Type): Type -> Type :=
| Yield (st: State): cE State State
.

Variable BehE: Type -> Type.
Variable UB: BehE void.

Section LENS.
  Variable S: Type.
  Variable V: Type.
  Variable E: Type -> Type.

  Variable get: S -> V.
  Variable put: S -> V -> S.

  Definition embed_itree:
    forall (s: S) R (itr: itree (E +' cE V) R),
      itree (E +' cE S) (R * S).
    cofix embed_itree.
    intros s R itr.
    destruct (observe itr) as [r|itr0|? [e|[]] ktr].
    { exact (Ret (r, s)). }
    { exact (Tau (embed_itree s _ itr0)). }
    { exact (Vis (inl1 e) (fun x => embed_itree s _ (ktr x))). }
    { exact (Vis (inr1 (Yield (put s st))) (fun s => embed_itree s _ (ktr (get s)))). }
    Show Proof.
  Defined.

  Definition embed_fun A B (ktr: ktree (E +' cE V) (A * V) (B * V)):
    ktree (E +' cE S) (A * S) (B * S) :=
    fun '(a, s) =>
      '(b, _, s) <- embed_itree s (ktr (a, get s));; Ret (b, s).
End LENS.

Variable fname: Type.
Variable fname_eq_dec: forall (f0 f1: fname), {f0 = f1} + {f0 <> f1}.
Variable fname_parse: fname -> option (bool * fname).

Variable Val: Type.

Variant callE (State: Type): Type -> Type :=
| Call (fn: fname) (arg: Val) (st: State): callE State (Val * State)
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

    Definition add_fun_left
               (ktr: ktree (BehE +' cE state0) (Val * state0) (Val * state0)):
      ktree (BehE +' cE add_state) (Val * add_state) (Val * add_state) :=
      embed_fun fst update_fst ktr.

    Definition add_fun_right
               (ktr: ktree (BehE +' cE state1) (Val * state1) (Val * state1)):
      ktree (BehE +' cE add_state) (Val * add_state) (Val * add_state) :=
      embed_fun snd update_snd ktr.

    Definition add_funs
               (funs0: fname -> ktree (BehE +' cE state0) (Val * state0) (Val * state0))
               (funs1: fname -> ktree (BehE +' cE state1) (Val * state1) (Val * state1))
      :
      fname -> ktree (BehE +' cE add_state) (Val * add_state) (Val * add_state) :=
      fun fn =>
        match fname_parse fn with
        | Some (true, fn) => add_fun_left (funs0 fn)
        | Some (false, fn) => add_fun_right (funs1 fn)
        | None => fun _ => trigger UB >>= Empty_set_rect _
        end.
  End ADD.

  Definition add (md0 md1: t): t :=
    @mk
      (add_state md0.(state) md1.(state))
      (add_st_init md0.(st_init) md1.(st_init))
      (add_funs md0.(funs) md1.(funs)).
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

    Definition link_itree:
      forall (s: link_state) R,
        itree (BehE +' callE omd.(state) +' cE omd.(state)) R -> itree (BehE +' callE link_state +' cE link_state) (link_state * R).
    Proof.
    Admitted.
  End LINK.
End OMod.
