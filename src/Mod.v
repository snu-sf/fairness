From sflib Require Import sflib.
From Paco Require Import paco.
From Fairness Require Export ITreeLib FairBeh.
Require Export Coq.Strings.String.

Set Implicit Arguments.

Notation fname := string (only parsing).
Definition Val := nat.

Variant cE: Type -> Type :=
| Yield: cE unit
| Spawn (fn: fname) (args: list Val): cE unit
| GetTid: cE nat
.

Variant stateE (State: Type): Type -> Type :=
| Put (st: State): stateE State unit
| Get: stateE State State
.

Module Mod.
  Record t: Type :=
    mk {
        state: Type;
        ident: ID;
        st_init: state;
        funs: fname -> ktree ((eventE +' cE) +' stateE state) (list Val) Val;
      }.
End Mod.




Definition update_fst {A B}: A * B -> A -> A * B :=
  fun '(_, b) a => (a, b).

Definition update_snd {A B}: A * B -> B -> A * B :=
  fun '(a, _) b => (a, b).

Section LENS.
  Variable S: Type.
  Variable V: Type.
  Variable E: Type -> Type.

  Variable get: S -> V.
  Variable put: S -> V -> S.

  Definition embed_itree:
    forall R (itr: itree (E +' stateE V) R),
      itree (E +' stateE S) R.
    cofix embed_itree.
    intros R itr.
    destruct (observe itr) as [r|itr0|? [e|[v|]] ktr].
    { exact (Ret r). }
    { exact (Tau (embed_itree _ itr0)). }
    { exact (Vis (inl1 e) (fun x => embed_itree _ (ktr x))). }
    { exact (Vis (inr1 (@Get _)) (fun s => Vis (inr1 (Put (put s v))) (fun x => embed_itree _ (ktr x)))). }
    { exact (Vis (inr1 (@Get _)) (fun s => embed_itree _ (ktr (get s)))). }
  Defined.
End LENS.

(* Section ADD. *)
(*   Variable state0 state1: Type. *)

(*   Definition add_state: Type := *)
(*     (state0 * state1)%type. *)

(*   Definition add_st_init: state0 -> state1 -> add_state := *)
(*     fun st_init0 st_init1 => (st_init0, st_init1). *)

(*   Definition add_fun_left *)
(*              (ktr: ktree (BehE +' cE state0) (Val * state0) (Val * state0)): *)
(*     ktree (BehE +' cE add_state) (Val * add_state) (Val * add_state) := *)
(*     embed_fun fst update_fst ktr. *)

(*   Definition add_fun_right *)
(*              (ktr: ktree (BehE +' cE state1) (Val * state1) (Val * state1)): *)
(*     ktree (BehE +' cE add_state) (Val * add_state) (Val * add_state) := *)
(*     embed_fun snd update_snd ktr. *)

(*   Definition add_funs *)
(*              (funs0: fname -> ktree (BehE +' cE state0) (Val * state0) (Val * state0)) *)
(*              (funs1: fname -> ktree (BehE +' cE state1) (Val * state1) (Val * state1)) *)
(*     : *)
(*     fname -> ktree (BehE +' cE add_state) (Val * add_state) (Val * add_state) := *)
(*     fun fn => *)
(*       match fname_parse fn with *)
(*       | Some (true, fn) => add_fun_left (funs0 fn) *)
(*       | Some (false, fn) => add_fun_right (funs1 fn) *)
(*       | None => fun _ => trigger UB >>= Empty_set_rect _ *)
(*       end. *)
(* End ADD. *)

(* Definition add (md0 md1: t): t := *)
(*   @mk *)
(*     (add_state md0.(state) md1.(state)) *)
(*     (add_st_init md0.(st_init) md1.(st_init)) *)
(*     (add_funs md0.(funs) md1.(funs)). *)
(* End Mod. *)


(* Module ModSim. *)
(*   Definition sim: Mod.t -> Mod.t -> Prop. *)
(*   Admitted. *)

(*   Lemma sim_id (md: Mod.t) *)
(*     : *)
(*     sim md md. *)
(*   Admitted. *)

(*   Lemma sim_horizontal *)
(*         (md_src0 md_src1 md_tgt0 md_tgt1: Mod.t) *)
(*         (SIM0: sim md_src0 md_tgt0) *)
(*         (SIM1: sim md_src1 md_tgt1) *)
(*     : *)
(*     sim (Mod.add md_src0 md_tgt0) (Mod.add md_src1 md_tgt1). *)
(*   Admitted. *)
(* End ModSim. *)

(* Variant callE: Type -> Type := *)
(* | Call (fn: fname) (arg: Val): callE Val *)
(* . *)

(* Module OMod. *)
(*   Record t: Type := *)
(*     mk { *)
(*         state: Type; *)
(*         st_init: state; *)
(*         funs: fname -> ktree (BehE +' cE state +' callE state) (Val * state) (Val * state); *)
(*       }. *)

(*   Section LINK. *)
(*     Variable omd: t. *)
(*     Variable md: Mod.t. *)

(*     Definition link_state: Type := omd.(state) * md.(Mod.state). *)

(*     Definition link_st_init: link_state := (omd.(st_init), md.(Mod.st_init)). *)

(*     Definition link_itree: *)
(*       forall (s: link_state) R, *)
(*         itree (BehE +' callE omd.(state) +' cE omd.(state)) R -> itree (BehE +' callE link_state +' cE link_state) (link_state * R). *)
(*     Proof. *)
(*     Admitted. *)
(*   End LINK. *)
(* End OMod. *)
