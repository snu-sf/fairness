From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Export ITreeLib WFLibLarge FairBeh NatStructs Mod pind.

Set Implicit Arguments.


Module WMod.
  Variant output (state: Type) (ident: ID) (mident: ID) (R: Type) :=
    | normal (st: state) (r: R) (fm: fmap (id_sum ident mident))
    | stuck
    | disabled
  .

  Record function (state: Type) (ident: ID) (mident: ID): Type :=
    mk_fun {
        type: ident;
        A: Type;
        R: Type;
        body: A -> state -> output state ident mident R -> Prop;
      }.

  Record t: Type :=
    mk {
        state: Type;
        ident: ID;
        mident: ID;
        st_init: state;
        funs: list (fname * function state ident mident);
      }.

  Section INTERP.
    Variable m: t.

    Definition interp_state := (m.(state) * NatMap.t m.(ident))%type.

    Definition interp_ident := id_sum thread_id m.(mident).

    Definition interp_fmap
               (fm: fmap (id_sum m.(ident) m.(mident))) (ts: NatMap.t m.(ident)) : fmap interp_ident :=
      fun i =>
        match i with
        | inl i =>
            match NatMap.find i ts with
            | Some i => fm (inl i)
            | None => Flag.emp
            end
        | inr i => fm (inr i)
        end.

    Definition interp_fun (f: function m.(state) m.(ident) m.(mident))
      : ktree (threadE interp_ident interp_state) f.(A) f.(R) :=
      fun (arg: f.(A)) =>
        _ <- trigger Yield;;

        tid <- trigger (GetTid);;
        '(st, ts) <- trigger (Get id);;
        let ts := NatMap.add tid f.(type) ts in
        _ <- trigger (Put (st, ts));;
        _ <- trigger (Fair (prism_fmap inlp (fun i => if tid_dec i tid then Flag.success else Flag.emp)));;

        ITree.iter
          (fun (_: unit) =>
             b <- trigger (Choose bool);;
             if (b: bool)
             then
               _ <- trigger (Fair (prism_fmap inlp (fun i => if tid_dec i tid then Flag.fail else Flag.emp)));;
               _ <- trigger Yield;; Ret (inl tt)
             else
               '(st, ts) <- trigger (Get id);;
               next <- trigger (Choose (sig (f.(body) arg st)));;
               match proj1_sig next with
               | normal st r fm =>
                   let ts := NatMap.remove tid ts in
                   _ <- trigger (Fair (interp_fmap fm ts));;
                   _ <- trigger (Put (st, ts));;
                   _ <- trigger Yield;;
                   Ret (inr r)
               | stuck _ _ _ _ => UB
               | disabled _ _ _ _ => _ <- trigger Yield;; Ret (inl tt)
               end) tt
    .

    Definition interp_fun_register (tid: thread_id) (i: m.(ident)): itree (threadE interp_ident interp_state) unit :=
      '(st, ts) <- trigger (Get id);;
      let ts := NatMap.add tid i ts in
      _ <- trigger (Put (st, ts));;
      _ <- trigger (Fair (prism_fmap inlp (fun i => if tid_dec i tid then Flag.success else Flag.emp)));;
      Ret tt
    .

    Definition interp_fun_body R (tid: thread_id)
               (step: m.(state) -> output m.(state) m.(ident) m.(mident) R -> Prop)
      : itree (threadE interp_ident interp_state) R :=
      ITree.iter
        (fun (_: unit) =>
           b <- trigger (Choose bool);;
           if (b: bool) then
             _ <- trigger (Fair (prism_fmap inlp (fun i => if tid_dec i tid then Flag.fail else Flag.emp)));;
             _ <- trigger Yield;; Ret (inl tt)
           else
             '(st, ts) <- trigger (Get id);;
             next <- trigger (Choose (sig (step st)));;
             match proj1_sig next with
             | normal st r fm =>
                 let ts := NatMap.remove tid ts in
                 _ <- trigger (Fair (interp_fmap fm ts));;
                 _ <- trigger (Put (st, ts));;
                 _ <- trigger Yield;;
                 Ret (inr r)
             | stuck _ _ _ _ => UB
             | disabled _ _ _ _ => _ <- trigger Yield;; Ret (inl tt)
             end) tt.

    Lemma interp_fun_unfold f arg
      :
      interp_fun f arg
      =
        _ <- trigger Yield;;
        tid <- trigger (GetTid);;
        _ <- (interp_fun_register tid f.(type));;
        interp_fun_body tid (f.(body) arg)
    .
    Proof.
      unfold interp_fun, interp_fun_register, interp_fun_body. grind.
    Qed.

    Lemma interp_loop_unfold
          R (tid: thread_id)
          (step: m.(state) -> output m.(state) m.(ident) m.(mident) R -> Prop)
      :
      interp_fun_body tid step
      =
        b <- trigger (Choose bool);;
        if (b: bool) then
          _ <- trigger (Fair (prism_fmap inlp (fun i => if tid_dec i tid then Flag.fail else Flag.emp)));;
          _ <- trigger Yield;;
          tau;; interp_fun_body tid step
        else
          '(st, ts) <- trigger (Get id);;
          next <- trigger (Choose (sig (step st)));;
          match proj1_sig next with
          | normal st r fm =>
              let ts := NatMap.remove tid ts in
              _ <- trigger (Fair (interp_fmap fm ts));;
              _ <- trigger (Put (st, ts));;
              _ <- trigger Yield;;
              Ret r
          | stuck _ _ _ _ => UB
          | disabled _ _ _ _ => _ <- trigger Yield;; tau;; interp_fun_body tid step
          end.
    Proof.
      unfold interp_fun_body at 1. rewrite unfold_iter_eq.
      unfold interp_fun_body, UB. grind.
    Qed.

    Definition interp_mod: Mod.t :=
      Mod.mk
        (m.(st_init), NatMap.empty m.(ident))
        (Mod.get_funs (List.map (fun '(fn, f) => (fn, Mod.wrap_fun (interp_fun f))) m.(funs)))
    .
  End INTERP.
End WMod.
Arguments WMod.disabled {_ _ _ _}.
Arguments WMod.stuck {_ _ _ _}.
