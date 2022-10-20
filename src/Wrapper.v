From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Export ITreeLib WFLib FairBeh NatStructs Mod pind OpenMod.

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
        body: thread_id -> A -> state -> output state ident mident R -> Prop;
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
      : ktree (((@eventE interp_ident) +' cE) +' sE interp_state) Any.t Any.t :=
      Mod.wrap_fun
        (fun (arg: f.(A)) =>
           _ <- trigger Yield;;

           tid <- trigger (GetTid);;
           '(st, ts) <- trigger (@Get _);;
           let ts := NatMap.add tid f.(type) ts in
           _ <- trigger (Put (st, ts));;
           _ <- trigger (Fair (sum_fmap_l (fun i => if tid_dec i tid then Flag.success else Flag.emp)));;

           ITree.iter
             (fun (_: unit) =>
                b <- trigger (Choose bool);;
                if (b: bool) then _ <- trigger Yield;; Ret (inl tt)
                else
                  '(st, ts) <- trigger (@Get _);;
                  next <- trigger (Choose (sig (f.(body) tid arg st)));;
                  match proj1_sig next with
                  | normal st r fm =>
                      let ts := NatMap.remove tid ts in
                      _ <- trigger (Fair (interp_fmap fm ts));;
                      _ <- trigger (Put (st, ts));;
                      _ <- trigger Yield;;
                      Ret (inr r)
                  | stuck _ _ _ _ => UB
                  | disabled _ _ _ _ => _ <- trigger Yield;; Ret (inl tt)
                  end) tt)
    .

    Definition interp_fun_register (i: m.(ident)): itree (((@eventE interp_ident) +' cE) +' sE interp_state) unit :=
      tid <- trigger (GetTid);;
      '(st, ts) <- trigger (@Get _);;
      let ts := NatMap.add tid i ts in
      _ <- trigger (Put (st, ts));;
      _ <- trigger (Fair (sum_fmap_l (fun i => if tid_dec i tid then Flag.success else Flag.emp)));;
      Ret tt
    .

    Definition interp_fun_body R (tid: thread_id) (i: m.(ident))
               (step: m.(state) -> output m.(state) m.(ident) m.(mident) R -> Prop)
      : itree (((@eventE interp_ident) +' cE) +' sE interp_state) R :=
      ITree.iter
        (fun (_: unit) =>
           b <- trigger (Choose bool);;
           if (b: bool) then _ <- trigger Yield;; Ret (inl tt)
           else
             '(st, ts) <- trigger (@Get _);;
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

    Definition interp_mod: Mod.t :=
      Mod.mk
        (m.(st_init), NatMap.empty m.(ident))
        (Mod.get_funs (List.map (fun '(fn, f) => (fn, interp_fun f)) m.(funs)))
    .
  End INTERP.
End WMod.
Arguments WMod.disabled {_ _ _ _}.
Arguments WMod.stuck {_ _ _ _}.
