From sflib Require Import sflib.
From Fairness Require Import Mod Linking.
From Fairness Require Import SCMemSpec.

Module TreiberStack.

  Section TREIBERSTACK.

    Context {state : Type}.
    Context {ident : ID}.

    Definition push_loop :
      ktree (threadE ident state) (SCMem.val * SCMem.val) unit
      :=
      fun '(s, node) =>
      ITree.iter (fun (_ : unit) =>
        head <- (OMod.call (R:=SCMem.val) "load" s);;
        _ <- (OMod.call (R:=unit) "store" (node,head));;
        b <- (OMod.call (R:=bool) "cas" (s, head, node));;
        if b then Ret (inr tt) else Ret (inl tt)
      ) tt.

    Definition push :
      (* ktree (threadE void unit) (SCMem.val * SCMem.val) unit *)
      ktree (threadE ident state) (SCMem.val * SCMem.val) unit
      :=
      fun '(s,val) =>
        node <- (OMod.call (R:=SCMem.val) "alloc" 2);;
        _ <- (OMod.call (R:=unit) "store" (SCMem.val_add node 1, val));;
        _ <- push_loop (s, node);;
        trigger Yield.

    Definition pop_loop :
      ktree (threadE ident state) SCMem.val (option SCMem.val)
      :=
      fun s =>
      ITree.iter (fun (_ : unit) =>
        head <- (OMod.call (R:=SCMem.val) "load" s);;
        is_null <- (OMod.call (R:=bool) "compare" (head, SCMem.val_null));;
        if is_null then Ret (inr None) else
        next <- (OMod.call (R:=SCMem.val) "load" head);;
        b <- (OMod.call (R:=bool) "cas" (s, head, next));;
        if b then
          data <- (OMod.call (R:=SCMem.val) "load" (SCMem.val_add head 1));;
          Ret (inr (Some data))
        else
          Ret (inl tt)
      ) tt.

    Definition pop :
      (* ktree (threadE void unit) SCMem.val (option (SCMem.val) *)
      ktree (threadE ident state) SCMem.val (option (SCMem.val))
      :=
      fun s =>
        _ <- trigger Yield;;
        pop_loop s.

    (** TODO : more rules for module composition. *)
    (* Definition omod : Mod.t := *)
    (*   Mod.mk *)
    (*     (* tt *) *)
    (*     (Mod.st_init Client) *)
    (*     (Mod.get_funs [("push", Mod.wrap_fun push); *)
    (*                    ("pop", Mod.wrap_fun pop)]) *)
    (* . *)

    (* Definition module gvs : Mod.t := *)
    (*   OMod.close *)
    (*     (omod) *)
    (*     (SCMem.mod gvs) *)
    (* . *)

  Lemma push_loop_red s node :
    push_loop (s, node) =
      head <- (OMod.call (R:=SCMem.val) "load" s);;
      _ <- (OMod.call (R:=unit) "store" (node,head));;
      b <- (OMod.call (R:=bool) "cas" (s, head, node));;
      if b then Ret tt else tau;; push_loop (s,node).
  Proof.
    unfold push_loop. etransitivity.
    { apply unfold_iter_eq. }
    grind.
  Qed.

  Lemma pop_loop_red s :
    pop_loop s =
      head <- (OMod.call (R:=SCMem.val) "load" s);;
      is_null <- (OMod.call (R:=bool) "compare" (head, SCMem.val_null));;
      if is_null then Ret None else
      next <- (OMod.call (R:=SCMem.val) "load" head);;
      b <- (OMod.call (R:=bool) "cas" (s, head, next));;
      if b then
        data <- (OMod.call (R:=SCMem.val) "load" (SCMem.val_add head 1));;
        Ret (Some data)
      else
        tau;; pop_loop s.
  Proof.
    unfold pop_loop. etransitivity.
    { apply unfold_iter_eq. }
    grind.
  Qed.

  Global Opaque push_loop pop_loop.
  End TREIBERSTACK.
End TreiberStack.
