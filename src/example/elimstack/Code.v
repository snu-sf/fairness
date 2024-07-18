(* Note: simplified, the original code does more serious case analysis on the current offer value, and pop can also make an offer. *)
From sflib Require Import sflib.
From Fairness Require Import Mod Linking.
From Fairness Require Import SCMemSpec.

Module ElimStack.
Section ELIMSTACK.

  Context {state : Type}.
  Context {ident : ID}.

  Definition push_loop :
    (* ktree (threadE void unit) (SCMem.val * SCMem.val) unit *)
    ktree (threadE ident state) (SCMem.val * SCMem.val) unit
    :=
    fun '(s, val) => ITree.iter (fun (_ : unit) =>
      head <- (OMod.call (R:=SCMem.val) "load" s);;
      node <- (OMod.call (R:=SCMem.val) "alloc" 2);;
      _ <- (OMod.call (R:=unit) "store" (node,head));;
      _ <- (OMod.call (R:=unit) "store" (SCMem.val_add node 1, val));;
      b <- (OMod.call (R:=bool) "cas" (s, head, node));;

      if b then Ret (inr tt) else

      (* Attempt to exchange *)
      _ <- (OMod.call (R:=unit) "store" (node,(0 : SCMem.val)));;
      _ <- (OMod.call (R:=unit) "store" (SCMem.val_add s 1,node));;

      (* Wait *)

      (* Done waiting *)
      _ <- (OMod.call (R:=unit) "store" (SCMem.val_add s 1,SCMem.val_null));;
      b <- (OMod.call (R:=bool) "cas" (node, (0 : SCMem.val), (1 : SCMem.val)));;
      if b then Ret (inl tt) else Ret (inr tt)
    ) tt.

  Definition push :
    ktree (threadE ident state) (SCMem.val * SCMem.val) unit
    :=
    fun '(s, val) =>
      _ <- trigger Yield;;
      push_loop (s,val).

  Definition pop_loop :
    (* ktree (threadE void unit) SCMem.val (option (SCMem.val) *)
    ktree (threadE ident state) SCMem.val (option (SCMem.val))
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

      offer <- (OMod.call (R:=SCMem.val) "load" (SCMem.val_add s 1));;

      is_null <- (OMod.call (R:=bool) "compare" (offer, SCMem.val_null));;
      if is_null then Ret (inl tt) else
        b <- (OMod.call (R:=bool) "cas" (offer, (0 : SCMem.val), (1 : SCMem.val)));;
        if b then
          data <- (OMod.call (R:=SCMem.val) "load" (SCMem.val_add offer 1));;
          Ret (inr (Some data))
        else
          Ret (inl tt)
    ) tt.

    Definition pop :
    ktree (threadE ident state) SCMem.val (option SCMem.val)
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

    Lemma push_loop_red s val :
      push_loop (s, val) =
        head <- (OMod.call (R:=SCMem.val) "load" s);;
        node <- (OMod.call (R:=SCMem.val) "alloc" 2);;
        _ <- (OMod.call (R:=unit) "store" (node,head));;
        _ <- (OMod.call (R:=unit) "store" (SCMem.val_add node 1, val));;
        b <- (OMod.call (R:=bool) "cas" (s, head, node));;

        if b then Ret tt else (

        (* Attempt to exchange *)
        _ <- (OMod.call (R:=unit) "store" (node,(0 : SCMem.val)));;
        _ <- (OMod.call (R:=unit) "store" (SCMem.val_add s 1,node));;

        (* Wait *)

        (* Done waiting *)
        _ <- (OMod.call (R:=unit) "store" (SCMem.val_add s 1,SCMem.val_null));;
        b <- (OMod.call (R:=bool) "cas" (node, (0 : SCMem.val), (1 : SCMem.val)));;
        if b then tau;; push_loop (s,val) else Ret tt
        )
      .
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

        offer <- (OMod.call (R:=SCMem.val) "load" (SCMem.val_add s 1));;

        is_null <- (OMod.call (R:=bool) "compare" (offer, SCMem.val_null));;
        if is_null then tau;; pop_loop s else
          b <- (OMod.call (R:=bool) "cas" (offer, (0 : SCMem.val), (1 : SCMem.val)));;
          if b then
            data <- (OMod.call (R:=SCMem.val) "load" (SCMem.val_add offer 1));;
            Ret (Some data)
          else
            tau;; pop_loop s
      .
    Proof.
      unfold pop_loop. etransitivity.
      { apply unfold_iter_eq. }
      grind.
    Qed.

    Global Opaque push_loop pop_loop.
End ELIMSTACK.
End ElimStack.
