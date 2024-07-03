From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Import pind Axioms ITreeLib Red TRed IRed2 WFLibLarge.
From Fairness Require Import FairBeh Mod Linking.
From Fairness Require Import PCM IProp IPM IPropAux.
From Fairness Require Import IndexedInvariants OpticsInterp SimWeakest.
From Fairness Require Import TemporalLogic SCMemSpec AuthExclAnysRA.

Module ElimStack.
Section ELIMSTACK.

  Context {state : Type}.
  Context {ident : ID}.

  Definition push :
    (* ktree (threadE void unit) (SCMem.val * SCMem.val) unit *)
    ktree (threadE ident state) (SCMem.val * SCMem.val) unit
    :=
    fun '(s, val) => _ <- trigger Yield;; ITree.iter (fun (_ : unit) =>
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
      b <- (OMod.call (R:=bool) "cas" (node, (0 : SCMem.val), (2 : SCMem.val)));;
      if b then Ret (inl tt) else Ret (inr tt)
    ) tt.

  Definition pop :
    (* ktree (threadE void unit) SCMem.val (option (SCMem.val) *)
    ktree (threadE ident state) SCMem.val (option (SCMem.val))
    :=
    fun s => _ <- trigger Yield;; ITree.iter (fun (_ : unit) =>
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

End ELIMSTACK.
End ElimStack.
