From sflib Require Import sflib.
From Fairness Require Import Mod Linking.
From Fairness Require Import SCMemSpec elimstack.Code.

Module ElimStackClient.

  Definition gvs : list nat := [1].
  Definition s : SCMem.val := SCMem.val_ptr (0, 0).

  Section CODE.

    Definition state := unit.
    Definition ident := void.

    Definition thread_push :
      ktree (threadE ident state) unit unit
      := fun _ =>
      _ <- (trigger Yield;;; ElimStack.push (s,SCMem.val_nat 1));;
      _ <- trigger Yield;;
      Ret tt.

    Definition thread_pop :
      ktree (threadE ident state) unit (SCMem.val)
      := fun _ =>
      _ <- trigger Yield;;
      v <- ITree.iter
        (fun _ =>
          ov <- (trigger Yield;;; ElimStack.pop s);;
          match ov with
          | Some v => Ret (inr v)
          | None => Ret (inl tt)
          end
        ) tt;;
        _ <- trigger Yield;;
        Ret v.

    Definition omod : Mod.t :=
      Mod.mk
        tt
        (Mod.get_funs [("thread_push", Mod.wrap_fun thread_push);
                       ("thread_pop", Mod.wrap_fun thread_pop)])
    .

    Definition module : Mod.t :=
      OMod.close
        (omod)
        (SCMem.mod gvs)
    .

  End CODE.

End ElimStackClient.

Module ElimStackClientSpec.

  Section SPEC.

    Notation state := unit.
    Notation ident := void.

    Definition thread_push :
      ktree (threadE ident state) unit unit
      :=
      fun _ =>
        _ <- trigger Yield;; Ret tt.

    Definition thread_pop:
      ktree (threadE void unit) unit SCMem.val
      :=
      fun _ =>
        _ <- trigger Yield;; Ret (1 : SCMem.val).

    Definition module : Mod.t :=
      Mod.mk
        tt
        (Mod.get_funs [("thread_push", Mod.wrap_fun thread_push);
                       ("thread_pop", Mod.wrap_fun thread_pop)])
    .

  End SPEC.

End ElimStackClientSpec.
