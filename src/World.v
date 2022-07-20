From sflib Require Import sflib.
Require Import Coq.Classes.RelationClasses.
From Fairness Require Import Axioms NatStructs.
From Fairness Require Import PCM.
From Fairness Require Import Mod.
Require Import String.

Set Implicit Arguments.


Section INVARIANT.
  Context `{M: URA.t}.

  Definition local_resources := NatMap.t URA.car.

  Definition unwrap_opt_resource (r: option URA.car): URA.car :=
    match r with
    | Some r => r
    | None => ε
    end.

  Definition sum_of_resources (rs: local_resources): URA.car :=
    NatMap.fold (fun _ r s => r ⋅ s) rs ε.

  Definition resources_wf (g: URA.car) (rs: local_resources): Prop :=
    URA.wf (g ⋅ sum_of_resources rs)
  .

  Definition get_resource
             (tid: thread_id.(id))
             (rs: local_resources)
    : (URA.car * local_resources) :=
    match nm_pop tid rs with
    | Some (r, rs) => (r, rs)
    | _ => (ε, rs)
    end.

  Lemma resources_wf_get_wf g0 tid rs0 r0 rs1
        (WF: resources_wf g0 rs0)
        (GET: get_resource tid rs0 = (r0, rs1))
    :
    (<<WF: URA.wf (g0 ⋅ r0 ⋅ sum_of_resources rs1)>>) /\
      (<<UPDATE: forall g1 r1
                        (WF: URA.wf (g0 ⋅ r0 ⋅ sum_of_resources rs1)),
          resources_wf g1 (NatMap.add tid r1 rs1)>>).
  Proof.
  Admitted.
End INVARIANT.
