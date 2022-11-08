Unset Universe Checking.
From sflib Require Import sflib.
From Paco Require Import paco.
From Fairness Require Import ITreeLib IProp IPM ModSim ModSimNat PCM Weakest Concurrency.
Require Import Program.

Set Implicit Arguments.

Module WSim.
  Section WSIM.
    Context `{Σ: GRA.t}.

    Variable md_src: Mod.t.
    Variable md_tgt: Mod.t.



(*     list_prop_sum (fun '(tid, f_src, f_tgt) => *)

(* (p_src, p_tgt) *)

(*     Record sim (p_src: Th.t _) (p_tgt: Th.t _) : Prop := *)
(*       mk { *)
(*           funs: forall im_tgt, *)
(*           exists im_src rs r_shared I, *)
(*             (<<INIT: I (key_set p_src, im_src, im_tgt, md_src.(Mod.st_init), md_tgt.(Mod.st_init)) r_shared>>) /\ *)
(*               (<<SIM: Forall3 *)
(*                         (fun '(t1, src) '(t2, tgt) '(t3, r) => *)
(*                            (t1 = t2 /\ t1 = t3) /\ *)
(*                            @local_sim_init _ md_src.(Mod.state) md_tgt.(Mod.state) md_src.(Mod.ident) md_tgt.(Mod.ident) wf_src wf_tgt I _ _ (@eq Any.t) r t1 src tgt) *)
(*                         (Th.elements p_src) (Th.elements p_tgt) (NatMap.elements rs)>>) /\ *)
(*               (<<WF: URA.wf (r_shared ⋅ NatMap.fold (fun _ r s => r ⋅ s) rs ε)>>) *)
(*         }. *)
  End MODSIM.
End UserSim.
