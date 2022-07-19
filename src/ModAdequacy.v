From sflib Require Import sflib.
From ITree Require Export ITree.
From Paco Require Import paco.

Require Export Coq.Strings.String Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Program.
Require Import Permutation.

Export ITreeNotations.

From Fairness Require Import pind5 pind8.
From Fairness Require Import Axioms.
From Fairness Require Export ITreeLib FairBeh FairSim NatStructs.
From Fairness Require Export Mod ModSimPico Concurrency.
From Fairness Require Import SchedSim Adequacy LocalAdequacy.

Set Implicit Arguments.

Section ADEQ.

  Definition program := list (fname * (list Val))%type.

  Definition fn2th (m: Mod.t) (fn: fname) (args: list Val): @thread (Mod.ident m) (sE (Mod.state m)) Val :=
    match Mod.funs m fn with
    | Some ktr => ktr args
    | None => (Vis (inl1 (inl1 Undefined)) (Empty_set_rect _))
    end.



  Definition mod_prog_wf (m: Mod.t) (p: program) :=
    Forall (fun '(fn, args) => match Mod.funs m fn with Some _ => True | _ => False end) p.

  Fixpoint mod_prog2ths_ (m: Mod.t) (p: program) (k: Th.key):
    option (list (Th.key * @thread (Mod.ident m) (sE (Mod.state m)) Val))%type :=
    match p with
    | (fn, args) :: tl =>
        match Mod.funs m fn with
        | Some ktr => match mod_prog2ths_ m tl (S k) with
                     | Some ths => Some ((k, ktr args) :: ths)
                     | _ => None
                     end
        | _ => None
        end
    | _ => Some []
    end.

  Definition mod_prog2ths (m: Mod.t) (p: program): option (@threads (Mod.ident m) (sE (Mod.state m)) Val) :=
    match mod_prog2ths_ m p 0 with
    | Some lths => Some (NatMapP.of_list lths)
    | _ => None
    end.

  Definition local_sim_threads_list
             (m1 m2: Mod.t)
             (lths_src: list (Th.key * @thread (Mod.ident m1) (sE (Mod.state m1)) Val)%type) 
             (lths_tgt: list (Th.key * @thread (Mod.ident m2) (sE (Mod.state m2)) Val)%type)
             (wf_src wf_tgt: WF)
             (world: Type) (world_le: world -> world -> Prop)
             I
    :=
    List.Forall2
      (fun '(t1, src) '(t2, tgt) => (t1 = t2) /\ (local_sim ( world_le I (@eq Val) src tgt))
      lths_src lths_tgt.

  Lemma mod_prog_wf_prog_ex_ths_
        m p
        (WF: mod_prog_wf m p)
        (MS: ModSim.mod_sim
    :
    forall n, exists ths, (mod_prog2ths_ m p n = Some ths).
  Proof.
    induction WF; i.
    { eexists. ss. }
    ss. des_ifs.
    { eexists. eauto. }
    { exfalso. specialize (IHWF (S n)). des. clarify. }
  Qed.

  Lemma mod_prog_wf_prog_ex_ths
        m p
        (WF: mod_prog_wf m p)
    :
    exists ths, mod_prog2ths m p = Some ths.
  Proof.
    unfold mod_prog2ths. hexploit mod_prog_wf_prog_ex_ths_; eauto. i; des. eexists. rewrite H. eauto.
  Qed.

  Definition mod_prog_improves (m_src m_tgt: Mod.t) sched (p: program) :=
    forall tid,
      let oths_src := mod_prog2ths m_src p in
      let oths_tgt := mod_prog2ths m_tgt p in
      match oths_src, oths_tgt with
      | Some ths_src, Some ths_tgt =>
          improves (interp_mod m_src tid ths_src sched_nondet) (interp_mod m_tgt tid ths_tgt sched)
      | _, _ => False
      end.

  Theorem 




End ADEQ.
