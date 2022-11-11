From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
Unset Universe Checking.
From Fairness Require Export ITreeLib WFLib FairBeh NatStructs Mod pind Axioms OpenMod WMM Red IRed Wrapper WeakestAdequacy FairLock Concurrency LockClient FIFOSched SchedSim FIFOSched FIFOSchedSim ModAdequacy TicketLockW.
From PromisingLib Require Import Loc Event.
From PromisingSEQ Require Import TView.
From Ordinal Require Export ClassicalHessenberg.
Require Import Coq.Numbers.BinNums.

Section ALL.
  Definition client_spec := ClientSpec.mod.

  Definition client_abstract_lock :=
    OMod.close ClientImpl.omod (ModAdd WMem.mod FairLockW.mod).

  Definition client_ticket_lock :=
    OMod.close ClientImpl.omod (ModAdd WMem.mod TicketLock.mod ).

  Theorem client_all
    :
    Adequacy.improves
      (interp_all
         (client_spec.(Mod.st_init))
         (prog2ths client_spec [("thread1", tt↑); ("thread2", tt↑)]) 0)
      (interp_all_fifo
         (client_ticket_lock.(Mod.st_init))
         (prog2ths client_ticket_lock [("thread1", tt↑); ("thread2", tt↑)]) 0)
  .
  Proof.
    eapply Adequacy.improves_trans.
    { eapply Adequacy.adequacy.
      { instantiate (1:=nat_wf). econs. exact 0. }
      { i. ss. eauto. }
      { eapply ssim_implies_gsim; ss.
        { instantiate (1:=id). ss. }
        { eapply ssim_nondet_fifo; ss. ii. compute in H. des. inv H; des; ss. inv H1; ss. }
      }
    }
    eapply Adequacy.improves_trans.
    { eapply modsim_adequacy.
  Admitted.
End ALL.
