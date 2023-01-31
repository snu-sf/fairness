From sflib Require Import sflib.
From Paco Require Import paco.
Unset Universe Checking.
From Fairness Require Export FairBeh Mod OpenMod WMM FairLock Concurrency LockClient FIFOSched SchedSim FIFOSched FIFOSchedSim ModAdequacy TicketLockW ModCloseSim ModAddSim.

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
    { eapply modsim_adequacy. eapply ModClose_mono.
      eapply ModAdd_right_mono. eapply ticketlock_fair.
    }
    { eapply usersim_adequacy. eapply client_correct. }
    Unshelve. all: exact true.
  Qed.
End ALL.
