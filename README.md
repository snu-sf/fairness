# Fair Operational Semantics
Coq Development for Fair Operational Semantics

## Build
Requirement: opam (>=2.0.0), Coq 8.15.0
- Install dependencies with opam
```
./configure
```
- Build the project
```
make build -j
```

## Code Structure
### Definitions
- `FairBeh.v`: Sec 4.1 (Definitions of Fair Operational Semantics)
- `FairSim.v`: Sec 4.2 (Global Simulation Relation)
- `Concurrency.v`: Sec 5 (Formalizing Fair Concurrency)
- `Mod.v`: Sec 6 (Module System)
- `WMM.v`: Sec 6.1 (Fair Weak Memory Module)
- `Weakest.v`: Sec 7 (Program Logic for Fairness) (See lemmas for `stsim`)

### Theorems
- `Theorem adequacy` in `Adequacy.v`: Theorem 4.1 (Adequacy)
- `Theorem gsim_nondet_fifo` in `FIFOSchedSim.v`: Theorem 5.2 (FIFOSch is fair)
- `Theorem modsim_adequacy` in `ModAdequacy.v`: Theorem 6.1 (Adequacy of module simulation)
- `Theorem usersim_adequacy` in `ModAdequacy.v`: Theorem 7.2 (Whole program adequacy)

### Examples
- `FairLockW.v`: Sec 3.1 (ABSLock)
- `TicketLockW.v`: Sec 3.1 (Ticket Lock)
- `LockClient.v`: Sec 1 (Example client code)
- `Lemma ticketlock_fair` in `TicketlockW.v`: Theorem 6.2 (TicketLock is Fair) (*not ported yet*)
- `Lemma client_correct` in `LockClient.v`: Module simulation between client modules (*not ported yet*)
- `Theorem client_all` in `LockClientAll.v` : Sec 8 (Case Study)
