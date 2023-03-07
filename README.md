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
#### Section 4
- In `src/semantics`
- `eventE` in `Event.v`: FL language (Sec 4.1, Fig.3)
- `RawTr.t` in `SelectBeh.v`: Trace (Sec 4.1, Fig.3)
- `Tr.t` in `FairBeh.v`: Behavior (Sec 4.1, Fig.3)
- `RawTr.is_fair` in `SelectBeh.v`: FairTr (Sec 4.1, Fig.3)
- `imap` in `FairBeh.v`: cmap (Sec 4.2, Fig.4)
- In `src/simulation`
- `improves` in `Adequacy.v`: whole-program refinement (Sec 4.1)
- `sim` in `FairSim.v`: simulation relation (Sec 4.2)
#### Section 5
- In `src/semantics`
- `cE` and `sE` in `Event.v`: TFL language (Sec 5.1, Fig.5)
- `schedulerE` in `Concurrency.v`: SFL language (Sec 5.1, Fig.5)
- `interp_thread` and `interp_state` in `Concurrency.v`: TI (Sec 5.1, Fig.5)
- `interp_sched` in `Concurrency.v`: SI (Sec 5.1, Fig.5)
- `sched_nondet` in `Concurrency.v`: FAIRSch (Sec 5.2, Fig.6)
- CI (Sec 5.1, Fig.5) and IsFairSch (Definition 5.1) unfold into combination of the above definitions
#### Section 6
- In `src/semantics`
- This artifact contains an improved version of the module system compared to the paper. We will revise the paper accordingly.
- `Mod.t` in `Mod.v`: Mod (Sec 6, Fig.7)
- `ModAdd` and `OMod.close` in `Linking.v`: addition and close operations (Sec 6, Fig.7)
- `WMM.v`: FWMM (Sec 6.1, Fair Weak Memory Module)
#### Section 7
- `Weakest.v`: Sec 7 (Program Logic for Fairness) (See lemmas for `stsim`)

### Theorems
- In `src/simulation`
- `Theorem adequacy` in `Adequacy.v`: Theorem 4.1 (Adequacy)
- `Theorem modsim_adequacy` in `ModAdequacy.v`: Theorem 6.1 (Adequacy of module simulation)
- `Theorem usersim_adequacy` in `ModAdequacy.v`: Theorem 7.2 (Whole program adequacy)
- In `src/logic`
- `Lemma context_sim_implies_contextual_refinement` in `WeakestAdequacy.v`: Theorem 7.1 (Contextual adequacy)
- `Lemma whole_sim_implies_refinement` in `WeakestAdequacy.v`: Theorem 7.2 (Whole program adequacy)

### Examples
- In `src/example`
- `LockClientSC.v`: CL<sub>I</sub> and CL<sub>S</sub> (Sec 1, Sec 3, Sec 8); SC memory version (*the paper has typos, code in Sec 1 is the correct one*)
- `LockClientW.v`: CL<sub>I</sub> and CL<sub>S</sub> (Sec 1, Sec 3, Sec 8); weak memory version (*the paper has typos, code in Sec 1 is the correct one*)
- `FairLock.v`: ABSLock (Sec 3.1, Fig.2); `AbsLock` corresponds to the SC memory version, `AbsLockW` to the weak memory version.
- `TicketLockSC.v`: TicketLock (Sec 3.1); SC memory version
- `TicketLockW.v`: TicketLock (Sec 3.1); weak memory version
- `FIFOSched.v`: FIFOSch (Sec 5.2, Fig.6)
- `Theorem gsim_nondet_fifo` in `FIFOSchedSim.v`: Theorem 5.2 (FIFOSch is fair)
- `Lemma ticketlock_fair` in `TicketlockW.v`: Theorem 6.2 (TicketLock is Fair); weak memory
- `Lemma correct` in `LockClientW.v`: Module simulation between client modules; weak memory
- `Theorem client_all` in `LockClientWAll.v`: Case Study (Sec 8)

## Guides for Readers
minor diffs

