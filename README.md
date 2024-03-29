# Fair Operational Semantics

This artifact contains Coq development for the paper *Fair Operational Semantics*.
- `fairness-source.zip` contains source code.
- `fairness.zip` contains a docker image (`fairness.tar`) where you can find the pre-compiled Coq development.
Use following commands to run the image:
```
sudo docker load < fairness.tar
docker run -it pldi2023ae /bin/bash
cd fairness # in the container
```

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
##### In `src/semantics`
- `eventE` in `Event.v`: FL language (Sec 4.1, Fig.3)
- `RawTr.t` in `SelectBeh.v`: Trace (Sec 4.1, Fig.3)
- `Tr.t` in `FairBeh.v`: Behavior (Sec 4.1, Fig.3)
- `RawTr.is_fair` in `SelectBeh.v`: FairTr (Sec 4.1, Fig.3)
- `imap` in `FairBeh.v`: cmap (Sec 4.2, Fig.4)
##### In `src/simulation`
- `improves` in `Adequacy.v`: whole-program refinement (Sec 4.1)
- `sim` in `FairSim.v`: simulation relation (Sec 4.2)
#### Section 5
##### In `src/semantics`
- `cE` and `sE` in `Event.v`: TFL language (Sec 5.1, Fig.5)
- `schedulerE` in `Concurrency.v`: SFL language (Sec 5.1, Fig.5)
- `interp_thread` and `interp_state` in `Concurrency.v`: TI (Sec 5.1, Fig.5)
- `interp_sched` in `Concurrency.v`: SI (Sec 5.1, Fig.5)
- `interp_concurrency` in `Concurrency.v`: CI (Sec 5.1, Fig.5)
- `sched_nondet` in `Concurrency.v`: FAIRSch (Sec 5.2, Fig.6)
##### In `src/simulation`
- `isFairSch` in `SchedSim.v`: IsFairSch (Sec 5.2, Definition 5.1)
#### Section 6
##### In `src/semantics`
- `programE` in `EventE`: OTFL (Sec 6, Fig.7)
- `program` in `Mod.v`: corresponds to Config (Sec 6, Fig.7)
- `prog2ths` in `Concurrency.v`: corresponds to Load (Sec 6, Fig.7)
- `Mod.t` in `Mod.v`: Mod (also OMod) (Sec 6, Fig.7); see the guide below
- `ModAdd` and `OMod.close` in `Linking.v`: linking and close operations (Sec 6, Fig.7)
##### In `src/simulation`
- `Theorem ModAdd_comm` and `Theorem ModAdd_right_mono` in `ModAddSim.v`: properties of the module linking operation (Sec 6, Fig.7)
- `Theorem ModClose_mono` in `ModCloseSim.v`: properties of the module close operation (Sec 6, Fig.7)
##### In `src/example`
- `WMM.v`: FWMM (Sec 6.1, Fair Weak Memory Module)
#### Section 7
##### In `src/logic`
- `FairRA.white` in `FairRA.v`: &#8885; (⊵) (Sec 7, Fig.8); also see related lemmas for the rules
- `FairRA.black` in `FairRA.v`: &#9830; (♦) (Sec 7, Fig.8); also see related lemmas for the rules
- `FairRA.white i 1` in `FairaRA.v`: &#9826;(i) (♢(i)) (Sec 7, Fig.8); actually a simple wrapper of &#8885;
- `stsim` in `Weakest.v`: corresponds to sim (Sec 7, Fig.8)
- `stsim_fairL` in `Weakest.v`: WIN-SRC and LOSE-SRC (Sec 7, Fig.8)
- `stsim_fairR_simple` in `Weakest.v`: WIN-TGT and LOSE-TGT (Sec 7, Fig.8)
- `stsim_yieldL` in `Weakest.v`: YIELD-SRC (Sec 7, Fig.8)
- `stsim_yieldR_simple` and `stsim_sync_simple` in `Weakest.v`: YIELD-TGT (Sec 7, Fig.8)
- `Weakest.v`: contains full program logic for fairness (Sec 7); see lemmas for `stsim`

### Theorems
##### In `src/simulation`
- `Theorem adequacy` in `Adequacy.v`: Theorem 4.1 (Adequacy)
- `Theorem modsim_adequacy` in `ModAdequacy.v`: Theorem 6.1 (Adequacy of module simulation)
- `Theorem usersim_adequacy` in `ModAdequacy.v`: Theorem 7.2 (Whole program adequacy)
##### In `src/logic`
- `Theorem context_sim_simple_implies_contextual_refinement` in `WeakestAdequacy.v`: Theorem 7.1 (Contextual adequacy)
- `Theorem whole_sim_simple_implies_refinement` in `WeakestAdequacy.v`: Theorem 7.2 (Whole program adequacy)

### Examples
##### In `src/example`
- `LockClientSC.v`: CL<sub>I</sub> and CL<sub>S</sub> (Sec 1, Sec 3, Sec 8); SC memory version (*the paper has typos, code in Sec 1 is the correct one*)
- `LockClientW.v`: CL<sub>I</sub> and CL<sub>S</sub> (Sec 1, Sec 3, Sec 8); weak memory version (*the paper has typos, code in Sec 1 is the correct one*)
- `FairLock.v`: ABSLock (Sec 3.1, Fig.2); `AbsLock` corresponds to the SC memory version, `AbsLockW` to the weak memory version.
- `TicketLockSC.v`: TicketLock (Sec 3.1); SC memory version
- `TicketLockW.v`: TicketLock (Sec 3.1); weak memory version
- `FIFOSched.v`: FIFOSch (Sec 5.2, Fig.6)
- `Theorem fifo_is_fair` in `FIFOSchedSim.v`: Theorem 5.2 (FIFOSch is fair)
- `Lemma ticketlock_fair` in `TicketlockW.v`: Theorem 6.2 (TicketLock is Fair); weak memory
- `Lemma correct` in `LockClientW.v`: Module simulation between client modules; weak memory
- `Theorem client_all` in `LockClientWAll.v`: Case Study (Sec 8)

## Guide for Readers
### Remark on Section 6
This artifact contains an improved version of the module system compared to the paper. We will revise the paper accordingly. The main difference is that Mod is extended to include OMod (Sec 6, Fig.7) and OMod is removed.
### Remark on Section 7
The paper is currently missing update modalities for MONO and DEC rules in Sec 7, Fig.8. We will correct the paper. We also developed additional lemmas for `stsim` to reduce proof complexity, as can be found in `src/logic/Weakest.v`. Proof of the case study is based on those lemmas, as can be found in `src/example/`.
