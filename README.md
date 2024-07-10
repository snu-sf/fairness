# Lilo
This artifact contains Coq development for the paper *Lilo: A higher-order, relational concurrent separation logic for liveness*.
- `Lilo-source.zip` contains source code.
- `Lilo.zip` contains a docker image (`Lilo.tar`) where you can find the pre-compiled Coq development.
Use following commands to run the image:
```
sudo docker load < Lilo.tar
docker run -it Lilo /bin/bash
cd Lilo # in the container
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
### Definitions and Rules
#### Section 3
##### In `src/tlogic`
- `duty` in `LiveObligations.v`: obligation map (Obls<sub>i</sub>(Φ)) (Sec 3.2, Fig.1)
- `duty_add` in `LiveObligations.v`: OMAP-ADD (Sec 3.2, Fig.1)
- `duty_fulfill` in `LiveObligations.v`: OMAP-FULFILL (Sec 3.2, Fig.1)
- `progress_credit` in `LiveObligations.v`: progress credits (◇) (Sec 3.2, Fig.1)
- `pc_split` in `LiveObligations.v`: PC-SPLIT (Sec 3.2, Fig.1)
- `pc_drop` in `LiveObligations.v`: PC-DROP (Sec 3.2, Fig.1)
- `thread_promise` in `LiveObligations.v`: thread promise (Sec 3.2, Fig.1)
- `duty_tpromise` in `LiveObligations.v`: PROM-GET (Sec 3.2, Fig.1)
- `tpromise_progress` in `LiveObligations.v`: PROM-PROGRESS (Sec 3.2, Fig.1)
- `tpromise_ind` in `LiveObligations.v`: PROM-IND (Sec 3.2, Fig.1)
- `wpsim` in `SimWeakest.v`: simulation relation (Sec 3.3, Fig.2)
- `wpsim_yieldR` in `SimWeakest.v`: YIELD-TGT (Sec 3.3, Fig.2)
- `wpsim_ret` in `SimWeakest.v`: SIM-TERM (Sec 3.3, Fig.2)
##### In `src/example`
- `SCMem_load_fun_spec` in `SCMemSpec.v`: MEM-READ (Sec 3.3, Fig.2)
- `SCMem_store_fun_spec` in `SCMemSpec.v`: MEM-WRITE (Sec 3.3, Fig.2)


#### Section 4
##### In `src/tlogic`
- `liveness_obligation_fine` in `LiveObligations.v`: liveness obligation (◆<sub>k</sub>⌈ℓ, n⌉) (Sec 4.2, Fig.3)
- `alloc_obligation_fine` in `LiveObligations.v`: OBL-NEW (Sec 4.2, Fig.3)
- `lo_ind_fine` in `LiveObligations.v`: OBL-NEW (Sec 4.2, Fig.3)
- `link` in `LiveObligations.v`: obligation link (◆<sub>k</sub>⌈ℓ, n⌉) (Sec 4.2, Fig.3)
- `link_new_fine` in `LiveObligations.v`: LINK-NEW (Sec 4.2, Fig.3)
- `link_amplify` in `LiveObligations.v`: LINK-AMP (Sec 4.2, Fig.3)
- `link_trans` in `LiveObligations.v`: LINK-TRANS (Sec 4.2, Fig.3)

#### Section 5
##### In `src/tlogic`
- `sProp` in `LogicSyntaxHOAS.v`: sProp<sub>i</sub> (Sec 5.1, Fig.4)
- `type` in `TemporalLogic.v`: types &#964;(τ) in sProp<sub>i</sub> (Sec 5.1, Fig.4)
- `type_interp` in `TemporalLogic.v`: type interpretation 𝓘 of τ in sProp<sub>i</sub> (Sec 5.1, Fig.4)
- `sPropT` in `TemporalLogic.v`: special type φ of sProp<sub>i</sub> (Sec 5.1, Fig.4)
- `SyntaxI.interp` in `LogicSyntaxHOAS.v`: semantic interpretation ⟦⋅⟧ of sProp<sub>i</sub> (Sec 5.1, Fig.4)
- `syn_wsat` in `TemporalLogic.v`: stratified world satisfaction W<sub>i</sub> (Sec 5.2)
- `FUpd` in `IndexedInvariants.v`: fancy update modality (Sec 5.3, Fig.5)

#### Section 6
##### In `src/tlogic`
- `delayed_tpromise` in `LiveObligations.v`: delayed promise (Sec 6.1, Fig.6)
- `pending_obligation` in `LiveObligations.v`: activation token &#10710;(⧖) (Sec 6.1, Fig.6)
- `active_obligation` in `LiveObligations.v`: activated token &#8904;(⋈) (Sec 6.1, Fig.6)
- `pending_active` in `LiveObligations.v`: ACTIVATE (Sec 6.1, Fig.6)
- `pending_not_active` in `LiveObligations.v`: NOT-ACT (Sec 6.1, Fig.6)
- `activate_tpromise` in `LiveObligations.v`: DP-ACT (Sec 6.1, Fig.6)
- `wpsim_yieldR_gen_pending` in `LiveObligations.v`: YIELD-TGT2 (Sec 6.1, Fig.6)

#### Section 7
##### In `src/example`
- `update_isSpinlock` in `SpinlockSpecUpdate.v`: SL-UPDATE (Sec 7.1)
- `pass_lock` in `SpinlockSpec0.v`: SL-PASS (Sec 7.1)
  
### Theorems
##### In `src/tlogic`
- `Theorem whole_sim_simple_implies_refinement` in `SimWeakestAdequacy.v`: Theorem 6.1 (Adequacy)

### Case Studies and Examples
##### In `src/example`
- `Client01.v`: SIG and SIG<sub>S</sub> (Sec 2, Sec 3)
- `Client04.v`: INF-SIG and INF-SIG-SPEC (Sec 2, Sec 7)
- `Client05.v`: SCH-ND and SCH-ND-SPEC (Sec 2, Sec 7)
- `TicketLock.v`: Ticketlock (Sec 7.1)
##### In `src/example/treiber`
- `SpecHOCAP.v`: Treiber-Stack (Sec 7)
##### In `src/example/elimstack`
- `SpecHOCAP.v`: Elimination-Stack (Sec 7)
