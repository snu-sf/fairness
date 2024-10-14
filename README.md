# Lilo
This artifact contains Coq development for the paper *Lilo: A Higher-Order, Relational Concurrent Separation Logic for Liveness*.
<!-- - `Lilo-source.zip` contains source code. -->
<!-- - `Lilo.zip` contains a docker image (`Lilo.tar`) where you can find the pre-compiled Coq development. -->
<!-- Use following commands to run the image: -->
<!-- ``` -->
<!-- sudo docker load < Lilo.tar -->
<!-- docker run -it Lilo /bin/bash -->
<!-- cd Lilo # in the container -->
<!-- ``` -->

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
- progress credits (◇) (Sec 3.1) : `progress_credit` in `LiveObligations.v`
- obligation lists (Obls<sub>i</sub>(Φ)) (Sec 3.1): `duty` in `LiveObligations.v`
- CRED-NEW (Sec 3.1, Fig.1) : `alloc_obligation` in `LiveObligations.v`
- PC-SPLIT (Sec 3.1, Fig.1) : `pc_split` in `LiveObligations.v`
- PC-DROP (Sec 3.1, Fig.1) : `pc_drop` in `LiveObligations.v`
- OBLS-ADD (Sec 3.1, Fig.1) : `duty_add` in `LiveObligations.v`
- OBLS-FULFILL (Sec 3.1, Fig.1) : `duty_fulfill` in `LiveObligations.v`
- PROM-GET (Sec 3.1, Fig.1) : `duty_tpromise` in `LiveObligations.v`
- scheduler credit (€) (Sec 3.2) : `fairness_credit` in `LiveObligations.v`
- promise (Sec 3.2, Fig.2) : `thread_promise` in `LiveObligations.v`
- credit bound (◆<sub>k</sub>⌈ℓ, n⌉) (Sec 3.2, Fig.2) : `liveness_obligation_fine` in `LiveObligations.v`
- PROM-PERS (Sec 3.2, Fig.2) : `Persistent_thread_promise` in `LiveObligations.v`
- PROM-PROGRESS (Sec 3.2, Fig.2) : `tpromise_progress` in `LiveObligations.v`
- CB-PERS (Sec 3.2, Fig.2) : `Persistent_liveness_obligation_fine` in `LiveObligations.v`
- CRED-IND (Sec 3.2, Fig.2) : `lo_ind_fine` in `LiveObligations.v`
- simulation weakest precondition (Sec 3.3, Fig.3) : `wpsim` in `SimWeakest.v`
- INV-ALLOC (Sec 3.3, Fig.3) : `FUpd_alloc` in `IndexedInvariants.v`
- INV-PERS (Sec 3.3, Fig.3) : `OwnI_persistent` in `IndexedInvariants.v`
- INV-OPEN (Sec 3.3, Fig.3) : `FUpd_open` in `IndexedInvariants.v`
- INV-CLOSE (Sec 3.3, Fig.3) : `FUpd_open` in `IndexedInvariants.v`
- MEM-READ (Sec 3.3, Fig.3) : `SCMem_load_fun_spec` in `SCMemSpec.v`
- MEM-WRITE (Sec 3.3, Fig.3) : `SCMem_store_fun_spec` in `SCMemSpec.v`
- YIELD-TGT (Sec 3.3, Fig.3) : `wpsim_yieldR_gen` in `SimWeakest.v`
- SIM-TERM (Sec 3.3, Fig.3) : `wpsim_ret` in `SimWeakest.v`
- Theorem 3.1 (Adequacy) : `Theorem whole_sim_implies_refinement` in `SimWeakestAdequacy.v` (the paper presents a slightly simplified form)

#### Section 4
##### In `src/tlogic`
- obligation link (κ1 -◇ κ2) (Sec 4.2, Fig.4) : `link` in `LiveObligations.v`
- LINK-PERS (Sec 4.2, Fig.4) : `Persistent_link` in `IndexedInvariants.v`
- LINK-NEW (Sec 4.2, Fig.4) : `link_new_fine` in `LiveObligations.v`
- LINK-AMP (Sec 4.2, Fig.4) : `link_amplify` in `LiveObligations.v`
- LINK-TRANS (Sec 4.2, Fig.4) : `link_trans` in `LiveObligations.v`

#### Section 5
##### In `src/tlogic`
- sProp<sub>i</sub> (Sec 5.1, Fig.4): `sProp` in `LogicSyntaxHOAS.v`
- types &#964;(τ) in sProp<sub>i</sub> (Sec 5.1, Fig.4): `type` in `TemporalLogic.v`
- type interpretation 𝓘 of τ in sProp<sub>i</sub> (Sec 5.1, Fig.4): `type_interp` in `TemporalLogic.v`
- type of predicates φ of sProp<sub>i</sub> (Sec 5.1, Fig.4): `sPropT` in `TemporalLogic.v`
- atoms of sProp<sub>i</sub> (Sec 5.1, Fig.4): `Atom.t` in `TemporalLogic.v` (also includes additional constructors to facilitate the development)
- semantic interpretation ⟦⋅⟧ of sProp<sub>i</sub> (Sec 5.1, Fig.4): `SyntaxI.interp` in `LogicSyntaxHOAS.v`
- stratified world satisfaction W<sub>i</sub> (Sec 5.2): `syn_wsat` in `TemporalLogic.v`
- worlds satisfaction Ws<sub>n</sub> (Sec 5.2): `syn_wsats` in `TemporalLogic.v`
- fancy update modality (Sec 5.3, Fig.5): `FUpd` in `IndexedInvariants.v` and `syn_fupd` in `TemporalLogic.v`
- INV-ALLOC (Sec 3.3, Fig.2): `FUpd_alloc` in `IndexedInvariants.v`
- INV-OPEN (Sec 5.3, Fig.5): `FUpd_open` in `IndexedInvariants.v`
- INV-CLOSE (Sec 5.3, Fig.5): `FUpd_open` in `IndexedInvariants.v`

#### Section 6
##### In `src/tlogic`
- delayed promise (Sec 6, Fig.6): `delayed_tpromise` in `LiveObligations.v`
- activation token &#10710;(⧖) (Sec 6, Fig.6): `pending_obligation` in `LiveObligations.v`
- activated token &#8904;(⋈) (Sec 6, Fig.6): `active_obligation` in `LiveObligations.v`
- ACTIVATE (Sec 6, Fig.6): `pending_active` in `LiveObligations.v`
- NOT-ACT (Sec 6, Fig.6): `pending_not_active` in `LiveObligations.v`
- OMAP-ADD2 (Sec 6.2, Fig.3): `duty_add` in `LiveObligations.v`
- DP-ACT (Sec 6, Fig.6): `activate_tpromise` in `LiveObligations.v`
- YIELD-TGT2 (Sec 6, Fig.6): `wpsim_yieldR_gen_pending` in `SimWeakest.v`

### Case Studies and Examples
##### In `src/example`
- SL-PASS (Sec 7.1): `pass_lock` in `SpinlockSpec0.v`
- Generalized spinlock specification and view shift rule (Sec 7.1): `Spinlock_lock_spec` and `update_isSpinlock` in `SpinlockSpecUpdate.v`
- INF-MP and INF-MP-SPEC (Sec 2, Sec 7): `Client04.v`
- MP and MP<sub>S</sub> (Sec 2, Sec 3): `Client01.v`
- SCH-ND and SCH-ND-SPEC (Sec 2, Sec 7): `Client05.v`
- Ticketlock (Sec 7.1): `TicketLock.v`
- LP and LP-SPEC (Sec 7.3): `ClientSpinlock2.v`
##### In `src/example/treiber`
- HT-ST (Sec 7.2): `Treiber_push_spec` in `SpecHOCAP.v`
- Treiber-Stack (Sec 7.2): `SpecHOCAP.v`
- STACK-MP (Sec 7.2): `ClientSpecHOCAP.v`
##### In `src/example/elimstack`
- HT-ST (Sec 7.2): `Elim_push_spec` in `SpecHOCAP.v`
- Elimination-Stack (Sec 7.2): `SpecHOCAP.v`
- STACK-MP (Sec 7.2): `ClientSpecHOCAP.v`
