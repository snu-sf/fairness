# Lilo
This artifact contains Coq development for the paper *Lilo: A Higher-Order, Relational Concurrent Separation Logic for Liveness*.

## Build
Requirement: `opam` (>=2.0.0). You can run `opam --version` to check if `opam` is installed. You will need at least version 2.0.0. If `opam` is not already installed, follow instructions at: https://opam.ocaml.org/doc/Install.html
- Create and initialize a new opam switch
```
opam switch create . ocaml-base-compiler.4.14.2 --no-install
eval $(opam env)
```
- Install dependencies with opam
```
./configure
```
- Build the project
```
make -j
```

## Code Structure

### Notable Gaps Between the Paper and the Code
We first describe the most relevant differences between the paper and 
the code to help readers of the paper understand the code.
Please see the "Definitions and Rules" section of this document for a mapping of definitions and rules between the paper and the code.

#### Auxiliary definitions for state interpretation
In the paper, the state interpretation predicate (that is needed to relate the memory state to points-to predicates in the logic) is assumed to be hidden inside the simulation weakest precondition.
However, the state interpretation predicate is made explicit in the code, and it is called `tgt_interp_as`, defined in `src/ra/OpticsInterp.v`.
This predicate is persistent (so not consumed), and when combined with a points-to predicate `X ↦ v`, tells us that the current value at the memory location `X` is `v`.

#### Notations related to stratified propositions (`sProp`s)
The code relies heavily on `sProp`s, and it is helpful to get familiar with the notations before getting to the rules and examples.
There are two files that are most directly related.

`src/tlogic/LogicSyntaxHOAS.v` defines `sProp` in a general form, parametrizing types and atoms.
This file also defines a set of notations and a scope `sProp_scope` for them (`%S` denotes that a predicate is a `sProp`).
Notations follow the ones in Iris, with some additional ones to notate atoms (`Syntax.atom`), first-order ghost states (`Syntax.ownM`), and the lift (`Syntax.lift`).

`src/tlogic/TemporalLogic.v` instantiates `sProp` by defining concrete types (`type`) and atoms (`Atom.t`).
We remark that `Atom.t` includes some predicates for first-order ghost states: they can be optimized away by encoding them using `Syntax.ownM`, but we choose this design to make the development easier.
Among many notations, the most important ones are those for the interpretations:
`τ{t, n}` is the type interpretation (`sType.interp`), converting a `sProp` type `t` into a corresponding Coq Type with the stratification index `n`.
`⟦F, n⟧` is the predicate interpretation (`SyntaxI.interp`), converting a `sProp` into a `iProp`.
Lemmas in `Section RED.` can be helpful to see how `sProp`s are interpreted into `iProp`s.

In addition, `src/tlogic/TemporalLogic.v` develops `sProp` encodings of core logical predicates of Lilo, such as the invariants and the liveness-related predicates.
Note that the original definition, namely `iProp`s, of these logical predicates are defined in different files (such as `src/ra/IndexedInvariants.v` and `src/tlogic/LiveObligations.v`).
The original definitions and their `sProp` encodings share the same notation.

#### Hoare triples
Many rules and examples in the code heavily utilize Hoare triples, which is defined in `src/tlogic/SimWeakest.v`, in particular utilizing the general definition `triple_gen`, along with the simulation weakest precondition `wpsim`.
The file also contains notations for the triples, and `src/tlogic/TemporalLogic.v` defines the `sProp` encodings of the triples, with the `sProp` version of the notations.

As an example to show how the triples are used, we describe how the MEM-READ rule in the paper (Sec 3.3, Fig.3) appears in the code.
The MEM-READ rule corresponds to the `SCMem_load_fun_spec` lemma in `src/example/SCMemSpec.v` (`SCMem_load_fun_syn_spec` is the `sProp` version of the rule, but this is not used in practice because when we are writing proofs, we usually convert `sProp`s into `iProp`s to utilize the Iris Proof Mode).

This lemma includes some details omitted in the paper.
First, the lemma is stated in the form of a triple and includes the details related to `sProp`, such as the stratification index.
One can unfold the triple to check that it is equivalent to MEM-READ.
Next, the rule requires the state interpretation `tgt_interp_as` in the precondition.
`tgt_interp_as` is persistent, so the lemma does not consume it.
Additionally, the program code is decorated with `map_event`, which is a boilerplate code inherited from the development of Fair Operational Semantics, and it is not relevant to Lilo.

Finally, the `SCMem_load_fun_spec_gen` lemma is a generalized version of the rule that is required when one needs to work with nontrivial stratification indices.
For example, we use this lemma for the elimination stack example (`src/example/elimstack/SpecHOCAP.v`), which involves nontrivial details related to stratification indices, as discussed in the paper.

#### Additional features of the logic
Some of the logical predicates for liveness reasoning are presented in a general form in the code: `src/tlogic/LiveObligations.v` contains the definitions for liveness predicates such as obligations, promises, and progress credits (please see the "Definitions and Rules" section for a mapping between the definitions).
We tried to keep the notations similar between the paper and the code, and we believe it is mostly successful.

However, a few notations are slightly different from the ones in the paper:
- Paper: Obls<sub>th</sub>(Φ) (obligation lists), Code: `Duty (th) Φ`.
- A promise is written `-[𝜅](a)-◇ f` and a link is written `s -(a)-◇ t` in the code, with an additional parameter `a`. This parameter `a` allows the user to obtain more progress credits when using the rules PROM-PROGRESS and LINK-AMP: with a larger `a`, the user can get more progress credits. However, the user needs to give up more progress credits when creating a promise or a link with a larger `a`. The paper assumes `a` = 0 to simplify discussions.
- The activation token ⧖<sub>𝜅</sub> has an additional parameter `q` in the code: `⧖[k , q]`. `q` denotes fractional ownership, and the paper assumes `q` = 1/2 and omits it for simplicity.

### Definitions and Rules
Definitions and rules in the code are more general compared to the corresponding ones presented in the paper.
Also, the code includes the full detail related to the stratified propositions.

#### Section 3
- progress credits (◇<sub>𝜅</sub>(ℓ, n)) (Sec 3.1) : `progress_credit` in `src/tlogic/LiveObligations.v`
- obligation lists (Obls<sub>th</sub>(Φ)) (Sec 3.1): `duty` in `src/tlogic/LiveObligations.v`
- CRED-NEW (Sec 3.1, Fig.1) : `alloc_obligation_fine` in `src/tlogic/LiveObligations.v`
- PC-SPLIT (Sec 3.1, Fig.1) : `pc_split` in `src/tlogic/LiveObligations.v`
- PC-DROP (Sec 3.1, Fig.1) : `pc_drop` in `src/tlogic/LiveObligations.v`
- OBLS-ADD (Sec 3.1, Fig.1) : `duty_add` in `src/tlogic/LiveObligations.v`
- OBLS-FULFILL (Sec 3.1, Fig.1) : `duty_fulfill` in `src/tlogic/LiveObligations.v`
- PROM-GET (Sec 3.1, Fig.1) : `duty_tpromise` in `src/tlogic/LiveObligations.v`
- scheduler credit (€) (Sec 3.2) : `thread_credit` in `src/tlogic/LiveObligations.v`
- promise (Sec 3.2, Fig.2) : `thread_promise` in `src/tlogic/LiveObligations.v`
- credit bound (◆<sub>𝜅</sub>⌈ℓ, n⌉) (Sec 3.2, Fig.2) : `liveness_obligation_fine` in `src/tlogic/LiveObligations.v`
- PROM-PERS (Sec 3.2, Fig.2) : `Persistent_thread_promise` in `src/tlogic/LiveObligations.v`
- PROM-PROGRESS (Sec 3.2, Fig.2) : `tpromise_progress` in `src/tlogic/LiveObligations.v`
- CB-PERS (Sec 3.2, Fig.2) : `Persistent_liveness_obligation_fine` in `src/tlogic/LiveObligations.v`
- CRED-IND (Sec 3.2, Fig.2) : `lo_ind_fine` in `src/tlogic/LiveObligations.v`
- simulation weakest precondition (Sec 3.3, Fig.3) : `wpsim` in `src/tlogic/SimWeakest.v`
- INV-ALLOC (Sec 3.3, Fig.3) : `FUpd_alloc` in `src/ra/IndexedInvariants.v`
- INV-PERS (Sec 3.3, Fig.3) : `OwnI_persistent` in `src/ra/IndexedInvariants.v`
- INV-OPEN (Sec 3.3, Fig.3) : `FUpd_open` in `src/ra/IndexedInvariants.v`
- INV-CLOSE (Sec 3.3, Fig.3) : `FUpd_open` in `src/ra/IndexedInvariants.v`
- MEM-READ (Sec 3.3, Fig.3) : `SCMem_load_fun_spec` in `src/example/SCMemSpec.v`
- MEM-WRITE (Sec 3.3, Fig.3) : `SCMem_store_fun_spec` in `src/example/SCMemSpec.v`
- YIELD-TGT (Sec 3.3, Fig.3) : `wpsim_yieldR_gen` in `src/tlogic/SimWeakest.v`
- SIM-TERM (Sec 3.3, Fig.3) : `wpsim_ret` in `src/tlogic/SimWeakest.v`
- Theorem 3.1 (Adequacy) : `Theorem whole_sim_implies_refinement` in `src/tlogic/SimWeakestAdequacy.v` (the paper presents a simplified form)

#### Section 4
- obligation link (κ1 -◇ κ2) (Sec 4.2, Fig.4) : `link` in `src/tlogic/LiveObligations.v`
- LINK-PERS (Sec 4.2, Fig.4) : `Persistent_link` in `src/tlogic/LiveObligations.v`
- LINK-NEW (Sec 4.2, Fig.4) : `link_new_fine` in `src/tlogic/LiveObligations.v`
- LINK-AMP (Sec 4.2, Fig.4) : `link_amplify` in `src/tlogic/LiveObligations.v`
- LINK-TRANS (Sec 4.2, Fig.4) : `link_trans` in `src/tlogic/LiveObligations.v`

#### Section 5
- sProp<sub>i</sub> (Sec 5.1, Fig.5): Definition `sProp` in `src/tlogic/LogicSyntaxHOAS.v`
- types &#964;(τ) in sProp<sub>i</sub> (Sec 5.1, Fig.5): `type` in `src/tlogic/TemporalLogic.v`
- type interpretation I of τ in sProp<sub>i</sub> (Sec 5.1, Fig.5): `type_interp` in `src/tlogic/TemporalLogic.v`
- type of predicates φ of sProp<sub>i</sub> (Sec 5.1, Fig.5): `sPropT` in `src/tlogic/TemporalLogic.v`
- atoms of sProp<sub>i</sub> (Sec 5.1, Fig.5): `Atom.t` (type t in Module Atom) in `src/tlogic/TemporalLogic.v` (also includes additional constructors to facilitate the development)
- semantic interpretation ⟦⋅⟧ of sProp<sub>i</sub> (Sec 5.1, Fig.5): `SyntaxI.interp` in `src/tlogic/LogicSyntaxHOAS.v`
- stratified world satisfaction W<sub>i</sub> (Sec 5.2): `syn_wsat` in `src/tlogic/TemporalLogic.v`
- world satisfactions Ws<sub>n</sub> (Sec 5.2): `syn_wsats` in `src/tlogic/TemporalLogic.v`
- FUPD-DEF (Sec 5.2, Fig 6): `FUpd` in `src/ra/IndexedInvariants.v` and `syn_fupd` in `src/tlogic/TemporalLogic.v`
- INV-ALLOC (Sec 5.2, Fig.6): `FUpd_alloc` in `src/ra/IndexedInvariants.v`
- INV-OPEN (Sec 5.2, Fig.6): `FUpd_open` in `src/ra/IndexedInvariants.v`
- INV-CLOSE (Sec 5.2, Fig.6): `FUpd_open` in `src/ra/IndexedInvariants.v`

#### Section 6
- delayed promise (Sec 6, Fig.7): `thread_delayed_promise` in `src/tlogic/LiveObligations.v`
- activation token &#10710;(⧖) (Sec 6, Fig.7): `pending_obligation` in `src/tlogic/LiveObligations.v`
- activated token &#8904;(⋈) (Sec 6, Fig.7): `active_obligation` in `src/tlogic/LiveObligations.v`
- ACTIVATE (Sec 6, Fig.7): `pending_active` in `src/tlogic/LiveObligations.v`
- NOT-ACT (Sec 6, Fig.7): `pending_not_active` in `src/tlogic/LiveObligations.v`
- CRED-NEW2 (Sec 6, Fig.7): `alloc_obligation_fine` in `src/tlogic/LiveObligations.v`
- OBLS-ADD2 (Sec 6, Fig.7): `duty_add` in `src/tlogic/LiveObligations.v`
- OBLS-FULFILL2 (Sec 6, Fig.7): `duty_fulfill` in `src/tlogic/LiveObligations.v`
- DP-PERS (Sec 6, Fig.7): `Persistent_thread_delayed_promise` in `src/tlogic/LiveObligations.v`
- DP-GET (Sec 6, Fig.7): `duty_delayed_promise` in `src/tlogic/LiveObligations.v`
- DP-ACT (Sec 6, Fig.7): `activate_tpromise` in `src/tlogic/LiveObligations.v`
- PROM-DEF (Sec 6, Fig.7): `unfold_promise` in `src/tlogic/LiveObligations.v`
- YIELD-TGT2 (Sec 6, Fig.7): `wpsim_yieldR_gen_pending` in `src/tlogic/SimWeakest.v`

### Case Studies and Examples
##### In `src/example`
- MP and MP<sub>S</sub> (Sec 2, Sec 3): `Client01.v`
- Specification of spinlock (Sec 4): `SpinlockSpec0.v`
- INCR_B (Sec 4.3): `DoubleIncrTicket.v`
- SL-PASS (Sec 7.1): `pass_lock` in `SpinlockSpec0.v`
- Generalized spinlock specification and view shift rules (Sec 7.1): `Spinlock_lock_spec` and `update_isSpinlock` in `SpinlockSpecUpdate.v`
- Ticketlock (Sec 7.1): `TicketLock.v`
- INF-MP and INF-MP-SPEC (Sec 2.1, Sec 7.3): `Client04.v`
- LP (Sec 7.3): `ClientSpinlock2.v`
- SCH-ND (Sec 2.1, Sec 7.3): `Client05.v`
- `fos_ticketlock/` contains the Lilo version of the weak memory ticket lock example from Fair Operational Semantics.
##### In `src/example/treiber`
- HT-ST (Sec 7.2): `Treiber_push_spec` in `SpecHOCAP.v`
- Treiber-Stack (Sec 7.2): `SpecHOCAP.v`
- STACK-MP (Sec 7.2): `ClientSpecHOCAP.v`
##### In `src/example/elimstack`
- HT-ST (Sec 7.2): `Elim_push_spec` in `SpecHOCAP.v`
- Elimination-Stack (Sec 7.2): `SpecHOCAP.v`
- STACK-MP (Sec 7.2): `ClientSpecHOCAP.v`
