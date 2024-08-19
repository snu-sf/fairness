# Refactor Iris

- The goal of this document is to dump the basic definitions of Iris CMRAs and own that used after the refactoring by Janggun Lee.
- It is meant to be read by someone that understand the "old" RA.t and URA.t definitions.
- For a more comprehensive introduction, read the "Iris from the ground up" paper or
  [the Coq implementation](https://gitlab.mpi-sws.org/iris/iris).
- The content was written at 2024-08-20, based on Iris 4.2.0.

## Why the refactoring?

- I was bored.
- Jokes aside, the main reason is (1) strictly reusing Iris constructions to reduce
  proof burden (2) not re-doing logic level Iris proofs (3) making Lilo work well
  with IPM.
- For 1, I don't mean high-level resue like "we take ideas from Iris's auth cmra",
  but literally being able to import `iris.algebra` at the coq level and use it, without having to define a single line of additional cmra metathory in Coq.
  - For example, proper usage of auth cmra (and advanced variants) requires the
    concept of "local-updates", which is not present in the current general form of Lilo.
  - I needed such advanded variant of auth for proofs of stacks, and had to copy and
    paste the entierty of `iris/algebra` source code and hand-remove the parts
    related to step indexing. I would rather not do it twice, especially since the
    Iris codebase also improves over time.
  - While doing this, I realized that such copying was not fundamental, but rather,
    the current construction of Lilo was the issue. So I decided to refactor Lilo
    during the downtime after the POPL 2025 deadline.
- For 2, one might think it is subsumed by 1. Unfortunatly, the base_logic
  layer of Iris cannot be taken as is, as it fundamentally a step-indexed
  logic. We can, however, copy the entire codebase and remove the
  step-indexing parts, and after that get all the ghost libaries "for free".
- For 3, IPM has an insane amount of typeclasses to help user proofs, and is still
  expanding. However, they aren't always easy to work with, and I kept on getting
  weird typeclass failures, which can be (1) a missed typeclass instance (2) some
  other fundamental bug that is very hard to debug. Making the construction of the
  logic in Lilo closer to that of Iris ensures that such problems are less likely,
  and in the case of one, most likely the same in Iris, so we can get help from Iris
  maintainers.

## ofe

- In Lilo, the type of carrier for RA are simply any Coq `Type`.
- In Iris, the carrier of a CMRA is an ordered family of equivalences (ofe).
- OFE is an setoid (O,(≡)) that has an **n-equivalence** relation for every n,
  (dist in Coq, notation ≡{n}≡), which satisfies the following properties.
  - ∀ n, x ≡ y → dist n x y
  - (∀ n, dist n x y) → x ≡ y
  - ∀ n m, n < m → dist n x y → dist m x y.
- It is more general than `Type` as it allows are custom equivalences, but more restrictive due to the existance of dist.

### Discrete ofe

- Dist is required to solve the cycle in the standard model of iProp supporting higher-order ghost state.
- Lilo takes an alternative approach, so it would be nice if we can ignore dist.
- To enforce this, iris supports the notion of **discrete OFEs**.
- Discrete OFEs are OFEs where equivalence at level 0 implies equivalence at all levels.
  - ∀ x y, x ≡{0}≡ y → x ≡ y.
- Combined with the fact that equivalence is stronger than dist and dist is monotone, this that dist and equivalence are equivalent.
- For Discrete OFEs, we can ignore dist and treat them as normal setoids.
- Iris comes with many lemmas the simplify working with discrete ofes.

## cmra

- In Lilo, RA.t is a type that with on binary operation (⋅) and unary wellformedness WF, such that
  - ⋅ is associativitve and commutativive.
  - WF is monotonically decresing w.r.t (⋅). I.e, WF (a ⋅ b) → WF a.
- CMRAs are OFE with a binary operation ⋅, unary validity ✓, unary **n-validity** ✓{n}, and a partical function **pcore** such that
  - ⋅ is associative and commutative.
  - ✓, ✓{n} is monotonically decresing w.r.t (⋅).
  - ✓ x ↔ ∀ n, ✓{n} x.
  - ✓{S n} x → ✓{n} x.
  - and various pcore axioms, explained later.
- Lilo also has the notions of "extends" and "updates", and "updates_set". In Iris, these are called included (≼), cmra_update (\~~>), and cmra_updateP (~~>: P).

### Core of a cmra

- In Lilo, only URA.t, a modification of RA.t with a unit element, has a core.
- In Iris, all CMRAs have a partial core, which suppors the followings.
  - pcore x ≡ Some cx → cx ⋅ x = x.
  - x ≼ y → pcore x ≡ Some cx → ∃ cy, pcore y ≡ Some cy ∧ cx ≼ cy.
- The first law ensures that cores do not "add information"
- The second law ensures that cores are monotonic w.r.t ≼.

#### total cmras and ucmras

- For many cases, the core is total, i.e., ∀ x, is_Some (pcore x), and it would be convenient to have a total core in such cases.
- Iris has the `CmraTotal` typeclass for such cmras, and it makes working with cores easier.
- One of the most prominent examples of such cmras are unitial cmras, which are cmras with a unit element ε w.r.t ⋅, and core ε = ε, and ✓ ε.
- Another example is the option cmra combination optionUR A, which takes an cmra (not a ucmra!) and makes a ucmra.

#### reason for partial cores

- One may wonder why non-unital cmras and partial cores exist at all, and not just have unly initial cmras.
- This is because many cmras don't have a natural notion of total core, and forcing them into a ucmra would be unnatural.
- For example, in the auth cmra, the auth element does not have a notion of a core. Enforing a total core would require adding a third element to the cmra, which would be (1) unnatural; and (2) is essentially packing the option cmra into every cmra, which is imply inefficient.

- For the reason for having cores at all, this enables one to make persistent elements when owning a element of a CMRA.
- For example, the frag part of the auth cmra does have a notion of core.
- Finally, the option cmra cobinator shows that any cmra can essentially be used as an ucmra, so not enforing ucmra does not have any practical issues.


### Discrete CMRAs

- Similar to ofes, it is annoying to work with ✓{n}, especially since we know that we don't need to worry about dist.
- Iris has the notion of **discrete CMRAs** `CmraDiscrete`, which are CMRAs where ✓{0} x → ✓ x.
- For CmraDiscrete , we can ignore ✓{n} and treat them as if they are the same as ✓.
- Iris also comes with many lemmas the simplify working with discrete CMRAs.

### global RA construction: own vs OwnM.

- NOTE: This stage of the refactoring is not yet complete, and probably won't be for some time.

- In Lilo, the global RA is essentionally the cmra given by `GRA.of_list Σ_list`, where Σ_list is a list of URA, which is a kind of the function RA.
  - The OwnM r constuctor allows for one to own the cmra element r without worrying about putting it in the global RA.

- In Iris, the global RA is constructed by the following function cmra:
  - discrete_funUR (λ i,
        gmapUR gname (gFunctors_lookup Σ i)).
  - The own γ r constructor allows for one to own the cmra element r **with ghost name** without worrying about putting it in the global RA.
- Compared to Lilo, the main difference is annother indirection of "gmapUR", which is a cmra for finite maps, where the key can be a cmra.
  - This is _almost_ equivalent to FiniteMap.t in Lilo. The difference was never exploited in Lilo, so FiniteMap.t is actually gmapUR.

- The own constructor, compared to ownM, has a ghost name γ. This allows one to create a "unique" ghost instance for different use cases. For example, proofs of many libraries uses the excl_auth cmra, and will even sometimes use the same ghost for multiple instances, where each must be used separately. Having separate ghost names ensures that such ghost does not get mixed, which can be very hard to debug.

- Of course, the own constructor can be implemented using OwnM, but personally I don't see the point of having two constructors at the same time, and own constructor works really well with IPM.

## Other refactoring plans

- Dependency structore of temporal logic and fairness ghost is weird. Ideally, the temporal logic should only depend on the existance of iprop (and maybe invariant), without the fairness ghosts.
- In the long term, it will be nice if the simulation relation can be
  defined inside the logic, to simpily the adequacy proofs and have a
  concrete abstraction layer. This is very difficult, and might be
  fundamentally impossible as CCR assume/assert must break iProp
  abstraction.
  - Dimsum did achieve this, so maybe it is possible.
- Doing this may enable re-using the Iris's base_logic layer, in a similar
  style to how Lola re-used the base logic layer.
