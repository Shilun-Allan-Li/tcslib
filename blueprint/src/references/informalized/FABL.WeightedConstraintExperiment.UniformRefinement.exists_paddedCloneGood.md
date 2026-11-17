<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.WeightedConstraintExperiment.UniformRefinement.exists_paddedCloneGood -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Existence of an injective padded clone scope

**Claim.** Given natural numbers $r,M$ with $r\le M$ and an upper bound $r$ on every predicate arity, there is a padded clone occurrence whose padded clone scope is injective.

**Proof.** Choose any occurrence from the uniform refinement, which exists by its nonemptiness property. Pair it with the inclusion of the first $r$ clone indices into the $M$ available indices. To prove the resulting scope is injective, suppose two positions have the same image. Equality of the ordered pairs gives equality of their clone indices. The inclusion of the first $r$ indices is injective, so the positions agree after casting into that range. Since the predicate's arity is at most $r$, that cast is also injective on the positions in question, and hence the original positions agree. Thus the padded clone scope is injective.

**Caveat.** The supplied informal statement describes a larger CSP reduction, but the formal declaration and proof establish only the existence of an occurrence with injective padded clone scope.
