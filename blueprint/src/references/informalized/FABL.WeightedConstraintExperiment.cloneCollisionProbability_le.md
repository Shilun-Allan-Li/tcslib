<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.WeightedConstraintExperiment.cloneCollisionProbability_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clone collision probability bound

**Claim.** If all outcome predicates have arity at most $r$ and clone indices are chosen uniformly and independently at the query positions, the probability of a collision between queried variable-clone pairs is at most $r^2/M$.

**Proof.** Condition on an original outcome. Its ordered query scope is a repeated-query scope of arity $a$, and choosing clones independently and uniformly gives a collision probability at most $a^2/M$ by the repeated-scope collision bound (`clonedScopeCollisionProbability_le`). Since $a\le r$, we have $a^2\le r^2$; dividing by the positive $M$ preserves the inequality. The conditional probability is therefore at most $r^2/M$ for every outcome. Averaging over the original outcome law preserves this bound (`pmfExpectation_mono`), and the expectation of the constant bound is that same constant (`pmfExpectation_const`). The expectation under the clone law is expressed as this iterated expectation by the bind and map expectation identities, with uniform clone sampling identified as a uniform mean (`pmfExpectation_bind`, `pmfExpectation_map`, `pmfExpectation_uniformPMF_eq_expect`).

**Key facts.** `FABL.pmfExpectation_bind`, `FABL.pmfExpectation_mono`, `FABL.RepeatedQueryScope.clonedScopeCollisionProbability_le`, `FABL.pmfExpectation_map`, `FABL.pmfExpectation_uniformPMF_eq_expect`, `FABL.pmfExpectation_const`.
