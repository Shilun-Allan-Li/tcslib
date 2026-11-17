<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.WeightedConstraintExperiment.UniformRefinement.paddedCloneValue_eq_clone_value -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Padded and ordinary clone values agree

**Claim.** For an assignment to variable-clone pairs, the padded-clone value equals the value of the experiment obtained by independently choosing a uniform clone at each query position.

**Proof.** Expand the padded-clone value as an expectation over a refinement occurrence and a function assigning one of the $r$ clone indices to every padded position. Since the occurrence space and the padded index space form a finite product, this is an iterated expectation (`fintype_expect_prod`). For each occurrence, the predicate actually queries only $a$ positions, where its arity $a$ is at most $r$. The restriction of a uniformly chosen function on the $r$ positions to those $a$ positions is uniform among all clone choices for the actual query positions: the extra coordinates do not affect the payoff, and averaging them leaves its mean unchanged (`uniformPaddedCloneExpectation`). Thus the inner expectation is the uniform mean of the ordinary cloned payoff. The refinement law agrees with the original outcome law (`R.law_eq`); expressing expectations under mapped and uniform laws as ordinary expectations (`pmfExpectation_map`, `pmfExpectation_uniformPMF_eq_expect`) identifies the resulting iterated expectation with the cloned experiment’s value, using the cloned-value expansion (`clone_value_eq_iterated`).

**Key facts.** `FABL.fintype_expect_prod`, `FABL.WeightedConstraintExperiment.clone_value_eq_iterated`, `FABL.pmfExpectation_map`, `FABL.pmfExpectation_uniformPMF_eq_expect`, `FABL.uniformPaddedCloneExpectation`.
