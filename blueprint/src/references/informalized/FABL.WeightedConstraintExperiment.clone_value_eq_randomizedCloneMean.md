<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.WeightedConstraintExperiment.clone_value_eq_randomizedCloneMean -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of the Cloned Experiment

**Claim.** The value of the cloned sign experiment equals the expected randomized predicate value whose coordinate means are the average signs across the clones.

**Proof.** Fix an outcome of the original experiment. The cloned experiment first chooses this outcome and then independently chooses a uniform clone at each predicate position, so its expected payoff is the expectation over those clone choices (`clone_value_eq_iterated`). View the uniform choice at each position as a probability law. For each fixed clone tuple, the predicate’s indicator agrees with its multilinear extension evaluated at the corresponding signs (`multilinearExtension_signValues`). The product-law expectation identity (`pmfExpectation_multilinearExtension_productLaw`) then moves the expectation over independent clone choices inside the multilinear extension, giving at each position the average sign over its clones. This average is exactly the clone mean, by the uniform-law expectation identity (`pmfExpectation_uniformPMF_eq_expect`). Each clone mean lies in $[-1,1]$ (`cloneMean_mem_Icc`), so the randomized predicate value is defined there and equals the multilinear extension (`SignPredicate.randomizedValue_eq_multilinearExtension`). Thus the two conditional expectations agree for every original outcome; averaging this pointwise equality under the original law proves the claimed equality of values.

**Key facts.** `FABL.WeightedConstraintExperiment.clone_value_eq_iterated`, `FABL.pmfExpectation_uniformPMF_eq_expect`, `FABL.independentProductPMF_uniform`, `FABL.RegularUniqueGame.multilinearExtension_signValues`, `FABL.RegularUniqueGame.pmfExpectation_multilinearExtension_productLaw`, `FABL.WeightedConstraintExperiment.cloneMean_mem_Icc`, `FABL.SignPredicate.randomizedValue_eq_multilinearExtension`.
