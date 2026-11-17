<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.deterministicAverageCostUnder_majorityThreeHardPMF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Average Cost Under the Hard-Input Distribution

**Claim.** The average query cost under the hard-input distribution equals the expected query count on a uniformly chosen seed.

**Proof.** Expand the deterministic average cost using its definition. The hard-input distribution is the image of the uniform seed distribution under the map sending a seed to its hard input. The expectation under an image distribution equals the original expectation of the function composed with that map (`pmfExpectation_map`). Finally, expectation under the uniform distribution is the finite uniform average (`pmfExpectation_uniformPMF_eq_expect`), yielding the stated identity.

**Key facts.** `FABL.pmfExpectation_map`, `FABL.pmfExpectation_uniformPMF_eq_expect`.
