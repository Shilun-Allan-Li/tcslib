<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/CorrelatedMajority.lean :: FABL.pmfExpectation_correlatedPairPMF_snd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second Marginal of the Correlated Pair

**Claim.** For every real-valued function $f$ on the sign cube, its expectation on the second coordinate of the correlated pair equals its expectation under the uniform distribution.

**Proof.** The joint distribution is unchanged when its two coordinates are swapped (`FABL.correlatedPairPMF_map_swap`). Apply expectation of the second-coordinate function to this distributional identity. The expectation under the swapped distribution is the expectation of the first-coordinate function under the original distribution, by the rule for expectations under a mapped mass function (`FABL.pmfExpectation_map`). The first marginal has the uniform expectation (`FABL.pmfExpectation_correlatedPairPMF_fst`), giving the result.

**Key facts.** `FABL.correlatedPairPMF_map_swap`, `FABL.pmfExpectation_map`, `FABL.pmfExpectation_correlatedPairPMF_fst`.
