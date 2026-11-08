<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.SignTester.noisePreprocessedAcceptanceProbability_dictator_ge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tester Dictator Noise Bound

**Claim.** If every check selected by a sign tester has arity $r$, then preprocessing its queries with noise parameter $\delta\in[0,1]$ lowers the tester's acceptance probability on a dictator by at most $r\delta/2$.

**Proof.** Write the original and preprocessed acceptance probabilities as expectations over the same seed law. For each seed, the selected check has arity $r$ by hypothesis, and its dictator value after preprocessing is at least its original value minus $r\delta/2$ (`SignQueryCheck.noisePreprocessedValue_dictator_ge`). Taking expectations preserves this pointwise inequality by monotonicity of probability expectation (`pmfExpectation_mono`). The subtracted constant remains $r\delta/2$ after averaging: expectation is additive (`pmfExpectation_add`) and the expectation of a constant under a probability mass function is that constant (`pmfExpectation_const`). Combining these facts gives the stated tester bound.

**Key facts.** `FABL.SignQueryCheck.noisePreprocessedValue_dictator_ge`, `FABL.pmfExpectation_add`, `FABL.pmfExpectation_const`, `FABL.pmfExpectation_mono`.
