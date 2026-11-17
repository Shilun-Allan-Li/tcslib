<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/CorrelatedMajority.lean :: FABL.pmfExpectation_correlatedPairPMF_fst -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Marginal of the Correlated Pair

**Claim.** For every real-valued function $f$ on the sign cube, its expectation on the first coordinate of the correlated pair equals its expectation under the uniform distribution.

**Proof.** Expand the expectation of the joint distribution, which is formed by first choosing $x$ and then sampling the noisy vector, as an iterated expectation (`FABL.pmfExpectation_bind`). The map sending the sampled vector $y$ to the pair $(x,y)$ does not change the value of a function that only reads the first coordinate (`FABL.pmfExpectation_map`): conditional on $x$, that function is the constant $f(x)$. Its expectation is therefore $f(x)$, since the expectation of a constant under a probability mass function equals that constant (`FABL.pmfExpectation_const`). Averaging over the uniform choice of $x$ gives the claimed equality.

**Key facts.** `FABL.pmfExpectation_bind`, `FABL.pmfExpectation_map`, `FABL.pmfExpectation_const`.
