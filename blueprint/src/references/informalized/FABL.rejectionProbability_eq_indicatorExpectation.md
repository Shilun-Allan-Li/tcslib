<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPThreeQuery.lean :: FABL.rejectionProbability_eq_indicatorExpectation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rejection Probability as an Expectation

**Claim.** For any input function, a finite-seed nonadaptive tester's rejection probability is the expectation of its rejection indicator over the seed distribution.

**Proof.** For each seed, the acceptance indicator and rejection indicator sum to $1$: if the tester accepts, their values are $1$ and $0$, and if it rejects, they are $0$ and $1$. Taking expectations and using additivity of expectation (`FABL.pmfExpectation_add`) shows that the acceptance probability plus the expected rejection indicator is the expectation of the constant function $1$. The latter is $1$ (`FABL.pmfExpectation_const_one`). Since rejection probability is one minus acceptance probability, rearranging yields the claim.

**Key facts.** `FABL.pmfExpectation_add`, `FABL.pmfExpectation_const_one`.
