<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/TestingAmplification.lean :: FABL.repeatAndFunctionTester_acceptanceProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance probability under repetition

**Claim.** For a nonadaptive tester $T$ and a function $f$, the probability that all $k$ independent repetitions accept is the $k$th power of the acceptance probability of $T$ on $f$.

**Proof.** For a seed tuple, the repeated tester accepts exactly when every component accepts. The transcript supplied to component $i$ is the original tester's transcript with seed $s_i$ (`repeatAndFunctionTester_componentTranscript`). Consequently, the indicator of acceptance by the repeated tester is the product over components of the indicators that the original tester accepts with seed $s_i$. The expectation of this product under the independent product seed distribution factors into the product of the individual expectations (`pmfExpectation_independentProductPMF_prod`). Each factor is the acceptance probability of $T$ on $f$, so the result is its $k$th power.

**Key facts.** `FABL.repeatAndFunctionTester_componentTranscript`, `FABL.pmfExpectation_independentProductPMF_prod`.
