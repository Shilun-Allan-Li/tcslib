<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/CorrelatedMajority.lean :: FABL.normalizedCorrelatedPairSum_projection_mean -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean of a Linear Projection

**Claim.** For every point $t$ in the plane, the expected inner product of the normalized pair sum with $t$ is zero.

**Proof.** Write the inner product with $t$ as the first coordinate of the normalized pair sum times the first coordinate of $t$, plus the second coordinate times the second coordinate of $t$. Expectation is additive and pulls out these fixed scalar coefficients (\texttt{FABL.pmfExpectation_add} and \texttt{FABL.pmfExpectation_mul_const}). The first and second coordinates each have mean zero (\texttt{FABL.normalizedCorrelatedPairSum_first_mean} and \texttt{FABL.normalizedCorrelatedPairSum_second_mean}), so both terms vanish and the projection has mean zero.

**Key facts.** `FABL.normalizedCorrelatedPairSum_first_mean`, `FABL.normalizedCorrelatedPairSum_second_mean`, `FABL.pmfExpectation_add`, `FABL.pmfExpectation_mul_const`.
