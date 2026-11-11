<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.BinarySubspaceSplit.vectorFourierCoeff_cosetAverage_eq_one_sub_two_distance -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Coefficient and Hamming Distance

**Claim.** The Fourier coefficient of the coset average at $\gamma$ is one minus twice the relative Hamming distance between $f$ and the corresponding character.\n\n**Proof.** The coset-average Fourier coefficient identity (`FABL.BinarySubspaceSplit.vectorFourierCoeff_cosetAverage`) rewrites the coefficient as the uniform expectation of the product of the sign values of $f$ and the character. For two sign-valued functions, this product is $1$ where they agree and $-1$ where they disagree. Its expectation is therefore the agreement probability minus the disagreement probability, which equals one minus twice the relative Hamming distance (`FABL.expect_signValue_mul_eq_one_sub_two_relativeHammingDist`).

**Key facts.** `FABL.BinarySubspaceSplit.vectorFourierCoeff_cosetAverage`, `FABL.expect_signValue_mul_eq_one_sub_two_relativeHammingDist`.
