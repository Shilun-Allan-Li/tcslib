<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/MatrixProductVerification.lean :: FABL.uniformPushforward_id_isBiased_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unbiasedness of the Uniform Cube Density

**Claim.** For every $n$, the density obtained by pushing forward the uniform distribution on $\mathbb{F}_2^n$ under the identity map has every nonconstant Fourier coefficient equal to zero; equivalently, it is biased with bias $0$.

**Proof.** Use the characterization of being biased in terms of expectations of vector Walsh characters (`isBiased_iff_expectation`). For the identity pushforward, the expectation of any function under the resulting density is its uniform expectation on the cube (`expectation_uniformPushforward`), since applying the identity changes no input. Thus, for each nonzero frequency $\gamma$, the relevant expectation is the uniform average of its Walsh character. That average is $0$ for nonzero $\gamma$ (`expect_vectorWalshCharacter`), so its absolute value is at most $0$, as required.

**Key facts.** `FABL.ProbabilityDensity.isBiased_iff_expectation`, `FABL.ProbabilityDensity.expectation_uniformPushforward`, `FABL.expect_vectorWalshCharacter`.
