<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/InnerProductSupportDensity.lean :: FABL.vectorFourierCoeff_booleanRealEmbedding_innerProductModTwoBit_of_ne_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Coefficient of the Inner-Product Bit Embedding

**Claim.** For a nonzero frequency $\gamma$ on two $m$-coordinate blocks, the Fourier coefficient of the Boolean real embedding of the inner-product bit equals $-\tfrac12$ times the Fourier coefficient of its sign encoding.

**Proof.** Write both Fourier coefficients as expectations against the Walsh character at $\gamma$ (`FABL.vectorFourierCoeff_eq_expect`). The Boolean real embedding of the inner-product bit is $(1-I(z))/2$, where $I$ is the sign encoding of that bit (`FABL.booleanRealEmbedding_innerProductModTwoBit`). Distribute this expression inside the expectation and use linearity to obtain one half of the difference between the expectation of the character alone and the Fourier expectation of $I$. The Walsh character has mean zero at every nonzero frequency, by its orthogonality identity (`FABL.expect_vectorWalshCharacter`). Thus the first expectation vanishes, leaving $-\tfrac12$ times the Fourier coefficient of $I$.

**Key facts.** `FABL.vectorFourierCoeff_eq_expect`, `FABL.booleanRealEmbedding_innerProductModTwoBit`, `FABL.expect_vectorWalshCharacter`.
