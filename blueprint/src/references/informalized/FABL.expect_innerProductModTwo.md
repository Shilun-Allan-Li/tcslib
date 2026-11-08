<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/InnerProductSupportDensity.lean :: FABL.expect_innerProductModTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean of the Binary Inner Product Sign

**Claim.** For every $m\in\mathbb N$, the uniform expectation over pairs of vectors in $\mathbb F_2^m$ of the sign $(-1)^{u\cdot v}$ is $2^{-m}$.

**Proof.** Apply the formula for the vector Fourier coefficient of the binary inner-product sign at a joined pair of vectors (\texttt{vectorFourierCoeff_innerProductModTwo_joinF₂CubeBlocks}). Take both vectors to be zero; their join is the zero vector. The formula then says that the coefficient at zero is $2^{-m}$, since the binary sign of the zero dot product is $1$. The coefficient-at-zero formula identifies this Fourier coefficient with the uniform expectation of the function, because the zero Walsh character is identically $1$ (\texttt{vectorFourierCoeff_eq_expect}). This is the desired expectation.

**Key facts.** `FABL.vectorFourierCoeff_innerProductModTwo_joinF₂CubeBlocks`, `FABL.vectorFourierCoeff_eq_expect`.
