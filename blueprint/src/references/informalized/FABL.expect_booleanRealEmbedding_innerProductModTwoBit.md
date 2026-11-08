<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/InnerProductSupportDensity.lean :: FABL.expect_booleanRealEmbedding_innerProductModTwoBit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean of the mod-two inner-product bit

**Claim.** For a uniform vector split into two blocks of length $m$, the average of the indicator that their dot product is $1$ in $\mathbb F_2$ is $(1-2^{-m})/2$.

**Proof.** At each vector, the indicator that the mod-two inner product is $1$ equals $(1-I)/2$, where $I$ is the real-valued mod-two inner product bit (`booleanRealEmbedding_innerProductModTwoBit`). Average this identity. Linearity of expectation and the fact that the average of the constant $1$ is $1$ give $(1-\mathbb E I)/2$. The mean of that bit is $2^{-m}$ (`expect_innerProductModTwo`), yielding $(1-2^{-m})/2$.

**Key facts.** `FABL.booleanRealEmbedding_innerProductModTwoBit`, `FABL.expect_innerProductModTwo`.
