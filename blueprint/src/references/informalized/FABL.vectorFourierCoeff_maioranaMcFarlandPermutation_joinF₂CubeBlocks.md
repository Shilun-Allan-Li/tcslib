<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/MaioranaMcFarlandPermutation.lean :: FABL.vectorFourierCoeff_maioranaMcFarlandPermutation_joinF₂CubeBlocks -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Permuted Maiorana–McFarland coefficient

**Claim.** For a permutation of the binary cube and a sign-valued function, the vector Fourier coefficient at the concatenation of $a$ and $b$ equals $2^{-n}$ times the real value of the sign at $\pi^{-1}(a)$, multiplied by the Walsh character indexed by $b$ evaluated at $\pi^{-1}(a)$.

**Proof.** Rewrite the coefficient as the expectation of the function times its Walsh character. Use the bijection that splits a point of the $2n$-dimensional cube into two $n$-dimensional blocks. Under this change of variables, the function becomes the product of the binary inner-product character indexed by the first block and the sign value at the second block; the Walsh character at the concatenated index splits into the product of the characters indexed by $a$ and $b$ on the respective blocks. Express the expectation as an iterated average, interchange the order so that the average over the first block is inner, and collect the factors independent of that block. The inner average is $1$ when $\pi(y)=a$ and $0$ otherwise, by the orthogonality of the binary inner-product character against a Walsh character. Thus only $y=\pi^{-1}(a)$ contributes. Averaging this single surviving term over the $2^n$ points gives the stated factor $2^{-n}$ and value.

**Key facts.** `FABL.vectorFourierCoeff_eq_expect`, `FABL.maioranaMcFarlandPermutation_joinF₂CubeBlocks`, `FABL.vectorWalshCharacter_joinF₂CubeBlocks`, `FABL.expect_innerProductModTwo_mul_vectorWalshCharacter`.
