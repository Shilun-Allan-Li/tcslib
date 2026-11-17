<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/BentFunctions.lean :: FABL.vectorFourierCoeff_maioranaMcFarland_joinF₂CubeBlocks -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Maiorana–McFarland coefficient

**Claim.** For a sign-valued function $g$ on the $n$-dimensional binary cube, the vector Fourier coefficient of the Maiorana–McFarland function at the concatenation of $a$ and $b$ equals $2^{-n}$ times the real value of $g(a)$ multiplied by the Walsh character indexed by $b$ evaluated at $a$.

**Proof.** Rewrite the coefficient as the expectation of the function times its Walsh character. Split each point of the $2n$-dimensional cube into two blocks. The function on the joined blocks is the product of the binary inner-product character of those blocks and the sign value of $g$ on the second block; the Walsh character at the joined index factors into the characters indexed by $a$ and $b$ on the two blocks. Turn the resulting expectation into an iterated average and interchange the order, making the average over the first block inner. The orthogonality of binary inner-product characters says this inner average is $1$ if the second block equals $a$ and $0$ otherwise. Only that block remains in the outer average, which contributes its value divided by the cube's size, $2^n$.

**Key facts.** `FABL.vectorFourierCoeff_eq_expect`, `FABL.maioranaMcFarland_joinF₂CubeBlocks`, `FABL.vectorWalshCharacter_joinF₂CubeBlocks`, `FABL.expect_innerProductModTwo_mul_vectorWalshCharacter`.
