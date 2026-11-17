<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/InnerProductModTwo.lean :: FABL.vectorFourierCoeff_innerProductModTwo_joinF₂CubeBlocks -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Coefficient of the Block Inner Product

**Claim.** For $a,b\in\mathbb F_2^n$, the vector Fourier coefficient of the sign encoding of the inner product on two blocks, at their concatenation, is $2^{-n}$ times the binary sign of the inner product of $a$ and $b$.

**Proof.** Write the coefficient as an expectation against its Walsh character (`FABL.vectorFourierCoeff_eq_expect`), then use the block equivalence to view the expectation over independent vectors $x,y\in\mathbb F_2^n$. The sign encoding of their inner product is the binary sign of $x\cdot y$ (`FABL.innerProductModTwo_joinF₂CubeBlocks`), and the character at the joined frequency factors into the characters indexed by $a$ and $b$ on the two blocks (`FABL.vectorWalshCharacter_joinF₂CubeBlocks`). By the character identity expressing the sign of a sum as a product, the integrand can be rewritten as the character at $a$ on $x$ times the character at $x+b$ on $y$. Averaging first over $y$ makes the latter character expectation the indicator of $x=b$ (`FABL.expect_mul_vectorWalshCharacter_add`). The remaining expectation is therefore the average of the character at $a$ evaluated at $b$, supported at that single point. The cube has $2^n$ elements, so this average is $2^{-n}$ times that character value, namely $2^{-n}$ times the binary sign of $a\cdot b$.

**Key facts.** `FABL.vectorFourierCoeff_eq_expect`, `FABL.innerProductModTwo_joinF₂CubeBlocks`, `FABL.vectorWalshCharacter_joinF₂CubeBlocks`, `FABL.expect_mul_vectorWalshCharacter_add`, `FABL.vectorWalshCharacter_apply`.
