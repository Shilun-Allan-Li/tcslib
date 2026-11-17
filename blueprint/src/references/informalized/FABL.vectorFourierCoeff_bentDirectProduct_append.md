<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/BentFunctions.lean :: FABL.vectorFourierCoeff_bentDirectProduct_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Coefficient of a Direct Product

**Claim.** The vector Fourier coefficient of the direct-product function at the concatenated vector $(a,b)$ is the product of the coefficient of $f$ at $a$ and the coefficient of $g$ at $b$.

**Proof.** Write each vector Fourier coefficient as the expectation of the function times its Walsh character (the expectation formula for vector Fourier coefficients, `FABL.vectorFourierCoeff_eq_expect`). Reindex the expectation over the concatenated cube by the equivalence with the product of the two cubes. Under this reindexing, the direct-product function becomes $f(x)g(y)$ (`FABL.bentDirectProduct_append`), and the Walsh character at $(a,b)$ factors as the characters at $a$ and $b$ (`FABL.vectorWalshCharacter_append`). Rearranging the factors gives the expectation of $(f(x)	ext{ character}_a(x))(g(y)	ext{ character}_b(y))$. The uniform expectation on the product cube is the iterated expectation, and independence of the two uniform coordinates factors this expectation into the product of the two individual expectations. These are precisely the Fourier coefficients at $a$ and $b$.

**Key facts.** `FABL.vectorFourierCoeff_eq_expect`, `FABL.bentDirectProduct_append`, `FABL.vectorWalshCharacter_append`.
