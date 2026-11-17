<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/SmallBias.lean :: FABL.ProbabilityDensity.isBiased_zero_iff_eq_uniform -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero bias characterizes the uniform density

**Claim.** A probability density is $0$-biased if and only if it is identically equal to $1$.

**Proof.** Suppose first that $\varphi$ is $0$-biased. By the equivalence between bias and Fourier regularity (`ProbabilityDensity.isBiased_iff_isFourierRegular`), its associated function on the sign cube is $0$-Fourier-regular. The characterization of zero-regular functions says that this function is constant, say equal to $c$ (`isFourierRegular_zero_iff_exists_const`). The sign-cube identification is a bijection, so $\varphi$ itself is also constantly $c$. Its uniform expectation is one (`ProbabilityDensity.expect_eq_one`); the expectation of a constant function is that constant, hence $c=1$. Thus $\varphi$ is identically one.

Conversely, suppose $\varphi$ is identically one. For any nonzero $\gamma$, its vector Fourier coefficient is the expectation of the corresponding Walsh character (`vectorFourierCoeff_eq_expect`). The mean of that character is zero when $\gamma\ne0$ (`expect_vectorWalshCharacter`). Therefore every such coefficient has absolute value zero, which is exactly the $0$-bias condition.

**Key facts.** `FABL.ProbabilityDensity.isBiased_iff_isFourierRegular`, `FABL.isFourierRegular_zero_iff_exists_const`, `FABL.ProbabilityDensity.expect_eq_one`, `FABL.vectorFourierCoeff_eq_expect`, `FABL.expect_vectorWalshCharacter`.
