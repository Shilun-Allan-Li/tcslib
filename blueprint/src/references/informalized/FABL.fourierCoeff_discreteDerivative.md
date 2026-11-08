<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/StableInfluence.lean :: FABL.fourierCoeff_discreteDerivative -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Coefficients of a Derivative

**Claim.** The Fourier coefficient of the discrete derivative in coordinate $i$ at $T$ is zero when $i\in T$; when $i\notin T$, it equals the Fourier coefficient of $f$ at $T\cup\{i\}$.

**Proof.** Expand the discrete derivative as a sum over sets $S$ containing $i$, with each term equal to $\widehat f(S)$ times the monomial on $S\setminus\{i\}$, using the derivative Fourier expansion (`discreteDerivative_eq_fourier_sum`). Multiply by the monomial on $T$ and take expectations. Linearity of expectation lets us interchange the finite sum and expectation. The orthogonality of cube monomials (`expect_monomial_mul`) makes the contribution from $S$ equal to $\widehat f(S)$ if $S\setminus\{i\}=T$, and zero otherwise. If $i\in T$, that equality is impossible because $i\notin S\setminus\{i\}$, so the coefficient vanishes. If $i\notin T$, the unique set containing $i$ whose deletion gives $T$ is $S=T\cup\{i\}$, leaving precisely $\widehat f(T\cup\{i\})$.

**Key facts.** `FABL.discreteDerivative_eq_fourier_sum`, `FABL.expect_monomial_mul`.

**Caveat.** The supplied informal statement gives a different derivative expansion; this account follows the formal theorem and its proof.
