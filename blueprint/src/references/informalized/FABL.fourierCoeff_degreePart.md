<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter01/BasicFourierFormulas.lean :: FABL.fourierCoeff_degreePart -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Coefficients of a Degree Part

**Claim.** For each degree $k$, the Fourier coefficient at $T$ of the degree-$k$ part of $f$ is $\widehat f(T)$ if $|T|=k$, and is zero otherwise.

**Proof.** Expand the degree-$k$ part as the finite sum of terms $\widehat f(S)\chi_S(x)$ over coordinate sets $S$ of size $k$. Multiplying by $\chi_T(x)$ distributes over this sum, and linearity of expectation allows the expectation to pass through the finite sum. For each summand, pull out the constant $\widehat f(S)$; the remaining expectation of $\chi_S\chi_T$ is $1$ when $S=T$ and $0$ otherwise (`expect_monomial_mul`). Thus only the summand with $S=T$ can contribute. It occurs in the sum exactly when $|T|=k$, yielding the claimed piecewise value.

**Key facts.** `FABL.expect_monomial_mul`.
