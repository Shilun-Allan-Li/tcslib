<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.expect_levelKPolynomial_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second Moment of a Level Polynomial

**Claim.** For nonnegative integers $n$ and $k$, the uniform second moment of the level-$k$ polynomial on the $n$-dimensional sign cube is $\binom{n}{k}$.

**Proof.** The uniform expectation of the square is the uniform inner product of the level-$k$ polynomial with itself. Parseval’s identity expresses this inner product as the sum of the squares of all its Fourier coefficients (\texttt{parseval}). Each coefficient is $1$ for a subset of size $k$ and $0$ for every other subset (\texttt{fourierCoeff_levelKPolynomial}). Thus the sum is the number of $k$-element subsets of an $n$-element set, namely $\binom{n}{k}$.

**Key facts.** `FABL.parseval`, `FABL.fourierCoeff_levelKPolynomial`.
