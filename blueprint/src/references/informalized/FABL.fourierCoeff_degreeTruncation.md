<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractivityExercises.lean :: FABL.fourierCoeff_degreeTruncation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Coefficients of Degree Truncation

**Claim.** Let $n,k\ge 0$, let $f$ be a real-valued function on the $n$-dimensional sign cube, and let $T$ be a set of coordinates. The Fourier coefficient at $T$ of the degree-$k$ truncation of $f$ equals the Fourier coefficient of $f$ at $T$ when $|T|\le k$, and equals $0$ when $|T|>k$.

**Proof.** Expand the degree-$k$ truncation as the finite sum of terms $\widehat f(S)\chi_S(x)$ over sets $S$ with $|S|\le k$. Distribute multiplication by $\chi_T$ over the sum and interchange the finite sum with expectation. In each summand, factoring out $\widehat f(S)$ leaves the expectation of $\chi_S\chi_T$, which is $1$ if $S=T$ and $0$ otherwise (`expect_monomial_mul`). Consequently only the term indexed by $T$ can survive, and it is present exactly when $|T|\le k$. This gives the asserted coefficient when that inequality holds and zero otherwise.

**Key facts.** `FABL.expect_monomial_mul`.
