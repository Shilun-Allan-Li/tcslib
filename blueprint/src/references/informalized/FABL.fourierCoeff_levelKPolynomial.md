<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.fourierCoeff_levelKPolynomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier coefficients of the level polynomial

**Claim.** The Fourier coefficient at $T$ of the sum of all coordinate monomials indexed by $k$-element sets is $1$ if $|T|=k$, and $0$ otherwise.

**Proof.** Expand the product of the sum defining the level polynomial with the monomial at $T$, then interchange the finite expectation and sum. Each summand is the expectation of the product of monomials indexed by $S$ and $T$. By orthogonality of Boolean-cube monomials (`FABL.expect_monomial_mul`), this expectation is $1$ when $S=T$ and $0$ otherwise. The sum therefore contributes $1$ precisely when $T$ itself is among the indexing sets, which is equivalent to $|T|=k$.

**Key facts.** `FABL.expect_monomial_mul`.
