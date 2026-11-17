<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/DNFSparsePolynomialThreshold.lean :: FABL.polynomialSparsity_half_sub_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sparsity after a half-shift

**Claim.** For every nonnegative integer $n$ and every real-valued function $q$ on the $n$-dimensional sign cube, the number of nonzero Fourier coefficients of $x\mapsto \tfrac12-q(x)$ is at most one more than the number for $q$.

**Proof.** First, show that the Fourier support of $x\mapsto \tfrac12-q(x)$ is contained in the union of the empty frequency and the Fourier support of $q$. The empty frequency is included automatically. For any nonempty frequency $S$, the constant function $1/2$ has zero Fourier coefficient at $S$: its coefficient factors as $1/2$ times the expectation of the monomial at $S$, and that expectation is zero for nonempty $S$ (`expect_monomial`). By linearity of Fourier coefficients under subtraction (`fourierCoeff_sub`), the coefficient of $1/2-q$ at $S$ is therefore the negative of the coefficient of $q$ there. Thus, if the latter coefficient vanishes, so does the former; the support criterion is exactly nonvanishing of the coefficient (`mem_fourierSupport`). Taking cardinalities of the support inclusion bounds the new support size by the size of the set obtained by adjoining one frequency to the support of $q$, which is at most one plus the original support size.

**Key facts.** `FABL.expect_monomial`, `FABL.fourierCoeff_sub`, `FABL.mem_fourierSupport`.
