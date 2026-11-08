<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter01/FunctionsAsMultilinearPolynomials.lean :: FABL.indicatorPolynomial_fourier_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier formula for the cube indicator

**Claim.** For sign vectors $a,x\in\{-1,1\}^n$, the indicator polynomial at $a$ equals the normalized sum of the products of their monomials over all coordinate subsets.

**Proof.** Rewrite each factor $(1+a_i x_i)/2$ as $2^{-1}(a_i x_i+1)$. Taking the product separates the constant factors, giving $2^{-n}\prod_i(a_i x_i+1)$; since the cube has $2^n$ points, the coefficient is the reciprocal of its cardinality. Expanding the remaining product chooses, for each subset $S$, the term $a_i x_i$ exactly at indices in $S$ and the term $1$ elsewhere. That contribution is $(\prod_{i\in S}a_i)(\prod_{i\in S}x_i)$, namely the product of the monomials at $a$ and $x$. Summing these contributions proves the formula.
