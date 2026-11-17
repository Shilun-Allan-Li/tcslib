<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/DNFSparsePolynomialThreshold.lean :: FABL.fourierCoeff_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier coefficient of a finite sum

**Claim.** The Fourier coefficient at $S$ of a finite sum of real-valued functions is the sum of their Fourier coefficients at $S$.

**Proof.** At each cube point, multiply the sum of the functions by the fixed monomial. Distributivity rewrites this as the sum of the individual products. Interchanging the two finite sums—the sum over cube points in the expectation and the sum over indices—then gives the sum of the individual expectations, which are precisely the Fourier coefficients in question.
