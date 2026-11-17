<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PolynomialThresholdInfluence.lean :: FABL.polynomialThresholdInfluenceExponent_succ_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successor Exponent Positivity

**Claim.** For every natural number $k$, the exponent $1-2^{-(k+1)}$ is positive.

**Proof.** The exponent at $k$ is nonnegative, and the successor exponent satisfies $2e_{k+1}=1+e_k$. Since $e_k\geq 0$, the right-hand side is at least $1$, so $2e_{k+1}>0$ and hence $e_{k+1}>0$.

**Key facts.** `FABL.polynomialThresholdInfluenceExponent_nonneg`, `FABL.two_mul_polynomialThresholdInfluenceExponent_succ`.
