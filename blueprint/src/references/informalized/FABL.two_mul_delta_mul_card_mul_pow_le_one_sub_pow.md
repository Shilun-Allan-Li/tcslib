<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/LTFNoiseSensitivityDerivative.lean :: FABL.two_mul_delta_mul_card_mul_pow_le_one_sub_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binomial Power Inequality

**Claim.** For $0\leq\delta\leq\tfrac12$ and every natural number $k$, $2\delta k(1-2\delta)^{k-1}\leq 1-(1-2\delta)^k$.

**Proof.** Set $\rho=1-2\delta$, so $0\leq\rho\leq1$. For every $j<k$, the exponent $k-1$ is at least $j$, and powers of a number in $[0,1]$ decrease as the exponent increases. Hence $\rho^{k-1}\leq\rho^j$. Summing these $k$ inequalities gives $k\rho^{k-1}\leq\sum_{j=0}^{k-1}\rho^j$. Multiply by the nonnegative quantity $1-\rho=2\delta$. The finite geometric-series identity makes the right side $(1-\rho)\sum_{j=0}^{k-1}\rho^j=1-\rho^k$. Substituting back for $\rho$ proves the bound.
