<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/EXPCOM.lean :: Complexity.expcom_summit_budget -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential-Polynomial Summit Bound

**Claim.** For the displayed function T, there are natural numbers K and j such that $T(n)\leq 2^{K(n+1)^j}$ for every n.

**Proof.** Set $g=n+C(n+1)^k+1$ and $G=(C+1)(n+1)^{k+1}$. Since $n+1\leq(n+1)^{k+1}$ and $(n+1)^k\leq(n+1)^{k+1}$, we have $g\leq G$. Consequently, the linear expression $2g+3$ is at most $3G$. The exponential term inside the large parentheses is therefore bounded by $A2^{3B(C+1)(n+1)^{k+1}}$. The other terms are powers of g, powers of $2g+3$, and products and sums of these quantities. The polynomial bound theorem (expPoly_poly) makes each fixed-degree polynomial in $n+1$ exponential-polynomial; the exponential-polynomial constant and power-of-two lemmas handle fixed factors and terms of the form $A2^{K(n+1)^j}$. Closure under multiplication and addition (ExpPoly.mul and ExpPoly.add) combines these bounds into one for the entire expression. The pointwise comparisons above and closure under domination (ExpPoly.of_le) then yield the asserted exponential-polynomial bound.

**Key facts.** `Complexity.expPoly_poly`, `Complexity.expcom_expPoly_mul_two_pow`, `Complexity.expcom_expPoly_const`, `Complexity.ExpPoly.mul`, `Complexity.ExpPoly.add`, `Complexity.ExpPoly.of_le`.
