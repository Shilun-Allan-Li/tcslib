<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/QuasiPolyHierarchy.lean :: Randomized.poly_sq_le_quasiPolyBudget -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Square Bound

**Claim.** If $A+2k+6\le m$, then $A((2^m)^k+1+2^m+1)^2\le 2^{m^2+1}$.

**Proof.** At $n=2^m$, the binary logarithm is $m$, so the quasi-polynomial budget is $2^{m^2+1}$. First, $A<2^A$. Also, $(2^m)^k\le 2^{m(k+1)}$ and $2^m\le 2^{m(k+1)}$, while $1\le 2^{m(k+1)}$. Consequently the sum inside the square is at most $2^{m(k+1)+2}$. The left side is therefore at most $2^A(2^{m(k+1)+2})^2=2^{A+2(m(k+1)+2)}$. The assumption $A+2k+6\le m$ implies $A+2(m(k+1)+2)\le m^2+1$ by elementary rearrangement. Monotonicity of powers of two gives the claimed bound.
