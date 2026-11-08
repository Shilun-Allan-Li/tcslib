<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/QuasiPolyHierarchy.lean :: Randomized.le_quasiPolyBudget -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quasipolynomial Budget Bound

**Claim.** For every natural number $n$, $n$ is at most $2^{(	ext{rounded-down }\\log_2 n)^2+1}$.

**Proof.** The strict logarithmic power bound says that $n<2^{\operatorname{Nat.log}(2,n)+1}$, so in particular $n$ is at most that power. Write $k=\operatorname{Nat.log}(2,n)$. Since $k$ is a natural number, $k\le k^2$; hence $k+1\le k^2+1$. Powers of $2$ are monotone in their natural-number exponent, so $2^{k+1}\le 2^{k^2+1}$. Combining the inequalities gives the result.
