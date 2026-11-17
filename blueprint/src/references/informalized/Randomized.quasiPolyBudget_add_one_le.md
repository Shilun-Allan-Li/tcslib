<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/QuasiPolyHierarchy.lean :: Randomized.quasiPolyBudget_add_one_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quasi-Polynomial Budget Bound

**Claim.** For every natural number $n$, the budget $B(n)=2^{(\lfloor\log_2 n\rfloor)^2+1}$ satisfies $B(n)+1\le3n^{\lfloor\log_2 n\rfloor}$.

**Proof.** Write $k=\lfloor\log_2 n\rfloor$. The bound $2^{k^2}\le n^k$ controls the budget's power-of-two factor, and $1\le n^k$ controls the added $1$. Since $2^{k^2+1}=2\cdot2^{k^2}$, these give $B(n)+1\le2n^k+n^k=3n^k$.

**Key facts.** `Randomized.two_pow_log_sq_le`, `Randomized.one_le_pow_log`.
