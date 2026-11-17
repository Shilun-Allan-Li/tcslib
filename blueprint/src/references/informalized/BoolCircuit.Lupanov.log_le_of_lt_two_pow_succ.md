<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LupanovGates.lean :: BoolCircuit.Lupanov.log_le_of_lt_two_pow_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logarithmic Bound from a Power Bound

**Claim.** If $q<2^{a+1}$, then the base-$2$ logarithm of $q$ is at most $a$.

**Proof.** If $q=0$, its natural logarithm is zero, so the assertion follows. If $q>0$, the strict upper bound on $q$ implies that its base-$2$ logarithm is strictly less than $a+1$, by the logarithm bound for numbers below a power of the base. Since the logarithm is an integer, it is therefore at most $a$.
