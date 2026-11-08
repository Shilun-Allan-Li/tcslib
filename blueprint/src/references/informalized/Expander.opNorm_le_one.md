<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Expanders/Walks.lean :: Expander.opNorm_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Operator norm bound for a stochastic matrix

**Claim.** For a symmetric stochastic matrix with nonnegative entries, the operator norm of its associated Euclidean operator is at most one.

**Proof.** The contraction estimate for each vector states that $\|Av\|\le\|v\|$. The operator-norm bound criterion says that a continuous linear map has norm at most $c$ if its value at every vector has norm at most $c$ times the vector's norm. Apply this criterion with $c=1$ to obtain the result.

**Key facts.** `Expander.norm_toCLM_apply_le`.
