<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean :: finrank_le_n_of_isotropic -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dimension bound for isotropic subspaces

**Claim.** Every totally isotropic subspace $S$ of the $2n$-dimensional symplectic vector space $V$ has dimension at most $n$.

**Proof.** Isotropy means $S\subseteq S^\perp$. Monotonicity of dimension for subspaces therefore gives $\dim S\le\dim S^\perp$. The orthogonal-complement dimension formula gives $\dim S^\perp=2n-\dim S$ (`finrank_sym_orth`), hence $\dim S\le2n-\dim S$. Because $S$ is a subspace of $V$, its dimension is at most $\dim V=2n$ (`finrank_V`); this ensures the subtraction inequality can be rearranged to $2\dim S\le2n$. Dividing by two yields $\dim S\le n$.

**Key facts.** `finrank_sym_orth`, `finrank_V`.
