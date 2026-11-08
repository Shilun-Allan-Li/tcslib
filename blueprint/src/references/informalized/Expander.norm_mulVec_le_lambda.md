<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Expanders/Basic.lean :: Expander.norm_mulVec_le_lambda -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Contraction on the Orthogonal Subspace

**Claim.** For a vector $v$ orthogonal to the uniform vector, $\|Av\|\le\lambda(A)\|v\|$.

**Proof.** If $v=0$, the inequality is immediate. Otherwise, its norm is positive, and $w=v/\|v\|$ is a unit vector still orthogonal to the uniform vector. The set of values whose supremum defines $\lambda(A)$ is bounded above by the operator norm, so its supremum bounds each of its members; in particular, $\|Aw\|\le\lambda(A)$. By linearity and homogeneity of the norm, $\|Av\|=\|v\|\|Aw\|$. Multiplying the preceding bound by the positive number $\|v\|$ yields the claim.
