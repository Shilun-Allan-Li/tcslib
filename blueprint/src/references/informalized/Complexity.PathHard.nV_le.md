<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHard.lean :: Complexity.PathHard.nV_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper bound for the vertex count

**Claim.** For nonnegative integers $K,c_0,m$, the vertex count satisfies $n_V(K,c_0,m)\le 2^{K+2}\,2^{K(c_0+1)}(m+1)^{K(c_0+1)}$.

**Proof.** By definition, the exponent of $n_V$ is $K(c_0+1)\ell(m)+(K+2)$. Splitting the power across this sum and rearranging gives $n_V=(2^{\ell(m)})^{K(c_0+1)}2^{K+2}$. The binary-length estimate $2^{\ell(m)}\le 2(m+1)$ (`two_pow_ell_le`), raised to the nonnegative power $K(c_0+1)$, yields $(2^{\ell(m)})^{K(c_0+1)}\le 2^{K(c_0+1)}(m+1)^{K(c_0+1)}$. Multiplying by $2^{K+2}$ and rearranging factors proves the bound.

**Key facts.** `Complexity.PathHard.two_pow_ell_le`.
