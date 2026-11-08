<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHard.lean :: Complexity.PathHard.nV_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of the vertex count

**Claim.** For nonnegative integers $K,c_0$ and $m\le m'$, one has $n_V(K,c_0,m)\le n_V(K,c_0,m')$.

**Proof.** The binary-expansion length is monotone: $\ell(m)\le\ell(m')$ whenever $m\le m'$ (`ell_mono`). Multiplication by the nonnegative coefficient $K(c_0+1)$ and addition of the fixed term $K+2$ preserve this inequality, so the exponent defining $n_V(K,c_0,m)$ is at most the exponent defining $n_V(K,c_0,m')$. Since powers of $2$ increase with their natural-number exponent, the claimed inequality follows.

**Key facts.** `Complexity.PathHard.ell_mono`.
