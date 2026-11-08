<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/OneBitHypercontractivity.lean :: FABL.uniformInner_le_uniformLpNorm_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Hölder inequality

**Claim.** For finite nonempty $\Omega$, if $p$ and $q$ are Hölder conjugates, then the uniform inner product of $f$ and $g$ is at most the product of their uniform $L^p$ and $L^q$ norms.

**Proof.** Put $N=|\Omega|$, $A=\sum_x|f(x)|^p$, and $B=\sum_x|g(x)|^q$. Finite-sum Hölder gives $\sum_x f(x)g(x)\le A^{1/p}B^{1/q}$. The uniform inner product is the left-hand sum divided by $N$. The uniform norms are $(A/N)^{1/p}$ and $(B/N)^{1/q}$. Their product equals $A^{1/p}B^{1/q}/N$, because the reciprocal exponents sum to $1$ for Hölder conjugates. Dividing the finite-sum inequality by $N>0$ yields the result.
