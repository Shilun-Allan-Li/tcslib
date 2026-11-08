<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/NoiseOperatorExercises.lean :: FABL.weighted_geometric_sum_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Weighted Geometric-Sum Inequality

**Claim.** For nonnegative weights $w_i,a_i$ on a finite set and $0<\lambda<1$, the weighted sum of $a_i^{1-\lambda}$ is at most $(\sum_i w_i)^\lambda(\sum_i w_i a_i)^{1-\lambda}$.

**Proof.** Set $p=1/(1-\lambda)$. Since $0<\lambda<1$, we have $p\geq1$ and $p^{-1}=1-\lambda$. Apply the weighted Hölder inequality in the form $\sum_i w_i b_i\leq(\sum_i w_i)^{1-1/p}(\sum_i w_i b_i^p)^{1/p}$ to $b_i=a_i^{1-\lambda}$. Nonnegativity makes these real powers well-defined, and the power laws give $b_i^p=a_i$. Thus the bound becomes $(\sum_i w_i)^\lambda(\sum_i w_i a_i)^{1-\lambda}$, as required.
